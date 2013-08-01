#lang racket

;; Step 1. Build a direct style CE intrpreter

(define empty-env '())

(define extend-env
  (lambda (e x arg)
    (cons (cons x arg) e)))

(define apply-env
  (lambda (e x)
    (match e
      [`() (error 'apply-env "~s is not in environment" x)]
      [`((,(? (lambda (y) (eq? y x)) y) . ,v) . ,e^) v]
      [`(,a . ,e^) (apply-env e^ x)])))

(define build-closure
  (lambda (x body e)
    `(closure ,x ,body ,e)))

;; overriding to support CE, CES, and CESK machines.
(define apply-closure
  (case-lambda
    [(p arg)
     (match p
       [`(closure ,x ,body ,e) (ce body (extend-env e x arg))]
       [_ (error 'apply-closure "~s is not a procedure" p)])]
    [(p arg s)
     (match p
       [`(closure ,x ,body ,e)
         (let ((loc (alloc)))
           (let ((s^ (extend-store s loc arg)))
             (let ((e^ (extend-env e x loc)))
               (ces body e^ s^))))]
       [_ (error 'apply-closure "~s is not a procedure" p)])]
    [(p arg s k)
     (match p
       [`(closure ,x ,body ,e)
         (let ((loc (alloc)))
           (let ((s^ (extend-store s loc arg)))
             (let ((e^ (extend-env e x loc)))
               (cesk body e^ s^ k))))])]))

(define ce
  (lambda (c e)
    (match c
      [(? symbol? x) (apply-env e x)]
      [`(lambda (,x) ,body) (build-closure x body e)]
      [`(,rator ,rand) (apply-closure (ce rator e) (ce rand e))])))

(provide ce empty-env)

;; Step 2. Turn it into a CES interpreter

(define alloc (lambda () (gensym "loc")))

(define empty-store '())

(define extend-store
  (lambda (s loc val)
    (cons (cons loc val) s)))

(define apply-store
  (lambda (s loc)
    (match s
      [`() (error 'apply-store "~s is not in store" loc)]
      [`((,(? (lambda (l) (eq? l loc)) l) . ,v) . ,s^) v]
      [`(,a . ,s^) (apply-store s^ loc)])))

(define lookup
  (lambda (s e x)
    (apply-store s (apply-env e x))))

(define ces
  (lambda (c e s)
    (match c
      [(? symbol? x) (values (lookup s e x) s)]
      [`(lambda (,x) ,body) (values (build-closure x body e) s)]
      [`(,rator ,rand) 
       (let-values ([(rator^ s^) (ces rator e s)])
         (let-values ([(rand^ s^^) (ces rand e s^)])
           (apply-closure rator^ rand^ s^^)))])))

(provide ces empty-store)

;; Step 3. Turn into a miniKanren CES interpreter

(require cKanren/miniKanren)
(require cKanren/absento)
(require cKanren/neq)

(define build-closureo
  (lambda (x body e v)
    (== `(closure ,x ,body ,e) v)))

(define apply-closureo
  (case-lambda
    [(p arg s v s^)
     (fresh (loc s^^ e^ x body e)
       (== `(closure ,x ,body ,e) p)
       (alloco s loc)
       (extend-storeo s loc arg s^^)
       (extend-envo e x loc e^)
       (ceso body e^ s^^ v s^))]
    [(p arg s k)
     (fresh (loc s^ e^ x body e)
       (== `(closure ,x ,body ,e) p)
       (alloco s loc)
       (extend-storeo s loc arg s^)
       (extend-envo e x loc e^)
       (cesko body e^ s^ k))]))

(define empty-envo (cons '() '()))

(define extend-envo
  (lambda (e x loc e^)
    (fresh (v* loc*)
      (== `(,v* . ,loc*) e)
      (== `((,x . ,v*) . (,loc . ,loc*)) e^))))

(define apply-env-helpero
  (lambda (v* loc* x loc)
    (fresh (v l v*^ loc*^)
      (== `(,v . ,v*^) v*)
      (== `(,l . ,loc*^) loc*)
      (conde
        [(== x v) (== l loc)]
        [(=/= x v) (apply-env-helpero v*^ loc*^ x loc)]))))

(define apply-envo
  (lambda (e x loc)
    (fresh (v* loc*)
      (== `(,v* . ,loc*) e)
      (apply-env-helpero v* loc* x loc))))

(define empty-storeo (cons '() '()))

(define alloco
  (lambda (s loc)
    (fresh (loc* val*)
      (== `(,loc* . ,val*) s)
      (symbolo loc)
      (absento loc loc*))))

(define extend-storeo
  (lambda (s loc val s^)
    (fresh (loc* val*)
      (== `(,loc* . ,val*) s)
      (== `((,loc . ,loc*) . (,val . ,val*)) s^))))

(define apply-store-helpero
  (lambda (loc* val* loc val)
    (fresh (l v val*^ loc*^)
      (== `(,l . ,loc*^) loc*)
      (== `(,v . ,val*^) val*)
      (conde
        [(== loc l) (== v val)]
        [(=/= loc l) (apply-store-helpero loc*^ val*^ loc val)]))))

(define apply-storeo
  (lambda (s loc val)
    (fresh (loc* val*)
      (== `(,loc* . ,val*) s)
      (apply-store-helpero loc* val* loc val))))

(define lookupo
  (lambda (s e x v)
    (fresh (loc)
      (apply-envo e x loc)
      (apply-storeo s loc v))))

(define ceso
  (lambda (c e s v s^)
    (conde
      [(symbolo c)
       (== s s^)
       (lookupo s e c v)]
      [(fresh (x body)
         (== `(lambda (,x) ,body) c)
         (== s s^)
         (build-closureo x body e v))]
      [(fresh (rator rand rator^ rand^ s^^ s^^^)
         (== `(,rator ,rand) c)
         (ceso rator e s rator^ s^^)
         (ceso rand e s^^ rand^ s^^^)
         (apply-closureo rator^ rand^ s^^^ v s^))])))

(provide ceso empty-envo empty-storeo
  ;; conveniences from miniKanren
  run fresh ==)

;; Step 3.25 Turn into a meta-parsable CES implmenetiaton.

(define ceso-clause
  (lambda (cl a b)
    (conde
      [(fresh (c e s v s^)
         (== `(ceso ,c ,e ,s ,v ,s^) a)
         (conde
           [(== 'CesVar cl)
            (symbolo c)
            (== s s^)
            (== `((lookupo ,s ,e ,c ,v)) b)]
           [(== 'CesLambda cl)
            (fresh (x body)
              (== `(lambda (,x) ,body) c)
              (== s s^)
              (== `((build-closureo ,x ,body ,e ,v)) b))]
           [(== 'CesCall cl)
            (fresh (rator rand rator^ rand^ s^^ s^^^)
              (== `(,rator ,rand) c)
              (== `((ceso ,rator ,e ,s ,rator^ ,s^^)
                    (ceso ,rand ,e ,s^^ ,rand^ ,s^^^)
                    (apply-closureo ,rator^ ,rand^ ,s^^^ ,v ,s^))
                b))]))]
      [(fresh (s e x v)
         (== 'Lookup cl)
         (== `(lookupo ,s ,e ,x ,v) a)
         (fresh (loc)
           (== `((apply-envo ,e ,x ,loc)
                 (apply-storeo ,s ,loc ,v))
             b)))]
      [(fresh (x body e v)
         (== 'BuildClosure cl)
         (== `(build-closureo ,x ,body ,e ,v) a)
         (== `(closure ,x ,body ,e) v)
         (== `() b))]
      [(fresh (p arg s v s^)
         (== 'ApplyClosure cl)
         (== `(apply-closureo ,p ,arg ,s ,v ,s^) a)
         (fresh (loc s^^ e^ x body e)
           (== `(closure ,x ,body ,e) p)
           (== `((alloco ,s ,loc)
                 (extend-storeo ,s ,loc ,arg ,s^^)
                 (extend-envo ,e ,x ,loc ,e^)
                 (ceso ,body ,e^ ,s^^ ,v ,s^))
             b)))]
      [(fresh (e x loc)
         (== 'ApplyEnv cl)
         (== `(apply-envo ,e ,x ,loc) a)
         (fresh (v* loc*)
           (== `(,v* . ,loc*) e)
           (== `((apply-env-helpero ,v* ,loc* ,x ,loc)) b)))]
      [(fresh (v* loc* x loc)
         (== 'ApplyEnvHelper cl)
         (== `(apply-env-helpero ,v* ,loc* ,x ,loc) a)
         (fresh (v l v*^ loc*^)
           (== `(,v . ,v*^) v*)
           (== `(,l . ,loc*^) loc*)
           (conde
             [(== x v) (== l loc) (== `() b)]
             [(=/= x v) (== `((apply-env-helpero ,v*^ ,loc*^ ,x ,loc)) b)])))]
      [(fresh (s loc val)
         (== 'ApplyStore cl)
         (== `(apply-storeo ,s ,loc ,val) a)
         (fresh (loc* val*)
           (== `(,loc* . ,val*) s)
           (== `((apply-store-helpero ,loc* ,val* ,loc ,val)) b)))]
      [(fresh (loc* val* loc val)
         (== 'ApplyStoreHelper cl)
         (== `(apply-store-helpero ,loc* ,val* ,loc ,val) a)
         (fresh (l v val*^ loc*^)
           (== `(,l . ,loc*^) loc*)
           (== `(,v . ,val*^) val*)
           (conde
             [(== loc l) (== val v) (== `() b)]
             [(=/= loc l) (== `((apply-store-helpero ,loc*^ ,val*^ ,loc ,val)) b)])))]
      [(fresh (s loc)
         (== 'Alloc cl)
         (== `(alloco ,s ,loc) a)
         (fresh (loc* val*)
           (== `(,loc* . ,val*) s)
           (symbolo loc)
           (absento loc loc*)
           (== `() b)))]
      [(fresh (s loc val s^)
         (== 'ExtendStore cl)
         (== `(extend-storeo ,s ,loc ,val ,s^) a)
         (fresh (loc* val*)
           (== `(,loc* . ,val*) s)
           (== `((,loc . ,loc*) . (,val . ,val*)) s^)
           (== `() b)))]
      [(fresh (e x loc e^)
         (== 'ExtendEnv cl)
         (== `(extend-envo ,e ,x ,loc ,e^) a)
         (fresh (x* loc*)
           (== `(,x* . ,loc*) e)
           (== `((,x . ,x*) . (,loc . ,loc*)) e^)
           (== `() b)))]
      [(fresh (kw rest)
         (== `(,kw . ,rest) a)
         (absento kw '(extend-envo extend-storeo alloco apply-store-helpero
                       apply-storeo apply-env-helpero apply-envo
                       apply-closureo build-closureo lookupo ceso))
         (== 'Unkown cl)
         (== `() b))])))

(define solve-for
  (lambda (clause)
    (lambda (goal)
      (let solve ([goals (list goal)])
        (conde
          [(== '() goals)]
          [(fresh (c g gs b goals^)
             (== `(,g . ,gs) goals)
             (clause c g b)
             (solve b)
             (solve gs))])))))

(define ceso-solve (solve-for ceso-clause))

(define solve-steps-for
  (lambda (clause)
    (lambda (goal steps)
      (let solve ([goals (list goal)] [steps steps])
        (project (goals steps)
          (prtm "steps: ~s\tgoals: ~s\n" steps goals)
          (if (= steps 0)
              succeed
              (conde
                [(== '() goals)]
                [(fresh (c g gs b goals^)
                   (== `(,g . ,gs) goals)
                   (clause c g b)
                   (appendo b gs goals^)
                   (solve goals^ (- steps 1)))])))))))

(define ceso-solve-steps (solve-steps-for ceso-clause))

(define tag-c
  (lambda (c)
    (let ([sym (gensym 'L)])
      (match c
        [(? symbol? x) (list sym x)]
        [`(lambda (,x) ,body) (list sym `(lambda (,x) ,(tag-c body)))]
        [`(,rator ,rand) (list sym `(,(tag-c rator) ,(tag-c rand)))]))))

(define untag-c
  (lambda (c)
    (match c
      [`(,t ,(? symbol? x)) x]
      [`(,t (lambda (,x) ,body)) `(lambda (,x) ,(untag-c body))]
      [`(,t (,rator ,rand)) `(,(untag-c rator) ,(untag-c rand))])))

(define solve-tagged-for
  (lambda (clause)
    (lambda (goal)
      (let solve ([goals (list goal)])
        (conde
          [(== '() goals)]
          [(fresh (g gs c b goals^)
             (== `(,g . ,gs) goals)
             ;; the following feels pretty entangled.
             (conde
               [(fresh (t r)
                  (== `(,t . ,r) g)
                  (=/= t 'ceso)
                  (clause c g b))]
               [(fresh (l e g^ r)
                  (== `(ceso (,l ,e) . ,r) g)
                  (== `(ceso ,e . ,r) g^)
                  (clause c g^ b))])
             (appendo b gs goals^)
             (solve goals^))])))))

(define ceso-solve-tagged (solve-tagged-for ceso-clause))

(define solve-abstract-timestamp-for
  (lambda (clause)
    (lambda (goal [k 0])
      (define drop-last
        (lambda (ls)
          (cond
            [(null? ls) ls]
            [(null? (cdr ls)) '()]
            [else (cons (car ls) (drop-last (cdr ls)))])))
      (define list-heado
        (lambda (t l t^)
          (if (= l 0)
              (== t^ '())
              (conde
                [(== '() t) (== '() t^)]
                [(fresh (ta td td^)
                   (== `(,ta . ,td) t)
                   (== `(,ta . ,td^) t^)
                   (list-heado td (- l 1) td^))]))))
      (define stepo
        (lambda (t l t^)
          (fresh (tt)
            (== tt `(,l . ,t))
            (list-heado tt k t^))))
      (let solve ([goals (list goal)] [time '()])
        (project (time goals)
          (prtm "time: ~s\tgoals: ~s\n" time goals)
          (conde
            [(== '() goals)]
            [(fresh (g gs c b goals^ time^ g^)
               (== `(,g . ,gs) goals)
               ;; the following feels pretty entangled.
               (conde
                 [(fresh (t r)
                    (== `(,t . ,r) g)
                    (=/= t 'ceso)
                    (== time time^)
                    (== g g^))]
                 [(fresh (l e r)
                    (== `(ceso (,l ,e) . ,r) g)
                    (== `(ceso ,e . ,r) g^)
                    ;; the following feels pretty entangled.
                    (conde
                      [(fresh (rator rand)
                         (== e `(,rator ,rand))
                         (stepo time l time^))]
                      [(fresh (x body)
                         (== e `(lambda (,x) ,body))
                         (== time time^))]
                      [(symbolo e) (== time time^)]))])
               (clause c g^ b)
               (appendo b gs goals^)
               (solve goals^ time^))]))))))

(define ceso-solve-abstract-timestamp (solve-abstract-timestamp-for ceso-clause))

(provide ceso-clause solve-for ceso-solve solve-steps-for ceso-solve-steps
  solve-tagged-for ceso-solve-tagged tag-c untag-c ceso-solve-abstract-timestamp solve-abstract-timestamp-for)


;; Step 3.5. Turn the Racket CES interpreter into CESK, by CPSing racket code.

(define initial-k (lambda (x s) x))

(define make-apply-1-k
  (lambda (rand e k)
    (lambda (rator^ s^)
      (cesk rand e s^
        (make-apply-2-k rator^ k)))))

(define make-apply-2-k
  (lambda (rator^ k)
    (lambda (rand^ s^^)
      (apply-closure rator^ rand^ s^^ k))))

(define cesk
  (lambda (c e s k)
    (match c
      [(? symbol? x)
       (k (lookup s e x) s)]
      [`(lambda (,x) ,body)
       (k (build-closure x body e) s)]
      [`(,rator ,rand) 
       (cesk rator e s (make-apply-1-k rand e k))])))

(provide initial-k cesk)


;; Step 4. Turn into a miniKanren CESK interpreter, by CPSing miniKanren code.

(define initial-ko
  (lambda (v s^)
    (lambda (v^ s^^)
      (fresh () (== v v^) (== s^ s^^)))))

(define cesko
  (let ()
    (define apply-closureo
      (lambda (p arg s k)
        (fresh (loc s^ e^ x body e)
          (== `(closure ,x ,body ,e) p)
          (alloco s loc)
          (extend-storeo s loc arg s^)
          (extend-envo e x loc e^)
          (cesko body e^ s^ k))))
    (lambda (c e s k)
      (conde
        [(symbolo c)
          (fresh (v s^)
            (== s s^)
            (lookupo s e c v)
            (k v s^))]
        [(fresh (x body v s^)
           (== `(lambda (,x) ,body) c)
           (== s s^)
           (build-closureo x body e v)
           (k v s^))]
        [(fresh (rator rand)
           (== `(,rator ,rand) c)
           (cesko rator e s
             (lambda (rator^ s^)
               (cesko rand e s^
                 (lambda (rand^ s^^)
                   (apply-closureo rator^ rand^ s^^ k))))))]))))

(provide initial-ko cesko)

;; Step 5. Turn into meta-parsable CESK interpreter

;; Tests!!!  We needs them!
;;
;; Here are the programs I've been testing with:
;; (lambda (x) x) => (closure x x ()) ()
;; ((lambda (x) x) (lambda (y) y)) => (closure y y ()) ((loc67 . (closure y y ())))
;; ((lambda (x) (x x)) (lambda (y) y)) =>
;;   (closure y y ())
;;   ((loc69 . (closure y y ())) (loc68 . (closure y y ())))
;; ((lambda (x) (x x)) (lambda (y) (y y))) => runs forever (test case for analyzer)
;;
;; Need more!
