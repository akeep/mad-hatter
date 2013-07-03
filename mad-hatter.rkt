#lang racket

;; Step 1. Build a direct style CES intrpreter

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

(define apply-closure
  (lambda (p arg)
    (match p
      [`(closure ,x ,body ,e) (ce body (extend-env e x arg))]
      [_ (error 'apply-closure "~s is not a procedure" p)])))

(define ce
  (lambda (c e)
    (match c
      [(? symbol? x) (apply-env e x)]
      [`(lambda (,x) ,body) (build-closure x body e)]
      [`(,rator ,rand) (apply-closure (ce rator e) (ce rand e))])))

(provide ce empty-env)
