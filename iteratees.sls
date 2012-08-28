#!r6rs
;;; iteratees.sls --- Iteratees

;; Copyright (C) 2012 Ian Price <ianprice90@googlemail.com>

;; Author: Ian Price <ianprice90@googlemail.com>

;; This program is free software, you can redistribute it and/or
;; modify it under the terms of the new-style BSD license.

;; You should have received a copy of the BSD license along with this
;; program. If not, see <http://www.debian.org/misc/bsd.license>.
(library (iteratees)
(export make-chunk
        chunk?
        chunk-data
        stream?

        make-done
        done?
        result
        make-cont
        cont?
        cont-k
        iteratee?

        return
        >>=

        peek
        head
        break
        heads
        take
        drop
        skip-to-eof
        length

        enum-eof
        enum-string
        enum-port
        enum-file
        >>>

        run
        run-enumerator
        &divergent
        make-divergent-condition
        divergent-condition?
        )
(import (except (rnrs) length)
        (srfi :13)
        (srfi :8)
        (prefix (monad maybe) m:))

;; Stream data type

(define-record-type chunk
  (fields data))

(define (stream? s)
  (or (chunk? s)
      (eof-object? s)))

(define-syntax stream-case
  (syntax-rules (chunk eof)
    ((stream-case stream-expr ((chunk) empty-chunk-case) ((chunk s) chunk-case) ((eof) empty-case))
     (let ((stream stream-expr))
       (if (chunk? stream)
           (let ((s (chunk-data stream)))
             (if (string-null? s)
                 empty-chunk-case
                 chunk-case))
           empty-case)))))

;; Iteratee data type

(define-record-type done
  (fields (immutable result result)))

(define-record-type cont
  ;; k : Stream -> Iteratee + Stream
  (fields k))

(define (iteratee? x)
  (or (done? x)
      (cont? x)))

;; utilities
(define empty-chunk (make-chunk ""))

(define (doneM s)
  (values (make-done s) empty-chunk))

(define (contM s)
  (values (make-cont s) empty-chunk))

(define (string-break p s)
  (define idx (string-index s p))
  (if idx
      (values (string-take s idx)
              (string-drop s idx))
      (values s "")))

(define (continue i v)
  ((cont-k i) v))

(define buffer-size 1024)

(define (string-split-at s n)
  (values (string-take n s)
          (string-drop n s)))

;; Iteratee Monad Instance

(define return make-done)

(define (>>= m f)
  (define (do-case i s)
    (if (done? i)
        (let ((new-i (f (result i))))
          (if (cont? new-i)
              (continue new-i s)
              (values new-i s)))
        (values (>>= i f) s)))
  (if (done? m)
      (f (result m))
      (make-cont
       (lambda (x)
         (receive (i s) (continue m x)
           (do-case i s))))))

;; Iteratees

(define peek
  (letrec ((step (lambda (stream)
                   (stream-case stream
                     ((chunk)
                      (values peek stream))
                     ((chunk s)
                      (values (make-done (m:just (string-ref s 0))) stream))
                     ((eof)
                      (values (make-done (m:nothing)) stream))))))
    (make-cont step)))

(define head
  (letrec ((step (lambda (stream)
                   (stream-case stream
                     ((chunk) (values peek stream))
                     ((chunk s)
                      (values (make-done (m:just (string-ref s 0)))
                              (make-chunk (string-drop s 1))))
                     ((eof)
                      (values (make-done (m:nothing)) stream))))))
    (make-cont step)))

(define (break pred?)
  (define (step before)
    (lambda (stream)
      (stream-case stream
        ((chunk) (contM (step before)))
        ((chunk s)
         (receive (prefix suffix) (string-break pred? s)
           (if (string-null? suffix)
               (contM (step (string-append before prefix)))
               (values (make-done (string-append before prefix))
                       (make-chunk suffix)))))
        ((eof)
         (values (make-done before) stream)))))
  (make-cont (step "")))

(define (heads prefix)
  (define (loop count cs)
    (if (null? cs)
        (return count)
        (make-cont (step count cs))))
  (define (step count cs)
    (lambda (stream)
      (stream-case stream
        ((chunk)
         (values (loop count cs) stream))
        ((chunk s)
         (if (null? cs)
             (values (make-done count) stream)
             (if (char=? (car cs) (string-ref s 0))
                 ((step (+ 1 count) (cdr cs))
                  (make-chunk (string-drop s 1)))
                 (values (make-done count) stream))))
        ((eof)
         (values (make-done count) stream)))))
  (loop 0 (string->list prefix)))

(define (take n iter)
  (define (step n k)
    (lambda (stream)
      (stream-case stream
        ((chunk)
         (contM (step n k)))
        ((chunk s)
         (if (< (string-length s) n)
             (receive (i s) (k stream)
               (values (take (- n (string-length s)) i)
                       empty-chunk))
             (let*-values (((s1 s2) (string-split-at n s))
                           ((i s*) (k (make-chunk s1))))
               (values (make-done i) (make-chunk s2)))))
        ((eof)
         (receive (i s) (k stream)
           (values (make-done i) stream))))))
  (cond ((and (zero? n) (cont? iter))
         (return iter))
        ((cont? iter)
         (make-cont (step n (cont-k iter))))
        (else
         (>>= (drop n)
              (lambda (_) (return iter))))))

(define (drop n)
  (define (step stream)
    (stream-case stream
      ((chunk)
       (values (make-cont step) stream))
      ((chunk s)
       (if (>= (string-length s) n)
           (values (make-done '()) (make-chunk (string-drop s n)))
           (values (drop (- n (string-length s))) empty-chunk)))
      ((eof)
       (values (make-done '()) stream))))
  (make-cont step))

(define length
  (letrec ((step (lambda (n)
                   (lambda (stream)
                     (stream-case stream
                       ((chunk)
                        (values (make-cont (step n)) stream))
                       ((chunk s)
                        (values (make-cont (step (+ n (string-length s))))
                                empty-chunk))
                       ((eof)
                        (values (make-done n) stream)))))))
    (make-cont (step 0))))

(define skip-to-eof
  (make-cont (lambda (stream)
               (if (chunk? stream)
                   (values skip-to-eof empty-chunk)
                   (values (make-done '()) stream)))))


;; enumerators
(define (enum-eof iter)
  (if (cont? iter)
      (receive (iter* stream) (continue iter (eof-object))
        iter*)
      iter))

(define (enum-string string)
  (lambda (iter)
    (if (cont? iter)
        (receive (iter* stream) (continue iter (make-chunk string))
          iter*)
        iter)))

(define (enum-port port)
  (define (loop iter)
    (if (cont? iter)
        (let ((str (get-string-n port buffer-size)))
          (if (eof-object? str)
              iter
              (receive (iter s) (continue iter (make-chunk str))
                (loop iter))))
        iter))
  loop)

(define (enum-file file)
  (enum-port (open-file-input-port file)))

(define >>>
  (let ((join (lambda (g f)
                (lambda (x)
                  (f (g x))))))
    (case-lambda
      (() (lambda (x) x))
      ((a) a)
      ((a b) (join a b))
      ((a b . c)
       (fold-left join a (cons b c))))))


;; running iteratees

(define (run iteratee)
  (if (done? iteratee)
      (result iteratee)
      (let ((iter2 (continue iteratee (eof-object))))
        (if (done? iter2)
            (result iter2)
            (diverges 'run "Iteratee diverges on eof" iteratee)))))

(define (run-enumerator enum iteratee)
  (run (enum iteratee)))

(define (diverges who message irritant)
  (raise
   (condition (make-divergent-condition)
              (make-who-condition who)
              (make-message-condition message)
              (make-irritants-condition irritant))))

(define-condition-type &divergent &error
  make-divergent-condition
  divergent-condition?)

)
