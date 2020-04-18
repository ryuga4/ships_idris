#!/usr/bin/chezscheme9.5 --script

(import (chezscheme))
(case (machine-type)
  [(i3le ti3le a6le ta6le) (load-shared-object "libc.so.6")]
  [(i3osx ti3osx a6osx ta6osx) (load-shared-object "libc.dylib")]
  [(i3nt ti3nt a6nt ta6nt) (load-shared-object "msvcrt.dll")]
  [else (load-shared-object "libc.so")])



(let ()
(define blodwen-read-args (lambda (desc)
  (case (vector-ref desc 0)
    ((0) '())
    ((1) (cons (vector-ref desc 2)
               (blodwen-read-args (vector-ref desc 3)))))))
(define b+ (lambda (x y bits) (remainder (+ x y) (expt 2 bits))))
(define b- (lambda (x y bits) (remainder (- x y) (expt 2 bits))))
(define b* (lambda (x y bits) (remainder (* x y) (expt 2 bits))))
(define b/ (lambda (x y bits) (remainder (floor (/ x y)) (expt 2 bits))))

(define blodwen-shl (lambda (x y) (ash x y)))
(define blodwen-shr (lambda (x y) (ash x (- y))))
(define blodwen-and (lambda (x y) (logand x y)))
(define blodwen-or (lambda (x y) (logor x y)))
(define blodwen-xor (lambda (x y) (logxor x y)))

(define cast-num
  (lambda (x)
    (if (number? x) x 0)))
(define destroy-prefix
  (lambda (x)
    (cond
      ((equal? x "") "")
      ((equal? (string-ref x 0) #\#) "")
      (else x))))
(define cast-string-int
  (lambda (x)
    (floor (cast-num (string->number (destroy-prefix x))))))
(define cast-string-double
  (lambda (x)
    (cast-num (string->number (destroy-prefix x)))))
(define string-cons (lambda (x y) (string-append (string x) y)))
(define get-tag (lambda (x) (vector-ref x 0)))
(define string-reverse (lambda (x)
  (list->string (reverse (string->list x)))))
(define (string-substr off len s)
    (let* ((l (string-length s))
          (b (max 0 off))
          (x (max 0 len))
          (end (min l (+ b x))))
          (substring s b end)))

(define either-left
  (lambda (x)
    (vector 0 #f #f x)))

(define either-right
  (lambda (x)
    (vector 1 #f #f x)))

(define blodwen-error-quit
  (lambda (msg)
    (display msg)
    (newline)
    (exit 1)))

;; Buffers

(define (blodwen-new-buffer size)
  (make-bytevector size 0))

(define (blodwen-buffer-size buf)
  (bytevector-length buf))

(define (blodwen-buffer-setbyte buf loc val)
  (bytevector-u8-set! buf loc val))

(define (blodwen-buffer-getbyte buf loc)
  (bytevector-u8-ref buf loc))

(define (blodwen-buffer-setint buf loc val)
  (bytevector-s32-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getint buf loc)
  (bytevector-s32-ref buf loc (native-endianness)))

(define (blodwen-buffer-setdouble buf loc val)
  (bytevector-ieee-double-set! buf loc val (native-endianness)))

(define (blodwen-buffer-getdouble buf loc)
  (bytevector-ieee-double-ref buf loc (native-endianness)))

(define (blodwen-stringbytelen str)
  (bytevector-length (string->utf8 str)))

(define (blodwen-buffer-setstring buf loc val)
  (let* [(strvec (string->utf8 val))
         (len (bytevector-length strvec))]
    (bytevector-copy! strvec 0 buf loc len)))

(define (blodwen-buffer-getstring buf loc len)
  (let [(newvec (make-bytevector len))]
    (bytevector-copy! buf loc newvec 0 len)
    (utf8->string newvec)))

(define (blodwen-buffer-copydata buf start len dest loc)
  (bytevector-copy! buf start dest loc len))

(define (blodwen-readbuffer-bytes h buf loc max)
  (guard (x (#t -1))
    (get-bytevector-n! h buf loc max)))

(define (blodwen-readbuffer h)
  (guard (x (#t (bytevector)))
    (get-bytevector-all h)))

(define (blodwen-writebuffer h buf loc max)
  (guard (x (#t -1))
     (put-bytevector h buf loc max)
     max))

;; Files: Much of the following adapted from idris-chez, thanks to Niklas
;; Larsson

;; All the file operations are implemented as primitives which return
;; Either Int x, where the Int is an error code:
(define (blodwen-error-code x)
    (cond
        ((i/o-read-error? x) 1)
        ((i/o-write-error? x) 2)
        ((i/o-file-does-not-exist-error? x) 3)
        ((i/o-file-protection-error? x) 4)
        (else 255)))

;; If the file operation raises an error, catch it and return an appropriate
;; error code
(define (blodwen-file-op op)
  (guard
    (x ((i/o-error? x) (either-left (blodwen-error-code x))))
    (either-right (op))))

(define (blodwen-get-n n p)
    (if (port? p) (get-string-n p n) ""))

(define (blodwen-putstring p s)
    (if (port? p) (put-string p s) void)
    0)

(define (blodwen-open file mode bin)
    (define tc (if (= bin 1) #f (make-transcoder (utf-8-codec))))
    (define bm (buffer-mode line))
    (case mode
        (("r") (open-file-input-port file (file-options) bm tc))
        (("w") (open-file-output-port file (file-options no-fail) bm tc))
        (("wx") (open-file-output-port file (file-options) bm tc))
        (("a") (open-file-output-port file (file-options no-fail no-truncate) bm tc))
        (("r+") (open-file-input/output-port file (file-options no-create) bm tc))
        (("w+") (open-file-input/output-port file (file-options no-fail) bm tc))
        (("w+x") (open-file-input/output-port file (file-options) bm tc))
        (("a+") (open-file-input/output-port file (file-options no-fail no-truncate) bm tc))
        (else (raise (make-i/o-error)))))

(define (blodwen-close-port p)
    (when (port? p) (close-port p)))

(define (blodwen-get-line p)
    (if (and (port? p) (not (port-eof? p)))
        (let ((str (get-line p)))
            (string-append str "\n"))
        ""))

(define (blodwen-get-char p)
    (if (and (port? p) (not (port-eof? p)))
        (get-char p)
        #\nul))

(define (blodwen-file-modified-time p)
    (time-second (file-modification-time p)))

(define (blodwen-file-size p)
    (port-length p))

(define (blodwen-eof p)
    (if (port-eof? p)
        1
        0))

;; Directories

(define (blodwen-current-directory)
  (current-directory))

(define (blodwen-change-directory dir)
  (if (file-directory? dir)
      (begin (current-directory dir) 1)
      0))

(define (blodwen-create-directory dir)
  (blodwen-file-op (lambda () (mkdir dir) 0)))

; Scheme only gives a primitive for reading all the files in a directory,
; so this is faking the C interface!
(define (blodwen-open-directory dir)
  (blodwen-file-op (lambda () (box (directory-list dir)))))

(define (blodwen-close-directory dir) '()) ; no-op, it's not really open

(define (blodwen-next-dir-entry dir)
  (let [(dlist (unbox dir))]
    (if (null? dlist)
      (either-left 255)
      (begin (set-box! dir (cdr dlist))
             (either-right (car dlist))))))

;; Threads

(define blodwen-thread-data (make-thread-parameter #f))

(define (blodwen-thread p)
    (fork-thread (lambda () (p (vector 0)))))

(define (blodwen-get-thread-data)
  (blodwen-thread-data))

(define (blodwen-set-thread-data a)
  (blodwen-thread-data a))

(define (blodwen-mutex) (make-mutex))
(define (blodwen-lock m) (mutex-acquire m))
(define (blodwen-unlock m) (mutex-release m))
(define (blodwen-thisthread) (get-thread-id))

(define (blodwen-condition) (make-condition))
(define (blodwen-condition-wait c m) (condition-wait c m))
(define (blodwen-condition-wait-timeout c m t) (condition-wait c m t))
(define (blodwen-condition-signal c) (condition-signal c))
(define (blodwen-condition-broadcast c) (condition-broadcast c))

(define (blodwen-sleep s) (sleep (make-time 'time-duration 0 s)))
(define (blodwen-usleep s)
  (let ((sec (div s 1000000))
        (micro (mod s 1000000)))
       (sleep (make-time 'time-duration (* 1000 micro) sec))))

(define (blodwen-time) (time-second (current-time)))

(define (blodwen-args)
  (define (blodwen-build-args args)
    (if (null? args)
        (vector 0 '())
        (vector 1 '() (car args) (blodwen-build-args (cdr args)))))
    (blodwen-build-args (command-line)))

(define (blodwen-hasenv var)
  (if (eq? (getenv var) #f) 0 1))

(define (blodwen-system cmd)
  (system cmd))
(define prim__add_Integer (lambda (v-0 v-1) (+ v-0 v-1)))
(define prim__sub_Integer (lambda (v-0 v-1) (- v-0 v-1)))
(define prim__mul_Integer (lambda (v-0 v-1) (* v-0 v-1)))
(define prim__lte_Integer (lambda (v-0 v-1) (or (and (<= v-0 v-1) 1) 0)))
(define prim__strAppend (lambda (v-0 v-1) (string-append v-0 v-1)))
(define Main-main (lambda () (PrimIO-putStrLn "hello Ships!")))
(define Prelude-case--3176-3342 (lambda (v-0 v-1) (let ((sc0 v-1)) (case (get-tag sc0) ((0) 0) ((1) (+ 1 (- v-0 ((Prelude-fromInteger_Num__Integer) 1))))))))
(define Prelude-fromInteger_Num__Integer (lambda () (lambda (v-0) v-0)))
(define Prelude-__Impl_Num_Integer (lambda () (vector 0 'erased (lambda (v-0) (lambda (v-1) (((Prelude-C-43_Num__Integer) v-0) v-1))) (lambda (v-0) (lambda (v-1) (((Prelude-C-42_Num__Integer) v-0) v-1))) (lambda (v-0) ((Prelude-fromInteger_Num__Integer) v-0)))))
(define Prelude-C-43_Num__Integer (lambda () (lambda (v-0) (lambda (v-1) (+ v-0 v-1)))))
(define Prelude-C-42_Num__Integer (lambda () (lambda (v-0) (lambda (v-1) (* v-0 v-1)))))
(define Prelude-natToInteger (lambda (v-0) (let ((sc0 v-0)) (cond ((equal? sc0 0) ((Prelude-fromInteger_Num__Integer) 0))(else (let ((v-1 (- v-0 1))) (((Prelude-C-43_Num__Integer) ((Prelude-fromInteger_Num__Integer) 1)) v-1)))))))
(define Prelude-integerToNat (lambda (v-0) (Prelude-case--3176-3342 v-0 (let ((sc0 (or (and (<= v-0 ((Prelude-fromInteger_Num__Integer) 0)) 1) 0))) (cond ((equal? sc0 0) (vector 1 ))(else (vector 0 )))))))
(define Prelude-intToBool (lambda (v-0) (let ((sc0 v-0)) (cond ((equal? sc0 0) (vector 1 ))(else (vector 0 ))))))
(define Prelude-id (lambda (v-0 v-1) v-1))
(define Prelude-fromInteger (lambda (v-0 v-1) (let ((sc0 v-1)) (case (get-tag sc0) ((0) (let ((v-2 (vector-ref sc0 1))) (let ((v-3 (vector-ref sc0 2))) (let ((v-4 (vector-ref sc0 3))) (let ((v-5 (vector-ref sc0 4))) (lambda (v-6) (v-5 v-6)))))))))))
(define Prelude-C-43 (lambda (v-0 v-1) (let ((sc0 v-1)) (case (get-tag sc0) ((0) (let ((v-2 (vector-ref sc0 1))) (let ((v-3 (vector-ref sc0 2))) (let ((v-4 (vector-ref sc0 3))) (let ((v-5 (vector-ref sc0 4))) (lambda (v-6) (lambda (v-7) ((v-3 v-6) v-7))))))))))))
(define PrimIO-case--307-329 (lambda (v-0 v-1 v-2 v-3) (PrimIO-unsafeDestroyWorld 'erased 'erased v-3)))
(define PrimIO-unsafePerformIO (lambda (v-0 v-1) (PrimIO-unsafeCreateWorld 'erased (lambda (v-2) (PrimIO-case--307-329 'erased v-1 'erased (v-1 v-2))))))
(define PrimIO-unsafeDestroyWorld (lambda (v-0 v-1 v-2) v-2))
(define PrimIO-unsafeCreateWorld (lambda (v-0 v-1) (v-1 #f)))
(define PrimIO-putStrLn (lambda (v-0) (PrimIO-putStr (string-append v-0 "\xa;"))))
(define PrimIO-putStr (lambda (v-0) (lambda (v-1) (display v-0) (vector 0 ))))
(define PrimIO-prim__putStr (lambda (v-0 v-1) (display v-0) (vector 0 )))
(define PrimIO-primIO (lambda (v-0 v-1) v-1))
(define Builtin-assert_total (lambda (v-0 v-1) v-1))
(PrimIO-unsafePerformIO 'erased (Main-main)))