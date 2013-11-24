;; heee.el --- Functional programming mini-library

;; Copyright (C) 2013  Mateusz Kowalczyk

;; Author: Mateusz Kowalczyk <fuuzetsu@fuuzetsu.co.uk>
;; Keywords: functional, haskell, why

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file contains various functional programming functions and types
;; used throughout yon-chan. Purity is emulated but can't be enforced.

;;; Code:

;; some utils

(defmacro flip (f)
  `(lambda (x y) (,f y x)))

;; Maybe a
(cl-defstruct maybe
  (val nil :read-only t)
  (is-nothing :read-only t))

(defun type-err (fn x)
  (error (concat "Called " fn " with the wrong type `"
                 (format "%s" (type-of x)) " with value "
                 (format "%s" x))))

(defun Nothing ()
  (make-maybe :is-nothing t))

(defun Just (x)
  (make-maybe :val x :is-nothing nil))

(defun is-just (x)
  (if (maybe-p x)
      (not (maybe-is-nothing x))
    (type-err "is-just" x)))

(defun fmap-maybe (f x)
  (if (is-just x)
      (Just (funcall f (maybe-val x)))
    (Nothing)))

(defun show-maybe (x)
  (if (is-just x)
      (concat "Just " (format "%s" (maybe-val x)))
    "Nothing"))

(defun pure-maybe (x)
  (Just x))

(defun <*>-maybe (f x)
  (if (maybe-is-nothing f)
      (Nothing)
    (if (maybe-is-nothing x)
        (Nothing)
      (Just (funcall (maybe-val f) (maybe-val x))))))

(defun return-maybe (x)
  (pure-maybe x))

(defun >>=-maybe (m f)
  (if (maybe-is-nothing m)
      (Nothing)
    (funcall f (maybe-val m))))

;; Either a b
(cl-defstruct either
  (val :read-only t)
  (is-left :read-only t))

(defun Left (x)
  (make-either :val x :is-left t))

(defun Right (x)
  (make-either :val x :is-left nil))

(defun is-left (x)
  (if (either-p x)
      (either-is-left x)
    (type-err "is-left" x)))

(defun is-right (x)
  (if (either-p x)
      (not (either-is-left x))
    (type-err "is-right" x)))

(defun fmap-either (f x)
  (if (is-right x)
      (Right (funcall f (either-val x)))
    x))

(defun show-either (x)
  (if (is-right x)
      (concat "Right " (format "%s" (either-val x)))
    (concat "Left " (format "%s" (either-val x)))))

(defun pure-either (x)
  (Right x))

(defun <*>-either (f x)
  (if (is-left f)
      f
    (fmap (either-val f) x)))

(defun return-either (x)
  (pure-either x))

(defun >>=-either (m f)
  (if (is-left m)
      m
    (funcall f (either-val m))))

;; [a]
(cl-defstruct func-list
  (val :read-only t)
  (list-type :read-only t))

(defun func-list-empty (x)
  "Creates an empty list of type passed using x."
  (make-func-list :val '() :list-type x))

(defun func-list-cons (x xs)
  (if (eq (type-of x) (func-list-list-type xs))
      (make-func-list
       :val (cons x (func-list-val xs))
       :list-type (func-list-list-type xs))
    (error (concat "func-list-cons expected element of type "
                   (format "%s" (func-list-list-type xs))
                   " but got " (format "%s" (type-of x))))))

(defun func-list-null (xs)
  (eq (length (func-list-val xs)) 0))

(defun cons-list->func-list (xs &optional t₁)
  "Makes a func-list out of an ELisp cons list while checking
the type of the topmost-element."
  (if (eq (length xs) 0) ;; cons-list empty
      (if (eq t₁ nil)
          (error "Can't convert empty lists without extra type information.")
        (func-list-empty t₁))
    (let ((v (car xs)))
      (func-list-cons v (cons-list->func-list (cdr xs) (type-of v))))))

(defun func-list->cons-list (xs)
  (func-list-val xs))

(defun func-list-length (xs)
  (length (func-list-val xs)))

(defun head (xs)
  (if (not (func-list-null xs))
      (car (func-list-val xs))
    (error "Tried to take head of an empty list!")))

(defun tail (xs)
  (if (func-list-null xs)
      (error "Tried to take tail of an empty list!")
    (cons-list->func-list (cdr (func-list-val xs)) (func-list-list-type xs))))

(defun func-list-map (f xs &optional t₁)
  (if (not (func-list-null xs))
      (let ((v (funcall f (head xs))))
        (func-list-cons v (func-list-map f (tail xs) (type-of v))))
    (if t₁
        (func-list-empty t₁)
      (error "Can't map over an empty list without extra type information."))))

(defun func-list-last (xs)
  (if (func-list-null xs)
      (error "Tried to take last of an empty list!")
    (if (eq (func-list-length xs)) 1)
        (head xs)
      (func-list-last (tail xs))))

;; helper, we'd hide it if we could
(defun prepend-to-all (x xs)
  (if (func-list-null xs)
      (func-list-empty (func-list-list-type xs))
    (func-list-cons x
                    (func-list-cons (head xs)
                                    (prepend-to-all x (tail xs))))))

(defun intersperse (x xs)
  (if (func-list-null xs)
      xs
    (func-list-cons (head xs) (prepend-to-all x (tail xs)))))

(defun func-list-++ (xs ys)
  (if (func-list-null xs)
      ys
    (func-list-cons (head xs) (func-list-++ (tail xs) ys))))

(defun func-list-reverse (xs)
  (foldl (flip func-list-cons) (func-list-empty (func-list-list-type xs)) xs))

(defun func-list-concat (xs &optional t₁)
  "This is very unsafe because we have to use unparametrised vector type
so with more than one level of nesting, we end up with a list of vectors and we
can't get anything that we can count on out of it. You're fine until you triple
nest."
  (if (func-list-null xs)
      (error "Can't concat an empty list without extra type information. ;(")
    (let ((t₂ (func-list-list-type (head xs))))
      (foldr 'func-list-++ (func-list-empty t₂) xs))))

(defun foldl (f x xs)
  (if (func-list-null xs)
      x
    (foldl f (funcall f x (head xs)) (tail xs))))

(defun foldr (f x xs)
  (if (func-list-null xs)
      x
    (funcall f (head xs) (foldr f x (tail xs)))))

(defun fmap-func-list (f xs &optional t₁)
  (func-list-map f xs t₁))

(defun show-func-list (xs)
  (if (func-list-null xs)
      "[]"
    (concat "["
            (foldr (lambda (x y) (concat x y)) ""
                   (intersperse ", " (func-list-map (lambda (x) (format "%s" x))
                                                    xs)))
            "]")))

(defun pure-func-list (x)
  (func-list-cons x (func-list-empty (type-of x))))

(defun <*>-func-list (fs xs &optional t₁)
  (if (or (func-list-null fs) (func-list-null xs))
      (if t₁
          (func-list-empty t₁)
        (error "Need extra type information for [] <*> xs or fs <*> []."))
    (let ((vs (func-list-map (head fs) xs)))
      (func-list-++ vs (<*>-func-list (tail fs) xs (func-list-list-type vs))))))

(defun return-func-list (x)
  (pure-func-list x))

(defun >>=-func-list (m f &optional t₁)
  (if (func-list-null m)
      (if t₁
          (func-list-empty t₁)
        (error "Need extra type information for >>=-func-list [] f."))
    (lexical-let* ((v (funcall f (head m))) ;; use length of m to >0
                   (f f)) ;; dynamic scoping is everything that's wrong
      (foldr (lambda (x y)
               (func-list-++ (funcall f x) y))
             v
             (tail m)))))

;; Function
(cl-defstruct func
  (name :read-only t)
  (take-type :read-only t)
  (return-type :read-only t)
  (body :read-only t))

(defun run-func (f &optional args)
  (if (> (length args) (length (func-take-type f)))
      (error (format "%s takes at most %d arguments but was applied to %d"
                     (func-name f)
                     (length (func-take-type f))
                     (length args)))
    (if (eq nil args) ;; empty args
        (if (func-take-type f)
            f ;; more stuff to take, return self
          (func-body f)) ;; done taking stuff, return result
      (if (func-take-type f) ;; non-nil args, more to take
          (if (eq (car (func-take-type f))
                  (type-of (car args)))
              (run-func (make-func
                         :name (func-name f)
                         :take-type (cdr (func-take-type f))
                         :return-type (func-return-type f)
                         :body (funcall (func-body f) (car args)))
                        (cdr args))
            (error (format "Expected %s and got %s in %s."
                           (car (func-take-type f))
                           (type-of (car args))
                           (func-name f))))))))

;; (setq somefun
;;       (make-func
;;        :name "addxy5"
;;        :take-type '(integer integer)
;;        :return-type 'integer
;;        :body (lambda (x)
;;                (lexical-let ((x x))
;;                  (lambda (y) (+ x y 5))))))

(defun show-func (f)
  (let ((input-types (cons-list->func-list (func-take-type f) 'symbol)))
    (foldr 'concat "" (intersperse
                       " -> "
                       (func-list-map (lambda (x) (format "%s" x))
                                      input-types)))))

;; type class stuff, sure wish this was less horrible

;; Functor
(defun fmap (f x &optional t₁)
  (cond ((maybe-p x) (fmap-maybe f x))
        ((either-p x) (fmap-either f x))
        ((func-list-p x) (fmap-func-list f x t₁))
        (t (error (concat (format "%s" (type-of x))
                          " type doesn't have an assigned fmap function.")))))

;; Incomplete Show
(defun show (x)
  (cond ((maybe-p x) (show-maybe x))
        ((either-p x) (show-either x))
        ((func-list-p x) (show-func-list x))
        ((func-p x) (show-func x))
        (t (format "%s" (type-of x)))))

;; Applicative
(defun pure (c x)
  (cond ((eq 'maybe x) (pure-maybe c))
        ((eq 'either x) (pure-either c))
        ((eq 'func-list x) (pure-func-list c))
        (t (error (concat (format "%s" (type-of x))
                          " type doesn't have an assigned pure function.")))))

(defun <*> (x y &optional t₁)
  (lexical-let* ((x x)
                 (y y)
                 (tp (lambda (p) (and (funcall p x) (funcall p y)))))
    (cond ((funcall tp 'maybe-p) (<*>-maybe x y))
          ((funcall tp 'either-p) (<*>-either x y))
          ((funcall tp 'func-list-p) (<*>-func-list x y t₁))
          (t (error (concat (format "%s" (type-of x))
                            " type doesn't have an assigned <*> function"
                            " or two different types were passed in."))))))
;; Monad
(defun return (c x)
  (cond ((eq 'maybe x) (return-maybe c))
        ((eq 'either x) (return-either c))
        ((eq 'func-list x) (return-func-list c))
        (t (error (concat (format "%s" (type-of x))
                          " type doesn't have an assigned return function.")))))

(defun >>= (m f &optional t₁)
  (cond ((maybe-p m) (>>=-maybe m f))
        ((either-p m) (>>=-either m f))
        ((func-list-p m) (>>=-func-list m f t₁))
        (t (error (concat (format "%s" (type-of m))
                          " type doesn't have an assigned >>= function.")))))

(defun >> (m f &optional t₁)
  (lexical-let ((f f))
    (>>= m (lambda (x) f) t₁)))

(defun fail (s)
  error s)

(provide 'heee)
;;; heee.el ends here
