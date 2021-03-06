{-# OPTIONS --rewriting #-}

module Lib where

open import Agda.Primitive public

private
  variable
    i j k : Level
    A : Set i
    B : Set j

record π : Set where
  constructor *
open π public

data π : Set where

exfalso : π β A
exfalso ()

infixl 4 _βΈ΄_

record Ξ£Μ (A : Set i)(B : A β Set j) : Set (i β j) where
  constructor _βΈ΄_
  field
    projβ : A
    projβ : B projβ
open Ξ£Μ public

infixl 5 _ΓΜ_

_ΓΜ_ : Set i β Set j β Set (i β j)
A ΓΜ B = Ξ£Μ A (Ξ» _ β B)

infixl 4 _β_

data _β_ (A : Set i)(B : Set j) : Set (i β j) where
  injβ : A β A β B
  injβ : B β A β B

indβ : (P : A β B β Set k)
     β (β x β P (injβ x))
     β (β y β P (injβ y))
     β β t
     β P t
indβ P u v (injβ x) = u x
indβ P u v (injβ y) = v y

caseβ : {C : Set k} β A β B β (A β C) β (B β C) β C
caseβ t u v = indβ _ u v t

record ββ (A : Set i){j} : Set (i β j) where
  constructor β[_]β
  field
    β[_]β : A
open ββ public

data β : Set where
  zero : β
  suc : β β β
{-# BUILTIN NATURAL β #-}

infix 1 _β‘_
data _β‘_ {A : Set i}(x : A) : A β Set i where
  rfl : x β‘ x
{-# BUILTIN EQUALITY _β‘_ #-}
{-# BUILTIN REWRITE _β‘_ #-}

JΜ : {x : A}(P : β {y} β x β‘ y β Set j)
  β P rfl
  β β {y}(p : x β‘ y)
  β P p
JΜ P Prfl rfl = Prfl

transport : (P : A β Set j){x y : A}
          β x β‘ y
          β P x
          β P y
transport P p Px = JΜ _ Px p
