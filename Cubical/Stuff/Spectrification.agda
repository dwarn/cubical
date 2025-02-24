{-# OPTIONS --safe #-}

module Cubical.Stuff.Spectrification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed.Base
open import Cubical.Foundations.Pointed.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Data.Nat
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit.Base
open import Cubical.Foundations.Structure

record Sequence∙ : Type1 where
  field
    obj∙ : ℕ → Pointed ℓ-zero
    map∙ : (n : ℕ) → obj∙ n →∙ obj∙ (suc n)

open Sequence∙

Sequence∙→Sequence : Sequence∙ → Sequence ℓ-zero
Sequence.obj (Sequence∙→Sequence S) n = typ (obj∙ S n)
Sequence.map (Sequence∙→Sequence S) {n} = fst (map∙ S n)

SeqColim∙ : Sequence∙ → Pointed ℓ-zero
SeqColim∙ S = SeqColim (Sequence∙→Sequence S) , incl (str (obj∙ S zero))

record Prespectrum : Type1 where
  field
    space : ℕ → Pointed ℓ-zero
    map : (n : ℕ) → space n →∙ Ω (space (suc n))

open Prespectrum

tailS : Prespectrum → Prespectrum
space (tailS X) n = space X (suc n)
map (tailS X) n = map X (suc n)

PS→seq-obj∙ : Prespectrum → ℕ → Pointed ℓ-zero
PS→seq-obj∙ X zero = space X zero
PS→seq-obj∙ X (suc n) = Ω (PS→seq-obj∙ (tailS X) n)

PS→seq-map∙ : (X : Prespectrum) (n : ℕ) → PS→seq-obj∙ X n →∙ PS→seq-obj∙ X (suc n)
PS→seq-map∙ X zero = map X zero
PS→seq-map∙ X (suc n) = Ω→ (PS→seq-map∙ (tailS X) n)

PS→seq : Prespectrum → Sequence∙
obj∙ (PS→seq X) = PS→seq-obj∙ X
map∙ (PS→seq X) = PS→seq-map∙ X

spectrification-space : Prespectrum → ℕ → Pointed ℓ-zero
spectrification-space X zero = SeqColim∙ (PS→seq X)
spectrification-space X (suc n) = spectrification-space (tailS X) n

spectrification : Prespectrum → Prespectrum
space (spectrification X) = spectrification-space X
map (spectrification X) = {!!}

isSpectrum : Prespectrum → Type
isSpectrum X = ∀ n → isEquiv (fst (map X n))

record _→S_ (X Y : Prespectrum) : Type where
  field
    app : (n : ℕ) → space X n →∙ space Y n
    nat : (n : ℕ) → map Y n ∘∙ app n ≡ Ω→ (app (suc n)) ∘∙ map X n

open _→S_

_∘S_ : {X Y Z : Prespectrum} → Y →S Z → X →S Y → X →S Z
app (f ∘S g) n = app f n ∘∙ app g n
nat (f ∘S g) = {!!}

spectrification-unit : (X : Prespectrum) → X →S spectrification X
spectrification-unit X = {!!}

spectrification-isSpectrum : (X : Prespectrum) → isSpectrum (spectrification X)
spectrification-isSpectrum X n = {!!}

bla : (X Y : Prespectrum) → spectrification X →S Y → X →S Y
bla X Y = _∘S spectrification-unit X

spectrification-UMP : (X : Prespectrum) (Y : Prespectrum) (Y-spectrum : isSpectrum Y) →
                    isEquiv (bla X Y)
spectrification-UMP = {!!}
