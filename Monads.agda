module Monads where

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

record MathMon (M : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → M A → M B
    unit : {A : Set} → A → M A
    mult : {A : Set} → M (M A) → M A
    -- functoriality
    fun-composition : {A B C : Set} → {f : B → C} → {g : A → B} → fmap (f ∘ g) ≡ (fmap f) ∘ (fmap g)
    fun-identity : {A : Set} → fmap {A} id ≡ id
    -- naturality
    nat-unit : {A B : Set} → {f : A → B} → (fmap f) ∘ unit ≡ unit ∘ f
    nat-comp : {A B : Set} → {f : A → B} → (fmap f) ∘ mult ≡ mult ∘ fmap (fmap f)
    -- consistency
    con-unit₁ : {A : Set} → mult {A} ∘ fmap unit ≡ id
    con-unit₂ : {A : Set} → mult {A} ∘ unit ≡ id
    con-mult  : {A : Set} → mult {A} ∘ fmap mult ≡ mult ∘ mult

record ProgMon (M : Set → Set) : Set₁ where
  field
    unit : {A : Set} → A -> M A
    _>>=_ : {A B : Set} → M A → (A → M B) -> M B
    -- monadicity
    unitˡ : {A B : Set} → {x : A} → {f : A → M B}
      → (unit x) >>= f ≡ f x
    unitʳ : {A : Set} → {m : M A}
      → m >>= unit ≡ m
    assoc : {A B C : Set} → {x : A} → {f : A → M B} → {g : B → M C} → {m : M A}
      → (m >>= f) >>= g ≡ m >>= λ{x → f x >>= g}

record FunkMon (M : Set → Set) : Set₁ where
  field
    unit : {A : Set} → A -> M A
    _>=>_ : {A B C : Set} → (A → M B) → (B → M C) → (A → M C)
    -- monadicity
    unitˡ : {A C : Set} → {g : A → M C}
      → unit >=> g ≡ g
    unitʳ : {A B : Set} → {f : A → M B}
      → f >=> unit ≡ f
    assoc : {A B C D : Set} → {f : A → M B} → {g : B → M C} → {h : C → M D}
      → (f >=> g) >=> h ≡ f >=> (g >=> h)


MathMon→ProgMon : {M : Set → Set} → MathMon M → ProgMon M
MathMon→ProgMon {M}
  record
    { fmap = fmap
    ; unit = unit
    ; mult = mult
    ; fun-composition = fun-composition
    ; fun-identity = _
    ; nat-unit = nat-unit
    ; nat-comp = nat-comp
    ; con-unit₁ = con-unit₁
    ; con-unit₂ = con-unit₂
    ; con-mult = con-mult
    }
  =
  record
    { unit = unit
    ; _>>=_ = _>>=_
    ; unitˡ = λ {_} {_} {x} {f} →
            begin
              (unit x) >>= f          ≡⟨⟩
              mult (fmap f (unit x))  ≡⟨ cong mult (cong-app nat-unit x) ⟩
              mult (unit (f x))       ≡⟨⟩
              (mult ∘ unit) (f x)     ≡⟨ cong-app con-unit₂ (f x) ⟩
              id (f x)                ≡⟨⟩
              f x
            ∎
    ; unitʳ = λ {_} {m} →
            begin
              m >>= unit            ≡⟨⟩
              mult (fmap unit m)    ≡⟨⟩
              (mult ∘ fmap unit) m  ≡⟨ cong-app con-unit₁ m ⟩
              id m                  ≡⟨⟩
              m
            ∎
    ; assoc = λ {_} {_} {_} {_} {f} {g} {m} →
            begin
              ((m >>= f) >>= g)                         ≡⟨⟩
              (mult (fmap f m)) >>= g                   ≡⟨⟩
              mult (fmap g (mult (fmap f m)))           ≡⟨⟩
              (mult ∘ fmap g ∘ mult ∘ fmap f) m         ≡⟨ cong mult (cong-app nat-comp (fmap f m)) ⟩
              (mult ∘ mult ∘ fmap (fmap g) ∘ fmap f) m  ≡⟨ cong (mult ∘ mult) (cong-app (sym fun-composition) m) ⟩
              (mult ∘ mult ∘ fmap (fmap g ∘ f)) m       ≡⟨ cong-app (cong (λ{h → h ∘ fmap (fmap g ∘ f)}) (sym con-mult)) m ⟩
              (mult ∘ fmap mult ∘ fmap (fmap g ∘ f)) m  ≡⟨ cong mult (cong-app (sym fun-composition) m) ⟩
              (mult ∘ fmap (mult ∘ fmap g ∘ f)) m       ≡⟨⟩
              m >>= (mult ∘ fmap g ∘ f)                 ≡⟨⟩
              m >>= (λ{ x → (mult ∘ fmap g ∘ f) x })    ≡⟨⟩
              m >>= (λ{ x → f x >>= g })
            ∎
    }
    where
      _>>=_ : {A B : Set} → M A → (A → M B) -> M B
      _>>=_ x f = mult (fmap f x)

ProgMon→MathMon : {M : Set → Set} → ProgMon M → MathMon M
ProgMon→MathMon {M}
  record
    { unit = unit
    ; _>>=_ = _>>=_
    ; unitˡ = unitˡ
    ; unitʳ = unitʳ
    ; assoc = assoc
    }
  =
  record
    { fmap = fmap
    ; unit = unit
    ; mult = mult
    ; fun-composition = λ {_} {_} {_} {f} {g} →
      begin
        fmap (f ∘ g)
      ≡⟨ {!!} ⟩
        fmap f ∘ fmap g
      ∎
    ; fun-identity =
      begin
        fmap id
      ≡⟨ {!!} ⟩
        id
      ∎
    ; nat-unit = λ {_} {_} {f} →
      begin
        fmap f ∘ unit
      ≡⟨ {!!} ⟩
        unit ∘ f
      ∎
    ; nat-comp = λ {_} {_} {f} →
      begin
        fmap f ∘ mult
      ≡⟨ {!!} ⟩
        mult ∘ fmap (fmap f)
      ∎
    ; con-unit₁ =
      begin
        mult ∘ fmap unit
      ≡⟨ {!!} ⟩
        id
      ∎
    ; con-unit₂ =
      begin
        mult ∘ unit
      ≡⟨ {!!} ⟩
        id
      ∎
    ; con-mult =
      begin
        mult ∘ fmap mult
      ≡⟨ {!!} ⟩
        mult ∘ mult
      ∎
    }
  where
    fmap : {A B : Set} → (A → B) → M A → M B
    fmap f x = x >>= (unit ∘ f)
    mult : {A : Set} → M (M A) → M A
    mult x = x >>= id

ProgMon→FunkMon : {M : Set → Set} → ProgMon M → FunkMon M
ProgMon→FunkMon {M}
  record
    { unit = unit
    ; _>>=_ = _>>=_
    ; unitˡ = unitˡ
    ; unitʳ = unitʳ
    ; assoc = assoc
    }
  =
  record
    { unit = unit
    ; _>=>_ = _>=>_
    ; unitˡ = {!!}
    ; unitʳ = {!!}
    ; assoc = {!!}
    }
  where
    _>=>_ : {A B C : Set} → (A → M B) → (B → M C) → A → M C
    _>=>_ m n x = m x >>= n

FunkMon→ProgMon : {M : Set → Set} → FunkMon M → ProgMon M
FunkMon→ProgMon {M}
  record
    { unit = unit
    ; _>=>_ = _>=>_
    ; unitˡ = unitˡ
    ; unitʳ = unitʳ
    ; assoc = assoc
    }
  =
  record
    { unit = unit
    ; _>>=_ = _>>=_
    ; unitˡ = {!!}
    ; unitʳ = {!!}
    ; assoc = {!!}
    }
  where
    _>>=_ : {A B : Set} → M A → (A → M B) → M B
    _>>=_ x f = (id >=> f) x -- TODO: check this, I made it up

