module Monads where

open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

{-
TODO:
  * use levels in definitions to account for more general sizes
  * set precedence of _>>=_ and _>=>_ w/ respect to ∘ in order to remove a few parantheses
  * define `a ● p ● z = ext (λ {x} → cong a (cong-app p (z x)))` to simplify proofs
-}

postulate
  ext : ∀ {A B : Set} {f g : A → B}
    → (∀ {x : A} → f x ≡ g x)
    → f ≡ g

record MathMon (M : Set → Set) : Set₁ where
  field
    fmap : {A B : Set} → (A → B) → M A → M B
    unit : {A : Set} → A → M A
    mult : {A : Set} → M (M A) → M A
    -- functoriality
    fun-composition : ∀ {A B C : Set} {f : B → C} {g : A → B} → fmap (f ∘ g) ≡ (fmap f) ∘ (fmap g)
    fun-identity : ∀ {A : Set} → fmap {A} id ≡ id
    -- naturality
    nat-unit : ∀ {A B : Set} {f : A → B} → (fmap f) ∘ unit ≡ unit ∘ f
    nat-comp : ∀ {A B : Set} {f : A → B} → (fmap f) ∘ mult ≡ mult ∘ fmap (fmap f)
    -- consistency
    con-unit₁ : ∀ {A : Set} → mult {A} ∘ fmap unit ≡ id
    con-unit₂ : ∀ {A : Set} → mult {A} ∘ unit ≡ id
    con-mult  : ∀ {A : Set} → mult {A} ∘ fmap mult ≡ mult ∘ mult

record ProgMon (M : Set → Set) : Set₁ where
  field
    unit : {A : Set} → A -> M A
    _>>=_ : {A B : Set} → M A → (A → M B) -> M B
    -- monadicity
    unitˡ : ∀ {A B : Set} {x : A} {f : A → M B}
      → (unit x) >>= f ≡ f x
    unitʳ : ∀ {A : Set} {m : M A}
      → m >>= unit ≡ m
    assoc : ∀ {A B C : Set} {m : M A} {f : A → M B} {g : B → M C}
      → (m >>= f) >>= g ≡ m >>= λ{x → f x >>= g}

record FunkMon (M : Set → Set) : Set₁ where
  field
    unit : {A : Set} → A -> M A
    _>=>_ : {A B C : Set} → (A → M B) → (B → M C) → (A → M C)
    -- monadicity
    unitˡ : ∀ {A C : Set} {g : A → M C}
      → unit >=> g ≡ g
    unitʳ : ∀ {A B : Set} {f : A → M B}
      → f >=> unit ≡ f
    assoc : ∀ {A B C D : Set} {f : A → M B} {g : B → M C} {h : C → M D}
      → (f >=> g) >=> h ≡ f >=> (g >=> h)

record KleisliMon (M : Set → Set) : Set₁ where
  field
    _⋆ : {A B : Set} → (A → M B) → (M A → M B)
    unit : {A : Set} → A -> M A
    _>=>_ : {A B C : Set} → (A → M B) → (B → M C) → (A → M C)
    -- monadicity
    unitˡ : ∀ {A C : Set} {g : A → M C}
      → unit >=> g ≡ g
    unitʳ : ∀ {A B : Set} {f : A → M B}
      → f >=> unit ≡ f
    assoc : ∀ {A B C D : Set} {f : A → M B} {g : B → M C} {h : C → M D}
      → (f >=> g) >=> h ≡ f >=> (g >=> h)
    -- extension operator
    -- extension axioms
    ext₁ : ∀ {A : Set}
      → (unit {A} ⋆) ≡ id
    ext₂ : ∀ {A B : Set} {f : A → M B}
      → (f ⋆) ∘ unit ≡ f
    ext₃ : ∀ {A B C : Set} {f : A → M B} {g : B → M C}
      → ((g ⋆) ∘ f)⋆ ≡ (g ⋆) ∘ (f ⋆)
    -- extension consistency with fish
    ext₄ : ∀ {A B C : Set} {f : A → M B} {g : B → M C}
      → f >=> g ≡ (g ⋆) ∘ f
    -- so, the extension operator is actually
    -- (g ⋆) ≡ id >=> g
    ext₁′ : ∀ {A : Set}
      → (id >=> unit {A}) ≡ id -- follows from unitʳ
    ext₂′ : ∀ {A B : Set} {f : A → M B}
      → (id >=> f) ∘ unit ≡ f -- follows from nothing
    ext₃′ : ∀ {A B C : Set} {f : A → M B} {g : B → M C}
      → id >=> ((id >=> g) ∘ f) ≡ (id >=> g) ∘ (id >=> f)


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
    ; assoc = λ {_} {_} {_} {m} {f} {g} →
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
        fmap (f ∘ g)                                       ≡⟨⟩
        (λ x → fmap (f ∘ g) x)                             ≡⟨⟩
        (λ x → x >>= (unit ∘ (f ∘ g)))                     ≡⟨⟩
        (λ x → x >>= (λ y → (unit ∘ f ∘ g) y))             ≡⟨ ext (λ {x} → cong (_>>=_ x) (ext (sym unitˡ))) ⟩
        (λ x → x >>= (λ y → (unit ∘ g) y >>= (unit ∘ f)))  ≡⟨ ext (sym assoc) ⟩
        (λ x → ((x >>= (unit ∘ g)) >>= (unit ∘ f)))        ≡⟨⟩
        (λ x → (fmap f) (x >>= (unit ∘ g)))                ≡⟨⟩
        (λ x → (fmap f ∘ fmap g) x)                        ≡⟨⟩
        fmap f ∘ fmap g
      ∎
    ; fun-identity =
      begin
        fmap id                    ≡⟨⟩
        (λ x → (fmap id) x)        ≡⟨⟩
        (λ x → x >>= (unit ∘ id))  ≡⟨⟩
        (λ x → x >>= unit)         ≡⟨⟩
        (λ x → (id x) >>= unit)    ≡⟨ ext unitʳ ⟩
        (λ x → id x)               ≡⟨⟩
        id
      ∎
    ; nat-unit = λ {_} {_} {f} →
      begin
        fmap f ∘ unit                  ≡⟨⟩
        (λ x → (fmap f ∘ unit) x)      ≡⟨⟩
        (λ x → unit x >>= (unit ∘ f))  ≡⟨ ext unitˡ ⟩
        (λ x → (unit ∘ f) x)           ≡⟨⟩
        unit ∘ f
      ∎
    ; nat-comp = λ {_} {_} {f} →
      begin
        fmap f ∘ mult                                       ≡⟨⟩
        (λ x → (fmap f ∘ mult) x)                           ≡⟨⟩
        (λ x → (mult x) >>= (unit ∘ f))                     ≡⟨⟩
        (λ x → (x >>= id) >>= (unit ∘ f))                   ≡⟨ ext assoc ⟩
        (λ x → x >>= (λ y → id y >>= (unit ∘ f)))           ≡⟨⟩
        (λ x → x >>= (λ y → y >>= (unit ∘ f)))              ≡⟨⟩
        (λ x → x >>= (λ y → fmap f y))                      ≡⟨⟩
        (λ x → x >>= (λ y → (id ∘ (fmap f)) y))             ≡⟨ ext (λ {x} → cong (_>>=_ x) (ext (sym unitˡ))) ⟩
        (λ x → x >>= (λ y → ((unit ∘ (fmap f)) y) >>= id))  ≡⟨ ext (sym assoc) ⟩
        (λ x → (x >>= (unit ∘ (fmap f))) >>= id)            ≡⟨⟩
        (λ x → (fmap (fmap f) x) >>= id)                    ≡⟨⟩
        (λ x → (mult ∘ fmap (fmap f)) x)                    ≡⟨⟩
        mult ∘ fmap (fmap f)
      ∎
    ; con-unit₁ =
      begin
        mult ∘ fmap unit                            ≡⟨⟩
        (λ x → (mult ∘ fmap unit) x)                ≡⟨⟩
        (λ x → fmap unit x >>= id)                  ≡⟨⟩
        (λ x → (x >>= (unit ∘ unit)) >>= id)        ≡⟨ ext assoc ⟩
        (λ x → x >>= (λ y → unit (unit y) >>= id))  ≡⟨ ext (λ {x} → cong (_>>=_ x) (ext unitˡ)) ⟩
        (λ x → x >>= (λ y → unit y))                ≡⟨⟩
        (λ x → x >>= unit)                          ≡⟨ ext unitʳ ⟩
        (λ x → id x)                                ≡⟨⟩
        id
      ∎
    ; con-unit₂ =
      begin
        mult ∘ unit              ≡⟨⟩
        (λ x → (mult ∘ unit) x)  ≡⟨⟩
        (λ x → unit x >>= id)    ≡⟨ ext unitˡ ⟩
        (λ x → id x)             ≡⟨⟩
        id
      ∎
    ; con-mult =
      begin
        mult ∘ fmap mult                              ≡⟨⟩
        (λ x → (mult ∘ fmap mult) x)                  ≡⟨⟩
        (λ x → (fmap mult x) >>= id)                  ≡⟨⟩
        (λ x → (x >>= (unit ∘ mult)) >>= id)          ≡⟨ ext assoc ⟩
        (λ x → x >>= (λ y → (unit ∘ mult) y >>= id))  ≡⟨ ext (λ {x} → cong (_>>=_ x) (ext unitˡ)) ⟩
        (λ x → x >>= (λ y → mult y))                  ≡⟨⟩
        (λ x → x >>= (λ y → y >>= id))                ≡⟨ ext (sym assoc) ⟩
        (λ x → (x >>= id) >>= id)                     ≡⟨⟩
        (λ x → mult (x >>= id))                       ≡⟨⟩
        (λ x → (mult ∘ mult) x)                       ≡⟨⟩
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
    ; unitˡ = λ {_} {_} {g} →
            begin
              unit >=> g            ≡⟨⟩
              (λ x → unit x >>= g)  ≡⟨ ext unitˡ ⟩
              (λ x → g x)           ≡⟨⟩
              g
            ∎
    ; unitʳ = λ {_} {_} {f} →
            begin
              f >=> unit            ≡⟨⟩
              (λ x → f x >>= unit)  ≡⟨ ext unitʳ ⟩
              (λ x → f x)           ≡⟨⟩
              f
            ∎
    ; assoc = λ {_} {_} {_} {_} {f} {g} {h} →
            begin
              (f >=> g) >=> h                    ≡⟨⟩
              (λ x → (f x >>= g) >>= h)          ≡⟨ ext assoc ⟩
              (λ x → f x >>= (λ y → g y >>= h))  ≡⟨⟩
              f >=> (g >=> h)
            ∎
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
    ; unitˡ = λ {_} {_} {x} {f} →
            begin
              (unit x) >>= f       ≡⟨⟩
              (id >=> f) (unit x)  ≡⟨ sym magic ⟩
              (unit >=> f) (x)     ≡⟨ cong-app unitˡ x ⟩
              f x
            ∎
    ; unitʳ = λ {_} {m} →
            begin
              m >>= unit       ≡⟨⟩
              (id >=> unit) m  ≡⟨ cong-app unitʳ m ⟩
              m
            ∎
    ; assoc = λ {_} {_} {_} {m} {f} {g} →
            begin
              (m >>= f) >>= g                      ≡⟨⟩
              (id >=> g) (m >>= f)                 ≡⟨⟩
              (id >=> g) ((id >=> f) m)            ≡⟨⟩
              ((id >=> g) ∘ (id >=> f)) m          ≡⟨ sym magic ⟩
              ((id >=> f) >=> g) m                 ≡⟨ cong-app assoc m ⟩
              (id >=> (f >=> g)) m                 ≡⟨⟩
              (id >=> (λ{x → (f >=> g) x})) m      ≡⟨ cong-app (cong (_>=>_ id) (ext magic)) m ⟩
              (id >=> (λ{x → (id >=> g)(f x)})) m  ≡⟨⟩
              (id >=> (λ{x → f x >>= g})) m        ≡⟨⟩
              m >>= (λ{x → f x >>= g})
            ∎
    }
  where
    _>>=_ : {A B : Set} → M A → (A → M B) → M B
    _>>=_ ma f = (id >=> f) ma
    -- _>>=_ ma f = ((λ _ → ma) >=> f) () -- NOTE: usually one sees this in Haskell
    postulate
      -- TODO: I'm both unable to prove this and unable to find another way
      magic : {A B C : Set} → {f : A → M B} → {g : B → M C} → ∀ {x : A}
        → (f >=> g) x ≡ ((id >=> g) ∘ f) x


MathMon→FunkMon : {M : Set → Set} → MathMon M → FunkMon M
MathMon→FunkMon {M}
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
    ; _>=>_ = _>=>_
    ; unitˡ = λ {_} {_} {g} →
            begin
              unit >=> g              ≡⟨⟩
              mult ∘ (fmap g) ∘ unit  ≡⟨ ext (λ {x} → cong mult (cong-app nat-unit x)) ⟩
              mult ∘ unit ∘ g         ≡⟨ ext (λ {x} → cong-app con-unit₂ (g x)) ⟩
              id ∘ g                  ≡⟨⟩
              g
            ∎
    ; unitʳ = λ {_} {_} {f} →
            begin
              f >=> unit              ≡⟨⟩
              mult ∘ (fmap unit) ∘ f  ≡⟨ ext (λ {x} → cong-app con-unit₁ (f x)) ⟩
              id ∘ f                  ≡⟨⟩
              f
            ∎
    ; assoc = λ {_} {_} {_} {_} {f} {g} {h} →
            begin
              (f >=> g) >=> h                                      ≡⟨⟩
              (mult ∘ (fmap g) ∘ f) >=> h                          ≡⟨⟩
              mult ∘ (fmap h) ∘ mult ∘ (fmap g) ∘ f                ≡⟨ ext (λ {x} → cong mult (cong-app nat-comp (((fmap g) ∘ f) x))) ⟩
              mult ∘ mult ∘ (fmap (fmap h)) ∘ (fmap g) ∘ f         ≡⟨ ext (λ {x} → cong-app (sym con-mult) (((fmap (fmap h)) ∘ (fmap g) ∘ f) x) ) ⟩
              mult ∘ (fmap mult) ∘ (fmap (fmap h)) ∘ (fmap g) ∘ f  ≡⟨ ext (λ {x} → cong mult (cong-app (sym fun-composition) (((fmap g) ∘ f) x))) ⟩
              mult ∘ (fmap (mult ∘ (fmap h))) ∘ (fmap g) ∘ f       ≡⟨ ext (λ {x} → cong mult (cong-app (sym fun-composition) (f x))) ⟩
              mult ∘ (fmap (mult ∘ (fmap h) ∘ g)) ∘ f              ≡⟨⟩
              f >=> (mult ∘ (fmap h) ∘ g)                          ≡⟨⟩
              f >=> (g >=> h)
            ∎
    }
  where
    _>=>_ : {A B C : Set} → (A → M B) → (B → M C) → A → M C
    _>=>_ f g x = mult (fmap g (f x))

FunkMon→MathMon : {M : Set → Set} → FunkMon M → MathMon M
FunkMon→MathMon {M}
  record
    { unit = unit
    ; _>=>_ = _>=>_
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
        fmap (f ∘ g)                               ≡⟨⟩
        id >=> (unit ∘ (f ∘ g))                    ≡⟨⟩
        id >=> ((unit ∘ f) ∘ g)                    ≡⟨ {!!} ⟩ -- ext2
        id >=> (((id >=> (unit ∘ f)) ∘ unit) ∘ g)  ≡⟨⟩
        id >=> ((id >=> (unit ∘ f)) ∘ (unit ∘ g))  ≡⟨ {!!} ⟩ -- ext3
        (id >=> (unit ∘ f)) ∘ (id >=> (unit ∘ g))  ≡⟨⟩
        fmap f ∘ fmap g
      ∎
    ; fun-identity =
      begin
        fmap id             ≡⟨⟩
        id >=> (unit ∘ id)  ≡⟨⟩
        id >=> unit         ≡⟨ unitʳ ⟩
        id
      ∎
    ; nat-unit = λ {_} {_} {f} →
      begin
        fmap f ∘ unit               ≡⟨⟩
        (id >=> (unit ∘ f)) ∘ unit  ≡⟨ {!!} ⟩ -- ext2
        unit ∘ f
      ∎
    ; nat-comp = λ {_} {_} {f} →
      begin
        fmap f ∘ mult                                        ≡⟨⟩
        (id >=> (unit ∘ f)) ∘ (id >=> id)                    ≡⟨ {!!} ⟩
        mult ∘ fmap (fmap f)
      ∎
    ; con-unit₁ =
      begin
        mult ∘ fmap unit                      ≡⟨⟩
        (id >=> id) ∘ (id >=> (unit ∘ unit))  ≡⟨ {!!} ⟩
        ((id >=> (unit ∘ unit)) >=> id)       ≡⟨ assoc ⟩
        (id >=> ((unit ∘ unit) >=> id))       ≡⟨ {!!} ⟩
        (id >=> ((unit >=> id) ∘ unit))       ≡⟨ {!unitˡ!} ⟩
        (id >=> (id ∘ unit))                  ≡⟨ {!!} ⟩
        (id >=> id) ∘ ((id >=> unit) ∘ unit)  ≡⟨ {!!} ⟩
        (id >=> id) ∘ (id ∘ unit)             ≡⟨⟩
        (id >=> id) ∘ unit                    ≡⟨ sym magic ⟩
        (unit >=> id)                         ≡⟨ unitˡ ⟩
        id
      ∎
    ; con-unit₂ =
      begin
        mult ∘ unit         ≡⟨⟩
        -- (id* ∘ id) ∘ unit
        -- id* ∘ unit
        -- id
        (id >=> id) ∘ unit  ≡⟨ {!!} ⟩ -- ext2
        id
      ∎
    ; con-mult =
      begin
        mult ∘ fmap mult                             ≡⟨⟩
        -- (id* ∘ id) ∘ (unit ∘ (id* ∘ id))* ∘ id
        -- id* ∘ (unit ∘ id*)*
        (id >=> id) ∘ (id >=> (unit ∘ (id >=> id)))  ≡⟨ {!!} ⟩ -- ext3
        (id >=> ((id >=> id) ∘ unit ∘ (id >=> id)))  ≡⟨ {!!} ⟩ -- ext2
        (id >=> (id ∘ (id >=> id)))                  ≡⟨⟩
        (id >=> ((id >=> id) ∘ id))                  ≡⟨ {!!} ⟩ -- ext3
        (id >=> id) ∘ (id >=> id)                    ≡⟨⟩
        -- (id* ∘ id) ∘ (id* ∘ id)
        mult ∘ mult
        -- → (id >=> unit {A}) ≡ id
        -- → (id >=> f) ∘ unit ≡ f
        -- → id >=> ((id >=> g) ∘ f) ≡ (id >=> g) ∘ (id >=> f)
      ∎
    }
  where
    fmap : {A B : Set} → (A → B) → M A → M B
    fmap f x = (id >=> (unit ∘ f)) x
    mult : {A : Set} → M (M A) → M A
    mult x = (id >=> id) x
    -- NOTE: these are the usual definitions but they have an ambiguous domain
    -- fmap f x = ((const x) >=> (unit ∘ f)) _
    -- mult x = ((const x) >=> id) _
    postulate
      -- TODO: I'm both unable to prove this and unable to find another way
      magic : {A B C : Set} → {f : A → M B} → {g : B → M C}
        → (f >=> g) ≡ (id >=> g) ∘ f
      boyah : {A B C : Set} → {f : A → B} → {g : B → C}
        → (unit ∘ f) >=> (unit ∘ g) ≡ unit ∘ (g ∘ f)



