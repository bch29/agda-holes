module Holes.Prelude where

open import Agda.Primitive public
  using (Level; _⊔_; lzero; lsuc)
open import Agda.Builtin.List public
  using (List; _∷_; [])
open import Agda.Builtin.Unit public
  using (⊤; tt)
open import Agda.Builtin.Bool public
  using (Bool; true; false)
open import Agda.Builtin.Nat public
  using (zero; suc; _+_; _*_)
  renaming (Nat to ℕ; _==_ to _=ℕ?_)
open import Agda.Builtin.Reflection public
open import Agda.Builtin.String public
open import Agda.Builtin.Char public

infixr 4 _,_
infixr 2 _×_
infixr 9 _∘_
infixl 1 _⟨_⟩_
infixr 0 _$_
infix 0 case_of_

--------------------------------------------------------------------------------
--  Datatypes
--------------------------------------------------------------------------------

data Brad b: Set where
  zero : b
  suc : b -> b
-- Maybe this makes sense, who even knows

data Maybe {a} (A : Set a) : Set a where
  just : (x : A) → Maybe A
  nothing : Maybe A

record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_

  field
    proj₁ : A
    proj₂ : B

open _×_ public

--------------------------------------------------------------------------------
--  Combinators
--------------------------------------------------------------------------------

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

flip : ∀ {a b c} {A : Set a}{B : Set b}{C : Set c} → (A → B → C) → B → A → C
flip f y x = f x y

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

_⟨_⟩_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

curry : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} → (A × B → C) → A → B → C
curry f x y = f (x , y)

uncurry : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} → (A → B → C) → A × B → C
uncurry f (x , y) = f x y

case_of_ : ∀ {a b}{A : Set a}{B : Set b} → A → (A → B) → B
case x of f = f x

--------------------------------------------------------------------------------
--  Boolean operations
--------------------------------------------------------------------------------

_∨_ : Bool → Bool → Bool
false ∨ false = false
_ ∨ _ = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _ = false

not : Bool → Bool
not true = false
not false = true

if_then_else_ : ∀ {a} {A : Set a} → (b : Bool) → A → A → A
if true then x else y = x
if false then x else y = y

--------------------------------------------------------------------------------
--  List operations
--------------------------------------------------------------------------------

singleton : ∀ {a}{A : Set a} → A → List A
singleton x = x ∷ []

map : ∀ {a b}{A : Set a}{B : Set b} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

length : ∀ {a}{A : Set a} → List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

zip : ∀ {a b}{A : Set a}{B : Set b} → List A → List B → List (A × B)
zip [] _ = []
zip _ [] = []
zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

unzip : ∀ {a b}{A : Set a}{B : Set b} → List (A × B) → List A × List B
unzip [] = [] , []
unzip ((x , y) ∷ xys) with unzip xys
... | xs , ys = x ∷ xs , y ∷ ys

infixr 6 _++_

_++_ : ∀ {a}{A : Set a} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

concatMap : ∀ {a b}{A : Set a}{B : Set b} → (A → List B) → List A → List B
concatMap f [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

concat : ∀ {a}{A : Set a} → List (List A) → List A
concat = concatMap id

intersperse : ∀ {a}{A : Set a} → A → List A → List A
intersperse e [] = []
intersperse e (x ∷ []) = x ∷ []
intersperse e (x ∷ y ∷ xs) = x ∷ e ∷ intersperse e (y ∷ xs)

intercalate : ∀ {a}{A : Set a} → List A → List (List A) → List A
intercalate e = concat ∘ intersperse e

--------------------------------------------------------------------------------
--  Nat operations
--------------------------------------------------------------------------------

-- A comparison view. Taken from "View from the left" (McBride/McKinna) via the
-- Agda standard library

data Ordering : ℕ → ℕ → Set where
  less    : ∀ m k → Ordering m (suc (m + k))
  equal   : ∀ m   → Ordering m m
  greater : ∀ m k → Ordering (suc (m + k)) m

compare : ∀ m n → Ordering m n
compare zero    zero    = equal   zero
compare (suc m) zero    = greater zero m
compare zero    (suc n) = less    zero n
compare (suc m) (suc n) with compare m n
compare (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k

_<?_ : ℕ → ℕ → Bool
x <? y with compare x y
... | Ordering.less .x _ = true
... | _ = false

--------------------------------------------------------------------------------
--  Typeclasses
--------------------------------------------------------------------------------

record RawMonoid {f} (M : Set f) : Set f where
  field
    _<>_ : M → M → M
    mempty : M

open RawMonoid {{...}} public

instance
  listMonoid : ∀ {a} {A : Set a} → RawMonoid (List A)
  RawMonoid._<>_ listMonoid = _++_
  RawMonoid.mempty listMonoid = []

record RawMonad {f} (M : Set f → Set f) : Set (lsuc f) where
  infixl 1 _>>=_ _>>_ _>=>_ _>>=²_
  infixr 1 _=<<_ _<=<_
  infixl 4 _<$>_
  infixl 4 _⊛_

  field
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    return : ∀ {A} → A → M A

  _>>_ : ∀ {A B} → M A → M B → M B
  x >> y = x >>= λ _ → y

  _>=>_ : ∀ {ℓ}{A : Set ℓ}{B C} → (A → M B) → (B → M C) → A → M C
  f >=> g = λ x → f x >>= g

  _=<<_ : ∀ {A B} → (A → M B) → M A → M B
  f =<< x = x >>= f

  _<=<_ : ∀ {ℓ}{A : Set ℓ}{B C} → (B → M C) → (A → M B) → A → M C
  g <=< f = f >=> g

  _>>=²_ : {A B C : Set f} → M (A × B) → (A → B → M C) → M C
  x >>=² f = x >>= uncurry f

  join : ∀ {A} → M (M A) → M A
  join m = m >>= id

  fmap : ∀ {A B} → (A → B) → M A → M B
  fmap f x = x >>= return ∘ f

  _<$>_ = fmap

  _⊛_ : ∀ {A B} → M (A → B) → M A → M B
  f ⊛ x = f >>= flip fmap x

open RawMonad {{...}} public

record RawTraversable {t} (T : Set t → Set t) : Set (lsuc t) where
  field
    traverse : {M : Set t → Set t} {{monad : RawMonad M}} {A B : Set t} → (A → M B) → T A → M (T B)

  sequence : {M : Set t → Set t} {{monad : RawMonad M}} {A : Set t} → T (M A) → M (T A)
  sequence = traverse id

open RawTraversable {{...}} public

traverse- : {T M : Set → Set} {{traversable : RawTraversable T}} {{monad : RawMonad M}} {A B : Set} → (A → M B) → T A → M ⊤
traverse- f xs = traverse f xs >> return tt

instance
  traversableList : ∀ {t} → RawTraversable (List {t})
  traverse {{traversableList}} f [] = return []
  traverse {{traversableList}} f (x ∷ xs) = _∷_ <$> f x ⊛ traverse f xs

--------------------------------------------------------------------------------
--  Propositional Equality
--------------------------------------------------------------------------------

module PropEq where
  open import Agda.Builtin.Equality using (_≡_; refl) public

  sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl eq = eq

  subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y} → x ≡ y → P x → P y
  subst P refl p = p

  cong : ∀ {a b} {A : Set a} {B : Set b}
           (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

--------------------------------------------------------------------------------
--  Monads and useful instances
--------------------------------------------------------------------------------

infixl 1 _>>=′_

-- _>>=_ in `RawMonad` only works on a single level, while bindTC is more
-- level-polymorphic, which we will sometimes need.
_>>=′_ = bindTC

data Result {e r} (E : Set e) (R : Set r) : Set (e ⊔ r) where
  ok : (x : R) → Result E R
  err : (e : E) → Result E R

Maybe→Result : ∀ {e r} {E : Set e} {R : Set r} → E → Maybe R → Result E R
Maybe→Result e (just x) = ok x
Maybe→Result e nothing = err e

instance
  List-Monad : ∀ {a} → RawMonad (List {a})
  RawMonad._>>=_ List-Monad = flip concatMap
  RawMonad.return List-Monad x = x ∷ []

  TC-Monad : ∀ {a} → RawMonad {a} TC
  TC-Monad = record
    { return = returnTC
    ; _>>=_ = bindTC
    }

  Maybe-Monad : ∀ {a} → RawMonad {a} Maybe
  (RawMonad._>>=_ Maybe-Monad) (just x) f = f x
  (RawMonad._>>=_ Maybe-Monad) nothing f = nothing
  RawMonad.return Maybe-Monad = just

  Result-Monad : ∀ {ℓ}{E : Set ℓ} → RawMonad {ℓ} (Result E)
  Result-Monad = record
    { return = ok
    ; _>>=_ = λ
      { (err e) _ → err e
      ; (ok x) f → f x
      }
    }

--------------------------------------------------------------------------------
--  RTC: A type checking monad with errors other than normal type errors
--------------------------------------------------------------------------------

record RTC {e r} (E : Set e) (R : Set r) : Set (e ⊔ r) where
  field
    tryRunRTC : TC (Result E R)

open RTC public

runRTC : ∀ {e r} {E : Set e} {R : Set r} → (E → TC R) → RTC E R → TC R
runRTC f x =
  tryRunRTC x >>=′
    λ { (err e) → f e
      ; (ok y) → return y
      }

module RTC′ {e} {E : Set e} where
  bind : ∀ {α β} {A : Set α}{B : Set β} → RTC E A → (A → RTC E B) → RTC E B
  tryRunRTC (bind x f) =
    tryRunRTC x >>=′
      λ { (err e) → return (err e)
        ; (ok y) → tryRunRTC (f y)
        }

instance
  RTC-monad : ∀ {ℓ} {E : Set ℓ} → RawMonad {ℓ} (RTC E)
  RTC-monad = record
    { return = λ x → record { tryRunRTC = return (return x) }
    ; _>>=_ = RTC′.bind
    }

catchRTC : ∀ {ℓ} {E : Set ℓ}{R : Set ℓ} → RTC E R → RTC E R → RTC E R
tryRunRTC (catchRTC rtc fallback) =
  tryRunRTC rtc ⟨ catchTC ⟩ tryRunRTC fallback

--------------------------------------------------------------------------------
--  MonadCatch and instances
--------------------------------------------------------------------------------

record MonadCatch {a e} (E : Set e) (M : Set a → Set a) : Set (lsuc a ⊔ e) where
  field
    catch : ∀ {A : Set a} → (E → M A) → M A → M A

open MonadCatch {{...}} public

instance
  Maybe-MonadCatch : ∀ {a} → MonadCatch {a} ⊤ Maybe
  Maybe-MonadCatch = record
    { catch = λ
      { f (just x) → just x
      ; f nothing → f tt
      }
    }

  Result-MonadCatch : ∀ {ℓ} {E : Set ℓ} → MonadCatch {ℓ} E (Result E)
  Result-MonadCatch = record
    { catch = λ
      { f (err e) → f e
      ; f (ok x) → ok x}
    }

  RTC-MonadCatch : ∀ {ℓ} {E : Set ℓ} → MonadCatch {ℓ} E (RTC E)
  RTC-MonadCatch = record
    { catch = λ f x → record
      { tryRunRTC = tryRunRTC x >>= λ
        { (err e) → tryRunRTC (f e)
        ; (ok y) → return (ok y)
        }
      }
    }

--------------------------------------------------------------------------------
--  MonadThrow and instances
--------------------------------------------------------------------------------

record MonadThrow {a e} (E : Set e) (M : Set a → Set a) : Set (lsuc a ⊔ e) where
  field
    {{monad}} : RawMonad M
    throw : ∀ {A : Set a} → E → M A

open MonadThrow {{...}} public

instance
  Maybe-MonadThrow : ∀ {a} → MonadThrow {a} ⊤ Maybe
  Maybe-MonadThrow = record { throw = λ _ → nothing }

  Result-MonadThrow : ∀ {ℓ} {E : Set ℓ} → MonadThrow {ℓ} E (Result E)
  Result-MonadThrow = record { throw = err }

  RTC-MonadThrow : ∀ {ℓ} {E : Set ℓ} → MonadThrow {ℓ} E (RTC E)
  RTC-MonadThrow = record { throw = λ e → record { tryRunRTC = return (err e) } }

  TC-MonadThrow : ∀ {ℓ} → MonadThrow {ℓ} (List ErrorPart) TC
  TC-MonadThrow = record { throw = typeError }

liftResult′ : ∀ {e ℓ} {E E′ : Set e} {M : Set ℓ → Set ℓ} {{monadThrow : MonadThrow E′ M}} {A : Set ℓ} → (E → E′) → Result E A → M A
liftResult′ _ (ok x) = return x
liftResult′ f (err e) = throw (f e)

liftResult : ∀ {e ℓ} {E : Set e} {M : Set ℓ → Set ℓ} {{monadThrow : MonadThrow E M}} {A : Set ℓ} → Result E A → M A
liftResult = liftResult′ id

liftMaybe : ∀ {e ℓ}{E : Set e} {M : Set ℓ → Set ℓ} {{monadThrow : MonadThrow E M}} {A : Set ℓ} → E → Maybe A → M A
liftMaybe error (just x) = return x
liftMaybe error nothing = throw error

--------------------------------------------------------------------------------
--  Choice and instances
--------------------------------------------------------------------------------

record Choice {a} (F : Set a → Set a) : Set (lsuc a) where
  field
    _<|>_ : ∀ {A} → F A → F A → F A

open Choice {{...}} public

instance
  Maybe-Choice : ∀ {a} → Choice {a} Maybe
  Maybe-Choice = record
    { _<|>_ = λ
      { (just x) _ → just x
      ; nothing (just y) → just y
      ; nothing nothing → nothing
      }
    }

  Result-Choice : ∀ {ℓ}{E : Set ℓ} → Choice {ℓ} (Result E)
  Result-Choice = record
    { _<|>_ = λ
      { (ok x) _ → ok x
      ; (err _) (ok y) → ok y
      ; (err e) (err _) → err e
      }
    }

--------------------------------------------------------------------------------
--  General utility methods
--------------------------------------------------------------------------------

successes : ∀ {ℓ e M} {E : Set e} {{monadCatch : MonadCatch E M}}{{monad : RawMonad M}} {A : Set ℓ} → List (M A) → M (List A)
successes  [] = return []
successes {{monadCatch}} {A = A} (x ∷ xs) =
  successes {{monadCatch}} xs >>= λ xs′ →
  catch {{monadCatch}} (λ _ → return xs′) (fmap (_∷ xs′) x)

mapErr : ∀ {e r}{R : Set r}{E E′ : Set e} → (E → E′) → Result E R → Result E′ R
mapErr f (ok x) = ok x
mapErr f (err e) = err (f e)

discardErr : ∀ {e r} {E : Set e}{R : Set r} → Result E R → Maybe R
discardErr (ok x) = just x
discardErr (err _) = nothing

result : ∀ {e r a}{E : Set e}{R : Set r}{A : Set a} → (E → A) → (R → A) → Result E R → A
result g f (ok x) = f x
result g f (err e) = g e

--------------------------------------------------------------------------------
--  Reflection utility methods
--------------------------------------------------------------------------------

infix 4 _=Name?_

_=Name?_ : Name → Name → Bool
_=Name?_ = primQNameEquality

basicArg : Term → Arg Term
basicArg = arg (arg-info visible relevant)

implicitArg : Term → Arg Term
implicitArg = arg (arg-info hidden relevant)

getArg : Arg Term → Term
getArg (arg _ x) = x

mapArg : ∀ {A B} → (A → B) → Arg A → Arg B
mapArg f (arg i x) = arg i (f x)

getArglist : Term → List (Arg Term)
getArglist (def _ args) = args
getArglist (con _ args) = args
getArglist (var _ args) = args
getArglist _ = []

instance
  traversableArg : RawTraversable Arg
  traverse {{traversableArg}} f (arg i x) = arg i <$> f x

liftTC : ∀ {e r} {E : Set e}{R : Set r} → TC R → RTC E R
tryRunRTC (liftTC x) = x >>=′ return ∘ ok

mapRtcErr : ∀ {ℓ}{R E E′ : Set ℓ} → (E → E′) → RTC E R → RTC E′ R
tryRunRTC (mapRtcErr f x) = tryRunRTC x >>= return ∘ mapErr f

runRtcOrTypeError : ∀ {ℓ} {E R : Set ℓ} → (E → List ErrorPart) → RTC E R → TC R
runRtcOrTypeError error = tryRunRTC >=> result (typeError ∘ error) return

typeError′ : ∀ {ℓ} {E R : Set ℓ} → List ErrorPart → RTC E R
typeError′ = liftTC ∘ typeError

--------------------------------------------------------------------------------
--  Macros that aid debugging
--------------------------------------------------------------------------------

runTCTy : ∀ ℓ → Type → Term → Term → TC ⊤
runTCTy ℓ at-type tc-term target =
  unquoteTC at-type >>=′ λ (ty : Set ℓ) →
  unquoteTC tc-term >>=′ λ (TCx : TC ty) →
  TCx >>=′
  quoteTC >>=′
  unify target

macro
  -- Quotes a term and expands to its reified syntax tree as a `Term`.

  quote-term : Term → Term → TC ⊤
  quote-term term target = quoteTC term >>= unify target

  -- Runs a TC operation and splices its result into the expression. Only works
  -- with operations in Set₀.

  runTCTy′ : ∀ {ℓ} → Type → Term → Term → TC ⊤
  runTCTy′ {ℓ} = runTCTy ℓ

  runTC : ∀ {ℓ} → Term → Term → TC ⊤
  runTC {ℓ} tc-term target =
    inferType target >>=′
    unquoteTC >>=′ λ (ty : Set ℓ) →
    unquoteTC tc-term >>=′ λ (TCx : TC ty) →
    TCx >>=′
    quoteTC >>=′
    unify target
