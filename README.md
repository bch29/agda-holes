Holes
-----

## Notice ##

This work is part of my undergraduate dissertation project, which is ongoing. As such I can't currently accept pull requests, although bug reports and feature requests are welcome.

## Introduction ##

Holes is an Agda library that uses reflection to make writing equational reasoning proofs easier.

It can turn proofs like this:

```agda
*-distrib-+₁ : ∀ a b c → a * (b + c) ≡ a * b + a * c
*-distrib-+₁ zero b c = refl
*-distrib-+₁ (suc a) b c =
    b + c + a * (b + c)          ≡⟨ cong (λ h → b + c + h) (*-distrib-+₁ a b c) ⟩
    (b + c) + (a * b + a * c)    ≡⟨ sym (+-assoc (b + c) (a * b) (a * c)) ⟩
    ((b + c) + a * b) + a * c    ≡⟨ cong (λ h → h + a * c) (+-assoc b c (a * b)) ⟩
    (b + (c + a * b)) + a * c    ≡⟨ cong (λ h → (b + h) + a * c) (+-comm c (a * b)) ⟩
    (b + (a * b + c)) + a * c    ≡⟨ cong (λ h → h + a * c) (sym (+-assoc b (a * b) c)) ⟩
    ((b + a * b) + c) + a * c    ≡⟨ +-assoc (b + a * b) c (a * c) ⟩
    (b + a * b) + (c + a * c)
  ∎
```

... into proofs like this:

```agda
*-distrib-+ : ∀ a b c → a * (b + c) ≡ a * b + a * c
*-distrib-+ zero b c = refl
*-distrib-+ (suc a) b c =
  b + c + ⌞ a * (b + c) ⌟         ≡⟨ cong! (*-distrib-+ a b c) ⟩
  ⌞ (b + c) + (a * b + a * c) ⌟   ≡⟨ cong! (+-assoc (b + c) (a * b) (a * c)) ⟩
  ⌞ (b + c) + a * b ⌟ + a * c     ≡⟨ cong! (+-assoc b c (a * b)) ⟩
  (b + ⌞ c + a * b ⌟) + a * c     ≡⟨ cong! (+-comm c (a * b)) ⟩
  ⌞ b + (a * b + c) ⌟ + a * c     ≡⟨ cong! (+-assoc b (a * b) c) ⟩
  ⌞ ((b + a * b) + c) + a * c ⌟   ≡⟨ cong! (+-assoc (b + a * b) c (a * c)) ⟩
  (b + a * b) + (c + a * c)
  ∎
```

It works best with propositional equality, but there is also (work in progress) support for equalities that do not have general congruence.

## Dependencies ##

This library is tested with Agda version 2.5.2. It does not work with earlier versions of Agda.

It doesn't require any other Agda libraries (although the examples require the standard library).

## Installation ##

To install from a bash shell:

```bash
# Clone this repository #
git clone https://github.com/bch29/agda-holes

# Add the .agda-lib file to your global Agda libraries file #
echo "$(pwd)/agda-holes/src/holes.agda-lib" >> ~/.agda/libraries
```

## Usage ##

For examples, see the `examples/` directory of this repository.

Assuming your project has a ".agda-lib" file, add `holes` to the `depend` section (see `examples/holes-examples.agda-lib`).

### In General ###

This library works by inspecting type information to discover congruence paths for you, and automatically produce the necessary boilerplate. You need to use two things to interact with it: the `⌞_⌟` function and the `cong!` macro.

`⌞_⌟` is just the identity function, defined like so:

```agda
⌞_⌟ : ∀ {a} {A : Set a} → A → A
⌞ x ⌟ = x
```

The `cong!` macro can be used to complete a goal whose type is the right equivalence relation, with instances of `⌞_⌟` in the _left hand side_ of the type. For example:

```agda
myLemma : ∀ a b c → a + ⌞ b + c ⌟ ≡ a + (c + b)
myLemma a b c = cong! (+-comm b c)
```

Notice that `⌞_⌟` is wrapped around the part of the expression that we want to rewrite in the left hand side. The goal type to the right of the `=` is `a + ⌞ b + c ⌟ ≡ a + (c + b)`, which is equivalent to `a + (b + c) ≡ a + (c + b)`. The argument to `cong!` is just the proof needed to perform the rewriting, assuming we are inside the 'hole'. The rest is done by `cong!`.

This works particularly well in conjunction with equational reasoning, as demonstrated above.

### Propositional Equality ###

Using this library with propositional equality is easy. Just import:

```agda
-- From the standard library
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- From the Holes library
open import Holes.Term using (⌞_⌟)
open import Holes.Cong.Propositional
```

then write your proofs with holes as in the introductory example.

### General Congruence ###

It's not much harder to use this library with a different equivalence relation that supports a general `cong` theorem. That is, if your relation is written `_≈_`, and you have a function with the type:

```agda
cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≈ y → f x ≈ f y
```

The names of the arguments don't matter, but the order and number of explicit arguments _does_ matter. So for example it won't work if the type is one of these instead

```agda
cong₁ : ∀ {a b} {A : Set a} {B : Set b} {x y} → x ≈ y → (f : A → B) → f x ≈ f y
cong₂ : ∀ {a b} (A : Set a) (B : Set b) (f : A → B) {x y} → x ≈ y → f x ≈ f y
```

You must also have available a `sym` function with the following type:

```agda
sym : ∀ {a} {A : Set a} {x y : A} → x ≈ y → y ≈ x
```

This function must have exactly _one_ explicit argument.

Now, to use the library, you must do the following (where `cong` and `sym` are the functions described above):

```agda
open import Holes.Term using (⌞_⌟)
open import Holes.Cong.General (quote-term _≈_) (quote-term cong) (quote-term sym)
```

Write your proofs as usual, but making use of the `cong!` macro.

### Limited Congruence ###

In order to use this library for proofs about equalities that _don't_ have a general `cong` theorem available, you have to provide it with a database of specific congruences that it can use.

This is currently a work in progress. It works but is somewhat cumbersome. See the file `src/Holes/Test/Limited.agda` for a few examples of usage.
