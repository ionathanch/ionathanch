<h1> <img src="https://ionathan.ch/favicon.png" width="30px"/><sup><sub><sup>closure ahead</sup></sub></sup><img src="https://ionathan.ch/favicon.png" width="30px"/> </h1>

Frankly everything you need to know about me should already be in the sidebar. Here, have some Agda instead:

```agda
{-# OPTIONS --sized-types #-}
open import Size
open import Data.Empty

data _<_ : Size → Size → Set where
  lt : ∀ s → (r : Size< s) → r < s

data Acc (s : Size) : Set where
  acc : (∀ {r} → r < s → Acc r) → Acc s

false : ⊥
false = ¬wf∞ (wf ∞) where
  wf : ∀ s → Acc s
  wf s = acc (λ {(lt .s r) → wf r})
  ¬wf∞ : Acc ∞ → ⊥
  ¬wf∞ (acc p) = ¬wf∞ (p (lt ∞ ∞))
```

<!-- <b>ion·a·thanch</b> [jɑːnəθənt͡ʃ] <i>abbr.</i> <b>ion·chy</b> [jɑːnt͡ʃi] <i>n.</i> The cybrespatial identity of the being known as <b>Jonathan Chan</b>. -->
