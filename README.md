<samp>
<p>
<kbd><ruby>｀<rt>～</rt></ruby></kbd>
<kbd><ruby>ㄅ<rt>1</rt></ruby></kbd>
<kbd><ruby>ㄉ<rt>2</rt></ruby></kbd>
<kbd><ruby>ˇ<rt>&hairsp;3&hairsp;</rt></ruby></kbd>
<kbd><ruby>ˋ<rt>&hairsp;4&hairsp;</rt></ruby></kbd>
<kbd><ruby>ㄓ<rt>5</rt></ruby></kbd>
<kbd><ruby>ˊ<rt>&hairsp;6&hairsp;</rt></ruby></kbd>
<kbd><ruby>˙<rt>&hairsp;7&hairsp;</rt></ruby></kbd>
<kbd><ruby>ㄚ<rt>8</rt></ruby></kbd>
<kbd><ruby>ㄞ<rt>9</rt></ruby></kbd>
<kbd><ruby>ㄢ<rt>0</rt></ruby></kbd>
<kbd><ruby>ㄦ<rt>－</rt></ruby></kbd>
<kbd><ruby>＝<rt>＋</rt></ruby></kbd>
<kbd><ruby>&nbsp;&nbsp;&nbsp;&nbsp;⌫<rt> </rt></ruby></kbd>
</p>
<p>
<kbd><ruby>⇥&nbsp;&nbsp;<rt></rt></ruby></kbd>
<kbd><ruby>ㄆ<rt>Q</rt></ruby></kbd>
<kbd><ruby>ㄊ<rt>W</rt></ruby></kbd>
<kbd><ruby>ㄍ<rt>E</rt></ruby></kbd>
<kbd><ruby>ㄐ<rt>R</rt></ruby></kbd>
<kbd><ruby>ㄔ<rt>T</rt></ruby></kbd>
<kbd><ruby>ㄗ<rt>Y</rt></ruby></kbd>
<kbd><ruby>ㄧ<rt>U</rt></ruby></kbd>
<kbd><ruby>ㄛ<rt>I</rt></ruby></kbd>
<kbd><ruby>ㄟ<rt>O</rt></ruby></kbd>
<kbd><ruby>ㄣ<rt>P</rt></ruby></kbd>
<kbd><ruby>「<rt>『</rt></ruby></kbd>
<kbd><ruby>」<rt>』</rt></ruby></kbd>
<kbd><ruby>、&nbsp;<rt>＼ </rt></ruby></kbd>
</p>
<p>
<kbd><ruby>⇪&nbsp;&nbsp;&nbsp;&nbsp;<rt></rt></ruby></kbd>
<kbd><ruby>ㄇ<rt>A</rt></ruby></kbd>
<kbd><ruby>ㄋ<rt>S</rt></ruby></kbd>
<kbd><ruby>ㄎ<rt>D</rt></ruby></kbd>
<kbd><ruby>ㄑ<rt>F</rt></ruby></kbd>
<kbd><ruby>ㄕ<rt>G</rt></ruby></kbd>
<kbd><ruby>ㄘ<rt>H</rt></ruby></kbd>
<kbd><ruby>ㄨ<rt>J</rt></ruby></kbd>
<kbd><ruby>ㄜ<rt>K</rt></ruby></kbd>
<kbd><ruby>ㄠ<rt>L</rt></ruby></kbd>
<kbd><ruby>ㄤ<rt>：</rt></ruby></kbd>
<kbd><ruby>＇<rt>＂</rt></ruby></kbd>
<kbd><ruby>&nbsp;&nbsp;&nbsp;&nbsp;↵<rt></rt></ruby></kbd>
</p>
<p>
<kbd><ruby>⇧&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<rt></rt></ruby></kbd>
<kbd><ruby>ㄈ<rt>Z</rt></ruby></kbd>
<kbd><ruby>ㄌ<rt>X</rt></ruby></kbd>
<kbd><ruby>ㄏ<rt>C</rt></ruby></kbd>
<kbd><ruby>ㄒ<rt>V</rt></ruby></kbd>
<kbd><ruby>ㄖ<rt>B</rt></ruby></kbd>
<kbd><ruby>ㄙ<rt>N</rt></ruby></kbd>
<kbd><ruby>ㄩ<rt>M</rt></ruby></kbd>
<kbd><ruby>ㄝ<rt>，</rt></ruby></kbd>
<kbd><ruby>ㄡ<rt>。</rt></ruby></kbd>
<kbd><ruby>ㄥ<rt>？</rt></ruby></kbd>
<kbd><ruby>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;⇧<rt>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</rt></ruby></kbd>
</p>
</samp>

<!--
<h1> <img src="https://ionathan.ch/favicon.png" width="30px"/><sup><sub><sup>closure ahead</sup></sub></sup><img src="https://ionathan.ch/favicon.png" width="30px"/> </h1>

```agda
{-# OPTIONS --sized-types #-}
open import Size
open import Data.Empty

data _<_ : Size → Size → Set where
  lt : ∀ s → (r : Size< s) → r < s

data Acc (s : Size) : Set where
  acc : (∀ {r} → r < s → Acc r) → Acc s

false₁ : ⊥
false₁ = ¬wf∞ (wf ∞) where
  wf : ∀ s → Acc s
  wf s = acc (λ {(lt .s r) → wf r})
  ¬wf∞ : Acc ∞ → ⊥
  ¬wf∞ (acc p) = ¬wf∞ (p (lt ∞ ∞))
```

```agda
data _≡_ : Size → Size → Set where
  refl : ∀ {i} → i ≡ i

data Up! : Size → Set where
  huh : ∀ {i} → Up! i
  up! : ∀ {i} → {j : Size< i} → Up! j → Up! i

false₂ : ⊥
false₂ = hup! ∞ refl huh where
  hup! : ∀ i → i ≡ (↑ ∞) → Up! i → ⊥
  hup! .∞ refl u = hup! ∞ refl (up! u)
```

<b>ion·a·thanch</b> [jɑːnəθənt͡ʃ] <i>abbr.</i> <b>ion·chy</b> [jɑːnt͡ʃi] <i>n.</i> The cybrespatial identity of the being known as <b>Jonathan Chan</b>.
-->
