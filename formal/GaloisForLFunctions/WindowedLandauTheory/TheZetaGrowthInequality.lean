import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.TheTranslateAverageOfTheBalance
import GaloisForLFunctions.WindowedLandauTheory.NonvanishingRightOfTheCriticalLine

/-!
# The growth inequality for `G_ζ` and the Riemann hypothesis from growth data

Fix a host (`H`, admissible Frobenius data, `ℓ`), points `a_t` with `|a_t/b - x| ≤ 1` (`t ∈ TT`) and
weight families `w_{u₀,j}` (`j < m`) that are `∈ [b, b+η+1]` on thick classes and `≤ 2b'` on thin split
classes. If the translate-averaged inert excess is at most `Err`, the thin scales are small and the
nonzero sign characters have square-root values at `x`, then (`zeta_growth_inequality`)

```text
|TT| m ( (|T₂|/2|H|) b (G_ζ(x) - 3x^{1/2+ε} - signCost) - 2|Φ|(x+1)bθ - 14|Φ|(x+1)(η+1) ) ≤ Err.
```

Each excess is the character side of the balance identity; thickening the weights costs the
Lipschitz term, the translate average leaves the sign signal, and the signal is `G_ζ(x)` up to the
three square-root terms.

With small costs, density `|T₂|/|H| ≥ x^{-ε}` and `Err ≤ x^{1/2+Cε} |TT| m b |T₂|/2|H|`
(`ZetaGrowthData`) this gives `G_ζ(x) ≤ 9 x^{1/2+max(1,C)ε}`, and growth data at all large `x` for
all small `ε` give the Riemann hypothesis (`riemannHypothesis_of_zetaGrowthData`).
-/

open Finset

namespace WindowedLandauTheory

noncomputable section

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The thin part of a thickened balance at the translate `u₀`. -/
def thinPart (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ) (T₂ : Finset H) (A b : ℝ)
    (t u₀ : H) (w : SignPair × H → ℝ) : ℂ :=
  (1 / ((splitSet H).card : ℂ)) * ∑ g ∈ (nonsplitSet H).filter
    (fun g => ¬IsThick T₂ u₀ (partnerClass t g)), ∑ ψ : AddChar (SignPair × H) ℂ,
      starRingEnd ℂ (ψ g) * ((thickened T₂ b u₀ w (partnerClass t g) : ℂ) *
        classCesaro D ℓ ψ (A / thickened T₂ b u₀ w (partnerClass t g)))

/-- **One point, all translates.** The translate-averaged inert excess at `A` is at least the
thick signal minus the thin and Lipschitz costs. -/
theorem average_inertExcess_ge (D : FrobeniusData H) (hD : D.Admissible)
    (ℓ : AddChar (SignPair × H) ℂ → ℂ) {N : ℕ} {T₂ : Finset H} {A : ℝ} (t : H)
    (w : H → SignPair × H → ℝ) {x ε b b' η X' θ CL : ℝ} (hx : 3 ≤ x) (hb : 0 < b)
    (hη : 0 ≤ η) (hX' : 0 < X') (hbX : b' * X' ≤ x * b) (hθ : 0 ≤ θ) (hCL : 0 ≤ CL)
    (hA : |A / b - x| ≤ 1) (hwpos : ∀ u₀ ρ, IsSplit ρ → 0 < w u₀ ρ)
    (hwthick : ∀ u₀ ρ, IsThick T₂ u₀ ρ → b ≤ w u₀ ρ ∧ w u₀ ρ ≤ b + η + 1)
    (hwthin : ∀ u₀ ρ, IsSplit ρ → ¬IsThick T₂ u₀ ρ → w u₀ ρ ≤ 2 * b')
    (hN : ∀ u₀ ρ, IsSplit ρ → A / w u₀ ρ ≤ N)
    (hThin : ∀ (ψ : AddChar (SignPair × H) ℂ) (y : ℝ), X' / 3 ≤ y →
      ‖classCesaro D ℓ ψ y‖ ≤ y * θ)
    (hVal : ∀ ψ : AddChar (SignPair × H) ℂ, IsSignCharacter ψ → ψ ≠ 0 →
      ‖classCesaro D ℓ ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ℓ ψ‖ ≤ CL * Real.log x) :
    (T₂.card : ℝ) / (2 * Fintype.card H) * b *
        (zetaCesaroFunctional x - 3 * x ^ ((1 : ℝ) / 2 + ε) - signCost x CL) -
      2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) -
      2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1)) ≤
    (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H,
      (inertTotal D N A t (w u₀) - (mainTotal ℓ A (w u₀)).re) := by
  have hAx : (x - 1) * b ≤ A ∧ A ≤ (x + 1) * b := by
    obtain ⟨h1, h2⟩ := abs_le.1 hA
    constructor
    · have : x - 1 ≤ A / b := by linarith
      rwa [le_div_iff₀ hb] at this
    · have : A / b ≤ x + 1 := by linarith
      rwa [div_le_iff₀ hb] at this
  have hA0 : 0 < A := lt_of_lt_of_le (by nlinarith) hAx.1
  have hHpos : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  set K₁ := 2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1)) with hK₁
  set K₂ := 2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) with hK₂
  -- the balance identity, translate by translate
  have hbal : ∀ u₀ : H, inertTotal D N A t (w u₀) - (mainTotal ℓ A (w u₀)).re =
      (balanceTotal D ℓ A t (w u₀)).re := by
    intro u₀
    have h := congrArg Complex.re (inertTotal_sub_mainTotal D hD ℓ t hA0 (hwpos u₀) (hN u₀))
    rwa [Complex.sub_re, Complex.ofReal_re] at h
  -- thickening the weights
  have hthk : ∀ u₀ : H, (balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re - K₁ ≤
      (balanceTotal D ℓ A t (w u₀)).re := by
    intro u₀
    have h := abs_re_balanceTotal_sub_le D ℓ T₂ t u₀ hA0 hAx.2 hb hη (by linarith) (hwthick u₀)
    linarith [(abs_le.1 h).1]
  -- the translate average of the thickened balances
  have havg : (1 / (Fintype.card H : ℂ)) * ∑ u₀ : H,
      balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀)) =
      (T₂.card : ℂ) / (2 * (Fintype.card H : ℂ)) * (b : ℂ) * signSignal D ℓ (A / b) +
      (1 / (Fintype.card H : ℂ)) * ∑ u₀ : H, thinPart D ℓ T₂ A b t u₀ (w u₀) :=
    average_balanceTotal_thickened D ℓ T₂ A b t w
  have hthin : ‖(1 / (Fintype.card H : ℂ)) * ∑ u₀ : H, thinPart D ℓ T₂ A b t u₀ (w u₀)‖ ≤ K₂ := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have h : ‖∑ u₀ : H, thinPart D ℓ T₂ A b t u₀ (w u₀)‖ ≤ (Fintype.card H : ℝ) * K₂ := by
      refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ K₂ fun u₀ _ =>
        norm_thinPart_le D ℓ T₂ t u₀ hx hb hX' hbX hθ hAx (hwpos u₀) (hwthin u₀) hThin).trans ?_)
      rw [nsmul_eq_mul, Finset.card_univ]
    calc 1 / (Fintype.card H : ℝ) * ‖∑ u₀ : H, thinPart D ℓ T₂ A b t u₀ (w u₀)‖
        ≤ 1 / (Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * K₂) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = K₂ := by field_simp
  have hsig := re_signSignal_ge D ℓ hx hCL (y := A / b) hA hVal
  have hre : ((1 / (Fintype.card H : ℂ)) * ∑ u₀ : H,
      balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re =
      (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H,
        (balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re := by
    rw [show (1 / (Fintype.card H : ℂ)) = ((1 / (Fintype.card H : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, Complex.re_sum]
  have hcoef : ((T₂.card : ℂ) / (2 * (Fintype.card H : ℂ)) * (b : ℂ) * signSignal D ℓ (A / b)).re =
      (T₂.card : ℝ) / (2 * Fintype.card H) * b * (signSignal D ℓ (A / b)).re := by
    rw [show (T₂.card : ℂ) / (2 * (Fintype.card H : ℂ)) * (b : ℂ) =
      (((T₂.card : ℝ) / (2 * Fintype.card H) * b : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  have hc0 : 0 ≤ (T₂.card : ℝ) / (2 * Fintype.card H) * b := by positivity
  have hthick_avg : (T₂.card : ℝ) / (2 * Fintype.card H) * b *
      (zetaCesaroFunctional x - 3 * x ^ ((1 : ℝ) / 2 + ε) - signCost x CL) - K₂ ≤
      (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H,
        (balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re := by
    rw [← hre, havg, Complex.add_re, hcoef]
    have h1 := mul_le_mul_of_nonneg_left hsig hc0
    have h2 := (abs_le.1 ((Complex.abs_re_le_norm _).trans hthin)).1
    linarith
  have hsum : (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H,
      (balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re - K₁ ≤
      (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H,
        (inertTotal D N A t (w u₀) - (mainTotal ℓ A (w u₀)).re) := by
    have h1 : ∑ u₀ : H, ((balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re - K₁) ≤
        ∑ u₀ : H, (inertTotal D N A t (w u₀) - (mainTotal ℓ A (w u₀)).re) :=
      Finset.sum_le_sum fun u₀ _ => by rw [hbal u₀]; exact hthk u₀
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 1 / (Fintype.card H : ℝ) by positivity)
    have e : 1 / (Fintype.card H : ℝ) * (∑ u₀ : H,
        (balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re - (Fintype.card H : ℝ) * K₁) =
        1 / (Fintype.card H : ℝ) * ∑ u₀ : H,
          (balanceTotal D ℓ A t (thickened T₂ b u₀ (w u₀))).re - K₁ := by
      field_simp
    linarith
  linarith

/-- **The growth inequality for `G_ζ`.** -/
theorem zeta_growth_inequality (D : FrobeniusData H) (hD : D.Admissible)
    (ℓ : AddChar (SignPair × H) ℂ → ℂ) {N m : ℕ} {TT T₂ : Finset H} {a : H → ℝ}
    {w : H → Fin m → SignPair × H → ℝ} {x ε b b' η X' θ CL Err : ℝ} (hx : 3 ≤ x) (hb : 0 < b)
    (hη : 0 ≤ η) (hX' : 0 < X') (hbX : b' * X' ≤ x * b) (hθ : 0 ≤ θ) (hCL : 0 ≤ CL)
    (ha : ∀ t ∈ TT, |a t / b - x| ≤ 1) (hwpos : ∀ u₀ j ρ, IsSplit ρ → 0 < w u₀ j ρ)
    (hwthick : ∀ u₀ j ρ, IsThick T₂ u₀ ρ → b ≤ w u₀ j ρ ∧ w u₀ j ρ ≤ b + η + 1)
    (hwthin : ∀ u₀ j ρ, IsSplit ρ → ¬IsThick T₂ u₀ ρ → w u₀ j ρ ≤ 2 * b')
    (hN : ∀ u₀ j t ρ, t ∈ TT → IsSplit ρ → a t / w u₀ j ρ ≤ N)
    (hTop : (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H, ∑ t ∈ TT, ∑ j : Fin m,
      (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) ≤ Err)
    (hThin : ∀ (ψ : AddChar (SignPair × H) ℂ) (y : ℝ), X' / 3 ≤ y →
      ‖classCesaro D ℓ ψ y‖ ≤ y * θ)
    (hVal : ∀ ψ : AddChar (SignPair × H) ℂ, IsSignCharacter ψ → ψ ≠ 0 →
      ‖classCesaro D ℓ ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ℓ ψ‖ ≤ CL * Real.log x) :
    (TT.card : ℝ) * m * ((T₂.card : ℝ) / (2 * Fintype.card H) * b *
        (zetaCesaroFunctional x - 3 * x ^ ((1 : ℝ) / 2 + ε) - signCost x CL) -
      2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) -
      2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1))) ≤ Err := by
  set L := (T₂.card : ℝ) / (2 * Fintype.card H) * b *
      (zetaCesaroFunctional x - 3 * x ^ ((1 : ℝ) / 2 + ε) - signCost x CL) -
    2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) -
    2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1)) with hL
  have hreorder : (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H, ∑ t ∈ TT, ∑ j : Fin m,
      (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) =
      ∑ t ∈ TT, ∑ j : Fin m, (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H,
        (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
  have hpt : ∀ t ∈ TT, ∀ j : Fin m, L ≤ (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H,
      (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) := by
    intro t ht j
    exact average_inertExcess_ge D hD ℓ t (fun u₀ => w u₀ j) hx hb hη hX' hbX hθ hCL (ha t ht)
      (fun u₀ => hwpos u₀ j) (fun u₀ => hwthick u₀ j) (fun u₀ => hwthin u₀ j)
      (fun u₀ ρ hρ => hN u₀ j t ρ ht hρ) hThin hVal
  have hlow : ∑ t ∈ TT, ∑ _j : Fin m, L ≤ ∑ t ∈ TT, ∑ j : Fin m, (1 / (Fintype.card H : ℝ)) *
      ∑ u₀ : H, (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) :=
    Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => hpt t ht j
  have hconst : ∑ _t ∈ TT, ∑ _j : Fin m, L = (TT.card : ℝ) * m * L := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hconst, ← hreorder] at hlow
  exact hlow.trans hTop

end

/-- **Growth data for `G_ζ` at `x`**: a host and weights satisfying the hypotheses of the growth
inequality, with small costs, thick density `≥ x^{-ε}` and inert excess
`Err ≤ x^{1/2+Cε} |TT| m b |T₂|/(2|H|)`. -/
def ZetaGrowthData (C ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H) (D : FrobeniusData H)
    (ℓ : AddChar (SignPair × H) ℂ → ℂ) (N m : ℕ) (TT T₂ : Finset H) (a : H → ℝ)
    (w : H → Fin m → SignPair × H → ℝ) (b b' η X' θ CL Err : ℝ),
    D.Admissible ∧ 3 ≤ x ∧ 0 < b ∧ 0 ≤ η ∧ 0 < X' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ 0 ≤ CL ∧
    (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
    (∀ u₀ j ρ, IsSplit ρ → 0 < w u₀ j ρ) ∧
    (∀ u₀ j ρ, IsThick T₂ u₀ ρ → b ≤ w u₀ j ρ ∧ w u₀ j ρ ≤ b + η + 1) ∧
    (∀ u₀ j ρ, IsSplit ρ → ¬IsThick T₂ u₀ ρ → w u₀ j ρ ≤ 2 * b') ∧
    (∀ u₀ j t ρ, t ∈ TT → IsSplit ρ → a t / w u₀ j ρ ≤ N) ∧
    (1 / (Fintype.card H : ℝ)) * ∑ u₀ : H, ∑ t ∈ TT, ∑ j : Fin m,
      (inertTotal D N (a t) t (w u₀ j) - (mainTotal ℓ (a t) (w u₀ j)).re) ≤ Err ∧
    (∀ (ψ : AddChar (SignPair × H) ℂ) (y : ℝ), X' / 3 ≤ y → ‖classCesaro D ℓ ψ y‖ ≤ y * θ) ∧
    (∀ ψ : AddChar (SignPair × H) ℂ, IsSignCharacter ψ → ψ ≠ 0 →
      ‖classCesaro D ℓ ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ℓ ψ‖ ≤ CL * Real.log x) ∧
    signCost x CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧
    2 * ((splitSet H).card : ℝ) * ((x + 1) * θ) ≤ 1 / x ∧
    14 * ((splitSet H).card : ℝ) * ((x + 1) * (η + 1)) ≤ b / x ∧
    TT.Nonempty ∧ 0 < m ∧
    x ^ (-ε) ≤ (T₂.card : ℝ) / Fintype.card H ∧
    Err ≤ x ^ ((1 : ℝ) / 2 + C * ε) * ((TT.card : ℝ) * m * b *
      ((T₂.card : ℝ) / (2 * Fintype.card H)))

/-- **Growth data bound `G_ζ(x)`.** -/
theorem zetaCesaroFunctional_le_of_zetaGrowthData {C ε x : ℝ} (hε : 0 < ε)
    (h : ZetaGrowthData C ε x) :
    zetaCesaroFunctional x ≤ 9 * x ^ ((1 : ℝ) / 2 + max 1 C * ε) := by
  obtain ⟨H, _, _, _, D, ℓ, N, m, TT, T₂, a, w, b, b', η, X', θ, CL, Err, hD, hx, hb, hη, hX', hbX,
    hθ, hCL, ha, hwpos, hwthick, hwthin, hN, hTop, hThin, hVal, hcost, hthinc, hthickc, hTT, hm,
    hdens, hErr⟩ := h
  have hg := zeta_growth_inequality D hD ℓ hx hb hη hX' hbX hθ hCL ha hwpos hwthick hwthin hN hTop
    hThin hVal
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set X := x ^ ((1 : ℝ) / 2 + ε) with hXdef
  set Y := x ^ ((1 : ℝ) / 2 + C * ε) with hYdef
  set c := (T₂.card : ℝ) / (2 * Fintype.card H) with hcdef
  have hHpos : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hdpos : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hx0 _
  have hc : x ^ (-ε) / 2 ≤ c := by
    rw [hcdef, div_mul_eq_div_div_swap]
    have := div_le_div_of_nonneg_right hdens (show (0 : ℝ) ≤ 2 by norm_num)
    linarith [show (T₂.card : ℝ) / Fintype.card H / 2 = (T₂.card : ℝ) / 2 / Fintype.card H by ring]
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hc
  have hTTpos : (0 : ℝ) < TT.card := by exact_mod_cast hTT.card_pos
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set Q := (TT.card : ℝ) * m * b with hQ
  have hQpos : 0 < Q := by positivity
  -- costs
  have hK₂ : 2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) ≤ b / x := by
    have := mul_le_mul_of_nonneg_left hthinc hb.le
    calc 2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) =
        b * (2 * ((splitSet H).card : ℝ) * ((x + 1) * θ)) := by ring
      _ ≤ b * (1 / x) := this
      _ = b / x := by ring
  have hK₁ : 2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1)) ≤ b / x := by
    calc 2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1)) =
        14 * ((splitSet H).card : ℝ) * ((x + 1) * (η + 1)) := by ring
      _ ≤ b / x := hthickc
  have hsig : c * b * (zetaCesaroFunctional x - 4 * X) ≤
      c * b * (zetaCesaroFunctional x - 3 * X - signCost x CL) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- divide by |TT| m b
  have hmain : Q * (c * (zetaCesaroFunctional x - 4 * X) - 2 / x) ≤ Q * (Y * c) := by
    have h1 : (TT.card : ℝ) * m * (c * b * (zetaCesaroFunctional x - 4 * X) - b / x - b / x) ≤
        (TT.card : ℝ) * m * (c * b * (zetaCesaroFunctional x - 3 * X - signCost x CL) -
          2 * ((splitSet H).card : ℝ) * ((x + 1) * b * θ) -
          2 * ((splitSet H).card : ℝ) * (7 * (x + 1) * (η + 1))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 := h1.trans (hg.trans hErr)
    have e1 : (TT.card : ℝ) * m * (c * b * (zetaCesaroFunctional x - 4 * X) - b / x - b / x) =
        Q * (c * (zetaCesaroFunctional x - 4 * X) - 2 / x) := by
      rw [hQ]
      ring
    have e2 : Y * (Q * c) = Q * (Y * c) := by ring
    rw [e1] at h2
    rw [hQ] at e2 ⊢
    linarith
  have h3 := le_of_mul_le_mul_left hmain hQpos
  -- 2/(x c) ≤ 4 X
  have h4 : 2 / x ≤ c * (4 * X) := by
    have hxe : x ^ ε / x ≤ X := by
      rw [hXdef, div_eq_mul_inv, ← Real.rpow_neg_one x, ← Real.rpow_add hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hprod : x ^ (-ε) * x ^ ε = 1 := by
      rw [← Real.rpow_add hx0]
      simp
    have hcx : 1 / 2 ≤ c * x ^ ε := by
      have h := mul_le_mul_of_nonneg_right hc (Real.rpow_pos_of_pos hx0 ε).le
      have e : x ^ (-ε) / 2 * x ^ ε = 1 / 2 := by rw [div_mul_eq_mul_div, hprod]
      linarith
    calc 2 / x = 2 * (1 * (1 / x)) := by ring
      _ ≤ 2 * (2 * (c * x ^ ε) * (1 / x)) := by
          have h := mul_le_mul_of_nonneg_right (show 1 ≤ 2 * (c * x ^ ε) by linarith)
            (show 0 ≤ 1 / x by positivity)
          linarith
      _ = c * (4 * (x ^ ε / x)) := by ring
      _ ≤ c * (4 * X) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
  have h5 : c * (zetaCesaroFunctional x - 8 * X - Y) ≤ 0 := by
    have e : c * (zetaCesaroFunctional x - 8 * X - Y) =
        c * (zetaCesaroFunctional x - 4 * X) - c * (4 * X) - Y * c := by ring
    rw [e]
    linarith
  have h6 : zetaCesaroFunctional x ≤ 8 * X + Y := by
    by_contra hc'
    push Not at hc'
    have : 0 < c * (zetaCesaroFunctional x - 8 * X - Y) := mul_pos hcpos (by linarith)
    linarith
  have hK : 1 ≤ max 1 C := le_max_left _ _
  have hXle : X ≤ x ^ ((1 : ℝ) / 2 + max 1 C * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [le_mul_of_one_le_left hε.le hK])
  have hYle : Y ≤ x ^ ((1 : ℝ) / 2 + max 1 C * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1
      (by linarith [mul_le_mul_of_nonneg_right (le_max_right 1 C) hε.le])
  linarith

/-- **The Riemann hypothesis from growth data.** If for some `C` and every small `ε > 0` growth
data for `G_ζ` exist at every large `x`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_zetaGrowthData {C ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ZetaGrowthData C ε x) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_zeta_windows
  intro ε' hε'
  set K := max 1 C with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  set ε := min (ε' / K) (ε₁ / 2) with hεdef
  have hε0 : 0 < ε := lt_min (div_pos hε' (by linarith)) (by linarith)
  have hεε₁ : ε < ε₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hKε : K * ε ≤ ε' := by
    have := min_le_left (ε' / K) (ε₁ / 2)
    calc K * ε ≤ K * (ε' / K) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = ε' := by field_simp
  obtain ⟨x₀, hx₀⟩ := h ε hε0 hεε₁
  refine ⟨1, one_pos, 9, fun Y₀ => ⟨max Y₀ (max x₀ 3), le_max_left _ _, fun y hy => ?_⟩⟩
  have hyY : max Y₀ (max x₀ 3) ≤ y := hy.1
  have hyx₀ : x₀ ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hyY
  have hy3 : 3 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hyY
  have hb := zetaCesaroFunctional_le_of_zetaGrowthData hε0 (hx₀ y hyx₀)
  have hle : y ^ ((1 : ℝ) / 2 + K * ε) ≤ y ^ ((1 : ℝ) / 2 + ε') :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc zetaCesaroFunctional y ≤ 9 * y ^ ((1 : ℝ) / 2 + K * ε) := hb
    _ ≤ 9 * y ^ ((1 : ℝ) / 2 + ε') := by linarith

end

end WindowedLandauTheory
