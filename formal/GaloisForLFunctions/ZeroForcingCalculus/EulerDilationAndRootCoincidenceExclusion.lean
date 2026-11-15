import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane
import GaloisForLFunctions.ZeroForcingCalculus.TheClosedConfigurationsOfHalvingAndDoubling
import GaloisForLFunctions.ZeroForcingCalculus.WittMonomialsShiftedConvolutionsAndBrauerCancellation
import GaloisForLFunctions.ZeroForcingCalculus.ExpandingForcingLawsRulersAndTheRiemannHypothesis

/-!
# Euler Dilation Quotients, Root-Coincidence Exclusion, and Upgraded Squarefree Rulers

This module resolves the Euler-dilation zero-transport test (`ζ(2s)/ζ(s)` and `((s-1)ζ(s))^m / ζ(ks)`)
and combines it with the unconditional `20999 / 24000 = 7/8 - 1/24000` zero-free half-plane:

1. **Sub-`7/8` zero width and abscissa bounds**
   (`zetaZeroWidth_le_sub_three_eighths`, `zetaZeroAbscissa_le_sub_seven_eighths`,
   `zeta_offLine_quartet_sub_seven_eighths`):
   `zetaZeroWidth ≤ 8999 / 24000` (`= 3/8 - 1/24000`) and
   `zetaZeroAbscissa ≤ 20999 / 24000` (`= 7/8 - 1/24000`).

2. **Exact order classification of `ζ(2s) / ζ(s)`**
   (`eulerDoublingQuotient`, `meromorphicOrderAt_eulerDoublingQuotient`,
   `meromorphicOrderAt_eulerDoublingQuotient_of_half_lt_re`,
   `eulerDoublingQuotient_poleFree_iff_zetaZeroAbscissa_le`):
   On `Re s > 1/2` (`s ≠ 1`), `Re(2s) > 1` makes `ζ(2s)` analytic and nonzero, so
   `ord_s (ζ(2s)/ζ(s)) = - ord_s ζ`: denominator zeros at `ρ` (`Re ρ > 1/2`) never cancel, and
   pole-freeness of `ζ(2s)/ζ(s)` on `{Re s > β, s ≠ 1}` (`β ≥ 1/2`) is equivalent to
   `zetaZeroAbscissa ≤ β`.

3. **Root-coincidence abscissa lower bound and unconditional `k ≥ 7` exclusion**
   (`abscissa_ge_of_zeta_zero_div_nat`, `riemannZeta_div_nat_ne_zero_of_seven_le`,
   `riemannZeta_nat_mul_ne_zero_of_seven_le`, `dilatedPowerQuotient_neg_order_at_div_of_seven_le`):
   If `k ≥ 1`, `0 < Re ρ`, and `ζ(ρ) = ζ(ρ/k) = 0`, functional reflection at `1 - ρ/k` forces
   `k / (k + 1) ≤ zetaZeroAbscissa`. Because `zetaZeroAbscissa ≤ 20999 / 24000 < 7 / 8 ≤ k / (k + 1)`
   for every `k ≥ 7`, no nontrivial zero `ρ` of `ζ` satisfies `ζ(ρ / k) = 0` (or `ζ(k ρ) = 0`) for
   any `k ≥ 7`, and every nontrivial zero `ρ` produces an uncancelled pole of
   `((s - 1) ζ(s))^m / ζ(k s)` at `s = ρ / k` for every `k ≥ 7` and `m : ℕ`.

4. **Upgraded `[1/2, 27001/48000)` squarefree ruler, Ramanujan margin, and `(1/2, 20999/24000]`
   covering criterion**
   (`squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le_sub`,
   `isRuler_squarefreePowerQuotient_sub`,
   `ramanujan_shift_margin_zeta_zero_ge_sub`,
   `riemannHypothesis_of_covering_levers_sub_seven_eighths`):
   Widens the unconditional squarefree pole-abscissa ruler from `[1/2, 9/16)` to
   `[1/2, 27001 / 48000)` (`= [1/2, 9/16 + 1/48000)`), raises the Ramanujan shift margin to
   `27001 / 48000`, and reduces lever-cover criteria for `RiemannHypothesis` from `(1/2, 7/8]` to
   `(1/2, 20999 / 24000]`.
-/

noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology
open GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

namespace GaloisForLFunctions.ZeroForcingCalculus

/-! ## 1. Sub-`7/8` zero width, zero abscissa, and off-line quartet bounds -/

/-- The `20999 / 24000` zero-free half-plane bounds the symmetric zero width by
`8999 / 24000 = 3 / 8 - 1 / 24000`. -/
theorem zetaZeroWidth_le_sub_three_eighths :
    SquareRootThreshold.zetaZeroWidth ≤ 8999 / 24000 := by
  refine (SquareRootThreshold.zetaZeroWidth_le_iff_re_le
    (by norm_num : (0 : ℝ) ≤ 8999 / 24000)).2 ?_
  intro ρ hρ
  obtain ⟨hz, hpos, -⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
  have hstrip :=
    MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip hpos hz
  linarith only [hstrip.2]

/-- Unconditionally, the zero abscissa of `riemannZeta` satisfies
`zetaZeroAbscissa ≤ 20999 / 24000 = 7 / 8 - 1 / 24000`. -/
theorem zetaZeroAbscissa_le_sub_seven_eighths :
    RHTower.zetaZeroAbscissa ≤ 20999 / 24000 := by
  have h := (isRuler_zetaZeroAbscissa (8999 / 24000) (Set.mem_Ici.2 (by norm_num))).1
    zetaZeroWidth_le_sub_three_eighths
  linarith only [h]

/-- Strengthened off-line quartet theorem: every zero `ρ` of `ζ` strictly right of `1/2` lies in
`(1/2, 20999 / 24000]` with nonzero imaginary part and four distinct quartet points of equal order. -/
theorem zeta_offLine_quartet_sub_seven_eighths {ρ : ℂ} (hre : 1 / 2 < ρ.re)
    (hz : riemannZeta ρ = 0) :
    ρ.re ≤ 20999 / 24000 ∧ ρ.im ≠ 0 ∧ (zeroQuartet ρ).card = 4 ∧
      ∀ z ∈ zeroQuartet ρ,
        0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0 ∧
          analyticOrderAt riemannZeta z = analyticOrderAt riemannZeta ρ ∧
          meromorphicOrderAt riemannZeta z = meromorphicOrderAt riemannZeta ρ := by
  obtain ⟨_, him, hcard, hq⟩ := zeta_offLine_quartet hre hz
  have hsub : ρ.re ≤ 20999 / 24000 :=
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip
      (by linarith) hz).2
  exact ⟨hsub, him, hcard, hq⟩

/-! ## 2. Exact classification of the Euler doubling quotient `ζ(2s) / ζ(s)` -/

/-- The Euler doubling quotient `ζ(2s) / ζ(s) = ∏_p (1 + p^{-s})⁻¹` (`Re s > 1`). -/
def eulerDoublingQuotient (s : ℂ) : ℂ :=
  riemannZeta (2 * s) / riemannZeta s

/-- Global meromorphic order of `ζ(2s) / ζ(s)`: at every `s ∈ ℂ`,
`ord_s (ζ(2s) / ζ(s)) = ord_{2s} ζ - ord_s ζ`. -/
theorem meromorphicOrderAt_eulerDoublingQuotient (s : ℂ) :
    meromorphicOrderAt eulerDoublingQuotient s =
      meromorphicOrderAt riemannZeta (2 * s) - meromorphicOrderAt riemannZeta s := by
  have h2 := meromorphicOrderAt_riemannZeta_const_mul (two_ne_zero : (2 : ℂ) ≠ 0) s
  change meromorphicOrderAt ((fun w : ℂ => riemannZeta (2 * w)) / riemannZeta) s = _
  rw [meromorphicOrderAt_div h2.1 (meromorphicAt_riemannZeta s), h2.2]

/-- On `Re s > 1/2` away from `s = 1`, `ζ(2s)` is analytic and nonzero (`Re(2s) > 1`), so
`ord_s (ζ(2s) / ζ(s)) = - ord_s ζ`: denominator zeros at off-line zeros `ρ` never cancel. -/
theorem meromorphicOrderAt_eulerDoublingQuotient_of_half_lt_re {s : ℂ}
    (hs : 1 / 2 < s.re) :
    meromorphicOrderAt eulerDoublingQuotient s = - meromorphicOrderAt riemannZeta s := by
  rw [meromorphicOrderAt_eulerDoublingQuotient]
  have h2re : 1 < (2 * s).re := by
    have hre : (2 * s).re = 2 * s.re := by simp
    linarith
  have h2ne1 : 2 * s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h2re
    exact lt_irrefl 1 h2re
  have ho0 : meromorphicOrderAt riemannZeta (2 * s) = 0 :=
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (analyticAt_riemannZeta h2ne1)
      (riemannZeta_ne_zero_of_one_le_re h2re.le)
  rw [ho0, zero_sub]

/-- At every off-line zero `ρ` of `riemannZeta` (`Re ρ > 1/2`), `ζ(2s) / ζ(s)` has a genuine pole
(`meromorphicOrderAt < 0`) of multiplicity `ord_ρ ζ`. -/
theorem eulerDoublingQuotient_neg_order_of_zeta_zero {ρ : ℂ}
    (hre : 1 / 2 < ρ.re) (hζ : riemannZeta ρ = 0) :
    meromorphicOrderAt eulerDoublingQuotient ρ < 0 := by
  rw [meromorphicOrderAt_eulerDoublingQuotient_of_half_lt_re hre]
  have hne1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hζ)
  have hpos : 0 < meromorphicOrderAt riemannZeta ρ :=
    meromorphicOrderAt_pos_of_analyticAt_eq_zero (analyticAt_riemannZeta hne1) hζ
  have hntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
    meromorphicOrderAt_riemannZeta_ne_top ρ
  lift meromorphicOrderAt riemannZeta ρ to ℤ using hntop with n hn
  have hn_pos : 0 < n := by exact_mod_cast hpos
  change ((-n : ℤ) : WithTop ℤ) < (0 : ℤ)
  exact_mod_cast neg_lt_zero.mpr hn_pos

/-- For every `β ≥ 1/2`, `ζ(2s) / ζ(s)` is pole-free on `{Re s > β, s ≠ 1}` if and only if
`zetaZeroAbscissa ≤ β`. -/
theorem eulerDoublingQuotient_poleFree_iff_zetaZeroAbscissa_le {β : ℝ} (hβ : 1 / 2 ≤ β) :
    (∀ s : ℂ, β < s.re → s ≠ 1 → 0 ≤ meromorphicOrderAt eulerDoublingQuotient s) ↔
      RHTower.zetaZeroAbscissa ≤ β := by
  constructor
  · intro hpole
    have hσ : 0 ≤ β - 1 / 2 := by linarith
    have hle : RHTower.zetaZeroAbscissa ≤ 1 / 2 + (β - 1 / 2) := by
      rw [SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ]
      intro ρ hρ
      obtain ⟨hζ, _, _⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
      by_contra hgt
      rw [not_le] at hgt
      have hβρ : β < ρ.re := by linarith
      have hne1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hζ)
      have hneg := eulerDoublingQuotient_neg_order_of_zeta_zero (lt_of_le_of_lt hβ hβρ) hζ
      exact not_le.mpr hneg (hpole ρ hβρ hne1)
    linarith only [hle]
  · intro habs s hs hs1
    rw [meromorphicOrderAt_eulerDoublingQuotient_of_half_lt_re (lt_of_le_of_lt hβ hs)]
    have hnz : riemannZeta s ≠ 0 := by
      intro hz
      exact not_le.mpr hs ((RHTower.re_le_zetaZeroAbscissa hz).trans habs)
    rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (analyticAt_riemannZeta hs1) hnz]
    simp

/-! ## 3. Root-coincidence abscissa bound and unconditional `k ≥ 7` exclusion -/

/-- **`k`-fold root-coincidence abscissa lower bound.** If `k ≥ 1` and `ρ` is a zero of `ζ` with
`0 < Re ρ` such that `ζ(ρ / k) = 0`, then functional reflection produces the strip zero `1 - ρ / k`
and forces `k / (k + 1) ≤ zetaZeroAbscissa`. -/
theorem abscissa_ge_of_zeta_zero_div_nat {k : ℕ} (hk : 1 ≤ k) {ρ : ℂ}
    (h0 : 0 < ρ.re) (hζ : riemannZeta ρ = 0) (hζk : riemannZeta (ρ / (k : ℂ)) = 0) :
    (k : ℝ) / ((k : ℝ) + 1) ≤ RHTower.zetaZeroAbscissa := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hρ_lt1 : ρ.re < 1 := by
    have hstrip :=
      MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip h0 hζ
    linarith [hstrip.2]
  have hdiv_re : (ρ / (k : ℂ)).re = ρ.re / (k : ℝ) := by
    have hm := congrArg Complex.re
      (show ((k : ℝ) : ℂ) * (ρ / (k : ℂ)) = ρ by push_cast; exact mul_div_cancel₀ ρ hkc_ne)
    rw [Complex.re_ofReal_mul] at hm
    exact (eq_div_iff hk_pos.ne').mpr hm
  have hdiv_pos : 0 < (ρ / (k : ℂ)).re := by
    rw [hdiv_re]
    exact div_pos h0 hk_pos
  have hdiv_lt1 : (ρ / (k : ℂ)).re < 1 := by
    rw [hdiv_re, div_lt_one hk_pos]
    linarith
  have hrefl : riemannZeta (1 - ρ / (k : ℂ)) = 0 :=
    (RHTower.riemannZeta_one_sub_eq_zero_iff hdiv_pos hdiv_lt1).mpr hζk
  have hle1 : ρ.re ≤ RHTower.zetaZeroAbscissa := RHTower.re_le_zetaZeroAbscissa hζ
  have hle2 : (1 - ρ / (k : ℂ)).re ≤ RHTower.zetaZeroAbscissa :=
    RHTower.re_le_zetaZeroAbscissa hrefl
  rw [Complex.sub_re, Complex.one_re, hdiv_re] at hle2
  have hmul : (k : ℝ) - ρ.re ≤ (k : ℝ) * RHTower.zetaZeroAbscissa := by
    have := mul_le_mul_of_nonneg_left hle2 hk_pos.le
    have hcancel : (k : ℝ) * (1 - ρ.re / (k : ℝ)) = (k : ℝ) - ρ.re := by
      field_simp
    rwa [hcancel] at this
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hle1, hmul]

/-- **Unconditional exclusion of `k`-fold root coincidences for all `k ≥ 7`.** Because
`zetaZeroAbscissa ≤ 20999 / 24000 < 7 / 8 ≤ k / (k + 1)` for `k ≥ 7`, no nontrivial zero `ρ` of
`riemannZeta` (`0 < Re ρ`) satisfies `riemannZeta (ρ / k) = 0`. -/
theorem riemannZeta_div_nat_ne_zero_of_seven_le {k : ℕ} (hk : 7 ≤ k) {ρ : ℂ}
    (h0 : 0 < ρ.re) (hζ : riemannZeta ρ = 0) :
    riemannZeta (ρ / (k : ℂ)) ≠ 0 := by
  intro hζk
  have hlo := abscissa_ge_of_zeta_zero_div_nat (by omega : 1 ≤ k) h0 hζ hζk
  have hhi := zetaZeroAbscissa_le_sub_seven_eighths
  have hk7 : (7 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h78 : (7 / 8 : ℝ) ≤ (k : ℝ) / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith

/--Multiplicative form: for every `k ≥ 7` and every zero `z` of `riemannZeta` with `0 < Re z`,
`riemannZeta (k * z) ≠ 0`. -/
theorem riemannZeta_nat_mul_ne_zero_of_seven_le {k : ℕ} (hk : 7 ≤ k) {z : ℂ}
    (h0 : 0 < z.re) (hζ : riemannZeta z = 0) :
    riemannZeta ((k : ℂ) * z) ≠ 0 := by
  intro hmul
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm_re : ((k : ℂ) * z).re = (k : ℝ) * z.re := by
    simpa using Complex.re_ofReal_mul (k : ℝ) z
  have hm_pos : 0 < ((k : ℂ) * z).re := by
    rw [hm_re]
    exact mul_pos hk_pos h0
  have hdiv : ((k : ℂ) * z) / (k : ℂ) = z := mul_div_cancel_left₀ z hkc_ne
  apply riemannZeta_div_nat_ne_zero_of_seven_le hk hm_pos hmul
  rwa [hdiv]

/-- Pole-cleared `k`-dilated Euler quotient `((s - 1) ζ(s))^m / ζ(k s)`. -/
def dilatedPowerQuotient (k m : ℕ) (s : ℂ) : ℂ :=
  ((s - 1) * riemannZeta s) ^ m / riemannZeta ((k : ℂ) * s)

/-- **Uncancelled pole theorem for `k ≥ 7`.** For every `k ≥ 7`, every `m : ℕ`, and every nontrivial
zero `ρ` of `riemannZeta` (`0 < Re ρ`), the denominator zero at `s = ρ / k` of
`((s - 1) ζ(s))^m / ζ(k s)` is never cancelled by the numerator:
`ord_{ρ/k} (((s - 1) ζ(s))^m / ζ(k s)) = - ord_ρ ζ < 0`. -/
theorem dilatedPowerQuotient_neg_order_at_div_of_seven_le {k : ℕ} (hk : 7 ≤ k) (m : ℕ) {ρ : ℂ}
    (h0 : 0 < ρ.re) (hζ : riemannZeta ρ = 0) :
    meromorphicOrderAt (dilatedPowerQuotient k m) (ρ / (k : ℂ)) =
        - meromorphicOrderAt riemannZeta ρ ∧
      meromorphicOrderAt (dilatedPowerQuotient k m) (ρ / (k : ℂ)) < 0 := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hρ_lt1 : ρ.re < 1 := by
    have hstrip :=
      MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip h0 hζ
    linarith [hstrip.2]
  have hρ_ne1 : ρ ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hζ)
  have hs_re : (ρ / (k : ℂ)).re = ρ.re / (k : ℝ) := by
    have hm := congrArg Complex.re
      (show ((k : ℝ) : ℂ) * (ρ / (k : ℂ)) = ρ by push_cast; exact mul_div_cancel₀ ρ hkc_ne)
    rw [Complex.re_ofReal_mul] at hm
    exact (eq_div_iff hk_pos.ne').mpr hm
  have hs_lt1 : (ρ / (k : ℂ)).re < 1 := by
    rw [hs_re, div_lt_one hk_pos]
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hs_ne1 : ρ / (k : ℂ) ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs_lt1
    exact lt_irrefl 1 hs_lt1
  have hnz_div : riemannZeta (ρ / (k : ℂ)) ≠ 0 :=
    riemannZeta_div_nat_ne_zero_of_seven_le hk h0 hζ
  set u : ℂ → ℂ := fun w => ((w - 1) * riemannZeta w) ^ m
  set v : ℂ → ℂ := fun w => riemannZeta ((k : ℂ) * w)
  have hu_an : AnalyticAt ℂ u (ρ / (k : ℂ)) :=
    ((analyticAt_id.sub analyticAt_const).mul (analyticAt_riemannZeta hs_ne1)).pow m
  have hu_ne : u (ρ / (k : ℂ)) ≠ 0 :=
    pow_ne_zero m (mul_ne_zero (sub_ne_zero.mpr hs_ne1) hnz_div)
  have hu_ord : meromorphicOrderAt u (ρ / (k : ℂ)) = 0 :=
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hu_an hu_ne
  have hv_pair := meromorphicOrderAt_riemannZeta_const_mul hkc_ne (ρ / (k : ℂ))
  have hmul_div : (k : ℂ) * (ρ / (k : ℂ)) = ρ := mul_div_cancel₀ ρ hkc_ne
  have hv_ord : meromorphicOrderAt v (ρ / (k : ℂ)) = meromorphicOrderAt riemannZeta ρ := by
    simpa [v, hmul_div] using hv_pair.2
  have hord : meromorphicOrderAt (dilatedPowerQuotient k m) (ρ / (k : ℂ)) =
      - meromorphicOrderAt riemannZeta ρ := by
    change meromorphicOrderAt (u / v) (ρ / (k : ℂ)) = _
    rw [meromorphicOrderAt_div hu_an.meromorphicAt hv_pair.1, hu_ord, hv_ord, zero_sub]
  refine ⟨hord, ?_⟩
  rw [hord]
  have hpos : 0 < meromorphicOrderAt riemannZeta ρ :=
    meromorphicOrderAt_pos_of_analyticAt_eq_zero (analyticAt_riemannZeta hρ_ne1) hζ
  have hntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
    meromorphicOrderAt_riemannZeta_ne_top ρ
  lift meromorphicOrderAt riemannZeta ρ to ℤ using hntop with n hn
  have hn_pos : 0 < n := by exact_mod_cast hpos
  change ((-n : ℤ) : WithTop ℤ) < (0 : ℤ)
  exact_mod_cast neg_lt_zero.mpr hn_pos

/-! ## 4. Upgraded `[1/2, 27001 / 48000)` squarefree ruler, Ramanujan margin, and lever covers -/

/-- **Upgraded `[1/2, 27001 / 48000)` squarefree pole-abscissa theorem.** Because
`1 - (20999 / 24000) / 2 = 27001 / 48000 = 9 / 16 + 1 / 48000`, pole-freeness of
`((s - 1) ζ(s))^m / ζ(2s)` on `{Re s > β / 2}` is unconditionally equivalent to
`zetaZeroAbscissa ≤ β` across all `β ∈ [1/2, 27001 / 48000)`. -/
theorem squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le_sub (m : ℕ) {β : ℝ}
    (hβ : β ∈ Set.Ico (1 / 2 : ℝ) (27001 / 48000)) :
    (∀ s : ℂ, β / 2 < s.re → 0 ≤ meromorphicOrderAt (squarefreePowerQuotient m) s) ↔
      RHTower.zetaZeroAbscissa ≤ β := by
  obtain ⟨hβ_lo, hβ_hi⟩ := hβ
  constructor
  · intro hpole
    have hhalf : ∀ ρ : ℂ, riemannZeta ρ = 0 → 2 * (β / 2) < ρ.re → ρ.re < 1 →
        riemannZeta (ρ / 2) = 0 := by
      intro ρ hζ hre1 hre2
      by_contra hnhalf
      have hs_re : (ρ / 2).re = ρ.re / 2 := by
        have h := congrArg Complex.re (show ((2 : ℝ) : ℂ) * (ρ / 2) = ρ by push_cast; ring)
        rw [Complex.re_ofReal_mul] at h
        linarith
      have hs_gt : β / 2 < (ρ / 2).re := by linarith
      have hs_ne1 : ρ / 2 ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hs_re
        linarith
      have hρ_ne1 : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hre2
        exact lt_irrefl 1 hre2
      set u : ℂ → ℂ := fun w => ((w - 1) * riemannZeta w) ^ m
      set v : ℂ → ℂ := fun w => riemannZeta (2 * w)
      have hu_an : AnalyticAt ℂ u (ρ / 2) :=
        ((analyticAt_id.sub analyticAt_const).mul (analyticAt_riemannZeta hs_ne1)).pow m
      have hu_ne : u (ρ / 2) ≠ 0 :=
        pow_ne_zero m (mul_ne_zero (sub_ne_zero.mpr hs_ne1) hnhalf)
      have hu_ord : meromorphicOrderAt u (ρ / 2) = 0 :=
        meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero hu_an hu_ne
      have hv_pair := meromorphicOrderAt_riemannZeta_const_mul (two_ne_zero : (2 : ℂ) ≠ 0) (ρ / 2)
      have h2half : (2 : ℂ) * (ρ / 2) = ρ := by ring
      have hv_ord : meromorphicOrderAt v (ρ / 2) = meromorphicOrderAt riemannZeta ρ := by
        simpa [v, h2half] using hv_pair.2
      have hρ_pos : 0 < meromorphicOrderAt riemannZeta ρ :=
        meromorphicOrderAt_pos_of_analyticAt_eq_zero (analyticAt_riemannZeta hρ_ne1) hζ
      have hρ_ntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
        meromorphicOrderAt_riemannZeta_ne_top ρ
      lift meromorphicOrderAt riemannZeta ρ to ℤ using hρ_ntop with n hn
      have hn_pos : 0 < n := by exact_mod_cast hρ_pos
      have hq_ord : meromorphicOrderAt (squarefreePowerQuotient m) (ρ / 2) =
          ((-n : ℤ) : WithTop ℤ) := by
        change meromorphicOrderAt (u / v) (ρ / 2) = _
        rw [meromorphicOrderAt_div hu_an.meromorphicAt hv_pair.1, hu_ord, hv_ord, zero_sub]
        rfl
      have hnonneg := hpole (ρ / 2) hs_gt
      rw [hq_ord] at hnonneg
      have hle : (0 : ℤ) ≤ -n := by exact_mod_cast hnonneg
      omega
    have hσ : 0 ≤ β - 1 / 2 := by linarith
    have hle : RHTower.zetaZeroAbscissa ≤ 1 / 2 + (β - 1 / 2) := by
      rw [SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ]
      intro ρ hρ
      obtain ⟨hζ, h0, _⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
      have hsub : ρ.re ≤ 20999 / 24000 :=
        (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip h0 hζ).2
      by_contra hgt
      rw [not_le] at hgt
      exact RHTower.SquarefreeDiscrepancy.riemannZeta_ne_zero_of_halving
        (by linarith : (0 : ℝ) ≤ β / 2) hhalf (by linarith) (by linarith) hζ
    linarith only [hle]
  · intro habs s hs
    rw [meromorphicOrderAt_congr (squarefreePowerQuotient_eventuallyEq_unit m s)]
    have h2s_re : (2 * s).re = 2 * s.re := by simp
    have hden_ne : RHTower.zetaResidueUnit (2 * s) ≠ 0 := by
      by_cases h2s1 : 2 * s = 1
      · rw [h2s1, RHTower.zetaResidueUnit_one]
        exact one_ne_zero
      · rw [RHTower.zetaResidueUnit, Function.update_of_ne h2s1]
        refine mul_ne_zero (sub_ne_zero.mpr h2s1) ?_
        intro hζ2
        have hle := (RHTower.re_le_zetaZeroAbscissa hζ2).trans habs
        linarith
    have han : AnalyticAt ℂ
        (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * (2 * w - 1) /
          RHTower.zetaResidueUnit (2 * w)) s := by
      have hnum : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * (2 * w - 1)) s :=
        ((RHTower.analyticAt_zetaResidueUnit s).pow m).mul
          ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
      have hden : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit (2 * w)) s :=
        (RHTower.analyticAt_zetaResidueUnit (2 * s)).comp (analyticAt_const.mul analyticAt_id)
      exact hnum.div hden hden_ne
    exact han.meromorphicOrderAt_nonneg

/-- **Upgraded squarefree ruler for `zetaZeroWidth` on `[0, 3001 / 48000)`**
(`3001 / 48000 = 1 / 16 + 1 / 48000`). -/
theorem isRuler_squarefreePowerQuotient_sub (m : ℕ) :
    IsRuler SquareRootThreshold.zetaZeroWidth
      (Set.Ico (0 : ℝ) (3001 / 48000))
      (fun w => ∀ s : ℂ, (1 / 2 + w) / 2 < s.re →
        0 ≤ meromorphicOrderAt (squarefreePowerQuotient m) s) := by
  intro w hw
  have hβ : 1 / 2 + w ∈ Set.Ico (1 / 2 : ℝ) (27001 / 48000) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  exact (SquareRootThreshold.zetaZeroWidth_le_iff_zetaZeroAbscissa_le hw.1).trans
    (squarefreePowerQuotient_poleFree_iff_zetaZeroAbscissa_le_sub m hβ).symm

/-- **Upgraded Ramanujan shift-margin theorem.** For every nontrivial zero `ρ` of `riemannZeta`
(`Re ρ > 0`) and every shift pair `(a, b) ∈ ℂ²`, the denominator zero `s_* = (ρ + a + b) / 2` lies
at least `27001 / 48000` (`> 9 / 16`) to the left of the polar abscissa `σ_pole(a, b)`. -/
theorem ramanujan_shift_margin_zeta_zero_ge_sub (a b : ℂ) {ρ : ℂ}
    (h0 : 0 < ρ.re) (hζ : riemannZeta ρ = 0) :
    (27001 / 48000 : ℝ) ≤
      (1 + max (max (0 : ℝ) a.re) (max b.re (a + b).re)) - ((ρ + a + b) / 2).re := by
  have hsub : ρ.re ≤ 20999 / 24000 :=
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip h0 hζ).2
  have hm := ramanujan_shift_margin_ge a b ρ
  linarith

/-- Witness predicate for a zero of any Dirichlet `L`-function on `Re w > 20999 / 24000` away from
`(χ = 1, w = 1)`. -/
def ExistsDirichletZeroRightOfSubSevenEighths : Prop :=
  ∃ (q : ℕ) (hq : q ≠ 0) (χ : DirichletCharacter ℂ q) (w : ℂ),
    ¬(χ = 1 ∧ w = 1) ∧ (20999 / 24000 : ℝ) < w.re ∧
      (letI : NeZero q := ⟨hq⟩; DirichletCharacter.LFunction χ w = 0)

/-- Unconditionally, no Dirichlet `L`-function has a zero on `Re w > 20999 / 24000` away from
`(χ = 1, w = 1)`. -/
theorem not_existsDirichletZeroRightOfSubSevenEighths :
    ¬ ExistsDirichletZeroRightOfSubSevenEighths := by
  rintro ⟨q, hq, χ, w, hexc, hw, hw0⟩
  exact MetaplecticMobiusDescent.CubicEisenstein.SubSevenEighthsZeroFree.dirichlet_sub_seven_eighths_nonzero
    q hq χ w hw hexc hw0

/-- **Covering lever family on `(1/2, 20999 / 24000]` implies `RiemannHypothesis`.** Because
`zetaZeroAbscissa ≤ 20999 / 24000` holds unconditionally, lever families only need to cover
`(1/2, 20999 / 24000]` rather than `(1/2, 7/8]`. -/
theorem riemannHypothesis_of_covering_levers_sub_seven_eighths {𝒯 : Set (ℝ → ℝ)}
    (hlev : ∀ T ∈ 𝒯, IsLever RHTower.zetaZeroAbscissa T)
    (hcov : Set.Ioc (1 / 2 : ℝ) (20999 / 24000) ⊆ ⋃ T ∈ 𝒯, excluded T) :
    RHTower.zetaZeroAbscissa = 1 / 2 ∧
      SquareRootThreshold.zetaZeroWidth = 0 ∧
      RiemannHypothesis := by
  have hhi : RHTower.zetaZeroAbscissa ≤ 20999 / 24000 := zetaZeroAbscissa_le_sub_seven_eighths
  have hlo : (1 / 2 : ℝ) ≤ RHTower.zetaZeroAbscissa := RHTower.half_le_zetaZeroAbscissa
  have hΘ : RHTower.zetaZeroAbscissa = 1 / 2 := by
    by_contra hne
    have hmem : RHTower.zetaZeroAbscissa ∈ Set.Ioc (1 / 2 : ℝ) (20999 / 24000) :=
      ⟨lt_of_le_of_ne hlo (Ne.symm hne), hhi⟩
    obtain ⟨_, ⟨T, rfl⟩, _, ⟨hT, rfl⟩, hex⟩ := hcov hmem
    exact absurd (hlev T hT).le_apply_self (not_le.mpr hex)
  have hw : SquareRootThreshold.zetaZeroWidth = 0 := by
    rw [SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half, hΘ]
    ring
  exact ⟨hΘ, hw, SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr hw⟩

end GaloisForLFunctions.ZeroForcingCalculus

