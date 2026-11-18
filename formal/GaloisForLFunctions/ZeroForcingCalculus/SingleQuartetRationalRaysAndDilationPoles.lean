import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity

/-!
# All-Scale Euler Dilation Rulers and Rational-Ray Zero Rigidity of a Single Off-Line Quartet

This module establishes two complementary structural results on the pole geometry of the
`k`-dilated Euler quotients `((s - 1) ζ(s))^m / ζ(k s)` (`dilatedPowerQuotient k m`) and on zero
transport along scalar rays under a single off-line quartet:

1. **All-`k ≥ 2` width rulers and `1/(2k)` equivalences with `RiemannHypothesis`**
   (`dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le`, `isRuler_dilatedPowerQuotient`,
   `dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le_of_seven_le`,
   `dilatedPowerQuotient_poleFree_iff_riemannHypothesis`):
   For every integer `k ≥ 2` and `m : ℕ`, pole-freeness of `((s - 1) ζ(s))^m / ζ(k s)` on
   `{Re s > β / k}` is unconditionally equivalent to `zetaZeroAbscissa ≤ β` across
   `β ∈ [1/2, 1 - 20999 / (24000 k))` (and across all `β ≥ 1/2` when `k ≥ 7`), via an iterated
   `k`-ary halving-reflection cascade `ρ_{n+1} = 1 - ρ_n / k` whose ordinates decay as
   `|Im ρ₀| / k^n → 0` against the strip-ordinate floor `|Im ρ| > 4`. At `β = 1/2`, pole-freeness
   on `{Re s > 1 / (2k)}` is equivalent to `RiemannHypothesis` for every `k ≥ 2` and `m : ℕ`.

2. **Rational-ray classification and complete `k ≥ 2` root-dilation exclusion under a single quartet**
   (`riemannZeta_pos_real_mul_eq_zero_imp`, `subsingleton_other_ray_zeros_of_singleQuartet`,
   `riemannZeta_rat_ray_ne_zero_of_irrational_re`,
   `riemannZeta_div_nat_ne_zero_of_singleQuartet`,
   `dilatedPowerQuotient_neg_order_of_singleQuartet`,
   `riemannZeta_nat_mul_ne_zero_of_singleQuartet_ge_four`):
   Under `HasSingleOffLineQuartet ρ₀`:
   - At most one positive scalar `r ≠ 1` (`r = 1 / (2 Re ρ₀) ∈ [12000/20999, 1)`) can satisfy
     `ζ(r ρ₀) = 0`; when `Irrational ρ₀.re`, `ζ(q ρ₀) ≠ 0` for every positive rational `q ≠ 1`.
   - Closing the unconditional `k ∈ {2, 3, 4, 5, 6}` gap, `ζ(ρ / k) ≠ 0` and
     `ord_{ρ/k} (((s - 1) ζ(s))^m / ζ(k s)) = - ord_ρ ζ < 0` hold for **every** `k ≥ 2`, `m : ℕ`,
     and `ρ ∈ zeroQuartetSet ρ₀`.
   - `ζ(k ρ) ≠ 0` holds for every `k ≥ 2` on `{ρ₀, conj ρ₀}` and for every `k ≥ 4` on the full
     quartet `zeroQuartetSet ρ₀`.
-/

noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology Zeta23
open scoped ComplexConjugate
open GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
open GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GaloisForLFunctions.ZeroForcingCalculus

/-! ## 1. Meromorphic unit representation and uncancelled-pole criterion for `dilatedPowerQuotient` -/

/-- Every strip zero `ρ` of `riemannZeta` (`0 < Re ρ < 1`) has ordinate `|Im ρ| > 4`. -/
theorem four_lt_abs_im_of_strip_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hζ : riemannZeta ρ = 0) : 4 < |ρ.im| := by
  have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hxi : RHTower.xi ρ = 0 := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mpr hζ
  obtain ⟨q, hq_eq⟩ := RHTower.exists_xiZeroCopy_of_xi_eq_zero hxi
  have h := RHTower.four_lt_abs_zeroOrdinate q
  rwa [RHTower.zeroOrdinate, hq_eq] at h

/-- On a punctured neighborhood of every `s : ℂ` (including `s = 1` and `s = 1 / k`),
`dilatedPowerQuotient k m` agrees with `zetaResidueUnit(w)^m * (k w - 1) / zetaResidueUnit(k w)`. -/
theorem dilatedPowerQuotient_eventuallyEq_unit {k : ℕ} (hk : 1 ≤ k) (m : ℕ) (s : ℂ) :
    dilatedPowerQuotient k m =ᶠ[𝓝[≠] s]
      fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1) /
        RHTower.zetaResidueUnit ((k : ℂ) * w) := by
  have hkc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hw1 : ∀ᶠ w : ℂ in 𝓝[≠] s, w ≠ 1 := by
    by_cases hs : s = 1
    · subst hs
      filter_upwards [self_mem_nhdsWithin] with w hw using hw
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hs)
  have hwk : ∀ᶠ w : ℂ in 𝓝[≠] s, w ≠ 1 / (k : ℂ) := by
    by_cases hs : s = 1 / (k : ℂ)
    · subst hs
      filter_upwards [self_mem_nhdsWithin] with w hw using hw
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hs)
  filter_upwards [hw1, hwk] with w hne1 hnek
  have hkw1 : (k : ℂ) * w ≠ 1 := by
    intro h
    apply hnek
    rw [eq_div_iff hkc, mul_comm]
    exact h
  have hsub : (k : ℂ) * w - 1 ≠ 0 := sub_ne_zero.mpr hkw1
  unfold dilatedPowerQuotient
  change ((w - 1) * riemannZeta w) ^ m / riemannZeta ((k : ℂ) * w) =
    Function.update (fun z => (z - 1) * riemannZeta z) 1 1 w ^ m * ((k : ℂ) * w - 1) /
      Function.update (fun z => (z - 1) * riemannZeta z) 1 1 ((k : ℂ) * w)
  rw [Function.update_of_ne hne1, Function.update_of_ne hkw1,
    mul_comm ((k : ℂ) * w - 1) (riemannZeta ((k : ℂ) * w)), mul_div_mul_right _ _ hsub]

/-- `dilatedPowerQuotient k m` is meromorphic at every `s : ℂ` for `k ≥ 1`. -/
theorem meromorphicAt_dilatedPowerQuotient {k : ℕ} (hk : 1 ≤ k) (m : ℕ) (s : ℂ) :
    MeromorphicAt (dilatedPowerQuotient k m) s := by
  have hnum : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1)) s :=
    ((RHTower.analyticAt_zetaResidueUnit s).pow m).mul
      ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
  have hden : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit ((k : ℂ) * w)) s :=
    (RHTower.analyticAt_zetaResidueUnit ((k : ℂ) * s)).comp (analyticAt_const.mul analyticAt_id)
  exact (hnum.meromorphicAt.div hden.meromorphicAt).congr
    (dilatedPowerQuotient_eventuallyEq_unit hk m s).symm

/-- Whenever `k ≥ 1`, `0 < Re ρ`, `ζ(ρ) = 0`, and `ζ(ρ / k) ≠ 0`, `dilatedPowerQuotient k m` has
exact meromorphic order `- ord_ρ ζ < 0` at `ρ / k`. -/
theorem dilatedPowerQuotient_neg_order_of_div_ne_zero {k : ℕ} (hk : 1 ≤ k) (m : ℕ) {ρ : ℂ}
    (h0 : 0 < ρ.re) (hζ : riemannZeta ρ = 0) (hnz : riemannZeta (ρ / (k : ℂ)) ≠ 0) :
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
    exact (eq_div_iff hk_pos.ne').mpr ((mul_comm _ _).trans hm)
  have hs_lt1 : (ρ / (k : ℂ)).re < 1 := by
    rw [hs_re, div_lt_one hk_pos]
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hs_ne1 : ρ / (k : ℂ) ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hs_lt1; exact lt_irrefl 1 hs_lt1
  set u : ℂ → ℂ := fun w => ((w - 1) * riemannZeta w) ^ m
  set v : ℂ → ℂ := fun w => riemannZeta ((k : ℂ) * w)
  have hu_an : AnalyticAt ℂ u (ρ / (k : ℂ)) :=
    ((analyticAt_id.sub analyticAt_const).mul (analyticAt_riemannZeta hs_ne1)).pow m
  have hu_ne : u (ρ / (k : ℂ)) ≠ 0 :=
    pow_ne_zero m (mul_ne_zero (sub_ne_zero.mpr hs_ne1) hnz)
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
  have hntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ := meromorphicOrderAt_riemannZeta_ne_top ρ
  lift meromorphicOrderAt riemannZeta ρ to ℤ using hntop with n hn
  have hn_pos : 0 < n := by exact_mod_cast hpos
  change ((-n : ℤ) : WithTop ℤ) < (0 : ℤ)
  exact_mod_cast neg_lt_zero.mpr hn_pos

/-! ## 2. All-`k ≥ 2` pole-abscissa rulers and `1/(2k)` equivalences with `RiemannHypothesis` -/

private theorem real_div_nat_re (z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (z / (k : ℂ)).re = z.re / (k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm := congrArg Complex.re
    (show ((k : ℝ) : ℂ) * (z / (k : ℂ)) = z by push_cast; exact mul_div_cancel₀ z hkc_ne)
  rw [Complex.re_ofReal_mul] at hm
  exact (eq_div_iff hk_pos.ne').mpr ((mul_comm _ _).trans hm)

private theorem real_div_nat_im (z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (z / (k : ℂ)).im = z.im / (k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkc_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm := congrArg Complex.im
    (show ((k : ℝ) : ℂ) * (z / (k : ℂ)) = z by push_cast; exact mul_div_cancel₀ z hkc_ne)
  rw [Complex.im_ofReal_mul] at hm
  exact (eq_div_iff hk_pos.ne').mpr ((mul_comm _ _).trans hm)

/-- **`k`-ary halving-reflection ordinate cascade.** For `k ≥ 2` and
`1/2 ≤ β < 1 - 20999 / (24000 k)`, if every strip zero `ρ` with `β < Re ρ < 1` satisfies
`ζ(ρ / k) = 0`, then no strip zero can lie strictly right of `β`. -/
theorem dilated_halving_reflection_impossible {k : ℕ} (hk : 2 ≤ k) {β : ℝ}
    (hβ_lo : 1 / 2 ≤ β) (hβ_hi : β < 1 - 20999 / (24000 * (k : ℝ)))
    (hdiv : ∀ ρ : ℂ, riemannZeta ρ = 0 → β < ρ.re → ρ.re < 1 → riemannZeta (ρ / (k : ℂ)) = 0)
    {ρ₀ : ℂ} (hζ₀ : riemannZeta ρ₀ = 0) (hre₀ : β < ρ₀.re) (hlt1₀ : ρ₀.re < 1) : False := by
  have hk1 : 1 ≤ k := by omega
  have hk_gt1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  let seq : ℕ → ℂ := fun n => Nat.recOn n ρ₀ (fun _ z => 1 - z / (k : ℂ))
  have hseq : ∀ n : ℕ, riemannZeta (seq n) = 0 ∧ β < (seq n).re ∧ (seq n).re < 1 ∧
      |(seq n).im| = |ρ₀.im| / (k : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      simpa [seq] using ⟨hζ₀, hre₀, hlt1₀⟩
    | succ n ih =>
      obtain ⟨hζn, hren, hlt1n, himn⟩ := ih
      have h0n : 0 < (seq n).re := by linarith
      have hsub : (seq n).re ≤ 20999 / 24000 :=
        (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip
          h0n hζn).2
      have hζ_div : riemannZeta (seq n / (k : ℂ)) = 0 := hdiv (seq n) hζn hren hlt1n
      have hw_re : (seq n / (k : ℂ)).re = (seq n).re / (k : ℝ) := real_div_nat_re (seq n) hk1
      have hw_im : (seq n / (k : ℂ)).im = (seq n).im / (k : ℝ) := real_div_nat_im (seq n) hk1
      have hw_pos : 0 < (seq n / (k : ℂ)).re := by rw [hw_re]; exact div_pos h0n hk_pos
      have hw_lt1 : (seq n / (k : ℂ)).re < 1 := by
        rw [hw_re, div_lt_one hk_pos]; linarith
      have hζ_next : riemannZeta (seq (n + 1)) = 0 :=
        (RHTower.riemannZeta_one_sub_eq_zero_iff hw_pos hw_lt1).mpr hζ_div
      have hre_eq : (seq (n + 1)).re = 1 - (seq n).re / (k : ℝ) := by
        change (1 - seq n / (k : ℂ)).re = _
        rw [Complex.sub_re, Complex.one_re, hw_re]
      have him_eq : |(seq (n + 1)).im| = |ρ₀.im| / (k : ℝ) ^ (n + 1) := by
        change |(1 - seq n / (k : ℂ)).im| = _
        rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, hw_im, abs_div,
          abs_of_pos hk_pos, himn, div_div, pow_succ]
      have hdiv_le : (seq n).re / (k : ℝ) ≤ 20999 / (24000 * (k : ℝ)) := by
        rw [div_le_div_iff₀ hk_pos (by positivity)]
        nlinarith
      exact ⟨hζ_next, by linarith, by linarith, him_eq⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt |ρ₀.im| hk_gt1
  obtain ⟨hζn, hren, hlt1n, himn⟩ := hseq n
  have h4 : 4 < |(seq n).im| := four_lt_abs_im_of_strip_zero (by linarith) hlt1n hζn
  have hle1 : |(seq n).im| < 1 := by
    rw [himn, div_lt_one (pow_pos hk_pos n)]
    exact hn
  linarith

/-- **All-`k ≥ 2` pole-abscissa theorem.** For every `k ≥ 2`, `m : ℕ`, and
`β ∈ [1/2, 1 - 20999 / (24000 k))`, `dilatedPowerQuotient k m` is pole-free on
`{Re s > β / k}` if and only if `zetaZeroAbscissa ≤ β`. -/
theorem dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le {k : ℕ} (hk : 2 ≤ k) (m : ℕ)
    {β : ℝ} (hβ : β ∈ Set.Ico (1 / 2 : ℝ) (1 - 20999 / (24000 * (k : ℝ)))) :
    (∀ s : ℂ, β / (k : ℝ) < s.re → 0 ≤ meromorphicOrderAt (dilatedPowerQuotient k m) s) ↔
      RHTower.zetaZeroAbscissa ≤ β := by
  obtain ⟨hβ_lo, hβ_hi⟩ := hβ
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  constructor
  · intro hpole
    have hdiv : ∀ ρ : ℂ, riemannZeta ρ = 0 → β < ρ.re → ρ.re < 1 →
        riemannZeta (ρ / (k : ℂ)) = 0 := by
      intro ρ hζ hre1 hre2
      by_contra hnz
      have hs_gt : β / (k : ℝ) < (ρ / (k : ℂ)).re := by
        rw [real_div_nat_re ρ hk1]
        exact div_lt_div_of_pos_right hre1 hk_pos
      have hneg := (dilatedPowerQuotient_neg_order_of_div_ne_zero hk1 m (by linarith) hζ hnz).2
      exact not_le.mpr hneg (hpole (ρ / (k : ℂ)) hs_gt)
    have hσ : 0 ≤ β - 1 / 2 := by linarith
    have hle : RHTower.zetaZeroAbscissa ≤ 1 / 2 + (β - 1 / 2) := by
      rw [SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ]
      intro ρ hρ
      obtain ⟨hζ, _, hlt1⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
      by_contra hgt
      rw [not_le] at hgt
      exact dilated_halving_reflection_impossible hk hβ_lo hβ_hi hdiv hζ (by linarith) hlt1
    linarith only [hle]
  · intro habs s hs
    rw [meromorphicOrderAt_congr (dilatedPowerQuotient_eventuallyEq_unit hk1 m s)]
    have hks_re : ((k : ℂ) * s).re = (k : ℝ) * s.re := by simp
    have hβ_lt : β < s.re * (k : ℝ) := (div_lt_iff₀ hk_pos).mp hs
    have hden_ne : RHTower.zetaResidueUnit ((k : ℂ) * s) ≠ 0 := by
      by_cases hks1 : (k : ℂ) * s = 1
      · rw [hks1, RHTower.zetaResidueUnit_one]
        exact one_ne_zero
      · rw [RHTower.zetaResidueUnit, Function.update_of_ne hks1]
        refine mul_ne_zero (sub_ne_zero.mpr hks1) ?_
        intro hζk
        have hle := (RHTower.re_le_zetaZeroAbscissa hζk).trans habs
        linarith
    have han : AnalyticAt ℂ
        (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1) /
          RHTower.zetaResidueUnit ((k : ℂ) * w)) s := by
      have hnum : AnalyticAt ℂ
          (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1)) s :=
        ((RHTower.analyticAt_zetaResidueUnit s).pow m).mul
          ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
      have hden : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit ((k : ℂ) * w)) s :=
        (RHTower.analyticAt_zetaResidueUnit ((k : ℂ) * s)).comp (analyticAt_const.mul analyticAt_id)
      exact hnum.div hden hden_ne
    exact han.meromorphicOrderAt_nonneg

/-- **All-`k ≥ 2` width ruler.** For every `k ≥ 2` and `m : ℕ`, pole-freeness of
`dilatedPowerQuotient k m` on `{Re s > (1/2 + w) / k}` is an unconditional ruler for
`zetaZeroWidth` on `[0, 1/2 - 20999 / (24000 k))`. -/
theorem isRuler_dilatedPowerQuotient {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    IsRuler SquareRootThreshold.zetaZeroWidth
      (Set.Ico (0 : ℝ) (1 / 2 - 20999 / (24000 * (k : ℝ))))
      (fun w => ∀ s : ℂ, (1 / 2 + w) / (k : ℝ) < s.re →
        0 ≤ meromorphicOrderAt (dilatedPowerQuotient k m) s) := by
  intro w hw
  have hβ : 1 / 2 + w ∈ Set.Ico (1 / 2 : ℝ) (1 - 20999 / (24000 * (k : ℝ))) :=
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  exact (SquareRootThreshold.zetaZeroWidth_le_iff_zetaZeroAbscissa_le hw.1).trans
    (dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le hk m hβ).symm

/-- **Unrestricted `[1/2, ∞)` pole-abscissa equivalence for `k ≥ 7`.** Because root coincidences
`ζ(ρ / k) = 0` are unconditionally impossible for `k ≥ 7`, no upper cutoff on `β ≥ 1/2` is needed. -/
theorem dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le_of_seven_le {k : ℕ} (hk : 7 ≤ k)
    (m : ℕ) {β : ℝ} (hβ : 1 / 2 ≤ β) :
    (∀ s : ℂ, β / (k : ℝ) < s.re → 0 ≤ meromorphicOrderAt (dilatedPowerQuotient k m) s) ↔
      RHTower.zetaZeroAbscissa ≤ β := by
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  constructor
  · intro hpole
    have hσ : 0 ≤ β - 1 / 2 := by linarith
    have hle : RHTower.zetaZeroAbscissa ≤ 1 / 2 + (β - 1 / 2) := by
      rw [SquareRootThreshold.zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ]
      intro ρ hρ
      obtain ⟨hζ, h0, _⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
      by_contra hgt
      rw [not_le] at hgt
      have hs_gt : β / (k : ℝ) < (ρ / (k : ℂ)).re := by
        rw [real_div_nat_re ρ hk1]
        exact div_lt_div_of_pos_right (by linarith) hk_pos
      have hneg := (dilatedPowerQuotient_neg_order_at_div_of_seven_le hk m h0 hζ).2
      exact not_le.mpr hneg (hpole (ρ / (k : ℂ)) hs_gt)
    linarith only [hle]
  · intro habs s hs
    rw [meromorphicOrderAt_congr (dilatedPowerQuotient_eventuallyEq_unit hk1 m s)]
    have hks_re : ((k : ℂ) * s).re = (k : ℝ) * s.re := by simp
    have hβ_lt : β < s.re * (k : ℝ) := (div_lt_iff₀ hk_pos).mp hs
    have hden_ne : RHTower.zetaResidueUnit ((k : ℂ) * s) ≠ 0 := by
      by_cases hks1 : (k : ℂ) * s = 1
      · rw [hks1, RHTower.zetaResidueUnit_one]; exact one_ne_zero
      · rw [RHTower.zetaResidueUnit, Function.update_of_ne hks1]
        refine mul_ne_zero (sub_ne_zero.mpr hks1) fun hζk => ?_
        have hle := (RHTower.re_le_zetaZeroAbscissa hζk).trans habs
        linarith
    have han : AnalyticAt ℂ
        (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1) /
          RHTower.zetaResidueUnit ((k : ℂ) * w)) s := by
      have hnum : AnalyticAt ℂ
          (fun w : ℂ => RHTower.zetaResidueUnit w ^ m * ((k : ℂ) * w - 1)) s :=
        ((RHTower.analyticAt_zetaResidueUnit s).pow m).mul
          ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
      have hden : AnalyticAt ℂ (fun w : ℂ => RHTower.zetaResidueUnit ((k : ℂ) * w)) s :=
        (RHTower.analyticAt_zetaResidueUnit ((k : ℂ) * s)).comp (analyticAt_const.mul analyticAt_id)
      exact hnum.div hden hden_ne
    exact han.meromorphicOrderAt_nonneg

/-- **`1 / (2k)` pole-freeness equivalence with `RiemannHypothesis` for every `k ≥ 2` and `m : ℕ`.**
In particular (`m = 1`), `(s - 1) ζ(s) / ζ(k s)` (generating `k`-free integers) is pole-free on
`{Re s > 1 / (2k)}` if and only if `RiemannHypothesis` holds. -/
theorem dilatedPowerQuotient_poleFree_iff_riemannHypothesis {k : ℕ} (hk : 2 ≤ k) (m : ℕ) :
    (∀ s : ℂ, 1 / (2 * (k : ℝ)) < s.re → 0 ≤ meromorphicOrderAt (dilatedPowerQuotient k m) s) ↔
      RiemannHypothesis := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (1 / 2 - 20999 / (24000 * (k : ℝ))) := by
    refine ⟨le_rfl, ?_⟩
    have hlt : 20999 / (24000 * (k : ℝ)) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hruler := (isRuler_dilatedPowerQuotient hk m 0 h0_mem).symm
  dsimp only at hruler
  have hdiv_eq : ((1 : ℝ) / 2 + 0) / (k : ℝ) = 1 / (2 * (k : ℝ)) := by ring
  simp_rw [hdiv_eq] at hruler
  rw [hruler]
  constructor
  · intro hle
    exact SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
      (le_antisymm hle SquareRootThreshold.zetaZeroWidth_nonneg)
  · intro hrh
    rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hrh]

/-! ## 3. Rational-ray classification and all-`k ≥ 2` dilation nonvanishing under a single quartet -/

/-- Under `HasSingleOffLineQuartet ρ₀`, the unconditional sub-`7/8` zero-free half-plane gives
`ρ₀.re ≤ 20999 / 24000`. -/
theorem re_le_sub_seven_eighths_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    ρ₀.re ≤ 20999 / 24000 :=
  (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_sub_quasiRH_strip
    hq.2.1.2.1 hq.2.1.1).2

/-- Strip-zero and coordinate invariants of every point in `zeroQuartetSet ρ₀` under
`HasSingleOffLineQuartet ρ₀`. -/
theorem mem_zeroQuartetSet_invariants {ρ₀ ρ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    (hρ : ρ ∈ zeroQuartetSet ρ₀) :
    riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| = |ρ₀.im| ∧
      (ρ.re = ρ₀.re ∨ ρ.re = 1 - ρ₀.re) := by
  have hne : ρ.re ≠ 1 / 2 := by
    simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact ne_of_gt hq.1
    · rw [Complex.conj_re]; exact ne_of_gt hq.1
    · rw [Complex.sub_re, Complex.one_re]; linarith [hq.1]
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith [hq.1]
  have hcar : ρ ∈ zetaZeroConfig.carrier := by
    have hmem : ρ ∈ {z ∈ zetaZeroConfig.carrier | z.re ≠ 1 / 2} := by
      rwa [hq.2.2]
    exact hmem.1
  refine ⟨hcar.1, hcar.2.1, hcar.2.2, ?_, ?_⟩
  · simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · rfl
    · simp
    · simp
    · simp
  · simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl (Complex.conj_re ρ₀)
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)

/-- **Positive scalar-ray classification under a single off-line quartet.** If
`HasSingleOffLineQuartet ρ₀`, `r > 0`, `r ≠ 1`, and `ζ(r ρ₀) = 0`, then `r ρ₀` is forced onto the
critical line, fixing `r = 1 / (2 Re ρ₀) ∈ [12000 / 20999, 1)`. -/
theorem riemannZeta_pos_real_mul_eq_zero_imp {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) (hζ : riemannZeta ((r : ℂ) * ρ₀) = 0) :
    r = 1 / (2 * ρ₀.re) ∧ 12000 / 20999 ≤ r ∧ r < 1 := by
  set s : ℂ := (r : ℂ) * ρ₀
  have hs_re : s.re = r * ρ₀.re := Complex.re_ofReal_mul r ρ₀
  have hs_im : s.im = r * ρ₀.im := Complex.im_ofReal_mul r ρ₀
  have hρ_pos : 0 < ρ₀.re := by linarith [hq.1]
  have hs_pos : 0 < s.re := by rw [hs_re]; exact mul_pos hr hρ_pos
  have hs_lt1 : s.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
  have hs_car : s ∈ zetaZeroConfig.carrier := ⟨hζ, hs_pos, hs_lt1⟩
  have hs_half : s.re = 1 / 2 := by
    by_contra hne
    have hmem : s ∈ zeroQuartetSet ρ₀ := by
      rw [← hq.2.2]; exact ⟨hs_car, hne⟩
    have him_eq : |s.im| = |ρ₀.im| := (mem_zeroQuartetSet_invariants hq hmem).2.2.2.1
    rw [hs_im, abs_mul, abs_of_pos hr] at him_eq
    have him_pos : 0 < |ρ₀.im| := by linarith [hq.four_lt_abs_im]
    have hr_eq : r = 1 := by nlinarith
    exact hr1 hr_eq
  rw [hs_re] at hs_half
  have hr_eq : r = 1 / (2 * ρ₀.re) := by
    rw [eq_div_iff (by positivity)]
    linarith
  have hhi : ρ₀.re ≤ 20999 / 24000 := re_le_sub_seven_eighths_of_singleQuartet hq
  refine ⟨hr_eq, ?_, ?_⟩
  · rw [hr_eq, le_div_iff₀ (by positivity)]
    linarith
  · rw [hr_eq, div_lt_one (by positivity)]
    linarith [hq.1]

/-- Under `HasSingleOffLineQuartet ρ₀`, `ζ(r ρ₀) ≠ 0` for every `r ∈ (0, 12000/20999) ∪ (1, ∞)`. -/
theorem riemannZeta_pos_real_mul_ne_zero_of_outside {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {r : ℝ} (hr : 0 < r) (hout : r < 12000 / 20999 ∨ 1 < r) :
    riemannZeta ((r : ℂ) * ρ₀) ≠ 0 := by
  intro hζ
  have hr1 : r ≠ 1 := by
    rcases hout with h | h <;> linarith
  obtain ⟨_, hlo, hhi⟩ := riemannZeta_pos_real_mul_eq_zero_imp hq hr hr1 hζ
  rcases hout with h | h <;> linarith

/-- Under `HasSingleOffLineQuartet ρ₀`, at most one `r ∈ ℝ_{>0} \ {1}` satisfies `ζ(r ρ₀) = 0`. -/
theorem subsingleton_other_ray_zeros_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    {r : ℝ | 0 < r ∧ r ≠ 1 ∧ riemannZeta ((r : ℂ) * ρ₀) = 0}.Subsingleton := by
  intro r₁ hr₁ r₂ hr₂
  have h1 := (riemannZeta_pos_real_mul_eq_zero_imp hq hr₁.1 hr₁.2.1 hr₁.2.2).1
  have h2 := (riemannZeta_pos_real_mul_eq_zero_imp hq hr₂.1 hr₂.2.1 hr₂.2.2).1
  exact h1.trans h2.symm

/-- **Irrational-abscissa rational-ray uniqueness.** Under `HasSingleOffLineQuartet ρ₀`, if
`Irrational ρ₀.re`, then `ζ(q ρ₀) ≠ 0` for every positive rational `q ≠ 1`: `ρ₀` is the unique
zero of `riemannZeta` on the entire open rational ray `ℚ_{>0} · ρ₀`. -/
theorem riemannZeta_rat_ray_ne_zero_of_irrational_re {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    (hirr : Irrational ρ₀.re) {q : ℚ} (hq_pos : 0 < q) (hq1 : q ≠ 1) :
    riemannZeta ((q : ℂ) * ρ₀) ≠ 0 := by
  intro hζ
  have hqr_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
  have hqr1 : (q : ℝ) ≠ 1 := by exact_mod_cast hq1
  have hζ' : riemannZeta (((q : ℝ) : ℂ) * ρ₀) = 0 := by simpa using hζ
  obtain ⟨heq, -, -⟩ := riemannZeta_pos_real_mul_eq_zero_imp hq hqr_pos hqr1 hζ'
  have hρ_pos : 0 < ρ₀.re := by linarith [hq.1]
  have hrat : ρ₀.re = ((1 / (2 * q) : ℚ) : ℝ) := by
    push_cast
    have hmul : (q : ℝ) * (2 * ρ₀.re) = 1 := (eq_div_iff (by positivity)).mp heq
    rw [eq_div_iff (by positivity)]
    linarith
  exact hirr ⟨1 / (2 * q), hrat.symm⟩

/-- **Complete `k ≥ 2` root-dilation nonvanishing under a single off-line quartet.** For every
`k ≥ 2` (closing `k ∈ {2, 3, 4, 5, 6}`) and every `ρ ∈ zeroQuartetSet ρ₀`, `ζ(ρ / k) ≠ 0`. -/
theorem riemannZeta_div_nat_ne_zero_of_singleQuartet {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ ∈ zeroQuartetSet ρ₀) {k : ℕ} (hk : 2 ≤ k) :
    riemannZeta (ρ / (k : ℂ)) ≠ 0 := by
  intro hζk
  have hk1 : 1 ≤ k := by omega
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  obtain ⟨_, h0, hlt1, him_eq, -⟩ := mem_zeroQuartetSet_invariants hq hρ
  set s : ℂ := ρ / (k : ℂ)
  have hs_re : s.re = ρ.re / (k : ℝ) := real_div_nat_re ρ hk1
  have hs_im : s.im = ρ.im / (k : ℝ) := real_div_nat_im ρ hk1
  have hs_pos : 0 < s.re := by rw [hs_re]; exact div_pos h0 hk_pos
  have hs_lt_half : s.re < 1 / 2 := by
    rw [hs_re, div_lt_div_iff₀ hk_pos (by norm_num)]
    nlinarith
  have hs_car : s ∈ zetaZeroConfig.carrier := ⟨hζk, hs_pos, by linarith⟩
  have hs_mem : s ∈ zeroQuartetSet ρ₀ := by
    rw [← hq.2.2]
    exact ⟨hs_car, ne_of_lt hs_lt_half⟩
  have hs_im_eq : |s.im| = |ρ₀.im| := (mem_zeroQuartetSet_invariants hq hs_mem).2.2.2.1
  rw [hs_im, abs_div, abs_of_pos hk_pos, him_eq] at hs_im_eq
  have him_pos : 0 < |ρ₀.im| := by linarith [hq.four_lt_abs_im]
  have hmul : |ρ₀.im| = |ρ₀.im| * (k : ℝ) := (div_eq_iff hk_pos.ne').mp hs_im_eq
  nlinarith

/-- **Uncancelled `k`-dilated pole law for every `k ≥ 2` under a single off-line quartet.** For
every `k ≥ 2`, `m : ℕ`, and `ρ ∈ zeroQuartetSet ρ₀`, `((s - 1) ζ(s))^m / ζ(k s)` has an
uncancelled pole of exact order `- ord_ρ ζ < 0` at `s = ρ / k`. -/
theorem dilatedPowerQuotient_neg_order_of_singleQuartet {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ ∈ zeroQuartetSet ρ₀) {k : ℕ} (hk : 2 ≤ k)
    (m : ℕ) :
    meromorphicOrderAt (dilatedPowerQuotient k m) (ρ / (k : ℂ)) =
        - meromorphicOrderAt riemannZeta ρ ∧
      meromorphicOrderAt (dilatedPowerQuotient k m) (ρ / (k : ℂ)) < 0 := by
  obtain ⟨hζ, h0, -, -, -⟩ := mem_zeroQuartetSet_invariants hq hρ
  exact dilatedPowerQuotient_neg_order_of_div_ne_zero (by omega) m h0 hζ
    (riemannZeta_div_nat_ne_zero_of_singleQuartet hq hρ hk)

/-- On the right quartet pair `{ρ₀, conj ρ₀}`, `ζ(k ρ) ≠ 0` holds for every `k ≥ 2`. -/
theorem riemannZeta_nat_mul_right_ne_zero_of_singleQuartet {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ = ρ₀ ∨ ρ = conj ρ₀) {k : ℕ} (hk : 2 ≤ k) :
    riemannZeta ((k : ℂ) * ρ) ≠ 0 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hre : 1 / 2 < ρ.re := by
    rcases hρ with rfl | rfl
    · exact hq.1
    · simpa using hq.1
  have h1 : 1 ≤ ((k : ℂ) * ρ).re := by
    have hm : ((k : ℂ) * ρ).re = (k : ℝ) * ρ.re := by simp
    rw [hm]; nlinarith
  exact riemannZeta_ne_zero_of_one_le_re h1

/-- **Full-quartet integer-multiple nonvanishing for `k ≥ 4`.** Because every `ρ ∈ zeroQuartetSet ρ₀`
satisfies `Re ρ ≥ 1 - 20999/24000 = 3001/24000`, every multiple `k ≥ 4` has `Re(k ρ) > 1/2` and
`|Im(k ρ)| > |Im ρ₀|`, so `ζ(k ρ) ≠ 0`. -/
theorem riemannZeta_nat_mul_ne_zero_of_singleQuartet_ge_four {ρ₀ ρ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) (hρ : ρ ∈ zeroQuartetSet ρ₀) {k : ℕ} (hk : 4 ≤ k) :
    riemannZeta ((k : ℂ) * ρ) ≠ 0 := by
  intro hζk
  have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨_, _, _, him_eq, hre_or⟩ := mem_zeroQuartetSet_invariants hq hρ
  have hhi : ρ₀.re ≤ 20999 / 24000 := re_le_sub_seven_eighths_of_singleQuartet hq
  have hρ_ge : 3001 / 24000 ≤ ρ.re := by
    rcases hre_or with h | h <;> linarith [hq.1]
  set s : ℂ := (k : ℂ) * ρ
  have hs_re : s.re = (k : ℝ) * ρ.re := by simp [s]
  have hs_im : s.im = (k : ℝ) * ρ.im := by simp [s]
  have hs_gt_half : 1 / 2 < s.re := by rw [hs_re]; nlinarith
  have hs_lt1 : s.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζk
  have hs_mem : s ∈ zeroQuartetSet ρ₀ := by
    rw [← hq.2.2]
    exact ⟨⟨hζk, by linarith, hs_lt1⟩, ne_of_gt hs_gt_half⟩
  have hs_im_eq : |s.im| = |ρ₀.im| := (mem_zeroQuartetSet_invariants hq hs_mem).2.2.2.1
  rw [hs_im, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < (k : ℝ)), him_eq] at hs_im_eq
  have him_pos : 0 < |ρ₀.im| := by linarith [hq.four_lt_abs_im]
  nlinarith

#print axioms dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le
#print axioms isRuler_dilatedPowerQuotient
#print axioms dilatedPowerQuotient_poleFree_iff_zetaZeroAbscissa_le_of_seven_le
#print axioms dilatedPowerQuotient_poleFree_iff_riemannHypothesis
#print axioms riemannZeta_pos_real_mul_eq_zero_imp
#print axioms subsingleton_other_ray_zeros_of_singleQuartet
#print axioms riemannZeta_rat_ray_ne_zero_of_irrational_re
#print axioms riemannZeta_div_nat_ne_zero_of_singleQuartet
#print axioms dilatedPowerQuotient_neg_order_of_singleQuartet
#print axioms riemannZeta_nat_mul_ne_zero_of_singleQuartet_ge_four

end GaloisForLFunctions.ZeroForcingCalculus
