import GaloisForLFunctions.ArithmeticCorrespondencePositivity.SymmetricSquareContractionsAndExteriorCounts
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Exterior and height-coupled zero-tax quartet contractions

`SymmetricSquareContractionsAndExteriorCounts` contracts every real off-critical pair `{β, 1 − β}`
of a `CompletedPositiveSystem κ d` onto `s = 1/2` at zero pole cost (`Δκ = 0`), whereas its
single-system contractions of complex off-critical quartets `{1/2 ± a ± iγ}` (`γ ≠ 0`) pay a
boundary pole tax `Δκ = 1` (`a ≤ 1/4`) or `Δκ = 2` (`0 < a < 1/2`).

This module establishes the real-anchor law governing zero-pole-tax quartet cancellations and
constructs the exterior and height-coupled multi-system couplings that eliminate the `Δκ ≥ 1`
pole tax by colliding conjugate phases `(±iγ) ↦ 0` onto the real axis:

* **Post–Widder polar scale positivity and the real-anchor law**
  (`posDef_polarSum_laplaceWeight_nonneg`, `real_anchor_of_posDef_polarSum`,
  `two_mul_le_real_anchor_of_single_ordinate`, `not_isEvenPosDef_quartetPureRatio`). Every finite
  conjugation-symmetric polar sum `G(s) = Σ_{z ∈ S} c(z)/(s − z)` with positive-definite vertical
  real-part sections on `σ > σ₁` has nonnegative scale weight
  `Σ_{z ∈ S} c(z) e^{Re z · t} cos(Im z · t) ≥ 0` for all `t > 0`. Consequently, any zero-tax
  cancellation of a rightmost non-real pole `σ_max + iγ₁` (`c(σ_max + iγ₁) > 0`) must
  simultaneously carry a real pole at `σ_max` of weight `c(σ_max) ≥ c(σ_max + iγ₁)`, and
  `c(σ_max) ≥ 2 c(σ_max + iγ₁)` in the single-ordinate case.
* **Functorial exterior-power curve data and quartet phase elimination**
  (`CurveDatum.exterior`, `detDeg_exterior_eq_exteriorDetDeg`, `quartetCurveDatum_detDeg_linear_pos`,
  `quartetCurveDatum_exterior_two_spectrum`). For every `CurveDatum ι` and `k ≥ 1`, `D.exterior k`
  is a `CurveDatum` on `k`-element subsets at base `q^k` (`Δκ = 0`) whose `detDeg` equals
  `exteriorDetDeg D k`. On any genus-`2` complex quartet datum `quartetCurveDatum q hq r hr θ`,
  `D.exterior 2` eliminates every non-real off-critical eigenvalue, decomposing the six exterior
  eigenvalues into one real off-critical pair `{q r², q r⁻²}` plus four unitary eigenvalues.
* **Archimedean exterior-square divisors and zero-tax contraction**
  (`exteriorTwoScaleTrace_eq_newton`, `exteriorTwoDivisorPoly_quartet`,
  `exteriorTwoDivisorPoly_quartet_contract`). In continuous scale `t`, the exterior-square trace
  `(z_ρ(t)² − z_ρ(2t))/2` kills the diagonal `2ρ_i − 1/2` and factors the exterior-square divisor
  of `{1/2 ± a ± iγ}` into `realPairPoly (1/2 + 2a) s · (s − 1/2)² ((s − 1/2)² + 4γ²)`, which
  contracts onto `Re s = 1/2` via `midpointSymSquare (1/2 + 2a)` at `Δκ = 0` (`0 < a < 1/4`).
* **Full-strip coupled symmetric-square contractions and height-coupled positive systems**
  (`coupledQuartetSymSquare`, `isEvenPosDef_coupledQuartetSymSquare`, `HeightCoupledSystem`,
  `CompletedPositiveSystem.heightCouple`, `HeightCoupledSystem.contractCollidedQuartet`,
  `HeightCoupledSystem.archimedean_budget`,
  `CompletedPositiveSystem.contractOrdinateQuartets_heightCoupled`,
  `HeightCoupledSystem.exists_real_offCritical_free`). Attaining the sharp `2 : 1` real-anchor
  bound, `coupledQuartetSymSquare b a γ` has nonnegative Laplace density across the entire strip
  `0 < a ≤ b < 1/2` at `Δκ = 0`. Lifting any `CompletedPositiveSystem κ d` to
  `F_γ(s) = F(s)² F(s + iγ) F(s − iγ)` (`HeightCoupledSystem (2κ) κ d γ`) collides `(ρ₀, ρ̄₀)` onto
  `1/2 + a ∈ ℝ` with multiplicity `2`, contracts arbitrarily many ordinate-`γ` quartets at
  `Δκ₀ = 0, Δκ_γ = 0` under a fixed archimedean budget, and terminates in finitely many steps.
-/

open Complex Polynomial Finset Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri MultiplicativePositivityGeometry StripBochnerWeilForcing HTGeometry

/-! ### 1. Post–Widder polar scale weights and the real-anchor law -/

/-- Finite polar sum `G(s) = Σ_{z ∈ S} c(z)/(s − z)` with real weights `c : ℂ → ℝ`. -/
def polarSum (S : Finset ℂ) (c : ℂ → ℝ) (s : ℂ) : ℂ :=
  ∑ z ∈ S, (c z : ℂ) / (s - z)

/-- Scale-`t` Laplace cosine weight `w(t) = Σ_{z ∈ S} c(z) e^{Re z · t} cos(Im z · t)` of a finite
polar sum. -/
def polarScaleWeight (S : Finset ℂ) (c : ℂ → ℝ) (t : ℝ) : ℝ :=
  ∑ z ∈ S, c z * Real.exp (z.re * t) * Real.cos (z.im * t)

private theorem polarSum_iterate_deriv_eqOn {S : Finset ℂ} {c : ℂ → ℝ} {a : ℝ}
    (hSa : ∀ z ∈ S, z.re ≤ a) (n : ℕ) :
    EqOn (deriv^[n] (polarSum S c))
      (fun s : ℂ => (-1 : ℂ) ^ n * (n.factorial : ℂ) *
        ∑ z ∈ S, (c z : ℂ) * ((s - z) ^ (n + 1))⁻¹)
      {s : ℂ | a < s.re} := by
  have hU : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  induction n with
  | zero =>
      intro s _
      simp [polarSum, div_eq_mul_inv]
  | succ n ih =>
      intro s hs
      have hs_re : a < s.re := hs
      rw [Function.iterate_succ_apply']
      have hev : deriv^[n] (polarSum S c) =ᶠ[𝓝 s]
          fun w : ℂ => (-1 : ℂ) ^ n * (n.factorial : ℂ) *
            ∑ z ∈ S, (c z : ℂ) * ((w - z) ^ (n + 1))⁻¹ :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun w hw => ih hw
      rw [hev.deriv_eq]
      have hterm : ∀ z ∈ S, HasDerivAt
          (fun w : ℂ => (c z : ℂ) * ((w - z) ^ (n + 1))⁻¹)
          (-(c z : ℂ) * ((n + 1 : ℕ) : ℂ) * ((s - z) ^ (n + 2))⁻¹) s := by
        intro z hz
        have hsz : s - z ≠ 0 := fun h0 => by
          have := congrArg Complex.re h0; simp at this; linarith [hSa z hz]
        have hd1 : HasDerivAt (fun w : ℂ => (w - z) ^ (n + 1))
            (((n + 1 : ℕ) : ℂ) * (s - z) ^ n * 1) s :=
          ((hasDerivAt_id s).sub_const z).pow (n + 1)
        have hd2 := (hd1.inv (pow_ne_zero (n + 1) hsz)).const_mul (c z : ℂ)
        refine hd2.congr_deriv ?_
        have hpow1 : (s - z) ^ (n + 1) ≠ 0 := pow_ne_zero _ hsz
        have hpow2 : (s - z) ^ (n + 2) ≠ 0 := pow_ne_zero _ hsz
        field_simp [hpow1, hpow2]
        ring
      have hsum_d := (HasDerivAt.sum hterm).const_mul ((-1 : ℂ) ^ n * (n.factorial : ℂ))
      rw [hsum_d.deriv]
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring

private theorem tendsto_inv_one_sub_div_pow_succ (w : ℂ) :
    Tendsto (fun n : ℕ => ((1 - w / (n : ℂ))⁻¹) ^ (n + 1)) atTop (𝓝 (Complex.exp w)) := by
  have hexp : Tendsto (fun n : ℕ => (1 + (-w) / (n : ℂ)) ^ n) atTop (𝓝 (Complex.exp (-w))) :=
    Complex.tendsto_one_add_div_pow_exp (-w)
  have hinv_exp : Tendsto (fun n : ℕ => ((1 + (-w) / (n : ℂ)) ^ n)⁻¹) atTop
      (𝓝 ((Complex.exp (-w))⁻¹)) :=
    hexp.inv₀ (Complex.exp_ne_zero (-w))
  have h1 : Tendsto (fun n : ℕ => (1 - w / (n : ℂ))⁻¹) atTop (𝓝 ((1 - 0 : ℂ)⁻¹)) := by
    have hdiv : Tendsto (fun n : ℕ => w / (n : ℂ)) atTop (𝓝 0) := by
      have hn : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := by
        have hr : Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
          (Complex.continuous_ofReal.tendsto 0).comp
            (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
        simpa using hr
      simpa [div_eq_mul_inv] using hn.const_mul w
    exact (tendsto_const_nhds.sub hdiv).inv₀ (by norm_num)
  have hprod := hinv_exp.mul h1
  have hlim : (Complex.exp (-w))⁻¹ * (1 - 0 : ℂ)⁻¹ = Complex.exp w := by
    rw [Complex.exp_neg, inv_inv, sub_zero, inv_one, mul_one]
  rw [hlim] at hprod
  refine hprod.congr fun n => ?_
  have heq : 1 + (-w) / (n : ℂ) = 1 - w / (n : ℂ) := by ring
  rw [heq, pow_succ, inv_pow]

/-- **Post–Widder scale-weight positivity for polar sums.** If `S ⊂ ℂ` and `c : ℂ → ℝ` are
conjugation-symmetric and `u ↦ Re G(σ + iu)` is positive definite on `σ > σ₁` (`∀ z ∈ S, Re z ≤ σ₁`),
then `polarScaleWeight S c t ≥ 0` for all `t > 0`. -/
theorem posDef_polarSum_laplaceWeight_nonneg {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S)
    (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ polarScaleWeight S c t := by
  set a : ℝ := max σ₁ 1
  have ha1 : 1 ≤ a := le_max_right σ₁ 1
  have hSa : ∀ z ∈ S, z.re ≤ a := fun z hz => (hS_re z hz).trans (le_max_left σ₁ 1)
  set U : Set ℂ := {s : ℂ | a < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hG_diff : DifferentiableOn ℂ (polarSum S c) U := by
    intro s hs
    change a < s.re at hs
    refine DifferentiableWithinAt.sum fun z hz => ?_
    have hsz : s - z ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith [hSa z hz]
    exact ((differentiableAt_const (c z : ℂ)).div
      (differentiableAt_id.sub_const z) hsz).differentiableWithinAt
  have hG_real : ∀ x : ℝ, a < x → (polarSum S c (x : ℂ)).im = 0 := by
    intro x _
    refine Complex.conj_eq_iff_im.mp ?_
    unfold polarSum
    rw [map_sum]
    refine Finset.sum_nbij' (fun z => conj z) (fun z => conj z)
      (fun z hz => hS_conj z hz) (fun z hz => hS_conj z hz)
      (fun z _ => Complex.conj_conj z) (fun z _ => Complex.conj_conj z) fun z hz => ?_
    simp only [map_div₀, Complex.conj_ofReal, map_sub, hc_conj z hz]
  have heven : ∀ j : ℕ, ∀ x : ℝ, a < x → 0 ≤ ((deriv^[2 * j] (polarSum S c)) (x : ℂ)).re :=
    fun j x hx => re_iterate_deriv_two_mul_nonneg hG_diff
      (fun σ hσ => hpd σ ((le_max_left σ₁ 1).trans_lt hσ)) j hx
  have hgrowth : ∀ x : ℝ, a + 1 ≤ x →
      (polarSum S c (x : ℂ)).re ≤ (∑ z ∈ S, |c z|) * Real.sqrt x := by
    intro x hx
    have hsum_nn : 0 ≤ ∑ z ∈ S, |c z| := Finset.sum_nonneg fun z _ => abs_nonneg (c z)
    have h1x : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
    calc (polarSum S c (x : ℂ)).re
        ≤ ‖polarSum S c (x : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ∑ z ∈ S, ‖(c z : ℂ) / ((x : ℂ) - z)‖ := norm_sum_le S _
      _ ≤ ∑ z ∈ S, |c z| := by
          refine Finset.sum_le_sum fun z hz => ?_
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
          have hden : 1 ≤ ‖(x : ℂ) - z‖ := by
            calc (1 : ℝ) ≤ x - z.re := by linarith [hSa z hz]
              _ = ((x : ℂ) - z).re := by simp
              _ ≤ ‖(x : ℂ) - z‖ := Complex.re_le_norm _
          exact div_le_self (abs_nonneg _) hden
      _ ≤ (∑ z ∈ S, |c z|) * Real.sqrt x := le_mul_of_one_le_right hsum_nn h1x
  have hodd : ∀ j : ℕ, ∀ x : ℝ, a < x → ((deriv^[2 * j + 1] (polarSum S c)) (x : ℂ)).re ≤ 0 :=
    tower_odd_nonpos
      (T := fun k x => ((deriv^[k] (polarSum S c)) (x : ℂ)).re)
      (fun k x hx => hasDerivAt_re_iterate_deriv hU hG_diff k (by simpa [U] using hx))
      heven hgrowth
  have hcm : ∀ n : ℕ, ∀ x : ℝ, a < x →
      0 ≤ (-1 : ℝ) ^ n * ((deriv^[n] (polarSum S c)) (x : ℂ)).re := by
    intro n x hx
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by omega, Even.neg_one_pow ⟨j, by omega⟩, one_mul]
      exact heven j x hx
    · rw [Odd.neg_one_pow ⟨j, rfl⟩, neg_one_mul, neg_nonneg]
      exact hodd j x hx
  have hlim : Tendsto
      (fun n : ℕ => (∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1)).re)
      atTop (𝓝 (polarScaleWeight S c t)) := by
    have hc_lim : Tendsto
        (fun n : ℕ => ∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1))
        atTop (𝓝 (∑ z ∈ S, (c z : ℂ) * Complex.exp (z * (t : ℂ)))) :=
      tendsto_finset_sum S fun z _ =>
        (tendsto_inv_one_sub_div_pow_succ (z * (t : ℂ))).const_mul (c z : ℂ)
    have hre_lim := (Complex.continuous_re.tendsto _).comp hc_lim
    have htarget : (∑ z ∈ S, (c z : ℂ) * Complex.exp (z * (t : ℂ))).re =
        polarScaleWeight S c t := by
      unfold polarScaleWeight
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Complex.re_ofReal_mul, Complex.exp_re]
      have hre_zt : (z * (t : ℂ)).re = z.re * t := by simp
      have him_zt : (z * (t : ℂ)).im = z.im * t := by simp
      rw [hre_zt, him_zt, mul_assoc]
    rwa [htarget] at hre_lim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil (a * t) + 1)] with n hn
  have hn_pos : 0 < n := by omega
  have hn_gt : a * t < (n : ℝ) := by
    have hceil : a * t ≤ (Nat.ceil (a * t) : ℝ) := Nat.le_ceil (a * t)
    have hn_cast : (Nat.ceil (a * t) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set xn : ℝ := (n : ℝ) / t
  have hxn_gt : a < xn := (lt_div_iff₀ ht).mpr hn_gt
  have hxn_pos : 0 < xn := by linarith
  have hcm_n := hcm n xn hxn_gt
  have hderiv_eq := polarSum_iterate_deriv_eqOn hSa n (show (xn : ℂ) ∈ U by simp [U, hxn_gt])
  have hscale_pos : 0 ≤ xn ^ (n + 1) / (n.factorial : ℝ) :=
    div_nonneg (pow_nonneg hxn_pos.le _) (Nat.cast_nonneg _)
  have hnonneg := mul_nonneg hscale_pos hcm_n
  have hident : xn ^ (n + 1) / (n.factorial : ℝ) *
      ((-1 : ℝ) ^ n * ((deriv^[n] (polarSum S c)) (xn : ℂ)).re) =
      (∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1)).re := by
    rw [hderiv_eq]
    have hcast : ((xn ^ (n + 1) / (n.factorial : ℝ) * (-1 : ℝ) ^ n : ℝ) : ℂ) *
        ((-1 : ℂ) ^ n * (n.factorial : ℂ) *
          ∑ z ∈ S, (c z : ℂ) * (((xn : ℂ) - z) ^ (n + 1))⁻¹) =
        ∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1) := by
      have hfac_ne : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hxnC : (xn : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxn_pos.ne'
      have hsign : ((-1 : ℝ) ^ n : ℂ) * (-1 : ℂ) ^ n = 1 := by
        push_cast; rw [← mul_pow]; norm_num
      have hpref : ((xn ^ (n + 1) / (n.factorial : ℝ) * (-1 : ℝ) ^ n : ℝ) : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ)) = (xn : ℂ) ^ (n + 1) := by
        push_cast
        calc (xn : ℂ) ^ (n + 1) / (n.factorial : ℂ) * (-1 : ℂ) ^ n *
              ((-1 : ℂ) ^ n * (n.factorial : ℂ))
            = (xn : ℂ) ^ (n + 1) * (((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
                ((n.factorial : ℂ) / (n.factorial : ℂ))) := by ring
          _ = (xn : ℂ) ^ (n + 1) := by
              rw [show (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 from by rw [← mul_pow]; norm_num,
                  div_self hfac_ne, mul_one, mul_one]
      rw [← mul_assoc, hpref, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z hz => ?_
      have hxz : (xn : ℂ) - z ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; linarith [hSa z hz]
      have hratio : ((xn : ℂ) - z) / (xn : ℂ) = 1 - z * (t : ℂ) / (n : ℂ) := by
        dsimp [xn]; push_cast; field_simp [hnC, htC]
      calc (xn : ℂ) ^ (n + 1) * ((c z : ℂ) * (((xn : ℂ) - z) ^ (n + 1))⁻¹)
          = (c z : ℂ) * ((((xn : ℂ) - z) / (xn : ℂ))⁻¹) ^ (n + 1) := by
              rw [inv_div, div_pow, inv_eq_one_div]
              field_simp [pow_ne_zero (n + 1) hxz, pow_ne_zero (n + 1) hxnC]
        _ = (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1) := by rw [hratio]
    have hre_lhs : (((xn ^ (n + 1) / (n.factorial : ℝ) * (-1 : ℝ) ^ n : ℝ) : ℂ) *
        ((-1 : ℂ) ^ n * (n.factorial : ℂ) *
          ∑ z ∈ S, (c z : ℂ) * (((xn : ℂ) - z) ^ (n + 1))⁻¹)).re =
        xn ^ (n + 1) / (n.factorial : ℝ) *
          ((-1 : ℝ) ^ n * ((deriv^[n] (polarSum S c)) (xn : ℂ)).re) := by
      rw [hderiv_eq, Complex.re_ofReal_mul]
      ring
    rw [← hcast, hre_lhs]
  rwa [← hident]

private theorem tendsto_avg_cos_zero {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T), Real.cos (ω * t)) atTop (𝓝 0) := by
  have hint_eq : ∀ T : ℝ, ∫ t in T..(2 * T), Real.cos (ω * t) =
      Real.sin (ω * (2 * T)) / ω - Real.sin (ω * T) / ω := by
    intro T
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Real.sin (ω * x) / ω)
      (fun x _ => ?_) (Continuous.intervalIntegrable (by fun_prop) T (2 * T))
    exact (((hasDerivAt_id x).const_mul ω).sin.div_const ω).congr_deriv (by field_simp [hω])
  refine squeeze_zero_norm' ?_
    ((tendsto_inv_atTop_zero.const_mul (2 / |ω|)).congr fun T => by ring)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [hint_eq T, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hT)]
  have h1 : |Real.sin (ω * (2 * T)) / ω - Real.sin (ω * T) / ω| ≤ 2 / |ω| := by
    rw [← sub_div, abs_div]
    refine div_le_div_of_nonneg_right ?_ (abs_nonneg ω)
    calc |Real.sin (ω * (2 * T)) - Real.sin (ω * T)|
        ≤ |Real.sin (ω * (2 * T))| + |Real.sin (ω * T)| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  exact mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hT).le

/-- **General multi-ordinate real-anchor law.** If a conjugation-symmetric polar sum has
positive-definite vertical sections on `σ > σ₁`, no nonzero poles to the right of `σ_max`, and a
positive weight `c(z₁) > 0` at a non-real rightmost point `z₁ = σ_max + iγ₁` (`γ₁ ≠ 0`), then
`σ_max ∈ S` and `c(z₁) ≤ c(σ_max)`. -/
theorem real_anchor_of_posDef_polarSum {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ σ_max γ₁ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S)
    (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re₁ : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ_max)
    (hγ₁ : γ₁ ≠ 0)
    (hz₁_mem : ((σ_max : ℂ) + (γ₁ : ℂ) * I) ∈ S)
    (hz₁_pos : 0 < c ((σ_max : ℂ) + (γ₁ : ℂ) * I)) :
    (σ_max : ℂ) ∈ S ∧ c ((σ_max : ℂ) + (γ₁ : ℂ) * I) ≤ c (σ_max : ℂ) := by
  classical
  set z₁ : ℂ := (σ_max : ℂ) + (γ₁ : ℂ) * I
  have hconj_z₁ : conj z₁ = (σ_max : ℂ) - (γ₁ : ℂ) * I := by
    simp [z₁]
  have hz₁_conj_mem : conj z₁ ∈ S := hS_conj z₁ hz₁_mem
  have hz₁_ne_conj : z₁ ≠ conj z₁ := by
    intro h
    have := congrArg Complex.im h
    simp [z₁] at this
    exact hγ₁ this
  have hw_nn : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t :=
    fun t ht => posDef_polarSum_laplaceWeight_nonneg hS_conj hc_conj hS_re₁ hpd ht
  let termVal : ℂ → ℝ := fun z =>
    if z = (σ_max : ℂ) then c z
    else if z = z₁ ∨ z = conj z₁ then -(c z / 2)
    else 0
  have hterm_lim : ∀ z ∈ S, Tendsto
      (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
        c z * Real.exp ((z.re - σ_max) * t) * Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t)))
      atTop (𝓝 (termVal z)) := by
    intro z hz
    by_cases hcz : c z = 0
    · have htv : termVal z = 0 := by simp [termVal, hcz]
      rw [htv]
      simpa [hcz] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
    have hz_le : z.re ≤ σ_max := hmax z hz hcz
    rcases lt_or_eq_of_le hz_le with hz_lt | hz_eq
    · have hne_real : z ≠ (σ_max : ℂ) := fun h => by subst h; simp at hz_lt
      have hne_z1 : z ≠ z₁ := fun h => by subst h; simp [z₁] at hz_lt
      have hne_cz1 : z ≠ conj z₁ := fun h => by subst h; simp [z₁] at hz_lt
      have htv : termVal z = 0 := by simp [termVal, hne_real, hne_z1, hne_cz1]
      rw [htv]
      have hdec : Tendsto (fun T : ℝ => 2 * |c z| * Real.exp ((z.re - σ_max) * T))
          atTop (𝓝 0) := by
        simpa [mul_zero] using
          (tendsto_exp_atTop_nhds_zero_of_lt_zero (by linarith : z.re - σ_max < 0)).const_mul
            (2 * |c z|)
      refine squeeze_zero_norm' ?_ hdec
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hT)]
      have hint_le : |∫ t in T..(2 * T),
          c z * Real.exp ((z.re - σ_max) * t) * Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t))| ≤
          (2 * |c z| * Real.exp ((z.re - σ_max) * T)) * (2 * T - T) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        refine le_trans (norm_setIntegral_le_of_norm_le_const (s := Ioc T (2 * T))
          (C := 2 * |c z| * Real.exp ((z.re - σ_max) * T))
          (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_) ?_
        · intro t ht
          rw [mem_Ioc] at ht
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp : Real.exp ((z.re - σ_max) * t) ≤ Real.exp ((z.re - σ_max) * T) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1.le (by linarith))
          have h1cos : |1 - Real.cos (γ₁ * t)| ≤ 2 := by
            have := Real.abs_cos_le_one (γ₁ * t)
            rw [abs_le] at this ⊢
            exact ⟨by linarith, by linarith⟩
          calc |c z| * Real.exp ((z.re - σ_max) * t) * |Real.cos (z.im * t)| *
                |1 - Real.cos (γ₁ * t)|
              ≤ |c z| * Real.exp ((z.re - σ_max) * T) * 1 * 2 := by
                gcongr
                exact Real.abs_cos_le_one _
            _ = 2 * |c z| * Real.exp ((z.re - σ_max) * T) := by ring
        · rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]; ring_nf; exact le_rfl
      calc T⁻¹ * |∫ t in T..(2 * T),
            c z * Real.exp ((z.re - σ_max) * t) * Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t))|
          ≤ T⁻¹ * ((2 * |c z| * Real.exp ((z.re - σ_max) * T)) * T) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hT).le
            simpa [show 2 * T - T = T by ring] using hint_le
        _ = 2 * |c z| * Real.exp ((z.re - σ_max) * T) := by field_simp [hT.ne']
    · -- On the line `z.re = σ_max`, `exp((z.re - σ_max) * t) = 1`.
      by_cases hz_im0 : z.im = 0
      · have hz_real : z = (σ_max : ℂ) := by
          apply Complex.ext <;> simp [hz_eq, hz_im0]
        subst hz_real
        have htv : termVal (σ_max : ℂ) = c (σ_max : ℂ) := by simp [termVal]
        rw [htv]
        have hcos_lim := (tendsto_avg_cos_zero hγ₁).const_mul (c (σ_max : ℂ))
        have h1_lim : Tendsto (fun T : ℝ => c (σ_max : ℂ) -
            c (σ_max : ℂ) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos (γ₁ * t)))
            atTop (𝓝 (c (σ_max : ℂ) - 0)) :=
          tendsto_const_nhds.sub (by simpa [mul_zero] using hcos_lim)
        rw [sub_zero] at h1_lim
        refine h1_lim.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
        have hfn : (fun t : ℝ => c (σ_max : ℂ) * Real.exp (((σ_max : ℂ).re - σ_max) * t) *
            Real.cos ((σ_max : ℂ).im * t) * (1 - Real.cos (γ₁ * t))) =
            fun t : ℝ => c (σ_max : ℂ) - c (σ_max : ℂ) * Real.cos (γ₁ * t) := by
          funext t; simp; ring
        rw [hfn, intervalIntegral.integral_sub intervalIntegrable_const
          ((Continuous.intervalIntegrable (by fun_prop) T (2 * T)).const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        simp only [smul_eq_mul]
        field_simp [hT.ne']
        ring
      · by_cases hz_pair : z = z₁ ∨ z = conj z₁
        · have hne_real : z ≠ (σ_max : ℂ) := fun h => hz_im0 (by rw [h]; simp)
          have htv : termVal z = -(c z / 2) := by simp [termVal, hne_real, hz_pair]
          rw [htv]
          have hcos_eq : ∀ t : ℝ, Real.cos (z.im * t) = Real.cos (γ₁ * t) := by
            intro t
            rcases hz_pair with rfl | rfl
            · simp [z₁]
            · simp [z₁, Real.cos_neg]
          have htrig : ∀ t : ℝ, c z * Real.exp ((z.re - σ_max) * t) *
              Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t)) =
              -(c z / 2) + c z * Real.cos (γ₁ * t) - (c z / 2) * Real.cos ((2 * γ₁) * t) := by
            intro t
            rw [hz_eq, sub_self, zero_mul, Real.exp_zero, mul_one, hcos_eq t]
            have hc2 := Real.cos_two_mul (γ₁ * t)
            rw [show 2 * (γ₁ * t) = (2 * γ₁) * t by ring] at hc2
            linarith
          have hl1 := (tendsto_avg_cos_zero hγ₁).const_mul (c z)
          have hl2 := (tendsto_avg_cos_zero (mul_ne_zero two_ne_zero hγ₁)).const_mul (c z / 2)
          have hcomb : Tendsto (fun T : ℝ => -(c z / 2) +
              c z * (T⁻¹ * ∫ t in T..(2 * T), Real.cos (γ₁ * t)) -
              (c z / 2) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos ((2 * γ₁) * t)))
              atTop (𝓝 (-(c z / 2) + 0 - 0)) :=
            (tendsto_const_nhds.add (by simpa [mul_zero] using hl1)).sub
              (by simpa [mul_zero] using hl2)
          simp only [add_zero, sub_zero] at hcomb
          refine hcomb.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
          simp_rw [htrig]
          have hi_c1 : IntervalIntegrable (fun t : ℝ => c z * Real.cos (γ₁ * t)) volume T (2 * T) :=
            (Continuous.intervalIntegrable (by fun_prop) T (2 * T)).const_mul _
          have hi_c2 : IntervalIntegrable
              (fun t : ℝ => (c z / 2) * Real.cos ((2 * γ₁) * t)) volume T (2 * T) :=
            (Continuous.intervalIntegrable (by fun_prop) T (2 * T)).const_mul _
          rw [intervalIntegral.integral_sub (intervalIntegrable_const.add hi_c1) hi_c2,
              intervalIntegral.integral_add intervalIntegrable_const hi_c1,
              intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
          simp only [smul_eq_mul]
          field_simp [hT.ne']
          ring
        · -- Remaining non-resonant imaginary parts on `z.re = σ_max`.
          have hne_real : z ≠ (σ_max : ℂ) := fun h => hz_im0 (by rw [h]; simp)
          have htv : termVal z = 0 := by simp [termVal, hne_real, hz_pair]
          rw [htv]
          have him_ne_p : z.im - γ₁ ≠ 0 := by
            intro h
            apply hz_pair; left
            apply Complex.ext <;> simp [z₁, hz_eq]; linarith
          have him_ne_m : z.im + γ₁ ≠ 0 := by
            intro h
            apply hz_pair; right
            apply Complex.ext <;> simp [z₁, hz_eq]; linarith
          have htrig : ∀ t : ℝ, c z * Real.exp ((z.re - σ_max) * t) *
              Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t)) =
              c z * Real.cos (z.im * t) -
                (c z / 2) * Real.cos ((z.im - γ₁) * t) -
                (c z / 2) * Real.cos ((z.im + γ₁) * t) := by
            intro t
            rw [hz_eq, sub_self, zero_mul, Real.exp_zero, mul_one]
            have hcs := Real.cos_sub (z.im * t) (γ₁ * t)
            have hca := Real.cos_add (z.im * t) (γ₁ * t)
            rw [show z.im * t - γ₁ * t = (z.im - γ₁) * t by ring] at hcs
            rw [show z.im * t + γ₁ * t = (z.im + γ₁) * t by ring] at hca
            linarith
          have hl0 := (tendsto_avg_cos_zero hz_im0).const_mul (c z)
          have hl1 := (tendsto_avg_cos_zero him_ne_p).const_mul (c z / 2)
          have hl2 := (tendsto_avg_cos_zero him_ne_m).const_mul (c z / 2)
          have hcomb : Tendsto (fun T : ℝ =>
              c z * (T⁻¹ * ∫ t in T..(2 * T), Real.cos (z.im * t)) -
              (c z / 2) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos ((z.im - γ₁) * t)) -
              (c z / 2) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos ((z.im + γ₁) * t)))
              atTop (𝓝 (0 - 0 - 0)) :=
            ((by simpa [mul_zero] using hl0 : Tendsto _ _ (𝓝 0)).sub
              (by simpa [mul_zero] using hl1)).sub (by simpa [mul_zero] using hl2)
          simp only [sub_zero] at hcomb
          refine hcomb.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
          simp_rw [htrig]
          have hi0 : IntervalIntegrable (fun t : ℝ => c z * Real.cos (z.im * t)) volume T (2 * T) :=
            (Continuous.intervalIntegrable (by fun_prop) T (2 * T)).const_mul _
          have hi1 : IntervalIntegrable
              (fun t : ℝ => (c z / 2) * Real.cos ((z.im - γ₁) * t)) volume T (2 * T) :=
            (Continuous.intervalIntegrable (by fun_prop) T (2 * T)).const_mul _
          have hi2 : IntervalIntegrable
              (fun t : ℝ => (c z / 2) * Real.cos ((z.im + γ₁) * t)) volume T (2 * T) :=
            (Continuous.intervalIntegrable (by fun_prop) T (2 * T)).const_mul _
          rw [intervalIntegral.integral_sub (hi0.sub hi1) hi2,
              intervalIntegral.integral_sub hi0 hi1,
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
          ring
  have hsum_lim : Tendsto
      (fun T : ℝ => ∑ z ∈ S, T⁻¹ * ∫ t in T..(2 * T),
        c z * Real.exp ((z.re - σ_max) * t) * Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t)))
      atTop (𝓝 (∑ z ∈ S, termVal z)) :=
    tendsto_finset_sum S hterm_lim
  have hsum_nn : 0 ≤ ∑ z ∈ S, termVal z := by
    refine ge_of_tendsto hsum_lim ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finset_sum
      (fun z _ => Continuous.intervalIntegrable (by fun_prop) T (2 * T))]
    refine mul_nonneg (inv_pos.mpr hT).le ?_
    refine intervalIntegral.integral_nonneg (by linarith) fun t ht => ?_
    have ht_pos : 0 < t := lt_of_lt_of_le hT ht.1
    have heq_sum : (∑ z ∈ S, c z * Real.exp ((z.re - σ_max) * t) *
        Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t))) =
        Real.exp (-σ_max * t) * polarScaleWeight S c t * (1 - Real.cos (γ₁ * t)) := by
      unfold polarScaleWeight
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun z _ => ?_
      have hexp : Real.exp ((z.re - σ_max) * t) = Real.exp (-σ_max * t) * Real.exp (z.re * t) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp]; ring
    rw [heq_sum]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (hw_nn t ht_pos))
      (sub_nonneg.mpr (Real.cos_le_one _))
  -- Evaluate `∑ z ∈ S, termVal z = (if σ_max ∈ S then c σ_max else 0) - c z₁`.
  have hsum_eval : ∑ z ∈ S, termVal z =
      (if (σ_max : ℂ) ∈ S then c (σ_max : ℂ) else 0) - c z₁ := by
    have hz1_ne_r : z₁ ≠ (σ_max : ℂ) := fun h => hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; exact this)
    have hcz1_ne_r : conj z₁ ≠ (σ_max : ℂ) := fun h => hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; linarith)
    have hsplit1 := Finset.add_sum_erase S termVal hz₁_mem
    have hcz1_er1 : conj z₁ ∈ S.erase z₁ := Finset.mem_erase.mpr ⟨hz₁_ne_conj.symm, hz₁_conj_mem⟩
    have hsplit2 := Finset.add_sum_erase (S.erase z₁) termVal hcz1_er1
    rw [← hsplit1, ← hsplit2]
    have htv_z1 : termVal z₁ = -(c z₁ / 2) := by simp [termVal, hz1_ne_r]
    have htv_cz1 : termVal (conj z₁) = -(c z₁ / 2) := by
      simp [termVal, hcz1_ne_r, hc_conj z₁ hz₁_mem]
    have hrest : ∑ z ∈ (S.erase z₁).erase (conj z₁), termVal z =
        if (σ_max : ℂ) ∈ S then c (σ_max : ℂ) else 0 := by
      by_cases hmem : (σ_max : ℂ) ∈ S
      · have hmem2 : (σ_max : ℂ) ∈ (S.erase z₁).erase (conj z₁) :=
          Finset.mem_erase.mpr ⟨hcz1_ne_r.symm, Finset.mem_erase.mpr ⟨hz1_ne_r.symm, hmem⟩⟩
        rw [if_pos hmem, ← Finset.add_sum_erase _ termVal hmem2]
        have htv_r : termVal (σ_max : ℂ) = c (σ_max : ℂ) := by simp [termVal]
        have hzero : ∑ z ∈ ((S.erase z₁).erase (conj z₁)).erase (σ_max : ℂ), termVal z = 0 := by
          refine Finset.sum_eq_zero fun z hz => ?_
          simp only [Finset.mem_erase] at hz
          simp [termVal, hz.1, hz.2.2.1, hz.2.1]
        rw [htv_r, hzero, add_zero]
      · rw [if_neg hmem]
        refine Finset.sum_eq_zero fun z hz => ?_
        simp only [Finset.mem_erase] at hz
        have hzr : z ≠ (σ_max : ℂ) := fun h => hmem (h ▸ hz.2.2.2)
        simp [termVal, hzr, hz.2.1, hz.1]
    rw [htv_z1, htv_cz1, hrest]
    ring
  rw [hsum_eval] at hsum_nn
  by_cases hmem : (σ_max : ℂ) ∈ S
  · rw [if_pos hmem] at hsum_nn
    exact ⟨hmem, by linarith⟩
  · rw [if_neg hmem] at hsum_nn
    linarith

/-- **Sharp `2 : 1` single-ordinate real-anchor law.** When `z₁ = σ_max + iγ₁` and `conj z₁` are
the only non-real nonzero poles on the rightmost vertical line `Re z = σ_max`, positive definiteness
of the vertical sections forces `σ_max ∈ S` and `2 * c(z₁) ≤ c(σ_max)`. -/
theorem two_mul_le_real_anchor_of_single_ordinate {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ σ_max γ₁ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S)
    (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re₁ : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σ_max)
    (hsingle : ∀ z ∈ S, c z ≠ 0 → z.re = σ_max → z.im = 0 ∨ z.im = γ₁ ∨ z.im = -γ₁)
    (hγ₁ : γ₁ ≠ 0)
    (hz₁_mem : ((σ_max : ℂ) + (γ₁ : ℂ) * I) ∈ S)
    (hz₁_pos : 0 < c ((σ_max : ℂ) + (γ₁ : ℂ) * I)) :
    (σ_max : ℂ) ∈ S ∧ 2 * c ((σ_max : ℂ) + (γ₁ : ℂ) * I) ≤ c (σ_max : ℂ) := by
  classical
  set z₁ : ℂ := (σ_max : ℂ) + (γ₁ : ℂ) * I
  have hz₁_conj_mem : conj z₁ ∈ S := hS_conj z₁ hz₁_mem
  have hz₁_ne_conj : z₁ ≠ conj z₁ := fun h =>
    hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; exact this)
  have hw_nn : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t :=
    fun t ht => posDef_polarSum_laplaceWeight_nonneg hS_conj hc_conj hS_re₁ hpd ht
  let tk : ℕ → ℝ := fun k => ((2 * (k : ℝ) + 1) * Real.pi) / |γ₁|
  have htk_pos : ∀ k : ℕ, 0 < tk k := fun k => by
    dsimp [tk]; exact div_pos (mul_pos (by positivity) Real.pi_pos) (abs_pos.mpr hγ₁)
  have htk_top : Tendsto tk atTop atTop := by
    have hlin : Tendsto (fun k : ℕ => (2 * (k : ℝ) + 1) * (Real.pi / |γ₁|)) atTop atTop :=
      Filter.Tendsto.atTop_mul_const (div_pos Real.pi_pos (abs_pos.mpr hγ₁))
        (tendsto_atTop_add_const_right atTop 1
          (Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop))
    exact hlin.congr fun k => by dsimp [tk]; ring
  have hcos_tk : ∀ k : ℕ, Real.cos (γ₁ * tk k) = -1 := by
    intro k
    have habs : γ₁ * tk k = (2 * (k : ℝ) + 1) * Real.pi ∨
        γ₁ * tk k = -((2 * (k : ℝ) + 1) * Real.pi) := by
      rcases lt_or_gt_of_ne hγ₁ with hneg | hpos
      · right; dsimp [tk]; rw [abs_of_neg hneg]; field_simp [hneg.ne']
      · left; dsimp [tk]; rw [abs_of_pos hpos]; field_simp [hpos.ne']
    have hcos_odd : Real.cos ((2 * (k : ℝ) + 1) * Real.pi) = -1 := by
      rw [show (2 * (k : ℝ) + 1) * Real.pi = Real.pi + (k : ℝ) * (2 * Real.pi) by ring,
          Real.cos_add_nat_mul_two_pi, Real.cos_pi]
    rcases habs with h | h
    · rw [h, hcos_odd]
    · rw [h, Real.cos_neg, hcos_odd]
  let limVal : ℂ → ℝ := fun z =>
    if z = (σ_max : ℂ) then c z
    else if z = z₁ ∨ z = conj z₁ then -c z
    else 0
  have hterm_lim : ∀ z ∈ S, Tendsto
      (fun k : ℕ => c z * Real.exp ((z.re - σ_max) * tk k) * Real.cos (z.im * tk k))
      atTop (𝓝 (limVal z)) := by
    intro z hz
    by_cases hcz : c z = 0
    · have hlv : limVal z = 0 := by simp [limVal, hcz]
      rw [hlv]; simpa [hcz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    rcases lt_or_eq_of_le (hmax z hz hcz) with hz_lt | hz_eq
    · have hnr : z ≠ (σ_max : ℂ) := fun h => by subst h; simp at hz_lt
      have hnz1 : z ≠ z₁ := fun h => by subst h; simp [z₁] at hz_lt
      have hncz1 : z ≠ conj z₁ := fun h => by subst h; simp [z₁] at hz_lt
      have hlv : limVal z = 0 := by simp [limVal, hnr, hnz1, hncz1]
      rw [hlv]
      have hdec : Tendsto (fun k : ℕ => |c z| * Real.exp ((z.re - σ_max) * tk k))
          atTop (𝓝 0) := by
        simpa [mul_zero] using
          ((tendsto_exp_atTop_nhds_zero_of_lt_zero (by linarith : z.re - σ_max < 0)).comp
            htk_top).const_mul |c z|
      refine squeeze_zero_norm (fun k => ?_) hdec
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    · rcases hsingle z hz hcz hz_eq with him0 | him1 | him2
      · have hzr : z = (σ_max : ℂ) := by apply Complex.ext <;> simp [hz_eq, him0]
        subst hzr
        simp [limVal]
      · have hzz1 : z = z₁ := by apply Complex.ext <;> simp [z₁, hz_eq, him1]
        subst hzz1
        have hnr : z₁ ≠ (σ_max : ℂ) := fun h => hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; exact this)
        have hlv : limVal z₁ = -c z₁ := by simp [limVal, hnr]
        rw [hlv]
        refine tendsto_const_nhds.congr fun k => ?_
        have hre : z₁.re = σ_max := by simp [z₁]
        have him : z₁.im = γ₁ := by simp [z₁]
        rw [hre, sub_self, zero_mul, Real.exp_zero, mul_one, him, hcos_tk k]; ring
      · have hzcz1 : z = conj z₁ := by apply Complex.ext <;> simp [z₁, hz_eq, him2]
        subst hzcz1
        have hnr : conj z₁ ≠ (σ_max : ℂ) := fun h => hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; linarith)
        have hlv : limVal (conj z₁) = -c (conj z₁) := by simp [limVal, hnr]
        rw [hlv]
        refine tendsto_const_nhds.congr fun k => ?_
        have hre : (conj z₁).re = σ_max := by simp [z₁]
        have him : (conj z₁).im = -γ₁ := by simp [z₁]
        rw [hre, sub_self, zero_mul, Real.exp_zero, mul_one, him, neg_mul, Real.cos_neg, hcos_tk k]
        ring
  have hsum_nn : 0 ≤ ∑ z ∈ S, limVal z := by
    refine ge_of_tendsto (tendsto_finset_sum S hterm_lim) (Eventually.of_forall fun k => ?_)
    have heq : (∑ z ∈ S, c z * Real.exp ((z.re - σ_max) * tk k) * Real.cos (z.im * tk k)) =
        Real.exp (-σ_max * tk k) * polarScaleWeight S c (tk k) := by
      unfold polarScaleWeight
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [show (z.re - σ_max) * tk k = -σ_max * tk k + z.re * tk k by ring, Real.exp_add]
      ring
    rw [heq]
    exact mul_nonneg (Real.exp_pos _).le (hw_nn (tk k) (htk_pos k))
  have hz1_ne_r : z₁ ≠ (σ_max : ℂ) := fun h => hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; exact this)
  have hcz1_ne_r : conj z₁ ≠ (σ_max : ℂ) := fun h => hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; linarith)
  have hsplit1 := Finset.add_sum_erase S limVal hz₁_mem
  have hcz1_er1 : conj z₁ ∈ S.erase z₁ := Finset.mem_erase.mpr ⟨hz₁_ne_conj.symm, hz₁_conj_mem⟩
  have hsplit2 := Finset.add_sum_erase (S.erase z₁) limVal hcz1_er1
  have hsum_eval : ∑ z ∈ S, limVal z =
      (if (σ_max : ℂ) ∈ S then c (σ_max : ℂ) else 0) - 2 * c z₁ := by
    rw [← hsplit1, ← hsplit2]
    have hlv1 : limVal z₁ = -c z₁ := by simp [limVal, hz1_ne_r]
    have hlv2 : limVal (conj z₁) = -c z₁ := by simp [limVal, hcz1_ne_r, hc_conj z₁ hz₁_mem]
    have hrest : ∑ z ∈ (S.erase z₁).erase (conj z₁), limVal z =
        if (σ_max : ℂ) ∈ S then c (σ_max : ℂ) else 0 := by
      by_cases hmem : (σ_max : ℂ) ∈ S
      · have hmem2 : (σ_max : ℂ) ∈ (S.erase z₁).erase (conj z₁) :=
          Finset.mem_erase.mpr ⟨hcz1_ne_r.symm, Finset.mem_erase.mpr ⟨hz1_ne_r.symm, hmem⟩⟩
        rw [if_pos hmem, ← Finset.add_sum_erase _ limVal hmem2]
        have hzero : ∑ z ∈ ((S.erase z₁).erase (conj z₁)).erase (σ_max : ℂ), limVal z = 0 := by
          refine Finset.sum_eq_zero fun z hz => ?_
          simp only [Finset.mem_erase] at hz
          simp [limVal, hz.1, hz.2.2.1, hz.2.1]
        simp [limVal, hzero]
      · rw [if_neg hmem]
        refine Finset.sum_eq_zero fun z hz => ?_
        simp only [Finset.mem_erase] at hz
        have hzr : z ≠ (σ_max : ℂ) := fun h => hmem (h ▸ hz.2.2.2)
        simp [limVal, hzr, hz.2.1, hz.1]
    rw [hlv1, hlv2, hrest]; ring
  rw [hsum_eval] at hsum_nn
  by_cases hmem : (σ_max : ℂ) ∈ S
  · rw [if_pos hmem] at hsum_nn; exact ⟨hmem, by linarith⟩
  · rw [if_neg hmem] at hsum_nn; linarith

/-- **No isolated zero-pole-tax quartet contraction.** Without a real anchor at depth `≥ a` or a
boundary pole, the pure relative-degree-zero quartet ratio `quartetCritPoly γ / quartetOffPoly a γ`
(`0 < a < 1/2`, `γ ≠ 0`) fails to have positive-definite vertical `−logDeriv` sections on `σ > 1`. -/
theorem not_isEvenPosDef_quartetPureRatio {a γ : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hγ : γ ≠ 0) :
    ¬ ∀ σ : ℝ, 1 < σ → IsEvenPosDef fun u : ℝ =>
      (-logDeriv (fun s => quartetCritPoly γ s / quartetOffPoly a γ s)
        ((σ : ℂ) + (u : ℂ) * I)).re := by
  classical
  intro hall
  let z_pp : ℂ := ((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I
  let z_pm : ℂ := ((1 / 2 + a : ℝ) : ℂ) - (γ : ℂ) * I
  let z_mp : ℂ := ((1 / 2 - a : ℝ) : ℂ) + (γ : ℂ) * I
  let z_mm : ℂ := ((1 / 2 - a : ℝ) : ℂ) - (γ : ℂ) * I
  let z_cp : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * I
  let z_cm : ℂ := (1 / 2 : ℂ) - (γ : ℂ) * I
  let S : Finset ℂ := {z_pp, z_pm, z_mp, z_mm, z_cp, z_cm}
  let c : ℂ → ℝ := fun z =>
    if z = z_pp ∨ z = z_pm ∨ z = z_mp ∨ z = z_mm then 1
    else if z = z_cp ∨ z = z_cm then -2
    else 0
  have hpair_ne :
      z_pp ≠ z_pm ∧ z_pp ≠ z_mp ∧ z_pp ≠ z_mm ∧ z_pp ≠ z_cp ∧ z_pp ≠ z_cm ∧
      z_pm ≠ z_mp ∧ z_pm ≠ z_mm ∧ z_pm ≠ z_cp ∧ z_pm ≠ z_cm ∧
      z_mp ≠ z_mm ∧ z_mp ≠ z_cp ∧ z_mp ≠ z_cm ∧
      z_mm ≠ z_cp ∧ z_mm ≠ z_cm ∧ z_cp ≠ z_cm := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp [z_pp, z_pm, z_mp, z_mm, z_cp, z_cm] at hre him
      first | linarith | exact hγ (by linarith)
  rcases hpair_ne with ⟨h12, h13, h14, h15, h16, h23, h24, h25, h26, h34, h35, h36, h45, h46, h56⟩
  have hconj_pp : conj z_pp = z_pm := by simp [z_pp, z_pm]
  have hconj_pm : conj z_pm = z_pp := by simp [z_pp, z_pm]
  have hconj_mp : conj z_mp = z_mm := by simp [z_mp, z_mm]
  have hconj_mm : conj z_mm = z_mp := by simp [z_mp, z_mm]
  have hconj_cp : conj z_cp = z_cm := by simp [z_cp, z_cm, map_ofNat]
  have hconj_cm : conj z_cm = z_cp := by simp [z_cp, z_cm, map_ofNat]
  have hS_conj : ∀ z ∈ S, conj z ∈ S := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · right; left; exact hconj_pp
    · left; exact hconj_pm
    · right; right; right; left; exact hconj_mp
    · right; right; left; exact hconj_mm
    · right; right; right; right; right; exact hconj_cp
    · right; right; right; right; left; exact hconj_cm
  have hc_conj : ∀ z ∈ S, c (conj z) = c z := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hconj_pp]; simp [c]
    · rw [hconj_pm]; simp [c]
    · rw [hconj_mp]; simp [c]
    · rw [hconj_mm]; simp [c]
    · rw [hconj_cp]; simp [c, h15.symm, h25.symm, h35.symm, h45.symm, h16.symm, h26.symm, h36.symm, h46.symm]
    · rw [hconj_cm]; simp [c, h15.symm, h25.symm, h35.symm, h45.symm, h16.symm, h26.symm, h36.symm, h46.symm]
  have hS_re₁ : ∀ z ∈ S, z.re ≤ 1 := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp [z_pp, z_pm, z_mp, z_mm, z_cp, z_cm]; linarith)
  have hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ 1 / 2 + a := by
    intro z hz _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp [z_pp, z_pm, z_mp, z_mm, z_cp, z_cm]; linarith)
  have hpd_polar : ∀ σ : ℝ, 1 < σ →
      IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
    intro σ hσ
    have heq_fn : (fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (-logDeriv (fun s => quartetCritPoly γ s / quartetOffPoly a γ s)
          ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u
      congr 1
      set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
      have hnz : ∀ z ∈ S, s - z ≠ 0 := fun z hz h0 => by
        have := congrArg Complex.re h0; simp [hs_def] at this; linarith [hS_re₁ z hz]
      have hpp := hnz z_pp (by simp [S])
      have hpm := hnz z_pm (by simp [S])
      have hmp := hnz z_mp (by simp [S])
      have hmm := hnz z_mm (by simp [S])
      have hcp := hnz z_cp (by simp [S])
      have hcm := hnz z_cm (by simp [S])
      have hcrit_eq : quartetCritPoly γ = fun w : ℂ => (w - z_cp) ^ 2 * (w - z_cm) ^ 2 := by
        funext w; unfold quartetCritPoly; dsimp [z_cp, z_cm]
        calc ((w - 1 / 2) ^ 2 + (γ : ℂ) ^ 2) ^ 2
            = ((w - 1 / 2) ^ 2 - ((γ : ℂ) * I) ^ 2) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
          _ = ((w - (1 / 2 + (γ : ℂ) * I)) * (w - (1 / 2 - (γ : ℂ) * I))) ^ 2 := by ring
          _ = (w - (1 / 2 + (γ : ℂ) * I)) ^ 2 * (w - (1 / 2 - (γ : ℂ) * I)) ^ 2 := by ring
      have hoff_eq : quartetOffPoly a γ =
          fun w : ℂ => ((w - z_pp) * (w - z_pm)) * ((w - z_mp) * (w - z_mm)) := by
        funext w; unfold quartetOffPoly; dsimp [z_pp, z_pm, z_mp, z_mm]
        have f1 : (w - ((1 / 2 + a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2 =
            (w - (((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I)) *
              (w - (((1 / 2 + a : ℝ) : ℂ) - (γ : ℂ) * I)) := by
          calc (w - ((1 / 2 + a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2
              = (w - ((1 / 2 + a : ℝ) : ℂ)) ^ 2 - ((γ : ℂ) * I) ^ 2 := by
                  rw [mul_pow, Complex.I_sq]; ring
            _ = _ := by ring
        have f2 : (w - ((1 / 2 - a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2 =
            (w - (((1 / 2 - a : ℝ) : ℂ) + (γ : ℂ) * I)) *
              (w - (((1 / 2 - a : ℝ) : ℂ) - (γ : ℂ) * I)) := by
          calc (w - ((1 / 2 - a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2
              = (w - ((1 / 2 - a : ℝ) : ℂ)) ^ 2 - ((γ : ℂ) * I) ^ 2 := by
                  rw [mul_pow, Complex.I_sq]; ring
            _ = _ := by ring
        rw [f1, f2]
      have hd_lin : ∀ z₀ : ℂ, logDeriv (fun w : ℂ => w - z₀) s = 1 / (s - z₀) := fun z₀ => by
        rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
      rw [hcrit_eq, hoff_eq,
          logDeriv_div (f := fun w => (w - z_cp) ^ 2 * (w - z_cm) ^ 2)
            (g := fun w => ((w - z_pp) * (w - z_pm)) * ((w - z_mp) * (w - z_mm))) s
            (mul_ne_zero (pow_ne_zero 2 hcp) (pow_ne_zero 2 hcm))
            (mul_ne_zero (mul_ne_zero hpp hpm) (mul_ne_zero hmp hmm))
            (((differentiableAt_id.sub_const z_cp).fun_pow 2).mul
              ((differentiableAt_id.sub_const z_cm).fun_pow 2))
            (((differentiableAt_id.sub_const z_pp).mul (differentiableAt_id.sub_const z_pm)).mul
              ((differentiableAt_id.sub_const z_mp).mul (differentiableAt_id.sub_const z_mm))),
          logDeriv_mul (f := fun w => (w - z_cp) ^ 2) (g := fun w => (w - z_cm) ^ 2) s
            (pow_ne_zero 2 hcp) (pow_ne_zero 2 hcm)
            ((differentiableAt_id.sub_const z_cp).fun_pow 2)
            ((differentiableAt_id.sub_const z_cm).fun_pow 2),
          logDeriv_fun_pow (differentiableAt_id.sub_const z_cp) 2,
          logDeriv_fun_pow (differentiableAt_id.sub_const z_cm) 2,
          logDeriv_mul (f := fun w => (w - z_pp) * (w - z_pm))
            (g := fun w => (w - z_mp) * (w - z_mm)) s
            (mul_ne_zero hpp hpm) (mul_ne_zero hmp hmm)
            ((differentiableAt_id.sub_const z_pp).mul (differentiableAt_id.sub_const z_pm))
            ((differentiableAt_id.sub_const z_mp).mul (differentiableAt_id.sub_const z_mm)),
          logDeriv_mul (f := fun w => w - z_pp) (g := fun w => w - z_pm) s hpp hpm
            (differentiableAt_id.sub_const z_pp) (differentiableAt_id.sub_const z_pm),
          logDeriv_mul (f := fun w => w - z_mp) (g := fun w => w - z_mm) s hmp hmm
            (differentiableAt_id.sub_const z_mp) (differentiableAt_id.sub_const z_mm),
          hd_lin, hd_lin, hd_lin, hd_lin, hd_lin, hd_lin]
      unfold polarSum
      dsimp [S]
      rw [Finset.sum_insert (by simp [h12, h13, h14, h15, h16]),
          Finset.sum_insert (by simp [h23, h24, h25, h26]),
          Finset.sum_insert (by simp [h34, h35, h36]),
          Finset.sum_insert (by simp [h45, h46]),
          Finset.sum_insert (by simp [h56]),
          Finset.sum_singleton]
      have hc1 : c z_pp = 1 := by simp [c]
      have hc2 : c z_pm = 1 := by simp [c]
      have hc3 : c z_mp = 1 := by simp [c]
      have hc4 : c z_mm = 1 := by simp [c]
      have hc5 : c z_cp = -2 := by simp [c, h15.symm, h25.symm, h35.symm, h45.symm]
      have hc6 : c z_cm = -2 := by simp [c, h16.symm, h26.symm, h36.symm, h46.symm]
      rw [hc1, hc2, hc3, hc4, hc5, hc6]
      push_cast; ring
    rw [heq_fn]
    exact (hall σ hσ).posDef
  have hz₁_mem : (((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I) ∈ S := by
    change z_pp ∈ S; simp [S]
  have hz₁_pos : 0 < c (((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I) := by
    change 0 < c z_pp; simp [c]
  obtain ⟨hreal_mem, -⟩ := real_anchor_of_posDef_polarSum hS_conj hc_conj hS_re₁ hpd_polar
    hmax hγ hz₁_mem hz₁_pos
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hreal_mem
  rcases hreal_mem with h | h | h | h | h | h <;>
    (have him := congrArg Complex.im h;
     simp [z_pp, z_pm, z_mp, z_mm, z_cp, z_cm] at him;
     exact hγ (by linarith))

/-! ### 2. Functorial exterior-power curve data and quartet phase elimination -/

/-- Index type `{S ⊆ ι : |S| = k}` of the `k`-th exterior power `Λ^k H¹`. -/
abbrev ExteriorIndex (ι : Type*) (k : ℕ) := {S : Finset ι // S.card = k}

private def permExterior {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) (k : ℕ) :
    Equiv.Perm (ExteriorIndex ι k) where
  toFun S := ⟨S.1.map σ.toEmbedding, by rw [Finset.card_map, S.2]⟩
  invFun S := ⟨S.1.map σ.symm.toEmbedding, by rw [Finset.card_map, S.2]⟩
  left_inv S := by
    ext i; simp
  right_inv S := by
    ext i; simp

/-- **Functorial `k`-th exterior curve datum** (`k ≥ 1`). Retains a simple boundary pole (`Δκ = 0`)
at base `q^k`, with normalized Frobenius eigenvalues `Π_{i ∈ S} β_i`. -/
def CurveDatum.exterior {ι : Type*} [Fintype ι] [DecidableEq ι] (D : CurveDatum ι)
    (k : ℕ) (hk : 1 ≤ k) : CurveDatum (ExteriorIndex ι k) where
  q := D.q ^ k
  one_lt_q := one_lt_pow₀ D.one_lt_q (by omega)
  β S := ∏ i ∈ S.1, D.β i
  conjPerm := permExterior D.conjPerm k
  β_conjPerm S := by
    dsimp [permExterior]
    rw [Finset.prod_map, map_prod]
    exact Finset.prod_congr rfl fun i _ => D.β_conjPerm i
  fePerm := permExterior D.fePerm k
  β_fePerm S := by
    dsimp [permExterior]
    rw [Finset.prod_map, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => D.β_fePerm i

theorem CurveDatum.sqrtq_exterior {ι : Type*} [Fintype ι] [DecidableEq ι] (D : CurveDatum ι)
    (k : ℕ) (hk : 1 ≤ k) :
    (D.exterior k hk).sqrtq = D.sqrtq ^ k := by
  have hq0 : 0 ≤ D.q := by linarith [D.one_lt_q]
  have hsqrt_pow : ∀ n : ℕ, Real.sqrt (D.q ^ n) = Real.sqrt D.q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg hq0 n), ih, pow_succ]
  exact hsqrt_pow k

/-- The Frobenius eigenvalues of `D.exterior k hk` are the `k`-fold exterior products
`exteriorEigenvalue D S`. -/
theorem eigenvalue_exterior {ι : Type*} [Fintype ι] [DecidableEq ι] (D : CurveDatum ι)
    (k : ℕ) (hk : 1 ≤ k) (S : ExteriorIndex ι k) :
    eigenvalue (D.exterior k hk) S = exteriorEigenvalue D S.1 := by
  rw [eigenvalue, CurveDatum.sqrtq_exterior, exteriorEigenvalue]
  dsimp [CurveDatum.exterior]
  have hcard : ((D.sqrtq : ℂ)) ^ k = ∏ _i ∈ S.1, (D.sqrtq : ℂ) := by
    rw [Finset.prod_const, S.2]
  rw [Complex.ofReal_pow, hcard, ← Finset.prod_mul_distrib]
  rfl

/-- `detDeg` of the functorial exterior curve datum `D.exterior k hk` is `exteriorDetDeg D k`. -/
theorem detDeg_exterior_eq_exteriorDetDeg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : CurveDatum ι) (k : ℕ) (hk : 1 ≤ k) (P : ℝ[X]) :
    detDeg (D.exterior k hk) P = exteriorDetDeg D k P := by
  rw [detDeg, exteriorDetDeg]
  refine Finset.prod_nbij' (fun S : ExteriorIndex ι k => S.1)
    (fun S => if h : S.card = k then ⟨S, h⟩ else
      ⟨∅, by exfalso; exact absurd rfl h⟩) ?_ ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S.1, S.2⟩
  · intro S hS
    exact Finset.mem_univ _
  · intro S _
    simp [S.2]
  · intro S hS
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    simp [hcard]
  · intro S _
    rw [eigenvalue_exterior]

/-- General genus-`2` complex quartet curve datum at base `q > 1`, radial modulus `r > 0`, and
phase `θ ∈ ℝ`, with normalized Frobenius eigenvalues `(r e^{iθ}, r e^{−iθ}, r⁻¹ e^{iθ}, r⁻¹ e^{−iθ})`. -/
def quartetCurveDatum (q : ℝ) (hq : 1 < q) (r : ℝ) (hr : 0 < r) (θ : ℝ) :
    CurveDatum (Fin 4) where
  q := q
  one_lt_q := hq
  β := ![
    (r : ℂ) * Complex.exp ((θ : ℂ) * I),
    (r : ℂ) * Complex.exp (-((θ : ℂ) * I)),
    ((r⁻¹ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I),
    ((r⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * I))
  ]
  conjPerm := {
    toFun := ![1, 0, 3, 2]
    invFun := ![1, 0, 3, 2]
    left_inv := fun i => by fin_cases i <;> rfl
    right_inv := fun i => by fin_cases i <;> rfl
  }
  β_conjPerm i := by
    have hcexp_p : conj (Complex.exp ((θ : ℂ) * I)) = Complex.exp (-((θ : ℂ) * I)) := by
      rw [← Complex.exp_conj]; congr 1; simp
    have hcexp_m : conj (Complex.exp (-((θ : ℂ) * I))) = Complex.exp ((θ : ℂ) * I) := by
      rw [← Complex.exp_conj]; congr 1; simp
    fin_cases i <;> simp [hcexp_p, hcexp_m]
  fePerm := {
    toFun := ![3, 2, 1, 0]
    invFun := ![3, 2, 1, 0]
    left_inv := fun i => by fin_cases i <;> rfl
    right_inv := fun i => by fin_cases i <;> rfl
  }
  β_fePerm i := by
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hexp_pm : Complex.exp (-((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    have hexp_mp : Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    fin_cases i <;>
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Equiv.coe_fn_mk, Complex.ofReal_inv]
      calc _ = ((r : ℂ)⁻¹ * (r : ℂ)) * _ := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hrC, one_mul]; first | exact hexp_pm | exact hexp_mp

/-- **Degree-one linear blindness on every non-real quartet.** Whenever `sin θ ≠ 0`, every linear
kernel count `detDeg (quartetCurveDatum q hq r hr θ) (C c − X)` (`c ∈ ℝ`) is strictly positive. -/
theorem quartetCurveDatum_detDeg_linear_pos {q : ℝ} (hq : 1 < q) {r : ℝ} (hr : 0 < r)
    {θ : ℝ} (hsin : Real.sin θ ≠ 0) (c : ℝ) :
    0 < (detDeg (quartetCurveDatum q hq r hr θ) (C c - X)).re := by
  set D := quartetCurveDatum q hq r hr θ
  have him_ne : ∀ i : Fin 4, (eigenvalue D i).im ≠ 0 := by
    intro i
    have hsq_pos : 0 < D.sqrtq := D.sqrtq_pos
    have hexp_p_im : (Complex.exp ((θ : ℂ) * I)).im = Real.sin θ := by
      rw [Complex.exp_mul_I]; simp
    have hexp_m_im : (Complex.exp (-((θ : ℂ) * I))).im = -Real.sin θ := by
      have : -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_mul_I]; simp [Real.sin_neg]
    fin_cases i <;>
    · simp only [eigenvalue, D, quartetCurveDatum, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three]
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul]
      first
      | (rw [hexp_p_im]; exact mul_ne_zero (mul_pos hsq_pos hr).ne' hsin)
      | (rw [hexp_m_im]; exact mul_ne_zero (mul_pos hsq_pos hr).ne' (neg_ne_zero.mpr hsin))
      | (rw [hexp_p_im]; exact mul_ne_zero (mul_pos hsq_pos (inv_pos.mpr hr)).ne' hsin)
      | (rw [hexp_m_im]; exact mul_ne_zero (mul_pos hsq_pos (inv_pos.mpr hr)).ne'
          (neg_ne_zero.mpr hsin))
  rw [detDeg, Fin.prod_univ_four]
  have hc01 : aeval (eigenvalue D 1) (C c - X) = conj (aeval (eigenvalue D 0) (C c - X)) := by
    rw [← aeval_conj, ← eigenvalue_conjPerm]
    rfl
  have hc23 : aeval (eigenvalue D 3) (C c - X) = conj (aeval (eigenvalue D 2) (C c - X)) := by
    rw [← aeval_conj, ← eigenvalue_conjPerm]
    rfl
  rw [hc01, hc23]
  have hprod : aeval (eigenvalue D 0) (C c - X) * conj (aeval (eigenvalue D 0) (C c - X)) *
      aeval (eigenvalue D 2) (C c - X) * conj (aeval (eigenvalue D 2) (C c - X)) =
      ((Complex.normSq (aeval (eigenvalue D 0) (C c - X)) *
        Complex.normSq (aeval (eigenvalue D 2) (C c - X)) : ℝ) : ℂ) := by
    calc aeval (eigenvalue D 0) (C c - X) * conj (aeval (eigenvalue D 0) (C c - X)) *
          aeval (eigenvalue D 2) (C c - X) * conj (aeval (eigenvalue D 2) (C c - X))
        = (aeval (eigenvalue D 0) (C c - X) * conj (aeval (eigenvalue D 0) (C c - X))) *
          (aeval (eigenvalue D 2) (C c - X) * conj (aeval (eigenvalue D 2) (C c - X))) := by ring
      _ = _ := by rw [Complex.mul_conj, Complex.mul_conj, Complex.ofReal_mul]
  rw [hprod, Complex.ofReal_re]
  have hnz0 : aeval (eigenvalue D 0) (C c - X) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [map_sub, aeval_C, aeval_X, Complex.coe_algebraMap, Complex.sub_im,
      Complex.ofReal_im, zero_sub, neg_eq_zero, Complex.zero_im] at this
    exact him_ne 0 this
  have hnz2 : aeval (eigenvalue D 2) (C c - X) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [map_sub, aeval_C, aeval_X, Complex.coe_algebraMap, Complex.sub_im,
      Complex.ofReal_im, zero_sub, neg_eq_zero, Complex.zero_im] at this
    exact him_ne 2 this
  exact mul_pos (Complex.normSq_pos.mpr hnz0) (Complex.normSq_pos.mpr hnz2)

/-- **Complete quartet phase elimination on `Λ²`.** Passing from `quartetCurveDatum q hq r hr θ` to
its exterior square `exterior 2` (`Δκ = 0`) collides `(0, 1)` to `q r² ∈ ℝ`, collides `(2, 3)` to
`q r⁻² ∈ ℝ`, and puts all four remaining exterior eigenvalues on the unitary circle `‖β‖ = 1`. -/
theorem quartetCurveDatum_exterior_two_spectrum {q : ℝ} (hq : 1 < q) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    let D₂ := (quartetCurveDatum q hq r hr θ).exterior 2 (by norm_num)
    eigenvalue D₂ ⟨{0, 1}, by decide⟩ = ((q * r ^ 2 : ℝ) : ℂ) ∧
    eigenvalue D₂ ⟨{2, 3}, by decide⟩ = ((q * r⁻¹ ^ 2 : ℝ) : ℂ) ∧
    ∀ S : ExteriorIndex (Fin 4) 2,
      S.1 ≠ {0, 1} → S.1 ≠ {2, 3} → ‖D₂.β S‖ = 1 := by
  intro D₂
  set D := quartetCurveDatum q hq r hr θ
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hexp_pm : Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hsq : (D.sqrtq : ℂ) * (D.sqrtq : ℂ) = (q : ℂ) := by
    rw [← sq, ← Complex.ofReal_pow, D.sqrtq_sq]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eigenvalue_exterior, exteriorEigenvalue, Finset.prod_pair (by decide)]
    simp only [eigenvalue, D, quartetCurveDatum, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc (D.sqrtq : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) *
          ((D.sqrtq : ℂ) * ((r : ℂ) * Complex.exp (-((θ : ℂ) * I))))
        = ((D.sqrtq : ℂ) * (D.sqrtq : ℂ)) * (r : ℂ) ^ 2 *
          (Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I))) := by ring
      _ = ((q * r ^ 2 : ℝ) : ℂ) := by rw [hsq, hexp_pm, mul_one]; push_cast; ring
  · rw [eigenvalue_exterior, exteriorEigenvalue, Finset.prod_pair (by decide)]
    simp only [eigenvalue, D, quartetCurveDatum, Matrix.cons_val_two, Matrix.cons_val_three]
    calc (D.sqrtq : ℂ) * (((r⁻¹ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)) *
          ((D.sqrtq : ℂ) * (((r⁻¹ : ℝ) : ℂ) * Complex.exp (-((θ : ℂ) * I))))
        = ((D.sqrtq : ℂ) * (D.sqrtq : ℂ)) * ((r⁻¹ : ℝ) : ℂ) ^ 2 *
          (Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I))) := by ring
      _ = ((q * r⁻¹ ^ 2 : ℝ) : ℂ) := by rw [hsq, hexp_pm, mul_one]; push_cast; ring
  · intro S h01 h23
    have hmem : S.1 ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S.1, S.2⟩
    have huniv : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
        {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by decide
    rw [huniv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hnorm_p : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    have hnorm_m : ‖Complex.exp (-((θ : ℂ) * I))‖ = 1 := by
      have : -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
      rw [this]; exact Complex.norm_exp_ofReal_mul_I (-θ)
    have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    rcases hmem with h | h | h | h | h | h
    · exact absurd h h01
    · dsimp [D₂, CurveDatum.exterior]
      rw [h, Finset.prod_pair (by decide)]
      simp only [D, quartetCurveDatum, Matrix.cons_val_zero, Matrix.cons_val_two,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, hnorm_p, mul_one, hrr]
    · dsimp [D₂, CurveDatum.exterior]
      rw [h, Finset.prod_pair (by decide)]
      simp only [D, quartetCurveDatum, Matrix.cons_val_zero, Matrix.cons_val_three,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, hnorm_p, hnorm_m, mul_one, hrr]
    · dsimp [D₂, CurveDatum.exterior]
      rw [h, Finset.prod_pair (by decide)]
      simp only [D, quartetCurveDatum, Matrix.cons_val_one, Matrix.cons_val_two,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, hnorm_p, hnorm_m, mul_one, hrr]
    · dsimp [D₂, CurveDatum.exterior]
      rw [h, Finset.prod_pair (by decide)]
      simp only [D, quartetCurveDatum, Matrix.cons_val_one, Matrix.cons_val_three,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, hnorm_m, mul_one, hrr]
    · exact absurd h h23

/-! ### 3. Archimedean exterior-square divisors and zero-tax quartet contraction -/

/-- Critical-line-centered scale trace `z_ρ(t) = Σ_i e^{(ρ_i − 1/2)t}` of a finite zero packet. -/
def centeredScaleTrace {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i : ι, Complex.exp ((ρ i - 1 / 2) * (t : ℂ))

/-- Archimedean exterior-square scale trace `Λ² z_ρ(t) = Σ_{|S| = 2} e^{(Σ_{i ∈ S} (ρ_i − 1/2)) t}`. -/
def exteriorTwoScaleTrace {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ S ∈ (Finset.univ : Finset ι).powersetCard 2,
    Complex.exp ((∑ i ∈ S, (ρ i - 1 / 2)) * (t : ℂ))

/-- **Archimedean Adams–Newton exterior-square identity.** In continuous scale `t`,
`2 Λ² z_ρ(t) = z_ρ(t)² − z_ρ(2t)`, killing the diagonal squares `e^{2(ρ_i − 1/2)t}`. -/
theorem exteriorTwoScaleTrace_eq_newton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : ι → ℂ) (t : ℝ) :
    2 * exteriorTwoScaleTrace ρ t =
      centeredScaleTrace ρ t ^ 2 - centeredScaleTrace ρ (2 * t) := by
  set x : ι → ℂ := fun i => Complex.exp ((ρ i - 1 / 2) * (t : ℂ))
  have h1 : centeredScaleTrace ρ t ^ 2 - centeredScaleTrace ρ (2 * t) =
      ∑ p ∈ (Finset.univ ×ˢ (Finset.univ : Finset ι)).filter (fun p => p.1 ≠ p.2),
        x p.1 * x p.2 := by
    have hdiag : centeredScaleTrace ρ (2 * t) = ∑ i : ι, x i * x i := by
      unfold centeredScaleTrace
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [x]
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hsq : centeredScaleTrace ρ t ^ 2 =
        (∑ i : ι, x i * x i) +
          ∑ p ∈ (Finset.univ ×ˢ (Finset.univ : Finset ι)).filter (fun p => p.1 ≠ p.2),
            x p.1 * x p.2 := by
      unfold centeredScaleTrace
      change (∑ i : ι, x i) ^ 2 = _
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
      have hpart := Finset.sum_filter_add_sum_filter_not
        (Finset.univ ×ˢ (Finset.univ : Finset ι)) (fun p : ι × ι => p.1 = p.2)
        (fun p => x p.1 * x p.2)
      rw [← hpart]
      congr 1
      refine Finset.sum_nbij' (fun p => p.1) (fun i => (i, i)) ?_ ?_ ?_ ?_ ?_
      · intro p _; exact Finset.mem_univ p.1
      · intro i _; simp
      · intro p hp; simp only [Finset.mem_filter] at hp; ext; · rfl; · exact hp.2.symm
      · intro i _; rfl
      · intro p hp; simp only [Finset.mem_filter] at hp; rw [hp.2]
    rw [hsq, hdiag, add_sub_cancel_left]
  rw [h1]
  let P2 := (Finset.univ : Finset ι).powersetCard 2
  let OD := (Finset.univ ×ˢ (Finset.univ : Finset ι)).filter (fun p => p.1 ≠ p.2)
  have hmaps : ∀ p ∈ OD, ({p.1, p.2} : Finset ι) ∈ P2 := by
    intro p hp
    simp only [OD, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hp⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  unfold exteriorTwoScaleTrace
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hS).2
  have hfib : OD.filter (fun p : ι × ι => ({p.1, p.2} : Finset ι) = {a, b}) = {(a, b), (b, a)} := by
    ext ⟨u, v⟩
    simp only [OD, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨huv, heq⟩
      have hu : u ∈ ({a, b} : Finset ι) := heq ▸ Finset.mem_insert_self u {v}
      have hv : v ∈ ({a, b} : Finset ι) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
      · exact absurd rfl huv
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hab, rfl⟩
      · exact ⟨hab.symm, Finset.pair_comm b a⟩
  have hpair_ne : (a, b) ≠ (b, a) := fun h => hab (Prod.mk.inj h).1
  rw [hfib, Finset.sum_pair hpair_ne, Finset.sum_pair hab, add_mul, Complex.exp_add]
  dsimp [x]
  ring

/-- Archimedean exterior-square divisor polynomial
`P_{Λ²}(ρ; s) = Π_{|S| = 2} (s − (1/2 + Σ_{i ∈ S} (ρ_i − 1/2)))`. -/
def exteriorTwoDivisorPoly {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℂ) (s : ℂ) : ℂ :=
  ∏ S ∈ (Finset.univ : Finset ι).powersetCard 2, (s - (1 / 2 + ∑ i ∈ S, (ρ i - 1 / 2)))

/-- Four-element complex quartet `(1/2 + a + iγ, 1/2 + a − iγ, 1/2 − a + iγ, 1/2 − a − iγ)`. -/
def quartetPoints (a γ : ℝ) : Fin 4 → ℂ :=
  ![1 / 2 + (a : ℂ) + (γ : ℂ) * I,
    1 / 2 + (a : ℂ) - (γ : ℂ) * I,
    1 / 2 - (a : ℂ) + (γ : ℂ) * I,
    1 / 2 - (a : ℂ) - (γ : ℂ) * I]

/-- **Exact exterior-square factorization of a complex quartet.** `P_{Λ²}` converts the complex
quartet `{1/2 ± a ± iγ}` into a single real off-critical pair `realPairPoly (1/2 + 2a) s` plus four
critical-line zeros `(s − 1/2)² ((s − 1/2)² + (2γ)²)`. -/
theorem exteriorTwoDivisorPoly_quartet (a γ : ℝ) (s : ℂ) :
    exteriorTwoDivisorPoly (quartetPoints a γ) s =
      realPairPoly (1 / 2 + 2 * a) s *
        ((s - 1 / 2) ^ 2 * ((s - 1 / 2) ^ 2 + (2 * (γ : ℂ)) ^ 2)) := by
  have huniv : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by decide
  rw [exteriorTwoDivisorPoly, huniv,
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton,
      Finset.sum_pair (by decide), Finset.sum_pair (by decide),
      Finset.sum_pair (by decide), Finset.sum_pair (by decide),
      Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
  simp only [quartetPoints, realPairPoly, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  push_cast
  calc (s - (1 / 2 + (1 / 2 + (a : ℂ) + (γ : ℂ) * I - 1 / 2 +
            (1 / 2 + (a : ℂ) - (γ : ℂ) * I - 1 / 2)))) *
        ((s - (1 / 2 + (1 / 2 + (a : ℂ) + (γ : ℂ) * I - 1 / 2 +
            (1 / 2 - (a : ℂ) + (γ : ℂ) * I - 1 / 2)))) *
        ((s - (1 / 2 + (1 / 2 + (a : ℂ) + (γ : ℂ) * I - 1 / 2 +
            (1 / 2 - (a : ℂ) - (γ : ℂ) * I - 1 / 2)))) *
        ((s - (1 / 2 + (1 / 2 + (a : ℂ) - (γ : ℂ) * I - 1 / 2 +
            (1 / 2 - (a : ℂ) + (γ : ℂ) * I - 1 / 2)))) *
        ((s - (1 / 2 + (1 / 2 + (a : ℂ) - (γ : ℂ) * I - 1 / 2 +
            (1 / 2 - (a : ℂ) - (γ : ℂ) * I - 1 / 2)))) *
        (s - (1 / 2 + (1 / 2 - (a : ℂ) + (γ : ℂ) * I - 1 / 2 +
            (1 / 2 - (a : ℂ) - (γ : ℂ) * I - 1 / 2))))))))
      = (s - (1 / 2 + 2 * (a : ℂ))) * (s - (1 - (1 / 2 + 2 * (a : ℂ)))) *
          ((s - 1 / 2) ^ 2 * ((s - 1 / 2) ^ 2 - (2 * (γ : ℂ)) ^ 2 * I ^ 2)) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- **Zero-pole-tax contraction of the exterior-square quartet** (`0 < a < 1/4`, `Δκ = 0`).
Multiplying `exteriorTwoDivisorPoly (quartetPoints a γ)` by `midpointSymSquare (1/2 + 2a)` moves
all six exterior zeros onto the critical line `Re s = 1/2` with even positive-definite vertical
`−logDeriv` sections on `σ > 1` and zero boundary poles. -/
theorem exteriorTwoDivisorPoly_quartet_contract {a : ℝ} (ha0 : 0 < a) (ha4 : a < 1 / 4) (γ : ℝ) :
    (∀ s : ℂ, realPairPoly (1 / 2 + 2 * a) s ≠ 0 →
      exteriorTwoDivisorPoly (quartetPoints a γ) s * midpointSymSquare (1 / 2 + 2 * a) s =
        (s - 1 / 2) ^ 4 * ((s - 1 / 2) ^ 2 + (2 * (γ : ℂ)) ^ 2)) ∧
    (∀ σ : ℝ, 1 < σ → IsEvenPosDef fun u : ℝ =>
      (-logDeriv (midpointSymSquare (1 / 2 + 2 * a)) ((σ : ℂ) + (u : ℂ) * I)).re) := by
  refine ⟨fun s hnz => ?_, fun σ hσ =>
    isEvenPosDef_midpointSymSquare (by linarith) (by linarith) hσ⟩
  rw [exteriorTwoDivisorPoly_quartet, midpointSymSquare]
  field_simp [hnz]
  ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
