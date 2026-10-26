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
      have hsum_d := (HasDerivAt.fun_sum hterm).const_mul ((-1 : ℂ) ^ n * (n.factorial : ℂ))
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
    unfold polarSum
    refine DifferentiableWithinAt.fun_sum fun z hz => ?_
    have hsz : s - z ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith [hSa z hz]
    exact ((differentiableAt_const (c z : ℂ)).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - z) s) hsz).differentiableWithinAt
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
      tendsto_finsetSum S fun z _ =>
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
  have hderiv_eq := polarSum_iterate_deriv_eqOn (c := c) hSa n (show (xn : ℂ) ∈ U by simp [U, hxn_gt])
  have hscale_pos : 0 ≤ xn ^ (n + 1) / (n.factorial : ℝ) :=
    div_nonneg (pow_nonneg hxn_pos.le _) (Nat.cast_nonneg _)
  have hnonneg := mul_nonneg hscale_pos hcm_n
  have hident : xn ^ (n + 1) / (n.factorial : ℝ) *
      ((-1 : ℝ) ^ n * ((deriv^[n] (polarSum S c)) (xn : ℂ)).re) =
      (∑ z ∈ S, (c z : ℂ) * ((1 - z * (t : ℂ) / (n : ℂ))⁻¹) ^ (n + 1)).re := by
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
  rw [← hident]
  exact hnonneg

private theorem tendsto_avg_cos_zero {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T), Real.cos (ω * t)) atTop (𝓝 0) := by
  have hint_eq : ∀ T : ℝ, ∫ t in T..(2 * T), Real.cos (ω * t) =
      Real.sin (ω * (2 * T)) / ω - Real.sin (ω * T) / ω := by
    intro T
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Real.sin (ω * x) / ω)
      (fun x _ => ?_) (Continuous.intervalIntegrable (by fun_prop) T (2 * T))
    exact (((hasDerivAt_id x).const_mul ω).sin.div_const ω).congr_deriv
      (by dsimp only [id]; field_simp [hω])
  have hzero_lim : Tendsto (fun T : ℝ => T⁻¹ * (2 / |ω|)) atTop (𝓝 0) :=
    ((by simpa [mul_zero] using tendsto_inv_atTop_zero.const_mul (2 / |ω|) :
      Tendsto (fun T : ℝ => 2 / |ω| * T⁻¹) atTop (𝓝 0)).congr fun T => by ring)
  refine squeeze_zero_norm' ?_ hzero_lim
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
    simp [z₁]; ring
  have hz₁_conj_mem : conj z₁ ∈ S := hS_conj z₁ hz₁_mem
  have hz₁_ne_conj : z₁ ≠ conj z₁ := by
    intro h
    have := congrArg Complex.im h
    simp [z₁] at this
    exact hγ₁ (by linarith)
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
      simp [hcz]
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
          (Real.tendsto_exp_atBot.comp
            (tendsto_id.const_mul_atTop_of_neg (by linarith : z.re - σ_max < 0))).const_mul
            (2 * |c z|)
      refine squeeze_zero_norm' ?_ hdec
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hT)]
      have hint_le : |∫ t in T..(2 * T),
          c z * Real.exp ((z.re - σ_max) * t) * Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t))| ≤
          (2 * |c z| * Real.exp ((z.re - σ_max) * T)) * (2 * T - T) := by
        set M : ℝ := 2 * |c z| * Real.exp ((z.re - σ_max) * T)
        have hcont_f : Continuous (fun t : ℝ =>
            c z * Real.exp ((z.re - σ_max) * t) * Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t))) :=
          by fun_prop
        have hf_abs : ∀ t ∈ Icc T (2 * T),
            |c z * Real.exp ((z.re - σ_max) * t) * Real.cos (z.im * t) * (1 - Real.cos (γ₁ * t))| ≤
              M := by
          intro t ht
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp : Real.exp ((z.re - σ_max) * t) ≤ Real.exp ((z.re - σ_max) * T) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (by linarith))
          have h1cos : |1 - Real.cos (γ₁ * t)| ≤ 2 := by
            have := Real.abs_cos_le_one (γ₁ * t)
            rw [abs_le] at this ⊢
            exact ⟨by linarith, by linarith⟩
          calc |c z| * Real.exp ((z.re - σ_max) * t) * |Real.cos (z.im * t)| *
                |1 - Real.cos (γ₁ * t)|
              ≤ |c z| * Real.exp ((z.re - σ_max) * T) * 1 * 2 := by
                gcongr
                exact Real.abs_cos_le_one _
            _ = M := by dsimp [M]; ring
        rw [abs_le]
        have hi_negM : IntervalIntegrable (fun _ : ℝ => -M) volume T (2 * T) :=
          intervalIntegrable_const
        have hi_M : IntervalIntegrable (fun _ : ℝ => M) volume T (2 * T) :=
          intervalIntegrable_const
        constructor
        · have hlow := intervalIntegral.integral_mono_on (by linarith : T ≤ 2 * T)
            hi_negM (hcont_f.intervalIntegrable T (2 * T))
            (fun t ht => (abs_le.mp (hf_abs t ht)).1)
          rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
          linarith
        · have hhigh := intervalIntegral.integral_mono_on (by linarith : T ≤ 2 * T)
            (hcont_f.intervalIntegrable T (2 * T)) hi_M
            (fun t ht => (abs_le.mp (hf_abs t ht)).2)
          rw [intervalIntegral.integral_const, smul_eq_mul] at hhigh
          linarith
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
            rw [hc2]; ring
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
            linear_combination (c z / 2) * hcs + (c z / 2) * hca
          have hl0 : Tendsto
              (fun T : ℝ => c z * (T⁻¹ * ∫ t in T..(2 * T), Real.cos (z.im * t)))
              atTop (𝓝 0) :=
            by simpa [mul_zero] using (tendsto_avg_cos_zero hz_im0).const_mul (c z)
          have hl1 : Tendsto
              (fun T : ℝ => (c z / 2) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos ((z.im - γ₁) * t)))
              atTop (𝓝 0) :=
            by simpa [mul_zero] using (tendsto_avg_cos_zero him_ne_p).const_mul (c z / 2)
          have hl2 : Tendsto
              (fun T : ℝ => (c z / 2) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos ((z.im + γ₁) * t)))
              atTop (𝓝 0) :=
            by simpa [mul_zero] using (tendsto_avg_cos_zero him_ne_m).const_mul (c z / 2)
          have hcomb : Tendsto (fun T : ℝ =>
              c z * (T⁻¹ * ∫ t in T..(2 * T), Real.cos (z.im * t)) -
              (c z / 2) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos ((z.im - γ₁) * t)) -
              (c z / 2) * (T⁻¹ * ∫ t in T..(2 * T), Real.cos ((z.im + γ₁) * t)))
              atTop (𝓝 (0 - 0 - 0)) :=
            (hl0.sub hl1).sub hl2
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
    tendsto_finsetSum S hterm_lim
  have hsum_nn : 0 ≤ ∑ z ∈ S, termVal z := by
    refine ge_of_tendsto hsum_lim ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum
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
        have hzr : z ≠ (σ_max : ℂ) := fun h => hmem (h ▸ hz.2.2)
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
    hγ₁ (by have := congrArg Complex.im h; simp [z₁] at this; linarith)
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
      rw [hlv]; simp [hcz]
    rcases lt_or_eq_of_le (hmax z hz hcz) with hz_lt | hz_eq
    · have hnr : z ≠ (σ_max : ℂ) := fun h => by subst h; simp at hz_lt
      have hnz1 : z ≠ z₁ := fun h => by subst h; simp [z₁] at hz_lt
      have hncz1 : z ≠ conj z₁ := fun h => by subst h; simp [z₁] at hz_lt
      have hlv : limVal z = 0 := by simp [limVal, hnr, hnz1, hncz1]
      rw [hlv]
      have hdec : Tendsto (fun k : ℕ => |c z| * Real.exp ((z.re - σ_max) * tk k))
          atTop (𝓝 0) := by
        simpa [mul_zero] using
          ((Real.tendsto_exp_atBot.comp
            (tendsto_id.const_mul_atTop_of_neg (by linarith : z.re - σ_max < 0))).comp
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
    refine ge_of_tendsto (tendsto_finsetSum S hterm_lim) (Eventually.of_forall fun k => ?_)
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
        have hzr : z ≠ (σ_max : ℂ) := fun h => hmem (h ▸ hz.2.2)
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
  have hconj_pp : conj z_pp = z_pm := by simp [z_pp, z_pm, map_ofNat]; ring
  have hconj_pm : conj z_pm = z_pp := by simp [z_pp, z_pm, map_ofNat]
  have hconj_mp : conj z_mp = z_mm := by simp [z_mp, z_mm, map_ofNat]; ring
  have hconj_mm : conj z_mm = z_mp := by simp [z_mp, z_mm, map_ofNat]
  have hconj_cp : conj z_cp = z_cm := by simp [z_cp, z_cm, map_ofNat]; ring
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
      (simp [z_pp, z_pm, z_mp, z_mm, z_cp, z_cm]; try linarith)
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
      have hd_sub : ∀ z₀ : ℂ, DifferentiableAt ℂ (fun w : ℂ => w - z₀) s := fun z₀ => by fun_prop
      have hd_lin : ∀ z₀ : ℂ, logDeriv (fun w : ℂ => w - z₀) s = 1 / (s - z₀) := fun z₀ => by
        rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
      rw [hcrit_eq, hoff_eq,
          logDeriv_div (f := fun w => (w - z_cp) ^ 2 * (w - z_cm) ^ 2)
            (g := fun w => ((w - z_pp) * (w - z_pm)) * ((w - z_mp) * (w - z_mm))) s
            (mul_ne_zero (pow_ne_zero 2 hcp) (pow_ne_zero 2 hcm))
            (mul_ne_zero (mul_ne_zero hpp hpm) (mul_ne_zero hmp hmm))
            (((hd_sub z_cp).fun_pow 2).mul ((hd_sub z_cm).fun_pow 2))
            (((hd_sub z_pp).mul (hd_sub z_pm)).mul ((hd_sub z_mp).mul (hd_sub z_mm))),
          logDeriv_mul (f := fun w => (w - z_cp) ^ 2) (g := fun w => (w - z_cm) ^ 2) s
            (pow_ne_zero 2 hcp) (pow_ne_zero 2 hcm)
            ((hd_sub z_cp).fun_pow 2) ((hd_sub z_cm).fun_pow 2),
          logDeriv_fun_pow (hd_sub z_cp) 2,
          logDeriv_fun_pow (hd_sub z_cm) 2,
          logDeriv_mul (f := fun w => (w - z_pp) * (w - z_pm))
            (g := fun w => (w - z_mp) * (w - z_mm)) s
            (mul_ne_zero hpp hpm) (mul_ne_zero hmp hmm)
            ((hd_sub z_pp).mul (hd_sub z_pm)) ((hd_sub z_mp).mul (hd_sub z_mm)),
          logDeriv_mul (f := fun w => w - z_pp) (g := fun w => w - z_pm) s hpp hpm
            (hd_sub z_pp) (hd_sub z_pm),
          logDeriv_mul (f := fun w => w - z_mp) (g := fun w => w - z_mm) s hmp hmm
            (hd_sub z_mp) (hd_sub z_mm),
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
    (CurveDatum.exterior D k hk).sqrtq = D.sqrtq ^ k := by
  have hq0 : 0 ≤ D.q := by linarith [D.one_lt_q]
  have hsqrt_pow : ∀ n : ℕ, Real.sqrt (D.q ^ n) = Real.sqrt D.q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg hq0 n), ih, pow_succ]
  exact hsqrt_pow k

/-- The Frobenius eigenvalues of `CurveDatum.exterior D k hk` are the `k`-fold exterior products
`exteriorEigenvalue D S`. -/
theorem eigenvalue_exterior {ι : Type*} [Fintype ι] [DecidableEq ι] (D : CurveDatum ι)
    (k : ℕ) (hk : 1 ≤ k) (S : ExteriorIndex ι k) :
    eigenvalue (CurveDatum.exterior D k hk) S = exteriorEigenvalue D S.1 := by
  rw [eigenvalue, CurveDatum.sqrtq_exterior, exteriorEigenvalue]
  dsimp [CurveDatum.exterior]
  have hcard : ((D.sqrtq : ℂ)) ^ k = ∏ _i ∈ S.1, (D.sqrtq : ℂ) := by
    rw [Finset.prod_const, S.2]
  rw [Complex.ofReal_pow, hcard, ← Finset.prod_mul_distrib]
  rfl

/-- `detDeg` of the functorial exterior curve datum `CurveDatum.exterior D k hk` is
`exteriorDetDeg D k`. -/
theorem detDeg_exterior_eq_exteriorDetDeg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : CurveDatum ι) (k : ℕ) (hk : 1 ≤ k) (P : ℝ[X]) :
    detDeg (CurveDatum.exterior D k hk) P = exteriorDetDeg D k P := by
  rw [detDeg, exteriorDetDeg]
  refine Finset.prod_bij (fun (S : ExteriorIndex ι k) _ => S.1) ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S.1, S.2⟩
  · intro S₁ _ S₂ _ h
    exact Subtype.ext h
  · intro S hS
    exact ⟨⟨S, (Finset.mem_powersetCard.mp hS).2⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    rw [eigenvalue_exterior D k hk S]

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
    fin_cases i
    · dsimp
      rw [Complex.ofReal_inv]
      calc ((r : ℂ)⁻¹ * Complex.exp (-((θ : ℂ) * I))) * ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
          = ((r : ℂ)⁻¹ * (r : ℂ)) *
              (Complex.exp (-((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I)) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hrC, hexp_pm, mul_one]
    · dsimp
      rw [Complex.ofReal_inv]
      calc ((r : ℂ)⁻¹ * Complex.exp ((θ : ℂ) * I)) * ((r : ℂ) * Complex.exp (-((θ : ℂ) * I)))
          = ((r : ℂ)⁻¹ * (r : ℂ)) *
              (Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I))) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hrC, hexp_mp, mul_one]
    · dsimp
      rw [Complex.ofReal_inv]
      calc ((r : ℂ) * Complex.exp (-((θ : ℂ) * I))) * ((r : ℂ)⁻¹ * Complex.exp ((θ : ℂ) * I))
          = ((r : ℂ) * (r : ℂ)⁻¹) *
              (Complex.exp (-((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I)) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ hrC, hexp_pm, mul_one]
    · dsimp
      rw [Complex.ofReal_inv]
      calc ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) * ((r : ℂ)⁻¹ * Complex.exp (-((θ : ℂ) * I)))
          = ((r : ℂ) * (r : ℂ)⁻¹) *
              (Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I))) := by ring
        _ = 1 := by rw [mul_inv_cancel₀ hrC, hexp_mp, mul_one]

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
      have hc : Complex.cos (θ : ℂ) = (Real.cos θ : ℂ) := (Complex.ofReal_cos θ).symm
      have hs : Complex.sin (θ : ℂ) = (Real.sin θ : ℂ) := (Complex.ofReal_sin θ).symm
      rw [Complex.exp_mul_I, hc, hs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im]
      ring
    have hexp_m_im : (Complex.exp (-((θ : ℂ) * I))).im = -Real.sin θ := by
      have hm : -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
      have hc : Complex.cos ((-θ : ℝ) : ℂ) = (Real.cos (-θ) : ℂ) := (Complex.ofReal_cos (-θ)).symm
      have hs : Complex.sin ((-θ : ℝ) : ℂ) = (Real.sin (-θ) : ℂ) := (Complex.ofReal_sin (-θ)).symm
      rw [hm, Complex.exp_mul_I, hc, hs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_re, Complex.I_im, Real.sin_neg]
      ring
    fin_cases i
    · dsimp [eigenvalue, D, quartetCurveDatum]
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul, hexp_p_im]
      exact mul_ne_zero (mul_pos hsq_pos hr).ne' hsin
    · dsimp [eigenvalue, D, quartetCurveDatum]
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul, hexp_m_im]
      exact mul_ne_zero (mul_pos hsq_pos hr).ne' (neg_ne_zero.mpr hsin)
    · dsimp [eigenvalue, D, quartetCurveDatum]
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul, hexp_p_im]
      exact mul_ne_zero (mul_pos hsq_pos (inv_pos.mpr hr)).ne' hsin
    · dsimp [eigenvalue, D, quartetCurveDatum]
      rw [← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul, hexp_m_im]
      exact mul_ne_zero (mul_pos hsq_pos (inv_pos.mpr hr)).ne' (neg_ne_zero.mpr hsin)
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
    let D₂ := CurveDatum.exterior (quartetCurveDatum q hq r hr θ) 2 (by norm_num)
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
  · rw [eigenvalue_exterior D 2 (by norm_num), exteriorEigenvalue, Finset.prod_pair (by decide)]
    dsimp [eigenvalue, D, quartetCurveDatum]
    calc (D.sqrtq : ℂ) * ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) *
          ((D.sqrtq : ℂ) * ((r : ℂ) * Complex.exp (-((θ : ℂ) * I))))
        = ((D.sqrtq : ℂ) * (D.sqrtq : ℂ)) * (r : ℂ) ^ 2 *
          (Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I))) := by ring
      _ = ((q * r ^ 2 : ℝ) : ℂ) := by rw [hsq, hexp_pm, mul_one]; push_cast; ring
  · rw [eigenvalue_exterior D 2 (by norm_num), exteriorEigenvalue, Finset.prod_pair (by decide)]
    dsimp [eigenvalue, D, quartetCurveDatum]
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
    · change ‖∏ i ∈ S.1, D.β i‖ = 1
      rw [h, Finset.prod_pair (by decide)]
      dsimp [D, quartetCurveDatum]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hr.le, Real.norm_of_nonneg (inv_pos.mpr hr).le,
          hnorm_p, mul_one, mul_one, hrr]
    · change ‖∏ i ∈ S.1, D.β i‖ = 1
      rw [h, Finset.prod_pair (by decide)]
      dsimp [D, quartetCurveDatum]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hr.le, Real.norm_of_nonneg (inv_pos.mpr hr).le,
          hnorm_p, hnorm_m, mul_one, mul_one, hrr]
    · change ‖∏ i ∈ S.1, D.β i‖ = 1
      rw [h, Finset.prod_pair (by decide)]
      dsimp [D, quartetCurveDatum]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hr.le, Real.norm_of_nonneg (inv_pos.mpr hr).le,
          hnorm_m, hnorm_p, mul_one, mul_one, hrr]
    · change ‖∏ i ∈ S.1, D.β i‖ = 1
      rw [h, Finset.prod_pair (by decide)]
      dsimp [D, quartetCurveDatum]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hr.le, Real.norm_of_nonneg (inv_pos.mpr hr).le,
          hnorm_m, mul_one, mul_one, hrr]
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
      · intro p hp; simp only [Finset.mem_filter] at hp; exact Prod.ext rfl hp.2
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
    · rintro (⟨rfl, rfl⟩ | ⟨hu, hv⟩)
      · exact ⟨hab, rfl⟩
      · rw [hu, hv]; exact ⟨hab.symm, Finset.pair_comm b a⟩
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
  calc realPairPoly (1 / 2 + 2 * a) s *
        ((s - 1 / 2) ^ 2 * ((s - 1 / 2) ^ 2 + (2 * (γ : ℂ)) ^ 2)) *
        ((s - 1 / 2) ^ 2 / realPairPoly (1 / 2 + 2 * a) s)
      = (realPairPoly (1 / 2 + 2 * a) s *
          ((s - 1 / 2) ^ 2 / realPairPoly (1 / 2 + 2 * a) s)) *
          ((s - 1 / 2) ^ 2 * ((s - 1 / 2) ^ 2 + (2 * (γ : ℂ)) ^ 2)) := by ring
    _ = (s - 1 / 2) ^ 2 *
          ((s - 1 / 2) ^ 2 * ((s - 1 / 2) ^ 2 + (2 * (γ : ℂ)) ^ 2)) := by
          rw [mul_div_cancel₀ _ hnz]
    _ = (s - 1 / 2) ^ 4 * ((s - 1 / 2) ^ 2 + (2 * (γ : ℂ)) ^ 2) := by ring

/-! ### 4. Full-strip coupled symmetric-square contractions at zero pole tax -/

/-- Full-strip zero-pole-tax (`Δκ = 0`) coupled symmetric-square quartet multiplier
`coupledQuartetSymSquare b a γ s = M_{1/2 + b}(s)² · Q_crit(γ; s) / Q_off(a, γ; s)`.
At `b = a`, this attains the sharp `2 : 1` single-ordinate real-anchor bound across the entire
strip `0 < a < 1/2`. -/
def coupledQuartetSymSquare (b a γ : ℝ) (s : ℂ) : ℂ :=
  midpointSymSquare (1 / 2 + b) s ^ 2 * (quartetCritPoly γ s / quartetOffPoly a γ s)

/-- Zero-pole-tax (`Δκ = 0`) single-deep-real-anchor quartet multiplier
`deepRealQuartetSymSquare b a γ s = M_{1/2 + b}(s) · Q_crit(γ; s) / Q_off(a, γ; s)`,
positive-definite on `σ > 1` whenever `0 < a` and `2a ≤ b < 1/2`. -/
def deepRealQuartetSymSquare (b a γ : ℝ) (s : ℂ) : ℂ :=
  midpointSymSquare (1 / 2 + b) s * (quartetCritPoly γ s / quartetOffPoly a γ s)

private theorem re_one_div_laplace_cos' (a b : ℝ) (ha : 0 < a) :
    (1 / ((a : ℂ) + (b : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0, Real.exp (-a * t) * Real.cos (b * t) := by
  set w : ℂ := -((a : ℂ) + (b : ℂ) * I)
  have hw_re : w.re < 0 := by simp [w]; linarith
  have hint_c : IntegrableOn (fun t : ℝ => Complex.exp (w * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hw_re 0
  have hval := integral_exp_mul_complex_Ioi hw_re 0
  have hrhs_eq : -Complex.exp (w * (0 : ℝ)) / w = 1 / ((a : ℂ) + (b : ℂ) * I) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    dsimp only [w]
    rw [div_neg, neg_div, neg_neg]
  rw [hrhs_eq] at hval
  have hre_int : (∫ t : ℝ in Ioi 0, Complex.exp (w * t)).re =
      ∫ t : ℝ in Ioi 0, (Complex.exp (w * t)).re :=
    (Complex.reCLM.integral_comp_comm hint_c).symm
  rw [← hval, hre_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hw_t_re : (w * (t : ℂ)).re = -a * t := by simp [w]
  have hw_t_im : (w * (t : ℂ)).im = -(b * t) := by simp [w]
  rw [Complex.exp_re, hw_t_re, hw_t_im, Real.cos_neg]

private theorem integrableOn_exp_cos_Ioi' (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Real.cos (b * t)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0)
    ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

private theorem isEvenPosDef_laplace_cos' {w φ : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hw_cont : Continuous w)
    (hw_nn : ∀ t : ℝ, 0 < t → 0 ≤ w t)
    (hw_le : ∀ t : ℝ, 0 < t → w t ≤ C * Real.exp (-a * t))
    (hφ : ∀ u : ℝ, φ u = ∫ t : ℝ in Ioi 0, w t * Real.cos (t * u)) :
    IsEvenPosDef φ := by
  have hint_dom : IntegrableOn (fun t : ℝ => C * Real.exp (-a * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0).const_mul C
  have hint_ker : ∀ u : ℝ,
      IntegrableOn (fun t : ℝ => w t * Real.cos (t * u)) (Ioi 0) := by
    intro u
    refine Integrable.mono' hint_dom
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nn t ht)]
    exact (mul_le_of_le_one_right (hw_nn t ht) (Real.abs_cos_le_one _)).trans (hw_le t ht)
  refine ⟨fun u => ?_, fun n x c => ?_⟩
  · rw [hφ (-u), hφ u]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_neg, Real.cos_neg]
  · have hsum_int : ∑ i, ∑ j, c i * c j * φ (x i - x j) =
        ∫ t : ℝ in Ioi 0, w t * ∑ i, ∑ j, c i * c j * Real.cos (t * (x i - x j)) := by
      simp_rw [hφ, ← integral_const_mul]
      have h1 : ∀ i : Fin n,
          ∑ j : Fin n, ∫ t : ℝ in Ioi 0, c i * c j * (w t * Real.cos (t * (x i - x j))) =
          ∫ t : ℝ in Ioi 0, ∑ j : Fin n, c i * c j * (w t * Real.cos (t * (x i - x j))) :=
        fun i => (integral_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)).symm
      simp_rw [h1]
      rw [← integral_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum_int]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    refine mul_nonneg (hw_nn t ht) ?_
    rw [gram_cos_eq]
    positivity

private theorem isEvenPosDef_add_coupled {φ ψ : ℝ → ℝ}
    (hφ : IsEvenPosDef φ) (hψ : IsEvenPosDef ψ) :
    IsEvenPosDef (fun u => φ u + ψ u) where
  even u := by rw [hφ.even, hψ.even]
  posDef n x c := by
    have h : (∑ i, ∑ j, c i * c j * (φ (x i - x j) + ψ (x i - x j))) =
        (∑ i, ∑ j, c i * c j * φ (x i - x j)) + ∑ i, ∑ j, c i * c j * ψ (x i - x j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    rw [h]
    exact add_nonneg (hφ.posDef n x c) (hψ.posDef n x c)

private theorem sq_add_sq_eq_mul_I' (w : ℂ) (x γ : ℝ) :
    (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2 =
      (w - ((x : ℂ) + (γ : ℂ) * I)) * (w - ((x : ℂ) - (γ : ℂ) * I)) := by
  calc (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2
      = (w - (x : ℂ)) ^ 2 - ((γ : ℂ) * I) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    _ = (w - ((x : ℂ) + (γ : ℂ) * I)) * (w - ((x : ℂ) - (γ : ℂ) * I)) := by ring

private theorem re_neg_logDeriv_midpointSymSquare_shift_eq {b σ : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1 / 2) (hσ : 1 < σ) (u : ℝ) :
    (-logDeriv (midpointSymSquare (1 / 2 + b)) ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) *
          (Real.exp (t / 2) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2) *
          Real.cos (t * u) := by
  set β : ℝ := 1 / 2 + b
  have hβ0 : 0 ≤ β := by dsimp [β]; linarith
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  have hs_half : s - 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hs_β1 : s - (β : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hs_β2 : s - ((1 - β : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hd_sub : ∀ c : ℂ, DifferentiableAt ℂ (fun z : ℂ => z - c) s := fun _ => by fun_prop
  have hd_lin : ∀ c : ℂ, logDeriv (fun z : ℂ => z - c) s = 1 / (s - c) := fun c => by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  have hld : -logDeriv (midpointSymSquare β) s =
      1 / (s - (β : ℂ)) + 1 / (s - ((1 - β : ℝ) : ℂ)) - 2 * (1 / (s - 1 / 2)) := by
    unfold midpointSymSquare realPairPoly
    rw [logDeriv_div (f := fun z : ℂ => (z - 1 / 2) ^ 2)
          (g := fun z : ℂ => (z - (β : ℂ)) * (z - ((1 - β : ℝ) : ℂ)))
          s (pow_ne_zero 2 hs_half) (mul_ne_zero hs_β1 hs_β2)
          ((hd_sub (1 / 2)).fun_pow 2)
          ((hd_sub (β : ℂ)).mul (hd_sub ((1 - β : ℝ) : ℂ))),
        logDeriv_fun_pow (hd_sub (1 / 2)) 2,
        logDeriv_mul (f := fun z : ℂ => z - (β : ℂ))
          (g := fun z : ℂ => z - ((1 - β : ℝ) : ℂ))
          s hs_β1 hs_β2 (hd_sub (β : ℂ)) (hd_sub ((1 - β : ℝ) : ℂ)),
        hd_lin, hd_lin, hd_lin]
    push_cast; ring
  have e1 : s - (β : ℂ) = (((σ - β : ℝ) : ℂ) + (u : ℂ) * I) := by rw [hs_def]; push_cast; ring
  have e2 : s - ((1 - β : ℝ) : ℂ) = (((σ - (1 - β) : ℝ) : ℂ) + (u : ℂ) * I) := by
    rw [hs_def]; push_cast; ring
  have e3 : s - 1 / 2 = (((σ - 1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by rw [hs_def]; push_cast; ring
  have hre : (-logDeriv (midpointSymSquare β) s).re =
      ((1 / (s - (β : ℂ))).re + (1 / (s - ((1 - β : ℝ) : ℂ))).re) -
        2 * (1 / (s - 1 / 2)).re := by
    rw [hld]
    have h2 : (2 * (1 / (s - 1 / 2))).re = 2 * (1 / (s - 1 / 2)).re := by
      simp [Complex.mul_re]
    rw [Complex.sub_re, Complex.add_re, h2]
  change (-logDeriv (midpointSymSquare β) s).re = _
  rw [hre, e1, e2, e3,
      re_one_div_laplace_cos' (σ - β) u (by linarith),
      re_one_div_laplace_cos' (σ - (1 - β)) u (by linarith),
      re_one_div_laplace_cos' (σ - 1 / 2) u (by linarith)]
  have hi1 := integrableOn_exp_cos_Ioi' (σ - β) u (by linarith)
  have hi2 := integrableOn_exp_cos_Ioi' (σ - (1 - β)) u (by linarith)
  have hi3_base := integrableOn_exp_cos_Ioi' (σ - 1 / 2) u (by linarith)
  have hi12 : IntegrableOn (fun t : ℝ =>
      Real.exp (-(σ - β) * t) * Real.cos (u * t) +
        Real.exp (-(σ - (1 - β)) * t) * Real.cos (u * t)) (Ioi 0) := hi1.add hi2
  have hi3 : IntegrableOn (fun t : ℝ =>
      2 * (Real.exp (-(σ - 1 / 2) * t) * Real.cos (u * t))) (Ioi 0) := hi3_base.const_mul 2
  symm
  calc ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) *
          (Real.exp (t / 2) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2) *
          Real.cos (t * u)
      = ∫ t : ℝ in Ioi 0,
          ((Real.exp (-(σ - β) * t) * Real.cos (u * t) +
              Real.exp (-(σ - (1 - β)) * t) * Real.cos (u * t)) -
            2 * (Real.exp (-(σ - 1 / 2) * t) * Real.cos (u * t))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        have hexp1 : Real.exp (-(σ - β) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) * Real.exp (b * t / 2) ^ 2 := by
          dsimp [β]; rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have hexp2 : Real.exp (-(σ - (1 - β)) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) * Real.exp (-(b * t / 2)) ^ 2 := by
          dsimp [β]; rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have hexp3 : Real.exp (-(σ - 1 / 2) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) *
              (Real.exp (b * t / 2) * Real.exp (-(b * t / 2))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [hexp1, hexp2, hexp3, mul_comm u t]
        ring
    _ = _ := by
        rw [integral_sub hi12 hi3, integral_add hi1 hi2, integral_const_mul]

private theorem re_logDeriv_sq_add_sq_laplace_cos' (σ u x γ : ℝ) (hx : x < σ) :
    (logDeriv (fun w : ℂ => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2) ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0, 2 * Real.exp (-(σ - x) * t) * Real.cos (γ * t) * Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  set z₁ : ℂ := (x : ℂ) + (γ : ℂ) * I
  set z₂ : ℂ := (x : ℂ) - (γ : ℂ) * I
  have hz₁ : s - z₁ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def, z₁] at this; linarith
  have hz₂ : s - z₂ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def, z₂] at this; linarith
  have hfun : (fun w : ℂ => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2) =
      fun w : ℂ => (w - z₁) * (w - z₂) :=
    funext fun w => sq_add_sq_eq_mul_I' w x γ
  have hd_sub : ∀ c : ℂ, DifferentiableAt ℂ (fun w : ℂ => w - c) s := fun _ => by fun_prop
  have hld : logDeriv (fun w : ℂ => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2) s =
      1 / (s - z₁) + 1 / (s - z₂) := by
    rw [hfun, logDeriv_mul (f := fun w => w - z₁) (g := fun w => w - z₂) s hz₁ hz₂
      (hd_sub z₁) (hd_sub z₂)]
    congr 1 <;> rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  have e₁ : s - z₁ = (((σ - x : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) := by
    dsimp [s, z₁]; push_cast; ring
  have e₂ : s - z₂ = (((σ - x : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I) := by
    dsimp [s, z₂]; push_cast; ring
  rw [hld, Complex.add_re, e₁, e₂,
      re_one_div_laplace_cos' (σ - x) (u - γ) (by linarith),
      re_one_div_laplace_cos' (σ - x) (u + γ) (by linarith),
      ← integral_add (integrableOn_exp_cos_Ioi' (σ - x) (u - γ) (by linarith))
        (integrableOn_exp_cos_Ioi' (σ - x) (u + γ) (by linarith))]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hc₁ : Real.cos ((u - γ) * t) =
      Real.cos (t * u) * Real.cos (γ * t) + Real.sin (t * u) * Real.sin (γ * t) := by
    rw [show (u - γ) * t = t * u - γ * t by ring, Real.cos_sub]
  have hc₂ : Real.cos ((u + γ) * t) =
      Real.cos (t * u) * Real.cos (γ * t) - Real.sin (t * u) * Real.sin (γ * t) := by
    rw [show (u + γ) * t = t * u + γ * t by ring, Real.cos_add]
  rw [hc₁, hc₂]
  ring

private theorem re_neg_logDeriv_quartetRatio_eq {a γ σ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hσ : 1 < σ) (u : ℝ) :
    (-logDeriv (fun w => quartetCritPoly γ w / quartetOffPoly a γ w)
        ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) *
          (2 * Real.exp (t / 2) * Real.cos (γ * t) *
            (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  let qAt : ℝ → ℂ → ℂ := fun x w => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2
  have hq_nz : ∀ x : ℝ, x < σ → qAt x s ≠ 0 := by
    intro x hx
    dsimp [qAt]
    rw [sq_add_sq_eq_mul_I']
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hnz_c := hq_nz (1 / 2) (by linarith)
  have hnz_p := hq_nz (1 / 2 + a) (by linarith)
  have hnz_m := hq_nz (1 / 2 - a) (by linarith)
  have hratio_eq : (fun w => quartetCritPoly γ w / quartetOffPoly a γ w) =
      fun w => qAt (1 / 2) w ^ 2 / (qAt (1 / 2 + a) w * qAt (1 / 2 - a) w) := by
    funext w
    unfold quartetCritPoly quartetOffPoly
    dsimp [qAt]
    norm_num
  have hld : -logDeriv (fun w => quartetCritPoly γ w / quartetOffPoly a γ w) s =
      logDeriv (qAt (1 / 2 + a)) s + logDeriv (qAt (1 / 2 - a)) s -
        2 * logDeriv (qAt (1 / 2)) s := by
    rw [hratio_eq,
        logDeriv_div (f := fun w => qAt (1 / 2) w ^ 2)
          (g := fun w => qAt (1 / 2 + a) w * qAt (1 / 2 - a) w)
          s (pow_ne_zero 2 hnz_c) (mul_ne_zero hnz_p hnz_m)
          (by dsimp [qAt]; fun_prop) (by dsimp [qAt]; fun_prop),
        logDeriv_fun_pow (by dsimp [qAt]; fun_prop) 2,
        logDeriv_mul (f := qAt (1 / 2 + a)) (g := qAt (1 / 2 - a)) s hnz_p hnz_m
          (by dsimp [qAt]; fun_prop) (by dsimp [qAt]; fun_prop)]
    push_cast; ring
  have hre : (-logDeriv (fun w => quartetCritPoly γ w / quartetOffPoly a γ w) s).re =
      ((logDeriv (qAt (1 / 2 + a)) s).re + (logDeriv (qAt (1 / 2 - a)) s).re) -
        2 * (logDeriv (qAt (1 / 2)) s).re := by
    rw [hld]
    have h2 : (2 * logDeriv (qAt (1 / 2)) s).re = 2 * (logDeriv (qAt (1 / 2)) s).re := by
      simp [Complex.mul_re]
    rw [Complex.sub_re, Complex.add_re, h2]
  rw [hre]
  dsimp [qAt]
  rw [re_logDeriv_sq_add_sq_laplace_cos' σ u (1 / 2 + a) γ (by linarith),
      re_logDeriv_sq_add_sq_laplace_cos' σ u (1 / 2 - a) γ (by linarith),
      re_logDeriv_sq_add_sq_laplace_cos' σ u (1 / 2) γ (by linarith)]
  have hint : ∀ x : ℝ, x < σ →
      IntegrableOn
        (fun t : ℝ => 2 * Real.exp (-(σ - x) * t) * Real.cos (γ * t) * Real.cos (t * u))
        (Ioi 0) := by
    intro x hx
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -(σ - x) < 0) 0).const_mul 2)
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (Real.exp_pos _)]
    have hc1 := Real.abs_cos_le_one (γ * t)
    have hc2 := Real.abs_cos_le_one (t * u)
    have hprod : |Real.cos (γ * t)| * |Real.cos (t * u)| ≤ 1 :=
      mul_le_one₀ hc1 (abs_nonneg _) hc2
    calc 2 * Real.exp (-(σ - x) * t) * |Real.cos (γ * t)| * |Real.cos (t * u)|
        = 2 * Real.exp (-(σ - x) * t) * (|Real.cos (γ * t)| * |Real.cos (t * u)|) := by ring
      _ ≤ 2 * Real.exp (-(σ - x) * t) * 1 :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 2 * Real.exp (-(σ - x) * t) := mul_one _
  have hip := hint (1 / 2 + a) (by linarith)
  have him := hint (1 / 2 - a) (by linarith)
  have hic_base := hint (1 / 2) (by linarith)
  have hipm : IntegrableOn (fun t : ℝ =>
      2 * Real.exp (-(σ - (1 / 2 + a)) * t) * Real.cos (γ * t) * Real.cos (t * u) +
        2 * Real.exp (-(σ - (1 / 2 - a)) * t) * Real.cos (γ * t) * Real.cos (t * u)) (Ioi 0) :=
    hip.add him
  have hic : IntegrableOn (fun t : ℝ =>
      2 * (2 * Real.exp (-(σ - 1 / 2) * t) * Real.cos (γ * t) * Real.cos (t * u))) (Ioi 0) :=
    hic_base.const_mul 2
  symm
  calc ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) *
          (2 * Real.exp (t / 2) * Real.cos (γ * t) *
            (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u)
      = ∫ t : ℝ in Ioi 0,
          ((2 * Real.exp (-(σ - (1 / 2 + a)) * t) * Real.cos (γ * t) * Real.cos (t * u) +
              2 * Real.exp (-(σ - (1 / 2 - a)) * t) * Real.cos (γ * t) * Real.cos (t * u)) -
            2 * (2 * Real.exp (-(σ - 1 / 2) * t) * Real.cos (γ * t) * Real.cos (t * u))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        have he_p : Real.exp (-(σ - (1 / 2 + a)) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) * Real.exp (a * t / 2) ^ 2 := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have he_m : Real.exp (-(σ - (1 / 2 - a)) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) * Real.exp (-(a * t / 2)) ^ 2 := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have he_c : Real.exp (-(σ - 1 / 2) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) *
              (Real.exp (a * t / 2) * Real.exp (-(a * t / 2))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [he_p, he_m, he_c]
        ring
    _ = _ := by
        rw [integral_sub hipm hic, integral_add hip him, integral_const_mul]

private theorem exp_sinh_sq_le_exp_half {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1 / 2) (ht : 0 < t) :
    (Real.exp (x * t / 2) - Real.exp (-(x * t / 2))) ^ 2 ≤ Real.exp (t / 2) := by
  have hnn : 0 ≤ Real.exp (x * t / 2) - Real.exp (-(x * t / 2)) := by
    have : Real.exp (-(x * t / 2)) ≤ Real.exp (x * t / 2) := Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hle : Real.exp (x * t / 2) - Real.exp (-(x * t / 2)) ≤ Real.exp (t / 4) := by
    have : Real.exp (x * t / 2) ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr (by nlinarith)
    linarith [Real.exp_pos (-(x * t / 2))]
  calc (Real.exp (x * t / 2) - Real.exp (-(x * t / 2))) ^ 2
      ≤ Real.exp (t / 4) ^ 2 := pow_le_pow_left₀ hnn hle 2
    _ = Real.exp (t / 2) := by rw [sq, ← Real.exp_add]; congr 1; ring

private theorem re_neg_logDeriv_midpointPow_quartet_eq (m : ℕ) {b a γ σ : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b < 1 / 2) (ha0 : 0 < a) (ha1 : a < 1 / 2) (hσ : 1 < σ) (u : ℝ) :
    (-logDeriv
        (fun s => midpointSymSquare (1 / 2 + b) s ^ m * (quartetCritPoly γ s / quartetOffPoly a γ s))
        ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) * Real.exp (t / 2) *
          ((m : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  set Q : ℂ → ℂ := fun w => quartetCritPoly γ w / quartetOffPoly a γ w
  have hMb_nz : midpointSymSquare (1 / 2 + b) s ≠ 0 := by
    unfold midpointSymSquare realPairPoly
    refine div_ne_zero (pow_ne_zero 2 (fun h => ?_)) (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hQ_nz : Q s ≠ 0 := by
    dsimp [Q]; unfold quartetCritPoly quartetOffPoly
    have hnz : ∀ x : ℝ, x < σ → (s - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2 ≠ 0 := by
      intro x hx
      rw [sq_add_sq_eq_mul_I']
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h; simp [hs_def] at this; linarith
      · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hc : (s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2 ≠ 0 := by
      simpa using hnz (1 / 2) (by linarith)
    exact div_ne_zero (pow_ne_zero 2 hc)
      (mul_ne_zero (hnz (1 / 2 + a) (by linarith)) (hnz (1 / 2 - a) (by linarith)))
  have hMb_diff : DifferentiableAt ℂ (midpointSymSquare (1 / 2 + b)) s := by
    unfold midpointSymSquare realPairPoly
    refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hQ_diff : DifferentiableAt ℂ Q s := by
    dsimp [Q]; unfold quartetCritPoly quartetOffPoly
    refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
    refine mul_ne_zero ?_ ?_ <;>
      (rw [sq_add_sq_eq_mul_I']; refine mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hld : (-logDeriv (fun z => midpointSymSquare (1 / 2 + b) z ^ m * Q z) s).re =
      (m : ℝ) * (-logDeriv (midpointSymSquare (1 / 2 + b)) s).re + (-logDeriv Q s).re := by
    rw [logDeriv_mul (f := fun z => midpointSymSquare (1 / 2 + b) z ^ m) (g := Q) s
          (pow_ne_zero m hMb_nz) hQ_nz (hMb_diff.fun_pow m) hQ_diff,
        logDeriv_fun_pow hMb_diff m, neg_add, Complex.add_re]
    congr 1
    have : -((m : ℂ) * logDeriv (midpointSymSquare (1 / 2 + b)) s) =
        ((m : ℝ) : ℂ) * (-logDeriv (midpointSymSquare (1 / 2 + b)) s) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  change (-logDeriv (fun z => midpointSymSquare (1 / 2 + b) z ^ m * Q z) s).re = _
  rw [hld, re_neg_logDeriv_midpointSymSquare_shift_eq hb0 hb1 hσ u,
      re_neg_logDeriv_quartetRatio_eq ha0 ha1 hσ u]
  have hi1 : IntegrableOn
      (fun t : ℝ => Real.exp (-σ * t) *
        (Real.exp (t / 2) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2) *
        Real.cos (t * u)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -(σ - 1) < 0) 0).const_mul 1)
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    have hsq := exp_sinh_sq_le_exp_half hb0 hb1 ht
    calc Real.exp (-σ * t) *
          (Real.exp (t / 2) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2) *
          |Real.cos (t * u)|
        ≤ Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le) (Real.exp_pos _).le)
            (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = 1 * Real.exp (-(σ - 1) * t) := by
          rw [mul_one, one_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hi2 : IntegrableOn
      (fun t : ℝ => Real.exp (-σ * t) *
        (2 * Real.exp (t / 2) * Real.cos (γ * t) *
          (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
        Real.cos (t * u)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -(σ - 1) < 0) 0).const_mul 2)
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hsq := exp_sinh_sq_le_exp_half ha0.le ha1 ht
    have hmid : |2 * Real.exp (t / 2) * Real.cos (γ * t) *
        (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2| ≤
        2 * (Real.exp (t / 2) * Real.exp (t / 2)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))))]
      have hp : |Real.cos (γ * t)| *
          (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤ Real.exp (t / 2) := by
        calc |Real.cos (γ * t)| * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2
            ≤ 1 * Real.exp (t / 2) := mul_le_mul (Real.abs_cos_le_one _) hsq (sq_nonneg _) zero_le_one
          _ = Real.exp (t / 2) := one_mul _
      calc 2 * Real.exp (t / 2) * |Real.cos (γ * t)| *
            (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2
          = 2 * Real.exp (t / 2) *
              (|Real.cos (γ * t)| * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) := by ring
        _ ≤ 2 * Real.exp (t / 2) * Real.exp (t / 2) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = 2 * (Real.exp (t / 2) * Real.exp (t / 2)) := by ring
    calc Real.exp (-σ * t) * |2 * Real.exp (t / 2) * Real.cos (γ * t) *
          (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2| * |Real.cos (t * u)|
        ≤ Real.exp (-σ * t) * (2 * (Real.exp (t / 2) * Real.exp (t / 2))) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmid (Real.exp_pos _).le)
            (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = 2 * Real.exp (-(σ - 1) * t) := by
          rw [mul_one, show Real.exp (-σ * t) * (2 * (Real.exp (t / 2) * Real.exp (t / 2))) =
            2 * (Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2))) by ring,
            ← Real.exp_add, ← Real.exp_add]
          congr 2; ring
  have hi1m := hi1.const_mul (m : ℝ)
  symm
  calc ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) * Real.exp (t / 2) *
          ((m : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u)
      = ∫ t : ℝ in Ioi 0,
          ((m : ℝ) * (Real.exp (-σ * t) *
              (Real.exp (t / 2) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2) *
              Real.cos (t * u)) +
            Real.exp (-σ * t) *
              (2 * Real.exp (t / 2) * Real.cos (γ * t) *
                (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
              Real.cos (t * u)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        ring
    _ = _ := by
        rw [integral_add hi1m hi2, integral_const_mul]

/-- **Full-strip Bochner positivity of `coupledQuartetSymSquare` (`0 < a ≤ b < 1/2`, `Δκ = 0`).**
At `b = a`, `coupledQuartetSymSquare a a γ` attains the sharp `2 : 1` single-ordinate real-anchor
bound across the entire strip `0 < a < 1/2` with zero boundary poles. -/
theorem isEvenPosDef_coupledQuartetSymSquare {b a γ σ : ℝ}
    (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1 / 2) (hσ : 1 < σ) :
    IsEvenPosDef fun u : ℝ =>
      (-logDeriv (coupledQuartetSymSquare b a γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
  refine isEvenPosDef_laplace_cos' (C := 4) (a := σ - 1) (by linarith) (by fun_prop)
    (fun t ht => ?_) (fun t ht => ?_)
    (re_neg_logDeriv_midpointPow_quartet_eq 2 (by linarith) hb1 ha0 (by linarith) hσ)
  · have ha_nn : 0 ≤ Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) := by
      have : Real.exp (-(a * t / 2)) ≤ Real.exp (a * t / 2) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hab_le : Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) ≤
        Real.exp (b * t / 2) - Real.exp (-(b * t / 2)) := by
      have h1 : Real.exp (a * t / 2) ≤ Real.exp (b * t / 2) := Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (-(b * t / 2)) ≤ Real.exp (-(a * t / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hsq_le : (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 :=
      pow_le_pow_left₀ ha_nn hab_le 2
    have hcos : -1 ≤ Real.cos (γ * t) := Real.neg_one_le_cos _
    have hinner : 0 ≤ ((2 : ℕ) : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 := by
      simp only [Nat.cast_ofNat]
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), hsq_le, hcos]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hinner
  · have hb_sq := exp_sinh_sq_le_exp_half (by linarith : 0 ≤ b) hb1 ht
    have ha_sq := exp_sinh_sq_le_exp_half ha0.le (by linarith : a < 1 / 2) ht
    have hcos1 : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
    have hinner_le : ((2 : ℕ) : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        4 * Real.exp (t / 2) := by
      simp only [Nat.cast_ofNat]
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), hb_sq, ha_sq, hcos1]
    calc Real.exp (-σ * t) * Real.exp (t / 2) *
          (((2 : ℕ) : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2)
        ≤ Real.exp (-σ * t) * Real.exp (t / 2) * (4 * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left hinner_le (by positivity)
      _ = 4 * (Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2))) := by ring
      _ = 4 * Real.exp (-(σ - 1) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

/-- **Bochner positivity of `deepRealQuartetSymSquare` (`0 < a`, `2a ≤ b < 1/2`, `Δκ = 0`).**
A single real zero pair at depth `b ≥ 2a` anchors a complex quartet at depth `a` at zero pole tax. -/
theorem isEvenPosDef_deepRealQuartetSymSquare {b a γ σ : ℝ}
    (ha0 : 0 < a) (hab : 2 * a ≤ b) (hb1 : b < 1 / 2) (hσ : 1 < σ) :
    IsEvenPosDef fun u : ℝ =>
      (-logDeriv (deepRealQuartetSymSquare b a γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
  have hfun : deepRealQuartetSymSquare b a γ =
      fun s => midpointSymSquare (1 / 2 + b) s ^ 1 * (quartetCritPoly γ s / quartetOffPoly a γ s) := by
    funext s; simp [deepRealQuartetSymSquare]
  rw [hfun]
  refine isEvenPosDef_laplace_cos' (C := 3) (a := σ - 1) (by linarith) (by fun_prop)
    (fun t ht => ?_) (fun t ht => ?_)
    (re_neg_logDeriv_midpointPow_quartet_eq 1 (by linarith) hb1 ha0 (by linarith) hσ)
  · have ha_nn : 0 ≤ Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) := by
      have : Real.exp (-(a * t / 2)) ≤ Real.exp (a * t / 2) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hsum_ge2 : 2 ≤ Real.exp (a * t / 2) + Real.exp (-(a * t / 2)) := by
      have hprod : Real.exp (a * t / 4) * Real.exp (-(a * t / 4)) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hsq1 : Real.exp (a * t / 4) ^ 2 = Real.exp (a * t / 2) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hsq2 : Real.exp (-(a * t / 4)) ^ 2 = Real.exp (-(a * t / 2)) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      nlinarith [sq_nonneg (Real.exp (a * t / 4) - Real.exp (-(a * t / 4))), hprod, hsq1, hsq2]
    have hfac : Real.exp (a * t) - Real.exp (-(a * t)) =
        (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) *
          (Real.exp (a * t / 2) + Real.exp (-(a * t / 2))) := by
      have hsq1 : Real.exp (a * t / 2) ^ 2 = Real.exp (a * t) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hsq2 : Real.exp (-(a * t / 2)) ^ 2 = Real.exp (-(a * t)) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      nlinarith [hsq1, hsq2]
    have hab_le : Real.exp (a * t) - Real.exp (-(a * t)) ≤
        Real.exp (b * t / 2) - Real.exp (-(b * t / 2)) := by
      have h1 : Real.exp (a * t) ≤ Real.exp (b * t / 2) := Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (-(b * t / 2)) ≤ Real.exp (-(a * t)) := Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have h2_le : 2 * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ≤
        Real.exp (b * t / 2) - Real.exp (-(b * t / 2)) := by
      nlinarith [hfac, hab_le, ha_nn, hsum_ge2]
    have h4_sq : 4 * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 := by
      have hpow := pow_le_pow_left₀ (by positivity) h2_le 2
      linarith
    have hcos : -1 ≤ Real.cos (γ * t) := Real.neg_one_le_cos _
    have hinner : 0 ≤ ((1 : ℕ) : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 := by
      simp only [Nat.cast_one, one_mul]
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), h4_sq, hcos]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hinner
  · have hb_sq := exp_sinh_sq_le_exp_half (by linarith : 0 ≤ b) hb1 ht
    have ha_sq := exp_sinh_sq_le_exp_half ha0.le (by linarith : a < 1 / 2) ht
    have hcos1 : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
    have hinner_le : ((1 : ℕ) : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        3 * Real.exp (t / 2) := by
      simp only [Nat.cast_one, one_mul]
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), hb_sq, ha_sq, hcos1]
    calc Real.exp (-σ * t) * Real.exp (t / 2) *
          (((1 : ℕ) : ℝ) * (Real.exp (b * t / 2) - Real.exp (-(b * t / 2))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2)
        ≤ Real.exp (-σ * t) * Real.exp (t / 2) * (3 * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left hinner_le (by positivity)
      _ = 3 * (Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2))) := by ring
      _ = 3 * Real.exp (-(σ - 1) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

private theorem orderOneEnvelope_sub_const' (c : ℂ) :
    OrderOneEnvelope (fun s : ℂ => s - c) :=
  (RHTower.orderOneEnvelope_id.add (orderOneEnvelope_const (-c))).congr fun s => by ring

private theorem orderOneEnvelope_pow_sub_const (c : ℂ) :
    ∀ n : ℕ, OrderOneEnvelope (fun s : ℂ => (s - c) ^ n)
  | 0 => (orderOneEnvelope_const 1).congr fun s => by simp
  | n + 1 => ((orderOneEnvelope_pow_sub_const c n).mul (orderOneEnvelope_sub_const' c)).congr
      fun s => by rw [pow_succ]

private theorem dslope_entire_and_orderOne' {f : ℂ → ℂ} {z₀ : ℂ}
    (hd : Differentiable ℂ f) (hf : OrderOneEnvelope f) (hz₀ : f z₀ = 0) :
    Differentiable ℂ (dslope f z₀) ∧
      OrderOneEnvelope (dslope f z₀) ∧
      ∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s := by
  have hD : Differentiable ℂ (dslope f z₀) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 z₀)).mpr
      hd.differentiableOn
  have hid : ∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s := fun s => by
    simpa [hz₀, smul_eq_mul] using sub_smul_dslope f z₀ s
  refine ⟨hD, ?_, hid⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  obtain ⟨C, _, hb⟩ := hf
  obtain ⟨D, _, hDb⟩ := orderOneEnvelope_const (B : ℂ)
  refine ⟨C + D, by linarith, fun z => ?_⟩
  by_cases hz : ‖z - z₀‖ ≤ 1
  · have hmem : z ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
    have hBabs : B ≤ ‖(B : ℂ)‖ := by simpa using le_abs_self B
    exact (hB z hmem).trans (hBabs.trans ((hDb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : D ≤ C + D) z))))
  · have hn := congrArg norm (hid z)
    rw [norm_mul] at hn
    have hle : ‖dslope f z₀ z‖ ≤ ‖f z‖ := by
      have hz1 : 1 ≤ ‖z - z₀‖ := le_of_not_ge hz
      nlinarith [norm_nonneg (dslope f z₀ z)]
    exact hle.trans ((hb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : C ≤ C + D) z)))

private theorem exists_quotient_pow_sub :
    ∀ (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ},
      Differentiable ℂ f → OrderOneEnvelope f →
      (m : ℕ∞) ≤ analyticOrderAt f z₀ →
      ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ OrderOneEnvelope Q ∧
        (∀ s : ℂ, (s - z₀) ^ m * Q s = f s) ∧
        analyticOrderAt f z₀ = (m : ℕ) + analyticOrderAt Q z₀ ∧
        (∀ w : ℂ, w ≠ z₀ → analyticOrderAt Q w = analyticOrderAt f w)
  | 0, f, _, hdf, hof, _ =>
      ⟨f, hdf, hof, fun s => by simp, by simp, fun _ _ => rfl⟩
  | m + 1, f, z₀, hdf, hof, hm => by
      have hf0 : f z₀ = 0 := by
        by_contra hnz
        rw [(hdf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hnz] at hm
        exact absurd hm (by simp)
      obtain ⟨hdg, hog, hg_eq⟩ := dslope_entire_and_orderOne' hdf hof hf0
      have hfeq : (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) = f :=
        funext fun s => by simpa using hg_eq s
      have han_lin : AnalyticAt ℂ ((fun x : ℂ => x - z₀) ^ 1) z₀ := by
        change AnalyticAt ℂ (fun x : ℂ => (x - z₀) ^ 1) z₀
        fun_prop
      have hord_prod : analyticOrderAt (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) z₀ =
          (1 : ℕ) + analyticOrderAt (dslope f z₀) z₀ := by
        rw [analyticOrderAt_mul han_lin (hdg.analyticAt z₀), analyticOrderAt_centeredMonomial]
      have hord_f : analyticOrderAt f z₀ = (1 : ℕ) + analyticOrderAt (dslope f z₀) z₀ := by
        rwa [hfeq] at hord_prod
      have hm' : (m : ℕ∞) ≤ analyticOrderAt (dslope f z₀) z₀ := by
        rw [hord_f] at hm
        rcases eq_top_or_lt_top (analyticOrderAt (dslope f z₀) z₀) with htop | hlt
        · rw [htop]; exact le_top
        · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
          rw [← hk] at hm ⊢
          norm_cast at hm ⊢
          omega
      obtain ⟨Q, hdQ, hoQ, hQ_eq, hQ_z₀, hQ_ord⟩ := exists_quotient_pow_sub m hdg hog hm'
      refine ⟨Q, hdQ, hoQ, fun s => ?_, ?_, fun w hw => ?_⟩
      · calc (s - z₀) ^ (m + 1) * Q s
            = (s - z₀) * ((s - z₀) ^ m * Q s) := by rw [pow_succ]; ring
          _ = f s := by rw [hQ_eq s, hg_eq s]
      · have h1m : ((1 : ℕ) : ℕ∞) + (m : ℕ) = ((m + 1 : ℕ) : ℕ∞) := by norm_cast; omega
        rw [hord_f, hQ_z₀, ← add_assoc, h1m]
      · have han_w : AnalyticAt ℂ ((fun x : ℂ => x - z₀) ^ 1) w := by
          change AnalyticAt ℂ (fun x : ℂ => (x - z₀) ^ 1) w
          fun_prop
        have hlin0 : analyticOrderAt ((fun x : ℂ => x - z₀) ^ 1) w = 0 :=
          han_w.analyticOrderAt_eq_zero.mpr (by simp [sub_ne_zero.mpr hw])
        have hord_prod_w : analyticOrderAt (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) w =
            analyticOrderAt (dslope f z₀) w := by
          rw [analyticOrderAt_mul han_w (hdg.analyticAt w), hlin0, zero_add]
        rw [hfeq] at hord_prod_w
        rw [hQ_ord w hw, hord_prod_w]

private theorem exists_quotient_prod_pow :
    ∀ (L : List (ℂ × ℕ)) (f : ℂ → ℂ),
      (L.map Prod.fst).Nodup → Differentiable ℂ f → OrderOneEnvelope f →
      (∀ p ∈ L, (p.2 : ℕ∞) ≤ analyticOrderAt f p.1) →
      ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ OrderOneEnvelope Q ∧
        (∀ s : ℂ, (L.map (fun p => (s - p.1) ^ p.2)).prod * Q s = f s) ∧
        (∀ p ∈ L, analyticOrderAt f p.1 = (p.2 : ℕ) + analyticOrderAt Q p.1) ∧
        (∀ w : ℂ, w ∉ L.map Prod.fst → analyticOrderAt Q w = analyticOrderAt f w)
  | [], f, _, hdf, hof, _ =>
      ⟨f, hdf, hof, fun s => by simp, by simp, fun _ _ => rfl⟩
  | (r, m) :: ps, f, hnd, hdf, hof, hord => by
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨Q₁, hdQ₁, hoQ₁, hQ₁_eq, hQ₁_r, hQ₁_ord⟩ :=
        exists_quotient_pow_sub m hdf hof (hord (r, m) (by simp))
      have hord₁ : ∀ p ∈ ps, (p.2 : ℕ∞) ≤ analyticOrderAt Q₁ p.1 := by
        intro p hp
        have hne : p.1 ≠ r := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
        rw [hQ₁_ord p.1 hne]
        exact hord p (List.mem_cons_of_mem _ hp)
      obtain ⟨Q, hdQ, hoQ, hQ_eq, hQ_in, hQ_out⟩ :=
        exists_quotient_prod_pow ps Q₁ hnd.2 hdQ₁ hoQ₁ hord₁
      refine ⟨Q, hdQ, hoQ, fun s => ?_, fun p hp => ?_, fun w hw => ?_⟩
      · simp only [List.map_cons, List.prod_cons]
        rw [mul_assoc, hQ_eq s, hQ₁_eq s]
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hps
        · rw [hQ₁_r, hQ_out r hnd.1]
        · have hne : p.1 ≠ r := fun heq => hnd.1 (heq ▸ List.mem_map.mpr ⟨p, hps, rfl⟩)
          rw [← hQ₁_ord p.1 hne, hQ_in p hps]
      · simp only [List.map_cons, List.mem_cons, not_or] at hw
        rw [hQ_out w hw.2, hQ₁_ord w hw.1]

private theorem continuous_eq_of_mul_eq_off_finset' {g₁ g₂ P : ℂ → ℂ} (S : Finset ℂ)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hP : ∀ z : ℂ, z ∉ S → P z ≠ 0)
    (hmul : ∀ z : ℂ, g₁ z * P z = g₂ z * P z) :
    ∀ s : ℂ, g₁ s = g₂ s := by
  intro s
  have hU : ((S.erase s : Set ℂ)ᶜ) ∈ 𝓝 s :=
    (S.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  have hev : g₁ =ᶠ[𝓝[≠] s] g₂ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz1 hz2
    have hzS : z ∉ S := fun hmem => hz1 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hz2, hmem⟩))
    exact mul_right_cancel₀ (hP z hzS) (hmul z)
  exact tendsto_nhds_unique (hg₁.continuousAt.continuousWithinAt.congr' hev)
    hg₂.continuousAt.continuousWithinAt

private theorem exists_coupled_entire_contraction (m : ℕ)
    {b a γ : ℝ} (hb0 : 0 < b) (ha0 : 0 < a) (hγ : γ ≠ 0)
    {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) (hoΛ : OrderOneEnvelope Λ)
    (hsym : ∀ s : ℂ, Λ (1 - s) = Λ s)
    (hconj : ∀ s : ℂ, Λ (starRingEnd ℂ s) = starRingEnd ℂ (Λ s))
    (hntop : ∀ z : ℂ, analyticOrderAt Λ z ≠ ⊤)
    (hreal_ord : m ≤ (analyticOrderAt Λ ((1 / 2 + b : ℝ) : ℂ)).toNat)
    (hquartet : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      Differentiable ℂ Λc ∧
      OrderOneEnvelope Λc ∧
      (∀ s : ℂ, Λc (1 - s) = Λc s) ∧
      (∀ s : ℂ, Λc (starRingEnd ℂ s) = starRingEnd ℂ (Λc s)) ∧
      (∀ s : ℂ, Λc s * (realPairPoly (1 / 2 + b) s ^ m * quartetOffPoly a γ s) =
        Λ s * ((s - 1 / 2) ^ (2 * m) * quartetCritPoly γ s)) ∧
      (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 2 * m ∧
      (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
        (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 ∧
      (analyticOrderAt Λc ((1 / 2 + b : ℝ) : ℂ)).toNat + m =
        (analyticOrderAt Λ ((1 / 2 + b : ℝ) : ℂ)).toNat ∧
      (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + 1 =
        (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
      (∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + b → z.re ≠ 1 / 2 - b →
        z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
        (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat) := by
  classical
  set x₁ : ℂ := ((1 / 2 + b : ℝ) : ℂ)
  set x₂ : ℂ := ((1 / 2 - b : ℝ) : ℂ)
  set r₁ : ℂ := ((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I
  set r₂ : ℂ := ((1 / 2 + a : ℝ) : ℂ) - (γ : ℂ) * I
  set r₃ : ℂ := ((1 / 2 - a : ℝ) : ℂ) + (γ : ℂ) * I
  set r₄ : ℂ := ((1 / 2 - a : ℝ) : ℂ) - (γ : ℂ) * I
  have hr₁_eq : r₁ = 1 / 2 + (a : ℂ) + (γ : ℂ) * I := by dsimp [r₁]; push_cast; ring
  have hr₁ : Λ r₁ = 0 := by rwa [hr₁_eq]
  have hr₂ : Λ r₂ = 0 := by
    have he : r₂ = starRingEnd ℂ r₁ := by dsimp [r₁, r₂]; simp [map_ofNat]; ring
    rw [he, hconj, hr₁, map_zero]
  have hr₄ : Λ r₄ = 0 := by
    have he : r₄ = 1 - r₁ := by dsimp [r₁, r₄]; push_cast; ring
    rw [he, hsym, hr₁]
  have hr₃ : Λ r₃ = 0 := by
    have he : r₃ = 1 - r₂ := by dsimp [r₂, r₃]; push_cast; ring
    rw [he, hsym, hr₂]
  have hord_x₁ : (m : ℕ∞) ≤ analyticOrderAt Λ x₁ := by
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hntop x₁)
    rw [← hk] at hreal_ord ⊢
    simp only [ENat.toNat_coe] at hreal_ord
    exact_mod_cast hreal_ord
  have hord_x₂ : (m : ℕ∞) ≤ analyticOrderAt Λ x₂ := by
    have hx₂_sym : x₂ = 1 - x₁ := by dsimp [x₁, x₂]; push_cast; ring
    have hcomp := RHTower.analyticOrderAt_comp_one_sub hΛ x₁
    rw [show (fun w => Λ (1 - w)) = Λ from funext hsym] at hcomp
    rw [hx₂_sym, hcomp]
    exact hord_x₁
  have hord_zero : ∀ {w : ℂ}, Λ w = 0 → (1 : ℕ∞) ≤ analyticOrderAt Λ w := by
    intro w hw
    have hne0 : analyticOrderAt Λ w ≠ 0 := fun hz =>
      ((hΛ.analyticAt w).analyticOrderAt_eq_zero.mp hz) hw
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hntop w)
    rcases eq_or_ne k 0 with rfl | hk0
    · exact absurd hk.symm hne0
    · rw [← hk]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hdistinct :
      x₁ ≠ x₂ ∧ x₁ ≠ r₁ ∧ x₁ ≠ r₂ ∧ x₁ ≠ r₃ ∧ x₁ ≠ r₄ ∧
      x₂ ≠ r₁ ∧ x₂ ≠ r₂ ∧ x₂ ≠ r₃ ∧ x₂ ≠ r₄ ∧
      r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₁ ≠ r₄ ∧ r₂ ≠ r₃ ∧ r₂ ≠ r₄ ∧ r₃ ≠ r₄ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp [x₁, x₂, r₁, r₂, r₃, r₄] at hre him
      first | linarith | exact hγ (by linarith)
  rcases hdistinct with
    ⟨hx12, hx1r1, hx1r2, hx1r3, hx1r4, hx2r1, hx2r2, hx2r3, hx2r4,
     hr12, hr13, hr14, hr23, hr24, hr34⟩
  let L : List (ℂ × ℕ) := [(x₁, m), (x₂, m), (r₁, 1), (r₂, 1), (r₃, 1), (r₄, 1)]
  have hnd : (L.map Prod.fst).Nodup := by
    simp [L, hx12, hx1r1, hx1r2, hx1r3, hx1r4, hx2r1, hx2r2, hx2r3, hx2r4,
      hr12, hr13, hr14, hr23, hr24, hr34]
  obtain ⟨Q, hdQ, hoQ, hQ_eq, hQ_in, hQ_out⟩ := exists_quotient_prod_pow L Λ hnd hΛ hoΛ (fun p hp => by
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hord_x₁
    · exact hord_x₂
    · exact hord_zero hr₁
    · exact hord_zero hr₂
    · exact hord_zero hr₃
    · exact hord_zero hr₄)
  let D_poly : ℂ → ℂ := fun s => realPairPoly (1 / 2 + b) s ^ m * quartetOffPoly a γ s
  let C_poly : ℂ → ℂ := fun s => (s - 1 / 2) ^ (2 * m) * quartetCritPoly γ s
  have hReal_fac : ∀ s : ℂ, realPairPoly (1 / 2 + b) s = (s - x₁) * (s - x₂) := fun s => by
    unfold realPairPoly
    have hx₂' : (((1 - (1 / 2 + b) : ℝ) : ℂ)) = x₂ := by dsimp [x₂]; push_cast; ring
    rw [hx₂']
  have hOff_fac : ∀ s : ℂ, quartetOffPoly a γ s =
      (s - r₁) * (s - r₂) * (s - r₃) * (s - r₄) := fun s => by
    unfold quartetOffPoly
    rw [sq_add_sq_eq_mul_I' s (1 / 2 + a) γ, sq_add_sq_eq_mul_I' s (1 / 2 - a) γ]
    dsimp [r₁, r₂, r₃, r₄]; ring
  have hD_fac : ∀ s : ℂ, D_poly s =
      (s - x₁) ^ m * (s - x₂) ^ m * ((s - r₁) * (s - r₂) * (s - r₃) * (s - r₄)) := fun s => by
    dsimp [D_poly]; rw [hReal_fac, mul_pow, hOff_fac]
  have hQ_poly : ∀ s : ℂ, D_poly s * Q s = Λ s := fun s => by
    have h := hQ_eq s
    simp only [L, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one, mul_one] at h
    rw [hD_fac s]
    linear_combination h
  let Λc : ℂ → ℂ := fun s => Q s * C_poly s
  have hdC : Differentiable ℂ C_poly := by dsimp [C_poly]; unfold quartetCritPoly; fun_prop
  have hdΛc : Differentiable ℂ Λc := hdQ.mul hdC
  have ho_crit : OrderOneEnvelope (quartetCritPoly γ) := by
    let p₁ := orderOneEnvelope_sub_const' (1 / 2 + (γ : ℂ) * I)
    let p₂ := orderOneEnvelope_sub_const' (1 / 2 - (γ : ℂ) * I)
    refine ((p₁.mul p₂).mul (p₁.mul p₂)).congr fun s => ?_
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I' s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf; rw [hf]; ring
  have hoΛc : OrderOneEnvelope Λc :=
    hoQ.mul ((orderOneEnvelope_pow_sub_const (1 / 2) (2 * m)).mul ho_crit)
  have hrel : ∀ s : ℂ, Λc s * D_poly s = Λ s * C_poly s := fun s => by
    dsimp [Λc]; rw [← hQ_poly s]; ring
  let S_roots : Finset ℂ := {x₁, x₂, r₁, r₂, r₃, r₄}
  have hD_nz_off : ∀ z : ℂ, z ∉ S_roots → D_poly z ≠ 0 := by
    intro z hz
    simp only [S_roots, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [hD_fac z]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero m (sub_ne_zero.mpr hz.1))
        (pow_ne_zero m (sub_ne_zero.mpr hz.2.1)))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz.2.2.1)
        (sub_ne_zero.mpr hz.2.2.2.1)) (sub_ne_zero.mpr hz.2.2.2.2.1))
        (sub_ne_zero.mpr hz.2.2.2.2.2))
  have hsym_c : ∀ s : ℂ, Λc (1 - s) = Λc s := by
    refine continuous_eq_of_mul_eq_off_finset' S_roots
      (hdΛc.continuous.comp (by fun_prop)) hdΛc.continuous hD_nz_off fun z => ?_
    have hD_sym : D_poly z = D_poly (1 - z) := by
      dsimp [D_poly]; unfold realPairPoly quartetOffPoly; push_cast; ring
    have hC_sym : C_poly (1 - z) = C_poly z := by
      dsimp [C_poly]; unfold quartetCritPoly
      have h1 : ((1 - z) - 1 / 2) ^ (2 * m) = (z - 1 / 2) ^ (2 * m) := by
        rw [pow_mul, pow_mul]; congr 1; ring
      have h2 : ((1 - z) - 1 / 2) ^ 2 = (z - 1 / 2) ^ 2 := by ring
      rw [h1, h2]
    rw [hD_sym, hrel (1 - z), hsym z, hC_sym, ← hD_sym, ← hrel z]
  have hconj_c : ∀ s : ℂ, Λc (starRingEnd ℂ s) = starRingEnd ℂ (Λc s) := by
    have hinv := continuous_eq_of_mul_eq_off_finset' S_roots
      (Complex.continuous_conj.comp (hdΛc.continuous.comp Complex.continuous_conj))
      hdΛc.continuous hD_nz_off fun z => by
        have hD_conj : starRingEnd ℂ (D_poly (starRingEnd ℂ z)) = D_poly z := by
          dsimp [D_poly]; unfold realPairPoly quartetOffPoly
          simp only [map_mul, map_add, map_pow, map_sub, Complex.conj_ofReal,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        have hC_conj : starRingEnd ℂ (C_poly (starRingEnd ℂ z)) = C_poly z := by
          dsimp [C_poly]; unfold quartetCritPoly; simp [map_ofNat]
        have h1 := congrArg (starRingEnd ℂ) (hrel (starRingEnd ℂ z))
        rw [map_mul (starRingEnd ℂ) (Λc (starRingEnd ℂ z)),
            map_mul (starRingEnd ℂ) (Λ (starRingEnd ℂ z)),
            hD_conj, hC_conj, hconj z, Complex.conj_conj, ← hrel z] at h1
        simpa only [Function.comp_apply] using h1
    intro s
    have hs := congrArg (starRingEnd ℂ) (hinv s)
    simpa [Function.comp_apply] using hs
  have hQ_ntop : ∀ w : ℂ, analyticOrderAt Q w ≠ ⊤ := by
    intro w
    by_cases hw : w ∈ L.map Prod.fst
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      have hin := hQ_in p hp
      intro htop
      rw [htop, add_top] at hin
      exact hntop p.1 hin
    · rw [hQ_out w hw]; exact hntop w
  have hCrit_fac : ∀ s : ℂ, quartetCritPoly γ s =
      (s - (1 / 2 + (γ : ℂ) * I)) ^ 2 * (s - (1 / 2 - (γ : ℂ) * I)) ^ 2 := fun s => by
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I' s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf; rw [hf]; ring
  have hC_nz_off_crit : ∀ w : ℂ, w.re ≠ 1 / 2 → C_poly w ≠ 0 := by
    intro w hw
    dsimp [C_poly]
    rw [hCrit_fac w]
    refine mul_ne_zero (pow_ne_zero (2 * m) (fun h => ?_))
      (mul_ne_zero (pow_ne_zero 2 (fun h => ?_)) (pow_ne_zero 2 (fun h => ?_)))
    · have := congrArg Complex.re h; simp at this; exact hw (by linarith)
    · have := congrArg Complex.re h; simp at this; exact hw (by linarith)
    · have := congrArg Complex.re h; simp at this; exact hw (by linarith)
  have hΛc_ord_off_crit : ∀ w : ℂ, w.re ≠ 1 / 2 → analyticOrderAt Λc w = analyticOrderAt Q w := by
    intro w hw
    have hΛc_eq : Λc = Q * C_poly := rfl
    rw [hΛc_eq, analyticOrderAt_mul (hdQ.analyticAt w) (hdC.analyticAt w),
        (hdC.analyticAt w).analyticOrderAt_eq_zero.mpr (hC_nz_off_crit w hw), add_zero]
  have hnot_mem_crit : ∀ w : ℂ, w.re = 1 / 2 → w ∉ L.map Prod.fst := by
    intro w hw hmem
    simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (simp [x₁, x₂, r₁, r₂, r₃, r₄] at hw; linarith)
  have hord_half : (analyticOrderAt Λc (1 / 2)).toNat =
      (analyticOrderAt Λ (1 / 2)).toNat + 2 * m := by
    have hΛc_eq : Λc = (Q * quartetCritPoly γ) * ((· - (1 / 2 : ℂ)) ^ (2 * m)) :=
      funext fun s => by dsimp [Λc, C_poly]; ring
    have hd_crit : Differentiable ℂ (quartetCritPoly γ) := by unfold quartetCritPoly; fun_prop
    have hcrit_nz : quartetCritPoly γ (1 / 2) ≠ 0 := by
      rw [hCrit_fac]
      refine mul_ne_zero (pow_ne_zero 2 (fun h => ?_)) (pow_ne_zero 2 (fun h => ?_))
      · have := congrArg Complex.im h; simp at this; exact hγ (by linarith)
      · have := congrArg Complex.im h; simp at this; exact hγ (by linarith)
    have han_mon : AnalyticAt ℂ ((· - (1 / 2 : ℂ)) ^ (2 * m)) (1 / 2) :=
      ((differentiable_id.sub_const (1 / 2 : ℂ)).pow (2 * m)).analyticAt (1 / 2)
    have h1 : analyticOrderAt Λc (1 / 2) = analyticOrderAt Λ (1 / 2) + (2 * m : ℕ) := by
      rw [hΛc_eq,
          analyticOrderAt_mul ((hdQ.mul hd_crit).analyticAt _) han_mon,
          analyticOrderAt_mul (hdQ.analyticAt _) (hd_crit.analyticAt _),
          (hd_crit.analyticAt _).analyticOrderAt_eq_zero.mpr hcrit_nz, add_zero,
          hQ_out (1 / 2) (hnot_mem_crit (1 / 2) (by norm_num)),
          analyticOrderAt_centeredMonomial]
    rw [h1, ENat.toNat_add (hntop (1 / 2)) (ENat.coe_ne_top (2 * m)), ENat.toNat_coe]
  have hord_crit_γ : (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
      (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 := by
    set w₀ : ℂ := 1 / 2 + (γ : ℂ) * I
    let R_poly : ℂ → ℂ := fun s => (s - 1 / 2) ^ (2 * m) * (s - (1 / 2 - (γ : ℂ) * I)) ^ 2
    have hdR : Differentiable ℂ R_poly := by dsimp [R_poly]; fun_prop
    have hR_nz : R_poly w₀ ≠ 0 := by
      dsimp [R_poly]
      refine mul_ne_zero (pow_ne_zero (2 * m) (fun h => ?_)) (pow_ne_zero 2 (fun h => ?_))
      · have := congrArg Complex.im h; simp [w₀] at this; exact hγ this
      · have := congrArg Complex.im h; simp [w₀] at this; exact hγ (by linarith)
    have hΛc_eq : Λc = (Q * R_poly) * ((· - w₀) ^ 2) := funext fun s => by
      dsimp [Λc, C_poly, R_poly, w₀]; rw [hCrit_fac s]; ring
    have han_mon : AnalyticAt ℂ ((· - w₀) ^ 2) w₀ :=
      ((differentiable_id.sub_const w₀).pow 2).analyticAt w₀
    have hw₀_re : w₀.re = 1 / 2 := by simp [w₀]
    have h1 : analyticOrderAt Λc w₀ = analyticOrderAt Λ w₀ + (2 : ℕ) := by
      rw [hΛc_eq,
          analyticOrderAt_mul ((hdQ.mul hdR).analyticAt _) han_mon,
          analyticOrderAt_mul (hdQ.analyticAt _) (hdR.analyticAt _),
          (hdR.analyticAt _).analyticOrderAt_eq_zero.mpr hR_nz, add_zero,
          hQ_out w₀ (hnot_mem_crit w₀ hw₀_re),
          analyticOrderAt_centeredMonomial]
    rw [h1, ENat.toNat_add (hntop w₀) (ENat.coe_ne_top 2), ENat.toNat_coe]
  have hord_real : (analyticOrderAt Λc x₁).toNat + m = (analyticOrderAt Λ x₁).toNat := by
    have hx₁_re : x₁.re ≠ 1 / 2 := by simp [x₁]; linarith
    have hin := hQ_in (x₁, m) (by simp [L])
    dsimp only at hin
    rw [← hΛc_ord_off_crit x₁ hx₁_re] at hin
    have hne : analyticOrderAt Λc x₁ ≠ ⊤ := by
      rw [hΛc_ord_off_crit x₁ hx₁_re]; exact hQ_ntop x₁
    rw [hin, ENat.toNat_add (ENat.coe_ne_top m) hne, ENat.toNat_coe]
    omega
  have hord_quart : (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + 1 =
      (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
    rw [← hr₁_eq]
    have hr₁_re : r₁.re ≠ 1 / 2 := by simp [r₁]; linarith
    have hin := hQ_in (r₁, 1) (by simp [L])
    dsimp only at hin
    rw [← hΛc_ord_off_crit r₁ hr₁_re] at hin
    have hne : analyticOrderAt Λc r₁ ≠ ⊤ := by
      rw [hΛc_ord_off_crit r₁ hr₁_re]; exact hQ_ntop r₁
    rw [hin, ENat.toNat_add (ENat.coe_ne_top 1) hne, ENat.toNat_coe]
    omega
  have hord_other : ∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + b → z.re ≠ 1 / 2 - b →
      z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
      (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat := by
    intro z hz0 hzb1 hzb2 hza1 hza2
    have hnot : z ∉ L.map Prod.fst := by
      intro hmem
      simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hzb1 (by simp [x₁])
      · exact hzb2 (by simp [x₂])
      · exact hza1 (by simp [r₁])
      · exact hza1 (by simp [r₂])
      · exact hza2 (by simp [r₃])
      · exact hza2 (by simp [r₄])
    rw [hΛc_ord_off_crit z hz0, hQ_out z hnot]
  exact ⟨Λc, hdΛc, hoΛc, hsym_c, hconj_c, hrel, hord_half, hord_crit_γ,
    hord_real, hord_quart, hord_other⟩

/-- **Single-system `Δκ = 0` cross-channel quartet contraction from a double real anchor.**
Whenever `0 < a ≤ b < 1/2`, `γ ≠ 0`, `2 ≤ ord_{1/2 + b}(Λ)`, and `Λ(1/2 + a + iγ) = 0`,
multiplying `F` by `coupledQuartetSymSquare b a γ` contracts both real pairs at `1/2 ± b` and the
complex quartet at `1/2 ± a ± iγ` onto `{1/2, 1/2 ± iγ}` inside `CompletedPositiveSystem κ d`
(`Δκ = 0`). -/
theorem CompletedPositiveSystem.contractComplexQuartet_of_doubleRealAnchor {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {b a γ : ℝ}
    (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1 / 2) (hγ : γ ≠ 0)
    (hreal : 2 ≤ (analyticOrderAt Λ ((1 / 2 + b : ℝ) : ℂ)).toNat)
    (hquartet : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      CompletedPositiveSystem κ d (fun s => F s * coupledQuartetSymSquare b a γ s) Λc ∧
      (∀ s : ℂ, Λc s * (realPairPoly (1 / 2 + b) s ^ 2 * quartetOffPoly a γ s) =
        Λ s * ((s - 1 / 2) ^ 4 * quartetCritPoly γ s)) ∧
      (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 4 ∧
      (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
        (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 ∧
      (analyticOrderAt Λc ((1 / 2 + b : ℝ) : ℂ)).toNat + 2 =
        (analyticOrderAt Λ ((1 / 2 + b : ℝ) : ℂ)).toNat ∧
      (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + 1 =
        (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
      (∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + b → z.re ≠ 1 / 2 - b →
        z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
        (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat) := by
  obtain ⟨Λc, hdΛc, hoΛc, hsym_c, hconj_c, hrel, h1, h2, h3, h4, h5⟩ :=
    exists_coupled_entire_contraction 2 (by linarith) ha0 hγ hS.entire_Λ hS.orderOne_Λ
      hS.sym_Λ hS.conj_Λ hS.orderAt_ne_top hreal hquartet
  have hP_nz : ∀ s : ℂ, 1 < s.re → realPairPoly (1 / 2 + b) s ≠ 0 := by
    intro s hs
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hOff_nz : ∀ s : ℂ, 1 < s.re → quartetOffPoly a γ s ≠ 0 := by
    intro s hs
    unfold quartetOffPoly
    rw [sq_add_sq_eq_mul_I', sq_add_sq_eq_mul_I']
    refine mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_))
      (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hCrit_nz : ∀ s : ℂ, 1 < s.re → quartetCritPoly γ s ≠ 0 := by
    intro s hs
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I' s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf; rw [hf]
    refine pow_ne_zero 2 (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hW_nz : ∀ s : ℂ, 1 < s.re → coupledQuartetSymSquare b a γ s ≠ 0 := by
    intro s hs
    unfold coupledQuartetSymSquare midpointSymSquare
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact mul_ne_zero (pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 hs_half) (hP_nz s hs)))
      (div_ne_zero (hCrit_nz s hs) (hOff_nz s hs))
  have hW_diffAt : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (coupledQuartetSymSquare b a γ) s := by
    intro s hs
    unfold coupledQuartetSymSquare midpointSymSquare
    exact (((DifferentiableAt.div (by fun_prop) (by unfold realPairPoly; fun_prop)
      (hP_nz s hs)).fun_pow 2).mul
      (DifferentiableAt.div (by unfold quartetCritPoly; fun_prop)
        (by unfold quartetOffPoly; fun_prop) (hOff_nz s hs)))
  have hSc : CompletedPositiveSystem κ d (fun s => F s * coupledQuartetSymSquare b a γ s) Λc :=
    { degree_pos := hS.degree_pos
      diffOn_F := hS.diffOn_F.mul (fun s hs => (hW_diffAt s hs).differentiableWithinAt)
      ne_zero_F := fun s hs => mul_ne_zero (hS.ne_zero_F s hs) (hW_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => F s * coupledQuartetSymSquare b a γ s)
              ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (coupledQuartetSymSquare b a γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := coupledQuartetSymSquare b a γ) s
                (hS.ne_zero_F s hs) (hW_nz s hs)
                ((hS.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                (hW_diffAt s hs),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add_coupled (hS.posDef_neg_logDeriv hσ)
          (isEvenPosDef_coupledQuartetSymSquare ha0 hab hb1 hσ)
      entire_Λ := hdΛc
      orderOne_Λ := hoΛc
      sym_Λ := hsym_c
      conj_Λ := hconj_c
      completed_eq := fun s hs => by
        have hden_nz : realPairPoly (1 / 2 + b) s ^ 2 * quartetOffPoly a γ s ≠ 0 :=
          mul_ne_zero (pow_ne_zero 2 (hP_nz s hs)) (hOff_nz s hs)
        apply mul_right_cancel₀ hden_nz
        have hW_mul : coupledQuartetSymSquare b a γ s *
            (realPairPoly (1 / 2 + b) s ^ 2 * quartetOffPoly a γ s) =
            (s - 1 / 2) ^ 4 * quartetCritPoly γ s := by
          unfold coupledQuartetSymSquare midpointSymSquare
          have hp2 : realPairPoly (1 / 2 + b) s ^ 2 ≠ 0 := pow_ne_zero 2 (hP_nz s hs)
          have ho : quartetOffPoly a γ s ≠ 0 := hOff_nz s hs
          rw [div_pow]
          calc ((s - 1 / 2) ^ 2) ^ 2 / realPairPoly (1 / 2 + b) s ^ 2 *
                (quartetCritPoly γ s / quartetOffPoly a γ s) *
                (realPairPoly (1 / 2 + b) s ^ 2 * quartetOffPoly a γ s)
              = (((s - 1 / 2) ^ 2) ^ 2 / realPairPoly (1 / 2 + b) s ^ 2 *
                  realPairPoly (1 / 2 + b) s ^ 2) *
                (quartetCritPoly γ s / quartetOffPoly a γ s * quartetOffPoly a γ s) := by ring
            _ = ((s - 1 / 2) ^ 2) ^ 2 * quartetCritPoly γ s := by
                rw [div_mul_cancel₀ _ hp2, div_mul_cancel₀ _ ho]
            _ = (s - 1 / 2) ^ 4 * quartetCritPoly γ s := by ring
        calc Λc s * (realPairPoly (1 / 2 + b) s ^ 2 * quartetOffPoly a γ s)
            = Λ s * ((s - 1 / 2) ^ 4 * quartetCritPoly γ s) := hrel s
          _ = ((s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * F s) *
                (coupledQuartetSymSquare b a γ s *
                  (realPairPoly (1 / 2 + b) s ^ 2 * quartetOffPoly a γ s)) := by
              rw [hS.completed_eq s hs, hW_mul]
          _ = (s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d *
                (F s * coupledQuartetSymSquare b a γ s) *
                (realPairPoly (1 / 2 + b) s ^ 2 * quartetOffPoly a γ s) := by ring }
  exact ⟨Λc, hSc, hrel, h1, h2, h3, h4, h5⟩

/-- **Single-system `Δκ = 0` cross-channel quartet contraction from a single deep real anchor.**
Even a simple real zero `Λ(1/2 + b) = 0` at depth `2a ≤ b < 1/2` (`0 < a < 1/4`) anchors a complex
quartet `{1/2 ± a ± iγ}` at zero boundary pole cost (`Δκ = 0`). -/
theorem CompletedPositiveSystem.contractComplexQuartet_of_singleDeepRealAnchor {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {b a γ : ℝ}
    (ha0 : 0 < a) (hab : 2 * a ≤ b) (hb1 : b < 1 / 2) (hγ : γ ≠ 0)
    (hreal : Λ ((1 / 2 + b : ℝ) : ℂ) = 0)
    (hquartet : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      CompletedPositiveSystem κ d (fun s => F s * deepRealQuartetSymSquare b a γ s) Λc ∧
      (∀ s : ℂ, Λc s * (realPairPoly (1 / 2 + b) s * quartetOffPoly a γ s) =
        Λ s * ((s - 1 / 2) ^ 2 * quartetCritPoly γ s)) ∧
      (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 2 ∧
      (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
        (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 ∧
      (analyticOrderAt Λc ((1 / 2 + b : ℝ) : ℂ)).toNat + 1 =
        (analyticOrderAt Λ ((1 / 2 + b : ℝ) : ℂ)).toNat ∧
      (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + 1 =
        (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
  have hreal1 : 1 ≤ (analyticOrderAt Λ ((1 / 2 + b : ℝ) : ℂ)).toNat :=
    hS.one_le_order_toNat_of_eq_zero hreal
  obtain ⟨Λc, hdΛc, hoΛc, hsym_c, hconj_c, hrel, h1, h2, h3, h4, _⟩ :=
    exists_coupled_entire_contraction 1 (by linarith) ha0 hγ hS.entire_Λ hS.orderOne_Λ
      hS.sym_Λ hS.conj_Λ hS.orderAt_ne_top hreal1 hquartet
  simp only [pow_one, Nat.mul_one] at hrel h1
  have hP_nz : ∀ s : ℂ, 1 < s.re → realPairPoly (1 / 2 + b) s ≠ 0 := by
    intro s hs
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hOff_nz : ∀ s : ℂ, 1 < s.re → quartetOffPoly a γ s ≠ 0 := by
    intro s hs
    unfold quartetOffPoly
    rw [sq_add_sq_eq_mul_I', sq_add_sq_eq_mul_I']
    refine mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_))
      (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hCrit_nz : ∀ s : ℂ, 1 < s.re → quartetCritPoly γ s ≠ 0 := by
    intro s hs
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I' s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf; rw [hf]
    refine pow_ne_zero 2 (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hW_nz : ∀ s : ℂ, 1 < s.re → deepRealQuartetSymSquare b a γ s ≠ 0 := by
    intro s hs
    unfold deepRealQuartetSymSquare midpointSymSquare
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact mul_ne_zero (div_ne_zero (pow_ne_zero 2 hs_half) (hP_nz s hs))
      (div_ne_zero (hCrit_nz s hs) (hOff_nz s hs))
  have hW_diffAt : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (deepRealQuartetSymSquare b a γ) s := by
    intro s hs
    unfold deepRealQuartetSymSquare midpointSymSquare
    exact ((DifferentiableAt.div (by fun_prop) (by unfold realPairPoly; fun_prop)
      (hP_nz s hs)).mul
      (DifferentiableAt.div (by unfold quartetCritPoly; fun_prop)
        (by unfold quartetOffPoly; fun_prop) (hOff_nz s hs)))
  have hSc : CompletedPositiveSystem κ d (fun s => F s * deepRealQuartetSymSquare b a γ s) Λc :=
    { degree_pos := hS.degree_pos
      diffOn_F := hS.diffOn_F.mul (fun s hs => (hW_diffAt s hs).differentiableWithinAt)
      ne_zero_F := fun s hs => mul_ne_zero (hS.ne_zero_F s hs) (hW_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => F s * deepRealQuartetSymSquare b a γ s)
              ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (deepRealQuartetSymSquare b a γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := deepRealQuartetSymSquare b a γ) s
                (hS.ne_zero_F s hs) (hW_nz s hs)
                ((hS.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                (hW_diffAt s hs),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add_coupled (hS.posDef_neg_logDeriv hσ)
          (isEvenPosDef_deepRealQuartetSymSquare ha0 hab hb1 hσ)
      entire_Λ := hdΛc
      orderOne_Λ := hoΛc
      sym_Λ := hsym_c
      conj_Λ := hconj_c
      completed_eq := fun s hs => by
        have hden_nz : realPairPoly (1 / 2 + b) s * quartetOffPoly a γ s ≠ 0 :=
          mul_ne_zero (hP_nz s hs) (hOff_nz s hs)
        apply mul_right_cancel₀ hden_nz
        have hW_mul : deepRealQuartetSymSquare b a γ s *
            (realPairPoly (1 / 2 + b) s * quartetOffPoly a γ s) =
            (s - 1 / 2) ^ 2 * quartetCritPoly γ s := by
          unfold deepRealQuartetSymSquare midpointSymSquare
          calc (s - 1 / 2) ^ 2 / realPairPoly (1 / 2 + b) s *
                (quartetCritPoly γ s / quartetOffPoly a γ s) *
                (realPairPoly (1 / 2 + b) s * quartetOffPoly a γ s)
              = ((s - 1 / 2) ^ 2 / realPairPoly (1 / 2 + b) s * realPairPoly (1 / 2 + b) s) *
                (quartetCritPoly γ s / quartetOffPoly a γ s * quartetOffPoly a γ s) := by ring
            _ = (s - 1 / 2) ^ 2 * quartetCritPoly γ s := by
                rw [div_mul_cancel₀ _ (hP_nz s hs), div_mul_cancel₀ _ (hOff_nz s hs)]
        calc Λc s * (realPairPoly (1 / 2 + b) s * quartetOffPoly a γ s)
            = Λ s * ((s - 1 / 2) ^ 2 * quartetCritPoly γ s) := hrel s
          _ = ((s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * F s) *
                (deepRealQuartetSymSquare b a γ s *
                  (realPairPoly (1 / 2 + b) s * quartetOffPoly a γ s)) := by
              rw [hS.completed_eq s hs, hW_mul]
          _ = (s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d *
                (F s * deepRealQuartetSymSquare b a γ s) *
                (realPairPoly (1 / 2 + b) s * quartetOffPoly a γ s) := by ring }
  exact ⟨Λc, hSc, hrel, h1, h2, h3, h4⟩

/-! ### 5. Height-coupled positive systems, zero-tax quartet elimination, and finite termination -/

/-- Shifted boundary pole factor `(s² + γ²)((s − 1)² + γ²) = (s + iγ)(s − iγ)(s − 1 + iγ)(s − 1 − iγ)`. -/
def shiftedPolePoly (γ : ℝ) (s : ℂ) : ℂ :=
  (s ^ 2 + (γ : ℂ) ^ 2) * ((s - 1) ^ 2 + (γ : ℂ) ^ 2)

/-- Coupled archimedean Gamma factor `Γ_ℝ(s)^{2d} (Γ_ℝ(s + iγ) Γ_ℝ(s − iγ))^d`. -/
def coupledGamma (γ : ℝ) (d : ℕ) (s : ℂ) : ℂ :=
  Complex.Gammaℝ s ^ (2 * d) *
    (Complex.Gammaℝ (s + (γ : ℂ) * I) * Complex.Gammaℝ (s - (γ : ℂ) * I)) ^ d

/-- **Height-coupled completed positive system** at ordinate `γ ∈ ℝ`, with central pole order `κ₀`,
shifted pole order `κγ` at `{±iγ, 1 ± iγ}`, and archimedean degree `d ≥ 1`. -/
structure HeightCoupledSystem (κ₀ κγ d : ℕ) (γ : ℝ) (F Λ : ℂ → ℂ) : Prop where
  degree_pos : 0 < d
  diffOn_F : DifferentiableOn ℂ F {s : ℂ | 1 < s.re}
  ne_zero_F : ∀ s : ℂ, 1 < s.re → F s ≠ 0
  posDef_neg_logDeriv : ∀ {σ : ℝ}, 1 < σ →
    IsEvenPosDef (fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re)
  entire_Λ : Differentiable ℂ Λ
  orderOne_Λ : OrderOneEnvelope Λ
  sym_Λ : ∀ s : ℂ, Λ (1 - s) = Λ s
  conj_Λ : ∀ s : ℂ, Λ (starRingEnd ℂ s) = starRingEnd ℂ (Λ s)
  completed_eq : ∀ s : ℂ, 1 < s.re →
    Λ s = (s * (s - 1)) ^ κ₀ * shiftedPolePoly γ s ^ κγ * coupledGamma γ d s * F s

/-- Height-coupled Euler/Dirichlet carrier `F_γ(s) = F(s)² F(s + iγ) F(s − iγ)`. -/
def heightCoupledF (F : ℂ → ℂ) (γ : ℝ) (s : ℂ) : ℂ :=
  F s ^ 2 * F (s + (γ : ℂ) * I) * F (s - (γ : ℂ) * I)

/-- Height-coupled completed carrier `Λ_γ(s) = Λ(s)² Λ(s + iγ) Λ(s − iγ)`. -/
def heightCoupledΛ (Λ : ℂ → ℂ) (γ : ℝ) (s : ℂ) : ℂ :=
  Λ s ^ 2 * Λ (s + (γ : ℂ) * I) * Λ (s - (γ : ℂ) * I)

private theorem logDeriv_comp_add_const {f : ℂ → ℂ} {s c : ℂ}
    (hf : DifferentiableAt ℂ f (s + c)) :
    logDeriv (fun w : ℂ => f (w + c)) s = logDeriv f (s + c) := by
  have hd : HasDerivAt (fun w : ℂ => f (w + c)) (deriv f (s + c) * 1) s :=
    hf.hasDerivAt.comp s ((hasDerivAt_id s).add_const c)
  rw [logDeriv_apply, logDeriv_apply, hd.deriv, mul_one]

private theorem logDeriv_comp_sub_const {f : ℂ → ℂ} {s c : ℂ}
    (hf : DifferentiableAt ℂ f (s - c)) :
    logDeriv (fun w : ℂ => f (w - c)) s = logDeriv f (s - c) := by
  have heq : (fun w : ℂ => f (w - c)) = fun w : ℂ => f (w + -c) :=
    funext fun w => congrArg f (sub_eq_add_neg w c)
  have hs : s + -c = s - c := (sub_eq_add_neg s c).symm
  rw [heq, logDeriv_comp_add_const (by rwa [hs]), hs]

private theorem analyticOrderAt_comp_add_const {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (z c : ℂ) :
    analyticOrderAt (fun w : ℂ => f (w + c)) z = analyticOrderAt f (z + c) := by
  have hg_an : AnalyticAt ℂ (fun w : ℂ => w + c) z := by fun_prop
  have hg_d : deriv (fun w : ℂ => w + c) z ≠ 0 := by
    rw [((hasDerivAt_id' z).add_const c).deriv]; exact one_ne_zero
  exact analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg_an hg_d

private theorem analyticOrderAt_comp_sub_const {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z c : ℂ) :
    analyticOrderAt (fun w : ℂ => f (w - c)) z = analyticOrderAt f (z - c) := by
  have heq : (fun w : ℂ => f (w - c)) = fun w : ℂ => f (w + -c) :=
    funext fun w => congrArg f (sub_eq_add_neg w c)
  rw [heq, analyticOrderAt_comp_add_const hf z (-c), ← sub_eq_add_neg]

private theorem shiftedPolePoly_ne_zero_of_one_lt_re (γ : ℝ) {s : ℂ} (hs : 1 < s.re) :
    shiftedPolePoly γ s ≠ 0 := by
  unfold shiftedPolePoly
  have h1 := sq_add_sq_eq_mul_I' s 0 γ
  simp only [Complex.ofReal_zero, sub_zero, zero_add, zero_sub] at h1
  have h2 := sq_add_sq_eq_mul_I' s 1 γ
  simp only [Complex.ofReal_one] at h2
  rw [h1, h2]
  refine mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_))
    (mul_ne_zero (fun h => ?_) (fun h => ?_))
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

private theorem re_logDeriv_shiftedPolePoly_two_le (γ : ℝ) :
    (logDeriv (shiftedPolePoly γ) 2).re ≤ 3 := by
  let p₁ : ℂ → ℂ := fun w => w ^ 2 + (γ : ℂ) ^ 2
  let p₂ : ℂ → ℂ := fun w => (w - 1) ^ 2 + (γ : ℂ) ^ 2
  have hp₁_val : p₁ 2 = ((4 + γ ^ 2 : ℝ) : ℂ) := by dsimp [p₁]; push_cast; ring
  have hp₂_val : p₂ 2 = ((1 + γ ^ 2 : ℝ) : ℂ) := by dsimp [p₂]; push_cast; ring
  have hp₁_pos : 0 < 4 + γ ^ 2 := by positivity
  have hp₂_pos : 0 < 1 + γ ^ 2 := by positivity
  have hp₁_nz : p₁ 2 ≠ 0 := by rw [hp₁_val]; exact Complex.ofReal_ne_zero.mpr hp₁_pos.ne'
  have hp₂_nz : p₂ 2 ≠ 0 := by rw [hp₂_val]; exact Complex.ofReal_ne_zero.mpr hp₂_pos.ne'
  have hd₁ : HasDerivAt p₁ 4 2 :=
    (((hasDerivAt_id (2 : ℂ)).pow 2).add_const ((γ : ℂ) ^ 2)).congr_deriv (by norm_num)
  have hd₂ : HasDerivAt p₂ 2 2 :=
    ((((hasDerivAt_id (2 : ℂ)).sub_const 1).pow 2).add_const ((γ : ℂ) ^ 2)).congr_deriv
      (by norm_num)
  have hsp : shiftedPolePoly γ = fun z => p₁ z * p₂ z := rfl
  rw [hsp, logDeriv_mul (f := p₁) (g := p₂) 2 hp₁_nz hp₂_nz hd₁.differentiableAt hd₂.differentiableAt,
      logDeriv_apply, logDeriv_apply, hd₁.deriv, hd₂.deriv, hp₁_val, hp₂_val]
  have hc : (4 : ℂ) / ((4 + γ ^ 2 : ℝ) : ℂ) + (2 : ℂ) / ((1 + γ ^ 2 : ℝ) : ℂ) =
      (((4 / (4 + γ ^ 2) + 2 / (1 + γ ^ 2) : ℝ)) : ℂ) := by push_cast; ring
  rw [hc, Complex.ofReal_re]
  have hb₁ : 4 / (4 + γ ^ 2) ≤ 1 := (div_le_one hp₁_pos).mpr (by nlinarith)
  have hb₂ : 2 / (1 + γ ^ 2) ≤ 2 := (div_le_iff₀ hp₂_pos).mpr (by nlinarith)
  linarith

namespace HeightCoupledSystem

variable {κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}

theorem ne_zero_of_one_lt_re (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) {s : ℂ} (hs : 1 < s.re) :
    Λ s ≠ 0 := by
  rw [hHC.completed_eq s hs]
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hΓ0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓp : Complex.Gammaℝ (s + (γ : ℂ) * I) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΓm : Complex.Gammaℝ (s - (γ : ℂ) * I) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (pow_ne_zero κ₀ (mul_ne_zero hs0 hs1))
        (pow_ne_zero κγ (shiftedPolePoly_ne_zero_of_one_lt_re γ hs)))
      (mul_ne_zero (pow_ne_zero (2 * d) hΓ0) (pow_ne_zero d (mul_ne_zero hΓp hΓm))))
    (hHC.ne_zero_F s hs)

theorem two_ne_zero (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) : Λ 2 ≠ 0 :=
  hHC.ne_zero_of_one_lt_re (by norm_num)

theorem zero_re_mem_Icc (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) {ρ : ℂ} (hρ : Λ ρ = 0) :
    0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : 1 < (1 - ρ).re := by simp; linarith
    exact hHC.ne_zero_of_one_lt_re h1 (by rw [hHC.sym_Λ, hρ])
  · by_contra hgt
    rw [not_le] at hgt
    exact hHC.ne_zero_of_one_lt_re hgt hρ

theorem analyticOnNhd_univ (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) : AnalyticOnNhd ℂ Λ univ :=
  hHC.entire_Λ.differentiableOn.analyticOnNhd isOpen_univ

theorem orderAt_ne_top (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) (z : ℂ) :
    analyticOrderAt Λ z ≠ ⊤ :=
  hHC.analyticOnNhd_univ.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ 2) (mem_univ z)
    (by rw [(hHC.analyticOnNhd_univ 2 (mem_univ 2)).analyticOrderAt_eq_zero.mpr hHC.two_ne_zero]
        exact ENat.zero_ne_top)

theorem one_le_order_toNat_of_eq_zero (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) {ρ : ℂ}
    (hρ : Λ ρ = 0) : 1 ≤ (analyticOrderAt Λ ρ).toNat := by
  have hne0 : analyticOrderAt Λ ρ ≠ 0 := fun hz =>
    ((hHC.analyticOnNhd_univ ρ (mem_univ ρ)).analyticOrderAt_eq_zero.mp hz) hρ
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hHC.orderAt_ne_top ρ)
  rcases eq_or_ne m 0 with rfl | hm0
  · exact absurd hm.symm hne0
  · rw [← hm, ENat.toNat_coe]; omega

theorem eq_zero_of_one_le_order_toNat (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) {ρ : ℂ}
    (hm : 1 ≤ (analyticOrderAt Λ ρ).toNat) : Λ ρ = 0 := by
  by_contra hnz
  rw [(hHC.analyticOnNhd_univ ρ (mem_univ ρ)).analyticOrderAt_eq_zero.mpr hnz] at hm
  simp at hm

theorem orderAt_one_sub (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) (z : ℂ) :
    analyticOrderAt Λ (1 - z) = analyticOrderAt Λ z := by
  have h := RHTower.analyticOrderAt_comp_one_sub hHC.entire_Λ z
  rwa [show (fun w => Λ (1 - w)) = Λ from funext hHC.sym_Λ] at h

theorem orderAt_conj (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) (z : ℂ) :
    analyticOrderAt Λ (starRingEnd ℂ z) = analyticOrderAt Λ z :=
  RHTower.analyticOrderAt_conj_of_conjEquivariant hHC.conj_Λ
    (hHC.analyticOnNhd_univ z (mem_univ z))
    (hHC.analyticOnNhd_univ (starRingEnd ℂ z) (mem_univ _))

theorem neg_logDeriv_F_eq (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv F s =
      (κ₀ : ℂ) * (1 / s + 1 / (s - 1)) +
      (κγ : ℂ) * logDeriv (shiftedPolePoly γ) s +
      (2 * d : ℕ) * logDeriv Complex.Gammaℝ s +
      (d : ℂ) * (logDeriv Complex.Gammaℝ (s + (γ : ℂ) * I) +
        logDeriv Complex.Gammaℝ (s - (γ : ℂ) * I)) -
      logDeriv Λ s := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Λ =ᶠ[𝓝 s] fun w =>
      (w * (w - 1)) ^ κ₀ * shiftedPolePoly γ w ^ κγ * coupledGamma γ d w * F w :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hs) fun w hw => hHC.completed_eq w hw
  have hΛ_ld : logDeriv Λ s =
      logDeriv (fun w =>
        (w * (w - 1)) ^ κ₀ * shiftedPolePoly γ w ^ κγ * coupledGamma γ d w * F w) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hq0 : s * (s - 1) ≠ 0 := mul_ne_zero hs0 hs1
  have hsp0 : shiftedPolePoly γ s ≠ 0 := shiftedPolePoly_ne_zero_of_one_lt_re γ hs
  have hΓ0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓp0 : Complex.Gammaℝ (s + (γ : ℂ) * I) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΓm0 : Complex.Gammaℝ (s - (γ : ℂ) * I) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hcG0 : coupledGamma γ d s ≠ 0 :=
    mul_ne_zero (pow_ne_zero (2 * d) hΓ0) (pow_ne_zero d (mul_ne_zero hΓp0 hΓm0))
  have hF0 : F s ≠ 0 := hHC.ne_zero_F s hs
  have hqd : DifferentiableAt ℂ (fun w : ℂ => w * (w - 1)) s := by fun_prop
  have hspd : DifferentiableAt ℂ (shiftedPolePoly γ) s := by unfold shiftedPolePoly; fun_prop
  have hΓd : DifferentiableAt ℂ Complex.Gammaℝ s :=
    GaloisForLFunctions.differentiableAt_Gammaℝ (by linarith)
  have hΓpd_at : DifferentiableAt ℂ Complex.Gammaℝ (s + (γ : ℂ) * I) :=
    GaloisForLFunctions.differentiableAt_Gammaℝ (by simp; linarith)
  have hΓmd_at : DifferentiableAt ℂ Complex.Gammaℝ (s - (γ : ℂ) * I) :=
    GaloisForLFunctions.differentiableAt_Gammaℝ (by simp; linarith)
  have hΓpd : DifferentiableAt ℂ (fun w : ℂ => Complex.Gammaℝ (w + (γ : ℂ) * I)) s :=
    DifferentiableAt.comp s hΓpd_at (differentiableAt_id.add_const _)
  have hΓmd : DifferentiableAt ℂ (fun w : ℂ => Complex.Gammaℝ (w - (γ : ℂ) * I)) s :=
    DifferentiableAt.comp s hΓmd_at (differentiableAt_id.sub_const _)
  have hΓpm_d : DifferentiableAt ℂ
      (fun w : ℂ => Complex.Gammaℝ (w + (γ : ℂ) * I) * Complex.Gammaℝ (w - (γ : ℂ) * I)) s :=
    hΓpd.mul hΓmd
  have hcGd : DifferentiableAt ℂ (coupledGamma γ d) s := by
    unfold coupledGamma
    exact (hΓd.fun_pow (2 * d)).mul (hΓpm_d.fun_pow d)
  have hFd : DifferentiableAt ℂ F s := (hHC.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs)
  have hq_ld : logDeriv (fun w : ℂ => w * (w - 1)) s = 1 / s + 1 / (s - 1) := by
    have hid : DifferentiableAt ℂ (fun w : ℂ => w) s := differentiableAt_id
    have hsub1 : DifferentiableAt ℂ (fun w : ℂ => w - 1) s := by fun_prop
    rw [logDeriv_mul (f := fun w : ℂ => w) (g := fun w : ℂ => w - 1) s hs0 hs1 hid hsub1]
    congr 1
    · rw [logDeriv_apply, deriv_id'', one_div]
    · rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  have hcG_ld : logDeriv (coupledGamma γ d) s =
      (2 * d : ℕ) * logDeriv Complex.Gammaℝ s +
        (d : ℂ) * (logDeriv Complex.Gammaℝ (s + (γ : ℂ) * I) +
          logDeriv Complex.Gammaℝ (s - (γ : ℂ) * I)) := by
    unfold coupledGamma
    rw [logDeriv_mul (f := fun w => Complex.Gammaℝ w ^ (2 * d))
          (g := fun w => (Complex.Gammaℝ (w + (γ : ℂ) * I) * Complex.Gammaℝ (w - (γ : ℂ) * I)) ^ d)
          s (pow_ne_zero (2 * d) hΓ0) (pow_ne_zero d (mul_ne_zero hΓp0 hΓm0))
          (hΓd.fun_pow (2 * d)) (hΓpm_d.fun_pow d),
        logDeriv_fun_pow hΓd (2 * d),
        logDeriv_fun_pow hΓpm_d d,
        logDeriv_mul (f := fun w => Complex.Gammaℝ (w + (γ : ℂ) * I))
          (g := fun w => Complex.Gammaℝ (w - (γ : ℂ) * I)) s hΓp0 hΓm0 hΓpd hΓmd,
        logDeriv_comp_add_const hΓpd_at, logDeriv_comp_sub_const hΓmd_at]
  rw [hΛ_ld,
      logDeriv_mul (f := fun w => (w * (w - 1)) ^ κ₀ * shiftedPolePoly γ w ^ κγ * coupledGamma γ d w)
        (g := F) s
        (mul_ne_zero (mul_ne_zero (pow_ne_zero κ₀ hq0) (pow_ne_zero κγ hsp0)) hcG0) hF0
        (((hqd.fun_pow κ₀).mul (hspd.fun_pow κγ)).mul hcGd) hFd,
      logDeriv_mul (f := fun w => (w * (w - 1)) ^ κ₀ * shiftedPolePoly γ w ^ κγ)
        (g := coupledGamma γ d) s
        (mul_ne_zero (pow_ne_zero κ₀ hq0) (pow_ne_zero κγ hsp0)) hcG0
        ((hqd.fun_pow κ₀).mul (hspd.fun_pow κγ)) hcGd,
      logDeriv_mul (f := fun w => (w * (w - 1)) ^ κ₀)
        (g := fun w => shiftedPolePoly γ w ^ κγ) s
        (pow_ne_zero κ₀ hq0) (pow_ne_zero κγ hsp0) (hqd.fun_pow κ₀) (hspd.fun_pow κγ),
      logDeriv_fun_pow hqd κ₀, logDeriv_fun_pow hspd κγ, hq_ld, hcG_ld]
  ring

end HeightCoupledSystem

/-- **Unconditional correspondence height coupling.** For any `CompletedPositiveSystem κ d F Λ` and
ordinate `γ ∈ ℝ`, `F_γ(s) = F(s)² F(s + iγ) F(s − iγ)` and `Λ_γ(s) = Λ(s)² Λ(s + iγ) Λ(s − iγ)`
form a `HeightCoupledSystem (2 * κ) κ d γ`. -/
theorem CompletedPositiveSystem.heightCouple {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (γ : ℝ) :
    HeightCoupledSystem (2 * κ) κ d γ (heightCoupledF F γ) (heightCoupledΛ Λ γ) where
  degree_pos := hS.degree_pos
  diffOn_F := by
    have hU_p : MapsTo (fun s : ℂ => s + (γ : ℂ) * I) {s : ℂ | 1 < s.re} {s : ℂ | 1 < s.re} :=
      fun s hs => by change 1 < (s + (γ : ℂ) * I).re; simp; exact hs
    have hU_m : MapsTo (fun s : ℂ => s - (γ : ℂ) * I) {s : ℂ | 1 < s.re} {s : ℂ | 1 < s.re} :=
      fun s hs => by change 1 < (s - (γ : ℂ) * I).re; simp; exact hs
    exact ((hS.diffOn_F.pow 2).mul (hS.diffOn_F.comp (by fun_prop) hU_p)).mul
      (hS.diffOn_F.comp (by fun_prop) hU_m)
  ne_zero_F := fun s hs => by
    unfold heightCoupledF
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero 2 (hS.ne_zero_F s hs))
        (hS.ne_zero_F (s + (γ : ℂ) * I) (by simp; exact hs)))
      (hS.ne_zero_F (s - (γ : ℂ) * I) (by simp; exact hs))
  posDef_neg_logDeriv := fun {σ} hσ => by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    let φ : ℝ → ℝ := fun u => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re
    have hφ : IsEvenPosDef φ := hS.posDef_neg_logDeriv hσ
    have hshift : IsEvenPosDef (symSquareShift γ (-1) φ) := IsEvenPosDef.symSquareShift hφ γ (-1)
    have heq : (fun u : ℝ =>
        (-logDeriv (heightCoupledF F γ) ((σ : ℂ) + (u : ℂ) * I)).re) =
        symSquareShift γ (-1) φ := by
      funext u
      set s : ℂ := (σ : ℂ) + (u : ℂ) * I
      have hs : 1 < s.re := by simp [s]; exact hσ
      have hsp : 1 < (s + (γ : ℂ) * I).re := by simp [s]; exact hσ
      have hsm : 1 < (s - (γ : ℂ) * I).re := by simp [s]; exact hσ
      have hFd : DifferentiableAt ℂ F s := (hS.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs)
      have hFpd_at : DifferentiableAt ℂ F (s + (γ : ℂ) * I) :=
        (hS.diffOn_F _ hsp).differentiableAt (hopen.mem_nhds hsp)
      have hFmd_at : DifferentiableAt ℂ F (s - (γ : ℂ) * I) :=
        (hS.diffOn_F _ hsm).differentiableAt (hopen.mem_nhds hsm)
      have hFpd : DifferentiableAt ℂ (fun w : ℂ => F (w + (γ : ℂ) * I)) s :=
        hFpd_at.comp s (by fun_prop)
      have hFmd : DifferentiableAt ℂ (fun w : ℂ => F (w - (γ : ℂ) * I)) s :=
        hFmd_at.comp s (by fun_prop)
      have hF0 : F s ≠ 0 := hS.ne_zero_F s hs
      have hFp0 : F (s + (γ : ℂ) * I) ≠ 0 := hS.ne_zero_F _ hsp
      have hFm0 : F (s - (γ : ℂ) * I) ≠ 0 := hS.ne_zero_F _ hsm
      unfold heightCoupledF
      rw [logDeriv_mul (f := fun w => F w ^ 2 * F (w + (γ : ℂ) * I))
            (g := fun w => F (w - (γ : ℂ) * I)) s
            (mul_ne_zero (pow_ne_zero 2 hF0) hFp0) hFm0
            ((hFd.fun_pow 2).mul hFpd) hFmd,
          logDeriv_mul (f := fun w => F w ^ 2) (g := fun w => F (w + (γ : ℂ) * I)) s
            (pow_ne_zero 2 hF0) hFp0 (hFd.fun_pow 2) hFpd,
          logDeriv_fun_pow hFd 2,
          logDeriv_comp_add_const hFpd_at, logDeriv_comp_sub_const hFmd_at]
      have ep : s + (γ : ℂ) * I = (σ : ℂ) + ((u + γ : ℝ) : ℂ) * I := by
        dsimp [s]; push_cast; ring
      have em : s - (γ : ℂ) * I = (σ : ℂ) + ((u - γ : ℝ) : ℂ) * I := by
        dsimp [s]; push_cast; ring
      rw [ep, em]
      dsimp [symSquareShift, φ, s]
      have h2 : ((2 : ℂ) * logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re =
          2 * (logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re := by
        simp [Complex.mul_re]
      rw [h2]
      ring
    rwa [heq]
  entire_Λ :=
    ((hS.entire_Λ.pow 2).mul (hS.entire_Λ.comp (by fun_prop))).mul
      (hS.entire_Λ.comp (by fun_prop))
  orderOne_Λ := by
    have hop : OrderOneEnvelope (fun s : ℂ => Λ (s + (γ : ℂ) * I)) :=
      (hS.orderOne_Λ.comp_affine 1 ((γ : ℂ) * I)).congr fun s => congrArg Λ (by ring)
    have hom : OrderOneEnvelope (fun s : ℂ => Λ (s - (γ : ℂ) * I)) :=
      (hS.orderOne_Λ.comp_affine 1 (-((γ : ℂ) * I))).congr fun s => congrArg Λ (by ring)
    exact (((hS.orderOne_Λ.mul hS.orderOne_Λ).mul hop).mul hom).congr fun s => by
      dsimp [heightCoupledΛ]; ring
  sym_Λ := fun s => by
    unfold heightCoupledΛ
    have ep : 1 - s + (γ : ℂ) * I = 1 - (s - (γ : ℂ) * I) := by ring
    have em : 1 - s - (γ : ℂ) * I = 1 - (s + (γ : ℂ) * I) := by ring
    rw [hS.sym_Λ s, ep, hS.sym_Λ (s - (γ : ℂ) * I), em, hS.sym_Λ (s + (γ : ℂ) * I)]
    ring
  conj_Λ := fun s => by
    unfold heightCoupledΛ
    have ep : starRingEnd ℂ s + (γ : ℂ) * I = starRingEnd ℂ (s - (γ : ℂ) * I) := by simp
    have em : starRingEnd ℂ s - (γ : ℂ) * I = starRingEnd ℂ (s + (γ : ℂ) * I) := by simp; ring
    rw [hS.conj_Λ s, ep, hS.conj_Λ (s - (γ : ℂ) * I), em, hS.conj_Λ (s + (γ : ℂ) * I)]
    simp only [map_mul, map_pow]
    ring
  completed_eq := fun s hs => by
    set sp : ℂ := s + (γ : ℂ) * I
    set sm : ℂ := s - (γ : ℂ) * I
    have hsp : 1 < sp.re := by simp [sp]; exact hs
    have hsm : 1 < sm.re := by simp [sm]; exact hs
    unfold heightCoupledΛ heightCoupledF coupledGamma
    change Λ s ^ 2 * Λ sp * Λ sm =
      (s * (s - 1)) ^ (2 * κ) * shiftedPolePoly γ s ^ κ *
        (Complex.Gammaℝ s ^ (2 * d) * (Complex.Gammaℝ sp * Complex.Gammaℝ sm) ^ d) *
        (F s ^ 2 * F sp * F sm)
    rw [hS.completed_eq s hs, hS.completed_eq sp hsp, hS.completed_eq sm hsm]
    have hpole : sp * (sp - 1) * (sm * (sm - 1)) = shiftedPolePoly γ s := by
      unfold shiftedPolePoly
      dsimp [sp, sm]
      calc (s + (γ : ℂ) * I) * (s + (γ : ℂ) * I - 1) *
            ((s - (γ : ℂ) * I) * (s - (γ : ℂ) * I - 1))
          = ((s + (γ : ℂ) * I) * (s - (γ : ℂ) * I)) *
              (((s - 1) + (γ : ℂ) * I) * ((s - 1) - (γ : ℂ) * I)) := by ring
        _ = (s ^ 2 - ((γ : ℂ) * I) ^ 2) * ((s - 1) ^ 2 - ((γ : ℂ) * I) ^ 2) := by ring
        _ = (s ^ 2 + (γ : ℂ) ^ 2) * ((s - 1) ^ 2 + (γ : ℂ) ^ 2) := by
              rw [mul_pow, Complex.I_sq]; ring
    have hk2 : ((s * (s - 1)) ^ κ) ^ 2 = (s * (s - 1)) ^ (2 * κ) := by
      rw [← pow_mul, mul_comm κ 2]
    have hd2 : (Complex.Gammaℝ s ^ d) ^ 2 = Complex.Gammaℝ s ^ (2 * d) := by
      rw [← pow_mul, mul_comm d 2]
    have hsp_pow : (sp * (sp - 1)) ^ κ * (sm * (sm - 1)) ^ κ = shiftedPolePoly γ s ^ κ := by
      rw [← mul_pow, hpole]
    have hΓ_pow : Complex.Gammaℝ sp ^ d * Complex.Gammaℝ sm ^ d =
        (Complex.Gammaℝ sp * Complex.Gammaℝ sm) ^ d := by
      rw [← mul_pow]
    calc ((s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * F s) ^ 2 *
          ((sp * (sp - 1)) ^ κ * Complex.Gammaℝ sp ^ d * F sp) *
          ((sm * (sm - 1)) ^ κ * Complex.Gammaℝ sm ^ d * F sm)
        = ((s * (s - 1)) ^ κ) ^ 2 * ((sp * (sp - 1)) ^ κ * (sm * (sm - 1)) ^ κ) *
          ((Complex.Gammaℝ s ^ d) ^ 2 * (Complex.Gammaℝ sp ^ d * Complex.Gammaℝ sm ^ d)) *
          (F s ^ 2 * F sp * F sm) := by ring
      _ = _ := by rw [hk2, hsp_pow, hd2, hΓ_pow]

private theorem enat_add_ne_top {a b : ℕ∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a + b ≠ ⊤ := by
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
  exact_mod_cast ENat.coe_ne_top (m + n)

/-- Exact vanishing-order formula for `heightCoupledΛ`:
`ord_z(Λ_γ) = 2 ord_z(Λ) + ord_{z + iγ}(Λ) + ord_{z − iγ}(Λ)`. -/
theorem CompletedPositiveSystem.orderAt_heightCoupledΛ {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (γ : ℝ) (z : ℂ) :
    (analyticOrderAt (heightCoupledΛ Λ γ) z).toNat =
      2 * (analyticOrderAt Λ z).toNat +
      (analyticOrderAt Λ (z + (γ : ℂ) * I)).toNat +
      (analyticOrderAt Λ (z - (γ : ℂ) * I)).toNat := by
  have hfn : heightCoupledΛ Λ γ =
      ((Λ * Λ) * fun w => Λ (w + (γ : ℂ) * I)) * fun w => Λ (w - (γ : ℂ) * I) :=
    funext fun w => by dsimp [heightCoupledΛ]; ring
  have han0 : AnalyticAt ℂ Λ z := hS.entire_Λ.analyticAt z
  have hanp : AnalyticAt ℂ (fun w => Λ (w + (γ : ℂ) * I)) z :=
    (hS.entire_Λ.comp (by fun_prop)).analyticAt z
  have hanm : AnalyticAt ℂ (fun w => Λ (w - (γ : ℂ) * I)) z :=
    (hS.entire_Λ.comp (by fun_prop)).analyticAt z
  have hord : analyticOrderAt (heightCoupledΛ Λ γ) z =
      ((analyticOrderAt Λ z + analyticOrderAt Λ z) +
        analyticOrderAt Λ (z + (γ : ℂ) * I)) +
      analyticOrderAt Λ (z - (γ : ℂ) * I) := by
    rw [hfn,
        analyticOrderAt_mul (((han0.mul han0).mul hanp)) hanm,
        analyticOrderAt_mul (han0.mul han0) hanp,
        analyticOrderAt_mul han0 han0,
        analyticOrderAt_comp_add_const hS.entire_Λ z ((γ : ℂ) * I),
        analyticOrderAt_comp_sub_const hS.entire_Λ z ((γ : ℂ) * I)]
  have nt0 := hS.orderAt_ne_top z
  have ntp := hS.orderAt_ne_top (z + (γ : ℂ) * I)
  have ntm := hS.orderAt_ne_top (z - (γ : ℂ) * I)
  have nt00 : analyticOrderAt Λ z + analyticOrderAt Λ z ≠ ⊤ := enat_add_ne_top nt0 nt0
  have nt00p : (analyticOrderAt Λ z + analyticOrderAt Λ z) +
      analyticOrderAt Λ (z + (γ : ℂ) * I) ≠ ⊤ := enat_add_ne_top nt00 ntp
  rw [hord, ENat.toNat_add nt00p ntm, ENat.toNat_add nt00 ntp, ENat.toNat_add nt0 nt0]
  omega

/-- **Phase collision on the real axis (`(±iγ) ↦ 0`).** At every real point `x : ℝ`,
`ord_x(heightCoupledΛ Λ γ) = 2 ord_x(Λ) + 2 ord_{x + iγ}(Λ)`, supplying the exact `2 : 1` real
anchor required by `two_mul_le_real_anchor_of_single_ordinate`. -/
theorem CompletedPositiveSystem.orderAt_heightCoupledΛ_real {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (γ x : ℝ) :
    (analyticOrderAt (heightCoupledΛ Λ γ) (x : ℂ)).toNat =
      2 * (analyticOrderAt Λ (x : ℂ)).toNat +
      2 * (analyticOrderAt Λ ((x : ℂ) + (γ : ℂ) * I)).toNat := by
  rw [CompletedPositiveSystem.orderAt_heightCoupledΛ hS γ (x : ℂ)]
  have hconj_eq : (x : ℂ) - (γ : ℂ) * I = starRingEnd ℂ ((x : ℂ) + (γ : ℂ) * I) := by
    simp; ring
  rw [hconj_eq, hS.orderAt_conj]
  omega

/-- **Zero-tax real-pair contraction inside `HeightCoupledSystem` (`Δκ₀ = 0, Δκγ = 0`).** -/
theorem HeightCoupledSystem.contractRealPair {κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) {β : ℝ} (hβ : β ≠ 1 / 2)
    (hzero : Λ (β : ℂ) = 0) :
    ∃ Λc : ℂ → ℂ,
      HeightCoupledSystem κ₀ κγ d γ (fun s => F s * midpointSymSquare β s) Λc ∧
      (∀ s : ℂ, Λc s * realPairPoly β s = Λ s * (s - 1 / 2) ^ 2) ∧
      (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 2 := by
  classical
  obtain ⟨hβ0, hβ1⟩ := hHC.zero_re_mem_Icc hzero
  simp only [Complex.ofReal_re] at hβ0 hβ1
  have hzero_sym : Λ (((1 - β : ℝ) : ℂ)) = 0 := by
    have he : (((1 - β : ℝ) : ℂ)) = 1 - (β : ℂ) := by push_cast; ring
    rw [he, hHC.sym_Λ, hzero]
  have hne_pair : (β : ℂ) ≠ ((1 - β : ℝ) : ℂ) := fun heq => by
    have := congrArg Complex.re heq; simp at this; exact hβ (by linarith)
  let L : List (ℂ × ℕ) := [((β : ℂ), 1), (((1 - β : ℝ) : ℂ), 1)]
  have hnd : (L.map Prod.fst).Nodup := by
    dsimp [L]
    rw [List.nodup_cons, List.mem_singleton]
    exact ⟨hne_pair, List.nodup_singleton _⟩
  have hb_ord : (1 : ℕ∞) ≤ analyticOrderAt Λ (β : ℂ) := by
    have h1 := hHC.one_le_order_toNat_of_eq_zero hzero
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hHC.orderAt_ne_top (β : ℂ))
    rw [← hk] at h1 ⊢; simp only [ENat.toNat_coe] at h1; exact_mod_cast h1
  have hb_sym_ord : (1 : ℕ∞) ≤ analyticOrderAt Λ (((1 - β : ℝ) : ℂ)) := by
    have h1 := hHC.one_le_order_toNat_of_eq_zero hzero_sym
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (hHC.orderAt_ne_top (((1 - β : ℝ) : ℂ)))
    rw [← hk] at h1 ⊢; simp only [ENat.toNat_coe] at h1; exact_mod_cast h1
  obtain ⟨Q, hdQ, hoQ, hQ_eq, _, hQ_out⟩ := exists_quotient_prod_pow L Λ hnd
    hHC.entire_Λ hHC.orderOne_Λ (fun p hp => by
      simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hb_ord
      · exact hb_sym_ord)
  have hQ_poly : ∀ s : ℂ, realPairPoly β s * Q s = Λ s := fun s => by
    have h := hQ_eq s
    simp only [L, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, pow_one, mul_one] at h
    unfold realPairPoly
    linear_combination h
  let Λc : ℂ → ℂ := fun s => Q s * (s - 1 / 2) ^ 2
  have hdΛc : Differentiable ℂ Λc := hdQ.mul (by fun_prop)
  have hoΛc : OrderOneEnvelope Λc := hoQ.mul (orderOneEnvelope_pow_sub_const (1 / 2) 2)
  have hrel : ∀ s : ℂ, Λc s * realPairPoly β s = Λ s * (s - 1 / 2) ^ 2 := fun s => by
    dsimp [Λc]; rw [← hQ_poly s]; ring
  have hP_nz_off : ∀ z : ℂ, z ∉ ({(β : ℂ), ((1 - β : ℝ) : ℂ)} : Finset ℂ) →
      realPairPoly β z ≠ 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    exact mul_ne_zero (sub_ne_zero.mpr hz.1) (sub_ne_zero.mpr hz.2)
  have hsym_c : ∀ s : ℂ, Λc (1 - s) = Λc s := by
    refine continuous_eq_of_mul_eq_off_finset' {(β : ℂ), ((1 - β : ℝ) : ℂ)}
      (hdΛc.continuous.comp (by fun_prop)) hdΛc.continuous hP_nz_off fun z => ?_
    have hP_sym : realPairPoly β z = realPairPoly β (1 - z) := by
      unfold realPairPoly; push_cast; ring
    have hC_sym : ((1 - z) - 1 / 2) ^ 2 = (z - 1 / 2) ^ 2 := by ring
    rw [hP_sym, hrel (1 - z), hHC.sym_Λ z, hC_sym, ← hP_sym, ← hrel z]
  have hconj_c : ∀ s : ℂ, Λc (starRingEnd ℂ s) = starRingEnd ℂ (Λc s) := by
    have hinv := continuous_eq_of_mul_eq_off_finset' {(β : ℂ), ((1 - β : ℝ) : ℂ)}
      (Complex.continuous_conj.comp (hdΛc.continuous.comp Complex.continuous_conj))
      hdΛc.continuous hP_nz_off fun z => by
        have hP_conj : starRingEnd ℂ (realPairPoly β (starRingEnd ℂ z)) = realPairPoly β z := by
          unfold realPairPoly
          simp only [map_mul, map_sub, Complex.conj_ofReal, RingHomCompTriple.comp_apply,
            RingHom.id_apply]
        have hC_conj : starRingEnd ℂ ((starRingEnd ℂ z - 1 / 2) ^ 2) = (z - 1 / 2) ^ 2 := by
          simp [map_ofNat]
        have h1 := congrArg (starRingEnd ℂ) (hrel (starRingEnd ℂ z))
        rw [map_mul (starRingEnd ℂ) (Λc (starRingEnd ℂ z)),
            map_mul (starRingEnd ℂ) (Λ (starRingEnd ℂ z)),
            hP_conj, hC_conj, hHC.conj_Λ z, Complex.conj_conj, ← hrel z] at h1
        simpa only [Function.comp_apply] using h1
    intro s
    have hs := congrArg (starRingEnd ℂ) (hinv s)
    simpa [Function.comp_apply] using hs
  have hP_nz_re : ∀ s : ℂ, 1 < s.re → realPairPoly β s ≠ 0 := by
    intro s hs
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hM_nz : ∀ s : ℂ, 1 < s.re → midpointSymSquare β s ≠ 0 := by
    intro s hs
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact div_ne_zero (pow_ne_zero 2 hs_half) (hP_nz_re s hs)
  have hM_diffAt : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (midpointSymSquare β) s := fun s hs =>
    DifferentiableAt.div (by fun_prop) (by unfold realPairPoly; fun_prop) (hP_nz_re s hs)
  have hHCc : HeightCoupledSystem κ₀ κγ d γ (fun s => F s * midpointSymSquare β s) Λc :=
    { degree_pos := hHC.degree_pos
      diffOn_F := hHC.diffOn_F.mul (fun s hs => (hM_diffAt s hs).differentiableWithinAt)
      ne_zero_F := fun s hs => mul_ne_zero (hHC.ne_zero_F s hs) (hM_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => F s * midpointSymSquare β s) ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (midpointSymSquare β) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := midpointSymSquare β) s
                (hHC.ne_zero_F s hs) (hM_nz s hs)
                ((hHC.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                (hM_diffAt s hs),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add_coupled (hHC.posDef_neg_logDeriv hσ)
          (isEvenPosDef_midpointSymSquare hβ0 hβ1 hσ)
      entire_Λ := hdΛc
      orderOne_Λ := hoΛc
      sym_Λ := hsym_c
      conj_Λ := hconj_c
      completed_eq := fun s hs => by
        have hP_nz := hP_nz_re s hs
        apply mul_right_cancel₀ hP_nz
        have hdiv : midpointSymSquare β s * realPairPoly β s = (s - 1 / 2) ^ 2 :=
          div_mul_cancel₀ _ hP_nz
        calc Λc s * realPairPoly β s
            = Λ s * (s - 1 / 2) ^ 2 := hrel s
          _ = ((s * (s - 1)) ^ κ₀ * shiftedPolePoly γ s ^ κγ * coupledGamma γ d s * F s) *
                (midpointSymSquare β s * realPairPoly β s) := by
              rw [hHC.completed_eq s hs, hdiv]
          _ = (s * (s - 1)) ^ κ₀ * shiftedPolePoly γ s ^ κγ * coupledGamma γ d s *
                (F s * midpointSymSquare β s) * realPairPoly β s := by ring }
  have hord : (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 2 := by
    have hnot : (1 / 2 : ℂ) ∉ L.map Prod.fst := by
      simp only [L, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := congrArg Complex.re h; simp at this; exact hβ (by linarith)
      · have := congrArg Complex.re h; simp at this; exact hβ (by linarith)
    have hΛc_eq : Λc = Q * ((· - (1 / 2 : ℂ)) ^ 2) := rfl
    have han_mon : AnalyticAt ℂ ((· - (1 / 2 : ℂ)) ^ 2) (1 / 2) :=
      ((differentiable_id.sub_const (1 / 2 : ℂ)).pow 2).analyticAt (1 / 2)
    have h1 : analyticOrderAt Λc (1 / 2) = analyticOrderAt Λ (1 / 2) + (2 : ℕ) := by
      rw [hΛc_eq, analyticOrderAt_mul (hdQ.analyticAt _) han_mon,
          hQ_out (1 / 2) hnot, analyticOrderAt_centeredMonomial]
    rw [h1, ENat.toNat_add (hHC.orderAt_ne_top (1 / 2)) (ENat.coe_ne_top 2), ENat.toNat_coe]
  exact ⟨Λc, hHCc, hrel, hord⟩

/-- **Zero-tax collided quartet contraction inside `HeightCoupledSystem` (`Δκ₀ = 0, Δκγ = 0`).**
Whenever `0 < a < 1/2`, `γ ≠ 0`, `2 ≤ ord_{1/2 + a}(Λ)`, and `Λ(1/2 + a + iγ) = 0`, multiplying `F`
by `coupledQuartetSymSquare a a γ` contracts both collided real pairs and the complex quartet onto
`{1/2, 1/2 ± iγ}` at zero marginal pole cost. -/
theorem HeightCoupledSystem.contractCollidedQuartet {κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hγ : γ ≠ 0)
    (hreal : 2 ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat)
    (hquartet : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      HeightCoupledSystem κ₀ κγ d γ (fun s => F s * coupledQuartetSymSquare a a γ s) Λc ∧
      (∀ s : ℂ, Λc s * (realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s) =
        Λ s * ((s - 1 / 2) ^ 4 * quartetCritPoly γ s)) ∧
      (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 4 ∧
      (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
        (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 ∧
      (analyticOrderAt Λc ((1 / 2 + a : ℝ) : ℂ)).toNat + 2 =
        (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat ∧
      (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + 1 =
        (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
      (∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
        (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat) := by
  obtain ⟨Λc, hdΛc, hoΛc, hsym_c, hconj_c, hrel, h1, h2, h3, h4, h5⟩ :=
    exists_coupled_entire_contraction 2 ha0 ha0 hγ hHC.entire_Λ hHC.orderOne_Λ
      hHC.sym_Λ hHC.conj_Λ hHC.orderAt_ne_top hreal hquartet
  have hP_nz : ∀ s : ℂ, 1 < s.re → realPairPoly (1 / 2 + a) s ≠ 0 := by
    intro s hs
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hOff_nz : ∀ s : ℂ, 1 < s.re → quartetOffPoly a γ s ≠ 0 := by
    intro s hs
    unfold quartetOffPoly
    rw [sq_add_sq_eq_mul_I', sq_add_sq_eq_mul_I']
    refine mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_))
      (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hCrit_nz : ∀ s : ℂ, 1 < s.re → quartetCritPoly γ s ≠ 0 := by
    intro s hs
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I' s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf; rw [hf]
    refine pow_ne_zero 2 (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hW_nz : ∀ s : ℂ, 1 < s.re → coupledQuartetSymSquare a a γ s ≠ 0 := by
    intro s hs
    unfold coupledQuartetSymSquare midpointSymSquare
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact mul_ne_zero (pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 hs_half) (hP_nz s hs)))
      (div_ne_zero (hCrit_nz s hs) (hOff_nz s hs))
  have hW_diffAt : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (coupledQuartetSymSquare a a γ) s := by
    intro s hs
    unfold coupledQuartetSymSquare midpointSymSquare
    exact (((DifferentiableAt.div (by fun_prop) (by unfold realPairPoly; fun_prop)
      (hP_nz s hs)).fun_pow 2).mul
      (DifferentiableAt.div (by unfold quartetCritPoly; fun_prop)
        (by unfold quartetOffPoly; fun_prop) (hOff_nz s hs)))
  have hHCc : HeightCoupledSystem κ₀ κγ d γ (fun s => F s * coupledQuartetSymSquare a a γ s) Λc :=
    { degree_pos := hHC.degree_pos
      diffOn_F := hHC.diffOn_F.mul (fun s hs => (hW_diffAt s hs).differentiableWithinAt)
      ne_zero_F := fun s hs => mul_ne_zero (hHC.ne_zero_F s hs) (hW_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => F s * coupledQuartetSymSquare a a γ s)
              ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (coupledQuartetSymSquare a a γ) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := coupledQuartetSymSquare a a γ) s
                (hHC.ne_zero_F s hs) (hW_nz s hs)
                ((hHC.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                (hW_diffAt s hs),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add_coupled (hHC.posDef_neg_logDeriv hσ)
          (isEvenPosDef_coupledQuartetSymSquare ha0 le_rfl ha1 hσ)
      entire_Λ := hdΛc
      orderOne_Λ := hoΛc
      sym_Λ := hsym_c
      conj_Λ := hconj_c
      completed_eq := fun s hs => by
        have hden_nz : realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s ≠ 0 :=
          mul_ne_zero (pow_ne_zero 2 (hP_nz s hs)) (hOff_nz s hs)
        apply mul_right_cancel₀ hden_nz
        have hW_mul : coupledQuartetSymSquare a a γ s *
            (realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s) =
            (s - 1 / 2) ^ 4 * quartetCritPoly γ s := by
          unfold coupledQuartetSymSquare midpointSymSquare
          have hp2 : realPairPoly (1 / 2 + a) s ^ 2 ≠ 0 := pow_ne_zero 2 (hP_nz s hs)
          have ho : quartetOffPoly a γ s ≠ 0 := hOff_nz s hs
          rw [div_pow]
          calc ((s - 1 / 2) ^ 2) ^ 2 / realPairPoly (1 / 2 + a) s ^ 2 *
                (quartetCritPoly γ s / quartetOffPoly a γ s) *
                (realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s)
              = (((s - 1 / 2) ^ 2) ^ 2 / realPairPoly (1 / 2 + a) s ^ 2 *
                  realPairPoly (1 / 2 + a) s ^ 2) *
                (quartetCritPoly γ s / quartetOffPoly a γ s * quartetOffPoly a γ s) := by ring
            _ = ((s - 1 / 2) ^ 2) ^ 2 * quartetCritPoly γ s := by
                rw [div_mul_cancel₀ _ hp2, div_mul_cancel₀ _ ho]
            _ = (s - 1 / 2) ^ 4 * quartetCritPoly γ s := by ring
        calc Λc s * (realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s)
            = Λ s * ((s - 1 / 2) ^ 4 * quartetCritPoly γ s) := hrel s
          _ = ((s * (s - 1)) ^ κ₀ * shiftedPolePoly γ s ^ κγ * coupledGamma γ d s * F s) *
                (coupledQuartetSymSquare a a γ s *
                  (realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s)) := by
              rw [hHC.completed_eq s hs, hW_mul]
          _ = (s * (s - 1)) ^ κ₀ * shiftedPolePoly γ s ^ κγ * coupledGamma γ d s *
                (F s * coupledQuartetSymSquare a a γ s) *
                (realPairPoly (1 / 2 + a) s ^ 2 * quartetOffPoly a γ s) := by ring }
  exact ⟨Λc, hHCc, hrel, h1, h2, h3, h4, fun z hz0 hza1 hza2 => h5 z hz0 hza1 hza2 hza1 hza2⟩

/-- **Unconditional height-coupled zero-tax contraction of ANY complex quartet across the entire
strip `0 < a < 1/2`.** Given only `Λ(1/2 + a + iγ) = 0` (`0 < a < 1/2`, `γ ≠ 0`) on a
`CompletedPositiveSystem κ d F Λ`, lifting to `heightCouple γ` automatically collides `(±iγ) ↦ 0`
with multiplicity `≥ 2` at `1/2 + a` and contracts the quartet at `Δκ₀ = 0, Δκγ = 0`. -/
theorem CompletedPositiveSystem.contractComplexQuartet_heightCoupled {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {a γ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hγ : γ ≠ 0)
    (hquartet : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      HeightCoupledSystem (2 * κ) κ d γ
        (fun s => heightCoupledF F γ s * coupledQuartetSymSquare a a γ s) Λc ∧
      (analyticOrderAt Λc (1 / 2)).toNat =
        2 * (analyticOrderAt Λ (1 / 2)).toNat +
        2 * (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 4 := by
  have hHC := CompletedPositiveSystem.heightCouple hS γ
  have hcast_a : (((1 / 2 + a : ℝ) : ℂ)) + (γ : ℂ) * I = 1 / 2 + (a : ℂ) + (γ : ℂ) * I := by
    push_cast; ring
  have hord_q : 1 ≤ (analyticOrderAt Λ (((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I)).toNat := by
    rw [hcast_a]; exact hS.one_le_order_toNat_of_eq_zero hquartet
  have hreal2 : 2 ≤ (analyticOrderAt (heightCoupledΛ Λ γ) ((1 / 2 + a : ℝ) : ℂ)).toNat := by
    have h := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hS γ (1 / 2 + a)
    omega
  have hq_hc : heightCoupledΛ Λ γ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 := by
    unfold heightCoupledΛ; rw [hquartet]; ring
  obtain ⟨Λc, hHCc, _, hord_half, _, _, _, _⟩ :=
    hHC.contractCollidedQuartet ha0 ha1 hγ hreal2 hq_hc
  refine ⟨Λc, hHCc, ?_⟩
  have hhalf_eq : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have h0 := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hS γ (1 / 2)
  rw [← hhalf_eq] at h0
  rw [hord_half, h0]

/-- **Contraction-invariant archimedean budget for `HeightCoupledSystem`.** For every finite set
`X ⊂ (1/2, 1]` of off-central real points,
`(2/3) ord_{1/2}(Λ) + (4/3) ∑_{x ∈ X} ord_x(Λ) < (3/2) κ₀ + 3 κγ + d log(3 + |γ|) − (7/6) d`. -/
theorem HeightCoupledSystem.archimedean_budget {κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) (X : Finset ℝ)
    (hX : ∀ x ∈ X, 1 / 2 < x ∧ x ≤ 1) :
    (2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ) +
      (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) <
    (3 / 2 : ℝ) * (κ₀ : ℝ) + 3 * (κγ : ℝ) +
      (d : ℝ) * Real.log (3 + |γ|) - (7 / 6 : ℝ) * (d : ℝ) := by
  open GaloisForLFunctions.EntireZeroDivisor RHTower RHTower.CompletionZeroPairs
    RHTower.WeilLineIntegral in
  classical
  have hpos2 : 0 ≤ (-logDeriv F (2 : ℂ)).re := by
    have hpd := (hHC.posDef_neg_logDeriv (σ := 2) (by norm_num)).posDef 1 (fun _ => 0) (fun _ => 1)
    simpa using hpd
  have hdecomp := congrArg Complex.re (hHC.neg_logDeriv_F_eq (s := 2) (by norm_num))
  have hre2 : ((κ₀ : ℂ) * (1 / (2 : ℂ) + 1 / ((2 : ℂ) - 1)) +
      (κγ : ℂ) * logDeriv (shiftedPolePoly γ) 2 +
      (2 * d : ℕ) * logDeriv Complex.Gammaℝ 2 +
      (d : ℂ) * (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I) +
        logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)) - logDeriv Λ 2).re =
      (3 / 2 : ℝ) * (κ₀ : ℝ) + (κγ : ℝ) * (logDeriv (shiftedPolePoly γ) 2).re +
      2 * (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re +
      (d : ℝ) * ((logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
        (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re) - (logDeriv Λ 2).re := by
    rw [Complex.sub_re, Complex.add_re, Complex.add_re, Complex.add_re,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
        Complex.add_re, Complex.add_re, Nat.cast_mul, Nat.cast_ofNat]
    have hp1 : (1 / (2 : ℂ)).re = 1 / 2 := by norm_num
    have hp2 : (1 / ((2 : ℂ) - 1)).re = 1 := by norm_num
    rw [hp1, hp2]; ring
  rw [hre2] at hdecomp
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hHC.degree_pos
  have hsp_le : (κγ : ℝ) * (logDeriv (shiftedPolePoly γ) 2).re ≤ 3 * (κγ : ℝ) := by
    have := mul_le_mul_of_nonneg_left (re_logDeriv_shiftedPolePoly_two_le γ) (Nat.cast_nonneg κγ)
    linarith
  have hd_central : 2 * (d : ℝ) * (logDeriv Complex.Gammaℝ 2).re < -(5 / 3 : ℝ) * (d : ℝ) := by
    have := mul_lt_mul_of_pos_left re_logDeriv_Gammaℝ_two_lt (by positivity : (0 : ℝ) < 2 * (d : ℝ))
    linarith
  have hΓp_le : (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) / 2 + 1 / 4 :=
    by simpa using re_logDeriv_Gammaℝ_le_all_heights (σ := 2) (t := γ) (by norm_num) le_rfl
  have hΓm_le : (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) / 2 + 1 / 4 := by
    have he : (2 : ℂ) - (γ : ℂ) * I = ((2 : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by push_cast; ring
    rw [he]
    simpa [abs_neg] using re_logDeriv_Gammaℝ_le_all_heights (σ := 2) (t := -γ) (by norm_num) le_rfl
  have hd_shifted : (d : ℝ) * ((logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
      (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re) ≤
      (d : ℝ) * Real.log (3 + |γ|) + (1 / 2 : ℝ) * (d : ℝ) := by
    have hsum_le : (logDeriv Complex.Gammaℝ (2 + (γ : ℂ) * I)).re +
        (logDeriv Complex.Gammaℝ (2 - (γ : ℂ) * I)).re ≤ Real.log (3 + |γ|) + 1 / 2 := by
      linarith
    have := mul_le_mul_of_nonneg_left hsum_le hd_pos.le
    linarith
  have hΛ2_lt : (logDeriv Λ 2).re <
      (3 / 2 : ℝ) * (κ₀ : ℝ) + 3 * (κγ : ℝ) +
        (d : ℝ) * Real.log (3 + |γ|) - (7 / 6 : ℝ) * (d : ℝ) := by
    linarith
  -- Hadamard zero-pair lower bound on `(logDeriv Λ 2).re`.
  set f : ℂ → ℂ := fun z => Λ (z + 2) with hfdef
  have hfd : Differentiable ℂ f := hHC.entire_Λ.comp (differentiable_id.add_const 2)
  have hf : AnalyticOnNhd ℂ f univ := hfd.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨C, hC, hgrow⟩ := hHC.orderOne_Λ
  have hsum_c : HasSum (fun q : ZeroCopy f =>
      (1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2) (logDeriv Λ 2) :=
    hasSum_logDeriv_zeroPairs hHC.entire_Λ one_ne_zero
      (fun w => by rw [hHC.sym_Λ w, one_mul]) hC.le
      (fun w => by simpa only [orderOneWeight] using hgrow w)
      hHC.two_ne_zero hHC.two_ne_zero
  set term : ZeroCopy f → ℝ := fun q => ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re
  have hsum_re : HasSum term (logDeriv Λ 2).re := hsum_c.mapL Complex.reCLM
  have hterm_nn : ∀ q : ZeroCopy f, 0 ≤ term q := by
    intro q
    have hzq0 : Λ (zeroCopyPoint f q + 2) = 0 := by simpa [hfdef] using apply_zeroCopyPoint hf q
    obtain ⟨h0, h1⟩ := hHC.zero_re_mem_Icc hzq0
    simp only [term, gPair]
    have ha : 0 ≤ (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2))).re := by
      rw [one_div, Complex.inv_re, Complex.sub_re]
      have h2re : (2 : ℂ).re = 2 := by norm_num
      exact div_nonneg (by rw [h2re]; linarith) (Complex.normSq_nonneg _)
    have hb : 0 ≤ (1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))).re := by
      rw [one_div, Complex.inv_re, Complex.sub_re, Complex.sub_re]
      have h2re : (2 : ℂ).re = 2 := by norm_num
      have h1re : (1 : ℂ).re = 1 := by norm_num
      exact div_nonneg (by rw [h2re, h1re]; linarith) (Complex.normSq_nonneg _)
    have he : ((1 / 2 : ℂ) * (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
        1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2))))).re =
        ((1 / ((2 : ℂ) - (zeroCopyPoint f q + 2))).re +
          (1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))).re) / 2 := by
      have : (1 / 2 : ℂ) * (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
          1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))) =
          (1 / ((2 : ℂ) - (zeroCopyPoint f q + 2)) +
            1 / ((2 : ℂ) - (1 - (zeroCopyPoint f q + 2)))) / 2 := by ring
      rw [this, Complex.div_ofNat_re, Complex.add_re]
    linarith
  have hdiv_toNat : ∀ w : ℂ,
      ((MeromorphicOn.divisor f univ) (w - 2)).toNat = (analyticOrderAt Λ w).toNat := by
    intro w
    have hg_an : AnalyticAt ℂ (fun z : ℂ => z + 2) (w - 2) := by fun_prop
    have hg_d : deriv (fun z : ℂ => z + 2) (w - 2) ≠ 0 := by
      rw [((hasDerivAt_id' (w - 2)).add_const 2).deriv]; exact one_ne_zero
    have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := Λ) hg_an hg_d
    have hfeq : Λ ∘ (fun z : ℂ => z + 2) = f := rfl
    rw [hfeq, sub_add_cancel] at hcomp
    rw [divisor_univ_eq_analyticOrder hf, hcomp]
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hHC.orderAt_ne_top w)
    rw [← hn]; simp
  obtain ⟨allCopiesAt, hall_pt, hall_card, hall_disj⟩ :
      ∃ allCopiesAt : ℂ → Finset (ZeroCopy f),
        (∀ w : ℂ, ∀ q ∈ allCopiesAt w, zeroCopyPoint f q + 2 = w) ∧
        (∀ w : ℂ, (allCopiesAt w).card = (analyticOrderAt Λ w).toNat) ∧
        (∀ w₁ w₂ : ℂ, w₁ ≠ w₂ → Disjoint (allCopiesAt w₁) (allCopiesAt w₂)) := by
    let cAt : ℂ → Finset (ZeroCopy f) := fun w =>
      if hw : w - 2 ∈ (MeromorphicOn.divisor f univ).support then
        Finset.univ.map ⟨fun j : Fin ((MeromorphicOn.divisor f univ) (w - 2)).toNat =>
          ⟨⟨w - 2, hw⟩, j⟩, fun j₁ j₂ heq => by
            simp only [Sigma.mk.injEq, heq_eq_eq] at heq; exact heq.2⟩
      else ∅
    have hc_pt : ∀ w : ℂ, ∀ q ∈ cAt w, zeroCopyPoint f q + 2 = w := by
      intro w q hq
      dsimp only [cAt] at hq
      split_ifs at hq with hw
      · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hq
        change (w - 2) + 2 = w; ring
      · exact absurd hq (Finset.notMem_empty _)
    have hc_card : ∀ w : ℂ, (cAt w).card = (analyticOrderAt Λ w).toNat := by
      intro w
      dsimp only [cAt]
      split_ifs with hw
      · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hdiv_toNat]
      · symm; rw [← hdiv_toNat]
        by_contra hne
        have hpos : 0 < ((MeromorphicOn.divisor f univ) (w - 2)).toNat := Nat.pos_of_ne_zero hne
        apply hw; rw [Function.mem_support]; intro hz0; rw [hz0] at hpos; simp at hpos
    have hc_disj : ∀ w₁ w₂ : ℂ, w₁ ≠ w₂ → Disjoint (cAt w₁) (cAt w₂) := by
      intro w₁ w₂ hne; rw [Finset.disjoint_left]; intro q h1 h2
      exact hne ((hc_pt w₁ q h1).symm.trans (hc_pt w₂ q h2))
    exact ⟨cAt, hc_pt, hc_card, hc_disj⟩
  obtain ⟨S_tot, htot_bound⟩ :
      ∃ S_tot : Finset (ZeroCopy f),
        (2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ) +
          (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) ≤
            ∑ q ∈ S_tot, term q := by
    let pairCopies : ℝ → Finset (ZeroCopy f) := fun x =>
      allCopiesAt (x : ℂ) ∪ allCopiesAt (1 - (x : ℂ))
    have hhalf_disj_pair : ∀ x ∈ X, Disjoint (allCopiesAt (1 / 2 : ℂ)) (pairCopies x) := by
      intro x hx
      obtain ⟨hx_gt, _⟩ := hX x hx
      rw [Finset.disjoint_union_right]
      refine ⟨hall_disj _ _ (fun h => ?_), hall_disj _ _ (fun h => ?_)⟩
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    have hpair_disj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint (pairCopies x) (pairCopies y) := by
      intro x hx y hy hxy
      obtain ⟨hx_gt, _⟩ := hX x hx
      obtain ⟨hy_gt, _⟩ := hX y hy
      simp only [pairCopies, Finset.disjoint_union_left, Finset.disjoint_union_right]
      refine ⟨⟨hall_disj _ _ (fun h => hxy (Complex.ofReal_inj.mp h)), hall_disj _ _ (fun h => ?_)⟩,
              ⟨hall_disj _ _ (fun h => ?_), hall_disj _ _ (fun h => ?_)⟩⟩
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
      · apply hxy; have := congrArg Complex.re h; simp at this; linarith
    have hsum_half : ((2 / 3 : ℝ) * ((analyticOrderAt Λ (1 / 2 : ℂ)).toNat : ℝ)) ≤
        ∑ q ∈ allCopiesAt (1 / 2 : ℂ), term q := by
      have hpt_val : ∀ q ∈ allCopiesAt (1 / 2 : ℂ), term q = 2 / 3 := by
        intro q hq
        rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl,
            hall_pt _ q hq]
        unfold gPair; norm_num
      rw [Finset.sum_congr rfl hpt_val, Finset.sum_const, hall_card, nsmul_eq_mul, mul_comm]
    have hsum_pair : ∀ x ∈ X,
        (4 / 3 : ℝ) * ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ) ≤ ∑ q ∈ pairCopies x, term q := by
      intro x hx
      obtain ⟨hx_gt, _⟩ := hX x hx
      have hne_x : (x : ℂ) ≠ 1 - (x : ℂ) := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      dsimp only [pairCopies]
      rw [Finset.sum_union (hall_disj _ _ hne_x)]
      have hval1 : ∀ q ∈ allCopiesAt (x : ℂ),
          term q = (1 / (2 - x) + 1 / (1 + x)) / 2 := by
        intro q hq
        rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl,
            hall_pt _ q hq]
        unfold gPair
        have e1 : (2 : ℂ) - (x : ℂ) = (((2 - x : ℝ) : ℂ)) := by push_cast; ring
        have e2 : (2 : ℂ) - (1 - (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by push_cast; ring
        have ec : (1 / 2 : ℂ) * (1 / (((2 - x : ℝ) : ℂ)) + 1 / (((1 + x : ℝ) : ℂ))) =
            ((((1 / (2 - x) + 1 / (1 + x)) / 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [e1, e2, ec, Complex.ofReal_re]
      have hval2 : ∀ q ∈ allCopiesAt (1 - (x : ℂ)),
          term q = (1 / (2 - x) + 1 / (1 + x)) / 2 := by
        intro q hq
        rw [show term q = ((1 / 2 : ℂ) * gPair (zeroCopyPoint f q + 2) 2).re from rfl,
            hall_pt _ q hq]
        unfold gPair; rw [sub_sub_cancel]
        have e1 : (2 : ℂ) - (1 - (x : ℂ)) = (((1 + x : ℝ) : ℂ)) := by push_cast; ring
        have e2 : (2 : ℂ) - (x : ℂ) = (((2 - x : ℝ) : ℂ)) := by push_cast; ring
        have ec : (1 / 2 : ℂ) * (1 / (((1 + x : ℝ) : ℂ)) + 1 / (((2 - x : ℝ) : ℂ))) =
            ((((1 / (2 - x) + 1 / (1 + x)) / 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [e1, e2, ec, Complex.ofReal_re]
      rw [Finset.sum_congr rfl hval1, Finset.sum_congr rfl hval2,
          Finset.sum_const, Finset.sum_const, hall_card, hall_card,
          hHC.orderAt_one_sub (x : ℂ), nsmul_eq_mul]
      have hge43 : (4 / 3 : ℝ) ≤ 1 / (2 - x) + 1 / (1 + x) := by
        have hp1 : 0 < 2 - x := by linarith
        have hp2 : 0 < 1 + x := by linarith
        rw [div_add_div _ _ hp1.ne' hp2.ne', div_le_div_iff₀ (by norm_num) (mul_pos hp1 hp2)]
        nlinarith [sq_nonneg (x - 1 / 2)]
      have hord_nn : (0 : ℝ) ≤ ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ) := Nat.cast_nonneg _
      nlinarith
    refine ⟨allCopiesAt (1 / 2 : ℂ) ∪ X.biUnion pairCopies, ?_⟩
    have hdisj_tot : Disjoint (allCopiesAt (1 / 2 : ℂ)) (X.biUnion pairCopies) := by
      rw [Finset.disjoint_biUnion_right]; exact hhalf_disj_pair
    rw [Finset.sum_union hdisj_tot,
        Finset.sum_biUnion (fun x hx y hy hxy => hpair_disj x hx y hy hxy)]
    have hX_sum_le : (4 / 3 : ℝ) * (∑ x ∈ X, ((analyticOrderAt Λ (x : ℂ)).toNat : ℝ)) ≤
        ∑ x ∈ X, ∑ q ∈ pairCopies x, term q := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun x hx => hsum_pair x hx
    linarith [hsum_half, hX_sum_le]
  have htot_le : ∑ q ∈ S_tot, term q ≤ (logDeriv Λ 2).re :=
    sum_le_hasSum S_tot (fun q _ => hterm_nn q) hsum_re
  linarith [htot_bound, htot_le, hΛ2_lt]

private theorem contractCollidedQuartet_iter :
    ∀ (k : ℕ) {κ₀ κγ d : ℕ} {γ a : ℝ} {F Λ : ℂ → ℂ},
      HeightCoupledSystem κ₀ κγ d γ F Λ →
      0 < a → a < 1 / 2 → γ ≠ 0 →
      2 * k ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat →
      k ≤ (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat →
      ∃ Fc Λc : ℂ → ℂ,
        HeightCoupledSystem κ₀ κγ d γ Fc Λc ∧
        (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 4 * k ∧
        (analyticOrderAt Λc (1 / 2 + (γ : ℂ) * I)).toNat =
          (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat + 2 * k ∧
        (analyticOrderAt Λc ((1 / 2 + a : ℝ) : ℂ)).toNat + 2 * k =
          (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat ∧
        (analyticOrderAt Λc (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat + k =
          (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
        (∀ z : ℂ, z.re ≠ 1 / 2 → z.re ≠ 1 / 2 + a → z.re ≠ 1 / 2 - a →
          (analyticOrderAt Λc z).toNat = (analyticOrderAt Λ z).toNat)
  | 0, _, _, _, _, _, F, Λ, hHC, _, _, _, _, _ =>
      ⟨F, Λ, hHC, by omega, by omega, by omega, by omega, fun _ _ _ _ => rfl⟩
  | k + 1, _, _, _, γ, a, F, Λ, hHC, ha0, ha1, hγ, hreal, hquart => by
      have hreal2 : 2 ≤ (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat := by omega
      have hq0 : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 :=
        hHC.eq_zero_of_one_le_order_toNat (by omega)
      obtain ⟨Λ₁, hHC₁, _, h1, h2, h3, h4, h5⟩ :=
        hHC.contractCollidedQuartet ha0 ha1 hγ hreal2 hq0
      obtain ⟨Fc, Λc, hHCc, hc1, hc2, hc3, hc4, hc5⟩ :=
        contractCollidedQuartet_iter k hHC₁ ha0 ha1 hγ (by omega) (by omega)
      refine ⟨Fc, Λc, hHCc, by omega, by omega, by omega, by omega, fun z hz0 hza1 hza2 => ?_⟩
      rw [hc5 z hz0 hza1 hza2, h5 z hz0 hza1 hza2]

/-- **Simultaneous zero-tax contraction of all quartets along ordinate `γ`.** For any finite set
`A ⊂ (0, 1/2)` of off-critical depths, lifting `hS : CompletedPositiveSystem κ d F Λ` to
`HeightCoupledSystem (2 * κ) κ d γ` and iterating `contractCollidedQuartet` contracts all
`∑_{a ∈ A} ord_{1/2 + a + iγ}(Λ)` complex quartets onto `{1/2, 1/2 ± iγ}` at `Δκ₀ = 0, Δκγ = 0`,
jumping `ord_{1/2}` by `4 ∑_{a ∈ A} ord_{1/2 + a + iγ}(Λ)` and annihilating all collided real
anchor zeros (`ord_{1/2 + a}(Λc) = 2 ord_{1/2 + a}(Λ)` for `a ∈ A`). -/
theorem CompletedPositiveSystem.contractOrdinateQuartets_heightCoupled {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {γ : ℝ} (hγ : γ ≠ 0)
    (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a ∧ a < 1 / 2) :
    ∃ Fc Λc : ℂ → ℂ,
      HeightCoupledSystem (2 * κ) κ d γ Fc Λc ∧
      (analyticOrderAt Λc (1 / 2)).toNat =
        2 * (analyticOrderAt Λ (1 / 2)).toNat +
        2 * (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat +
        4 * ∑ a ∈ A, (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
      (∀ a ∈ A, (analyticOrderAt Λc ((1 / 2 + a : ℝ) : ℂ)).toNat =
        2 * (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat) := by
  classical
  suffices haux : ∀ B : Finset ℝ, B ⊆ A →
      ∃ Fc Λc : ℂ → ℂ,
        HeightCoupledSystem (2 * κ) κ d γ Fc Λc ∧
        (analyticOrderAt Λc (1 / 2)).toNat =
          2 * (analyticOrderAt Λ (1 / 2)).toNat +
          2 * (analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat +
          4 * ∑ a ∈ B, (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat ∧
        (∀ a ∈ B, (analyticOrderAt Λc ((1 / 2 + a : ℝ) : ℂ)).toNat =
          2 * (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat) ∧
        (∀ z : ℂ, z.re ≠ 1 / 2 → (∀ b ∈ B, z.re ≠ 1 / 2 + b ∧ z.re ≠ 1 / 2 - b) →
          (analyticOrderAt Λc z).toNat = (analyticOrderAt (heightCoupledΛ Λ γ) z).toNat) by
    obtain ⟨Fc, Λc, hHCc, hhalf, hreal, _⟩ := haux A Finset.Subset.rfl
    exact ⟨Fc, Λc, hHCc, hhalf, hreal⟩
  intro B
  induction B using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨heightCoupledF F γ, heightCoupledΛ Λ γ, CompletedPositiveSystem.heightCouple hS γ, ?_,
        fun _ h => absurd h (Finset.notMem_empty _), fun _ _ _ => rfl⟩
      have hhalf_eq : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      have h0 := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hS γ (1 / 2)
      rw [← hhalf_eq] at h0
      rw [Finset.sum_empty, mul_zero, add_zero]
      exact h0
  | @insert a B ha_not ih =>
      intro hB_sub
      obtain ⟨ha0, ha1⟩ := hA a (hB_sub (Finset.mem_insert_self a B))
      obtain ⟨F₁, Λ₁, hHC₁, hhalf₁, hreal₁, hout₁⟩ :=
        ih (Finset.Subset.trans (Finset.subset_insert a B) hB_sub)
      have ha_sep : ∀ b ∈ B, (1 / 2 + a : ℝ) ≠ 1 / 2 + b ∧ (1 / 2 + a : ℝ) ≠ 1 / 2 - b := by
        intro b hb
        have hb0 : 0 < b := (hA b (hB_sub (Finset.mem_insert_of_mem hb))).1
        have hab : a ≠ b := fun heq => ha_not (heq ▸ hb)
        exact ⟨fun h => hab (by linarith), fun h => by linarith⟩
      have hcast_a : (((1 / 2 + a : ℝ) : ℂ)) + (γ : ℂ) * I = 1 / 2 + (a : ℂ) + (γ : ℂ) * I := by
        push_cast; ring
      have hord_F₁_real : (analyticOrderAt Λ₁ ((1 / 2 + a : ℝ) : ℂ)).toNat =
          2 * (analyticOrderAt Λ ((1 / 2 + a : ℝ) : ℂ)).toNat +
          2 * (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
        rw [hout₁ ((1 / 2 + a : ℝ) : ℂ) (by simp; linarith) (fun b hb => by simpa using ha_sep b hb),
            CompletedPositiveSystem.orderAt_heightCoupledΛ_real hS γ (1 / 2 + a), hcast_a]
      have hord_F₁_quart : (analyticOrderAt Λ₁ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat =
          (analyticOrderAt (heightCoupledΛ Λ γ) (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
        refine hout₁ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) (by simp; linarith) fun b hb => ?_
        have hre : (1 / 2 + (a : ℂ) + (γ : ℂ) * I).re = 1 / 2 + a := by simp
        rw [hre]; exact ha_sep b hb
      set k : ℕ := (analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat
      have hk_quart : k ≤ (analyticOrderAt Λ₁ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat := by
        rw [hord_F₁_quart,
            CompletedPositiveSystem.orderAt_heightCoupledΛ hS γ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)]
        dsimp [k]; omega
      obtain ⟨Fc, Λc, hHCc, hc_half, _, hc_real, _, hc_out⟩ :=
        contractCollidedQuartet_iter k hHC₁ ha0 ha1 hγ (by omega) hk_quart
      refine ⟨Fc, Λc, hHCc, ?_, ?_, ?_⟩
      · rw [Finset.sum_insert ha_not, hc_half, hhalf₁]
        dsimp [k]; omega
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxB
        · omega
        · have hx0 : 0 < x := (hA x (hB_sub (Finset.mem_insert_of_mem hxB))).1
          have hxa : x ≠ a := fun heq => ha_not (heq ▸ hxB)
          rw [hc_out ((1 / 2 + x : ℝ) : ℂ) (by simp; linarith)
                (by simp; intro h; exact hxa (by linarith)) (by simp; linarith),
              hreal₁ x hxB]
      · intro z hz0 hz_ins
        have hz_a := hz_ins a (Finset.mem_insert_self a B)
        have hz_B : ∀ b ∈ B, z.re ≠ 1 / 2 + b ∧ z.re ≠ 1 / 2 - b :=
          fun b hb => hz_ins b (Finset.mem_insert_of_mem hb)
        rw [hc_out z hz0 hz_a.1 hz_a.2, hout₁ z hz0 hz_B]

/-- **Unconditional zero-tax ordinate-`γ` quartet multiplicity bound.** Contracting arbitrarily many
ordinate-`γ` quartets at `Δκ₀ = 0, Δκγ = 0` inside `HeightCoupledSystem (2 * κ) κ d γ` bounds their
total multiplicity against the fixed archimedean budget:
`8 ∑_{a ∈ A} ord_{1/2 + a + iγ}(Λ) + 4 ord_{1/2}(Λ) + 4 ord_{1/2 + iγ}(Λ) < 18 κ + 3 d log(3 + |γ|) − (7/2) d`. -/
theorem CompletedPositiveSystem.ordinateQuartet_multiplicity_archimedean_bound
    {κ d : ℕ} {F Λ : ℂ → ℂ} (hS : CompletedPositiveSystem κ d F Λ) {γ : ℝ} (hγ : γ ≠ 0)
    (A : Finset ℝ) (hA : ∀ a ∈ A, 0 < a ∧ a < 1 / 2) :
    8 * (∑ a ∈ A, ((analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat : ℝ)) +
      4 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
      4 * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) <
    18 * (κ : ℝ) + 3 * (d : ℝ) * Real.log (3 + |γ|) - (7 / 2 : ℝ) * (d : ℝ) := by
  obtain ⟨Fc, Λc, hHCc, hhalf, _⟩ :=
    CompletedPositiveSystem.contractOrdinateQuartets_heightCoupled hS hγ A hA
  have hbud := hHCc.archimedean_budget ∅ (fun _ hx => absurd hx (Finset.notMem_empty _))
  simp only [Finset.sum_empty, mul_zero, add_zero, Nat.cast_mul, Nat.cast_ofNat] at hbud
  have hcast : ((analyticOrderAt Λc (1 / 2)).toNat : ℝ) =
      2 * ((analyticOrderAt Λ (1 / 2)).toNat : ℝ) +
      2 * ((analyticOrderAt Λ (1 / 2 + (γ : ℂ) * I)).toNat : ℝ) +
      4 * (∑ a ∈ A, ((analyticOrderAt Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I)).toNat : ℝ)) := by
    rw [hhalf]; push_cast; ring
  rw [hcast] at hbud
  linarith

/-- **Finite-step zero-tax elimination of all real off-critical zeros in `HeightCoupledSystem`.**
Because each `contractRealPair` step jumps `ord_{1/2}` by `+2` at `Δκ₀ = 0, Δκγ = 0` while the
archimedean ceiling remains fixed, repeated contraction terminates in finitely many steps. -/
theorem HeightCoupledSystem.exists_real_offCritical_free {κ₀ κγ d : ℕ} {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem κ₀ κγ d γ F Λ) :
    ∃ Fc Λc : ℂ → ℂ,
      HeightCoupledSystem κ₀ κγ d γ Fc Λc ∧
      ∀ β : ℝ, β ≠ 1 / 2 → Λc (β : ℂ) ≠ 0 := by
  let B : ℕ :=
    Nat.ceil ((9 / 4 : ℝ) * (κ₀ : ℝ) + (9 / 2 : ℝ) * (κγ : ℝ) +
      (3 / 2 : ℝ) * (d : ℝ) * Real.log (3 + |γ|)) + 1
  have hord_lt_B : ∀ {F' Λ' : ℂ → ℂ}, HeightCoupledSystem κ₀ κγ d γ F' Λ' →
      (analyticOrderAt Λ' (1 / 2)).toNat < B := by
    intro F' Λ' hHC'
    have hbud := hHC'.archimedean_budget ∅ (fun _ hx => absurd hx (Finset.notMem_empty _))
    simp only [Finset.sum_empty, mul_zero, add_zero] at hbud
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast hHC'.degree_pos
    have hlt_real : ((analyticOrderAt Λ' (1 / 2)).toNat : ℝ) <
        (9 / 4 : ℝ) * (κ₀ : ℝ) + (9 / 2 : ℝ) * (κγ : ℝ) +
          (3 / 2 : ℝ) * (d : ℝ) * Real.log (3 + |γ|) := by
      linarith
    have hceil := Nat.le_ceil
      ((9 / 4 : ℝ) * (κ₀ : ℝ) + (9 / 2 : ℝ) * (κγ : ℝ) +
        (3 / 2 : ℝ) * (d : ℝ) * Real.log (3 + |γ|))
    have hlt_B : ((analyticOrderAt Λ' (1 / 2)).toNat : ℝ) < (B : ℝ) := by
      dsimp [B]; push_cast; linarith
    exact_mod_cast hlt_B
  suffices haux : ∀ (N : ℕ) {F' Λ' : ℂ → ℂ}, HeightCoupledSystem κ₀ κγ d γ F' Λ' →
      B - (analyticOrderAt Λ' (1 / 2)).toNat ≤ N →
      ∃ Fc Λc : ℂ → ℂ,
        HeightCoupledSystem κ₀ κγ d γ Fc Λc ∧ ∀ β : ℝ, β ≠ 1 / 2 → Λc (β : ℂ) ≠ 0 from
    haux (B - (analyticOrderAt Λ (1 / 2)).toNat) hHC le_rfl
  intro N
  induction N with
  | zero =>
      intro F' Λ' hHC' hN
      have hlt := hord_lt_B hHC'
      omega
  | succ N ih =>
      intro F' Λ' hHC' hN
      by_cases hfree : ∀ β : ℝ, β ≠ 1 / 2 → Λ' (β : ℂ) ≠ 0
      · exact ⟨F', Λ', hHC', hfree⟩
      · push Not at hfree
        obtain ⟨β, hβ, hzero⟩ := hfree
        obtain ⟨Λ₁, hHC₁, _, hord₁⟩ := hHC'.contractRealPair hβ hzero
        exact ih hHC₁ (by omega)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
