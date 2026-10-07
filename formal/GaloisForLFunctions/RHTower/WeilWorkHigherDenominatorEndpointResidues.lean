import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorLogPolynomialDefect
import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Exact endpoint residues of the actual quotient

The local numerator E/(2 xi s²) and its reflected germ give the two
logarithmic endpoint terms. Arbitrary interior pole orders are untouched.
-/

noncomputable section

open Complex Set Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

private lemma doublePole_shift (B : ℂ → ℂ) (p : ℂ) :
    laurentShift (fun s => B s / (s - p) ^ 2) p 3 = fun t => t ^ 1 * B (p + t) := by
  funext t
  simp only [laurentShift, add_sub_cancel_left]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · field_simp

private lemma doublePole_shift_analytic {B : ℂ → ℂ} {p : ℂ} (hB : AnalyticAt ℂ B p) :
    AnalyticAt ℂ (laurentShift (fun s => B s / (s - p) ^ 2) p 3) 0 := by
  rw [doublePole_shift]
  exact (analyticAt_id.pow 1).mul (analyticAt_comp_const_add hB)

/-- The double-pole polynomial retains both its residue and its leading coefficient. -/
theorem residueLogPolynomial_doublePole {B : ℂ → ℂ} {p : ℂ} (hB : AnalyticAt ℂ B p) :
    residueLogPolynomial (fun s => B s / (s - p) ^ 2) p 3 =
      C (deriv B p) - C (B p) * X := by
  have hk := doublePole_shift_analytic hB
  have hcoeff : ∀ ℓ : ℤ, -3 ≤ ℓ →
      laurentCoeff (fun s => B s / (s - p) ^ 2) p ℓ =
        taylorCoeffZero (fun t : ℂ => t ^ 1 * B (p + t)) (ℓ + 3).toNat := by
    intro ℓ hℓ
    rw [laurentCoeff_eq_taylorCoeffZero hk (by omega), doublePole_shift]
    norm_num
  have h₁ : laurentCoeff (fun s => B s / (s - p) ^ 2) p (-1) = deriv B p := by
    rw [hcoeff (-1) (by norm_num), taylorCoeffZero_pow_mul (analyticAt_comp_const_add hB)]
    simp [taylorCoeffZero, iteratedDeriv_one, deriv_comp_const_add]
  have h₂ : laurentCoeff (fun s => B s / (s - p) ^ 2) p (-2) = B p := by
    rw [hcoeff (-2) (by norm_num), taylorCoeffZero_pow_mul (analyticAt_comp_const_add hB)]
    simp [taylorCoeffZero]
  have h₃ : laurentCoeff (fun s => B s / (s - p) ^ 2) p (-3) = 0 := by
    rw [hcoeff (-3) (by norm_num), taylorCoeffZero_pow_mul (analyticAt_comp_const_add hB)]
    norm_num
  simp [residueLogPolynomial, Finset.sum_range_succ, h₁, h₂, h₃,
    Polynomial.C_mul_X_eq_monomial]
  ring

/-- Exact weighted residue at a pole of order at most two. -/
theorem laurentCoeff_mellin_doublePole {B : ℂ → ℂ} {p : ℂ} (hB : AnalyticAt ℂ B p)
    {x : ℝ} (hx : 0 < x) :
    laurentCoeff (fun s => (x : ℂ) ^ (-s) * (B s / (s - p) ^ 2)) p (-1) =
      (x : ℂ) ^ (-p) * (deriv B p - B p * (Real.log x : ℂ)) := by
  rw [laurentCoeff_mellin_weight_eq_polynomial (doublePole_shift_analytic hB) (by norm_num) hx,
    residueLogPolynomial_doublePole hB]
  simp

/-- The analytic numerator of the endpoint at one. -/
def degreeTwoEndpointNumerator (E : ℂ → ℂ) (s : ℂ) : ℂ :=
  E s / (2 * xi s * s ^ 2)

theorem degreeTwoEndpointNumerator_analyticAt_one {E : ℂ → ℂ} (hE : Differentiable ℂ E) :
    AnalyticAt ℂ (degreeTwoEndpointNumerator E) 1 := by
  have hξ : AnalyticAt ℂ xi 1 := xi_analyticOnNhd_univ 1 (mem_univ _)
  exact (hE.differentiableOn.analyticAt Filter.univ_mem).div
    ((analyticAt_const.mul hξ).mul (analyticAt_id.pow 2)) (by norm_num [xi_one])

/-- The meromorphic representative agrees with E/(2 xi s²(s−1)²) near a nonzero xi value. -/
theorem poleClearedDegreeTwoCompletion_germ {E H : ℂ → ℂ} (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {p : ℂ} (hξ : xi p ≠ 0) :
    poleClearedDegreeTwoCompletion P H =ᶠ[𝓝 p]
      (fun s => E s / (2 * xi s * s ^ 2 * (s - 1) ^ 2)) := by
  have hP : P.eval p ≠ 0 := fun hp => hξ (deficitPolynomial_root_xi_zero P hord hp)
  have hPe := P.continuous.continuousAt.eventually_ne hP
  have hξe := (xi_analyticOnNhd_univ p (mem_univ _)).continuousAt.eventually_ne hξ
  filter_upwards [hPe, hξe] with s hsP hsξ
  have hr : H s / P.eval s = E s / xi s := by
    apply (div_eq_div_iff hsP hsξ).mpr
    simpa only [mul_comm] using (hfac s).symm
  calc
    poleClearedDegreeTwoCompletion P H s =
        (H s / P.eval s) / (2 * s ^ 2 * (s - 1) ^ 2) := by
      simp only [poleClearedDegreeTwoCompletion, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = E s / (2 * xi s * s ^ 2 * (s - 1) ^ 2) := by
      rw [hr]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private lemma mellin_weight_meromorphic {x : ℝ} (hx : 0 < x) (p : ℂ) :
    MeromorphicAt (fun s : ℂ => (x : ℂ) ^ (-s)) p := by
  have hd : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ (-s)) :=
    (by fun_prop : Differentiable ℂ (fun s : ℂ => -s)).const_cpow
      (Or.inl (by exact_mod_cast hx.ne'))
  exact (hd.differentiableOn.analyticAt Filter.univ_mem).meromorphicAt

/-- Actual endpoint-one residue, including the logarithmic term. -/
theorem poleClearedDegreeTwoCompletion_residue_one {E H : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hH : Differentiable ℂ H) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {x : ℝ} (hx : 0 < x) :
    laurentCoeff (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) 1 (-1) =
      (x : ℂ) ^ (-1 : ℂ) * (deriv (degreeTwoEndpointNumerator E) 1 -
        degreeTwoEndpointNumerator E 1 * (Real.log x : ℂ)) := by
  have hg := poleClearedDegreeTwoCompletion_germ P hfac hord (p := 1) (by norm_num [xi_one])
  have heq : (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) =ᶠ[𝓝 1]
      (fun s => (x : ℂ) ^ (-s) * (degreeTwoEndpointNumerator E s / (s - 1) ^ 2)) := by
    filter_upwards [hg] with s hs
    rw [hs, degreeTwoEndpointNumerator, div_div]
  have hm : MeromorphicAt (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) 1 :=
    (mellin_weight_meromorphic hx 1).mul (poleClearedDegreeTwoCompletion_meromorphicAt P hH 1)
  rw [laurentCoeff_congr hm (heq.filter_mono nhdsWithin_le_nhds) (-1)]
  exact laurentCoeff_mellin_doublePole (degreeTwoEndpointNumerator_analyticAt_one hE) hx

/-- Actual endpoint-zero residue, forced by the original functional equation. -/
theorem poleClearedDegreeTwoCompletion_residue_zero {E H : ℂ → ℂ} {ε : ℂ}
    (hE : Differentiable ℂ E) (hH : Differentiable ℂ H)
    (hfe : ∀ s, E (1 - s) = ε * E s) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {x : ℝ} (hx : 0 < x) :
    laurentCoeff (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) 0 (-1) =
      -ε * (deriv (degreeTwoEndpointNumerator E) 1 +
        degreeTwoEndpointNumerator E 1 * (Real.log x : ℂ)) := by
  let B : ℂ → ℂ := fun s => ε * degreeTwoEndpointNumerator E (1 - s)
  have hB : AnalyticAt ℂ B 0 := by
    have hA := degreeTwoEndpointNumerator_analyticAt_one hE
    exact analyticAt_const.mul (AnalyticAt.comp (g := degreeTwoEndpointNumerator E)
      (f := fun s : ℂ => 1 - s) (x := 0) (by simpa using hA) (by fun_prop))
  have hg := poleClearedDegreeTwoCompletion_germ P hfac hord (p := 0) (by norm_num [xi_zero])
  have heq : (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) =ᶠ[𝓝 0]
      (fun s => (x : ℂ) ^ (-s) * (B s / (s - 0) ^ 2)) := by
    filter_upwards [hg] with s hs
    rw [hs]
    congr 1
    have hE' : E s = ε * E (1 - s) := by simpa using hfe (1 - s)
    simp only [B, degreeTwoEndpointNumerator, xi_one_sub, sub_zero]
    rw [hE', show (1 - s) ^ 2 = (s - 1) ^ 2 by ring]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hm : MeromorphicAt (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) 0 :=
    (mellin_weight_meromorphic hx 0).mul (poleClearedDegreeTwoCompletion_meromorphicAt P hH 0)
  rw [laurentCoeff_congr hm (heq.filter_mono nhdsWithin_le_nhds) (-1),
    laurentCoeff_mellin_doublePole hB hx]
  simp only [B, deriv_const_mul_field, deriv_comp_const_sub, sub_zero, neg_zero, cpow_zero, one_mul]
  ring

end RHTower.WeilHigherDenominator
