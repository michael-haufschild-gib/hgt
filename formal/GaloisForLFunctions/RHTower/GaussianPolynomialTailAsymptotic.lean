import GaloisForLFunctions.RHTower.GaussianMonomialTailAsymptotic
import GaloisForLFunctions.HTGeometry.HermitePolynomialSpan
import Mathlib.Analysis.Polynomial.Basic

/-!
# Sharp polynomial--Gaussian and Hermite tail asymptotics

The moving-tail L'Hôpital argument extends from monomials to every nonzero real polynomial of
degree at least two.  Only the leading coefficient survives after division by
`a^(degree-1) exp (-b a^2)`.  Applying this to products of the self-dual Hermite polynomials gives
the exact scalar leading constants needed for Hermite leakage Gram matrices.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped Real BigOperators

noncomputable section

namespace RHTower

/-- A polynomial times a positive-rate Gaussian is integrable on the positive ray. -/
theorem integrableOn_polyEval_mul_exp_neg_mul_sq_Ioi_zero
    (q : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => q.eval x * Real.exp (-(b * x ^ 2))) (Ioi 0) := by
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ i ∈ q.support,
        q.coeff i * (x ^ i * Real.exp (-(b * x ^ 2)))) (Ioi 0) := by
    exact integrable_finsetSum q.support fun i _ =>
      (integrableOn_pow_mul_exp_neg_mul_sq_Ioi_zero i hb).const_mul (q.coeff i)
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Differentiating a moving polynomial--Gaussian tail gives minus its boundary density. -/
theorem hasDerivAt_polynomialGaussianTail
    (q : ℝ[X]) {b : ℝ} (hb : 0 < b) {a : ℝ} (ha : 0 < a) :
    HasDerivAt
      (fun t : ℝ => ∫ x in Ioi t, q.eval x * Real.exp (-(b * x ^ 2)))
      (-(q.eval a * Real.exp (-(b * a ^ 2)))) a := by
  let f : ℝ → ℝ := fun x => q.eval x * Real.exp (-(b * x ^ 2))
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hfint : IntegrableOn f (Ioi 0) :=
    integrableOn_polyEval_mul_exp_neg_mul_sq_Ioi_zero q hb
  have hinterval : IntervalIntegrable f volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
    exact hfint.mono_set Ioc_subset_Ioi_self
  have hprimitive : HasDerivAt (fun t : ℝ => ∫ x in 0..t, f x) (f a) a :=
    intervalIntegral.integral_hasDerivAt_right hinterval
      (hfcont.stronglyMeasurableAtFilter volume (nhds a)) hfcont.continuousAt
  have hmodel : HasDerivAt
      (fun t : ℝ => (∫ x in Ioi 0, f x) - ∫ x in 0..t, f x) (-f a) a :=
    hprimitive.const_sub (∫ x in Ioi 0, f x)
  have heq :
      (fun t : ℝ => ∫ x in Ioi t, f x) =ᶠ[nhds a]
        (fun t : ℝ => (∫ x in Ioi 0, f x) - ∫ x in 0..t, f x) := by
    filter_upwards [Ioi_mem_nhds ha] with t ht
    rw [← intervalIntegral.integral_Ioi_sub_Ioi hfint ht.le]
    ring
  simpa only [f] using hmodel.congr_of_eventuallyEq heq

/-- Sharp polynomial--Gaussian tail asymptotic in terms of degree and leading coefficient. -/
theorem tendsto_polynomialGaussianTail_div_leading
    (q : ℝ[X]) (hq : q ≠ 0) (hdeg : 2 ≤ q.natDegree) {b : ℝ} (hb : 0 < b) :
    Tendsto
      (fun a : ℝ =>
        (∫ x in Ioi a, q.eval x * Real.exp (-(b * x ^ 2))) /
          (a ^ (q.natDegree - 1) * Real.exp (-(b * a ^ 2))))
      atTop (nhds (q.leadingCoeff / (2 * b))) := by
  let d := q.natDegree
  let F : ℝ → ℝ := fun a => ∫ x in Ioi a, q.eval x * Real.exp (-(b * x ^ 2))
  let G : ℝ → ℝ := fun a => a ^ (d - 1) * Real.exp (-(b * a ^ 2))
  let F' : ℝ → ℝ := fun a => -(q.eval a * Real.exp (-(b * a ^ 2)))
  let G' : ℝ → ℝ := fun a =>
    ((d - 1 : ℕ) : ℝ) * a ^ (d - 2) * Real.exp (-(b * a ^ 2)) -
      2 * b * a ^ d * Real.exp (-(b * a ^ 2))
  have hd : 2 ≤ d := hdeg
  have hF' : ∀ᶠ a : ℝ in atTop, HasDerivAt F (F' a) a := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact hasDerivAt_polynomialGaussianTail q hb ha
  have hG' : ∀ᶠ a : ℝ in atTop, HasDerivAt G (G' a) a := by
    filter_upwards with a
    have hpow := hasDerivAt_pow (d - 1) a
    have hinner : HasDerivAt (fun x : ℝ => -(b * x ^ 2)) (-2 * b * a) a := by
      have hraw := ((hasDerivAt_pow 2 a).const_mul b).neg
      have hfun : -(fun x : ℝ => b * x ^ 2) = (fun x : ℝ => -(b * x ^ 2)) := by
        rfl
      rw [hfun] at hraw
      exact hraw.congr_deriv (by ring)
    have hexp := hinner.exp
    dsimp only [G, G']
    apply (hpow.mul hexp).congr_deriv
    have hpowa : a ^ (d - 1) = a ^ (d - 2) * a := by
      calc
        a ^ (d - 1) = a ^ ((d - 2) + 1) := by congr 1 <;> omega
        _ = a ^ (d - 2) * a := by rw [pow_succ]
    have hpowd : a ^ d = a ^ (d - 2) * a ^ 2 := by
      calc
        a ^ d = a ^ ((d - 2) + 2) := by congr 1 <;> omega
        _ = a ^ (d - 2) * a ^ 2 := by rw [pow_add]
    rw [show d - 1 - 1 = d - 2 by omega, hpowa, hpowd]
    ring
  have hG'ne : ∀ᶠ a : ℝ in atTop, G' a ≠ 0 := by
    have hquad : Tendsto (fun a : ℝ => 2 * b * a ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (Filter.tendsto_pow_atTop (by norm_num))
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hquad.eventually (eventually_gt_atTop (((d - 1 : ℕ) : ℝ)))] with a ha hlarge
    have hpowpos : 0 < a ^ (d - 2) := pow_pos ha _
    have hexppos : 0 < Real.exp (-(b * a ^ 2)) := Real.exp_pos _
    have hfactor : ((d - 1 : ℕ) : ℝ) - 2 * b * a ^ 2 < 0 := by linarith
    have hrewrite : G' a =
        a ^ (d - 2) * Real.exp (-(b * a ^ 2)) *
          (((d - 1 : ℕ) : ℝ) - 2 * b * a ^ 2) := by
      dsimp only [G']
      have hpowd : a ^ d = a ^ (d - 2) * a ^ 2 := by
        calc
          a ^ d = a ^ ((d - 2) + 2) := by congr 1 <;> omega
          _ = a ^ (d - 2) * a ^ 2 := by rw [pow_add]
      rw [hpowd]
      ring
    rw [hrewrite]
    exact mul_ne_zero (mul_ne_zero hpowpos.ne' hexppos.ne') hfactor.ne
  have hF0 : Tendsto F atTop (nhds 0) := by
    dsimp only [F]
    exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
  have hG0 : Tendsto G atTop (nhds 0) := by
    dsimp only [G]
    exact tendsto_pow_mul_exp_neg_mul_sq_atTop_nhds_zero (d - 1) hb
  have hpolyRaw := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    q (Polynomial.X ^ d) (by simp [d, Polynomial.degree_eq_natDegree hq])
  have hpoly : Tendsto (fun a : ℝ => q.eval a / a ^ d) atTop (nhds q.leadingCoeff) := by
    simpa using hpolyRaw
  have hsqInv : Tendsto (fun a : ℝ => (a ^ 2)⁻¹) atTop (nhds 0) :=
    (Filter.tendsto_pow_atTop (by norm_num)).inv_tendsto_atTop
  have hden : Tendsto
      (fun a : ℝ => (((d - 1 : ℕ) : ℝ) * (a ^ 2)⁻¹ - 2 * b))
      atTop (nhds (0 - 2 * b)) := by
    simpa using
      (hsqInv.const_mul (((d - 1 : ℕ) : ℝ))).sub (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => 2 * b) atTop (nhds (2 * b)))
  have hratioModel : Tendsto
      (fun a : ℝ => -(q.eval a / a ^ d) /
        (((d - 1 : ℕ) : ℝ) * (a ^ 2)⁻¹ - 2 * b))
      atTop (nhds (-q.leadingCoeff / (0 - 2 * b))) :=
    hpoly.neg.div hden (by linarith)
  have hlim : -q.leadingCoeff / (0 - 2 * b) = q.leadingCoeff / (2 * b) := by
    field_simp [hb.ne']
    ring
  rw [hlim] at hratioModel
  have hratio : Tendsto (fun a => F' a / G' a) atTop
      (nhds (q.leadingCoeff / (2 * b))) := by
    refine hratioModel.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with a ha
    dsimp only [F', G']
    have hpowd : a ^ d = a ^ (d - 2) * a ^ 2 := by
      calc
        a ^ d = a ^ ((d - 2) + 2) := by congr 1 <;> omega
        _ = a ^ (d - 2) * a ^ 2 := by rw [pow_add]
    rw [hpowd]
    field_simp [ha, Real.exp_ne_zero]
  simpa only [d, F, G] using
    HasDerivAt.lhopital_zero_atTop hF' hG' hG'ne hF0 hG0 hratio

/-- One-sided tail constant for a product of two self-dual Hermite polynomials. -/
theorem tendsto_hermitePolyProductTail_div_leading
    (m n : ℕ) (hdeg : 2 ≤ m + n) :
    Tendsto
      (fun a : ℝ =>
        (∫ x in Ioi a,
          (GaloisForLFunctions.hermitePoly m).eval x *
            (GaloisForLFunctions.hermitePoly n).eval x *
            Real.exp (-(2 * Real.pi * x ^ 2))) /
          (a ^ (m + n - 1) * Real.exp (-(2 * Real.pi * a ^ 2))))
      atTop (nhds (2 ^ (m + n) / (4 * Real.pi))) := by
  let q : ℝ[X] := GaloisForLFunctions.hermitePoly m *
    GaloisForLFunctions.hermitePoly n
  have hm0 : GaloisForLFunctions.hermitePoly m ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp
      (by rw [GaloisForLFunctions.hermitePoly_leadingCoeff]; positivity)
  have hn0 : GaloisForLFunctions.hermitePoly n ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mp
      (by rw [GaloisForLFunctions.hermitePoly_leadingCoeff]; positivity)
  have hq0 : q ≠ 0 := mul_ne_zero hm0 hn0
  have hqdeg : q.natDegree = m + n := by
    dsimp only [q]
    rw [Polynomial.natDegree_mul hm0 hn0,
      Polynomial.natDegree_eq_of_degree_eq_some
        (GaloisForLFunctions.hermitePoly_degree m),
      Polynomial.natDegree_eq_of_degree_eq_some
        (GaloisForLFunctions.hermitePoly_degree n)]
  have hqlead : q.leadingCoeff = 2 ^ (m + n) := by
    dsimp only [q]
    rw [Polynomial.leadingCoeff_mul,
      GaloisForLFunctions.hermitePoly_leadingCoeff,
      GaloisForLFunctions.hermitePoly_leadingCoeff, pow_add]
  have h := tendsto_polynomialGaussianTail_div_leading q hq0
    (by simpa [hqdeg] using hdeg) (b := 2 * Real.pi) (by positivity)
  convert h using 1 <;>
    simp only [q, Polynomial.eval_mul, hqdeg, hqlead, mul_assoc] <;> ring

/-- One-sided squared-tail constant for every positive Hermite index. -/
theorem tendsto_hermitePolySqTail_div_leading (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun a : ℝ =>
        (∫ x in Ioi a,
          (GaloisForLFunctions.hermitePoly n).eval x ^ 2 *
            Real.exp (-(2 * Real.pi * x ^ 2))) /
          (a ^ (2 * n - 1) * Real.exp (-(2 * Real.pi * a ^ 2))))
      atTop (nhds (2 ^ (2 * n) / (4 * Real.pi))) := by
  have h := tendsto_hermitePolyProductTail_div_leading n n (by omega)
  simpa [pow_two, two_mul] using h

end RHTower
