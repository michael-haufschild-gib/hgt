import GaloisForLFunctions.RHTower.DeBruijnHeatGaussianAverage
import GaloisForLFunctions.HTGeometry.PolynomialHeatFlow
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The polynomial heat flow is a Gaussian average

For `t > 0` the Gaussian density `g_t` of variance `2t` has moments `∫ g_t(u) u^{2m} du =
(2m)! t^m / m!` and vanishing odd moments (`integral_gaussDensity_mul_pow_even`,
`integral_gaussDensity_mul_pow_odd`).  Expanding a polynomial `Q` around `z` by Taylor's formula
gives

`∫ g_t(u) Q(z − iu) du = Σ_m (−t)^m/m! · Q^{(2m)}(z) = (e^{−tD²}Q)(z)`

(`integral_gaussDensity_mul_eval_sub`): the polynomial heat flow is the same imaginary-direction
Gaussian average as the de Bruijn–Newman flow (`riemannHeat_eq_integral_gaussian_xi`).
-/

open Complex MeasureTheory Filter Topology Set Polynomial

namespace RHTower.DeBruijn

noncomputable section

/-! ## Gaussian moments -/

theorem integrable_gaussDensity_mul_pow {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun u : ℝ => gaussDensity t u * u ^ k) := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ)) (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)).const_mul ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)))
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only [gaussDensity, Real.rpow_natCast]
  rw [show -(1 / (4 * t)) * u ^ 2 = -(u ^ 2 / (4 * t)) by ring]
  ring

theorem integral_gaussDensity_mul_pow_odd (t : ℝ) (m : ℕ) :
    ∫ u : ℝ, gaussDensity t u * u ^ (2 * m + 1) = 0 := by
  have hneg : ∫ u : ℝ, gaussDensity t u * u ^ (2 * m + 1) =
      ∫ u : ℝ, gaussDensity t (-u) * (-u) ^ (2 * m + 1) :=
    (integral_neg_eq_self (fun u : ℝ => gaussDensity t u * u ^ (2 * m + 1)) volume).symm
  have hodd : ∀ u : ℝ, gaussDensity t (-u) * (-u) ^ (2 * m + 1) =
      -(gaussDensity t u * u ^ (2 * m + 1)) := by
    intro u
    simp only [gaussDensity, neg_sq, Odd.neg_pow (odd_two_mul_add_one m)]
    ring
  simp_rw [hodd, integral_neg] at hneg
  linarith

theorem Gamma_nat_add_half (m : ℕ) :
    Real.Gamma (m + 1 / 2) = Real.sqrt Real.pi * ((2 * m).factorial : ℝ) /
      (4 ^ m * (m.factorial : ℝ)) := by
  induction m with
  | zero => rw [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq]; simp
  | succ m ih =>
    have h := Real.Gamma_add_one (s := (m : ℝ) + 1 / 2) (by positivity)
    rw [show ((m + 1 : ℕ) : ℝ) + 1 / 2 = (m : ℝ) + 1 / 2 + 1 by push_cast; ring, h, ih,
      show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem integral_gaussDensity_mul_pow_even {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∫ u : ℝ, gaussDensity t u * u ^ (2 * m) = ((2 * m).factorial : ℝ) * t ^ m / m.factorial := by
  have hb : (0 : ℝ) < 1 / (4 * t) := by positivity
  -- reduce to the half line
  have heven : ∫ u : ℝ, gaussDensity t u * u ^ (2 * m) =
      2 * ∫ u in Ioi (0 : ℝ), gaussDensity t u * u ^ (2 * m) := by
    have hint := integrable_gaussDensity_mul_pow ht (2 * m)
    rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0)
      (f := fun u => gaussDensity t u * u ^ (2 * m)) hint.integrableOn hint.integrableOn]
    have hIic : ∫ u in Iic (0 : ℝ), gaussDensity t u * u ^ (2 * m) =
        ∫ u in Ioi (0 : ℝ), gaussDensity t u * u ^ (2 * m) := by
      have h := integral_comp_neg_Ioi 0 (fun u => gaussDensity t u * u ^ (2 * m))
      rw [neg_zero] at h
      rw [← h]
      congr 1; funext u
      simp only [gaussDensity, neg_sq, Even.neg_pow (even_two_mul m)]
    rw [hIic]; ring
  rw [heven]
  have hhalf : ∫ u in Ioi (0 : ℝ), gaussDensity t u * u ^ (2 * m) =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        ∫ u in Ioi (0 : ℝ), u ^ ((2 * m : ℕ) : ℝ) * Real.exp (-(1 / (4 * t)) * u ^ (2 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [gaussDensity, Real.rpow_natCast, Real.rpow_two]
    rw [show -(1 / (4 * t)) * u ^ 2 = -(u ^ 2 / (4 * t)) by ring]
    ring
  rw [hhalf, _root_.integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by
    have : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) hb]
  have hG : Real.Gamma ((((2 * m : ℕ) : ℝ) + 1) / 2) = Real.Gamma (m + 1 / 2) := by
    congr 1; push_cast; ring
  rw [hG, Gamma_nat_add_half]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  rw [show (1 / (4 * t)) ^ (-(((2 * m : ℕ) : ℝ) + 1) / 2) = (4 * t) ^ ((m : ℝ) + 1 / 2) by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1; push_cast; ring]
  rw [Real.rpow_add (by positivity), Real.rpow_natCast,
    show (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) = ((4 * t) ^ (1 / 2 : ℝ) * Real.sqrt Real.pi)⁻¹ by
      rw [Real.rpow_neg (by positivity), show 4 * Real.pi * t = (4 * t) * Real.pi by ring,
        Real.mul_rpow (by positivity) hpi.le, Real.sqrt_eq_rpow]]
  have h4 : (0 : ℝ) < (4 * t) ^ (1 / 2 : ℝ) := by positivity
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [mul_pow]
  field_simp

/-! ## The polynomial heat flow as a Gaussian average -/

theorem eval_sub_eq_sum_taylor (Q : ℂ[X]) (z w : ℂ) :
    Q.eval (z - w) = ∑ j ∈ Finset.range (Q.natDegree + 1),
      (hasseDeriv j Q).eval z * (-w) ^ j := by
  rw [show z - w = -w + z by ring, ← taylor_eval, eval_eq_sum_range' (n := Q.natDegree + 1)
    (by rw [natDegree_taylor]; omega)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [taylor_coeff]

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), f j = ∑ m ∈ Finset.range n, (f (2 * m) + f (2 * m + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    abel

theorem integral_gaussDensity_mul_ofReal_pow (t : ℝ) (j : ℕ) :
    ∫ u : ℝ, (gaussDensity t u : ℂ) * ((u : ℂ)) ^ j =
      ((∫ u : ℝ, gaussDensity t u * u ^ j : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  push_cast
  rfl

/-- **The polynomial heat flow as a Gaussian average.** For `t > 0` and a complex polynomial `Q`,
`∫ g_t(u) Q(z − iu) du = Σ_m (−t)^m/m! · Q^{(2m)}(z)`. -/
theorem integral_gaussDensity_mul_eval_sub {t : ℝ} (ht : 0 < t) (Q : ℂ[X]) (z : ℂ) :
    ∫ u : ℝ, (gaussDensity t u : ℂ) * Q.eval (z - I * u) =
      ∑ m ∈ Finset.range (Q.natDegree + 1),
        ((-t : ℂ) ^ m / (m.factorial : ℂ)) * (derivative^[2 * m] Q).eval z := by
  set N := Q.natDegree + 1
  set c : ℕ → ℂ := fun j => (hasseDeriv j Q).eval z
  have hc0 : ∀ j, N ≤ j → c j = 0 := by
    intro j hj
    simp only [c]
    rw [hasseDeriv_eq_zero_of_lt_natDegree _ _ (by omega), eval_zero]
  -- expand and integrate term by term
  have hexp : ∀ u : ℝ, (gaussDensity t u : ℂ) * Q.eval (z - I * u) =
      ∑ j ∈ Finset.range N, c j * (-I) ^ j * ((gaussDensity t u : ℂ) * (u : ℂ) ^ j) := by
    intro u
    rw [eval_sub_eq_sum_taylor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c]
    rw [show -(I * (u : ℂ)) = (-I) * u by ring, mul_pow]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun j _ => ((integrable_gaussDensity_mul_pow ht j).ofReal.congr
    (Eventually.of_forall fun u => by push_cast; rfl)).const_mul _)]
  simp_rw [integral_const_mul, integral_gaussDensity_mul_ofReal_pow t]
  -- pass to the even indices
  set f : ℕ → ℂ := fun j => c j * (-I) ^ j * ((∫ u : ℝ, gaussDensity t u * u ^ j : ℝ) : ℂ)
  have hext : ∑ j ∈ Finset.range N, f j = ∑ j ∈ Finset.range (2 * N), f j := by
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => ?_
    simp only [Finset.mem_range, not_lt] at hj
    simp only [f, hc0 j hj, zero_mul]
  change ∑ j ∈ Finset.range N, f j = _
  rw [hext, sum_range_two_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hodd : f (2 * m + 1) = 0 := by
    simp only [f, integral_gaussDensity_mul_pow_odd t m, Complex.ofReal_zero, mul_zero]
  rw [hodd, add_zero]
  simp only [f, c, integral_gaussDensity_mul_pow_even ht m]
  have hfac := congrFun (factorial_smul_hasseDeriv (R := ℂ) (k := 2 * m)) Q
  rw [LinearMap.smul_apply] at hfac
  rw [← hfac, eval_smul, nsmul_eq_mul]
  have hI : (-I) ^ (2 * m) = (-1 : ℂ) ^ m := by
    rw [pow_mul, neg_sq, I_sq]
  rw [hI]
  have hf2 : ((2 * m).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp
  ring

end

end RHTower.DeBruijn
