import GaloisForLFunctions.HTGeometry.PartialBoundaryApproximationForcesSmallValues
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheTailOfAReturnCarriesTheZero

/-!
# An almost-closed Euler approximation requires prime mass

An Euler head approximating a function with a central zero on all but an angle `δ`
must have logarithmic prime mass of order `1/δ`. The proof applies the short-arc
small-value inequality to the target times the Euler mollifier and to the constant
function `1`.

For a fixed zeta disc and fixed relative accuracy, `δ ≤ 1/log(2+|τ|)` therefore
forces the prime mass to grow at least linearly in `log(2+|τ|)`. This is a necessary
condition on Euler-head approximations; it does not assert existence of zeta returns.
-/

open Complex Metric Real Set Finset
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

/-- The logarithm of the uniform Euler-mollifier bound on `Re s ≥ σ`. -/
def primeBoundaryMass (y : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ headPrimes y, Real.log (1 + (p : ℝ) ^ (-σ))

theorem primeBoundaryMass_nonneg (y : ℕ) (σ : ℝ) : 0 ≤ primeBoundaryMass y σ := by
  refine Finset.sum_nonneg fun p _ => Real.log_nonneg ?_
  have hp : 0 ≤ (p : ℝ) ^ (-σ) := by positivity
  linarith only [hp]

theorem primeBoundaryMass_le_sum (y : ℕ) (σ : ℝ) :
    primeBoundaryMass y σ ≤ ∑ p ∈ headPrimes y, (p : ℝ) ^ (-σ) := by
  refine Finset.sum_le_sum fun p _ => ?_
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + (p : ℝ) ^ (-σ) by positivity)
  linarith only [h]

/-- Each local factor contributes at most `log(1+p⁻σ)` to the logarithmic norm. -/
theorem norm_eulerMollifier_le_exp_primeBoundaryMass (y : ℕ) {σ : ℝ} {s : ℂ}
    (hs : σ ≤ s.re) : ‖eulerMollifier y s‖ ≤ Real.exp (primeBoundaryMass y σ) := by
  rw [eulerMollifier, norm_prod, primeBoundaryMass, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_
  rw [Real.exp_log (by positivity : 0 < 1 + (p : ℝ) ^ (-σ))]
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ p))
      (neg_le_neg hs)
  calc
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ = 1 + (p : ℝ) ^ (-s.re) := by
      rw [norm_one, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    _ ≤ 1 + (p : ℝ) ^ (-σ) := by linarith only [hpow]

private theorem disc_left_le_re {c z : ℂ} {R : ℝ} (hz : z ∈ closedBall c R) :
    c.re - R ≤ z.re := by
  have hn : ‖z - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have ha := (Complex.abs_re_le_norm (z - c)).trans hn
  rw [Complex.sub_re, abs_le] at ha
  linarith only [ha.1]

/-- Multiplying a central zero by an Euler mollifier forces a definite logarithmic
cost when the product stays close to `1` on the long arc. -/
theorem shortArc_eulerResidual_primeMass {f : ℂ → ℂ} {c : ℂ} {R δ η B : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hδπ : δ ≤ 2 * π) (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c = 0)
    (hB : 0 ≤ B) (hbound : ∀ θ : ℝ, ‖f (circleMap c R θ)‖ ≤ B) (y : ℕ) (τ : ℝ)
    (hreturn : ∀ θ ∈ Icc δ (2 * π),
      ‖1 - f (circleMap c R θ) * eulerMollifier y (circleMap c R θ + (τ : ℂ) * I)‖ ≤ η) :
    (2 * π - δ) * (-Real.log η) ≤
      δ * (Real.log (1 + B) + primeBoundaryMass y (c.re - R)) := by
  have hmul : AnalyticOnNhd ℂ (fun z => f z * eulerMollifier y (z + (τ : ℂ) * I))
      (closedBall c R) := by
    refine hf.mul fun z _ => ?_
    exact ((differentiable_eulerMollifier y).analyticAt (z + (τ : ℂ) * I)).comp
      (f := fun w : ℂ => w + (τ : ℂ) * I) (x := z)
      (analyticAt_id.add analyticAt_const)
  have hzero : f c * eulerMollifier y (c + (τ : ℂ) * I) = 0 := by rw [hfc, zero_mul]
  have hret : ∀ θ ∈ Icc δ (2 * π),
      ‖(1 : ℂ) - f (circleMap c R θ) * eulerMollifier y (circleMap c R θ + (τ : ℂ) * I)‖ ≤
        η * ‖(1 : ℂ)‖ := by simpa only [norm_one, mul_one] using hreturn
  rcases zero_or_shortArc_small_value hR hδ hδπ hη hmul analyticOnNhd_const hzero hret with
    hz | ⟨θ, _, hsmall⟩
  · obtain ⟨z, _, hz⟩ := hz
    exact (one_ne_zero hz).elim
  · simp only [norm_one, mul_one, norm_mul] at hsmall
    have hre : c.re - R ≤ (circleMap c R θ + (τ : ℂ) * I).re := by
      simpa using disc_left_le_re
        (sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ))
    have hnorm := mul_le_mul (hbound θ)
      (norm_eulerMollifier_le_exp_primeBoundaryMass y hre) (norm_nonneg _) hB
    have hmass := primeBoundaryMass_nonneg y (c.re - R)
    have he1 : 1 ≤ Real.exp (primeBoundaryMass y (c.re - R)) :=
      Real.one_le_exp_iff.mpr hmass
    have he : Real.exp (-(2 * π - δ) * Real.log η / δ) ≤
        (1 + B) * Real.exp (primeBoundaryMass y (c.re - R)) := by
      nlinarith only [hsmall, hnorm, he1]
    have hl := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hl
    have hk := (div_le_iff₀ hδ).mp hl
    nlinarith only [hk]

private theorem log_height_gt_half (τ : ℝ) : 1 / 2 < Real.log (2 + |τ|) := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ 2 + |τ| by linarith only [abs_nonneg τ])
  linarith only [hlog, Real.log_two_gt_d9]

/-- At inverse-logarithmic gap size, the necessary Euler mass is linear in log height. -/
theorem logarithmicGap_eulerResidual_primeMass {f : ℂ → ℂ} {c : ℂ} {R δ η B : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hη : 0 < η) (hη1 : η < 1)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c = 0)
    (hB : 0 ≤ B) (hbound : ∀ θ : ℝ, ‖f (circleMap c R θ)‖ ≤ B) (y : ℕ) (τ : ℝ)
    (hgap : δ ≤ 1 / Real.log (2 + |τ|))
    (hreturn : ∀ θ ∈ Icc δ (2 * π),
      ‖1 - f (circleMap c R θ) * eulerMollifier y (circleMap c R θ + (τ : ℂ) * I)‖ ≤ η) :
    2 * π * (-Real.log η) * Real.log (2 + |τ|) ≤
      -Real.log η + Real.log (1 + B) + primeBoundaryMass y (c.re - R) := by
  have hlog := log_height_gt_half τ
  have hlog0 : 0 < Real.log (2 + |τ|) := by linarith only [hlog]
  have hδlog := (le_div_iff₀ hlog0).mp hgap
  have hδ2 : δ ≤ 2 := by nlinarith only [hδlog, hlog, hδ]
  have hδπ : δ ≤ 2 * π := by linarith only [hδ2, Real.pi_gt_three]
  have hcost := shortArc_eulerResidual_primeMass hR hδ hδπ hη hf hfc hB hbound y τ hreturn
  have hL : 0 < -Real.log η := neg_pos.mpr (Real.log_neg hη hη1)
  have hA : 0 ≤ -Real.log η + Real.log (1 + B) + primeBoundaryMass y (c.re - R) :=
    add_nonneg (add_nonneg hL.le (Real.log_nonneg (by linarith only [hB])))
      (primeBoundaryMass_nonneg y (c.re - R))
  have hprod := mul_le_mul_of_nonneg_right hgap hA
  have hdiv : 2 * π * (-Real.log η) ≤
      (-Real.log η + Real.log (1 + B) + primeBoundaryMass y (c.re - R)) /
        Real.log (2 + |τ|) := by
    calc
      _ ≤ δ * (-Real.log η + Real.log (1 + B) + primeBoundaryMass y (c.re - R)) := by
        nlinarith only [hcost]
      _ ≤ (1 / Real.log (2 + |τ|)) *
          (-Real.log η + Real.log (1 + B) + primeBoundaryMass y (c.re - R)) := hprod
      _ = _ := by ring
  exact (le_div_iff₀ hlog0).mp hdiv

/-- A relative Euler-head approximation is exactly a small mollified residual. -/
theorem eulerHead_relative_error_iff {s a : ℂ} {η : ℝ} (y : ℕ) (hs : 0 < s.re) :
    ‖RHTower.eulerHead y s - a‖ ≤ η * ‖RHTower.eulerHead y s‖ ↔
      ‖1 - a * eulerMollifier y s‖ ≤ η := by
  have hm : eulerMollifier y s ≠ 0 := eulerMollifier_ne_zero y hs
  have he : RHTower.eulerHead y s * eulerMollifier y s = 1 := by
    rw [eulerHead_eq_inv, inv_mul_cancel₀ hm]
  have hnorm : ‖RHTower.eulerHead y s‖ * ‖eulerMollifier y s‖ = 1 := by
    rw [← norm_mul, he, norm_one]
  have hres : ‖1 - a * eulerMollifier y s‖ =
      ‖RHTower.eulerHead y s - a‖ * ‖eulerMollifier y s‖ := by
    rw [← norm_mul, sub_mul, he]
  rw [hres]
  constructor
  · intro h
    have hh := mul_le_mul_of_nonneg_right h (norm_nonneg (eulerMollifier y s))
    simpa only [mul_assoc, hnorm, mul_one] using hh
  · intro h
    have hd := (le_div_iff₀ (norm_pos_iff.mpr hm)).mpr h
    simpa only [eulerHead_eq_inv, norm_inv, div_eq_mul_inv] using hd

/-- A fixed zeta zero, disc, and accuracy determine a uniform additive constant in
the prime-mass bound. Analyticity and the circle bound are supplied by zeta itself. -/
theorem exists_zeta_euler_logarithmicGap_primeMass_bound {ρ : ℂ} {R η : ℝ}
    (hρ : riemannZeta ρ = 0) (hR : 0 < R) (hleft : 0 < ρ.re - R)
    (hupper : ρ.re + R < 1) (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℕ) (τ δ : ℝ), 0 < δ →
      δ ≤ 1 / Real.log (2 + |τ|) →
      (∀ θ ∈ Icc δ (2 * π),
        ‖RHTower.eulerHead y (circleMap ρ R θ + (τ : ℂ) * I) -
            riemannZeta (circleMap ρ R θ)‖ ≤
          η * ‖RHTower.eulerHead y (circleMap ρ R θ + (τ : ℂ) * I)‖) →
      2 * π * (-Real.log η) * Real.log (2 + |τ|) ≤
        C + primeBoundaryMass y (ρ.re - R) := by
  have hf : AnalyticOnNhd ℂ riemannZeta (closedBall ρ R) := by
    intro z hz
    apply HTGeometry.analyticAt_riemannZeta
    have hre := lt_of_le_of_lt (RHTower.re_le_of_mem_closedBall hz) hupper
    intro heq
    rw [heq] at hre
    exact (lt_irrefl (1 : ℝ)) hre
  obtain ⟨B, hB⟩ := (isCompact_closedBall ρ R).exists_bound_of_continuousOn hf.continuousOn
  have hBm : 0 ≤ max B 0 := le_max_right B 0
  have hcircle : ∀ θ : ℝ, ‖riemannZeta (circleMap ρ R θ)‖ ≤ max B 0 := fun θ =>
    (hB _ (sphere_subset_closedBall (circleMap_mem_sphere ρ hR.le θ))).trans (le_max_left B 0)
  refine ⟨-Real.log η + Real.log (1 + max B 0),
    add_pos_of_pos_of_nonneg (neg_pos.mpr (Real.log_neg hη hη1))
      (Real.log_nonneg (by linarith only [hBm])), ?_⟩
  intro y τ δ hδ hgap hreturn
  apply logarithmicGap_eulerResidual_primeMass hR hδ hη hη1 hf hρ hBm hcircle y τ hgap
  intro θ hθ
  have hre : 0 < (circleMap ρ R θ + (τ : ℂ) * I).re := by
    have hz := disc_left_le_re (sphere_subset_closedBall (circleMap_mem_sphere ρ hR.le θ))
    simpa using hleft.trans_le hz
  exact (eulerHead_relative_error_iff y hre).mp (hreturn θ hθ)

#print axioms primeBoundaryMass_le_sum
#print axioms shortArc_eulerResidual_primeMass
#print axioms logarithmicGap_eulerResidual_primeMass
#print axioms exists_zeta_euler_logarithmicGap_primeMass_bound

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
