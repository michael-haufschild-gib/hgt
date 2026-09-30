import GaloisForLFunctions.RHTower.SteinhausEulerQuadraticApprox
import GaloisForLFunctions.RHTower.SteinhausEulerTiltFiniteDensity

/-!
# Exact second moments of the literal finite Steinhaus Euler product

The complex Poisson kernel at the conjugate of a point in the unit disc gives
an exact squared-norm integral for one Euler factor, with arbitrary phase shift.
Finite product integration then identifies the second moment of the existing
`steinhausFiniteEulerProduct` on the whole positive half-plane with its arithmetic
partition function. The imaginary part disappears from the answer.

These are unconditional source identities for the BAG spatial maximum estimate;
no recurrence, critical-mass decay, or probabilistic moment estimate is assumed.
-/

open MeasureTheory Complex InnerProductSpace
open scoped BigOperators

noncomputable section
namespace RHTower
open SteinhausModel
open GaloisForLFunctions.RHTower

private theorem circlePhase_norm (x : ℝ) : ‖circleMap 0 1 (2 * Real.pi * x)‖ = 1 := by
  simp [circleMap, Complex.norm_exp]

private theorem poissonKernel_conj_eq {z w : ℂ} (hw : ‖w‖ = 1) :
    poissonKernel 0 (starRingEnd ℂ z) w = (1 - ‖z‖ ^ 2) / ‖1 - z * w‖ ^ 2 := by
  have hsq : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
  have hden : ‖w - starRingEnd ℂ z‖ ^ 2 = ‖1 - z * w‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one,
      Complex.normSq_conj, map_mul, hsq, Complex.conj_conj, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    ring
  simp only [poissonKernel_def, sub_zero, hw, one_pow, Complex.norm_conj, hden]

private theorem integral_circlePhase (f : ℂ → ℝ) :
    ∫ x, f (circleMap 0 1 (2 * Real.pi * x))
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = Real.circleAverage f 0 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_comp_mul_left (fun t => f (circleMap 0 1 t))
    (by positivity : 2 * Real.pi ≠ 0)]
  simp [Real.circleAverage]

/-- Exact second moment of a single Euler factor, including arbitrary complex phase shifts. -/
theorem integral_norm_sq_steinhausEulerFactor {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, ‖(1 - z * circleMap 0 1 (2 * Real.pi * x))⁻¹‖ ^ 2
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) = (1 - ‖z‖ ^ 2)⁻¹ := by
  have hw : starRingEnd ℂ z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have hp := (harmonicOnNhd_const (E := ℂ) (1 : ℝ)).circleAverage_poissonKernel_smul hw
  change Real.circleAverage (fun w => poissonKernel 0 (starRingEnd ℂ z) w * 1) 0 1 = 1 at hp
  simp only [mul_one] at hp
  rw [← integral_circlePhase] at hp
  simp_rw [poissonKernel_conj_eq (circlePhase_norm _), div_eq_mul_inv,
    ← inv_pow, ← norm_inv] at hp
  rw [integral_const_mul] at hp
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [← one_div]
  apply (eq_div_iff hpos.ne').mpr
  nlinarith [hp]

private theorem euler_denominator_ne_zero {z : ℂ} (hz : ‖z‖ < 1) (x : ℝ) :
    1 - z * circleMap 0 1 (2 * Real.pi * x) ≠ 0 := by
  have hn : ‖z * circleMap 0 1 (2 * Real.pi * x)‖ < 1 := by
    simpa only [norm_mul, circlePhase_norm, mul_one] using hz
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hn
  exact lt_irrefl _ hn

/-- Continuity of the coordinate squared Euler factor on the actual real phase model. -/
theorem continuous_norm_sq_steinhausEulerFactor {z : ℂ} (hz : ‖z‖ < 1) :
    Continuous (fun x : ℝ => ‖(1 - z * circleMap 0 1 (2 * Real.pi * x))⁻¹‖ ^ 2) := by
  have hc : Continuous (fun x : ℝ => 1 - z * circleMap 0 1 (2 * Real.pi * x)) := by fun_prop
  exact (hc.inv₀ (euler_denominator_ne_zero hz)).norm.pow 2

/-- A prime Steinhaus character is the literal unit-circle coordinate. -/
theorem steinhausCharacter_prime_eq_circleMap {p : ℕ} (hp : p.Prime) (ω : Omega) :
    X p ω = circleMap 0 1 (2 * Real.pi * ω p) := by
  rw [X_prime_eq hp]
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  ring

private theorem prime_cpow_norm_lt_one {s : ℂ} (hs : 0 < s.re) {p : ℕ} (hp : p.Prime) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  exact (prime_rpow_neg_le_rho hs hp).trans_lt (randomEulerRho_lt_one hs)

private theorem prime_cpow_norm_sq {s : ℂ} {p : ℕ} (hp : p.Prime) :
    ‖(p : ℂ) ^ (-s)‖ ^ 2 = (p : ℝ) ^ (-(2 * s.re)) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re,
    ← Real.rpow_two, ← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
  congr 1
  ring

/-- The exact arithmetic partition function of a finite prime Euler product. -/
def steinhausEulerPartition (P : Finset ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - (p : ℝ) ^ (-(2 * σ)))⁻¹

/-- The arithmetic second moment is strictly positive on the positive half-plane. -/
theorem steinhausEulerPartition_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {σ : ℝ} (hσ : 0 < σ) : 0 < steinhausEulerPartition P σ := by
  unfold steinhausEulerPartition
  apply Finset.prod_pos
  intro p hp
  apply inv_pos.mpr
  apply sub_pos.mpr
  exact (prime_rpow_neg_le_rho (by linarith : 0 < 2 * σ) (hP p hp)).trans_lt
    (randomEulerRho_lt_one (by linarith))

/-- At the critical abscissa the partition function is the literal reciprocal Euler product. -/
theorem steinhausEulerPartition_half (P : Finset ℕ) :
    steinhausEulerPartition P (1 / 2) = ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := by
  simp [steinhausEulerPartition, Real.rpow_neg_one]

/-- Exact second moment of the existing finite random Euler product throughout `Re(s)>0`.
The imaginary part is unrestricted and disappears from the arithmetic answer. -/
theorem integral_norm_sq_steinhausFiniteEulerProduct (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (∫ ω, ‖steinhausFiniteEulerProduct P s ω‖ ^ 2 ∂steinhausMeasure) =
      steinhausEulerPartition P s.re := by
  classical
  let f : (p : ↥P) → ℝ → ℝ := fun p x =>
    ‖(1 - (p.val : ℂ) ^ (-s) * circleMap 0 1 (2 * Real.pi * x))⁻¹‖ ^ 2
  have hf (p : ↥P) : Continuous (f p) :=
    continuous_norm_sq_steinhausEulerFactor (prime_cpow_norm_lt_one hs (hP p p.property))
  have hprod : Continuous (fun x : ↥P → ℝ => ∏ p, f p (x p)) :=
    continuous_finsetProd _ fun p _ => (hf p).comp (continuous_apply p)
  have heq (ω : Omega) : ‖steinhausFiniteEulerProduct P s ω‖ ^ 2 =
      ∏ p : ↥P, f p (ω p) := by
    rw [steinhausFiniteEulerProduct, norm_prod, ← Finset.prod_pow]
    dsimp only [f]
    rw [Finset.prod_coe_sort P (fun p : ℕ =>
      ‖(1 - (p : ℂ) ^ (-s) * circleMap 0 1 (2 * Real.pi * ω p))⁻¹‖ ^ 2)]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [steinhausEulerPrimeTerm, steinhausCharacter_prime_eq_circleMap (hP p hp)]
    rw [mul_comm]
  calc
    _ = ∫ ω, ∏ p : ↥P, f p (ω p) ∂steinhausMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = ∫ x : ↥P → ℝ, ∏ p, f p (x p)
        ∂(Measure.pi fun _ : ↥P => volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integral_restrict_infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))
        hprod.aestronglyMeasurable
    _ = ∏ p : ↥P, ∫ x, f p x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      integral_fintype_prod_eq_prod f
    _ = ∏ p : ↥P, (1 - (p.val : ℝ) ^ (-(2 * s.re)))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p _
      have hm := integral_norm_sq_steinhausEulerFactor (prime_cpow_norm_lt_one hs (hP p p.property))
      simpa only [f, prime_cpow_norm_sq (hP p p.property)] using hm
    _ = _ := by
      simpa only [steinhausEulerPartition] using
        (Finset.prod_coe_sort P (fun p : ℕ => (1 - (p : ℝ) ^ (-(2 * s.re)))⁻¹))

end RHTower
