import GaloisForLFunctions.HTGeometry.PolyatomicLaplace
import GaloisForLFunctions.HTGeometry.QuantumGeometricTensorGram
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Fractional collision energies as actual Hilbert and quantum-metric geometry

The auxiliary Laplace factorization in arXiv:2608.29825 produces actual
half-line L² features. Their Gram matrix is the fractional coupled-energy
kernel, multiplied by the Gamma normalizer. Applying the corpus's
quantum-metric/Berry decomposition gives zero Berry curvature and a
strictly positive metric area exactly when the two squared energy
coordinates differ. Thus these features distinguish energies, while
opposite signs of the same coordinate are necessarily identified.
-/

open MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A Gamma-weighted, decaying half-line feature for one energy coordinate. -/
def collisionLaplaceFeature (a e x t : ℝ) : ℂ :=
  (t ^ ((Real.exp a - 1) / 2) * Real.exp (-(Real.exp e / 2 + x ^ 2) * t) : ℝ)

/-- The feature belongs to the actual half-line L² space for every parameter value. -/
theorem collisionLaplaceFeature_memLp (a e x : ℝ) :
    MemLp (collisionLaplaceFeature a e x) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hb : 0 < 2 * (Real.exp e / 2 + x ^ 2) := by positivity
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ))
    (s := Real.exp a - 1) (b := 2 * (Real.exp e / 2 + x ^ 2))
    (by linarith [Real.exp_pos a]) (le_refl _) hb
  apply (memLp_two_iff_integrable_sq_norm
    ((show Measurable (collisionLaplaceFeature a e x) by
      unfold collisionLaplaceFeature
      fun_prop).aestronglyMeasurable)).mpr
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hp : (t ^ ((Real.exp a - 1) / 2)) ^ 2 = t ^ (Real.exp a - 1) := by
    rw [← Real.rpow_natCast (t ^ ((Real.exp a - 1) / 2)) 2,
      ← Real.rpow_mul ht.le]
    congr 1
    ring
  simp only [collisionLaplaceFeature, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.rpow_one, mul_pow, hp]
  rw [pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

/-- The completed feature, rather than an abstract coefficient-space surrogate. -/
def collisionLaplaceAtom (a e x : ℝ) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (collisionLaplaceFeature_memLp a e x).toLp (collisionLaplaceFeature a e x)

theorem collisionLaplaceAtom_ae (a e x : ℝ) :
    (collisionLaplaceAtom a e x : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      collisionLaplaceFeature a e x :=
  (collisionLaplaceFeature_memLp a e x).coeFn_toLp

/-- Exact inner product of the completed energy features. -/
theorem collisionLaplaceAtom_inner (a e x y : ℝ) :
    inner ℂ (collisionLaplaceAtom a e x) (collisionLaplaceAtom a e y) =
      ((Real.Gamma (Real.exp a) * collisionFractionalKernel a e x y : ℝ) : ℂ) := by
  have hG := ne_of_gt (Real.Gamma_pos_of_pos (Real.exp_pos a))
  have hint : (∫ t : ℝ in Ioi 0, t ^ (Real.exp a - 1) *
      Real.exp (-(Real.exp e + x ^ 2 + y ^ 2) * t)) =
      Real.Gamma (Real.exp a) * collisionFractionalKernel a e x y := by
    rw [collisionFractionalKernel_laplace]
    field_simp
  rw [L2.inner_def, ← hint, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [collisionLaplaceAtom_ae a e x, collisionLaplaceAtom_ae a e y,
    ae_restrict_mem measurableSet_Ioi] with t hx hy ht
  rw [hx, hy, RCLike.inner_apply]
  simp only [collisionLaplaceFeature, Complex.conj_ofReal, ← Complex.ofReal_mul]
  congr 1
  have hp : (t ^ ((Real.exp a - 1) / 2)) ^ 2 = t ^ (Real.exp a - 1) := by
    rw [← Real.rpow_natCast (t ^ ((Real.exp a - 1) / 2)) 2,
      ← Real.rpow_mul ht.le]
    congr 1
    ring
  calc
    _ = (t ^ ((Real.exp a - 1) / 2)) ^ 2 *
        (Real.exp (-(Real.exp e / 2 + x ^ 2) * t) *
          Real.exp (-(Real.exp e / 2 + y ^ 2) * t)) := by ring
    _ = _ := by
      rw [hp, ← Real.exp_add]
      congr 2
      ring

/-- The diagonal Gram entry is the exact Hilbert norm, not merely a bound. -/
theorem collisionLaplaceAtom_norm_sq (a e x : ℝ) :
    ‖collisionLaplaceAtom a e x‖ ^ 2 =
      Real.Gamma (Real.exp a) * collisionFractionalKernel a e x x := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), collisionLaplaceAtom_inner]
  rfl

/-- The fractional energy kernel separates two squared rates sharply. -/
theorem collisionFractionalKernel_det_pos_iff (a e x y : ℝ) :
    0 < collisionFractionalKernel a e x x * collisionFractionalKernel a e y y -
      collisionFractionalKernel a e x y ^ 2 ↔ x ^ 2 ≠ y ^ 2 := by
  have hA : 0 < Real.exp e + x ^ 2 + x ^ 2 := by positivity
  have hB : 0 < Real.exp e + y ^ 2 + y ^ 2 := by positivity
  have hC : 0 < Real.exp e + x ^ 2 + y ^ 2 := by positivity
  have hsq : collisionFractionalKernel a e x y ^ 2 =
      ((Real.exp e + x ^ 2 + y ^ 2) * (Real.exp e + x ^ 2 + y ^ 2)) ^
        (-Real.exp a) := by
    rw [Real.mul_rpow hC.le hC.le, pow_two]
    rfl
  rw [hsq, collisionFractionalKernel, collisionFractionalKernel,
    ← Real.mul_rpow hA.le hB.le, sub_pos,
    Real.rpow_lt_rpow_iff_of_neg (mul_pos hC hC) (mul_pos hA hB)
      (neg_neg_of_pos (Real.exp_pos a))]
  constructor
  · intro h he
    rw [he] at h
    exact (lt_irrefl _ h)
  · intro h
    have hp : 0 < (x ^ 2 - y ^ 2) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
    nlinarith

/-- Real Laplace features carry no Berry curvature. -/
theorem collisionLaplaceAtom_berry_zero (a e x y : ℝ) :
    HTGeometry.berryCurvatureValue (collisionLaplaceAtom a e x) (collisionLaplaceAtom a e y) = 0 := by
  simp only [HTGeometry.berryCurvatureValue, collisionLaplaceAtom_inner,
    Complex.ofReal_im, mul_zero]

/-- The corpus quantum metric is the exact fractional-energy determinant. -/
theorem collisionLaplaceAtom_metric_area (a e x y : ℝ) :
    HTGeometry.quantumMetricAreaValue (collisionLaplaceAtom a e x) (collisionLaplaceAtom a e y) =
      Real.Gamma (Real.exp a) ^ 2 *
        (collisionFractionalKernel a e x x * collisionFractionalKernel a e y y -
          collisionFractionalKernel a e x y ^ 2) := by
  simp only [HTGeometry.quantumMetricAreaValue, collisionLaplaceAtom_norm_sq,
    collisionLaplaceAtom_inner, Complex.ofReal_re]
  ring

/-- Quantum-metric area is positive exactly for distinct energies, with no separation premise. -/
theorem collisionLaplaceAtom_metric_pos_iff (a e x y : ℝ) :
    0 < HTGeometry.quantumMetricAreaValue
      (collisionLaplaceAtom a e x) (collisionLaplaceAtom a e y) ↔ x ^ 2 ≠ y ^ 2 := by
  rw [collisionLaplaceAtom_metric_area,
    mul_pos_iff_of_pos_left (sq_pos_of_pos (Real.Gamma_pos_of_pos (Real.exp_pos a))),
    collisionFractionalKernel_det_pos_iff]

/-- Opposite signed coordinates give the identical completed feature. -/
theorem collisionLaplaceAtom_neg (a e x : ℝ) :
    collisionLaplaceAtom a e (-x) = collisionLaplaceAtom a e x := by
  apply Lp.ext
  filter_upwards [collisionLaplaceAtom_ae a e (-x), collisionLaplaceAtom_ae a e x] with t hneg hpos
  rw [hneg, hpos]
  simp only [collisionLaplaceFeature, neg_sq]

/-- The two completed features are complex-linearly independent exactly at distinct energies. -/
theorem collisionLaplaceAtom_pair_independent_iff (a e x y : ℝ) :
    LinearIndependent ℂ ![collisionLaplaceAtom a e x, collisionLaplaceAtom a e y] ↔
      x ^ 2 ≠ y ^ 2 := by
  rw [← HTGeometry.quantumMetricArea_strict_iff_linearIndependent_pair,
    collisionLaplaceAtom_berry_zero]
  simpa using collisionLaplaceAtom_metric_pos_iff a e x y

/-- The feature map identifies precisely equal squared-energy coordinates. -/
theorem collisionLaplaceAtom_eq_iff (a e x y : ℝ) :
    collisionLaplaceAtom a e x = collisionLaplaceAtom a e y ↔ x ^ 2 = y ^ 2 := by
  constructor
  · intro h
    have hh := congrArg (fun u => inner ℂ u (collisionLaplaceAtom a e 0)) h
    rw [collisionLaplaceAtom_inner, collisionLaplaceAtom_inner] at hh
    have hr := Complex.ofReal_inj.mp hh
    have hK := mul_left_cancel₀ (ne_of_gt (Real.Gamma_pos_of_pos (Real.exp_pos a))) hr
    unfold collisionFractionalKernel at hK
    rw [Real.rpow_left_inj (by positivity) (by positivity)
      (ne_of_lt (neg_neg_of_pos (Real.exp_pos a)))] at hK
    linarith
  · intro h
    apply Lp.ext
    filter_upwards [collisionLaplaceAtom_ae a e x, collisionLaplaceAtom_ae a e y] with t hx hy
    rw [hx, hy]
    simp only [collisionLaplaceFeature, h]

end GaloisForLFunctions.HTGeometry
