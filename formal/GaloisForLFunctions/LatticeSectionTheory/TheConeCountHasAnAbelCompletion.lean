import GaloisForLFunctions.LatticeSectionTheory.TheBoostCountHasLogarithmicDuality
import GaloisForLFunctions.LatticeSectionTheory.TheIsotropicConeCountsDivisors
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# An Abel completion of the literal cone count

The absolutely convergent Abel integral `4∫₀∞ C(t cosh u)du` equals the Gaussian
boost count. Adding the regularized axes `log t + 2/√t + c` gives a positive count
with reciprocal-scale duality and logarithmic Riemann--Roch on the pole plane.
The comparison translates each Gaussian pair into a hyperbolic cone kernel;
a summable majorant justifies exchanging the series and the boost integral.
-/

open Real MeasureTheory Set
noncomputable section

namespace GaloisForLFunctions.LatticeSectionTheory
open ArithmeticOrientationGeometry

private def abelKernel (k u : ℝ) : ℝ := Real.exp (-k * Real.cosh (2*u))

private theorem integrable_abelKernel {k : ℝ} (hk : 0 < k) : Integrable (abelKernel k) := by
  -- Exponential decay in the absolute boost gives an integrable majorant.
  have hc (u : ℝ) : |u| ≤ Real.cosh (2*u) := by
    rw [Real.cosh_eq]
    apply abs_le.mpr
    constructor <;> linarith only [Real.add_one_le_exp (2*u),
      Real.add_one_le_exp (-(2*u)), Real.exp_pos (2*u), Real.exp_pos (-(2*u))]
  refine (integrable_inv_one_add_sq.const_mul ((min 1 (k^2/2))⁻¹)).mono'
    (show Continuous (abelKernel k) by unfold abelKernel; fun_prop).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [abelKernel, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hc u) (by linarith))).trans
    (exp_neg_mul_abs_le hk u)

private theorem abelKernel_bound {a k : ℝ} (ha : 0 ≤ a) (hk : 2*a ≤ k) (u : ℝ) :
    abelKernel k u ≤ Real.exp (-k/2) * abelKernel a u := by
  unfold abelKernel
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_left (Real.one_le_cosh (2*u))
    (show 0 ≤ k-a by linarith only [ha, hk])
  nlinarith only [h, hk]

private theorem coneWeight_ge (i : ℕ × ℕ) : 2*Real.pi ≤ coneWeight i := by
  have hm : (0:ℝ) ≤ i.1 := Nat.cast_nonneg _
  have hn : (0:ℝ) ≤ i.2 := Nat.cast_nonneg _
  have h : 1 ≤ ((i.1:ℝ)+1)*((i.2:ℝ)+1) := by nlinarith only [hm, hn, mul_nonneg hm hn]
  calc
    2*Real.pi = 2*Real.pi*1 := (mul_one _).symm
    _ ≤ 2*Real.pi*(((i.1:ℝ)+1)*((i.2:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = coneWeight i := rfl

private theorem summable_integral_abelKernel {t : ℝ} (ht : 0 < t) :
    Summable (fun i : ℕ × ℕ => ∫ u, ‖abelKernel (coneWeight i*t) u‖) := by
  -- Half of each cone weight pays for summation; the other half pays for integration.
  have ha : 0 < Real.pi*t := mul_pos Real.pi_pos ht
  have hbase := integrable_abelKernel ha
  refine ((summable_coneCount (half_pos ht)).mul_right (∫ u, abelKernel (Real.pi*t) u)).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) fun i => ?_
  have hi := integrable_abelKernel (mul_pos (coneWeight_pos i) ht)
  calc
    (∫ u, ‖abelKernel (coneWeight i*t) u‖) = ∫ u, abelKernel (coneWeight i*t) u := by
      apply integral_congr_ae
      filter_upwards with u
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    _ ≤ ∫ u, Real.exp (-(coneWeight i*t)/2) * abelKernel (Real.pi*t) u := by
      apply integral_mono hi (hbase.const_mul _)
      intro u
      apply abelKernel_bound ha.le
      nlinarith only [mul_le_mul_of_nonneg_right (coneWeight_ge i) ht.le]
    _ = Real.exp (-coneWeight i*(t/2)) * ∫ u, abelKernel (Real.pi*t) u := by
      rw [integral_const_mul]
      congr 2
      ring

private def natGaussian (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-Real.pi * Real.exp (2*x) * ((n:ℝ)+1)^2)

private theorem summable_natGaussian (x : ℝ) : Summable (natGaussian x) := by
  have hi : Function.Injective (fun n : ℕ => (n+1:ℤ)) := by
    intro n m h
    exact_mod_cast (add_right_cancel h)
  refine ((summable_thetaSum (Real.exp_pos (2*x))).comp_injective hi).congr fun n => ?_
  simp only [natGaussian, Function.comp_apply, Int.cast_add, Int.cast_natCast, Int.cast_one]

private theorem logThetaTail_eq_tsum (x : ℝ) :
    logThetaTail x = 2 * ∑' n : ℕ, natGaussian x n := by
  have he : Function.Even (fun n : ℤ => Real.exp (-Real.pi*Real.exp (2*x)*(n:ℝ)^2)) := by
    intro n
    simp only [Int.cast_neg, neg_sq]
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat he (summable_thetaSum (Real.exp_pos (2*x)))
  have hp : (∑' n : ℕ+, Real.exp (-Real.pi*Real.exp (2*x)*(n:ℝ)^2)) =
      ∑' n : ℕ, natGaussian x n := by
    simpa only [natGaussian, Nat.cast_add, Nat.cast_one] using
      (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => Real.exp (-Real.pi*Real.exp (2*x)*(n:ℝ)^2)))
  simp only [Int.cast_zero, zero_pow (by decide : 2≠0), mul_zero, Real.exp_zero,
    Int.cast_natCast, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [hp] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [logThetaTail, thetaSum, add_comm] using h)

/-- A Gaussian pair is a translate of the hyperbolic kernel with its cone weight. -/
private theorem gaussianPair_eq_kernel (x u : ℝ) (i : ℕ × ℕ) :
    natGaussian (x+u) i.1 * natGaussian (x-u) i.2 =
      abelKernel (coneWeight i * Real.exp (2*x))
        (u + (Real.log ((i.1:ℝ)+1)-Real.log ((i.2:ℝ)+1))/2) := by
  have hm : 0 < (i.1:ℝ)+1 := by positivity
  have hn : 0 < (i.2:ℝ)+1 := by positivity
  have he₁ : Real.exp (2*(u+(Real.log ((i.1:ℝ)+1)-Real.log ((i.2:ℝ)+1))/2)) =
      Real.exp (2*u)*((i.1:ℝ)+1)/((i.2:ℝ)+1) := by
    rw [show 2*(u+(Real.log ((i.1:ℝ)+1)-Real.log ((i.2:ℝ)+1))/2) =
      2*u+Real.log ((i.1:ℝ)+1)-Real.log ((i.2:ℝ)+1) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hm, Real.exp_log hn]
  have he₂ : Real.exp (-(2*(u+(Real.log ((i.1:ℝ)+1)-Real.log ((i.2:ℝ)+1))/2))) =
      Real.exp (-2*u)*((i.2:ℝ)+1)/((i.1:ℝ)+1) := by
    rw [show -(2*(u+(Real.log ((i.1:ℝ)+1)-Real.log ((i.2:ℝ)+1))/2)) =
      -2*u+Real.log ((i.2:ℝ)+1)-Real.log ((i.1:ℝ)+1) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hn, Real.exp_log hm]
  have hp : Real.exp (2*(x+u)) = Real.exp (2*x)*Real.exp (2*u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hq : Real.exp (2*(x-u)) = Real.exp (2*x)*Real.exp (-2*u) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold natGaussian abelKernel
  rw [hp, hq, ← Real.exp_add, Real.cosh_eq, he₁, he₂]
  congr 1
  unfold coneWeight
  field_simp [ne_of_gt hm, ne_of_gt hn]
  ring

private theorem gaussianPair_integral (x : ℝ) (i : ℕ × ℕ) :
    (∫ u, natGaussian (x+u) i.1 * natGaussian (x-u) i.2) =
      ∫ u, abelKernel (coneWeight i*Real.exp (2*x)) u := by
  simp_rw [gaussianPair_eq_kernel]
  exact integral_add_right_eq_self _ _

private theorem integrable_gaussianPair (x : ℝ) (i : ℕ × ℕ) :
    Integrable (fun u => natGaussian (x+u) i.1 * natGaussian (x-u) i.2) := by
  simp_rw [gaussianPair_eq_kernel]
  exact (integrable_abelKernel (mul_pos (coneWeight_pos i) (Real.exp_pos _))).comp_add_right _

private theorem summable_integral_gaussianPair (x : ℝ) :
    Summable (fun i : ℕ × ℕ => ∫ u, ‖natGaussian (x+u) i.1 * natGaussian (x-u) i.2‖) := by
  refine (summable_integral_abelKernel (Real.exp_pos (2*x))).congr fun i => ?_
  calc
    (∫ u, ‖abelKernel (coneWeight i*Real.exp (2*x)) u‖) =
        ∫ u, abelKernel (coneWeight i*Real.exp (2*x)) u := by
      apply integral_congr_ae
      filter_upwards with u
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    _ = ∫ u, natGaussian (x+u) i.1 * natGaussian (x-u) i.2 :=
      (gaussianPair_integral x i).symm
    _ = ∫ u, ‖natGaussian (x+u) i.1 * natGaussian (x-u) i.2‖ := by
      apply integral_congr_ae
      filter_upwards with u
      exact (Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).symm

private theorem gaussianTailProduct_eq_tsum (x u : ℝ) :
    logThetaTail (x+u) * logThetaTail (x-u) =
      4 * ∑' i : ℕ × ℕ, natGaussian (x+u) i.1 * natGaussian (x-u) i.2 := by
  rw [logThetaTail_eq_tsum, logThetaTail_eq_tsum]
  have h := (summable_natGaussian (x+u)).tsum_mul_tsum (summable_natGaussian (x-u))
    ((summable_natGaussian (x+u)).mul_of_nonneg (summable_natGaussian (x-u))
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  rw [← h]
  ring

private theorem coneCount_cosh_eq_tsum (t u : ℝ) :
    coneCount (t*Real.cosh (2*u)) = ∑' i : ℕ × ℕ, abelKernel (coneWeight i*t) u := by
  unfold coneCount abelKernel
  apply tsum_congr
  intro i
  congr 1
  ring

/-- The hyperbolic Abel transform of the cone count is absolutely convergent. -/
theorem integrable_coneCount_cosh_two_mul {t : ℝ} (ht : 0 < t) :
    Integrable (fun u => coneCount (t*Real.cosh (2*u))) := by
  have ha : 0 < Real.pi*t := mul_pos Real.pi_pos ht
  have hm : AEStronglyMeasurable (fun u => coneCount (t*Real.cosh (2*u))) := by
    simp_rw [coneCount_cosh_eq_tsum]
    exact (AEMeasurable.tsum (fun i =>
      (show Continuous (abelKernel (coneWeight i*t)) by unfold abelKernel; fun_prop).aemeasurable)).aestronglyMeasurable
  apply ((integrable_abelKernel ha).const_mul (coneCount (t/2))).mono' hm
  filter_upwards with u
  have hs : Summable (fun i : ℕ × ℕ => abelKernel (coneWeight i*t) u) := by
    simpa only [abelKernel, neg_mul, mul_assoc] using
      summable_coneCount (mul_pos ht (Real.cosh_pos (2*u)))
  have hb : Summable (fun i : ℕ × ℕ =>
      Real.exp (-coneWeight i*(t/2))*abelKernel (Real.pi*t) u) :=
    (summable_coneCount (half_pos ht)).mul_right _
  have hpos : 0 ≤ coneCount (t*Real.cosh (2*u)) :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [Real.norm_of_nonneg hpos, coneCount_cosh_eq_tsum]
  calc
    (∑' i : ℕ × ℕ, abelKernel (coneWeight i*t) u) ≤
        ∑' i : ℕ × ℕ, Real.exp (-coneWeight i*(t/2))*abelKernel (Real.pi*t) u := by
      apply Summable.tsum_le_tsum _ hs hb
      intro i
      have h := abelKernel_bound ha.le
        (show 2*(Real.pi*t) ≤ coneWeight i*t by
          nlinarith only [mul_le_mul_of_nonneg_right (coneWeight_ge i) ht.le]) u
      rw [show -coneWeight i*(t/2) = -(coneWeight i*t)/2 by ring]
      exact h
    _ = coneCount (t/2)*abelKernel (Real.pi*t) u := tsum_mul_right

private theorem gaussianBoostCount_eq_cone_integral (x : ℝ) :
    gaussianBoostCount x = 4*∫ u, coneCount (Real.exp (2*x)*Real.cosh (2*u)) := by
  rw [gaussianBoostCount_eq_integral]
  simp_rw [gaussianTailProduct_eq_tsum]
  rw [integral_const_mul,
    ← integral_tsum_of_summable_integral_norm (integrable_gaussianPair x)
      (summable_integral_gaussianPair x)]
  simp_rw [gaussianPair_integral]
  rw [integral_tsum_of_summable_integral_norm
    (fun i => integrable_abelKernel (mul_pos (coneWeight_pos i) (Real.exp_pos _)))
    (summable_integral_abelKernel (Real.exp_pos (2*x)))]
  simp_rw [← coneCount_cosh_eq_tsum]

/-- The literal cone count integrated against the hyperbolic Abel kernel. -/
def coneAbelCount (t : ℝ) : ℝ :=
  4 * ∫ u in Ioi (0:ℝ), coneCount (t*Real.cosh u)

private theorem cone_integral_rescale (t : ℝ) :
    (∫ u, coneCount (t*Real.cosh (2*u))) =
      ∫ u in Ioi (0:ℝ), coneCount (t*Real.cosh u) := by
  have h := Measure.integral_comp_mul_left (fun u => coneCount (t*Real.cosh u)) (2:ℝ)
  have he := integral_comp_abs (f := fun u => coneCount (t*Real.cosh u))
  simp only [Real.cosh_abs] at he
  rw [h, he]
  norm_num [smul_eq_mul]
  ring

/-- The Abel integral of the exponential cone count equals the Gaussian boost count. -/
theorem coneAbelCount_exp (x : ℝ) :
    coneAbelCount (Real.exp (2*x)) = gaussianBoostCount x := by
  rw [gaussianBoostCount_eq_cone_integral, cone_integral_rescale, coneAbelCount]

/-- The regularized isotropic axes complete the Abel count. -/
def completedConeCount (t : ℝ) : ℝ :=
  coneAbelCount t + Real.log t + 2 / Real.sqrt t + boostLogConstant

/-- This completion is exactly the positive regularized split-plane count. -/
theorem completedConeCount_exp (x : ℝ) :
    completedConeCount (Real.exp (2*x)) = regularizedBoostCount x := by
  have he : Real.exp (2*x) = (Real.exp x)^2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hr : Real.sqrt (Real.exp (2*x)) = Real.exp x := by
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos x)]
  rw [completedConeCount, coneAbelCount_exp, regularizedBoostCount_eq, Real.log_exp,
    hr, div_eq_mul_inv, ← Real.exp_neg]

/-- The Abel integral converges on the entire boost line. -/
theorem integrable_coneCount_cosh {t : ℝ} (ht : 0 < t) :
    Integrable (fun u => coneCount (t*Real.cosh u)) := by
  exact (integrable_comp_mul_left_iff (fun u => coneCount (t*Real.cosh u))
    (by norm_num : (2:ℝ) ≠ 0)).mp
    (integrable_coneCount_cosh_two_mul ht)

/-- The positive-scale version of the literal cone/boost comparison. -/
theorem coneAbelCount_eq_gaussianBoostCount {t : ℝ} (ht : 0 < t) :
    coneAbelCount t = gaussianBoostCount (Real.log t/2) := by
  have h := coneAbelCount_exp (Real.log t/2)
  rw [show 2*(Real.log t/2)=Real.log t by ring, Real.exp_log ht] at h
  exact h

/-- The uncompleted Abel count has an explicit logarithmic reflection defect. -/
theorem coneAbelCount_inv {t : ℝ} (ht : 0 < t) :
    coneAbelCount (1/t) = t*coneAbelCount t + (1+t)*Real.log t + boostLogConstant*(t-1) := by
  rw [coneAbelCount_eq_gaussianBoostCount (one_div_pos.mpr ht),
    coneAbelCount_eq_gaussianBoostCount ht, gaussianBoostCount_log_inv ht]

theorem completedConeCount_eq_regularizedBoostCount {t : ℝ} (ht : 0 < t) :
    completedConeCount t = regularizedBoostCount (Real.log t/2) := by
  have h := completedConeCount_exp (Real.log t/2)
  rw [show 2*(Real.log t/2)=Real.log t by ring, Real.exp_log ht] at h
  exact h

/-- The regularized axes leave a strictly positive count at every positive scale. -/
theorem completedConeCount_pos {t : ℝ} (ht : 0 < t) : 0 < completedConeCount t := by
  rw [completedConeCount_eq_regularizedBoostCount ht]
  exact regularizedBoostCount_pos _

/-- Reciprocal-scale duality of the completed literal cone transform. -/
theorem completedConeCount_inv {t : ℝ} (ht : 0 < t) :
    completedConeCount (1/t) = t*completedConeCount t := by
  rw [completedConeCount_eq_regularizedBoostCount (one_div_pos.mpr ht),
    completedConeCount_eq_regularizedBoostCount ht, one_div, Real.log_inv, neg_div,
    regularizedBoostCount_neg, show 2*(Real.log t/2)=Real.log t by ring, Real.exp_log ht]

/-- The completed cone count carries logarithmic Riemann--Roch on the pole plane. -/
theorem log_completedConeCount_inv {t : ℝ} (ht : 0 < t) :
    Real.log (completedConeCount (1/t)) - Real.log (completedConeCount t) = Real.log t := by
  rw [completedConeCount_inv ht, Real.log_mul ht.ne' (completedConeCount_pos ht).ne']
  ring

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.integrable_coneCount_cosh
#print axioms GaloisForLFunctions.LatticeSectionTheory.coneAbelCount_eq_gaussianBoostCount
#print axioms GaloisForLFunctions.LatticeSectionTheory.coneAbelCount_inv
#print axioms GaloisForLFunctions.LatticeSectionTheory.completedConeCount_pos
#print axioms GaloisForLFunctions.LatticeSectionTheory.completedConeCount_inv
#print axioms GaloisForLFunctions.LatticeSectionTheory.log_completedConeCount_inv
