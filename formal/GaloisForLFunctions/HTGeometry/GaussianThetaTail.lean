import GaloisForLFunctions.HTGeometry.GaussianThetaCharacteristics

/-!
# Uniform Poisson errors from the nonzero dual Gaussian mass

Removing the dual zero frequency bounds every affine Gaussian count and its
logarithmic ratio. The bounds retain the lattice and the spatial shift explicitly.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "Z" => ι → ℤ

/-- Removing the dual zero frequency bounds every shifted Gaussian characteristic. -/
theorem gaussian_dual_characteristic_error (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (w : E) :
    ‖(∑' k : Z, latticePhase w (inverseAdjoint B (euclideanIntegerPoint k)) *
      gaussianKernel a (inverseAdjoint B (euclideanIntegerPoint k))) - 1‖ ≤
        gaussianLatticeSum (inverseAdjointEquiv B) a - 1 := by
  classical
  let c : Z → ℂ := fun k => if k = 0 then 1 else 0
  let r : Z → ℝ := fun k => if k = 0 then 1 else 0
  have hc : HasSum c 1 := by
    simpa only [c, if_pos rfl] using
      (hasSum_single (f := c) 0 (fun k hk => if_neg hk))
  have hr : HasSum r 1 := by
    simpa only [r, if_pos rfl] using
      (hasSum_single (f := r) 0 (fun k hk => if_neg hk))
  have hd := summable_gaussianLatticeSum (inverseAdjointEquiv B) ha
  have hs := summable_norm_dual_gaussian_phase B ha w 0
  simp only [sub_zero] at hs
  have hn (k : Z) :
      ‖latticePhase w (inverseAdjoint B (euclideanIntegerPoint k)) *
        gaussianKernel a (inverseAdjoint B (euclideanIntegerPoint k)) - c k‖ =
      Real.exp (-a*‖inverseAdjointEquiv B (euclideanIntegerPoint k)‖^2) - r k := by
    by_cases hk : k = 0
    · subst k
      have hz : euclideanIntegerPoint (0 : Z) = 0 := by
        ext i
        change ((0 : ℤ) : ℝ) = 0
        exact Int.cast_zero
      simp [hz, c, r, latticePhase, gaussianKernel]
    · simp only [c, r, if_neg hk, sub_zero, norm_mul, norm_latticePhase, one_mul,
        norm_gaussianKernel, inverseAdjointEquiv_apply]
  have hsn := (hd.sub hr.summable).congr fun k => (hn k).symm
  have h := norm_tsum_le_tsum_norm hsn
  rw [hs.of_norm.tsum_sub hc.summable, hc.tsum_eq, tsum_congr hn,
    hd.tsum_sub hr.summable, hr.tsum_eq] at h
  exact h

/-- The positive Gaussian count on an affine full lattice. -/
def gaussianAffineLatticeSum (B : E ≃L[ℝ] E) (a : ℝ) (w : E) : ℝ :=
  ∑' k : Z, Real.exp (-a * ‖B (euclideanIntegerPoint k) + w‖^2)

theorem gaussianAffineLatticeSum_pos (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a) (w : E) :
    0 < gaussianAffineLatticeSum B a w := by
  have hs : Summable (fun k : Z => Real.exp (-a*‖B (euclideanIntegerPoint k)+w‖^2)) := by
    simpa only [norm_gaussianKernel] using summable_norm_gaussian_affine_lattice B ha w
  exact (Real.exp_pos _).trans_le (hs.le_tsum 0 (fun _ _ => (Real.exp_pos _).le))

/-- Poisson summation gives a uniform affine-count error controlled by the nonzero dual mass. -/
theorem gaussianAffineLatticeSum_poisson_error (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a)
    (w : E) :
    |gaussianAffineLatticeSum B a w - latticeScale B * gaussianFactor (ι := ι) a| ≤
      (latticeScale B * gaussianFactor (ι := ι) a) *
        (gaussianLatticeSum (inverseAdjointEquiv B) (Real.pi^2/a) - 1) := by
  let C := latticeScale B * gaussianFactor (ι := ι) a
  let F : ℂ := ∑' k : Z, latticePhase w (inverseAdjoint B (euclideanIntegerPoint k)) *
    gaussianKernel (Real.pi^2/a) (inverseAdjoint B (euclideanIntegerPoint k))
  have hC : 0 < C := mul_pos (latticeScale_pos B)
    (Real.rpow_pos_of_pos (div_pos Real.pi_pos ha) _)
  have hm (x : E) : gaussianModulation a 0 x = gaussianKernel a x := by
    simp only [gaussianModulation, latticePhase, inner_zero_right, mul_zero,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  have hp := gaussian_lattice_poisson_with_characteristics B ha w 0
  simp only [hm, sub_zero, Complex.real_smul] at hp
  have hr : (gaussianAffineLatticeSum B a w : ℂ) =
      ∑' k : Z, gaussianKernel a (B (euclideanIntegerPoint k)+w) := by
    simp only [gaussianAffineLatticeSum, Complex.ofReal_tsum, gaussianKernel_eq_ofReal]
  have he : (gaussianAffineLatticeSum B a w : ℂ) = (C : ℂ)*F := by
    simpa only [C, F, Complex.ofReal_mul, mul_assoc] using hr.trans hp
  have hd := gaussian_dual_characteristic_error B
    (div_pos (sq_pos_of_pos Real.pi_pos) ha) w
  have he' : (C : ℂ)*(F-1) = (gaussianAffineLatticeSum B a w : ℂ)-(C : ℂ) := by
    rw [mul_sub, ← he, mul_one]
  have hn : |gaussianAffineLatticeSum B a w-C| = C*‖F-1‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub, ← he',
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  rw [show latticeScale B * gaussianFactor (ι := ι) a = C from rfl, hn]
  exact mul_le_mul_of_nonneg_left hd hC.le

/-- The same nonzero dual mass controls all spatial shifts. -/
theorem gaussianAffineLatticeSum_bounds (B : E ≃L[ℝ] E) {a : ℝ} (ha : 0 < a) (w : E) :
    latticeScale B * gaussianFactor (ι := ι) a *
        (2-gaussianLatticeSum (inverseAdjointEquiv B) (Real.pi^2/a)) ≤
      gaussianAffineLatticeSum B a w ∧
    gaussianAffineLatticeSum B a w ≤
      latticeScale B * gaussianFactor (ι := ι) a *
        gaussianLatticeSum (inverseAdjointEquiv B) (Real.pi^2/a) := by
  have h := abs_le.mp (gaussianAffineLatticeSum_poisson_error B ha w)
  constructor <;> linarith only [h.1, h.2]

/-- A small dual tail controls the log-count ratio uniformly over every spatial shift. -/
theorem gaussianAffineLatticeSum_log_ratio_le (B : E ≃L[ℝ] E) {a R : ℝ}
    (ha : 0 < a) (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hdual : gaussianLatticeSum (inverseAdjointEquiv B) (Real.pi^2/a) ≤ 1+R) (w : E) :
    Real.log (gaussianAffineLatticeSum B a 0) - Real.log (gaussianAffineLatticeSum B a w) ≤
      Real.log ((1+R)/(1-R)) := by
  let C := latticeScale B * gaussianFactor (ι := ι) a
  have hC : 0 < C := mul_pos (latticeScale_pos B)
    (Real.rpow_pos_of_pos (div_pos Real.pi_pos ha) _)
  have hplus : 0 < 1+R := by linarith only [hR0]
  have hminus : 0 < 1-R := by linarith only [hR1]
  have hupper : gaussianAffineLatticeSum B a 0 ≤ C*(1+R) :=
    (gaussianAffineLatticeSum_bounds B ha 0).2.trans
      (mul_le_mul_of_nonneg_left hdual hC.le)
  have hlower : C*(1-R) ≤ gaussianAffineLatticeSum B a w := by
    refine le_trans ?_ (gaussianAffineLatticeSum_bounds B ha w).1
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith only [hdual]
  have hu := Real.log_le_log (gaussianAffineLatticeSum_pos B ha 0) hupper
  have hl := Real.log_le_log (mul_pos hC hminus) hlower
  calc
    _ ≤ Real.log (C*(1+R))-Real.log (C*(1-R)) := sub_le_sub hu hl
    _ = _ := by
      rw [Real.log_mul hC.ne' hplus.ne', Real.log_mul hC.ne' hminus.ne',
        Real.log_div hplus.ne' hminus.ne']
      ring

/-- A half-sized dual tail incurs at most four times its mass in logarithmic height. -/
theorem gaussianAffineLatticeSum_log_ratio_le_four (B : E ≃L[ℝ] E) {a R : ℝ}
    (ha : 0 < a) (hR0 : 0 ≤ R) (hR1 : R ≤ 1/2)
    (hdual : gaussianLatticeSum (inverseAdjointEquiv B) (Real.pi^2/a) ≤ 1+R) (w : E) :
    Real.log (gaussianAffineLatticeSum B a 0) - Real.log (gaussianAffineLatticeSum B a w) ≤
      4*R := by
  have hminus : 0 < 1-R := by linarith only [hR1]
  refine (gaussianAffineLatticeSum_log_ratio_le B ha hR0
    (by linarith only [hR1]) hdual w).trans ?_
  refine (Real.log_le_sub_one_of_pos (div_pos (by linarith only [hR0]) hminus)).trans ?_
  rw [sub_le_iff_le_add, div_le_iff₀ hminus]
  have h := mul_le_mul_of_nonneg_left hR1 hR0
  nlinarith only [h]

end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

#print axioms GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.gaussian_dual_characteristic_error
#print axioms GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.gaussianAffineLatticeSum_pos
#print axioms GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.gaussianAffineLatticeSum_poisson_error
#print axioms GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.gaussianAffineLatticeSum_bounds
#print axioms GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.gaussianAffineLatticeSum_log_ratio_le
#print axioms GaloisForLFunctions.HTGeometry.IntegerLatticePoisson.gaussianAffineLatticeSum_log_ratio_le_four
