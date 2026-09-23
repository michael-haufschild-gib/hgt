import GaloisForLFunctions.HTGeometry.TwoTimeAutonomousEndpointJacobianLaw

open NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Exponential is quantitatively injective between two nearby skew-adjoint
generators.  The estimate is global on the indicated norm ball, not merely a
derivative statement. -/
theorem norm_exp_sub_exp_lower_of_skewAdjoint
    (x y : A) (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmallx : 4 * δ * ‖x‖ ≤ 1)
    (hsmallxy : δ * ‖y - x‖ ≤ 1 / 4) :
    δ / 4 * ‖y - x‖ ≤ ‖exp (δ • y) - exp (δ • x)‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let p := y - x
  have hp : p ∈ skewAdjoint A := (skewAdjoint A).sub_mem hy hx
  have hlin := duhamelConjugationPrimitive_shortTime_lower
    x p hx hδ hsmallx
  have hunit : exp (δ • x) ∈ unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem δ hx)
  have hlin' : δ / 2 * ‖p‖ ≤
      ‖exp (δ • x) * duhamelConjugationPrimitive x p δ‖ := by
    rw [CStarRing.norm_mem_unitary_mul _ hunit]
    exact hlin
  have herr := norm_autonomousPerturbedEndpoint_linearizationError_le
    x p hx hp hδ 1
  have hendpointOne : autonomousPerturbedEndpoint x p δ 1 = exp (δ • y) := by
    simp [autonomousPerturbedEndpoint, p]
  have hendpointZero : autonomousPerturbedEndpoint x p δ 0 = exp (δ • x) := by
    simp [autonomousPerturbedEndpoint]
  rw [hendpointOne, hendpointZero, one_smul] at herr
  norm_num at herr
  have herr' :
      ‖exp (δ • y) - exp (δ • x) -
          exp (δ • x) * duhamelConjugationPrimitive x p δ‖ ≤
        δ / 4 * ‖p‖ := by
    refine herr.trans ?_
    calc
      δ ^ (2 : ℕ) * ‖p‖ ^ (2 : ℕ) = (δ * ‖p‖) * (δ * ‖p‖) := by ring
      _ ≤ (1 / 4) * (δ * ‖p‖) := by
        gcongr
      _ = δ / 4 * ‖p‖ := by ring
  have htri :
      ‖exp (δ • x) * duhamelConjugationPrimitive x p δ‖ ≤
        ‖exp (δ • y) - exp (δ • x)‖ +
          ‖exp (δ • y) - exp (δ • x) -
            exp (δ • x) * duhamelConjugationPrimitive x p δ‖ := by
    calc
      ‖exp (δ • x) * duhamelConjugationPrimitive x p δ‖ =
          ‖(exp (δ • y) - exp (δ • x)) -
            (exp (δ • y) - exp (δ • x) -
              exp (δ • x) * duhamelConjugationPrimitive x p δ)‖ := by
        congr 1
        abel
      _ ≤ _ := norm_sub_le _ _
  dsimp only [p] at hlin' herr' htri ⊢
  linarith

/-- Pair of autonomous endpoints separated by `δ`. -/
def twoTimeAutonomousEndpoint (x : A) (t δ : ℝ) : A × A :=
  (exp (t • x), exp ((t + δ) • x))

/-- A short increment is recovered exactly from either endpoint pair. -/
theorem twoTimeAutonomousEndpoint_increment
    (x : A) (t δ : ℝ) :
    exp ((-t) • x) * (twoTimeAutonomousEndpoint x t δ).2 = exp (δ • x) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  change exp ((-t) • x) * exp ((t + δ) • x) = exp (δ • x)
  rw [← NormedSpace.exp_add_of_commute
    ((Commute.refl x).smul_left (-t) |>.smul_right (t + δ))]
  congr 1
  module

theorem exp_neg_time_eq_star_exp_time
    (x : A) (hx : x ∈ skewAdjoint A) (t : ℝ) :
    exp ((-t) • x) = star (exp (t • x)) := by
  have hxstar : star x = -x := skewAdjoint.mem_iff.mp hx
  rw [NormedSpace.star_exp, star_smul, hxstar]
  congr 1
  module

/-- The short-increment distance is at most twice the paired-endpoint
distance.  This estimate is independent of base time. -/
theorem norm_increment_sub_increment_le_two_mul_twoTimeEndpoint
    (x y : A) (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A)
    (t δ : ℝ) :
    ‖exp (δ • y) - exp (δ • x)‖ ≤
      2 * ‖twoTimeAutonomousEndpoint y t δ -
        twoTimeAutonomousEndpoint x t δ‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let D := twoTimeAutonomousEndpoint y t δ -
    twoTimeAutonomousEndpoint x t δ
  have hnegNorm :
      ‖exp ((-t) • y) - exp ((-t) • x)‖ =
        ‖exp (t • y) - exp (t • x)‖ := by
    rw [exp_neg_time_eq_star_exp_time y hy,
      exp_neg_time_eq_star_exp_time x hx, ← star_sub, norm_star]
  have hsplit :
      exp (δ • y) - exp (δ • x) =
        exp ((-t) • y) *
            (exp ((t + δ) • y) - exp ((t + δ) • x)) +
          (exp ((-t) • y) - exp ((-t) • x)) * exp ((t + δ) • x) := by
    rw [← twoTimeAutonomousEndpoint_increment y t δ,
      ← twoTimeAutonomousEndpoint_increment x t δ]
    noncomm_ring
  have huy : exp ((-t) • y) ∈ unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem (-t) hy)
  have hux : exp ((t + δ) • x) ∈ unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint
      (skewAdjoint.smul_mem (t + δ) hx)
  rw [hsplit]
  calc
    ‖exp ((-t) • y) *
          (exp ((t + δ) • y) - exp ((t + δ) • x)) +
        (exp ((-t) • y) - exp ((-t) • x)) * exp ((t + δ) • x)‖ ≤
        ‖exp ((-t) • y) *
          (exp ((t + δ) • y) - exp ((t + δ) • x))‖ +
        ‖(exp ((-t) • y) - exp ((-t) • x)) *
          exp ((t + δ) • x)‖ := norm_add_le _ _
    _ = ‖exp ((t + δ) • y) - exp ((t + δ) • x)‖ +
        ‖exp (t • y) - exp (t • x)‖ := by
      rw [CStarRing.norm_mem_unitary_mul _ huy,
        CStarRing.norm_mul_mem_unitary _ hux, hnegNorm]
    _ ≤ 2 * ‖D‖ := by
      have hfirst := norm_fst_le D
      have hsecond := norm_snd_le D
      dsimp only [D, twoTimeAutonomousEndpoint] at hfirst hsecond ⊢
      exact add_le_add hsecond hfirst |>.trans_eq (two_mul _).symm

/-- Global no-folding law for paired autonomous endpoints. -/
theorem twoTimeAutonomousEndpoint_lower_of_skewAdjoint
    (x y : A) (hx : x ∈ skewAdjoint A) (hy : y ∈ skewAdjoint A)
    (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmallx : 4 * δ * ‖x‖ ≤ 1)
    (hsmallxy : δ * ‖y - x‖ ≤ 1 / 4) :
    δ / 8 * ‖y - x‖ ≤
      ‖twoTimeAutonomousEndpoint y t δ -
        twoTimeAutonomousEndpoint x t δ‖ := by
  have hlower := norm_exp_sub_exp_lower_of_skewAdjoint
    x y hx hy hδ hsmallx hsmallxy
  have hupper := norm_increment_sub_increment_le_two_mul_twoTimeEndpoint
    x y hx hy t δ
  nlinarith [norm_nonneg (y - x)]

end

end GaloisForLFunctions.HTGeometry
