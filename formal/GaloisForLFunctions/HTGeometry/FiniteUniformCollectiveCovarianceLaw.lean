import GaloisForLFunctions.HTGeometry.CollectiveReplicaOperatorCovarianceLaw

/-!
# Uniform directional collective covariance

The collective-replica row law is converted here into a normalized bound
for every vector in the ordered replica Hilbert space.  The estimate is
dimension-sharp at the coefficient level: one inverse copy of the ordered
replica dimension, multiplied only by the factorial sheet count and the
intrinsic near-action crowding degree.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def finiteUniformDirectionalWeight
    {I : Type*} [Fintype I]
    (target : EuclideanSpace ℂ I) (i : I) : ℝ :=
  (Real.sqrt (Fintype.card I : ℝ))⁻¹ * ‖target i‖

def finiteUniformDirectionalTwist
    {I : Type*} [Fintype I]
    (target : EuclideanSpace ℂ I) (i : I) : ℂ :=
  if target i = 0 then 1 else target i / (‖target i‖ : ℂ)

theorem norm_finiteUniformDirectionalTwist
    {I : Type*} [Fintype I]
    (target : EuclideanSpace ℂ I) (i : I) :
    ‖finiteUniformDirectionalTwist target i‖ = 1 := by
  unfold finiteUniformDirectionalTwist
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr h)

theorem finiteUniformDirectionalWeight_nonneg
    {I : Type*} [Fintype I]
    (target : EuclideanSpace ℂ I) (i : I) :
    0 ≤ finiteUniformDirectionalWeight target i := by
  unfold finiteUniformDirectionalWeight
  positivity

theorem sum_finiteUniformDirectionalWeight_le_one
    {I : Type*} [Fintype I] [Nonempty I]
    {target : EuclideanSpace ℂ I} (htarget : ‖target‖ ≤ 1) :
    ∑ i, finiteUniformDirectionalWeight target i ≤ 1 := by
  have hcardR : 0 < (Fintype.card I : ℝ) := by positivity
  have hsqrtPos : 0 < Real.sqrt (Fintype.card I : ℝ) := Real.sqrt_pos.2 hcardR
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset I) (fun _ => (1 : ℝ)) (fun i => ‖target i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcs
  have hrootNorm : Real.sqrt (∑ i : I, ‖target i‖ ^ 2) ≤ 1 := by
    rw [← EuclideanSpace.norm_sq_eq target,
      Real.sqrt_sq (norm_nonneg target)]
    exact htarget
  have hsumNorm : ∑ i : I, ‖target i‖ ≤
      Real.sqrt (Fintype.card I : ℝ) := by
    calc
      ∑ i : I, ‖target i‖ ≤
          Real.sqrt (Fintype.card I : ℝ) *
            Real.sqrt (∑ i : I, ‖target i‖ ^ 2) := hcs
      _ ≤ Real.sqrt (Fintype.card I : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hrootNorm hsqrtPos.le
      _ = Real.sqrt (Fintype.card I : ℝ) := mul_one _
  calc
    ∑ i, finiteUniformDirectionalWeight target i =
        (Real.sqrt (Fintype.card I : ℝ))⁻¹ * ∑ i, ‖target i‖ := by
      unfold finiteUniformDirectionalWeight
      rw [Finset.mul_sum]
    _ ≤ (Real.sqrt (Fintype.card I : ℝ))⁻¹ *
        Real.sqrt (Fintype.card I : ℝ) :=
      mul_le_mul_of_nonneg_left hsumNorm (inv_nonneg.mpr hsqrtPos.le)
    _ = 1 := inv_mul_cancel₀ hsqrtPos.ne'

theorem sum_sq_finiteUniformDirectionalWeight_le_inv
    {I : Type*} [Fintype I] [Nonempty I]
    {target : EuclideanSpace ℂ I} (htarget : ‖target‖ ≤ 1) :
    ∑ i, finiteUniformDirectionalWeight target i ^ 2 ≤
      (Fintype.card I : ℝ)⁻¹ := by
  have hcardR : 0 < (Fintype.card I : ℝ) := by positivity
  calc
    ∑ i, finiteUniformDirectionalWeight target i ^ 2 =
        (Real.sqrt (Fintype.card I : ℝ))⁻¹ ^ 2 *
          ∑ i, ‖target i‖ ^ 2 := by
      unfold finiteUniformDirectionalWeight
      simp_rw [mul_pow, ← Finset.mul_sum]
    _ ≤ (Real.sqrt (Fintype.card I : ℝ))⁻¹ ^ 2 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [← EuclideanSpace.norm_sq_eq target]
      nlinarith [norm_nonneg target]
    _ = (Fintype.card I : ℝ)⁻¹ := by
      rw [mul_one, inv_pow, Real.sq_sqrt hcardR.le]

/-- **Uniform directional collective covariance.**  For every vector in the
closed unit ball of the ordered replica space, the Gaussian directional
moment is at most `r! (1 + crowding) / card(I)^r`, plus the resolved-action
tail. -/
theorem norm_twistedGaussian_collectiveUniformDirection_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {energy : I → ℝ} (henergy : MaximallyProjectiveEnergy energy)
    {r : ℕ} (target : EuclideanSpace ℂ (Fin r → I))
    (htarget : ‖target‖ ≤ 1)
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean
        (finiteUniformDirectionalWeight target)
        (collectiveReplicaEnergy energy)
        (finiteUniformDirectionalTwist target) 1 T‖ ≤
      (r.factorial : ℝ) *
          (1 + replicaActionCrowdingDegree energy r δ) *
          (Fintype.card I : ℝ)⁻¹ ^ r +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  have hbase := norm_twistedGaussian_collectiveReplicaMean_one_le henergy
    (finiteUniformDirectionalWeight_nonneg target)
    (sum_finiteUniformDirectionalWeight_le_one htarget)
    (norm_finiteUniformDirectionalTwist target) hT hδ
  have hsquare := sum_sq_finiteUniformDirectionalWeight_le_inv htarget
  have hfactor : 0 ≤ (r.factorial : ℝ) *
      (1 + replicaActionCrowdingDegree energy r δ) := by positivity
  calc
    _ ≤ (r.factorial : ℝ) *
          (1 + replicaActionCrowdingDegree energy r δ) *
          ∑ α, finiteUniformDirectionalWeight target α ^ 2 +
        Real.exp (-((T * δ) ^ 2) / 2) := hbase
    _ ≤ (r.factorial : ℝ) *
          (1 + replicaActionCrowdingDegree energy r δ) *
          (Fintype.card (Fin r → I) : ℝ)⁻¹ +
        Real.exp (-((T * δ) ^ 2) / 2) := by gcongr
    _ = _ := by
      rw [Fintype.card_fun, Fintype.card_fin]
      push_cast
      rw [inv_pow]

end

end GaloisForLFunctions.HTGeometry
