import GaloisForLFunctions.RHTower.ResidualReplicaOptimalDesignTransportLaw
import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignWeightedCrowdingFirstReturnLaw

/-!
# Subunit static-Choi weighted crowding

Gaussian replica moment bounds extend from normalized endpoints to the closed
unit ball. This is the natural regime for unnormalized return-orthogonal
residuals and preserves the exact weighted near-action term.
-/

open scoped BigOperators Matrix ComplexConjugate
open Set MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

theorem sum_norm_sq_staticChoiTarget_diagonal_le_one_of_norm_le_one
    {d : ℕ} {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ ≤ 1) :
    ∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ) ≤ 1 := by
  let diag : Fin d → Fin d × Fin d := fun i => (i, i)
  have hdiag : Function.Injective diag := by
    intro i j h
    exact congrArg Prod.fst h
  calc
    ∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ) =
        ∑ i : Fin d, ‖target (diag i)‖ ^ (2 : ℕ) := rfl
    _ = ∑ ij ∈ Finset.univ.image diag, ‖target ij‖ ^ (2 : ℕ) := by
      rw [Finset.sum_image]
      exact hdiag.injOn
    _ ≤ ∑ ij : Fin d × Fin d, ‖target ij‖ ^ (2 : ℕ) :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    _ = ‖target‖ ^ (2 : ℕ) := (EuclideanSpace.norm_sq_eq target).symm
    _ ≤ 1 := by nlinarith [norm_nonneg target]

theorem sum_directStaticChoiTargetWeight_le_one_of_norm_le_one
    {d : ℕ} (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ ≤ 1) :
    ∑ i, directStaticChoiTargetWeight d target i ≤ 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrtPos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hmass := sum_norm_sq_staticChoiTarget_diagonal_le_one_of_norm_le_one htarget
  have hmassNonneg : 0 ≤ ∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hrootMass : Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ)) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using hmass⟩
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ))
      (fun i => ‖target (i, i)‖)
  simp only [one_mul, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hsumNorm : ∑ i : Fin d, ‖target (i, i)‖ ≤ Real.sqrt (d : ℝ) := by
    calc
      ∑ i : Fin d, ‖target (i, i)‖ ≤
          Real.sqrt (d : ℝ) *
            Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ (2 : ℕ)) := hcs
      _ ≤ Real.sqrt (d : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hrootMass hsqrtPos.le
      _ = Real.sqrt (d : ℝ) := mul_one _
  calc
    ∑ i, directStaticChoiTargetWeight d target i =
        (Real.sqrt (d : ℝ))⁻¹ * ∑ i, ‖target (i, i)‖ := by
      unfold directStaticChoiTargetWeight
      rw [Finset.mul_sum]
    _ ≤ (Real.sqrt (d : ℝ))⁻¹ * Real.sqrt (d : ℝ) :=
      mul_le_mul_of_nonneg_left hsumNorm (inv_nonneg.mpr hsqrtPos.le)
    _ = 1 := inv_mul_cancel₀ hsqrtPos.ne'

theorem sum_sq_directStaticChoiTargetWeight_le_inv_of_norm_le_one
    {d : ℕ} (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ ≤ 1) :
    ∑ i, directStaticChoiTargetWeight d target i ^ (2 : ℕ) ≤ (d : ℝ)⁻¹ := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmass := sum_norm_sq_staticChoiTarget_diagonal_le_one_of_norm_le_one htarget
  calc
    ∑ i, directStaticChoiTargetWeight d target i ^ (2 : ℕ) =
        (Real.sqrt (d : ℝ))⁻¹ ^ (2 : ℕ) *
          ∑ i, ‖target (i, i)‖ ^ (2 : ℕ) := by
      unfold directStaticChoiTargetWeight
      simp_rw [mul_pow, ← Finset.mul_sum]
    _ ≤ (Real.sqrt (d : ℝ))⁻¹ ^ (2 : ℕ) * 1 :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ = (d : ℝ)⁻¹ := by
      rw [mul_one, inv_pow, Real.sq_sqrt hdR.le]

theorem directStaticChoiTarget_collision_le_factorial_inv_pow_of_norm_le_one
    {d : ℕ} (hd : 0 < d)
    {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ ≤ 1) (n : ℕ) :
    fidelityReplicaCollisionMass
        (directStaticChoiTargetWeight d target) (fun i => -energy i) n ≤
      (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n := by
  rw [fidelityReplicaCollisionMass_eq_floor_of_maximallyProjective
    (directStaticChoiTargetWeight d target) (fun i => -energy i) n
    (maximallyProjectiveEnergy_neg hmax)]
  exact (fidelityReplicaPermutationFloor_le_factorial_mul_sum_sq_pow
    (directStaticChoiTargetWeight_nonneg target) n).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity)
          (sum_sq_directStaticChoiTargetWeight_le_inv_of_norm_le_one hd htarget) n)
        (by positivity))

theorem integrable_staticChoi_fidelity_pow_of_norm_le_one
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (T : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ‖target‖ ≤ 1) (r : ℕ) (R : Set ℝ) :
    Integrable
      (fun x => finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r)
      ((gaussianReal 0 1).restrict R) := by
  have hcState := continuous_staticSpectralChoiVector_scaled hd energy T
  have hcInner : Continuous (fun x =>
      inner ℂ target (staticSpectralChoiVector d (T * x) energy)) :=
    Continuous.inner continuous_const hcState
  have hc : Continuous (fun x => finitePureStateFidelity
      (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r) := by
    simp_rw [finitePureStateFidelity_eq_norm_inner_sq]
    simp only [WithLp.toLp_ofLp]
    exact (hcInner.norm.pow 2).pow r
  apply Integrable.of_bound hc.aestronglyMeasurable 1
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sq_nonneg _) r)]
  have hinner : ‖inner ℂ target
      (staticSpectralChoiVector d (T * x) energy)‖ ≤ 1 := by
    calc
      _ ≤ ‖target‖ * ‖staticSpectralChoiVector d (T * x) energy‖ :=
        norm_inner_le_norm _ _
      _ = ‖target‖ := by rw [staticSpectralChoiVector_norm hd, mul_one]
      _ ≤ 1 := htarget
  have hsquare : ‖inner ℂ target
      (staticSpectralChoiVector d (T * x) energy)‖ ^ (2 : ℕ) ≤ 1 := by
    nlinarith [norm_nonneg (inner ℂ target
      (staticSpectralChoiVector d (T * x) energy))]
  simp only [finitePureStateFidelity_eq_norm_inner_sq, WithLp.toLp_ofLp]
  exact pow_le_one₀ (by positivity) hsquare

theorem integral_gaussian_staticChoi_fidelity_pow_le_weightedCrowding_of_norm_le_one
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ‖target‖ ≤ 1)
    (r : ℕ) {T delta : ℝ} (hT : 0 < T) (hdelta : 0 < delta) :
    (∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
      ∂gaussianReal 0 1) ≤
      (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        directStaticChoiTargetNearActionMass target energy r delta +
        Real.exp (-((T * delta) ^ (2 : ℕ)) / 2) := by
  let weight := directStaticChoiTargetWeight d target
  let negEnergy : Fin d → ℝ := fun i => -energy i
  let twist := directStaticChoiTargetTwist target
  have hmean :
      (((∫ x, finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
        ∂gaussianReal 0 1 : ℝ) : ℂ)) =
        twistedGaussianSpectralFidelityMean weight negEnergy twist r T := by
    unfold twistedGaussianSpectralFidelityMean
    have hInt : Integrable
        (fun x => finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r)
        (gaussianReal 0 1) := by
      simpa using
        (integrable_staticChoi_fidelity_pow_of_norm_le_one
          hd energy T target htarget r Set.univ)
    change Complex.ofRealCLM (∫ x, finitePureStateFidelity
        (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
      ∂gaussianReal 0 1) = _
    rw [← Complex.ofRealCLM.integral_comp_comm hInt]
    apply integral_congr_ae
    filter_upwards with x
    rw [← staticChoi_fidelity_eq_directTwistedFidelity
      (d := d) (T * x) energy target]
    norm_cast
  have hreal :
      (∫ x, finitePureStateFidelity
          (staticSpectralChoiVector d (T * x) energy).ofLp target.ofLp ^ r
        ∂gaussianReal 0 1) =
        (twistedGaussianSpectralFidelityMean weight negEnergy twist r T).re := by
    rw [← hmean]
    simp
  rw [hreal]
  calc
    _ ≤ ‖twistedGaussianSpectralFidelityMean weight negEnergy twist r T‖ :=
      Complex.re_le_norm _
    _ ≤ fidelityReplicaCollisionMass weight negEnergy r +
        fidelityReplicaNearActionMass weight negEnergy r delta +
        Real.exp (-((T * delta) ^ (2 : ℕ)) / 2) :=
      norm_twistedGaussianSpectralFidelityMean_le_collision_add_crowding
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one_of_norm_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) r hT hdelta
    _ ≤ (r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
        fidelityReplicaNearActionMass weight negEnergy r delta +
        Real.exp (-((T * delta) ^ (2 : ℕ)) / 2) := by
      gcongr
      exact directStaticChoiTarget_collision_le_factorial_inv_pow_of_norm_le_one
        hd hmax htarget r
    _ = _ := rfl

end RHTower
