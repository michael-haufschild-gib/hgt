import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# Finite-window resolution of replica collisions

The completed replica-collision mass is approached at a rate controlled
exactly by the smallest retained nonzero replica detuning. For nonnegative
normalized spectral weights, the error constant is one at every replica
order and in every finite dimension.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The absolute sinc reporter never exceeds one. -/
theorem abs_real_sinc_le_one (x : ℝ) :
    |Real.sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx, abs_div]
    exact (div_le_one (abs_pos.mpr hx)).2
      Real.abs_sin_le_abs

/-- Away from zero, absolute sinc is bounded by inverse distance. -/
theorem abs_real_sinc_le_inv_abs {x : ℝ} (hx : x ≠ 0) :
    |Real.sinc x| ≤ |x|⁻¹ := by
  rw [Real.sinc_of_ne_zero hx, abs_div]
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg x))
    (Real.abs_sin_le_one x)

/-- A detuning separated from zero by `δ` contributes at most
`min 1 (T * δ)⁻¹` to the symmetric-window reporter. -/
theorem norm_symmetricPhaseAverage_le_min_inv
    {T δ detuning : ℝ}
    (hT : 0 < T) (hδ : 0 < δ)
    (hdetuning : δ ≤ |detuning|) :
    ‖symmetricPhaseAverage T detuning‖ ≤
      min 1 (T * δ)⁻¹ := by
  rw [symmetricPhaseAverage_eq_sinc T detuning hT.ne',
    Complex.norm_real, Real.norm_eq_abs]
  apply le_min
  · exact abs_real_sinc_le_one _
  · have hdetuning_ne : detuning ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hdetuning
      linarith
    have hprod_ne : T * detuning ≠ 0 :=
      mul_ne_zero hT.ne' hdetuning_ne
    calc
      |Real.sinc (T * detuning)| ≤ |T * detuning|⁻¹ :=
        abs_real_sinc_le_inv_abs hprod_ne
      _ ≤ (T * δ)⁻¹ := by
        rw [abs_mul, abs_of_pos hT]
        exact
          (inv_le_inv₀
            (mul_pos hT (abs_pos.mpr hdetuning_ne))
            (mul_pos hT hδ)).2
            (mul_le_mul_of_nonneg_left hdetuning hT.le)

/-- For normalized spectral weights, all bivariate replica coefficients
sum to one at every order. -/
theorem sum_fidelityReplicaMultiplicityWeight_eq_one
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ)
    (hweightSum : ∑ i, weight i = 1) :
    (∑ p ∈ Finset.univ.piAntidiag n,
      ∑ q ∈ Finset.univ.piAntidiag n,
        fidelityReplicaMultiplicityWeight weight p q) = 1 := by
  classical
  have h :=
    complexFidelityReplicaMultiplicityExpansion
      weight (fun _ => 1) (fun _ => 1) n
  simp only [mul_one, one_pow, Finset.prod_const_one] at h
  rw [show (∑ i, (weight i : ℂ)) = 1 by
    exact_mod_cast hweightSum] at h
  norm_num at h
  exact_mod_cast h.symm

/-- Replica multiplicity weights remain nonnegative for nonnegative,
not necessarily full-support, spectral weights. -/
theorem fidelityReplicaMultiplicityWeight_nonneg
    {I : Type*} [Fintype I]
    {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (p q : I → ℕ) :
    0 ≤ fidelityReplicaMultiplicityWeight weight p q := by
  unfold fidelityReplicaMultiplicityWeight
  have hpMult : 0 ≤ (Nat.multinomial Finset.univ p : ℝ) := by
    positivity
  have hqMult : 0 ≤ (Nat.multinomial Finset.univ q : ℝ) := by
    positivity
  have hpWeight : 0 ≤ ∏ i, weight i ^ p i :=
    Finset.prod_nonneg fun i hi => pow_nonneg (hweight i) _
  have hqWeight : 0 ≤ ∏ i, weight i ^ q i :=
    Finset.prod_nonneg fun i hi => pow_nonneg (hweight i) _
  positivity

/-- Sum of exactly the nonresonant finite-window replica reporters. -/
def fidelityReplicaFiniteWindowRemainder
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) (T : ℝ) : ℂ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if replicaMultiplicityEnergy energy p =
          replicaMultiplicityEnergy energy q
      then 0
      else
        (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
          symmetricPhaseAverage T
            (replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q)

/-- Exact decomposition into completed collision mass and finite-window
nonresonant remainder. -/
theorem finiteSpectralSurvivalFidelityMean_eq_collisionMass_add_remainder
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ)
    {T : ℝ} (hT : T ≠ 0) :
    finiteSpectralSurvivalFidelityMean weight energy n T =
      (fidelityReplicaCollisionMass weight energy n : ℂ) +
        fidelityReplicaFiniteWindowRemainder weight energy n T := by
  classical
  rw [finiteSpectralSurvivalFidelityMean_eq_replicaPhaseAverage,
    ← fidelityReplicaResonantMass_eq_collisionMass]
  unfold fidelityReplicaResonantMass
    fidelityReplicaFiniteWindowRemainder
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases heq :
      replicaMultiplicityEnergy energy p =
        replicaMultiplicityEnergy energy q
  · simp [heq, symmetricPhaseAverage_eq_sinc T 0 hT]
  · simp [heq]

/-- The nonresonant remainder is bounded by the inverse replica-detuning
resolution scale, with unit constant independent of dimension and order. -/
theorem norm_fidelityReplicaFiniteWindowRemainder_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (n : ℕ) {T δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ)
    (hgap :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            δ ≤
              |replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q|) :
    ‖fidelityReplicaFiniteWindowRemainder
        weight energy n T‖ ≤
      min 1 (T * δ)⁻¹ := by
  classical
  let B : ℝ := min 1 (T * δ)⁻¹
  have hBnonneg : 0 ≤ B := by
    unfold B
    positivity
  have htotal :
      (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          fidelityReplicaMultiplicityWeight weight p q) = 1 :=
    sum_fidelityReplicaMultiplicityWeight_eq_one
      weight n hweightSum
  unfold fidelityReplicaFiniteWindowRemainder
  calc
    ‖∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          if replicaMultiplicityEnergy energy p =
              replicaMultiplicityEnergy energy q
          then 0
          else
            (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
              symmetricPhaseAverage T
                (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q)‖
        ≤ ∑ p ∈ Finset.univ.piAntidiag n,
            ‖∑ q ∈ Finset.univ.piAntidiag n,
              if replicaMultiplicityEnergy energy p =
                  replicaMultiplicityEnergy energy q
              then 0
              else
                (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
                  symmetricPhaseAverage T
                    (replicaMultiplicityEnergy energy p -
                      replicaMultiplicityEnergy energy q)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            ‖if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
              then 0
              else
                (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
                  symmetricPhaseAverage T
                    (replicaMultiplicityEnergy energy p -
                      replicaMultiplicityEnergy energy q)‖ := by
          apply Finset.sum_le_sum
          intro p hp
          exact norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            fidelityReplicaMultiplicityWeight weight p q * B := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          by_cases heq :
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          · simpa [heq] using
              mul_nonneg
                (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
                hBnonneg
          · rw [if_neg heq, norm_mul, Complex.norm_real,
              Real.norm_eq_abs,
              abs_of_nonneg
                (fidelityReplicaMultiplicityWeight_nonneg
                  hweight p q)]
            exact mul_le_mul_of_nonneg_left
              (norm_symmetricPhaseAverage_le_min_inv
                hT hδ (hgap p hp q hq heq))
              (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
    _ = B := by
          simp_rw [← Finset.sum_mul]
          rw [htotal, one_mul]
    _ = min 1 (T * δ)⁻¹ := rfl

/-- **Finite-window collision certificate.** For normalized nonnegative
spectral weights, any positive lower bound `δ` on nonzero order-`n`
detunings controls the normalized symmetric-window error by
`min 1 (T * δ)⁻¹`. -/
theorem norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (n : ℕ) {T δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ)
    (hgap :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            δ ≤
              |replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q|) :
    ‖finiteSpectralSurvivalFidelityMean weight energy n T -
        (fidelityReplicaCollisionMass weight energy n : ℂ)‖ ≤
      min 1 (T * δ)⁻¹ := by
  rw [finiteSpectralSurvivalFidelityMean_eq_collisionMass_add_remainder
    weight energy n hT.ne', add_sub_cancel_left]
  exact norm_fidelityReplicaFiniteWindowRemainder_le
    hweight hweightSum n hT hδ hgap

end

end GaloisForLFunctions.HTGeometry
