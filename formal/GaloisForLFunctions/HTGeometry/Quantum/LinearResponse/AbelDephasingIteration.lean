import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelDephasingChannel
import Mathlib.Data.NNReal.Basic

/-!
# Exact leakage under repeated Abel averaging

Every iteration multiplies one energy transition by its complex Cauchy
coefficient. The sharp squared Hilbert--Schmidt contraction on the
nonstationary part is the largest squared coefficient among nonzero
Bohr frequencies. A single matrix unit witnesses this constant.
-/

open Filter Matrix Set
open scoped Matrix NNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

theorem energyCoordinates_iterate_abelDephasing_apply
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (i j : Fin n) :
    hamiltonianEnergyCoordinates hH (((hamiltonianDampedGapResponse hH 0 ε)^[m]) X) i j =
      (abelCoherence ε (hamiltonianGap hH i j)) ^ m * hamiltonianEnergyCoordinates hH X i j := by
  induction m with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ m hm =>
    rw [Function.iterate_succ_apply', energyCoordinates_dampedGapResponse_apply_coherence,
      sub_zero, hm, pow_succ', mul_assoc]

/-- After any number of applications, the squared leakage is the sum of
the original nonstationary transition intensities times the corresponding
powers of the squared attenuation. -/
theorem hsSqRe_iterate_abelDephasing_sub
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    hsSqRe (((hamiltonianDampedGapResponse hH 0 ε)^[m]) X - hamiltonianGapComponent hH 0 X) =
      ∑ i, ∑ j, if hamiltonianGap hH i j = 0 then 0 else
        (‖abelCoherence ε (hamiltonianGap hH i j)‖ ^ 2) ^ m *
          ‖hamiltonianEnergyCoordinates hH X i j‖ ^ 2 := by
  rw [hsSqRe_eq_sum_energyCoordinates hH]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_sub, Matrix.sub_apply, energyCoordinates_iterate_abelDephasing_apply,
    energyCoordinates_gapComponent_apply]
  by_cases hg : hamiltonianGap hH i j = 0
  · simp only [hg, if_true, abelCoherence_zero, one_pow, one_mul, sub_self, norm_zero,
      zero_pow two_ne_zero]
  · simp only [hg, if_false, sub_zero, norm_mul, norm_pow, mul_pow]
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul]

private theorem norm_sq_abelCoherence_lt_one (ε : Ioi (0 : ℝ)) {g : ℝ} (hg : g ≠ 0) :
    ‖abelCoherence ε g‖ ^ 2 < 1 := by
  have hε : 0 < (ε : ℝ) := ε.2
  have hg2 := sq_pos_of_ne_zero hg
  rw [norm_sq_abelCoherence, div_lt_iff₀ (add_pos (sq_pos_of_ne_zero hε.ne') hg2), one_mul]
  exact lt_add_of_pos_right _ hg2

private def abelLeakageFactor (ε : Ioi (0 : ℝ)) (g : ℝ) : ℝ≥0 :=
  if g = 0 then 0 else ⟨‖abelCoherence ε g‖ ^ 2, sq_nonneg _⟩

/-- Largest squared attenuation of an off-resonant transition. The empty
set of off-resonant transitions gives zero. -/
def abelMaxLeakage (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) : ℝ≥0 :=
  (Finset.univ : Finset (Fin n × Fin n)).sup
    (fun p => abelLeakageFactor ε (hamiltonianGap hH p.1 p.2))

theorem abelMaxLeakage_lt_one (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) :
    abelMaxLeakage hH ε < 1 := by
  unfold abelMaxLeakage
  refine (Finset.sup_lt_iff (show (⊥ : ℝ≥0) < 1 from zero_lt_one)).mpr ?_
  rintro ⟨i, j⟩ _
  by_cases hg : hamiltonianGap hH i j = 0
  · rw [abelLeakageFactor, if_pos hg]
    exact zero_lt_one
  · rw [abelLeakageFactor, if_neg hg]
    apply NNReal.coe_lt_coe.mp
    rw [NNReal.coe_one]
    exact norm_sq_abelCoherence_lt_one ε hg

theorem hsSqRe_iterate_abelDephasing_sub_le
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    hsSqRe (((hamiltonianDampedGapResponse hH 0 ε)^[m]) X - hamiltonianGapComponent hH 0 X) ≤
      (abelMaxLeakage hH ε : ℝ) ^ m * hsSqRe (X - hamiltonianGapComponent hH 0 X) := by
  have hzero := hsSqRe_iterate_abelDephasing_sub hH ε X 0
  simp only [Function.iterate_zero_apply, pow_zero, one_mul] at hzero
  rw [hsSqRe_iterate_abelDephasing_sub hH ε X m, hzero, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hg : hamiltonianGap hH i j = 0
  · simp only [hg, if_true, mul_zero, le_refl]
  · have hb : abelLeakageFactor ε (hamiltonianGap hH i j) ≤ abelMaxLeakage hH ε :=
      Finset.le_sup
        (f := fun p : Fin n × Fin n => abelLeakageFactor ε (hamiltonianGap hH p.1 p.2))
        (Finset.mem_univ (i, j))
    have hc : ‖abelCoherence ε (hamiltonianGap hH i j)‖ ^ 2 ≤ (abelMaxLeakage hH ε : ℝ) := by
      rw [abelLeakageFactor, if_neg hg] at hb
      exact NNReal.coe_le_coe.mpr hb
    rw [if_neg hg, if_neg hg]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) hc m) (sq_nonneg _)

private theorem hsSqRe_iterate_abelDephasing_sub_matrixUnit
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (m : ℕ) (i j : Fin n) :
    let X := (hamiltonianEnergyCoordinates hH).symm (Matrix.single i j (1 : ℂ))
    hsSqRe (((hamiltonianDampedGapResponse hH 0 ε)^[m]) X - hamiltonianGapComponent hH 0 X) =
      if hamiltonianGap hH i j = 0 then 0 else (‖abelCoherence ε (hamiltonianGap hH i j)‖ ^ 2) ^ m := by
  dsimp only
  rw [hsSqRe_iterate_abelDephasing_sub]
  simp only [StarAlgEquiv.apply_symm_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Matrix.single_apply_same]
    · intro b _ hb
      simp [Matrix.single_apply_of_col_ne i i (Ne.symm hb)]
    · exact fun h => (h (Finset.mem_univ j)).elim
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by
      simp [Matrix.single_apply_of_row_ne (Ne.symm ha)]
  · exact fun h => (h (Finset.mem_univ i)).elim

/-- The worst one-step squared leakage is the least uniform constant
in the contraction inequality on the nonstationary part. -/
theorem abelMaxLeakage_optimal (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (r : ℝ≥0) :
    (∀ X : Matrix (Fin n) (Fin n) ℂ,
      hsSqRe (((hamiltonianDampedGapResponse hH 0 ε)^[1]) X - hamiltonianGapComponent hH 0 X) ≤
        (r : ℝ) * hsSqRe (X - hamiltonianGapComponent hH 0 X)) ↔ abelMaxLeakage hH ε ≤ r := by
  constructor
  · intro h
    unfold abelMaxLeakage
    refine Finset.sup_le ?_
    rintro ⟨i, j⟩ _
    by_cases hg : hamiltonianGap hH i j = 0
    · rw [abelLeakageFactor, if_pos hg]
      exact zero_le
    · let X := (hamiltonianEnergyCoordinates hH).symm (Matrix.single i j (1 : ℂ))
      have h₁ := hsSqRe_iterate_abelDephasing_sub_matrixUnit hH ε 1 i j
      have h₀ := hsSqRe_iterate_abelDephasing_sub_matrixUnit hH ε 0 i j
      change hsSqRe (((hamiltonianDampedGapResponse hH 0 ε)^[1]) X -
        hamiltonianGapComponent hH 0 X) = _ at h₁
      change hsSqRe (X - hamiltonianGapComponent hH 0 X) = _ at h₀
      simp only [if_neg hg, pow_one] at h₁
      simp only [if_neg hg, pow_zero] at h₀
      have hx := h X
      rw [h₁, h₀, mul_one] at hx
      rw [abelLeakageFactor, if_neg hg]
      exact NNReal.coe_le_coe.mp hx
  · intro h X
    have hX := hsSqRe_iterate_abelDephasing_sub_le hH ε X 1
    rw [pow_one] at hX
    exact hX.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr h) (hsSqRe_nonneg _))

/-- Iterating the zero-centered filter converges to the full
energy-block pinching, with all degenerate blocks retained. -/
theorem tendsto_iterate_abelDephasing
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun m : ℕ => ((hamiltonianDampedGapResponse hH 0 ε)^[m]) X) atTop
      (𝓝 (hamiltonianGapComponent hH 0 X)) := by
  have hc : Tendsto (fun m : ℕ =>
      hamiltonianEnergyCoordinates hH (((hamiltonianDampedGapResponse hH 0 ε)^[m]) X))
      atTop (𝓝 (hamiltonianEnergyCoordinates hH (hamiltonianGapComponent hH 0 X))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hg : hamiltonianGap hH i j = 0
    · simp only [energyCoordinates_iterate_abelDephasing_apply, energyCoordinates_gapComponent_apply,
        hg, if_true, abelCoherence_zero, one_pow, one_mul]
      exact tendsto_const_nhds
    · have hnorm : ‖abelCoherence ε (hamiltonianGap hH i j)‖ < 1 := by
        have hsq := norm_sq_abelCoherence_lt_one ε hg
        nlinarith only [hsq, norm_nonneg (abelCoherence ε (hamiltonianGap hH i j))]
      simpa only [energyCoordinates_iterate_abelDephasing_apply, energyCoordinates_gapComponent_apply,
        if_neg hg, zero_mul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm).mul_const
          (hamiltonianEnergyCoordinates hH X i j)
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  have hcont : Continuous (fun Y : Matrix (Fin n) (Fin n) ℂ => (hamiltonianEnergyCoordinates hH).symm Y) := by
    change Continuous (fun Y : Matrix (Fin n) (Fin n) ℂ => U * Y * star U)
    exact (continuous_const.mul continuous_id).mul continuous_const
  simpa only [Function.comp_def, StarAlgEquiv.symm_apply_apply] using hcont.continuousAt.tendsto.comp hc

#print axioms hsSqRe_iterate_abelDephasing_sub
#print axioms abelMaxLeakage_optimal
#print axioms tendsto_iterate_abelDephasing

end

end GaloisForLFunctions.HTGeometry
