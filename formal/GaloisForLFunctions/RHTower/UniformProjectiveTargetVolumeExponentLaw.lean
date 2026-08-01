import GaloisForLFunctions.RHTower.ProjectiveWeightedTargetVolumeLower

/-!
# Sharp equal-weight projective recurrence-volume exponent

For a uniform packet of `d` phases, both Haar-volume bounds for the
high-fidelity projective recurrence target have the same exponent
`(d - 1) / 2`. This is the exact projective temporal dimension divided by
two; no dimension-linear remainder appears in the exponent.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

def uniformProjectiveWeight (d : ℕ) : Fin d → ℝ :=
  fun _ ↦ (d : ℝ)⁻¹

/-- Common reciprocal scale of every nonpivot coordinate. -/
def uniformProjectiveWaterScale (d : ℕ) (η : ℝ) : ℝ :=
  (d - 1 : ℕ) / ((d : ℝ) * η)

theorem sum_ite_zero_else_eq_card_sub_one_mul
    {d : ℕ} (k : Fin d) (a : ℝ) :
    (∑ j : Fin d, if j = k then 0 else a) = (d - 1 : ℕ) * a := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr fun hd0 ↦ by
    subst d
    exact Fin.elim0 k
  calc
    (∑ j : Fin d, if j = k then 0 else a) =
        (∑ j : Fin d, a) - ∑ j, if j = k then a else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j = k <;> simp [hj]
    _ = (d : ℝ) * a - a := by simp
    _ = (d - 1 : ℕ) * a := by
      rw [Nat.cast_sub hd]
      ring

theorem uniformProjectiveWeight_nonneg (d : ℕ) :
    ∀ i, 0 ≤ uniformProjectiveWeight d i := by
  intro i
  simp [uniformProjectiveWeight]

theorem uniformProjectiveWeight_sum {d : ℕ} (hd : 0 < d) :
    ∑ i, uniformProjectiveWeight d i = 1 := by
  simp [uniformProjectiveWeight]
  field_simp

theorem uniformProjectiveWaterScale_ge_one
    {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η)
    (hηmax : η ≤ (d - 1 : ℕ) / (d : ℝ)) :
    1 ≤ uniformProjectiveWaterScale d η := by
  rw [uniformProjectiveWaterScale]
  have hdreal : (0 : ℝ) < d := by positivity
  rw [le_div_iff₀ (mul_pos hdreal hη)]
  calc
    1 * ((d : ℝ) * η) ≤
        (d : ℝ) * ((d - 1 : ℕ) / (d : ℝ)) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_left hηmax hdreal.le
    _ = (d - 1 : ℕ) := by field_simp

theorem uniformProjectiveWaterScale_feasible
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d)
    {η : ℝ} (hη : 0 < η)
    (hηmax : η ≤ (d - 1 : ℕ) / (d : ℝ)) :
    ProjectiveWaterFeasible (uniformProjectiveWeight d) k η
      (fun _ ↦ uniformProjectiveWaterScale d η) := by
  have hx := uniformProjectiveWaterScale_ge_one hd hη hηmax
  refine ⟨fun _ ↦ hx, ?_⟩
  have hdreal : (0 : ℝ) < d := by positivity
  rw [show (∑ j : Fin d, if j = k then 0 else
      uniformProjectiveWeight d j / uniformProjectiveWaterScale d η) =
        (d - 1 : ℕ) * ((d : ℝ)⁻¹ /
          uniformProjectiveWaterScale d η) by
    simpa only [uniformProjectiveWeight] using
      sum_ite_zero_else_eq_card_sub_one_mul k
        ((d : ℝ)⁻¹ / uniformProjectiveWaterScale d η)]
  rw [uniformProjectiveWaterScale]
  have hdm1nat : 0 < d - 1 := Nat.sub_pos_of_lt (by omega)
  have hdm1 : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast hdm1nat
  field_simp [hdreal.ne', hdm1.ne', hη.ne']
  norm_num

theorem uniformProjectiveWaterEntropyAt
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d)
    {η : ℝ} (hη : 0 < η)
    (hηmax : η ≤ (d - 1 : ℕ) / (d : ℝ)) :
    projectiveWaterEntropyAt (uniformProjectiveWeight d) k
        ((d - 1 : ℕ) / η) =
      (1 / 2 : ℝ) * (d - 1 : ℕ) *
        Real.log (uniformProjectiveWaterScale d η) := by
  have hx := uniformProjectiveWaterScale_ge_one hd hη hηmax
  rw [projectiveWaterEntropyAt]
  have hinside : ((d - 1 : ℕ) / η) *
      uniformProjectiveWeight d k = uniformProjectiveWaterScale d η := by
    rw [uniformProjectiveWeight, uniformProjectiveWaterScale]
    field_simp
  simp_rw [show ∀ j : Fin d,
      ((d - 1 : ℕ) / η) * uniformProjectiveWeight d j =
        uniformProjectiveWaterScale d η by
    intro j
    simpa only [uniformProjectiveWeight] using hinside]
  rw [max_eq_right hx]
  rw [sum_ite_zero_else_eq_card_sub_one_mul]
  ring

/-- **Sharp uniform target-volume exponent.** Both Haar-volume bounds have
the same half-dimensional logarithmic term. -/
theorem uniformProjectiveCoherenceTarget_volume_bounds
    {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η)
    (hηmax : η ≤ (d - 1 : ℕ) / (d : ℝ)) :
    (Real.sqrt (2 / uniformProjectiveWaterScale d η) /
        Real.pi) ^ (d - 1) ≤
      volume.real
        (torusProjectiveWeightedCoherenceTarget
          (uniformProjectiveWeight d) η) ∧
    volume.real
        (torusProjectiveWeightedCoherenceTarget
          (uniformProjectiveWeight d) η) ≤
      (d : ℝ) * Real.exp (
        (Real.pi / 4) * (d - 1 : ℕ) -
          (1 / 2 : ℝ) * (d - 1 : ℕ) *
            Real.log (uniformProjectiveWaterScale d η)) := by
  let k : Fin d := ⟨0, by omega⟩
  let x : Fin d → ℝ := fun _ ↦ uniformProjectiveWaterScale d η
  have hw := uniformProjectiveWeight_nonneg d
  have hmass := uniformProjectiveWeight_sum (by omega : 0 < d)
  have hxge := uniformProjectiveWaterScale_ge_one hd hη hηmax
  have hfeasible := uniformProjectiveWaterScale_feasible hd k hη hηmax
  have hlower := projectiveWaterProduct_le_volumeReal_coherenceTarget
    (uniformProjectiveWeight d) k x hw hmass (fun _ ↦ hxge)
      hfeasible.2
  have hlower' :
      (Real.sqrt (2 / uniformProjectiveWaterScale d η) /
          Real.pi) ^ (d - 1) ≤
        volume.real
          (torusProjectiveWeightedCoherenceTarget
            (uniformProjectiveWeight d) η) := by
    rw [← prod_one_except_eq_pow_card_sub_one k]
    simpa [x] using hlower
  have hdreal : (0 : ℝ) < d := by positivity
  have hdm1nat : 0 < d - 1 := Nat.sub_pos_of_lt (by omega)
  have hdm1 : (0 : ℝ) < (d - 1 : ℕ) := by exact_mod_cast hdm1nat
  have hη1 : η ≤ 1 := hηmax.trans <| by
    apply (div_le_one hdreal).2
    exact_mod_cast (Nat.sub_le d 1)
  let lam : Fin d → ℝ := fun _ ↦ (d - 1 : ℕ) / η
  have hlam : ∀ j, 0 < lam j := by
    intro j
    exact div_pos hdm1 hη
  have hbudget : ∀ j, lam j * η ≤ (d - 1 : ℕ) := by
    intro j
    dsimp only [lam]
    rw [div_mul_cancel₀ _ hη.ne']
  have hentropy : ∀ j,
      (1 / 2 : ℝ) * (d - 1 : ℕ) *
          Real.log (uniformProjectiveWaterScale d η) ≤
        projectiveWaterEntropyAt (uniformProjectiveWeight d) j (lam j) := by
    intro j
    rw [uniformProjectiveWaterEntropyAt hd j hη hηmax]
  have hupper :=
    measureReal_torusProjectiveWeightedCoherenceTarget_waterEntropy_le
      (uniformProjectiveWeight d) hw hmass hη1 lam hlam hbudget hentropy
  exact ⟨hlower', hupper⟩

end

end RHTower
