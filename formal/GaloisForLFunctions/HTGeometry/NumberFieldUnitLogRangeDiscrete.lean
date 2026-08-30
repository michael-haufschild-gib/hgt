import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogDiscrete

/-!
# Discrete logarithmic-unit range

Local finiteness of bounded unit-log profiles gives a positive isolation radius at zero.  Additive
translation gives the same radius at every point of the logarithmic range, so the range carries its
actual induced discrete topology.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The bounded part of the logarithmic-unit range is finite. -/
theorem finite_range_numberFieldUnitLog_inter_norm_le (R : ℝ) :
    {x : (K →+* ℂ) → ℝ |
      x ∈ (numberFieldUnitLog (K := K)).range ∧ ‖x‖ ≤ R}.Finite := by
  have hfinite :=
    (finite_numberFieldUnits_of_log_norm_le (K := K) R).image
      numberFieldUnitLogEmbeddings
  refine hfinite.subset ?_
  rintro x ⟨⟨a, rfl⟩, ha⟩
  refine ⟨Additive.toMul a, ?_, rfl⟩
  exact ha

/-- Every bounded ball in the subtype of the logarithmic-unit range is finite. -/
theorem finite_numberFieldUnitLogRange_norm_le (R : ℝ) :
    {x : (numberFieldUnitLog (K := K)).range | ‖(x : (K →+* ℂ) → ℝ)‖ ≤ R}.Finite := by
  let S : Set ((K →+* ℂ) → ℝ) :=
    {x | x ∈ (numberFieldUnitLog (K := K)).range ∧ ‖x‖ ≤ R}
  have hS : S.Finite := finite_range_numberFieldUnitLog_inter_norm_le R
  have hpre :
      ((fun x : (numberFieldUnitLog (K := K)).range =>
          (x : (K →+* ℂ) → ℝ)) ⁻¹' S).Finite :=
    hS.preimage Subtype.coe_injective.injOn
  refine hpre.subset ?_
  intro x hx
  exact ⟨x.2, hx⟩

/-- The logarithmic-unit range inherits the discrete topology. -/
noncomputable instance numberFieldUnitLogRange.discreteTopology :
    DiscreteTopology (numberFieldUnitLog (K := K)).range := by
  let L := (numberFieldUnitLog (K := K)).range
  let T : Set L := {x | ‖(x : (K →+* ℂ) → ℝ)‖ ≤ 1 ∧ x ≠ 0}
  have hTfinite : T.Finite :=
    (finite_numberFieldUnitLogRange_norm_le (K := K) 1).subset fun _ hx => hx.1
  by_cases hTnonempty : T.Nonempty
  · rcases hTfinite.toFinset.exists_min_image
        (fun x : L => ‖(x : (K →+* ℂ) → ℝ)‖)
        ⟨hTnonempty.some, hTfinite.mem_toFinset.2 hTnonempty.some_mem⟩ with
      ⟨v, hvfin, hvmin⟩
    have hvT : v ∈ T := hTfinite.mem_toFinset.1 hvfin
    let δ : ℝ := ‖(v : (K →+* ℂ) → ℝ)‖ / 2
    have hvpos : 0 < ‖(v : (K →+* ℂ) → ℝ)‖ := by
      rw [norm_pos_iff]
      intro hv
      exact hvT.2 (Subtype.ext hv)
    have hδpos : 0 < δ := by dsimp [δ]; linarith
    have hδle : δ ≤ 1 := by
      dsimp [δ]
      have := hvT.1
      have := norm_nonneg (v : (K →+* ℂ) → ℝ)
      linarith
    have hisolate : ∀ y : L,
        ‖(y : (K →+* ℂ) → ℝ)‖ < δ → y = 0 := by
      intro y hy
      by_contra hy0
      have hyT : y ∈ T := ⟨le_trans (le_of_lt hy) hδle, hy0⟩
      have hvle := hvmin y (hTfinite.mem_toFinset.2 hyT)
      dsimp [δ] at hy
      linarith
    have hball : ∀ x : L, Metric.ball x δ = {x} := by
      intro x
      ext y
      constructor
      · intro hy
        have hdiff : ‖((y - x : L) : (K →+* ℂ) → ℝ)‖ < δ := by
          simpa [Metric.mem_ball, dist_eq_norm] using hy
        exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp (hisolate (y - x) hdiff))
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        simpa [Metric.mem_ball] using hδpos
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    rw [← hball x]
    exact Metric.isOpen_ball
  · have hisolate : ∀ y : L,
        ‖(y : (K →+* ℂ) → ℝ)‖ < 1 → y = 0 := by
      intro y hy
      by_contra hy0
      exact hTnonempty ⟨y, ⟨le_of_lt hy, hy0⟩⟩
    have hball : ∀ x : L, Metric.ball x 1 = {x} := by
      intro x
      ext y
      constructor
      · intro hy
        have hdiff : ‖((y - x : L) : (K →+* ℂ) → ℝ)‖ < 1 := by
          simpa [Metric.mem_ball, dist_eq_norm] using hy
        exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp (hisolate (y - x) hdiff))
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        simp [Metric.mem_ball]
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    rw [← hball x]
    exact Metric.isOpen_ball

end

end GaloisForLFunctions.HTGeometry
