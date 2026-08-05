import GaloisForLFunctions.HTGeometry.UniversalProjectiveRecurrencePhaseDiagramLaw

/-!
# Transverse projective control families exist

A control family is projectively transverse when no nonzero phase character has vanishing detuning.
The coordinate response family on a finite control space is transverse: the detuning of a character
evaluated at a coordinate vector returns that character's own coefficient, which is nonzero
somewhere on its support.

So the phase-diagram law applies to the tautological control family, with no analytic input.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The coordinate response family is projectively transverse.** -/
theorem projectivelyTransverseControl_proj {I : Type*} [Fintype I] [DecidableEq I] :
    ProjectivelyTransverseControl
      (fun i : I => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) i)) := by
  intro k hk
  have hk1 : (k.1 : I →₀ ℤ) ≠ 0 := fun h => hk (Subtype.ext h)
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hk1
  intro hzero
  have happ := congrArg (fun f : (I → ℝ) →L[ℝ] ℝ => f (Pi.single j 1)) hzero
  simp only [zero_apply] at happ
  rw [projectiveControlDetuning_apply, projectiveCharacterDetuning] at happ
  have hval : ∑ i ∈ k.1.support,
      ((k.1 i : ℝ) * ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) i)
        (Pi.single j 1))) = (k.1 j : ℝ) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hnot
      exact absurd hj hnot
  rw [hval] at happ
  exact (Finsupp.mem_support_iff.mp hj) (by exact_mod_cast happ)

end GaloisForLFunctions.HTGeometry
