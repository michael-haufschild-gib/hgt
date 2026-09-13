import GaloisForLFunctions.HTGeometry.BanaszczykSignRecovery

open Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Open Banaszczyk transforms commute with continuous linear coordinate equivalences. -/
theorem ContinuousLinearEquiv.image_openBanaszczykTransform
    (e : E ≃L[ℝ] F) (K : Set E) (v : E) :
    e '' openBanaszczykTransform K v = openBanaszczykTransform (e '' K) (e v) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases mem_openBanaszczykTransform.mp hx with ⟨z, hzplus, hzminus, t, ht, hzt⟩
    refine mem_openBanaszczykTransform.mpr ⟨e z, ?_, ?_, t, ht, ?_⟩
    · exact ⟨z + v, hzplus, by simp⟩
    · exact ⟨z - v, hzminus, by simp⟩
    · rw [← e.map_smul, ← e.map_add, hzt]
  · intro hy
    rcases mem_openBanaszczykTransform.mp hy with ⟨z, hzplus, hzminus, t, ht, hzt⟩
    rcases hzplus with ⟨kp, hkp, hkpz⟩
    rcases hzminus with ⟨km, hkm, hkmz⟩
    have hzplus' : e.symm z + v ∈ K := by
      have heq : kp = e.symm z + v := by
        apply e.injective
        rw [hkpz]
        simp
      rwa [← heq]
    have hzminus' : e.symm z - v ∈ K := by
      have heq : km = e.symm z - v := by
        apply e.injective
        rw [hkmz]
        simp
      rwa [← heq]
    have hpre : e.symm z + t • v = e.symm y := by
      apply e.injective
      simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
      exact hzt
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact mem_openBanaszczykTransform.mpr
      ⟨e.symm z, hzplus', hzminus', t, ht, hpre⟩

theorem ContinuousLinearEquiv.image_iteratedOpenBanaszczykTransform
    (e : E ≃L[ℝ] F) (K : Set E) (vs : List E) :
    e '' iteratedOpenBanaszczykTransform K vs =
      iteratedOpenBanaszczykTransform (e '' K) (vs.map e) := by
  induction vs generalizing K with
  | nil => rfl
  | cons v vs ih =>
      calc
        e '' iteratedOpenBanaszczykTransform K (v :: vs) =
            iteratedOpenBanaszczykTransform
              (e '' openBanaszczykTransform K v) (vs.map e) := ih _
        _ = iteratedOpenBanaszczykTransform
              (openBanaszczykTransform (e '' K) (e v)) (vs.map e) := by
          rw [ContinuousLinearEquiv.image_openBanaszczykTransform e K v]
        _ = iteratedOpenBanaszczykTransform (e '' K) ((v :: vs).map e) := rfl

theorem ContinuousLinearEquiv.map_signedListSum (e : E ≃L[ℝ] F) :
    ∀ (vs : List E) (signs : List Bool),
      e (signedListSum vs signs) = signedListSum (vs.map e) signs := by
  intro vs
  induction vs with
  | nil => intro signs; simp [signedListSum]
  | cons v vs ih =>
      intro signs
      cases signs with
      | nil => simp [signedListSum]
      | cons sign signs =>
          cases sign <;> simp [signedListSum, ih]

end GaloisForLFunctions.HTGeometry

