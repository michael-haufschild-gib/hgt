import GaloisForLFunctions.HTGeometry.GomesTruncatedJetNilpotentSpace
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetResonantCoordinates

/-!
# Positive resonant coefficients are the full nilpotent coordinate space

The existing resonant chart of the joint algebra restricts exactly to its
augmentation kernel: the constant coordinate is zero and every remaining
resonant coefficient is free. No phase or horizon is excluded.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The constant coefficient is a resonant weight for every actual phase. -/
def gomesTruncatedJetZeroResonance (n : ℕ) (z : ℂ) : GomesTruncatedJetResonantIndex n z :=
  ⟨0, dvd_zero _⟩

/-- The resonant coefficient indices after removing the constant weight. -/
abbrev GomesTruncatedJetPositiveResonantIndex (n : ℕ) (z : ℂ) :=
  {k : GomesTruncatedJetResonantIndex n z // k ≠ gomesTruncatedJetZeroResonance n z}

/-- Every remaining resonant coordinate has genuinely positive integer weight. -/
theorem gomesTruncatedJetPositiveResonantIndex_pos (n : ℕ) (z : ℂ)
    (k : GomesTruncatedJetPositiveResonantIndex n z) : 0 < k.val.val.val := by
  apply Nat.pos_of_ne_zero
  intro h
  apply k.property
  apply Subtype.ext
  exact Fin.ext h

/-- Observe the positive resonant head-row coefficients of a nilpotent joint matrix. -/
def gomesTruncatedJetNilpotentObservation (n : ℕ) (z : ℂ) :
    gomesTruncatedJetNilpotentSpace n z →ₗ[ℂ] (GomesTruncatedJetPositiveResonantIndex n z → ℂ) where
  toFun E k := E.val.val 0 k.val.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The positive resonant observations determine every actual nilpotent joint matrix. -/
theorem gomesTruncatedJetNilpotentObservation_injective (n : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetNilpotentObservation n z) := by
  intro E F h
  apply Subtype.ext
  apply gomesTruncatedJetResonantObservation_injective n z
  funext k
  by_cases hk : k = gomesTruncatedJetZeroResonance n z
  · subst k
    change gomesTruncatedJetAugmentation n z E.val = gomesTruncatedJetAugmentation n z F.val
    rw [gomesTruncatedJetNilpotentSpace_augmentation, gomesTruncatedJetNilpotentSpace_augmentation]
  · exact congrFun h ⟨k, hk⟩

/-- Every assignment of positive resonant coefficients is realized by an actual nilpotent joint matrix. -/
theorem gomesTruncatedJetNilpotentObservation_surjective (n : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetNilpotentObservation n z) := by
  intro c
  let full : GomesTruncatedJetResonantIndex n z → ℂ :=
    fun k => if hk : k = gomesTruncatedJetZeroResonance n z then 0 else c ⟨k, hk⟩
  let E := (gomesTruncatedJetResonantLinearEquiv n z).symm full
  have hObs : gomesTruncatedJetResonantObservation n z E = full :=
    (gomesTruncatedJetResonantLinearEquiv n z).apply_symm_apply full
  have hzero : gomesTruncatedJetAugmentation n z E = 0 := by
    have h := congrFun hObs (gomesTruncatedJetZeroResonance n z)
    change gomesTruncatedJetAugmentation n z E = full (gomesTruncatedJetZeroResonance n z) at h
    simpa only [full, dif_pos rfl] using h
  refine ⟨⟨E, hzero⟩, ?_⟩
  funext k
  have h := congrFun hObs k.val
  change E.val 0 k.val.val = full k.val at h
  change E.val 0 k.val.val = c k
  simpa only [full, dif_neg k.property] using h

/-- The full nilpotent joint matrix space is exactly the complex vector space of positive resonant coefficients. -/
def gomesTruncatedJetNilpotentLinearEquiv (n : ℕ) (z : ℂ) :
    gomesTruncatedJetNilpotentSpace n z ≃ₗ[ℂ] (GomesTruncatedJetPositiveResonantIndex n z → ℂ) :=
  LinearEquiv.ofBijective (gomesTruncatedJetNilpotentObservation n z)
    ⟨gomesTruncatedJetNilpotentObservation_injective n z,
      gomesTruncatedJetNilpotentObservation_surjective n z⟩

/-- The complete linear coordinate chart reads the literal positive resonant matrix entries. -/
theorem gomesTruncatedJetNilpotentLinearEquiv_apply (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    gomesTruncatedJetNilpotentLinearEquiv n z E k = E.val.val 0 k.val.val := rfl

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
