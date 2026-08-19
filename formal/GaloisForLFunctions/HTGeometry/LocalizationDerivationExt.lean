import GaloisForLFunctions.HTGeometry.SigmaJetCoordinateAutomorphism

/-!
# Derivations on a localization are determined by the base, and commutation transports

Two derivations of a localization agreeing on the image of the base ring are equal: their difference
kills the base, and for `z` with `z s = a` the Leibniz rule gives `s · D z = 0` with `s` invertible.

That uniqueness is what transports commutation.  Conjugating the extended derivation by the extended
difference operator gives another derivation of the localization, and downstairs the two agree
because the operators commute there; so they agree everywhere.

Both statements are mathlib gaps.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- **Derivations of a localization are determined by their values on the base.** -/
theorem localizationDerivation_ext (M : Submonoid A) [IsLocalization M S]
    (D₁ D₂ : Derivation ℤ S S)
    (h : ∀ a : A, D₁ (algebraMap A S a) = D₂ (algebraMap A S a)) : D₁ = D₂ := by
  ext z
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M z
  have hunit : IsUnit (algebraMap A S (s : A)) := IsLocalization.map_units S s
  have h1 : D₁ (z * algebraMap A S (s : A)) = D₂ (z * algebraMap A S (s : A)) := by
    rw [hs]
    exact h a
  rw [Derivation.leibniz, Derivation.leibniz] at h1
  simp only [smul_eq_mul, h (s : A)] at h1
  have h2 : algebraMap A S (s : A) * D₁ z = algebraMap A S (s : A) * D₂ z := by
    have hcancel : z * D₂ (algebraMap A S (s : A)) + algebraMap A S (s : A) * D₁ z
        = z * D₂ (algebraMap A S (s : A)) + algebraMap A S (s : A) * D₂ z := h1
    exact add_left_cancel hcancel
  obtain ⟨u, hu⟩ := hunit
  have h3 : D₁ z = D₂ z := by
    have hcancel : (u : S) * D₁ z = (u : S) * D₂ z := by rw [hu]; exact h2
    exact (Units.mul_right_inj u).mp hcancel
  exact h3

/-- Conjugating a derivation by a ring automorphism. -/
def automorphismConjDerivation (σ : S ≃+* S) (D : Derivation ℤ S S) : Derivation ℤ S S :=
  Derivation.mk'
    ((AddMonoidHom.mk' (fun z => σ.symm (D (σ z)))
      (by intro x y; rw [map_add, map_add, map_add])).toIntLinearMap)
    (by
      intro x y
      show σ.symm (D (σ (x * y))) = x • σ.symm (D (σ y)) + y • σ.symm (D (σ x))
      rw [map_mul, Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, RingEquiv.symm_apply_apply])

@[simp] theorem automorphismConjDerivation_apply (σ : S ≃+* S) (D : Derivation ℤ S S) (z : S) :
    automorphismConjDerivation σ D z = σ.symm (D (σ z)) := rfl

/-- **Commutation of a difference operator with a derivation transports to a localization.** -/
theorem localization_commutes_of_base (M : Submonoid A) [IsLocalization M S]
    (D : Derivation ℤ S S) (σ : S ≃+* S)
    (hbase : ∀ a : A, σ (D (algebraMap A S a)) = D (σ (algebraMap A S a)))
    (z : S) : σ (D z) = D (σ z) := by
  have hconj : automorphismConjDerivation σ D = D := by
    refine localizationDerivation_ext M _ _ ?_
    intro a
    show σ.symm (D (σ (algebraMap A S a))) = D (algebraMap A S a)
    rw [← hbase a, RingEquiv.symm_apply_apply]
  have := congrArg (fun E : Derivation ℤ S S => E z) hconj
  simp only [automorphismConjDerivation_apply] at this
  have hz : σ.symm (D (σ z)) = D z := this
  rw [← hz, RingEquiv.apply_symm_apply]

end

end GaloisForLFunctions.HTGeometry
