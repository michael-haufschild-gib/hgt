import GaloisForLFunctions.HTGeometry.DifferentialDeltaSimple
import GaloisForLFunctions.HTGeometry.QuotientDerivation

/-!
# `δ`-simple quotients

The quotient of a differential ring by a `δ`-ideal maximal among the proper `δ`-ideals is
`δ`-simple: `δ`-ideals of the quotient correspond to `δ`-ideals of the ring containing the given
one.  Together with the existence of maximal `δ`-ideals this produces `δ`-simple differential rings
in which a prescribed fundamental matrix survives, which is the construction of a Picard--Vessiot
ring.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] [Differential R]

/-- The preimage of a `δ`-ideal of the quotient is a `δ`-ideal. -/
theorem isDeltaIdeal_comap {M : Ideal R} (hM : IsDeltaIdeal M) {J : Ideal (R ⧸ M)}
    (hJ : @IsDeltaIdeal (R ⧸ M) _ (quotientDifferential M hM) J) :
    IsDeltaIdeal (J.comap (Ideal.Quotient.mk M)) := by
  intro x hx
  have hx' : Ideal.Quotient.mk M x ∈ J := hx
  have hd := hJ _ hx'
  rwa [quotientDifferential_deriv_mk] at hd

/-- **The quotient by a maximal `δ`-ideal is `δ`-simple.** -/
theorem isDeltaSimple_quotient_of_maximal {M : Ideal R} (hM : IsDeltaIdeal M)
    (hmax : ∀ J : Ideal R, IsDeltaIdeal J → J ≠ ⊤ → M ≤ J → J = M) :
    @IsDeltaSimple (R ⧸ M) _ (quotientDifferential M hM) := by
  intro J hJ
  by_cases hJtop : J = ⊤
  · exact Or.inr hJtop
  · left
    have hcomap : IsDeltaIdeal (J.comap (Ideal.Quotient.mk M)) := isDeltaIdeal_comap hM hJ
    have hle : M ≤ J.comap (Ideal.Quotient.mk M) := by
      intro x hx
      have : Ideal.Quotient.mk M x = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hx
      show Ideal.Quotient.mk M x ∈ J
      rw [this]
      exact J.zero_mem
    have hne : J.comap (Ideal.Quotient.mk M) ≠ ⊤ := by
      intro htop
      apply hJtop
      have h1 : (1 : R) ∈ J.comap (Ideal.Quotient.mk M) := by rw [htop]; trivial
      have h1' : (1 : R ⧸ M) ∈ J := by simpa using h1
      exact Ideal.eq_top_of_isUnit_mem J h1' isUnit_one
    have heq := hmax _ hcomap hne hle
    refine (Submodule.eq_bot_iff _).mpr fun z hz => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hxJ : x ∈ J.comap (Ideal.Quotient.mk M) := hz
    rw [heq] at hxJ
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hxJ

omit [Differential R] in
/-- The quotient by a proper ideal is nontrivial. -/
theorem nontrivial_quotient_of_ne_top {M : Ideal R} (hMne : M ≠ ⊤) : Nontrivial (R ⧸ M) := by
  rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
  exact hMne

end

end GaloisForLFunctions.HTGeometry
