import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular sequences pass to retracts

If `f : M → N` is a linear map with a linear retraction `g`, every `N`-weakly-regular sequence is
`M`-weakly-regular: `f` is injective, so each element stays a nonzerodivisor, and the retraction
descends to the quotients by one scalar (`quotSMulTopMap`), so the induction on the list goes
through.

This is the transport step of the Cohen–Macaulay argument for the critical horizon: in
characteristic zero the trace map splits the inclusion of a normalization into a regular ring
containing it, so a regular sequence on the regular ring is regular on the normalization.
-/

namespace GaloisForLFunctions.HTGeometry

open RingTheory.Sequence

universe u v w

variable {A : Type u} [CommRing A]

/-- A split injection descends to the quotients by one scalar. -/
noncomputable def quotSMulTopMap {M : Type v} {N : Type w} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (y : A) :
    QuotSMulTop y M →ₗ[A] QuotSMulTop y N :=
  Submodule.mapQ _ _ f (fun z hz => by
    simp only [Submodule.mem_comap]
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists z y ⊤).1 hz
    rw [← hw, f.map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (by trivial))

theorem quotSMulTopMap_mk {M : Type v} {N : Type w} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (y : A) (m : M) :
    quotSMulTopMap f y (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) := rfl


/-- **A weakly regular sequence stays weakly regular on a retract.**  If `f : M → N` admits a
linear retraction `g`, then every `N`-weakly-regular sequence is `M`-weakly-regular.  This is how a
trace splitting transports regularity from a regular ambient ring to a normalization sitting inside
it. -/
theorem isWeaklyRegular_of_leftInverse :
    ∀ (rs : List A) {M : Type v} {N : Type v} [AddCommGroup M] [Module A M]
      [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (g : N →ₗ[A] M),
      (∀ m, g (f m) = m) → IsWeaklyRegular N rs → IsWeaklyRegular M rs := by
  intro rs
  induction rs with
  | nil => intro M N _ _ _ _ f g _ _; exact RingTheory.Sequence.IsWeaklyRegular.nil (R := A) M
  | cons y rs ih =>
      intro M N _ _ _ _ f g hgf hreg
      rw [isWeaklyRegular_cons_iff] at hreg ⊢
      obtain ⟨hy, hreg'⟩ := hreg
      constructor
      · intro a b hab
        have : f a = f b := hy (by
          simp only [← map_smul]
          exact congrArg f hab)
        rw [← hgf a, ← hgf b, this]
      · refine ih (quotSMulTopMap f y) (quotSMulTopMap g y) ?_ hreg'
        intro z
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        rw [quotSMulTopMap_mk, quotSMulTopMap_mk, hgf]

end GaloisForLFunctions.HTGeometry
