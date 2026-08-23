import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionDirectedSystem
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisH2TorsionCharacter

/-!
# Transitions between finite local-invariant layers

Any additive groups identified with finite torsion layers `ℚ/ℤ[m]` and `ℚ/ℤ[n]` acquire a
canonical injective transition when `m ∣ n`.  These transitions satisfy identity and composition,
are uniquely characterized by invariant compatibility, and preserve standard circle characters.

The construction applies in particular to finite continuous unit-`H²` layers.  It is a canonical
coordinate transport, not yet a theorem identifying it with cohomological inflation along a
specific tower of unramified field extensions.  Proving that comparison is the remaining
source-side local-class-field-theory compatibility step.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Transport between finite invariant layers through their `ℚ/ℤ` coordinates. -/
def finiteTorsionInvariantTransition
    {Gm Gn : Type*} [AddGroup Gm] [AddGroup Gn] {m n : ℕ}
    (em : Gm ≃+ ratModIntNTorsion m) (en : Gn ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) : Gm →+ Gn :=
  en.symm.toAddMonoidHom.comp
    ((ratModIntNTorsionInclusion hmn).comp em.toAddMonoidHom)

/-- Applying the target invariant to a transition is finite torsion inclusion. -/
theorem finiteTorsionInvariantTransition_apply
    {Gm Gn : Type*} [AddGroup Gm] [AddGroup Gn] {m n : ℕ}
    (em : Gm ≃+ ratModIntNTorsion m) (en : Gn ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) (x : Gm) :
    en (finiteTorsionInvariantTransition em en hmn x) =
      ratModIntNTorsionInclusion hmn (em x) := by
  change en (en.symm (ratModIntNTorsionInclusion hmn (em x))) = _
  rw [AddEquiv.apply_symm_apply]

/-- Coordinate transitions are injective. -/
theorem finiteTorsionInvariantTransition_injective
    {Gm Gn : Type*} [AddGroup Gm] [AddGroup Gn] {m n : ℕ}
    (em : Gm ≃+ ratModIntNTorsion m) (en : Gn ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) : Function.Injective (finiteTorsionInvariantTransition em en hmn) := by
  intro x y hxy
  apply em.injective
  apply Subtype.ext
  have h := congrArg en hxy
  rw [finiteTorsionInvariantTransition_apply,
    finiteTorsionInvariantTransition_apply] at h
  have hv := congrArg (fun z : ratModIntNTorsion n ↦ (z : RatModInt)) h
  exact hv

/-- Invariant compatibility uniquely determines a transition. -/
theorem finiteTorsionInvariantTransition_unique
    {Gm Gn : Type*} [AddGroup Gm] [AddGroup Gn] {m n : ℕ}
    (em : Gm ≃+ ratModIntNTorsion m) (en : Gn ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) (f : Gm →+ Gn)
    (hf : ∀ x, en (f x) = ratModIntNTorsionInclusion hmn (em x)) :
    f = finiteTorsionInvariantTransition em en hmn := by
  ext x
  apply en.injective
  rw [hf, finiteTorsionInvariantTransition_apply]

/-- Identity law for finite invariant transitions. -/
theorem finiteTorsionInvariantTransition_self
    {G : Type*} [AddGroup G] {n : ℕ}
    (e : G ≃+ ratModIntNTorsion n) :
    finiteTorsionInvariantTransition e e (dvd_refl n) = AddMonoidHom.id G := by
  symm
  apply finiteTorsionInvariantTransition_unique e e (dvd_refl n)
  intro x
  rfl

/-- Composition law for finite invariant transitions. -/
theorem finiteTorsionInvariantTransition_comp
    {Gl Gm Gn : Type*} [AddGroup Gl] [AddGroup Gm] [AddGroup Gn]
    {l m n : ℕ}
    (el : Gl ≃+ ratModIntNTorsion l) (em : Gm ≃+ ratModIntNTorsion m)
    (en : Gn ≃+ ratModIntNTorsion n) (hlm : l ∣ m) (hmn : m ∣ n) :
    (finiteTorsionInvariantTransition em en hmn).comp
        (finiteTorsionInvariantTransition el em hlm) =
      finiteTorsionInvariantTransition el en (dvd_trans hlm hmn) := by
  apply finiteTorsionInvariantTransition_unique el en (dvd_trans hlm hmn)
  intro x
  rw [AddMonoidHom.comp_apply, finiteTorsionInvariantTransition_apply,
    finiteTorsionInvariantTransition_apply]
  rfl

/-- Refining a finite invariant layer does not change its standard circle phase. -/
theorem finiteTorsionInvariantTransition_character
    {Gm Gn : Type*} [AddGroup Gm] [AddGroup Gn] {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (em : Gm ≃+ ratModIntNTorsion m) (en : Gn ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) (x : Gm) :
    ratModIntNTorsionStdAddChar n hn
        (en (finiteTorsionInvariantTransition em en hmn x)) =
      ratModIntNTorsionStdAddChar m hm (em x) := by
  rw [finiteTorsionInvariantTransition_apply,
    ratModIntNTorsionStdAddChar_inclusion hm hn hmn]

/-- Canonical coordinate transition between two finite continuous unit-`H²` layers. -/
def continuousGaloisH2TorsionTransition
    (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    {m n : ℕ}
    (eL : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion m)
    (eM : continuousGaloisUnitCohomology 2 K M ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) :
    continuousGaloisUnitCohomology 2 K L →+ continuousGaloisUnitCohomology 2 K M :=
  finiteTorsionInvariantTransition eL eM hmn

/-- Continuous `H²` coordinate transition commutes with its torsion invariant. -/
theorem continuousGaloisH2TorsionTransition_invariant
    (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    {m n : ℕ}
    (eL : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion m)
    (eM : continuousGaloisUnitCohomology 2 K M ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) (z : continuousGaloisUnitCohomology 2 K L) :
    eM (continuousGaloisH2TorsionTransition K L M eL eM hmn z) =
      ratModIntNTorsionInclusion hmn (eL z) :=
  finiteTorsionInvariantTransition_apply eL eM hmn z

/-- Continuous `H²` standard phases are stable under coordinate transition. -/
theorem continuousGaloisH2TorsionTransition_character
    (K L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (eL : continuousGaloisUnitCohomology 2 K L ≃+ ratModIntNTorsion m)
    (eM : continuousGaloisUnitCohomology 2 K M ≃+ ratModIntNTorsion n)
    (hmn : m ∣ n) (z : continuousGaloisUnitCohomology 2 K L) :
    continuousGaloisH2TorsionStdAddChar K M n hn eM
        (continuousGaloisH2TorsionTransition K L M eL eM hmn z) =
      continuousGaloisH2TorsionStdAddChar K L m hm eL z := by
  exact finiteTorsionInvariantTransition_character hm hn eL eM hmn z

end

end GaloisForLFunctions.HTGeometry.ABHN
