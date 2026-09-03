import GaloisForLFunctions.HTGeometry.FiniteEtaleAlgClosedSplit
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Rank one from a singleton rational fibre

A finite etale algebra over an algebraically closed field splits as a finite product of copies of
that field.  Hence one rational point and subsingleton rational-point space force rank one.  By
base change, the same conclusion computes the local rank of a finite etale algebra at any rational
point of its base.
-/

namespace Algebra

noncomputable section

open scoped TensorProduct

universe u v

/-- A nonempty finite etale algebra over an algebraically closed field whose rational points are
subsingleton has rank one. -/
theorem finrank_eq_one_of_algHom_subsingleton
    {K : Type u} {D : Type v} [Field K] [IsAlgClosed K]
    [CommRing D] [Algebra K D] [Etale K D] [Module.Finite K D]
    (f : D →ₐ[K] K) (h : Subsingleton (D →ₐ[K] K)) : Module.finrank K D = 1 := by
  classical
  have hne : (0 : D) ≠ 1 := by
    intro h01
    have hmap := congrArg f h01
    exact zero_ne_one (by simpa only [map_zero, map_one] using hmap)
  letI : Nontrivial D := ⟨⟨0, 1, hne⟩⟩
  letI : IsArtinianRing D := isArtinian_of_tower K inferInstance
  letI : Fintype (PrimeSpectrum D) := Fintype.ofFinite _
  obtain ⟨e⟩ := nonempty_algEquiv_pi_of_finiteEtale_isAlgClosed (K := K) (A := D)
  have hinj : Function.Injective (fun p : PrimeSpectrum D ↦
      (Pi.evalAlgHom K (fun _ : PrimeSpectrum D ↦ K) p).comp e.toAlgHom) := by
    intro p q hpq
    by_contra hpneq
    have heval := DFunLike.congr_fun hpq (e.symm (Pi.single p 1))
    simp [hpneq] at heval
  have hspec : Subsingleton (PrimeSpectrum D) :=
    ⟨fun p q ↦ hinj (Subsingleton.elim _ _)⟩
  have hnonempty : Nonempty (PrimeSpectrum D) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  have hcard : Fintype.card (PrimeSpectrum D) = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨Classical.choice hnonempty, fun _ ↦ Subsingleton.elim _ _⟩
  calc
    Module.finrank K D = Module.finrank K (PrimeSpectrum D → K) := e.toLinearEquiv.finrank_eq
    _ = Fintype.card (PrimeSpectrum D) := by simp
    _ = 1 := hcard

/-- If the geometric fibre over a rational point of the base has one rational point, then a finite
etale algebra has local rank one at that point. -/
theorem rankAtStalk_eq_one_of_algSpec_fiber_subsingleton
    {K : Type u} {A : Type v} {B : Type*}
    [Field K] [IsAlgClosed K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Etale A B] [Module.Finite A B]
    (chi : A →ₐ[K] K)
    (psi : B →ₐ[K] K)
    (hpsi : psi.comp (IsScalarTower.toAlgHom K A B) = chi)
    (hfiber : Subsingleton
      {phi : B →ₐ[K] K // phi.comp (IsScalarTower.toAlgHom K A B) = chi}) :
    Module.rankAtStalk B
      ((⊥ : PrimeSpectrum K).comap chi.toRingHom) = 1 := by
  letI : Algebra A K := chi.toRingHom.toAlgebra
  letI : IsScalarTower K A K := IsScalarTower.of_algebraMap_eq fun k ↦ by
    change k = chi (algebraMap K A k)
    exact (chi.commutes k).symm
  let psiA : B →ₐ[A] K :=
    { psi.toRingHom with
      commutes' := fun a ↦ DFunLike.congr_fun hpsi a }
  let psiD : TensorProduct A K B →ₐ[K] K :=
    (AlgHom.liftEquiv A K B K) psiA
  have hhom : Subsingleton (TensorProduct A K B →ₐ[K] K) := by
    constructor
    intro f g
    let fA : B →ₐ[A] K := (AlgHom.liftEquiv A K B K).symm f
    let gA : B →ₐ[A] K := (AlgHom.liftEquiv A K B K).symm g
    let fK : B →ₐ[K] K := fA.restrictScalars K
    let gK : B →ₐ[K] K := gA.restrictScalars K
    have hfK : fK.comp (IsScalarTower.toAlgHom K A B) = chi := by
      ext a
      change fA (algebraMap A B a) = chi a
      rw [fA.commutes]
      rfl
    have hgK : gK.comp (IsScalarTower.toAlgHom K A B) = chi := by
      ext a
      change gA (algebraMap A B a) = chi a
      rw [gA.commutes]
      rfl
    have heq : (⟨fK, hfK⟩ :
        {phi : B →ₐ[K] K // phi.comp (IsScalarTower.toAlgHom K A B) = chi}) =
        ⟨gK, hgK⟩ := hfiber.elim _ _
    apply (AlgHom.liftEquiv A K B K).symm.injective
    apply AlgHom.ext
    intro b
    exact DFunLike.congr_fun (congrArg Subtype.val heq) b
  have hfinrank : Module.finrank K (TensorProduct A K B) = 1 :=
    finrank_eq_one_of_algHom_subsingleton psiD hhom
  calc
    Module.rankAtStalk B ((⊥ : PrimeSpectrum K).comap chi.toRingHom) =
        Module.rankAtStalk (TensorProduct A K B) (⊥ : PrimeSpectrum K) :=
      (Module.rankAtStalk_baseChange (R := A) (M := B) (⊥ : PrimeSpectrum K)).symm
    _ = Module.finrank K (TensorProduct A K B) := by
      exact congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := K) (M := TensorProduct A K B)) ⊥
    _ = 1 := hfinrank

end

end Algebra
