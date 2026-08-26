import GaloisForLFunctions.HTGeometry.LocalizedAlgebraTensorEquiv
import GaloisForLFunctions.HTGeometry.AdjoinRootSplitFibreSeparable

/-!
# Separable specializations from split scalar-extension fibres

The defining polynomial of a monogenic algebra remains visible after arbitrary field scalar
extension.  If that scalar-extended algebra splits as a finite product of copies of the field, the
specialized polynomial is separable.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing
open scoped TensorProduct

/-- A split residue algebra is equivalently a split tensor fibre, with the standard quotient
algebra structure used by scalar extension. -/
theorem nonempty_tensorProduct_algEquiv_pi_of_split_residue_fibre
    {T N : Type*} [CommRing T] [IsLocalRing T]
    [CommRing N] [Algebra T N]
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((N ⧸ maxExt T N) ≃ₐ[ResidueField T] (ι → ResidueField T))) :
    Nonempty ((TensorProduct T (ResidueField T) N) ≃ₐ[ResidueField T]
      (ι → ResidueField T)) := by
  obtain ⟨s⟩ := hsplit
  let oldAlg : Algebra (ResidueField T) (N ⧸ maxExt T N) :=
    residueAlgebraQuotient T N
  let sr : (N ⧸ maxExt T N) ≃+* (ι → ResidueField T) := s.toRingEquiv
  have hscomm (x : ResidueField T) :
      sr (@algebraMap (ResidueField T) (N ⧸ maxExt T N) _ _ oldAlg x) =
        algebraMap (ResidueField T) (ι → ResidueField T) x := s.commutes x
  let stdAlg : Algebra (ResidueField T) (N ⧸ maxExt T N) :=
    Ideal.Quotient.algebraQuotientMapQuotient
  letI : Algebra (ResidueField T) (N ⧸ maxExt T N) := stdAlg
  let s' : (N ⧸ maxExt T N) ≃ₐ[ResidueField T] (ι → ResidueField T) :=
    { sr with
      commutes' := fun x => by
        rw [show algebraMap (ResidueField T) (N ⧸ maxExt T N) x =
            @algebraMap (ResidueField T) (N ⧸ maxExt T N) _ _ oldAlg x by rfl]
        exact hscomm x }
  change Nonempty ((TensorProduct T (T ⧸ maximalIdeal T) N) ≃ₐ[T ⧸ maximalIdeal T]
    (ι → (T ⧸ maximalIdeal T)))
  exact ⟨(Algebra.TensorProduct.quotIdealMapEquivQuotTensor
    N (maximalIdeal T)).symm.trans s'⟩

/-- A split scalar-extension fibre of an `AdjoinRoot` presentation forces the coefficientwise
specialized polynomial to be separable. -/
theorem separable_map_of_adjoinRoot_equiv_of_split_baseChange
    {A B k : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Field k] [Algebra A k]
    (p : Polynomial A) (hp : p.Monic) (e : AdjoinRoot p ≃ₐ[A] B)
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((TensorProduct A k B) ≃ₐ[k] (ι → k))) :
    (p.map (algebraMap A k)).Separable := by
  obtain ⟨s⟩ := hsplit
  exact separable_of_adjoinRoot_algEquiv_pi _ (hp.map _)
    ((ABHN.adjoinRootScalarExtensionEquiv A k p).symm |>.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl) e) |>.trans s)

/-- A principal-open `AdjoinRoot` presentation specializes separably whenever a later localized
algebra has split field fibre. -/
theorem separable_map_of_adjoinRoot_equiv_of_localized_split_baseChange
    (R : Type*) [CommRing R]
    (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [IsLocalization M T]
    (k : Type*) [Field k] [Algebra R k] [Algebra S k] [Algebra T k]
    [IsScalarTower R S k] [IsScalarTower R T k] [IsScalarTower S T k]
    (B : Type*) [CommRing B] [Algebra R B]
    (N : Type*) [CommRing N] [Algebra R N] [Algebra T N] [IsScalarTower R T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule M fN.toLinearMap]
    (q : Polynomial S) (hq : q.Monic)
    (e : AdjoinRoot q ≃ₐ[S] TensorProduct R S B)
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((TensorProduct T k N) ≃ₐ[k] (ι → k))) :
    (q.map (algebraMap S k)).Separable :=
  separable_map_of_adjoinRoot_equiv_of_split_baseChange q hq e
    (nonempty_split_baseChange_of_localizedAlgebra R M S T k B N fN hsplit)

end GaloisForLFunctions.HTGeometry
