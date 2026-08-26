import GaloisForLFunctions.HTGeometry.AffineExponentialPrincipalOpenLocusSource
import GaloisForLFunctions.HTGeometry.AffineExponentialSymmetricProductSource
import GaloisForLFunctions.HTGeometry.IteratedBialgebraProductKaehler
import GaloisForLFunctions.HTGeometry.BialgebraInvariantKaehlerTorsion
import GaloisForLFunctions.HTGeometry.AffineExponentialCoLieClassification

/-!
# Stable Hopf locus of a vanishing affine-exponential differential

An invariant Kähler relation at an extension-valued affine-exponential point produces an integral
finite-type translated principal-open source.  Symmetrizing that source, stabilizing its finite
product kernels, and using source inversion gives an actual Hopf ideal.  The stable quotient is a
finite-type domain.  Its invariant differential is torsion, hence has zero co-Lie value after
translation to a rational point.  The same stable kernel annihilates the original translated
extension point.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry

open AffineExponentialGroup AffineExponentialPointEvaluation
open AffineExponentialPointClosure AffineExponentialInvariantKaehler
open AffineExponentialCoLieClassification

universe u

noncomputable section

/-- Exact stable Hopf-locus certificate supplied by a vanishing mixed invariant differential. -/
structure AffineExponentialStableHopfLocus
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (n : ℕ) (p : Point L n) (tor add : Fin n → k) where
  algebraicPoint : Point k n
  ideal : Ideal (CoordinateAlgebra k n)
  [isHopfIdeal : ideal.IsHopfIdeal k]
  coset_zero : ∀ a ∈ ideal,
    ((eval (k := k) p).comp (rightTranslate algebraicPoint⁻¹)) a = 0
  coLie_zero : subgroupQuotientCoLieMap k ideal
    (mixedCoLieVector k tor add) = 0

/-- A vanishing mixed invariant Kähler form has an exact stable Hopf locus whose quotient co-Lie
vector vanishes and whose translated extension point annihilates the Hopf ideal. -/
theorem exists_affineExponentialStableHopfLocus
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [IsAlgClosed k] [CharZero k]
    {n : ℕ} (p : Point L n) (tor add : Fin n → k)
    (hw : pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add) = 0) :
    Nonempty (AffineExponentialStableHopfLocus k L n p tor add) := by
  let A := CoordinateAlgebra k n
  let w := mixedInvariantKaehlerVector k tor add
  let D := Classical.choice
    (exists_affineExponentialPrincipalOpenSource k L p tor add hw)
  letI : CommRing D.carrier := D.commRing
  letI : Algebra k D.carrier := D.algebra
  letI : IsDomain D.carrier := D.isDomain
  letI : Algebra.FiniteType k D.carrier := D.finiteType
  letI : IsDomain (D.carrier ⊗[k] D.carrier) :=
    isDomain_tensorProduct_of_finiteType
  letI : Algebra.FiniteType D.carrier (D.carrier ⊗[k] D.carrier) :=
    Algebra.FiniteType.baseChange D.carrier
  letI : Algebra.FiniteType k (D.carrier ⊗[k] D.carrier) :=
    Algebra.FiniteType.trans D.finiteType inferInstance
  let f : A →ₐ[k] D.carrier ⊗[k] D.carrier :=
    affineExponentialSymmetricSourceMap D.map
  let e : (D.carrier ⊗[k] D.carrier) →ₐ[k] k :=
    tensorPoint D.identityPoint D.identityPoint
  have he : e.comp f = Bialgebra.counitAlgHom k A := by
    exact tensorPoint_comp_affineExponentialSymmetricSourceMap
      D.map D.identityPoint D.map_identity
  let σ : (D.carrier ⊗[k] D.carrier) →ₐ[k]
      D.carrier ⊗[k] D.carrier :=
    (Algebra.TensorProduct.comm k D.carrier D.carrier).toAlgHom
  have hσ : σ.comp f = f.comp (HopfAlgebra.antipodeAlgHom k A) := by
    exact affineExponentialSymmetricSourceMap_swap D.map
  obtain ⟨m, hstable⟩ := exists_iteratedProductKernel_stabilizes f e he
  let I : Ideal A := iteratedProductKernel f m
  have hprime : I.IsPrime := by
    exact iteratedProductKernel_isPrime f m
  have hHopf : I.IsHopfIdeal k := by
    exact affineExponential_iteratedProductKernel_isHopfIdeal
      k (D.carrier ⊗[k] D.carrier) f e he σ hσ m hstable
  letI : I.IsPrime := hprime
  letI : I.IsHopfIdeal k := hHopf
  let Q := A ⧸ I
  letI : IsDomain Q := Ideal.Quotient.isDomain I
  letI : Algebra.FiniteType k Q :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k I)
      Ideal.Quotient.mk_surjective
  let πB : A →ₐc[k] Q := Bialgebra.Quotient.mkBialgHom (R := k) I
  let wQ : Ω[Q⁄k] := algHomKaehlerMap πB.toAlgHom w
  letI : IsDomain
      (IteratedTensorAlgebra k (D.carrier ⊗[k] D.carrier) m) :=
    iteratedTensorAlgebra_isDomain
      k (D.carrier ⊗[k] D.carrier) m
  let F : A →ₐ[k] IteratedTensorAlgebra k (D.carrier ⊗[k] D.carrier) m :=
    iteratedProductMap f m
  let Fbar : Q →ₐ[k]
      IteratedTensorAlgebra k (D.carrier ⊗[k] D.carrier) m :=
    Ideal.Quotient.liftₐ I F (fun a ha => ha)
  have hFbar_comp : Fbar.comp πB.toAlgHom = F := by
    rfl
  have hFbar_injective : Function.Injective Fbar := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq]
    change F (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hfw : algHomKaehlerMap f w = 0 := by
    exact algHomKaehlerMap_affineExponentialSymmetricSourceMap_eq_zero
      D.map tor add D.kaehler_zero
  have hFw : algHomKaehlerMap F w = 0 := by
    exact algHomKaehlerMap_iteratedProductMap_eq_zero f w
      (algHomKaehlerMap_mixedInvariantKaehlerVector_comul k tor add) hfw m
  have hFbarw : algHomKaehlerMap Fbar wQ = 0 := by
    change algHomKaehlerMap Fbar (algHomKaehlerMap πB.toAlgHom w) = 0
    rw [← algHomKaehlerMap_comp, hFbar_comp]
    exact hFw
  let FT := FractionRing
    (IteratedTensorAlgebra k (D.carrier ⊗[k] D.carrier) m)
  let j : IteratedTensorAlgebra k (D.carrier ⊗[k] D.carrier) m →ₐ[k] FT :=
    IsScalarTower.toAlgHom k
      (IteratedTensorAlgebra k (D.carrier ⊗[k] D.carrier) m) FT
  let jFbar : Q →ₐ[k] FT := j.comp Fbar
  have hjFbar_injective : Function.Injective jFbar :=
    (IsFractionRing.injective
      (IteratedTensorAlgebra k (D.carrier ⊗[k] D.carrier) m) FT).comp
        hFbar_injective
  have hjFbarw : algHomKaehlerMap jFbar wQ = 0 := by
    change algHomKaehlerMap (j.comp Fbar) wQ = 0
    rw [algHomKaehlerMap_comp, hFbarw, map_zero]
  obtain ⟨s, hs, hsw⟩ :=
    exists_nonzero_smul_eq_zero_of_algHomKaehlerMap_eq_zero
      jFbar hjFbar_injective hjFbarw
  have htranslateQ (φ : Q →ₐ[k] k) :
      algHomKaehlerMap (bialgebraRightTranslate φ) wQ = wQ := by
    change algHomKaehlerMap (bialgebraRightTranslate φ)
        (algHomKaehlerMap πB.toAlgHom w) =
      algHomKaehlerMap πB.toAlgHom w
    rw [← algHomKaehlerMap_comp]
    rw [bialgebraRightTranslate_naturality πB φ]
    rw [algHomKaehlerMap_comp]
    rw [algHomKaehlerMap_bialgebraRightTranslate_eq_of_comul w
      (algHomKaehlerMap_mixedInvariantKaehlerVector_comul k tor add)]
  have hcoLieQ : AffineGroupScheme.kaehlerToCoLie wQ = 0 :=
    kaehlerToCoLie_eq_zero_of_torsion_of_rightTranslate_invariant
      wQ htranslateQ s hs hsw
  have hcoLie : subgroupQuotientCoLieMap k I
      (mixedCoLieVector k tor add) = 0 := by
    have hnat := kaehlerToCoLie_algHomKaehlerMap πB w
    have hzero : AffineGroupScheme.kaehlerToCoLie
        (algHomKaehlerMap πB.toAlgHom w) = 0 := by
      change AffineGroupScheme.kaehlerToCoLie wQ = 0
      exact hcoLieQ
    rw [hzero] at hnat
    rw [kaehlerToCoLie_mixedInvariantKaehlerVector] at hnat
    exact hnat.symm
  have hcoset : ∀ a ∈ I,
      ((eval (k := k) p).comp (rightTranslate D.algebraicPoint⁻¹)) a = 0 := by
    intro a ha
    have ha0 : a ∈ iteratedProductKernel f 0 :=
      (iteratedProductKernel_antitone f e he (Nat.zero_le m)) ha
    change f a = 0 at ha0
    let τ : (D.carrier ⊗[k] D.carrier) →ₐ[k] L :=
      Algebra.TensorProduct.lift D.genericPoint
        ((Algebra.ofId k L).comp D.identityPoint)
        (fun _ _ => Commute.all _ _)
    have hτ : τ.comp f = D.genericPoint.comp D.map := by
      exact tensorExtensionPoint_comp_affineExponentialSymmetricSourceMap_right_identity
        D.map D.identityPoint D.genericPoint D.map_identity
    have hz := congrArg τ ha0
    rw [map_zero] at hz
    have hτa := DFunLike.congr_fun hτ a
    have hgen := DFunLike.congr_fun D.map_generic a
    change τ (f a) = D.genericPoint (D.map a) at hτa
    change D.genericPoint (D.map a) =
      ((eval (k := k) p).comp (rightTranslate D.algebraicPoint⁻¹)) a at hgen
    rw [← hgen, ← hτa]
    exact hz
  exact ⟨{
    algebraicPoint := D.algebraicPoint
    ideal := I
    isHopfIdeal := hHopf
    coset_zero := hcoset
    coLie_zero := hcoLie
  }⟩

end

end GaloisForLFunctions.HTGeometry
