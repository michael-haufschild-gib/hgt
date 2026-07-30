import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction
import GaloisForLFunctions.HTGeometry.DifferentialOperatorToeplitzRank
import GaloisForLFunctions.HTGeometry.LocalizedQuotientMatroid

/-!
# Source-boundary quotient matroids

This module equips a differential field with its canonical `C[D]`-module structure when `C` is
constant, forms the quotient of complete source-increment packets by simultaneous coboundaries,
and localizes that quotient to `C(D)`.  The resulting represented matroid is independent exactly
when no nonzero finite jet character is one simultaneous source coboundary; finite packet rank is
the `C(D)`-dimension of the localized quotient-class span.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial
open scoped Classical Differential nonZeroDivisors

noncomputable section

universe u v

/-- The unit differential operator acts as the identity. -/
@[simp]
theorem differentialOperatorApply_one
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (x : K) :
    differentialOperatorApply (1 : Polynomial C) x = x := by
  rw [show (1 : Polynomial C) = Polynomial.monomial 0 1 by simp,
    differentialOperatorApply_monomial]
  simp

/-- Every constant-coefficient differential operator kills the zero input. -/
@[simp]
theorem differentialOperatorApply_zero_input
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (P : Polynomial C) :
    differentialOperatorApply P (0 : K) = 0 := by
  classical
  have hjet : ∀ n : ℕ, differentialJet n (0 : K) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show n + 1 = n + 1 by rfl, differentialJet_succ, ih, map_zero]
  unfold differentialOperatorApply
  rw [Polynomial.sum_def]
  simp [hjet]

/-- Constant-coefficient differential operators are additive in their input. -/
theorem differentialOperatorApply_add_input
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (P : Polynomial C) (x y : K) :
    differentialOperatorApply P (x + y) =
      differentialOperatorApply P x + differentialOperatorApply P y := by
  classical
  unfold differentialOperatorApply
  simp_rw [differentialJet_additive, mul_add]
  rw [Polynomial.sum_def, Polynomial.sum_def, Polynomial.sum_def]
  exact Finset.sum_add_distrib

/-- The `C[D]`-module structure on a differential field whose embedded copy of `C` is constant. -/
@[reducible] def differentialOperatorModule
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0) :
    Module (Polynomial C) K where
  smul P x := differentialOperatorApply P x
  one_smul := differentialOperatorApply_one
  mul_smul P Q x := (differentialOperatorApply_mul hconst P Q x).symm
  smul_zero := differentialOperatorApply_zero_input
  zero_smul := differentialOperatorApply_zero
  smul_add := differentialOperatorApply_add_input
  add_smul := differentialOperatorApply_add

set_option linter.unusedVariables false in
/-- The base field viewed as a module over constant-coefficient differential
operators.  The type records the proof that the coefficient field is constant,
so its scalar action is stable under typeclass inference. -/
def DifferentialOperatorSpace
    (C K : Type*) [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0) := K

/-- The additive-group structure transported to the proof-indexed operator space. -/
instance differentialOperatorSpaceAddCommGroup
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0) :
    AddCommGroup (DifferentialOperatorSpace C K hconst) := by
  unfold DifferentialOperatorSpace
  infer_instance

/-- The canonical `C[D]`-module structure on the proof-indexed operator space. -/
instance differentialOperatorSpaceModule
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0) :
    Module (Polynomial C) (DifferentialOperatorSpace C K hconst) :=
  by
    unfold DifferentialOperatorSpace
    exact differentialOperatorModule hconst

/-- The additive identification of the field with its proof-indexed
differential-operator space. -/
def differentialOperatorSpaceAddEquiv
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0) :
    K ≃+ DifferentialOperatorSpace C K hconst := by
  unfold DifferentialOperatorSpace
  exact AddEquiv.refl K

/-- A differential algebra automorphism commutes with every constant-coefficient differential
operator. -/
theorem DifferentialAlgEquiv.map_differentialOperatorApply
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (tau : DifferentialAlgEquiv C K) (P : Polynomial C) (x : K) :
    tau.toAlgEquiv (differentialOperatorApply P x) =
      differentialOperatorApply P (tau.toAlgEquiv x) := by
  classical
  unfold differentialOperatorApply
  rw [Polynomial.sum_def, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, tau.toAlgEquiv.commutes, tau.map_differentialJet]

/-- A ring automorphism fixing the differential constants and commuting with the
derivation packages as a differential algebra automorphism. -/
def differentialAlgEquivOfRingEquiv
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (tau : K ≃+* K)
    (hC : ∀ c : C, tau (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ x : K, tau x′ = (tau x)′) :
    DifferentialAlgEquiv C K where
  toAlgEquiv := AlgEquiv.ofRingEquiv (f := tau) hC
  map_deriv' := hderiv

/-- Finite jet coefficients are canonically the same as finite families of
constant-coefficient differential operators. -/
noncomputable def differentialOperatorCoefficientEquiv
    {J C : Type*} [Field C] :
    (J × ℕ →₀ C) ≃ₗ[C] (J →₀ Polynomial C) :=
  (Finsupp.curryLinearEquiv C).trans
    (Finsupp.mapRange.linearEquiv
      ((Polynomial.toFinsuppIsoLinear C).trans
        (AddMonoidAlgebra.coeffLinearEquiv C)).symm)

section OperatorModule

variable {I C K : Type u}
  [Field C] [Field K] [Algebra C K] [Differential K]
  (hconst : ∀ c : C, (algebraMap C K c)′ = 0)

/-- The `C[D]`-linear simultaneous-coboundary map `k ↦ (τᵢ(k) - k)ᵢ`. -/
def simultaneousCoboundaryLinearMap
    (tau : I → DifferentialAlgEquiv C K) :
    DifferentialOperatorSpace C K hconst →ₗ[Polynomial C]
      (I → DifferentialOperatorSpace C K hconst) where
  toFun k i := differentialOperatorSpaceAddEquiv hconst
    ((tau i).toAlgEquiv ((differentialOperatorSpaceAddEquiv hconst).symm k) -
      (differentialOperatorSpaceAddEquiv hconst).symm k)
  map_add' x y := by
    apply _root_.funext
    intro i
    change (tau i).toAlgEquiv
        ((differentialOperatorSpaceAddEquiv hconst).symm (x + y)) -
        (differentialOperatorSpaceAddEquiv hconst).symm (x + y) =
      (tau i).toAlgEquiv ((differentialOperatorSpaceAddEquiv hconst).symm x) -
          (differentialOperatorSpaceAddEquiv hconst).symm x +
        ((tau i).toAlgEquiv ((differentialOperatorSpaceAddEquiv hconst).symm y) -
          (differentialOperatorSpaceAddEquiv hconst).symm y)
    simp only [map_add]
    abel
  map_smul' P k := by
    funext i
    change (tau i).toAlgEquiv
          (differentialOperatorApply P
            ((differentialOperatorSpaceAddEquiv hconst).symm k)) -
        differentialOperatorApply P
          ((differentialOperatorSpaceAddEquiv hconst).symm k) =
      differentialOperatorApply P
        ((tau i).toAlgEquiv
            ((differentialOperatorSpaceAddEquiv hconst).symm k) -
          (differentialOperatorSpaceAddEquiv hconst).symm k)
    rw [(tau i).map_differentialOperatorApply,
      differentialOperatorApply_sub]

/-- The source-boundary module before localization: complete source packets modulo the image of
one simultaneous base coboundary. -/
abbrev SourceBoundaryQuotientModule
    (tau : I → DifferentialAlgEquiv C K) :=
  (I → DifferentialOperatorSpace C K hconst) ⧸
    LinearMap.range (simultaneousCoboundaryLinearMap hconst tau)

/-- A source packet mapped to its quotient class and localized from `C[D]` to `C(D)`. -/
def sourceBoundaryQuotientFamily
    {J : Type u} (tau : I → DifferentialAlgEquiv C K) (omega : J → I → K) :
    J → LocalizedModule (Polynomial C)⁰ (SourceBoundaryQuotientModule hconst tau) :=
  localizedQuotientFamily
    (LinearMap.range (simultaneousCoboundaryLinearMap hconst tau))
    (fun j i ↦ differentialOperatorSpaceAddEquiv hconst (omega j i))

/-- The source coboundary quotient matroid over the rational differential-operator field.  Its
vectors are source-increment families modulo one simultaneous base coboundary. -/
def sourceBoundaryQuotientMatroid
    {J : Type u} (tau : I → DifferentialAlgEquiv C K) (omega : J → I → K) :
    Matroid J :=
  localizedQuotientMatroid
    (LinearMap.range (simultaneousCoboundaryLinearMap hconst tau))
    (fun j i ↦ differentialOperatorSpaceAddEquiv hconst (omega j i))

/-- The source-boundary quotient matroid has the full index type as ground set. -/
@[simp]
theorem sourceBoundaryQuotientMatroid_ground
    {J : Type u} (tau : I → DifferentialAlgEquiv C K) (omega : J → I → K) :
    (sourceBoundaryQuotientMatroid hconst tau omega).E = Set.univ := by
  simp [sourceBoundaryQuotientMatroid]

/-- Evaluation of the simultaneous-coboundary map after returning to the original field. -/
@[simp]
theorem simultaneousCoboundaryLinearMap_apply
    (tau : I → DifferentialAlgEquiv C K) (k : K) (i : I) :
    (differentialOperatorSpaceAddEquiv hconst).symm
        (simultaneousCoboundaryLinearMap hconst tau
          (differentialOperatorSpaceAddEquiv hconst k) i) =
      (tau i).toAlgEquiv k - k := rfl

/-- Apply a finite family of constant-coefficient operators to a source packet
and add the outputs in one source direction. -/
def differentialOperatorLinearCombination
    {J : Type v} (omega : J → I → K) (c : J →₀ Polynomial C) (i : I) : K :=
  c.sum fun j P ↦ differentialOperatorApply P (omega j i)

/-- Evaluation of a `C[D]`-linear combination of source packets agrees with direct operator
application after returning to the original field. -/
@[simp]
theorem differentialOperatorSpace_linearCombination_apply
    {J : Type v} (omega : J → I → K) (c : J →₀ Polynomial C) (i : I) :
    (differentialOperatorSpaceAddEquiv hconst).symm
      ((Finsupp.linearCombination (Polynomial C)
        (fun j i ↦ differentialOperatorSpaceAddEquiv hconst (omega j i)) c) i) =
        differentialOperatorLinearCombination omega c i := by
  rw [Finsupp.linearCombination_apply]
  unfold differentialOperatorLinearCombination Finsupp.sum
  simp_rw [Finset.sum_apply, Pi.smul_apply]
  rfl

/-- Polynomial differential-operator coefficients and flattened finite jet coefficients give the
same source linear combination. -/
theorem differentialOperator_linearCombination_eq_jetLinearCombination
    {J : Type v} (omega : J → I → K) (c : J →₀ Polynomial C) (i : I) :
    differentialOperatorLinearCombination omega c i =
      Finsupp.linearCombination K
        (fun p : J × ℕ ↦ differentialJet p.2 (omega p.1 i))
        (Finsupp.mapRange (algebraMap C K)
          (map_zero (algebraMap C K))
          ((differentialOperatorCoefficientEquiv (J := J) (C := C)).symm c)) := by
  unfold differentialOperatorLinearCombination differentialOperatorCoefficientEquiv
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  simp only [smul_eq_mul]
  let f : J →₀ ℕ →₀ C :=
    Finsupp.mapRange (fun P : Polynomial C => P.toFinsupp.coeff) (by simp) c
  change (c.sum fun j P ↦ differentialOperatorApply P (omega j i)) =
    f.uncurry.sum
      (fun p a ↦ algebraMap C K a * differentialJet p.2 (omega p.1 i))
  calc
    (c.sum fun j P ↦ differentialOperatorApply P (omega j i)) =
        f.sum (fun j P ↦ P.sum fun n a ↦
          algebraMap C K a * differentialJet n (omega j i)) := by
      dsimp only [f]
      rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
      rfl
    _ = f.uncurry.sum
        (fun p a ↦ (fun j n a ↦
          algebraMap C K a * differentialJet n (omega j i)) p.1 p.2 a) :=
      (Finsupp.sum_uncurry_index' f
        (fun j n a ↦ algebraMap C K a * differentialJet n (omega j i))).symm
    _ = f.uncurry.sum
        (fun p a ↦ algebraMap C K a * differentialJet p.2 (omega p.1 i)) := rfl

/-- The rank of a finite source packet is the `C(D)`-dimension of the span of its localized
source-boundary quotient classes. -/
theorem sourceBoundaryQuotientMatroid_eRk_finset
    {J : Type u} (tau : I → DifferentialAlgEquiv C K) (omega : J → I → K)
    (T : Finset J) :
    (sourceBoundaryQuotientMatroid hconst tau omega).eRk (↑T : Set J) =
      (Module.finrank (FractionRing (Polynomial C))
        (Submodule.span (FractionRing (Polynomial C))
          (sourceBoundaryQuotientFamily hconst tau omega '' (↑T : Set J))) : ℕ∞) := by
  simpa [sourceBoundaryQuotientMatroid, sourceBoundaryQuotientFamily] using!
    (localizedQuotientMatroid_eRk_finset
      (LinearMap.range (simultaneousCoboundaryLinearMap hconst tau))
      (fun j i ↦ differentialOperatorSpaceAddEquiv hconst (omega j i)) T)

/-- Independence in the source-boundary quotient is exactly the absence of a
nonzero finite differential-operator character that is one simultaneous
coboundary. -/
theorem sourceBoundaryQuotientMatroid_indep_iff
    {J : Type u} (tau : I → DifferentialAlgEquiv C K) (omega : J → I → K)
    (S : Set J) :
    (sourceBoundaryQuotientMatroid hconst tau omega).Indep S ↔
      ∀ c : S →₀ Polynomial C, c ≠ 0 → ∀ k : K, ∃ i : I,
        (tau i).toAlgEquiv k - k ≠
          differentialOperatorLinearCombination (fun s : S ↦ omega s) c i := by
  rw [sourceBoundaryQuotientMatroid,
    localizedQuotientMatroid_indep_iff_relation]
  constructor
  · intro h c hc k
    by_contra hnone
    push Not at hnone
    apply hc
    apply h c
    refine ⟨differentialOperatorSpaceAddEquiv hconst k, ?_⟩
    apply _root_.funext
    intro i
    apply (differentialOperatorSpaceAddEquiv hconst).symm.injective
    rw [simultaneousCoboundaryLinearMap_apply]
    rw [differentialOperatorSpace_linearCombination_apply]
    exact hnone i
  · intro h c hcRange
    obtain ⟨k, hk⟩ := hcRange
    by_contra hc
    obtain ⟨i, hi⟩ := h c hc ((differentialOperatorSpaceAddEquiv hconst).symm k)
    apply hi
    have hki := congrFun hk i
    have hki' := congrArg (differentialOperatorSpaceAddEquiv hconst).symm hki
    rw [show k = differentialOperatorSpaceAddEquiv hconst
      ((differentialOperatorSpaceAddEquiv hconst).symm k) by simp] at hki'
    rw [simultaneousCoboundaryLinearMap_apply] at hki'
    rw [differentialOperatorSpace_linearCombination_apply] at hki'
    exact hki'

/-- Jet-coefficient form of the source-boundary independence criterion. -/
theorem sourceBoundaryQuotientMatroid_indep_iff_no_jet_telescoping
    {J : Type u} (tau : I → DifferentialAlgEquiv C K) (omega : J → I → K)
    (S : Set J) :
    (sourceBoundaryQuotientMatroid hconst tau omega).Indep S ↔
      ∀ d : (S × ℕ) →₀ C, d ≠ 0 → ∀ k : K, ∃ i : I,
        (tau i).toAlgEquiv k - k ≠
          Finsupp.linearCombination K
            (fun p : S × ℕ ↦ differentialJet p.2 (omega p.1 i))
            (Finsupp.mapRange (algebraMap C K)
              (map_zero (algebraMap C K)) d) := by
  rw [sourceBoundaryQuotientMatroid_indep_iff hconst tau omega S]
  constructor
  · intro h d hd k
    let e := differentialOperatorCoefficientEquiv (J := S) (C := C)
    let c : S →₀ Polynomial C := e d
    have hc : c ≠ 0 := by
      exact e.map_ne_zero_iff.mpr hd
    obtain ⟨i, hi⟩ := h c hc k
    refine ⟨i, ?_⟩
    simpa [e, c] using hi.trans_eq
      (differentialOperator_linearCombination_eq_jetLinearCombination
        (fun s : S ↦ omega s) c i)
  · intro h c hc k
    let e := differentialOperatorCoefficientEquiv (J := S) (C := C)
    let d : (S × ℕ) →₀ C := e.symm c
    have hd : d ≠ 0 := by
      exact e.symm.map_ne_zero_iff.mpr hc
    obtain ⟨i, hi⟩ := h d hd k
    refine ⟨i, ?_⟩
    simpa [e, d] using hi.trans_eq
      (differentialOperator_linearCombination_eq_jetLinearCombination
        (fun s : S ↦ omega s) c i).symm

end OperatorModule

end

end GaloisForLFunctions.HTGeometry
