import GaloisForLFunctions.HTGeometry.PlacePeelSmallResponse
import GaloisForLFunctions.HTGeometry.CascadeUpperBound
import GaloisForLFunctions.HTGeometry.DerivationAlgebraicStability
import GaloisForLFunctions.HTGeometry.DerivationPrescription
import GaloisForLFunctions.HTGeometry.CascadeStateIndependence
import GaloisForLFunctions.HTGeometry.LocalInverseHypertranscendence
import GaloisForLFunctions.HTGeometry.FractionRingAdjoinX
import GaloisForLFunctions.HTGeometry.RittDifferentialAlgebraicBridge
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative
import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import GaloisForLFunctions.HTGeometry.HyperexponentialPrimitive

/-!
# Universal first-order entire cascade: unit-response place cancellation

The general algebraic cascade has a unit-sized response at a place above infinity, so the
small-response estimate does not apply.  Its replacement is the exact mixed-derivative identity:
the shifted logarithmic derivative is a coordinate derivative of the law's logarithmic derivative.
Consequently it gains the second place degree from differentiation rather than from a small
response.

This file also packages every finite family of algebraic branch elements into a single primitive
extension and isolates the law-independent reflection step from entrywise place limits to
nonvanishing of a determinant.  These are exact components of the general place peel; they add no
axiom or analytic assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Finite algebraic branch data admit simultaneous coordinates in one simple extension.**

Every entry is represented by a polynomial of degree below the primitive element's minimal
polynomial.  This is the simultaneous branch-packaging step needed before constructing coordinate
derivations and compatible places. -/
theorem exists_primitive_representation_of_finite_algebraic_family
    {k L : Type*} [Field k] [CharZero k] [Field L] [Algebra k L]
    {ι : Type*} [Fintype ι] (alpha : ι → L)
    (halpha : ∀ i, IsAlgebraic k (alpha i)) :
    ∃ theta : L, ∃ q : ι → Polynomial k, IsAlgebraic k theta ∧
      (∀ i, (q i).natDegree < (minpoly k theta).natDegree) ∧
      ∀ i, alpha i = Polynomial.aeval theta (q i) := by
  classical
  let E : IntermediateField k L := IntermediateField.adjoin k (Set.range alpha)
  letI : Finite (Set.range alpha) := Set.finite_range alpha
  haveI : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin fun x hx => by
    rcases hx with ⟨i, rfl⟩
    exact (halpha i).isIntegral
  let pb : PowerBasis k E := Field.powerBasisOfFiniteOfSeparable k E
  let alphaE : ι → E := fun i =>
    ⟨alpha i, IntermediateField.subset_adjoin k (Set.range alpha) (Set.mem_range_self i)⟩
  choose q hqdeg hq using fun i => pb.exists_eq_aeval (alphaE i)
  let theta : L := algebraMap E L pb.gen
  have htheta : IsAlgebraic k theta := by
    exact (Algebra.IsAlgebraic.isAlgebraic pb.gen).algHom (IsScalarTower.toAlgHom k E L)
  have hmin : minpoly k theta = minpoly k pb.gen := by
    simpa [theta] using minpoly.algebraMap_eq (algebraMap E L).injective pb.gen
  refine ⟨theta, q, htheta, ?_, ?_⟩
  · intro i
    rw [hmin, pb.natDegree_minpoly]
    exact hqdeg i
  · intro i
    let incl : E →ₐ[k] L := IsScalarTower.toAlgHom k E L
    calc
      alpha i = incl (alphaE i) := by rfl
      _ = incl (Polynomial.aeval pb.gen (q i)) := congrArg incl (hq i)
      _ = Polynomial.aeval (incl pb.gen) (q i) :=
        (Polynomial.aeval_algHom_apply incl pb.gen (q i)).symm
      _ = Polynomial.aeval theta (q i) := by rfl

/-- **A finite packet in a relative algebraic closure lies in one simple extension.** -/
theorem exists_primitive_representation_of_finite_family_mem_algebraicClosure
    {k L : Type*} [Field k] [Field L] [CharZero L] [Algebra k L]
    (E : IntermediateField k L) {ι : Type*} [Fintype ι] (alpha : ι → L)
    (halpha : ∀ i, alpha i ∈ algebraicClosure E L) :
    ∃ theta : L, ∃ q : ι → Polynomial E, IsAlgebraic E theta ∧
      (∀ i, (q i).natDegree < (minpoly E theta).natDegree) ∧
      ∀ i, alpha i = Polynomial.aeval theta (q i) := by
  letI : CharZero E := (algebraMap E L).charZero
  exact exists_primitive_representation_of_finite_algebraic_family alpha
    (fun i => mem_algebraicClosure_iff.mp (halpha i))

/-- **Commutation on the state field extends through its algebraic branch field.** -/
theorem derivation_commute_of_isAlgebraic_over
    {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    (E : IntermediateField C L) [Algebra.IsAlgebraic E L]
    (D₁ D₂ : Derivation C L L)
    (hcomm : ∀ x : L, x ∈ E → D₁ (D₂ x) = D₂ (D₁ x)) :
    ∀ x : L, D₁ (D₂ x) = D₂ (D₁ x) := by
  intro x
  have hzero : ⁅D₁, D₂⁆ x = 0 := derivationBase_eq_zero_of_isAlgebraic E ⁅D₁, D₂⁆
    (fun y hy => by rw [Derivation.commutator_apply, hcomm y hy, sub_self])
    (Algebra.IsAlgebraic.isAlgebraic x)
  rw [Derivation.commutator_apply] at hzero
  exact sub_eq_zero.mp hzero

/-- **An affine mixed law on the state field extends through every algebraic branch.**

The commutator defect itself is a derivation.  Once it vanishes on the state field, separability in
characteristic zero forces it to vanish on all algebraic branch elements. -/
theorem derivation_mixed_affine_of_isAlgebraic_over
    {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    (E : IntermediateField C L) [Algebra.IsAlgebraic E L]
    (D E' : Derivation C L L) (c : L)
    (hmix : ∀ x : L, x ∈ E → D (E' x) = E' (D x) + c * E' x) :
    ∀ x : L, D (E' x) = E' (D x) + c * E' x := by
  intro x
  have hzero : (⁅D, E'⁆ - c • E') x = 0 :=
    derivationBase_eq_zero_of_isAlgebraic E (⁅D, E'⁆ - c • E')
      (fun y hy => by simp [Derivation.commutator_apply, hmix y hy])
      (Algebra.IsAlgebraic.isAlgebraic x)
  change D (E' x) - E' (D x) - c * E' x = 0 at hzero
  linear_combination hzero

/-- **A commuting family of state-field derivations extends simultaneously and still commutes.** -/
theorem exists_commuting_derivation_extension_family
    {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    (E : IntermediateField C L) [Algebra.IsAlgebraic E L]
    {ι : Type*} (D : ι → Derivation C E E)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x)) :
    ∃ D' : ι → Derivation C L L,
      (∀ i a, D' i (algebraMap E L a) = algebraMap E L (D i a)) ∧
      ∀ i j x, D' i (D' j x) = D' j (D' i x) := by
  letI : CharZero E := (algebraMap E L).charZero
  letI : Algebra.IsIntegral E L := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable E L := by infer_instance
  choose D' hD' using fun i => exists_derivation_extension (K := C) (F := E) (L := L) (D i)
  refine ⟨D', hD', ?_⟩
  intro i j
  refine derivation_commute_of_isAlgebraic_over E (D' i) (D' j) ?_
  intro x hx
  let a : E := ⟨x, hx⟩
  change D' i (D' j (algebraMap E L a)) = D' j (D' i (algebraMap E L a))
  rw [hD' j a, hD' i (D j a), hD' i a, hD' j (D i a), hcomm]

/-- **Law and coordinate derivations extend together with every affine mixed law intact.** -/
theorem exists_mixed_affine_commuting_derivation_extension_family
    {C L : Type*} [Field C] [CharZero C] [Field L] [CharZero L] [Algebra C L]
    (E : IntermediateField C L) [Algebra.IsAlgebraic E L]
    {ι : Type*} (D : Derivation C E E) (P : ι → Derivation C E E) (c : ι → E)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x))
    (hmix : ∀ i x, D (P i x) = P i (D x) + c i * P i x) :
    ∃ D' : Derivation C L L, ∃ P' : ι → Derivation C L L,
      (∀ a, D' (algebraMap E L a) = algebraMap E L (D a)) ∧
      (∀ i a, P' i (algebraMap E L a) = algebraMap E L (P i a)) ∧
      (∀ i j x, P' i (P' j x) = P' j (P' i x)) ∧
      ∀ i x, D' (P' i x) = P' i (D' x) + algebraMap E L (c i) * P' i x := by
  letI : CharZero E := (algebraMap E L).charZero
  letI : Algebra.IsIntegral E L := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable E L := by infer_instance
  obtain ⟨P', hP'res, hP'comm⟩ :=
    exists_commuting_derivation_extension_family E P hcomm
  obtain ⟨D', hD'⟩ := exists_derivation_extension (K := C) (F := E) (L := L) D
  refine ⟨D', P', hD', hP'res, hP'comm, ?_⟩
  intro i
  refine derivation_mixed_affine_of_isAlgebraic_over E D' (P' i)
    (algebraMap E L (c i)) ?_
  intro x hx
  let a : E := ⟨x, hx⟩
  change D' (P' i (algebraMap E L a)) =
    P' i (D' (algebraMap E L a)) + algebraMap E L (c i) * P' i (algebraMap E L a)
  rw [hP'res i a, hD' (P i a), hD' a, hP'res i (D a),
    ← map_mul, ← map_add, hmix]

/-- **Every algebraically independent family carries its concrete commuting coordinate frame.** -/
theorem exists_commuting_coordinate_derivations_adjoin
    {C L : Type*} [Field C] [CharZero C] [Field L] [Algebra C L]
    {ι : Type*} [DecidableEq ι] (x : ι → L) (hx : AlgebraicIndependent C x) :
    let E := IntermediateField.adjoin C (Set.range x)
    let xE : ι → E := fun i =>
      ⟨x i, IntermediateField.subset_adjoin C (Set.range x) (Set.mem_range_self i)⟩
    ∃ P : ι → Derivation C E E,
      (∀ i j, P i (xE j) = algebraMap C E (if j = i then 1 else 0)) ∧
      ∀ i j y, P i (P j y) = P j (P i y) := by
  classical
  let E := IntermediateField.adjoin C (Set.range x)
  let xE : ι → E := fun i =>
    ⟨x i, IntermediateField.subset_adjoin C (Set.range x) (Set.mem_range_self i)⟩
  choose P hP using fun i => exists_derivation_adjoin hx (fun j => if j = i then 1 else 0)
  have hP' : ∀ i j, P i (xE j) = algebraMap C E (if j = i then 1 else 0) := hP
  refine ⟨P, hP', ?_⟩
  have hxTop : IntermediateField.adjoin C (Set.range xE) = ⊤ := by
    simpa [E, xE] using adjoin_range_lift_eq_top x x rfl
  intro i j y
  have hzero : ⁅P i, P j⁆ y = 0 := derivationBase_eq_zero_of_mem_adjoin
    (S := Set.range xE) ⁅P i, P j⁆
    (fun _ hy => by
      rcases hy with ⟨k, rfl⟩
      rw [Derivation.commutator_apply, hP' j k, hP' i k]
      split_ifs <;> simp)
    (by rw [hxTop]; exact IntermediateField.mem_top)
  rw [Derivation.commutator_apply] at hzero
  exact sub_eq_zero.mp hzero

/-- **A commuting family extends through an arbitrary algebraic field tower.**

This tower form is the one needed for the relative algebraic closure of an actual state field: the
base is a field type, rather than an intermediate field of the extension written over the original
constant field. -/
theorem exists_commuting_derivation_extension_family_tower
    {C F L : Type*} [Field C] [CharZero C] [Field F] [CharZero F]
    [Field L] [CharZero L] [Algebra C F] [Algebra F L] [Algebra C L]
    [IsScalarTower C F L] [Algebra.IsAlgebraic F L]
    {ι : Type*} (D : ι → Derivation C F F)
    (hcomm : ∀ i j x, D i (D j x) = D j (D i x)) :
    ∃ D' : ι → Derivation C L L,
      (∀ i a, D' i (algebraMap F L a) = algebraMap F L (D i a)) ∧
      ∀ i j x, D' i (D' j x) = D' j (D' i x) := by
  letI : Algebra.IsIntegral F L := Algebra.IsAlgebraic.isIntegral
  letI : Algebra.IsSeparable F L := by infer_instance
  choose D' hD' using fun i => exists_derivation_extension (K := C) (F := F) (L := L) (D i)
  refine ⟨D', hD', ?_⟩
  intro i j x
  have hzero : ⁅D' i, D' j⁆ x = 0 := by
    apply derivation_eq_zero_of_isAlgebraic (C := F) (⊥ : IntermediateField F L)
      (toIntDerivation ⁅D' i, D' j⁆)
    · intro y hy
      rw [IntermediateField.mem_bot] at hy
      obtain ⟨a, rfl⟩ := hy
      rw [toIntDerivation_apply, Derivation.commutator_apply, hD', hD', hD', hD',
        ← map_sub, sub_eq_zero.mpr (hcomm i j a), map_zero]
    · exact Algebra.IsAlgebraic.isAlgebraic x
  rw [Derivation.commutator_apply] at hzero
  exact sub_eq_zero.mp hzero

section CascadeModel

open Filter Set Topology GaloisForLFunctions Bottcher
open scoped Differential

local instance cascadeUnitCostDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

noncomputable local instance cascadeUnitCostRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

noncomputable local instance cascadeUnitCostComplexAlgebra :
    Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra

local instance cascadeUnitCostScalarTower :
    IsScalarTower ℂ (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable local instance cascadeUnitCostDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

local instance cascadeUnitCostCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective

private theorem cascadeUnitCost_deriv_complexConst (c : ℂ) :
    (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ = 0 := by
  change (algebraMap (RatFunc ℂ) (meroField Set.univ)
    (algebraMap ℂ (RatFunc ℂ) c))′ = 0
  change (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ (algebraMap ℂ (RatFunc ℂ) c))′ = 0
  rw [meroField_deriv_ratfuncToMero]
  have hzero : ratFuncCoordinateDerivation ℂ (algebraMap ℂ (RatFunc ℂ) c) = 0 :=
    (ratFuncCoordinateDerivation_eq_zero_iff
      (algebraMap ℂ (RatFunc ℂ) c)).mpr ⟨c, rfl⟩
  rw [hzero, map_zero]

private theorem cascadeUnitCost_deriv_smul (c : ℂ)
    (x : meroField (Set.univ : Set ℂ)) : (c • x)′ = c • x′ := by
  rw [Algebra.smul_def c x, differential_deriv_mul,
    cascadeUnitCost_deriv_complexConst, zero_mul, zero_add, Algebra.smul_def]

private theorem cascadeUnitCost_deriv_one :
    (1 : meroField (Set.univ : Set ℂ))′ = 0 := by
  have h := cascadeUnitCost_deriv_complexConst (1 : ℂ)
  rwa [map_one] at h

private theorem cascadeUnitCost_deriv_leibniz
    (a b : meroField (Set.univ : Set ℂ)) : (a * b)′ = a • b′ + b • a′ := by
  rw [differential_deriv_mul]
  simp only [smul_eq_mul]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
private noncomputable def cascadeUnitCostComplexDerivation :
    Derivation ℂ (meroField (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) where
  toLinearMap :=
    { toAddHom := { toFun := fun x => x′, map_add' := fun x y => map_add _ x y }
      map_smul' := cascadeUnitCost_deriv_smul }
  map_one_eq_zero' := cascadeUnitCost_deriv_one
  leibniz' := cascadeUnitCost_deriv_leibniz

@[simp] private theorem cascadeUnitCostComplexDerivation_apply
    (x : meroField (Set.univ : Set ℂ)) : cascadeUnitCostComplexDerivation x = x′ := rfl

/-- **The coordinate and every cascade state are independent in the actual meromorphic field.** -/
theorem algebraicIndependent_cascadeMero_over_complex
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (n : ℕ) :
    AlgebraicIndependent ℂ (fun i : Fin (n + 1) => cascadeMero hfan i) := by
  rw [algebraicIndependent_iff]
  intro q hq
  have hpoint := (aeval_analyticMeroElement_eq_zero_iff isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ
    (fun i : Fin (n + 1) => entireCascade f i)
    (fun i => analyticOnNhd_entireCascade hfan i) q).mp hq
  by_contra hq0
  exact noRelation_entireCascade_of_transcendental (n + 1) f hall q hq0
    (fun z => hpoint z (Set.mem_univ z))

/-- **Every rational-coordinate coefficient belongs to the field generated by the zeroth
cascade state over the complex constants.** -/
theorem algebraMap_ratFunc_mem_adjoin_cascadeMero_zero
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (r : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r ∈
      IntermediateField.adjoin ℂ {cascadeMero hfan 0} := by
  let F₀ := IntermediateField.adjoin ℂ {cascadeMero hfan 0}
  have hX : algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) RatFunc.X ∈ F₀ := by
    rw [← cascadeMero_zero hfan]
    exact IntermediateField.subset_adjoin ℂ {cascadeMero hfan 0}
      (Set.mem_singleton (cascadeMero hfan 0))
  have hpoly : ∀ p : Polynomial ℂ,
      algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) ∈ F₀ := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add, map_add]
        exact add_mem hp hq
    | monomial n a =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
        refine mul_mem ?_ (pow_mem hX n)
        change algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
          (algebraMap ℂ (RatFunc ℂ) a) ∈ F₀
        rw [← IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (meroField (Set.univ : Set ℂ))]
        exact IntermediateField.algebraMap_mem F₀ a
  induction r using RatFunc.induction_on with
  | _ p q hq =>
      rw [map_div₀ (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))]
      exact div_mem (hpoly p) (hpoly q)

/-- **The rational-coordinate cascade field embeds into the complex-coordinate cascade field.**

This comparison is required to transport the already-proved algebraicity of actual derivative
branches from the rational state model to the state model supporting the Kronecker frame. -/
theorem ratFuncCascadeStateField_restrictScalars_le_complexCascadeStateField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (n : ℕ) :
    (IntermediateField.adjoin (RatFunc ℂ) (Set.range (cascadeStates hfan n))).restrictScalars ℂ ≤
      IntermediateField.adjoin ℂ
        (Set.range (fun i : Fin (n + 1) => cascadeMero hfan i)) := by
  let E := IntermediateField.adjoin ℂ
    (Set.range (fun i : Fin (n + 1) => cascadeMero hfan i))
  have hF₀ : IntermediateField.adjoin ℂ {cascadeMero hfan 0} ≤ E := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact IntermediateField.subset_adjoin ℂ _
      (Set.mem_range_self (⟨0, by omega⟩ : Fin (n + 1)))
  intro y hy
  rw [IntermediateField.mem_restrictScalars] at hy
  refine IntermediateField.adjoin_induction (RatFunc ℂ)
    (p := fun w (_ : w ∈ IntermediateField.adjoin (RatFunc ℂ)
      (Set.range (cascadeStates hfan n))) => w ∈ E)
    ?_ ?_ ?_ ?_ ?_ hy
  · intro w hw
    rcases hw with ⟨i, rfl⟩
    rw [cascadeStates]
    exact IntermediateField.subset_adjoin ℂ _
      (Set.mem_range_self (⟨i.1 + 1, by omega⟩ : Fin (n + 1)))
  · intro r
    exact hF₀ (algebraMap_ratFunc_mem_adjoin_cascadeMero_zero hfan r)
  · intro x y _ _ hx hy
    exact add_mem hx hy
  · intro x _ hx
    exact inv_mem hx
  · intro x y _ _ hx hy
    exact mul_mem hx hy

/-- **Every actual derivative branch is algebraic over the complex cascade-state field.**

This puts branch elements and coordinate derivations over one and the same actual field, rather
than over merely isomorphic rational-function and complex-coordinate presentations. -/
theorem cascadeMeroDeriv_mem_complexCascadeStateField_algebraicClosure
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    ∀ i : Fin (n + 1), cascadeMeroDeriv hfan i ∈
      algebraicClosure
        (IntermediateField.adjoin ℂ
          (Set.range (fun j : Fin (n + 1) => cascadeMero hfan j)))
        (meroField (Set.univ : Set ℂ)) := by
  intro i
  let Eᵣ := IntermediateField.adjoin (RatFunc ℂ) (Set.range (cascadeStates hfan n))
  let E := IntermediateField.adjoin ℂ
    (Set.range (fun j : Fin (n + 1) => cascadeMero hfan j))
  have hsmall : cascadeMeroDeriv hfan i ∈ algebraicClosure Eᵣ
      (meroField (Set.univ : Set ℂ)) :=
    cascadeMeroDeriv_mem_algebraicClosure hfan (fun k _ => hall k) h1
      (fun k _ => pairAlgIndep_of_transcendental hfan hall k) i (by omega)
  have halgSmall : IsAlgebraic Eᵣ (cascadeMeroDeriv hfan i) :=
    mem_algebraicClosure_iff.mp hsmall
  have hle : Eᵣ.restrictScalars ℂ ≤ E :=
    ratFuncCascadeStateField_restrictScalars_le_complexCascadeStateField hfan n
  have halgRestricted : IsAlgebraic (Eᵣ.restrictScalars ℂ) (cascadeMeroDeriv hfan i) := by
    change IsAlgebraic Eᵣ (cascadeMeroDeriv hfan i)
    exact halgSmall
  exact mem_algebraicClosure_iff.mpr
    (isAlgebraic_of_intermediateField_le hle halgRestricted)

/-- **Actual arbitrary-cascade branches, law, and commuting coordinate frame coexist in one
algebraic field.**

The branch field is the literal relative algebraic closure of the actual meromorphic state field.
Its law derivation is the restriction of ordinary meromorphic differentiation, so its value on
each state is the corresponding actual derivative branch.  The Kronecker coordinate derivations
extend simultaneously and remain pairwise commuting throughout that same branch field. -/
theorem exists_actualCascade_algebraicBranch_lawCoordinateFrame
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    let x : Fin (n + 1) → meroField (Set.univ : Set ℂ) := fun i => cascadeMero hfan i
    let E := IntermediateField.adjoin ℂ (Set.range x)
    let xE : Fin (n + 1) → E := fun i =>
      ⟨x i, IntermediateField.subset_adjoin ℂ (Set.range x) (Set.mem_range_self i)⟩
    let B := algebraicClosure E (meroField (Set.univ : Set ℂ))
    ∃ b : Fin (n + 1) → B, ∃ D : Derivation ℂ B B,
      ∃ P : Fin (n + 1) → Derivation ℂ B B,
        (∀ i, ((b i : B) : meroField (Set.univ : Set ℂ)) = cascadeMeroDeriv hfan i) ∧
        (∀ i, D (algebraMap E B (xE i)) = b i) ∧
        (∀ i j, P i (algebraMap E B (xE j)) =
          algebraMap E B (algebraMap ℂ E (if j = i then 1 else 0))) ∧
        ∀ i j y, P i (P j y) = P j (P i y) := by
  classical
  let M := meroField (Set.univ : Set ℂ)
  let x : Fin (n + 1) → M := fun i => cascadeMero hfan i
  let E := IntermediateField.adjoin ℂ (Set.range x)
  let xE : Fin (n + 1) → E := fun i =>
    ⟨x i, IntermediateField.subset_adjoin ℂ (Set.range x) (Set.mem_range_self i)⟩
  let B := algebraicClosure E M
  letI : CharZero E := (algebraMap E M).charZero
  letI : CharZero B := (algebraMap B M).charZero
  have hstateDeriv : ∀ a : E, cascadeUnitCostComplexDerivation (a : M) ∈ B := by
    intro a
    exact (derivationBase_mem_of_mem_adjoin cascadeUnitCostComplexDerivation
      (M := B.restrictScalars ℂ)
      (fun y hy => by
        rcases hy with ⟨i, rfl⟩
        constructor
        · exact mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (xE i))
        · change (cascadeMero hfan i)′ ∈ B.restrictScalars ℂ
          rw [← differentialJet_zero (cascadeMero hfan i)]
          rw [← differentialJet_succ, differentialJet_one_cascadeMero]
          exact cascadeMeroDeriv_mem_complexCascadeStateField_algebraicClosure hfan hall h1 i)
      a.2).2
  have hBstable : ∀ y : M, y ∈ B → cascadeUnitCostComplexDerivation y ∈ B := by
    intro y hy
    apply derivationInt_mem_algebraicClosure E
      (toIntDerivation cascadeUnitCostComplexDerivation) ?_ hy
    intro z hz
    rw [IntermediateField.mem_bot] at hz
    obtain ⟨a, rfl⟩ := hz
    exact hstateDeriv a
  let D : Derivation ℂ B B :=
    restrictDerivation cascadeUnitCostComplexDerivation (B.restrictScalars ℂ) hBstable
  obtain ⟨P₀, hP₀, hcomm₀⟩ :=
    exists_commuting_coordinate_derivations_adjoin x
      (algebraicIndependent_cascadeMero_over_complex hfan hall n)
  obtain ⟨P, hPres, hcomm⟩ :=
    exists_commuting_derivation_extension_family_tower (L := B) P₀ hcomm₀
  let b : Fin (n + 1) → B := fun i =>
    ⟨cascadeMeroDeriv hfan i,
      cascadeMeroDeriv_mem_complexCascadeStateField_algebraicClosure hfan hall h1 i⟩
  refine ⟨b, D, P, ?_, ?_, ?_, hcomm⟩
  · intro i
    rfl
  · intro i
    apply Subtype.ext
    change cascadeUnitCostComplexDerivation (cascadeMero hfan i) = cascadeMeroDeriv hfan i
    rw [cascadeUnitCostComplexDerivation_apply, ← differentialJet_zero (cascadeMero hfan i)]
    rw [← differentialJet_succ, differentialJet_one_cascadeMero]
  · intro i j
    rw [hPres, hP₀]

/-- **The actual meromorphic cascade state field carries a commuting Kronecker frame.** -/
theorem exists_commuting_coordinate_derivations_cascadeStateField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (n : ℕ) :
    let x : Fin (n + 1) → meroField (Set.univ : Set ℂ) := fun i => cascadeMero hfan i
    let E := IntermediateField.adjoin ℂ (Set.range x)
    let xE : Fin (n + 1) → E := fun i =>
      ⟨x i, IntermediateField.subset_adjoin ℂ (Set.range x) (Set.mem_range_self i)⟩
    ∃ P : Fin (n + 1) → Derivation ℂ E E,
      (∀ i j, P i (xE j) = algebraMap ℂ E (if j = i then 1 else 0)) ∧
      ∀ i j y, P i (P j y) = P j (P i y) := by
  exact exists_commuting_coordinate_derivations_adjoin
    (fun i : Fin (n + 1) => cascadeMero hfan i)
    (algebraicIndependent_cascadeMero_over_complex hfan hall n)

/-- **All derivative branches through a finite cascade height lie in one simple extension.**

This instantiates simultaneous primitive-element packaging on the actual meromorphic cascade-state
derivatives already known to lie in the relative algebraic closure of the state field. -/
theorem exists_primitive_representation_cascadeMeroDeriv
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hft : ∀ k, k < n → TranscendentalEntire (f k))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1)
    (hindep : ∀ k, k < n →
      PairAlgIndep (cascadeMero hfan k) (cascadeMero hfan (k + 1))) :
    let E := IntermediateField.adjoin (RatFunc ℂ) (Set.range (cascadeStates hfan n))
    ∃ theta : meroField (Set.univ : Set ℂ),
      ∃ q : Fin (n + 1) → Polynomial E, IsAlgebraic E theta ∧
        (∀ i : Fin (n + 1), (q i).natDegree < (minpoly E theta).natDegree) ∧
        ∀ i : Fin (n + 1), cascadeMeroDeriv hfan i = Polynomial.aeval theta (q i) := by
  let E := IntermediateField.adjoin (RatFunc ℂ) (Set.range (cascadeStates hfan n))
  exact exists_primitive_representation_of_finite_family_mem_algebraicClosure E
    (fun i : Fin (n + 1) => cascadeMeroDeriv hfan i)
    (fun i => cascadeMeroDeriv_mem_algebraicClosure hfan hft h1 hindep i (by omega))

/-- **Transcendence alone supplies branch packaging without an independence premise.** -/
theorem exists_primitive_representation_cascadeMeroDeriv_of_transcendental
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n → DifferentiallyAlgebraicOfOrder (f k) 1) :
    let E := IntermediateField.adjoin (RatFunc ℂ) (Set.range (cascadeStates hfan n))
    ∃ theta : meroField (Set.univ : Set ℂ),
      ∃ q : Fin (n + 1) → Polynomial E, IsAlgebraic E theta ∧
        (∀ i : Fin (n + 1), (q i).natDegree < (minpoly E theta).natDegree) ∧
        ∀ i : Fin (n + 1), cascadeMeroDeriv hfan i = Polynomial.aeval theta (q i) := by
  exact exists_primitive_representation_cascadeMeroDeriv hfan (fun k _ => hall k) h1
    (fun k _ => pairAlgIndep_of_transcendental hfan hall k)

end CascadeModel

/-- **On a one-variable polynomial factor, the mixed law is forced by the coordinate-law
response.** -/
theorem derivation_eval_mixed_of_eq_one
    {A : Type*} [CommRing A] [Algebra A K]
    (D E : Derivation A K K) {F : Subfield K} {x : K}
    (hDF : ∀ a ∈ F, D a = 0) (hEF : ∀ a ∈ F, E a = 0) (hEx : E x = 1)
    (p : Polynomial K) (hp : CoeffsIn F p) :
    E (D (p.eval x)) =
      D (E (p.eval x)) + E (D x) * E (p.eval x) := by
  have hp' : CoeffsIn F p.derivative := hp.derivative
  have hDp : D (p.eval x) = p.derivative.eval x * D x :=
    derivation_eval_of_coeff D (fun i => hDF _ (hp i)) x
  have hEp : E (p.eval x) = p.derivative.eval x := by
    rw [derivation_eval_of_coeff E (fun i => hEF _ (hp i)) x, hEx, mul_one]
  have hDp' : D (p.derivative.eval x) = p.derivative.derivative.eval x * D x :=
    derivation_eval_of_coeff D (fun i => hDF _ (hp' i)) x
  have hEp' : E (p.derivative.eval x) = p.derivative.derivative.eval x := by
    rw [derivation_eval_of_coeff E (fun i => hEF _ (hp' i)) x, hEx, mul_one]
  rw [hDp, E.leibniz, hEp', hEp, hDp']
  simp only [smul_eq_mul]
  ring

/-- **Exact logarithmic cancellation behind the unit-response place peel.** -/
theorem placeShift_logDeriv_eq_of_mixed
    {A : Type*} [CommRing A] [Algebra A K]
    (D E : Derivation A K K) {c Φ : K} (hΦ : Φ ≠ 0)
    (hmix : E (D Φ) = D (E Φ) + c * E Φ) :
    placeShift D c (E Φ / Φ) = E (D Φ / Φ) := by
  rw [placeShift_apply, Derivation.leibniz_div, Derivation.leibniz_div]
  simp only [smul_eq_mul]
  rw [hmix]
  field_simp
  ring

/-- **Mixed-derivative cancellation supplies the two-degree place decay.**

The response `c` need not be small.  Exact cancellation rewrites the shifted logarithmic
derivative as one coordinate derivative of a one-degree-small logarithmic law, and the rational
derivation bound supplies the other degree. -/
theorem placeDegLE_placeShift_logDeriv_of_mixed
    (v : HeightOneSpectrum R)
    {A : Type*} [CommRing A] [Algebra A K]
    (D E : Derivation A K K) {F : Subfield K} {x c Φ : K}
    (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hEF : ∀ a ∈ F, E a = 0) (hExv : v.valuation K (E x) ≤ 1)
    (hΦ : Φ ≠ 0) (hmix : E (D Φ) = D (E Φ) + c * E Φ)
    (hlogmem : D Φ / Φ ∈ RatIn F x)
    (hlogdeg : PlaceDegLE v (v.valuation K x)⁻¹ (D Φ / Φ)) :
    PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (placeShift D c (E Φ / Φ)) := by
  rw [placeShift_logDeriv_eq_of_mixed D E hΦ hmix]
  have hdrop := valuation_derivation_mul_le_of_ratIn v E hF hEF hx hExv hlogmem
  have hstep : v.valuation K (E (D Φ / Φ)) * v.valuation K x
      ≤ (v.valuation K x)⁻¹ := le_trans hdrop hlogdeg
  have hx0 : v.valuation K x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hmul := mul_le_mul' hstep (le_refl ((v.valuation K x)⁻¹))
  rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one] at hmul
  exact hmul

/-- **Polynomial-factor form of the unit-response Wronskian cancellation.**

This is the exact leading-column estimate consumed by the place peel. -/
theorem placeDegLE_placeShift_logFactor_of_mixed
    (v : HeightOneSpectrum R)
    {A : Type*} [CommRing A] [Algebra A K]
    (D E : Derivation A K K) {F : Subfield K} {x c : K} {p : Polynomial K}
    (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hEF : ∀ a ∈ F, E a = 0) (hEx : E x = 1)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree)
    (hmix : E (D (p.eval x)) = D (E (p.eval x)) + c * E (p.eval x))
    (hlogmem : D (p.eval x) / p.eval x ∈ RatIn F x)
    (hlogdeg : PlaceDegLE v (v.valuation K x)⁻¹ (D (p.eval x) / p.eval x)) :
    PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (placeShift D c ((Polynomial.derivative p).eval x / p.eval x)) := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  have hpx : p.eval x ≠ 0 := eval_ne_zero_of_valuation v hF hp hx hp0
  have hExv : v.valuation K (E x) ≤ 1 := by rw [hEx, Valuation.map_one]
  have hEp : E (p.eval x) = (Polynomial.derivative p).eval x := by
    rw [derivation_eval_of_coeff E (fun i => hEF _ (hp i)) x, hEx, mul_one]
  rw [← hEp]
  exact placeDegLE_placeShift_logDeriv_of_mixed v D E hF hx hEF hExv hpx hmix
    hlogmem hlogdeg

/-- **The newest place column vanishes below its border under the exact mixed law.**

Unlike `placeLim_below_of_borderShape_of_small_response`, this permits a unit-sized response. -/
theorem placeLim_below_of_borderShape_of_mixed
    (v : HeightOneSpectrum R)
    {A : Type*} [CommRing A] [Algebra A K]
    (D E : Derivation A K K) {F : Subfield K} {x c : K} {p : Polynomial K}
    (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hDF : ∀ a ∈ F, D a = 0) (hDx : D x ∈ RatIn F x)
    (hDxv : v.valuation K (D x) ≤ 1) (hc : c ∈ RatIn F x)
    (hcv : v.valuation K c ≤ 1)
    (hEF : ∀ a ∈ F, E a = 0) (hEx : E x = 1)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree)
    (hmix : E (D (p.eval x)) = D (E (p.eval x)) + c * E (p.eval x))
    (hlogmem : D (p.eval x) / p.eval x ∈ RatIn F x)
    (hlogdeg : PlaceDegLE v (v.valuation K x)⁻¹ (D (p.eval x) / p.eval x))
    {u : K} (hu : u ∈ RatIn F x)
    (hshape : PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (u - (Polynomial.derivative p).eval x / p.eval x))
    (r : ℕ) :
    PlaceLim v (v.valuation K x)⁻¹
      (x * ((placeShift D c)^[r] (placeShift D c u))) 0 := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  exact placeLim_below_of_borderShape v D hF hx hDF hDx hDxv hc hcv hp hp0 hu le_rfl
    hshape
    (placeDegLE_placeShift_logFactor_of_mixed v D E hF hx hEF hEx hp hdeg hmix
      hlogmem hlogdeg)
    r

/-- **The actual unit response of a coordinate law supplies two-degree Wronskian decay.**

The response is constructed internally as `E (D x)`.  Polynomial chain rules force the mixed
identity, while rational-class closure and the unit bound on `D x` provide the logarithmic-law
input to exact cancellation. -/
theorem placeDegLE_placeShift_logFactor_of_unit_response
    (v : HeightOneSpectrum R)
    {A : Type*} [CommRing A] [Algebra A K]
    (D E : Derivation A K K) {F : Subfield K} {x : K} {p : Polynomial K}
    (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hDF : ∀ a ∈ F, D a = 0) (hDx : D x ∈ RatIn F x)
    (hDxv : v.valuation K (D x) ≤ 1)
    (hEF : ∀ a ∈ F, E a = 0) (hEx : E x = 1)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree) :
    PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (placeShift D (E (D x)) ((Polynomial.derivative p).eval x / p.eval x)) := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  have hpx : p.eval x ≠ 0 := eval_ne_zero_of_valuation v hF hp hx hp0
  have hDlog : D (p.eval x) / p.eval x =
      ((Polynomial.derivative p).eval x / p.eval x) * D x := by
    rw [derivation_eval_of_coeff D (fun i => hDF _ (hp i)) x]
    field_simp
  have hlogmem : D (p.eval x) / p.eval x ∈ RatIn F x := by
    rw [hDlog]
    exact ratIn_mul (ratIn_logFactor v hF hx hp hp0) hDx
  have hlogdeg : PlaceDegLE v (v.valuation K x)⁻¹ (D (p.eval x) / p.eval x) := by
    rw [hDlog]
    simpa only [mul_one] using PlaceDegLE.mul v
      (placeDegLE_logFactor v hF hp hx hdeg) hDxv
  exact placeDegLE_placeShift_logFactor_of_mixed v D E hF hx hEF hEx hp hdeg
    (derivation_eval_mixed_of_eq_one D E hDF hEF hEx p hp) hlogmem hlogdeg

/-- **Full below-border place peel for the law's internally constructed unit response.** -/
theorem placeLim_below_of_borderShape_of_unit_response
    (v : HeightOneSpectrum R)
    {A : Type*} [CommRing A] [Algebra A K]
    (D E : Derivation A K K) {F : Subfield K} {x : K} {p : Polynomial K}
    (hF : PlaceTrivialOn v F) (hx : 1 < v.valuation K x)
    (hDF : ∀ a ∈ F, D a = 0) (hDx : D x ∈ RatIn F x)
    (hDxv : v.valuation K (D x) ≤ 1)
    (hc : E (D x) ∈ RatIn F x) (hcv : v.valuation K (E (D x)) ≤ 1)
    (hEF : ∀ a ∈ F, E a = 0) (hEx : E x = 1)
    (hp : CoeffsIn F p) (hdeg : 1 ≤ p.natDegree)
    {u : K} (hu : u ∈ RatIn F x)
    (hshape : PlaceDegLE v ((v.valuation K x)⁻¹ * (v.valuation K x)⁻¹)
      (u - (Polynomial.derivative p).eval x / p.eval x))
    (r : ℕ) :
    PlaceLim v (v.valuation K x)⁻¹
      (x * ((placeShift D (E (D x)))^[r] (placeShift D (E (D x)) u))) 0 := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
  exact placeLim_below_of_borderShape v D hF hx hDF hDx hDxv hc hcv hp hp0 hu le_rfl
    hshape (placeDegLE_placeShift_logFactor_of_unit_response v D E hF hx hDF hDx hDxv
      hEF hEx hp hdeg) r

/-- **A nonzero place value reflects nonvanishing.** -/
theorem ne_zero_of_placeLim_of_mem
    (v : HeightOneSpectrum R) {F : Subfield K} (hF : PlaceTrivialOn v F)
    {γ : ℤᵐ⁰} (hγ : γ < 1) {f a : K} (ha : a ∈ F) (ha0 : a ≠ 0)
    (hlim : PlaceLim v γ f a) : f ≠ 0 := by
  intro hf
  have hzero : PlaceLim v γ f 0 := by
    rw [hf]
    exact placeLim_self v γ 0
  have hazero : a = 0 := placeLim_unique v hF hγ ha F.zero_mem hlim hzero
  exact ha0 hazero

/-- **A nonzero determinant of place values reflects nonvanishing of the original determinant.** -/
theorem matrix_det_ne_zero_of_placeLim
    (v : HeightOneSpectrum R) {F : Subfield K} (hF : PlaceTrivialOn v F)
    {γ : ℤᵐ⁰} (hγ : γ < 1) {n : ℕ} (M L : Matrix (Fin n) (Fin n) K)
    (hL : ∀ i j, L i j ∈ F) (hlim : ∀ i j, PlaceLim v γ (M i j) (L i j))
    (hdet : L.det ≠ 0) : M.det ≠ 0 := by
  have hdetmem : L.det ∈ F := by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ =>
      mul_mem (intCast_mem F _) (prod_mem fun i _ => hL (σ i) i)
  exact ne_zero_of_placeLim_of_mem v hF hγ hdetmem hdet
    (placeLim_det_of_mem v hF (le_of_lt hγ) M L hL hlim)

end GaloisForLFunctions.HTGeometry
