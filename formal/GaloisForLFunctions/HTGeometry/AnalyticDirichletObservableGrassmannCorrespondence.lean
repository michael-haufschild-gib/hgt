import GaloisForLFunctions.HTGeometry.AnalyticDirichletObservableFieldCorrespondence
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Analytic Grassmann correspondence for hypertranscendental Dirichlet fields

Fix a tail-dense prime sampler and an arbitrary independent bounded continuous source frame.
Every algebraic source subspace of the frame's finitely supported coordinate space determines a
basis-independent embedded differential field over the actual meromorphic coordinate field
`ℂ(s)`.  This assignment reflects order and equality and preserves both intersections and
composita.  More strongly, it is left adjoint to the canonical all-jet source subspace decoded
from an arbitrary ambient intermediate field.  Tail completeness and source independence split
this Galois connection: decoding a represented field recovers the source subspace exactly.  Hence
arbitrary source joins become field composita, and every ambient field has a canonical maximal
source-representable core.  This is a Grassmann representation, not merely the Boolean lattice of
subsets of a chosen frame.

The relative theorem is sharper.  For an arbitrary family of new source coordinates, the
corresponding analytic germs are jointly differentially independent over the field of an old
subspace `W` if and only if their classes are linearly independent in the quotient by `W`.
Consequently every finite or infinite interaction packet has an exact source-side relative-rank
criterion: hypertranscendental creation is precisely quotient-linear creation.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section

universe u v

attribute [local instance]
  analyticObservableUpperEndAnalyticDomain
  analyticObservableUpperEndMeroComplexAlgebra
  analyticObservableUpperEndMeroDifferential

/-- The continuous source observable synthesized by a finitely supported coordinate vector. -/
def analyticObservableCoordinateSource
    {V : Type u} {J : Type v} (f : J → V → ℂ) (c : J →₀ ℂ) : V → ℂ :=
  Finsupp.linearCombination ℂ f c

def analyticObservableCoordinateBound
    {J : Type v} (M : J → ℝ) (c : J →₀ ℂ) : ℝ :=
  c.sum fun j z ↦ ‖z‖ * M j

theorem continuous_analyticObservableCoordinateSource
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j)) (c : J →₀ ℂ) :
    Continuous (analyticObservableCoordinateSource f c) := by
  classical
  unfold analyticObservableCoordinateSource
  rw [Finsupp.linearCombination_apply]
  simp only [Finsupp.sum]
  have h := continuous_finsetSum c.support fun j _ ↦ (hf j).const_smul (c j)
  have heq : (∑ j ∈ c.support, c j • f j) =
      (fun z ↦ ∑ j ∈ c.support, c j • f j z) := by
    funext z
    simp
  rw [heq]
  exact h

theorem analyticObservableCoordinateSource_bound
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (c : J →₀ ℂ) (p : Nat.Primes) :
    ‖analyticObservableCoordinateSource f c (x p)‖ ≤
      analyticObservableCoordinateBound M c := by
  classical
  rw [analyticObservableCoordinateSource, Finsupp.linearCombination_apply,
    analyticObservableCoordinateBound]
  simp only [Finsupp.sum]
  rw [Finset.sum_apply]
  calc
    ‖∑ j ∈ c.support, c j • f j (x p)‖ ≤
        ∑ j ∈ c.support, ‖c j • f j (x p)‖ := norm_sum_le _ _
    _ = ∑ j ∈ c.support, ‖c j‖ * ‖f j (x p)‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp
    _ ≤ ∑ j ∈ c.support, ‖c j‖ * M j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hM j p) (norm_nonneg (c j))

abbrev analyticObservableGrassmannIndex
    {J : Type v} (W : Submodule ℂ (J →₀ ℂ)) :=
  Module.Basis.ofVectorSpaceIndex ℂ W

def analyticObservableGrassmannCoordinate
    {J : Type v} (W : Submodule ℂ (J →₀ ℂ))
    (i : analyticObservableGrassmannIndex W) : J →₀ ℂ :=
  (Module.Basis.ofVectorSpace ℂ W i).1

def analyticObservableGrassmannSource
    {V : Type u} {J : Type v} (f : J → V → ℂ)
    (W : Submodule ℂ (J →₀ ℂ))
    (i : analyticObservableGrassmannIndex W) : V → ℂ :=
  analyticObservableCoordinateSource f (analyticObservableGrassmannCoordinate W i)

def analyticObservableGrassmannBound
    {J : Type v} (M : J → ℝ)
    (W : Submodule ℂ (J →₀ ℂ))
    (i : analyticObservableGrassmannIndex W) : ℝ :=
  analyticObservableCoordinateBound M (analyticObservableGrassmannCoordinate W i)

theorem analyticObservableGrassmannSource_linearIndependent
    {V : Type u} {J : Type v} {K : Set V}
    (f : J → V → ℂ)
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (W : Submodule ℂ (J →₀ ℂ)) :
    LinearIndependent ℂ
      (fun i : analyticObservableGrassmannIndex W ↦
        fun z : K ↦ analyticObservableGrassmannSource f W i z.1) := by
  let vf : J → K → ℂ := fun j z ↦ f j z.1
  let b := Module.Basis.ofVectorSpace ℂ W
  have hbcoord : LinearIndependent ℂ (fun i ↦ (b i : J →₀ ℂ)) :=
    b.linearIndependent.map' W.subtype W.ker_subtype
  have hmap : (fun i ↦ fun z : K ↦ analyticObservableGrassmannSource f W i z.1) =
      (Finsupp.linearCombination ℂ vf) ∘ (fun i ↦ (b i : J →₀ ℂ)) := by
    funext i z
    simp [analyticObservableGrassmannSource, analyticObservableCoordinateSource,
      analyticObservableGrassmannCoordinate, vf, b,
      Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hmap]
  exact hbcoord.map'
    (Finsupp.linearCombination ℂ vf)
    (LinearMap.ker_eq_bot.mpr hlinear.finsuppLinearCombination_injective)

theorem analyticObservableGrassmannSource_span
    {V : Type u} {J : Type v} {K : Set V}
    (f : J → V → ℂ)
    (W : Submodule ℂ (J →₀ ℂ)) :
    Submodule.span ℂ
        (Set.range (fun i : analyticObservableGrassmannIndex W ↦
          fun z : K ↦ analyticObservableGrassmannSource f W i z.1)) =
      W.map (Finsupp.linearCombination ℂ (fun j ↦ fun z : K ↦ f j z.1)) := by
  let L : (J →₀ ℂ) →ₗ[ℂ] (K → ℂ) :=
    Finsupp.linearCombination ℂ (fun j ↦ fun z : K ↦ f j z.1)
  let b := Module.Basis.ofVectorSpace ℂ W
  have hfamily :
      (fun i : analyticObservableGrassmannIndex W ↦
        fun z : K ↦ analyticObservableGrassmannSource f W i z.1) =
      L ∘ (fun i ↦ (b i : J →₀ ℂ)) := by
    funext i z
    simp [analyticObservableGrassmannSource, analyticObservableCoordinateSource,
      analyticObservableGrassmannCoordinate, L, b,
      Finsupp.linearCombination_apply, Finsupp.sum]
  have hspan : Submodule.span ℂ (Set.range fun i ↦ (b i : J →₀ ℂ)) = W := by
    rw [show Set.range (fun i ↦ (b i : J →₀ ℂ)) =
        W.subtype '' Set.range b by aesop,
      ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  rw [hfamily, Set.range_comp, ← Submodule.map_span, hspan]

/-- The basis-independent analytic differential field of an arbitrary source subspace. -/
def analyticObservableGrassmannField
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : Submodule ℂ (J →₀ ℂ)) :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  analyticObservableShiftField x
    (analyticObservableGrassmannSource f W)
    (analyticObservableGrassmannBound M W)
    (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM
      (analyticObservableGrassmannCoordinate W i) p)
    a

theorem cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (U W : Submodule ℂ (J →₀ ℂ)) :
    analyticObservableGrassmannField x f M hM a U ≤
        analyticObservableGrassmannField x f M hM a W ↔ U ≤ W := by
  let L : (J →₀ ℂ) →ₗ[ℂ] (K → ℂ) :=
    Finsupp.linearCombination ℂ (fun j ↦ fun z : K ↦ f j z.1)
  have hWlinear := analyticObservableGrassmannSource_linearIndependent f hlinear W
  have horder :=
    cofiniteTailDenseOn_analyticObservableShiftField_le_iff_span_le_arbitrary
      x K hx (analyticObservableGrassmannSource f U)
        (analyticObservableGrassmannSource f W)
      (fun i ↦ continuous_analyticObservableCoordinateSource f hf
        (analyticObservableGrassmannCoordinate U i))
      (fun i ↦ continuous_analyticObservableCoordinateSource f hf
        (analyticObservableGrassmannCoordinate W i))
      hWlinear
      (analyticObservableGrassmannBound M U)
      (analyticObservableGrassmannBound M W)
      (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM
        (analyticObservableGrassmannCoordinate U i) p)
      (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM
        (analyticObservableGrassmannCoordinate W i) p) a
  unfold analyticObservableGrassmannField
  rw [horder, analyticObservableGrassmannSource_span f U,
    analyticObservableGrassmannSource_span f W]
  exact LinearMap.map_le_map_iff'
    (LinearMap.ker_eq_bot.mpr hlinear.finsuppLinearCombination_injective)

/-- **Full analytic Grassmann order embedding.** Every source subspace, of arbitrary dimension,
is represented by an actual embedded meromorphic differential field, and field inclusion reflects
exactly source-subspace inclusion. -/
noncomputable def analyticObservableGrassmannFieldOrderEmbedding
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j) (a : ℂ) :
    Submodule ℂ (J →₀ ℂ) ↪o
      IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  OrderEmbedding.ofMapLEIff
    (analyticObservableGrassmannField x f M hM a)
    (fun U W ↦ cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
      x K hx f hf hlinear M hM a U W)

theorem cofiniteTailDenseOn_analyticObservableGrassmannField_eq_iff
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (U W : Submodule ℂ (J →₀ ℂ)) :
    analyticObservableGrassmannField x f M hM a U =
        analyticObservableGrassmannField x f M hM a W ↔ U = W := by
  constructor
  · intro h
    apply le_antisymm
    · exact (cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
        x K hx f hf hlinear M hM a U W).mp h.le
    · exact (cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
        x K hx f hf hlinear M hM a W U).mp h.ge
  · intro h
    rw [h]

theorem analyticObservableGrassmann_sum_source_linearIndependent_of_quotient
    {V : Type u} {J : Type v} {I : Type*} {K : Set V}
    (f : J → V → ℂ)
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (W : Submodule ℂ (J →₀ ℂ)) (g : I → J →₀ ℂ)
    (hg : LinearIndependent ℂ (W.mkQ ∘ g)) :
    LinearIndependent ℂ
      (Sum.elim
        (fun i : analyticObservableGrassmannIndex W ↦
          fun z : K ↦ analyticObservableGrassmannSource f W i z.1)
        (fun i : I ↦
          fun z : K ↦ analyticObservableCoordinateSource f (g i) z.1)) := by
  let b := Module.Basis.ofVectorSpace ℂ W
  have hcoord : LinearIndependent ℂ
      (Sum.elim (fun i ↦ (b i : J →₀ ℂ)) g) :=
    LinearIndependent.sumElim_of_quotient b.linearIndependent g hg
  let vf : J → K → ℂ := fun j z ↦ f j z.1
  let L : (J →₀ ℂ) →ₗ[ℂ] (K → ℂ) := Finsupp.linearCombination ℂ vf
  have hmapped := hcoord.map' L
    (LinearMap.ker_eq_bot.mpr hlinear.finsuppLinearCombination_injective)
  have heq :
      (Sum.elim
        (fun i : analyticObservableGrassmannIndex W ↦
          fun z : K ↦ analyticObservableGrassmannSource f W i z.1)
        (fun i : I ↦
          fun z : K ↦ analyticObservableCoordinateSource f (g i) z.1)) =
      L ∘ (Sum.elim (fun i ↦ (b i : J →₀ ℂ)) g) := by
    funext q z
    rcases q with i | i
    · simp [analyticObservableGrassmannSource, analyticObservableCoordinateSource,
        analyticObservableGrassmannCoordinate, L, vf, b,
        Finsupp.linearCombination_apply, Finsupp.sum]
    · simp [analyticObservableCoordinateSource, L, vf,
        Finsupp.linearCombination_apply, Finsupp.sum]
  rw [heq]
  exact hmapped

theorem cofiniteTailDenseOn_analyticObservableCoordinateCarrier_relativeDI_of_quotient
    {V : Type u} {J : Type v} {I : Type*} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : Submodule ℂ (J →₀ ℂ)) (g : I → J →₀ ℂ)
    (hg : LinearIndependent ℂ (W.mkQ ∘ g)) :
    GaloisForLFunctions.DifferentialIndependent
      (analyticObservableGrassmannField x f M hM a W)
      (fun i ↦ analyticPrimeObservableShiftCarrier
        (fun p ↦ analyticObservableCoordinateSource f (g i) (x p))
        (analyticObservableCoordinateBound M (g i))
        (analyticObservableCoordinateSource_bound x f M hM (g i)) a) := by
  let A := analyticObservableGrassmannIndex W
  let oldSource : A → V → ℂ := analyticObservableGrassmannSource f W
  let newSource : I → V → ℂ := fun i ↦ analyticObservableCoordinateSource f (g i)
  let oldBound : A → ℝ := analyticObservableGrassmannBound M W
  let newBound : I → ℝ := fun i ↦ analyticObservableCoordinateBound M (g i)
  let source : A ⊕ I → V → ℂ := Sum.elim oldSource newSource
  let bounds : A ⊕ I → ℝ := Sum.elim oldBound newBound
  have hsourceContinuous : ∀ q, Continuous (source q) := by
    intro q
    rcases q with i | i
    · exact continuous_analyticObservableCoordinateSource f hf
        (analyticObservableGrassmannCoordinate W i)
    · exact continuous_analyticObservableCoordinateSource f hf (g i)
  have hsourceLinear : LinearIndependent ℂ
      (fun q ↦ fun z : K ↦ source q z.1) := by
    have h := analyticObservableGrassmann_sum_source_linearIndependent_of_quotient
      f hlinear W g hg
    convert h using 1
    funext q z
    rcases q with i | i <;> rfl
  have hsourceBound : ∀ q p, ‖source q (x p)‖ ≤ bounds q := by
    intro q p
    rcases q with i | i
    · exact analyticObservableCoordinateSource_bound x f M hM
        (analyticObservableGrassmannCoordinate W i) p
    · exact analyticObservableCoordinateSource_bound x f M hM (g i) p
  have hjoint :=
    cofiniteTailDenseOn_analyticObservableShiftCarrier_differentialIndependent_arbitrary
      x K hx source hsourceContinuous hsourceLinear bounds hsourceBound a
  let oldCarrier : A → upperEndMeroField := fun i ↦
    analyticPrimeObservableShiftCarrier
      (fun p ↦ oldSource i (x p)) (oldBound i)
      (fun p ↦ hsourceBound (Sum.inl i) p) a
  let newCarrier : I → upperEndMeroField := fun i ↦
    analyticPrimeObservableShiftCarrier
      (fun p ↦ newSource i (x p)) (newBound i)
      (fun p ↦ hsourceBound (Sum.inr i) p) a
  have hjoint' : GaloisForLFunctions.DifferentialIndependent
      upperEndRationalCoordinateField (Sum.elim oldCarrier newCarrier) := by
    have hfamily :
        (fun q ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ source q (x p)) (bounds q) (hsourceBound q) a) =
        Sum.elim oldCarrier newCarrier := by
      funext q
      rcases q with i | i <;> rfl
    rwa [hfamily] at hjoint
  have hrelative :=
    GaloisForLFunctions.differentialIndependent_sum_right_over_left_differentialAdjoin
      oldCarrier newCarrier hjoint'
  simpa only [analyticObservableGrassmannField, analyticObservableShiftField,
    oldCarrier, newCarrier, oldSource, newSource, oldBound, newBound] using hrelative

theorem finsupp_linearMvPolynomial_sub_C_ne_zero
    {F I : Type*} [Field F] [Algebra ℂ F]
    (c : I →₀ ℂ) (hc : c ≠ 0) (b : F) :
    c.sum (fun i z ↦ MvPolynomial.C (algebraMap ℂ F z) * MvPolynomial.X i) -
        MvPolynomial.C b ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hc
  intro hzero
  have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) hzero
  have hisupport : i ∈ c.support := Finsupp.mem_support_iff.mpr hi
  have hsingle : (Finsupp.single i 1 : I →₀ ℕ) ≠ 0 :=
    Finsupp.single_ne_zero.mpr one_ne_zero
  have hzeroSingle : (0 : I →₀ ℕ) ≠ Finsupp.single i 1 := hsingle.symm
  rw [Finsupp.sum, MvPolynomial.coeff_sub, MvPolynomial.coeff_sum] at hcoeff
  simp_rw [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.coeff_monomial] at hcoeff
  simp [Finsupp.single_eq_single_iff, hisupport, hzeroSingle] at hcoeff
  exact hi ((FaithfulSMul.algebraMap_injective ℂ F) (by simpa using hcoeff))

theorem cofiniteTailDenseOn_analyticObservableCoordinateCarrier_mem_grassmannField_iff
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : Submodule ℂ (J →₀ ℂ)) (c : J →₀ ℂ) :
    analyticPrimeObservableShiftCarrier
        (fun p ↦ analyticObservableCoordinateSource f c (x p))
        (analyticObservableCoordinateBound M c)
        (analyticObservableCoordinateSource_bound x f M hM c) a ∈
      analyticObservableGrassmannField x f M hM a W ↔ c ∈ W := by
  let L : (J →₀ ℂ) →ₗ[ℂ] (K → ℂ) :=
    Finsupp.linearCombination ℂ (fun j ↦ fun z : K ↦ f j z.1)
  have hbasisLinear := analyticObservableGrassmannSource_linearIndependent f hlinear W
  have hmem :=
    cofiniteTailDenseOn_analyticObservableShiftCarrier_mem_field_iff_mem_span_arbitrary
      x K hx (analyticObservableGrassmannSource f W)
      (fun i ↦ continuous_analyticObservableCoordinateSource f hf
        (analyticObservableGrassmannCoordinate W i))
      hbasisLinear (analyticObservableGrassmannBound M W)
      (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM
        (analyticObservableGrassmannCoordinate W i) p)
      (analyticObservableCoordinateSource f c)
      (continuous_analyticObservableCoordinateSource f hf c)
      (analyticObservableCoordinateBound M c)
      (analyticObservableCoordinateSource_bound x f M hM c) a
  unfold analyticObservableGrassmannField
  rw [hmem, analyticObservableGrassmannSource_span f W]
  have hcsource : (fun z : K ↦ analyticObservableCoordinateSource f c z.1) = L c := by
    funext z
    simp [analyticObservableCoordinateSource, L,
      Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hcsource]
  change L c ∈ W.map L ↔ c ∈ W
  constructor
  · rintro ⟨w, hw, hcw⟩
    have : c = w := hlinear.finsuppLinearCombination_injective hcw.symm
    rwa [this]
  · intro hc
    exact ⟨c, hc, rfl⟩

/-- **Exact relative quotient-rank law.** An arbitrary family of analytic source carriers is
jointly differentially independent over the field of `W` exactly when its source-coordinate
classes are linearly independent modulo `W`.  This simultaneously gives necessity, sufficiency,
and the exact number of genuinely new hypertranscendental directions. -/
theorem cofiniteTailDenseOn_analyticObservableCoordinateCarrier_relativeDI_iff_quotient
    {V : Type u} {J : Type v} {I : Type*} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : Submodule ℂ (J →₀ ℂ)) (g : I → J →₀ ℂ) :
    GaloisForLFunctions.DifferentialIndependent
        (analyticObservableGrassmannField x f M hM a W)
        (fun i ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f (g i) (x p))
          (analyticObservableCoordinateBound M (g i))
          (analyticObservableCoordinateSource_bound x f M hM (g i)) a) ↔
      LinearIndependent ℂ (W.mkQ ∘ g) := by
  let F₀ := analyticObservableGrassmannField x f M hM a W
  let carrier : I → upperEndMeroField := fun i ↦
    analyticPrimeObservableShiftCarrier
      (fun p ↦ analyticObservableCoordinateSource f (g i) (x p))
      (analyticObservableCoordinateBound M (g i))
      (analyticObservableCoordinateSource_bound x f M hM (g i)) a
  constructor
  · intro hrel
    have hAIall := hrel
    unfold GaloisForLFunctions.DifferentialIndependent at hAIall
    have hAI : AlgebraicIndependent F₀ carrier := by
      have hcomp := hAIall.comp (fun i : I ↦ (i, 0)) (by
        intro i j hij
        exact congrArg Prod.fst hij)
      simpa only [carrier, F₀, GaloisForLFunctions.differentialJet_zero] using hcomp
    rw [linearIndependent_iff_injective_finsuppLinearCombination]
    intro c d hcd
    let e : I →₀ ℂ := c - d
    have heqQ : Finsupp.linearCombination ℂ (W.mkQ ∘ g) e = 0 := by
      calc
        Finsupp.linearCombination ℂ (W.mkQ ∘ g) e =
            Finsupp.linearCombination ℂ (W.mkQ ∘ g) c -
              Finsupp.linearCombination ℂ (W.mkQ ∘ g) d := by
                exact map_sub _ _ _
        _ = 0 := sub_eq_zero.mpr hcd
    let q : J →₀ ℂ := Finsupp.linearCombination ℂ g e
    have hqW : q ∈ W := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change W.mkQ q = 0
      rw [show W.mkQ q = Finsupp.linearCombination ℂ (W.mkQ ∘ g) e by
        exact Finsupp.apply_linearCombination ℂ W.mkQ g e]
      exact heqQ
    by_contra hecd
    have he : e ≠ 0 := by
      intro he0
      apply hecd
      exact sub_eq_zero.mp he0
    have hcoeff : ∀ p : Nat.Primes,
        analyticObservableCoordinateSource f q (x p) =
          e.sum fun i z ↦ z * analyticObservableCoordinateSource f (g i) (x p) := by
      intro p
      simp [q, e, analyticObservableCoordinateSource,
        Finsupp.linearCombination_apply, Finsupp.sum]
    have hcarrier := analyticPrimeObservableShiftCarrier_finsuppLinearCombination
      (fun i p ↦ analyticObservableCoordinateSource f (g i) (x p))
      (fun i ↦ analyticObservableCoordinateBound M (g i))
      (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM (g i) p)
      e
      (fun p ↦ analyticObservableCoordinateSource f q (x p))
      (analyticObservableCoordinateBound M q)
      (analyticObservableCoordinateSource_bound x f M hM q)
      hcoeff a
    have hqmem : analyticPrimeObservableShiftCarrier
        (fun p ↦ analyticObservableCoordinateSource f q (x p))
        (analyticObservableCoordinateBound M q)
        (analyticObservableCoordinateSource_bound x f M hM q) a ∈ F₀ := by
      change _ ∈ analyticObservableGrassmannField x f M hM a W
      exact (cofiniteTailDenseOn_analyticObservableCoordinateCarrier_mem_grassmannField_iff
        x K hx f hf hlinear M hM a W q).mpr hqW
    let b : F₀ := ⟨analyticPrimeObservableShiftCarrier
      (fun p ↦ analyticObservableCoordinateSource f q (x p))
      (analyticObservableCoordinateBound M q)
      (analyticObservableCoordinateSource_bound x f M hM q) a, hqmem⟩
    let P : MvPolynomial I F₀ :=
      e.sum (fun i z ↦ MvPolynomial.C (algebraMap ℂ F₀ z) * MvPolynomial.X i) -
        MvPolynomial.C b
    have hPne : P ≠ 0 := by
      exact finsupp_linearMvPolynomial_sub_C_ne_zero e he b
    have hPzero : MvPolynomial.aeval carrier P = 0 := by
      simp only [P, Finsupp.sum, map_sub, map_sum, map_mul,
        MvPolynomial.aeval_C, MvPolynomial.aeval_X]
      have hscalar : ∀ z : ℂ,
          algebraMap F₀ upperEndMeroField (algebraMap ℂ F₀ z) =
            algebraMap ℂ upperEndMeroField z := by
        intro z
        rw [IsScalarTower.algebraMap_apply ℂ upperEndRationalCoordinateField F₀]
        rw [← IsScalarTower.algebraMap_apply upperEndRationalCoordinateField F₀
          upperEndMeroField]
        rw [← IsScalarTower.algebraMap_apply ℂ upperEndRationalCoordinateField
          upperEndMeroField]
      simp_rw [hscalar]
      change e.sum (fun i z ↦ algebraMap ℂ upperEndMeroField z * carrier i) - b.1 = 0
      rw [← hcarrier]
      simp [b]
    exact hPne (hAI.eq_zero_of_aeval_eq_zero P hPzero)
  · exact cofiniteTailDenseOn_analyticObservableCoordinateCarrier_relativeDI_of_quotient
      x K hx f hf hlinear M hM a W g

def analyticObservableCoordinateField
    {V : Type u} {J : Type v} {I : Type*}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (g : I → J →₀ ℂ) :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  analyticObservableShiftField x
    (fun i ↦ analyticObservableCoordinateSource f (g i))
    (fun i ↦ analyticObservableCoordinateBound M (g i))
    (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM (g i) p) a

theorem cofiniteTailDenseOn_analyticObservableCoordinateField_eq_grassmannField
    {V : Type u} {J : Type v} {I : Type*} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (g : I → J →₀ ℂ) (hg : LinearIndependent ℂ g)
    (W : Submodule ℂ (J →₀ ℂ))
    (hspan : Submodule.span ℂ (Set.range g) = W) :
    analyticObservableCoordinateField x f M hM a g =
      analyticObservableGrassmannField x f M hM a W := by
  let L : (J →₀ ℂ) →ₗ[ℂ] (K → ℂ) :=
    Finsupp.linearCombination ℂ (fun j ↦ fun z : K ↦ f j z.1)
  have hsourceLinear : LinearIndependent ℂ
      (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (g i) z.1) := by
    have hmapped := hg.map' L
      (LinearMap.ker_eq_bot.mpr hlinear.finsuppLinearCombination_injective)
    have heq :
        (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (g i) z.1) =
          L ∘ g := by
      funext i z
      simp [analyticObservableCoordinateSource, L,
        Finsupp.linearCombination_apply, Finsupp.sum]
    rwa [heq]
  have hbasisLinear := analyticObservableGrassmannSource_linearIndependent f hlinear W
  have heq := cofiniteTailDenseOn_analyticObservableShiftField_eq_iff_span_eq_arbitrary
    x K hx
    (fun i ↦ analyticObservableCoordinateSource f (g i))
    (analyticObservableGrassmannSource f W)
    (fun i ↦ continuous_analyticObservableCoordinateSource f hf (g i))
    (fun i ↦ continuous_analyticObservableCoordinateSource f hf
      (analyticObservableGrassmannCoordinate W i))
    hsourceLinear hbasisLinear
    (fun i ↦ analyticObservableCoordinateBound M (g i))
    (analyticObservableGrassmannBound M W)
    (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM (g i) p)
    (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM
      (analyticObservableGrassmannCoordinate W i) p) a
  unfold analyticObservableCoordinateField analyticObservableGrassmannField
  apply heq.mpr
  rw [analyticObservableGrassmannSource_span f W]
  have hfamily :
      (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (g i) z.1) =
        L ∘ g := by
    funext i z
    simp [analyticObservableCoordinateSource, L,
      Finsupp.linearCombination_apply, Finsupp.sum]
  rw [hfamily, Set.range_comp, ← Submodule.map_span, hspan]

theorem span_range_ofVectorSpace_subtype
    {E : Type*} [AddCommGroup E] [Module ℂ E] (W : Submodule ℂ E) :
    Submodule.span ℂ
        (Set.range (fun i : Module.Basis.ofVectorSpaceIndex ℂ W ↦
          ((Module.Basis.ofVectorSpace ℂ W i : W) : E))) = W := by
  let b := Module.Basis.ofVectorSpace ℂ W
  rw [show Set.range (fun i ↦ ((b i : W) : E)) =
      W.subtype '' Set.range b by aesop,
    ← Submodule.map_span, b.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem exists_submodule_complement_of_le_general
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (U V : Submodule ℂ E) (hUV : U ≤ V) :
    ∃ Q : Submodule ℂ E, Q ≤ V ∧ Disjoint U Q ∧ U ⊔ Q = V := by
  let U' : Submodule ℂ V := U.comap V.subtype
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl U'
  let Q : Submodule ℂ E := Q'.map V.subtype
  have hQV : Q ≤ V := by
    rintro x ⟨q, hq, rfl⟩
    exact q.2
  have hUQ : Disjoint U Q := by
    rw [Submodule.disjoint_def]
    intro x hxU hxQ
    obtain ⟨q, hq, hqx⟩ := hxQ
    subst x
    have hqU' : q ∈ U' := hxU
    have hqzero : q = 0 :=
      (Submodule.disjoint_def.mp hQ'.disjoint) q hqU' hq
    exact congrArg Subtype.val hqzero
  refine ⟨Q, hQV, hUQ, ?_⟩
  apply le_antisymm
  · exact sup_le hUV hQV
  · intro x hxV
    let xv : V := ⟨x, hxV⟩
    have hxsum : xv ∈ U' ⊔ Q' := by
      rw [hQ'.codisjoint.eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, q, hq, huq⟩ := Submodule.mem_sup.mp hxsum
    apply Submodule.mem_sup.mpr
    refine ⟨u.1, ?_, q.1, ?_, ?_⟩
    · exact hu
    · exact ⟨q, hq, rfl⟩
    · exact congrArg Subtype.val huq

/-- **Basis-free analytic Grassmann meet law.** Field intersection is exactly source-subspace
intersection, without any finiteness or coordinate-subset hypothesis. -/
theorem cofiniteTailDenseOn_analyticObservableGrassmannField_inf
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (U W : Submodule ℂ (J →₀ ℂ)) :
    analyticObservableGrassmannField x f M hM a U ⊓
        analyticObservableGrassmannField x f M hM a W =
      analyticObservableGrassmannField x f M hM a (U ⊓ W) := by
  let A := U ⊓ W
  obtain ⟨B, hBU, hAB, hABsup⟩ :=
    exists_submodule_complement_of_le_general A U inf_le_left
  obtain ⟨C, hCW, hAC, hACsup⟩ :=
    exists_submodule_complement_of_le_general A W inf_le_right
  have hUC : Disjoint U C := by
    rw [Submodule.disjoint_def]
    intro z hzU hzC
    have hzW : z ∈ W := hCW hzC
    have hzA : z ∈ A := ⟨hzU, hzW⟩
    exact (Submodule.disjoint_def.mp hAC) z hzA hzC
  have hABC : Disjoint (A ⊔ B) C := by
    rw [hABsup]
    exact hUC
  have hBC : Disjoint B C := hABC.mono_left le_sup_right
  have hA_BC : Disjoint A (B ⊔ C) :=
    hAB.disjoint_sup_right_of_disjoint_sup_left hABC
  let bA := Module.Basis.ofVectorSpace ℂ A
  let bB := Module.Basis.ofVectorSpace ℂ B
  let bC := Module.Basis.ofVectorSpace ℂ C
  let cA : Module.Basis.ofVectorSpaceIndex ℂ A → J →₀ ℂ :=
    fun i ↦ (bA i).1
  let cB : Module.Basis.ofVectorSpaceIndex ℂ B → J →₀ ℂ :=
    fun i ↦ (bB i).1
  let cC : Module.Basis.ofVectorSpaceIndex ℂ C → J →₀ ℂ :=
    fun i ↦ (bC i).1
  have hspanA : Submodule.span ℂ (Set.range cA) = A := by
    simpa only [cA, bA] using span_range_ofVectorSpace_subtype A
  have hspanB : Submodule.span ℂ (Set.range cB) = B := by
    simpa only [cB, bB] using span_range_ofVectorSpace_subtype B
  have hspanC : Submodule.span ℂ (Set.range cC) = C := by
    simpa only [cC, bC] using span_range_ofVectorSpace_subtype C
  have hcA : LinearIndependent ℂ cA := by
    exact bA.linearIndependent.map' A.subtype A.ker_subtype
  have hcB : LinearIndependent ℂ cB := by
    exact bB.linearIndependent.map' B.subtype B.ker_subtype
  have hcC : LinearIndependent ℂ cC := by
    exact bC.linearIndependent.map' C.subtype C.ker_subtype
  have hcBC : LinearIndependent ℂ (Sum.elim cB cC) :=
    hcB.sum_type hcC (by rw [hspanB, hspanC]; exact hBC)
  have hspanBC : Submodule.span ℂ (Set.range (Sum.elim cB cC)) = B ⊔ C := by
    rw [Set.Sum.elim_range, Submodule.span_union, hspanB, hspanC]
  have hcABC : LinearIndependent ℂ (Sum.elim cA (Sum.elim cB cC)) :=
    hcA.sum_type hcBC (by rw [hspanA, hspanBC]; exact hA_BC)
  let L : (J →₀ ℂ) →ₗ[ℂ] (K → ℂ) :=
    Finsupp.linearCombination ℂ (fun j ↦ fun z : K ↦ f j z.1)
  have hsourceLinear : LinearIndependent ℂ
      (Sum.elim
        (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (cA i) z.1)
        (Sum.elim
          (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (cB i) z.1)
          (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (cC i) z.1))) := by
    have hmapped := hcABC.map' L
      (LinearMap.ker_eq_bot.mpr hlinear.finsuppLinearCombination_injective)
    have heq :
        (Sum.elim
          (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (cA i) z.1)
          (Sum.elim
            (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (cB i) z.1)
            (fun i ↦ fun z : K ↦ analyticObservableCoordinateSource f (cC i) z.1))) =
          L ∘ Sum.elim cA (Sum.elim cB cC) := by
      funext q z
      rcases q with i | q
      · simp [analyticObservableCoordinateSource, L,
          Finsupp.linearCombination_apply, Finsupp.sum]
      · rcases q with i | i <;>
          simp [analyticObservableCoordinateSource, L,
            Finsupp.linearCombination_apply, Finsupp.sum]
    rwa [heq]
  have hmeet := cofiniteTailDenseOn_analyticObservable_threeBlock_field_inf
    x K hx
    (fun i ↦ analyticObservableCoordinateSource f (cA i))
    (fun i ↦ analyticObservableCoordinateSource f (cB i))
    (fun i ↦ analyticObservableCoordinateSource f (cC i))
    (fun i ↦ continuous_analyticObservableCoordinateSource f hf (cA i))
    (fun i ↦ continuous_analyticObservableCoordinateSource f hf (cB i))
    (fun i ↦ continuous_analyticObservableCoordinateSource f hf (cC i))
    hsourceLinear
    (fun i ↦ analyticObservableCoordinateBound M (cA i))
    (fun i ↦ analyticObservableCoordinateBound M (cB i))
    (fun i ↦ analyticObservableCoordinateBound M (cC i))
    (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM (cA i) p)
    (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM (cB i) p)
    (fun i p ↦ analyticObservableCoordinateSource_bound x f M hM (cC i) p) a
  have hspanAB : Submodule.span ℂ (Set.range (Sum.elim cA cB)) = U := by
    rw [Set.Sum.elim_range, Submodule.span_union, hspanA, hspanB, hABsup]
  have hspanAC : Submodule.span ℂ (Set.range (Sum.elim cA cC)) = W := by
    rw [Set.Sum.elim_range, Submodule.span_union, hspanA, hspanC, hACsup]
  have hcAB : LinearIndependent ℂ (Sum.elim cA cB) :=
    hcA.sum_type hcB (by rw [hspanA, hspanB]; exact hAB)
  have hcAC : LinearIndependent ℂ (Sum.elim cA cC) :=
    hcA.sum_type hcC (by rw [hspanA, hspanC]; exact hAC)
  have hfieldU := cofiniteTailDenseOn_analyticObservableCoordinateField_eq_grassmannField
    x K hx f hf hlinear M hM a (Sum.elim cA cB) hcAB U hspanAB
  have hfieldW := cofiniteTailDenseOn_analyticObservableCoordinateField_eq_grassmannField
    x K hx f hf hlinear M hM a (Sum.elim cA cC) hcAC W hspanAC
  have hfieldA := cofiniteTailDenseOn_analyticObservableCoordinateField_eq_grassmannField
    x K hx f hf hlinear M hM a cA hcA A hspanA
  have hABcarrier :
      (fun q ↦ analyticPrimeObservableShiftCarrier
        (fun p ↦ analyticObservableCoordinateSource f (Sum.elim cA cB q) (x p))
        (analyticObservableCoordinateBound M (Sum.elim cA cB q))
        (analyticObservableCoordinateSource_bound x f M hM (Sum.elim cA cB q)) a) =
      Sum.elim
        (fun i ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f (cA i) (x p))
          (analyticObservableCoordinateBound M (cA i))
          (analyticObservableCoordinateSource_bound x f M hM (cA i)) a)
        (fun i ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f (cB i) (x p))
          (analyticObservableCoordinateBound M (cB i))
          (analyticObservableCoordinateSource_bound x f M hM (cB i)) a) := by
    funext q
    rcases q with i | i <;> rfl
  have hACcarrier :
      (fun q ↦ analyticPrimeObservableShiftCarrier
        (fun p ↦ analyticObservableCoordinateSource f (Sum.elim cA cC q) (x p))
        (analyticObservableCoordinateBound M (Sum.elim cA cC q))
        (analyticObservableCoordinateSource_bound x f M hM (Sum.elim cA cC q)) a) =
      Sum.elim
        (fun i ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f (cA i) (x p))
          (analyticObservableCoordinateBound M (cA i))
          (analyticObservableCoordinateSource_bound x f M hM (cA i)) a)
        (fun i ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f (cC i) (x p))
          (analyticObservableCoordinateBound M (cC i))
          (analyticObservableCoordinateSource_bound x f M hM (cC i)) a) := by
    funext q
    rcases q with i | i <;> rfl
  have hmeetCoord :
      analyticObservableCoordinateField x f M hM a (Sum.elim cA cB) ⊓
          analyticObservableCoordinateField x f M hM a (Sum.elim cA cC) =
        analyticObservableCoordinateField x f M hM a cA := by
    unfold analyticObservableCoordinateField analyticObservableShiftField
    rw [hABcarrier, hACcarrier]
    exact hmeet
  rw [hfieldU, hfieldW, hfieldA] at hmeetCoord
  exact hmeetCoord

theorem analyticObservableCoordinateField_sum
    {V : Type u} {J : Type v} {I L : Type*}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (g : I → J →₀ ℂ) (h : L → J →₀ ℂ) :
    analyticObservableCoordinateField x f M hM a (Sum.elim g h) =
      analyticObservableCoordinateField x f M hM a g ⊔
        analyticObservableCoordinateField x f M hM a h := by
  unfold analyticObservableCoordinateField analyticObservableShiftField
  unfold GaloisForLFunctions.differentialAdjoin
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨y, ⟨q, rfl⟩, n, rfl⟩
    rcases q with i | j
    · apply (le_sup_left :
        IntermediateField.adjoin upperEndRationalCoordinateField
          (GaloisForLFunctions.differentialJetSet
            (Set.range fun i ↦ analyticPrimeObservableShiftCarrier
              (fun p ↦ analyticObservableCoordinateSource f (g i) (x p))
              (analyticObservableCoordinateBound M (g i))
              (analyticObservableCoordinateSource_bound x f M hM (g i)) a)) ≤ _)
      exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        upperEndRationalCoordinateField (Set.mem_range_self i) n
    · apply (le_sup_right :
        IntermediateField.adjoin upperEndRationalCoordinateField
          (GaloisForLFunctions.differentialJetSet
            (Set.range fun j ↦ analyticPrimeObservableShiftCarrier
              (fun p ↦ analyticObservableCoordinateSource f (h j) (x p))
              (analyticObservableCoordinateBound M (h j))
              (analyticObservableCoordinateSource_bound x f M hM (h j)) a)) ≤ _)
      exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        upperEndRationalCoordinateField (Set.mem_range_self j) n
  · apply sup_le
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro z ⟨y, ⟨i, rfl⟩, n, rfl⟩
      exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        upperEndRationalCoordinateField
        (s := Set.range fun q : I ⊕ L ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f (Sum.elim g h q) (x p))
          (analyticObservableCoordinateBound M (Sum.elim g h q))
          (analyticObservableCoordinateSource_bound x f M hM (Sum.elim g h q)) a)
        (Set.mem_range_self (Sum.inl i)) n
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro z ⟨y, ⟨j, rfl⟩, n, rfl⟩
      exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        upperEndRationalCoordinateField
        (s := Set.range fun q : I ⊕ L ↦ analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f (Sum.elim g h q) (x p))
          (analyticObservableCoordinateBound M (Sum.elim g h q))
          (analyticObservableCoordinateSource_bound x f M hM (Sum.elim g h q)) a)
        (Set.mem_range_self (Sum.inr j)) n

/-- **Basis-free analytic Grassmann compositum law.** Field compositum is exactly source-subspace
sum, without any finiteness or coordinate-subset hypothesis. -/
theorem cofiniteTailDenseOn_analyticObservableGrassmannField_sup
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (U W : Submodule ℂ (J →₀ ℂ)) :
    analyticObservableGrassmannField x f M hM a U ⊔
        analyticObservableGrassmannField x f M hM a W =
      analyticObservableGrassmannField x f M hM a (U ⊔ W) := by
  let A := U ⊓ W
  obtain ⟨Q, hQW, hAQ, hAQsup⟩ :=
    exists_submodule_complement_of_le_general A W inf_le_right
  have hUQ : Disjoint U Q := by
    rw [Submodule.disjoint_def]
    intro z hzU hzQ
    have hzW : z ∈ W := hQW hzQ
    have hzA : z ∈ A := ⟨hzU, hzW⟩
    exact (Submodule.disjoint_def.mp hAQ) z hzA hzQ
  have hUQsup : U ⊔ Q = U ⊔ W := by
    apply le_antisymm
    · exact sup_le le_sup_left (hQW.trans le_sup_right)
    · apply sup_le le_sup_left
      rw [← hAQsup]
      exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  let bU := Module.Basis.ofVectorSpace ℂ U
  let bQ := Module.Basis.ofVectorSpace ℂ Q
  let cU : Module.Basis.ofVectorSpaceIndex ℂ U → J →₀ ℂ :=
    fun i ↦ (bU i).1
  let cQ : Module.Basis.ofVectorSpaceIndex ℂ Q → J →₀ ℂ :=
    fun i ↦ (bQ i).1
  have hspanU : Submodule.span ℂ (Set.range cU) = U := by
    simpa only [cU, bU] using span_range_ofVectorSpace_subtype U
  have hspanQ : Submodule.span ℂ (Set.range cQ) = Q := by
    simpa only [cQ, bQ] using span_range_ofVectorSpace_subtype Q
  have hcU : LinearIndependent ℂ cU := by
    exact bU.linearIndependent.map' U.subtype U.ker_subtype
  have hcQ : LinearIndependent ℂ cQ := by
    exact bQ.linearIndependent.map' Q.subtype Q.ker_subtype
  have hcUQ : LinearIndependent ℂ (Sum.elim cU cQ) :=
    hcU.sum_type hcQ (by rw [hspanU, hspanQ]; exact hUQ)
  have hspanUQ : Submodule.span ℂ (Set.range (Sum.elim cU cQ)) = U ⊔ W := by
    rw [Set.Sum.elim_range, Submodule.span_union, hspanU, hspanQ, hUQsup]
  have hfieldU := cofiniteTailDenseOn_analyticObservableCoordinateField_eq_grassmannField
    x K hx f hf hlinear M hM a cU hcU U hspanU
  have hfieldQ := cofiniteTailDenseOn_analyticObservableCoordinateField_eq_grassmannField
    x K hx f hf hlinear M hM a cQ hcQ Q hspanQ
  have hfieldUQ := cofiniteTailDenseOn_analyticObservableCoordinateField_eq_grassmannField
    x K hx f hf hlinear M hM a (Sum.elim cU cQ) hcUQ (U ⊔ W) hspanUQ
  have hsum := analyticObservableCoordinateField_sum x f M hM a cU cQ
  apply le_antisymm
  · apply sup_le
    · exact (cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
        x K hx f hf hlinear M hM a U (U ⊔ W)).mpr le_sup_left
    · exact (cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
        x K hx f hf hlinear M hM a W (U ⊔ W)).mpr le_sup_right
  · rw [← hfieldUQ, hsum, hfieldU, hfieldQ]
    exact sup_le le_sup_left
      ((cofiniteTailDenseOn_analyticObservableGrassmannField_le_iff
        x K hx f hf hlinear M hM a Q W).mpr hQW |>.trans le_sup_right)

/-! ## Canonical source extraction and the split Galois connection -/

/-- The carrier jet of order k as a complex-linear map of the finitely supported source
coordinate.  This is the algebraic interface used to decode source directions from an arbitrary
ambient intermediate field. -/
def analyticObservableCoordinateJetLinearMap
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (k : ℕ) : (J →₀ ℂ) →ₗ[ℂ] upperEndMeroField :=
  Finsupp.linearCombination ℂ fun j ↦
    GaloisForLFunctions.differentialJet k
      (analyticPrimeObservableShiftCarrier
        (fun p ↦ f j (x p)) (M j) (hM j) a)

/-- Every actual coordinate-carrier jet is exactly the corresponding value of the coordinate jet
linear map. -/
theorem differentialJet_analyticObservableCoordinateCarrier
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (k : ℕ) (c : J →₀ ℂ) :
    GaloisForLFunctions.differentialJet k
        (analyticPrimeObservableShiftCarrier
          (fun p ↦ analyticObservableCoordinateSource f c (x p))
          (analyticObservableCoordinateBound M c)
          (analyticObservableCoordinateSource_bound x f M hM c) a) =
      analyticObservableCoordinateJetLinearMap x f M hM a k c := by
  have h := differentialJet_analyticPrimeObservableShiftCarrier_finsuppLinearCombination
    (fun j p ↦ f j (x p)) M hM c
    (fun p ↦ analyticObservableCoordinateSource f c (x p))
    (analyticObservableCoordinateBound M c)
    (analyticObservableCoordinateSource_bound x f M hM c)
    (fun p ↦ by
      simp [analyticObservableCoordinateSource,
        Finsupp.linearCombination_apply, Finsupp.sum]) a k
  simpa [analyticObservableCoordinateJetLinearMap,
    Finsupp.linearCombination_apply, Finsupp.sum] using h

/-- The canonical source subspace decoded from an arbitrary ambient intermediate field: a
coordinate belongs exactly when the field contains every jet of its analytic carrier.  The
definition makes sense without assuming that the ambient field is derivation-closed. -/
def analyticObservableRecoveredJetSource
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ)
    (F : IntermediateField upperEndRationalCoordinateField upperEndMeroField) :
    Submodule ℂ (J →₀ ℂ) :=
  ⨅ k, (F.toSubalgebra.toSubmodule.restrictScalars ℂ).comap
    (analyticObservableCoordinateJetLinearMap x f M hM a k)

@[simp]
theorem mem_analyticObservableRecoveredJetSource_iff
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ)
    (F : IntermediateField upperEndRationalCoordinateField upperEndMeroField)
    (c : J →₀ ℂ) :
    c ∈ analyticObservableRecoveredJetSource x f M hM a F ↔
      ∀ k, analyticObservableCoordinateJetLinearMap x f M hM a k c ∈ F := by
  simp [analyticObservableRecoveredJetSource]

/-- **Canonical source-field adjunction.** The field generated by a source subspace is contained
in an arbitrary ambient intermediate field exactly when the source subspace lies in the canonical
all-jet source subspace decoded from that field.  This statement is purely structural and requires
no tail-density or source-independence hypothesis. -/
theorem analyticObservableGrassmann_galoisConnection
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) :
    GaloisConnection
      (analyticObservableGrassmannField x f M hM a)
      (analyticObservableRecoveredJetSource x f M hM a) := by
  intro W F
  constructor
  · intro hWF
    have hWrecovered :
        W ≤ analyticObservableRecoveredJetSource x f M hM a
          (analyticObservableGrassmannField x f M hM a W) := by
      have hbasis :
          Submodule.span ℂ
              (Set.range (fun i : Module.Basis.ofVectorSpaceIndex ℂ W ↦
                ((Module.Basis.ofVectorSpace ℂ W i : W) : J →₀ ℂ))) ≤
            analyticObservableRecoveredJetSource x f M hM a
              (analyticObservableGrassmannField x f M hM a W) := by
        apply Submodule.span_le.mpr
        rintro c ⟨i, rfl⟩
        apply (mem_analyticObservableRecoveredJetSource_iff
          x f M hM a _ _).mpr
        intro k
        change analyticObservableCoordinateJetLinearMap x f M hM a k
            (analyticObservableGrassmannCoordinate W i) ∈
          analyticObservableGrassmannField x f M hM a W
        rw [← differentialJet_analyticObservableCoordinateCarrier
          x f M hM a k (analyticObservableGrassmannCoordinate W i)]
        unfold analyticObservableGrassmannField analyticObservableShiftField
        simpa only [analyticObservableGrassmannSource,
          analyticObservableGrassmannBound] using
          GaloisForLFunctions.differentialJet_mem_differentialAdjoin
            upperEndRationalCoordinateField (Set.mem_range_self i) k
      rw [span_range_ofVectorSpace_subtype W] at hbasis
      exact hbasis
    intro c hc
    apply (mem_analyticObservableRecoveredJetSource_iff
      x f M hM a F c).mpr
    intro k
    exact hWF ((mem_analyticObservableRecoveredJetSource_iff
      x f M hM a _ c).mp (hWrecovered hc) k)
  · intro hW
    unfold analyticObservableGrassmannField analyticObservableShiftField
    unfold GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨z, ⟨i, rfl⟩, k, rfl⟩
    have hcoord :
        analyticObservableGrassmannCoordinate W i ∈ W :=
      (Module.Basis.ofVectorSpace ℂ W i).2
    have hmem := (mem_analyticObservableRecoveredJetSource_iff
      x f M hM a F _).mp (hW hcoord) k
    rw [← differentialJet_analyticObservableCoordinateCarrier
      x f M hM a k (analyticObservableGrassmannCoordinate W i)] at hmem
    simpa only [analyticObservableGrassmannSource,
      analyticObservableGrassmannBound] using hmem

/-- **Exact source reconstruction from the represented field.** Under tail completeness and
source independence, the canonical all-jet decoder is a left inverse to the analytic Grassmann
field representation. -/
theorem cofiniteTailDenseOn_analyticObservableRecoveredJetSource_grassmannField
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : Submodule ℂ (J →₀ ℂ)) :
    analyticObservableRecoveredJetSource x f M hM a
        (analyticObservableGrassmannField x f M hM a W) = W := by
  apply le_antisymm
  · intro c hc
    have hzero := (mem_analyticObservableRecoveredJetSource_iff
      x f M hM a _ c).mp hc 0
    rw [← differentialJet_analyticObservableCoordinateCarrier
      x f M hM a 0 c] at hzero
    simpa only [GaloisForLFunctions.differentialJet_zero] using
      (cofiniteTailDenseOn_analyticObservableCoordinateCarrier_mem_grassmannField_iff
        x K hx f hf hlinear M hM a W c).mp hzero
  · exact (analyticObservableGrassmann_galoisConnection
      x f M hM a).le_u_l W

/-- The analytic Grassmann representation and canonical source decoder form a split Galois
connection: source reconstruction is exact on every represented field. -/
noncomputable def cofiniteTailDenseOn_analyticObservableGrassmannGaloisCoinsertion
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) :
    GaloisCoinsertion
      (analyticObservableGrassmannField x f M hM a)
      (analyticObservableRecoveredJetSource x f M hM a) :=
  (analyticObservableGrassmann_galoisConnection
    x f M hM a).toGaloisCoinsertion fun W ↦
      le_of_eq (cofiniteTailDenseOn_analyticObservableRecoveredJetSource_grassmannField
        x K hx f hf hlinear M hM a W)

/-- **Arbitrary compositum law.** The source-field adjunction forces preservation of arbitrary
source-subspace joins, not only binary sums. -/
theorem analyticObservableGrassmannField_iSup
    {V : Type u} {J : Type v} {ι : Sort*}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : ι → Submodule ℂ (J →₀ ℂ)) :
    analyticObservableGrassmannField x f M hM a (⨆ i, W i) =
      ⨆ i, analyticObservableGrassmannField x f M hM a (W i) :=
  (analyticObservableGrassmann_galoisConnection
    x f M hM a).l_iSup

/-- The canonical source-representable core of an arbitrary ambient intermediate field. -/
def analyticObservableRepresentableCore
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ)
    (F : IntermediateField upperEndRationalCoordinateField upperEndMeroField) :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  analyticObservableGrassmannField x f M hM a
    (analyticObservableRecoveredJetSource x f M hM a F)

/-- The representable core is contained in the ambient field from which it was decoded. -/
theorem analyticObservableRepresentableCore_le
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ)
    (F : IntermediateField upperEndRationalCoordinateField upperEndMeroField) :
    analyticObservableRepresentableCore x f M hM a F ≤ F :=
  (analyticObservableGrassmann_galoisConnection x f M hM a).l_u_le F

/-- **Maximality of the representable core.** Every analytic source field contained in an ambient
field is contained in its canonical representable core. -/
theorem analyticObservableGrassmannField_le_representableCore_of_le
    {V : Type u} {J : Type v}
    (x : Nat.Primes → V) (f : J → V → ℂ)
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (W : Submodule ℂ (J →₀ ℂ))
    (F : IntermediateField upperEndRationalCoordinateField upperEndMeroField)
    (hWF : analyticObservableGrassmannField x f M hM a W ≤ F) :
    analyticObservableGrassmannField x f M hM a W ≤
      analyticObservableRepresentableCore x f M hM a F := by
  apply (analyticObservableGrassmann_galoisConnection x f M hM a).monotone_l
  exact (analyticObservableGrassmann_galoisConnection x f M hM a W F).mp hWF

/-- Under tail completeness and source independence, taking the representable core is idempotent. -/
theorem cofiniteTailDenseOn_analyticObservableRepresentableCore_idempotent
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ)
    (F : IntermediateField upperEndRationalCoordinateField upperEndMeroField) :
    analyticObservableRepresentableCore x f M hM a
        (analyticObservableRepresentableCore x f M hM a F) =
      analyticObservableRepresentableCore x f M hM a F := by
  unfold analyticObservableRepresentableCore
  rw [cofiniteTailDenseOn_analyticObservableRecoveredJetSource_grassmannField
    x K hx f hf hlinear M hM a]

/-- **Analytic modularity law.** Although the ambient lattice of intermediate fields need not be
modular, the analytic fields carried by source subspaces form a modular sublattice.  Thus a source
inclusion `U ≤ W` forces the exact modular identity among the corresponding embedded differential
fields. -/
theorem cofiniteTailDenseOn_analyticObservableGrassmannField_modular
    {V : Type u} {J : Type v} [TopologicalSpace V]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j ↦ fun z : K ↦ f j z.1))
    (M : J → ℝ) (hM : ∀ j p, ‖f j (x p)‖ ≤ M j)
    (a : ℂ) (U V₀ W : Submodule ℂ (J →₀ ℂ)) (hUW : U ≤ W) :
    (analyticObservableGrassmannField x f M hM a U ⊔
        analyticObservableGrassmannField x f M hM a V₀) ⊓
          analyticObservableGrassmannField x f M hM a W =
      analyticObservableGrassmannField x f M hM a U ⊔
        (analyticObservableGrassmannField x f M hM a V₀ ⊓
          analyticObservableGrassmannField x f M hM a W) := by
  rw [cofiniteTailDenseOn_analyticObservableGrassmannField_sup
      x K hx f hf hlinear M hM a U V₀,
    cofiniteTailDenseOn_analyticObservableGrassmannField_inf
      x K hx f hf hlinear M hM a (U ⊔ V₀) W,
    cofiniteTailDenseOn_analyticObservableGrassmannField_inf
      x K hx f hf hlinear M hM a V₀ W,
    cofiniteTailDenseOn_analyticObservableGrassmannField_sup
      x K hx f hf hlinear M hM a U (V₀ ⊓ W),
    sup_inf_assoc_of_le V₀ hUW]

end

end GaloisForLFunctions.HTGeometry
