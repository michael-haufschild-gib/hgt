import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeValuationMaster
import GaloisForLFunctions.HTGeometry.HomogeneousConstraintValuationFunctoriality
import GaloisForLFunctions.HTGeometry.PrimeValuationProfileFieldClassification

/-!
# Tail-dense observable field classification

A tail-dense prime profile turns finite-dimensional spaces of continuous source observables into
embedded differential fields without losing the source linear geometry.  One common Dirichlet
shift already suffices: membership in the generated differential field is exactly membership in
the linear span of the source observables on the constraint set.  Consequently field inclusion
and field equality are classified by inclusion and equality of observable subspaces.

This is the source-space form of valuation--Hilbert completeness.  Polynomial restriction spaces
recover the homogeneous Hilbert layers, while arbitrary continuous observable spaces give the
intrinsic field-moduli statement.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Differential

noncomputable section

universe u v

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000

local instance complexFinitePrimeRationalAmbientScalarTowerTailDense :
    IsScalarTower ℂ finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  .of_algebraMap_eq fun z => by
    change algebraMap ℂ arithmeticFunctionRationalCoordinateField z =
      finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap ℂ finitePrimeRationalCoefficientField z)
    rw [IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      finitePrimeRationalCoefficientField]
    rw [finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap]
    rw [← IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      arithmeticFunctionFractionField]
    rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField]

/-- The differential carrier of a continuous observable sampled by a prime profile. -/
def tailDenseObservableShiftCarrier
    {V : Type*} (x : Nat.Primes → V) (f : V → ℂ) (a : ℂ) :
    arithmeticFunctionRationalCoordinateField :=
  primeCoefficientShiftCarrier (fun p => f (x p)) a

/-- Tail density is natural under continuous maps: every cofinite tail remains dense in the
geometric image. -/
theorem cofiniteTailDenseOn_comp_continuous
    {P V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (φ : V → W) (hφ : Continuous φ) :
    CofiniteTailDenseOn (φ ∘ x) (φ '' K) := by
  constructor
  · rintro _ ⟨p, rfl⟩
    exact ⟨x p, hx.1 ⟨p, rfl⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (hx.2 v hv).continuousAt_comp hφ.continuousAt

/-- A homogeneous polynomial constraint map is continuous for the product topologies. -/
theorem HomogeneousConstraintMap.continuous_apply
    {σ τ : Type*} {q : ℕ} (Φ : HomogeneousConstraintMap σ τ q) :
    Continuous Φ.apply := by
  apply continuous_pi
  intro j
  exact MvPolynomial.continuous_eval (Φ.coord j).1

/-- Natural pushforward of a tail-dense constraint realization through a homogeneous map. -/
theorem HomogeneousConstraintMap.pushforward_cofiniteTailDenseOn
    {σ τ : Type*} {q : ℕ} (Φ : HomogeneousConstraintMap σ τ q)
    (x : Nat.Primes → σ → ℂ) (K : Set (σ → ℂ))
    (hx : CofiniteTailDenseOn x K) :
    CofiniteTailDenseOn (fun p => Φ.apply (x p)) (Φ.apply '' K) := by
  simpa only [Function.comp_apply] using
    cofiniteTailDenseOn_comp_continuous x K hx Φ.apply Φ.continuous_apply

/-- Every finite linearly independent family of continuous observables on the constraint set
gives a differentially independent family of prime-supported carriers at any one common shift. -/
theorem cofiniteTailDenseOn_observableShiftCarrier_differentialIndependent
    {V : Type u} {J : Type v}
    [TopologicalSpace V] [Fintype J] [DecidableEq J] [Nonempty J]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (a : ℂ) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun j => tailDenseObservableShiftCarrier x (f j) a) := by
  unfold GaloisForLFunctions.DifferentialIndependent
  simp_rw [tailDenseObservableShiftCarrier,
    differentialJet_primeCoefficientShiftCarrier]
  let y : J → ℕ → arithmeticFunctionRationalCoordinateField := fun j k =>
    algebraMap arithmeticFunctionFractionField arithmeticFunctionRationalCoordinateField
      (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (primeCoefficientShiftedRotatedJet (fun p => f j (x p)) a k))
  apply algebraicIndependent_prod_nat_of_fin y
  intro m
  let coeff : J × (Unit × Fin (m + 1)) → Nat.Primes → ℂ := fun jak p =>
    f jak.1 (x p) * primeShiftFactor a p * rotatedPrimeLogClock p ^ (jak.2.2 : ℕ)
  have htail : TailCoefficientIndependent coeff := by
    have h :=
      cofiniteTailDenseOn_primePowerShiftedRotatedJet_tailIndependent
        0 x K hx f hf hlinear (fun _ : Unit => a) (by
          intro b c _
          exact Subsingleton.elim b c) m
    norm_num at h
    simpa only [coeff] using h
  have hraw :=
    (algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField_iff
      coeff).2 htail
  have hbase :=
    algebraicIndependent_constants_over_finitePrimeRationalCoefficientField _ hraw
  let e : J × Fin (m + 1) → J × (Unit × Fin (m + 1)) := fun jk =>
    (jk.1, ((), jk.2))
  have he : Function.Injective e := by
    intro j k h
    exact Prod.ext (congrArg (fun z => z.1) h) (congrArg (fun z => z.2.2) h)
  have hsub := hbase.comp e he
  simpa only [Function.comp_apply, e, coeff, y,
    primeCoefficientShiftedRotatedJet] using hsub

/-- The embedded differential field generated by a finite observable family at one common
Dirichlet shift. -/
def tailDenseObservableShiftField
    {V J : Type*} (x : Nat.Primes → V) (f : J → V → ℂ) (a : ℂ) :
    IntermediateField finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
    (Set.range fun j => tailDenseObservableShiftCarrier x (f j) a)

/-- **Tail-dense source membership law.** Relative hypertranscendence is exactly escape from the
source-observable span: a new continuous observable carrier belongs to the differential field of
an independent finite family precisely when its restriction to the constraint set belongs to the
ordinary linear span of that family. -/
theorem cofiniteTailDenseOn_observableShiftCarrier_mem_field_iff_mem_span
    {V : Type u} {d : ℕ} [TopologicalSpace V] [Nonempty (Fin d)]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : Fin d → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (g : V → ℂ) (hg : Continuous g) (a : ℂ) :
    tailDenseObservableShiftCarrier x g a ∈
        tailDenseObservableShiftField x f a ↔
      (fun v : K => g v.1) ∈
        Submodule.span ℂ (Set.range fun j => fun v : K => f j v.1) := by
  let vf : Fin d → K → ℂ := fun j v => f j v.1
  let vg : K → ℂ := fun v => g v.1
  constructor
  · intro hmem
    by_contra hnot
    let F : Fin (d + 1) → V → ℂ := Fin.snoc f g
    have hFcontinuous : ∀ j, Continuous (F j) := by
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa [F] using hg
      · simpa [F] using hf i
    have hFlinear : LinearIndependent ℂ (fun j => fun v : K => F j v.1) := by
      have hsnoc : LinearIndependent ℂ (Fin.snoc vf vg) :=
        linearIndependent_finSnoc.mpr ⟨hlinear, hnot⟩
      have heq : (fun j => fun v : K => F j v.1) = Fin.snoc vf vg := by
        funext j v
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp [F, vf, vg]
        · simp [F, vf, vg]
      rw [heq]
      exact hsnoc
    have hDIext :=
      cofiniteTailDenseOn_observableShiftCarrier_differentialIndependent
        x K hx F hFcontinuous hFlinear a
    let u : Fin d → arithmeticFunctionRationalCoordinateField := fun j =>
      tailDenseObservableShiftCarrier x (f j) a
    let v : Fin 1 → arithmeticFunctionRationalCoordinateField := fun _ =>
      tailDenseObservableShiftCarrier x g a
    let e : Fin d ⊕ Fin 1 ≃ Fin (d + 1) := finSumFinEquiv
    have hDIsum : GaloisForLFunctions.DifferentialIndependent
        finitePrimeRationalCoefficientField (Sum.elim u v) := by
      have hcomp := hDIext.comp e e.injective
      have hfun :
          ((fun j => tailDenseObservableShiftCarrier x (F j) a) ∘ e) =
            Sum.elim u v := by
        funext q
        rcases q with j | k
        · change tailDenseObservableShiftCarrier x
              ((Fin.snoc f g : Fin (d + 1) → V → ℂ) j.castSucc) a = u j
          rw [Fin.snoc_castSucc]
        · have hk : k = 0 := Subsingleton.elim _ _
          subst k
          change tailDenseObservableShiftCarrier x
              ((Fin.snoc f g : Fin (d + 1) → V → ℂ) (Fin.last d)) a = v 0
          rw [Fin.snoc_last]
      rw [hfun] at hcomp
      exact hcomp
    exact differentialIndependent_sum_right_not_mem_left_differentialAdjoin
      u v hDIsum 0 hmem
  · intro hspan
    rw [← Fintype.range_linearCombination ℂ vf] at hspan
    obtain ⟨A, hA⟩ := hspan
    have hcoeff : (fun p : Nat.Primes => g (x p)) =
        fun p => ∑ j, A j * f j (x p) := by
      funext p
      have hpK : x p ∈ K := hx.1 ⟨p, rfl⟩
      have hp := congrFun hA ⟨x p, hpK⟩
      simpa [Fintype.linearCombination_apply, vf, vg] using hp.symm
    change primeCoefficientShiftCarrier (fun p => g (x p)) a ∈ _
    rw [hcoeff]
    have hjet := differentialJet_primeCoefficientShiftCarrier_linearCombination
      (fun j p => f j (x p)) A a 0
    have hcarrier :
        primeCoefficientShiftCarrier (fun p => ∑ j, A j * f j (x p)) a =
          ∑ j, algebraMap ℂ arithmeticFunctionRationalCoordinateField (A j) *
            tailDenseObservableShiftCarrier x (f j) a := by
      simpa [tailDenseObservableShiftCarrier] using hjet
    rw [hcarrier]
    apply IntermediateField.sum_mem
    intro j _
    apply IntermediateField.mul_mem
    · rw [IsScalarTower.algebraMap_apply ℂ finitePrimeRationalCoefficientField
        arithmeticFunctionRationalCoordinateField]
      exact IntermediateField.algebraMap_mem _
        (algebraMap ℂ finitePrimeRationalCoefficientField (A j))
    · exact GaloisForLFunctions.subset_differentialAdjoin
        finitePrimeRationalCoefficientField _ (Set.mem_range_self j)

/-- **Tail-dense observable field order law.** Relative to an independent target family sampled
by the same tail-dense profile, inclusion of embedded differential fields is equivalent to
inclusion of source-observable spans on the constraint set. -/
theorem cofiniteTailDenseOn_observableShiftField_le_iff_span_le
    {V : Type u} {d e : ℕ} [TopologicalSpace V]
    [Nonempty (Fin d)] [Nonempty (Fin e)]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : Fin d → V → ℂ) (g : Fin e → V → ℂ)
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hgind : LinearIndependent ℂ (fun j => fun v : K => g j v.1))
    (a : ℂ) :
    tailDenseObservableShiftField x f a ≤ tailDenseObservableShiftField x g a ↔
      Submodule.span ℂ (Set.range fun j => fun v : K => f j v.1) ≤
        Submodule.span ℂ (Set.range fun j => fun v : K => g j v.1) := by
  constructor
  · intro hfield
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨j, rfl⟩ := hw
    apply (cofiniteTailDenseOn_observableShiftCarrier_mem_field_iff_mem_span
      x K hx g hg hgind (f j) (hf j) a).mp
    apply hfield
    exact GaloisForLFunctions.subset_differentialAdjoin
      finitePrimeRationalCoefficientField _ (Set.mem_range_self j)
  · intro hspan
    unfold tailDenseObservableShiftField GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨y, ⟨j, rfl⟩, n, rfl⟩
    let vg : Fin e → K → ℂ := fun i v => g i v.1
    have hfj : (fun v : K => f j v.1) ∈ Submodule.span ℂ (Set.range vg) := by
      apply hspan
      exact Submodule.subset_span (Set.mem_range_self j)
    rw [← Fintype.range_linearCombination ℂ vg] at hfj
    obtain ⟨A, hA⟩ := hfj
    have hcoeff : (fun p : Nat.Primes => f j (x p)) =
        fun p => ∑ i, A i * g i (x p) := by
      funext p
      have hpK : x p ∈ K := hx.1 ⟨p, rfl⟩
      have hp := congrFun hA ⟨x p, hpK⟩
      simpa [Fintype.linearCombination_apply, vg] using hp.symm
    change GaloisForLFunctions.differentialJet n
      (primeCoefficientShiftCarrier (fun p => f j (x p)) a) ∈ _
    rw [hcoeff]
    rw [differentialJet_primeCoefficientShiftCarrier_linearCombination]
    apply IntermediateField.sum_mem
    intro i _
    apply IntermediateField.mul_mem
    · rw [IsScalarTower.algebraMap_apply ℂ finitePrimeRationalCoefficientField
        arithmeticFunctionRationalCoordinateField]
      exact IntermediateField.algebraMap_mem _
        (algebraMap ℂ finitePrimeRationalCoefficientField (A i))
    · exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        finitePrimeRationalCoefficientField (Set.mem_range_self i) n

/-- **Tail-dense Grassmann field classification.** Two independent finite continuous source
families generate the same embedded differential field at one common shift exactly when their
restriction spans on the constraint set are equal. Thus the construction is a faithful order
embedding of the finite-dimensional observable-subspace lattice into embedded differential
fields. -/
theorem cofiniteTailDenseOn_observableShiftField_eq_iff_span_eq
    {V : Type u} {d e : ℕ} [TopologicalSpace V]
    [Nonempty (Fin d)] [Nonempty (Fin e)]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : Fin d → V → ℂ) (g : Fin e → V → ℂ)
    (hf : ∀ j, Continuous (f j)) (hg : ∀ j, Continuous (g j))
    (hfind : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (hgind : LinearIndependent ℂ (fun j => fun v : K => g j v.1))
    (a : ℂ) :
    tailDenseObservableShiftField x f a = tailDenseObservableShiftField x g a ↔
      Submodule.span ℂ (Set.range fun j => fun v : K => f j v.1) =
        Submodule.span ℂ (Set.range fun j => fun v : K => g j v.1) := by
  let hfg := cofiniteTailDenseOn_observableShiftField_le_iff_span_le
    x K hx f g hf hg hgind a
  let hgf := cofiniteTailDenseOn_observableShiftField_le_iff_span_le
    x K hx g f hg hf hfind a
  constructor
  · intro hfield
    apply le_antisymm
    · exact hfg.mp hfield.le
    · exact hgf.mp hfield.ge
  · intro hspan
    apply le_antisymm
    · exact hfg.mpr hspan.le
    · exact hgf.mpr hspan.ge

/-- **Homogeneous constraint reconstruction law.** For tail-dense profiles, equality of the full
graded prime-tail relation system is equivalent to equality of the full homogeneous vanishing
system of the source constraints. The labelled arithmetic relations therefore recover exactly
the reduced homogeneous constraint algebra. -/
theorem cofiniteTailDenseOn_homogeneousRelationSystem_eq_iff_constraintSystem_eq
    {σ : Type u} [Fintype σ]
    (x y : Nat.Primes → σ → ℂ)
    (K L : Set (σ → ℂ))
    (hx : CofiniteTailDenseOn x K) (hy : CofiniteTailDenseOn y L) :
    (∀ m, homogeneousTailRelationSubmodule x m =
        homogeneousTailRelationSubmodule y m) ↔
      ∀ m, homogeneousConstraintVanishingSubmodule K m =
        homogeneousConstraintVanishingSubmodule L m := by
  constructor <;> intro h m
  · simpa only [
      homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
        x K hx m,
      homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
        y L hy m] using h m
  · rw [
      homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
        x K hx m,
      homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
        y L hy m]
    exact h m

end

end GaloisForLFunctions.HTGeometry
