import GaloisForLFunctions.HTGeometry.FiniteQuotientPrimeDifferentialDuality
import GaloisForLFunctions.HTGeometry.TailCompletePrimeValuationFusionRepresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite-quotient interaction cohomology

Finite observable subspaces are sent to embedded prime differential fields by adjoining the
carriers of all their observables.  On a tail-complete source this construction is a faithful
lattice embedding: source sums become field composita and source intersections become field
intersections.

For two finite quotient relations `r` and `s`, their separate invariant-observable spaces do not
usually span every observable of the common refinement `r ⊓ s`.  The quotient of the joint-cell
space by the two marginal spaces is the interaction cohomology.  Its dimension is the exact
Euler defect

`|W/(r ⊓ s)| - |W/r| - |W/s| + |W/(r ⊔ s)|`.

The capstone theorem constructs a complementary representative of this cohomology.  Any basis of
that complement is differentially independent over the compositum of the two marginal fields,
has exactly the Euler-defect cardinality, and adjoining it generates the full common-refinement
field.  Thus every missing hypertranscendental direction is an interaction-cohomology direction,
and there are no others.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000

universe u

variable {W : Type u}

local instance complexFinitePrimeRationalAmbientScalarTowerInteraction :
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

theorem classInvariantRestricted_finrank (r : Setoid W)
    [Fintype (FiniteQuotientType r)] :
    Module.finrank ℂ (ClassInvariantRestricted r) =
      Fintype.card (FiniteQuotientType r) := by
  rw [← finiteClassDeltaRestricted_span_eq_invariant r]
  simpa [FiniteQuotientRank] using
    (finrank_span_eq_card (finiteClassDeltaRestricted_linearIndependent r))

theorem classInvariantRestricted_supSetoid_eq_inf
    (r s : Setoid W) :
    ClassInvariantRestricted (r ⊔ s) =
      ClassInvariantRestricted r ⊓ ClassInvariantRestricted s := by
  ext f
  constructor
  · intro hf
    constructor
    · intro x y hxy
      exact hf x y ((show r ≤ r ⊔ s from le_sup_left) hxy)
    · intro x y hxy
      exact hf x y ((show s ≤ r ⊔ s from le_sup_right) hxy)
  · rintro ⟨hr, hs⟩
    let t : Setoid W := Setoid.ker (fun w ↦ f ⟨w, Set.mem_univ _⟩)
    have hrt : r ≤ t := by
      intro x y hxy
      exact hr ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ hxy
    have hst : s ≤ t := by
      intro x y hxy
      exact hs ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ hxy
    intro x y hxy
    exact (sup_le hrt hst) hxy

theorem classInvariantRestricted_sup_le_infSetoid
    (r s : Setoid W) :
    ClassInvariantRestricted r ⊔ ClassInvariantRestricted s ≤
      ClassInvariantRestricted (r ⊓ s) := by
  apply sup_le
  · exact (classInvariantRestricted_le_iff_reverseSetoid r (r ⊓ s)).mpr inf_le_left
  · exact (classInvariantRestricted_le_iff_reverseSetoid s (r ⊓ s)).mpr inf_le_right

/-- The codimension of the two marginal observable spaces inside their common refinement. -/
def finiteQuotientInteractionDefect (r s : Setoid W) : ℕ :=
  Module.finrank ℂ (ClassInvariantRestricted (r ⊓ s)) -
    Module.finrank ℂ
      ↑((ClassInvariantRestricted r ⊔ ClassInvariantRestricted s) :
        Submodule ℂ (FullValueSubtype W → ℂ))

def finiteQuotientInteractionMarginalSubmodule (r s : Setoid W) :
    Submodule ℂ (ClassInvariantRestricted (r ⊓ s)) :=
  (ClassInvariantRestricted r ⊔ ClassInvariantRestricted s).comap
    (ClassInvariantRestricted (r ⊓ s)).subtype

/-- The canonical joint-observable quotient modulo observables visible to the two marginals. -/
abbrev FiniteQuotientInteractionCohomology (r s : Setoid W) :=
  (ClassInvariantRestricted (r ⊓ s)) ⧸
    finiteQuotientInteractionMarginalSubmodule r s

theorem classInvariantRestricted_sup_finrank
    [Nonempty W] (r s : Setoid W)
    [Fintype (FiniteQuotientType r)]
    [Fintype (FiniteQuotientType s)]
    [Fintype (FiniteQuotientType (r ⊔ s))] :
    Module.finrank ℂ
        ↑((ClassInvariantRestricted r ⊔ ClassInvariantRestricted s) :
          Submodule ℂ (FullValueSubtype W → ℂ)) =
      Fintype.card (FiniteQuotientType r) +
        Fintype.card (FiniteQuotientType s) -
          Fintype.card (FiniteQuotientType (r ⊔ s)) := by
  have hrank := classInvariantRestricted_finrank r
  have hsrank := classInvariantRestricted_finrank s
  have hjrank := classInvariantRestricted_finrank (r ⊔ s)
  have hrpos : 0 < Module.finrank ℂ (ClassInvariantRestricted r) := by
    rw [hrank]
    exact Fintype.card_pos_iff.mpr ((nonempty_quotient_iff r).mpr inferInstance)
  have hspos : 0 < Module.finrank ℂ (ClassInvariantRestricted s) := by
    rw [hsrank]
    exact Fintype.card_pos_iff.mpr ((nonempty_quotient_iff s).mpr inferInstance)
  letI : FiniteDimensional ℂ (ClassInvariantRestricted r) :=
    FiniteDimensional.of_finrank_pos hrpos
  letI : FiniteDimensional ℂ (ClassInvariantRestricted s) :=
    FiniteDimensional.of_finrank_pos hspos
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (ClassInvariantRestricted r) (ClassInvariantRestricted s)
  rw [← classInvariantRestricted_supSetoid_eq_inf r s, hrank, hsrank, hjrank] at hdim
  omega

theorem finiteQuotientInteractionDefect_eq_euler
    [Nonempty W] (r s : Setoid W)
    [Fintype (FiniteQuotientType r)]
    [Fintype (FiniteQuotientType s)]
    [Fintype (FiniteQuotientType (r ⊔ s))]
    [Fintype (FiniteQuotientType (r ⊓ s))] :
    finiteQuotientInteractionDefect r s =
      Fintype.card (FiniteQuotientType (r ⊓ s)) -
        (Fintype.card (FiniteQuotientType r) +
          Fintype.card (FiniteQuotientType s) -
            Fintype.card (FiniteQuotientType (r ⊔ s))) := by
  rw [finiteQuotientInteractionDefect,
    classInvariantRestricted_finrank (r ⊓ s),
    classInvariantRestricted_sup_finrank r s]

noncomputable def finiteSubmoduleObservable
    (U : Submodule ℂ (FullValueSubtype W → ℂ)) [FiniteDimensional ℂ U]
    (j : Fin (Module.finrank ℂ U)) (w : W) : ℂ :=
  (Module.finBasis ℂ U j : FullValueSubtype W → ℂ) ⟨w, Set.mem_univ _⟩

theorem finiteSubmoduleObservable_restricted_linearIndependent
    (U : Submodule ℂ (FullValueSubtype W → ℂ)) [FiniteDimensional ℂ U] :
    LinearIndependent ℂ (fun j : Fin (Module.finrank ℂ U) ↦
      fun w : FullValueSubtype W ↦ finiteSubmoduleObservable U j w.1) := by
  have h := (Module.finBasis ℂ U).linearIndependent.map'
    U.subtype (Submodule.ker_subtype U)
  simpa [finiteSubmoduleObservable, Function.comp_def] using h

theorem finiteSubmoduleObservable_restricted_span
    (U : Submodule ℂ (FullValueSubtype W → ℂ)) [FiniteDimensional ℂ U] :
    Submodule.span ℂ (Set.range (fun j : Fin (Module.finrank ℂ U) ↦
      fun w : FullValueSubtype W ↦ finiteSubmoduleObservable U j w.1)) = U := by
  have hspan :
      Submodule.span ℂ (Set.range (U.subtype ∘ Module.finBasis ℂ U)) = U := by
    rw [Set.range_comp, Submodule.span_image, (Module.finBasis ℂ U).span_eq,
      Submodule.map_subtype_top]
  simpa [finiteSubmoduleObservable, Function.comp_def] using hspan

theorem differentialJet_tailDenseObservableShiftCarrier_add
    (y : Nat.Primes → W) (f g : W → ℂ) (a : ℂ) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (tailDenseObservableShiftCarrier y (f + g) a) =
      GaloisForLFunctions.differentialJet k
          (tailDenseObservableShiftCarrier y f a) +
        GaloisForLFunctions.differentialJet k
          (tailDenseObservableShiftCarrier y g a) := by
  have h := differentialJet_primeCoefficientShiftCarrier_linearCombination
    (B := Fin 2) (fun j p => Fin.cases (f (y p)) (fun _ => g (y p)) j)
      (fun _ => (1 : ℂ)) a k
  simpa [tailDenseObservableShiftCarrier, Pi.add_apply, Fin.sum_univ_two] using h

/-- The canonical prime differential field generated by every observable in a source subspace. -/
def primeObservableSubspaceShiftField
    (y : Nat.Primes → W) (U : Submodule ℂ (FullValueSubtype W → ℂ)) (a : ℂ) :
    IntermediateField finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
    (Set.range fun f : U =>
      tailDenseObservableShiftCarrier y (fun w => f.1 ⟨w, Set.mem_univ _⟩) a)

theorem primeObservableSubspaceShiftField_mono
    (y : Nat.Primes → W) {U V : Submodule ℂ (FullValueSubtype W → ℂ)}
    (hUV : U ≤ V) (a : ℂ) :
    primeObservableSubspaceShiftField y U a ≤
      primeObservableSubspaceShiftField y V a := by
  unfold primeObservableSubspaceShiftField GaloisForLFunctions.differentialAdjoin
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨x, ⟨f, rfl⟩, n, rfl⟩
  let g : V := ⟨f.1, hUV f.2⟩
  exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
    finitePrimeRationalCoefficientField (s := Set.range fun g : V =>
      tailDenseObservableShiftCarrier y (fun w => g.1 ⟨w, Set.mem_univ _⟩) a)
      (Set.mem_range_self g) n

/-- Canonical observable fields carry source sums exactly to field composita. -/
theorem primeObservableSubspaceShiftField_sup
    (y : Nat.Primes → W) (U V : Submodule ℂ (FullValueSubtype W → ℂ)) (a : ℂ) :
    primeObservableSubspaceShiftField y (U ⊔ V) a =
      primeObservableSubspaceShiftField y U a ⊔
        primeObservableSubspaceShiftField y V a := by
  apply le_antisymm
  · unfold primeObservableSubspaceShiftField GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨x, ⟨f, rfl⟩, n, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp f.2
    have hcarrier :
        (fun w : W => f.1 ⟨w, Set.mem_univ _⟩) =
          (fun w : W => u ⟨w, Set.mem_univ _⟩) +
            (fun w : W => v ⟨w, Set.mem_univ _⟩) := by
      funext w
      simpa [Pi.add_apply] using congrFun huv.symm ⟨w, Set.mem_univ _⟩
    change GaloisForLFunctions.differentialJet n
      (tailDenseObservableShiftCarrier y
        (fun w : W => f.1 ⟨w, Set.mem_univ _⟩) a) ∈ _
    rw [hcarrier, differentialJet_tailDenseObservableShiftCarrier_add]
    apply IntermediateField.add_mem
    · apply show
        GaloisForLFunctions.differentialJet n
            (tailDenseObservableShiftCarrier y
              (fun w : W => u ⟨w, Set.mem_univ _⟩) a) ∈
          primeObservableSubspaceShiftField y U a ⊔
            primeObservableSubspaceShiftField y V a from ?_
      exact (show primeObservableSubspaceShiftField y U a ≤
          primeObservableSubspaceShiftField y U a ⊔
            primeObservableSubspaceShiftField y V a from le_sup_left)
        (GaloisForLFunctions.differentialJet_mem_differentialAdjoin
          finitePrimeRationalCoefficientField
          (s := Set.range fun u : U =>
            tailDenseObservableShiftCarrier y
              (fun w => u.1 ⟨w, Set.mem_univ _⟩) a)
          (Set.mem_range_self (⟨u, hu⟩ : U)) n)
    · apply show
        GaloisForLFunctions.differentialJet n
            (tailDenseObservableShiftCarrier y
              (fun w : W => v ⟨w, Set.mem_univ _⟩) a) ∈
          primeObservableSubspaceShiftField y U a ⊔
            primeObservableSubspaceShiftField y V a from ?_
      exact (show primeObservableSubspaceShiftField y V a ≤
          primeObservableSubspaceShiftField y U a ⊔
            primeObservableSubspaceShiftField y V a from le_sup_right)
        (GaloisForLFunctions.differentialJet_mem_differentialAdjoin
          finitePrimeRationalCoefficientField
          (s := Set.range fun v : V =>
            tailDenseObservableShiftCarrier y
              (fun w => v.1 ⟨w, Set.mem_univ _⟩) a)
          (Set.mem_range_self (⟨v, hv⟩ : V)) n)
  · exact sup_le
      (primeObservableSubspaceShiftField_mono y le_sup_left a)
      (primeObservableSubspaceShiftField_mono y le_sup_right a)

theorem tailDenseObservableShiftField_sum
    {I J : Type*} (y : Nat.Primes → W)
    (f : I → W → ℂ) (g : J → W → ℂ) (a : ℂ) :
    tailDenseObservableShiftField y (Sum.elim f g) a =
      tailDenseObservableShiftField y f a ⊔
        tailDenseObservableShiftField y g a := by
  unfold tailDenseObservableShiftField GaloisForLFunctions.differentialAdjoin
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨x, ⟨q, rfl⟩, n, rfl⟩
    rcases q with i | j
    · exact (show
          IntermediateField.adjoin finitePrimeRationalCoefficientField
              (GaloisForLFunctions.differentialJetSet
                (Set.range fun i => tailDenseObservableShiftCarrier y (f i) a)) ≤
            IntermediateField.adjoin finitePrimeRationalCoefficientField
                (GaloisForLFunctions.differentialJetSet
                  (Set.range fun i => tailDenseObservableShiftCarrier y (f i) a)) ⊔
              IntermediateField.adjoin finitePrimeRationalCoefficientField
                (GaloisForLFunctions.differentialJetSet
                  (Set.range fun j => tailDenseObservableShiftCarrier y (g j) a))
          from le_sup_left)
        (GaloisForLFunctions.differentialJet_mem_differentialAdjoin
          finitePrimeRationalCoefficientField (Set.mem_range_self i) n)
    · exact (show
          IntermediateField.adjoin finitePrimeRationalCoefficientField
              (GaloisForLFunctions.differentialJetSet
                (Set.range fun j => tailDenseObservableShiftCarrier y (g j) a)) ≤
            IntermediateField.adjoin finitePrimeRationalCoefficientField
                (GaloisForLFunctions.differentialJetSet
                  (Set.range fun i => tailDenseObservableShiftCarrier y (f i) a)) ⊔
              IntermediateField.adjoin finitePrimeRationalCoefficientField
                (GaloisForLFunctions.differentialJetSet
                  (Set.range fun j => tailDenseObservableShiftCarrier y (g j) a))
          from le_sup_right)
        (GaloisForLFunctions.differentialJet_mem_differentialAdjoin
          finitePrimeRationalCoefficientField (Set.mem_range_self j) n)
  · apply sup_le
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro z ⟨x, ⟨i, rfl⟩, n, rfl⟩
      exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        finitePrimeRationalCoefficientField
        (s := Set.range fun q : I ⊕ J =>
          tailDenseObservableShiftCarrier y (Sum.elim f g q) a)
        (Set.mem_range_self (Sum.inl i)) n
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro z ⟨x, ⟨j, rfl⟩, n, rfl⟩
      exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        finitePrimeRationalCoefficientField
        (s := Set.range fun q : I ⊕ J =>
          tailDenseObservableShiftCarrier y (Sum.elim f g q) a)
        (Set.mem_range_self (Sum.inr j)) n

theorem primeObservableSubspaceShiftField_eq_basis
    (y : Nat.Primes → W) (U : Submodule ℂ (FullValueSubtype W → ℂ))
    [FiniteDimensional ℂ U] (a : ℂ) :
    primeObservableSubspaceShiftField y U a =
      tailDenseObservableShiftField y (finiteSubmoduleObservable U) a := by
  apply le_antisymm
  · unfold primeObservableSubspaceShiftField GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨x, ⟨f, rfl⟩, n, rfl⟩
    have hfspan : f.1 ∈ Submodule.span ℂ
        (Set.range (fun j : Fin (Module.finrank ℂ U) ↦
          fun w : FullValueSubtype W ↦ finiteSubmoduleObservable U j w.1)) := by
      rw [finiteSubmoduleObservable_restricted_span]
      exact f.2
    rw [← Fintype.range_linearCombination ℂ
      (fun j : Fin (Module.finrank ℂ U) ↦
        fun w : FullValueSubtype W ↦ finiteSubmoduleObservable U j w.1)] at hfspan
    obtain ⟨A, hA⟩ := hfspan
    have hcoeff :
        (fun p : Nat.Primes => f.1 ⟨y p, Set.mem_univ _⟩) =
          fun p => ∑ j, A j * finiteSubmoduleObservable U j (y p) := by
      funext p
      have hp := congrFun hA ⟨y p, Set.mem_univ _⟩
      simpa [Fintype.linearCombination_apply] using hp.symm
    change GaloisForLFunctions.differentialJet n
      (primeCoefficientShiftCarrier
        (fun p : Nat.Primes => f.1 ⟨y p, Set.mem_univ _⟩) a) ∈ _
    rw [hcoeff, differentialJet_primeCoefficientShiftCarrier_linearCombination]
    apply IntermediateField.sum_mem
    intro j _
    apply IntermediateField.mul_mem
    · rw [IsScalarTower.algebraMap_apply ℂ finitePrimeRationalCoefficientField
        arithmeticFunctionRationalCoordinateField]
      exact IntermediateField.algebraMap_mem _
        (algebraMap ℂ finitePrimeRationalCoefficientField (A j))
    · exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
        finitePrimeRationalCoefficientField
        (s := Set.range fun j : Fin (Module.finrank ℂ U) =>
          tailDenseObservableShiftCarrier y (finiteSubmoduleObservable U j) a)
        (Set.mem_range_self j) n
  · unfold tailDenseObservableShiftField GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨x, ⟨j, rfl⟩, n, rfl⟩
    exact GaloisForLFunctions.differentialJet_mem_differentialAdjoin
      finitePrimeRationalCoefficientField
      (s := Set.range fun f : U =>
        tailDenseObservableShiftCarrier y
          (fun w => f.1 ⟨w, Set.mem_univ _⟩) a)
      (Set.mem_range_self (Module.finBasis ℂ U j)) n

theorem cofiniteTailDenseOn_complementObservable_differentialIndependent
    [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (U Q : Submodule ℂ (FullValueSubtype W → ℂ))
    [FiniteDimensional ℂ U] [FiniteDimensional ℂ Q]
    (hUpos : 0 < Module.finrank ℂ U) (hUQ : Disjoint U Q) (a : ℂ) :
    GaloisForLFunctions.DifferentialIndependent
      (primeObservableSubspaceShiftField y U a)
      (fun j : Fin (Module.finrank ℂ Q) =>
        tailDenseObservableShiftCarrier y (finiteSubmoduleObservable Q j) a) := by
  letI : Nonempty (Fin (Module.finrank ℂ U)) := Fin.pos_iff_nonempty.mp hUpos
  let f : Fin (Module.finrank ℂ U) → W → ℂ := finiteSubmoduleObservable U
  let g : Fin (Module.finrank ℂ Q) → W → ℂ := finiteSubmoduleObservable Q
  have hlinear : LinearIndependent ℂ
      (fun q => fun w : FullValueSubtype W => Sum.elim f g q w.1) := by
    have hf := finiteSubmoduleObservable_restricted_linearIndependent U
    have hg := finiteSubmoduleObservable_restricted_linearIndependent Q
    have hfg := hf.sum_type hg (by
      rw [finiteSubmoduleObservable_restricted_span,
        finiteSubmoduleObservable_restricted_span]
      exact hUQ)
    have heq :
        (fun q => fun w : FullValueSubtype W => Sum.elim f g q w.1) =
          Sum.elim
            (fun j => fun w : FullValueSubtype W => finiteSubmoduleObservable U j w.1)
            (fun j => fun w : FullValueSubtype W => finiteSubmoduleObservable Q j w.1) := by
      funext q w
      rcases q with j | k <;> rfl
    rw [heq]
    exact hfg
  have hDI := cofiniteTailDenseOn_observableShiftCarrier_differentialIndependent
    y Set.univ hy (Sum.elim f g)
      (fun _ => continuous_of_discreteTopology) hlinear a
  let cf : Fin (Module.finrank ℂ U) →
      arithmeticFunctionRationalCoordinateField := fun j =>
    tailDenseObservableShiftCarrier y (f j) a
  let cg : Fin (Module.finrank ℂ Q) →
      arithmeticFunctionRationalCoordinateField := fun j =>
    tailDenseObservableShiftCarrier y (g j) a
  have hsum : GaloisForLFunctions.DifferentialIndependent
      finitePrimeRationalCoefficientField (Sum.elim cf cg) := by
    have hfun :
        (fun q => tailDenseObservableShiftCarrier y (Sum.elim f g q) a) =
          Sum.elim cf cg := by
      funext q
      rcases q with j | k <;> rfl
    rw [hfun] at hDI
    exact hDI
  have hrel := GaloisForLFunctions.differentialIndependent_sum_right_over_left_differentialAdjoin
    cf cg hsum
  change GaloisForLFunctions.DifferentialIndependent
    (tailDenseObservableShiftField y (finiteSubmoduleObservable U) a)
    (fun j : Fin (Module.finrank ℂ Q) =>
      tailDenseObservableShiftCarrier y (finiteSubmoduleObservable Q j) a) at hrel
  rw [← primeObservableSubspaceShiftField_eq_basis] at hrel
  exact hrel

theorem complement_finrank_eq_sub
    (U Q V : Submodule ℂ (FullValueSubtype W → ℂ))
    [FiniteDimensional ℂ U] [FiniteDimensional ℂ Q]
    (hdisj : Disjoint U Q) (hsup : U ⊔ Q = V) :
    Module.finrank ℂ Q = Module.finrank ℂ V - Module.finrank ℂ U := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq U Q
  rw [hsup, hdisj.eq_bot] at hdim
  simp only [finrank_bot, add_zero] at hdim
  omega

theorem exists_submodule_complement_of_le
    (U V : Submodule ℂ (FullValueSubtype W → ℂ)) (hUV : U ≤ V) :
    ∃ Q : Submodule ℂ (FullValueSubtype W → ℂ),
      Q ≤ V ∧ Disjoint U Q ∧ U ⊔ Q = V := by
  let U' : Submodule ℂ V := U.comap V.subtype
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl U'
  let Q : Submodule ℂ (FullValueSubtype W → ℂ) := Q'.map V.subtype
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

/-- On a tail-complete discrete source, canonical observable fields preserve finite intersections. -/
theorem cofiniteTailDenseOn_primeObservableSubspaceShiftField_inf
    [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (U V : Submodule ℂ (FullValueSubtype W → ℂ))
    [FiniteDimensional ℂ U] [FiniteDimensional ℂ V]
    (hApos : 0 < Module.finrank ℂ (↥(U ⊓ V))) (a : ℂ) :
    primeObservableSubspaceShiftField y U a ⊓
        primeObservableSubspaceShiftField y V a =
      primeObservableSubspaceShiftField y (U ⊓ V) a := by
  let A := U ⊓ V
  letI : FiniteDimensional ℂ A := inferInstance
  obtain ⟨B, hBU, hAB, hABsup⟩ :=
    exists_submodule_complement_of_le A U inf_le_left
  obtain ⟨C, hCV, hAC, hACsup⟩ :=
    exists_submodule_complement_of_le A V inf_le_right
  letI : FiniteDimensional ℂ B := Submodule.finiteDimensional_of_le hBU
  letI : FiniteDimensional ℂ C := Submodule.finiteDimensional_of_le hCV
  letI : Nonempty (Fin (Module.finrank ℂ A)) := Fin.pos_iff_nonempty.mp hApos
  have hUC : Disjoint U C := by
    rw [Submodule.disjoint_def]
    intro x hxU hxC
    have hxV : x ∈ V := hCV hxC
    have hxA : x ∈ A := ⟨hxU, hxV⟩
    exact (Submodule.disjoint_def.mp hAC) x hxA hxC
  have hABC : Disjoint (A ⊔ B) C := by
    rw [hABsup]
    exact hUC
  have hBC : Disjoint B C := hABC.mono_left le_sup_right
  have hA_BC : Disjoint A (B ⊔ C) :=
    hAB.disjoint_sup_right_of_disjoint_sup_left hABC
  let f : Fin (Module.finrank ℂ A) → W → ℂ := finiteSubmoduleObservable A
  let g : Fin (Module.finrank ℂ B) → W → ℂ := finiteSubmoduleObservable B
  let h : Fin (Module.finrank ℂ C) → W → ℂ := finiteSubmoduleObservable C
  have hlinear : LinearIndependent ℂ
      (fun q => fun w : FullValueSubtype W =>
        Sum.elim f (Sum.elim g h) q w.1) := by
    have hf := finiteSubmoduleObservable_restricted_linearIndependent A
    have hg := finiteSubmoduleObservable_restricted_linearIndependent B
    have hh := finiteSubmoduleObservable_restricted_linearIndependent C
    have hgh := hg.sum_type hh (by
      rw [finiteSubmoduleObservable_restricted_span,
        finiteSubmoduleObservable_restricted_span]
      exact hBC)
    have hghspan :
        Submodule.span ℂ (Set.range (Sum.elim
          (fun j => fun w : FullValueSubtype W => finiteSubmoduleObservable B j w.1)
          (fun k => fun w : FullValueSubtype W => finiteSubmoduleObservable C k w.1))) =
          B ⊔ C := by
      rw [Set.Sum.elim_range, Submodule.span_union,
        finiteSubmoduleObservable_restricted_span,
        finiteSubmoduleObservable_restricted_span]
    have htotal := hf.sum_type hgh (by
      rw [finiteSubmoduleObservable_restricted_span, hghspan]
      exact hA_BC)
    have heq :
        (fun q => fun w : FullValueSubtype W =>
          Sum.elim f (Sum.elim g h) q w.1) =
        Sum.elim
          (fun i => fun w : FullValueSubtype W => finiteSubmoduleObservable A i w.1)
          (Sum.elim
            (fun j => fun w : FullValueSubtype W => finiteSubmoduleObservable B j w.1)
            (fun k => fun w : FullValueSubtype W => finiteSubmoduleObservable C k w.1)) := by
      funext q w
      rcases q with i | q
      · rfl
      · rcases q with j | k <;> rfl
    rw [heq]
    exact htotal
  have hmeet := cofiniteTailDenseOn_observableShiftField_threeBlock_inf
    y Set.univ hy f g h
      (fun _ => continuous_of_discreteTopology)
      (fun _ => continuous_of_discreteTopology)
      (fun _ => continuous_of_discreteTopology) hlinear a
  rw [tailDenseObservableShiftField_sum,
    tailDenseObservableShiftField_sum] at hmeet
  rw [← primeObservableSubspaceShiftField_eq_basis y A a,
    ← primeObservableSubspaceShiftField_eq_basis y B a,
    ← primeObservableSubspaceShiftField_eq_basis y C a] at hmeet
  rw [← primeObservableSubspaceShiftField_sup,
    ← primeObservableSubspaceShiftField_sup, hABsup, hACsup] at hmeet
  exact hmeet

@[reducible] noncomputable def classInvariantRestrictedFiniteDimensional
    (r : Setoid W) [Fintype (FiniteQuotientType r)] :
    FiniteDimensional ℂ (ClassInvariantRestricted r) := by
  rw [← finiteClassDeltaRestricted_span_eq_invariant r]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem cofiniteTailDenseOn_primeObservableClassInvariantField_eq
    [Nonempty W] [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (r : Setoid W) [Fintype (FiniteQuotientType r)] (a : ℂ) :
    primeObservableSubspaceShiftField y (ClassInvariantRestricted r) a =
      primeFiniteQuotientShiftField y r a := by
  letI : FiniteDimensional ℂ (ClassInvariantRestricted r) :=
    classInvariantRestrictedFiniteDimensional r
  have hqpos : 0 < Fintype.card (FiniteQuotientType r) :=
    Fintype.card_pos_iff.mpr ((nonempty_quotient_iff r).mpr inferInstance)
  have hUpos : 0 < Module.finrank ℂ (ClassInvariantRestricted r) := by
    rw [classInvariantRestricted_finrank]
    exact hqpos
  letI : Nonempty (Fin (Module.finrank ℂ (ClassInvariantRestricted r))) :=
    Fin.pos_iff_nonempty.mp hUpos
  letI : Nonempty (Fin (FiniteQuotientRank r)) :=
    Fin.pos_iff_nonempty.mp hqpos
  rw [primeObservableSubspaceShiftField_eq_basis,
    primeFiniteQuotientShiftField_eq_tailDenseObservableShiftField]
  apply (cofiniteTailDenseOn_observableShiftField_eq_iff_span_eq
    y Set.univ hy
    (finiteSubmoduleObservable (ClassInvariantRestricted r))
    (finiteClassDeltaObservable r)
    (fun _ => continuous_of_discreteTopology)
    (fun _ => continuous_of_discreteTopology)
    (finiteSubmoduleObservable_restricted_linearIndependent
      (ClassInvariantRestricted r))
    (finiteClassDeltaRestricted_linearIndependent r) a).2
  rw [finiteSubmoduleObservable_restricted_span,
    finiteClassDeltaRestricted_span_eq_invariant]

/-- Interaction cohomology has exactly the finite-quotient interaction defect as its dimension. -/
theorem finiteQuotientInteractionCohomology_finrank
    (r s : Setoid W)
    [Fintype (FiniteQuotientType r)] [Fintype (FiniteQuotientType s)]
    [Fintype (FiniteQuotientType (r ⊓ s))] :
    Module.finrank ℂ (FiniteQuotientInteractionCohomology r s) =
      finiteQuotientInteractionDefect r s := by
  let Ur := ClassInvariantRestricted r
  let Us := ClassInvariantRestricted s
  let U := Ur ⊔ Us
  let V := ClassInvariantRestricted (r ⊓ s)
  let M := finiteQuotientInteractionMarginalSubmodule r s
  letI : FiniteDimensional ℂ Ur := classInvariantRestrictedFiniteDimensional r
  letI : FiniteDimensional ℂ Us := classInvariantRestrictedFiniteDimensional s
  letI : FiniteDimensional ℂ V :=
    classInvariantRestrictedFiniteDimensional (r ⊓ s)
  have hUV : U ≤ V := classInvariantRestricted_sup_le_infSetoid r s
  have hMdim : Module.finrank ℂ M = Module.finrank ℂ U := by
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hUV)
  have hquot := (M.finrank_quotient_add_finrank)
  rw [hMdim] at hquot
  unfold finiteQuotientInteractionDefect
  change Module.finrank ℂ (V ⧸ M) = Module.finrank ℂ V - Module.finrank ℂ U
  dsimp only [V, U, M, Ur, Us] at hquot ⊢
  omega

noncomputable def finiteQuotientInteractionCohomologyEquivComplement
    (r s : Setoid W)
    (Q : Submodule ℂ (FullValueSubtype W → ℂ))
    (hQV : Q ≤ ClassInvariantRestricted (r ⊓ s))
    (hUQ : Disjoint
      (ClassInvariantRestricted r ⊔ ClassInvariantRestricted s) Q)
    (hsup : (ClassInvariantRestricted r ⊔ ClassInvariantRestricted s) ⊔ Q =
      ClassInvariantRestricted (r ⊓ s)) :
    FiniteQuotientInteractionCohomology r s ≃ₗ[ℂ] Q := by
  let U := ClassInvariantRestricted r ⊔ ClassInvariantRestricted s
  let V := ClassInvariantRestricted (r ⊓ s)
  let M := finiteQuotientInteractionMarginalSubmodule r s
  let QV : Submodule ℂ V := Q.comap V.subtype
  have hUV : U ≤ V := classInvariantRestricted_sup_le_infSetoid r s
  have hMQdisj : Disjoint M QV := by
    rw [Submodule.disjoint_def]
    intro x hxM hxQ
    have hxU : x.1 ∈ U := hxM
    have hxQambient : x.1 ∈ Q := hxQ
    have hxzero : x.1 = 0 :=
      (Submodule.disjoint_def.mp hUQ) x.1 hxU hxQambient
    exact Subtype.ext hxzero
  have hMQsup : M ⊔ QV = ⊤ := by
    apply top_unique
    intro x _
    have hxAmbient : x.1 ∈ U ⊔ Q := by
      rw [hsup]
      exact x.2
    obtain ⟨u, hu, q, hq, huq⟩ := Submodule.mem_sup.mp hxAmbient
    apply Submodule.mem_sup.mpr
    refine ⟨(⟨u, hUV hu⟩ : V), hu, (⟨q, hQV hq⟩ : V), hq, ?_⟩
    exact Subtype.ext huq
  let hcompl : IsCompl M QV :=
    ⟨hMQdisj, codisjoint_iff.mpr hMQsup⟩
  exact (M.quotientEquivOfIsCompl QV hcompl).trans
    (Submodule.comapSubtypeEquivOfLe hQV)

theorem cofiniteTailDenseOn_primeObservableSubspaceField_eq_iff
    [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (U V : Submodule ℂ (FullValueSubtype W → ℂ))
    [FiniteDimensional ℂ U] [FiniteDimensional ℂ V]
    (hUpos : 0 < Module.finrank ℂ U) (hVpos : 0 < Module.finrank ℂ V)
    (a : ℂ) :
    primeObservableSubspaceShiftField y U a =
        primeObservableSubspaceShiftField y V a ↔ U = V := by
  letI : Nonempty (Fin (Module.finrank ℂ U)) := Fin.pos_iff_nonempty.mp hUpos
  letI : Nonempty (Fin (Module.finrank ℂ V)) := Fin.pos_iff_nonempty.mp hVpos
  rw [primeObservableSubspaceShiftField_eq_basis,
    primeObservableSubspaceShiftField_eq_basis]
  rw [cofiniteTailDenseOn_observableShiftField_eq_iff_span_eq
    y Set.univ hy
    (finiteSubmoduleObservable U) (finiteSubmoduleObservable V)
    (fun _ => continuous_of_discreteTopology)
    (fun _ => continuous_of_discreteTopology)
    (finiteSubmoduleObservable_restricted_linearIndependent U)
    (finiteSubmoduleObservable_restricted_linearIndependent V) a]
  rw [finiteSubmoduleObservable_restricted_span,
    finiteSubmoduleObservable_restricted_span]

theorem cofiniteTailDenseOn_primeFiniteQuotientField_sup_eq_interactionField
    [Nonempty W] [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (r s : Setoid W)
    [Fintype (FiniteQuotientType r)] [Fintype (FiniteQuotientType s)] (a : ℂ) :
    primeFiniteQuotientShiftField y r a ⊔
        primeFiniteQuotientShiftField y s a =
      primeObservableSubspaceShiftField y
        (ClassInvariantRestricted r ⊔ ClassInvariantRestricted s) a := by
  rw [← cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy r a,
    ← cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy s a,
    primeObservableSubspaceShiftField_sup]

/-- Quotient joins become exact intersections of their embedded prime differential fields. -/
theorem cofiniteTailDenseOn_primeFiniteQuotientField_inf_eq_supSetoid
    [Nonempty W] [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (r s : Setoid W)
    [Fintype (FiniteQuotientType r)] [Fintype (FiniteQuotientType s)]
    [Fintype (FiniteQuotientType (r ⊔ s))] (a : ℂ) :
    primeFiniteQuotientShiftField y r a ⊓
        primeFiniteQuotientShiftField y s a =
      primeFiniteQuotientShiftField y (r ⊔ s) a := by
  let Ur := ClassInvariantRestricted r
  let Us := ClassInvariantRestricted s
  let A := ClassInvariantRestricted (r ⊔ s)
  letI : FiniteDimensional ℂ Ur := classInvariantRestrictedFiniteDimensional r
  letI : FiniteDimensional ℂ Us := classInvariantRestrictedFiniteDimensional s
  have hApos : 0 < Module.finrank ℂ (↥(Ur ⊓ Us)) := by
    rw [← classInvariantRestricted_supSetoid_eq_inf r s]
    rw [classInvariantRestricted_finrank]
    exact Fintype.card_pos_iff.mpr
      ((nonempty_quotient_iff (r ⊔ s)).mpr inferInstance)
  calc
    primeFiniteQuotientShiftField y r a ⊓
        primeFiniteQuotientShiftField y s a =
      primeObservableSubspaceShiftField y Ur a ⊓
        primeObservableSubspaceShiftField y Us a := by
          rw [cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy r a,
            cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy s a]
    _ = primeObservableSubspaceShiftField y (Ur ⊓ Us) a :=
      cofiniteTailDenseOn_primeObservableSubspaceShiftField_inf
        y hy Ur Us hApos a
    _ = primeObservableSubspaceShiftField y A a := by
      rw [← classInvariantRestricted_supSetoid_eq_inf r s]
    _ = primeFiniteQuotientShiftField y (r ⊔ s) a :=
      cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy (r ⊔ s) a

/-- The two marginal fields generate the full common-refinement field exactly when interaction
cohomology vanishes. -/
theorem cofiniteTailDenseOn_primeFiniteQuotientField_sup_eq_infSetoid_iff_defect_zero
    [Nonempty W] [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (r s : Setoid W)
    [Fintype (FiniteQuotientType r)] [Fintype (FiniteQuotientType s)]
    [Fintype (FiniteQuotientType (r ⊓ s))] (a : ℂ) :
    (primeFiniteQuotientShiftField y r a ⊔
        primeFiniteQuotientShiftField y s a =
      primeFiniteQuotientShiftField y (r ⊓ s) a) ↔
      finiteQuotientInteractionDefect r s = 0 := by
  let Ur := ClassInvariantRestricted r
  let Us := ClassInvariantRestricted s
  let U := Ur ⊔ Us
  let V := ClassInvariantRestricted (r ⊓ s)
  letI : FiniteDimensional ℂ Ur := classInvariantRestrictedFiniteDimensional r
  letI : FiniteDimensional ℂ Us := classInvariantRestrictedFiniteDimensional s
  letI : FiniteDimensional ℂ V :=
    classInvariantRestrictedFiniteDimensional (r ⊓ s)
  have hrpos : 0 < Module.finrank ℂ Ur := by
    rw [classInvariantRestricted_finrank]
    exact Fintype.card_pos_iff.mpr ((nonempty_quotient_iff r).mpr inferInstance)
  have hUpos : 0 < Module.finrank ℂ U := by
    have hle := Submodule.finrank_mono (show Ur ≤ U from le_sup_left)
    omega
  have hVpos : 0 < Module.finrank ℂ V := by
    rw [classInvariantRestricted_finrank]
    exact Fintype.card_pos_iff.mpr
      ((nonempty_quotient_iff (r ⊓ s)).mpr inferInstance)
  have hUV : U ≤ V := classInvariantRestricted_sup_le_infSetoid r s
  rw [cofiniteTailDenseOn_primeFiniteQuotientField_sup_eq_interactionField
    y hy r s a]
  rw [← cofiniteTailDenseOn_primeObservableClassInvariantField_eq
    y hy (r ⊓ s) a]
  rw [cofiniteTailDenseOn_primeObservableSubspaceField_eq_iff
    y hy U V hUpos hVpos a]
  constructor
  · intro hUVeq
    unfold finiteQuotientInteractionDefect
    change Module.finrank ℂ V - Module.finrank ℂ U = 0
    rw [hUVeq]
    exact Nat.sub_self _
  · intro hdef
    apply Submodule.eq_of_le_of_finrank_eq hUV
    unfold finiteQuotientInteractionDefect at hdef
    change Module.finrank ℂ V - Module.finrank ℂ U = 0 at hdef
    have hle := Submodule.finrank_mono hUV
    omega

/-- **Finite-quotient interaction-cohomology law.**  There is a complement representing the
canonical interaction cohomology whose basis is relatively differentially independent over the
two marginal fields and whose adjunction generates the full common-refinement field.  The basis
cardinality is exactly the Euler interaction defect. -/
theorem cofiniteTailDenseOn_exists_primeFiniteQuotientInteractionComplement
    [Nonempty W] [TopologicalSpace W] [DiscreteTopology W]
    (y : Nat.Primes → W) (hy : CofiniteTailDenseOn y Set.univ)
    (r s : Setoid W)
    [Fintype (FiniteQuotientType r)] [Fintype (FiniteQuotientType s)]
    [Fintype (FiniteQuotientType (r ⊓ s))] (a : ℂ) :
    ∃ Q : Submodule ℂ (FullValueSubtype W → ℂ),
      ∃ q : Fin (Module.finrank ℂ Q) → W → ℂ,
        Q ≤ ClassInvariantRestricted (r ⊓ s) ∧
        Disjoint (ClassInvariantRestricted r ⊔ ClassInvariantRestricted s) Q ∧
        (ClassInvariantRestricted r ⊔ ClassInvariantRestricted s) ⊔ Q =
          ClassInvariantRestricted (r ⊓ s) ∧
        Module.finrank ℂ Q = finiteQuotientInteractionDefect r s ∧
        Nonempty (FiniteQuotientInteractionCohomology r s ≃ₗ[ℂ] Q) ∧
        LinearIndependent ℂ
          (fun j => fun w : FullValueSubtype W => q j w.1) ∧
        Submodule.span ℂ
          (Set.range (fun j => fun w : FullValueSubtype W => q j w.1)) = Q ∧
        GaloisForLFunctions.DifferentialIndependent
          (↥(primeFiniteQuotientShiftField y r a ⊔
            primeFiniteQuotientShiftField y s a))
          (fun j => tailDenseObservableShiftCarrier y (q j) a) ∧
        (primeFiniteQuotientShiftField y r a ⊔
            primeFiniteQuotientShiftField y s a) ⊔
            tailDenseObservableShiftField y q a =
          primeFiniteQuotientShiftField y (r ⊓ s) a := by
  let Ur := ClassInvariantRestricted r
  let Us := ClassInvariantRestricted s
  let U := Ur ⊔ Us
  let V := ClassInvariantRestricted (r ⊓ s)
  letI : FiniteDimensional ℂ Ur := classInvariantRestrictedFiniteDimensional r
  letI : FiniteDimensional ℂ Us := classInvariantRestrictedFiniteDimensional s
  letI : FiniteDimensional ℂ V :=
    classInvariantRestrictedFiniteDimensional (r ⊓ s)
  have hrpos : 0 < Module.finrank ℂ Ur := by
    rw [classInvariantRestricted_finrank]
    exact Fintype.card_pos_iff.mpr ((nonempty_quotient_iff r).mpr inferInstance)
  have hUpos : 0 < Module.finrank ℂ U := by
    have hle := Submodule.finrank_mono (show Ur ≤ U from le_sup_left)
    omega
  have hUV : U ≤ V := classInvariantRestricted_sup_le_infSetoid r s
  obtain ⟨Q, hQV, hUQ, hUQsup⟩ := exists_submodule_complement_of_le U V hUV
  letI : FiniteDimensional ℂ Q := Submodule.finiteDimensional_of_le hQV
  let q : Fin (Module.finrank ℂ Q) → W → ℂ := finiteSubmoduleObservable Q
  have hfield :
      primeFiniteQuotientShiftField y r a ⊔
          primeFiniteQuotientShiftField y s a =
        primeObservableSubspaceShiftField y U a :=
    cofiniteTailDenseOn_primeFiniteQuotientField_sup_eq_interactionField
      y hy r s a
  have hQfield :
      primeObservableSubspaceShiftField y Q a =
        tailDenseObservableShiftField y q a :=
    primeObservableSubspaceShiftField_eq_basis y Q a
  refine ⟨Q, q, hQV, hUQ, hUQsup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      Module.finrank ℂ Q = Module.finrank ℂ V - Module.finrank ℂ U :=
        complement_finrank_eq_sub U Q V hUQ hUQsup
      _ = finiteQuotientInteractionDefect r s := rfl
  · exact ⟨finiteQuotientInteractionCohomologyEquivComplement
      r s Q hQV hUQ hUQsup⟩
  · exact finiteSubmoduleObservable_restricted_linearIndependent Q
  · exact finiteSubmoduleObservable_restricted_span Q
  · have hDI := cofiniteTailDenseOn_complementObservable_differentialIndependent
      y hy U Q hUpos hUQ a
    rw [← hfield] at hDI
    exact hDI
  · calc
      (primeFiniteQuotientShiftField y r a ⊔
          primeFiniteQuotientShiftField y s a) ⊔
          tailDenseObservableShiftField y q a =
        primeObservableSubspaceShiftField y U a ⊔
          primeObservableSubspaceShiftField y Q a := by rw [hfield, hQfield]
      _ = primeObservableSubspaceShiftField y (U ⊔ Q) a :=
        (primeObservableSubspaceShiftField_sup y U Q a).symm
      _ = primeObservableSubspaceShiftField y V a := by rw [hUQsup]
      _ = primeFiniteQuotientShiftField y (r ⊓ s) a :=
        cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy (r ⊓ s) a

end

end GaloisForLFunctions.HTGeometry
