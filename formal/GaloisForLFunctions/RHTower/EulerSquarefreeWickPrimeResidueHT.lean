import GaloisForLFunctions.RHTower.EulerSquarefreeWickInteractionCohomology
import GaloisForLFunctions.HTGeometry.CoprimePrimeResidueInteraction

/-!
# Prime-residue hypertranscendence of the Euler--Wick interaction

The normalized raw four-factor Euler packet has Wick defect `-2`.  Its two-leg coefficient-gauge
orbit therefore supplies a nonzero canonical checkerboard, not an existentially chosen complement
vector.  Actual primes, observed simultaneously modulo three and modulo four, visit every cell of
the two-by-two gauge square beyond every finite cutoff.

The resulting prime-supported Euler checkerboard is relatively differentially independent over
the two separate residue-marginal fields.  Its one-dimensional observable submodule generates the
entire joint residue field after adjoining the marginals.  Thus marginal or grade-one field
completion cannot erase this literal mixed Euler direction.
-/

namespace GaloisForLFunctions.RHTower

open Set
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical normalized four-factor squarefree Euler packet. -/
def eulerSquarefreeWickNormalizedPacket : Fin 4 → ℂ := fun _ => 1

theorem eulerSquarefreeWickNormalizedDefect :
    eulerSquarefreeWickFourDefect eulerSquarefreeWickNormalizedPacket = -2 := by
  rw [eulerSquarefreeWickFourDefect_eq]
  norm_num [eulerSquarefreeWickNormalizedPacket]

theorem eulerSquarefreeWickNormalizedInteraction_ne_zero :
    eulerSquarefreeWickAnchoredInteractionObservable
      eulerSquarefreeWickNormalizedPacket ≠ 0 := by
  intro hzero
  have hdefect :=
    (eulerSquarefreeWickAnchoredInteractionObservable_zero_iff _).mp hzero
  rw [eulerSquarefreeWickNormalizedDefect] at hdefect
  norm_num at hdefect

/-- Units modulo three, enumerated by the two sign-gauge values. -/
noncomputable def zmodThreeUnitsEquivFinTwo : (ZMod 3)ˣ ≃ Fin 2 :=
  (Fintype.equivFin (ZMod 3)ˣ).trans (finCongr (by
    rw [ZMod.card_units_eq_totient]
    simpa using Nat.totient_prime (p := 3) (by norm_num)))

/-- Units modulo four, enumerated by the two sign-gauge values. -/
noncomputable def zmodFourUnitsEquivFinTwo : (ZMod 4)ˣ ≃ Fin 2 :=
  (Fintype.equivFin (ZMod 4)ˣ).trans (finCongr (by
    rw [ZMod.card_units_eq_totient]
    simpa using Nat.totient_prime_pow (p := 2) (n := 2)
      Nat.prime_two (by norm_num)))

/-- Actual primes observed through the coprime mod-three/mod-four residue gauges. -/
noncomputable def finTwoCoprimePrimeResidueProfile :
    Nat.Primes → Fin 2 × Fin 2 :=
  (Equiv.prodCongr zmodThreeUnitsEquivFinTwo zmodFourUnitsEquivFinTwo) ∘
    coprimePrimeUnitResidueProfile 3 4 (by norm_num)

/-- Every two-gauge cell recurs beyond every finite prime cutoff. -/
theorem cofiniteTailDenseOn_finTwoCoprimePrimeResidueProfile :
    CofiniteTailDenseOn finTwoCoprimePrimeResidueProfile Set.univ := by
  let e := Equiv.prodCongr zmodThreeUnitsEquivFinTwo zmodFourUnitsEquivFinTwo
  have ht := cofiniteTailDenseOn_comp_continuous
    (coprimePrimeUnitResidueProfile 3 4 (by norm_num)) Set.univ
    (cofiniteTailDenseOn_coprimePrimeUnitResidueProfile 3 4 (by norm_num))
    e continuous_of_discreteTopology
  have he : e '' Set.univ = Set.univ := by
    exact Set.image_univ_of_surjective e.surjective
  rw [he] at ht
  simpa [finTwoCoprimePrimeResidueProfile, e, Function.comp_def] using ht

/-- The normalized Euler checkerboard is the whole anchored interaction complement. -/
theorem span_eulerSquarefreeWickNormalizedInteraction_eq_anchored :
    ℂ ∙ eulerSquarefreeWickAnchoredInteractionObservable
        eulerSquarefreeWickNormalizedPacket =
      productAnchoredInteractionSubmodule (Fin 2) (Fin 2) := by
  let r := productFstSetoid (Fin 2) (Fin 2)
  let s := productSndSetoid (Fin 2) (Fin 2)
  let U := productMarginalObservableSubmodule (Fin 2) (Fin 2)
  let V := ClassInvariantRestricted (r ⊓ s)
  let Q := productAnchoredInteractionSubmodule (Fin 2) (Fin 2)
  have hcompl := productAnchoredInteractionSubmodule_isCompl (Fin 2) (Fin 2)
  have hQV : Q ≤ V := by
    dsimp only [Q, V, r, s]
    rw [← hcompl.2]
    exact le_sup_right
  letI : FiniteDimensional ℂ V :=
    classInvariantRestrictedFiniteDimensional (r ⊓ s)
  letI : FiniteDimensional ℂ Q := Submodule.finiteDimensional_of_le hQV
  let e : FiniteQuotientInteractionCohomology r s ≃ₗ[ℂ] Q :=
    finiteQuotientInteractionCohomologyEquivComplement
      r s Q hQV hcompl.1 hcompl.2
  have hQrank : Module.finrank ℂ Q = 1 := by
    rw [← LinearEquiv.finrank_eq e]
    exact finTwoProductInteractionCohomology_finrank
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (eulerSquarefreeWickAnchoredInteractionObservable_mem _)
  · rw [finrank_span_singleton
      eulerSquarefreeWickNormalizedInteraction_ne_zero, hQrank]

/-- The literal normalized Euler checkerboard is relatively differentially independent over the
two separate residue-marginal fields. -/
theorem finTwoPrimeResidue_normalizedEulerWick_relativeDifferentialIndependent
    (shift : ℂ) :
    GaloisForLFunctions.DifferentialIndependent
      (↥(primeFiniteQuotientShiftField
            finTwoCoprimePrimeResidueProfile
            (productFstSetoid (Fin 2) (Fin 2)) shift ⊔
          primeFiniteQuotientShiftField
            finTwoCoprimePrimeResidueProfile
            (productSndSetoid (Fin 2) (Fin 2)) shift))
      (fun _ : Fin 1 => tailDenseObservableShiftCarrier
        finTwoCoprimePrimeResidueProfile
        (fun w : Fin 2 × Fin 2 =>
          eulerSquarefreeWickAnchoredInteractionObservable
            eulerSquarefreeWickNormalizedPacket ⟨w, Set.mem_univ _⟩)
        shift) := by
  let W := Fin 2 × Fin 2
  let y : Nat.Primes → W := finTwoCoprimePrimeResidueProfile
  let r := productFstSetoid (Fin 2) (Fin 2)
  let s := productSndSetoid (Fin 2) (Fin 2)
  let Ur := ClassInvariantRestricted r
  let Us := ClassInvariantRestricted s
  let U := Ur ⊔ Us
  let Q := productAnchoredInteractionSubmodule (Fin 2) (Fin 2)
  let f : Fin (Module.finrank ℂ U) → W → ℂ := finiteSubmoduleObservable U
  let g : Fin 1 → W → ℂ := fun _ w =>
    eulerSquarefreeWickAnchoredInteractionObservable
      eulerSquarefreeWickNormalizedPacket ⟨w, Set.mem_univ _⟩
  letI : FiniteDimensional ℂ Ur := classInvariantRestrictedFiniteDimensional r
  letI : FiniteDimensional ℂ Us := classInvariantRestrictedFiniteDimensional s
  have hUpos : 0 < Module.finrank ℂ U := by
    have hrpos : 0 < Module.finrank ℂ Ur := by
      rw [classInvariantRestricted_finrank]
      exact Fintype.card_pos_iff.mpr ((nonempty_quotient_iff r).mpr inferInstance)
    have hle := Submodule.finrank_mono (show Ur ≤ U from le_sup_left)
    omega
  letI : Nonempty (Fin (Module.finrank ℂ U)) := Fin.pos_iff_nonempty.mp hUpos
  have hf : LinearIndependent ℂ
      (fun j => fun w : FullValueSubtype W => f j w.1) :=
    finiteSubmoduleObservable_restricted_linearIndependent U
  have hg : LinearIndependent ℂ
      (fun j => fun w : FullValueSubtype W => g j w.1) := by
    apply linearIndependent_unique_iff.mpr
    intro hzero
    apply eulerSquarefreeWickNormalizedInteraction_ne_zero
    funext w
    simpa [g] using congrFun hzero w
  have hspanG : Submodule.span ℂ
      (Set.range (fun j => fun w : FullValueSubtype W => g j w.1)) = Q := by
    rw [Set.range_unique]
    change ℂ ∙ eulerSquarefreeWickAnchoredInteractionObservable
      eulerSquarefreeWickNormalizedPacket = Q
    exact span_eulerSquarefreeWickNormalizedInteraction_eq_anchored
  have hlinear : LinearIndependent ℂ
      (fun q => fun w : FullValueSubtype W => Sum.elim f g q w.1) := by
    have hsum := hf.sum_type hg (by
      rw [finiteSubmoduleObservable_restricted_span, hspanG]
      exact (productAnchoredInteractionSubmodule_isCompl (Fin 2) (Fin 2)).1)
    have heq :
        (fun q => fun w : FullValueSubtype W => Sum.elim f g q w.1) =
          Sum.elim
            (fun j => fun w : FullValueSubtype W => f j w.1)
            (fun j => fun w : FullValueSubtype W => g j w.1) := by
      funext q w
      rcases q with j | k <;> rfl
    rw [heq]
    exact hsum
  have hDI := cofiniteTailDenseOn_observableShiftCarrier_differentialIndependent
    y Set.univ cofiniteTailDenseOn_finTwoCoprimePrimeResidueProfile
    (Sum.elim f g) (fun _ => continuous_of_discreteTopology) hlinear shift
  let cf : Fin (Module.finrank ℂ U) →
      arithmeticFunctionRationalCoordinateField := fun j =>
    tailDenseObservableShiftCarrier y (f j) shift
  let cg : Fin 1 → arithmeticFunctionRationalCoordinateField := fun j =>
    tailDenseObservableShiftCarrier y (g j) shift
  have hsum : GaloisForLFunctions.DifferentialIndependent
      finitePrimeRationalCoefficientField (Sum.elim cf cg) := by
    have hfun :
        (fun q => tailDenseObservableShiftCarrier y (Sum.elim f g q) shift) =
          Sum.elim cf cg := by
      funext q
      rcases q with j | k <;> rfl
    rw [hfun] at hDI
    exact hDI
  have hrel :=
    GaloisForLFunctions.differentialIndependent_sum_right_over_left_differentialAdjoin
      cf cg hsum
  change GaloisForLFunctions.DifferentialIndependent
    (tailDenseObservableShiftField y (finiteSubmoduleObservable U) shift) cg at hrel
  rw [← primeObservableSubspaceShiftField_eq_basis] at hrel
  have hfield := cofiniteTailDenseOn_primeFiniteQuotientField_sup_eq_interactionField
    y cofiniteTailDenseOn_finTwoCoprimePrimeResidueProfile r s shift
  rw [hfield]
  exact hrel

/-- Adjoining the normalized Euler interaction submodule to the two marginal fields generates the
entire joint residue-observable field. -/
theorem finTwoPrimeResidue_normalizedEulerWick_generates_jointField
    (shift : ℂ) :
    (primeFiniteQuotientShiftField
          finTwoCoprimePrimeResidueProfile
          (productFstSetoid (Fin 2) (Fin 2)) shift ⊔
        primeFiniteQuotientShiftField
          finTwoCoprimePrimeResidueProfile
          (productSndSetoid (Fin 2) (Fin 2)) shift) ⊔
      primeObservableSubspaceShiftField finTwoCoprimePrimeResidueProfile
        (ℂ ∙ eulerSquarefreeWickAnchoredInteractionObservable
          eulerSquarefreeWickNormalizedPacket) shift =
    primeFiniteQuotientShiftField finTwoCoprimePrimeResidueProfile
      (productFstSetoid (Fin 2) (Fin 2) ⊓
        productSndSetoid (Fin 2) (Fin 2)) shift := by
  let y := finTwoCoprimePrimeResidueProfile
  let r := productFstSetoid (Fin 2) (Fin 2)
  let s := productSndSetoid (Fin 2) (Fin 2)
  let U := productMarginalObservableSubmodule (Fin 2) (Fin 2)
  let Q := productAnchoredInteractionSubmodule (Fin 2) (Fin 2)
  let V := ClassInvariantRestricted (r ⊓ s)
  have hy := cofiniteTailDenseOn_finTwoCoprimePrimeResidueProfile
  have hfield := cofiniteTailDenseOn_primeFiniteQuotientField_sup_eq_interactionField
    y hy r s shift
  have hfield' :
      primeFiniteQuotientShiftField y r shift ⊔
          primeFiniteQuotientShiftField y s shift =
        primeObservableSubspaceShiftField y U shift := by
    simpa [U, r, s, productMarginalObservableSubmodule] using hfield
  calc
    (primeFiniteQuotientShiftField y r shift ⊔
        primeFiniteQuotientShiftField y s shift) ⊔
        primeObservableSubspaceShiftField y
          (ℂ ∙ eulerSquarefreeWickAnchoredInteractionObservable
            eulerSquarefreeWickNormalizedPacket) shift =
      primeObservableSubspaceShiftField y U shift ⊔
        primeObservableSubspaceShiftField y Q shift := by
          rw [hfield', span_eulerSquarefreeWickNormalizedInteraction_eq_anchored]
    _ = primeObservableSubspaceShiftField y (U ⊔ Q) shift :=
      (primeObservableSubspaceShiftField_sup y U Q shift).symm
    _ = primeObservableSubspaceShiftField y V shift := by
      rw [(productAnchoredInteractionSubmodule_isCompl (Fin 2) (Fin 2)).2]
    _ = primeFiniteQuotientShiftField y (r ⊓ s) shift :=
      cofiniteTailDenseOn_primeObservableClassInvariantField_eq y hy (r ⊓ s) shift

end

end GaloisForLFunctions.RHTower
