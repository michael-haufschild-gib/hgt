import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveCycleIndex
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerEvenWordIndex
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPairMultiplier

/-! Exact source words, lengths, expanding multipliers and trace terms in
primitive pair-cycle coordinates. -/

open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerWords MayerGaussCoding MayerPrimitiveCycles MayerCycleIndex MayerEvenWordIndex
open MayerPairMultiplier
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitWords

abbrev Orbit := PrimitiveCycle (ℕ × ℕ)

/-- Expanding multiplier of a primitive pair cycle. Rotation invariance makes
this independent of the chosen representative. -/
def multiplier (c : Orbit) : ℝ := pairMultiplier (representative c).val

theorem multiplier_gt_one (c : Orbit) : 1 < multiplier c :=
  pairMultiplier_gt_one _ (representative c).property.1

/-- Every actual nonempty even Gauss word has unique primitive-cycle data. -/
def sourceCycleEquiv : EvenWord ≃ CycleIndex (ℕ × ℕ) :=
  evenWordPairEquiv.trans wordCycleEquiv.symm

theorem toPairs_sourceCycleEquiv_symm (p : CycleIndex (ℕ × ℕ)) :
    toPairs (sourceCycleEquiv.symm p) = expand p := by
  exact congrArg Subtype.val (evenWordPairEquiv.apply_symm_apply (wordCycleEquiv p))

/-- Source half-length is primitive pair length times repetition. -/
theorem source_index_length (p : CycleIndex (ℕ × ℕ)) :
    (sourceCycleEquiv.symm p).1+1 = p.2.1.val * cycleLength p.1 := by
  calc
    _ = (toPairs (sourceCycleEquiv.symm p)).length := (toPairs_length _).symm
    _ = (expand p).length := congrArg List.length (toPairs_sourceCycleEquiv_symm p)
    _ = _ := expand_length p

/-- The literal fixed-point multiplier becomes the primitive multiplier to
the repetition exponent. -/
theorem source_multiplier (p : CycleIndex (ℕ × ℕ)) :
    wordMultiplier (2*(sourceCycleEquiv.symm p).1+1) (sourceCycleEquiv.symm p).2 =
      multiplier p.1 ^ p.2.1.val := by
  rw [wordMultiplier_eq_pairMultiplier]
  change pairMultiplier (toPairs (sourceCycleEquiv.symm p)) =
    pairMultiplier (representative p.1).val ^ p.2.1.val
  rw [toPairs_sourceCycleEquiv_symm,expand,pairMultiplier_wordPower _
    ((representative p.1).property.rotate p.2.2.val).1 p.2.1.pos,pairMultiplier_rotate]

/-- The actual trace-series term in primitive coordinates, before the finite
rotation count cancels the primitive length from its denominator. -/
theorem source_trace_term (w z : ℂ) (p : CycleIndex (ℕ × ℕ)) :
    z^(2*(sourceCycleEquiv.symm p).1+2) /
      (((sourceCycleEquiv.symm p).1+1 : ℕ) : ℂ) *
        wordTrace w (2*(sourceCycleEquiv.symm p).1+1) (sourceCycleEquiv.symm p).2 =
    z^(2*(p.2.1.val*cycleLength p.1)) /
      ((p.2.1.val : ℂ)*(cycleLength p.1 : ℂ)) *
        (((multiplier p.1 ^ p.2.1.val : ℝ) : ℂ)^(-w) /
          (1-1/((multiplier p.1 ^ p.2.1.val : ℝ) : ℂ)^2)) := by
  have hsign : (-1 : ℂ)^(2*(sourceCycleEquiv.symm p).1+1+1) = 1 := by
    rw [show 2*(sourceCycleEquiv.symm p).1+1+1 =
      2*((sourceCycleEquiv.symm p).1+1) by omega,pow_mul,neg_one_sq,one_pow]
  rw [wordTrace_eq_multiplier,hsign]
  simp only [source_multiplier,
    show 2*(sourceCycleEquiv.symm p).1+2 = 2*((sourceCycleEquiv.symm p).1+1) by omega,
    source_index_length,Nat.cast_mul]

#print axioms multiplier_gt_one
#print axioms sourceCycleEquiv
#print axioms toPairs_sourceCycleEquiv_symm
#print axioms source_index_length
#print axioms source_multiplier
#print axioms source_trace_term
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerOrbitWords
