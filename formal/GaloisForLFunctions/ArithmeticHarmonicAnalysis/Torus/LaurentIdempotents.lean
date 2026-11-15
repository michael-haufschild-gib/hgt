import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.LaurentNilpotence
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.Abel

/-!
# Laurent polynomials have exactly the coefficient-ring idempotents

Reduce an idempotent modulo each prime of the coefficient ring. The Laurent
ring over that domain has only the idempotents `0` and `1`, so every nonzero
exponent coefficient of the original idempotent is nilpotent. The whole
nonconstant tail is therefore nilpotent.

Augmentation sends all Laurent monomials to `1`. Subtracting its constant
image from the original idempotent gives a nilpotent difference of two
idempotents, hence zero. Thus every idempotent is constant, without any
reducedness assumption on the coefficient ring or finiteness assumption on
the coordinate index.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {A ι : Type*} [CommRing A]

/-- Evaluation with every Laurent variable equal to `1`. -/
def laurentAugmentation : AddMonoidAlgebra A (ι → ℤ) →ₐ[A] A :=
  AddMonoidAlgebra.lift A A (ι → ℤ) 1

@[simp] theorem laurentAugmentation_single (q : ι → ℤ) (a : A) :
    laurentAugmentation (AddMonoidAlgebra.single q a) = a := by
  simp [laurentAugmentation]

/-- Prime reductions make every nonconstant idempotent coefficient nilpotent. -/
theorem laurent_idempotent_nonzero_coeff_nilpotent (f : AddMonoidAlgebra A (ι → ℤ))
    (hf : IsIdempotentElem f) (q : ι → ℤ) (hq : q ≠ 0) : IsNilpotent (f.coeff q) := by
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  letI := hJ
  let F := AddMonoidAlgebra.mapRingHom (ι → ℤ) (Ideal.Quotient.mk J)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hf.map F) with hz | ho
  · have he := congrArg (fun p : AddMonoidAlgebra (A ⧸ J) (ι → ℤ) => p.coeff q) hz
    simpa [F] using he
  · have he := congrArg (fun p : AddMonoidAlgebra (A ⧸ J) (ι → ℤ) => p.coeff q) ho
    simpa [F, AddMonoidAlgebra.one_def, hq, Ne.symm hq] using he

/-- The finite sum of the nonconstant terms of an idempotent is nilpotent. -/
theorem laurent_idempotent_tail_nilpotent (f : AddMonoidAlgebra A (ι → ℤ))
    (hf : IsIdempotentElem f) :
    IsNilpotent (f - AddMonoidAlgebra.single 0 (f.coeff 0)) := by
  classical
  apply (laurent_isNilpotent_iff _).mpr
  intro q
  by_cases hq : q = 0
  · subst q
    simp
  · simpa [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_single, hq, Ne.symm hq] using
      laurent_idempotent_nonzero_coeff_nilpotent f hf q hq

/-- Nilpotent rigidity of idempotents identifies an idempotent with its constant augmentation. -/
theorem laurent_idempotent_eq_augmentation (f : AddMonoidAlgebra A (ι → ℤ))
    (hf : IsIdempotentElem f) :
    f = AddMonoidAlgebra.single 0 (laurentAugmentation f) := by
  let c : A →+* AddMonoidAlgebra A (ι → ℤ) := AddMonoidAlgebra.singleZeroRingHom
  have hc (a : A) : laurentAugmentation (c a) = a := by
    change laurentAugmentation (AddMonoidAlgebra.single 0 a) = a
    exact laurentAugmentation_single 0 a
  have hn := laurent_idempotent_tail_nilpotent f hf
  change IsNilpotent (f - c (f.coeff 0)) at hn
  have hd := (Commute.all _ _).isNilpotent_sub hn ((hn.map laurentAugmentation).map c)
  have he : (f - c (f.coeff 0)) - c (laurentAugmentation (f - c (f.coeff 0))) =
      f - c (laurentAugmentation f) := by
    rw [map_sub, hc, map_sub]
    abel
  exact eq_of_isNilpotent_sub_of_isIdempotentElem hf ((hf.map laurentAugmentation).map c) (he ▸ hd)

/-- A Laurent idempotent has no nonconstant terms, even over a nonreduced coefficient ring. -/
theorem laurent_idempotent_eq_constantCoeff (f : AddMonoidAlgebra A (ι → ℤ))
    (hf : IsIdempotentElem f) : f = AddMonoidAlgebra.single 0 (f.coeff 0) := by
  have he := laurent_idempotent_eq_augmentation f hf
  have hc := congrArg (fun g : AddMonoidAlgebra A (ι → ℤ) => g.coeff 0) he
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
  rw [hc]
  exact he

/-- The complete classification of Laurent idempotents over an arbitrary commutative ring. -/
theorem laurent_isIdempotent_iff (f : AddMonoidAlgebra A (ι → ℤ)) :
    IsIdempotentElem f ↔ ∃ a : A, IsIdempotentElem a ∧ f = AddMonoidAlgebra.single 0 a := by
  constructor
  · intro hf
    exact ⟨laurentAugmentation f, hf.map laurentAugmentation, laurent_idempotent_eq_augmentation f hf⟩
  · rintro ⟨a, ha, rfl⟩
    exact ha.map (AddMonoidAlgebra.singleZeroRingHom : A →+* AddMonoidAlgebra A (ι → ℤ))

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.laurent_idempotent_eq_constantCoeff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.laurent_isIdempotent_iff
