import GaloisForLFunctions.RHProofLab.EulerProductArithmetic

/-!
# The raw squarefree Euler source is not a Wick matching source

At four distinct local indices, a squarefree Euler coefficient is one copy of the fourfold local
monomial.  If the two-index Euler coefficients are instead treated as dimer edge weights, the
three Wick pairings contribute three copies.  Their defect is therefore minus twice the fourfold
monomial and cannot vanish when all local coefficients are nonzero.

This closes the direct “raw Euler coefficient equals matching sum” proposal.  Its positive residue
is exact: a monomer--dimer route needs a new completed prime--Gamma pair kernel, or it must retain
the nonzero four-point interaction in a separately proved stable hypergraph construction.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.RHProofLab

/-! ### Positive successor: the raw even packet is a shared Rademacher packet -/

/-- Average a squarefree local monomial over one shared sign `ε ∈ {+1,-1}`.  This is the
finite algebraic moment functional of the rank-one Rademacher packet `Xᵢ = aᵢ ε`. -/
noncomputable def sharedRademacherMoment {ι : Type*} [DecidableEq ι]
    (a : ι → ℂ) (S : Finset ι) : ℂ :=
  (squarefreeMonomial a S + squarefreeMonomial (fun i => -a i) S) / 2

/-- Every even shared-Rademacher moment is exactly the corresponding squarefree Euler monomial. -/
theorem sharedRademacherMoment_eq_of_even_card {ι : Type*} [DecidableEq ι]
    (a : ι → ℂ) (S : Finset ι)
    (hS : Even S.card) :
    sharedRademacherMoment a S = squarefreeMonomial a S := by
  rw [sharedRademacherMoment, squarefreeMonomial, squarefreeMonomial,
    Finset.prod_neg, hS.neg_one_pow]
  ring

/-- Defect between one four-index squarefree Euler coefficient and the sum of the three Wick
pairings of its two-index coefficients. -/
noncomputable def eulerSquarefreeWickFourDefect (a : Fin 4 → ℂ) : ℂ :=
  squarefreeMonomial a {0, 1, 2, 3} -
    (squarefreeMonomial a {0, 1} * squarefreeMonomial a {2, 3} +
      squarefreeMonomial a {0, 2} * squarefreeMonomial a {1, 3} +
      squarefreeMonomial a {0, 3} * squarefreeMonomial a {1, 2})

/-- Raw Euler multiplicativity gives one copy of the fourfold monomial; the three Wick pairings
give three copies. -/
theorem eulerSquarefreeWickFourDefect_eq (a : Fin 4 → ℂ) :
    eulerSquarefreeWickFourDefect a = -2 * a 0 * a 1 * a 2 * a 3 := by
  simp [eulerSquarefreeWickFourDefect, squarefreeMonomial]
  ring

/-- The nonzero Euler Wick defect is not merely a failure of Gaussianity: it is exactly the
fourth joint cumulant of one shared Rademacher spin whose even moments reproduce the raw
squarefree packet. -/
theorem eulerSquarefreeWickFourDefect_eq_sharedRademacherCumulant (a : Fin 4 → ℂ) :
    eulerSquarefreeWickFourDefect a =
      sharedRademacherMoment a {0, 1, 2, 3} -
        (sharedRademacherMoment a {0, 1} * sharedRademacherMoment a {2, 3} +
          sharedRademacherMoment a {0, 2} * sharedRademacherMoment a {1, 3} +
          sharedRademacherMoment a {0, 3} * sharedRademacherMoment a {1, 2}) := by
  rw [sharedRademacherMoment_eq_of_even_card a {0, 1, 2, 3} (by decide),
    sharedRademacherMoment_eq_of_even_card a {0, 1} (by decide),
    sharedRademacherMoment_eq_of_even_card a {2, 3} (by decide),
    sharedRademacherMoment_eq_of_even_card a {0, 2} (by decide),
    sharedRademacherMoment_eq_of_even_card a {1, 3} (by decide),
    sharedRademacherMoment_eq_of_even_card a {0, 3} (by decide),
    sharedRademacherMoment_eq_of_even_card a {1, 2} (by decide)]
  rfl

/-- The ordered four-point free cumulant keeps the two noncrossing pair partitions and excludes
the crossing pairing `{0,2}{1,3}`. -/
noncomputable def sharedRademacherFreeFourCumulant (a : Fin 4 → ℂ) : ℂ :=
  sharedRademacherMoment a {0, 1, 2, 3} -
    (sharedRademacherMoment a {0, 1} * sharedRademacherMoment a {2, 3} +
      sharedRademacherMoment a {0, 3} * sharedRademacherMoment a {1, 2})

/-- Exact rank-four free-probability obstruction: the shared Rademacher Euler packet has negative
ordered fourth free cumulant `-a₀a₁a₂a₃`. -/
theorem sharedRademacherFreeFourCumulant_eq (a : Fin 4 → ℂ) :
    sharedRademacherFreeFourCumulant a = -a 0 * a 1 * a 2 * a 3 := by
  rw [sharedRademacherFreeFourCumulant,
    sharedRademacherMoment_eq_of_even_card a {0, 1, 2, 3} (by decide),
    sharedRademacherMoment_eq_of_even_card a {0, 1} (by decide),
    sharedRademacherMoment_eq_of_even_card a {2, 3} (by decide),
    sharedRademacherMoment_eq_of_even_card a {0, 3} (by decide),
    sharedRademacherMoment_eq_of_even_card a {1, 2} (by decide)]
  simp [squarefreeMonomial]
  ring

/-- The classical Wick defect is the fourth free cumulant minus the one crossing pair product. -/
theorem eulerSquarefreeWickFourDefect_eq_freeCumulant_sub_crossing (a : Fin 4 → ℂ) :
    eulerSquarefreeWickFourDefect a =
      sharedRademacherFreeFourCumulant a -
        sharedRademacherMoment a {0, 2} * sharedRademacherMoment a {1, 3} := by
  rw [eulerSquarefreeWickFourDefect_eq_sharedRademacherCumulant]
  rw [sharedRademacherFreeFourCumulant]
  ring

def eulerSquarefreeWickFourLaw (a : Fin 4 → ℂ) : Prop :=
  eulerSquarefreeWickFourDefect a = 0

/-- Exact classification: the raw four-point Wick law holds only on the union of the four
coordinate hyperplanes. -/
theorem eulerSquarefreeWickFourLaw_iff (a : Fin 4 → ℂ) :
    eulerSquarefreeWickFourLaw a ↔ a 0 = 0 ∨ a 1 = 0 ∨ a 2 = 0 ∨ a 3 = 0 := by
  rw [eulerSquarefreeWickFourLaw, eulerSquarefreeWickFourDefect_eq]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, neg_eq_zero, false_or]
  tauto

/-- In particular, a genuine four-local-factor Euler packet cannot satisfy the pairwise Wick law. -/
theorem not_eulerSquarefreeWickFourLaw_of_nonzero (a : Fin 4 → ℂ)
    (ha : ∀ i, a i ≠ 0) : ¬ eulerSquarefreeWickFourLaw a := by
  rw [eulerSquarefreeWickFourLaw_iff]
  simp [ha]

end GaloisForLFunctions.RHTower
