import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.FiniteEnergy
import GaloisForLFunctions.RHTower.SquarefreeExteriorHorizonLift

/-! # Counting occupied primes and measuring their energy on one configuration -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open _root_.RHTower Set

/-- Each occupied prime contributes one count and its own one-particle heat amplitude. -/
def partition (S : Finset Nat.Primes) (w u : ℂ) :=
  ∏ p : ↥S, (1+w*Complex.exp (u*(squarefreePrimeEnergy p.val:ℂ)))

/-- Joint moment of the occupation count and scaled energy at inverse temperature s. -/
def jointMoment (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (w z : ℂ) :=
  ∑ x : SquarefreeBitConfig S, (finiteSquarefreeBornWeight S s x:ℂ)*w^(squarefreeOccupationFinset x).card*
    Complex.exp (z*(packetEnergy S h x:ℂ))

theorem partition_trace (S : Finset Nat.Primes) (w u : ℂ) :
    partition S w u = ∑ x : SquarefreeBitConfig S,
      w^(squarefreeOccupationFinset x).card*Complex.exp (u*(finiteSquarefreeHamiltonian S x:ℂ)) := by
  classical
  let term (T : Finset ↥S) := w^T.card*Complex.exp (u*∑ p ∈ T,(squarefreePrimeEnergy p.val:ℂ))
  calc partition S w u = ∑ T : Finset ↥S, term T := by
         rw [partition,Finset.prod_one_add,Finset.powerset_univ]
         apply Finset.sum_congr rfl
         intro T _
         simp only [term,Finset.prod_mul_distrib,Finset.prod_const,← Complex.exp_sum,Finset.mul_sum]
       _ = ∑ x : SquarefreeBitConfig S, term (squarefreeOccupationEquiv S x) :=
         ((squarefreeOccupationEquiv S).sum_comp term).symm
       _ = _ := by
         apply Finset.sum_congr rfl
         intro x _
         change term (squarefreeOccupationFinset x) = _
         simp only [term,finiteSquarefreeHamiltonian_eq_sum_occupation,Complex.ofReal_sum]

/-- The count is marked in the numerator while the Born normalization uses the unmarked partition. -/
theorem jointMoment_eq (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (w z : ℂ) :
    jointMoment S s h w z = partition S w (z*(h.val:ℂ)-(s:ℂ))/(finiteSquarefreePartition S s:ℂ) := by
  rw [partition_trace,Finset.sum_div,jointMoment]
  apply Finset.sum_congr rfl
  intro x _
  let E := (finiteSquarefreeHamiltonian S x:ℂ)
  let W := w^(squarefreeOccupationFinset x).card
  rw [finiteSquarefreeBornWeight_eq,Complex.ofReal_div,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  change Complex.exp (-(s:ℂ)*E)/(finiteSquarefreePartition S s:ℂ)*W*
    Complex.exp (z*((h.val*finiteSquarefreeHamiltonian S x:ℝ):ℂ)) = _
  rw [Complex.ofReal_mul]
  change Complex.exp (-(s:ℂ)*E)/(finiteSquarefreePartition S s:ℂ)*W*Complex.exp (z*((h.val:ℂ)*E)) =
    W*Complex.exp ((z*(h.val:ℂ)-(s:ℂ))*E)/(finiteSquarefreePartition S s:ℂ)
  rw [show (z*(h.val:ℂ)-(s:ℂ))*E = -(s:ℂ)*E+z*((h.val:ℂ)*E) by ring,Complex.exp_add]
  ring

theorem unmarked (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) (z : ℂ) :
    jointMoment S (1+h.val) h 1 z = packetMoment S h z := by
  simp only [jointMoment,packetMoment,one_pow,mul_one]

/-- A real energy tilt changes only the inverse temperature of the marked count. -/
theorem real_tilt (S : Finset Nat.Primes) (s r : ℝ) (h : Ioi (0:ℝ)) (w : ℂ) :
    jointMoment S s h w (r:ℂ) = jointMoment S (s-r*h.val) h w 0 *
      ((finiteSquarefreePartition S (s-r*h.val)/finiteSquarefreePartition S s:ℝ):ℂ) := by
  rw [jointMoment_eq,jointMoment_eq,zero_mul,zero_sub,Complex.ofReal_sub,Complex.ofReal_mul,neg_sub,
    Complex.ofReal_div]
  field_simp [(Complex.ofReal_ne_zero.mpr (finiteSquarefreePartition_pos S (s-r*h.val)).ne'),
    (Complex.ofReal_ne_zero.mpr (finiteSquarefreePartition_pos S s).ne')]

#print axioms partition_trace
#print axioms jointMoment_eq
#print axioms unmarked
#print axioms real_tilt

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks
