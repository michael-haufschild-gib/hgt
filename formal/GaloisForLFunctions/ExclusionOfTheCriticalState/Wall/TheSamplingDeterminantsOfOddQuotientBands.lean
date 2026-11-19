import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Exact sampling determinants for quotient digits

The translation sign of a quotient changes for the first time at its
denominator. Sampling successive first changes yields integer determinants
independent of the sizes and common factors of the denominators.
-/

open Finset Matrix OrderDual
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
noncomputable section
open scoped Classical

/-- Odd quotient digits sampled at the ordered positive denominators d(i)+1. -/
def oddDigitSamples {k : ℕ} (d : Fin k ↪o ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j => if (d i+1)/(d j+1)%2=1 then 1 else 0

/-- Sampling at the denominators gives a unimodular integer matrix. -/
theorem det_oddDigitSamples {k : ℕ} (d : Fin k ↪o ℕ) : (oddDigitSamples d).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [oddDigitSamples,Nat.div_self]
  · intro i j hij
    have h : d i + 1 < d j + 1 := Nat.succ_lt_succ (d.strictMono (show i<j from hij))
    simp [oddDigitSamples,Nat.div_eq_of_lt h]

/-- The sampled integer matrix reads the actual arithmetic discrepancy when
its input vector consists of the ordinary prime excess coefficients. -/
theorem oddDigitSamples_prime_reading {k : ℕ} (d : Fin k ↪o ℕ) (i : Fin k) :
    oddQuotientPrimeExcess (univ.image (fun j => d j+1)) (d i+1) =
      ∑ j : Fin k, (oddDigitSamples d i j : ℝ)*ordinaryPrimeExcessCoeff (d j+1) := by
  rw [oddQuotientPrimeExcess,sum_image (fun x _ y _ h => d.injective (Nat.succ.inj h))]
  refine sum_congr rfl fun j _ => ?_
  simp only [oddDigitSamples]
  split_ifs <;> simp

/-- A sign reading at zero followed by readings at all but the largest
denominator. The sample count equals the number of unknown coefficients. -/
def quotientSignSamples {k : ℕ} (d : Fin (k+1) ↪o ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℤ :=
  fun i j => (-1)^((Fin.cases 0 (fun l => d l.castSucc+1) i)/(d j+1))

private def nextColumn (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℤ :=
  fun i => Fin.cases 0 (fun j => if i=j.castSucc then 1 else 0)

private theorem multiply_nextColumn {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℤ)
    (i : Fin (k+1)) :
    (A*nextColumn k) i 0=0 ∧ ∀ j : Fin k, (A*nextColumn k) i j.succ = A i j.castSucc := by
  constructor
  · simp [Matrix.mul_apply,nextColumn]
  · intro j
    simp [Matrix.mul_apply,nextColumn,mul_ite]

private theorem difference_det (k : ℕ) : ((1:Matrix (Fin (k+1)) (Fin (k+1)) ℤ)-nextColumn k).det=1 := by
  have hn (i j : Fin (k+1)) (h : j≤i) : nextColumn k i j=0 := by
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      have hne : i≠j.castSucc := by intro he; subst i; exact (Nat.not_succ_le_self j.val) h
      simp [nextColumn,hne]
  rw [Matrix.det_of_upperTriangular]
  · simp [Matrix.sub_apply,hn]
  · intro i j hij
    have h : j<i := hij
    simp [Matrix.sub_apply,Matrix.one_apply,h.ne',hn i j h.le]

/-- Consecutive column differences first appear on the diagonal, always as
two. Thus the centered sign readings have determinant 2^k on any k+1
distinct ordered denominators, without waiting for a common period. -/
theorem det_quotientSignSamples {k : ℕ} (d : Fin (k+1) ↪o ℕ) :
    (quotientSignSamples d).det = 2^k := by
  let A := quotientSignSamples d
  let B := A*(1-nextColumn k)
  have h0 (i : Fin (k+1)) : B i 0 = A i 0 := by
    simp [B,mul_sub,(multiply_nextColumn A i).1]
  have hs (i : Fin (k+1)) (j : Fin k) : B i j.succ = A i j.succ-A i j.castSucc := by
    simp [B,mul_sub,(multiply_nextColumn A i).2 j]
  have early (u v : Fin (k+1)) (h : u<v) : (d u+1)/(d v+1)=0 :=
    Nat.div_eq_of_lt (Nat.succ_lt_succ (d.strictMono h))
  have htri : B.BlockTriangular toDual := by
    intro i j hj
    have hij : i<j := hj
    induction j using Fin.cases with
    | zero => exact (Fin.not_lt_zero i hij).elim
    | succ j =>
      rw [hs]
      cases i using Fin.cases with
      | zero => simp [A,quotientSignSamples]
      | succ i =>
        have h₁ : i.castSucc < j.castSucc := by omega
        have h₂ : i.castSucc < j.succ := by omega
        simp [A,quotientSignSamples,early _ _ h₁,early _ _ h₂]
  have hd (j : Fin k) : B j.succ j.succ = 2 := by
    rw [hs]
    have hj : j.castSucc < j.succ := by omega
    simp [A,quotientSignSamples,early _ _ hj,Nat.div_self]
  have hfirst : B 0 0=1 := by rw [h0]; simp [A,quotientSignSamples]
  have he : B.det=2^k := by
    rw [Matrix.det_of_lowerTriangular B htri,Fin.prod_univ_succ,hfirst,one_mul]
    simp [hd]
  simpa only [B,Matrix.det_mul,difference_det,mul_one,A] using he

#print axioms det_oddDigitSamples
#print axioms oddDigitSamples_prime_reading
#print axioms det_quotientSignSamples
end
end GaloisForLFunctions.ExclusionOfTheCriticalState
