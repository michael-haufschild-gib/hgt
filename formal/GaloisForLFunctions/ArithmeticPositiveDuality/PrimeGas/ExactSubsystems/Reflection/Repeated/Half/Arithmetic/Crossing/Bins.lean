import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Distinct primes in prescribed logarithmic bins -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing

open Real

private theorem in_bin (k : ℕ) :
    ∃ p : Nat.Primes, 2^k<p.val ∧ p.val≤2^(k+1) := by
  obtain ⟨p,hp,lo,hi⟩ := Nat.exists_prime_lt_and_le_two_mul (2^k) (pow_ne_zero _ (by omega : (2 : ℕ)≠0))
  exact ⟨⟨p,hp⟩,lo,by rwa [pow_succ,Nat.mul_comm]⟩

def binPrime (k : ℕ) := (in_bin k).choose

theorem bin_bounds (k : ℕ) : 2^k<(binPrime k).val ∧ (binPrime k).val≤2^(k+1) := (in_bin k).choose_spec

theorem bin_strict : StrictMono (fun k => (binPrime k).val) := by
  intro k l h
  exact (bin_bounds k).2.trans_lt ((pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by omega) h).trans_lt (bin_bounds l).1)

theorem log_bounds (k : ℕ) :
    (k : ℝ)*log 2 ≤ log ((binPrime k).val : ℝ) ∧ log ((binPrime k).val : ℝ) ≤ ((k : ℝ)+1)*log 2 := by
  have lower : (2 : ℝ)^k ≤ (binPrime k).val := by exact_mod_cast (bin_bounds k).1.le
  have upper : ((binPrime k).val : ℝ) ≤ 2^(k+1) := by exact_mod_cast (bin_bounds k).2
  have lo := log_le_log (pow_pos (show (0 : ℝ)<2 by positivity) k) lower
  have hi := log_le_log (Nat.cast_pos.mpr (binPrime k).property.pos) upper
  simpa only [log_pow,Nat.cast_add,Nat.cast_one] using And.intro lo hi

/-- Each target is rounded to an integer bin with a reserved residue modulo the
packet size. This keeps prime labels distinct even for identical target energies. -/
def binIndex {n : ℕ} (M : ℕ) (v : Fin n → ℝ) (i : Fin n) := M+(n*⌊v i⌋₊+i.val)

theorem index_injective {n : ℕ} (M : ℕ) (v : Fin n → ℝ) : Function.Injective (binIndex M v) := by
  intro i j eq
  have h := congrArg (· % n) (Nat.add_left_cancel (show M+(n*⌊v i⌋₊+i.val)=M+(n*⌊v j⌋₊+j.val) from eq))
  exact Fin.ext (by simpa only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using h)

def distinctPrimes {n : ℕ} (M : ℕ) (v : Fin n → ℝ) : Fin n ↪ Nat.Primes :=
  ⟨fun i => binPrime (binIndex M v i),fun _ _ he => index_injective M v (bin_strict.injective (congrArg Subtype.val he))⟩

theorem above_cutoff {n : ℕ} (M : ℕ) (v : Fin n → ℝ) (i : Fin n) : M<(distinctPrimes M v i).val := by
  have h : M ≤ binIndex M v i := Nat.le_add_right _ _
  have growth (j : ℕ) : j<2^j := by
    induction j with
    | zero => exact Nat.zero_lt_one
    | succ j ih => rw [pow_succ]; omega
  exact ((growth M).le.trans (pow_le_pow_right₀ (by omega : (1 : ℕ)≤2) h)).trans_lt (bin_bounds _).1

theorem index_bounds {n : ℕ} (M : ℕ) (v : Fin n → ℝ) (i : Fin n) (hi : 0≤v i) :
    (M : ℝ)+(n : ℝ)*(v i-1) ≤ (binIndex M v i : ℝ) ∧
    (binIndex M v i : ℝ)+1 ≤ (M : ℝ)+(n : ℝ)*(v i+1) := by
  have floorLo := Nat.floor_le hi
  have floorHi := Nat.lt_floor_add_one (v i)
  have pos : (0 : ℝ)≤n := Nat.cast_nonneg _
  have ii : (i.val : ℝ)+1≤n := by exact_mod_cast i.isLt
  have bottom := mul_le_mul_of_nonneg_left (show v i-1 ≤ (⌊v i⌋₊ : ℝ) by linarith only [floorHi]) pos
  have top := mul_le_mul_of_nonneg_left floorLo pos
  simp only [binIndex,Nat.cast_add,Nat.cast_mul]
  constructor
  · linarith only [bottom,(Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)]
  · linarith only [top,ii]

#print axioms distinctPrimes
#print axioms index_bounds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing
