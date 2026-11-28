import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands.Edges
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Triple

/-! # Every band of at least three distinct prime logarithms detects signed scale -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands

open Finset Real

private theorem third_index {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  by_contra! hall
  have cover : (univ : Finset (Fin n)) ⊆ {i,j} := by
    intro a _
    by_cases ha : a=i
    · simp [ha]
    · simp [hall a ha]
  have hcard := card_le_card cover
  have upper := card_insert_le i ({j} : Finset (Fin n))
  simp only [card_univ,Fintype.card_fin,card_singleton] at hcard upper
  omega

/-- An index away from the two endpoints has coefficient −2 in the
integer relation that a zero reading would impose on the prime logarithms. -/
theorem prime_edge_ne_zero {n : ℕ} [NeZero n] (hn : 3 ≤ n) (P : Fin n ↪ Nat.Primes) :
    edge (sample P energy) ≠ 0 := by
  let x := sample P energy
  have ind : LinearIndependent ℤ x :=
    GaloisForLFunctions.logPrime_linearIndependent_int.comp P P.injective
  obtain ⟨i,j,lo,hi⟩ := extrema x
  obtain ⟨k,ki,kj⟩ := third_index hn i j
  let d (t a : Fin n) : ℤ := if t=a then n else 0
  have mass (t : Fin n) : (∑ a, d t a • x a) = (n:ℤ) • x t := by
    rw [sum_eq_single t]
    · simp [d]
    · intro b _ hb
      simp [d,Ne.symm hb]
    · simp
  let w (a : Fin n) : ℤ := d i a + d j a - 2
  intro zero
  change edge x=0 at zero
  rw [edge_at x i j lo hi] at zero
  have relation : ∑ a, w a • x a = 0 := by
    simp only [w,sub_smul,add_smul,sum_sub_distrib,sum_add_distrib,mass]
    simp only [zsmul_eq_mul,Int.cast_natCast,Int.cast_ofNat,←Finset.mul_sum,←mul_add]
    exact zero
  have missing := linearIndependent_iff'.mp ind univ w relation k (mem_univ k)
  simp [w,d,Ne.symm ki,Ne.symm kj] at missing

#print axioms prime_edge_ne_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands
