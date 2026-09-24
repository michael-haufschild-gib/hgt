import GaloisForLFunctions.RHTower.Sieve.RootsOfUnityFrequencies
import GaloisForLFunctions.RHTower.Sieve.ConcreteRoot

/-!
# Exact finite Fourier coefficient of the centered residue sawtooth

A weighted geometric telescoping identity computes each nonzero additive
Fourier coefficient. This is the local algebraic bridge needed to express the
signed residue source in the reduced Farey basis without dropping signs.
-/

noncomputable section
open Finset

namespace RHTower.Sieve

theorem weighted_geom_telescoping (z : ℂ) (n : ℕ) :
    (1 - z) * (∑ r ∈ Finset.range n, (r : ℂ) * z ^ r) +
        (n : ℂ) * z ^ n =
      (∑ r ∈ Finset.range n, z ^ r) - 1 + z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    push_cast
    rw [pow_succ]
    linear_combination ih

theorem weighted_geom_root (z : ℂ) (n : ℕ)
    (hpow : z ^ n = 1) (hne : z ≠ 1) :
    (∑ r ∈ Finset.range n, (r : ℂ) * z ^ r) =
      -(n : ℂ) / (1 - z) := by
  have htel := weighted_geom_telescoping z n
  rw [sum_range_pow_eq_zero hpow hne, hpow] at htel
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  apply (eq_div_iff hden).2
  linear_combination htel

/-- The nonzero Fourier coefficient of the centered normalized residue sawtooth. -/
theorem centered_residue_fourier_coeff (d : ℕ) (hd : 0 < d) (z : ℂ)
    (hpow : z ^ d = 1) (hne : z ≠ 1) :
    (1 / (d : ℂ)) *
      (∑ r ∈ Finset.range d,
        ((r : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ))) * z ^ r) =
      -1 / ((d : ℂ) * (1 - z)) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hG := sum_range_pow_eq_zero hpow hne
  have hS := weighted_geom_root z d hpow hne
  have hsplit :
      (∑ r ∈ Finset.range d,
        ((r : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ))) * z ^ r) =
      (∑ r ∈ Finset.range d, (r : ℂ) * z ^ r) / (d : ℂ) -
        (((d : ℂ) - 1) / (2 * (d : ℂ))) *
          ∑ r ∈ Finset.range d, z ^ r := by
    calc
      _ = ∑ r ∈ Finset.range d,
          (((r : ℂ) * z ^ r) / (d : ℂ) -
            (((d : ℂ) - 1) / (2 * (d : ℂ))) * z ^ r) := by
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  rw [hsplit, hG, mul_zero, sub_zero, hS]
  have hz : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  field_simp

/-- The exact coefficient at a nonzero standard root harmonic. -/
theorem centered_residue_fourier_root (d t : ℕ) (hd : 0 < d)
    (ht0 : 0 < t) (htd : t < d) :
    (1 / (d : ℂ)) *
      (∑ r ∈ Finset.range d,
        ((r : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ))) *
          ((rootOfUnity d) ^ t) ^ r) =
      -1 / ((d : ℂ) * (1 - (rootOfUnity d) ^ t)) := by
  have hprim := isPrimitiveRoot_rootOfUnity hd.ne'
  have hpow : ((rootOfUnity d) ^ t) ^ d = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hne : (rootOfUnity d) ^ t ≠ 1 := by
    intro h
    have hdvd := (hprim.pow_eq_one_iff_dvd t).mp h
    have hle := Nat.le_of_dvd ht0 hdvd
    omega
  exact centered_residue_fourier_coeff d hd ((rootOfUnity d) ^ t) hpow hne

end RHTower.Sieve
