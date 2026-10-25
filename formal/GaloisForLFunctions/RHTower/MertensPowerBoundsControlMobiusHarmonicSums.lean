import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicTailIdentity
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate

/-!
Partial summation writes the finite Möbius harmonic sum as a successor boundary
term minus a strict Mertens tail. A Mertens power saving then transfers with the
same exponent and an explicit constant.
-/

open Finset Filter
open scoped BigOperators Topology
noncomputable section
namespace RHTower
set_option autoImplicit false

/-- The harmonic Möbius prefix is its successor boundary term minus the strict Mertens tail. -/
theorem deningerHarmonicPartial_eq_succ_boundary_sub_tail {N : ℕ} (hN : 1 ≤ N) :
    deningerHarmonicPartial N = Sieve.mertensM N / ((N : ℝ) + 1) -
      ∑' i : ℕ, Sieve.mertensM (i + (N + 1)) /
        (((i + (N + 1) : ℕ) : ℝ) * (((i + (N + 1) : ℕ) : ℝ) + 1)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpartial := Sieve.deningerHarmonicPartial_eq_mertens_boundary_add N
  have hsplit := deningerMertensHarmonic_summable.sum_add_tsum_nat_add (N + 1)
  rw [Sieve.tsum_mertensHarmonic_eq_zero, Finset.sum_range_succ] at hsplit
  have hb : Sieve.mertensM N / (N : ℝ) -
      Sieve.mertensM N / ((N : ℝ) * ((N : ℝ) + 1)) =
        Sieve.mertensM N / ((N : ℝ) + 1) := by
    field_simp [hN0.ne', (show (N : ℝ) + 1 ≠ 0 by positivity)]
    ring
  linear_combination hpartial + hsplit + hb

/-- A Mertens power saving transfers to the harmonic Möbius sum with the same exponent. -/
theorem abs_deningerHarmonicPartial_le_of_mertens_power {η C : ℝ}
    (hη : 0 < η) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n → |Sieve.mertensM n| ≤ C * (n : ℝ) ^ (1 - η))
    {N : ℕ} (hN : 1 ≤ N) :
    |deningerHarmonicPartial N| ≤ (C * (1 + 1 / η)) * (N : ℝ) ^ (-η) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcell (n : ℕ) (hn : 1 ≤ n) :
      |Sieve.mertensM n / ((n : ℝ) * ((n : ℝ) + 1))| ≤ C * (n : ℝ) ^ (-1 - η) := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_div, abs_of_pos (mul_pos hn0 (by positivity))]
    calc
      _ ≤ (C * (n : ℝ) ^ (1 - η)) / ((n : ℝ) * ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right (hM n hn) (by positivity)
      _ ≤ (C * (n : ℝ) ^ (1 - η)) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn0)
          (by nlinarith only [hn0])
      _ = _ := by
        rw [show -1 - η = (1 - η) - 2 by ring,
          Real.rpow_sub hn0 (1 - η) (2 : ℝ), Real.rpow_two]
        ring
  have hs : Summable (fun i : ℕ => Sieve.mertensM (i + (N + 1)) /
      (((i + (N + 1) : ℕ) : ℝ) * (((i + (N + 1) : ℕ) : ℝ) + 1))) :=
    (summable_nat_add_iff (N + 1)).mpr deningerMertensHarmonic_summable
  have htail : |∑' i : ℕ, Sieve.mertensM (i + (N + 1)) /
      (((i + (N + 1) : ℕ) : ℝ) * (((i + (N + 1) : ℕ) : ℝ) + 1))| ≤
        C * (N : ℝ) ^ (-η) / η := by
    have hnorm := norm_tsum_le_tsum_norm hs.norm
    simp only [Real.norm_eq_abs] at hnorm
    refine hnorm.trans (Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) (fun m => ?_))
    have hp : (∑ i ∈ range m, ((i + (N + 1) : ℕ) : ℝ) ^ (-1 - η)) ≤
        (N : ℝ) ^ (-η) / η := by
      simpa only [show -(1 + η) = -1 - η by ring,
        show 1 - (1 + η) = -η by ring, show (1 + η) - 1 = η by ring] using
        sum_range_add_rpow_neg_le (c := 1 + η) (by linarith only [hη]) hN m
    calc
      _ ≤ ∑ i ∈ range m, C * ((i + (N + 1) : ℕ) : ℝ) ^ (-1 - η) :=
        sum_le_sum fun i _ => hcell _ (by omega)
      _ = C * ∑ i ∈ range m, ((i + (N + 1) : ℕ) : ℝ) ^ (-1 - η) := (mul_sum _ _ _).symm
      _ ≤ C * ((N : ℝ) ^ (-η) / η) := mul_le_mul_of_nonneg_left hp hC
      _ = _ := by ring
  have hboundary : |Sieve.mertensM N / ((N : ℝ) + 1)| ≤ C * (N : ℝ) ^ (-η) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    calc
      _ ≤ C * (N : ℝ) ^ (1 - η) / ((N : ℝ) + 1) :=
        div_le_div_of_nonneg_right (hM N hN) (by positivity)
      _ ≤ C * (N : ℝ) ^ (1 - η) / N :=
        div_le_div_of_nonneg_left (by positivity) hN0 (by linarith)
      _ = _ := by
        rw [show 1 - η = -η + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
        field_simp [hN0.ne']
  rw [deningerHarmonicPartial_eq_succ_boundary_sub_tail hN]
  exact (abs_sub _ _).trans ((add_le_add hboundary htail).trans_eq (by ring))

#print axioms deningerHarmonicPartial_eq_succ_boundary_sub_tail
#print axioms abs_deningerHarmonicPartial_le_of_mertens_power
end RHTower
