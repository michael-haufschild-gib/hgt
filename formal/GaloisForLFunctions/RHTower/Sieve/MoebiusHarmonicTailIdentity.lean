import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusHarmonicZero

/-!
# Exact tail identity for the Möbius harmonic sum

The corpus proves both convergence of `sum mu(n)/n` and that its limit is
zero.  This file exposes the quantitative entry point hidden inside that
proof: every finite harmonic sum is one Mertens boundary term minus the
literal tail of an absolutely convergent Mertens series.

This identity lets any quantitative Mertens estimate transfer directly to
the logarithmically weighted Möbius sums used in Graham's Barban--Vehov
mean-square theorem.
-/

noncomputable section

namespace RHTower.Sieve

open ArithmeticFunction Filter Topology

/-- Finite Abel summation for the Möbius harmonic partial sum. -/
theorem deningerHarmonicPartial_eq_mertens_boundary_add (N : ℕ) :
    RHTower.deningerHarmonicPartial N =
      mertensM N / (N : ℝ) +
        ∑ i ∈ Finset.range N,
          mertensM i / ((i : ℝ) * ((i : ℝ) + 1)) := by
  let F : ℕ → ℝ := fun i => 1 / (i : ℝ)
  let G : ℕ → ℝ := fun i => ((moebius i : ℤ) : ℝ)
  have hMsum : ∀ i : ℕ,
      (∑ j ∈ Finset.range (i + 1), G j) = mertensM i := fun i => rfl
  have hbp := Finset.sum_range_by_parts F G (N + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hbp
  rw [hMsum N] at hbp
  have hinner : ∀ i ∈ Finset.range N,
      (F (i + 1) - F i) * (∑ j ∈ Finset.range (i + 1), G j) =
        -(mertensM i / ((i : ℝ) * ((i : ℝ) + 1))) := by
    intro i hi
    rw [hMsum i]
    dsimp only [F]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · have hz : mertensM 0 = 0 := by
        rw [mertensM]
        simp
      rw [hz]
      simp
    · have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hipos
      have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
      have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
        push_cast
        ring
      rw [hcast]
      field_simp
      ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_neg_distrib] at hbp
  have hlhs : RHTower.deningerHarmonicPartial N =
      ∑ n ∈ Finset.range (N + 1), F n * G n := by
    rw [RHTower.deningerHarmonicPartial]
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp only [F, G]
    ring
  rw [hlhs, hbp]
  dsimp only [F]
  ring

/-- The absolutely convergent Mertens coefficient series has total mass
zero. -/
theorem tsum_mertensHarmonic_eq_zero :
    (∑' i : ℕ, mertensM i / ((i : ℝ) * ((i : ℝ) + 1))) = 0 := by
  rw [← RHTower.deningerHarmonicLimit,
    RHTower.deningerHarmonicLimit_eq_zero]

/-- Exact boundary-minus-tail form of the Möbius harmonic partial sum. -/
theorem deningerHarmonicPartial_eq_mertens_boundary_sub_tail (N : ℕ) :
    RHTower.deningerHarmonicPartial N =
      mertensM N / (N : ℝ) -
        ∑' i : ℕ, mertensM (i + N) /
          (((i + N : ℕ) : ℝ) * (((i + N : ℕ) : ℝ) + 1)) := by
  have hsplit := deningerMertensHarmonic_summable.sum_add_tsum_nat_add N
  rw [tsum_mertensHarmonic_eq_zero] at hsplit
  rw [deningerHarmonicPartial_eq_mertens_boundary_add]
  linarith

end RHTower.Sieve
