import GaloisForLFunctions.RHTower.Sieve.LadderHarmonicSplit

/-!
# Comparing a ladder block's size with its harmonic mass

Every prime of the `j`-th block of a geometric ladder is at most the block's right endpoint, so the
block's cardinality is at most that endpoint times the block's harmonic mass.  This is the only
comparison between counting and harmonic measure the short-interval argument needs, and it holds for
every subdivision — no prime counting in short intervals is involved.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem stepMass_nonneg (P : Finset ℕ) (Q η : ℝ) (j : ℕ) : 0 ≤ stepMass P Q η j := by
  rw [stepMass]
  refine Finset.sum_nonneg fun p _ => ?_
  positivity

/-- **A ladder block's size is at most its right endpoint times its harmonic mass.** -/
theorem card_geomBlock_le_mul_stepMass {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    ((geomBlock P Q (1 + η) j).card : ℝ) ≤ (Q * (1 + η) ^ (j + 1)) * stepMass P Q η j := by
  classical
  have hkey : ((geomBlock P Q (1 + η) j).card : ℝ) = ∑ _p ∈ geomBlock P Q (1 + η) j, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hkey, stepMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [geomBlock, Finset.mem_filter] at hp
  obtain ⟨-, hlo, hhi⟩ := hp
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans hbase hlo
  rw [mul_one_div, le_div_iff₀ hp0, one_mul]
  exact hhi

/-- **The ladder's counting sum against the cofactor lengths is the harmonic mass.**  This is the
estimate that replaces every short-interval prime count in the spectral side. -/
theorem sum_card_geomBlock_div_le {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ}
    (hL : 1 ≤ L) (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) {B : ℝ} (hB : 0 ≤ B) :
    (∑ j ∈ Finset.range L, ((geomBlock P Q (1 + η) j).card : ℝ) * (B / (Q * (1 + η) ^ j)))
      ≤ (1 + η) * B * ∑ p ∈ P, 1 / (p : ℝ) := by
  classical
  have hstep : ∀ j ∈ Finset.range L,
      ((geomBlock P Q (1 + η) j).card : ℝ) * (B / (Q * (1 + η) ^ j))
        ≤ (1 + η) * B * stepMass P Q η j := by
    intro j _
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    have hcard := card_geomBlock_le_mul_stepMass (P := P) hQ hη j
    have hBdiv : (0 : ℝ) ≤ B / (Q * (1 + η) ^ j) := div_nonneg hB hbase.le
    have hmul := mul_le_mul_of_nonneg_right hcard hBdiv
    refine hmul.trans (le_of_eq ?_)
    rw [pow_succ]
    field_simp
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, sum_stepMass_eq hQ hη hL hP]

end

end RHTower.Sieve
