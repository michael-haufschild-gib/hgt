import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeAbel
import GaloisForLFunctions.RHTower.Sieve.Section4AllBlocksSmall

/-!
# Narrow-block transfer from ordinary to harmonic prime polynomials

On a geometric block, reciprocal prime weights differ from the frozen left-endpoint weight by at
most `eta / Q`.  This transfers the initial-range ordinary all-small partition to Menon's harmonic
Ramaré products while retaining the exact block cardinality and geometric endpoint.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Free narrow-interval comparison between harmonic and ordinary prime polynomials. -/
theorem norm_harmonicPrimeBlockPoly_le_narrow
    {B : Finset ℕ} {Q eta : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta)
    (hB : ∀ p ∈ B, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + eta)) (w : ℝ) :
    ‖harmonicPrimeBlockPoly B w‖ ≤
      ‖primeBlockPoly B w‖ / Q + (B.card : ℝ) * eta / Q := by
  have hdecomp : harmonicPrimeBlockPoly B w =
      (1 / (Q : ℂ)) * primeBlockPoly B w +
        ∑ p ∈ B, ((((1 / (p : ℝ)) - 1 / Q : ℝ) : ℂ) * moebiusPhase w p) := by
    rw [harmonicPrimeBlockPoly_eq_weighted_sum, primeBlockPoly, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    push_cast
    field_simp
    ring
  rw [hdecomp]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simp only [norm_mul, norm_div, norm_one, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_pos hQ]
    ring_nf
    exact le_rfl
  · calc
      ‖∑ p ∈ B, ((((1 / (p : ℝ)) - 1 / Q : ℝ) : ℂ) * moebiusPhase w p)‖
          ≤ ∑ p ∈ B,
              ‖((((1 / (p : ℝ)) - 1 / Q : ℝ) : ℂ) * moebiusPhase w p)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _p ∈ B, eta / Q := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpQ := hB p hp
        have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans hQ hpQ.1
        have hdiff : |(1 / (p : ℝ)) - 1 / Q| ≤ eta / Q := by
          rw [abs_of_nonpos (sub_nonpos.mpr (one_div_le_one_div_of_le hQ hpQ.1.le)), neg_sub]
          have hnum : (p : ℝ) - Q ≤ Q * eta := by linarith [hpQ.2]
          have hident : 1 / Q - 1 / (p : ℝ) = ((p : ℝ) - Q) / (Q * (p : ℝ)) := by
            field_simp
          rw [hident]
          exact (div_le_div_iff₀ (mul_pos hQ hp0) hQ).2 (by
            nlinarith [mul_le_mul_of_nonneg_right hpQ.1.le heta])
        rw [norm_mul, Complex.norm_real]
        have hphase := norm_moebiusPhase_le_one w p
        calc
          |1 / (p : ℝ) - 1 / Q| * ‖moebiusPhase w p‖
              ≤ |1 / (p : ℝ) - 1 / Q| * 1 :=
                mul_le_mul_of_nonneg_left hphase (abs_nonneg _)
          _ ≤ eta / Q := by simpa using hdiff
      _ = (B.card : ℝ) * eta / Q := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- Geometric-block form of the frozen reciprocal-weight comparison. -/
theorem norm_harmonicPrimeBlockPoly_geom_le
    (P : Finset ℕ) {Q eta : ℝ} (hQ : 0 < Q) (heta : 0 ≤ eta)
    (j : ℕ) (w : ℝ) :
    ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤
      ‖primeBlockPoly (geomBlock P Q (1 + eta) j) w‖ /
          (Q * (1 + eta) ^ j) +
        ((geomBlock P Q (1 + eta) j).card : ℝ) * eta /
          (Q * (1 + eta) ^ j) := by
  have hQj : 0 < Q * (1 + eta) ^ j := by positivity
  refine norm_harmonicPrimeBlockPoly_le_narrow hQj heta ?_ w
  intro p hp
  have hp' := Finset.mem_filter.1 hp
  refine ⟨hp'.2.1, ?_⟩
  calc
    (p : ℝ) ≤ Q * (1 + eta) ^ (j + 1) := hp'.2.2
    _ = (Q * (1 + eta) ^ j) * (1 + eta) := by ring

/-- Every ordinary all-small frequency supplies the corresponding harmonic block bound. -/
theorem norm_harmonicPrimeBlockPoly_le_of_mem_ordinary_allBlocksSmall
    {P : Finset ℕ} {Q eta theta W : ℝ} {L j : ℕ}
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hj : j ∈ Finset.range L)
    {w : ℝ}
    (hw : w ∈ allBlocksSmall P Q eta L
      (fun i => ((geomBlock P Q (1 + eta) i).card : ℝ) * theta) W) :
    ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖ ≤
      ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
        (Q * (1 + eta) ^ j) := by
  have hprime := norm_primeBlockPoly_le_of_mem_allBlocksSmall hj hw
  have hbase := norm_harmonicPrimeBlockPoly_geom_le P hQ heta j w
  have hden : 0 < Q * (1 + eta) ^ j := by positivity
  calc
    ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w‖
        ≤ ‖primeBlockPoly (geomBlock P Q (1 + eta) j) w‖ /
            (Q * (1 + eta) ^ j) +
          ((geomBlock P Q (1 + eta) j).card : ℝ) * eta /
            (Q * (1 + eta) ^ j) := hbase
    _ ≤ (((geomBlock P Q (1 + eta) j).card : ℝ) * theta) /
            (Q * (1 + eta) ^ j) +
          ((geomBlock P Q (1 + eta) j).card : ℝ) * eta /
            (Q * (1 + eta) ^ j) := by
      gcongr
    _ = ((geomBlock P Q (1 + eta) j).card : ℝ) * (theta + eta) /
          (Q * (1 + eta) ^ j) := by ring

end

end RHTower.Sieve
