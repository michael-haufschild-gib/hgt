import GaloisForLFunctions.RHTower.Sieve.JointTuranKubilius
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightTransfer

/-!
# The joint designated-prime weight on the fibres

Soundararajan's exposé §4 replaces the single weight `ω_P` of §3 by the product `ω_P·ω_Q` of two
designated counts over **disjoint** prime ranges — a short one and a long one.  The reason is
structural: on the exceptional set where the short prime polynomial fails to cancel, the long one
does (Lemma 2.3 applies to it), and without a second designated variable there is nothing left to
save with.

The transfer itself is the corpus's `Sieve/WeightRemovalFibre.sum_sq_fibreSum_le_weighted`, which is
already stated for an arbitrary real weight.  What has to be supplied is the variance of the joint
weight over the dyadic block carrying the fibres, and that is
`Sieve/JointTuranKubilius.sum_sq_joint_deviation_le` restricted to the block.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The dyadic block carrying every fibre sits inside an initial segment. -/
theorem fibreDyadicIndex_subset_Icc_one {x : ℝ} (hx : 4 ≤ x) (h : ℝ) :
    fibreDyadicIndex x h ⊆ Finset.Icc 1 ⌊Real.sqrt x + h⌋₊ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hce : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
  intro b hb
  rw [fibreDyadicIndex, Finset.mem_Icc] at hb
  rw [Finset.mem_Icc]
  omega

/-- **The variance of the joint designated-prime count over the fibre block.** -/
theorem sum_variance_joint_fibreDyadicIndex_le {x : ℝ} (hx : 4 ≤ x) (h : ℝ) {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) :
    (∑ b ∈ fibreDyadicIndex x h,
        (((primeFactorsIn P b).card : ℝ) * ((primeFactorsIn Q b).card : ℝ)
          - (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))) ^ (2 : ℕ))
      ≤ ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ)
            * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
            * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) + (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) + 1)
        + 2 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
            * (P.card : ℝ) * (Q.card : ℝ) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fibreDyadicIndex_subset_Icc_one hx h) fun b _ _ => sq_nonneg _) ?_
  exact sum_sq_joint_deviation_le hP hQ hPQ _

/-- **The joint Turán–Kubilius transfer on the fibres.**  The fibre mean square of a unit-bounded
sequence is at most twice that of its joint-weighted multiple, plus the joint variance over the
block. -/
theorem sum_sq_fibreSum_le_jointWeighted {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 4 ≤ x) (hh0 : 0 ≤ h) {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) :
    ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))) ^ (2 : ℕ)
        * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ)
      ≤ 2 * ∑ a ∈ outerBlock x h,
            (∑ b ∈ innerFibre x h a,
              f b * (((primeFactorsIn P b).card : ℝ) * ((primeFactorsIn Q b).card : ℝ))) ^ (2 : ℕ)
        + 2 * (h + 1) * (2 * h + 1)
            * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ)
                  * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
                  * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) + (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) + 1)
              + 2 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
                  * (P.card : ℝ) * (Q.card : ℝ)) := by
  classical
  have hbase := sum_sq_fibreSum_le_weighted (f := f)
    (g := fun b => ((primeFactorsIn P b).card : ℝ) * ((primeFactorsIn Q b).card : ℝ)) hf hx hh0
    ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
  have hvar := sum_variance_joint_fibreDyadicIndex_le hx h hP hQ hPQ
  have hfac : (0 : ℝ) ≤ 2 * (h + 1) * (2 * h + 1) := by nlinarith [hh0]
  linarith [hbase, mul_le_mul_of_nonneg_left hvar hfac]

end

end RHTower.Sieve
