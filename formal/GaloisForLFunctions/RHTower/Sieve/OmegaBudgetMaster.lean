import GaloisForLFunctions.RHTower.Sieve.AnnulusBoundUniform
import GaloisForLFunctions.RHTower.Sieve.DiscBoundUniform
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetLadderTail

/-!
# The Route E budget from elementary conditions on the parameters

Every analytic input of the short-interval argument has now been reduced to a uniform statement on
a fixed frequency range, so the whole budget follows from elementary inequalities among the ladder's
parameters.  This is the statement the substitution consumes.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The annulus constant of the ladder. -/
def ladderRho (Ctot D Lx Hmaj μ q w₀ xmin Q η : ℝ) : ℝ :=
  (4 / Real.log 2)
    * ((1 + η) * relScaledMajorant Ctot D Lx Hmaj μ q (2 * Real.pi * w₀) xmin
      + 7 * Real.exp 9 / Q)

/-- **The Route E budget from elementary conditions on the parameters.** -/
theorem exists_omegaBudget_master :
    ∃ (A delta Ctot τ₀ : ℝ) (K₀ : ℕ) (N₁ : ℝ), 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (x h : ℝ) (z₀ z L B₀ : ℕ) (Q η D w₀ T₀ G Lx q μ xmin Hmaj Nmin : ℝ),
        0 < fibreWidth x h → B₀ = ⌊Real.sqrt x + h⌋₊ → 0 < (B₀ : ℝ) →
        1 ≤ z₀ → Q = (z₀ : ℝ) → 1 < Q → 0 < η → 1 ≤ L → z = ⌊Q * (1 + η) ^ L⌋₊ →
        1 ≤ G → G ≤ T₀ → 0 ≤ w₀ → w₀ ≤ G →
        1 ≤ D → max τ₀ (16 * Real.pi / 3) ≤ 2 * Real.pi * w₀ →
        0 ≤ Lx →
        (∀ j ∈ Finset.range L,
          Real.log (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) ≤ Lx) →
        0 ≤ q →
        (∀ j ∈ Finset.range L,
          q ≤ Real.log (max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1)) →
        0 ≤ μ → μ ≤ min delta (routeTWidthPolylogLower A (2 * Real.pi * T₀)) / 2 →
        0 < xmin →
        (∀ j ∈ Finset.range L, xmin ≤ max ((⌊Q * (1 + η) ^ (j + 1)⌋₊ : ℕ) : ℝ) 1) →
        1 / (2 * Real.pi * w₀)
            + Real.log (3 * (2 * Real.pi * T₀) / 2)
              / routeTWidthPolylogLower A (2 * Real.pi * T₀) ≤ Hmaj →
        1 ≤ Nmin → N₁ ≤ Nmin →
        (∀ j ∈ Finset.range L, Nmin ≤ ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) →
        K₀ ≤ contourParam Nmin →
        5 + 8 * Real.pi * w₀ ≤ ((contourParam Nmin : ℕ) : ℝ) →
        omegaBudget x h z₀ z
          ≤ 16 * Real.sqrt x
              * (2 * (fibreWidth x h) ^ (2 : ℕ)
                  * (ladderAffineSlope L B₀ Q η (ladderRho Ctot D Lx Hmaj μ q w₀ xmin Q η) * G
                    + ladderAffineConst z₀ z L B₀ Q η
                        (ladderRho Ctot D Lx Hmaj μ q w₀ xmin Q η) (relMoebiusSharp Nmin) w₀)
                + (4 * (ladderAffineSlope L B₀ Q η (ladderRho Ctot D Lx Hmaj μ q w₀ xmin Q η)
                      + 5 * Real.pi / 2
                        * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ))
                      + 5 * Real.exp 1 / 2 * (B₀ : ℝ)
                        * (∑ n ∈ Finset.Icc 1 B₀, ‖omegaCoeff (primesRange z₀ z) n‖ ^ (2 : ℕ)) / T₀)
                    / (Real.pi ^ (2 : ℕ) * G)
                  + 4 * ladderAffineConst z₀ z L B₀ Q η
                        (ladderRho Ctot D Lx Hmaj μ q w₀ xmin Q η) (relMoebiusSharp Nmin) w₀
                    / (3 * Real.pi ^ (2 : ℕ) * G ^ (2 : ℕ))))
            + 204 * (((primesRange z₀ z).card : ℝ) + 1) ^ (2 : ℕ) * (Real.sqrt x + 1)
            + 2 * (h + 1) * (2 * h + 1)
                * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
                  + 8 * ((Nat.primesLE z).card : ℝ) ^ (2 : ℕ)) := by
  obtain ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, hann⟩ := exists_annulus_bound_uniform
  obtain ⟨K₀, N₁, hdisc⟩ := exists_disc_bound_uniform
  refine ⟨A, delta, Ctot, τ₀, K₀, N₁, hdelta, hCtot, hτ₀, ?_⟩
  intro x h z₀ z L B₀ Q η D w₀ T₀ G Lx q μ xmin Hmaj Nmin hδ hB₀ hB hz₀ hQ hQ1 hη hL hz
    hG hGT₀ hw₀ hwG hD hw₀τ hLx0 hLxj hq0 hqj hμ0 hμ hxmin hxminj hHmaj hNmin hN₁ hNj hK hτd
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hw₀0 : (0 : ℝ) < 2 * Real.pi * w₀ := by
    have := le_trans (le_max_right τ₀ (16 * Real.pi / 3)) hw₀τ
    linarith
  have hHm0 : (0 : ℝ) ≤ Hmaj := by
    have h1 : (0 : ℝ) < 1 / (2 * Real.pi * w₀) := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * T₀) / 2)
        / routeTWidthPolylogLower A (2 * Real.pi * T₀) := by
      have hT₀ : (0 : ℝ) < T₀ := lt_of_lt_of_le zero_lt_one (le_trans hG hGT₀)
      have hlog : (0 : ℝ) ≤ Real.log (3 * (2 * Real.pi * T₀) / 2) := by
        refine Real.log_nonneg ?_
        have hwT : (2 : ℝ) * Real.pi * w₀ ≤ 2 * Real.pi * T₀ := by
          have : w₀ ≤ T₀ := le_trans hwG hGT₀
          nlinarith [hpi]
        have h16 : 16 * Real.pi / 3 ≤ 2 * Real.pi * w₀ :=
          le_trans (le_max_right _ _) hw₀τ
        nlinarith [hpi, hpi3, h16, hwT]
      exact div_nonneg hlog (routeTWidthPolylogLower_pos A (2 * Real.pi * T₀)).le
    linarith
  have hR0 : (0 : ℝ) ≤ relScaledMajorant Ctot D Lx Hmaj μ q (2 * Real.pi * w₀) xmin :=
    relScaledMajorant_nonneg hCtot.le (by linarith) hLx0 hHm0 hw₀0 hxmin
  have hρ : (0 : ℝ) < ladderRho Ctot D Lx Hmaj μ q w₀ xmin Q η := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : (0 : ℝ) ≤ (1 + η) * relScaledMajorant Ctot D Lx Hmaj μ q (2 * Real.pi * w₀) xmin :=
      mul_nonneg (by linarith) hR0
    have h2 : (0 : ℝ) < 7 * Real.exp 9 / Q := by positivity
    rw [ladderRho]
    have h3 : (0 : ℝ) < 4 / Real.log 2 := by positivity
    nlinarith [h1, h2, h3]
  have hs0 : (0 : ℝ) ≤ relMoebiusSharp Nmin := relMoebiusSharp_nonneg (by linarith)
  have hV := hann z₀ z L B₀ Q η D w₀ T₀ Lx q μ xmin Hmaj hz₀ hQ hη.le hz hD hw₀τ
    (le_trans hwG hGT₀) hLxj hq0 hqj hμ0 hμ hxmin hxminj hHmaj
  have hU := hdisc B₀ L Q η w₀ Nmin (by linarith) hη.le hNmin hN₁ hw₀ hNj hK hτd
  exact omegaBudget_le_ladder_final hδ hB₀ hQ hQ1 hη hG hGT₀ hw₀ hwG hL hρ hs0 hz hB hV hU

end

end RHTower.Sieve
