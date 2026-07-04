/-
Coefficient-tail provider layer for the RHTower spur multiplier.

This is the RHTower analogue of the factored-tail/provider pattern used in the
Hurwitz and Böttcher/U0 formal lanes: the envelope theorem should consume a
named tail interface, while the polynomial coefficient bookkeeping lives here.
-/
import GaloisForLFunctions.RHTower.SpurCumulant

namespace RHTower

open Polynomial

noncomputable section

/-- Provider interface for bounding the exact polynomial tail after the multiplier jet. -/
def multiplierJetTailEvalBound (K : ℝ) (P n j d : ℕ) : Prop :=
  ∃ Q : ℝ[X],
    (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹) =
        (multiplierJetPoly P n j).eval ((d : ℝ)⁻¹) +
          ((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹) ∧
      |Q.eval ((d : ℝ)⁻¹)| ≤ K * (j : ℝ) ^ (2 * P)

/-- A provider bound for `Q(1/d)` gives the scaled `d^{-P}` tail bound. -/
theorem tail_term_bound_of_multiplierJetTailEvalBound {K : ℝ} {P n j d : ℕ}
    (hd : 0 < d) (hTail : multiplierJetTailEvalBound K P n j d) :
    ∃ Q : ℝ[X],
      (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹) =
          (multiplierJetPoly P n j).eval ((d : ℝ)⁻¹) +
            ((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹) ∧
        |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)| ≤
          K * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  obtain ⟨Q, hQeq, hQbound⟩ := hTail
  refine ⟨Q, hQeq, ?_⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hscale_nonneg : 0 ≤ |((d : ℝ)⁻¹) ^ P| := abs_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hQbound hscale_nonneg
  have hscale : |((d : ℝ)⁻¹) ^ P| = ((d : ℝ) ^ P)⁻¹ := by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt hdR)) P), inv_pow]
  calc
    |((d : ℝ)⁻¹) ^ P * Q.eval ((d : ℝ)⁻¹)|
        = |((d : ℝ)⁻¹) ^ P| * |Q.eval ((d : ℝ)⁻¹)| := abs_mul _ _
    _ ≤ |((d : ℝ)⁻¹) ^ P| * (K * (j : ℝ) ^ (2 * P)) := hmul
    _ = K * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
      rw [hscale]
      rw [div_eq_mul_inv]
      ring

/-- Coefficient-sum provider for the exact multiplier-jet tail.

This replaces the anonymous tail quotient in `multiplierJetTailEvalBound` by the
explicit shifted high-coefficient quotient.  The remaining R1 tail task is now
the finite coefficient sum on the hypothesis line. -/
theorem multiplierJetTailEvalBound_of_coeff_sum_bound {K : ℝ} (P : ℕ) {j d : ℕ}
    (hCoeff :
      ∑ r ∈ Finset.range (P * (P - 1) + 1),
        |multiplierCoeff P (P - 1) j (P + r)| * |((d : ℝ)⁻¹)| ^ r ≤
          K * (j : ℝ) ^ (2 * P)) :
    multiplierJetTailEvalBound K P (P - 1) j d := by
  let Q : ℝ[X] := PolynomialTruncation.shiftedTailUpTo
    (multiplierTruncPoly P (P - 1) j) P (P * (P - 1))
  refine ⟨Q, ?_, ?_⟩
  · have hdeg : (multiplierTruncPoly P (P - 1) j).natDegree ≤
        P + P * (P - 1) := by
      exact le_trans (natDegree_multiplierTruncPoly_le P (P - 1) j) (by omega)
    have hsplit := PolynomialTruncation.eval_eq_lowTrunc_add_pow_mul_shiftedTailUpTo_of_natDegree_le
      (P := multiplierTruncPoly P (P - 1) j) P (P * (P - 1)) ((d : ℝ)⁻¹) hdeg
    simpa [Q, multiplierJetPoly] using hsplit
  · have hbound := PolynomialTruncation.abs_eval_shiftedTailUpTo_le
      (P := multiplierTruncPoly P (P - 1) j) P (P * (P - 1)) ((d : ℝ)⁻¹)
    exact le_trans (by simpa [Q, multiplierCoeff] using hbound) hCoeff

/-- If the explicit high-coefficient sum is bounded without the `d` weights, it
supplies the tail provider for every positive `d`.

This removes `d` from the remaining R1 coefficient-tail obligation: under `0 < d`,
all factors `|1/d|^r` are at most `1`. -/
theorem multiplierJetTailEvalBound_of_coeff_abs_sum_bound {K : ℝ} (P : ℕ) {j d : ℕ}
    (hd : 0 < d)
    (hCoeff :
      ∑ r ∈ Finset.range (P * (P - 1) + 1),
        |multiplierCoeff P (P - 1) j (P + r)| ≤ K * (j : ℝ) ^ (2 * P)) :
    multiplierJetTailEvalBound K P (P - 1) j d := by
  refine multiplierJetTailEvalBound_of_coeff_sum_bound (K := K) P ?_
  have hweighted_le :
      ∑ r ∈ Finset.range (P * (P - 1) + 1),
        |multiplierCoeff P (P - 1) j (P + r)| * |((d : ℝ)⁻¹)| ^ r ≤
      ∑ r ∈ Finset.range (P * (P - 1) + 1),
        |multiplierCoeff P (P - 1) j (P + r)| := by
    apply Finset.sum_le_sum
    intro r _
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have h1dNat : 1 ≤ d := Nat.succ_le_iff.mpr hd
    have h1d : (1 : ℝ) ≤ d := by exact_mod_cast h1dNat
    have hinv_abs_le_one : |((d : ℝ)⁻¹)| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hdR))]
      exact inv_le_one_of_one_le₀ h1d
    have hpow : |((d : ℝ)⁻¹)| ^ r ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hinv_abs_le_one
    have hcoeff_nonneg : 0 ≤ |multiplierCoeff P (P - 1) j (P + r)| := abs_nonneg _
    calc
      |multiplierCoeff P (P - 1) j (P + r)| * |((d : ℝ)⁻¹)| ^ r
          ≤ |multiplierCoeff P (P - 1) j (P + r)| * 1 :=
            mul_le_mul_of_nonneg_left hpow hcoeff_nonneg
      _ = |multiplierCoeff P (P - 1) j (P + r)| := by ring
  exact le_trans hweighted_le hCoeff

end

end RHTower
