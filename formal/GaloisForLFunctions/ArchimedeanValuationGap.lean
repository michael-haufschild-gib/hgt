import GaloisForLFunctions.ArchimedeanBendLaw
import Mathlib

/-!
# Valuation gap forces dominance

The magnitude hypertranscendence cards verify the strict-dominance hypothesis of the Archimedean
bend law through a **valuation gap**.  If the atoms `x i` have moduli `‖x i‖ = exp(−V i)`, the
integer weights and the atom count are bounded by `B ≥ 1`, and the distinguished minimizer `i₀`
beats every other valuation by more than `2·log B`, then the minimizer strictly dominates and the
integer-weighted sum is nonzero (`sum_ne_zero_of_valuation_gap`).

For a superlacunary log-magnitude sequence `b_n = −log|a_n|` with successive ratios `→ ∞`, the
unique valuation minimizer of any nonvacuous coefficient identity beats the runner-up by a
super-logarithmic gap, so this lemma refutes the identity — the analytic core of the log-superlacunary
and sibling Taylor-magnitude cards.
-/

open Finset Real

namespace GaloisForLFunctions

/-- **Valuation gap ⟹ nonzero sum.**  A super-`2 log B` valuation gap at the distinguished
minimizer makes an integer-weighted sum of exponential-modulus atoms nonzero. -/
theorem sum_ne_zero_of_valuation_gap {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℤ)
    (x : ι → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ s) (hc : c i₀ ≠ 0) (V : ι → ℝ)
    (hnorm : ∀ i ∈ s, ‖x i‖ = Real.exp (- V i))
    (B : ℝ) (hB : 1 ≤ B) (hcB : ∀ i ∈ s, ‖(c i : ℂ)‖ ≤ B) (hcard : (s.card : ℝ) ≤ B)
    (hgap : ∀ i ∈ s, i ≠ i₀ → V i₀ + 2 * Real.log B < V i) :
    ∑ i ∈ s, (c i : ℂ) * x i ≠ 0 := by
  have hBpos : (0 : ℝ) < B := by linarith
  refine sum_ne_zero_of_dominant s c x hi₀ hc ?_
  rw [hnorm i₀ hi₀]
  rcases (s.erase i₀).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]; exact Real.exp_pos _
  -- key identity B^2 · exp(-(2 log B)) = 1
  have hkey : B ^ 2 * Real.exp (-(2 * Real.log B)) = 1 := by
    rw [Real.exp_neg, two_mul, Real.exp_add, Real.exp_log hBpos]
    field_simp
  -- strict per-term bound
  have hterm : ∀ i ∈ s.erase i₀,
      ‖(c i : ℂ) * x i‖ < B * Real.exp (- (V i₀ + 2 * Real.log B)) := by
    intro i hi
    rw [Finset.mem_erase] at hi
    obtain ⟨hine, hisS⟩ := hi
    rw [norm_mul, hnorm i hisS]
    have hVi : Real.exp (- V i) < Real.exp (- (V i₀ + 2 * Real.log B)) :=
      Real.exp_lt_exp.mpr (by linarith [hgap i hisS hine])
    calc ‖(c i : ℂ)‖ * Real.exp (- V i)
        ≤ B * Real.exp (- V i) :=
          mul_le_mul_of_nonneg_right (hcB i hisS) (le_of_lt (Real.exp_pos _))
      _ < B * Real.exp (- (V i₀ + 2 * Real.log B)) := mul_lt_mul_of_pos_left hVi hBpos
  calc ∑ i ∈ s.erase i₀, ‖(c i : ℂ) * x i‖
      < ∑ _i ∈ s.erase i₀, B * Real.exp (- (V i₀ + 2 * Real.log B)) :=
        Finset.sum_lt_sum_of_nonempty hne hterm
    _ = (s.erase i₀).card * (B * Real.exp (- (V i₀ + 2 * Real.log B))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (- V i₀) := by
        have hcarderase : ((s.erase i₀).card : ℝ) ≤ B :=
          le_trans (by exact_mod_cast Finset.card_erase_le) hcard
        have hexp : Real.exp (- (V i₀ + 2 * Real.log B))
            = Real.exp (- V i₀) * Real.exp (-(2 * Real.log B)) := by
          rw [← Real.exp_add]; ring_nf
        rw [hexp]
        have hBEF : (0 : ℝ) ≤ B * (Real.exp (- V i₀) * Real.exp (-(2 * Real.log B))) := by
          positivity
        calc ((s.erase i₀).card : ℝ) * (B * (Real.exp (- V i₀) * Real.exp (-(2 * Real.log B))))
            ≤ B * (B * (Real.exp (- V i₀) * Real.exp (-(2 * Real.log B)))) :=
              mul_le_mul_of_nonneg_right hcarderase hBEF
          _ = B ^ 2 * Real.exp (-(2 * Real.log B)) * Real.exp (- V i₀) := by ring
          _ = Real.exp (- V i₀) := by rw [hkey, one_mul]

end GaloisForLFunctions
