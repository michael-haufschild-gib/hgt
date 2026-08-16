import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Abel assembly of Mertens' partial sums

Summation by parts writes `∑_{i<n+1} c_i/(i+1)` as the boundary term `P(n+1)/(n+1)` plus a sum
against the increments of `1/m`.  Splitting the summatory function `P(m) = m + E(m)` turns the
second piece into `H_{n+1} - 1` plus the error tail, so the whole expression minus `log(n+1)`
converges to `γ` plus the tail limit.
-/

open Filter Topology Finset

namespace RHTower

noncomputable section

/-- **Summation by parts for the harmonic weight.** -/
theorem sum_div_succ_eq_abel (c : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), c i / ((i : ℝ) + 1)
      = (∑ i ∈ range (n + 1), c i) / ((n : ℝ) + 1)
        + ∑ k ∈ range n, (∑ i ∈ range (k + 1), c i)
            * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun i => c i / ((i : ℝ) + 1)), ih]
    rw [Finset.sum_range_succ (fun k => (∑ i ∈ range (k + 1), c i)
      * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)))]
    have hP : (∑ i ∈ range (n + 1 + 1), c i) = (∑ i ∈ range (n + 1), c i) + c (n + 1) :=
      Finset.sum_range_succ _ _
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
    rw [hP]
    push_cast
    field_simp
    ring

/-- The harmonic tail produced by the linear part of the summatory function. -/
theorem sum_linear_increment (n : ℕ) :
    ∑ k ∈ range n, ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))
      = (harmonic (n + 1) : ℝ) - 1 := by
  induction n with
  | zero => norm_num [harmonic_succ]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hh : ((harmonic (n + 1 + 1) : ℚ) : ℝ)
        = ((harmonic (n + 1) : ℚ) : ℝ) + 1 / ((n : ℝ) + 2) := by
      rw [harmonic_succ]
      push_cast
      ring
    rw [hh]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring

/-- **The Abel assembly.**  If the summatory function has mean one and the error tail converges,
then the harmonic-weighted partial sums minus `log` converge to `γ` plus the tail. -/
theorem tendsto_abelPartialSum_sub_log {c : ℕ → ℝ} {T : ℝ}
    (hP : Tendsto (fun n : ℕ => (∑ i ∈ range n, c i) / (n : ℝ)) atTop (𝓝 1))
    (hT : Tendsto (fun n : ℕ => ∑ k ∈ range n,
        ((∑ i ∈ range (k + 1), c i) - ((k : ℝ) + 1))
          * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))) atTop (𝓝 T)) :
    Tendsto (fun n : ℕ => (∑ i ∈ range (n + 1), c i / ((i : ℝ) + 1)) - Real.log ((n : ℝ) + 1))
      atTop (𝓝 (Real.eulerMascheroniConstant + T)) := by
  have hsplit : ∀ n : ℕ, (∑ i ∈ range (n + 1), c i / ((i : ℝ) + 1)) - Real.log ((n : ℝ) + 1)
      = ((∑ i ∈ range (n + 1), c i) / ((n : ℝ) + 1) - 1)
        + ((harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1))
        + ∑ k ∈ range n, ((∑ i ∈ range (k + 1), c i) - ((k : ℝ) + 1))
            * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
    intro n
    have hsub : ∀ k : ℕ, ((∑ i ∈ range (k + 1), c i) - ((k : ℝ) + 1))
        * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))
        = (∑ i ∈ range (k + 1), c i) * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))
          - ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
      intro k
      ring
    rw [Finset.sum_congr rfl fun k _ => hsub k, Finset.sum_sub_distrib, sum_linear_increment,
      sum_div_succ_eq_abel]
    ring
  have hb : Tendsto (fun n : ℕ => (∑ i ∈ range (n + 1), c i) / ((n : ℝ) + 1) - 1) atTop (𝓝 0) := by
    have hshift := hP.comp (tendsto_add_atTop_nat 1)
    have hcong : ∀ n : ℕ, ((fun n : ℕ => (∑ i ∈ range n, c i) / (n : ℝ)) ∘ (fun n => n + 1)) n
        = (∑ i ∈ range (n + 1), c i) / ((n : ℝ) + 1) := by
      intro n
      simp only [Function.comp_apply]
      push_cast
      ring
    have := (hshift.congr hcong).sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa using this
  have hh : Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have hshift := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    refine hshift.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring
  have hsum := (hb.add hh).add hT
  rw [zero_add] at hsum
  exact hsum.congr fun n => (hsplit n).symm

end

end RHTower
