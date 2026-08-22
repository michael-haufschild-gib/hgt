import GaloisForLFunctions.HTGeometry.BuresWasserstein.EtemadiRecursionLimit

/-!
# Robbins–Monro with a Cesàro-null perturbation

The stochastic-approximation recursion driving the no-dice and strong-law approximations has the
form

`d(n+1) ≤ (1 - α/(n+1)) d(n) + (n+1)⁻¹ εₙ + C (n+1)⁻²`,

where the perturbation `εₙ` is not summable but only Cesàro-null.  The classical Robbins–Monro
argument, which absorbs a square-summable error, does not apply; Etemadi's weighted extension of
the Cesàro limit does, because the recursion is exactly a weighted average of the driving terms
`εₙ + C/(n+1)` whose Cesàro means vanish.

This is the deterministic engine of the strong law of large numbers for the Wasserstein
barycentre.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

open GaloisForLFunctions.HTGeometry.Etemadi

/-- **Robbins–Monro with a Cesàro-null perturbation.** -/
theorem tendsto_zero_of_robbins_cesaro {d ε : ℕ → ℝ} {α C : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hd : ∀ n, 0 ≤ d n)
    (hrec : ∀ n : ℕ, d (n + 1) ≤ (1 - α / ((n : ℝ) + 1)) * d n
      + (1 / ((n : ℝ) + 1)) * ε n + C * (1 / ((n : ℝ) + 1)) ^ 2)
    (hces : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, ε i) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto d atTop (𝓝 0) := by
  -- the driving sequence of the comparison recursion
  set bb : ℕ → ℝ := fun n => (ε n + C / ((n : ℝ) + 1)) / α with hbbdef
  -- the comparison sequence
  set s : ℕ → ℝ := fun n =>
    Nat.rec (d 0) (fun k acc => (1 - α / ((k : ℝ) + 1)) * acc + (α / ((k : ℝ) + 1)) * bb k) n
    with hsdef
  have hs0 : s 0 = d 0 := rfl
  have hsrec : ∀ n : ℕ, s (n + 1)
      = (1 - α / ((n : ℝ) + 1)) * s n + (α / ((n : ℝ) + 1)) * bb n := fun _ => rfl
  -- the coefficient is nonnegative
  have hcoef : ∀ n : ℕ, (0 : ℝ) ≤ 1 - α / ((n : ℝ) + 1) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : α / ((n : ℝ) + 1) ≤ α := by
      rw [div_le_iff₀ h1]
      nlinarith [Nat.cast_nonneg (α := ℝ) n, hα.le]
    linarith
  -- the driving term is exactly the perturbation
  have hdrive : ∀ n : ℕ, (α / ((n : ℝ) + 1)) * bb n
      = (1 / ((n : ℝ) + 1)) * ε n + C * (1 / ((n : ℝ) + 1)) ^ 2 := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hbbdef]
    field_simp
  -- the comparison sequence dominates
  have hdom : ∀ n, d n ≤ s n := by
    intro n
    induction n with
    | zero => rw [hs0]
    | succ n ih =>
      rw [hsrec n, hdrive n]
      have h := hrec n
      have hmul : (1 - α / ((n : ℝ) + 1)) * d n ≤ (1 - α / ((n : ℝ) + 1)) * s n :=
        mul_le_mul_of_nonneg_left ih (hcoef n)
      linarith
  -- the Cesàro means of the driving sequence vanish
  have hharm : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) / (n : ℝ))
      atTop (𝓝 0) := by
    have h : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine h.cesaro.congr fun n => ?_
    rw [div_eq_inv_mul]
  have hbb : Tendsto (fun n : ℕ => partialSum bb n / (n : ℝ)) atTop (𝓝 0) := by
    have hsum : ∀ n : ℕ, partialSum bb n / (n : ℝ)
        = ((∑ i ∈ Finset.range n, ε i) / (n : ℝ)
            + C * ((∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) / (n : ℝ))) / α := by
      intro n
      have hps : partialSum bb n
          = ((∑ i ∈ Finset.range n, ε i) + C * ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) / α := by
        rw [partialSum, hbbdef]
        rw [eq_div_iff (ne_of_gt hα), Finset.sum_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      rw [hps]
      field_simp
    have hlim : Tendsto (fun n : ℕ => ((∑ i ∈ Finset.range n, ε i) / (n : ℝ)
        + C * ((∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1))) / (n : ℝ))) / α)
        atTop (𝓝 ((0 + C * 0) / α)) :=
      ((hces.add (tendsto_const_nhds.mul hharm)).div_const α)
    have hzero : ((0 : ℝ) + C * 0) / α = 0 := by simp
    rw [hzero] at hlim
    exact hlim.congr fun n => (hsum n).symm
  -- the comparison sequence converges to zero
  have hstend : Tendsto s atTop (𝓝 0) := tendsto_of_etemadiRecursion hα hα1 hsrec hbb
  exact squeeze_zero hd hdom hstend

end GaloisForLFunctions.HTGeometry.BuresWasserstein
