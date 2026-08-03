import GaloisForLFunctions.HTGeometry.BarnesConeLogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# The Barnes source is the convergent atom series

Off the poles the cone product is nonzero and its logarithmic derivative is the sum of the atoms of
its factors:

```text
logDeriv (barnesConeProduct ω) z = ∑' n, (-z/w_n)^N / (w_n + z).
```

Both statements rest on one summability principle: a nonnegative weight dominated by the inverse
`(N+1)`-st power of the cone value outside a finite set is summable, because the exceptional set is
finite and the cone powers are summable.  Applied to the deviation of the factors from one it gives
nonvanishing of the product; applied to the atoms it gives convergence of the series.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## Summability from a cone majorant off a finite set -/

/-- A nonnegative weight dominated by the inverse `(N+1)`-st cone power outside a finite set is
summable. -/
theorem summable_of_conePeriod_majorant (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    {g : (ι → ℕ) → ℝ} (hg : ∀ n, 0 ≤ g n) (B R : ℝ)
    (hbound : ∀ n : ι → ℕ, n ≠ 0 → 2 * R ≤ ‖conePeriod ω n‖ →
      g n ≤ B * (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹) :
    Summable g := by
  classical
  have hTfin : {n : ι → ℕ | n = 0 ∨ ¬ (2 * R ≤ ‖conePeriod ω n‖)}.Finite := by
    refine Set.Finite.subset ((Set.finite_singleton 0).union (finite_conePeriod_lt ω hω R)) ?_
    intro n hn
    rcases hn with h | h
    · exact Or.inl h
    · exact Or.inr h
  set s : Finset (ι → ℕ) := hTfin.toFinset with hs
  have hsplit : ∀ n : ι → ℕ, n ∉ s → n ≠ 0 ∧ 2 * R ≤ ‖conePeriod ω n‖ := by
    intro n hn
    rw [hs, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
    push Not at hn
    exact ⟨hn.1, hn.2⟩
  have hfinsum : Summable fun n : ι → ℕ => if n ∈ s then g n else 0 :=
    summable_of_ne_finset_zero fun n hn => if_neg hn
  have hconesum : Summable fun n : ι → ℕ =>
      max B 0 * (if n = 0 then 0 else (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹) :=
    (summable_conePeriod_inv_pow ω hω).mul_left (max B 0)
  refine Summable.of_nonneg_of_le hg (fun n => ?_) (hconesum.add hfinsum)
  by_cases hn : n ∈ s
  · have h1 : (0 : ℝ) ≤ max B 0 *
        (if n = 0 then 0 else (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹) := by
      refine mul_nonneg (le_max_right _ _) ?_
      split_ifs
      · exact le_rfl
      · positivity
    rw [if_pos hn]
    linarith
  · obtain ⟨hn0, hcone⟩ := hsplit n hn
    have h2 : g n ≤ max B 0 * (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ :=
      (hbound n hn0 hcone).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [if_neg hn, if_neg hn0, add_zero]
    exact h2

/-! ## Nonvanishing off the poles -/

theorem summable_norm_barnesConeFactor_sub_one (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (z : ℂ) :
    Summable fun n : ι → ℕ => ‖barnesConeFactor ω n z - 1‖ := by
  refine summable_of_conePeriod_majorant ω hω (fun n => norm_nonneg _)
    (Real.exp (weierstrassLogBound (Fintype.card ι)) * ‖z‖ ^ (Fintype.card ι + 1))
    ‖z‖ fun n hn hcone => ?_
  rw [barnesConeFactor, if_neg hn]
  exact norm_weierstrassFactor_conePeriod_sub_one_le ω z n hcone

theorem barnesConeFactor_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) (n : ι → ℕ) :
    barnesConeFactor ω n z ≠ 0 := by
  rw [barnesConeFactor]
  split_ifs with h
  · exact one_ne_zero
  · have hw : conePeriod ω n ≠ 0 := conePeriod_ne_zero ω hω h
    rw [weierstrassFactor]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    intro hcon
    apply hpole n h
    have hmul : conePeriod ω n * (1 - -(z / conePeriod ω n)) = conePeriod ω n + z := by
      rw [sub_neg_eq_add]
      field_simp
    rw [hcon, mul_zero] at hmul
    exact hmul.symm

theorem barnesConeProduct_ne_zero_of_notMem_poles (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) :
    barnesConeProduct ω z ≠ 0 := by
  have hprod := tprod_one_add_ne_zero_of_summable
    (f := fun n : ι → ℕ => barnesConeFactor ω n z - 1)
    (fun n => by simpa using barnesConeFactor_ne_zero ω hω hpole n)
    (summable_norm_barnesConeFactor_sub_one ω hω z)
  have heq : ∏' n : ι → ℕ, (1 + (barnesConeFactor ω n z - 1)) = barnesConeProduct ω z := by
    rw [barnesConeProduct]
    exact tprod_congr fun n => by ring
  rw [← heq]
  exact hprod

/-! ## Summability of the atoms -/

theorem norm_logDeriv_barnesConeFactor_le (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    {n : ι → ℕ} (hn : n ≠ 0) (z : ℂ)
    (hcone : 2 * ‖z‖ ≤ ‖conePeriod ω n‖) :
    ‖logDeriv (barnesConeFactor ω n) z‖ ≤
      2 * ‖z‖ ^ Fintype.card ι * (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ := by
  have hwpos : 0 < ‖conePeriod ω n‖ := norm_pos_iff.mpr (conePeriod_ne_zero ω hω hn)
  have hhalf : ‖conePeriod ω n‖ / 2 ≤ ‖conePeriod ω n + z‖ := by
    have hge : ‖conePeriod ω n‖ - ‖z‖ ≤ ‖conePeriod ω n + z‖ := by
      have h := norm_sub_norm_le (conePeriod ω n) (-z)
      simpa [sub_neg_eq_add] using h
    linarith
  have hpos : 0 < ‖conePeriod ω n + z‖ := lt_of_lt_of_le (by positivity) hhalf
  have hne : conePeriod ω n + z ≠ 0 := norm_pos_iff.mp hpos
  rw [logDeriv_barnesConeFactor ω hω hn z hne, norm_div, norm_pow, norm_neg, norm_div,
    div_pow, div_div, div_le_iff₀ (by positivity :
      (0 : ℝ) < ‖conePeriod ω n‖ ^ Fintype.card ι * ‖conePeriod ω n + z‖)]
  have hrw : 2 * ‖z‖ ^ Fintype.card ι * (‖conePeriod ω n‖ ^ (Fintype.card ι + 1))⁻¹ *
      (‖conePeriod ω n‖ ^ Fintype.card ι * ‖conePeriod ω n + z‖) =
      2 * ‖conePeriod ω n + z‖ / ‖conePeriod ω n‖ * ‖z‖ ^ Fintype.card ι := by
    field_simp [pow_succ]
    ring
  rw [hrw]
  have hone : (1 : ℝ) ≤ 2 * ‖conePeriod ω n + z‖ / ‖conePeriod ω n‖ := by
    rw [le_div_iff₀ hwpos]
    linarith
  exact le_mul_of_one_le_left (by positivity) hone

theorem summable_logDeriv_barnesConeFactor (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (z : ℂ) :
    Summable fun n : ι → ℕ => logDeriv (barnesConeFactor ω n) z := by
  refine Summable.of_norm ?_
  exact summable_of_conePeriod_majorant ω hω (fun n => norm_nonneg _)
    (2 * ‖z‖ ^ Fintype.card ι) ‖z‖ fun n hn hcone =>
      norm_logDeriv_barnesConeFactor_le ω hω hn z hcone

/-! ## The source is the atom series -/

/-- **The Barnes source as a convergent series.**  Off the poles the logarithmic derivative of the
cone product is the sum of the rational atoms of its factors. -/
theorem logDeriv_barnesConeProduct_eq_tsum (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) :
    logDeriv (barnesConeProduct ω) z =
      ∑' n : ι → ℕ, logDeriv (barnesConeFactor ω n) z := by
  have hmult : MultipliableLocallyUniformlyOn (barnesConeFactor ω) Set.univ :=
    ⟨_, hasProdLocallyUniformlyOn_barnesConeFactor ω hω⟩
  have hz : (∏' n : ι → ℕ, barnesConeFactor ω n z) ≠ 0 :=
    barnesConeProduct_ne_zero_of_notMem_poles ω hω hpole
  change logDeriv (fun x => ∏' n : ι → ℕ, barnesConeFactor ω n x) z = _
  exact logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
    (barnesConeFactor_ne_zero ω hω hpole)
    (fun n => (differentiable_barnesConeFactor ω n).differentiableOn)
    (summable_logDeriv_barnesConeFactor ω hω z) hmult hz

end

end GaloisForLFunctions
