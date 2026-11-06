import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros
import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationDeterminesThePrimes

/-!
# Beurling One-Off Zero Countermodels and Quantitative Functional-Equation Defect Trade-Off

This module pairs two complementary unconditional results explaining why positive Euler-product
structure and smooth integer-counting asymptotics alone allow isolated "one-off" off-line zeros,
while the exact Riemann functional equation forbids any Beurling deformation of the rational primes:

1. **Complete zero classification and one-off non-recurrence of `overRegularZeta`**
   (`overRegularZeta_eq_zero_iff`, `overRegularZeta_right_zeroSet_eq_pair`,
   `tendsto_overRegularZeta_im_atTop`, `tendsto_overRegularZeta_im_atBot`,
   `not_weakRecurrence_overRegularZeta`):
   For `1/3 < μ < 1/2`, `0 < ν < 3μ − 1`, and `γ ≠ 0`, the continuous Beurling zeta function
   `overRegularZeta μ ν γ` (which has nonnegative prime and integer densities and integer-count
   remainder `N(x) − ρ x − C → 0`) has **exact** pole-free zero set in `Re s > −(3μ − 1 − ν)` equal
   to `{(1 − μ) + iγ, (1 − μ) − iγ, −(4μ − 1)}`. For every `h ∈ [0, 1/2 − μ)`, its pole-free zero
   set in `Re s > 1/2 + h` is the finite two-element pair `{(1 − μ) ± iγ}`, violating the
   asymptotic abscissa law. Moreover, `overRegularZeta μ ν γ (σ + it) → 1` as `|t| → ∞` on every
   vertical line, so vertical shifts of the off-line zero `ρ₀ = (1 − μ) + iγ` satisfy
   `‖ζ_B(ρ₀ + iτ) − ζ_B(ρ₀)‖ ≥ 1/2` for all large `|τ|`, refuting weak zero-disc recurrence.

2. **Zero-defect rational-prime rigidity and quantitative `L¹` defect lower bounds**
   (`beurling_intNorm_eq_round_and_primes_of_zero_defect`,
   `critical_line_defect_gt_of_not_prime_equiv`,
   `critical_line_defect_ge_of_prime_dist_gt`,
   `critical_line_defect_ge_of_intNorm_dist_gt`):
   In any countable Beurling system `B` satisfying an approximate Riemann functional equation on
   `Re s = 1/2` with integrable defect `g`, vanishing `L¹` defect `∫ ‖g‖ = 0` forces every
   generalized integer norm to be a positive integer and every Beurling prime norm to match the
   rational primes bijectively; conversely, any prime-count mismatch below `N − 3/2`, any prime
   displacement `> δ`, or any relative integer-lattice displacement `> η` forces an explicit
   strictly positive lower bound on `∫ ‖g(t)‖ dt`.
-/

open Complex MeasureTheory Filter Topology Set Function
open GaloisForLFunctions.HTGeometry RHTower.BeurlingOverRegularIntegers

namespace GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

/-! ### 1. Complete zero classification and one-off non-recurrence of `overRegularZeta` -/

/-- **Complete zero classification of `overRegularZeta` right of `−(3μ − 1 − ν)`.**
Away from the simple pole at `s = 1`, `overRegularZeta μ ν γ` vanishes in
`Re s > −(3μ − 1 − ν)` if and only if `s = (1 − μ) ± iγ` or `s = −(4μ − 1)`. -/
theorem overRegularZeta_eq_zero_iff {μ ν γ : ℝ} (hν : 0 ≤ ν) {s : ℂ}
    (hs : -(3 * μ - 1 - ν) < s.re) (hne : s ≠ 1) :
    overRegularZeta μ ν γ s = 0 ↔
      s = ((1 - μ : ℝ) : ℂ) + (γ : ℂ) * I ∨
        s = ((1 - μ : ℝ) : ℂ) - (γ : ℂ) * I ∨
        s = -((4 * μ - 1 : ℝ) : ℂ) := by
  have hden : (s - 1) * (s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν)) ≠ 0 :=
    overRegularZeta_denom_ne_zero hν hs hne
  have hfac1 : (s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 =
      (s - (((1 - μ : ℝ) : ℂ) + (γ : ℂ) * I)) *
        (s - (((1 - μ : ℝ) : ℂ) - (γ : ℂ) * I)) := by
    push_cast
    linear_combination ((γ : ℂ) ^ 2) * Complex.I_sq
  have hfac2 : s + (4 * μ - 1) = s - (-((4 * μ - 1 : ℝ) : ℂ)) := by
    push_cast; ring
  unfold overRegularZeta
  rw [div_eq_zero_iff, or_iff_left hden, hfac1, hfac2, mul_eq_zero, mul_eq_zero,
    sub_eq_zero, sub_eq_zero, sub_eq_zero, or_assoc]

/-- `overRegularZeta` also vanishes at the conjugate off-line zero `(1 − μ) − iγ`. -/
theorem overRegularZeta_eq_zero_conj (μ ν γ : ℝ) :
    overRegularZeta μ ν γ (((1 - μ : ℝ) : ℂ) - (γ : ℂ) * I) = 0 := by
  have hnum : ((((1 - μ : ℝ) : ℂ) - (γ : ℂ) * I) - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
    push_cast
    linear_combination ((γ : ℂ) ^ 2) * Complex.I_sq
  rw [overRegularZeta, hnum, zero_mul, zero_div]

/-- **Exact finite one-off right-half-plane zero set.** For `μ < 1/2`, `0 < ν < 3μ − 1`, and every
`h ∈ [0, 1/2 − μ)`, the pole-free zero set of `overRegularZeta μ ν γ` in `Re s > 1/2 + h` is
precisely the two-point conjugate pair `{(1 − μ) + iγ, (1 − μ) − iγ}` (finitely many zeros right of
`1/2 + h`, yet nonempty, violating the asymptotic abscissa law). -/
theorem overRegularZeta_right_zeroSet_eq_pair {μ ν γ : ℝ}
    (hν0 : 0 < ν) (hν1 : ν < 3 * μ - 1)
    {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1 / 2 - μ) :
    {s : ℂ | 1 / 2 + h < s.re ∧ s ≠ 1 ∧ overRegularZeta μ ν γ s = 0} =
      {((1 - μ : ℝ) : ℂ) + (γ : ℂ) * I, ((1 - μ : ℝ) : ℂ) - (γ : ℂ) * I} := by
  ext s
  simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hs_re, hs_ne1, hzero⟩
    have hs_dom : -(3 * μ - 1 - ν) < s.re := by linarith
    rcases (overRegularZeta_eq_zero_iff hν0.le hs_dom hs_ne1).mp hzero with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso
      have hre := congrArg Complex.re h3
      simp only [Complex.neg_re, Complex.ofReal_re] at hre
      linarith
  · rintro (rfl | rfl)
    · refine ⟨?_, ?_, overRegularZeta_eq_zero μ ν γ⟩
      · simp; linarith
      · intro hc
        have hre := congrArg Complex.re hc
        simp at hre
        linarith
    · refine ⟨?_, ?_, overRegularZeta_eq_zero_conj μ ν γ⟩
      · simp; linarith
      · intro hc
        have hre := congrArg Complex.re hc
        simp at hre
        linarith

/-- Decay of `c / (a + t I)` as `t → +∞` (`c, a ∈ ℂ`). -/
private theorem tendsto_const_div_add_mul_I_atTop (c a : ℂ) :
    Tendsto (fun t : ℝ => c / (a + (t : ℂ) * I)) atTop (𝓝 0) := by
  have hbound_lim : Tendsto (fun t : ℝ => ‖c‖ / (t - |a.im|)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (-|a.im|) tendsto_id)
  refine squeeze_zero_norm' ?_ hbound_lim
  filter_upwards [eventually_gt_atTop (|a.im| + 1)] with t ht
  rw [norm_div]
  have him_le : t - |a.im| ≤ ‖a + (t : ℂ) * I‖ := by
    have h1 : |(a + (t : ℂ) * I).im| ≤ ‖a + (t : ℂ) * I‖ := Complex.abs_im_le_norm _
    have h2 : (a + (t : ℂ) * I).im = a.im + t := by simp
    rw [h2] at h1
    have h3 : -|a.im| ≤ a.im := neg_abs_le a.im
    have h4 : t - |a.im| ≤ |a.im + t| := (by linarith : t - |a.im| ≤ a.im + t).trans (le_abs_self _)
    exact h4.trans h1
  exact div_le_div_of_nonneg_left (norm_nonneg c) (by linarith) him_le

/-- **Vertical high-ordinate limit (`t → +∞`).** On every vertical line `Re s = σ`,
`overRegularZeta μ ν γ (σ + i t) → 1` as `t → +∞`. -/
theorem tendsto_overRegularZeta_im_atTop {μ ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 3 * μ - 1)
    (γ σ : ℝ) :
    Tendsto (fun t : ℝ => overRegularZeta μ ν γ ((σ : ℂ) + (t : ℂ) * I)) atTop (𝓝 1) := by
  have hν_ne : ν ≠ 0 := hν0.ne'
  have h₁ : 3 * μ - ν ≠ 0 := by linarith
  have h₂ : 3 * μ + ν ≠ 0 := by linarith
  set f : ℝ → ℂ := fun t =>
    1 + (rho μ ν γ : ℂ) / (((σ : ℂ) - 1) + (t : ℂ) * I) +
      (lowResidue μ ν γ : ℂ) / (((σ : ℂ) + (3 * μ - 1 - ν)) + (t : ℂ) * I) +
      (highResidue μ ν γ : ℂ) / (((σ : ℂ) + (3 * μ - 1 + ν)) + (t : ℂ) * I)
  have hf_lim : Tendsto f atTop (𝓝 1) := by
    have t1 := tendsto_const_div_add_mul_I_atTop (rho μ ν γ : ℂ) ((σ : ℂ) - 1)
    have t2 := tendsto_const_div_add_mul_I_atTop (lowResidue μ ν γ : ℂ)
      ((σ : ℂ) + (3 * μ - 1 - ν))
    have t3 := tendsto_const_div_add_mul_I_atTop (highResidue μ ν γ : ℂ)
      ((σ : ℂ) + (3 * μ - 1 + ν))
    simpa [f] using ((tendsto_const_nhds.add t1).add t2).add t3
  refine hf_lim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ne_of_im : ∀ z : ℂ, z.im = t → z ≠ 0 := fun z hz h0 => by
    rw [h0, Complex.zero_im] at hz
    linarith
  have hs1 : (σ : ℂ) + (t : ℂ) * I - 1 ≠ 0 := ne_of_im _ (by simp)
  have hsl : (σ : ℂ) + (t : ℂ) * I + (3 * μ - 1 - ν) ≠ 0 := ne_of_im _ (by simp)
  have hsh : (σ : ℂ) + (t : ℂ) * I + (3 * μ - 1 + ν) ≠ 0 := ne_of_im _ (by simp)
  rw [overRegularZeta_eq_partialFractions hν_ne h₁ h₂ hs1 hsl hsh]
  simp only [f]
  congr 1; congr 1; congr 1 <;> congr 1 <;> ring

/-- **Vertical high-ordinate limit (`t → −∞`).** On every vertical line `Re s = σ`,
`overRegularZeta μ ν γ (σ + i t) → 1` as `t → −∞`. -/
theorem tendsto_overRegularZeta_im_atBot {μ ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 3 * μ - 1)
    (γ σ : ℝ) :
    Tendsto (fun t : ℝ => overRegularZeta μ ν γ ((σ : ℂ) + (t : ℂ) * I)) atBot (𝓝 1) := by
  have hν_ne : ν ≠ 0 := hν0.ne'
  have h₁ : 3 * μ - ν ≠ 0 := by linarith
  have h₂ : 3 * μ + ν ≠ 0 := by linarith
  have hneg_top : Tendsto (fun u : ℝ => overRegularZeta μ ν γ ((σ : ℂ) - (u : ℂ) * I))
      atTop (𝓝 1) := by
    have hconj_lim : Tendsto
        (fun u : ℝ => starRingEnd ℂ (overRegularZeta μ ν γ ((σ : ℂ) + (u : ℂ) * I)))
        atTop (𝓝 (starRingEnd ℂ 1)) :=
      (Complex.continuous_conj.tendsto 1).comp (tendsto_overRegularZeta_im_atTop hν0 hν1 γ σ)
    rw [map_one] at hconj_lim
    refine hconj_lim.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have ne_pos : ∀ z : ℂ, z.im = u → z ≠ 0 := fun z hz h0 => by
      rw [h0, Complex.zero_im] at hz; linarith
    have ne_neg : ∀ z : ℂ, z.im = -u → z ≠ 0 := fun z hz h0 => by
      rw [h0, Complex.zero_im] at hz; linarith
    rw [overRegularZeta_eq_partialFractions hν_ne h₁ h₂
          (ne_pos _ (by simp)) (ne_pos _ (by simp)) (ne_pos _ (by simp)),
      overRegularZeta_eq_partialFractions hν_ne h₁ h₂
          (ne_neg _ (by simp)) (ne_neg _ (by simp)) (ne_neg _ (by simp))]
    simp only [map_add, map_div₀, map_sub, map_mul, map_one, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  refine (hneg_top.comp tendsto_neg_atBot_atTop).congr fun t => ?_
  simp only [Function.comp_apply, Complex.ofReal_neg, neg_mul, sub_neg_eq_add]

/-- **Refutation of weak zero-disc recurrence for `overRegularZeta`.** At the off-line zero
`ρ₀ = (1 − μ) + iγ`, vertical translates stay at uniform distance `≥ 1/2` from `ζ_B(ρ₀) = 0` for
all sufficiently large `|τ|`, so no return shift exists beyond that height for `ε ≤ 1/2`. -/
theorem not_weakRecurrence_overRegularZeta {μ ν : ℝ} (hν0 : 0 < ν) (hν1 : ν < 3 * μ - 1)
    (γ : ℝ) :
    let ρ₀ : ℂ := ((1 - μ : ℝ) : ℂ) + (γ : ℂ) * I
    (∃ T₀ : ℝ, 0 < T₀ ∧ ∀ τ : ℝ, T₀ ≤ |τ| →
      (1 / 2 : ℝ) ≤ ‖overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I) - overRegularZeta μ ν γ ρ₀‖) ∧
    ¬ (∀ ε > (0 : ℝ), ∀ T₀ : ℝ, ∃ τ : ℝ, T₀ ≤ τ ∧
      ‖overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I) - overRegularZeta μ ν γ ρ₀‖ < ε) := by
  intro ρ₀
  have hρ₀ : overRegularZeta μ ν γ ρ₀ = 0 := overRegularZeta_eq_zero μ ν γ
  have hshift_eq : ∀ τ : ℝ, ρ₀ + (τ : ℂ) * I = ((1 - μ : ℝ) : ℂ) + ((γ + τ : ℝ) : ℂ) * I := by
    intro τ; simp only [ρ₀]; push_cast; ring
  have htop : Tendsto (fun τ : ℝ => overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I)) atTop (𝓝 1) := by
    simp_rw [hshift_eq]
    exact (tendsto_overRegularZeta_im_atTop hν0 hν1 γ (1 - μ)).comp
      (tendsto_const_nhds.add_atTop tendsto_id)
  have hbot : Tendsto (fun τ : ℝ => overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I)) atBot (𝓝 1) := by
    simp_rw [hshift_eq]
    exact (tendsto_overRegularZeta_im_atBot hν0 hν1 γ (1 - μ)).comp
      (tendsto_const_nhds.add_atBot tendsto_id)
  have hev_top := htop.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  have hev_bot := hbot.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp hev_top
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atBot.mp hev_bot
  set T₀ : ℝ := max (max T₁ (-T₂)) 1
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ τ : ℝ, T₀ ≤ |τ| →
      (1 / 2 : ℝ) ≤ ‖overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I) - overRegularZeta μ ν γ ρ₀‖ := by
    intro τ hτ
    rw [hρ₀, sub_zero]
    have hball : dist (overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I)) 1 < 1 / 2 := by
      rcases le_abs.mp hτ with hge | hle
      · exact hT₁ τ ((le_trans (le_max_left T₁ (-T₂)) (le_max_left _ 1)).trans hge)
      · exact hT₂ τ (by
          have : max T₁ (-T₂) ≤ -τ := (le_max_left _ 1).trans hle
          have : -T₂ ≤ -τ := (le_max_right T₁ (-T₂)).trans this
          linarith)
    rw [dist_eq_norm, norm_sub_rev] at hball
    have htri : (1 : ℝ) - ‖overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I)‖ ≤
        ‖(1 : ℂ) - overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I)‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) (overRegularZeta μ ν γ (ρ₀ + (τ : ℂ) * I))
    linarith
  refine ⟨⟨T₀, hT₀_pos, hbound⟩, fun hrec => ?_⟩
  obtain ⟨τ, hτ_ge, hτ_lt⟩ := hrec (1 / 2) (by norm_num) T₀
  have hτ_abs : T₀ ≤ |τ| := hτ_ge.trans (le_abs_self τ)
  linarith [hbound τ hτ_abs]

/-! ### 2. Zero-defect rational-prime rigidity and quantitative `L¹` defect lower bounds -/

section CriticalLineDefectTradeoff

variable (B : RHTower.BeurlingSystem) [Countable B.Label]
  (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
  {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
  (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
  (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
  (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
  (hR : ∀ s : ℂ, s.re = 3 / 2 →
    Complex.Gammaℝ s * beurlingZeta B s = E s + β * Complex.Gammaℝ (s - 1))
  (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
    -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
  (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng) (hgi : Integrable g)
include hBsum hEc hEd hdecay hR hC hgm hgb hgi

/-- **Zero-defect rational-prime rigidity.** When `∫ ‖g(t)‖ dt = 0`, every generalized integer has
exact integer norm `B.intNorm x = round (B.intNorm x)`, every positive integer `m ≥ 1` is the norm
of a unique generalized integer, and for every `N ≥ 4` the Beurling primes of norm `< N − 3/2` are
in exact norm-preserving bijection with the rational primes `≤ N − 2`. -/
theorem beurling_intNorm_eq_round_and_primes_of_zero_defect
    (hzero : ∫ t, ‖g t‖ = 0) :
    (∀ x : B.Integer, B.intNorm x = (round (B.intNorm x) : ℝ)) ∧
    (∀ m : ℕ, 1 ≤ m → ∃! x : B.Integer, B.intNorm x = (m : ℝ)) ∧
    (∀ N : ℕ, 4 ≤ N →
      Nonempty {e : {p : B.Label // B.labelNorm p < N - 3 / 2} ≃ {q : ℕ // q.Prime ∧ q + 2 ≤ N} //
        ∀ p, B.labelNorm p.1 = ((e p : ℕ) : ℝ)}) := by
  have h4 := beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC hgm hgb hgi
    (N := 4) (by norm_num) (by rw [hzero]; norm_num)
  have hint_eq : ∀ x : B.Integer, B.intNorm x = (round (B.intNorm x) : ℝ) := fun x => by
    have hx := h4.1 x
    rw [hzero, mul_zero, Real.sqrt_zero, zero_mul] at hx
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hx)
  refine ⟨hint_eq, ?_, ?_⟩
  · intro m hm
    set N : ℕ := max 4 (m + 2)
    have hN4 : 4 ≤ N := le_max_left 4 (m + 2)
    have hmN : m + 2 ≤ N := le_max_right 4 (m + 2)
    have hN := beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC hgm hgb hgi
      hN4 (by rw [hzero]; norm_num)
    obtain ⟨x₀, hx₀, huniq⟩ := hN.2.1 m hm hmN
    have hx₀_eq : B.intNorm x₀ = (m : ℝ) := by
      have hr : round (B.intNorm x₀) = (m : ℤ) := by
        apply int_eq_of_abs_sub_lt_one
        rw [← hint_eq x₀, Int.cast_natCast]
        linarith
      rw [hint_eq x₀, hr, Int.cast_natCast]
    refine ⟨x₀, hx₀_eq, fun y hy => huniq y ?_⟩
    rw [hy, sub_self, abs_zero]
    norm_num
  · intro N hN
    have hN_res := beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC hgm hgb hgi
      hN (by rw [hzero]; norm_num)
    obtain ⟨e, he⟩ := hN_res.2.2
    refine ⟨⟨e, fun p => ?_⟩⟩
    have hp := he p
    rw [hzero, mul_zero, Real.sqrt_zero, zero_mul] at hp
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hp)

/-- **Quantitative `L¹` defect lower bound from prime-count mismatch.** If `N ≥ 4` and the Beurling
primes of norm `< N − 3/2` are not in bijection with the rational primes `≤ N − 2`, then
`∫ ‖g(t)‖ dt > 1 / (400 N²)`. -/
theorem critical_line_defect_gt_of_not_prime_equiv {N : ℕ} (hN : 4 ≤ N)
    (hnequiv : ¬ Nonempty
      ({p : B.Label // B.labelNorm p < N - 3 / 2} ≃ {q : ℕ // q.Prime ∧ q + 2 ≤ N})) :
    1 / (400 * (N : ℝ) ^ 2) < ∫ t, ‖g t‖ := by
  by_contra hle
  push Not at hle
  have hN_pos : (0 : ℝ) < 400 * (N : ℝ) ^ 2 := by
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  have hsmall : 400 * (N : ℝ) ^ 2 * ∫ t, ‖g t‖ ≤ 1 := by
    rwa [div_le_iff₀ hN_pos, mul_comm] at hle
  obtain ⟨_, _, ⟨e, _⟩⟩ :=
    beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC hgm hgb hgi hN hsmall
  exact hnequiv ⟨e⟩

/-- **Quantitative `L¹` defect lower bound from a displaced Beurling prime.** If `N ≥ 4` and some
Beurling prime `p₀` of norm `< N − 3/2` lies at distance `> δ` (`δ ≥ 0`) from every rational prime
`q ≤ N − 2`, then `∫ ‖g(t)‖ dt ≥ min (1 / (400 N²)) (2 δ² / (3 π N²))`. -/
theorem critical_line_defect_ge_of_prime_dist_gt {N : ℕ} (hN : 4 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ)
    {p₀ : B.Label} (hp₀ : B.labelNorm p₀ < N - 3 / 2)
    (hdist : ∀ q : ℕ, q.Prime → q + 2 ≤ N → δ < |B.labelNorm p₀ - (q : ℝ)|) :
    min (1 / (400 * (N : ℝ) ^ 2)) (2 * δ ^ 2 / (3 * Real.pi * (N : ℝ) ^ 2)) ≤ ∫ t, ‖g t‖ := by
  set M : ℝ := ∫ t, ‖g t‖
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hsmall : 400 * (N : ℝ) ^ 2 * M ≤ 1
  · obtain ⟨_, _, ⟨e, he⟩⟩ :=
      beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC hgm hgb hgi hN hsmall
    set q₀ := e ⟨p₀, hp₀⟩
    have hlt : δ < Real.sqrt (3 * Real.pi / 2 * M) * (N : ℝ) :=
      (hdist q₀.1 q₀.2.1 q₀.2.2).trans_le (he ⟨p₀, hp₀⟩)
    have hsq : δ ^ 2 ≤ 3 * Real.pi / 2 * M * (N : ℝ) ^ 2 := by
      have h1 : δ ^ 2 ≤ (Real.sqrt (3 * Real.pi / 2 * M) * (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hδ hlt.le 2
      rwa [mul_pow, Real.sq_sqrt (by positivity)] at h1
    have hbound : 2 * δ ^ 2 / (3 * Real.pi * (N : ℝ) ^ 2) ≤ M := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact (min_le_right _ _).trans hbound
  · push Not at hsmall
    have hbound : 1 / (400 * (N : ℝ) ^ 2) ≤ M := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact (min_le_left _ _).trans hbound

/-- **Quantitative `L¹` defect lower bound from an off-lattice generalized integer.** If some
generalized integer `x₀` satisfies `|B.intNorm x₀ − round (B.intNorm x₀)| > η · B.intNorm x₀`
(`η ≥ 0`), then `∫ ‖g(t)‖ dt ≥ min (1 / 6400) (2 η² / (3 π))`. -/
theorem critical_line_defect_ge_of_intNorm_dist_gt {η : ℝ} (hη : 0 ≤ η)
    {x₀ : B.Integer} (hx₀ : η * B.intNorm x₀ < |B.intNorm x₀ - round (B.intNorm x₀)|) :
    min (1 / 6400) (2 * η ^ 2 / (3 * Real.pi)) ≤ ∫ t, ‖g t‖ := by
  set M : ℝ := ∫ t, ‖g t‖
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hpi : 0 < Real.pi := Real.pi_pos
  by_cases hsmall : 400 * (4 : ℝ) ^ 2 * M ≤ 1
  · obtain ⟨hnear, _, _⟩ :=
      beurling_primes_of_critical_line_defect B hBsum hEc hEd hdecay hR hC hgm hgb hgi
        (N := 4) (by norm_num) hsmall
    have hlt_mul : η * B.intNorm x₀ < Real.sqrt (3 * Real.pi / 2 * M) * B.intNorm x₀ :=
      hx₀.trans_le (hnear x₀)
    have hlt : η < Real.sqrt (3 * Real.pi / 2 * M) :=
      lt_of_mul_lt_mul_right hlt_mul (B.intNorm_pos x₀).le
    have hsq : η ^ 2 ≤ 3 * Real.pi / 2 * M := by
      have h1 : η ^ 2 ≤ Real.sqrt (3 * Real.pi / 2 * M) ^ 2 := pow_le_pow_left₀ hη hlt.le 2
      rwa [Real.sq_sqrt (by positivity)] at h1
    have hbound : 2 * η ^ 2 / (3 * Real.pi) ≤ M := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    exact (min_le_right _ _).trans hbound
  · push Not at hsmall
    have hbound : (1 / 6400 : ℝ) ≤ M := by linarith
    exact (min_le_left _ _).trans hbound

end CriticalLineDefectTradeoff

end

end GaloisForLFunctions.ArithmeticPositiveDuality
