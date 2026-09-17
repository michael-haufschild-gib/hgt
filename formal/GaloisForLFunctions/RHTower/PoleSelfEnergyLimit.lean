import GaloisForLFunctions.RHTower.PoleBoundaryLogSharpConstant
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant

/-!
# The archimedean genus: limit and positivity of the pole self-energy

Unconditionally, the diagonal entry of the fixed exponential-pole Weil matrix satisfies

`A(a) e^{−a} → 2 + γ − log 4π = 0.0461…`,

by the exact decomposition of `PoleBoundaryLogSharpConstant`, Mertens' theorem with the Euler
constant, and the prime number theorem with error term.  The constant is positive: `γ > 0.545`
from the fifteenth Euler–Mascheroni partial sum and `log 4π < 2.534` from `π < 3.1416` and the
series for `log(3/2)`.  Hence the pole self-energy is positive for all large apertures.  On paper
the constant is `Σ_ρ 1/(ρ(1−ρ))`, the regularised count of the nontrivial zeros: the archimedean
genus.  No zero data or RH premise enters.
-/

open Filter Topology
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-- The reciprocal Mangoldt error tends to Mertens' constant `−γ`. -/
theorem tendsto_reciprocalMangoldtError :
    Tendsto reciprocalMangoldtError atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hsum : ∀ X : ℝ, (∑ n ∈ Finset.Icc 2 ⌊X⌋₊, vonMangoldt n / n) =
      ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, vonMangoldt n / n := by
    intro X
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      exact ⟨by omega, hn.2⟩
    · intro n hn hn2
      rw [Finset.mem_Icc] at hn hn2
      have : n = 0 ∨ n = 1 := by omega
      rcases this with rfl | rfl
      · simp
      · simp [ArithmeticFunction.vonMangoldt_apply_one]
  have h := tendsto_real_sum_vonMangoldt_div_sub_log.comp Real.tendsto_exp_atTop
  refine h.congr fun t => ?_
  simp only [Function.comp_def, reciprocalMangoldtError, reciprocalMangoldtCumulative, hsum,
    Real.log_exp]

/-- **The archimedean genus limit.** -/
theorem tendsto_poleDiagonalExplicit_div_exp :
    Tendsto (fun a : ℝ => poleDiagonalExplicit a / Real.exp a) atTop (𝓝 poleSharpConstant) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2a : Tendsto (fun a : ℝ => 2 * a) atTop atTop := tendsto_id.const_mul_atTop two_pos
  have hT1 : Tendsto (fun a : ℝ =>
      2 * |reciprocalMangoldtError (2 * a) + Real.eulerMascheroniConstant|) atTop (𝓝 0) := by
    have h := (tendsto_reciprocalMangoldtError.comp h2a).add_const Real.eulerMascheroniConstant
    simp only [Function.comp_def, neg_add_cancel] at h
    have := (h.abs).const_mul 2
    simpa using this
  have hT2 : Tendsto (fun a : ℝ =>
      2 * Real.exp (-(2 * a)) * |Chebyshev.psi (Real.exp (2 * a)) - Real.exp (2 * a)|)
      atTop (𝓝 0) := by
    have h := tendsto_chebyshevError_div.comp (Real.tendsto_exp_atTop.comp h2a)
    have h' := (h.abs).const_mul 2
    simp only [Function.comp_def, abs_zero, mul_zero] at h'
    refine h'.congr fun a => ?_
    simp only [chebyshevError, abs_div, abs_of_pos (Real.exp_pos _), Real.exp_neg]
    ring
  have hT3 : Tendsto (fun a : ℝ => (10 * a + 20) * Real.exp (-(2 * a))) atTop (𝓝 0) := by
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h2a
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2a
    have := (h1.const_mul 5).add (h2.const_mul 20)
    simp only [Function.comp_def, mul_zero, add_zero] at this
    refine this.congr fun a => ?_
    simp only [pow_one]
    ring
  have hsum := (hT1.add hT2).add hT3
  simp only [add_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [eventually_ge_atTop 1] with a ha
  rw [norm_norm, Real.norm_eq_abs]
  exact abs_poleDiagonalExplicit_div_exp_sub_sharp_le ha

/-! ## Positivity of the constant -/

theorem eulerMascheroniConstant_gt : (0.545 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 15
  unfold Real.eulerMascheroniSeq at h
  have hh : ((harmonic 15 : ℚ) : ℝ) = 1195757 / 360360 := by
    norm_num [harmonic_succ, harmonic_zero]
  have hlog : Real.log ((15 : ℕ) + 1 : ℝ) = 4 * Real.log 2 := by
    rw [show ((15 : ℕ) + 1 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [hh, hlog] at h
  have := Real.log_two_lt_d9
  linarith

theorem log_three_halves_lt : Real.log (3 / 2) < (0.4065 : ℝ) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -1 / 2) (by norm_num) 10
  have hs : (∑ i ∈ Finset.range 10, (-1 / 2 : ℝ) ^ (i + 1) / (i + 1)) = -(130777 / 322560) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [hs, show (1 : ℝ) - -1 / 2 = 3 / 2 by norm_num] at h
  have h' := (abs_le.mp h).2
  norm_num at h'
  linarith

theorem log_four_pi_lt : Real.log (4 * Real.pi) < (2.534 : ℝ) := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hl2 := Real.log_two_lt_d9
  have hl32 := log_three_halves_lt
  have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hpi3 : Real.log Real.pi ≤ Real.log 3 + (Real.pi / 3 - 1) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < Real.pi / 3 by positivity)
    have : Real.log Real.pi = Real.log 3 + Real.log (Real.pi / 3) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      ring
    linarith
  have h4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) hpi0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h4]
  linarith

/-- The archimedean genus `2 + γ − log 4π` is positive. -/
theorem poleSharpConstant_pos : 0 < poleSharpConstant := by
  unfold poleSharpConstant
  have := eulerMascheroniConstant_gt
  have := log_four_pi_lt
  linarith

/-- **Unconditional positivity of the pole self-energy for large apertures.** -/
theorem eventually_poleDiagonalExplicit_pos : ∀ᶠ a : ℝ in atTop, 0 < poleDiagonalExplicit a := by
  have h := tendsto_poleDiagonalExplicit_div_exp
  have hev : ∀ᶠ a : ℝ in atTop, poleSharpConstant / 2 < poleDiagonalExplicit a / Real.exp a :=
    h.eventually (lt_mem_nhds (by linarith [poleSharpConstant_pos]))
  filter_upwards [hev] with a ha
  have hc := poleSharpConstant_pos
  have he := Real.exp_pos a
  have : 0 < poleDiagonalExplicit a / Real.exp a := by linarith
  exact (div_pos_iff_of_pos_right he).mp this

end

end RHTower
