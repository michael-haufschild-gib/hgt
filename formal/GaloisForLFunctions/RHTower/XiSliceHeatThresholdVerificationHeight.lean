import GaloisForLFunctions.RHTower.XiSliceHeatEffectiveKKL
import GaloisForLFunctions.RHTower.XiHorizontalSliceConeCriterion
import GaloisForLFunctions.RHTower.XiSliceFiniteOrderReduction

/-!
# The WD heat threshold is controlled by the height up to which RH holds

**Theorem** (`wdHeatThreshold_le_of_zeros_on_line_below`).  There is `H₀` such that, whenever every
zero `ρ` of `ξ` with `|Im ρ| ≤ H` lies on the critical line and `H ≥ H₀`,

  `λ_WD ≤ 100 / log(H − ½)`.

**Corollary** (`exists_offLine_zero_below_of_wdHeatThreshold_pos`).  If `λ_WD > 0` (equivalently,
RH fails), some zero off the critical line has `|Im ρ| ≤ max(H₀, e^{100/λ_WD} + 1)`: the first
counterexample to RH lies below an explicit function of the WD heat threshold.

Proof.  Let `λ = 100/log(H − ½)`.
* At heights `|t| ≥ H − ½` every even heated coefficient is positive by the effective slice
  Ki–Kim–Lee theorem (`exists_xiSliceHeatTransfer_pos_heat_over_log`), and the odd ones vanish.
* At heights `|t| < H − ½` every zero satisfies the cone condition `|Re ρ − ½| ≤ |Im ρ − t|`:
  the zeros with `|Im ρ| ≤ H` are on the line, and the others have `|Im ρ − t| > ½ > |Re ρ − ½|`.
  So the unheated slice has nonnegative Taylor coefficients (`nonnegTaylorAtZero_xiSliceProduct_of_cone`),
  and the heat series `T_n = Σ_k w_k c_{n+2k}` with `w_k ≥ 0` keeps them nonnegative.
Hence `λ` is admissible.
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-- Nonnegative unheated slice coefficients give nonnegative heated ones. -/
theorem xiSliceHeatTransfer_nonneg_of_coeff_nonneg {lam : ℝ} (hlam : 0 ≤ lam) {t : ℝ}
    (hc : ∀ n : ℕ, 0 ≤ xiSliceCoeff t n) (n : ℕ) : 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam 0 t n
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hterm : ∀ k : ℕ, 0 ≤ ((((lam / 2) ^ k / k.factorial *
      ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) * xiSliceCoeff t (n + 2 * k)) := fun k =>
    mul_nonneg (Complex.zero_le_real.mpr (by positivity)) (hc _)
  exact le_trans (hterm 0) (le_hasSum hT 0 fun j _ => hterm j)

/-- **Verification height bound.**  If RH holds up to height `H ≥ H₀`, then
`λ_WD ≤ 100 / log(H − ½)`. -/
theorem wdHeatThreshold_le_of_zeros_on_line_below :
    ∃ H₀ : ℝ, 200 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      (∀ ρ : ℂ, xi ρ = 0 → |ρ.im| ≤ H → ρ.re = 1 / 2) →
        wdHeatThreshold ≤ 100 / Real.log (H - 1 / 2) := by
  obtain ⟨t₀, ht₀, hkkl⟩ := exists_xiSliceHeatTransfer_pos_heat_over_log
  refine ⟨t₀ + 1, by linarith, fun H hH hRH => ?_⟩
  have hH2 : t₀ ≤ H - 1 / 2 := by linarith
  have hlogH : 0 < Real.log (H - 1 / 2) := Real.log_pos (by linarith)
  have hlam0 : 0 ≤ 100 / Real.log (H - 1 / 2) := by positivity
  refine csInf_le wdHeatAdmissible_bddBelow fun t n => ?_
  by_cases ht : H - 1 / 2 ≤ |t|
  · -- large heights: effective Ki–Kim–Lee
    have hlog : Real.log (H - 1 / 2) ≤ Real.log |t| := Real.log_le_log (by linarith) ht
    have hle : 100 / Real.log |t| ≤ 100 / Real.log (H - 1 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) hlogH hlog
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [← two_mul]
      exact (hkkl t (le_trans hH2 ht) _ hle m).le
    · rw [xiSliceHeatTransfer_odd_eq_zero hlam0]
  · -- low heights: the cone criterion with RH up to `H`
    push Not at ht
    have hcone : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).im - t| := by
      intro q
      have hz := xi_eq_zero_of_mem_divisor_support q.1
      by_cases hq : |(q.1 : ℂ).im| ≤ H
      · rw [hRH _ hz hq, sub_self, abs_zero]
        exact abs_nonneg _
      · push Not at hq
        have hstrip := xiZeroCopy_re_mem_open_unit q
        have h1 : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 := by
          rw [abs_lt]
          constructor <;> linarith [hstrip.1, hstrip.2]
        have h2 : 1 / 2 < |(q.1 : ℂ).im - t| := by
          have := abs_sub_abs_le_abs_sub (q.1 : ℂ).im t
          linarith
        linarith
    have hnn := nonnegTaylorAtZero_xiSliceProduct_of_cone hcone
    have hc : ∀ k : ℕ, 0 ≤ xiSliceCoeff t k := by
      intro k
      unfold xiSliceCoeff
      have hf : (0 : ℂ) ≤ (k.factorial : ℂ)⁻¹ := by
        rw [show ((k.factorial : ℂ))⁻¹ = (((k.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl]
        exact Complex.zero_le_real.mpr (by positivity)
      exact mul_nonneg hf (hnn.2 k)
    exact xiSliceHeatTransfer_nonneg_of_coeff_nonneg hlam0 hc n

/-- **The first counterexample lies below `e^{100/λ_WD}`.**  If `λ_WD > 0`, some zero of `ξ` off the
critical line has `|Im ρ| ≤ max(H₀, e^{100/λ_WD} + 1)`. -/
theorem exists_offLine_zero_below_of_wdHeatThreshold_pos :
    ∃ H₀ : ℝ, 200 ≤ H₀ ∧ (0 < wdHeatThreshold →
      ∃ ρ : ℂ, xi ρ = 0 ∧ ρ.re ≠ 1 / 2 ∧
        |ρ.im| ≤ max H₀ (Real.exp (100 / wdHeatThreshold) + 1)) := by
  obtain ⟨H₀, hH₀, h⟩ := wdHeatThreshold_le_of_zeros_on_line_below
  refine ⟨H₀, hH₀, fun hpos => ?_⟩
  set H := max H₀ (Real.exp (100 / wdHeatThreshold) + 1) with hHdef
  by_contra hno
  push Not at hno
  have hRH : ∀ ρ : ℂ, xi ρ = 0 → |ρ.im| ≤ H → ρ.re = 1 / 2 := by
    intro ρ hρ hle
    by_contra hne
    exact absurd (hno ρ hρ hne) (not_lt.mpr hle)
  have hbound := h H (le_max_left _ _) hRH
  have hexp : Real.exp (100 / wdHeatThreshold) < H - 1 / 2 := by
    have := le_max_right H₀ (Real.exp (100 / wdHeatThreshold) + 1)
    linarith
  have hlog : 100 / wdHeatThreshold < Real.log (H - 1 / 2) := by
    rw [← Real.log_exp (100 / wdHeatThreshold)]
    exact Real.log_lt_log (Real.exp_pos _) hexp
  have hlogpos : 0 < Real.log (H - 1 / 2) := lt_trans (by positivity) hlog
  have : 100 / Real.log (H - 1 / 2) < wdHeatThreshold := by
    rw [div_lt_iff₀ hlogpos]
    rw [div_lt_iff₀ hpos] at hlog
    linarith
  linarith

end

end RHTower.DeBruijn
