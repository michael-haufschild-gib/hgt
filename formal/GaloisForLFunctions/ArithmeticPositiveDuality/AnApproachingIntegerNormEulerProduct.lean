import GaloisForLFunctions.ArithmeticPositiveDuality.ATwoScaleIntegerNormOneOff
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheLandingLaw

/-!
# An integer-norm Euler product whose remainder approaches the line without landing

Feed the wave construction (`WaveSpec`) a remainder sequence `½ < θ_n ≤ θ_max` with `θ_n → ½`.
The result is a convergent Euler product `∏_k (1 - q_k^{-s})^{-1} = ∑_n a_n n^{-s}` with natural
norms `q_k ≥ 2`, natural coefficients, linear counting and zero-free continuation across
`Re s = ½`, whose strip configuration has

* the top pair `β ± iγ` (`zeroAbscissa Z = β`),
* infinitely many zeros `θ_n ± iω_n` right of the line, approaching it (`ApproachesLine Z`),

so the landing law `ZAL ⇒ FiniteOffLine` fails (`exists_approaching_integer_norm_euler_product`).
The configuration lies in the sector `B13 ∧ ¬B138 ∧ DH`: the finite stratum holds vacuously and
the asymptotic Deuring–Heilbronn law holds because the zeros approach the line. Together with the
integer-norm one-off (`¬B13`) and the two-scale product (`¬DH`), each atom of the abscissa law fails
alone on positive integer-norm Euler products: none of them follows without the functional
equation.
-/

open Set Filter Topology Complex
open Zeta23
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
open GaloisForLFunctions.ArithmeticPositiveDuality.TwoScaleIntegerNormOneOff

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.ApproachingIntegerNormEulerProduct

/-- **An integer-norm Euler product violating the landing law.** For every remainder sequence
`½ < θ_n ≤ θ_max < β < 2/3` with `θ_n → ½` and every height `γ > 0`, there is a convergent Euler
product with natural norms, natural coefficients, linear counting and zero-free continuation across
`Re s = ½`, whose strip configuration `Z` has abscissa `β`, top layer `β ± iγ`, approaches the
line, and has infinitely many zeros off it. -/
theorem exists_approaching_integer_norm_euler_product
    {θmax β γ : ℝ} {θSeq : ℕ → ℝ} (hhalf : ∀ n, 1 / 2 < θSeq n) (hle : ∀ n, θSeq n ≤ θmax)
    (hβ : θmax < β) (h23 : β < 2 / 3) (hγ : 0 < γ) (hlim : Tendsto θSeq atTop (𝓝 (1 / 2))) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧ ∃ Z : ZeroConfig,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
      {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re} ∧
      {s ∈ Z.carrier | 1 / 2 < s.re ∧ |s.im| ≤ γ} =
        {(β : ℂ) + (γ : ℂ) * I, (β : ℂ) - (γ : ℂ) * I} ∧
      zeroAbscissa Z = β ∧
      ApproachesLine Z ∧
      (rightOf Z 0).Infinite ∧
      ¬ LandingLaw Z ∧
      AbscissaLawAt Z 0 ∧
      (¬ AbscissaLaw Z → ApproachesLine Z) := by
  let S : WaveSpec := ⟨θmax, β, γ, θSeq, hhalf, hle, hβ, h23, hγ⟩
  obtain ⟨q, a, hq, F, A, hA, hEuler, hcount, hdiff, hcrit, hright⟩ :=
    S.exists_integer_norm_euler_product
  have hZAL : ApproachesLine S.zeroConfig :=
    (approachesLine_iff_asymptoticAbscissa_eq_half _).mpr
      (S.zeroConfig_asymptoticAbscissa_of_tendsto hlim)
  have hinf := S.zeroConfig_rightOf_zero_infinite
  exact ⟨q, a, hq, F, A, hA, S.zeroConfig, hEuler, hcount, hdiff, hcrit, hright,
    S.zeroConfig_top_layer, S.zeroConfig_zeroAbscissa, hZAL, hinf, fun hL => hinf (hL hZAL),
    fun hfin => absurd hfin hinf, fun _ => hZAL⟩

/-- A concrete instance: `θ_n = ½ + 1/(20(n + 1))`, `β = 3/5`, `γ = 1`. -/
theorem exists_integer_norm_euler_product_not_landingLaw :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ, ∃ A : ℝ, 0 < A ∧ ∃ Z : ZeroConfig,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, (a n : ℝ)) / N) atTop (𝓝 A) ∧
      DifferentiableOn ℂ F {s : ℂ | 1 / 3 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, s.re = 1 / 2 → F s ≠ 0) ∧
      {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ F s = 0} = {s ∈ Z.carrier | 1 / 2 < s.re} ∧
      ApproachesLine Z ∧ ¬ LandingLaw Z := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / (20 * ((n : ℝ) + 1)) := fun n => by positivity
  have hle : ∀ n : ℕ, 1 / (20 * ((n : ℝ) + 1)) ≤ 1 / 20 := fun n =>
    one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlim : Tendsto (fun n : ℕ => 1 / 2 + 1 / (20 * ((n : ℝ) + 1))) atTop (𝓝 (1 / 2)) := by
    have h : Tendsto (fun n : ℕ => 20 * ((n : ℝ) + 1)) atTop atTop :=
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
        (by norm_num)
    have h0 := h.inv_tendsto_atTop.const_add (1 / 2 : ℝ)
    rw [add_zero] at h0
    exact h0.congr fun n => by simp only [Pi.inv_apply, one_div]
  obtain ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright, -, -, hZAL, -, hnot, -⟩ :=
    exists_approaching_integer_norm_euler_product (θmax := 11 / 20) (β := 3 / 5) (γ := 1)
      (fun n => by linarith [hpos n]) (fun n => by linarith [hle n]) (by norm_num) (by norm_num)
      one_pos hlim
  exact ⟨q, a, hq, F, A, hA, Z, hEuler, hcount, hdiff, hcrit, hright, hZAL, hnot⟩

end GaloisForLFunctions.ArithmeticPositiveDuality.ApproachingIntegerNormEulerProduct
