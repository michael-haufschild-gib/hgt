import GaloisForLFunctions.RHTower.WeilWorkQuantizationVariationLocal
import GaloisForLFunctions.RHTower.WeilWorkQuantizationQuietScales

/-!
# Intrinsic phase variation: no arbitrarily late sublinear scales

The final source alternative measures the unit-circle path, so integer jumps
are invisible and no real phase lift is charged for them. Arbitrary canonical
spectral measures and radial trace zeros remain in scope.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

/-- A power-small circle-phase variation along selected radii annihilates each scaled remainder. -/
theorem tendsto_quantization_variation_remainder_quiet_radii {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ι : Type*} {l : Filter ι} {U : ι → ℝ} (hU : Tendsto U l atTop)
    {α K q p r : ℝ} (hg : ∀ᶠ j in l, quantizationPhaseVariation hW (U j) ≤ K * (U j) ^ α)
    (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hgap : α < q * (1 - p)) (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun j => (((U j) ^ (-q) / r : ℝ) : ℂ) *
      ∫ t in Iic (-1 : ℝ), quantizationCirclePhase hW (-t) *
        quantizationRadialRemainder hW m ((((U j) ^ (-q) / r : ℝ) : ℂ) + (m : ℂ) * I) t)
      l (𝓝 0) := by
  obtain ⟨A, D, hA, hD, hb⟩ := exists_quantization_variation_local_bound hW hp0 hp1.le hm
  let e : ι → ℝ := fun j => (U j) ^ (-q) / r
  have he : Tendsto e l (𝓝[>] 0) := (tendsto_radial_power_div hq0 hr).comp hU
  have h0 : Tendsto (fun j => e j ^ (1 - p)) l (𝓝 0) := by
    have h := ((Real.continuous_rpow_const (sub_pos.mpr hp1).le).tendsto 0).comp
      (he.mono_right nhdsWithin_le_nhds)
    simpa [Real.zero_rpow (sub_pos.mpr hp1).ne', Function.comp_def] using h
  have h1 := (tendsto_radial_power_cost hr hgap).comp hU
  have h2 := (tendsto_radial_power_tail hq1 hr
    (show (0 : ℝ) < m + 1 by positivity)).comp hU
  have hlim : Tendsto (fun j => A * e j ^ (1 - p) +
      (A * 2 * K) * (e j ^ (1 - p) * (U j) ^ α) +
      D * (e j)⁻¹ * Real.exp (-(e j * U j / ((m : ℝ) + 1)))) l (𝓝 0) := by
    simpa only [mul_zero, zero_add, Function.comp_def, mul_assoc] using
      ((h0.const_mul A).add (h1.const_mul (A * 2 * K))).add (h2.const_mul D)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hg, hU.eventually (eventually_ge_atTop (1 : ℝ)),
    he.eventually (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))] with j hj hUj hej
  refine (hb (e j) (U j) hej.1 hej.2.le hUj).trans ?_
  have hmass : quantizationPhaseVariation hW (U j) - quantizationPhaseVariation hW 1 ≤ K * (U j) ^ α := by
    have h0 := quantizationPhaseVariation_nonneg hW (x := 1) (by norm_num)
    linarith
  calc A * e j ^ (1 - p) * (1 + 2 * (quantizationPhaseVariation hW (U j) - quantizationPhaseVariation hW 1)) +
      D * (e j)⁻¹ * Real.exp (-(e j * U j / ((m : ℝ) + 1)))
      ≤ A * e j ^ (1 - p) * (1 + 2 * (K * (U j) ^ α)) +
        D * (e j)⁻¹ * Real.exp (-(e j * U j / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring
/-- Arbitrarily late sublinear phase-variation scales already force rigidity. -/
theorem quantization_rigidity_of_frequently_phaseVariation_power {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {α K : ℝ} (hα : α < 1)
    (hf : ∃ᶠ U : ℝ in atTop, quantizationPhaseVariation hW U ≤ K * U ^ α) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  let C := quantizationPhaseVariation hW
  let a : ℝ := max α (1 / 2)
  let k : ℝ := |K| + 1
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have ha1 : a < 1 := max_lt hα (by norm_num)
  have hk : 0 < k := by dsimp [k]; positivity
  have hf' : ∃ᶠ U : ℝ in atTop, C U ≤ k * U ^ a := by
    apply (hf.and_eventually (eventually_ge_atTop (1 : ℝ))).mono
    intro U hU
    calc C U ≤ K * U ^ α := hU.1
      _ ≤ k * U ^ α := mul_le_mul_of_nonneg_right
        (by dsimp [k]; linarith [le_abs_self K]) (Real.rpow_nonneg (by linarith [hU.2]) _)
      _ ≤ k * U ^ a := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU.2 (le_max_left _ _)) hk.le
  let l : Filter ℝ := atTop ⊓ 𝓟 {U | C U ≤ k * U ^ a}
  letI : NeBot l := frequently_iff_neBot.mp hf'
  have hU : Tendsto (fun U : ℝ => U) l atTop := tendsto_id.mono_left inf_le_left
  have hg : ∀ᶠ U in l, C U ≤ k * U ^ a :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ h => h)
  let q : ℝ := (a + 1) / 2
  let p : ℝ := (1 - a) / (4 * q)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hp0 : 0 < p := div_pos (sub_pos.mpr ha1) (by positivity)
  have hqp : q * p = (1 - a) / 4 := by dsimp [p]; field_simp
  have hp1 : p < 1 := by dsimp [q] at hqp; nlinarith
  have hgap : a < q * (1 - p) := by dsimp [q] at hqp ⊢; nlinarith
  have he : Tendsto (fun U : ℝ => U ^ (-q)) l (𝓝[>] 0) := by
    simpa only [div_one, Function.comp_def] using (tendsto_radial_power_div hq0 zero_lt_one).comp hU
  apply quantization_rigidity_of_remainder_along hW
    (monotone_quantizationResidualCumulative hW).measurable
    (ae_quantizationReflectedTraceF_cumulative_phase hW) he
  intro m hm r hr
  exact tendsto_quantization_variation_remainder_quiet_radii hW hU hg hq0 hq1 hp0 hp1 hgap hr hm

/-- Intrinsic source alternative: every sublinear power is eventually below circle-phase variation. -/
theorem quantization_rigidity_or_phaseVariation_eventual_power {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ α : ℝ, α < 1 → ∀ K : ℝ, ∀ᶠ U : ℝ in atTop,
        K * U ^ α < quantizationPhaseVariation hW U := by
  classical
  by_cases h : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl h
  right
  intro α hα K
  by_contra hn
  have hf := not_eventually.mp hn
  simp only [not_lt] at hf
  exact h (quantization_rigidity_of_frequently_phaseVariation_power hW hα hf)

end RHTower.WeilSpectral
