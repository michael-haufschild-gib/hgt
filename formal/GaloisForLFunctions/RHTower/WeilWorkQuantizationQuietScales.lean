import GaloisForLFunctions.RHTower.WeilWorkQuantizationLocalPhase
import GaloisForLFunctions.RHTower.WeilWorkQuantizationPowerRigidity

/-!
# No arbitrarily late sublinear residual scales

For each actual Weil-positive source, either arithmetic rigidity holds or every
sublinear power is eventually smaller than its integer-floor residual mass.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

/-- A real power of the radius loses to exponential damping at any positive power scale. -/
theorem tendsto_power_exponential_radius (s : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun U : ℝ => U ^ s * Real.exp (-(b * U ^ a))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / a) b hb).comp (tendsto_rpow_atTop ha)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with U hU
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hU]
  have heq : a * (s / a) = s := by field_simp
  simp only [heq, neg_mul]

/-- Positive radial powers tend to zero through positive values. -/
theorem tendsto_radial_power_div {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    Tendsto (fun U : ℝ => U ^ (-q) / r) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa using (tendsto_rpow_neg_atTop hq).div_const r
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    exact div_pos (Real.rpow_pos_of_pos hU _) hr

/-- The radial-power cost times a smaller mass power vanishes. -/
theorem tendsto_radial_power_cost {q r p α : ℝ} (hr : 0 < r) (hgap : α < q * (1 - p)) :
    Tendsto (fun U : ℝ => (U ^ (-q) / r) ^ (1 - p) * U ^ α) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hgap)).div_const (r ^ (1 - p))
  simp only [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
  rw [Real.div_rpow (Real.rpow_nonneg hU.le _) hr.le,
    ← Real.rpow_mul hU.le, div_mul_eq_mul_div, ← Real.rpow_add hU]
  congr 2
  ring

/-- The absolute tail vanishes along every fixed rescaling of a quiet radial power. -/
theorem tendsto_radial_power_tail {q r M : ℝ} (hq : q < 1) (hr : 0 < r) (hM : 0 < M) :
    Tendsto (fun U : ℝ => (U ^ (-q) / r)⁻¹ *
      Real.exp (-((U ^ (-q) / r) * U / M))) atTop (𝓝 0) := by
  have h := (tendsto_power_exponential_radius q (sub_pos.mpr hq)
    (by positivity : 0 < (r * M)⁻¹)).const_mul r
  simp only [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
  have hp : U ^ (-q) * U = U ^ (1 - q) := by
    calc U ^ (-q) * U = U ^ (-q) * U ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = U ^ (1 - q) := by rw [← Real.rpow_add hU]; congr 1; ring
  have hinv : (U ^ (-q) / r)⁻¹ = r * U ^ q := by
    rw [inv_div, Real.rpow_neg hU.le, div_inv_eq_mul]
  have heq : -(U ^ (-q) / r * U / M) = -((r * M)⁻¹ * U ^ (1 - q)) := by
    rw [div_mul_eq_mul_div, hp]
    field_simp
  rw [hinv, heq]
  ring
/-- A power-small cumulative phase along selected radii annihilates each scaled remainder. -/
theorem tendsto_quantization_remainder_quiet_radii {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Monotone C) (hC1 : 0 ≤ C 1) (β : ℝ)
    {ι : Type*} {l : Filter ι} {U : ι → ℝ} (hU : Tendsto U l atTop)
    {α K q p r : ℝ} (hg : ∀ᶠ j in l, C (U j) ≤ K * (U j) ^ α)
    (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hgap : α < q * (1 - p)) (hr : 0 < r) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun j => (((U j) ^ (-q) / r : ℝ) : ℂ) *
      ∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) *
        quantizationRadialRemainder hW m ((((U j) ^ (-q) / r : ℝ) : ℂ) + (m : ℂ) * I) t)
      l (𝓝 0) := by
  obtain ⟨A, D, hA, hD, hb⟩ := exists_quantization_twist_local_bound hW hC β hp0 hp1.le hm
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
      (A * |β| * K) * (e j ^ (1 - p) * (U j) ^ α) +
      D * (e j)⁻¹ * Real.exp (-(e j * U j / ((m : ℝ) + 1)))) l (𝓝 0) := by
    simpa only [mul_zero, zero_add, Function.comp_def, mul_assoc] using
      ((h0.const_mul A).add (h1.const_mul (A * |β| * K))).add (h2.const_mul D)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hg, hU.eventually (eventually_ge_atTop (1 : ℝ)),
    he.eventually (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))] with j hj hUj hej
  refine (hb (e j) (U j) hej.1 hej.2.le hUj).trans ?_
  have hmass : C (U j) - C 1 ≤ K * (U j) ^ α := by linarith
  calc A * e j ^ (1 - p) * (1 + |β| * (C (U j) - C 1)) +
      D * (e j)⁻¹ * Real.exp (-(e j * U j / ((m : ℝ) + 1)))
      ≤ A * e j ^ (1 - p) * (1 + |β| * (K * (U j) ^ α)) +
        D * (e j)⁻¹ * Real.exp (-(e j * U j / ((m : ℝ) + 1))) := by gcongr
    _ = _ := by ring
/-- Arbitrarily late sublinear cumulative-phase scales already force rigidity. -/
theorem quantization_rigidity_of_frequently_cumulative_power {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {α K : ℝ} (hα : α < 1)
    (hf : ∃ᶠ U : ℝ in atTop, quantizationResidualCumulative hW U ≤ K * U ^ α) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  let C := quantizationResidualCumulative hW
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
  exact tendsto_quantization_remainder_quiet_radii hW (monotone_quantizationResidualCumulative hW)
    (by exact ENNReal.toReal_nonneg) (2 * Real.pi) hU hg hq0 hq1 hp0 hp1 hgap hr hm

/-- Intrinsic source alternative: every sublinear power is eventually below cumulative residual mass. -/
theorem quantization_rigidity_or_cumulative_eventual_power {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ α : ℝ, α < 1 → ∀ K : ℝ, ∀ᶠ U : ℝ in atTop,
        K * U ^ α < quantizationResidualCumulative hW U := by
  classical
  by_cases h : (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis
  · exact Or.inl h
  right
  intro α hα K
  by_contra hn
  have hf := not_eventually.mp hn
  simp only [not_lt] at hf
  exact h (quantization_rigidity_of_frequently_cumulative_power hW hα hf)

/-- Failure of rigidity excludes every arbitrarily late sublinear residual-mass scale. -/
theorem quantization_rigidity_or_residual_eventual_power {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      ∀ α : ℝ, α < 1 → ∀ K : ℝ, ∀ᶠ T : ℝ in atTop,
        K * T ^ α < (quantizationResidualMeasure hW).real (Icc (-T) T) := by
  rcases quantization_rigidity_or_cumulative_eventual_power hW with h | h
  · exact Or.inl h
  right
  intro α hα K
  have ht : Tendsto (fun T : ℝ => T / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  filter_upwards [ht.eventually (h α hα (K * 2 ^ α)), eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hfin : quantizationResidualMeasure hW (Icc (-T) T) ≠ ∞ :=
    ne_top_of_le_ne_top (quantization_boundaryMeasure_Icc_ne_top hW (-T) T)
      (quantizationResidualMeasure_le hW _)
  have hmass : quantizationResidualCumulative hW (T / 2) ≤
      (quantizationResidualMeasure hW).real (Icc (-T) T) := by
    unfold quantizationResidualCumulative
    apply ENNReal.toReal_mono hfin (measure_mono ?_)
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hid : (K * 2 ^ α) * (T / 2) ^ α = K * T ^ α := by
    rw [mul_assoc, ← Real.mul_rpow (by norm_num) (by linarith : 0 ≤ T / 2)]
    congr 2
    ring
  rw [hid] at hT
  exact hT.trans_le hmass

end RHTower.WeilSpectral
