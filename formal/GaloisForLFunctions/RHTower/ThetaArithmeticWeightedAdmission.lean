import GaloisForLFunctions.RHTower.ThetaPowerWeightedSource

/-!
# Sharp power-weighted admission of finite arithmetic theta shifts

For an actual signed finite shift polynomial with positive integer shifts,
the last nonzero coefficient determines its exact `L²(k⁻q dx)` boundary.
Both tails are integrated, and the boundary itself is excluded.
-/

open MeasureTheory Filter Topology Set

namespace RHTower

noncomputable section

/-- The arithmetic terminal shift has exactly the Gaussian exponent `2 / b²`. -/
theorem thetaArithmeticTerminalThreshold_eq (b : ℕ) (hb : 0 < b) :
    2 * Real.exp (-2 * Real.log (b : ℝ)) = 2 / (b : ℝ) ^ 2 := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [show -2 * Real.log (b : ℝ) =
    -(Real.log (b : ℝ) + Real.log (b : ℝ)) by ring,
    Real.exp_neg, Real.exp_add, Real.exp_log hbR]
  ring

/-- Below both cusp thresholds the exact exponential envelope is integrable. -/
theorem integrable_thetaShiftPowerEnvelope (q a : ℝ) (hq : q < 2)
    (ha : q < 2 * Real.exp (-2 * a)) :
    Integrable (thetaShiftPowerEnvelope q a) := by
  have hb : 0 < 9 * (2 - q) / 2 := by linarith
  have hσ : 0 < Real.pi * (2 * Real.exp (-2 * a) - q) := by positivity
  convert (integrable_exp_mul_exp_neg_mul_exp_two_mul hb hσ).const_mul
    (Real.exp (-9 * a)) using 1
  funext x
  rw [thetaShiftPowerEnvelope_eq_exp, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

private theorem integrableOn_tail_of_ratio_tendsto
    (f g : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 < g x) (hg : Integrable g) (L : ℝ)
    (hlim : Tendsto (fun x => f x / g x) atTop (𝓝 L)) :
    ∃ R : ℝ, IntegrableOn f (Ioi R) := by
  have hupper : L < |L| + 1 := by linarith [le_abs_self L]
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hlim.eventually (Iio_mem_nhds hupper))
  refine ⟨R, ((hg.const_mul (|L| + 1)).integrableOn (s := Ioi R)).mono_nonneg
    hf.aestronglyMeasurable (ae_of_all _ hf0) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact ((div_lt_iff₀ (hg0 x)).mp (hR x hx.le)).le

/-- At or beyond the terminal Gaussian threshold the model stays positively bounded below.
This includes the equality case, where the remaining linear exponent cannot give decay. -/
theorem thetaShiftPowerEnvelope_eventually_bounded_below
    (q a : ℝ) (ha : 0 ≤ a) (hq : 2 * Real.exp (-2 * a) ≤ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ x : ℝ in atTop, ε ≤ thetaShiftPowerEnvelope q a x := by
  refine ⟨Real.exp (-9 * a), Real.exp_pos _, ?_⟩
  have hthreshold : 2 * Real.exp (-2 * a) ≤ 2 := by
    have he : Real.exp (-2 * a) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (by linarith : -2 * a ≤ 0)
    linarith
  let B : ℝ := 9 * (2 - q) / 2
  let C : ℝ := Real.pi * (q - 2 * Real.exp (-2 * a))
  have hC0 : 0 ≤ C := mul_nonneg Real.pi_pos.le (by linarith)
  by_cases hq2 : q ≤ 2
  · have hB0 : 0 ≤ B := by dsimp [B]; linarith
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [thetaShiftPowerEnvelope_eq_exp]
    apply Real.exp_le_exp.mpr
    have hlinear := mul_nonneg hB0 hx
    have hgauss := mul_nonneg hC0 (Real.exp_pos (2 * x)).le
    dsimp [B, C] at hlinear hgauss
    linarith
  · have hC : 0 < C := mul_pos Real.pi_pos (by linarith)
    filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (-B / C)] with x hx hxB
    have hBx : 0 ≤ B + C * x := by
      have h := (div_le_iff₀ hC).mp hxB
      nlinarith
    have hpoly := mul_nonneg hBx hx
    have he := Real.quadratic_le_exp_of_nonneg (x := 2 * x) (by linarith)
    have hsq : x ^ 2 ≤ Real.exp (2 * x) := by nlinarith [sq_nonneg x]
    have hgauss := mul_le_mul_of_nonneg_left hsq hC.le
    rw [thetaShiftPowerEnvelope_eq_exp]
    apply Real.exp_le_exp.mpr
    have hsum : 0 ≤ B * x + C * Real.exp (2 * x) := by nlinarith
    dsimp [B, C] at hsum
    linarith

private theorem thetaArithmeticTerminalThreshold_le_two (b : ℕ) (hb : 0 < b) :
    2 / (b : ℝ) ^ 2 ≤ 2 := by
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ 2)).mpr
  nlinarith [sq_nonneg ((b : ℝ) - 1)]

/-- Both literal cusp energies are integrable below the terminal arithmetic threshold. -/
theorem integrable_finiteArithmeticThetaShift_energy
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b)
    (q : ℝ) (hq : q < 2 / (b : ℝ) ^ 2) :
    Integrable (thetaPowerWeightedEnergy q (finiteArithmeticThetaShift D c)) := by
  let E := thetaPowerWeightedEnergy q (finiteArithmeticThetaShift D c)
  have hcont : Continuous E :=
    continuous_thetaPowerWeightedEnergy q (continuous_finiteArithmeticThetaShift D c)
  have hE0 : ∀ x, 0 ≤ E x := thetaPowerWeightedEnergy_nonneg q _
  have hb0 := hpositive b hb
  have hq2 : q < 2 := hq.trans_le (thetaArithmeticTerminalThreshold_le_two b hb0)
  have hnmodel := integrable_thetaShiftPowerEnvelope q (Real.log (b : ℝ)) hq2
    (by rwa [thetaArithmeticTerminalThreshold_eq b hb0])
  have hpmodel := integrable_thetaShiftPowerEnvelope q 0 hq2 (by simpa using hq2)
  have hncont : Continuous (fun x => E (-x)) := by
    simpa only [Function.comp_def] using hcont.comp continuous_neg
  obtain ⟨Rn, hn⟩ := integrableOn_tail_of_ratio_tendsto
    (fun x => E (-x)) (thetaShiftPowerEnvelope q (Real.log (b : ℝ))) hncont
    (fun x => hE0 (-x)) (thetaShiftPowerEnvelope_pos q _) hnmodel _
    (finiteArithmeticThetaShift_negative_energy_ratio D c b hb hpositive hmax q)
  obtain ⟨Rp, hp⟩ := integrableOn_tail_of_ratio_tendsto E (thetaShiftPowerEnvelope q 0)
    hcont hE0 (thetaShiftPowerEnvelope_pos q 0) hpmodel _
    (finiteArithmeticThetaShift_positive_energy_ratio D c hpositive q)
  have hflip : IntegrableOn (fun x => E (-x)) (Ioi Rn) ↔
      IntegrableOn E (Iio (-Rn)) := by
    simpa [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding (f := E) (s := Iio (-Rn))
  have hmiddle : IntegrableOn E (Icc (-Rn) Rp) := hcont.integrableOn_Icc
  have hwhole : IntegrableOn E ((Iio (-Rn) ∪ Icc (-Rn) Rp) ∪ Ioi Rp) :=
    integrableOn_union.mpr ⟨integrableOn_union.mpr ⟨hflip.mp hn, hmiddle⟩, hp⟩
  have hcover : (Iio (-Rn) ∪ Icc (-Rn) Rp) ∪ Ioi Rp = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases hn : x < -Rn
    · exact Or.inl (Or.inl hn)
    · by_cases hp : Rp < x
      · exact Or.inr hp
      · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
  rw [hcover] at hwhole
  exact integrableOn_univ.mp hwhole

/-- A nonzero terminal word fails integrability at the boundary and everywhere above it. -/
theorem not_integrable_finiteArithmeticThetaShift_energy
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b) (hc : c b ≠ 0)
    (q : ℝ) (hq : 2 / (b : ℝ) ^ 2 ≤ q) :
    ¬ Integrable (thetaPowerWeightedEnergy q (finiteArithmeticThetaShift D c)) := by
  let E := thetaPowerWeightedEnergy q (finiteArithmeticThetaShift D c)
  let L := (c b * (4 * Real.pi ^ 2)) ^ 2 * (4 * Real.pi ^ 2) ^ (-q)
  have hc4 : c b * (4 * Real.pi ^ 2) ≠ 0 := mul_ne_zero hc (by positivity)
  have hL : 0 < L := mul_pos (sq_pos_of_ne_zero hc4) (by positivity)
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (show 1 ≤ b from hpositive b hb)
  obtain ⟨ε, hε, hmodel⟩ := thetaShiftPowerEnvelope_eventually_bounded_below
    q (Real.log (b : ℝ)) (Real.log_nonneg hb1)
    (by rwa [thetaArithmeticTerminalThreshold_eq b (hpositive b hb)])
  have hlim := finiteArithmeticThetaShift_negative_energy_ratio D c b hb hpositive hmax q
  have hhalf : L / 2 < L := by linarith
  have hlarge : ∀ᶠ x : ℝ in atTop, ε * (L / 2) ≤ E (-x) := by
    filter_upwards [hlim.eventually (Ioi_mem_nhds hhalf), hmodel] with x hx hm
    have hratio : L / 2 * thetaShiftPowerEnvelope q (Real.log (b : ℝ)) x ≤ E (-x) :=
      (le_div_iff₀ (thetaShiftPowerEnvelope_pos q _ x)).mp hx.le
    have hcompare := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ L / 2)
    nlinarith
  intro hint
  have hn : Integrable (fun x : ℝ => E (-x)) := by
    simpa only [Function.comp_def] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hint
  obtain ⟨R, hR⟩ := eventually_atTop.1 hlarge
  have hC : 0 < ε * (L / 2) := mul_pos hε (by linarith)
  have hconst : IntegrableOn (fun _ : ℝ => ε * (L / 2)) (Ioi R) := by
    refine MeasureTheory.Integrable.mono (hn.integrableOn (s := Ioi R))
      continuous_const.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hC, Real.norm_eq_abs,
      abs_of_nonneg (thetaPowerWeightedEnergy_nonneg q _ (-x))]
    exact hR x hx.le
  rw [MeasureTheory.integrableOn_const_iff (by finiteness), Real.volume_Ioi] at hconst
  simp [hε.ne', hL.ne'] at hconst

/-- Exact unconditional classification of every signed arithmetic finite shift polynomial. -/
theorem finiteArithmeticThetaShift_integrable_energy_iff
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b) (hc : c b ≠ 0)
    (q : ℝ) (_hq : 0 < q) :
    Integrable (thetaPowerWeightedEnergy q (finiteArithmeticThetaShift D c)) ↔
      q < 2 / (b : ℝ) ^ 2 := by
  constructor
  · intro hint
    by_contra hn
    exact not_integrable_finiteArithmeticThetaShift_energy D c b hb hpositive hmax hc q
      (le_of_not_gt hn) hint
  · exact integrable_finiteArithmeticThetaShift_energy D c b hb hpositive hmax q

/-- The exact sharp theorem in the literal real power-weighted `L²` carrier. -/
theorem finiteArithmeticThetaShift_memLp_iff
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b) (hc : c b ≠ 0)
    (q : ℝ) (hq : 0 < q) :
    MemLp (finiteArithmeticThetaShift D c) 2 (thetaPowerWeightedMeasure q) ↔
      q < 2 / (b : ℝ) ^ 2 := by
  rw [memLp_thetaPowerWeightedMeasure_iff q (continuous_finiteArithmeticThetaShift D c)]
  exact finiteArithmeticThetaShift_integrable_energy_iff D c b hb hpositive hmax hc q hq

/-- The same sharp theorem in the actual complex Hilbert carrier. -/
theorem finiteArithmeticThetaShift_ofReal_memLp_iff
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b) (hc : c b ≠ 0)
    (q : ℝ) (hq : 0 < q) :
    MemLp (fun x => (finiteArithmeticThetaShift D c x : ℂ)) 2
      (thetaPowerWeightedMeasure q) ↔ q < 2 / (b : ℝ) ^ 2 := by
  rw [memLp_ofReal_thetaPowerWeightedMeasure_iff q (continuous_finiteArithmeticThetaShift D c)]
  exact finiteArithmeticThetaShift_integrable_energy_iff D c b hb hpositive hmax hc q hq

end

end RHTower
