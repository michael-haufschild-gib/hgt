import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialRemainder
import GaloisForLFunctions.RHTower.WeilLinearTwistQuantization

/-!
# Frequency twists of the actual canonical radial trace

Compact radial convergence and open-strip rectangle displacement remain valid
for every linear frequency multiplier. The resulting radial integrals admit
a common exponential frequency majorant derived from Weil positivity alone.
This pays the contour and domination prerequisites for retaining resonances;
it does not assert spectral quantization or periodicity of the actual phase.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

/-- The linear frequency multiplier preserves actual compact radial convergence. -/
theorem tendsto_integral_quantization_twist {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (ω : ℝ) {τ : ℂ} (hτ : τ ≠ 0) (a b : ℝ) :
    Tendsto (fun η : ℝ => ∫ y in a..b,
      linTwist ω (((1 / 2 + η : ℝ) : ℂ) + y * I) *
        (prodF (quantizationCompletion hW) (((1 / 2 + η : ℝ) : ℂ) + y * I) *
          offKernel τ (((1 / 2 + η : ℝ) : ℂ) + y * I))) (𝓝[>] 0)
      (𝓝 (∫ y in a..b, linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
        (quantizationTraceF hW y * offKernel τ (((1 / 2 : ℝ) : ℂ) + y * I)))) := by
  obtain ⟨B, hB⟩ := exists_bound_quantizationRadialProduct hW hτ a b
  have hη : Ioo (0 : ℝ) (1 / 4) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => Real.exp (|ω| / 2) * B)
  · filter_upwards [hη] with η hη
    have hc : Continuous (fun y : ℝ =>
        offKernel τ (((1 / 2 + η : ℝ) : ℂ) + y * I)) := by
      rw [continuous_iff_continuousAt]
      intro y
      exact (differentiableAt_offKernel hτ (s := (((1 / 2 + η : ℝ) : ℂ) + y * I))
        (by simp; linarith [hη.1]) (by simp; linarith [hη.2])).continuousAt.comp
        (f := fun y : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I))
        (show ContinuousAt (fun y : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) y from by fun_prop)
    exact (((continuous_linTwist ω).comp (by fun_prop)).mul
      ((continuous_quantizationProdF_slice hW (by linarith [hη.1])
        (by linarith [hη.2])).mul hc)).aestronglyMeasurable.restrict
  · filter_upwards [hη] with η hη
    refine Eventually.of_forall fun y hy => ?_
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (norm_linTwist_strip_le ω (by simp; linarith [hη.1])
        (by simp; linarith [hη.2])) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hB η hη y (uIoc_subset_uIcc hy)) (Real.exp_pos _).le)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun y _ => ?_
    have hp : Continuous (fun η : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) := by fun_prop
    have ht : Tendsto (fun η : ℝ => (((1 / 2 + η : ℝ) : ℂ) + y * I)) (𝓝[>] 0)
        (𝓝 (((1 / 2 : ℝ) : ℂ) + y * I)) := by
      simpa using (hp.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ((continuous_linTwist ω).tendsto _ |>.comp ht).mul
      ((tendsto_quantizationTraceF hW y).mul
        ((differentiableAt_offKernel hτ (by norm_num)
          (by norm_num)).continuousAt.tendsto.comp ht))

/-- Frequency twists use the open rectangle; no continuous critical-edge completion is supplied. -/
theorem norm_quantization_twist_rectangle_sub {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C p : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p)
    (ω : ℝ) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖)
    {A B : ℝ} (hAB : A ≤ B) (hB : B ≤ -2) :
    ‖(∫ y in A..B, linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
        (quantizationTraceF hW y * pairKernel y τ)) -
      (∫ y in A..B, linTwist ω (edgePt y) *
        edgeIntegrand (quantizationCompletion hW) τ (edgePt y))‖ ≤
      quantizationContourBound (Real.exp (|ω| / 2) * C) p τ A +
        quantizationContourBound (Real.exp (|ω| / 2) * C) p τ B := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  simp only [quantization_pairKernel_eq_offKernel]
  apply le_of_tendsto ((tendsto_integral_quantization_twist hW ω hτ0 A B).sub_const
    (∫ y in A..B, linTwist ω (edgePt y) *
      edgeIntegrand (quantizationCompletion hW) τ (edgePt y))).norm
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with η hη
  have h := norm_quantization_open_rectangle_sub
    (F := fun s => linTwist ω s * prodF (quantizationCompletion hW) s)
    (C := Real.exp (|ω| / 2) * C) (p := p) (mul_nonneg (Real.exp_pos _).le hC)
    (fun s hs _ hi => (hasDerivAt_linTwist ω s).differentiableAt.mul
      (differentiableAt_prodF (fun _ hz => hasDerivAt_quantizationCompletion hW hz) hs
        (fun h => by simp [h] at hi; linarith) (fun h => by simp [h] at hi; linarith)))
    (fun x y hx hx' hy => by
      rw [norm_mul]
      calc _ ≤ Real.exp (|ω| / 2) * (C * (1 + |y|) ^ p) :=
          mul_le_mul (norm_linTwist_strip_le ω (by simpa using hx.le) (by simpa using hx'))
            (hF x y hx hx' (by rw [abs_of_neg (by linarith)]; linarith))
            (norm_nonneg _) (Real.exp_pos _).le
        _ = _ := by ring)
    hτre hτ1 (σ := 1 / 2 + η) (by linarith [hη.1]) (by linarith [hη.2]) hAB hB
  simpa only [edgePt, edgeIntegrand, mul_assoc] using h

/-- Unit boundary modulus pays integrability of every frequency twist. -/
theorem integrableOn_quantization_twist_left {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (ω : ℝ) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -2) :
    IntegrableOn (fun y : ℝ => linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
      (quantizationTraceF hW y * pairKernel y τ)) (Iic B) := by
  apply (integrableOn_quantizationTraceF_pairKernel hW hτre hτ1 hB).bdd_mul
    (c := 1) (((continuous_linTwist ω).comp (by fun_prop)).aestronglyMeasurable.restrict)
  exact Eventually.of_forall fun y => by simp [norm_linTwist]

/-- The frequency multiplier has constant modulus on the arithmetic right edge. -/
theorem integrableOn_quantization_twist_right {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (ω : ℝ) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -2) :
    IntegrableOn (fun y : ℝ => linTwist ω (edgePt y) *
      edgeIntegrand (quantizationCompletion hW) τ (edgePt y)) (Iic B) := by
  apply (integrableOn_quantization_rightEdge hW hτre hτ1 hB).bdd_mul
    (c := Real.exp (-(ω / 2)))
    (((continuous_linTwist ω).comp (by unfold edgePt; fun_prop)).aestronglyMeasurable.restrict)
  exact Eventually.of_forall fun y => (norm_linTwist_edgePt ω y).le

/-- Actual-source contour displacement for every frequency, with its uniform exponential cost. -/
theorem norm_quantization_twist_halfline_sub {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C p : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y : ℝ, 1 / 2 < x → x ≤ 3 / 2 → 2 ≤ |y| →
      ‖prodF (quantizationCompletion hW) ((x : ℂ) + y * I)‖ ≤ C * (1 + |y|) ^ p)
    (ω : ℝ) {τ : ℂ} (hτre : 0 < τ.re) (hτ1 : 1 ≤ ‖τ‖) {B : ℝ} (hB : B ≤ -2) :
    ‖(∫ y in Iic B, linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
        (quantizationTraceF hW y * pairKernel y τ)) -
      (∫ y in Iic B, linTwist ω (edgePt y) *
        edgeIntegrand (quantizationCompletion hW) τ (edgePt y))‖ ≤
      quantizationContourBound (Real.exp (|ω| / 2) * C) p τ B := by
  have hL := intervalIntegral_tendsto_integral_Iic B
    (integrableOn_quantization_twist_left hW ω hτre hτ1 hB) tendsto_id
  have hR := intervalIntegral_tendsto_integral_Iic B
    (integrableOn_quantization_twist_right hW ω hτre hτ1 hB) tendsto_id
  have hlim := (tendsto_quantizationContourBound (Real.exp (|ω| / 2) * C) p hτre).add_const
    (quantizationContourBound (Real.exp (|ω| / 2) * C) p τ B)
  rw [zero_add] at hlim
  apply le_of_tendsto_of_tendsto (hL.sub hR).norm hlim
  filter_upwards [eventually_le_atBot B] with A hA
  exact norm_quantization_twist_rectangle_sub hW hC hF ω hτre hτ1 hA hB

/-- A uniform frequency majorant for the actual lower radial integral, derived from hW alone. -/
theorem exists_bound_quantization_twist_radial {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖(ε : ℂ) * ∫ y in Iic (-2 : ℝ), linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
        (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I))‖ ≤
        K * Real.exp (|ω| / 2) := by
  obtain ⟨C, hC, hF⟩ := exists_norm_quantizationProdF_le hW
  let S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) (((3 / 2 : ℝ) : ℂ)) n‖
  let Q : ℝ := 4 * Real.pi ^ (3 / 4 : ℝ)
  let M : ℝ := (m : ℝ) + 1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨Real.exp S * Q * M ^ 2 + C * 3 ^ (1 / 2 : ℝ) * (Q * M), by positivity, ?_⟩
  intro ω ε hε hε1
  let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
  let δ : ℝ := ε / ‖τ‖
  let c : ℝ := Real.exp (|ω| / 2)
  have hc : 0 < c := Real.exp_pos _
  have hτre : τ.re = ε := by simp [τ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [τ]
    rw [him, abs_of_nonneg (by positivity)] at h
    linarith
  have hτM : ‖τ‖ ≤ M := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    exact h.trans (by dsimp [M]; linarith)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hεδ : ε / δ = ‖τ‖ := by dsimp [δ]; field_simp
  have hδre : τ.re / ‖τ‖ = δ := by rw [hτre]
  let L : ℂ := ∫ y in Iic (-2 : ℝ), linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
    (quantizationTraceF hW y * pairKernel y τ)
  let R : ℂ := ∫ y in Iic (-2 : ℝ), linTwist ω (edgePt y) *
    edgeIntegrand (quantizationCompletion hW) τ (edgePt y)
  have hright : ‖R‖ ≤ c * Real.exp S * Q * ‖τ‖ * (Real.exp (-2 * δ) / δ) := by
    have hint := (integrableOn_exp_mul_Iic hδ (-2)).const_mul (c * Real.exp S * Q * ‖τ‖)
    refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Iic).mpr
      (Eventually.of_forall fun y hy => ?_))).trans (le_of_eq ?_)
    · have hy' : y ≤ -2 := hy
      have he := norm_edgeIntegrand_three_halves_le
        (fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ)
        (fun _ hz => quantizationContinuation_eq_arch hW hz)
        (fun _ hz => hasDerivAt_quantizationCompletion hW hz)
        (quantizationCompletion_two hW) hτre0 hτ1 (y := y)
        (by rw [abs_of_neg (by linarith)]; linarith)
      rw [norm_mul]
      have ht := mul_le_mul (norm_linTwist_strip_le ω (s := edgePt y) (by rw [edgePt_re]; norm_num)
        (by rw [edgePt_re])) he (norm_nonneg _) hc.le
      rw [abs_of_neg (by linarith : y < 0), hδre] at ht
      calc _ ≤ c * (Real.exp S * (Q * ‖τ‖ * Real.exp (-(-y * δ)))) := ht
        _ = _ := by rw [show -(-y * δ) = δ * y by ring]; ring
    · rw [integral_const_mul, integral_exp_mul_Iic hδ]
      congr 2
      ring
  have hrightε : ε * ‖R‖ ≤ c * (Real.exp S * Q * M ^ 2) := by
    have he : Real.exp (-2 * δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc ε * ‖R‖ ≤ ε * (c * Real.exp S * Q * ‖τ‖ * (Real.exp (-2 * δ) / δ)) :=
          mul_le_mul_of_nonneg_left hright hε.le
      _ = c * Real.exp S * Q * ‖τ‖ * Real.exp (-2 * δ) * (ε / δ) := by ring
      _ ≤ c * Real.exp S * Q * M * 1 * M := by rw [hεδ]; gcongr
      _ = _ := by ring
  have hsub : ‖L - R‖ ≤ c * (C * 3 ^ (1 / 2 : ℝ) * (Q * M)) := by
    have h := norm_quantization_twist_halfline_sub hW hC hF ω hτre0 hτ1 (B := -2) le_rfl
    change ‖L - R‖ ≤ _ at h
    refine h.trans ?_
    have he : Real.exp (-(2 * (τ.re / ‖τ‖))) ≤ 1 := by
      rw [Real.exp_le_one_iff, hδre]; linarith
    simp only [quantizationContourBound, abs_neg, abs_two] at ⊢
    calc Real.exp (|ω| / 2) * C * (1 + 2) ^ (1 / 2 : ℝ) *
          (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖ * Real.exp (-(2 * (τ.re / ‖τ‖))))
        ≤ c * C * 3 ^ (1 / 2 : ℝ) * (Q * M * 1) := by dsimp [c, Q]; gcongr; norm_num
      _ = _ := by ring
  have hsubε : ε * ‖L - R‖ ≤ c * (C * 3 ^ (1 / 2 : ℝ) * (Q * M)) :=
    (mul_le_mul_of_nonneg_right hε1 (norm_nonneg _)).trans (by simpa using hsub)
  change ‖(ε : ℂ) * L‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hL : ‖L‖ ≤ ‖L - R‖ + ‖R‖ := by simpa using norm_add_le (L - R) R
  calc ε * ‖L‖ ≤ ε * (‖L - R‖ + ‖R‖) := mul_le_mul_of_nonneg_left hL hε.le
    _ = ε * ‖L - R‖ + ε * ‖R‖ := by ring
    _ ≤ c * (C * 3 ^ (1 / 2 : ℝ) * (Q * M)) + c * (Real.exp S * Q * M ^ 2) :=
      add_le_add hsubε hrightε
    _ = _ := by dsimp [c]; ring

end RHTower.WeilSpectral
