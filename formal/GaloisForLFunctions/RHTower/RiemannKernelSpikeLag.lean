import GaloisForLFunctions.RHTower.RiemannKernelEdgeWeilEnergy

/-!
# Thin spikes of Riemann's kernel and their pairwise lags

At a level `L` let `Y = 2πe^{2L}` and `η = 1/Y`. The spike `P_L = Φ·(χ_{L+2η} − χ_L)`
(`combSpike`), with both cutoffs of width `η`, is nonnegative, even and smooth. It vanishes outside
`L < |u| < L + 3η`, equals `Φ` on `L + η ≤ |u| ≤ L + 2η`, and is bounded by `A e^{−c(|u| − L)}` with
`A = C₀E(L)` (`spikeAmp`) and `c = Y − 9/2` (`spikeRate`).

For two levels `L, L'`, with `d = L − L'`, `D = L + L'`, `m = min(c, c')` and `M = max(c, c')`, the
lag correlation obeys, for every lag `x ≥ 0`,

`∫ P_L(u) P_{L'}(u − x) du ≤ AA'[(e^{−m|x − d|} + e^{−m|x + d|})/(c + c') + 1_{D ≤ x}(2/M)e^{−(m/2)(x − D)}]`

(`integral_combSpike_lag_le`). The first two terms come from `u` and `u − x` on the same side of the
origin. There the exponent `c(u − L) + c'(u − x − L')` exceeds `m|x − d|` plus `(c + c')` times the
distance to the first admissible point. The last term comes from opposite sides, where the larger
rate controls the integration variable and the smaller one the distance `x − D`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- The cutoff `χ_{L,η}` increases with `L`. -/
theorem edgeCutoff_mono {L L' η : ℝ} (hη : 0 < η) (hLL : L ≤ L') (u : ℝ) :
    edgeCutoff L η u ≤ edgeCutoff L' η u := by
  unfold edgeCutoff
  have h1 : (L + η - u) / η ≤ (L' + η - u) / η := by gcongr
  have h2 : (L + η + u) / η ≤ (L' + η + u) / η := by gcongr
  exact mul_le_mul (Real.smoothTransition.monotone h1) (Real.smoothTransition.monotone h2)
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- The thin spike `P_L = Φ·(χ_{L+2η} − χ_L)` of Riemann's kernel at level `L`, `η = 1/Y(L)`. -/
def combSpike (L u : ℝ) : ℝ :=
  riemannKernelReal u *
    (edgeCutoff (L + 2 * edgeWidth L) (edgeWidth L) u - edgeCutoff L (edgeWidth L) u)

/-- The spike amplitude `A = C₀E(L)`. -/
def spikeAmp (L : ℝ) : ℝ := riemannEnvelopeConst * kernelEnvelope L

/-- The spike decay rate `c = Y − 9/2`. -/
def spikeRate (L : ℝ) : ℝ := edgeRate L - 9 / 2

theorem spikeAmp_pos (L : ℝ) : 0 < spikeAmp L :=
  mul_pos riemannEnvelopeConst_pos (kernelEnvelope_pos L)

theorem spikeRate_pos {L : ℝ} (hL : 1 ≤ L) : 0 < spikeRate L := by
  unfold spikeRate; linarith [(edgeRate_ge hL).1]

theorem combSpike_nonneg (L u : ℝ) : 0 ≤ combSpike L u :=
  mul_nonneg (riemannKernelReal_pos u).le (sub_nonneg.mpr
    (edgeCutoff_mono (edgeWidth_pos L) (by linarith [edgeWidth_pos L]) u))

theorem combSpike_le (L u : ℝ) : combSpike L u ≤ riemannKernelReal u := by
  unfold combSpike
  have h1 := edgeCutoff_le_one (L + 2 * edgeWidth L) (edgeWidth L) u
  have h2 := edgeCutoff_nonneg L (edgeWidth L) u
  have := riemannKernelReal_pos u
  nlinarith

theorem combSpike_eq_zero_of_le {L u : ℝ} (hu : |u| ≤ L) : combSpike L u = 0 := by
  have hη := edgeWidth_pos L
  unfold combSpike
  rw [edgeCutoff_eq_one hη (by linarith), edgeCutoff_eq_one hη hu, sub_self, mul_zero]

theorem combSpike_eq_zero_of_ge {L u : ℝ} (hu : L + 3 * edgeWidth L ≤ |u|) : combSpike L u = 0 := by
  have hη := edgeWidth_pos L
  unfold combSpike
  rw [edgeCutoff_eq_zero hη (by linarith), edgeCutoff_eq_zero hη (by linarith), sub_self, mul_zero]

theorem combSpike_eq_kernel {L u : ℝ} (h1 : L + edgeWidth L ≤ |u|) (h2 : |u| ≤ L + 2 * edgeWidth L) :
    combSpike L u = riemannKernelReal u := by
  unfold combSpike
  rw [edgeCutoff_eq_one (edgeWidth_pos L) h2, edgeCutoff_eq_zero (edgeWidth_pos L) h1, sub_zero,
    mul_one]

theorem combSpike_neg (L u : ℝ) : combSpike L (-u) = combSpike L u := by
  unfold combSpike; rw [riemannKernelReal_neg_eq, edgeCutoff_neg, edgeCutoff_neg]

theorem contDiff_combSpike (L : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (combSpike L) :=
  contDiff_riemannKernelReal.mul
    ((contDiff_edgeCutoff _ _).sub (contDiff_edgeCutoff L (edgeWidth L)))

theorem continuous_combSpike (L : ℝ) : Continuous (combSpike L) := (contDiff_combSpike L).continuous

theorem combSpike_mem_of_ne_zero {L u : ℝ} (h : combSpike L u ≠ 0) :
    L < |u| ∧ |u| < L + 3 * edgeWidth L := by
  constructor
  · by_contra hc; push Not at hc; exact h (combSpike_eq_zero_of_le hc)
  · by_contra hc; push Not at hc; exact h (combSpike_eq_zero_of_ge hc)

theorem hasCompactSupport_combSpike (L : ℝ) : HasCompactSupport (combSpike L) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -(|L| + 3 * edgeWidth L)) (b := |L| + 3 * edgeWidth L)) fun u hu => ?_
  apply combSpike_eq_zero_of_ge
  have hL := le_abs_self L
  rw [Set.mem_Icc, not_and_or] at hu
  rcases hu with h | h
  · push Not at h; exact le_abs.2 (Or.inr (by linarith))
  · push Not at h; exact le_abs.2 (Or.inl (by linarith))

theorem integrable_combSpike (L : ℝ) : Integrable (combSpike L) :=
  (continuous_combSpike L).integrable_of_hasCompactSupport (hasCompactSupport_combSpike L)

/-! ## Size of a spike -/

/-- Beyond the level the spike is below `A e^{−c(|u| − L)}`. -/
theorem combSpike_le_exp {L u : ℝ} (hL : 1 ≤ L) (hu : L < |u|) :
    combSpike L u ≤ spikeAmp L * Real.exp (-spikeRate L * (|u| - L)) := by
  refine (combSpike_le L u).trans
    ((riemannKernelReal_le_envelope (three_le_exp_two_mul_abs (by linarith))).trans ?_)
  have h := kernelEnvelope_add_le L (|u| - L)
  rw [show L + (|u| - L) = |u| by ring] at h
  unfold spikeAmp spikeRate
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h riemannEnvelopeConst_pos.le

theorem combSpike_le_edgeMajorant {L : ℝ} (hL : 1 ≤ L) (u : ℝ) :
    combSpike L u ≤ edgeMajorant (spikeAmp L) (spikeRate L) L |u| := by
  by_cases hu : L < |u|
  · rw [edgeMajorant_of_lt hu]; exact combSpike_le_exp hL hu
  · push Not at hu
    rw [combSpike_eq_zero_of_le hu]
    exact edgeMajorant_nonneg (spikeAmp_pos L).le _

/-- `∫ P_L ≤ 2A/c`. -/
theorem integral_combSpike_le {L : ℝ} (hL : 1 ≤ L) :
    ∫ u, combSpike L u ≤ 2 * (spikeAmp L / spikeRate L) := by
  have hc := spikeRate_pos hL
  calc ∫ u, combSpike L u
      ≤ ∫ u, edgeMajorant (spikeAmp L) (spikeRate L) L |u| :=
        integral_mono_of_nonneg (Eventually.of_forall fun u => combSpike_nonneg L u)
          (integrable_edgeMajorant_abs (spikeAmp_pos L).le hc L)
          (Eventually.of_forall fun u => combSpike_le_edgeMajorant hL u)
    _ = _ := integral_edgeMajorant_abs hc (by linarith)

/-- On the layer `L + η ≤ u ≤ L + 2η` the spike is at least `20 e^{−3} E(L)`. -/
theorem combSpike_ge_on_layer {L : ℝ} (hL : 1 ≤ L) (hY : 8 ≤ edgeRate L) {u : ℝ}
    (hu1 : L + edgeWidth L ≤ u) (hu2 : u ≤ L + 2 * edgeWidth L) :
    20 * Real.exp (-3) * kernelEnvelope L ≤ combSpike L u := by
  have hY0 := edgeRate_pos L
  have hηY : edgeWidth L * edgeRate L = 1 := by unfold edgeWidth; field_simp
  have hη0 := edgeWidth_pos L
  have hη8 : edgeWidth L * 8 ≤ 1 := by nlinarith
  have hu0 : 0 ≤ u := by linarith
  have habs : |u| = u := abs_of_nonneg hu0
  rw [combSpike_eq_kernel (by rw [habs]; exact hu1) (by rw [habs]; exact hu2)]
  obtain ⟨y, hy⟩ : ∃ y, y = u - L := ⟨_, rfl⟩
  have hy0 : edgeWidth L ≤ y := by rw [hy]; linarith
  have hy1 : y ≤ 2 * edgeWidth L := by rw [hy]; linarith
  have hge := kernelEnvelope_add_ge L (y := y) (by linarith) (by linarith)
  rw [show L + y = u by rw [hy]; ring] at hge
  have hYy : edgeRate L * y ≤ 2 := by nlinarith
  have hYy2 : edgeRate L * (2 * y ^ 2) ≤ 1 := by
    have h1 : y ^ 2 ≤ (2 * edgeWidth L) ^ 2 := pow_le_pow_left₀ (by linarith) hy1 2
    nlinarith
  have hexp : Real.exp (-3) ≤ Real.exp (-(edgeRate L) * y - edgeRate L * (2 * y ^ 2)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hE := kernelEnvelope_pos L
  have h20 := envelope_le_riemannKernelReal hu0
  calc 20 * Real.exp (-3) * kernelEnvelope L
      = 20 * (kernelEnvelope L * Real.exp (-3)) := by ring
    _ ≤ 20 * (kernelEnvelope L * Real.exp (-(edgeRate L) * y - edgeRate L * (2 * y ^ 2))) := by
        gcongr
    _ ≤ 20 * kernelEnvelope u := by gcongr
    _ ≤ _ := h20

theorem integrable_combSpike_sq (L : ℝ) : Integrable (fun u => combSpike L u ^ 2) := by
  have h2 : HasCompactSupport (fun u => combSpike L u ^ 2) := by
    simpa [Function.comp_def] using
      (hasCompactSupport_combSpike L).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact ((continuous_combSpike L).pow 2).integrable_of_hasCompactSupport h2

/-- `∫ P_L² ≥ 400 e^{−6} E(L)²/Y`. -/
theorem integral_combSpike_sq_ge {L : ℝ} (hL : 1 ≤ L) (hY : 8 ≤ edgeRate L) :
    400 * Real.exp (-6) * kernelEnvelope L ^ 2 / edgeRate L ≤ ∫ u, combSpike L u ^ 2 := by
  have hY0 := edgeRate_pos L
  have hηY : edgeWidth L * edgeRate L = 1 := by unfold edgeWidth; field_simp
  have hη0 := edgeWidth_pos L
  have hT := integrable_combSpike_sq L
  have hconst : 400 * Real.exp (-6) * kernelEnvelope L ^ 2 =
      (20 * Real.exp (-3) * kernelEnvelope L) ^ 2 := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; norm_num
  have hlow : ∀ u ∈ Icc (L + edgeWidth L) (L + 2 * edgeWidth L),
      400 * Real.exp (-6) * kernelEnvelope L ^ 2 ≤ combSpike L u ^ 2 := fun u hu => by
    rw [hconst]
    exact pow_le_pow_left₀ (by have := kernelEnvelope_pos L; positivity)
      (combSpike_ge_on_layer hL hY hu.1 hu.2) 2
  calc 400 * Real.exp (-6) * kernelEnvelope L ^ 2 / edgeRate L
      = ∫ _u in Icc (L + edgeWidth L) (L + 2 * edgeWidth L),
          400 * Real.exp (-6) * kernelEnvelope L ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
          max_eq_left (by linarith), show L + 2 * edgeWidth L - (L + edgeWidth L) = edgeWidth L by ring,
          div_eq_iff hY0.ne']
        nlinarith
    _ ≤ ∫ u in Icc (L + edgeWidth L) (L + 2 * edgeWidth L), combSpike L u ^ 2 :=
        setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne) hT.integrableOn
          measurableSet_Icc hlow
    _ ≤ ∫ u, combSpike L u ^ 2 :=
        setIntegral_le_integral hT (Eventually.of_forall fun _ => sq_nonneg _)

/-! ## Pairwise lags -/

theorem integral_edgeMajorant (A : ℝ) {c : ℝ} (hc : 0 < c) (L : ℝ) :
    ∫ t, edgeMajorant A c L t = A / c := by
  unfold edgeMajorant
  rw [integral_indicator measurableSet_Ioi, integral_edgeMajorant_exp A hc L]

theorem integral_edgeMajorant_neg (A : ℝ) {c : ℝ} (hc : 0 < c) (L : ℝ) :
    ∫ t, edgeMajorant A c L (-t) = A / c := by
  rw [integral_neg_eq_self (fun t => edgeMajorant A c L t), integral_edgeMajorant A hc L]

/-- Exponent bound for two points on the positive side. -/
theorem lag_exponent_pos {c c' m L L' x u : ℝ} (hm : m ≤ c) (hm' : m ≤ c') :
    m * |x - (L - L')| + (c + c') * (u - max L (L' + x)) ≤ c * (u - L) + c' * (u - x - L') := by
  have h1 := le_max_left L (L' + x)
  have h2 := le_max_right L (L' + x)
  rcases le_total L (L' + x) with h | h
  · rw [max_eq_right h]
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  · rw [max_eq_left h]
    rw [abs_of_nonpos (by linarith)]
    nlinarith

/-- Exponent bound for two points on the negative side. -/
theorem lag_exponent_neg {c c' m L L' x u : ℝ} (hm : m ≤ c) (hm' : m ≤ c') :
    m * |x + (L - L')| + (c + c') * (-u - max L (L' - x)) ≤ c * (-u - L) + c' * (x - u - L') := by
  have h1 := le_max_left L (L' - x)
  have h2 := le_max_right L (L' - x)
  rcases le_total L (L' - x) with h | h
  · rw [max_eq_right h]
    rw [abs_of_nonpos (by linarith)]
    nlinarith
  · rw [max_eq_left h]
    rw [abs_of_nonneg (by linarith)]
    nlinarith

/-- The opposite-side majorant: a one-sided exponential driven by the larger rate. -/
def oppositeLagMajorant (B c c' L L' x u : ℝ) : ℝ :=
  if c ≤ c' then edgeMajorant B (c' / 2) (-(x - L')) (-u) else edgeMajorant B (c / 2) L u

theorem oppositeLagMajorant_nonneg {B : ℝ} (hB : 0 ≤ B) (c c' L L' x u : ℝ) :
    0 ≤ oppositeLagMajorant B c c' L L' x u := by
  unfold oppositeLagMajorant; split_ifs <;> exact edgeMajorant_nonneg hB _

theorem integral_oppositeLagMajorant (B : ℝ) {c c' : ℝ} (hc' : 0 < c') (L L' x : ℝ) :
    ∫ u, oppositeLagMajorant B c c' L L' x u = B / (max c c' / 2) := by
  unfold oppositeLagMajorant
  by_cases h : c ≤ c'
  · simp only [if_pos h]
    rw [integral_edgeMajorant_neg B (by linarith) _, max_eq_right h]
  · simp only [if_neg h]
    rw [integral_edgeMajorant B (by linarith) _, max_eq_left (by linarith)]

theorem integrable_oppositeLagMajorant (B : ℝ) {c c' : ℝ} (hc' : 0 < c') (L L' x : ℝ) : Integrable (fun u => oppositeLagMajorant B c c' L L' x u) := by
  unfold oppositeLagMajorant
  by_cases h : c ≤ c'
  · simp only [if_pos h]
    exact (integrable_edgeMajorant B (by linarith) _).comp_neg
  · simp only [if_neg h]
    exact integrable_edgeMajorant B (by linarith) _

/-- The three majorants of the lag product, for a lag `x ≥ 0`. -/
def spikeLagMajorant (L L' x u : ℝ) : ℝ :=
  edgeMajorant (spikeAmp L * spikeAmp L' *
      Real.exp (-(min (spikeRate L) (spikeRate L') * |x - (L - L')|)))
    (spikeRate L + spikeRate L') (max L (L' + x)) u +
  edgeMajorant (spikeAmp L * spikeAmp L' *
      Real.exp (-(min (spikeRate L) (spikeRate L') * |x + (L - L')|)))
    (spikeRate L + spikeRate L') (max L (L' - x)) (-u) +
  if L + L' ≤ x then
    oppositeLagMajorant (spikeAmp L * spikeAmp L' *
        Real.exp (-(min (spikeRate L) (spikeRate L') / 2 * (x - (L + L')))))
      (spikeRate L) (spikeRate L') L L' x u
  else 0

/-- **Pointwise lag bound.** -/
theorem combSpike_mul_lag_le {L L' x : ℝ} (hL : 1 ≤ L) (hL' : 1 ≤ L') (hx : 0 ≤ x) (u : ℝ) :
    combSpike L u * combSpike L' (u - x) ≤ spikeLagMajorant L L' x u := by
  set A := spikeAmp L with hA
  set A' := spikeAmp L' with hA'
  set c := spikeRate L with hc
  set c' := spikeRate L' with hc'
  set m := min c c' with hm
  have hA0 : 0 < A := spikeAmp_pos L
  have hA0' : 0 < A' := spikeAmp_pos L'
  have hc0 : 0 < c := spikeRate_pos hL
  have hc0' : 0 < c' := spikeRate_pos hL'
  have hmc : m ≤ c := min_le_left _ _
  have hmc' : m ≤ c' := min_le_right _ _
  have hm0 : 0 ≤ m := le_min hc0.le hc0'.le
  have hg1 : 0 ≤ edgeMajorant (A * A' * Real.exp (-(m * |x - (L - L')|))) (c + c')
      (max L (L' + x)) u := edgeMajorant_nonneg (by positivity) _
  have hg2 : 0 ≤ edgeMajorant (A * A' * Real.exp (-(m * |x + (L - L')|))) (c + c')
      (max L (L' - x)) (-u) := edgeMajorant_nonneg (by positivity) _
  have hg3 : 0 ≤ (if L + L' ≤ x then
      oppositeLagMajorant (A * A' * Real.exp (-(m / 2 * (x - (L + L'))))) c c' L L' x u
      else 0) := by
    split_ifs
    · exact oppositeLagMajorant_nonneg (by positivity) _ _ _ _ _ _
    · exact le_refl 0
  unfold spikeLagMajorant
  rw [← hA, ← hA', ← hc, ← hc', ← hm]
  by_cases ha : combSpike L u = 0
  · rw [ha, zero_mul]; linarith
  by_cases hb : combSpike L' (u - x) = 0
  · rw [hb, mul_zero]; linarith
  obtain ⟨ha1, -⟩ := combSpike_mem_of_ne_zero ha
  obtain ⟨hb1, -⟩ := combSpike_mem_of_ne_zero hb
  have hPa := combSpike_le_exp hL ha1
  have hPb := combSpike_le_exp hL' hb1
  rw [← hA, ← hc] at hPa
  rw [← hA', ← hc'] at hPb
  have hprod : combSpike L u * combSpike L' (u - x) ≤
      A * Real.exp (-c * (|u| - L)) * (A' * Real.exp (-c' * (|u - x| - L'))) :=
    mul_le_mul hPa hPb (combSpike_nonneg _ _) (by positivity)
  have hrw : A * Real.exp (-c * (|u| - L)) * (A' * Real.exp (-c' * (|u - x| - L'))) =
      A * A' * Real.exp (-(c * (|u| - L) + c' * (|u - x| - L'))) := by
    rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring
  rw [hrw] at hprod
  rcases lt_or_gt_of_ne (show u ≠ 0 by rintro rfl; simp at ha1; linarith) with hu | hu
  · -- both points on the negative side
    have hux : u - x < 0 := by linarith
    rw [abs_of_neg hu] at ha1 hprod
    rw [abs_of_neg hux] at hb1 hprod
    have hmax : max L (L' - x) < -u := max_lt ha1 (by linarith)
    have hexp := lag_exponent_neg (c := c) (c' := c') (m := m) (L := L) (L' := L') (x := x) (u := u)
      hmc hmc'
    have hg : edgeMajorant (A * A' * Real.exp (-(m * |x + (L - L')|))) (c + c') (max L (L' - x)) (-u)
        = A * A' * Real.exp (-(m * |x + (L - L')|)) * Real.exp (-(c + c') * (-u - max L (L' - x))) :=
      edgeMajorant_of_lt hmax
    have hle : A * A' * Real.exp (-(c * (-u - L) + c' * (-(u - x) - L'))) ≤
        A * A' * Real.exp (-(m * |x + (L - L')|)) * Real.exp (-(c + c') * (-u - max L (L' - x))) := by
      rw [mul_assoc (A * A'), ← Real.exp_add]
      gcongr
      nlinarith [hexp]
    linarith
  · rw [abs_of_pos hu] at ha1 hprod
    rcases lt_or_gt_of_ne (show u - x ≠ 0 by
        intro h; rw [h] at hb1; simp at hb1; linarith) with hux | hux
    · -- opposite sides
      rw [abs_of_neg hux] at hb1 hprod
      have hD : L + L' ≤ x := by linarith
      rw [if_pos hD]
      have hα : 0 ≤ u - L := by linarith
      have hβ : 0 ≤ x - u - L' := by linarith
      unfold oppositeLagMajorant
      by_cases hcc : c ≤ c'
      · rw [if_pos hcc]
        have hlt : -(x - L') < -u := by linarith
        rw [edgeMajorant_of_lt hlt]
        have hmeq : m = c := min_eq_left hcc
        have hle : A * A' * Real.exp (-(c * (u - L) + c' * (-(u - x) - L'))) ≤
            A * A' * Real.exp (-(m / 2 * (x - (L + L')))) *
              Real.exp (-(c' / 2) * (-u - -(x - L'))) := by
          rw [mul_assoc (A * A'), ← Real.exp_add]
          gcongr
          rw [hmeq]; nlinarith
        linarith
      · rw [if_neg hcc]
        push Not at hcc
        rw [edgeMajorant_of_lt ha1]
        have hmeq : m = c' := min_eq_right hcc.le
        have hle : A * A' * Real.exp (-(c * (u - L) + c' * (-(u - x) - L'))) ≤
            A * A' * Real.exp (-(m / 2 * (x - (L + L')))) * Real.exp (-(c / 2) * (u - L)) := by
          rw [mul_assoc (A * A'), ← Real.exp_add]
          gcongr
          rw [hmeq]; nlinarith
        linarith
    · -- both points on the positive side
      rw [abs_of_pos hux] at hb1 hprod
      have hmax : max L (L' + x) < u := max_lt ha1 (by linarith)
      have hexp := lag_exponent_pos (c := c) (c' := c') (m := m) (L := L) (L' := L') (x := x)
        (u := u) hmc hmc'
      have hle : A * A' * Real.exp (-(c * (u - L) + c' * (u - x - L'))) ≤
          A * A' * Real.exp (-(m * |x - (L - L')|)) * Real.exp (-(c + c') * (u - max L (L' + x))) := by
        rw [mul_assoc (A * A'), ← Real.exp_add]
        gcongr
        nlinarith [hexp]
      rw [edgeMajorant_of_lt hmax]
      linarith

theorem integrable_combSpike_lag (L L' x : ℝ) :
    Integrable (fun u => combSpike L u * combSpike L' (u - x)) := by
  have hc : Continuous (fun u => combSpike L u * combSpike L' (u - x)) :=
    (continuous_combSpike L).mul ((continuous_combSpike L').comp (continuous_id.sub continuous_const))
  have hs : HasCompactSupport (fun u => combSpike L u * combSpike L' (u - x)) :=
    (hasCompactSupport_combSpike L).mul_right
  exact hc.integrable_of_hasCompactSupport hs

/-- **Integrated lag bound.** For `x ≥ 0`,
`∫ P_L(u)P_{L'}(u − x) ≤ AA'[(e^{−m|x−d|} + e^{−m|x+d|})/(c+c') + 1_{D ≤ x}(2/M)e^{−(m/2)(x−D)}]`. -/
theorem integral_combSpike_lag_le {L L' x : ℝ} (hL : 1 ≤ L) (hL' : 1 ≤ L') (hx : 0 ≤ x) :
    ∫ u, combSpike L u * combSpike L' (u - x) ≤
      spikeAmp L * spikeAmp L' *
        ((Real.exp (-(min (spikeRate L) (spikeRate L') * |x - (L - L')|)) +
            Real.exp (-(min (spikeRate L) (spikeRate L') * |x + (L - L')|))) /
              (spikeRate L + spikeRate L') +
          if L + L' ≤ x then
            2 / max (spikeRate L) (spikeRate L') *
              Real.exp (-(min (spikeRate L) (spikeRate L') / 2 * (x - (L + L'))))
          else 0) := by
  have hc0 := spikeRate_pos hL
  have hc0' := spikeRate_pos hL'
  have hcc : 0 < spikeRate L + spikeRate L' := by linarith
  have hM : 0 < max (spikeRate L) (spikeRate L') := lt_max_of_lt_left hc0
  have i1 := integrable_edgeMajorant (spikeAmp L * spikeAmp L' *
      Real.exp (-(min (spikeRate L) (spikeRate L') * |x - (L - L')|))) hcc (max L (L' + x))
  have i2 := (integrable_edgeMajorant (spikeAmp L * spikeAmp L' *
      Real.exp (-(min (spikeRate L) (spikeRate L') * |x + (L - L')|))) hcc (max L (L' - x))).comp_neg
  have i3 : Integrable (fun u => if L + L' ≤ x then
      oppositeLagMajorant (spikeAmp L * spikeAmp L' *
        Real.exp (-(min (spikeRate L) (spikeRate L') / 2 * (x - (L + L')))))
        (spikeRate L) (spikeRate L') L L' x u else 0) := by
    split_ifs
    · exact integrable_oppositeLagMajorant _ hc0' _ _ _
    · exact integrable_zero _ _ _
  have i12 : Integrable (fun u => edgeMajorant (spikeAmp L * spikeAmp L' *
      Real.exp (-(min (spikeRate L) (spikeRate L') * |x - (L - L')|)))
        (spikeRate L + spikeRate L') (max L (L' + x)) u +
      edgeMajorant (spikeAmp L * spikeAmp L' *
      Real.exp (-(min (spikeRate L) (spikeRate L') * |x + (L - L')|)))
        (spikeRate L + spikeRate L') (max L (L' - x)) (-u)) := i1.add i2
  have hmaj : Integrable (spikeLagMajorant L L' x) := by
    unfold spikeLagMajorant; exact i12.add i3
  refine (integral_mono (integrable_combSpike_lag L L' x) hmaj
    (fun u => combSpike_mul_lag_le hL hL' hx u)).trans (le_of_eq ?_)
  unfold spikeLagMajorant
  rw [integral_add i12 i3, integral_add i1 i2, integral_edgeMajorant _ hcc,
    integral_edgeMajorant_neg _ hcc]
  split_ifs with hD
  · rw [integral_oppositeLagMajorant _ hc0']
    field_simp
  · rw [integral_zero]
    field_simp
    ring

end

end RHTower
