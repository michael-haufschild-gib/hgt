import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity
import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaSources

/-!
# The edge profile of Riemann's kernel

Riemann's kernel `Φ(u) = Σ_{n ≥ 1} e^{u/2}(4π²n⁴e^{4u} − 6πn²e^{2u})e^{−πn²e^{2u}}` is squeezed
between multiples of the envelope `E(u) = e^{9u/2} e^{−π e^{2u}}`:
`20 E(u) ≤ Φ(u) ≤ C₀ E(u)` for `u ≥ 0` (upper bound once `e^{2u} ≥ 3`).  The envelope decays at
rate `Y = 2π e^{2L}` beyond `L`:
`E(L)e^{−Yy − 2Yy²} ≤ E(L + y) ≤ E(L)e^{−(Y − 9/2)y}` for `0 ≤ y ≤ 1/2`.

Cutting `Φ` at `|u| = L` with a transition of width `1/Y` leaves a tail
`T = Φ(χ_{L+2} − χ_L)` concentrated in a layer of width `≍ 1/Y` at `|u| = L`:
`∫T ≤ 2C₀E(L)/(Y − 9/2)` and `∫T² ≥ 400 e^{−6} E(L)²/Y`, so `(∫T)² ≤ (C/Y)∫T²`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-! ## The envelope -/

/-- The envelope `E(u) = e^{9u/2} e^{−π e^{2u}}`. -/
def kernelEnvelope (u : ℝ) : ℝ := Real.exp (9 * u / 2) * Real.exp (-π * Real.exp (2 * u))

/-- The edge rate `Y = 2π e^{2L}`. -/
def edgeRate (L : ℝ) : ℝ := 2 * π * Real.exp (2 * L)

/-- The envelope constant `C₀ = 12 Mθ e^π`. -/
def riemannEnvelopeConst : ℝ := 12 * jacobiThetaTailConstant * Real.exp π

theorem kernelEnvelope_pos (u : ℝ) : 0 < kernelEnvelope u := by
  unfold kernelEnvelope; positivity

theorem edgeRate_pos (L : ℝ) : 0 < edgeRate L := by
  unfold edgeRate; positivity

theorem riemannEnvelopeConst_pos : 0 < riemannEnvelopeConst := by
  have : 0 < jacobiThetaTailConstant := by
    unfold jacobiThetaTailConstant
    have h := Real.exp_lt_one_iff.mpr (show -π < 0 by linarith [Real.pi_pos])
    have : 0 < 1 - Real.exp (-π) := by linarith
    positivity
  unfold riemannEnvelopeConst; positivity

theorem envelope_le_riemannKernelReal {u : ℝ} (hu : 0 ≤ u) :
    20 * kernelEnvelope u ≤ riemannKernelReal u := by
  have hfirst : cuspTerm riemannCuspPoly (0 + 1) u ≤ cuspSeries riemannCuspPoly u :=
    (summable_cuspTerm riemannCuspPoly u).le_tsum 0
      (fun j _ => (cuspTerm_riemannCuspPoly_pos (by omega) hu).le)
  have hreal : riemannKernelReal u = cuspSeries riemannCuspPoly u := by
    unfold riemannKernelReal; rw [abs_of_nonneg hu]
  rw [hreal]
  refine le_trans ?_ hfirst
  unfold cuspTerm kernelEnvelope
  rw [riemannCuspPoly_eval]
  push_cast
  simp only [one_pow, one_mul]
  set y := Real.exp (2 * u) with hy
  have hy1 : 1 ≤ y := Real.one_le_exp (by linarith)
  have h4 : Real.exp (9 * u / 2) = Real.exp (u / 2) * y ^ 2 := by
    rw [hy, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  rw [h4]
  have hπ := Real.pi_gt_d2
  have hq : 0 ≤ 4 * π ^ 2 - 6 * π - 20 := by nlinarith [hπ]
  have hpoly : 20 * y ^ 2 ≤ 4 * π ^ 2 * y ^ 2 - 6 * π * y := by
    have h1 : 0 ≤ (4 * π ^ 2 - 20) * (y - 1) := mul_nonneg (by nlinarith) (by linarith)
    have h2 : 0 ≤ y * ((4 * π ^ 2 - 20) * (y - 1) + (4 * π ^ 2 - 6 * π - 20)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have he1 := Real.exp_pos (u / 2)
  have he2 := Real.exp_pos (-π * y)
  calc 20 * (Real.exp (u / 2) * y ^ 2 * Real.exp (-π * y))
      = Real.exp (u / 2) * (20 * y ^ 2) * Real.exp (-π * y) := by ring
    _ ≤ Real.exp (u / 2) * (4 * π ^ 2 * y ^ 2 - 6 * π * y) * Real.exp (-π * y) := by gcongr

theorem riemannKernelReal_neg_eq (u : ℝ) : riemannKernelReal (-u) = riemannKernelReal u := by
  unfold riemannKernelReal; rw [abs_neg]

theorem riemannKernelReal_le_envelope {u : ℝ} (hu : 3 ≤ Real.exp (2 * |u|)) :
    riemannKernelReal u ≤ riemannEnvelopeConst * kernelEnvelope |u| := by
  have h1 := norm_riemannPhiKernel_le hu
  rw [norm_riemannPhiKernel_abs, riemannPhiKernel_eq_ofReal, Complex.norm_real,
    Real.norm_eq_abs] at h1
  refine (le_abs_self _).trans (h1.trans ?_)
  set y := Real.exp (2 * |u|) with hy
  have hy3 : 3 * y ≤ y ^ 2 := by nlinarith
  have h4 : Real.exp (9 * |u| / 2) = Real.exp (|u| / 2) * y ^ 2 := by
    rw [hy, ← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
  unfold riemannEnvelopeConst kernelEnvelope
  rw [h4]
  have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
  have he := Real.exp_pos (|u| / 2)
  have he2 := Real.exp_pos (-π * y)
  have heπ := Real.exp_pos π
  have : 3 * y + 2 * y ^ 2 ≤ 3 * y ^ 2 := by linarith
  calc 4 * jacobiThetaTailConstant * Real.exp π * Real.exp (|u| / 2) * (3 * y + 2 * y ^ 2) *
        Real.exp (-π * y)
      ≤ 4 * jacobiThetaTailConstant * Real.exp π * Real.exp (|u| / 2) * (3 * y ^ 2) *
        Real.exp (-π * y) := by gcongr
    _ = _ := by ring

/-- **Decay of the envelope beyond `L`.** -/
theorem kernelEnvelope_add_le (L y : ℝ) :
    kernelEnvelope (L + y) ≤ kernelEnvelope L * Real.exp (-(edgeRate L - 9 / 2) * y) := by
  have h1 : Real.exp (2 * (L + y)) = Real.exp (2 * L) * Real.exp (2 * y) := by
    rw [← Real.exp_add]; ring_nf
  have hl : kernelEnvelope (L + y) =
      Real.exp (9 * (L + y) / 2 + -π * (Real.exp (2 * L) * Real.exp (2 * y))) := by
    unfold kernelEnvelope; rw [h1, ← Real.exp_add]
  have hr : kernelEnvelope L * Real.exp (-(edgeRate L - 9 / 2) * y) =
      Real.exp (9 * L / 2 + -π * Real.exp (2 * L) + -(edgeRate L - 9 / 2) * y) := by
    unfold kernelEnvelope; rw [← Real.exp_add, ← Real.exp_add]
  rw [hl, hr]
  apply Real.exp_le_exp.mpr
  have h2 : 1 + 2 * y ≤ Real.exp (2 * y) := by linarith [Real.add_one_le_exp (2 * y)]
  have hL := Real.exp_pos (2 * L)
  have : π * Real.exp (2 * L) * (1 + 2 * y) ≤ π * Real.exp (2 * L) * Real.exp (2 * y) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  unfold edgeRate
  nlinarith

/-- **Lower bound for the envelope just beyond `L`.** -/
theorem kernelEnvelope_add_ge (L : ℝ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : 2 * y ≤ 1) :
    kernelEnvelope L * Real.exp (-(edgeRate L) * y - edgeRate L * (2 * y ^ 2)) ≤
      kernelEnvelope (L + y) := by
  have h1 : Real.exp (2 * (L + y)) = Real.exp (2 * L) * Real.exp (2 * y) := by
    rw [← Real.exp_add]; ring_nf
  have hl : kernelEnvelope (L + y) =
      Real.exp (9 * (L + y) / 2 + -π * (Real.exp (2 * L) * Real.exp (2 * y))) := by
    unfold kernelEnvelope; rw [h1, ← Real.exp_add]
  have hr : kernelEnvelope L * Real.exp (-(edgeRate L) * y - edgeRate L * (2 * y ^ 2)) =
      Real.exp (9 * L / 2 + -π * Real.exp (2 * L) + (-(edgeRate L) * y - edgeRate L * (2 * y ^ 2))) := by
    unfold kernelEnvelope; rw [← Real.exp_add, ← Real.exp_add]
  rw [hl, hr]
  apply Real.exp_le_exp.mpr
  have h2 : Real.exp (2 * y) ≤ 1 + 2 * y + (2 * y) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := 2 * y)
      (by rw [abs_of_nonneg (by linarith)]; exact hy1)
    have := (abs_le.mp this).2
    linarith
  have hL := Real.exp_pos (2 * L)
  have : π * Real.exp (2 * L) * Real.exp (2 * y) ≤
      π * Real.exp (2 * L) * (1 + 2 * y + (2 * y) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  unfold edgeRate
  nlinarith

/-! ## The edge cutoff -/

/-- The even cutoff equal to `1` on `|u| ≤ L` and `0` on `|u| ≥ L + η`. -/
def edgeCutoff (L η u : ℝ) : ℝ :=
  Real.smoothTransition ((L + η - u) / η) * Real.smoothTransition ((L + η + u) / η)

theorem edgeCutoff_nonneg (L η u : ℝ) : 0 ≤ edgeCutoff L η u :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem edgeCutoff_le_one (L η u : ℝ) : edgeCutoff L η u ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem edgeCutoff_neg (L η u : ℝ) : edgeCutoff L η (-u) = edgeCutoff L η u := by
  unfold edgeCutoff; rw [mul_comm]; ring_nf

theorem contDiff_edgeCutoff (L η : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (edgeCutoff L η) := by
  unfold edgeCutoff
  exact (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const η)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.add contDiff_id).div_const η))

theorem edgeCutoff_eq_one {L η u : ℝ} (hη : 0 < η) (hu : |u| ≤ L) : edgeCutoff L η u = 1 := by
  unfold edgeCutoff
  have h1 := (abs_le.mp hu)
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hη]; linarith),
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hη]; linarith), mul_one]

theorem edgeCutoff_eq_zero {L η u : ℝ} (hη : 0 < η) (hu : L + η ≤ |u|) : edgeCutoff L η u = 0 := by
  unfold edgeCutoff
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h] at hu
    rw [Real.smoothTransition.zero_of_nonpos (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith),
      zero_mul]
  · rw [abs_of_neg h] at hu
    rw [Real.smoothTransition.zero_of_nonpos (x := (L + η + u) / η)
      (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith), mul_zero]

/-! ## The edge tail -/

/-- The inner width `1/Y`. -/
def edgeWidth (L : ℝ) : ℝ := 1 / edgeRate L

theorem edgeWidth_pos (L : ℝ) : 0 < edgeWidth L := one_div_pos.mpr (edgeRate_pos L)

variable {R : ℝ}

/-- The tail `T_R = Φ(χ_R − χ_L)` of the truncation of Riemann's kernel at `L`, cut off again at
`R`. -/
def edgeTail (L R u : ℝ) : ℝ :=
  riemannKernelReal u * (edgeCutoff R 1 u - edgeCutoff L (edgeWidth L) u)

theorem edgeWidth_le_two {L : ℝ} (hL : 0 ≤ L) : edgeWidth L ≤ 2 := by
  unfold edgeWidth edgeRate
  rw [div_le_iff₀ (by positivity)]
  have : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  nlinarith [Real.pi_gt_three]

theorem edgeCutoff_outer_eq_one_of_pos {L u : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R)
    (h : 0 < edgeCutoff L (edgeWidth L) u) : edgeCutoff R 1 u = 1 := by
  apply edgeCutoff_eq_one one_pos
  by_contra hc
  push Not at hc
  have := edgeCutoff_eq_zero (L := L) (edgeWidth_pos L) (u := u)
    (by linarith [edgeWidth_le_two hL])
  linarith

theorem edgeTail_nonneg {L : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) (u : ℝ) : 0 ≤ edgeTail L R u := by
  unfold edgeTail
  refine mul_nonneg (riemannKernelReal_pos u).le ?_
  rcases (edgeCutoff_nonneg L (edgeWidth L) u).lt_or_eq with h | h
  · rw [edgeCutoff_outer_eq_one_of_pos hL hR h]; linarith [edgeCutoff_le_one L (edgeWidth L) u]
  · rw [← h]; linarith [edgeCutoff_nonneg R 1 u]

theorem edgeTail_le (L R u : ℝ) : edgeTail L R u ≤ riemannKernelReal u := by
  unfold edgeTail
  have h1 := edgeCutoff_le_one R 1 u
  have h2 := edgeCutoff_nonneg L (edgeWidth L) u
  have := riemannKernelReal_pos u
  nlinarith

theorem edgeTail_eq_zero_of_le {L u : ℝ} (hR : L ≤ R) (hu : |u| ≤ L) : edgeTail L R u = 0 := by
  unfold edgeTail
  rw [edgeCutoff_eq_one one_pos (by linarith), edgeCutoff_eq_one (edgeWidth_pos L) hu, sub_self,
    mul_zero]

theorem edgeTail_eq_zero_of_ge {L u : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) (hu : R + 1 ≤ |u|) :
    edgeTail L R u = 0 := by
  unfold edgeTail
  rw [edgeCutoff_eq_zero one_pos (by linarith),
    edgeCutoff_eq_zero (edgeWidth_pos L) (by linarith [edgeWidth_le_two hL]), sub_self, mul_zero]

theorem edgeTail_eq_kernel {L u : ℝ} (h1 : L + edgeWidth L ≤ |u|) (h2 : |u| ≤ R) :
    edgeTail L R u = riemannKernelReal u := by
  unfold edgeTail
  rw [edgeCutoff_eq_one one_pos h2, edgeCutoff_eq_zero (edgeWidth_pos L) h1, sub_zero, mul_one]

theorem edgeTail_neg (L R u : ℝ) : edgeTail L R (-u) = edgeTail L R u := by
  unfold edgeTail; rw [riemannKernelReal_neg_eq, edgeCutoff_neg, edgeCutoff_neg]

theorem continuous_edgeTail (L R : ℝ) : Continuous (edgeTail L R) :=
  continuous_riemannKernelReal.mul
    ((contDiff_edgeCutoff R 1).continuous.sub (contDiff_edgeCutoff L (edgeWidth L)).continuous)

theorem hasCompactSupport_edgeTail {L : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) :
    HasCompactSupport (edgeTail L R) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun u hu => ?_
  apply edgeTail_eq_zero_of_ge hL hR
  rw [Set.mem_Icc, not_and_or] at hu
  rcases hu with h | h
  · push Not at h; exact le_abs.2 (Or.inr (by linarith))
  · push Not at h; exact le_abs.2 (Or.inl h.le)

/-! ## Narrowness of the tail -/

theorem three_le_exp_two_mul_abs {u : ℝ} (hu : 1 ≤ |u|) : 3 ≤ Real.exp (2 * |u|) := by
  have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  exact h2.trans (Real.exp_le_exp.mpr (by linarith))

/-- The exponential majorant `A e^{−c(t − L)}` of the tail beyond `L`. -/
def edgeMajorant (A c L t : ℝ) : ℝ := (Ioi L).indicator (fun t => A * Real.exp (-c * (t - L))) t

theorem edgeMajorant_nonneg {A c L : ℝ} (hA : 0 ≤ A) (t : ℝ) : 0 ≤ edgeMajorant A c L t :=
  indicator_nonneg (fun _ _ => mul_nonneg hA (Real.exp_pos _).le) t

theorem measurable_edgeMajorant (A c L : ℝ) : Measurable (edgeMajorant A c L) :=
  Measurable.indicator (by fun_prop) measurableSet_Ioi

theorem edgeMajorant_exp_eq (A c L : ℝ) :
    (fun t => A * Real.exp (-c * (t - L))) = fun t => A * Real.exp (c * L) * Real.exp (-c * t) := by
  funext t; rw [mul_assoc, ← Real.exp_add]; congr 1; ring_nf

theorem integrableOn_edgeMajorant_exp (A : ℝ) {c : ℝ} (hc : 0 < c) (L : ℝ) :
    IntegrableOn (fun t => A * Real.exp (-c * (t - L))) (Ioi L) := by
  rw [edgeMajorant_exp_eq]
  exact (integrableOn_exp_mul_Ioi (by linarith) L).const_mul _

theorem integral_edgeMajorant_exp (A : ℝ) {c : ℝ} (hc : 0 < c) (L : ℝ) :
    ∫ t in Ioi L, A * Real.exp (-c * (t - L)) = A / c := by
  rw [edgeMajorant_exp_eq, integral_const_mul, integral_exp_mul_Ioi (by linarith) L]
  calc A * Real.exp (c * L) * (-Real.exp (-c * L) / -c)
      = A * (Real.exp (c * L) * Real.exp (-c * L)) / c := by field_simp
    _ = A / c := by rw [← Real.exp_add, show c * L + -c * L = 0 by ring, Real.exp_zero, mul_one]

theorem integrable_edgeMajorant (A : ℝ) {c : ℝ} (hc : 0 < c) (L : ℝ) :
    Integrable (edgeMajorant A c L) :=
  (integrableOn_edgeMajorant_exp A hc L).integrable_indicator measurableSet_Ioi

theorem integrable_edgeMajorant_abs {A : ℝ} (hA : 0 ≤ A) {c : ℝ} (hc : 0 < c) (L : ℝ) :
    Integrable (fun u => edgeMajorant A c L |u|) := by
  have hi := integrable_edgeMajorant A hc L
  refine (hi.comp_neg.add hi).mono' ((measurable_edgeMajorant A c L).comp
    measurable_abs).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (edgeMajorant_nonneg hA _)]
  simp only [Pi.add_apply]
  have h1 := edgeMajorant_nonneg hA (A := A) (c := c) (L := L) (-u)
  have h2 := edgeMajorant_nonneg hA (A := A) (c := c) (L := L) u
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_neg h]; linarith

theorem integral_edgeMajorant_abs {A : ℝ} {c : ℝ} (hc : 0 < c) {L : ℝ} (hL : 0 ≤ L) :
    ∫ u, edgeMajorant A c L |u| = 2 * (A / c) := by
  rw [integral_comp_abs]
  congr 1
  unfold edgeMajorant
  rw [setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi L = Ioi L from by
      ext t; simp only [mem_inter_iff, mem_Ioi]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨by linarith, h⟩,
    integral_edgeMajorant_exp A hc L]

theorem edgeTail_le_edgeMajorant {L : ℝ} (hL : 1 ≤ L) (hR : L ≤ R) (u : ℝ) :
    edgeTail L R u ≤ edgeMajorant (riemannEnvelopeConst * kernelEnvelope L) (edgeRate L - 9 / 2) L |u| := by
  unfold edgeMajorant
  by_cases hu : L < |u|
  · rw [indicator_of_mem (show |u| ∈ Ioi L from hu)]
    refine (edgeTail_le L R u).trans
      ((riemannKernelReal_le_envelope (three_le_exp_two_mul_abs (by linarith))).trans ?_)
    have h := kernelEnvelope_add_le L (|u| - L)
    rw [show L + (|u| - L) = |u| by ring] at h
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h riemannEnvelopeConst_pos.le
  · push Not at hu
    rw [indicator_of_notMem (show |u| ∉ Ioi L from fun h => by simp at h; linarith),
      edgeTail_eq_zero_of_le hR hu]

/-- `∫ T ≤ 2 C₀ E(L)/(Y − 9/2)`. -/
theorem integral_edgeTail_le {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) :
    ∫ u, edgeTail L R u ≤ 2 * riemannEnvelopeConst * kernelEnvelope L / (edgeRate L - 9 / 2) := by
  have hc : 0 < edgeRate L - 9 / 2 := by linarith
  have hA : 0 ≤ riemannEnvelopeConst * kernelEnvelope L :=
    mul_nonneg riemannEnvelopeConst_pos.le (kernelEnvelope_pos L).le
  calc ∫ u, edgeTail L R u
      ≤ ∫ u, edgeMajorant (riemannEnvelopeConst * kernelEnvelope L) (edgeRate L - 9 / 2) L |u| :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u => edgeTail_nonneg (by linarith) hR u)
          (integrable_edgeMajorant_abs hA hc L)
          (Filter.Eventually.of_forall fun u => edgeTail_le_edgeMajorant hL (by linarith) u)
    _ = 2 * (riemannEnvelopeConst * kernelEnvelope L / (edgeRate L - 9 / 2)) :=
        integral_edgeMajorant_abs hc (by linarith)
    _ = _ := by ring

/-- The tail is bounded below by `20 e^{−3} E(L)` on `[L + 1/Y, L + 2/Y]`. -/
theorem edgeTail_ge_on_layer {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 8 ≤ edgeRate L) {u : ℝ}
    (hu1 : L + edgeWidth L ≤ u) (hu2 : u ≤ L + 2 * edgeWidth L) :
    20 * Real.exp (-3) * kernelEnvelope L ≤ edgeTail L R u := by
  have hY0 := edgeRate_pos L
  have hηY : edgeWidth L * edgeRate L = 1 := by unfold edgeWidth; field_simp
  have hη0 := edgeWidth_pos L
  have hη8 : edgeWidth L * 8 ≤ 1 := by nlinarith
  have hu0 : 0 ≤ u := by linarith
  have habs : |u| = u := abs_of_nonneg hu0
  rw [edgeTail_eq_kernel (by rw [habs]; exact hu1) (by rw [habs]; linarith)]
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

theorem integrable_edgeTail_sq {L : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) :
    Integrable (fun u => edgeTail L R u ^ 2) := by
  have h2 : HasCompactSupport (fun u => edgeTail L R u ^ 2) := by
    simpa [Function.comp_def] using
      (hasCompactSupport_edgeTail hL hR).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact ((continuous_edgeTail L R).pow 2).integrable_of_hasCompactSupport h2

/-- `∫ T² ≥ 400 e^{−6} E(L)²/Y`. -/
theorem integral_edgeTail_sq_ge {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 8 ≤ edgeRate L) :
    400 * Real.exp (-6) * kernelEnvelope L ^ 2 / edgeRate L ≤ ∫ u, edgeTail L R u ^ 2 := by
  have hY0 := edgeRate_pos L
  have hηY : edgeWidth L * edgeRate L = 1 := by unfold edgeWidth; field_simp
  have hη0 := edgeWidth_pos L
  have hT := integrable_edgeTail_sq (L := L) (by linarith) hR
  have hconst : 400 * Real.exp (-6) * kernelEnvelope L ^ 2 =
      (20 * Real.exp (-3) * kernelEnvelope L) ^ 2 := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]; norm_num
  have hlow : ∀ u ∈ Icc (L + edgeWidth L) (L + 2 * edgeWidth L),
      400 * Real.exp (-6) * kernelEnvelope L ^ 2 ≤ edgeTail L R u ^ 2 := fun u hu => by
    rw [hconst]
    exact pow_le_pow_left₀ (by have := kernelEnvelope_pos L; positivity)
      (edgeTail_ge_on_layer hL hR hY hu.1 hu.2) 2
  calc 400 * Real.exp (-6) * kernelEnvelope L ^ 2 / edgeRate L
      = ∫ _u in Icc (L + edgeWidth L) (L + 2 * edgeWidth L),
          400 * Real.exp (-6) * kernelEnvelope L ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
          max_eq_left (by linarith), show L + 2 * edgeWidth L - (L + edgeWidth L) = edgeWidth L by ring,
          div_eq_iff hY0.ne']
        nlinarith
    _ ≤ ∫ u in Icc (L + edgeWidth L) (L + 2 * edgeWidth L), edgeTail L R u ^ 2 :=
        setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne) hT.integrableOn
          measurableSet_Icc hlow
    _ ≤ ∫ u, edgeTail L R u ^ 2 :=
        setIntegral_le_integral hT (Filter.Eventually.of_forall fun _ => sq_nonneg _)

theorem contDiff_edgeTail (L R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (edgeTail L R) :=
  contDiff_riemannKernelReal.mul ((contDiff_edgeCutoff R 1).sub (contDiff_edgeCutoff L (edgeWidth L)))

theorem integral_edgeTail_nonneg {L : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) : 0 ≤ ∫ u, edgeTail L R u :=
  integral_nonneg fun u => edgeTail_nonneg hL hR u

/-- **Narrowness of the tail.** `(∫ T)² ≤ (C₀² e⁶/25)/Y · ∫ T²`. -/
theorem sq_integral_edgeTail_le {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) :
    (∫ u, edgeTail L R u) ^ 2 ≤
      riemannEnvelopeConst ^ 2 * Real.exp 6 / 25 / edgeRate L * ∫ u, edgeTail L R u ^ 2 := by
  have hY0 := edgeRate_pos L
  have hE := kernelEnvelope_pos L
  have hC := riemannEnvelopeConst_pos
  have h1 := integral_edgeTail_le hL hR hY
  have h0 := integral_edgeTail_nonneg (by linarith : (0 : ℝ) ≤ L) hR
  have h2 := integral_edgeTail_sq_ge hL hR (by linarith)
  have h3 : 2 * riemannEnvelopeConst * kernelEnvelope L / (edgeRate L - 9 / 2) ≤
      4 * riemannEnvelopeConst * kernelEnvelope L / edgeRate L := by
    rw [div_le_div_iff₀ (by linarith) hY0]; nlinarith [mul_pos hC hE]
  have h4 : (∫ u, edgeTail L R u) ^ 2 ≤ (4 * riemannEnvelopeConst * kernelEnvelope L / edgeRate L) ^ 2 :=
    pow_le_pow_left₀ h0 (h1.trans h3) 2
  have h6 : Real.exp 6 * Real.exp (-6) = 1 := by rw [← Real.exp_add]; norm_num
  have h5 : (4 * riemannEnvelopeConst * kernelEnvelope L / edgeRate L) ^ 2 =
      riemannEnvelopeConst ^ 2 * Real.exp 6 / 25 / edgeRate L *
        (400 * Real.exp (-6) * kernelEnvelope L ^ 2 / edgeRate L) := by
    field_simp
    nlinarith [h6]
  rw [h5] at h4
  refine h4.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-! ## Lags of the tail -/

theorem edgeMajorant_of_lt {A c L t : ℝ} (ht : L < t) :
    edgeMajorant A c L t = A * Real.exp (-c * (t - L)) := by
  unfold edgeMajorant; rw [indicator_of_mem (show t ∈ Ioi L from ht)]

/-- **Pointwise lag bound.** For a lag `x ≥ 0`, with `A = C₀E(L)` and `c = Y − 9/2`,
`T(u)T(u − x) ≤ A e^{−cx}(T(u) + T(u − x)) + A² e^{−c(x − 2L)} 1_{[L, x − L]}(u)`. -/
theorem edgeTail_mul_lag_le {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L) {x : ℝ}
    (hx : 0 ≤ x) (u : ℝ) :
    edgeTail L R u * edgeTail L R (u - x) ≤
      riemannEnvelopeConst * kernelEnvelope L * Real.exp (-(edgeRate L - 9 / 2) * x) *
          (edgeTail L R u + edgeTail L R (u - x)) +
        (riemannEnvelopeConst * kernelEnvelope L) ^ 2 *
          Real.exp (-(edgeRate L - 9 / 2) * (x - 2 * L)) * (Icc L (x - L)).indicator 1 u := by
  set A := riemannEnvelopeConst * kernelEnvelope L with hA
  set c := edgeRate L - 9 / 2 with hc
  have hA0 : 0 ≤ A := mul_nonneg riemannEnvelopeConst_pos.le (kernelEnvelope_pos L).le
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hT0 : ∀ v, 0 ≤ edgeTail L R v := edgeTail_nonneg (by linarith) hR
  have hmaj : ∀ v, L < |v| → edgeTail L R v ≤ A * Real.exp (-c * (|v| - L)) := fun v hv => by
    have := edgeTail_le_edgeMajorant (R := R) hL (by linarith) v
    rw [edgeMajorant_of_lt hv, ← hA, ← hc] at this
    exact this
  have hind : 0 ≤ (Icc L (x - L)).indicator (1 : ℝ → ℝ) u :=
    indicator_nonneg (fun _ _ => zero_le_one) u
  have hrest : 0 ≤ A ^ 2 * Real.exp (-c * (x - 2 * L)) * (Icc L (x - L)).indicator 1 u := by
    positivity
  have hfirst : 0 ≤ A * Real.exp (-c * x) * (edgeTail L R u + edgeTail L R (u - x)) :=
    mul_nonneg (by positivity) (add_nonneg (hT0 u) (hT0 (u - x)))
  -- trivial cases: one factor vanishes
  by_cases h1 : |u| ≤ L
  · have hz : edgeTail L R u * edgeTail L R (u - x) = 0 := by
      rw [edgeTail_eq_zero_of_le (by linarith) h1, zero_mul]
    rw [hz]; linarith
  by_cases h2 : |u - x| ≤ L
  · have hz : edgeTail L R u * edgeTail L R (u - x) = 0 := by
      rw [edgeTail_eq_zero_of_le (by linarith) h2, mul_zero]
    rw [hz]; linarith
  push Not at h1 h2
  have hexp_le : ∀ t : ℝ, x ≤ t → Real.exp (-c * t) ≤ Real.exp (-c * x) := fun t ht =>
    Real.exp_le_exp.mpr (by nlinarith)
  rcases lt_or_gt_of_ne (show u ≠ 0 by rintro rfl; simp at h1; linarith) with hu | hu
  · -- `u < 0`, so `u − x < 0`
    have hux : u - x < 0 := by linarith
    have hb := hmaj (u - x) h2
    rw [abs_of_neg hux] at hb
    rw [abs_of_neg hu] at h1
    have : Real.exp (-c * (-(u - x) - L)) ≤ Real.exp (-c * x) := hexp_le _ (by linarith)
    have h3 : edgeTail L R (u - x) ≤ A * Real.exp (-c * x) :=
      hb.trans (mul_le_mul_of_nonneg_left this hA0)
    have := mul_le_mul_of_nonneg_left h3 (hT0 u)
    nlinarith [hT0 u, hT0 (u - x), Real.exp_pos (-c * x)]
  · rw [abs_of_pos hu] at h1
    have ha := hmaj u (by rw [abs_of_pos hu]; exact h1)
    rw [abs_of_pos hu] at ha
    rcases le_or_gt 0 (u - x) with hux | hux
    · -- both nonnegative: `u − L ≥ x`
      rw [abs_of_nonneg hux] at h2
      have : Real.exp (-c * (u - L)) ≤ Real.exp (-c * x) := hexp_le _ (by linarith)
      have h3 : edgeTail L R u ≤ A * Real.exp (-c * x) :=
        ha.trans (mul_le_mul_of_nonneg_left this hA0)
      have := mul_le_mul_of_nonneg_right h3 (hT0 (u - x))
      nlinarith [hT0 u, hT0 (u - x), Real.exp_pos (-c * x)]
    · -- opposite sides: `u ∈ [L, x − L]`
      have hb := hmaj (u - x) h2
      rw [abs_of_neg hux] at hb h2
      have hmem : u ∈ Icc L (x - L) := ⟨h1.le, by linarith⟩
      rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
      have hprod : edgeTail L R u * edgeTail L R (u - x) ≤
          A * Real.exp (-c * (u - L)) * (A * Real.exp (-c * (-(u - x) - L))) :=
        mul_le_mul ha hb (hT0 _) (by positivity)
      have he : A * Real.exp (-c * (u - L)) * (A * Real.exp (-c * (-(u - x) - L))) =
          A ^ 2 * Real.exp (-c * (x - 2 * L)) := by
        rw [show A * Real.exp (-c * (u - L)) * (A * Real.exp (-c * (-(u - x) - L))) =
          A ^ 2 * (Real.exp (-c * (u - L)) * Real.exp (-c * (-(u - x) - L))) by ring,
          ← Real.exp_add]
        congr 2; ring
      linarith

theorem integrable_edgeTail {L : ℝ} (hL : 0 ≤ L) (hR : L + 2 ≤ R) : Integrable (edgeTail L R) :=
  (continuous_edgeTail L R).integrable_of_hasCompactSupport (hasCompactSupport_edgeTail hL hR)

/-- **Integrated lag bound.** For `x ≥ 0`,
`∫ T(u)T(u − x) du ≤ 2A e^{−cx} ∫T + A² e^{−c(x − 2L)} max(0, x − 2L)`. -/
theorem integral_edgeTail_lag_le {L : ℝ} (hL : 1 ≤ L) (hR : L + 2 ≤ R) (hY : 9 ≤ edgeRate L)
    {x : ℝ} (hx : 0 ≤ x) :
    ∫ u, edgeTail L R u * edgeTail L R (u - x) ≤
      2 * (riemannEnvelopeConst * kernelEnvelope L) * Real.exp (-(edgeRate L - 9 / 2) * x) *
          (∫ u, edgeTail L R u) +
        (riemannEnvelopeConst * kernelEnvelope L) ^ 2 *
          Real.exp (-(edgeRate L - 9 / 2) * (x - 2 * L)) * max 0 (x - 2 * L) := by
  have hT := integrable_edgeTail (by linarith : (0 : ℝ) ≤ L) hR
  have hTx : Integrable (fun u => edgeTail L R (u - x)) := hT.comp_sub_right x
  have hI : Integrable ((Icc L (x - L)).indicator (1 : ℝ → ℝ)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  set a := riemannEnvelopeConst * kernelEnvelope L * Real.exp (-(edgeRate L - 9 / 2) * x) with ha
  set b := (riemannEnvelopeConst * kernelEnvelope L) ^ 2 *
    Real.exp (-(edgeRate L - 9 / 2) * (x - 2 * L)) with hb
  have hmaj : Integrable (fun u => a * (edgeTail L R u + edgeTail L R (u - x)) +
      b * (Icc L (x - L)).indicator 1 u) :=
    ((hT.add hTx).const_mul a).add (hI.const_mul b)
  have hprod_int : Integrable (fun u => edgeTail L R u * edgeTail L R (u - x)) := by
    refine hmaj.mono' ((continuous_edgeTail L R).mul ((continuous_edgeTail L R).comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    have h0 := edgeTail_nonneg (by linarith) hR u
    have h1 := edgeTail_nonneg (by linarith) hR (u - x)
    rw [Real.norm_of_nonneg (mul_nonneg h0 h1)]
    exact edgeTail_mul_lag_le hL hR hY hx u
  calc ∫ u, edgeTail L R u * edgeTail L R (u - x)
      ≤ ∫ u, (a * (edgeTail L R u + edgeTail L R (u - x)) + b * (Icc L (x - L)).indicator 1 u) :=
        integral_mono hprod_int hmaj fun u => edgeTail_mul_lag_le hL hR hY hx u
    _ = a * (2 * ∫ u, edgeTail L R u) + b * max 0 (x - 2 * L) := by
        have hTT : Integrable (fun u => edgeTail L R u + edgeTail L R (u - x)) := hT.add hTx
        have h1 : Integrable (fun u => a * (edgeTail L R u + edgeTail L R (u - x))) :=
          hTT.const_mul a
        have h2 : Integrable (fun u => b * (Icc L (x - L)).indicator (1 : ℝ → ℝ) u) :=
          hI.const_mul b
        rw [integral_add h1 h2, integral_const_mul, integral_const_mul, integral_add hT hTx,
          integral_sub_right_eq_self, integral_indicator measurableSet_Icc]
        simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc]
        congr 2
        · ring
        · rw [max_comm]; congr 1; ring
    _ = _ := by rw [ha, hb]; ring

end

end RHTower
