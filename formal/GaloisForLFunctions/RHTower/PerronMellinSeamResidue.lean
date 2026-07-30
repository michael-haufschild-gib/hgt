import GaloisForLFunctions.RHTower.SoninPerronSupportTransfer

/-!
# Perron--Mellin seam residues

Exact cross-line Mellin coherence forces finite Dirichlet support.  This module replaces exact
coherence by an additive `L²` seam defect.  The full defect norm is not the native arithmetic
quantity: the variable Perron contour sees one coefficient-indexed pairing.

At every sufficiently deep negative line, Cauchy transport splits the exact coefficient charge into
a lower-supported source charge and a seam residue.  Beyond the reciprocal physical cutoff, the
source charge decays geometrically and the seam residue converges to the coefficient itself.  Thus
the infinite arithmetic tail is not an unexplained failure of coherence; it is recovered as the
asymptotic Perron coordinate of the cross-line defect.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set
open scoped ENNReal Topology Interval

/-- Cauchy--Schwarz in the exact `lpNorm` normalization used for complex `L²` representatives. -/
theorem norm_integral_mul_le_lpNorm_mul_lpNorm
    {u v : ℝ → ℂ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    ‖∫ t : ℝ, u t * v t‖ ≤ lpNorm u 2 volume * lpNorm v 2 volume := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := fun t : ℝ => ‖u t‖) (g := fun t : ℝ => ‖v t‖)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa using hu.norm) (by simpa using hv.norm)
  have hholder' :
      (∫ t : ℝ, ‖u t‖ * ‖v t‖) ≤
        Real.sqrt (∫ t : ℝ, ‖u t‖ ^ 2) *
          Real.sqrt (∫ t : ℝ, ‖v t‖ ^ 2) := by
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hholder
  calc
    ‖∫ t : ℝ, u t * v t‖ ≤ ∫ t : ℝ, ‖u t * v t‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖u t‖ * ‖v t‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∫ t : ℝ, ‖u t‖ ^ 2) *
          Real.sqrt (∫ t : ℝ, ‖v t‖ ^ 2) := hholder'
    _ = lpNorm u 2 volume * lpNorm v 2 volume := by
      rw [sqrt_integral_norm_sq_eq_lpNorm hu, sqrt_integral_norm_sq_eq_lpNorm hv]

/-- The variable Perron kernel on `Re s=-M` is in `L²`, with its exact geometric flank scale and
the fixed loss `sqrt π`. -/
theorem perronEAt_left_flank_memLp_and_lpNorm_le
    {n M : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    MemLp (fun y : ℝ => perronEAt n δ (↑(-(M : ℝ)) + ↑y * I)) 2 volume ∧
      lpNorm (fun y : ℝ => perronEAt n δ (↑(-(M : ℝ)) + ↑y * I)) 2 volume ≤
        (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) * Real.sqrt Real.pi := by
  let D : ℝ := perronSupportScaleAt n δ
  let C : ℝ := 4 * D ^ (1 - (M : ℝ))
  let e : ℝ → ℂ := fun y => perronEAt n δ (↑(-(M : ℝ)) + ↑y * I)
  let wR : ℝ → ℝ := fun y => (1 + y ^ 2)⁻¹
  let w : ℝ → ℂ := fun y => (wR y : ℂ)
  have hDpos : 0 < D := by
    dsimp [D, perronSupportScaleAt]
    linarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hwRcont : Continuous wR := by
    dsimp [wR]
    refine (continuous_const.add (continuous_id.pow 2)).inv₀ ?_
    intro y
    change 1 + y ^ 2 ≠ 0
    nlinarith [sq_nonneg y]
  have hwcont : Continuous w := Complex.continuous_ofReal.comp hwRcont
  have hwmeas : AEStronglyMeasurable w := hwcont.aestronglyMeasurable
  have hwRpos : ∀ y, 0 < wR y := by
    intro y
    dsimp [wR]
    positivity
  have hwRle : ∀ y, wR y ≤ 1 := by
    intro y
    dsimp [wR]
    exact (inv_le_one₀ (by nlinarith [sq_nonneg y] : 0 < 1 + y ^ 2)).2
      (by nlinarith [sq_nonneg y])
  have hwRsqle : ∀ y, wR y ^ 2 ≤ wR y := by
    intro y
    nlinarith [hwRpos y, hwRle y]
  have hwRInt : Integrable wR := by
    simpa only [wR] using integrable_inv_one_add_sq
  have hwRsqInt : Integrable (fun y => wR y ^ 2) :=
    hwRInt.mono' (hwRcont.aestronglyMeasurable.pow 2)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (wR y))]
        exact hwRsqle y)
  have hwsqInt : Integrable (fun y => ‖w y‖ ^ 2) := by
    simpa only [w, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hwRpos _)] using hwRsqInt
  have hwLp : MemLp w 2 volume :=
    (memLp_two_iff_integrable_sq_norm hwmeas).2 hwsqInt
  have hwSqBound : (∫ y : ℝ, ‖w y‖ ^ 2) ≤ Real.pi := by
    calc
      (∫ y : ℝ, ‖w y‖ ^ 2) = ∫ y : ℝ, wR y ^ 2 := by
        congr 1
        funext y
        simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hwRpos y)]
      _ ≤ ∫ y : ℝ, wR y := integral_mono hwRsqInt hwRInt hwRsqle
      _ = Real.pi := by simpa only [wR] using integral_univ_inv_one_add_sq
  have hwNorm : lpNorm w 2 volume ≤ Real.sqrt Real.pi := by
    rw [← sqrt_integral_norm_sq_eq_lpNorm hwLp]
    exact Real.sqrt_le_sqrt hwSqBound
  have hemeas : AEStronglyMeasurable e := by
    exact ((perronEAt_differentiable hn hδ0 hδn).continuous.comp
      (by fun_prop)).aestronglyMeasurable
  have hdom : ∀ y, ‖e y‖ ≤ ‖(C : ℂ) * w y‖ := by
    intro y
    have hE := perronEAt_left_flank_norm_le hn hM hδ0 hδn (y := y)
    calc
      ‖e y‖ ≤ C / (1 + y ^ 2) := by simpa only [e, C, D] using hE
      _ = ‖(C : ℂ) * w y‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC0]
        simp only [w, wR, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < (1 + y ^ 2)⁻¹), div_eq_mul_inv]
  have hCw : MemLp (fun y => (C : ℂ) * w y) 2 volume := hwLp.const_mul C
  have heLp : MemLp e 2 volume := hCw.of_le hemeas (Eventually.of_forall hdom)
  refine ⟨by simpa only [e] using heLp, ?_⟩
  have hmono : eLpNorm e 2 volume ≤ eLpNorm (fun y => (C : ℂ) * w y) 2 volume :=
    eLpNorm_mono_ae (Eventually.of_forall hdom)
  have hreal := ENNReal.toReal_mono hCw.eLpNorm_ne_top hmono
  rw [toReal_eLpNorm heLp.1, toReal_eLpNorm hCw.1] at hreal
  rw [show (fun y => (C : ℂ) * w y) = (C : ℂ) • w by rfl,
    lpNorm_const_smul] at hreal
  norm_cast at hreal
  rw [Real.norm_of_nonneg hC0] at hreal
  calc
    lpNorm (fun y : ℝ => perronEAt n δ (↑(-(M : ℝ)) + ↑y * I)) 2 volume =
        lpNorm e 2 volume := rfl
    _ ≤ C * lpNorm w 2 volume := hreal
    _ ≤ C * Real.sqrt Real.pi := mul_le_mul_of_nonneg_left hwNorm hC0
    _ = (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) *
        Real.sqrt Real.pi := by rfl

/-- If the horizontal edges escape and the left edge is integrable, Cauchy's rectangle identity
identifies the full right and left vertical integrals exactly. -/
theorem perron_left_integral_eq_right_integral_of_boundaryEscapeAt
    {F : ℂ → ℂ} {c δ : ℝ} {n M : ℕ}
    (hF : Differentiable ℂ F)
    (hE : Differentiable ℂ (perronEAt n δ))
    (hleft : Integrable (fun y : ℝ =>
      perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)))
    (hescape : HasPerronBoundaryEscapeAt F c n δ M) :
    (∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I)) =
      ∫ y : ℝ, perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I) := by
  rcases hescape with ⟨T, hTtop, _hTnonneg, hright, htop, hbot⟩
  have hGdiff : Differentiable ℂ (perronContourIntegrand F n δ) := by
    unfold perronContourIntegrand
    exact hF.mul hE
  let R : ℕ → ℂ := fun k => ∫ y in (-(T k))..(T k),
    perronContourIntegrand F n δ (↑c + ↑y * I)
  let Top : ℕ → ℂ := fun k => ∫ x in (-(M : ℝ))..c,
    perronContourIntegrand F n δ (↑x + ↑(T k) * I)
  let Bot : ℕ → ℂ := fun k => ∫ x in (-(M : ℝ))..c,
    perronContourIntegrand F n δ (↑x + ↑(-(T k)) * I)
  let L : ℕ → ℂ := fun k => ∫ y in (-(T k))..(T k),
    perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)
  have heq : ∀ k, I * R k = Top k - Bot k + I * L k := by
    intro k
    set z : ℂ := ⟨-(M : ℝ), -(T k)⟩ with hz
    set w : ℂ := ⟨c, T k⟩ with hw
    have hrect := integral_boundary_rect_eq_zero_of_differentiableOn
      (perronContourIntegrand F n δ) z w hGdiff.differentiableOn
    have hzre : z.re = -(M : ℝ) := rfl
    have hzim : z.im = -(T k) := rfl
    have hwre : w.re = c := rfl
    have hwim : w.im = T k := rfl
    rw [hzre, hzim, hwre, hwim] at hrect
    simp only [smul_eq_mul] at hrect
    dsimp [R, Top, Bot, L]
    linear_combination hrect
  have hleftlim : Tendsto L atTop
      (𝓝 (∫ y : ℝ, perronContourIntegrand F n δ
        (↑(-(M : ℝ)) + ↑y * I))) := by
    exact intervalIntegral_tendsto_integral hleft
      (tendsto_neg_atBot_iff.mpr hTtop) hTtop
  have hRlim : Tendsto R atTop
      (𝓝 (∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I))) := by
    simpa only [R] using hright
  have hToplim : Tendsto Top atTop (𝓝 0) := by simpa only [Top] using htop
  have hBotlim : Tendsto Bot atTop (𝓝 0) := by simpa only [Bot] using hbot
  have hleftlim' : Tendsto L atTop
      (𝓝 (∫ y : ℝ, perronContourIntegrand F n δ
        (↑(-(M : ℝ)) + ↑y * I))) := hleftlim
  have hLHS := hRlim.const_mul I
  have hRHS := (hToplim.sub hBotlim).add (hleftlim'.const_mul I)
  have hRHS' : Tendsto (fun k => I * R k) atTop
      (𝓝 (I * ∫ y : ℝ, perronContourIntegrand F n δ
        (↑(-(M : ℝ)) + ↑y * I))) := by
    simpa using hRHS.congr' (Eventually.of_forall fun k => (heq k).symm)
  have hprod := tendsto_nhds_unique hLHS hRHS'
  exact mul_left_cancel₀ (by simp : I ≠ 0) hprod

/-- An additive Mellin defect decomposition at one negative integer line. -/
def HasCrossLineMellinDefectAt
    (F : ℂ → ℂ) (g : SoninL2) (τ : ℝ)
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (Δ : ℕ → SoninL2) (M : ℕ) : Prop :=
  (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I)) =ᵐ[volume]
    fun t => negativeMellinL2Trace g τ hsupp M t + Δ M t

/-- **Additive cross-line Mellin defect.**  Every negative integer line of `F` is the normalized
weighted trace of a common source plus an `L²` seam class `Δ M`. -/
def HasCrossLineMellinDefect
    (F : ℂ → ℂ) (g : SoninL2) (τ : ℝ)
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (Δ : ℕ → SoninL2) : Prop :=
  ∀ M : ℕ, HasCrossLineMellinDefectAt F g τ hsupp Δ M

/-- The contour only needs the additive defect decomposition eventually in the negative depth. -/
def HasEventuallyCrossLineMellinDefect
    (F : ℂ → ℂ) (g : SoninL2) (τ : ℝ)
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (Δ : ℕ → SoninL2) : Prop :=
  ∀ᶠ M : ℕ in atTop, HasCrossLineMellinDefectAt F g τ hsupp Δ M

/-- An all-depth decomposition supplies the eventual interface consumed by asymptotic extraction. -/
theorem HasCrossLineMellinDefect.hasEventually
    {F : ℂ → ℂ} {g : SoninL2} {τ : ℝ}
    {hsupp : HasAELowerSupport (fun t => g t) τ} {Δ : ℕ → SoninL2}
    (hdef : HasCrossLineMellinDefect F g τ hsupp Δ) :
    HasEventuallyCrossLineMellinDefect F g τ hsupp Δ :=
  Eventually.of_forall hdef

/-- Exact coherence is the zero-defect specialization of additive cross-line coherence. -/
theorem HasCoherentNegativeMellinTraces.hasCrossLineMellinDefect_zero
    {F : ℂ → ℂ} {g : SoninL2} {τ : ℝ}
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (hcoh : HasCoherentNegativeMellinTraces F g τ hsupp) :
    HasCrossLineMellinDefect F g τ hsupp (fun _ => 0) := by
  intro M
  filter_upwards [hcoh M, Lp.coeFn_zero ℂ 2 volume] with t ht hz
  simpa only [Pi.zero_apply, hz, add_zero] using ht

/-- The normalized variable-Perron charge carried by the lower-supported Mellin source trace. -/
def negativeMellinSourcePerronCharge
    (g : SoninL2) (τ : ℝ) (hsupp : HasAELowerSupport (fun t => g t) τ)
    (M n : ℕ) (δ : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
    negativeMellinL2Trace g τ hsupp M t *
      perronEAt n δ (↑(-(M : ℝ)) + ↑t * I)

/-- The normalized variable-Perron coordinate of the additive seam defect. -/
def perronMellinSeamResidue
    (Δ : ℕ → SoninL2) (M n : ℕ) (δ : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
    Δ M t * perronEAt n δ (↑(-(M : ℝ)) + ↑t * I)

/-- The knot-width-normalized seam residue, on the scale of the Dirichlet coefficient itself. -/
def perronMellinSeamCoefficient
    (Δ : ℕ → SoninL2) (M n : ℕ) (δ : ℝ) : ℂ :=
  (δ : ℂ)⁻¹ * perronMellinSeamResidue Δ M n δ

/-- The source charge is bounded by the product of its negative-line trace radius and the exact
variable Perron flank scale. -/
theorem negativeMellinSourcePerronCharge_norm_le
    (g : SoninL2) (τ : ℝ) (hsupp : HasAELowerSupport (fun t => g t) τ)
    {M n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    ‖negativeMellinSourcePerronCharge g τ hsupp M n δ‖ ≤
      perronFlankL2Constant *
        (Real.exp (-(M : ℝ) * τ) * ‖g‖) *
          perronSupportScaleAt n δ ^ (1 - (M : ℝ)) := by
  let T : SoninL2 := negativeMellinL2Trace g τ hsupp M
  let E : ℝ → ℂ := fun t => perronEAt n δ (↑(-(M : ℝ)) + ↑t * I)
  have hTLp : MemLp (fun t => T t) 2 volume := Lp.memLp T
  have hELp : MemLp E 2 volume := by
    simpa only [E] using
      (perronEAt_left_flank_memLp_and_lpNorm_le hn hM hδ0 hδn).1
  have hTnorm : lpNorm (fun t => T t) 2 volume = ‖T‖ := by
    calc
      lpNorm (fun t => T t) 2 volume =
          (eLpNorm (fun t => T t) 2 volume).toReal :=
        (toReal_eLpNorm hTLp.1).symm
      _ = ‖T‖ := by rw [Lp.norm_def]
  have hTbound : lpNorm (fun t => T t) 2 volume ≤
      Real.exp (-(M : ℝ) * τ) * ‖g‖ := by
    rw [hTnorm]
    exact negativeMellinL2Trace_norm_le g τ hsupp M
  have hEbound : lpNorm E 2 volume ≤
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) * Real.sqrt Real.pi := by
    simpa only [E] using
      (perronEAt_left_flank_memLp_and_lpNorm_le hn hM hδ0 hδn).2
  have hint := norm_integral_mul_le_lpNorm_mul_lpNorm hTLp hELp
  have hsource0 : 0 ≤ Real.exp (-(M : ℝ) * τ) * ‖g‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hDpos : 0 < perronSupportScaleAt n δ := by
    rw [perronSupportScaleAt]
    linarith
  have hE0 : 0 ≤
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) * Real.sqrt Real.pi := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hDpos.le _))
      (Real.sqrt_nonneg _)
  unfold negativeMellinSourcePerronCharge
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ, T t * E t‖ ≤
      (1 / (2 * Real.pi)) *
        (lpNorm (fun t => T t) 2 volume * lpNorm E 2 volume) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
        ((Real.exp (-(M : ℝ) * τ) * ‖g‖) *
          ((4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) *
            Real.sqrt Real.pi)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hTbound hEbound
        (lpNorm_nonneg : 0 ≤ lpNorm E 2 volume) hsource0
    _ = perronFlankL2Constant *
        (Real.exp (-(M : ℝ) * τ) * ‖g‖) *
          perronSupportScaleAt n δ ^ (1 - (M : ℝ)) := by
      unfold perronFlankL2Constant
      field_simp [Real.pi_ne_zero]
      ring

/-- For a Sonin source at cutoff `q`, the source charge has exact geometric radius `q⁻¹`. -/
theorem soninSourcePerronCharge_norm_le
    {q : ℝ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    {M n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    ‖negativeMellinSourcePerronCharge (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) M n δ‖ ≤
      perronFlankL2Constant * (q⁻¹ ^ M * ‖logEvenUnitary f‖) *
        perronSupportScaleAt n δ ^ (1 - (M : ℝ)) := by
  simpa only [exp_neg_nat_mul_log_eq_inv_pow hq] using
    negativeMellinSourcePerronCharge_norm_le (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) hn hM hδ0 hδn

/-- Beyond the reciprocal physical cutoff, the source contribution to a variable-Perron
coefficient charge tends to zero. -/
theorem soninSourcePerronCharge_tendsto_zero
    {q : ℝ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hδ0 : 0 < δ)
    (hδn : δ < (n : ℝ))
    (hgap : q⁻¹ < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ =>
      negativeMellinSourcePerronCharge (logEvenUnitary f) (Real.log q)
        (logEvenUnitary_hasAELowerSupport hq f hf) M n δ) atTop (𝓝 0) := by
  let H : ℕ → ℝ := fun M =>
    perronFlankL2Constant * (q⁻¹ ^ M * ‖logEvenUnitary f‖)
  have hR0 : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  have hD0 : 0 < perronSupportScaleAt n δ := by
    rw [perronSupportScaleAt]
    linarith
  have hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M := by
    exact Eventually.of_forall fun M => by
      dsimp [H]
      exact mul_nonneg perronFlankL2Constant_pos.le
        (mul_nonneg (pow_nonneg hR0 M) (norm_nonneg _))
  have hH : ∀ᶠ M : ℕ in atTop,
      H M ≤ (perronFlankL2Constant * ‖logEvenUnitary f‖) * q⁻¹ ^ M := by
    exact Eventually.of_forall fun M => by
      dsimp [H]
      ring_nf
      rfl
  have hdecay : Tendsto (fun M : ℕ =>
      H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) atTop (𝓝 0) :=
    tendsto_flank_product_of_geometric_envelope hR0 hD0 hgap hH0 hH
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop 2] with M hM
    exact soninSourcePerronCharge_norm_le hq f hf hn hM hδ0 hδn
  · exact hdecay

/-- **Exact coefficient charge splitting at one depth.**  A local additive defect and boundary
escape split the arithmetic coefficient charge into source charge and seam residue. -/
theorem coefficient_eq_sourceCharge_add_seamResidue_of_defectAt
    {F : ℂ → ℂ} {g : SoninL2} {τ c δ : ℝ} {coeff : ℕ → ℂ}
    {Δ : ℕ → SoninL2} {n M : ℕ}
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (hdef : HasCrossLineMellinDefectAt F g τ hsupp Δ M)
    (hescape : HasPerronBoundaryEscapeAt F c n δ M)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδn : δ < (n : ℝ)) :
    coeff n * (δ : ℂ) =
      negativeMellinSourcePerronCharge g τ hsupp M n δ +
        perronMellinSeamResidue Δ M n δ := by
  let T : ℝ → ℂ := fun t => negativeMellinL2Trace g τ hsupp M t
  let D : ℝ → ℂ := fun t => Δ M t
  let E : ℝ → ℂ := fun t => perronEAt n δ (↑(-(M : ℝ)) + ↑t * I)
  let line : ℝ → ℂ := fun t => F (↑(-(M : ℝ)) + ↑t * I)
  have hTLp : MemLp T 2 volume := Lp.memLp _
  have hDLp : MemLp D 2 volume := Lp.memLp _
  have hELp : MemLp E 2 volume := by
    simpa only [E] using
      (perronEAt_left_flank_memLp_and_lpNorm_le hn hM hδ0 hδn).1
  have hlineDef : line =ᵐ[volume] fun t => T t + D t := by
    simpa only [line, T, D] using! hdef
  have hlineLp : MemLp line 2 volume := (hTLp.add hDLp).ae_eq hlineDef.symm
  have hleftInt : Integrable (fun t => line t * E t) := hlineLp.integrable_mul hELp
  have hsourceInt : Integrable (fun t => T t * E t) := hTLp.integrable_mul hELp
  have hdefectInt : Integrable (fun t => D t * E t) := hDLp.integrable_mul hELp
  have hboundary :
      (∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I)) =
        ∫ y : ℝ, line y * E y := by
    have hleftInt' : Integrable (fun y : ℝ =>
        perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)) := by
      simpa only [perronContourIntegrand, line, E] using hleftInt
    simpa only [perronContourIntegrand, line, E] using
      perron_left_integral_eq_right_integral_of_boundaryEscapeAt hF
        (perronEAt_differentiable hn hδ0 hδn) hleftInt' hescape
  have hsplit :
      (∫ y : ℝ, line y * E y) =
        (∫ y : ℝ, T y * E y) + ∫ y : ℝ, D y * E y := by
    rw [← integral_add hsourceInt hdefectInt]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hlineDef] with y hy
    rw [hy]
    ring
  have hrepr : coeff n * (δ : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, perronContourIntegrand F n δ (↑c + ↑t * I) := by
    simpa only [perronContourIntegrand] using
      perronSecondDiffAt_integral hc0 hsum hF hFeq hn hδ0 hδ1
  rw [hboundary, hsplit] at hrepr
  simpa only [negativeMellinSourcePerronCharge, perronMellinSeamResidue,
    T, D, E, smul_add] using hrepr

/-- **One-depth coefficient splitting from horizontal carrier mass.**  The weighted horizontal
mass constructs boundary escape internally, so the escape Prop disappears from the public
statement. -/
theorem coefficient_eq_sourceCharge_add_seamResidue_of_defectAt_carrierHorizontalMassAt
    {F : ℂ → ℂ} {g : SoninL2} {τ c δ : ℝ} {coeff : ℕ → ℂ}
    {Δ : ℕ → SoninL2} {n M : ℕ}
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (hdef : HasCrossLineMellinDefectAt F g τ hsupp Δ M)
    (hhorizontal : HasPerronCarrierHorizontalMassAt F c M)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδn : δ < (n : ℝ)) :
    coeff n * (δ : ℂ) =
      negativeMellinSourcePerronCharge g τ hsupp M n δ +
        perronMellinSeamResidue Δ M n δ :=
  coefficient_eq_sourceCharge_add_seamResidue_of_defectAt hsupp hdef
    (hasPerronBoundaryEscapeAt_of_carrierHorizontalMassAt
      hhorizontal hc0 hsum hF hFeq hn hδ0 hδn)
    hc0 hsum hF hFeq hn hM hδ0 hδ1 hδn

/-- **Exact coefficient charge splitting.**  At every depth with boundary escape, the arithmetic
coefficient charge is the sum of the lower-supported source charge and the seam residue. -/
theorem coefficient_eq_sourceCharge_add_seamResidue
    {F : ℂ → ℂ} {g : SoninL2} {τ c δ : ℝ} {coeff : ℕ → ℂ}
    {Δ : ℕ → SoninL2} {n M : ℕ}
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (hdef : HasCrossLineMellinDefect F g τ hsupp Δ)
    (hescape : HasPerronBoundaryEscapeAt F c n δ M)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδn : δ < (n : ℝ)) :
    coeff n * (δ : ℂ) =
      negativeMellinSourcePerronCharge g τ hsupp M n δ +
        perronMellinSeamResidue Δ M n δ :=
  coefficient_eq_sourceCharge_add_seamResidue_of_defectAt hsupp (hdef M) hescape
    hc0 hsum hF hFeq hn hM hδ0 hδ1 hδn

/-- **All-depth coefficient splitting from horizontal carrier mass.**  The cross-line defect may
be supplied at every depth, but boundary escape is no longer an independent interface. -/
theorem coefficient_eq_sourceCharge_add_seamResidue_of_carrierHorizontalMassAt
    {F : ℂ → ℂ} {g : SoninL2} {τ c δ : ℝ} {coeff : ℕ → ℂ}
    {Δ : ℕ → SoninL2} {n M : ℕ}
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (hdef : HasCrossLineMellinDefect F g τ hsupp Δ)
    (hhorizontal : HasPerronCarrierHorizontalMassAt F c M)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hδn : δ < (n : ℝ)) :
    coeff n * (δ : ℂ) =
      negativeMellinSourcePerronCharge g τ hsupp M n δ +
        perronMellinSeamResidue Δ M n δ :=
  coefficient_eq_sourceCharge_add_seamResidue_of_defectAt_carrierHorizontalMassAt
    hsupp (hdef M) hhorizontal hc0 hsum hF hFeq hn hM hδ0 hδ1 hδn

/-- **Arithmetic tail recovery by the seam.**  If `n-δ` lies beyond the reciprocal Sonin cutoff,
the Perron--Mellin seam residue converges exactly to `δ * coeff n`.  No geometric norm bound on the
defect is assumed. -/
theorem soninPerronMellinSeamResidue_tendsto_coefficient
    {F : ℂ → ℂ} {q c δ : ℝ} {coeff : ℕ → ℂ} {Δ : ℕ → SoninL2}
    {n : ℕ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    (hdef : HasCrossLineMellinDefect F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) Δ)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap : q⁻¹ < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ => perronMellinSeamResidue Δ M n δ) atTop
      (𝓝 (coeff n * (δ : ℂ))) := by
  let hsupp := logEvenUnitary_hasAELowerSupport hq f hf
  let source : ℕ → ℂ := fun M =>
    negativeMellinSourcePerronCharge (logEvenUnitary f) (Real.log q) hsupp M n δ
  have hsource : Tendsto source atTop (𝓝 0) := by
    simpa only [source, hsupp] using
      soninSourcePerronCharge_tendsto_zero hq f hf hn hδ0 hδn hgap
  have hvarEscape : HasVariablePerronBoundaryEscape F c n :=
    (hhorizontal.hasVariablePerronHorizontalEscape hF hc0 hn).hasVariablePerronBoundaryEscape
      hc0 hsum hF hFeq hn
  have hescape : ∀ᶠ M : ℕ in atTop, HasPerronBoundaryEscapeAt F c n δ M :=
    hvarEscape δ hδ0 hδ1 hδn
  have heq : ∀ᶠ M : ℕ in atTop,
      perronMellinSeamResidue Δ M n δ = coeff n * (δ : ℂ) - source M := by
    filter_upwards [hescape, eventually_ge_atTop 2] with M hMescape hM
    have hsplit := coefficient_eq_sourceCharge_add_seamResidue
      hsupp hdef hMescape hc0 hsum hF hFeq hn hM hδ0 hδ1 hδn
    dsimp only [source]
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hsplit.symm
  have hlim : Tendsto (fun M => coeff n * (δ : ℂ) - source M) atTop
      (𝓝 (coeff n * (δ : ℂ))) := by
    simpa using tendsto_const_nhds.sub hsource
  exact hlim.congr' (heq.mono fun _ h => h.symm)

/-- The arithmetic-tail recovery theorem only requires the cross-line defect decomposition
eventually in the negative depth. -/
theorem soninPerronMellinSeamResidue_tendsto_coefficient_of_eventuallyDefect
    {F : ℂ → ℂ} {q c δ : ℝ} {coeff : ℕ → ℂ} {Δ : ℕ → SoninL2}
    {n : ℕ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    (hdef : HasEventuallyCrossLineMellinDefect F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) Δ)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap : q⁻¹ < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ => perronMellinSeamResidue Δ M n δ) atTop
      (𝓝 (coeff n * (δ : ℂ))) := by
  let hsupp := logEvenUnitary_hasAELowerSupport hq f hf
  let source : ℕ → ℂ := fun M =>
    negativeMellinSourcePerronCharge (logEvenUnitary f) (Real.log q) hsupp M n δ
  have hsource : Tendsto source atTop (𝓝 0) := by
    simpa only [source, hsupp] using
      soninSourcePerronCharge_tendsto_zero hq f hf hn hδ0 hδn hgap
  have hvarEscape : HasVariablePerronBoundaryEscape F c n :=
    (hhorizontal.hasVariablePerronHorizontalEscape hF hc0 hn).hasVariablePerronBoundaryEscape
      hc0 hsum hF hFeq hn
  have hescape : ∀ᶠ M : ℕ in atTop, HasPerronBoundaryEscapeAt F c n δ M :=
    hvarEscape δ hδ0 hδ1 hδn
  have heq : ∀ᶠ M : ℕ in atTop,
      perronMellinSeamResidue Δ M n δ = coeff n * (δ : ℂ) - source M := by
    filter_upwards [hdef, hescape, eventually_ge_atTop 2] with M hMdef hMescape hM
    have hsplit := coefficient_eq_sourceCharge_add_seamResidue_of_defectAt
      hsupp hMdef hMescape hc0 hsum hF hFeq hn hM hδ0 hδ1 hδn
    dsimp only [source]
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hsplit.symm
  have hlim : Tendsto (fun M => coeff n * (δ : ℂ) - source M) atTop
      (𝓝 (coeff n * (δ : ℂ))) := by
    simpa using tendsto_const_nhds.sub hsource
  exact hlim.congr' (heq.mono fun _ h => h.symm)

/-- Eventual additive coherence is enough for the normalized seam coordinate to recover the
Dirichlet coefficient itself. -/
theorem soninPerronMellinSeamCoefficient_tendsto_coefficient_of_eventuallyDefect
    {F : ℂ → ℂ} {q c δ : ℝ} {coeff : ℕ → ℂ} {Δ : ℕ → SoninL2}
    {n : ℕ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    (hdef : HasEventuallyCrossLineMellinDefect F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) Δ)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap : q⁻¹ < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ => perronMellinSeamCoefficient Δ M n δ) atTop
      (𝓝 (coeff n)) := by
  have hres := soninPerronMellinSeamResidue_tendsto_coefficient_of_eventuallyDefect
    hq f hf hdef hhorizontal hc0 hsum hF hFeq hn hδ0 hδ1 hδn hgap
  have hδne : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ0
  have hscaled := hres.const_mul (δ : ℂ)⁻¹
  have hval : (δ : ℂ)⁻¹ * (coeff n * (δ : ℂ)) = coeff n := by
    calc
      (δ : ℂ)⁻¹ * (coeff n * (δ : ℂ)) = coeff n * ((δ : ℂ)⁻¹ * (δ : ℂ)) := by ring
      _ = coeff n := by rw [inv_mul_cancel₀ hδne, mul_one]
  rw [hval] at hscaled
  simpa only [perronMellinSeamCoefficient] using hscaled

/-- The normalized seam coordinate converges to the Dirichlet coefficient itself.  This removes the
auxiliary Perron knot width from the recovered arithmetic datum. -/
theorem soninPerronMellinSeamCoefficient_tendsto_coefficient
    {F : ℂ → ℂ} {q c δ : ℝ} {coeff : ℕ → ℂ} {Δ : ℕ → SoninL2}
    {n : ℕ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    (hdef : HasCrossLineMellinDefect F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) Δ)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap : q⁻¹ < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ => perronMellinSeamCoefficient Δ M n δ) atTop
      (𝓝 (coeff n)) := by
  have hres := soninPerronMellinSeamResidue_tendsto_coefficient
    hq f hf hdef hhorizontal hc0 hsum hF hFeq hn hδ0 hδ1 hδn hgap
  have hδne : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ0
  have hscaled := hres.const_mul (δ : ℂ)⁻¹
  have hval : (δ : ℂ)⁻¹ * (coeff n * (δ : ℂ)) = coeff n := by
    calc
      (δ : ℂ)⁻¹ * (coeff n * (δ : ℂ)) = coeff n * ((δ : ℂ)⁻¹ * (δ : ℂ)) := by ring
      _ = coeff n := by rw [inv_mul_cancel₀ hδne, mul_one]
  rw [hval] at hscaled
  simpa only [perronMellinSeamCoefficient] using hscaled

/-- A nonzero Dirichlet coefficient makes its normalized seam coordinate eventually nonzero. -/
theorem soninPerronMellinSeamCoefficient_eventually_ne_zero
    {F : ℂ → ℂ} {q c δ : ℝ} {coeff : ℕ → ℂ} {Δ : ℕ → SoninL2}
    {n : ℕ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    (hdef : HasCrossLineMellinDefect F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) Δ)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap : q⁻¹ < perronSupportScaleAt n δ) (han : coeff n ≠ 0) :
    ∀ᶠ M : ℕ in atTop, perronMellinSeamCoefficient Δ M n δ ≠ 0 := by
  have hlim := soninPerronMellinSeamCoefficient_tendsto_coefficient
    hq f hf hdef hhorizontal hc0 hsum hF hFeq hn hδ0 hδ1 hδn hgap
  exact hlim.eventually (isOpen_compl_singleton.mem_nhds han)

/-- **Knot-width independence.**  Any two admissible variable-Perron probes beyond the physical
radius recover the same coefficient, so their normalized seam coordinates differ by `o(1)`. -/
theorem soninPerronMellinSeamCoefficient_sub_tendsto_zero
    {F : ℂ → ℂ} {q c δ₁ δ₂ : ℝ} {coeff : ℕ → ℂ} {Δ : ℕ → SoninL2}
    {n : ℕ} (hq : 0 < q) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier q)
    (hdef : HasCrossLineMellinDefect F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) Δ)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n)
    (hδ₁0 : 0 < δ₁) (hδ₁1 : δ₁ < 1) (hδ₁n : δ₁ < (n : ℝ))
    (hgap₁ : q⁻¹ < perronSupportScaleAt n δ₁)
    (hδ₂0 : 0 < δ₂) (hδ₂1 : δ₂ < 1) (hδ₂n : δ₂ < (n : ℝ))
    (hgap₂ : q⁻¹ < perronSupportScaleAt n δ₂) :
    Tendsto (fun M : ℕ =>
      perronMellinSeamCoefficient Δ M n δ₁ -
        perronMellinSeamCoefficient Δ M n δ₂) atTop (𝓝 0) := by
  have h₁ := soninPerronMellinSeamCoefficient_tendsto_coefficient
    hq f hf hdef hhorizontal hc0 hsum hF hFeq hn hδ₁0 hδ₁1 hδ₁n hgap₁
  have h₂ := soninPerronMellinSeamCoefficient_tendsto_coefficient
    hq f hf hdef hhorizontal hc0 hsum hF hFeq hn hδ₂0 hδ₂1 hδ₂n hgap₂
  simpa using h₁.sub h₂

end RHTower
