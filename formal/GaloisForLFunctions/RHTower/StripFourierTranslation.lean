import GaloisForLFunctions.RHTower.SuzukiGammaStripFourierWeight
import GaloisForLFunctions.HTGeometry.CompactTestTransformOrder

/-!
# Vector-valued Paley–Wiener translation on the unit strip

A holomorphic function on the open unit strip which grows at most polynomially on every closed
substrip and is square integrable on every interior line has one single frequency profile: its `L²`
inverse Fourier transforms on the different lines differ exactly by the exponential weights
`e^{2πσL}`.

The mechanism is the same at this level of generality as for the Gamma seam.  Multiplying the datum
by the entire Fourier extension of a compactly supported smooth test function produces a holomorphic
integrand which decays quadratically along every horizontal line of a closed substrip — the test
transform decays faster than every power, so it absorbs the polynomial growth — and Cauchy's theorem
for rectangles then moves the line of integration freely.  The multiplication formula for
tempered distributions turns that shift into an identity between the `L²` transforms, and the
du Bois-Reymond lemma for locally integrable functions converts it into an almost-everywhere
identity.

No pointwise inversion is available, because for `σ ≤ 1/2` the boundary datum is only `L²`; the whole
argument is a pairing argument.
-/

open Set Complex MeasureTheory Filter SchwartzMap

open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- A holomorphic strip datum: holomorphic on the open unit strip, of at most polynomial growth on
every closed substrip, and square integrable on every interior horizontal line. -/
structure StripDatum (f : ℂ → X) : Prop where
  /-- Holomorphy on the open unit strip. -/
  diff : DifferentiableOn ℂ f (imStrip 0 1)
  /-- Polynomial growth on every closed substrip. -/
  bdd : ∀ σ₀ σ₁ : ℝ, 0 < σ₀ → σ₀ ≤ σ₁ → σ₁ < 1 →
    ∃ (D : ℝ) (n : ℕ), 0 ≤ D ∧ ∀ z : ℂ, z.im ∈ Icc σ₀ σ₁ → ‖f z‖ ≤ D * (1 + ‖z‖) ^ n
  /-- Square integrability on every interior line. -/
  memLp : ∀ σ : ℝ, σ ∈ Ioo (0 : ℝ) 1 →
    MemLp (fun x : ℝ => f ((x : ℂ) + (σ : ℂ) * Complex.I)) 2 (volume : Measure ℝ)

variable {f : ℂ → X}

/-- The boundary datum on the interior line of height `σ`. -/
def stripDatumLine (f : ℂ → X) (σ : ℝ) : ℝ → X :=
  fun x => f ((x : ℂ) + (σ : ℂ) * Complex.I)

/-- The boundary datum as an `L²` class. -/
def stripDatumLp (hf : StripDatum f) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    Lp X 2 (volume : Measure ℝ) :=
  (hf.memLp σ hσ).toLp _

omit [CompleteSpace X] in
theorem continuous_stripDatumLine (hf : StripDatum f) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    Continuous (stripDatumLine f σ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hline : ContinuousAt (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I)) x := by fun_prop
  have hmem : ((x : ℂ) + (σ : ℂ) * Complex.I) ∈ imStrip 0 1 := by
    constructor <;> simp [hσ.1, hσ.2]
  have hdiff : DifferentiableAt ℂ f ((x : ℂ) + (σ : ℂ) * Complex.I) :=
    hf.diff.differentiableAt ((isOpen_imStrip 0 1).mem_nhds hmem)
  have hcomp : ContinuousAt (f ∘ (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I))) x :=
    ContinuousAt.comp hdiff.continuousAt hline
  exact hcomp

/-- The paired integrand: the rescaled test transform times the strip datum. -/
def datumPaired (ψ : ℝ → ℂ) (f : ℂ → X) (z : ℂ) : X :=
  testTransformTwoPi ψ z • f z

omit [CompleteSpace X] in
theorem differentiableAt_datumPaired {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hf : StripDatum f) {σ σ' : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : z.im ∈ uIcc σ σ') :
    DifferentiableAt ℂ (datumPaired ψ f) z := by
  have hmem : z ∈ imStrip 0 1 := mem_imStrip_of_mem_uIcc hσ hσ' hz
  have hfd : DifferentiableAt ℂ f z :=
    hf.diff.differentiableAt ((isOpen_imStrip 0 1).mem_nhds hmem)
  exact (differentiable_testTransformTwoPi hψc hψs z).smul hfd

omit [CompleteSpace X] in
/-- The paired integrand decays quadratically in the real part, uniformly across the substrip. -/
theorem exists_bound_datumPaired {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) (hf : StripDatum f) {σ σ' : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, z.im ∈ uIcc σ σ' →
      ‖datumPaired ψ f z‖ ≤ A / (1 + z.re ^ 2) := by
  obtain ⟨D, n, hD0, hD⟩ := hf.bdd (σ ⊓ σ') (σ ⊔ σ') (lt_min hσ.1 hσ'.1) inf_le_sup
    (max_lt hσ.2 hσ'.2)
  obtain ⟨C, hC0, hC⟩ := exists_testTransformTwoPi_decay_order hψ hψs σ σ' (n + 2)
  refine ⟨C * D, by positivity, fun z hz => ?_⟩
  have hzIcc : z.im ∈ Icc (σ ⊓ σ') (σ ⊔ σ') := hz
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hre : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hcollapse : (C / (1 + ‖z‖) ^ (n + 2)) * (D * (1 + ‖z‖) ^ n)
      = (C * D) / (1 + ‖z‖) ^ 2 := by
    have hne : ((1 : ℝ) + ‖z‖) ^ n ≠ 0 := by positivity
    rw [pow_add]
    field_simp
  calc ‖datumPaired ψ f z‖
      = ‖testTransformTwoPi ψ z‖ * ‖f z‖ := by rw [datumPaired, norm_smul]
    _ ≤ (C / (1 + ‖z‖) ^ (n + 2)) * (D * (1 + ‖z‖) ^ n) :=
        mul_le_mul (hC z hz) (hD z hzIcc) (norm_nonneg _) (by positivity)
    _ = (C * D) / (1 + ‖z‖) ^ 2 := hcollapse
    _ ≤ (C * D) / (1 + z.re ^ 2) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        nlinarith [hz0, hre]

omit [CompleteSpace X] in
theorem continuous_datumPaired_line {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hf : StripDatum f) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun x : ℝ => datumPaired ψ f ((x : ℂ) + (σ : ℂ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hline : ContinuousAt (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I)) x := by fun_prop
  have hmem : ((x : ℂ) + (σ : ℂ) * Complex.I).im ∈ uIcc σ σ := by simp
  have hdiff : DifferentiableAt ℂ (datumPaired ψ f) ((x : ℂ) + (σ : ℂ) * Complex.I) :=
    differentiableAt_datumPaired hψc hψs hf hσ hσ hmem
  have hcomp : ContinuousAt ((datumPaired ψ f)
      ∘ (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I))) x :=
    ContinuousAt.comp hdiff.continuousAt hline
  exact hcomp

omit [CompleteSpace X] in
theorem integrable_datumPaired_line {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) (hf : StripDatum f) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun x : ℝ => datumPaired ψ f ((x : ℂ) + (σ : ℂ) * Complex.I)) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_datumPaired hψ hψs hf hσ hσ
  have hint : Integrable (fun x : ℝ => A / (1 + x ^ 2)) := by
    have := integrable_inv_one_add_sq.const_mul A
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [div_eq_mul_inv]
  refine Integrable.mono' hint
    ((continuous_datumPaired_line hψ.continuous hψs hf hσ).aestronglyMeasurable) ?_
  filter_upwards with x
  have hmem : ((x : ℂ) + (σ : ℂ) * Complex.I).im ∈ uIcc σ σ := by simp
  have hre : ((x : ℂ) + (σ : ℂ) * Complex.I).re = x := by simp
  have := hA _ hmem
  rwa [hre] at this

omit [CompleteSpace X] in
/-- **The pairing is independent of the height.** -/
theorem datumPaired_line_shift {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) (hf : StripDatum f) {σ σ' : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1) :
    (∫ x : ℝ, datumPaired ψ f ((x : ℂ) + (σ : ℂ) * Complex.I))
      = ∫ x : ℝ, datumPaired ψ f ((x : ℂ) + (σ' : ℂ) * Complex.I) := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_datumPaired hψ hψs hf hσ hσ'
  refine integral_line_shift
    (fun z hz => differentiableAt_datumPaired hψ.continuous hψs hf hσ hσ' hz)
    (integrable_datumPaired_line hψ hψs hf hσ)
    (integrable_datumPaired_line hψ hψs hf hσ') ?_
  have hbound : ∀ R : ℝ,
      ‖∫ y in σ..σ', datumPaired ψ f ((R : ℂ) + (y : ℂ) * Complex.I)‖
        + ‖∫ y in σ..σ', datumPaired ψ f (-(R : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 2 * (A / (1 + R ^ 2) * |σ' - σ|) := by
    intro R
    have hpos : ∀ (w : ℂ) (y : ℝ), y ∈ Set.uIoc σ σ' → w.re ^ 2 = R ^ 2 →
        w.im = y → ‖datumPaired ψ f w‖ ≤ A / (1 + R ^ 2) := by
      intro w y hy hwre hwim
      have hyIcc : y ∈ uIcc σ σ' := Set.Ioc_subset_Icc_self hy
      have := hA w (by rw [hwim]; exact hyIcc)
      rwa [hwre] at this
    have h1 : ‖∫ y in σ..σ', datumPaired ψ f ((R : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ A / (1 + R ^ 2) * |σ' - σ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
      refine hpos _ y hy ?_ ?_ <;> simp
    have h2 : ‖∫ y in σ..σ', datumPaired ψ f (-(R : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ A / (1 + R ^ 2) * |σ' - σ| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
      refine hpos _ y hy ?_ ?_ <;> simp
    linarith
  refine squeeze_zero (fun R => by positivity) hbound ?_
  have hquad : Tendsto (fun R : ℝ => 1 + R ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  have hdiv : Tendsto (fun R : ℝ => A / (1 + R ^ 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hquad
  have := (hdiv.mul_const |σ' - σ|).const_mul (2 : ℝ)
  simpa using this

set_option maxHeartbeats 1000000 in
/-- **The multiplication formula for the boundary pairing.** -/
theorem integral_weightedTest_smul_fourierInv_datum {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) (hf : StripDatum f) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    (∫ L : ℝ, weightedTest ψ σ L •
        ((𝓕⁻ (stripDatumLp hf hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L)
      = ∫ x : ℝ, datumPaired ψ f ((x : ℂ) + (σ : ℂ) * Complex.I) := by
  set u : Lp X 2 (volume : Measure ℝ) := stripDatumLp hf hσ with hu
  set φ : 𝓢(ℝ, ℂ) :=
    (hasCompactSupport_weightedTest hψs σ).toSchwartzMap (contDiff_weightedTest hψ σ) with hφ
  set φinv : 𝓢(ℝ, ℂ) := 𝓕⁻ φ with hφinv
  have hφcoe : ⇑φ = weightedTest ψ σ := rfl
  have hstep1 : (∫ L : ℝ, weightedTest ψ σ L •
      ((𝓕⁻ u : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L)
      = (((𝓕⁻ u : Lp X 2 (volume : Measure ℝ)) : 𝓢'(ℝ, X))) φ := by
    rw [MeasureTheory.Lp.toTemperedDistribution_apply, hφcoe]
  have hstep2 : (((𝓕⁻ u : Lp X 2 (volume : Measure ℝ)) : 𝓢'(ℝ, X))) φ
      = ((u : 𝓢'(ℝ, X))) φinv := by
    rw [← MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq u, hφinv]
    exact TemperedDistribution.fourierInv_apply _ _
  have hstep3 : ((u : 𝓢'(ℝ, X))) φinv = ∫ x : ℝ, φinv x • (u : ℝ → X) x :=
    MeasureTheory.Lp.toTemperedDistribution_apply u φinv
  have hcoeinv : ∀ x : ℝ, φinv x = testTransformTwoPi ψ ((x : ℂ) + (σ : ℂ) * Complex.I) := by
    intro x
    have h1 : ⇑φinv = 𝓕⁻ (weightedTest ψ σ) := by
      rw [hφinv, SchwartzMap.fourierInv_coe, hφcoe]
    rw [h1]
    exact fourierInv_weightedTest ψ σ x
  have hucoe : (u : ℝ → X) =ᵐ[volume] stripDatumLine f σ := by
    rw [hu, stripDatumLp]
    exact (hf.memLp σ hσ).coeFn_toLp
  have hstep4 : (∫ x : ℝ, φinv x • (u : ℝ → X) x)
      = ∫ x : ℝ, datumPaired ψ f ((x : ℂ) + (σ : ℂ) * Complex.I) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hucoe] with x hx
    rw [hcoeinv x, hx, datumPaired, stripDatumLine]
  rw [hstep1, hstep2, hstep3, hstep4]

set_option maxHeartbeats 1000000 in
/-- **The exponentially damped transforms of the different lines agree.** -/
theorem stripDatumFourier_weight_eq (hf : StripDatum f) {σ σ' : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ L : ℝ, Real.exp (-(2 * Real.pi * σ * L)) •
        ((𝓕⁻ (stripDatumLp hf hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L
      = Real.exp (-(2 * Real.pi * σ' * L)) •
        ((𝓕⁻ (stripDatumLp hf hσ') : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L := by
  have hloc : ∀ {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1),
      LocallyIntegrable (fun L : ℝ => Real.exp (-(2 * Real.pi * τ * L)) •
        ((𝓕⁻ (stripDatumLp hf hτ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L)
        (volume : Measure ℝ) := by
    intro τ hτ
    refine locallyIntegrable_real_continuous_smul ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_
    exact Real.continuous_exp.comp (by fun_prop)
  refine ae_eq_of_integral_contDiff_smul_eq (hloc hσ) (hloc hσ') ?_
  intro g hg hgs
  set ψ : ℝ → ℂ := (fun r : ℝ => ((r : ℝ) : ℂ)) ∘ g with hψdef
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hg
  have hψs : HasCompactSupport ψ := hgs.comp_left rfl
  have hrewrite : ∀ {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1),
      (∫ L : ℝ, g L • (Real.exp (-(2 * Real.pi * τ * L)) •
        ((𝓕⁻ (stripDatumLp hf hτ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L))
      = ∫ x : ℝ, datumPaired ψ f ((x : ℂ) + (τ : ℂ) * Complex.I) := by
    intro τ hτ
    rw [← integral_weightedTest_smul_fourierInv_datum hψ hψs hf hτ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
    have hcast : weightedTest ψ τ L = (((g L * Real.exp (-(2 * Real.pi * τ * L)) : ℝ)) : ℂ) := by
      simp only [weightedTest, hψdef, Function.comp_apply, Complex.ofReal_mul,
        Complex.ofReal_exp, Complex.ofReal_neg]
    simp only [hcast, Complex.coe_smul, mul_smul]
  rw [hrewrite hσ, hrewrite hσ']
  exact datumPaired_line_shift hψ hψs hf hσ hσ'

set_option maxHeartbeats 1000000 in
/-- **One frequency profile carries every interior line.**  There is a measurable `F` whose
exponential weights `e^{2πσL}F(L)` are exactly the `L²` transforms of the interior lines, hence are
square integrable for every `0 < σ < 1`. -/
theorem exists_memLp_exp_smul_stripDatumFourier (hf : StripDatum f) :
    ∃ F : ℝ → X, ∀ σ : ℝ, ∀ hσ : σ ∈ Ioo (0 : ℝ) 1,
      (∀ᵐ L : ℝ, ((𝓕⁻ (stripDatumLp hf hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L
          = Real.exp (2 * Real.pi * σ * L) • F L)
        ∧ MemLp (fun L : ℝ => Real.exp (2 * Real.pi * σ * L) • F L) 2 (volume : Measure ℝ) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨fun L => Real.exp (-(2 * Real.pi * (1 / 2 : ℝ) * L)) •
    ((𝓕⁻ (stripDatumLp hf hhalf) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L, ?_⟩
  intro σ hσ
  have hkey : ∀ᵐ L : ℝ,
      ((𝓕⁻ (stripDatumLp hf hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L
        = Real.exp (2 * Real.pi * σ * L) •
          (Real.exp (-(2 * Real.pi * (1 / 2 : ℝ) * L)) •
            ((𝓕⁻ (stripDatumLp hf hhalf) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L) := by
    filter_upwards [stripDatumFourier_weight_eq hf hσ hhalf] with L hL
    rw [← hL, smul_smul, ← Real.exp_add]
    have hzero : 2 * Real.pi * σ * L + -(2 * Real.pi * σ * L) = 0 := by ring
    rw [hzero, Real.exp_zero, one_smul]
  exact ⟨hkey, (Lp.memLp _).ae_eq hkey⟩

end

end GaloisForLFunctions.RHTower
