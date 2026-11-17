import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.AFiniteNegativeLayerAboveAPositiveSeriesHasAGroundState
import GaloisForLFunctions.SquareRootThreshold.WeilPositivityForcesTheCriticalLine
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TemperedConfigurationPontryaginLaw
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Tempered configurations with a finite off-line layer have critical states

A model of the zero side is a tempered zero configuration `Z` (multiset of points `ρ` in the strip,
invariant under `ρ ↦ 1 − ρ̄`, with `Σ m_ρ/(1 + |γ_ρ|²) < ∞`). Its confined half-line form lives on the
confinement space `E = L²(e^{−8u} du, u < 0)`: with `z = ρ − ½`,

  `𝓔_Z(F) = Σ_{Re ρ = ½} m_ρ |L F(z)|² + Σ_{Re ρ ≠ ½} m_ρ Re(L F(z) L F(−z))`,

where `L F(z) = ∫_{u<0} F(u) e^{zu} du = ⟪e^{(z̄+8)u}, F⟫_E`. For a compactly supported `C²` test on
`u < 0` this is Weil's form of the configuration, `𝓔_Z(f) = Re W_Z(f, f)`
(`configEnergy_toLp_eq_re_W`).

**Critical states of the models** (`exists_configCriticalState`). If `Z` has finitely many points off
the critical line, at least one of them, and is invariant under conjugation, then there are a
critical ratio `a* > 0` and a unit critical state `F* ∈ E`:

  `𝓔_Z(G) + a* ‖G‖² ≥ 0` for every admissible `G`, with equality at `F*`.

It satisfies the weak equation `𝓔_Z(F*, G) + a* ⟪F*, G⟫ = 0` (`exists_configCriticalState_weak`).
If all points are on the line, `𝓔_Z ≥ 0` and no critical state exists (`configEnergy_nonneg_of_onLine`).

Mechanism. The on-line zeros give a nonnegative series of squares of continuous functionals of `E`,
the finitely many off-line zeros a finite-rank form, so a negative value is attained
(`GroundState.LayeredEnergy.exists_groundState_of_negative`). A negative value exists: an off-line
zero is seen by a `C²` test with `Re W_Z(f, f) < 0` (`offLine_visible`); translation keeps `W_Z`,
moves the test into `u < 0`, and by conjugation invariance `W_Z` is real on real tests, so the real
or the imaginary part of the test is a real negative direction.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
open scoped ComplexConjugate ENNReal NNReal ContDiff RealInnerProductSpace

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ModelStates
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig offLine_visible)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (summable_norm_Wsummand)

/-! ### The confinement space -/

/-- The confinement measure `e^{−8u} du` on the negative half-line. -/
def confMeasure : Measure ℝ :=
  (volume.restrict (Iio (0 : ℝ))).withDensity fun u => ENNReal.ofReal (Real.exp (-(8 * u)))

/-- The confinement Hilbert space `L²(e^{−8u} du, u < 0)`. -/
abbrev ConfSpace : Type := Lp ℝ 2 confMeasure

instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩

instance : SFinite confMeasure := by unfold confMeasure; infer_instance

instance : TopologicalSpace.SeparableSpace ConfSpace := inferInstance

theorem measurable_expDensity : Measurable fun u : ℝ => (Real.exp (-(8 * u))).toNNReal := by
  fun_prop

theorem integral_confMeasure (g : ℝ → ℝ) :
    ∫ u, g u ∂confMeasure = ∫ u in Iio 0, Real.exp (-(8 * u)) * g u := by
  unfold confMeasure
  rw [show (fun u : ℝ => ENNReal.ofReal (Real.exp (-(8 * u)))) =
    fun u => ((Real.exp (-(8 * u))).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul measurable_expDensity]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]

theorem integrable_confMeasure_iff {g : ℝ → ℝ} :
    Integrable g confMeasure ↔ IntegrableOn (fun u => Real.exp (-(8 * u)) * g u) (Iio 0) := by
  unfold confMeasure
  rw [show (fun u : ℝ => ENNReal.ofReal (Real.exp (-(8 * u)))) =
    fun u => ((Real.exp (-(8 * u))).toNNReal : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_smul measurable_expDensity]
  have e : (fun x => (Real.exp (-(8 * x))).toNNReal • g x) = fun x => Real.exp (-(8 * x)) * g x := by
    funext x; simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
  rw [e]
  rfl

theorem memLp_conf {g : ℝ → ℝ} (hg : Measurable g)
    (h : IntegrableOn (fun u => Real.exp (-(8 * u)) * g u ^ 2) (Iio 0)) : MemLp g 2 confMeasure :=
  (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr (integrable_confMeasure_iff.mpr h)

theorem inner_toLp {f g : ℝ → ℝ} (hf : MemLp f 2 confMeasure) (hg : MemLp g 2 confMeasure) :
    @inner ℝ ConfSpace _ (hf.toLp f) (hg.toLp g) = ∫ u in Iio 0, Real.exp (-(8 * u)) * (f u * g u) := by
  rw [L2.inner_def, ← integral_confMeasure]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with u h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-! ### Exponential vectors -/

/-- `e^{(σ+8)u} cos(τu)`, the real part of `e^{(z+8)u}` for `z = σ + iτ`. -/
def expCos (σ τ u : ℝ) : ℝ := Real.exp ((σ + 8) * u) * Real.cos (τ * u)

/-- `e^{(σ+8)u} sin(τu)`, the imaginary part of `e^{(z+8)u}`. -/
def expSin (σ τ u : ℝ) : ℝ := Real.exp ((σ + 8) * u) * Real.sin (τ * u)

theorem integrableOn_expSq {σ : ℝ} (hσ : -4 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp ((2 * σ + 8) * u)) (Iio 0) :=
  (integrableOn_exp_mul_Iic (by linarith) 0).mono_set Iio_subset_Iic_self

theorem memLp_expCos {σ : ℝ} (hσ : -4 < σ) (τ : ℝ) : MemLp (expCos σ τ) 2 confMeasure := by
  refine memLp_conf (by unfold expCos; fun_prop) ((integrableOn_expSq hσ).mono'
    (by unfold expCos; fun_prop : Measurable fun u : ℝ =>
      Real.exp (-(8 * u)) * expCos σ τ u ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_))
  unfold expCos
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : Real.cos (τ * u) ^ 2 ≤ 1 := Real.cos_sq_le_one _
  calc Real.exp (-(8 * u)) * (Real.exp ((σ + 8) * u) * Real.cos (τ * u)) ^ 2
      = Real.exp (-(8 * u)) * Real.exp ((σ + 8) * u) ^ 2 * Real.cos (τ * u) ^ 2 := by ring
    _ ≤ Real.exp (-(8 * u)) * Real.exp ((σ + 8) * u) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp ((2 * σ + 8) * u) := by
        rw [mul_one, sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem memLp_expSin {σ : ℝ} (hσ : -4 < σ) (τ : ℝ) : MemLp (expSin σ τ) 2 confMeasure := by
  refine memLp_conf (by unfold expSin; fun_prop) ((integrableOn_expSq hσ).mono'
    (by unfold expSin; fun_prop : Measurable fun u : ℝ =>
      Real.exp (-(8 * u)) * expSin σ τ u ^ 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_))
  unfold expSin
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : Real.sin (τ * u) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  calc Real.exp (-(8 * u)) * (Real.exp ((σ + 8) * u) * Real.sin (τ * u)) ^ 2
      = Real.exp (-(8 * u)) * Real.exp ((σ + 8) * u) ^ 2 * Real.sin (τ * u) ^ 2 := by ring
    _ ≤ Real.exp (-(8 * u)) * Real.exp ((σ + 8) * u) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp ((2 * σ + 8) * u) := by
        rw [mul_one, sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- The vector of `E` representing `F ↦ Re L F(σ + iτ)`. -/
def cosVec (σ τ : ℝ) : ConfSpace := if h : -4 < σ then (memLp_expCos h τ).toLp _ else 0

/-- The vector of `E` representing `F ↦ Im L F(σ + iτ)`. -/
def sinVec (σ τ : ℝ) : ConfSpace := if h : -4 < σ then (memLp_expSin h τ).toLp _ else 0

theorem inner_cosVec {σ : ℝ} (hσ : -4 < σ) (τ : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 confMeasure) :
    @inner ℝ ConfSpace _ (cosVec σ τ) (hf.toLp f) =
      ∫ u in Iio 0, f u * (Real.exp (σ * u) * Real.cos (τ * u)) := by
  rw [cosVec, dif_pos hσ, inner_toLp]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  unfold expCos
  have : Real.exp (-(8 * u)) * Real.exp ((σ + 8) * u) = Real.exp (σ * u) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only
  rw [← mul_assoc, ← mul_assoc, this]
  ring

theorem inner_sinVec {σ : ℝ} (hσ : -4 < σ) (τ : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 confMeasure) :
    @inner ℝ ConfSpace _ (sinVec σ τ) (hf.toLp f) =
      ∫ u in Iio 0, f u * (Real.exp (σ * u) * Real.sin (τ * u)) := by
  rw [sinVec, dif_pos hσ, inner_toLp]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  unfold expSin
  have : Real.exp (-(8 * u)) * Real.exp ((σ + 8) * u) = Real.exp (σ * u) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only
  rw [← mul_assoc, ← mul_assoc, this]
  ring

/-! ### Tests on the negative half-line -/

/-- A real `C²` test with compact support in `u < 0`. -/
structure HalfLineTest (f : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 2 f
  compact : HasCompactSupport f
  support : ∀ u, 0 ≤ u → f u = 0

theorem HalfLineTest.memLp {f : ℝ → ℝ} (hf : HalfLineTest f) : MemLp f 2 confMeasure := by
  refine memLp_conf hf.smooth.continuous.measurable ?_
  refine (((by fun_prop : Continuous fun u : ℝ => Real.exp (-(8 * u))).mul
    (hf.smooth.continuous.pow 2)).integrable_of_hasCompactSupport
    (hf.compact.mono' fun u hu => subset_tsupport f fun h0 => hu ?_)).integrableOn
  simp [h0]

theorem HalfLineTest.integrableOn_mul {f : ℝ → ℝ} (hf : HalfLineTest f) {g : ℝ → ℝ}
    (hg : Continuous g) : IntegrableOn (fun u => f u * g u) (Iio 0) :=
  ((hf.smooth.continuous.mul hg).integrable_of_hasCompactSupport hf.compact.mul_right).integrableOn

/-- The coordinate `∫_{u<0} f(u) e^{σu} cos(τu) du`, the real part of `L f(σ + iτ)`. -/
def testRe (f : ℝ → ℝ) (σ τ : ℝ) : ℝ := ∫ u in Iio 0, f u * (Real.exp (σ * u) * Real.cos (τ * u))

/-- The coordinate `∫_{u<0} f(u) e^{σu} sin(τu) du`, the imaginary part of `L f(σ + iτ)`. -/
def testIm (f : ℝ → ℝ) (σ τ : ℝ) : ℝ := ∫ u in Iio 0, f u * (Real.exp (σ * u) * Real.sin (τ * u))

theorem testRe_neg (f : ℝ → ℝ) (σ τ : ℝ) : testRe f σ (-τ) = testRe f σ τ := by
  unfold testRe; congr 1; funext u; rw [neg_mul, Real.cos_neg]

theorem testIm_neg (f : ℝ → ℝ) (σ τ : ℝ) : testIm f σ (-τ) = -testIm f σ τ := by
  unfold testIm; rw [← integral_neg]; congr 1; funext u; rw [neg_mul, Real.sin_neg]; ring

/-- The Laplace transform of a half-line test splits into its two exponential coordinates. -/
theorem HalfLineTest.paperFT_eq {f : ℝ → ℝ} (hf : HalfLineTest f) (w : ℂ) :
    paperFT (fun u => (f u : ℂ)) w =
      (testRe f (I * w).re (I * w).im : ℂ) + I * (testIm f (I * w).re (I * w).im : ℂ) := by
  set σ := (I * w).re
  set τ := (I * w).im
  have hrest : paperFT (fun u => (f u : ℂ)) w = ∫ u in Iio 0, (f u : ℂ) * cexp (I * w * u) := by
    unfold paperFT
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    show ((f u : ℝ) : ℂ) * cexp (I * w * u) = 0
    rw [hf.support u (not_lt.mp hu), Complex.ofReal_zero, zero_mul]
  have hpt : ∀ u : ℝ, (f u : ℂ) * cexp (I * w * u) =
      ((f u * (Real.exp (σ * u) * Real.cos (τ * u)) : ℝ) : ℂ) +
        I * ((f u * (Real.exp (σ * u) * Real.sin (τ * u)) : ℝ) : ℂ) := fun u => by
    have hz : I * w * u = ((σ * u : ℝ) : ℂ) + ((τ * u : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [σ, τ, Complex.mul_re, Complex.mul_im]
    rw [hz, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    push_cast
    ring
  have h1 : IntegrableOn (fun u : ℝ => ((f u * (Real.exp (σ * u) * Real.cos (τ * u)) : ℝ) : ℂ))
      (Iio 0) := (hf.integrableOn_mul (by fun_prop)).ofReal
  have h2 : IntegrableOn (fun u : ℝ => I * ((f u * (Real.exp (σ * u) * Real.sin (τ * u)) : ℝ) : ℂ))
      (Iio 0) := ((hf.integrableOn_mul (by fun_prop)).ofReal).const_mul I
  rw [hrest]
  simp_rw [hpt]
  rw [integral_add h1 h2, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  rfl

theorem I_mul_gammaOf (ρ : ℂ) : I * gammaOf ρ = ρ - 1 / 2 := by
  unfold gammaOf; field_simp

theorem I_mul_conj_gammaOf (ρ : ℂ) : I * conj (gammaOf ρ) = 1 / 2 - conj ρ := by
  unfold gammaOf
  rw [map_div₀, Complex.conj_I, map_sub, map_div₀, map_one, map_ofNat]
  field_simp
  ring

theorem HalfLineTest.paperFT_gammaOf {f : ℝ → ℝ} (hf : HalfLineTest f) (ρ : ℂ) :
    paperFT (fun u => (f u : ℂ)) (gammaOf ρ) =
      (testRe f (ρ.re - 1 / 2) ρ.im : ℂ) + I * (testIm f (ρ.re - 1 / 2) ρ.im : ℂ) := by
  rw [hf.paperFT_eq, I_mul_gammaOf]
  have h1 : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
  have h2 : (ρ - 1 / 2).im = ρ.im := by simp
  rw [h1, h2]

theorem HalfLineTest.conj_paperFT_conj_gammaOf {f : ℝ → ℝ} (hf : HalfLineTest f) (ρ : ℂ) :
    conj (paperFT (fun u => (f u : ℂ)) (conj (gammaOf ρ))) =
      (testRe f (1 / 2 - ρ.re) (-ρ.im) : ℂ) + I * (testIm f (1 / 2 - ρ.re) (-ρ.im) : ℂ) := by
  rw [hf.paperFT_eq, I_mul_conj_gammaOf]
  have h1 : (1 / 2 - conj ρ).re = 1 / 2 - ρ.re := by simp
  have h2 : (1 / 2 - conj ρ).im = ρ.im := by simp
  rw [h1, h2, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    testRe_neg, testIm_neg]
  push_cast
  ring

variable (Z : ZeroConfig)

/-- The Weil summand of a half-line test at a point, in exponential coordinates. -/
theorem Wsummand_eq {f : ℝ → ℝ} (hf : HalfLineTest f) (ρ : ℂ) :
    Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ =
      (Z.mult ρ : ℂ) * ((testRe f (ρ.re - 1 / 2) ρ.im : ℂ) + I * (testIm f (ρ.re - 1 / 2) ρ.im : ℂ)) *
        ((testRe f (1 / 2 - ρ.re) (-ρ.im) : ℂ) + I * (testIm f (1 / 2 - ρ.re) (-ρ.im) : ℂ)) := by
  unfold ZeroConfig.Wsummand
  rw [hf.paperFT_gammaOf, hf.conj_paperFT_conj_gammaOf]

theorem re_Wsummand_eq {f : ℝ → ℝ} (hf : HalfLineTest f) (ρ : ℂ) :
    (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re =
      (Z.mult ρ : ℝ) * (testRe f (ρ.re - 1 / 2) ρ.im * testRe f (1 / 2 - ρ.re) (-ρ.im) -
        testIm f (ρ.re - 1 / 2) ρ.im * testIm f (1 / 2 - ρ.re) (-ρ.im)) := by
  rw [Wsummand_eq Z hf]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- On the line the summand is `m (A² + B²)`. -/
theorem Wsummand_eq_of_onLine {f : ℝ → ℝ} (hf : HalfLineTest f) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ =
      (((Z.mult ρ : ℝ) * (testRe f 0 ρ.im ^ 2 + testIm f 0 ρ.im ^ 2) : ℝ) : ℂ) := by
  rw [Wsummand_eq Z hf, hρ, sub_self, testRe_neg, testIm_neg]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-! ### The configuration energy -/

/-- The off-line points of the configuration. -/
def offLineSet : Set ℂ := {ρ | ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2}

/-- The on-line points, as an index type. -/
def OnLineIdx : Type := {ρ : Z.carrier // (ρ : ℂ).re = 1 / 2}

variable {Z}

/-- **The confined zero-side energy of a configuration with a finite off-line layer.** The on-line
points give the squares `m |L F(iγ)|²`, each off-line point the two products of
`Re(L F(z) L F(−z)) = Re L F(z) Re L F(−z) − Im L F(z) Im L F(−z)`. -/
def configEnergy (hfin : (offLineSet Z).Finite) :
    GroundState.LayeredEnergy ConfSpace (OnLineIdx Z) (hfin.toFinset × Bool) where
  w ρ := Z.mult (ρ.1 : ℂ)
  a ρ := cosVec 0 (ρ.1 : ℂ).im
  b ρ := sinVec 0 (ρ.1 : ℂ).im
  w_nonneg _ := Nat.cast_nonneg _
  v x := (Z.mult (x.1 : ℂ) : ℝ) * (if x.2 then 1 else -1)
  p x := if x.2 then cosVec ((x.1 : ℂ).re - 1 / 2) (x.1 : ℂ).im
    else sinVec ((x.1 : ℂ).re - 1 / 2) (x.1 : ℂ).im
  q x := if x.2 then cosVec (1 / 2 - (x.1 : ℂ).re) (-(x.1 : ℂ).im)
    else sinVec (1 / 2 - (x.1 : ℂ).re) (-(x.1 : ℂ).im)

theorem strip_bounds {ρ : ℂ} (hρ : ρ ∈ Z.carrier) : -4 < ρ.re - 1 / 2 ∧ -4 < 1 / 2 - ρ.re := by
  have := Z.strip ρ hρ
  constructor <;> linarith [this.1, this.2]

/-- **On a half-line test the configuration energy is Weil's form of the configuration.** -/
theorem configEnergy_toLp_eq_re_W (hZ : TemperedConfig Z) (hfin : (offLineSet Z).Finite)
    {f : ℝ → ℝ} (hf : HalfLineTest f) :
    (configEnergy hfin).Admissible (hf.memLp.toLp f) ∧
      (configEnergy hfin).energy (hf.memLp.toLp f) =
        (Z.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re := by
  set F := hf.memLp.toLp f
  have hcf : ContDiff ℝ 2 fun u => (f u : ℂ) := Complex.ofRealCLM.contDiff.comp hf.smooth
  have hcc : HasCompactSupport fun u => (f u : ℂ) := hf.compact.comp_left Complex.ofReal_zero
  have hsum := summable_norm_Wsummand Z hZ hcf hcc hcf hcc
  have hcos : ∀ {σ : ℝ}, -4 < σ → ∀ τ, @inner ℝ ConfSpace _ (cosVec σ τ) F = testRe f σ τ :=
    fun hσ τ => inner_cosVec hσ τ hf.memLp
  have hsin : ∀ {σ : ℝ}, -4 < σ → ∀ τ, @inner ℝ ConfSpace _ (sinVec σ τ) F = testIm f σ τ :=
    fun hσ τ => inner_sinVec hσ τ hf.memLp
  -- on-line terms are the norms of the summands
  have hterm : ∀ ρ : OnLineIdx Z, (configEnergy hfin).term F ρ =
      ‖Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ.1‖ := by
    intro ρ
    rw [Wsummand_eq_of_onLine Z hf ρ.2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    show (Z.mult (ρ.1 : ℂ) : ℝ) * (inner ℝ (cosVec 0 (ρ.1 : ℂ).im) F ^ 2 + inner ℝ (sinVec 0 (ρ.1 : ℂ).im) F ^ 2) = _
    rw [hcos (by norm_num), hsin (by norm_num)]
  have hadm : (configEnergy hfin).Admissible F := by
    unfold GroundState.LayeredEnergy.Admissible
    exact (hsum.subtype {ρ : Z.carrier | (ρ : ℂ).re = 1 / 2}).congr fun ρ => (hterm ρ).symm
  refine ⟨hadm, ?_⟩
  -- the real part of Weil's form, split by the critical line
  have hre : Summable fun ρ : Z.carrier =>
      (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re :=
    Complex.reCLM.summable hsum.of_norm
  have hW : (Z.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re =
      ∑' ρ : Z.carrier, (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) ρ).re := by
    unfold ZeroConfig.W
    exact Complex.reCLM.map_tsum hsum.of_norm
  rw [hW, ← hre.tsum_subtype_add_tsum_subtype_compl {ρ : Z.carrier | (ρ : ℂ).re = 1 / 2}]
  unfold GroundState.LayeredEnergy.energy
  congr 1
  · unfold GroundState.LayeredEnergy.series
    refine tsum_congr fun ρ => ?_
    rw [hterm ρ, Wsummand_eq_of_onLine Z hf ρ.2, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Complex.ofReal_re]
  · -- the finite off-line layer
    let e : ({ρ : Z.carrier | (ρ : ℂ).re = 1 / 2}ᶜ : Set Z.carrier) ≃ {x : ℂ // x ∈ hfin.toFinset} :=
      { toFun := fun x => ⟨x.1.1, (Set.Finite.mem_toFinset hfin).mpr ⟨x.1.2, x.2⟩⟩
        invFun := fun y => ⟨⟨y.1, ((Set.Finite.mem_toFinset hfin).mp y.2).1⟩,
          ((Set.Finite.mem_toFinset hfin).mp y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    rw [← e.symm.tsum_eq, tsum_fintype]
    unfold GroundState.LayeredEnergy.layer
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : ℂ) ∈ Z.carrier := ((Set.Finite.mem_toFinset hfin).mp x.2).1
    rw [Fintype.sum_bool]
    symm
    obtain ⟨h1, h2⟩ := strip_bounds hx
    show (Z.Wsummand (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) (x : ℂ)).re =
      (Z.mult (x : ℂ) : ℝ) * (if true = true then 1 else -1) *
          (inner ℝ (if true = true then cosVec ((x : ℂ).re - 1 / 2) (x : ℂ).im
            else sinVec ((x : ℂ).re - 1 / 2) (x : ℂ).im) F *
          inner ℝ (if true = true then cosVec (1 / 2 - (x : ℂ).re) (-(x : ℂ).im)
            else sinVec (1 / 2 - (x : ℂ).re) (-(x : ℂ).im)) F) +
        (Z.mult (x : ℂ) : ℝ) * (if false = true then 1 else -1) *
          (inner ℝ (if false = true then cosVec ((x : ℂ).re - 1 / 2) (x : ℂ).im
            else sinVec ((x : ℂ).re - 1 / 2) (x : ℂ).im) F *
          inner ℝ (if false = true then cosVec (1 / 2 - (x : ℂ).re) (-(x : ℂ).im)
            else sinVec (1 / 2 - (x : ℂ).re) (-(x : ℂ).im)) F)
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [re_Wsummand_eq Z hf, hcos h1, hcos h2, hsin h1, hsin h2]
    ring

/-- With every point on the line the energy is a sum of squares: no critical state. -/
theorem configEnergy_nonneg_of_onLine (hfin : (offLineSet Z).Finite)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) (F : ConfSpace) : 0 ≤ (configEnergy hfin).energy F := by
  have hempty : hfin.toFinset = ∅ := by
    rw [Set.Finite.toFinset_eq_empty]
    ext ρ
    simp only [offLineSet, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    exact hon ρ
  unfold GroundState.LayeredEnergy.energy GroundState.LayeredEnergy.layer
  have : IsEmpty (hfin.toFinset × Bool) := by
    rw [hempty]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  exact (configEnergy hfin).series_nonneg F

/-! ### A real negative direction -/

theorem paperFT_translate (g : ℝ → ℂ) (R : ℝ) (w : ℂ) :
    paperFT (fun u => g (u + R)) w = cexp (-(I * w * R)) * paperFT g w := by
  unfold paperFT
  calc ∫ u : ℝ, g (u + R) * cexp (I * w * u)
      = ∫ u : ℝ, g (u + R) * cexp (I * w * (((u + R : ℝ) : ℂ) - R)) := by
        congr 1; funext u; push_cast; ring_nf
    _ = ∫ u : ℝ, g u * cexp (I * w * ((u : ℂ) - R)) :=
        integral_add_right_eq_self (fun u : ℝ => g u * cexp (I * w * ((u : ℂ) - R))) R
    _ = ∫ u : ℝ, cexp (-(I * w * R)) * (g u * cexp (I * w * u)) := by
        congr 1; funext u
        rw [mul_left_comm, ← Complex.exp_add]
        congr 2; ring
    _ = _ := integral_const_mul _ _

theorem Wsummand_translate (g : ℝ → ℂ) (R : ℝ) (ρ : ℂ) :
    Z.Wsummand (fun u => g (u + R)) (fun u => g (u + R)) ρ = Z.Wsummand g g ρ := by
  unfold ZeroConfig.Wsummand
  rw [paperFT_translate, paperFT_translate, map_mul, ← Complex.exp_conj]
  have h : cexp (-(I * gammaOf ρ * R)) * cexp (conj (-(I * conj (gammaOf ρ) * R))) = 1 := by
    rw [← Complex.exp_add]
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    rw [show -(I * gammaOf ρ * R) + -(-I * gammaOf ρ * R) = 0 by ring, Complex.exp_zero]
  calc (Z.mult ρ : ℂ) * (cexp (-(I * gammaOf ρ * R)) * paperFT g (gammaOf ρ)) *
        (cexp (conj (-(I * conj (gammaOf ρ) * R))) * conj (paperFT g (conj (gammaOf ρ))))
      = (Z.mult ρ : ℂ) * paperFT g (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ))) *
          (cexp (-(I * gammaOf ρ * R)) * cexp (conj (-(I * conj (gammaOf ρ) * R)))) := by ring
    _ = _ := by rw [h, mul_one]

theorem W_translate (g : ℝ → ℂ) (R : ℝ) :
    Z.W (fun u => g (u + R)) (fun u => g (u + R)) = Z.W g g := by
  unfold ZeroConfig.W
  exact tsum_congr fun ρ => Wsummand_translate g R ρ

/-- For a real test, `f̂(−w̄) = conj f̂(w)`. -/
theorem paperFT_neg_conj (u : ℝ → ℝ) (w : ℂ) :
    paperFT (fun x => (u x : ℂ)) (-conj w) = conj (paperFT (fun x => (u x : ℂ)) w) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1; funext x
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem gammaOf_conj (ρ : ℂ) : gammaOf (conj ρ) = -conj (gammaOf ρ) := by
  unfold gammaOf
  rw [map_div₀, Complex.conj_I, map_sub, map_div₀, map_one, map_ofNat]
  field_simp

/-- **Conjugation symmetry.** At a conjugated point the summand of real tests is conjugated. -/
theorem Wsummand_conj (u v : ℝ → ℝ) {ρ : ℂ} (hm : Z.mult (conj ρ) = Z.mult ρ) :
    Z.Wsummand (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) (conj ρ) =
      conj (Z.Wsummand (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) ρ) := by
  unfold ZeroConfig.Wsummand
  rw [hm, gammaOf_conj, paperFT_neg_conj, map_neg, Complex.conj_conj,
    show -gammaOf ρ = -conj (conj (gammaOf ρ)) by rw [Complex.conj_conj], paperFT_neg_conj]
  simp only [map_mul, Complex.conj_conj, map_natCast]

theorem im_W_eq_zero (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    (u v : ℝ → ℝ) :
    (Z.W (fun x => (u x : ℂ)) (fun x => (v x : ℂ))).im = 0 := by
  let e : Z.carrier ≃ Z.carrier :=
    { toFun := fun ρ => ⟨conj (ρ : ℂ), (hconj ρ ρ.2).1⟩
      invFun := fun ρ => ⟨conj (ρ : ℂ), (hconj ρ ρ.2).1⟩
      left_inv := fun ρ => Subtype.ext (Complex.conj_conj _)
      right_inv := fun ρ => Subtype.ext (Complex.conj_conj _) }
  have h : Z.W (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) =
      conj (Z.W (fun x => (u x : ℂ)) (fun x => (v x : ℂ))) := by
    unfold ZeroConfig.W
    rw [Complex.conj_tsum, ← e.tsum_eq]
    exact tsum_congr fun ρ => Wsummand_conj u v (hconj ρ ρ.2).2
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- **A real half-line test with negative energy.** -/
theorem exists_halfLineTest_neg (hZ : TemperedConfig Z)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ f : ℝ → ℝ, HalfLineTest f ∧ (Z.W (fun u => (f u : ℂ)) (fun u => (f u : ℂ))).re < 0 := by
  obtain ⟨g, hg, hgc, hneg⟩ := offLine_visible Z hZ hρ₀ hre
  obtain ⟨M, hM⟩ := hgc.isCompact.bddAbove
  set R := max M 0 + 1
  have hzero : ∀ u, 0 ≤ u → g (u + R) = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hM hmem
      have : M < R := by simp only [R]; linarith [le_max_left M 0]
      linarith
  set g₁ : ℝ → ℂ := fun u => g (u + R)
  have hg₁ : ContDiff ℝ 2 g₁ := hg.comp (contDiff_id.add contDiff_const)
  have hg₁c : HasCompactSupport g₁ := hgc.comp_homeomorph (Homeomorph.addRight R)
  set u : ℝ → ℝ := fun x => (g₁ x).re
  set v : ℝ → ℝ := fun x => (g₁ x).im
  have hu : HalfLineTest u :=
    ⟨Complex.reCLM.contDiff.comp hg₁, hg₁c.comp_left Complex.zero_re,
      fun x hx => by simp only [u, g₁, hzero x hx, Complex.zero_re]⟩
  have hv : HalfLineTest v :=
    ⟨Complex.imCLM.contDiff.comp hg₁, hg₁c.comp_left Complex.zero_im,
      fun x hx => by simp only [v, g₁, hzero x hx, Complex.zero_im]⟩
  have hsplit : g₁ = fun x => (u x : ℂ) + I * (v x : ℂ) := by
    funext x; simp only [u, v]; rw [mul_comm]; exact (Complex.re_add_im _).symm
  have hcu : ContDiff ℝ 2 fun x => (u x : ℂ) := Complex.ofRealCLM.contDiff.comp hu.smooth
  have hcv : ContDiff ℝ 2 fun x => (v x : ℂ) := Complex.ofRealCLM.contDiff.comp hv.smooth
  have hcuc : HasCompactSupport fun x => (u x : ℂ) := hu.compact.comp_left Complex.ofReal_zero
  have hcvc : HasCompactSupport fun x => (v x : ℂ) := hv.compact.comp_left Complex.ofReal_zero
  -- linearity of the transform
  have hlin : ∀ w : ℂ, paperFT g₁ w = paperFT (fun x => (u x : ℂ)) w +
      I * paperFT (fun x => (v x : ℂ)) w := by
    intro w
    rw [hsplit]
    unfold paperFT
    rw [← integral_const_mul, ← integral_add]
    · congr 1; funext x; ring
    · exact (hcu.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcuc.mul_right
    · exact ((hcv.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
        hcvc.mul_right).const_mul _
  have hexp : ∀ ρ : ℂ, Z.Wsummand g₁ g₁ ρ =
      Z.Wsummand (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) ρ +
        Z.Wsummand (fun x => (v x : ℂ)) (fun x => (v x : ℂ)) ρ +
          I * (Z.Wsummand (fun x => (v x : ℂ)) (fun x => (u x : ℂ)) ρ -
            Z.Wsummand (fun x => (u x : ℂ)) (fun x => (v x : ℂ)) ρ) := by
    intro ρ
    unfold ZeroConfig.Wsummand
    rw [hlin, hlin, map_add, map_mul, Complex.conj_I]
    ring_nf
    rw [I_sq]
    ring
  have s1 := (summable_norm_Wsummand Z hZ hcu hcuc hcu hcuc).of_norm
  have s2 := (summable_norm_Wsummand Z hZ hcv hcvc hcv hcvc).of_norm
  have s3 := (summable_norm_Wsummand Z hZ hcv hcvc hcu hcuc).of_norm
  have s4 := (summable_norm_Wsummand Z hZ hcu hcuc hcv hcvc).of_norm
  have hWsplit : Z.W g₁ g₁ = Z.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ)) +
      Z.W (fun x => (v x : ℂ)) (fun x => (v x : ℂ)) +
        I * (Z.W (fun x => (v x : ℂ)) (fun x => (u x : ℂ)) -
          Z.W (fun x => (u x : ℂ)) (fun x => (v x : ℂ))) := by
    unfold ZeroConfig.W
    simp_rw [hexp]
    rw [Summable.tsum_add (s1.add s2) ((s3.sub s4).mul_left I), Summable.tsum_add s1 s2,
      tsum_mul_left, Summable.tsum_sub s3 s4]
  have hW₀ : Z.W g₁ g₁ = Z.W g g := W_translate g R
  have him1 := im_W_eq_zero hconj v u
  have him2 := im_W_eq_zero hconj u v
  have hre' : (Z.W g g).re = (Z.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ))).re +
      (Z.W (fun x => (v x : ℂ)) (fun x => (v x : ℂ))).re := by
    rw [← hW₀, hWsplit]
    simp [Complex.mul_re, him1, him2]
  rcases lt_or_ge (Z.W (fun x => (u x : ℂ)) (fun x => (u x : ℂ))).re 0 with h | h
  · exact ⟨u, hu, h⟩
  · exact ⟨v, hv, by linarith⟩

/-- **Confined critical states of the models.** A tempered configuration, invariant under
conjugation, with finitely many points off the critical line and at least one, has a critical
ratio ˋa > 0ˋ and a unit critical state ˋF ∈ Eˋ: ˋ𝓔_Z(G) + a ‖G‖² ≥ 0ˋ for every admissible ˋGˋ,
with equality at ˋFˋ. -/
theorem exists_configCriticalState (hZ : TemperedConfig Z) (hfin : (offLineSet Z).Finite)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ (a : ℝ) (F : ConfSpace), 0 < a ∧ (configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧
      (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      ∀ G : ConfSpace, (configEnergy hfin).Admissible G →
        0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2 := by
  obtain ⟨f, hf, hneg⟩ := exists_halfLineTest_neg hZ hconj hρ₀ hre
  obtain ⟨hadm, heq⟩ := configEnergy_toLp_eq_re_W hZ hfin hf
  obtain ⟨F, hFa, hF1, hFneg, hmin⟩ :=
    (configEnergy hfin).exists_groundState_of_negative hadm (by rw [heq]; exact hneg)
  refine ⟨-(configEnergy hfin).energy F, F, by linarith, hFa, hF1, by rw [hF1]; ring,
    fun G hG => ?_⟩
  have := hmin G hG
  linarith

/-- **The weak equation of a model critical state.** The critical state of
`exists_configCriticalState` satisfies `𝓔_Z(F, G) + a ⟪F, G⟫ = 0` for every admissible `G`, the
polar form of the zero-side energy being the model's own explicit formula. -/
theorem exists_configCriticalState_weak (hZ : TemperedConfig Z) (hfin : (offLineSet Z).Finite)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ (a : ℝ) (F : ConfSpace), 0 < a ∧ (configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧
      (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      (∀ G : ConfSpace, (configEnergy hfin).Admissible G →
        0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2) ∧
      ∀ G : ConfSpace, (configEnergy hfin).Admissible G →
        (configEnergy hfin).pair F G + a * inner ℝ F G = 0 := by
  obtain ⟨a, F, ha, hFa, hF1, hEq, hmin⟩ := exists_configCriticalState hZ hfin hconj hρ₀ hre
  refine ⟨a, F, ha, hFa, hF1, hEq, hmin, fun G hG => ?_⟩
  have h := (configEnergy hfin).pair_eq_of_groundState (lam := -a) hFa (by linarith)
    (fun G hG => by have := hmin G hG; linarith) hG
  linarith

#print axioms exists_configCriticalState
#print axioms exists_configCriticalState_weak

end GaloisForLFunctions.ExclusionOfTheCriticalState.ModelStates
