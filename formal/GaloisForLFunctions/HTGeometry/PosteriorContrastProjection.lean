import GaloisForLFunctions.HTGeometry.CommonMarkovRecoveryNeutrality

/-!
# Posterior contrast and the exact information current

Two probability laws are compared through their balanced law `η = (P+Q)/2`.  The posterior
contrast `d` is defined by `dP/dη = 1 + d`, `dQ/dη = 1 - d`; it takes values in `[-1,1]` and
vanishes exactly when the two laws agree.  A common observation kernel transports the contrast to
the observed space, and the transported contrast is the conditional expectation of the source
contrast under the joint observation law.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-! ## The balanced law -/

/-- `(PMP.1)`  The balanced law of a binary experiment. -/
def balancedLaw (P Q : Measure X) : Measure X := (2 : ℝ≥0∞)⁻¹ • (P + Q)

theorem two_smul_balancedLaw (P Q : Measure X) : (2 : ℝ≥0∞) • balancedLaw P Q = P + Q := by
  rw [balancedLaw, smul_smul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_smul]

instance isProbabilityMeasure_balancedLaw (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] : IsProbabilityMeasure (balancedLaw P Q) := by
  constructor
  rw [balancedLaw, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ,
    smul_eq_mul, show (1 : ℝ≥0∞) + 1 = 2 by norm_num,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

instance isFiniteMeasure_balancedLaw (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    IsFiniteMeasure (balancedLaw P Q) := by
  constructor
  rw [balancedLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

theorem absolutelyContinuous_balancedLaw_left (P Q : Measure X) : P ≪ balancedLaw P Q := by
  rw [balancedLaw]
  exact (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)).trans
    (Measure.absolutelyContinuous_smul (by simp))

theorem absolutelyContinuous_balancedLaw_right (P Q : Measure X) : Q ≪ balancedLaw P Q := by
  rw [balancedLaw]
  exact (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)).trans
    (Measure.absolutelyContinuous_smul (by simp))

/-- `(PMP.2)`  The two Radon--Nikodym densities against the balanced law sum to `2`. -/
theorem rnDeriv_add_rnDeriv_balancedLaw (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (fun x => P.rnDeriv (balancedLaw P Q) x + Q.rnDeriv (balancedLaw P Q) x)
      =ᵐ[balancedLaw P Q] fun _ => 2 := by
  rw [← withDensity_eq_iff_of_sigmaFinite (by fun_prop) (by fun_prop)]
  rw [show (fun x => (P.rnDeriv (balancedLaw P Q)) x + (Q.rnDeriv (balancedLaw P Q)) x)
      = P.rnDeriv (balancedLaw P Q) + Q.rnDeriv (balancedLaw P Q) from rfl,
    withDensity_add_left (Measure.measurable_rnDeriv _ _),
    Measure.withDensity_rnDeriv_eq P _ (absolutelyContinuous_balancedLaw_left P Q),
    Measure.withDensity_rnDeriv_eq Q _ (absolutelyContinuous_balancedLaw_right P Q),
    withDensity_const, two_smul_balancedLaw]

/-! ## The posterior contrast -/

/-- `(PMP.2)`  The balanced posterior contrast: `dP/dη = 1 + d`. -/
def posteriorContrast (P Q : Measure X) (x : X) : ℝ :=
  (P.rnDeriv (balancedLaw P Q) x).toReal - 1

theorem measurable_posteriorContrast (P Q : Measure X) : Measurable (posteriorContrast P Q) := by
  unfold posteriorContrast
  fun_prop

theorem rnDeriv_left_toReal (P Q : Measure X) (x : X) :
    (P.rnDeriv (balancedLaw P Q) x).toReal = 1 + posteriorContrast P Q x := by
  rw [posteriorContrast]; ring

/-- `(PMP.2)`  The complementary density is `1 - d`. -/
theorem rnDeriv_right_toReal (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    (fun x => (Q.rnDeriv (balancedLaw P Q) x).toReal)
      =ᵐ[balancedLaw P Q] fun x => 1 - posteriorContrast P Q x := by
  filter_upwards [rnDeriv_add_rnDeriv_balancedLaw P Q,
    Measure.rnDeriv_lt_top P (balancedLaw P Q), Measure.rnDeriv_lt_top Q (balancedLaw P Q)]
    with x hsum hPtop hQtop
  have h := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hPtop.ne hQtop.ne] at h
  rw [posteriorContrast]
  simp only [ENNReal.toReal_ofNat] at h
  linarith

/-- `(PMP.2)`  The contrast is bounded by one in absolute value. -/
theorem abs_posteriorContrast_le_one (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∀ᵐ x ∂(balancedLaw P Q), |posteriorContrast P Q x| ≤ 1 := by
  filter_upwards [rnDeriv_right_toReal P Q] with x hx
  have h1 : 0 ≤ (P.rnDeriv (balancedLaw P Q) x).toReal := ENNReal.toReal_nonneg
  have h2 : 0 ≤ (Q.rnDeriv (balancedLaw P Q) x).toReal := ENNReal.toReal_nonneg
  rw [hx] at h2
  rw [abs_le]
  constructor
  · rw [posteriorContrast]; linarith
  · linarith

/-! ## The observed contrast -/

theorem balancedLaw_comp (κ : Kernel X Y) (P Q : Measure X) :
    balancedLaw (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) = ⇑κ ∘ₘ (balancedLaw P Q) := by
  rw [balancedLaw, balancedLaw, Measure.comp_smul, Measure.comp_add]

/-- Bounded measurable functions are integrable against a finite measure. -/
theorem integrable_of_bound {μ : Measure X} [IsFiniteMeasure μ] {G : X → ℝ}
    (hG : Measurable G) {C : ℝ} (hGb : ∀ x, |G x| ≤ C) : Integrable G μ :=
  Integrable.mono' (integrable_const C) hG.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hGb x)

/-- The source contrast pairs a bounded observable against the signed half-difference. -/
theorem integral_mul_posteriorContrast (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {G : X → ℝ} (hG : Measurable G) {C : ℝ} (hGb : ∀ x, |G x| ≤ C) :
    ∫ x, G x * posteriorContrast P Q x ∂(balancedLaw P Q)
      = ∫ x, G x ∂P - ∫ x, G x ∂(balancedLaw P Q) := by
  have hac : P ≪ balancedLaw P Q := absolutelyContinuous_balancedLaw_left P Q
  have hGη : Integrable G (balancedLaw P Q) := integrable_of_bound hG hGb
  have hGP : Integrable G P := integrable_of_bound hG hGb
  have hfun : (fun x => G x * posteriorContrast P Q x)
      = fun x => (P.rnDeriv (balancedLaw P Q) x).toReal • G x - G x := by
    funext x
    rw [smul_eq_mul, rnDeriv_left_toReal]
    ring
  rw [hfun, integral_sub _ hGη, integral_rnDeriv_smul hac]
  exact (integrable_rnDeriv_smul_iff hac).mpr hGP

/-- The observed pairing of a bounded observable, read on the source. -/
def kernelPairing (κ : Kernel X Y) (g : Y → ℝ) (x : X) : ℝ := ∫ y, g y ∂(κ x)

theorem measurable_kernelPairing (κ : Kernel X Y) [IsSFiniteKernel κ] {g : Y → ℝ}
    (hg : Measurable g) : Measurable (kernelPairing κ g) :=
  (StronglyMeasurable.integral_kernel_prod_right (f := fun _ y => g y)
    (hg.comp measurable_snd).stronglyMeasurable).measurable

theorem abs_kernelPairing_le (κ : Kernel X Y) [IsMarkovKernel κ] {g : Y → ℝ} (hg : Measurable g)
    {C : ℝ} (hgb : ∀ y, |g y| ≤ C) (x : X) : |kernelPairing κ g x| ≤ C := by
  have hint : Integrable g (κ x) := integrable_of_bound hg hgb
  calc |kernelPairing κ g x| ≤ ∫ y, |g y| ∂(κ x) := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Y, C ∂(κ x) :=
        integral_mono hint.abs (integrable_const C) (fun y => hgb y)
    _ = C := by simp

theorem integral_comp_eq (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [IsFiniteMeasure μ]
    {g : Y → ℝ} (hg : Measurable g) {C : ℝ} (hgb : ∀ y, |g y| ≤ C) :
    ∫ y, g y ∂(⇑κ ∘ₘ μ) = ∫ x, kernelPairing κ g x ∂μ := by
  have hint : Integrable (fun p : X × Y => g p.2) (μ ⊗ₘ κ) :=
    integrable_of_bound (hg.comp measurable_snd) (fun p => hgb p.2)
  rw [← Measure.snd_compProd μ κ, Measure.snd,
    integral_map measurable_snd.aemeasurable
      (by rw [← Measure.snd, Measure.snd_compProd]; exact hg.aestronglyMeasurable),
    Measure.integral_compProd hint]
  rfl

/-- `(PMP.7)`  The observed contrast is the conditional expectation of the source contrast:
tested against every bounded observable, the two pairings agree. -/
theorem integral_observedContrast (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {g : Y → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hgb : ∀ y, |g y| ≤ C) :
    ∫ p, g p.2 * posteriorContrast P Q p.1 ∂((balancedLaw P Q) ⊗ₘ κ)
      = ∫ y, g y ∂(⇑κ ∘ₘ P) - ∫ y, g y ∂(⇑κ ∘ₘ (balancedLaw P Q)) := by
  have hae : ∀ᵐ p ∂((balancedLaw P Q) ⊗ₘ κ), |posteriorContrast P Q p.1| ≤ 1 := by
    have h1 : ∀ᵐ x ∂(((balancedLaw P Q) ⊗ₘ κ).map Prod.fst), |posteriorContrast P Q x| ≤ 1 := by
      rw [← Measure.fst, Measure.fst_compProd]
      exact abs_posteriorContrast_le_one P Q
    exact (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_le ((measurable_posteriorContrast P Q).abs) measurable_const)).mp h1
  have hint : Integrable (fun p : X × Y => g p.2 * posteriorContrast P Q p.1)
      ((balancedLaw P Q) ⊗ₘ κ) := by
    refine Integrable.mono' (integrable_const C)
      (((hg.comp measurable_snd).mul
        ((measurable_posteriorContrast P Q).comp measurable_fst)).aestronglyMeasurable) ?_
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    calc |g p.2| * |posteriorContrast P Q p.1| ≤ C * 1 := by
          exact mul_le_mul (hgb p.2) hp (abs_nonneg _) hC
      _ = C := mul_one C
  rw [Measure.integral_compProd hint]
  have hstep : ∀ x, ∫ y, g y * posteriorContrast P Q x ∂(κ x)
      = kernelPairing κ g x * posteriorContrast P Q x := fun x => integral_mul_const _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep),
    integral_mul_posteriorContrast P Q (measurable_kernelPairing κ hg)
      (abs_kernelPairing_le κ hg hgb),
    integral_comp_eq κ P hg hgb, integral_comp_eq κ (balancedLaw P Q) hg hgb]

theorem integral_snd_compProd (κ : Kernel X Y) [IsSFiniteKernel κ] (μ : Measure X)
    [SFinite μ] {F : Y → ℝ} (hF : Measurable F) :
    ∫ p, F p.2 ∂(μ ⊗ₘ κ) = ∫ y, F y ∂(⇑κ ∘ₘ μ) := by
  rw [← Measure.snd_compProd μ κ, Measure.snd,
    integral_map measurable_snd.aemeasurable hF.aestronglyMeasurable]

/-- `(PMP.7)`  The observed pairing of the transported contrast. -/
theorem integral_observedContrast_snd (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {g : Y → ℝ} (hg : Measurable g) {C : ℝ}
    (_hC : 0 ≤ C) (hgb : ∀ y, |g y| ≤ C) :
    ∫ p, g p.2 * posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2 ∂((balancedLaw P Q) ⊗ₘ κ)
      = ∫ y, g y ∂(⇑κ ∘ₘ P) - ∫ y, g y ∂(⇑κ ∘ₘ (balancedLaw P Q)) := by
  rw [integral_snd_compProd κ (balancedLaw P Q)
      (F := fun y => g y * posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) y)
      (hg.mul (measurable_posteriorContrast _ _)), ← balancedLaw_comp κ P Q,
    integral_mul_posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) hg hgb, balancedLaw_comp]

/-! ## The vertical information current -/

theorem ae_abs_posteriorContrast_fst (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∀ᵐ p ∂((balancedLaw P Q) ⊗ₘ κ), |posteriorContrast P Q p.1| ≤ 1 := by
  have h1 : ∀ᵐ x ∂(((balancedLaw P Q) ⊗ₘ κ).map Prod.fst), |posteriorContrast P Q x| ≤ 1 := by
    rw [← Measure.fst, Measure.fst_compProd]
    exact abs_posteriorContrast_le_one P Q
  exact (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_le ((measurable_posteriorContrast P Q).abs) measurable_const)).mp h1

theorem ae_abs_posteriorContrast_snd (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∀ᵐ p ∂((balancedLaw P Q) ⊗ₘ κ),
      |posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2| ≤ 1 := by
  have h1 : ∀ᵐ y ∂(((balancedLaw P Q) ⊗ₘ κ).map Prod.snd),
      |posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) y| ≤ 1 := by
    rw [← Measure.snd, Measure.snd_compProd, ← balancedLaw_comp κ P Q]
    exact abs_posteriorContrast_le_one _ _
  exact (ae_map_iff measurable_snd.aemeasurable
    (measurableSet_le ((measurable_posteriorContrast _ _).abs) measurable_const)).mp h1

theorem integrable_mul_of_ae_bound {μ : Measure (X × Y)} [IsFiniteMeasure μ] {g : Y → ℝ}
    (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C) (hgb : ∀ y, |g y| ≤ C) {h : X × Y → ℝ}
    (hh : Measurable h) (hhb : ∀ᵐ p ∂μ, |h p| ≤ 1) :
    Integrable (fun p => g p.2 * h p) μ := by
  refine Integrable.mono' (integrable_const C)
    (((hg.comp measurable_snd).mul hh).aestronglyMeasurable) ?_
  filter_upwards [hhb] with p hp
  rw [Real.norm_eq_abs, abs_mul]
  calc |g p.2| * |h p| ≤ C * 1 := mul_le_mul (hgb p.2) hp (abs_nonneg _) hC
    _ = C := mul_one C

/-- `(PMP.8)`  The vertical information current. -/
def informationCurrent (κ : Kernel X Y) (P Q : Measure X) (p : X × Y) : ℝ :=
  posteriorContrast P Q p.1 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2

theorem measurable_informationCurrent (κ : Kernel X Y) (P Q : Measure X) :
    Measurable (informationCurrent κ P Q) :=
  ((measurable_posteriorContrast P Q).comp measurable_fst).sub
    ((measurable_posteriorContrast _ _).comp measurable_snd)

/-- `(PMP.9)`  The vertical current is orthogonal to every bounded observable. -/
theorem integral_mul_informationCurrent (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] {g : Y → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : 0 ≤ C) (hgb : ∀ y, |g y| ≤ C) :
    ∫ p, g p.2 * informationCurrent κ P Q p ∂((balancedLaw P Q) ⊗ₘ κ) = 0 := by
  have h1 : Integrable (fun p : X × Y => g p.2 * posteriorContrast P Q p.1)
      ((balancedLaw P Q) ⊗ₘ κ) :=
    integrable_mul_of_ae_bound (μ := (balancedLaw P Q) ⊗ₘ κ) hg hC hgb
      (h := fun p => posteriorContrast P Q p.1)
      ((measurable_posteriorContrast P Q).comp measurable_fst)
      (ae_abs_posteriorContrast_fst κ P Q)
  have h2 : Integrable (fun p : X × Y => g p.2 * posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2)
      ((balancedLaw P Q) ⊗ₘ κ) :=
    integrable_mul_of_ae_bound (μ := (balancedLaw P Q) ⊗ₘ κ) hg hC hgb
      (h := fun p => posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2)
      ((measurable_posteriorContrast _ _).comp measurable_snd)
      (ae_abs_posteriorContrast_snd κ P Q)
  have hfun : ∫ p, g p.2 * informationCurrent κ P Q p ∂((balancedLaw P Q) ⊗ₘ κ)
      = ∫ p, (g p.2 * posteriorContrast P Q p.1
        - g p.2 * posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2) ∂((balancedLaw P Q) ⊗ₘ κ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [informationCurrent]
    ring
  rw [hfun, integral_sub h1 h2, integral_observedContrast κ P Q hg hC hgb,
    integral_observedContrast_snd κ P Q hg hC hgb, sub_self]

/-! ## Exact information-current conservation -/

/-- The contrast truncated to `[-1,1]`; it agrees with the contrast almost everywhere. -/
def truncContrast (P Q : Measure X) (x : X) : ℝ := max (-1) (min 1 (posteriorContrast P Q x))

theorem measurable_truncContrast (P Q : Measure X) : Measurable (truncContrast P Q) :=
  (measurable_const.max (measurable_const.min (measurable_posteriorContrast P Q)))

theorem abs_truncContrast_le_one (P Q : Measure X) (x : X) : |truncContrast P Q x| ≤ 1 := by
  rw [abs_le, truncContrast]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem truncContrast_ae_eq (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    truncContrast P Q =ᵐ[balancedLaw P Q] posteriorContrast P Q := by
  filter_upwards [abs_posteriorContrast_le_one P Q] with x hx
  rw [abs_le] at hx
  rw [truncContrast, min_eq_right hx.2, max_eq_right hx.1]

/-- `(PMP.11)`  Coherence work. -/
def coherenceWork (P Q : Measure X) : ℝ :=
  4 * ∫ x, (posteriorContrast P Q x) ^ 2 ∂(balancedLaw P Q)

/-- `(PMP.10)`  Triangular discrimination. -/
def triangularDiscrimination (P Q : Measure X) : ℝ :=
  2 * ∫ x, (posteriorContrast P Q x) ^ 2 ∂(balancedLaw P Q)

/-- `(PMP.11)`  Coherence work is twice the triangular discrimination. -/
theorem coherenceWork_eq_two_mul (P Q : Measure X) :
    coherenceWork P Q = 2 * triangularDiscrimination P Q := by
  rw [coherenceWork, triangularDiscrimination]; ring

/-- `(PMP.10)`  Triangular discrimination is the classical `∫ (dP-dQ)²/(dP+dQ)`. -/
theorem triangularDiscrimination_eq (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    triangularDiscrimination P Q
      = ∫ x, ((P.rnDeriv (balancedLaw P Q) x).toReal - (Q.rnDeriv (balancedLaw P Q) x).toReal) ^ 2
          / ((P.rnDeriv (balancedLaw P Q) x).toReal
            + (Q.rnDeriv (balancedLaw P Q) x).toReal) ∂(balancedLaw P Q) := by
  rw [triangularDiscrimination, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [rnDeriv_right_toReal P Q] with x hx
  rw [hx, rnDeriv_left_toReal]
  have h : (1 + posteriorContrast P Q x) + (1 - posteriorContrast P Q x) = 2 := by ring
  rw [h, show (1 + posteriorContrast P Q x) - (1 - posteriorContrast P Q x)
    = 2 * posteriorContrast P Q x by ring]
  ring

theorem integral_fst_compProd (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [SFinite μ]
    {F : X → ℝ} (hF : Measurable F) :
    ∫ p, F p.1 ∂(μ ⊗ₘ κ) = ∫ x, F x ∂μ := by
  conv_rhs => rw [← Measure.fst_compProd μ κ]
  rw [Measure.fst, integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable]

theorem ae_snd_compProd (κ : Kernel X Y) [IsMarkovKernel κ] (μ : Measure X) [SFinite μ]
    {p : Y → Prop} (hp : MeasurableSet {y | p y}) (h : ∀ᵐ y ∂(⇑κ ∘ₘ μ), p y) :
    ∀ᵐ q ∂(μ ⊗ₘ κ), p q.2 := by
  have h1 : ∀ᵐ y ∂((μ ⊗ₘ κ).map Prod.snd), p y := by
    rw [← Measure.snd, Measure.snd_compProd]; exact h
  exact (ae_map_iff measurable_snd.aemeasurable hp).mp h1

/-- **Theorem 3.1, `(PMP.12)`.**  The exact Pythagorean data-processing identity: observed
coherence work plus vertical current energy reconstructs the source coherence work. -/
theorem coherenceWork_eq_add (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    coherenceWork P Q = coherenceWork (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q)
      + 4 * ∫ p, (informationCurrent κ P Q p) ^ 2 ∂((balancedLaw P Q) ⊗ₘ κ) := by
  set ρ := (balancedLaw P Q) ⊗ₘ κ with hρ
  set u : X × Y → ℝ := fun p => posteriorContrast P Q p.1 with hu
  set v : X × Y → ℝ := fun p => posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2 with hv
  have hum : Measurable u := (measurable_posteriorContrast P Q).comp measurable_fst
  have hvm : Measurable v := (measurable_posteriorContrast _ _).comp measurable_snd
  have hjm : Measurable (informationCurrent κ P Q) := measurable_informationCurrent κ P Q
  have hau : ∀ᵐ p ∂ρ, |u p| ≤ 1 := ae_abs_posteriorContrast_fst κ P Q
  have hav : ∀ᵐ p ∂ρ, |v p| ≤ 1 := ae_abs_posteriorContrast_snd κ P Q
  have haj : ∀ᵐ p ∂ρ, |informationCurrent κ P Q p| ≤ 2 := by
    filter_upwards [hau, hav] with p h1 h2
    have : informationCurrent κ P Q p = u p - v p := rfl
    rw [this]
    calc |u p - v p| ≤ |u p| + |v p| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
  have hbound : ∀ (w : X × Y → ℝ) (Cw : ℝ), 0 ≤ Cw → Measurable w → (∀ᵐ p ∂ρ, |w p| ≤ Cw) →
      Integrable w ρ := fun w Cw hCw hwm hwb =>
    Integrable.mono' (integrable_const Cw) hwm.aestronglyMeasurable
      (by filter_upwards [hwb] with p hp; simpa [Real.norm_eq_abs] using hp)
  have hiv2 : Integrable (fun p => (v p) ^ 2) ρ :=
    hbound _ 1 (by norm_num) (hvm.pow_const 2)
      (by filter_upwards [hav] with p hp; rw [abs_pow]; nlinarith [abs_nonneg (v p)])
  have hij2 : Integrable (fun p => (informationCurrent κ P Q p) ^ 2) ρ :=
    hbound _ 4 (by norm_num) (hjm.pow_const 2)
      (by filter_upwards [haj] with p hp; rw [abs_pow]
          nlinarith [abs_nonneg (informationCurrent κ P Q p)])
  have hivj : Integrable (fun p => v p * informationCurrent κ P Q p) ρ :=
    hbound _ 2 (by norm_num) (hvm.mul hjm)
      (by filter_upwards [hav, haj] with p h1 h2
          rw [abs_mul]
          nlinarith [abs_nonneg (v p), abs_nonneg (informationCurrent κ P Q p)])
  have hcross : ∫ p, v p * informationCurrent κ P Q p ∂ρ = 0 := by
    have htr : ∀ᵐ p ∂ρ, truncContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) p.2 = v p := by
      refine ae_snd_compProd κ (balancedLaw P Q)
        (measurableSet_eq_fun (measurable_truncContrast _ _) (measurable_posteriorContrast _ _)) ?_
      rw [← balancedLaw_comp κ P Q]
      exact truncContrast_ae_eq _ _
    have h0 := integral_mul_informationCurrent κ P Q (measurable_truncContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q))
      (C := 1) (by norm_num) (abs_truncContrast_le_one _ _)
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [htr] with p hp
    rw [hp]
  have hexpand : ∫ p, (u p) ^ 2 ∂ρ
      = ∫ p, (v p) ^ 2 ∂ρ + 2 * ∫ p, v p * informationCurrent κ P Q p ∂ρ
        + ∫ p, (informationCurrent κ P Q p) ^ 2 ∂ρ := by
    have hfun : ∀ p, (u p) ^ 2 = (v p) ^ 2 + 2 * (v p * informationCurrent κ P Q p)
        + (informationCurrent κ P Q p) ^ 2 := by
      intro p
      have : informationCurrent κ P Q p = u p - v p := rfl
      rw [this]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun),
      integral_add (f := fun p => (v p) ^ 2 + 2 * (v p * informationCurrent κ P Q p))
        (g := fun p => (informationCurrent κ P Q p) ^ 2) (hiv2.add (hivj.const_mul 2)) hij2,
      integral_add (f := fun p => (v p) ^ 2)
        (g := fun p => 2 * (v p * informationCurrent κ P Q p)) hiv2 (hivj.const_mul 2),
      integral_const_mul]
  have hA : ∫ x, (posteriorContrast P Q x) ^ 2 ∂(balancedLaw P Q) = ∫ p, (u p) ^ 2 ∂ρ :=
    (integral_fst_compProd κ (balancedLaw P Q)
      ((measurable_posteriorContrast P Q).pow_const 2)).symm
  have hB : ∫ y, (posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) y) ^ 2
      ∂(balancedLaw (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q)) = ∫ p, (v p) ^ 2 ∂ρ := by
    rw [balancedLaw_comp κ P Q,
      ← integral_snd_compProd κ (balancedLaw P Q)
        ((measurable_posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q)).pow_const 2)]
  rw [coherenceWork, coherenceWork, hA, hB, hexpand, hcross]
  ring

/-- **Theorem 3.1, `(PMP.13)`.**  The triangular-discrimination form. -/
theorem triangularDiscrimination_eq_add (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    triangularDiscrimination P Q = triangularDiscrimination (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q)
      + 2 * ∫ p, (informationCurrent κ P Q p) ^ 2 ∂((balancedLaw P Q) ⊗ₘ κ) := by
  have h := coherenceWork_eq_add κ P Q
  rw [coherenceWork_eq_two_mul, coherenceWork_eq_two_mul] at h
  linarith

theorem integrable_sq_informationCurrent (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    Integrable (fun z => (informationCurrent κ P Q z) ^ 2) ((balancedLaw P Q) ⊗ₘ κ) := by
  have haj : ∀ᵐ z ∂((balancedLaw P Q) ⊗ₘ κ), |informationCurrent κ P Q z| ≤ 2 := by
    filter_upwards [ae_abs_posteriorContrast_fst κ P Q, ae_abs_posteriorContrast_snd κ P Q]
      with z h1 h2
    have hz : informationCurrent κ P Q z
        = posteriorContrast P Q z.1 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) z.2 := rfl
    rw [hz]
    calc |posteriorContrast P Q z.1 - posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) z.2|
        ≤ |posteriorContrast P Q z.1| + |posteriorContrast (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) z.2| :=
          abs_sub _ _
      _ ≤ 1 + 1 := add_le_add h1 h2
      _ = 2 := by norm_num
  refine Integrable.mono' (integrable_const 4)
    ((measurable_informationCurrent κ P Q).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [haj] with z hz
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith [abs_nonneg (informationCurrent κ P Q z)]

/-- Triangular discrimination is monotone under a common observation kernel. -/
theorem triangularDiscrimination_comp_le (κ : Kernel X Y) [IsMarkovKernel κ] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    triangularDiscrimination (⇑κ ∘ₘ P) (⇑κ ∘ₘ Q) ≤ triangularDiscrimination P Q := by
  have h := triangularDiscrimination_eq_add κ P Q
  have hnn : 0 ≤ ∫ z, (informationCurrent κ P Q z) ^ 2 ∂((balancedLaw P Q) ⊗ₘ κ) :=
    integral_nonneg fun z => sq_nonneg _
  linarith


/-- The balanced law of a degenerate experiment is the law itself. -/
theorem balancedLaw_self (P : Measure X) : balancedLaw P P = P := by
  rw [balancedLaw, ← two_smul ℝ≥0∞ P, smul_smul,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

/-- A degenerate experiment has vanishing posterior contrast. -/
theorem posteriorContrast_self (P : Measure X) [SigmaFinite P] :
    posteriorContrast P P =ᵐ[balancedLaw P P] fun _ => 0 := by
  rw [balancedLaw_self]
  filter_upwards [Measure.rnDeriv_self P] with x hx
  rw [posteriorContrast, balancedLaw_self, hx]
  simp


end

end GaloisForLFunctions.HTGeometry
