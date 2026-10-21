import GaloisForLFunctions.RHTower.HorocyclicSlicePointPairParseval
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.ParametricSmoothness

/-!
# The point-pair form as an integral of horocyclic fibre forms

Let `g` be continuous with compact support on `ℍ` and let its zero extension `G` to `ℂ` be smooth.
Put `A(ξ, y) = ∫ e^{−2πiξx} G(x + iy) dx` (`horocyclicCoefficient`).

* `y ↦ A(ξ, y)` is a Kontorovich–Lebedev test (`isKLTest_horocyclicCoefficient`) and
  `|A(ξ, y)| (1 + 2π|ξ|) ≤ D` uniformly (`exists_bound_horocyclicCoefficient`).
* Parseval on each pair of horocycles and Fubini give
  `Q_k(g) = ∫ B_ξ(A(ξ, ·)) dξ` (`pointPairForm_eq_integral_horocyclicFibreForm`).
* Hence `Re Q_k(g) ≥ 0` as soon as `Re h_k(½ + iτ) ≥ 0` for every `τ`
  (`re_pointPairForm_nonneg_of_contDiff`).
-/

open Complex MeasureTheory Set Filter Topology FourierTransform
open scoped ComplexConjugate Real ContDiff UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

open KontorovichLebedev

/-- The horocyclic slice `x ↦ G(x + iy)` of the zero extension `G` of `g`. -/
def horocyclicSlice (g : ℍ → ℂ) (y x : ℝ) : ℂ := zeroExtendC g ⟨x, y⟩

/-- The horocyclic Fourier coefficient `A(ξ, y) = ∫ e^{−2πiξx} G(x + iy) dx`. -/
def horocyclicCoefficient (g : ℍ → ℂ) (ξ y : ℝ) : ℂ := 𝓕 (horocyclicSlice g y) ξ

/-- Fubini on `ℝ × ℝ` for a measurable integrand dominated by `P 1_{[lo, hi]}(y) (1 + τ²)⁻¹`. -/
theorem integral_integral_comm_of_le_indicator {F : ℝ → ℝ → ℂ}
    (hF : Measurable (Function.uncurry F)) {lo hi P : ℝ}
    (hb : ∀ y τ, ‖F y τ‖ ≤ P * (Icc lo hi).indicator 1 y * (1 + τ ^ 2)⁻¹) :
    ∫ y, ∫ τ, F y τ = ∫ τ, ∫ y, F y τ :=
  integral_integral_swap ((Integrable.mul_prod
    (((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp) (by simp))).const_mul P) integrable_inv_one_add_sq).mono'
    hF.aestronglyMeasurable (Eventually.of_forall fun p => hb p.1 p.2))

section Smooth

variable {g : ℍ → ℂ} (hgs : ContDiff ℝ ∞ (zeroExtendC g))

include hgs in
theorem contDiff_zeroExtendC_chart : ContDiff ℝ ∞ fun p : ℝ × ℝ => zeroExtendC g ⟨p.1, p.2⟩ :=
  hgs.comp Complex.equivRealProdCLM.symm.contDiff

include hgs in
theorem contDiff_horocyclicSlice (y : ℝ) : ContDiff ℝ ∞ (horocyclicSlice g y) :=
  (contDiff_zeroExtendC_chart hgs).comp (contDiff_id.prodMk contDiff_const)

include hgs in
/-- `(ξ, y) ↦ A(ξ, y)` is measurable. -/
theorem measurable_horocyclicCoefficient :
    Measurable fun p : ℝ × ℝ => horocyclicCoefficient g p.1 p.2 := by
  have h : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ =>
      horocyclicPhase q.1.1 q.2 * horocyclicSlice g q.1.2 q.2 :=
    ((continuous_horocyclicPhase_uncurry.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      ((contDiff_zeroExtendC_chart hgs).continuous.comp
        (continuous_snd.prodMk continuous_fst.snd))).stronglyMeasurable
  rw [show (fun p : ℝ × ℝ => horocyclicCoefficient g p.1 p.2) =
    fun p => ∫ x, horocyclicPhase p.1 x * horocyclicSlice g p.2 x from
      funext fun p => fourier_eq_integral_horocyclicPhase _ _]
  exact h.integral_prod_right'.measurable

variable {a b X : ℝ} (ha : 0 < a) (hX : 0 ≤ X)
  (hbox : ∀ w : ℂ, zeroExtendC g w ≠ 0 → a ≤ w.im ∧ w.im ≤ b ∧ |w.re| ≤ X)

include hbox in
theorem horocyclicSlice_eq_zero_of_im {y : ℝ} (hy : y ∉ Icc a b) (x : ℝ) :
    horocyclicSlice g y x = 0 := by
  by_contra h
  exact hy ⟨(hbox _ h).1, (hbox _ h).2.1⟩

include hbox in
theorem horocyclicSlice_eq_zero_of_re {x : ℝ} (hx : X < |x|) (y : ℝ) :
    horocyclicSlice g y x = 0 := by
  by_contra h
  exact absurd (hbox _ h).2.2 (not_le.mpr hx)

include hbox in
theorem hasCompactSupport_horocyclicSlice (y : ℝ) : HasCompactSupport (horocyclicSlice g y) :=
  HasCompactSupport.intro (isCompact_Icc (a := -X) (b := X)) fun _ hx =>
    horocyclicSlice_eq_zero_of_re hbox (not_le.mp fun h => hx (abs_le.mp h)) y

include hbox in
theorem horocyclicCoefficient_eq_zero {y : ℝ} (hy : y ∉ Icc a b) (ξ : ℝ) :
    horocyclicCoefficient g ξ y = 0 := by
  rw [horocyclicCoefficient, fourier_eq_integral_horocyclicPhase]
  simp [horocyclicSlice_eq_zero_of_im hbox hy]

include hgs hX hbox in
/-- `y ↦ A(ξ, y)` is smooth: rescaled to `[0, 1]` it is a parametric average. -/
theorem contDiff_horocyclicCoefficient (ξ : ℝ) :
    ContDiff ℝ ∞ fun y => horocyclicCoefficient g ξ y := by
  have hc : 2 * (X + 1) ≠ 0 := by positivity
  set F : ℝ → ℝ → ℂ := fun y t => ((2 * (X + 1) : ℝ) : ℂ) *
    (horocyclicPhase ξ (2 * (X + 1) * t + -(X + 1)) *
      horocyclicSlice g y (2 * (X + 1) * t + -(X + 1))) with hFdef
  have hrep : ∀ y, horocyclicCoefficient g ξ y = HTGeometry.Interfinity.paramAvg F y := by
    intro y
    have h := intervalIntegral.integral_comp_mul_add
      (fun x => horocyclicPhase ξ x * horocyclicSlice g y x) hc (-(X + 1)) (a := 0) (b := 1)
    rw [mul_zero, zero_add, mul_one, show 2 * (X + 1) + -(X + 1) = X + 1 by ring] at h
    rw [HTGeometry.Interfinity.paramAvg, hFdef, intervalIntegral.integral_const_mul, h, Complex.real_smul,
      ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hc, Complex.ofReal_one, one_mul,
      intervalIntegral.integral_of_le (by linarith), horocyclicCoefficient,
      fourier_eq_integral_horocyclicPhase, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [horocyclicSlice_eq_zero_of_re hbox ?_ y, mul_zero]
    by_contra hle
    exact hx ⟨by linarith [neg_abs_le x, not_lt.mp hle], by linarith [le_abs_self x, not_lt.mp hle]⟩
  have hphase : ContDiff ℝ ∞ fun p : ℝ × ℝ => horocyclicPhase ξ (2 * (X + 1) * p.2 + -(X + 1)) := by
    unfold horocyclicPhase
    exact ((Complex.contDiff_exp : ContDiff ℂ ∞ cexp).restrict_scalars ℝ).comp
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        ((contDiff_const.mul contDiff_snd).add contDiff_const)))
  have hslice : ContDiff ℝ ∞ fun p : ℝ × ℝ =>
      horocyclicSlice g p.1 (2 * (X + 1) * p.2 + -(X + 1)) :=
    (contDiff_zeroExtendC_chart hgs).comp
      (((contDiff_const.mul contDiff_snd).add contDiff_const).prodMk contDiff_fst)
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := contDiff_const.mul (hphase.mul hslice)
  rw [show (fun y => horocyclicCoefficient g ξ y) = HTGeometry.Interfinity.paramAvg F from funext hrep]
  exact contDiff_infty.mpr fun n =>
    HTGeometry.Interfinity.contDiff_paramAvg n (hF.of_le (by exact_mod_cast le_top))

include hgs ha hX hbox in
/-- `y ↦ A(ξ, y)` is a Kontorovich–Lebedev test. -/
theorem isKLTest_horocyclicCoefficient (ξ : ℝ) :
    IsKLTest fun y => horocyclicCoefficient g ξ y := by
  have hsub : (Function.support fun y => horocyclicCoefficient g ξ y) ⊆ Icc a b :=
    fun y hy => by_contra fun h => hy (horocyclicCoefficient_eq_zero hbox h ξ)
  refine ⟨contDiff_horocyclicCoefficient hgs hX hbox ξ,
    HasCompactSupport.intro isCompact_Icc fun y hy => horocyclicCoefficient_eq_zero hbox hy ξ,
    fun y hy => ?_⟩
  exact ha.trans_le (closure_minimal hsub isClosed_Icc hy).1

include hgs hX hbox in
/-- **Uniform decay.**  `|A(ξ, y)| (1 + 2π|ξ|) ≤ D` for all `ξ, y`. -/
theorem exists_bound_horocyclicCoefficient :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ξ y, ‖horocyclicCoefficient g ξ y‖ * (1 + 2 * π * |ξ|) ≤ D := by
  set Φ := fun p : ℝ × ℝ => zeroExtendC g ⟨p.1, p.2⟩ with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_zeroExtendC_chart hgs
  have hΦs : HasCompactSupport Φ := HasCompactSupport.intro
    (isCompact_Icc (a := ((-X, a) : ℝ × ℝ)) (b := (X, b))) fun p hp => by
      by_contra h
      obtain ⟨h1, h2, h3⟩ := hbox _ h
      exact hp ⟨⟨(abs_le.mp h3).1, h1⟩, ⟨(abs_le.mp h3).2, h2⟩⟩
  have hΦ1c : Continuous fun p => fderiv ℝ Φ p (1, 0) :=
    (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hΦ1s : HasCompactSupport fun p => fderiv ℝ Φ p (1, 0) :=
    (hΦs.fderiv ℝ).mono fun p hp h0 => hp (by simp [h0])
  obtain ⟨S0, hS0⟩ := hΦ.continuous.bounded_above_of_compact_support hΦs
  obtain ⟨S1, hS1⟩ := hΦ1c.bounded_above_of_compact_support hΦ1s
  have hS0p : 0 ≤ S0 := (norm_nonneg _).trans (hS0 0)
  have hS1p : 0 ≤ S1 := (norm_nonneg _).trans (hS1 0)
  refine ⟨2 * X * S0 + 2 * X * S1, by positivity, fun ξ y => ?_⟩
  set s := horocyclicSlice g y
  have hder : ∀ x, HasDerivAt s (fderiv ℝ Φ (x, y) (1, 0)) x := fun x => by
    have hd : DifferentiableAt ℝ Φ (x, y) := hΦ.differentiable (by simp) (x, y)
    exact hd.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  have hds : deriv s = fun x => fderiv ℝ Φ (x, y) (1, 0) := funext fun x => (hder x).deriv
  have hsc : HasCompactSupport s := hasCompactSupport_horocyclicSlice hbox y
  have hsi : Integrable s := (contDiff_horocyclicSlice hgs y).continuous.integrable_of_hasCompactSupport hsc
  have hdsc : Continuous (deriv s) := by
    rw [hds]
    exact hΦ1c.comp (continuous_id.prodMk continuous_const)
  have hdsi : Integrable (deriv s) := hdsc.integrable_of_hasCompactSupport hsc.deriv
  have hout : ∀ {x}, X < |x| → s x = 0 ∧ deriv s x = 0 := fun {x} hx =>
    ⟨horocyclicSlice_eq_zero_of_re hbox hx y, by
      have hev : s =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with t ht
        exact horocyclicSlice_eq_zero_of_re hbox ht y
      rw [hev.deriv_eq, deriv_const]⟩
  have hint : ∀ {f : ℝ → ℂ} {S : ℝ}, (∀ x, ‖f x‖ ≤ S) → (∀ {x}, X < |x| → f x = 0) →
      ∫ x, ‖f x‖ ≤ 2 * X * S := fun {f S} hfS hf0 => by
    have hle : ∀ x, ‖f x‖ ≤ (Icc (-X) X).indicator (fun _ => S) x := fun x => by
      by_cases hx : x ∈ Icc (-X) X
      · rw [indicator_of_mem hx]; exact hfS x
      · rw [indicator_of_notMem hx, hf0 (not_le.mp fun h => hx (abs_le.mp h)), norm_zero]
    calc ∫ x, ‖f x‖ ≤ ∫ x, (Icc (-X) X).indicator (fun _ => S) x :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            ((integrable_indicator_iff measurableSet_Icc).mpr
              (integrableOn_const (by simp) (by simp))) (Eventually.of_forall hle)
      _ = 2 * X * S := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
            smul_eq_mul]
          ring
  have h0 : ‖horocyclicCoefficient g ξ y‖ ≤ 2 * X * S0 :=
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
      (hint (fun x => hS0 (x, y)) fun hx => (hout hx).1)
  have h1 : ‖horocyclicCoefficient g ξ y‖ * (2 * π * |ξ|) ≤ 2 * X * S1 := by
    have hkey := congrFun (Real.fourier_deriv hsi
      (fun x => (hder x).differentiableAt) hdsi) ξ
    have hb : ‖𝓕 (deriv s) ξ‖ ≤ 2 * X * S1 :=
      (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _).trans
        (hint (fun x => by rw [hds]; exact hS1 (x, y)) fun hx => (hout hx).2)
    rw [hkey, norm_smul] at hb
    have hn : ‖(2 * (π : ℂ) * Complex.I * (ξ : ℂ))‖ = 2 * π * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul]
      simp [abs_of_nonneg Real.pi_nonneg]
    rw [hn] at hb
    rw [horocyclicCoefficient]
    linarith
  nlinarith

end Smooth

/-! ### The fibre decomposition -/

section Decomposition

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : DeckPointPair.KernelSupport k R)
  {g : ℍ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : ContDiff ℝ ∞ (zeroExtendC g))
include hkc hkR hg hgc hgs

/-- **The fibre decomposition.**  `Q_k(g) = ∫ B_ξ(A(ξ, ·)) dξ`. -/
theorem pointPairForm_eq_integral_horocyclicFibreForm :
    pointPairForm k g = ∫ ξ, horocyclicFibreForm k ξ (horocyclicCoefficient g ξ) := by
  obtain ⟨a, b, X, ha, hX, hbox⟩ := exists_support_box_zeroExtendC hgc
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  obtain ⟨D, hD0, hD⟩ := exists_bound_horocyclicCoefficient hgs hX hbox
  set Ψ : ℝ → ℝ → ℝ → ℂ := fun y y' ξ => (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ : ℝ) : ℂ) *
    horocyclicFibreKernel k ξ y y' * horocyclicCoefficient g ξ y *
      conj (horocyclicCoefficient g ξ y') with hΨ
  -- Parseval on each pair of horocycles
  have hpars : ∀ y y', ∫ x, ∫ x', formIntegrand k g y y' x x' = ∫ ξ, Ψ y y' ξ := by
    intro y y'
    by_cases hy : y ∈ Icc a b
    · by_cases hy' : y' ∈ Icc a b
      · have h := integral_integral_pairKernel_slices hkc hkR
          (contDiff_horocyclicSlice hgs y).continuous (hasCompactSupport_horocyclicSlice hbox y)
          (contDiff_horocyclicSlice hgs y') (hasCompactSupport_horocyclicSlice hbox y')
          (ha.trans_le hy.1) (ha.trans_le hy'.1)
        calc ∫ x, ∫ x', formIntegrand k g y y' x x'
            = (((y ^ 2)⁻¹ * (y' ^ 2)⁻¹ : ℝ) : ℂ) * ∫ x, ∫ x', (k (pairUCoord x y x' y') : ℂ) *
                horocyclicSlice g y x * conj (horocyclicSlice g y' x') := by
              rw [← integral_const_mul]
              congr 1 with x
              rw [← integral_const_mul]
              congr 1 with x'
              simp only [formIntegrand, horocyclicSlice]
              push_cast
              ring
          _ = ∫ ξ, Ψ y y' ξ := by
              rw [h, ← integral_const_mul]
              congr 1 with ξ
              simp only [hΨ, horocyclicCoefficient]
              ring
      · have h1 := horocyclicSlice_eq_zero_of_im hbox hy'
        have h2 := fun ξ => horocyclicCoefficient_eq_zero hbox hy' ξ
        simp only [horocyclicSlice] at h1
        simp [formIntegrand, h1, hΨ, h2]
    · have h1 := horocyclicSlice_eq_zero_of_im hbox hy
      have h2 := fun ξ => horocyclicCoefficient_eq_zero hbox hy ξ
      simp only [horocyclicSlice] at h1
      simp [formIntegrand, h1, hΨ, h2]
  -- a uniform bound
  set Q := (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * (4 * Real.sqrt (max R 0 * (b * b)) * M) * D ^ 2
  have hΨb : ∀ y y' ξ, ‖Ψ y y' ξ‖ ≤
      Q * (Icc a b).indicator 1 y * (Icc a b).indicator 1 y' * (1 + ξ ^ 2)⁻¹ := by
    intro y y' ξ
    by_cases hy : y ∈ Icc a b
    · by_cases hy' : y' ∈ Icc a b
      · simp only [indicator_of_mem hy, indicator_of_mem hy', Pi.one_apply, mul_one]
        have hy0 : 0 < y := ha.trans_le hy.1
        have hy'0 : 0 < y' := ha.trans_le hy'.1
        have hK : ‖horocyclicFibreKernel k ξ y y'‖ ≤ 4 * Real.sqrt (max R 0 * (b * b)) * M :=
          (norm_horocyclicFibreKernel_le hkR hM hy0 hy'0).trans (by
            gcongr <;> first | exact hy.2 | exact hy'.2 | linarith [hy.1, hy.2])
        have hinv : (y ^ 2)⁻¹ * (y' ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ * (a ^ 2)⁻¹ := by
          gcongr
          · exact hy.1
          · exact hy'.1
        have hAA : ‖horocyclicCoefficient g ξ y‖ * ‖horocyclicCoefficient g ξ y'‖ ≤
            D ^ 2 * (1 + ξ ^ 2)⁻¹ := by
          have hsq : 1 + ξ ^ 2 ≤ (1 + 2 * π * |ξ|) ^ 2 := by
            have h1 : (1 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith [Real.pi_gt_three]
            calc 1 + ξ ^ 2 = 1 + |ξ| ^ 2 := by rw [sq_abs]
              _ ≤ 1 + (2 * π) ^ 2 * |ξ| ^ 2 := by
                  nlinarith [le_mul_of_one_le_left (sq_nonneg |ξ|) h1]
              _ ≤ (1 + 2 * π * |ξ|) ^ 2 := by
                  nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg ξ)]
          rw [le_mul_inv_iff₀ (by positivity)]
          calc ‖horocyclicCoefficient g ξ y‖ * ‖horocyclicCoefficient g ξ y'‖ * (1 + ξ ^ 2)
              ≤ ‖horocyclicCoefficient g ξ y‖ * ‖horocyclicCoefficient g ξ y'‖ *
                  (1 + 2 * π * |ξ|) ^ 2 := by gcongr
            _ = (‖horocyclicCoefficient g ξ y‖ * (1 + 2 * π * |ξ|)) *
                  (‖horocyclicCoefficient g ξ y'‖ * (1 + 2 * π * |ξ|)) := by ring
            _ ≤ D * D := by gcongr <;> exact hD _ _
            _ = D ^ 2 := by ring
        calc ‖Ψ y y' ξ‖ = (y ^ 2)⁻¹ * (y' ^ 2)⁻¹ * ‖horocyclicFibreKernel k ξ y y'‖ *
              (‖horocyclicCoefficient g ξ y‖ * ‖horocyclicCoefficient g ξ y'‖) := by
              simp only [hΨ, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
                abs_of_nonneg (inv_nonneg.mpr (sq_nonneg y)),
                abs_of_nonneg (inv_nonneg.mpr (sq_nonneg y'))]
              ring
          _ ≤ (a ^ 2)⁻¹ * (a ^ 2)⁻¹ * (4 * Real.sqrt (max R 0 * (b * b)) * M) *
              (D ^ 2 * (1 + ξ ^ 2)⁻¹) := by gcongr
          _ = Q * (1 + ξ ^ 2)⁻¹ := by ring
      · simp [hΨ, horocyclicCoefficient_eq_zero hbox hy' ξ, indicator_of_notMem hy']
    · simp [hΨ, horocyclicCoefficient_eq_zero hbox hy ξ, indicator_of_notMem hy]
  -- measurability
  have hA := measurable_horocyclicCoefficient hgs
  have hΨm : Measurable fun q : ℝ × ℝ × ℝ => Ψ q.1 q.2.1 q.2.2 := by
    have h1 : Measurable fun q : ℝ × ℝ × ℝ => ((((q.1 ^ 2)⁻¹ * (q.2.1 ^ 2)⁻¹ : ℝ)) : ℂ) := by
      fun_prop
    have h2 : Measurable fun q : ℝ × ℝ × ℝ => horocyclicFibreKernel k q.2.2 q.1 q.2.1 :=
      (measurable_horocyclicFibreKernel_uncurry hkc).comp
        (f := fun q : ℝ × ℝ × ℝ => (q.2.2, q.1, q.2.1)) (by fun_prop)
    have h3 : Measurable fun q : ℝ × ℝ × ℝ => horocyclicCoefficient g q.2.2 q.1 :=
      hA.comp (f := fun q : ℝ × ℝ × ℝ => (q.2.2, q.1)) (by fun_prop)
    have h4 : Measurable fun q : ℝ × ℝ × ℝ => horocyclicCoefficient g q.2.2 q.2.1 :=
      hA.comp (f := fun q : ℝ × ℝ × ℝ => (q.2.2, q.2.1)) (by fun_prop)
    exact ((h1.mul h2).mul h3).mul (Complex.continuous_conj.measurable.comp h4)
  -- reorder: `∫ y ∫ y' ∫ ξ = ∫ ξ ∫ y ∫ y'`
  have hin : ∀ y, ∫ y', ∫ ξ, Ψ y y' ξ = ∫ ξ, ∫ y', Ψ y y' ξ := fun y =>
    integral_integral_comm_of_le_indicator (F := fun y' ξ => Ψ y y' ξ)
      (hΨm.comp (f := fun p : ℝ × ℝ => (y, p.1, p.2)) (by fun_prop))
      (P := Q * (Icc a b).indicator 1 y) fun y' ξ => hΨb y y' ξ
  have hout : ∫ y, ∫ ξ, ∫ y', Ψ y y' ξ = ∫ ξ, ∫ y, ∫ y', Ψ y y' ξ := by
    refine integral_integral_comm_of_le_indicator (F := fun y ξ => ∫ y', Ψ y y' ξ) ?_
      (lo := a) (hi := b) (P := Q * volume.real (Icc a b)) fun y ξ => ?_
    · exact ((hΨm.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2, q.1.2))
        (by fun_prop)).stronglyMeasurable.integral_prod_right').measurable
    · have hQ : 0 ≤ Q := by positivity
      calc ‖∫ y', Ψ y y' ξ‖
          ≤ ∫ y', Q * (Icc a b).indicator 1 y * (1 + ξ ^ 2)⁻¹ * (Icc a b).indicator 1 y' :=
            norm_integral_le_of_norm_le (((integrable_indicator_iff measurableSet_Icc).mpr
              (integrableOn_const (by simp) (by simp))).const_mul _)
              (Eventually.of_forall fun y' => (hΨb y y' ξ).trans_eq (by ring))
        _ = Q * volume.real (Icc a b) * (Icc a b).indicator 1 y * (1 + ξ ^ 2)⁻¹ := by
            rw [integral_const_mul, integral_indicator_one measurableSet_Icc]
            ring
  simp only [pointPairForm_eq_iterated hkc hkR hg hgc, hpars, hin, hout]
  rfl

include hkc hkR hg hgc hgs in
/-- **Positivity for smooth tests.**  If `Re h_k(½ + iτ) ≥ 0` for every `τ`, then
`Re Q_k(g) ≥ 0` for every `g` with smooth zero extension. -/
theorem re_pointPairForm_nonneg_of_contDiff
    (hh : ∀ τ : ℝ, 0 ≤ (DeckPointPair.selbergTransform k (1 / 2 + τ * I)).re) :
    0 ≤ (pointPairForm k g).re := by
  obtain ⟨a, b, X, ha, hX, hbox⟩ := exists_support_box_zeroExtendC hgc
  rw [pointPairForm_eq_integral_horocyclicFibreForm hkc hkR hg hgc hgs]
  have hae : ∀ᵐ ξ : ℝ, 0 ≤ (horocyclicFibreForm k ξ (horocyclicCoefficient g ξ)).re := by
    have h0 : ∀ᵐ ξ : ℝ, ξ ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with ξ hξ
    exact re_horocyclicFibreForm_nonneg hkc hkR hξ
      (isKLTest_horocyclicCoefficient hgs ha hX hbox ξ) hh
  by_cases hint : Integrable fun ξ => horocyclicFibreForm k ξ (horocyclicCoefficient g ξ)
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    exact integral_nonneg_of_ae hae
  · rw [integral_undef hint, Complex.zero_re]

end Decomposition

end GaloisForLFunctions.RHTower.MehlerFock
