import GaloisForLFunctions.HTGeometry.FourierZeroDivisionGroundStates

/-!
# Division by a Fourier–Laplace zero for integrable compactly supported functions

For `f` integrable and vanishing off `[-a, a]`, put `f̂(w) = ∫ e^{-2πiwx} f(x) dx`
(`unitaryLaplace`; on the real line it is mathlib's Fourier transform, `unitaryLaplace_ofReal`).
If `f̂(w₀) = 0`, the function

`g(x) = 2πi e^{2πiw₀x} ∫_{-a}^{x} e^{-2πiw₀y} f(y) dy`  (`divLaplace`)

is continuous, vanishes off `[-a, a]` (the primitive is `f̂(w₀) = 0` beyond `a`), and

`ĝ(w) = f̂(w)/(w − w₀)`,  `w ≠ w₀`  (`unitaryLaplace_divLaplace`).

The proof is Fubini on the triangle `-a ≤ y ≤ x ≤ a`: the inner integral
`∫_y^a e^{-2πi(w−w₀)x} dx` is explicit, and the boundary term is a multiple of `f̂(w₀) = 0`.
No continuity of `f` is used, so the division applies to `L²` functions on an interval.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Real

namespace GaloisForLFunctions.HTGeometry.FourierLaplaceDivision

open GaloisForLFunctions.HTGeometry.FourierZeroFlip

/-- The Fourier–Laplace transform in the unitary convention, `f̂(w) = ∫ e^{-2πiwx} f(x) dx`. -/
def unitaryLaplace (f : ℝ → ℂ) (w : ℂ) : ℂ := ∫ x : ℝ, cexp (-(2 * π * I * w * x)) * f x

/-- The division kernel `g(x) = 2πi e^{2πiw₀x} ∫_{-a}^{x} e^{-2πiw₀y} f(y) dy`. -/
def divLaplace (a : ℝ) (f : ℝ → ℂ) (w₀ : ℂ) (x : ℝ) : ℂ :=
  2 * π * I * cexp (2 * π * I * w₀ * x) * ∫ y in (-a)..x, cexp (-(2 * π * I * w₀ * y)) * f y

theorem norm_cexp_le_of_mem_Icc {a : ℝ} (w : ℂ) {x : ℝ} (hx : x ∈ Icc (-a) a) :
    ‖cexp (-(2 * π * I * w * x))‖ ≤ Real.exp (2 * π * |w.im| * a) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (-(2 * π * I * w * (x : ℂ))).re = 2 * π * w.im * x := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hxa : |x| ≤ a := abs_le.mpr ⟨hx.1, hx.2⟩
  have h1 : w.im * x ≤ |w.im| * |x| := by
    rw [← abs_mul]; exact le_abs_self _
  have h2 : |w.im| * |x| ≤ |w.im| * a := mul_le_mul_of_nonneg_left hxa (abs_nonneg _)
  have hπ := Real.pi_pos
  nlinarith

theorem integrable_exp_mul_of_supportedIn {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hs : SupportedIn a f) (w : ℂ) : Integrable fun x : ℝ => cexp (-(2 * π * I * w * x)) * f x := by
  have hon : IntegrableOn (fun x : ℝ => cexp (-(2 * π * I * w * x)) * f x) (Icc (-a) a) :=
    Integrable.bdd_mul (c := Real.exp (2 * π * |w.im| * a)) hf.integrableOn
      ((by fun_prop : Continuous fun x : ℝ => cexp (-(2 * π * I * w * x))).aestronglyMeasurable)
      (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => norm_cexp_le_of_mem_Icc w hx)
  refine (hon.integrable_indicator measurableSet_Icc).congr (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Icc (-a) a
  · simp [hx]
  · simp [hx, hs x hx]

theorem primitive_eq_zero_of_le {a : ℝ} {f : ℝ → ℂ} (hs : SupportedIn a f) (w₀ : ℂ) {x : ℝ}
    (hx : x ≤ -a) : ∫ y in (-a)..x, cexp (-(2 * π * I * w₀ * y)) * f y = 0 := by
  apply intervalIntegral.integral_zero_ae
  filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := -a))] with y hy hyI
  rw [uIoc_of_ge hx] at hyI
  have hlt : y < -a := lt_of_le_of_ne hyI.2 (Set.mem_compl_singleton_iff.mp hy)
  rw [hs y fun h => by linarith [h.1], mul_zero]

theorem primitive_eq_unitaryLaplace_of_ge {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hs : SupportedIn a f) (w₀ : ℂ) {x : ℝ} (hx : a ≤ x) :
    ∫ y in (-a)..x, cexp (-(2 * π * I * w₀ * y)) * f y = unitaryLaplace f w₀ := by
  rw [intervalIntegral.integral_of_le (by linarith), unitaryLaplace,
    ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := -a))] with y hy
  by_cases hy' : y ∈ Ioc (-a) x
  · simp [hy']
  · rw [indicator_of_notMem hy']
    have hyc : y ∉ Icc (-a) a := by
      intro h
      exact hy' ⟨lt_of_le_of_ne h.1 fun h' => Set.mem_compl_singleton_iff.mp hy h'.symm,
        le_trans h.2 hx⟩
    rw [hs y hyc, mul_zero]

theorem supportedIn_divLaplace {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hs : SupportedIn a f) {w₀ : ℂ} (hz : unitaryLaplace f w₀ = 0) :
    SupportedIn a (divLaplace a f w₀) := by
  intro x hx
  rcases le_or_gt x (-a) with h | h
  · simp [divLaplace, primitive_eq_zero_of_le hs w₀ h]
  · have hax : a ≤ x := by
      by_contra hlt
      exact hx ⟨h.le, (not_le.mp hlt).le⟩
    simp [divLaplace, primitive_eq_unitaryLaplace_of_ge ha hs w₀ hax, hz]

theorem continuous_divLaplace {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f) (hs : SupportedIn a f)
    (w₀ : ℂ) : Continuous (divLaplace a f w₀) := by
  have hi : ∀ b c : ℝ, IntervalIntegrable (fun y : ℝ => cexp (-(2 * π * I * w₀ * y)) * f y)
      volume b c := fun b c => (integrable_exp_mul_of_supportedIn hf hs w₀).intervalIntegrable
  have hp := intervalIntegral.continuous_primitive hi (-a)
  exact (continuous_const.mul (by fun_prop)).mul hp

theorem hasCompactSupport_of_supportedIn {a : ℝ} {g : ℝ → ℂ} (hs : SupportedIn a g) :
    HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun x hx => hs x hx

/-- **Division by a Fourier–Laplace zero.**  If `f̂(w₀) = 0`, then `ĝ(w) = f̂(w)/(w − w₀)` for the
compactly supported `g = divLaplace a f w₀`. -/
theorem unitaryLaplace_divLaplace {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : SupportedIn a f) {w₀ : ℂ} (hz : unitaryLaplace f w₀ = 0) {w : ℂ} (hw : w ≠ w₀) :
    unitaryLaplace (divLaplace a f w₀) w = unitaryLaplace f w / (w - w₀) := by
  set g : ℝ → ℂ := fun y => cexp (-(2 * π * I * w₀ * y)) * f y with hgdef
  set c : ℂ := -(2 * π * I * (w - w₀)) with hcdef
  have hwz : w - w₀ ≠ 0 := sub_ne_zero.mpr hw
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) hwz)
  have hgi : Integrable g := integrable_exp_mul_of_supportedIn hf hs w₀
  set φ : ℝ → ℂ := (Icc (-a) a).indicator fun x => cexp (c * x) with hφ
  have hφi : Integrable φ := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    exact (by fun_prop : Continuous fun x : ℝ => cexp (c * x)).integrableOn_Icc
  set K : ℝ × ℝ → ℂ := fun p => φ p.1 * ((Iic p.1).indicator g p.2) with hK
  -- integrability of the kernel
  have hKm : AEStronglyMeasurable K (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1) (volume.prod volume) :=
      hφi.aestronglyMeasurable.comp_fst
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2) (volume.prod volume) :=
      hgi.aestronglyMeasurable.comp_snd
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => ({q : ℝ × ℝ | q.2 ≤ q.1}.indicator
        (fun _ => (1 : ℂ)) p)) (volume.prod volume) :=
      (Measurable.indicator measurable_const
        (measurableSet_le measurable_snd measurable_fst)).aestronglyMeasurable
    refine (h1.mul (h3.mul h2)).congr (Eventually.of_forall fun p => ?_)
    by_cases h : p.2 ≤ p.1
    · simp [hK, indicator_of_mem (show p.2 ∈ Iic p.1 from h),
        indicator_of_mem (show p ∈ {q : ℝ × ℝ | q.2 ≤ q.1} from h)]
    · simp [hK, indicator_of_notMem (show p.2 ∉ Iic p.1 from h),
        indicator_of_notMem (show p ∉ {q : ℝ × ℝ | q.2 ≤ q.1} from h)]
  have hKi : Integrable K (volume.prod volume) := by
    refine (hφi.mul_prod hgi).mono hKm (Eventually.of_forall fun p => ?_)
    simp only [hK, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases h : p.2 ≤ p.1
    · simp [indicator_of_mem (show p.2 ∈ Iic p.1 from h)]
    · simp [indicator_of_notMem (show p.2 ∉ Iic p.1 from h)]
  -- the x-first iterated integral is `f̂(divLaplace)/(2πi)`
  have hprim : ∀ x ∈ Icc (-a) a, (∫ y in (-a)..x, g y) = ∫ y, (Iic x).indicator g y := by
    intro x hx
    rw [intervalIntegral.integral_of_le hx.1, ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (Real.volume_singleton (a := -a))] with y hy
    by_cases hy1 : y ≤ -a
    · have hya : y < -a := lt_of_le_of_ne hy1 (Set.mem_compl_singleton_iff.mp hy)
      have hgy : g y = 0 := by
        simp only [hgdef]; rw [hs y fun h => by linarith [h.1], mul_zero]
      rw [indicator_of_notMem (fun h : y ∈ Ioc (-a) x => by linarith [h.1])]
      by_cases hyx : y ≤ x
      · rw [indicator_of_mem (show y ∈ Iic x from hyx), hgy]
      · rw [indicator_of_notMem (show y ∉ Iic x from hyx)]
    · push Not at hy1
      by_cases hyx : y ≤ x
      · rw [indicator_of_mem (show y ∈ Ioc (-a) x from ⟨hy1, hyx⟩),
          indicator_of_mem (show y ∈ Iic x from hyx)]
      · rw [indicator_of_notMem (fun h : y ∈ Ioc (-a) x => hyx h.2),
          indicator_of_notMem (show y ∉ Iic x from hyx)]
  have hleft : unitaryLaplace (divLaplace a f w₀) w = 2 * π * I * ∫ x, ∫ y, K (x, y) := by
    rw [unitaryLaplace, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hK]
    rw [integral_const_mul]
    by_cases hx : x ∈ Icc (-a) a
    · simp only [hφ, indicator_of_mem hx]
      rw [← hprim x hx, divLaplace]
      have he : cexp (-(2 * π * I * w * x)) * cexp (2 * π * I * w₀ * x) = cexp (c * x) := by
        rw [← Complex.exp_add, hcdef]; ring_nf
      linear_combination (2 * π * I * ∫ y in (-a)..x, g y) * he
    · simp only [hφ, indicator_of_notMem hx, zero_mul, mul_zero]
      rw [supportedIn_divLaplace ha hs hz x hx, mul_zero]
  -- the y-first iterated integral
  have hinner : ∀ y : ℝ, (∫ x, K (x, y)) = g y * ((cexp (c * a) - cexp (c * y)) / c) := by
    intro y
    by_cases hy : y ∈ Icc (-a) a
    · have hpt : (fun x : ℝ => K (x, y)) =
          (Icc y a).indicator fun x : ℝ => cexp (c * x) * g y := by
        funext x
        simp only [hK, hφ]
        by_cases hx : x ∈ Icc y a
        · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ Icc (-a) a from ⟨le_trans hy.1 hx.1,
            hx.2⟩), indicator_of_mem (show y ∈ Iic x from hx.1)]
        · rw [indicator_of_notMem hx]
          by_cases hxa : x ∈ Icc (-a) a
          · rw [indicator_of_mem hxa, indicator_of_notMem (show y ∉ Iic x from fun h =>
              hx ⟨h, hxa.2⟩), mul_zero]
          · rw [indicator_of_notMem hxa, zero_mul]
      rw [hpt, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hy.2, intervalIntegral.integral_mul_const,
        integral_exp_mul_complex hc]
      ring
    · have hgy : g y = 0 := by simp only [hgdef]; rw [hs y hy, mul_zero]
      have hz0 : (fun x : ℝ => K (x, y)) = fun _ => 0 := by
        funext x; simp only [hK]
        by_cases hyx : y ≤ x
        · rw [indicator_of_mem (show y ∈ Iic x from hyx), hgy, mul_zero]
        · rw [indicator_of_notMem (show y ∉ Iic x from hyx), mul_zero]
      rw [hz0, integral_zero, hgy, zero_mul]
  have hswap := integral_integral_swap (f := fun x y => K (x, y)) hKi
  have hright : (∫ y, ∫ x, K (x, y)) = (cexp (c * a) * unitaryLaplace f w₀ -
      unitaryLaplace f w) / c := by
    simp_rw [hinner]
    have hgw : Integrable fun y : ℝ => g y * cexp (c * y) := by
      refine (integrable_exp_mul_of_supportedIn hf hs w).congr (Eventually.of_forall fun y => ?_)
      simp only [hgdef]
      have : cexp (-(2 * π * I * w * y)) = cexp (-(2 * π * I * w₀ * y)) * cexp (c * y) := by
        rw [← Complex.exp_add, hcdef]; ring_nf
      rw [this]; ring
    have hsplit : (fun y : ℝ => g y * ((cexp (c * a) - cexp (c * y)) / c)) =
        fun y => (cexp (c * a) / c) * g y - (1 / c) * (g y * cexp (c * y)) := by
      funext y; field_simp
    rw [hsplit, integral_sub (hgi.const_mul _) (hgw.const_mul _), integral_const_mul,
      integral_const_mul]
    have hFw : (∫ y, g y * cexp (c * y)) = unitaryLaplace f w := by
      rw [unitaryLaplace]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hgdef]
      have : cexp (-(2 * π * I * w * y)) = cexp (-(2 * π * I * w₀ * y)) * cexp (c * y) := by
        rw [← Complex.exp_add, hcdef]; ring_nf
      rw [this]; ring
    rw [hFw, show (∫ y, g y) = unitaryLaplace f w₀ from rfl]
    field_simp
  rw [hleft, hswap, hright, hz, mul_zero, zero_sub, hcdef]
  field_simp

/-- On the real line the Fourier–Laplace transform is mathlib's Fourier transform. -/
theorem unitaryLaplace_ofReal (f : ℝ → ℂ) (ξ : ℝ) :
    unitaryLaplace f ξ = FourierTransform.fourier f ξ := by
  rw [Real.fourier_eq', unitaryLaplace]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 1
  push_cast
  ring_nf

theorem continuous_unitaryLaplace_ofReal {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous fun ξ : ℝ => unitaryLaplace f ξ := by
  unfold unitaryLaplace
  refine continuous_of_dominated (bound := fun x => ‖f x‖) (fun ξ => ?_) (fun ξ => ?_)
    hf.norm (Eventually.of_forall fun x => by fun_prop)
  · exact ((by fun_prop : Continuous fun x : ℝ =>
      cexp (-(2 * π * I * (ξ : ℂ) * x))).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(2 * π * I * (ξ : ℂ) * (x : ℂ))).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero, one_mul]

theorem unitaryLaplace_add_mul {a : ℝ} {f g : ℝ → ℂ} (hf : Integrable f) (hfs : SupportedIn a f)
    (hg : Integrable g) (hgs : SupportedIn a g) (c w : ℂ) :
    unitaryLaplace (fun x => f x + c * g x) w = unitaryLaplace f w + c * unitaryLaplace g w := by
  unfold unitaryLaplace
  rw [← integral_const_mul, ← integral_add (integrable_exp_mul_of_supportedIn hf hfs w)
    ((integrable_exp_mul_of_supportedIn hg hgs w).const_mul c)]
  congr 1
  funext x
  ring

theorem integrable_divLaplace {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : SupportedIn a f) {w₀ : ℂ} (hz : unitaryLaplace f w₀ = 0) :
    Integrable (divLaplace a f w₀) :=
  (continuous_divLaplace hf hs w₀).integrable_of_hasCompactSupport
    (hasCompactSupport_of_supportedIn (supportedIn_divLaplace ha hs hz))

theorem memLp_divLaplace {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : SupportedIn a f) {w₀ : ℂ} (hz : unitaryLaplace f w₀ = 0) :
    MemLp (divLaplace a f w₀) 2 volume :=
  (continuous_divLaplace hf hs w₀).memLp_of_hasCompactSupport
    (hasCompactSupport_of_supportedIn (supportedIn_divLaplace ha hs hz))

end GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
