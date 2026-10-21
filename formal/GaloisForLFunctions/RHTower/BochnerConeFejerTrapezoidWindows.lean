import GaloisForLFunctions.RHTower.HyperbolicAbelTransformHorocyclicSlice

/-!
# The Bochner cone on the line and Fejér windows

The **Bochner form** of a kernel `q` is `B_q(f) = ∫∫ q(a − b) f(a) f̄(b) da db` (`bochnerForm`);
`q` lies in the **Bochner cone** if `Re B_q(f) ≥ 0` for every continuous compactly supported `f`
(`IsBochnerPositive`).

**Fejér windows.**  The fejerTrapezoid `φ_L` (`1` on `[−L, L]`, `0` off `[−L−1, L+1]`, linear between)
has autocorrelation `A_L(t) = ∫ φ_L(x) φ_L(x − t) dx` within `4 + 4|t|` of `2L`
(`abs_autocorrelation_fejerTrapezoid_sub_le`): `φ_L(x − t) = φ_L(x)` off two intervals of length
`1 + 2|t|`.  Hence for a continuous compactly supported `κ`
`|∫∫ κ(x − x') φ_L(x) φ_L(x') − 2L ∫ κ| ≤ ∫ |κ(t)| (4 + 4|t|) dt`
(`norm_fejerTrapezoidForm_sub_le`): the form of a Fejér window grows like `2L ∫ κ`.

**Bochner cone ⟹ nonnegative transform** (`integral_mul_cos_nonneg_of_isBochnerPositive`).  With
`f = e^{iτ·} φ_L` the form is `2L ∫ q(t) e^{iτt} dt + O(1)`; letting `L → ∞`,
`∫ q(t) cos(τt) dt ≥ 0` for every real `τ`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

/-! ### The Bochner form -/

/-- The Bochner form `∫∫ q(a − b) f(a) f̄(b) da db`. -/
def bochnerForm (q f : ℝ → ℂ) : ℂ := ∫ a, ∫ b, q (a - b) * f a * conj (f b)

/-- The Bochner cone: `Re ∫∫ q(a − b) f(a) f̄(b) ≥ 0` for all continuous compactly supported `f`. -/
def IsBochnerPositive (q : ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f → 0 ≤ (bochnerForm (fun t => (q t : ℂ)) f).re

/-! ### The fejerTrapezoid -/

/-- The fejerTrapezoid `φ_L(x) = max(0, min(1, L + 1 − |x|))`. -/
def fejerTrapezoid (L x : ℝ) : ℝ := max 0 (min 1 (L + 1 - |x|))

theorem fejerTrapezoid_nonneg (L x : ℝ) : 0 ≤ fejerTrapezoid L x := le_max_left _ _

theorem fejerTrapezoid_le_one (L x : ℝ) : fejerTrapezoid L x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem fejerTrapezoid_eq_one {L x : ℝ} (hx : |x| ≤ L) : fejerTrapezoid L x = 1 := by
  rw [fejerTrapezoid, min_eq_left (by linarith), max_eq_right zero_le_one]

theorem fejerTrapezoid_eq_zero {L x : ℝ} (hx : L + 1 ≤ |x|) : fejerTrapezoid L x = 0 := by
  rw [fejerTrapezoid, max_eq_left (min_le_of_right_le (by linarith))]

theorem continuous_fejerTrapezoid (L : ℝ) : Continuous (fejerTrapezoid L) := by
  unfold fejerTrapezoid; fun_prop

theorem hasCompactSupport_fejerTrapezoid (L : ℝ) : HasCompactSupport (fejerTrapezoid L) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(L + 1)) (b := L + 1)) fun x hx => by
    refine fejerTrapezoid_eq_zero ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]

theorem integrable_indicator_one (s : Set ℝ) (hs : MeasurableSet s) (hfin : volume s ≠ ⊤) :
    Integrable (s.indicator fun _ => (1 : ℝ)) :=
  (integrable_indicator_iff hs).mpr (integrableOn_const hfin (by simp))

theorem integral_indicator_Icc {a b : ℝ} (hab : a ≤ b) :
    ∫ x, (Icc a b).indicator (fun _ => (1 : ℝ)) x = b - a := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
    Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

section Trapezoid

variable {L : ℝ} (hL : 0 ≤ L)
include hL

omit hL in
theorem integrable_fejerTrapezoid_mul {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable fun x => fejerTrapezoid L x * f x :=
  ((continuous_fejerTrapezoid L).mul hf).integrable_of_hasCompactSupport
    (hasCompactSupport_fejerTrapezoid L).mul_right

/-- `2L ≤ ∫ φ_L² ≤ 2L + 2`. -/
theorem abs_integral_fejerTrapezoid_sq_sub_le :
    |(∫ x, fejerTrapezoid L x * fejerTrapezoid L x) - 2 * L| ≤ 2 := by
  have hint := integrable_fejerTrapezoid_mul (L := L) (continuous_fejerTrapezoid L)
  have hlow : (Icc (-L) L).indicator (fun _ => (1 : ℝ)) ≤ fun x => fejerTrapezoid L x * fejerTrapezoid L x := by
    intro x
    dsimp only
    by_cases hx : x ∈ Icc (-L) L
    · rw [indicator_of_mem hx, fejerTrapezoid_eq_one (abs_le.mpr hx), mul_one]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (fejerTrapezoid_nonneg _ _) (fejerTrapezoid_nonneg _ _)
  have hupp : (fun x => fejerTrapezoid L x * fejerTrapezoid L x) ≤
      (Icc (-(L + 1)) (L + 1)).indicator (fun _ => (1 : ℝ)) := by
    intro x
    dsimp only
    by_cases hx : x ∈ Icc (-(L + 1)) (L + 1)
    · rw [indicator_of_mem hx]
      exact mul_le_one₀ (fejerTrapezoid_le_one _ _) (fejerTrapezoid_nonneg _ _) (fejerTrapezoid_le_one _ _)
    · rw [indicator_of_notMem hx]
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      have : L + 1 ≤ |x| := by
        rcases hx with h | h
        · linarith [neg_le_abs x]
        · linarith [le_abs_self x]
      rw [fejerTrapezoid_eq_zero this, zero_mul]
  have h1 : 2 * L ≤ ∫ x, fejerTrapezoid L x * fejerTrapezoid L x := by
    have h := integral_mono (integrable_indicator_one _ measurableSet_Icc (by simp)) hint hlow
    rw [integral_indicator_Icc (by linarith)] at h
    exact le_of_eq_of_le (by ring) h
  have h2 : ∫ x, fejerTrapezoid L x * fejerTrapezoid L x ≤ 2 * L + 2 := by
    have h := integral_mono hint (integrable_indicator_one _ measurableSet_Icc (by simp)) hupp
    rw [integral_indicator_Icc (by linarith)] at h
    exact le_of_le_of_eq h (by ring)
  rw [abs_le]; constructor <;> linarith

omit hL in
/-- `φ_L(x − t) = φ_L(x)` off `T = [−L−1−|t|, −L+|t|] ∪ [L−|t|, L+1+|t|]`. -/
theorem abs_fejerTrapezoid_mul_sub_le (t x : ℝ) :
    |fejerTrapezoid L x * (fejerTrapezoid L (x - t) - fejerTrapezoid L x)| ≤
      (Icc (-L - 1 - |t|) (-L + |t|)).indicator (fun _ => (1 : ℝ)) x +
        (Icc (L - |t|) (L + 1 + |t|)).indicator (fun _ => (1 : ℝ)) x := by
  have hbound : |fejerTrapezoid L x * (fejerTrapezoid L (x - t) - fejerTrapezoid L x)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (fejerTrapezoid_nonneg _ _)]
    refine mul_le_one₀ (fejerTrapezoid_le_one _ _) (abs_nonneg _) ?_
    rw [abs_le]
    constructor <;> linarith [fejerTrapezoid_nonneg L x, fejerTrapezoid_le_one L x,
      fejerTrapezoid_nonneg L (x - t), fejerTrapezoid_le_one L (x - t)]
  have hxt : |x| - |t| ≤ |x - t| ∧ |x - t| ≤ |x| + |t| :=
    ⟨by linarith [abs_sub_abs_le_abs_sub x t], abs_sub _ _⟩
  by_cases h1 : |x| ≤ L - |t|
  · rw [fejerTrapezoid_eq_one (by linarith), fejerTrapezoid_eq_one (by linarith)]
    simp only [sub_self, mul_zero, abs_zero]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun _ _ => zero_le_one) _)
  by_cases h2 : L + 1 + |t| ≤ |x|
  · rw [fejerTrapezoid_eq_zero (by linarith), fejerTrapezoid_eq_zero (by linarith)]
    simp only [sub_self, mul_zero, abs_zero]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun _ _ => zero_le_one) _)
  push Not at h1 h2
  refine hbound.trans ?_
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h1 h2
    rw [indicator_of_mem (show x ∈ Icc (L - |t|) (L + 1 + |t|) from ⟨h1.le, h2.le⟩)]
    have : 0 ≤ (Icc (-L - 1 - |t|) (-L + |t|)).indicator (fun _ => (1 : ℝ)) x :=
      indicator_nonneg (fun _ _ => zero_le_one) x
    linarith
  · rw [abs_of_neg hx] at h1 h2
    rw [indicator_of_mem (show x ∈ Icc (-L - 1 - |t|) (-L + |t|) from ⟨by linarith, by linarith⟩)]
    have : 0 ≤ (Icc (L - |t|) (L + 1 + |t|)).indicator (fun _ => (1 : ℝ)) x :=
      indicator_nonneg (fun _ _ => zero_le_one) x
    linarith

/-- **The Fejér autocorrelation.**  `|∫ φ_L(x) φ_L(x − t) dx − 2L| ≤ 4 + 4|t|`. -/
theorem abs_autocorrelation_fejerTrapezoid_sub_le (t : ℝ) :
    |(∫ x, fejerTrapezoid L x * fejerTrapezoid L (x - t)) - 2 * L| ≤ 4 + 4 * |t| := by
  have hint := integrable_fejerTrapezoid_mul (L := L) (continuous_fejerTrapezoid L)
  have hint' : Integrable fun x => fejerTrapezoid L x * fejerTrapezoid L (x - t) :=
    integrable_fejerTrapezoid_mul (L := L) ((continuous_fejerTrapezoid L).comp (continuous_sub_right t))
  have hT1 := integrable_indicator_one (Icc (-L - 1 - |t|) (-L + |t|)) measurableSet_Icc (by simp)
  have hT2 := integrable_indicator_one (Icc (L - |t|) (L + 1 + |t|)) measurableSet_Icc (by simp)
  have hsub : (∫ x, fejerTrapezoid L x * fejerTrapezoid L (x - t)) - ∫ x, fejerTrapezoid L x * fejerTrapezoid L x =
      ∫ x, (fejerTrapezoid L x * fejerTrapezoid L (x - t) - fejerTrapezoid L x * fejerTrapezoid L x) :=
    (integral_sub hint' hint).symm
  have hT : ∫ x, ((Icc (-L - 1 - |t|) (-L + |t|)).indicator (fun _ => (1 : ℝ)) x +
      (Icc (L - |t|) (L + 1 + |t|)).indicator (fun _ => (1 : ℝ)) x) = 2 + 4 * |t| := by
    rw [integral_add hT1 hT2, integral_indicator_Icc (by linarith [abs_nonneg t]),
      integral_indicator_Icc (by linarith [abs_nonneg t])]
    ring
  have hmono : ∫ x, |fejerTrapezoid L x * fejerTrapezoid L (x - t) - fejerTrapezoid L x * fejerTrapezoid L x| ≤
      ∫ x, ((Icc (-L - 1 - |t|) (-L + |t|)).indicator (fun _ => (1 : ℝ)) x +
        (Icc (L - |t|) (L + 1 + |t|)).indicator (fun _ => (1 : ℝ)) x) := by
    refine integral_mono (hint'.sub hint).abs (hT1.add hT2) fun x => ?_
    have := abs_fejerTrapezoid_mul_sub_le (L := L) t x
    rwa [mul_sub] at this
  have habs : |∫ x, (fejerTrapezoid L x * fejerTrapezoid L (x - t) - fejerTrapezoid L x * fejerTrapezoid L x)| ≤
      ∫ x, |fejerTrapezoid L x * fejerTrapezoid L (x - t) - fejerTrapezoid L x * fejerTrapezoid L x| :=
    abs_integral_le_integral_abs
  have hdiff : |(∫ x, fejerTrapezoid L x * fejerTrapezoid L (x - t)) - ∫ x, fejerTrapezoid L x * fejerTrapezoid L x| ≤
      2 + 4 * |t| := by
    rw [hsub]; linarith
  have hsq := abs_integral_fejerTrapezoid_sq_sub_le hL
  have htri := abs_sub_le (∫ x, fejerTrapezoid L x * fejerTrapezoid L (x - t))
    (∫ x, fejerTrapezoid L x * fejerTrapezoid L x) (2 * L)
  linarith

end Trapezoid

/-! ### Fejér windows and the Bochner cone -/

theorem hasCompactSupport_prod_mul {φ κ : ℝ → ℂ} (hφc : HasCompactSupport φ)
    (hκc : HasCompactSupport κ) (h : ℝ × ℝ → ℂ) :
    HasCompactSupport fun p : ℝ × ℝ => φ p.1 * κ p.2 * h p :=
  HasCompactSupport.intro (hφc.isCompact.prod hκc.isCompact) fun p hp => by
    rw [mem_prod, not_and_or] at hp
    rcases hp with h1 | h1
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero, zero_mul]

/-- `∫∫ κ(x − x') φ(x) ψ(x') dx dx' = ∫ κ(t) (∫ φ(x) ψ(x − t) dx) dt`. -/
theorem integral_integral_conv_eq {κ : ℝ → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hψ : Continuous ψ) :
    ∫ x, ∫ x', κ (x - x') * φ x * ψ x' = ∫ t, κ t * ((∫ x, φ x * ψ (x - t) : ℝ) : ℂ) := by
  have hin : ∀ x, ∫ x', κ (x - x') * φ x * ψ x' = ∫ t, (φ x : ℂ) * κ t * ψ (x - t) := by
    intro x
    have h := integral_sub_left_eq_self (fun t => (φ x : ℂ) * κ t * ψ (x - t)) (μ := volume) x
    simp only [sub_sub_cancel] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun x' => by simp only; ring)
  have hint : Integrable (Function.uncurry fun x t => (φ x : ℂ) * κ t * ψ (x - t))
      (volume.prod volume) := by
    have hc : Continuous (Function.uncurry fun x t => (φ x : ℂ) * κ t * ψ (x - t)) := by
      refine ((continuous_ofReal.comp (hφ.comp continuous_fst)).mul (hκ.comp continuous_snd)).mul
        (continuous_ofReal.comp (hψ.comp (continuous_fst.sub continuous_snd)))
    have hs := hasCompactSupport_prod_mul (φ := fun x => (φ x : ℂ)) (κ := κ)
      (hφc.comp_left Complex.ofReal_zero) hκc (fun p => (ψ (p.1 - p.2) : ℂ))
    rw [← Measure.volume_eq_prod]
    exact hc.integrable_of_hasCompactSupport hs
  rw [integral_congr_ae (Eventually.of_forall hin), integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [← integral_complex_ofReal, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => by push_cast; ring)

/-- **The Fejér form.**  `|∫∫ κ(x − x') φ_L(x) φ_L(x') − 2L ∫ κ| ≤ ∫ |κ(t)| (4 + 4|t|) dt`. -/
theorem norm_fejerTrapezoidForm_sub_le {κ : ℝ → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    {L : ℝ} (hL : 0 ≤ L) :
    ‖(∫ x, ∫ x', κ (x - x') * fejerTrapezoid L x * fejerTrapezoid L x') - 2 * L * ∫ t, κ t‖ ≤
      ∫ t, ‖κ t‖ * (4 + 4 * |t|) := by
  rw [integral_integral_conv_eq hκ hκc (continuous_fejerTrapezoid L) (hasCompactSupport_fejerTrapezoid L)
    (continuous_fejerTrapezoid L)]
  set A : ℝ → ℝ := fun t => ∫ x, fejerTrapezoid L x * fejerTrapezoid L (x - t) with hA
  have hAm : Measurable A := by
    have hm : StronglyMeasurable fun p : ℝ × ℝ => fejerTrapezoid L p.2 * fejerTrapezoid L (p.2 - p.1) :=
      ((continuous_fejerTrapezoid L).comp continuous_snd |>.mul
        ((continuous_fejerTrapezoid L).comp (continuous_snd.sub continuous_fst))).stronglyMeasurable
    exact hm.integral_prod_right'.measurable
  have hbnd : Integrable fun t => ‖κ t‖ * (4 + 4 * |t|) :=
    ((hκ.norm.mul (by fun_prop : Continuous fun t : ℝ => 4 + 4 * |t|))).integrable_of_hasCompactSupport
      (hκc.norm.mul_right)
  have hκi : Integrable κ := hκ.integrable_of_hasCompactSupport hκc
  have hint1 : Integrable fun t => κ t * ((A t : ℝ) : ℂ) := by
    refine ((hbnd.add (hκi.norm.const_mul (2 * L)))).mono'
      (hκ.aestronglyMeasurable.mul (continuous_ofReal.measurable.comp hAm).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    have h := abs_autocorrelation_fejerTrapezoid_sub_le hL t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |A t| ≤ 4 + 4 * |t| + 2 * L := by
      have := abs_sub_abs_le_abs_sub (A t) (2 * L)
      rw [abs_of_nonneg (by linarith : 0 ≤ 2 * L)] at this
      linarith
    calc ‖κ t‖ * |A t| ≤ ‖κ t‖ * (4 + 4 * |t| + 2 * L) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖κ t‖ * (4 + 4 * |t|) + 2 * L * ‖κ t‖ := by ring
  have heq : (∫ t, κ t * ((A t : ℝ) : ℂ)) - 2 * L * ∫ t, κ t =
      ∫ t, κ t * (((A t - 2 * L : ℝ)) : ℂ) := by
    rw [← integral_const_mul, ← integral_sub hint1 (hκi.const_mul _)]
    exact integral_congr_ae (Eventually.of_forall fun t => by push_cast; ring)
  rw [heq]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) hbnd (Eventually.of_forall fun t => ?_))
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (abs_autocorrelation_fejerTrapezoid_sub_le hL t) (norm_nonneg _)

/-- **The Bochner cone has nonnegative cosine transform.**  If `q` is continuous with compact
support and `Re ∫∫ q(a − b) f(a) f̄(b) ≥ 0` for all `f`, then `∫ q(v) cos(τv) dv ≥ 0`. -/
theorem integral_mul_cos_nonneg_of_isBochnerPositive {q : ℝ → ℝ} (hq : Continuous q)
    (hqc : HasCompactSupport q) (hpos : IsBochnerPositive q) (τ : ℝ) :
    0 ≤ ∫ v, q v * Real.cos (τ * v) := by
  set κ : ℝ → ℂ := fun t => (q t : ℂ) * cexp (τ * t * I) with hκ
  have hκc : Continuous κ := by simp only [hκ]; fun_prop
  have hκs : HasCompactSupport κ := (hqc.comp_left Complex.ofReal_zero).mul_right
  set D := ∫ t, ‖κ t‖ * (4 + 4 * |t|) with hD
  have hD0 : 0 ≤ D := integral_nonneg fun t => by positivity
  have hre : (∫ t, κ t).re = ∫ v, q v * Real.cos (τ * v) := by
    have hi : Integrable κ := hκc.integrable_of_hasCompactSupport hκs
    rw [← RCLike.re_eq_complex_re, ← integral_re hi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hκ, RCLike.re_eq_complex_re]
    rw [show (τ : ℂ) * t * I = ((τ * t : ℝ) : ℂ) * I by push_cast; ring, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  by_contra hneg
  push Not at hneg
  set c := ∫ v, q v * Real.cos (τ * v) with hc
  set L := D / (-c) + 1 with hL
  have hL0 : 0 ≤ L := by rw [hL]; have := div_nonneg hD0 (by linarith : 0 ≤ -c); linarith
  set f : ℝ → ℂ := fun a => cexp (τ * a * I) * fejerTrapezoid L a with hf
  have hfc : Continuous f := by
    simp only [hf]; exact (by fun_prop : Continuous fun a : ℝ => cexp (τ * a * I)).mul
      (continuous_ofReal.comp (continuous_fejerTrapezoid L))
  have hfs : HasCompactSupport f :=
    ((hasCompactSupport_fejerTrapezoid L).comp_left Complex.ofReal_zero).mul_left
  have hform : bochnerForm (fun t => (q t : ℂ)) f =
      ∫ x, ∫ x', κ (x - x') * fejerTrapezoid L x * fejerTrapezoid L x' := by
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    have e1 : conj (cexp ((τ : ℂ) * b * I)) = cexp (-((τ : ℂ) * b * I)) := by
      rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
    have e2 : cexp ((τ : ℂ) * ((a - b : ℝ) : ℂ) * I) =
        cexp ((τ : ℂ) * a * I) * cexp (-((τ : ℂ) * b * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp only [hf, hκ, map_mul, Complex.conj_ofReal, e1, e2]
    ring
  have h1 := hpos f hfc hfs
  have h2 := norm_fejerTrapezoidForm_sub_le hκc hκs hL0
  rw [← hform] at h2
  have h3 : (bochnerForm (fun t => (q t : ℂ)) f).re ≤ 2 * L * c + D := by
    have h4 := (Complex.re_le_norm _).trans h2
    rw [Complex.sub_re, show (2 * (L : ℂ) * ∫ t, κ t).re = 2 * L * (∫ t, κ t).re by
      rw [show (2 * (L : ℂ)) = ((2 * L : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul],
      hre] at h4
    linarith
  have h5 : 2 * L * c + D < 0 := by
    have hcneg : 0 < -c := by linarith
    have : L * (-c) = D + (-c) := by
      rw [hL, add_mul, div_mul_cancel₀ D hcneg.ne', one_mul]
    nlinarith
  linarith

end GaloisForLFunctions.RHTower.MehlerFock
