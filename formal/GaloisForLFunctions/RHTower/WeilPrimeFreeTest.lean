import GaloisForLFunctions.RHTower.WeilPrimeFreeFamily
import GaloisForLFunctions.RHTower.WeilDeletionCCMSource
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCCMScalingBridge

/-!
# A pole-vanishing low-frequency test source

The wide bump `x ↦ φ(x/L)` built from the smooth kernel `φ = phiN 2`, multiplied by the polar
translate combination of the corpus, is a pole-vanishing smooth interior source whose Fourier
transform is `m(ξ)·L·φ̂(Lξ)` with `m(ξ) = (cos 2πξ − 1)(cos 2πξ − cosh ½)`.  This file records the
Fourier identities and the pointwise bounds on `m` and on `φ̂` (decay of order three at infinity,
size at least one half near the origin) that the negativity estimate of the archimedean part uses,
together with the two facts about the archimedean phase rate it needs: it is negative on a
neighbourhood of the origin and bounded by `35 + |t|` everywhere.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform

noncomputable section

namespace RHTower.WeilDeletion

/-! ## The wide bump source -/

/-- Support radius of the base kernel `phiN 2`. -/
def sTwo : ℝ := sN 2

theorem sTwo_pos : 0 < sTwo := sN_pos 2

theorem sTwo_val : sTwo = 2 / 5 + 3 * (39 / 50) := by
  unfold sTwo sN
  norm_num

/-- The base kernel as a complex-valued function. -/
def phiTwoC : ℝ → ℂ := fun x => (phiN 2 x : ℂ)

def wideBumpAperture (L : ℝ) (hL : 1 ≤ L) : SuzukiPositiveAperture :=
  ⟨L * sTwo + 1, by have := sTwo_pos; positivity⟩

theorem support_wideBump_subset (L : ℝ) (hL : 1 ≤ L) :
    Function.support (fun x : ℝ => (phiN 2 (x / L) : ℂ)) ⊆ Icc (-(L * sTwo)) (L * sTwo) := by
  intro x hx
  rw [Function.mem_support] at hx
  have hne : phiN 2 (x / L) ≠ 0 := fun h => hx (by rw [h]; simp)
  have hmem := support_phiN_subset 2 (Function.mem_support.mpr hne)
  rw [mem_Icc] at hmem ⊢
  have hLpos : 0 < L := by linarith
  constructor
  · have := hmem.1
    rw [le_div_iff₀ hLpos] at this
    change -(L * sN 2) ≤ x
    linarith
  · have := hmem.2
    rw [div_le_iff₀ hLpos] at this
    change x ≤ L * sN 2
    linarith

/-- The wide bump `x ↦ φ(x/L)` as a smooth interior source. -/
def wideBumpSource (L : ℝ) (hL : 1 ≤ L) : CCMComplexSmoothInteriorSource (wideBumpAperture L hL) where
  toFun := fun x => (phiN 2 (x / L) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp ((phiN_contDiff_top 2).comp (contDiff_id.div_const L))
  hasCompactSupport :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_wideBump_subset L hL)
  tsupport_subset := by
    refine (closure_minimal (support_wideBump_subset L hL) isClosed_Icc).trans ?_
    have := sTwo_pos
    exact Icc_subset_Ioo (by show -(L * sTwo + 1) < -(L * sTwo); linarith)
      (by show L * sTwo < L * sTwo + 1; linarith)

/-- The pole-vanishing test: the polar translate of the wide bump. -/
def primeFreeTest (L : ℝ) (hL : 1 ≤ L) :
    CCMComplexSmoothInteriorSource ((wideBumpAperture L hL).enlarge 1 one_pos) :=
  (wideBumpSource L hL).polarTranslate one_pos

theorem primeFreeTest_isPolarConstrained (L : ℝ) (hL : 1 ≤ L) :
    IsPolarConstrained _ (primeFreeTest L hL).toCCMFormVector :=
  isPolarConstrained_polarTranslate _ one_pos

/-! ## Fourier identities -/

/-- Mathlib's Fourier transform in terms of the paper transform. -/
theorem fourier_eq_paperFT (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = Zeta23.paperFT f (-(2 * Real.pi * ξ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold Zeta23.paperFT
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

theorem fourier_eq_integral_cexp (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ v : ℝ, Complex.exp ((-(I * ((2 * Real.pi * ξ : ℝ) : ℂ))) * (v : ℂ)) * f v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- The Fourier transform of a polar translate is the spectral symbol times the transform. -/
theorem fourier_polarTranslate {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    {h : ℝ} (hh : 0 < h) (ξ : ℝ) :
    𝓕 ((u.polarTranslate hh).toSchwartz : ℝ → ℂ) ξ =
      polarMultiplierSpectral h ((2 * Real.pi * ξ : ℝ) : ℂ) * 𝓕 (u.toSchwartz : ℝ → ℂ) ξ := by
  have hfun : ((u.polarTranslate hh).toSchwartz : ℝ → ℂ) =
      translateCombo (polarMultiplierWeight h) (polarMultiplierShift h) (u : ℝ → ℂ) := by
    funext x
    rfl
  have hfun' : (u.toSchwartz : ℝ → ℂ) = (u : ℝ → ℂ) := by
    funext x
    rfl
  rw [hfun, hfun', fourier_eq_integral_cexp, fourier_eq_integral_cexp]
  rw [integral_cexp_mul_translateCombo _ _ (u.smooth.continuous) u.hasCompactSupport]
  rw [translateSymbol_polarMultiplier, polarMultiplierSymbol_neg_I_mul]

/-- The Fourier transform of the wide bump is the dilated transform of the kernel. -/
theorem fourier_wideBumpSource (L : ℝ) (hL : 1 ≤ L) (ξ : ℝ) :
    𝓕 ((wideBumpSource L hL).toSchwartz : ℝ → ℂ) ξ = (L : ℂ) * 𝓕 phiTwoC (L * ξ) := by
  have hLpos : 0 < L := by linarith
  have hfun : ((wideBumpSource L hL).toSchwartz : ℝ → ℂ) = fun x => (phiN 2 (x / L) : ℂ) := by
    funext x
    rfl
  rw [hfun, Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hcomp : (fun v : ℝ => Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I) • (phiN 2 (v / L) : ℂ)) =
      fun v : ℝ => (fun y : ℝ => Complex.exp (((-2 * Real.pi * y * (L * ξ) : ℝ) : ℂ) * I) •
        phiTwoC y) (v / L) := by
    funext v
    simp only [phiTwoC]
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
    congr 2
    push_cast
    field_simp
  rw [hcomp]
  rw [Measure.integral_comp_div
    (fun y : ℝ => Complex.exp (((-2 * Real.pi * y * (L * ξ) : ℝ) : ℂ) * I) • phiTwoC y) L,
    abs_of_pos hLpos, Complex.real_smul]

/-! ## The spectral symbol on the real axis -/

/-- The real form of the spectral symbol. -/
def mSym (ξ : ℝ) : ℝ :=
  (Real.cos (2 * Real.pi * ξ) - 1) * (Real.cos (2 * Real.pi * ξ) - Real.cosh (1 / 2))

theorem polarMultiplierSpectral_one_ofReal (ξ : ℝ) :
    polarMultiplierSpectral 1 ((2 * Real.pi * ξ : ℝ) : ℂ) = (mSym ξ : ℂ) := by
  unfold polarMultiplierSpectral mSym
  simp only [Complex.ofReal_one, mul_one]
  push_cast
  ring

theorem abs_mSym_le (ξ : ℝ) : |mSym ξ| ≤ 2 * (1 + Real.cosh (1 / 2)) := by
  unfold mSym
  have hc1 := Real.neg_one_le_cos (2 * Real.pi * ξ)
  have hc2 := Real.cos_le_one (2 * Real.pi * ξ)
  have hcosh : 1 ≤ Real.cosh (1 / 2) := Real.one_le_cosh _
  rw [abs_mul]
  have h1 : |Real.cos (2 * Real.pi * ξ) - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h2 : |Real.cos (2 * Real.pi * ξ) - Real.cosh (1 / 2)| ≤ 1 + Real.cosh (1 / 2) := by
    rw [abs_le]; constructor <;> linarith
  calc |Real.cos (2 * Real.pi * ξ) - 1| * |Real.cos (2 * Real.pi * ξ) - Real.cosh (1 / 2)|
      ≤ 2 * (1 + Real.cosh (1 / 2)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)

/-- `1 − cos θ ≥ 2θ²/π²` for `|θ| ≤ π`. -/
theorem one_sub_cos_ge {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    2 * θ ^ (2 : ℕ) / Real.pi ^ (2 : ℕ) ≤ 1 - Real.cos θ := by
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ (2 : ℕ) := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    rw [h, Real.cos_sq']
    ring
  have hsin : 2 / Real.pi * (|θ| / 2) ≤ Real.sin (|θ| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  have hsq : Real.sin (θ / 2) ^ (2 : ℕ) = Real.sin (|θ| / 2) ^ (2 : ℕ) := by
    rcases le_or_gt 0 θ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, show -θ / 2 = -(θ / 2) by ring, Real.sin_neg, neg_sq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnn : 0 ≤ 2 / Real.pi * (|θ| / 2) := by positivity
  have hsq' : (2 / Real.pi * (|θ| / 2)) ^ (2 : ℕ) ≤ Real.sin (|θ| / 2) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hnn hsin 2
  rw [hcos, hsq]
  have h1 : 2 / Real.pi * (|θ| / 2) = |θ| / Real.pi := by field_simp
  have this : (2 / Real.pi * (|θ| / 2)) ^ (2 : ℕ) = θ ^ (2 : ℕ) / Real.pi ^ (2 : ℕ) := by
    rw [h1, div_pow, sq_abs]
  have h2 : 2 * θ ^ (2 : ℕ) / Real.pi ^ (2 : ℕ) = 2 * (θ ^ (2 : ℕ) / Real.pi ^ (2 : ℕ)) := by ring
  rw [h2]
  linarith

theorem mSym_sq_ge {ξ : ℝ} (hξ : |ξ| ≤ 1 / 2) :
    64 * (Real.cosh (1 / 2) - 1) ^ (2 : ℕ) * ξ ^ (4 : ℕ) ≤ mSym ξ ^ (2 : ℕ) := by
  unfold mSym
  have hθ : |2 * Real.pi * ξ| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_pos]
  have hcos := one_sub_cos_ge hθ
  have hcosh : 1 < Real.cosh (1 / 2) := Real.one_lt_cosh.mpr (by norm_num)
  have hc2 := Real.cos_le_one (2 * Real.pi * ξ)
  have hA : 8 * ξ ^ (2 : ℕ) ≤ 1 - Real.cos (2 * Real.pi * ξ) := by
    have : 2 * (2 * Real.pi * ξ) ^ (2 : ℕ) / Real.pi ^ (2 : ℕ) = 8 * ξ ^ (2 : ℕ) := by
      field_simp
      ring
    linarith
  have hB : Real.cosh (1 / 2) - 1 ≤ Real.cosh (1 / 2) - Real.cos (2 * Real.pi * ξ) := by linarith
  have hA0 : 0 ≤ 8 * ξ ^ (2 : ℕ) := by positivity
  have hB0 : 0 ≤ Real.cosh (1 / 2) - 1 := by linarith
  have hprod : (8 * ξ ^ (2 : ℕ)) * (Real.cosh (1 / 2) - 1) ≤
      (1 - Real.cos (2 * Real.pi * ξ)) * (Real.cosh (1 / 2) - Real.cos (2 * Real.pi * ξ)) :=
    mul_le_mul hA hB hB0 (by linarith)
  have hsq : ((Real.cos (2 * Real.pi * ξ) - 1) * (Real.cos (2 * Real.pi * ξ) - Real.cosh (1 / 2))) ^ (2 : ℕ) =
      ((1 - Real.cos (2 * Real.pi * ξ)) * (Real.cosh (1 / 2) - Real.cos (2 * Real.pi * ξ))) ^ (2 : ℕ) := by
    ring
  rw [hsq]
  have hlhs : 64 * (Real.cosh (1 / 2) - 1) ^ (2 : ℕ) * ξ ^ (4 : ℕ) = ((8 * ξ ^ (2 : ℕ)) * (Real.cosh (1 / 2) - 1)) ^ (2 : ℕ) := by
    ring
  rw [hlhs]
  exact pow_le_pow_left₀ (mul_nonneg hA0 hB0) hprod 2

/-! ## Bounds on the transform of the base kernel -/

/-- Decay constant of the base kernel transform. -/
def kappaTwo : ℝ := Real.exp (1 / 5) * (1081 / 780) ^ (3 : ℕ) / (2 * Real.pi) ^ (3 : ℕ)

theorem kappaTwo_pos : 0 < kappaTwo := by unfold kappaTwo; positivity

theorem norm_fourier_phiTwoC_le {η : ℝ} (hη : η ≠ 0) : ‖𝓕 phiTwoC η‖ ≤ kappaTwo / |η| ^ (3 : ℕ) := by
  rw [fourier_eq_paperFT]
  have hz : (-(2 * Real.pi * η) : ℂ) ≠ 0 := by
    have : (2 * Real.pi * η) ≠ 0 := by positivity
    exact_mod_cast neg_ne_zero.mpr this
  have him : |(-(2 * Real.pi * η) : ℂ).im| ≤ 1 / 2 := by
    simp [Complex.mul_im]
  have h := norm_paperFT_phiN_le 2 hz him
  have hnorm : ‖(-(2 * Real.pi * η) : ℂ)‖ = 2 * Real.pi * |η| := by
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    simp
  rw [hnorm] at h
  refine h.trans (le_of_eq ?_)
  unfold kappaTwo
  have hηpos : 0 < |η| := abs_pos.mpr hη
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hη0 : |η| ≠ 0 := hηpos.ne'
  rw [div_pow, mul_pow]
  field_simp
  try ring

/-- The near-origin radius of the base kernel transform. -/
def epsTwo : ℝ := 1 / (8 * Real.pi * sTwo)

theorem epsTwo_pos : 0 < epsTwo := by unfold epsTwo; have := sTwo_pos; positivity

theorem fourier_phiTwoC_zero : 𝓕 phiTwoC 0 = 1 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_smul]
  unfold phiTwoC
  rw [integral_complex_ofReal, integral_phiN]
  simp

theorem norm_fourier_phiTwoC_ge {η : ℝ} (hη : |η| ≤ epsTwo) : 1 / 2 ≤ ‖𝓕 phiTwoC η‖ := by
  have hint : Integrable phiTwoC := by
    unfold phiTwoC
    exact (integrable_phiN 2).ofReal
  have hexp' : Integrable (fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * v * η : ℝ) : ℂ) * I) * phiTwoC v) := by
    refine hint.bdd_mul (c := 1) ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with v
      rw [Complex.norm_exp_ofReal_mul_I]
  have hexp : Integrable (fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * v * η : ℝ) : ℂ) * I) • phiTwoC v) :=
    hexp'.congr (Filter.Eventually.of_forall fun v => (smul_eq_mul _ _).symm)
  have hexp0 : Integrable (fun v : ℝ =>
      Complex.exp (((-2 * Real.pi * v * (0 : ℝ) : ℝ) : ℂ) * I) • phiTwoC v) := by
    refine hint.congr (Filter.Eventually.of_forall fun v => ?_)
    show phiTwoC v = Complex.exp (((-2 * Real.pi * v * (0 : ℝ) : ℝ) : ℂ) * I) • phiTwoC v
    rw [show (-2 * Real.pi * v * (0 : ℝ) : ℝ) = 0 by ring, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul]
  have hF0 : ∫ v : ℝ, Complex.exp (((-2 * Real.pi * v * (0 : ℝ) : ℝ) : ℂ) * I) • phiTwoC v = 1 := by
    rw [← Real.fourier_real_eq_integral_exp_smul]
    exact fourier_phiTwoC_zero
  have hdiff : 𝓕 phiTwoC η - 1 =
      ∫ v : ℝ, phiTwoC v * (Complex.exp (((-2 * Real.pi * v * η : ℝ) : ℂ) * I) - 1) := by
    conv_lhs => rw [Real.fourier_real_eq_integral_exp_smul, ← hF0]
    rw [← integral_sub hexp hexp0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show Complex.exp (((-2 * Real.pi * v * η : ℝ) : ℂ) * I) • phiTwoC v -
      Complex.exp (((-2 * Real.pi * v * (0 : ℝ) : ℝ) : ℂ) * I) • phiTwoC v =
      phiTwoC v * (Complex.exp (((-2 * Real.pi * v * η : ℝ) : ℂ) * I) - 1)
    rw [show (-2 * Real.pi * v * (0 : ℝ) : ℝ) = 0 by ring, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul, smul_eq_mul, mul_sub, mul_one, mul_comm (phiTwoC v)]
  have hsupp := support_phiN_subset 2
  have hbound : ∀ v : ℝ, ‖phiTwoC v * (Complex.exp (((-2 * Real.pi * v * η : ℝ) : ℂ) * I) - 1)‖ ≤
      phiN 2 v * (4 * Real.pi * sTwo * |η|) := by
    intro v
    rw [norm_mul]
    unfold phiTwoC
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (phiN_nonneg 2 v)]
    by_cases hv : phiN 2 v = 0
    · rw [hv]; simp
    · have hvmem := hsupp (Function.mem_support.mpr hv)
      rw [mem_Icc] at hvmem
      have hvabs : |v| ≤ sTwo := by
        rw [abs_le]
        unfold sTwo
        exact ⟨by linarith [hvmem.1], hvmem.2⟩
      have hx : ‖(((-2 * Real.pi * v * η : ℝ) : ℂ) * I)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        have : |(-2 * Real.pi * v * η)| = 2 * Real.pi * |v| * |η| := by
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
        rw [this]
        have hs := sTwo_pos
        have hη' : |η| ≤ 1 / (8 * Real.pi * sTwo) := hη
        calc 2 * Real.pi * |v| * |η| ≤ 2 * Real.pi * sTwo * (1 / (8 * Real.pi * sTwo)) := by
              gcongr
          _ = 1 / 4 := by field_simp; ring
          _ ≤ 1 := by norm_num
      have h1 := Complex.norm_exp_sub_one_le hx
      have hx' : ‖(((-2 * Real.pi * v * η : ℝ) : ℂ) * I)‖ = 2 * Real.pi * |v| * |η| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
      rw [hx'] at h1
      have hs := sTwo_pos
      calc phiN 2 v * ‖Complex.exp (((-2 * Real.pi * v * η : ℝ) : ℂ) * I) - 1‖
          ≤ phiN 2 v * (2 * (2 * Real.pi * |v| * |η|)) :=
            mul_le_mul_of_nonneg_left h1 (phiN_nonneg 2 v)
        _ ≤ phiN 2 v * (4 * Real.pi * sTwo * |η|) := by
            apply mul_le_mul_of_nonneg_left _ (phiN_nonneg 2 v)
            calc 2 * (2 * Real.pi * |v| * |η|) = 4 * Real.pi * (|v| * |η|) := by ring
              _ ≤ 4 * Real.pi * (sTwo * |η|) := by gcongr
              _ = 4 * Real.pi * sTwo * |η| := by ring
  have hnormdiff : ‖𝓕 phiTwoC η - 1‖ ≤ 4 * Real.pi * sTwo * |η| := by
    rw [hdiff]
    have hg : Integrable (fun v : ℝ => phiN 2 v * (4 * Real.pi * sTwo * |η|)) :=
      (integrable_phiN 2).mul_const _
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)).trans ?_
    rw [integral_mul_const, integral_phiN, one_mul]
  have hsmall : 4 * Real.pi * sTwo * |η| ≤ 1 / 2 := by
    have hs := sTwo_pos
    have hη' : |η| ≤ 1 / (8 * Real.pi * sTwo) := hη
    calc 4 * Real.pi * sTwo * |η| ≤ 4 * Real.pi * sTwo * (1 / (8 * Real.pi * sTwo)) := by
          gcongr
      _ = 1 / 2 := by field_simp; ring
  have h1 : ‖(1 : ℂ)‖ = 1 := by simp
  have h3 := norm_sub_norm_le (1 : ℂ) (𝓕 phiTwoC η)
  have h2 := norm_sub_rev (𝓕 phiTwoC η) 1
  rw [h1] at h3
  linarith

/-! ## The archimedean phase rate near the origin and at infinity -/

theorem exists_phaseRate_negative_radius :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ Real.pi ∧
      ∀ t : ℝ, |t| ≤ t₀ → gammaHardyPhaseRate t ≤ gammaHardyPhaseRate 0 / 2 := by
  have hneg := gammaHardyPhaseRate_zero_neg
  have hcont : ContinuousAt gammaHardyPhaseRate 0 :=
    (differentiable_gammaHardyPhaseRate 0).continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.1 hcont (-gammaHardyPhaseRate 0 / 2)
    (by linarith)
  refine ⟨min (δ / 2) Real.pi, lt_min (by linarith) Real.pi_pos, min_le_right _ _, fun t ht => ?_⟩
  have hdist : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt ht (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h := hclose hdist
  rw [Real.dist_eq] at h
  have := (abs_lt.mp h).2
  linarith

theorem gammaHardyPhaseRate_le_linear (t : ℝ) : gammaHardyPhaseRate t ≤ 35 + |t| := by
  have heven : gammaHardyPhaseRate t = gammaHardyPhaseRate |t| := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, gammaHardyPhaseRate_neg]
  rw [heven]
  have hmono := strictMonoOn_gammaHardyPhaseRate
  by_cases hbig : 2 * Real.pi ≤ |t|
  · set r : ℝ := |t| / (2 * Real.pi) with hr
    have hr1 : 1 ≤ r := by
      rw [hr, le_div_iff₀ (by positivity)]
      linarith
    have hrpos : 0 < r := by linarith
    have h34 := gammaHardyPhaseRate_log_abs_le_thirtyFour hr1
    have hrt : 2 * Real.pi * r = |t| := by
      rw [hr]
      field_simp
    rw [hrt] at h34
    have hlog : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hrpos
    have hle : gammaHardyPhaseRate |t| ≤ Real.log r / 2 + 34 := by
      have := (abs_le.mp h34).2
      linarith
    have hrle : r ≤ |t| := by
      rw [hr, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three, abs_nonneg t]
    linarith
  · have hlt : |t| < 2 * Real.pi := lt_of_not_ge hbig
    have h1 : gammaHardyPhaseRate |t| ≤ gammaHardyPhaseRate (2 * Real.pi) := by
      rcases eq_or_lt_of_le (abs_nonneg t) with h0 | hpos
      · rw [← h0]
        exact (gammaHardyPhaseRate_zero_lt (by positivity : (2 * Real.pi) ≠ 0)).le
      · exact (hmono (Set.mem_Ici.mpr (abs_nonneg t)) (Set.mem_Ici.mpr (by positivity)) hlt).le
    have h34 := gammaHardyPhaseRate_log_abs_le_thirtyFour (le_refl (1 : ℝ))
    rw [mul_one, Real.log_one, zero_div, sub_zero] at h34
    have := (abs_le.mp h34).2
    linarith [abs_nonneg t]

end RHTower.WeilDeletion

end
