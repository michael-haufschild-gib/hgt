import GaloisForLFunctions.RHTower.CHMDStage15ZeroSideSummabilityAndSechHalfOriginPositivity
import GaloisForLFunctions.RHTower.FiniteOffLineConverse
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity

/-!
# CHMD: Growth–Positivity Collapse of the Causal Wave and the Two-Point Criterion

This module continues the **Causal Hyperbolic–Modular Duality (CHMD)**
formalization in `RHTower`. Stage 15 gave the unconditional zero-side series of the causal wave
$$\varphi_\Lambda(y) := \operatorname{cosineShiftFn}\ \Lambda\ \operatorname{sechHalf}\ y
  = \sum_{\rho} m_\rho \operatorname{Re}\bigl(\cos(y\,\rho_\rho)\,w_\rho\bigr),
  \qquad \rho_\rho := \sqrt{\gamma_\rho^2 + 2},\quad w_\rho := \operatorname{sech}^2(\gamma_\rho/2),$$
and Stage 4 proved that `RiemannHypothesis` is equivalent to the Bochner positive definiteness of
$\varphi_\Lambda$, i.e. to the nonnegativity of **all** finite Toeplitz forms
$\sum_{i,j} c_i c_j \varphi_\Lambda(t_j - t_i)$. The frontier obstacle was to produce the Bochner
measure unconditionally.

**This stage collapses the whole Toeplitz hierarchy to a one-sided growth statement.** Every
nontrivial zero $\rho$ has Klein–Gordon frequency $\rho_\rho = \sqrt{\gamma_\rho^2+2}$ with
$\operatorname{Re}\rho_\rho > 1$ and $|\operatorname{Im}\rho_\rho| < 1/2$; an off-line zero has
$\operatorname{Im}\rho_\rho \ne 0$ and contributes an exponentially growing hyperbolic mode. The
Laplace transform of $\varphi_\Lambda$ on $\operatorname{Re} s > 1/2$ is the **Klein–Gordon pole
series**
$$G(s) = \sum_\rho m_\rho\,\frac{w_\rho}{2}\Bigl(\frac{1}{s - i\rho_\rho} + \frac{1}{s + i\rho_\rho}\Bigr),$$
analytic off the locally finite pole set $\{\pm i\rho_\rho\}$ and blowing up like $A/d$ at every
pole. Landau's theorem (corpus `exists_differentiable_extension_of_le_exp`) continues the Laplace
transform of a one-sidedly bounded function to the half-plane $\operatorname{Re} s > a$, and a
tilted-ray identity-theorem argument shows this is incompatible with any pole there. Hence:

1. **Exact growth law** (`abs_im_kgFreq_le_of_chmdWave_le_exp`, `chmdWave_growth_law`): for every
   $0 \le a < 1/2$,
   $$\exists M,\ \varphi_\Lambda(u) \le M e^{au}\ (u \ge 0)
     \iff \forall \rho,\ |\operatorname{Im}\rho_\rho| \le a
     \iff \exists M,\ -M e^{au} \le \varphi_\Lambda(u)\ (u \ge 0)
     \iff \exists K,\ |\varphi_\Lambda(u)| \le K e^{a|u|}\ (u \in \mathbb{R}).$$
2. **Growth–positivity collapse at $a = 0$**
   (`riemannHypothesis_iff_chmdWave_bddAbove`, `riemannHypothesis_iff_chmdWave_bddBelow`,
   `riemannHypothesis_iff_forall_chmdWave_le_zero_value`,
   `riemannHypothesis_iff_forall_abs_chmdWave_le_zero_value`,
   `riemannHypothesis_iff_forall_twoPointDiff_nonneg`): `RiemannHypothesis` holds iff
   $\varphi_\Lambda$ is bounded above on $[0,\infty)$, iff bounded below, iff
   $\varphi_\Lambda(y) \le \varphi_\Lambda(0)$ for all $y$, iff all two-point difference packets of
   Stage 13 are nonnegative. Positivity of the whole Toeplitz cone is therefore **automatic from a
   one-sided bound** on the single causal wave.
3. **Positive-real criterion** (`riemannHypothesis_iff_kgPoleSeries_positiveReal`):
   `RiemannHypothesis` holds iff the Klein–Gordon pole series has nonnegative real part on
   $\operatorname{Re} s > 0$.

No hypothesis is used anywhere: the Laplace identity rests only on the Stage 15 series and the
Zeta23 zero-sum bound `WeilEF.zero_sum_inv_sq`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDGrowthCollapse

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage1 RHTower.CHMDStage3 RHTower.CHMDStage4
open RHTower.CHMDStage11 RHTower.CHMDStage12 RHTower.CHMDStage13 RHTower.CHMDStage14
open RHTower.CHMDStage15

/-! ## Section 1: Klein–Gordon spectral data at the nontrivial zeros -/

/-- The Klein–Gordon frequency `√(γ_ρ² + 2)` of a nontrivial zero `ρ`. -/
def kgFreq (ρ : zetaZeroConfig.carrier) : ℂ := rhoC (Zeta23.gammaOf (ρ : ℂ))

/-- The hyperbolic-secant weight `specSq sechHalf (γ_ρ) = sech²(γ_ρ / 2)` of a nontrivial zero. -/
def kgWeight (ρ : zetaZeroConfig.carrier) : ℂ := specSq sechHalf (Zeta23.gammaOf (ρ : ℂ))

theorem abs_im_gammaOf_lt (ρ : zetaZeroConfig.carrier) :
    |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  exact WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩

theorem abs_im_kgFreq_lt (ρ : zetaZeroConfig.carrier) : |(kgFreq ρ).im| < 1 / 2 :=
  (abs_im_rhoC_le _).trans_lt (abs_im_gammaOf_lt ρ)

theorem kgFreq_sq (ρ : zetaZeroConfig.carrier) :
    kgFreq ρ ^ 2 = Zeta23.gammaOf (ρ : ℂ) ^ 2 + 2 := rhoC_sq _

/-- The principal square root has positive real part when the radicand has positive real part. -/
theorem re_rhoC_pos {z : ℂ} (hz : 0 < (z ^ 2 + 2).re) : 0 < (rhoC z).re := by
  have hne : z ^ 2 + 2 ≠ 0 := fun h => by rw [h] at hz; simp at hz
  unfold rhoC
  rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have harg : |(z ^ 2 + 2).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have h2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have him : (Complex.log (z ^ 2 + 2) * (1 / 2 : ℂ)).im = (z ^ 2 + 2).arg / 2 := by
    rw [h2, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.log_im]; ring
  rw [him]
  apply Real.cos_pos_of_mem_Ioo
  obtain ⟨h1, h2'⟩ := abs_lt.mp harg
  constructor <;> linarith [Real.pi_pos]

theorem re_sq_add_two (z : ℂ) : (z ^ 2 + 2).re = z.re ^ 2 - z.im ^ 2 + 2 := by
  simp [sq]

theorem im_sq_gammaOf_lt (ρ : zetaZeroConfig.carrier) :
    (Zeta23.gammaOf (ρ : ℂ)).im ^ 2 < 1 / 4 := by
  have h := abs_im_gammaOf_lt ρ
  have := sq_abs (Zeta23.gammaOf (ρ : ℂ)).im
  nlinarith [abs_nonneg (Zeta23.gammaOf (ρ : ℂ)).im]

theorem re_kgFreq_pos (ρ : zetaZeroConfig.carrier) : 0 < (kgFreq ρ).re := by
  apply re_rhoC_pos
  rw [re_sq_add_two]
  nlinarith [sq_nonneg (Zeta23.gammaOf (ρ : ℂ)).re, im_sq_gammaOf_lt ρ]

/-- Every Klein–Gordon frequency has real part `> 1` (in fact `≥ √7/2`). -/
theorem one_lt_re_kgFreq (ρ : zetaZeroConfig.carrier) : 1 < (kgFreq ρ).re := by
  have hpos := re_kgFreq_pos ρ
  have hsq := kgFreq_sq ρ
  have h1 : (kgFreq ρ ^ 2).re = (kgFreq ρ).re ^ 2 - (kgFreq ρ).im ^ 2 := by simp [sq]
  rw [hsq, re_sq_add_two] at h1
  have him := im_sq_gammaOf_lt ρ
  nlinarith [sq_nonneg (Zeta23.gammaOf (ρ : ℂ)).re, sq_nonneg (kgFreq ρ).im]

theorem gammaOf_reflect (ρ : ℂ) :
    Zeta23.gammaOf (Zeta23.reflect ρ) = conj (Zeta23.gammaOf ρ) := by
  unfold Zeta23.gammaOf Zeta23.reflect
  apply Complex.ext <;> simp [Complex.div_I]
  ring

theorem reflect_reflect (ρ : ℂ) : Zeta23.reflect (Zeta23.reflect ρ) = ρ := by
  unfold Zeta23.reflect; simp

/-- The reflection `ρ ↦ 1 − ρ̄` on the zero carrier. -/
def reflectZero (ρ : zetaZeroConfig.carrier) : zetaZeroConfig.carrier :=
  ⟨Zeta23.reflect (ρ : ℂ), zetaZeroConfig.reflect_mem _ ρ.2⟩

/-- The reflection as an involutive equivalence of the zero carrier. -/
def reflectEquiv : zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier where
  toFun := reflectZero
  invFun := reflectZero
  left_inv ρ := Subtype.ext (reflect_reflect (ρ : ℂ))
  right_inv ρ := Subtype.ext (reflect_reflect (ρ : ℂ))

theorem mult_reflectZero (ρ : zetaZeroConfig.carrier) :
    zetaZeroConfig.mult (reflectZero ρ) = zetaZeroConfig.mult ρ :=
  zetaZeroConfig.mult_reflect _ ρ.2

theorem kgFreq_reflectZero (ρ : zetaZeroConfig.carrier) :
    kgFreq (reflectZero ρ) = conj (kgFreq ρ) := by
  unfold kgFreq reflectZero
  simp only
  rw [gammaOf_reflect, rhoC_conj (abs_im_lt_sqrt_two (by linarith [abs_im_gammaOf_lt ρ]))]

theorem specSq_conj (Φ : ℂ → ℂ) (z : ℂ) : specSq Φ (conj z) = conj (specSq Φ z) := by
  unfold specSq
  rw [Complex.conj_conj, map_mul, Complex.conj_conj, mul_comm]

theorem kgWeight_reflectZero (ρ : zetaZeroConfig.carrier) :
    kgWeight (reflectZero ρ) = conj (kgWeight ρ) := by
  unfold kgWeight reflectZero
  simp only
  rw [gammaOf_reflect, specSq_conj]

/-- Zeros with the same Klein–Gordon frequency have the same weight. -/
theorem kgWeight_eq_of_kgFreq_eq {ρ σ : zetaZeroConfig.carrier} (h : kgFreq ρ = kgFreq σ) :
    kgWeight ρ = kgWeight σ := by
  have hsq : Zeta23.gammaOf (ρ : ℂ) ^ 2 = Zeta23.gammaOf (σ : ℂ) ^ 2 := by
    have h2 := congrArg (fun w : ℂ => w ^ 2) h
    simp only [kgFreq_sq] at h2
    linear_combination h2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · unfold kgWeight; rw [h1]
  · unfold kgWeight; rw [h1, specSq_neg_of_even evenStrip_sechHalf.even]

theorem re_kgWeight_pos (ρ : zetaZeroConfig.carrier) : 0 < (kgWeight ρ).re :=
  re_specSq_sechHalf_gammaOf_pos ρ

theorem kgWeight_ne_zero (ρ : zetaZeroConfig.carrier) : kgWeight ρ ≠ 0 := fun h => by
  have := re_kgWeight_pos ρ; rw [h] at this; simp at this

theorem norm_kgWeight_pos (ρ : zetaZeroConfig.carrier) : 0 < ‖kgWeight ρ‖ :=
  norm_pos_iff.mpr (kgWeight_ne_zero ρ)

/-- Norm-summability of the weighted sech² weights over the zeros. -/
theorem summable_mult_mul_norm_kgWeight :
    Summable fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ := by
  have h := summable_zeroSide_of_goodDensity (goodDensity_specSq evenStrip_sechHalf)
  have h2 := summable_norm_iff.mpr h
  refine h2.congr fun _ => ?_
  rw [norm_mul, Complex.norm_natCast]
  rfl

/-- The total weighted sech² mass `Σ m_ρ ‖w_ρ‖`. -/
def kgMass : ℝ := ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖

theorem kgMass_nonneg : 0 ≤ kgMass :=
  tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

/-! ## Section 2: The causal wave as a real cosine series with complex frequencies -/

/-- The CHMD causal wave `φ_Λ(y) = cosineShiftFn Λ sechHalf y`. -/
def chmdWave (y : ℝ) : ℝ :=
  cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y

theorem chmdWave_neg (y : ℝ) : chmdWave (-y) = chmdWave y := cosineShiftFn_neg _ _ _

theorem continuous_chmdWave : Continuous chmdWave :=
  continuous_cosineShiftFn abs_vonMangoldt_le_sqrt_mul_one_add_log evenStrip_sechHalf

theorem chmdWave_eq_tsum_re (y : ℝ) :
    chmdWave y = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re := by
  unfold chmdWave
  rw [cosineShiftFn_vonMangoldt_eq_tsum_re evenStrip_sechHalf]
  rfl

theorem summable_cosTerm (y : ℝ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ) := by
  refine (summable_zeroSide_of_goodDensity (goodDensity_cosShift y evenStrip_sechHalf)).congr
    fun ρ => ?_
  simp only [kgFreq, kgWeight, rhoCosShift]

theorem cosTerm_reflectZero (y : ℝ) (ρ : zetaZeroConfig.carrier) :
    Complex.cos (y * kgFreq (reflectZero ρ)) * kgWeight (reflectZero ρ) =
      conj (Complex.cos (y * kgFreq ρ) * kgWeight ρ) := by
  rw [kgFreq_reflectZero, kgWeight_reflectZero, map_mul, ← Complex.cos_conj, map_mul,
    Complex.conj_ofReal]

/-- The imaginary parts cancel under the reflection involution. -/
theorem tsum_im_cosTerm (y : ℝ) :
    ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).im = 0 := by
  set f : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).im with hf
  have hrefl : ∀ ρ, f (reflectEquiv ρ) = -f ρ := by
    intro ρ
    simp only [hf, reflectEquiv, Equiv.coe_fn_mk, mult_reflectZero, cosTerm_reflectZero,
      Complex.conj_im]
    ring
  have h1 : ∑' ρ, f ρ = ∑' ρ, f (reflectEquiv ρ) := (reflectEquiv.tsum_eq f).symm
  have h2 : ∑' ρ, f (reflectEquiv ρ) = -∑' ρ, f ρ := by
    simp_rw [hrefl]; exact tsum_neg
  have : ∑' ρ, f ρ = -∑' ρ, f ρ := h1.trans h2
  linarith

/-- **The causal wave is the real cosine series with complex frequencies**:
`(φ_Λ(y) : ℂ) = Σ' ρ, m_ρ cos(y ρ_ρ) w_ρ`. -/
theorem ofReal_chmdWave (y : ℝ) :
    (chmdWave y : ℂ) = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re, chmdWave_eq_tsum_re, Complex.re_tsum (summable_cosTerm y)]
    exact tsum_congr fun ρ => by simp [Complex.mul_re]
  · rw [Complex.ofReal_im, Complex.im_tsum (summable_cosTerm y), ← tsum_im_cosTerm y]
    exact tsum_congr fun ρ => by simp [Complex.mul_im]

theorem norm_cos_mul_kgFreq_le (y : ℝ) (ρ : zetaZeroConfig.carrier) :
    ‖Complex.cos (y * kgFreq ρ)‖ ≤ Real.exp (|y| * |(kgFreq ρ).im|) := by
  refine (norm_ccos_le_exp_abs_im _).trans (Real.exp_le_exp.mpr ?_)
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]

/-- **Two-sided growth from a frequency displacement bound**: if every zero has
`|Im ρ_ρ| ≤ a`, then `|φ_Λ(y)| ≤ kgMass · e^{a|y|}`. -/
theorem abs_chmdWave_le_of_forall_abs_im_kgFreq_le {a : ℝ}
    (ha : ∀ ρ : zetaZeroConfig.carrier, |(kgFreq ρ).im| ≤ a) (y : ℝ) :
    |chmdWave y| ≤ kgMass * Real.exp (a * |y|) := by
  have h : |chmdWave y| = ‖(chmdWave y : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [h, ofReal_chmdWave]
  have hb : ∀ ρ : zetaZeroConfig.carrier,
      ‖(zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ)‖ ≤
        (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * Real.exp (a * |y|) := by
    intro ρ
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h1 := norm_cos_mul_kgFreq_le y ρ
    have h2 : Real.exp (|y| * |(kgFreq ρ).im|) ≤ Real.exp (a * |y|) := by
      apply Real.exp_le_exp.mpr
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (ha ρ) (abs_nonneg y)
    calc (zetaZeroConfig.mult ρ : ℝ) * (‖Complex.cos (y * kgFreq ρ)‖ * ‖kgWeight ρ‖)
        ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (a * |y|) * ‖kgWeight ρ‖) := by
          gcongr
          exact h1.trans h2
      _ = (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * Real.exp (a * |y|) := by ring
  refine (tsum_of_norm_bounded
    (summable_mult_mul_norm_kgWeight.mul_right (Real.exp (a * |y|))).hasSum hb).trans ?_
  rw [tsum_mul_right]
  unfold kgMass
  exact le_rfl

/-- **Unconditional growth bound**: `|φ_Λ(y)| ≤ kgMass · e^{|y|/2}`. -/
theorem abs_chmdWave_le (y : ℝ) : |chmdWave y| ≤ kgMass * Real.exp (|y| / 2) := by
  have h := abs_chmdWave_le_of_forall_abs_im_kgFreq_le (a := 1 / 2)
    (fun ρ => (abs_im_kgFreq_lt ρ).le) y
  rwa [show (1 / 2 : ℝ) * |y| = |y| / 2 by ring] at h

/-! ## Section 3: The Klein–Gordon pole series is the Laplace transform of the causal wave -/

/-- One Laplace term `m_ρ (w_ρ/2) (1/(s − iρ_ρ) + 1/(s + iρ_ρ))`. -/
def kgTerm (s : ℂ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2) *
    (1 / (s - I * kgFreq ρ) + 1 / (s + I * kgFreq ρ))

/-- The Klein–Gordon pole series `G(s) = Σ' ρ, m_ρ (w_ρ/2)(1/(s − iρ_ρ) + 1/(s + iρ_ρ))`. -/
def kgPoleSeries (s : ℂ) : ℂ := ∑' ρ : zetaZeroConfig.carrier, kgTerm s ρ

theorem re_sub_I_mul_kgFreq_pos {s : ℂ} (hs : 1 / 2 < s.re) (ρ : zetaZeroConfig.carrier) :
    0 < (s - I * kgFreq ρ).re := by
  rw [Complex.sub_re, Complex.I_mul_re]
  have := abs_lt.mp (abs_im_kgFreq_lt ρ)
  linarith [this.1, this.2]

theorem re_add_I_mul_kgFreq_pos {s : ℂ} (hs : 1 / 2 < s.re) (ρ : zetaZeroConfig.carrier) :
    0 < (s + I * kgFreq ρ).re := by
  rw [Complex.add_re, Complex.I_mul_re]
  have := abs_lt.mp (abs_im_kgFreq_lt ρ)
  linarith [this.1, this.2]

/-- The cosine Laplace integrand as a sum of two exponentials. -/
theorem cosTerm_mul_cexp_eq (s : ℂ) (ρ : zetaZeroConfig.carrier) (u : ℝ) :
    (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (u * kgFreq ρ) * kgWeight ρ) *
        Complex.exp (-s * u) =
      (zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2) * Complex.exp (-(s - I * kgFreq ρ) * u) +
        (zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2) * Complex.exp (-(s + I * kgFreq ρ) * u) := by
  have e1 : Complex.exp (-(s - I * kgFreq ρ) * u) =
      Complex.exp (u * kgFreq ρ * I) * Complex.exp (-s * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-(s + I * kgFreq ρ) * u) =
      Complex.exp (-(u * kgFreq ρ) * I) * Complex.exp (-s * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2, Complex.cos]
  ring

theorem integrableOn_cosTerm_mul_cexp {s : ℂ} (hs : 1 / 2 < s.re) (ρ : zetaZeroConfig.carrier) :
    IntegrableOn (fun u : ℝ =>
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (u * kgFreq ρ) * kgWeight ρ) *
        Complex.exp (-s * u)) (Ioi (0 : ℝ)) := by
  have h1 := (integrableOn_cexp_neg_mul_ofReal_Ioi (re_sub_I_mul_kgFreq_pos hs ρ)).const_mul
    ((zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2))
  have h2 := (integrableOn_cexp_neg_mul_ofReal_Ioi (re_add_I_mul_kgFreq_pos hs ρ)).const_mul
    ((zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2))
  exact IntegrableOn.congr_fun (h1.add h2) (fun u _ => (cosTerm_mul_cexp_eq s ρ u).symm)
    measurableSet_Ioi

/-- **Laplace transform of one cosine mode**: `∫₀^∞ m cos(uρ) w e^{−su} du = kgTerm s ρ`. -/
theorem integral_cosTerm_mul_cexp {s : ℂ} (hs : 1 / 2 < s.re) (ρ : zetaZeroConfig.carrier) :
    ∫ u in Ioi (0 : ℝ),
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (u * kgFreq ρ) * kgWeight ρ) *
        Complex.exp (-s * u) = kgTerm s ρ := by
  simp_rw [cosTerm_mul_cexp_eq s ρ]
  rw [integral_add, integral_const_mul, integral_const_mul,
    integral_cexp_neg_mul_Ioi (re_sub_I_mul_kgFreq_pos hs ρ),
    integral_cexp_neg_mul_Ioi (re_add_I_mul_kgFreq_pos hs ρ)]
  · unfold kgTerm; ring
  · exact (integrableOn_cexp_neg_mul_ofReal_Ioi (re_sub_I_mul_kgFreq_pos hs ρ)).const_mul _
  · exact (integrableOn_cexp_neg_mul_ofReal_Ioi (re_add_I_mul_kgFreq_pos hs ρ)).const_mul _

theorem norm_cosTerm_mul_cexp_le {s : ℂ} (ρ : zetaZeroConfig.carrier) {u : ℝ} (hu : 0 ≤ u) :
    ‖(zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (u * kgFreq ρ) * kgWeight ρ) *
        Complex.exp (-s * u)‖ ≤
      (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * Real.exp (-((s.re - 1 / 2) * u)) := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp]
  have hre : (-s * (u : ℂ)).re = -(s.re * u) := by simp [Complex.mul_re]
  rw [hre]
  have h1 := norm_cos_mul_kgFreq_le u ρ
  have h2 : Real.exp (|u| * |(kgFreq ρ).im|) ≤ Real.exp (u / 2) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hu]
    have := (abs_im_kgFreq_lt ρ).le
    nlinarith
  have h3 : Real.exp (u / 2) * Real.exp (-(s.re * u)) = Real.exp (-((s.re - 1 / 2) * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (zetaZeroConfig.mult ρ : ℝ) * (‖Complex.cos (u * kgFreq ρ)‖ * ‖kgWeight ρ‖) *
        Real.exp (-(s.re * u))
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (u / 2) * ‖kgWeight ρ‖) *
        Real.exp (-(s.re * u)) := by
        gcongr
        exact h1.trans h2
    _ = (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ *
        (Real.exp (u / 2) * Real.exp (-(s.re * u))) := by ring
    _ = _ := by rw [h3]

theorem integral_norm_cosTerm_mul_cexp_le {s : ℂ} (hs : 1 / 2 < s.re)
    (ρ : zetaZeroConfig.carrier) :
    ∫ u in Ioi (0 : ℝ),
      ‖(zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (u * kgFreq ρ) * kgWeight ρ) *
        Complex.exp (-s * u)‖ ≤
      (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / (s.re - 1 / 2)) := by
  have hb : 0 < s.re - 1 / 2 := by linarith
  have hint : IntegrableOn (fun u : ℝ =>
      (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * Real.exp (-((s.re - 1 / 2) * u)))
      (Ioi (0 : ℝ)) := by
    have := (exp_neg_integrableOn_Ioi 0 hb).const_mul
      ((zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖)
    exact IntegrableOn.congr_fun this (fun u _ => by simp only [neg_mul]) measurableSet_Ioi
  calc ∫ u in Ioi (0 : ℝ),
        ‖(zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (u * kgFreq ρ) * kgWeight ρ) *
          Complex.exp (-s * u)‖
      ≤ ∫ u in Ioi (0 : ℝ),
          (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * Real.exp (-((s.re - 1 / 2) * u)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) hint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact norm_cosTerm_mul_cexp_le ρ (le_of_lt hu)
    _ = (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / (s.re - 1 / 2)) := by
        rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero hb]

/-- **The Klein–Gordon pole series is the Laplace transform of the causal wave** on
`Re s > 1/2`: `∫₀^∞ φ_Λ(u) e^{−su} du = kgPoleSeries s`. -/
theorem integral_chmdWave_mul_cexp {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (chmdWave u : ℂ) * Complex.exp (-s * u) = kgPoleSeries s := by
  haveI : Countable zetaZeroConfig.carrier := WeilConditional.countable_carrier.to_subtype
  have hpt : ∀ u : ℝ, (chmdWave u : ℂ) * Complex.exp (-s * u) =
      ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (u * kgFreq ρ) * kgWeight ρ) *
          Complex.exp (-s * u) := by
    intro u; rw [ofReal_chmdWave, tsum_mul_right]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm (fun ρ => integrableOn_cosTerm_mul_cexp hs ρ)]
  · exact tsum_congr fun ρ => integral_cosTerm_mul_cexp hs ρ
  · refine Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => integral_norm_cosTerm_mul_cexp_le hs ρ)
      (summable_mult_mul_norm_kgWeight.mul_right _)

/-! ## Section 4: The pole set is locally finite and the pole series is analytic off it -/

/-- The pole set `{± i ρ_ρ}` of the Klein–Gordon pole series. -/
def kgPoleSet : Set ℂ :=
  {z | ∃ ρ : zetaZeroConfig.carrier, z = I * kgFreq ρ ∨ z = -(I * kgFreq ρ)}

/-- Real points are never poles: every pole has imaginary part `± Re ρ_ρ ≠ 0`. -/
theorem ofReal_notMem_kgPoleSet (t : ℝ) : (t : ℂ) ∉ kgPoleSet := by
  rintro ⟨ρ, h | h⟩
  · have := congrArg Complex.im h
    rw [Complex.ofReal_im, Complex.I_mul_im] at this
    linarith [re_kgFreq_pos ρ]
  · have := congrArg Complex.im h
    rw [Complex.ofReal_im, Complex.neg_im, Complex.I_mul_im] at this
    linarith [re_kgFreq_pos ρ]

/-- The frequency controls the ordinate: `|Im ρ| ≤ ‖ρ_ρ‖ + 2`. -/
theorem abs_im_le_norm_kgFreq_add_two (ρ : zetaZeroConfig.carrier) :
    |(ρ : ℂ).im| ≤ ‖kgFreq ρ‖ + 2 := by
  have h1 : ‖kgFreq ρ‖ ^ 2 = ‖Zeta23.gammaOf (ρ : ℂ) ^ 2 + 2‖ := by
    rw [← norm_pow, kgFreq_sq]
  have h2 : ‖Zeta23.gammaOf (ρ : ℂ)‖ ^ 2 - 2 ≤ ‖Zeta23.gammaOf (ρ : ℂ) ^ 2 + 2‖ := by
    have := norm_sub_norm_le (Zeta23.gammaOf (ρ : ℂ) ^ 2) (-2 : ℂ)
    have e : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [sub_neg_eq_add, e, norm_pow] at this
    exact this
  have h3 : |(ρ : ℂ).im| ≤ ‖Zeta23.gammaOf (ρ : ℂ)‖ := by
    rw [← WeilEF.gammaOf_re]; exact Complex.abs_re_le_norm _
  have h5 : (ρ : ℂ).im ^ 2 ≤ (‖kgFreq ρ‖ + 2) ^ 2 := by
    have h6 : |(ρ : ℂ).im| * |(ρ : ℂ).im| ≤
        ‖Zeta23.gammaOf (ρ : ℂ)‖ * ‖Zeta23.gammaOf (ρ : ℂ)‖ :=
      mul_self_le_mul_self (abs_nonneg _) h3
    rw [← pow_two, ← pow_two, sq_abs] at h6
    nlinarith [norm_nonneg (kgFreq ρ)]
  exact abs_le.mpr (abs_le_of_sq_le_sq' h5 (by positivity))

/-- Only finitely many zeros have frequency of norm at most `R`. -/
theorem finite_kgFreq_norm_le (R : ℝ) :
    {ρ : zetaZeroConfig.carrier | ‖kgFreq ρ‖ ≤ R}.Finite := by
  have hfin := zetaZeroConfig.finite_window (-(R + 3)) (R + 2)
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  intro ρ hρ
  simp only [mem_setOf_eq] at hρ
  have h2 := abs_le.mp (abs_im_le_norm_kgFreq_add_two ρ)
  rw [mem_preimage, mem_inter_iff, mem_setOf_eq]
  exact ⟨ρ.2, by linarith [h2.1], by linarith [h2.2]⟩

/-- Around a point off the pole set, all pole distances are bounded below by a common radius. -/
theorem exists_ball_kgFreq_dist {z₀ : ℂ} (hz₀ : z₀ ∉ kgPoleSet) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ z ∈ Metric.ball z₀ r, ∀ ρ : zetaZeroConfig.carrier,
      r ≤ ‖z - I * kgFreq ρ‖ ∧ r ≤ ‖z + I * kgFreq ρ‖ := by
  set S := {ρ : zetaZeroConfig.carrier | ‖kgFreq ρ‖ ≤ ‖z₀‖ + 2} with hS
  have hSfin : S.Finite := finite_kgFreq_norm_le _
  set P : Set ℂ := (fun ρ => I * kgFreq ρ) '' S ∪ (fun ρ => -(I * kgFreq ρ)) '' S with hP
  have hPfin : P.Finite := (hSfin.image _).union (hSfin.image _)
  have hz₀P : z₀ ∉ P := by
    rintro (⟨ρ, _, h⟩ | ⟨ρ, _, h⟩)
    · exact hz₀ ⟨ρ, Or.inl h.symm⟩
    · exact hz₀ ⟨ρ, Or.inr h.symm⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hPfin.isClosed.isOpen_compl z₀ hz₀P
  refine ⟨min (δ / 2) 1, by positivity, min_le_right _ _, fun z hz ρ => ?_⟩
  have hzz₀ : ‖z - z₀‖ < min (δ / 2) 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have hr1 : min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
  have hr2 : min (δ / 2) 1 ≤ 1 := min_le_right _ _
  by_cases hρ : ρ ∈ S
  · have hp1 : I * kgFreq ρ ∉ Metric.ball z₀ δ := fun h => hball h (Or.inl ⟨ρ, hρ, rfl⟩)
    have hp2 : -(I * kgFreq ρ) ∉ Metric.ball z₀ δ := fun h => hball h (Or.inr ⟨ρ, hρ, rfl⟩)
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hp1 hp2
    constructor
    · have h1 := norm_sub_norm_le (z₀ - I * kgFreq ρ) (z₀ - z)
      rw [show z₀ - I * kgFreq ρ - (z₀ - z) = z - I * kgFreq ρ by ring, norm_sub_rev z₀ z,
        norm_sub_rev z₀] at h1
      linarith
    · have h1 := norm_sub_norm_le (z₀ - -(I * kgFreq ρ)) (z₀ - z)
      rw [show z₀ - -(I * kgFreq ρ) - (z₀ - z) = z + I * kgFreq ρ by ring, norm_sub_rev z₀ z,
        norm_sub_rev z₀] at h1
      linarith
  · have hbig : ‖z₀‖ + 2 < ‖kgFreq ρ‖ := not_le.mp hρ
    have hz' : ‖z‖ < ‖z₀‖ + 1 := by
      have := norm_sub_norm_le z z₀
      linarith
    constructor
    · have h1 := norm_sub_norm_le (I * kgFreq ρ) z
      rw [norm_mul, Complex.norm_I, one_mul, norm_sub_rev] at h1
      linarith
    · have h1 := norm_sub_norm_le (I * kgFreq ρ) (-z)
      rw [norm_mul, Complex.norm_I, one_mul, norm_neg, sub_neg_eq_add, add_comm] at h1
      linarith

/-- Norm bound for one Laplace term away from the poles. -/
theorem norm_term_div_le (m : ℕ) (w z : ℂ) {c : ℝ} (hc : 0 < c) (hz : c ≤ ‖z‖) :
    ‖(m : ℂ) * (w / 2) * (1 / z)‖ ≤ (m : ℝ) * ‖w‖ * (1 / (2 * c)) := by
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_div, norm_div, norm_one]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have : 1 / ‖z‖ ≤ 1 / c := one_div_le_one_div_of_le hc hz
  calc (m : ℝ) * (‖w‖ / 2) * (1 / ‖z‖) ≤ (m : ℝ) * (‖w‖ / 2) * (1 / c) := by gcongr
    _ = (m : ℝ) * ‖w‖ * (1 / (2 * c)) := by ring

theorem norm_kgTerm_le {r : ℝ} (hr : 0 < r) {z : ℂ} (ρ : zetaZeroConfig.carrier)
    (h1 : r ≤ ‖z - I * kgFreq ρ‖) (h2 : r ≤ ‖z + I * kgFreq ρ‖) :
    ‖kgTerm z ρ‖ ≤ (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ / r := by
  unfold kgTerm
  rw [mul_add]
  refine (norm_add_le _ _).trans ?_
  have ha := norm_term_div_le (zetaZeroConfig.mult ρ) (kgWeight ρ) _ hr h1
  have hb := norm_term_div_le (zetaZeroConfig.mult ρ) (kgWeight ρ) _ hr h2
  calc _ ≤ (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / (2 * r)) +
        (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / (2 * r)) := add_le_add ha hb
    _ = (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ / r := by
        field_simp
        ring

theorem differentiableAt_kgTerm {z : ℂ} (ρ : zetaZeroConfig.carrier)
    (h1 : z - I * kgFreq ρ ≠ 0) (h2 : z + I * kgFreq ρ ≠ 0) :
    DifferentiableAt ℂ (fun w => kgTerm w ρ) z := by
  unfold kgTerm
  refine (differentiableAt_const _).mul (DifferentiableAt.add ?_ ?_)
  · exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) h1
  · exact (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) h2

theorem differentiableOn_kgPoleSeries_ball {z₀ : ℂ} (hz₀ : z₀ ∉ kgPoleSet) :
    ∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ kgPoleSeries (Metric.ball z₀ r) := by
  obtain ⟨r, hr, -, hball⟩ := exists_ball_kgFreq_dist hz₀
  refine ⟨r, hr, ?_⟩
  have hu : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ / r :=
    summable_mult_mul_norm_kgWeight.div_const r
  unfold kgPoleSeries
  refine differentiableOn_tsum_of_summable_norm hu (fun ρ => ?_) Metric.isOpen_ball
    (fun ρ z hz => norm_kgTerm_le hr ρ (hball z hz ρ).1 (hball z hz ρ).2)
  intro z hz
  have h := hball z hz ρ
  have h1 : z - I * kgFreq ρ ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith [h.1]
  have h2 : z + I * kgFreq ρ ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith [h.2]
  exact (differentiableAt_kgTerm ρ h1 h2).differentiableWithinAt

/-- **The Klein–Gordon pole series is analytic off its pole set.** -/
theorem analyticAt_kgPoleSeries {z₀ : ℂ} (hz₀ : z₀ ∉ kgPoleSet) :
    AnalyticAt ℂ kgPoleSeries z₀ := by
  obtain ⟨r, hr, hd⟩ := differentiableOn_kgPoleSeries_ball hz₀
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

/-! ## Section 5: Exact blow-up decomposition of the pole series at a pole -/

/-- Frequencies different from `ρ_{ρ₀}` stay at a positive distance from it. -/
theorem exists_pos_forall_kgFreq_ne (ρ₀ : zetaZeroConfig.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ ρ : zetaZeroConfig.carrier, kgFreq ρ ≠ kgFreq ρ₀ →
      ε ≤ ‖kgFreq ρ - kgFreq ρ₀‖ := by
  set S := {ρ : zetaZeroConfig.carrier | ‖kgFreq ρ‖ ≤ ‖kgFreq ρ₀‖ + 1} with hS
  have hSfin : S.Finite := finite_kgFreq_norm_le _
  set P : Set ℂ := (kgFreq '' S) \ {kgFreq ρ₀} with hP
  have hPfin : P.Finite := (hSfin.image _).subset sdiff_subset
  have hnot : kgFreq ρ₀ ∉ P := fun h => h.2 (mem_singleton _)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hPfin.isClosed.isOpen_compl _ hnot
  refine ⟨min δ 1, by positivity, min_le_right _ _, fun ρ hρ => ?_⟩
  by_cases hρS : ρ ∈ S
  · have hmem : kgFreq ρ ∈ P := ⟨⟨ρ, hρS, rfl⟩, hρ⟩
    have h : kgFreq ρ ∉ Metric.ball (kgFreq ρ₀) δ := fun h => hball h hmem
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at h
    exact (min_le_left _ _).trans h
  · have hbig : ‖kgFreq ρ₀‖ + 1 < ‖kgFreq ρ‖ := not_le.mp hρS
    have := norm_sub_norm_le (kgFreq ρ) (kgFreq ρ₀)
    linarith [min_le_right δ 1]

/-- The residue coefficient at the pole `−i ρ_{ρ₀}`: `m_ρ w_{ρ₀}/2` on the zeros sharing the
frequency, `0` otherwise. -/
def kgResidueTerm (ρ₀ ρ : zetaZeroConfig.carrier) : ℂ :=
  if kgFreq ρ = kgFreq ρ₀ then (zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ₀ / 2) else 0

/-- The regular remainder of `kgTerm` at `−i ρ_{ρ₀} + d`. -/
def kgRegularTerm (ρ₀ : zetaZeroConfig.carrier) (d : ℂ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2) * (1 / (-(I * kgFreq ρ₀) + d - I * kgFreq ρ)) +
    (if kgFreq ρ = kgFreq ρ₀ then 0 else
      (zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2) * (1 / (-(I * kgFreq ρ₀) + d + I * kgFreq ρ)))

theorem kgTerm_eq_residue_add_regular (ρ₀ : zetaZeroConfig.carrier) (d : ℂ)
    (ρ : zetaZeroConfig.carrier) :
    kgTerm (-(I * kgFreq ρ₀) + d) ρ = kgResidueTerm ρ₀ ρ / d + kgRegularTerm ρ₀ d ρ := by
  unfold kgTerm kgResidueTerm kgRegularTerm
  by_cases h : kgFreq ρ = kgFreq ρ₀
  · rw [if_pos h, if_pos h, kgWeight_eq_of_kgFreq_eq h, h]
    have e : -(I * kgFreq ρ₀) + d + I * kgFreq ρ₀ = d := by ring
    rw [e]; ring
  · rw [if_neg h, if_neg h]; ring

theorem finite_sameFreq (ρ₀ : zetaZeroConfig.carrier) :
    {ρ : zetaZeroConfig.carrier | kgFreq ρ = kgFreq ρ₀}.Finite :=
  (finite_kgFreq_norm_le ‖kgFreq ρ₀‖).subset fun ρ hρ => by
    simp only [mem_setOf_eq] at hρ ⊢; rw [hρ]

theorem summable_kgResidueTerm (ρ₀ : zetaZeroConfig.carrier) :
    Summable (kgResidueTerm ρ₀) := by
  refine summable_of_ne_finset_zero (s := (finite_sameFreq ρ₀).toFinset) fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  simp only [mem_setOf_eq] at hρ
  unfold kgResidueTerm; rw [if_neg hρ]

/-- The total residue `A_{ρ₀} = Σ' ρ, kgResidueTerm ρ₀ ρ` of the pole series at `−i ρ_{ρ₀}`. -/
def kgResidue (ρ₀ : zetaZeroConfig.carrier) : ℂ := ∑' ρ, kgResidueTerm ρ₀ ρ

theorem summable_sameFreq_mult (ρ₀ : zetaZeroConfig.carrier) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (if kgFreq ρ = kgFreq ρ₀ then (zetaZeroConfig.mult ρ : ℝ) else 0) := by
  refine summable_of_ne_finset_zero (s := (finite_sameFreq ρ₀).toFinset) fun ρ hρ => ?_
  rw [Set.Finite.mem_toFinset] at hρ
  simp only [mem_setOf_eq] at hρ
  rw [if_neg hρ]

theorem kgResidue_eq (ρ₀ : zetaZeroConfig.carrier) :
    kgResidue ρ₀ = (kgWeight ρ₀ / 2) *
      ((∑' ρ : zetaZeroConfig.carrier,
        (if kgFreq ρ = kgFreq ρ₀ then (zetaZeroConfig.mult ρ : ℝ) else 0) : ℝ) : ℂ) := by
  unfold kgResidue kgResidueTerm
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  split_ifs
  · push_cast; ring
  · simp

/-- **The residue is bounded below by half the weight**: `‖w_{ρ₀}‖/2 ≤ ‖A_{ρ₀}‖`. -/
theorem norm_kgResidue_ge (ρ₀ : zetaZeroConfig.carrier) :
    ‖kgWeight ρ₀‖ / 2 ≤ ‖kgResidue ρ₀‖ := by
  rw [kgResidue_eq, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hf := summable_sameFreq_mult ρ₀
  have hnn : 0 ≤ ∑' ρ : zetaZeroConfig.carrier,
      (if kgFreq ρ = kgFreq ρ₀ then (zetaZeroConfig.mult ρ : ℝ) else 0) :=
    tsum_nonneg fun ρ => by split_ifs <;> positivity
  have hge : (1 : ℝ) ≤ ∑' ρ : zetaZeroConfig.carrier,
      (if kgFreq ρ = kgFreq ρ₀ then (zetaZeroConfig.mult ρ : ℝ) else 0) := by
    have h1 := hf.le_tsum ρ₀ (fun ρ _ => by split_ifs <;> positivity)
    rw [if_pos rfl] at h1
    have h2 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ₀ := by
      exact_mod_cast zetaZeroConfig.one_le_mult _ ρ₀.2
    linarith
  rw [abs_of_nonneg hnn]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  calc ‖kgWeight ρ₀‖ / 2 = ‖kgWeight ρ₀‖ / 2 * 1 := by ring
    _ ≤ ‖kgWeight ρ₀‖ / 2 * ∑' ρ : zetaZeroConfig.carrier,
        (if kgFreq ρ = kgFreq ρ₀ then (zetaZeroConfig.mult ρ : ℝ) else 0) := by gcongr

theorem kgResidue_ne_zero (ρ₀ : zetaZeroConfig.carrier) : kgResidue ρ₀ ≠ 0 := by
  intro h
  have := norm_kgResidue_ge ρ₀
  rw [h, norm_zero] at this
  linarith [norm_kgWeight_pos ρ₀]

theorem two_lt_norm_add_kgFreq (ρ₀ ρ : zetaZeroConfig.carrier) :
    2 < ‖kgFreq ρ₀ + kgFreq ρ‖ := by
  have h := Complex.abs_re_le_norm (kgFreq ρ₀ + kgFreq ρ)
  rw [Complex.add_re] at h
  have h1 := one_lt_re_kgFreq ρ₀
  have h2 := one_lt_re_kgFreq ρ
  linarith [le_abs_self ((kgFreq ρ₀).re + (kgFreq ρ).re)]

theorem norm_kgRegularTerm_le (ρ₀ : zetaZeroConfig.carrier) {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hsep : ∀ ρ : zetaZeroConfig.carrier, kgFreq ρ ≠ kgFreq ρ₀ → ε₁ ≤ ‖kgFreq ρ - kgFreq ρ₀‖)
    {d : ℂ} (hd1 : ‖d‖ < 1) (hd2 : ‖d‖ < ε₁ / 2) (ρ : zetaZeroConfig.carrier) :
    ‖kgRegularTerm ρ₀ d ρ‖ ≤
      (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / 2 + 1 / ε₁) := by
  unfold kgRegularTerm
  have hA : 1 ≤ ‖-(I * kgFreq ρ₀) + d - I * kgFreq ρ‖ := by
    have e : -(I * kgFreq ρ₀) + d - I * kgFreq ρ = d - I * (kgFreq ρ₀ + kgFreq ρ) := by ring
    rw [e]
    have h1 := norm_sub_norm_le (I * (kgFreq ρ₀ + kgFreq ρ)) d
    rw [norm_mul, Complex.norm_I, one_mul, norm_sub_rev] at h1
    linarith [two_lt_norm_add_kgFreq ρ₀ ρ]
  have hterm1 := norm_term_div_le (zetaZeroConfig.mult ρ) (kgWeight ρ) _ one_pos hA
  refine (norm_add_le _ _).trans ?_
  have hterm2 : ‖(if kgFreq ρ = kgFreq ρ₀ then (0 : ℂ) else
      (zetaZeroConfig.mult ρ : ℂ) * (kgWeight ρ / 2) *
        (1 / (-(I * kgFreq ρ₀) + d + I * kgFreq ρ)))‖ ≤
      (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / ε₁) := by
    split_ifs with h
    · rw [norm_zero]; positivity
    · have hB : ε₁ / 2 ≤ ‖-(I * kgFreq ρ₀) + d + I * kgFreq ρ‖ := by
        have e : -(I * kgFreq ρ₀) + d + I * kgFreq ρ = d + I * (kgFreq ρ - kgFreq ρ₀) := by ring
        rw [e]
        have h1 := norm_sub_norm_le (I * (kgFreq ρ - kgFreq ρ₀)) (-d)
        rw [norm_mul, Complex.norm_I, one_mul, norm_neg, sub_neg_eq_add, add_comm] at h1
        linarith [hsep ρ h]
      have := norm_term_div_le (zetaZeroConfig.mult ρ) (kgWeight ρ) _ (by positivity) hB
      rwa [show (1 : ℝ) / (2 * (ε₁ / 2)) = 1 / ε₁ by field_simp] at this
  calc _ ≤ (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / (2 * 1)) +
        (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / ε₁) := add_le_add hterm1 hterm2
    _ = (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / 2 + 1 / ε₁) := by ring

/-- **Exact blow-up decomposition at the pole `−i ρ_{ρ₀}`**: for all small `d ≠ 0`,
`G(−i ρ_{ρ₀} + d) = A_{ρ₀}/d + B(d)` with `‖B(d)‖` uniformly bounded. -/
theorem kgPoleSeries_decomp (ρ₀ : zetaZeroConfig.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ d : ℂ, ‖d‖ < ε →
      ∃ B : ℂ, ‖B‖ ≤ C ∧ kgPoleSeries (-(I * kgFreq ρ₀) + d) = kgResidue ρ₀ / d + B := by
  obtain ⟨ε₁, hε₁, hε₁1, hsep⟩ := exists_pos_forall_kgFreq_ne ρ₀
  refine ⟨ε₁ / 2, by positivity,
    ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * ‖kgWeight ρ‖ * (1 / 2 + 1 / ε₁),
    fun d hdε => ?_⟩
  have hd1 : ‖d‖ < 1 := by linarith
  have hbound := fun ρ => norm_kgRegularTerm_le ρ₀ hε₁ hsep hd1 hdε ρ
  have hsumB : Summable (kgRegularTerm ρ₀ d) :=
    Summable.of_norm_bounded (summable_mult_mul_norm_kgWeight.mul_right _) hbound
  refine ⟨∑' ρ, kgRegularTerm ρ₀ d ρ,
    tsum_of_norm_bounded (summable_mult_mul_norm_kgWeight.mul_right _).hasSum hbound, ?_⟩
  unfold kgPoleSeries
  rw [tsum_congr (kgTerm_eq_residue_add_regular ρ₀ d),
    Summable.tsum_add ((summable_kgResidueTerm ρ₀).div_const d) hsumB, tsum_div_const]
  rfl

/-! ## Section 6: No holomorphic extension through a blow-up point (tilted-ray argument) -/

/-- **A holomorphic extension through a blow-up point is impossible.** Let `Q` meet the closed
ball of radius `3` about `p₀` in finitely many points, `G` be analytic off `Q`, `F` be holomorphic on
`Re z > a`, and `F = G` on `Re s > 1/2`. If `a < Re p₀ < 1/2` and `‖G(p₀ + d)‖ ≥ c/‖d‖ − C` for all
small `d ≠ 0` with `c > 0`, this is contradictory: along a ray from `p₀` into `Re s > 1/2` whose
slope avoids `Q`, both functions are real-analytic and agree near the far end, hence on the whole
ray, but `F` stays bounded at `p₀` while `G` blows up. -/
theorem false_of_extension_of_blowup {a : ℝ} {F G : ℂ → ℂ} {Q : Set ℂ} {p₀ : ℂ}
    (hQ : (Q ∩ Metric.closedBall p₀ 3).Finite)
    (hFd : ∀ z : ℂ, a < z.re → DifferentiableAt ℂ F z)
    (hG : ∀ z : ℂ, z ∉ Q → AnalyticAt ℂ G z)
    (hFG : ∀ s : ℂ, 1 / 2 < s.re → F s = G s) (ha : 0 ≤ a)
    (hp₀a : a < p₀.re) (hp₀half : p₀.re < 1 / 2) {c : ℝ} (hc : 0 < c)
    (hblow : ∃ ε > 0, ∃ C : ℝ, ∀ d : ℂ, 0 < ‖d‖ → ‖d‖ < ε → c / ‖d‖ - C ≤ ‖G (p₀ + d)‖) :
    False := by
  set B : Set ℂ := Q ∩ Metric.closedBall p₀ 3 with hB
  -- a slope avoiding every obstacle
  set Sl : Set ℝ := (fun b : ℂ => (b - p₀).im / (b - p₀).re) '' B with hSl
  have hSlc : Sl.Countable := (hQ.image _).countable
  obtain ⟨σ, hσSl, hσ0, hσ1⟩ :=
    (hSlc.dense_compl ℝ).exists_between (show (0:ℝ) < 1 by norm_num)
  set v : ℂ := 1 + σ * I with hv
  have hvnorm : ‖v‖ ≤ 2 := by
    calc ‖v‖ ≤ ‖(1:ℂ)‖ + ‖(σ:ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |σ| := by simp
      _ ≤ 2 := by rw [abs_of_pos hσ0]; linarith
  set ℓ : ℝ → ℂ := fun t => p₀ + t * v with hℓ
  have hℓre : ∀ t : ℝ, (ℓ t).re = p₀.re + t := by intro t; simp [hℓ, hv]
  have hℓB : ∀ t : ℝ, 0 < t → ℓ t ∉ B := by
    intro t ht hmem
    apply hσSl
    refine ⟨ℓ t, hmem, ?_⟩
    have e : ℓ t - p₀ = t * v := by simp [hℓ]
    show (ℓ t - p₀).im / (ℓ t - p₀).re = σ
    rw [e]
    simp [hv]
    field_simp
  have hℓball : ∀ t : ℝ, 0 < t → t < 3 / 2 → ℓ t ∈ Metric.closedBall p₀ 3 := by
    intro t ht ht2
    rw [Metric.mem_closedBall, Complex.dist_eq]
    have e : ℓ t - p₀ = t * v := by simp [hℓ]
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hℓQ : ∀ t : ℝ, 0 < t → t < 3 / 2 → ℓ t ∉ Q := fun t ht ht2 h =>
    hℓB t ht ⟨h, hℓball t ht ht2⟩
  -- both sides are real-analytic along the ray
  set U : Set ℝ := Ioo (0:ℝ) (3 / 2) with hU
  set V : Set ℂ := {z : ℂ | a < z.re} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    simp only [hV, Set.mem_setOf_eq, hℓre]
    linarith [ht.1]
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  have hFdiff : DifferentiableOn ℂ F V := fun z hz => (hFd z hz).differentiableWithinAt
  have hFan : AnalyticOnNhd ℝ (fun t : ℝ => F (ℓ t)) U := by
    intro t ht
    have hFz : AnalyticAt ℂ F (ℓ t) := hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))
    exact hFz.restrictScalars.comp (hℓan t)
  have hGan : AnalyticOnNhd ℝ (fun t : ℝ => G (ℓ t)) U := fun t ht =>
    (hG _ (hℓQ t ht.1 ht.2)).restrictScalars.comp (hℓan t)
  -- they agree to the right of `Re = ½`, hence on the whole ray
  set t₁ : ℝ := (1 / 2 - p₀.re + 3 / 2) / 2 with ht₁
  have ht₁U : t₁ ∈ U := ⟨by rw [ht₁]; linarith, by rw [ht₁]; linarith⟩
  have hfg : (fun t : ℝ => F (ℓ t)) =ᶠ[𝓝 t₁] (fun t : ℝ => G (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (show 1 / 2 - p₀.re < t₁ by rw [ht₁]; linarith)
        (show t₁ < 3 / 2 by rw [ht₁]; linarith)) fun t ht => ?_
    exact hFG _ (by rw [hℓre]; linarith [ht.1])
  have heq := hFan.eqOn_of_preconnected_of_eventuallyEq hGan isPreconnected_Ioo ht₁U hfg
  -- `F` stays bounded at `p₀` while `G` blows up
  have hFcont : ContinuousAt F p₀ := (hFd p₀ hp₀a).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ) * v) (𝓝 0) (𝓝 (p₀ + ((0:ℝ) : ℂ) * v)) :=
      tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).mul tendsto_const_nhds)
    simpa using this
  have hcomp : Tendsto (fun t : ℝ => F (ℓ t)) (𝓝 0) (𝓝 (F p₀)) := hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  obtain ⟨ε, hε, C, hC⟩ := hblow
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  set Bd : ℝ := ‖F p₀‖ + 1 with hBd
  have hK : 0 < Bd + C' + 1 := by positivity
  set m : ℝ := min (min δ (ε / 2)) (min (3 / 2) (c / (2 * (Bd + C' + 1)))) with hm
  have hmpos : 0 < m :=
    lt_min (lt_min hδ (by positivity)) (lt_min (by norm_num) (by positivity))
  have hmδ : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hmε : m ≤ ε / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hmT : m ≤ 3 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hmw : m ≤ c / (2 * (Bd + C' + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  set t₀ : ℝ := m / 2 with ht₀
  have ht₀pos : 0 < t₀ := half_pos hmpos
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, by rw [ht₀]; linarith⟩
  have hFb : ‖F (ℓ t₀)‖ ≤ Bd := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; rw [ht₀]; linarith
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖F (ℓ t₀)‖ = ‖(F (ℓ t₀) - F p₀) + F p₀‖ := by congr 1; ring
      _ ≤ ‖F (ℓ t₀) - F p₀‖ + ‖F p₀‖ := norm_add_le _ _
      _ ≤ Bd := by rw [hBd]; linarith
  have hdn : ‖(t₀ : ℂ) * v‖ = t₀ * ‖v‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht₀pos]
  have hvpos : 0 < ‖v‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    have := congrArg Complex.re h
    simp [hv] at this
  have hGb : Bd < ‖G (ℓ t₀)‖ := by
    have h1 := hC ((t₀ : ℂ) * v) (by rw [hdn]; positivity)
      (by rw [hdn]; rw [ht₀]; nlinarith)
    have h2 : c / (2 * t₀) ≤ c / ‖(t₀ : ℂ) * v‖ := by
      rw [hdn]
      exact div_le_div_of_nonneg_left hc.le (by positivity) (by nlinarith)
    have h3 : 2 * (Bd + C' + 1) ≤ c / (2 * t₀) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * t₀ = m := by rw [ht₀]; ring
      rw [this]
      calc 2 * (Bd + C' + 1) * m
          ≤ 2 * (Bd + C' + 1) * (c / (2 * (Bd + C' + 1))) := by gcongr
        _ = c := by field_simp
    have hℓt : ℓ t₀ = p₀ + (t₀ : ℂ) * v := rfl
    rw [hℓt]
    linarith [le_max_left C 0]
  have hEq : F (ℓ t₀) = G (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-! ## Section 7: One-sided growth bounds force the frequency displacement bound -/

/-- Landau's theorem applied to `c · φ_Λ` (`|c| = 1`): a one-sided exponential bound extends the
Laplace transform `c · kgPoleSeries` holomorphically to `Re z > a`. -/
theorem exists_extension_of_le_exp {c : ℝ} (hc : |c| = 1) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) (hM : ∀ u : ℝ, 0 ≤ u → c * chmdWave u ≤ M * Real.exp (a * u)) :
    ∃ F : ℂ → ℂ, (∀ z : ℂ, a < z.re → DifferentiableAt ℂ F z) ∧
      ∀ s : ℂ, 1 / 2 < s.re → F s = (c : ℂ) * kgPoleSeries s := by
  refine exists_differentiable_extension_of_le_exp (φ := fun u => c * chmdWave u)
    (continuous_const.mul continuous_chmdWave).measurable (K := kgMass) ?_ ha0 ha
    (fun u hu => hM u hu) (Λ := fun s => (c : ℂ) * kgPoleSeries s) ?_ ?_
  · intro u hu
    rw [abs_mul, hc, one_mul]
    have := abs_chmdWave_le u
    rwa [abs_of_pos hu] at this
  · intro t _
    exact analyticAt_const.mul (analyticAt_kgPoleSeries (ofReal_notMem_kgPoleSet t))
  · intro s hs
    simp only [Complex.ofReal_mul]
    rw [← integral_chmdWave_mul_cexp hs, ← integral_const_mul]
    congr 1
    funext u
    ring

/-- **The pole exclusion theorem.** If `c · φ_Λ(u) ≤ M e^{au}` on `u ≥ 0` with `|c| = 1` and
`0 ≤ a < 1/2`, then every nontrivial zero has `Im ρ_ρ ≤ a`. -/
theorem im_kgFreq_le_of_le_exp {c : ℝ} (hc : |c| = 1) {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ u : ℝ, 0 ≤ u → c * chmdWave u ≤ M * Real.exp (a * u))
    (ρ₀ : zetaZeroConfig.carrier) : (kgFreq ρ₀).im ≤ a := by
  by_contra hle
  have hlt : a < (kgFreq ρ₀).im := not_le.mp hle
  obtain ⟨F, hFd, hFG⟩ := exists_extension_of_le_exp hc ha0 ha hM
  set p₀ : ℂ := -(I * kgFreq ρ₀) with hp₀
  have hp₀re : p₀.re = (kgFreq ρ₀).im := by
    rw [hp₀, Complex.neg_re, Complex.I_mul_re, neg_neg]
  have hQ : (kgPoleSet ∩ Metric.closedBall p₀ 3).Finite := by
    set S := {ρ : zetaZeroConfig.carrier | ‖kgFreq ρ‖ ≤ ‖p₀‖ + 3} with hS
    have hSfin : S.Finite := finite_kgFreq_norm_le _
    refine ((hSfin.image (fun ρ => I * kgFreq ρ)).union
      (hSfin.image (fun ρ => -(I * kgFreq ρ)))).subset ?_
    rintro z ⟨⟨ρ, h | h⟩, hz⟩
    · refine Or.inl ⟨ρ, ?_, h.symm⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      show ‖kgFreq ρ‖ ≤ ‖p₀‖ + 3
      have e : ‖z‖ = ‖kgFreq ρ‖ := by rw [h, norm_mul, Complex.norm_I, one_mul]
      have := norm_sub_norm_le z p₀
      linarith
    · refine Or.inr ⟨ρ, ?_, h.symm⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      show ‖kgFreq ρ‖ ≤ ‖p₀‖ + 3
      have e : ‖z‖ = ‖kgFreq ρ‖ := by rw [h, norm_neg, norm_mul, Complex.norm_I, one_mul]
      have := norm_sub_norm_le z p₀
      linarith
  obtain ⟨ε, hε, C, hdec⟩ := kgPoleSeries_decomp ρ₀
  have hblow : ∃ ε > 0, ∃ C : ℝ, ∀ d : ℂ, 0 < ‖d‖ → ‖d‖ < ε →
      ‖kgResidue ρ₀‖ / ‖d‖ - C ≤ ‖(c : ℂ) * kgPoleSeries (p₀ + d)‖ := by
    refine ⟨ε, hε, C, fun d _ hdε => ?_⟩
    obtain ⟨B, hB, hGd⟩ := hdec d hdε
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hc, one_mul, hGd]
    have h1 := norm_sub_norm_le (kgResidue ρ₀ / d) (-B)
    rw [norm_neg, sub_neg_eq_add, norm_div] at h1
    linarith
  exact false_of_extension_of_blowup hQ hFd
    (fun z hz => analyticAt_const.mul (analyticAt_kgPoleSeries hz)) hFG ha0
    (by rw [hp₀re]; exact hlt) (by rw [hp₀re]; exact (abs_lt.mp (abs_im_kgFreq_lt ρ₀)).2)
    ((half_pos (norm_kgWeight_pos ρ₀)).trans_le (norm_kgResidue_ge ρ₀)) hblow

/-- Both signs of the displacement, via the reflection `ρ ↦ 1 − ρ̄`. -/
theorem abs_im_kgFreq_le_of_le_exp {c : ℝ} (hc : |c| = 1) {a M : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 1 / 2) (hM : ∀ u : ℝ, 0 ≤ u → c * chmdWave u ≤ M * Real.exp (a * u))
    (ρ : zetaZeroConfig.carrier) : |(kgFreq ρ).im| ≤ a := by
  rw [abs_le]
  refine ⟨?_, im_kgFreq_le_of_le_exp hc ha0 ha hM ρ⟩
  have h := im_kgFreq_le_of_le_exp hc ha0 ha hM (reflectZero ρ)
  rw [kgFreq_reflectZero, Complex.conj_im] at h
  linarith

/-- **Upper bound version**: `φ_Λ(u) ≤ M e^{au}` on `u ≥ 0` forces `|Im ρ_ρ| ≤ a` at every zero. -/
theorem abs_im_kgFreq_le_of_chmdWave_le_exp {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ u : ℝ, 0 ≤ u → chmdWave u ≤ M * Real.exp (a * u))
    (ρ : zetaZeroConfig.carrier) : |(kgFreq ρ).im| ≤ a :=
  abs_im_kgFreq_le_of_le_exp (c := 1) (by simp) ha0 ha
    (fun u hu => by rw [one_mul]; exact hM u hu) ρ

/-- **Lower bound version**: `−M e^{au} ≤ φ_Λ(u)` on `u ≥ 0` forces `|Im ρ_ρ| ≤ a` at every
zero. -/
theorem abs_im_kgFreq_le_of_neg_exp_le_chmdWave {a M : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2)
    (hM : ∀ u : ℝ, 0 ≤ u → -(M * Real.exp (a * u)) ≤ chmdWave u)
    (ρ : zetaZeroConfig.carrier) : |(kgFreq ρ).im| ≤ a :=
  abs_im_kgFreq_le_of_le_exp (c := -1) (by simp) ha0 ha (M := M)
    (fun u hu => by rw [neg_one_mul]; linarith [hM u hu]) ρ

/-- **The exact growth law of the causal wave.** For `0 ≤ a < 1/2`: an upper exponential bound on
`u ≥ 0`, a lower exponential bound on `u ≥ 0`, and a two-sided exponential bound on `ℝ` are each
equivalent to the frequency displacement bound `|Im √(γ_ρ² + 2)| ≤ a` at every nontrivial zero. -/
theorem chmdWave_growth_law {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    ((∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → chmdWave u ≤ M * Real.exp (a * u)) ↔
      ∀ ρ : zetaZeroConfig.carrier, |(kgFreq ρ).im| ≤ a) ∧
    ((∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → -(M * Real.exp (a * u)) ≤ chmdWave u) ↔
      ∀ ρ : zetaZeroConfig.carrier, |(kgFreq ρ).im| ≤ a) ∧
    ((∃ K : ℝ, ∀ u : ℝ, |chmdWave u| ≤ K * Real.exp (a * |u|)) ↔
      ∀ ρ : zetaZeroConfig.carrier, |(kgFreq ρ).im| ≤ a) := by
  refine ⟨⟨fun ⟨M, hM⟩ => abs_im_kgFreq_le_of_chmdWave_le_exp ha0 ha hM,
      fun h => ⟨kgMass, fun u hu => ?_⟩⟩,
    ⟨fun ⟨M, hM⟩ => abs_im_kgFreq_le_of_neg_exp_le_chmdWave ha0 ha hM,
      fun h => ⟨kgMass, fun u hu => ?_⟩⟩,
    ⟨fun ⟨K, hK⟩ => ?_, fun h => ⟨kgMass, abs_chmdWave_le_of_forall_abs_im_kgFreq_le h⟩⟩⟩
  · have := abs_chmdWave_le_of_forall_abs_im_kgFreq_le h u
    rw [abs_of_nonneg hu] at this
    exact (le_abs_self _).trans this
  · have := abs_chmdWave_le_of_forall_abs_im_kgFreq_le h u
    rw [abs_of_nonneg hu] at this
    linarith [neg_abs_le (chmdWave u)]
  · refine abs_im_kgFreq_le_of_chmdWave_le_exp ha0 ha (M := K) fun u hu => ?_
    have := hK u
    rw [abs_of_nonneg hu] at this
    exact (le_abs_self _).trans this

/-! ## Section 8: Growth–positivity collapse at `a = 0`: the Riemann Hypothesis chain -/

/-- When the frequency of a zero is real, its zero-side Toeplitz summand is nonnegative: the packet
weight is `trigPacketWeight ≥ 0` and the sech² weight has positive real part. -/
theorem re_summand_nonneg_of_im_kgFreq_eq_zero {N : ℕ} (t c : Fin N → ℝ)
    (ρ : zetaZeroConfig.carrier) (h : (kgFreq ρ).im = 0) :
    0 ≤ (zetaZeroConfig.mult ρ : ℝ) *
      (specSq (cosComb t c sechHalf) (Zeta23.gammaOf ρ) +
        specSq (sinComb t c sechHalf) (Zeta23.gammaOf ρ)).re := by
  rw [specSq_cosComb_add_specSq_sinComb_gammaOf]
  set r : ℝ := (kgFreq ρ).re with hr
  have hreal : kgFreq ρ = (r : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simp [h]
  have hsum : (∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ,
      ((c p.1 * c p.2 : ℝ) : ℂ) * rhoCosShift (t p.2 - t p.1) sechHalf (Zeta23.gammaOf ρ)) =
      ((trigPacketWeight t c r : ℝ) : ℂ) * kgWeight ρ := by
    rw [trigPacketWeight_eq_sum_sum_cos, ← Finset.sum_product', Complex.ofReal_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    change ((c p.1 * c p.2 : ℝ) : ℂ) *
      (Complex.cos (((t p.2 - t p.1 : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ) = _
    rw [hreal]
    push_cast
    ring
  rw [hsum, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (trigPacketWeight_nonneg t c _) (re_kgWeight_pos ρ).le)

/-- **Real frequencies at every zero imply the Riemann Hypothesis**, through the Stage 4 Toeplitz
criterion: every zero-side summand is nonnegative. -/
theorem riemannHypothesis_of_forall_im_kgFreq_eq_zero
    (h : ∀ ρ : zetaZeroConfig.carrier, (kgFreq ρ).im = 0) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_sum_sum_cosineShiftFn_sechHalf_nonneg]
  intro N t c
  rw [sum_sum_cosineShiftFn_sechHalf_vonMangoldt_eq_tsum_re]
  exact tsum_nonneg fun ρ => re_summand_nonneg_of_im_kgFreq_eq_zero t c ρ (h ρ)

theorem re_eq_half_of_rh (hRH : RiemannHypothesis) (ρ : zetaZeroConfig.carrier) :
    (ρ : ℂ).re = 1 / 2 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  refine hRH _ hmem.1 ?_ ?_
  · rintro ⟨n, hn⟩
    have := congrArg Complex.re hn
    simp at this
    linarith [hmem.2.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · intro h1
    have := hmem.2.2
    rw [h1] at this
    simp at this

/-- Under the Riemann Hypothesis every frequency is real and every weight is a nonnegative real. -/
theorem kgFreq_kgWeight_of_rh (hRH : RiemannHypothesis) (ρ : zetaZeroConfig.carrier) :
    (kgFreq ρ).im = 0 ∧ kgWeight ρ = (((kgWeight ρ).re : ℝ) : ℂ) ∧ 0 ≤ (kgWeight ρ).re := by
  have hγ := gammaOf_eq_ofReal_im_of_re_eq_half (re_eq_half_of_rh hRH ρ)
  refine ⟨?_, ?_, (re_kgWeight_pos ρ).le⟩
  · unfold kgFreq; rw [hγ, rhoC_ofReal, Complex.ofReal_im]
  · apply Complex.ext
    · simp
    · unfold kgWeight; rw [hγ, specSq_im_ofReal, Complex.ofReal_im]

theorem summable_re_cosTerm (y : ℝ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re := by
  refine (summable_re_zeroSide_of_goodDensity (goodDensity_cosShift y evenStrip_sechHalf)).congr
    fun ρ => ?_
  simp only [kgFreq, kgWeight, rhoCosShift]

/-- **Under the Riemann Hypothesis the causal wave is dominated by its value at the origin**:
`|φ_Λ(y)| ≤ φ_Λ(0)`. -/
theorem abs_chmdWave_le_zero_value_of_rh (hRH : RiemannHypothesis) (y : ℝ) :
    |chmdWave y| ≤ chmdWave 0 := by
  rw [chmdWave_eq_tsum_re y, chmdWave_eq_tsum_re 0]
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      |(zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re| ≤
        (zetaZeroConfig.mult ρ : ℝ) *
          (Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re := by
    intro ρ
    obtain ⟨him, hw, hwre⟩ := kgFreq_kgWeight_of_rh hRH ρ
    set r : ℝ := (kgFreq ρ).re with hr
    set w : ℝ := (kgWeight ρ).re with hwdef
    have hreal : kgFreq ρ = (r : ℂ) := by
      apply Complex.ext
      · simp [hr]
      · simp [him]
    have e1 : (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re = Real.cos (y * r) * w := by
      rw [hreal, hw, ← Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    have e0 : (Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re = w := by
      rw [hreal, hw, ← Complex.ofReal_mul, ← Complex.ofReal_cos, ← Complex.ofReal_mul,
        Complex.ofReal_re, zero_mul, Real.cos_zero, one_mul]
    rw [e1, e0, abs_mul, Nat.abs_cast, abs_mul, abs_of_nonneg hwre]
    have hc := Real.abs_cos_le_one (y * r)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hwre hc) hm
  have hs0 := summable_re_cosTerm 0
  have hsy := summable_re_cosTerm y
  calc |∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re|
      ≤ ∑' ρ : zetaZeroConfig.carrier,
          |(zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re| := by
        have := norm_tsum_le_tsum_norm (f := fun ρ : zetaZeroConfig.carrier =>
          (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re)
          (hsy.abs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * (Complex.cos (0 * kgFreq ρ) * kgWeight ρ).re :=
        Summable.tsum_le_tsum hterm hsy.abs hs0

/-- **Riemann Hypothesis ⟺ real Klein–Gordon frequencies at every zero.** -/
theorem riemannHypothesis_iff_forall_im_kgFreq_eq_zero :
    RiemannHypothesis ↔ ∀ ρ : zetaZeroConfig.carrier, (kgFreq ρ).im = 0 :=
  ⟨fun h ρ => (kgFreq_kgWeight_of_rh h ρ).1, riemannHypothesis_of_forall_im_kgFreq_eq_zero⟩

theorem im_kgFreq_eq_zero_of_abs_le_zero {ρ : zetaZeroConfig.carrier}
    (h : |(kgFreq ρ).im| ≤ 0) : (kgFreq ρ).im = 0 :=
  abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- **Riemann Hypothesis ⟺ the causal wave is bounded above on `[0, ∞)`.** -/
theorem riemannHypothesis_iff_chmdWave_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → chmdWave u ≤ M := by
  constructor
  · intro h
    exact ⟨chmdWave 0, fun u _ => (le_abs_self _).trans (abs_chmdWave_le_zero_value_of_rh h u)⟩
  · rintro ⟨M, hM⟩
    refine riemannHypothesis_of_forall_im_kgFreq_eq_zero fun ρ => im_kgFreq_eq_zero_of_abs_le_zero ?_
    exact abs_im_kgFreq_le_of_chmdWave_le_exp (a := 0) le_rfl (by norm_num) (M := M)
      (fun u hu => by simpa using hM u hu) ρ

/-- **Riemann Hypothesis ⟺ the causal wave is bounded below on `[0, ∞)`.** -/
theorem riemannHypothesis_iff_chmdWave_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → -M ≤ chmdWave u := by
  constructor
  · intro h
    refine ⟨chmdWave 0, fun u _ => ?_⟩
    have := abs_chmdWave_le_zero_value_of_rh h u
    linarith [neg_abs_le (chmdWave u)]
  · rintro ⟨M, hM⟩
    refine riemannHypothesis_of_forall_im_kgFreq_eq_zero fun ρ => im_kgFreq_eq_zero_of_abs_le_zero ?_
    exact abs_im_kgFreq_le_of_neg_exp_le_chmdWave (a := 0) le_rfl (by norm_num) (M := M)
      (fun u hu => by simpa using hM u hu) ρ

/-- **Riemann Hypothesis ⟺ the causal wave is bounded on `ℝ`.** -/
theorem riemannHypothesis_iff_chmdWave_bounded :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ u : ℝ, |chmdWave u| ≤ K := by
  constructor
  · intro h; exact ⟨chmdWave 0, abs_chmdWave_le_zero_value_of_rh h⟩
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_iff_chmdWave_bddAbove.mpr
      ⟨K, fun u _ => (le_abs_self _).trans (hK u)⟩

/-- **Riemann Hypothesis ⟺ `φ_Λ(y) ≤ φ_Λ(0)` for every `y`** (the sharp one-sided bound). -/
theorem riemannHypothesis_iff_forall_chmdWave_le_zero_value :
    RiemannHypothesis ↔ ∀ y : ℝ, chmdWave y ≤ chmdWave 0 := by
  constructor
  · intro h y; exact (le_abs_self _).trans (abs_chmdWave_le_zero_value_of_rh h y)
  · intro h
    exact riemannHypothesis_iff_chmdWave_bddAbove.mpr ⟨chmdWave 0, fun u _ => h u⟩

/-- **Riemann Hypothesis ⟺ `|φ_Λ(y)| ≤ φ_Λ(0)` for every `y`** (all `2 × 2` Toeplitz forms). -/
theorem riemannHypothesis_iff_forall_abs_chmdWave_le_zero_value :
    RiemannHypothesis ↔ ∀ y : ℝ, |chmdWave y| ≤ chmdWave 0 := by
  constructor
  · intro h y; exact abs_chmdWave_le_zero_value_of_rh h y
  · intro h
    exact riemannHypothesis_iff_forall_chmdWave_le_zero_value.mpr
      fun y => (le_abs_self _).trans (h y)

/-- **Riemann Hypothesis ⟺ every two-point difference packet of Stage 13 is nonnegative**: the
whole Toeplitz hierarchy of `cosineShiftFn Λ sechHalf` collapses to the packets `![0, y]`, `![1, -1]`. -/
theorem riemannHypothesis_iff_forall_twoPointDiff_nonneg :
    RiemannHypothesis ↔ ∀ y : ℝ, 0 ≤ ∑ i, ∑ j, twoPointDiffCoeff i * twoPointDiffCoeff j *
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf
        (twoPointShift y j - twoPointShift y i) := by
  rw [riemannHypothesis_iff_forall_chmdWave_le_zero_value]
  refine forall_congr' fun y => ?_
  rw [sum_sum_twoPointDiff_cosineShiftFn]
  change chmdWave y ≤ chmdWave 0 ↔ 0 ≤ 2 * (chmdWave 0 - chmdWave y)
  constructor <;> intro h <;> linarith

/-- **The Bochner measure of the causal wave exists iff the wave is bounded above.** -/
theorem exists_sechHalf_measure_iff_chmdWave_bddAbove :
    (∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ y : ℝ, charFun ν y =
      (cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf y : ℂ)) ↔
      ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → chmdWave u ≤ M :=
  riemannHypothesis_iff_exists_sechHalf_measure_vonMangoldt.symm.trans
    riemannHypothesis_iff_chmdWave_bddAbove

/-! ## Section 9: The positive-real criterion for the Klein–Gordon pole series -/

theorem notMem_kgPoleSet_of_rh (hRH : RiemannHypothesis) {s : ℂ} (hs : 0 < s.re) :
    s ∉ kgPoleSet := by
  rintro ⟨ρ, h | h⟩
  · have him := (kgFreq_kgWeight_of_rh hRH ρ).1
    have := congrArg Complex.re h
    rw [Complex.I_mul_re, him] at this
    linarith
  · have him := (kgFreq_kgWeight_of_rh hRH ρ).1
    have := congrArg Complex.re h
    rw [Complex.neg_re, Complex.I_mul_re, him] at this
    linarith

theorem summable_kgTerm_of_notMem {s : ℂ} (hs : s ∉ kgPoleSet) : Summable (kgTerm s) := by
  obtain ⟨r, hr, -, hball⟩ := exists_ball_kgFreq_dist hs
  refine Summable.of_norm_bounded (summable_mult_mul_norm_kgWeight.div_const r) fun ρ => ?_
  exact norm_kgTerm_le hr ρ (hball s (Metric.mem_ball_self hr) ρ).1
    (hball s (Metric.mem_ball_self hr) ρ).2

theorem re_one_div_sub_I_mul_ofReal_nonneg {s : ℂ} (hs : 0 < s.re) (r : ℝ) :
    0 ≤ (1 / (s - I * (r : ℂ))).re ∧ 0 ≤ (1 / (s + I * (r : ℂ))).re := by
  constructor
  · rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.sub_re, Complex.I_mul_re, Complex.ofReal_im]
    linarith
  · rw [one_div, Complex.inv_re]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    rw [Complex.add_re, Complex.I_mul_re, Complex.ofReal_im]
    linarith

theorem re_kgTerm_nonneg_of_rh (hRH : RiemannHypothesis) {s : ℂ} (hs : 0 < s.re)
    (ρ : zetaZeroConfig.carrier) : 0 ≤ (kgTerm s ρ).re := by
  obtain ⟨him, hw, hwre⟩ := kgFreq_kgWeight_of_rh hRH ρ
  have hreal : kgFreq ρ = (((kgFreq ρ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  unfold kgTerm
  rw [hreal, hw]
  have e : (zetaZeroConfig.mult ρ : ℂ) * ((((kgWeight ρ).re : ℝ) : ℂ) / 2) =
      (((zetaZeroConfig.mult ρ : ℝ) * ((kgWeight ρ).re / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.add_re]
  obtain ⟨h1, h2⟩ := re_one_div_sub_I_mul_ofReal_nonneg hs (kgFreq ρ).re
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (add_nonneg h1 h2)

/-- **Riemann Hypothesis ⟺ the Klein–Gordon pole series is positive-real**: its real part is
nonnegative on the open right half-plane. -/
theorem riemannHypothesis_iff_kgPoleSeries_positiveReal :
    RiemannHypothesis ↔ ∀ s : ℂ, 0 < s.re → 0 ≤ (kgPoleSeries s).re := by
  constructor
  · intro hRH s hs
    unfold kgPoleSeries
    rw [Complex.re_tsum (summable_kgTerm_of_notMem (notMem_kgPoleSet_of_rh hRH hs))]
    exact tsum_nonneg fun ρ => re_kgTerm_nonneg_of_rh hRH hs ρ
  · intro hpos
    refine riemannHypothesis_of_forall_im_kgFreq_eq_zero fun ρ => ?_
    by_contra hne
    -- reduce to a zero with positive displacement
    have hmain : ∀ ρ₀ : zetaZeroConfig.carrier, 0 < (kgFreq ρ₀).im → False := by
      intro ρ₀ hβ
      obtain ⟨ε, hε, C, hdec⟩ := kgPoleSeries_decomp ρ₀
      set A : ℂ := kgResidue ρ₀ with hA
      have hA0 : A ≠ 0 := kgResidue_ne_zero ρ₀
      have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA0
      set β : ℝ := (kgFreq ρ₀).im with hβdef
      set t : ℝ := min (min (ε / 2) (β / 2)) (‖A‖ / (2 * (|C| + 1))) with ht
      have htpos : 0 < t := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
      have htε : t ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
      have htβ : t ≤ β / 2 := (min_le_left _ _).trans (min_le_right _ _)
      have htA : t ≤ ‖A‖ / (2 * (|C| + 1)) := min_le_right _ _
      set d : ℂ := -((t : ℂ) * (A / (‖A‖ : ℂ))) with hd
      have hdn : ‖d‖ = t := by
        rw [hd, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos,
          norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hAn.ne', mul_one]
      obtain ⟨B, hB, hG⟩ := hdec d (by rw [hdn]; linarith)
      have hAd : A / d = (((-(‖A‖ / t)) : ℝ) : ℂ) := by
        rw [hd]
        have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
        have hAn0 : (‖A‖ : ℂ) ≠ 0 := by exact_mod_cast hAn.ne'
        push_cast
        field_simp
      have hre : 0 < (-(I * kgFreq ρ₀) + d).re := by
        rw [Complex.add_re, Complex.neg_re, Complex.I_mul_re, neg_neg]
        have h1 := Complex.abs_re_le_norm d
        rw [hdn] at h1
        have h2 := (abs_le.mp h1).1
        linarith
      have hcontra := hpos _ hre
      rw [hG, Complex.add_re, hAd, Complex.ofReal_re] at hcontra
      have hBre : B.re ≤ |C| := (Complex.abs_re_le_norm B).trans' (le_abs_self _) |>.trans
        (hB.trans (le_abs_self C))
      have hbig : 2 * (|C| + 1) ≤ ‖A‖ / t := by
        rw [le_div_iff₀ htpos]
        calc 2 * (|C| + 1) * t ≤ 2 * (|C| + 1) * (‖A‖ / (2 * (|C| + 1))) := by gcongr
          _ = ‖A‖ := by field_simp
      linarith [abs_nonneg C]
    rcases lt_or_gt_of_ne hne with hneg | hposβ
    · apply hmain (reflectZero ρ)
      rw [kgFreq_reflectZero, Complex.conj_im]
      linarith
    · exact hmain ρ hposβ

end RHTower.CHMDGrowthCollapse

end
