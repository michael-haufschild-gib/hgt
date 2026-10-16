import GaloisForLFunctions.RHTower.CHMDForcedSpectralMeasureAndOffLineDefectWave

/-!
# CHMD: Klein–Gordon Energy Positivity and the Unconditional Origin Maximum of the Causal Wave

The causal wave `φ_Λ(y) = cosineShiftFn Λ sechHalf y = Σ_ρ m_ρ Re(cos(y ρ_ρ) w_ρ)` has
`ρ_ρ = √(γ_ρ² + 2)` and `w_ρ = sech²(γ_ρ/2)`. Stage 15 proved `Re w_ρ > 0` for every zero, on or
off the line, hence `φ_Λ(0) ≥ 0`. This module establishes the next unconditional positivity, one
order up: the **Klein–Gordon energy density** `(z² + 2) sech²(z/2)` has positive real part on the
critical strip `|Im z| < 1/2` (`re_energyDensity_pos`), so every zero contributes positive curvature
at the origin, `Re(ρ_ρ² w_ρ) > 0` (`kgEnergyTerm_pos`).

Consequences, all unconditional:

1. **The energy moment** `Σ_ρ m_ρ Re(ρ_ρ² w_ρ)` is nonnegative, strictly positive as soon as a
   nontrivial zero exists, and equals the even Weil functional of the explicit spectral density
   `specSq (rhoC · sechHalf) = (z² + 2) sech²(z/2)` (`kgEnergyMoment_eq_evenWeilDensity`). This gives a
   new unconditional prime-side inequality, the energy-weighted explicit-formula inequality
   `prime_energy_le_pole_add_arch`: the prime sum against the kernel of `(r² + 2) sech²(r/2)` is at
   most `7/(2 cos²(1/4))` plus the archimedean energy integral.
2. **Second-order expansion with explicit remainder** (`chmdWave_zero_sub_ge`): for `|y| ≤ 1/2`,
   `φ_Λ(0) − φ_Λ(y) ≥ (y²/2) E_y − 3 y⁴ Q`, where `E_y` sums the positive energy terms of the zeros
   with `|y ρ_ρ| ≤ 1` and `Q = Σ_ρ m_ρ ‖w_ρ‖ ‖ρ_ρ‖⁴` is the finite quartic mass.
3. **The origin maximum principle** (`exists_origin_maximum`): there is `y₀ > 0` such that
   `φ_Λ(y) ≤ φ_Λ(0)` for all `|y| ≤ y₀`. Equivalently every two-point difference packet of Stage 13
   with shift at most `y₀` is nonnegative: the first unconditional positivity of the
   Riemann-Hypothesis-sensitive `2 × 2` Toeplitz family on an open set of shifts, with the
   Klein–Gordon energy positivity as its mechanism.

The radius `y₀` is explicit in terms of a single zero's energy term and frequency and the quartic mass.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDEnergyPositivity

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry RHTower.EvenSector
open RHTower.CHMDStage11 RHTower.CHMDStage13 RHTower.CHMDStage15 RHTower.CHMDGrowthCollapse

/-! ## Section 1: The Klein–Gordon energy density has positive real part on the strip -/

theorem cosh_half_eq_re_add_im (z : ℂ) :
    Complex.cosh (z / 2) =
      ((Real.cosh (z.re / 2) * Real.cos (z.im / 2) : ℝ) : ℂ) +
        ((Real.sinh (z.re / 2) * Real.sin (z.im / 2) : ℝ) : ℂ) * I := by
  have hz : z / 2 = ((z.re / 2 : ℝ) : ℂ) + ((z.im / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hz, cosh_ofReal_add_mul_I]

/-- Imaginary part of `cosh(z/2)²`: `sinh(Re z) sin(Im z) / 2`. -/
theorem im_cosh_half_sq (z : ℂ) :
    (Complex.cosh (z / 2) ^ 2).im = Real.sinh z.re * Real.sin z.im / 2 := by
  rw [cosh_half_eq_re_add_im, sq]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero, mul_one, sub_zero]
  have h1 : Real.sinh z.re = 2 * Real.sinh (z.re / 2) * Real.cosh (z.re / 2) := by
    rw [← Real.sinh_two_mul]; ring_nf
  have h2 : Real.sin z.im = 2 * Real.sin (z.im / 2) * Real.cos (z.im / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [h1, h2]; ring

theorem normSq_cosh_half_ge (z : ℂ) :
    (Real.cosh (z.re / 2) * Real.cos (z.im / 2)) ^ 2 ≤ Complex.normSq (Complex.cosh (z / 2)) := by
  rw [cosh_half_eq_re_add_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero, mul_one, sub_zero]
  nlinarith [sq_nonneg (Real.sinh (z.re / 2) * Real.sin (z.im / 2))]

theorem self_mul_sinh_nonneg (a : ℝ) : 0 ≤ a * Real.sinh a := by
  rcases le_or_gt 0 a with ha | ha
  · exact mul_nonneg ha (Real.sinh_nonneg_iff.mpr ha)
  · have : Real.sinh a < 0 := Real.sinh_neg_iff.mpr ha
    nlinarith

theorem self_mul_sin_nonneg {b : ℝ} (hb : |b| < 1 / 2) : 0 ≤ b * Real.sin b := by
  have hb' := abs_lt.mp hb
  rcases le_or_gt 0 b with h | h
  · exact mul_nonneg h (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [Real.pi_gt_three]))
  · have : Real.sin b ≤ 0 := by
      have h1 : 0 ≤ Real.sin (-b) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
      rw [Real.sin_neg] at h1
      linarith
    nlinarith

/-- **Energy positivity on the strip**: `Re((z² + 2) · conj(cosh(z/2)²)) > 0` for `|Im z| < 1/2`. -/
theorem re_sq_add_two_mul_conj_cosh_half_sq_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < ((z ^ 2 + 2) * conj (Complex.cosh (z / 2) ^ 2)).re := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, re_cosh_half_sq, im_cosh_half_sq,
    re_sq_add_two]
  have him : (z ^ 2 + 2).im = 2 * z.re * z.im := by simp [sq]; ring
  rw [him]
  have hb := abs_lt.mp hz
  have hb2 : z.im ^ 2 < 1 / 4 := by nlinarith [abs_nonneg z.im, sq_abs z.im]
  have hcos : 0 < Real.cos z.im := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_gt_three]
  have hcos2 : 0 < Real.cos (z.im / 2) ^ 2 := by
    have : 0 < Real.cos (z.im / 2) := by
      apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_gt_three]
    positivity
  have hA : 0 < z.re ^ 2 - z.im ^ 2 + 2 := by nlinarith [sq_nonneg z.re]
  have hB : 0 < Real.cos (z.im / 2) ^ 2 + Real.sinh (z.re / 2) ^ 2 * Real.cos z.im := by
    have := mul_nonneg (sq_nonneg (Real.sinh (z.re / 2))) hcos.le
    linarith
  have hC : 0 ≤ (z.re * Real.sinh z.re) * (z.im * Real.sin z.im) :=
    mul_nonneg (self_mul_sinh_nonneg _) (self_mul_sin_nonneg hz)
  nlinarith [mul_pos hA hB]

/-- **The Klein–Gordon energy density `(z² + 2) sech²(z/2)` has positive real part on the strip.** -/
theorem re_energyDensity_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < ((z ^ 2 + 2) * specSq sechHalf z).re := by
  rw [specSq_sechHalf_eq_inv_cosh_sq, Complex.inv_def, ← mul_assoc, Complex.re_mul_ofReal]
  have hne : Complex.cosh (z / 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (cosh_half_ne_zero (by linarith))
  have hpos : 0 < (Complex.normSq (Complex.cosh (z / 2) ^ 2))⁻¹ :=
    inv_pos.mpr (Complex.normSq_pos.mpr hne)
  exact mul_pos (re_sq_add_two_mul_conj_cosh_half_sq_pos hz) hpos

/-- The energy term of a zero, `m_ρ Re(ρ_ρ² w_ρ)`, is positive. -/
def kgEnergyTerm (ρ : zetaZeroConfig.carrier) : ℝ :=
  (zetaZeroConfig.mult ρ : ℝ) * (kgFreq ρ ^ 2 * kgWeight ρ).re

theorem re_kgFreq_sq_mul_kgWeight_pos (ρ : zetaZeroConfig.carrier) :
    0 < (kgFreq ρ ^ 2 * kgWeight ρ).re := by
  rw [kgFreq_sq]
  exact re_energyDensity_pos (abs_im_gammaOf_lt ρ)

theorem kgEnergyTerm_pos (ρ : zetaZeroConfig.carrier) : 0 < kgEnergyTerm ρ := by
  unfold kgEnergyTerm
  have h1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ ρ.2
  exact mul_pos (by linarith) (re_kgFreq_sq_mul_kgWeight_pos ρ)

/-! ## Section 2: Polynomial-weighted densities are good densities; the quartic mass -/

theorem norm_rhoC_le (z : ℂ) : ‖rhoC z‖ ≤ ‖z‖ + 2 := by
  have h1 : ‖rhoC z‖ ^ 2 = ‖z ^ 2 + 2‖ := by rw [← norm_pow, rhoC_sq]
  have h2 : ‖z ^ 2 + 2‖ ≤ ‖z‖ ^ 2 + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
  have h3 : ‖rhoC z‖ ^ 2 ≤ (‖z‖ + 2) ^ 2 := by nlinarith [norm_nonneg z]
  exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2

/-- Fourth powers are dominated by every exponential: `t⁴ ≤ (24 / δ⁴) e^{δ t}` for `t ≥ 0`. -/
theorem pow_four_le_exp {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ 4 ≤ 24 / δ ^ 4 * Real.exp (δ * t) := by
  have h := Real.pow_div_factorial_le_exp (δ * t) (by positivity) 4
  have hfac : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at h
  have hδ4 : 0 < δ ^ 4 := by positivity
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 24)] at h
  calc t ^ 4 = (δ * t) ^ 4 / δ ^ 4 := by field_simp
    _ ≤ Real.exp (δ * t) * 24 / δ ^ 4 := by gcongr
    _ = 24 / δ ^ 4 * Real.exp (δ * t) := by ring

/-- A quartic polynomial is dominated by every exponential. -/
theorem exists_quartic_le_exp {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → 2 * (t + 5 / 4) ^ 4 + 8 ≤ K * Real.exp (δ * t) := by
  refine ⟨16 * (24 / δ ^ 4) + (16 * (5 / 4) ^ 4 + 8), by positivity, fun t ht => ?_⟩
  have h1 := pow_four_le_exp hδ ht
  have hab : (t + 5 / 4) ^ 2 ≤ 2 * t ^ 2 + 2 * (5 / 4) ^ 2 := by
    nlinarith [sq_nonneg (t - 5 / 4)]
  have hab2 : ((t + 5 / 4) ^ 2) ^ 2 ≤ (2 * t ^ 2 + 2 * (5 / 4) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hab 2
  have h2 : (t + 5 / 4) ^ 4 ≤ 8 * t ^ 4 + 8 * (5 / 4) ^ 4 := by
    have e : ((t + 5 / 4) ^ 2) ^ 2 = (t + 5 / 4) ^ 4 := by ring
    rw [e] at hab2
    nlinarith [sq_nonneg (t ^ 2 - (5 / 4) ^ 2)]
  have h3 : 1 ≤ Real.exp (δ * t) := by
    rw [Real.one_le_exp_iff]; positivity
  have hK : 0 ≤ 16 * (5 / 4 : ℝ) ^ 4 + 8 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hK]

theorem norm_sq_add_two_sq_le {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    ‖(z ^ 2 + 2) ^ 2‖ ≤ 2 * (|z.re| + 5 / 4) ^ 4 + 8 := by
  rw [norm_pow]
  have h1 : ‖z ^ 2 + 2‖ ≤ ‖z‖ ^ 2 + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
  have h2 : ‖z‖ ≤ |z.re| + 5 / 4 :=
    (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  have h3 : ‖z‖ ^ 2 ≤ (|z.re| + 5 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 : ‖z ^ 2 + 2‖ ^ 2 ≤ (‖z‖ ^ 2 + 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h5 : (‖z‖ ^ 2 + 2) ^ 2 ≤ 2 * (‖z‖ ^ 2) ^ 2 + 8 := by
    nlinarith [sq_nonneg (‖z‖ ^ 2 - 2)]
  have h6 : (‖z‖ ^ 2) ^ 2 ≤ ((|z.re| + 5 / 4) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h7 : ((|z.re| + 5 / 4) ^ 2) ^ 2 = (|z.re| + 5 / 4) ^ 4 := by ring
  linarith

theorem norm_rhoC_mul_le (z : ℂ) (hz : |z.im| ≤ 5 / 4) : ‖rhoC z‖ ≤ |z.re| + 13 / 4 := by
  have := norm_rhoC_le z
  have h2 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  linarith

/-- The spectral density `(z² + 2)² sech²(z/2)` is a good density. -/
theorem goodDensity_sq_add_two_sq_mul_specSq_sechHalf :
    GoodDensity (fun z : ℂ => (z ^ 2 + 2) ^ 2 * specSq sechHalf z) := by
  obtain ⟨ε, C, hε, hs⟩ := evenStrip_sechHalf.strip
  have hC := hs.const_nonneg (by norm_num)
  obtain ⟨K, hK, hKb⟩ := exists_quartic_le_exp (show 0 < ε / 2 by positivity)
  refine ⟨⟨3 * ε / 2, K * C ^ 2, by positivity, fun z hz => ?_, fun z hz => ?_⟩,
    fun z => ?_, fun r => ?_⟩
  · exact (((differentiableAt_id.pow 2).add (differentiableAt_const _)).pow 2).mul
      (differentiableAt_specSq hs hz)
  · show ‖(z ^ 2 + 2) ^ 2 * specSq sechHalf z‖ ≤ K * C ^ 2 * Real.exp (-(3 * ε / 2 * |z.re|))
    rw [norm_mul]
    have h1 := norm_sq_add_two_sq_le hz
    have h2 := norm_specSq_le hs hz
    have h3 := hKb |z.re| (abs_nonneg _)
    have hexp : Real.exp (ε / 2 * |z.re|) * Real.exp (-(2 * ε * |z.re|)) =
        Real.exp (-(3 * ε / 2 * |z.re|)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖(z ^ 2 + 2) ^ 2‖ * ‖specSq sechHalf z‖
        ≤ (2 * (|z.re| + 5 / 4) ^ 4 + 8) * (C ^ 2 * Real.exp (-(2 * ε * |z.re|))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (K * Real.exp (ε / 2 * |z.re|)) * (C ^ 2 * Real.exp (-(2 * ε * |z.re|))) := by
          gcongr
      _ = K * C ^ 2 * Real.exp (-(3 * ε / 2 * |z.re|)) := by rw [← hexp]; ring
  · show ((-z) ^ 2 + 2) ^ 2 * specSq sechHalf (-z) = (z ^ 2 + 2) ^ 2 * specSq sechHalf z
    rw [neg_sq, specSq_neg_of_even evenStrip_sechHalf.even]
  · show (((r : ℂ) ^ 2 + 2) ^ 2 * specSq sechHalf r).im = 0
    rw [show ((r : ℂ) ^ 2 + 2) ^ 2 = (((r ^ 2 + 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.im_ofReal_mul, specSq_im_ofReal, mul_zero]

/-- The quartic mass `Σ_ρ m_ρ ‖w_ρ‖ ‖ρ_ρ‖⁴` is finite. -/
theorem summable_quartic :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4) := by
  have h := summable_zeroSide_of_goodDensity goodDensity_sq_add_two_sq_mul_specSq_sechHalf
  have h2 := summable_norm_iff.mpr h
  refine h2.congr fun ρ => ?_
  show ‖(zetaZeroConfig.mult ρ : ℂ) *
      ((Zeta23.gammaOf (ρ : ℂ) ^ 2 + 2) ^ 2 * specSq sechHalf (Zeta23.gammaOf (ρ : ℂ)))‖ = _
  rw [norm_mul, Complex.norm_natCast, norm_mul, norm_pow, ← kgFreq_sq, norm_pow]
  unfold CHMDGrowthCollapse.kgWeight
  ring

/-- The quartic mass of the zero measure. -/
def kgQuarticMass : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4)

theorem kgQuarticMass_nonneg : 0 ≤ kgQuarticMass :=
  tsum_nonneg fun _ => by positivity

theorem kgEnergyTerm_le (ρ : zetaZeroConfig.carrier) :
    kgEnergyTerm ρ ≤ (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * (1 + ‖kgFreq ρ‖ ^ 4)) := by
  unfold kgEnergyTerm
  have h1 : (kgFreq ρ ^ 2 * kgWeight ρ).re ≤ ‖kgFreq ρ‖ ^ 2 * ‖kgWeight ρ‖ := by
    calc (kgFreq ρ ^ 2 * kgWeight ρ).re ≤ ‖kgFreq ρ ^ 2 * kgWeight ρ‖ := Complex.re_le_norm _
      _ = ‖kgFreq ρ‖ ^ 2 * ‖kgWeight ρ‖ := by rw [norm_mul, norm_pow]
  have h2 : ‖kgFreq ρ‖ ^ 2 ≤ 1 + ‖kgFreq ρ‖ ^ 4 := by
    nlinarith [sq_nonneg (‖kgFreq ρ‖ ^ 2 - 1)]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hw : 0 ≤ ‖kgWeight ρ‖ := norm_nonneg _
  calc (zetaZeroConfig.mult ρ : ℝ) * (kgFreq ρ ^ 2 * kgWeight ρ).re
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (‖kgFreq ρ‖ ^ 2 * ‖kgWeight ρ‖) :=
        mul_le_mul_of_nonneg_left h1 hm
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * (1 + ‖kgFreq ρ‖ ^ 4)) := by
        apply mul_le_mul_of_nonneg_left _ hm
        nlinarith [mul_le_mul_of_nonneg_left h2 hw]

theorem summable_kgEnergyTerm : Summable kgEnergyTerm := by
  refine Summable.of_nonneg_of_le (fun ρ => (kgEnergyTerm_pos ρ).le) kgEnergyTerm_le ?_
  have h1 := summable_mult_mul_norm_kgWeight
  have h2 := summable_quartic
  refine (h1.add h2).congr fun ρ => ?_
  ring

/-- The windowed energy sum `E_y = Σ_{|y ρ_ρ| ≤ 1} m_ρ Re(ρ_ρ² w_ρ)`. -/
def windowedEnergy (y : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, if |y| * ‖kgFreq ρ‖ ≤ 1 then kgEnergyTerm ρ else 0

theorem windowedEnergy_term_nonneg (y : ℝ) (ρ : zetaZeroConfig.carrier) :
    0 ≤ if |y| * ‖kgFreq ρ‖ ≤ 1 then kgEnergyTerm ρ else 0 := by
  split_ifs
  · exact (kgEnergyTerm_pos ρ).le
  · exact le_rfl

theorem summable_windowedEnergy_term (y : ℝ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      if |y| * ‖kgFreq ρ‖ ≤ 1 then kgEnergyTerm ρ else 0 := by
  refine Summable.of_nonneg_of_le (windowedEnergy_term_nonneg y) (fun ρ => ?_)
    summable_kgEnergyTerm
  split_ifs
  · exact le_rfl
  · exact (kgEnergyTerm_pos ρ).le

theorem windowedEnergy_nonneg (y : ℝ) : 0 ≤ windowedEnergy y :=
  tsum_nonneg (windowedEnergy_term_nonneg y)

/-! ## Section 3: Second-order expansion with explicit remainder, and the origin maximum -/

/-- One-mode lower bound: for `|y| ≤ 1/2`,
`m Re(w (1 − cos(y ρ))) ≥ 1_{|yρ| ≤ 1} · (y²/2) m Re(ρ² w) − 3 y⁴ m ‖w‖ ‖ρ‖⁴`. -/
theorem mode_lower_bound {y : ℝ} (hy : |y| ≤ 1 / 2) (ρ : zetaZeroConfig.carrier) :
    (if |y| * ‖kgFreq ρ‖ ≤ 1 then kgEnergyTerm ρ else 0) * (y ^ 2 / 2) -
        3 * y ^ 4 * ((zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4)) ≤
      (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ * (1 - Complex.cos (y * kgFreq ρ))).re := by
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hw : 0 ≤ ‖kgWeight ρ‖ := norm_nonneg _
  set x : ℂ := y * kgFreq ρ with hx
  have hxn : ‖x‖ = |y| * ‖kgFreq ρ‖ := by
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with hsmall
  · -- the low regime: Taylor with the `cos_bound` remainder
    have hx1 : ‖x‖ ≤ 1 := by rw [hxn]; exact hsmall
    have hcb := Complex.cos_bound hx1
    have hdecomp : kgWeight ρ * (1 - Complex.cos x) =
        kgWeight ρ * (x ^ 2 / 2) - kgWeight ρ * (Complex.cos x - (1 - x ^ 2 / 2)) := by ring
    have hx2 : kgWeight ρ * (x ^ 2 / 2) = ((y ^ 2 / 2 : ℝ) : ℂ) * (kgFreq ρ ^ 2 * kgWeight ρ) := by
      rw [hx]; push_cast; ring
    rw [hdecomp, Complex.sub_re, hx2, Complex.re_ofReal_mul]
    have hrem : |(kgWeight ρ * (Complex.cos x - (1 - x ^ 2 / 2))).re| ≤
        ‖kgWeight ρ‖ * (‖x‖ ^ 4 * (5 / 96)) := by
      calc |(kgWeight ρ * (Complex.cos x - (1 - x ^ 2 / 2))).re|
          ≤ ‖kgWeight ρ * (Complex.cos x - (1 - x ^ 2 / 2))‖ := Complex.abs_re_le_norm _
        _ = ‖kgWeight ρ‖ * ‖Complex.cos x - (1 - x ^ 2 / 2)‖ := norm_mul _ _
        _ ≤ ‖kgWeight ρ‖ * (‖x‖ ^ 4 * (5 / 96)) := mul_le_mul_of_nonneg_left hcb hw
    have hy4abs : |y| ^ 4 = y ^ 4 := by
      rw [← abs_pow]; exact abs_of_nonneg (by positivity)
    have hx4 : ‖x‖ ^ 4 = y ^ 4 * ‖kgFreq ρ‖ ^ 4 := by
      rw [hxn, mul_pow, hy4abs]
    rw [hx4] at hrem
    have hrem' := (abs_le.mp hrem).2
    unfold kgEnergyTerm
    have hy4 : 0 ≤ y ^ 4 * ‖kgFreq ρ‖ ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hrem' hm, mul_nonneg hm (mul_nonneg hw hy4)]
  · -- the high regime: `|yρ| > 1`, crude bound
    have hbig : 1 < |y| * ‖kgFreq ρ‖ := not_le.mp hsmall
    have hcos : ‖Complex.cos x‖ ≤ 2 := by
      refine (norm_ccos_le_exp_abs_im _).trans ?_
      have him : |x.im| ≤ 1 / 4 := by
        rw [hx, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]
        have := (abs_im_kgFreq_lt ρ).le
        have hy0 := abs_nonneg y
        nlinarith [abs_nonneg (kgFreq ρ).im]
      calc Real.exp |x.im| ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr him
        _ ≤ 2 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp (1 / 4) ^ 4 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          nlinarith [Real.exp_pos (1 / 4), sq_nonneg (Real.exp (1 / 4)),
            sq_nonneg (Real.exp (1 / 4) ^ 2 - 2)]
    have h1 : |(kgWeight ρ * (1 - Complex.cos x)).re| ≤ ‖kgWeight ρ‖ * 3 := by
      calc |(kgWeight ρ * (1 - Complex.cos x)).re|
          ≤ ‖kgWeight ρ * (1 - Complex.cos x)‖ := Complex.abs_re_le_norm _
        _ = ‖kgWeight ρ‖ * ‖1 - Complex.cos x‖ := norm_mul _ _
        _ ≤ ‖kgWeight ρ‖ * 3 := by
            apply mul_le_mul_of_nonneg_left _ hw
            calc ‖1 - Complex.cos x‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.cos x‖ := norm_sub_le _ _
              _ ≤ 1 + 2 := by rw [norm_one]; linarith
              _ = 3 := by norm_num
    have h2 := (abs_le.mp h1).1
    have hx4 : 1 ≤ y ^ 4 * ‖kgFreq ρ‖ ^ 4 := by
      have : 1 ≤ (|y| * ‖kgFreq ρ‖) ^ 4 := one_le_pow₀ hbig.le
      have hy4abs : |y| ^ 4 = y ^ 4 := by
        rw [← abs_pow]; exact abs_of_nonneg (by positivity)
      rwa [mul_pow, hy4abs] at this
    have hy4 : 0 ≤ y ^ 4 * ‖kgFreq ρ‖ ^ 4 := by positivity
    rw [zero_mul, zero_sub]
    nlinarith [mul_le_mul_of_nonneg_left h2 hm, mul_nonneg hm hw,
      mul_le_mul_of_nonneg_left hx4 (mul_nonneg hm hw)]

theorem summable_oneMinusCosTerm (y : ℝ) :
    Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ * (1 - Complex.cos (y * kgFreq ρ))).re := by
  have h0 := summable_re_cosTerm 0
  have hy := summable_re_cosTerm y
  refine (h0.sub hy).congr fun ρ => ?_
  have e0 : Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) = 1 := by simp
  have e1 : (kgWeight ρ * (1 - Complex.cos (y * kgFreq ρ))).re =
      (Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re -
        (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re := by
    rw [e0, one_mul, ← Complex.sub_re]; congr 1; ring
  rw [e1]; ring

theorem chmdWave_zero_sub_eq_tsum (y : ℝ) :
    chmdWave 0 - chmdWave y = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (kgWeight ρ * (1 - Complex.cos (y * kgFreq ρ))).re := by
  rw [chmdWave_eq_tsum_re 0, chmdWave_eq_tsum_re y,
    ← (summable_re_cosTerm 0).tsum_sub (summable_re_cosTerm y)]
  refine tsum_congr fun ρ => ?_
  have e0 : Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) = 1 := by simp
  have e1 : (kgWeight ρ * (1 - Complex.cos (y * kgFreq ρ))).re =
      (Complex.cos (((0 : ℝ) : ℂ) * kgFreq ρ) * kgWeight ρ).re -
        (Complex.cos (y * kgFreq ρ) * kgWeight ρ).re := by
    rw [e0, one_mul, ← Complex.sub_re]; congr 1; ring
  rw [e1]; ring

/-- **Second-order expansion of the causal wave at the origin with explicit remainder**:
for `|y| ≤ 1/2`, `φ_Λ(0) − φ_Λ(y) ≥ (y²/2) E_y − 3 y⁴ Q`. -/
theorem chmdWave_zero_sub_ge {y : ℝ} (hy : |y| ≤ 1 / 2) :
    windowedEnergy y * (y ^ 2 / 2) - 3 * y ^ 4 * kgQuarticMass ≤ chmdWave 0 - chmdWave y := by
  rw [chmdWave_zero_sub_eq_tsum]
  have hA : Summable fun ρ : zetaZeroConfig.carrier =>
      (if |y| * ‖kgFreq ρ‖ ≤ 1 then kgEnergyTerm ρ else 0) * (y ^ 2 / 2) :=
    (summable_windowedEnergy_term y).mul_right _
  have hB : Summable fun ρ : zetaZeroConfig.carrier =>
      3 * y ^ 4 * ((zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4)) :=
    summable_quartic.mul_left _
  have hsum : windowedEnergy y * (y ^ 2 / 2) - 3 * y ^ 4 * kgQuarticMass =
      ∑' ρ : zetaZeroConfig.carrier,
        ((if |y| * ‖kgFreq ρ‖ ≤ 1 then kgEnergyTerm ρ else 0) * (y ^ 2 / 2) -
          3 * y ^ 4 * ((zetaZeroConfig.mult ρ : ℝ) * (‖kgWeight ρ‖ * ‖kgFreq ρ‖ ^ 4))) := by
    unfold windowedEnergy kgQuarticMass
    rw [← tsum_mul_right, ← tsum_mul_left, hA.tsum_sub hB]
  rw [hsum]
  exact Summable.tsum_le_tsum (fun ρ => mode_lower_bound hy ρ) (hA.sub hB)
    (summable_oneMinusCosTerm y)

theorem chmdWave_eq_zero_of_isEmpty [IsEmpty zetaZeroConfig.carrier] (y : ℝ) : chmdWave y = 0 := by
  rw [chmdWave_eq_tsum_re]; exact tsum_empty

/-- **The origin maximum principle**: there is `y₀ > 0` with `φ_Λ(y) ≤ φ_Λ(0)` for all `|y| ≤ y₀`,
unconditionally. -/
theorem exists_origin_maximum :
    ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ y : ℝ, |y| ≤ y₀ → chmdWave y ≤ chmdWave 0 := by
  rcases isEmpty_or_nonempty zetaZeroConfig.carrier with hempty | hne
  · exact ⟨1, one_pos, fun y _ => by rw [chmdWave_eq_zero_of_isEmpty y, chmdWave_eq_zero_of_isEmpty 0]⟩
  · haveI := hne
    let ρ₀ : zetaZeroConfig.carrier := Classical.arbitrary _
    set M : ℝ := kgEnergyTerm ρ₀ with hM
    have hMpos : 0 < M := kgEnergyTerm_pos ρ₀
    set R : ℝ := ‖kgFreq ρ₀‖ with hR
    have hRpos : 0 < R := by
      rw [hR, norm_pos_iff]; intro h
      have := re_kgFreq_pos ρ₀; rw [h] at this; simp at this
    set Q : ℝ := kgQuarticMass with hQ
    have hQ0 : 0 ≤ Q := kgQuarticMass_nonneg
    set y₀ : ℝ := min (min (1 / 2) (1 / R)) (Real.sqrt (M / (6 * (Q + 1)))) with hy₀
    have hy₀pos : 0 < y₀ :=
      lt_min (lt_min (by norm_num) (by positivity)) (Real.sqrt_pos.mpr (by positivity))
    refine ⟨y₀, hy₀pos, fun y hy => ?_⟩
    have hy1 : |y| ≤ 1 / 2 := hy.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hy2 : |y| ≤ 1 / R := hy.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hy3 : |y| ≤ Real.sqrt (M / (6 * (Q + 1))) := hy.trans (min_le_right _ _)
    have hy3' : y ^ 2 ≤ M / (6 * (Q + 1)) := by
      have h := Real.sqrt_le_sqrt (show 0 ≤ M / (6 * (Q + 1)) by positivity)
      have h2 : |y| ^ 2 ≤ Real.sqrt (M / (6 * (Q + 1))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hy3 2
      rwa [sq_abs, Real.sq_sqrt (by positivity)] at h2
    -- the zero `ρ₀` is in the window, so `E_y ≥ M`
    have hwin : |y| * ‖kgFreq ρ₀‖ ≤ 1 := by
      rw [← hR]
      calc |y| * R ≤ (1 / R) * R := mul_le_mul_of_nonneg_right hy2 hRpos.le
        _ = 1 := by field_simp
    have hE : M ≤ windowedEnergy y := by
      have h := (summable_windowedEnergy_term y).le_tsum ρ₀
        (fun ρ _ => windowedEnergy_term_nonneg y ρ)
      rw [if_pos hwin] at h
      exact h
    have hmain := chmdWave_zero_sub_ge hy1
    have hy2' : 0 ≤ y ^ 2 := sq_nonneg y
    have hkey : 0 ≤ windowedEnergy y * (y ^ 2 / 2) - 3 * y ^ 4 * Q := by
      have h1 : 3 * y ^ 4 * Q ≤ y ^ 2 * (M / 2) * (Q / (Q + 1)) := by
        have : y ^ 4 = y ^ 2 * y ^ 2 := by ring
        rw [this]
        have h2 : 3 * y ^ 2 * Q ≤ M / 2 * (Q / (Q + 1)) := by
          calc 3 * y ^ 2 * Q ≤ 3 * (M / (6 * (Q + 1))) * Q := by gcongr
            _ = M / 2 * (Q / (Q + 1)) := by field_simp; ring
        nlinarith
      have h3 : y ^ 2 * (M / 2) * (Q / (Q + 1)) ≤ y ^ 2 * (M / 2) := by
        apply mul_le_of_le_one_right (by positivity)
        rw [div_le_one (by positivity)]; linarith
      have h4 : y ^ 2 * (M / 2) ≤ windowedEnergy y * (y ^ 2 / 2) := by
        have := mul_le_mul_of_nonneg_right hE (by positivity : (0 : ℝ) ≤ y ^ 2 / 2)
        linarith
      linarith
    linarith

/-- **Two-point difference packets with small shift are nonnegative**, unconditionally. -/
theorem exists_twoPointDiff_nonneg_near_origin :
    ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ y : ℝ, |y| ≤ y₀ →
      0 ≤ ∑ i, ∑ j, twoPointDiffCoeff i * twoPointDiffCoeff j *
        cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf
          (twoPointShift y j - twoPointShift y i) := by
  obtain ⟨y₀, hy₀, h⟩ := exists_origin_maximum
  refine ⟨y₀, hy₀, fun y hy => ?_⟩
  rw [sum_sum_twoPointDiff_cosineShiftFn]
  have := h y hy
  change chmdWave y ≤ chmdWave 0 at this
  change (0 : ℝ) ≤ 2 * (chmdWave 0 - chmdWave y)
  linarith

/-! ## Section 4: The energy moment and the energy-weighted explicit-formula inequality -/

/-- The Klein–Gordon energy moment `Σ_ρ m_ρ Re(ρ_ρ² w_ρ)` of the zero measure. -/
def kgEnergyMoment : ℝ := ∑' ρ : zetaZeroConfig.carrier, kgEnergyTerm ρ

theorem kgEnergyMoment_nonneg : 0 ≤ kgEnergyMoment :=
  tsum_nonneg fun ρ => (kgEnergyTerm_pos ρ).le

theorem kgEnergyMoment_pos [Nonempty zetaZeroConfig.carrier] : 0 < kgEnergyMoment := by
  let ρ₀ : zetaZeroConfig.carrier := Classical.arbitrary _
  have h := summable_kgEnergyTerm.le_tsum ρ₀ (fun ρ _ => (kgEnergyTerm_pos ρ).le)
  exact (kgEnergyTerm_pos ρ₀).trans_le h

/-- The energy test function `rhoC · sechHalf`. -/
def energyTest (z : ℂ) : ℂ := rhoC z * sechHalf z

theorem evenStrip_energyTest : EvenStrip energyTest := by
  obtain ⟨ε, C, hε, hs⟩ := evenStrip_sechHalf.strip
  have hC := hs.const_nonneg (by norm_num)
  refine ⟨⟨ε / 2, (2 / (ε / 2) + 13 / 4) * C, by positivity, fun z hz => ?_, fun z hz => ?_⟩,
    fun z => ?_, fun r => ?_⟩
  · exact (differentiableAt_rhoC (abs_im_lt_sqrt_two hz)).mul (hs.diff z hz)
  · unfold energyTest
    rw [norm_mul]
    have h1 := norm_rhoC_mul_le z hz
    have h2 := hs.bound z hz
    have hδ : 0 < ε / 2 := by positivity
    have h3 : |z.re| ≤ 2 / (ε / 2) * Real.exp (ε / 2 * |z.re|) := by
      have h4 : ε / 2 * |z.re| ≤ Real.exp (ε / 2 * |z.re|) := by
        linarith [Real.add_one_le_exp (ε / 2 * |z.re|)]
      have h5 : |z.re| ≤ Real.exp (ε / 2 * |z.re|) / (ε / 2) := by
        rw [le_div_iff₀ hδ]; linarith
      have h6 : Real.exp (ε / 2 * |z.re|) / (ε / 2) ≤ 2 / (ε / 2) * Real.exp (ε / 2 * |z.re|) := by
        rw [show 2 / (ε / 2) * Real.exp (ε / 2 * |z.re|) =
          2 * (Real.exp (ε / 2 * |z.re|) / (ε / 2)) by ring]
        have : 0 ≤ Real.exp (ε / 2 * |z.re|) / (ε / 2) := by positivity
        linarith
      exact h5.trans h6
    have h5 : (13 / 4 : ℝ) ≤ 13 / 4 * Real.exp (ε / 2 * |z.re|) := by
      have : 1 ≤ Real.exp (ε / 2 * |z.re|) := by
        rw [Real.one_le_exp_iff]; positivity
      nlinarith
    have hexp : Real.exp (ε / 2 * |z.re|) * Real.exp (-(ε * |z.re|)) =
        Real.exp (-(ε / 2 * |z.re|)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖rhoC z‖ * ‖sechHalf z‖ ≤ (|z.re| + 13 / 4) * (C * Real.exp (-(ε * |z.re|))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ ((2 / (ε / 2) + 13 / 4) * Real.exp (ε / 2 * |z.re|)) * (C * Real.exp (-(ε * |z.re|))) := by
          gcongr
          linarith
      _ = (2 / (ε / 2) + 13 / 4) * C * Real.exp (-(ε / 2 * |z.re|)) := by
          rw [← hexp]; ring
  · unfold energyTest; rw [rhoC_neg, evenStrip_sechHalf.even]
  · unfold energyTest
    rw [Complex.mul_im, rhoC_ofReal, Complex.ofReal_im, Complex.ofReal_re, evenStrip_sechHalf.real]
    ring

theorem specSq_energyTest {z : ℂ} (hz : |z.im| < Real.sqrt 2) :
    specSq energyTest z = (z ^ 2 + 2) * specSq sechHalf z := by
  unfold specSq energyTest
  rw [rhoC_conj hz, map_mul, Complex.conj_conj, ← rhoC_sq]
  ring

/-- **The energy moment is the even Weil functional of the energy density.** -/
theorem kgEnergyMoment_eq_evenWeilDensity :
    kgEnergyMoment =
      evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (specSq energyTest) := by
  rw [evenWeilDensity_specSq_vonMangoldt_eq_tsum_re evenStrip_energyTest]
  unfold kgEnergyMoment kgEnergyTerm
  refine tsum_congr fun ρ => ?_
  rw [specSq_energyTest (abs_im_lt_sqrt_two (by linarith [abs_im_gammaOf_lt ρ])), ← kgFreq_sq]
  rfl

/-- **The energy-weighted explicit-formula inequality**, unconditional:
`Σ_{n ≥ 2} (Λ(n)/√n) (1/π) ∫ (r² + 2) sech²(r/2) cos(r log n) dr ≤ 7/(2 cos²(1/4)) + (1/2π) ∫ (r² + 2) sech²(r/2) γ(r) dr`. -/
theorem prime_energy_le_pole_add_arch :
    (∑' n : ℕ,
      (if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0) *
        (1 / Real.pi * ∫ r : ℝ, ((r ^ 2 + 2) * sechSqHalf r) * Real.cos (r * Real.log n))) ≤
      7 / (2 * Real.cos (1 / 4 : ℝ) ^ 2) +
        1 / (2 * Real.pi) * (∫ r : ℝ, ((r ^ 2 + 2) * sechSqHalf r) * EF.gammaBracket r) := by
  have h0 : 0 ≤ evenWeilDensity (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (specSq energyTest) := by
    rw [← kgEnergyMoment_eq_evenWeilDensity]; exact kgEnergyMoment_nonneg
  have hreal : ∀ r : ℝ, (specSq energyTest r).re = (r ^ 2 + 2) * sechSqHalf r := by
    intro r
    rw [specSq_energyTest (by rw [Complex.ofReal_im, abs_zero]; positivity),
      show ((r : ℂ) ^ 2 + 2) = ((r ^ 2 + 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul, specSq_sechHalf_ofReal_re]
  have hpole : (specSq energyTest (I / 2) + specSq energyTest (-I / 2)).re =
      7 / (2 * Real.cos (1 / 4 : ℝ) ^ 2) := by
    have hi : |(I / 2 : ℂ).im| < Real.sqrt 2 := by
      rw [Complex.div_ofNat_im, Complex.I_im, abs_of_pos (by norm_num)]
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hi' : |(-I / 2 : ℂ).im| < Real.sqrt 2 := by
      rw [show (-I / 2 : ℂ) = -(I / 2) by ring, Complex.neg_im, abs_neg]; exact hi
    rw [specSq_energyTest hi, specSq_energyTest hi',
      show ((I / 2 : ℂ) ^ 2 + 2) = ((7 / 4 : ℝ) : ℂ) by
        rw [div_pow, Complex.I_sq]; push_cast; ring,
      show ((-I / 2 : ℂ) ^ 2 + 2) = ((7 / 4 : ℝ) : ℂ) by
        rw [div_pow, neg_sq, Complex.I_sq]; push_cast; ring,
      ← mul_add, Complex.re_ofReal_mul]
    have := evenPolePart_specSq_sechHalf
    unfold evenPolePart at this
    rw [this]
    field_simp
    ring
  unfold evenWeilDensity at h0
  rw [hpole] at h0
  simp_rw [hreal] at h0
  linarith

end RHTower.CHMDEnergyPositivity

end
