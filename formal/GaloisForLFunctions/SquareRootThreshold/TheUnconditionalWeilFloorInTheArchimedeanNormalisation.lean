import GaloisForLFunctions.HTGeometry.NarrowPlateauSamplingAtDepth
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowNyquistExclusion
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime
import Zeta23.RvM.LocalCount
import Zeta23.Tail

/-!
# The Weil form is bounded below in the archimedean normalisation, unconditionally

The zero side of Weil's form is a sum of the squared transform over the zeros, and the
unconditional local zero count is logarithmic in the height.  Sampling at depth against a
logarithmic density (`HTGeometry.LocalSampling.sum_norm_sq_fourierAt_le`) therefore bounds the
whole zero side by the **logarithmically weighted** energy of the transform — the archimedean
weight — with no hypothesis on how the zeros are distributed:

`Re W(f, f) ≥ −C(a) ∫ ‖𝓕 f(y)‖² log(|y| + 3) dy`

for every `C²` test supported in `[−a, a]`.  The three inputs are the unconditional window count
`Zeta23.RvM.zetaZeroConfig_local_count`, the strip `0 ≤ β ≤ 1` (which bounds the depth), and the
sampling inequality; the term inequality `Re(u \bar v) ≥ −(|u|² + |v|²)/2` is all that is used of
the Weil summand.
-/

open MeasureTheory Set Real Complex
open scoped FourierTransform

namespace GaloisForLFunctions.SquareRootThreshold

open HTGeometry.LocalSampling

noncomputable section
set_option autoImplicit false

/-! ## The sample point of a zero -/

/-- The sample point of a zero in the convention of the localised sampling bound. -/
def spectralSample (ρ : ℂ) : ℂ := -(Zeta23.gammaOf ρ / (2 * π))

theorem div_ofReal_eq_smul (z : ℂ) {r : ℝ} (_hr : r ≠ 0) : z / ((r : ℝ) : ℂ) = (r⁻¹ : ℝ) • z := by
  rw [Complex.real_smul]
  push_cast
  field_simp

theorem paperFT_eq_fourierAt (f : ℝ → ℂ) (w : ℂ) :
    Zeta23.paperFT f w = fourierAt f (-(w / (2 * π))) := by
  have hpi : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Zeta23.paperFT, fourierAt, chi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  field_simp

theorem gammaOf_re (ρ : ℂ) : (Zeta23.gammaOf ρ).re = ρ.im := by
  simp [Zeta23.gammaOf, Complex.div_I]

theorem gammaOf_im (ρ : ℂ) : (Zeta23.gammaOf ρ).im = 1 / 2 - ρ.re := by
  simp [Zeta23.gammaOf, Complex.div_I]

theorem spectralSample_re (ρ : ℂ) : (spectralSample ρ).re = -(ρ.im / (2 * π)) := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  rw [spectralSample, show ((2:ℂ) * ((π : ℝ) : ℂ)) = (((2 * π : ℝ)) : ℂ) by push_cast; ring,
    div_ofReal_eq_smul _ hpi, Complex.neg_re, Complex.smul_re, gammaOf_re]
  simp only [smul_eq_mul]
  ring

theorem spectralSample_im (ρ : ℂ) : (spectralSample ρ).im = (ρ.re - 1 / 2) / (2 * π) := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [spectralSample, show ((2:ℂ) * ((π : ℝ) : ℂ)) = (((2 * π : ℝ)) : ℂ) by push_cast; ring,
    div_ofReal_eq_smul _ hpi, Complex.neg_im, Complex.smul_im, gammaOf_im]
  simp only [smul_eq_mul]
  ring

/-! ## From a unit-window count in the ordinate to a unit-window count in the sample point -/

/-- The unit-window count of the ordinates gives a unit-window count of the sample points, with
the constant inflated by the nine unit windows that cover one window of length `2π`. -/
theorem exists_count_spectralSample {ι : Type*} [DecidableEq ι] {γ : ι → ℝ} {m : ι → ℕ}
    {A₀ : ℝ} (h : Zeta23.Tail.LocalCount γ m A₀) :
    ∃ A₁ : ℝ, 0 ≤ A₁ ∧ ∀ (S : Finset ι) (n : ℤ),
      (∑ q ∈ S.filter fun q =>
          (n : ℝ) ≤ -(γ q / (2 * π)) ∧ -(γ q / (2 * π)) ≤ (n : ℝ) + 1, (m q : ℝ)) ≤
        A₁ * Real.log (|(n : ℝ)| + 3) := by
  classical
  have hA₀ : 0 < A₀ := h.A₀_pos
  have hpi0 : (0:ℝ) < 2 * π := by positivity
  have hpi8 : (2:ℝ) * π ≤ 8 := by linarith [Real.pi_le_four]
  have hlog3 : (1:ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_three]
  refine ⟨9 * A₀ * (1 + Real.log 8), by positivity, fun S n => ?_⟩
  set t₀ : ℝ := -(2 * π * ((n : ℝ) + 1)) - 1 with ht₀
  set F : Finset ι := S.filter fun q =>
    (n : ℝ) ≤ -(γ q / (2 * π)) ∧ -(γ q / (2 * π)) ≤ (n : ℝ) + 1 with hF
  have hlogn : (1:ℝ) ≤ Real.log (|(n : ℝ)| + 3) := by
    refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
    linarith [abs_nonneg ((n : ℝ))]
  -- members of `F` have ordinate in one window of length `2π`
  have hrange : ∀ q ∈ F, 1 ≤ γ q - t₀ ∧ γ q - t₀ ≤ 2 * π + 1 := by
    intro q hq
    rw [hF, Finset.mem_filter] at hq
    obtain ⟨-, h1, h2⟩ := hq
    have hdiv : -(γ q / (2 * π)) = (-γ q) / (2 * π) := by ring
    rw [hdiv] at h1 h2
    rw [le_div_iff₀ hpi0] at h1
    rw [div_le_iff₀ hpi0] at h2
    have hlow : -(2 * π * ((n : ℝ) + 1)) ≤ γ q := by nlinarith
    have hhigh : γ q ≤ -(2 * π * (n : ℝ)) := by nlinarith
    simp only [ht₀]
    constructor
    · linarith
    · nlinarith
  have hmaps : ∀ q ∈ F, (⌈γ q - t₀⌉ : ℤ) ∈ Finset.Icc (1 : ℤ) 9 := by
    intro q hq
    obtain ⟨h1, h2⟩ := hrange q hq
    rw [Finset.mem_Icc]
    refine ⟨Int.one_le_ceil_iff.mpr (by linarith), Int.ceil_le.mpr ?_⟩
    push_cast
    linarith [hpi8]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ Finset.Icc (1 : ℤ) 9,
      (∑ q ∈ F.filter fun q => (⌈γ q - t₀⌉ : ℤ) = j, (m q : ℝ)) ≤
        A₀ * (1 + Real.log 8) * Real.log (|(n : ℝ)| + 3) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hwin : ∀ q ∈ F.filter fun q => (⌈γ q - t₀⌉ : ℤ) = j,
        t₀ + ((j : ℝ) - 1) < γ q ∧ γ q ≤ t₀ + ((j : ℝ) - 1) + 1 := by
      intro q hq
      rw [Finset.mem_filter] at hq
      have hc : (⌈γ q - t₀⌉ : ℤ) = j := hq.2
      have hjc : ((j : ℤ) : ℝ) = ((⌈γ q - t₀⌉ : ℤ) : ℝ) := by rw [hc]
      have hup : γ q - t₀ ≤ (j : ℝ) := by
        rw [hjc]
        exact Int.le_ceil _
      have hlow : (j : ℝ) - 1 < γ q - t₀ := by
        rw [hjc]
        linarith [Int.ceil_lt_add_one (γ q - t₀)]
      exact ⟨by linarith, by linarith⟩
    refine (h.window (t₀ + ((j : ℝ) - 1)) (F.filter fun q => (⌈γ q - t₀⌉ : ℤ) = j) hwin).trans ?_
    have hj1 : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hj9 : (j : ℝ) ≤ 9 := by exact_mod_cast hj.2
    have habs : |t₀ + ((j : ℝ) - 1)| ≤ 8 * |(n : ℝ)| + 16 := by
      rw [ht₀]
      rcases abs_cases (-(2 * π * ((n : ℝ) + 1)) - 1 + ((j : ℝ) - 1)) with ⟨he, _⟩ | ⟨he, _⟩ <;>
        rw [he] <;>
        nlinarith [abs_nonneg ((n : ℝ)), le_abs_self ((n : ℝ)), neg_abs_le ((n : ℝ)), hpi8,
          Real.pi_pos]
    have hlogle : Real.log (|t₀ + ((j : ℝ) - 1)| + 3) ≤
        (1 + Real.log 8) * Real.log (|(n : ℝ)| + 3) := by
      have h1 : Real.log (|t₀ + ((j : ℝ) - 1)| + 3) ≤ Real.log (8 * (|(n : ℝ)| + 3)) := by
        refine Real.log_le_log (by positivity) ?_
        nlinarith [habs, abs_nonneg ((n : ℝ))]
      have h2 : Real.log (8 * (|(n : ℝ)| + 3)) = Real.log 8 + Real.log (|(n : ℝ)| + 3) :=
        Real.log_mul (by norm_num) (by positivity)
      have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
      nlinarith [h1, h2.le, h2.ge, hlogn, hl8]
    calc A₀ * Real.log (|t₀ + ((j : ℝ) - 1)| + 3)
        ≤ A₀ * ((1 + Real.log 8) * Real.log (|(n : ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hlogle hA₀.le
      _ = A₀ * (1 + Real.log 8) * Real.log (|(n : ℝ)| + 3) := by ring
  refine (Finset.sum_le_sum hfib).trans (le_of_eq ?_)
  rw [Finset.sum_const, Int.card_Icc]
  norm_num
  push_cast
  ring

/-! ## The floor -/

/-- The two sample points attached to a zero, and the depth bound coming from the strip. -/
theorem abs_spectralSample_im_le {ρ : ℂ} (h : ρ ∈ Zeta23.zetaZeroConfig.carrier) :
    |(spectralSample ρ).im| ≤ 1 / (4 * π) := by
  obtain ⟨h0, h1⟩ := Zeta23.zetaZeroConfig.strip ρ h
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hnum : |ρ.re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [spectralSample_im, abs_div, abs_of_pos hpi, div_le_iff₀ hpi,
    show (1:ℝ) / (4 * π) * (2 * π) = 1 / 2 by field_simp; ring]
  exact hnum

/-- Each Weil summand is bounded below by the squared transforms at the two sample points. -/
theorem re_Wsummand_ge (f : ℝ → ℂ) (ρ : ℂ) :
    -(((Zeta23.zetaZeroConfig.mult ρ : ℝ)) / 2 *
        (‖fourierAt f (spectralSample ρ)‖ ^ 2 +
          ‖fourierAt f ((starRingEnd ℂ) (spectralSample ρ))‖ ^ 2)) ≤
      (Zeta23.zetaZeroConfig.Wsummand f f ρ).re := by
  set u : ℂ := Zeta23.paperFT f (Zeta23.gammaOf ρ) with hu
  set v : ℂ := Zeta23.paperFT f ((starRingEnd ℂ) (Zeta23.gammaOf ρ)) with hv
  have hue : u = fourierAt f (spectralSample ρ) := by
    rw [hu, paperFT_eq_fourierAt, spectralSample]
  have hconjarg : (starRingEnd ℂ) (spectralSample ρ) =
      -((starRingEnd ℂ) (Zeta23.gammaOf ρ) / (2 * π)) := by
    rw [spectralSample, map_neg, map_div₀]
    congr 1
    simp [map_ofNat]
  have hve : v = fourierAt f ((starRingEnd ℂ) (spectralSample ρ)) := by
    rw [hv, paperFT_eq_fourierAt, hconjarg]
  have hre : (Zeta23.zetaZeroConfig.Wsummand f f ρ).re =
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) * (u * (starRingEnd ℂ) v).re := by
    rw [Zeta23.ZeroConfig.Wsummand, ← hu, ← hv]
    rw [show ((Zeta23.zetaZeroConfig.mult ρ : ℂ) * u * (starRingEnd ℂ) v) =
      ((Zeta23.zetaZeroConfig.mult ρ : ℝ) : ℂ) * (u * (starRingEnd ℂ) v) by push_cast; ring]
    rw [Complex.re_ofReal_mul]
  have hbd : -((‖u‖ ^ 2 + ‖v‖ ^ 2) / 2) ≤ (u * (starRingEnd ℂ) v).re := by
    have h1 : |(u * (starRingEnd ℂ) v).re| ≤ ‖u * (starRingEnd ℂ) v‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖u * (starRingEnd ℂ) v‖ = ‖u‖ * ‖v‖ := by
      rw [norm_mul, RCLike.norm_conj]
    have h3 : ‖u‖ * ‖v‖ ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
    have h5 : ‖u * (starRingEnd ℂ) v‖ ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := le_trans (le_of_eq h2) h3
    have h4 := abs_le.mp (h1.trans h5)
    linarith [h4.1]
  have hm : (0:ℝ) ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) := Nat.cast_nonneg _
  rw [← hue, ← hve, hre]
  calc -(((Zeta23.zetaZeroConfig.mult ρ : ℝ)) / 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2))
      = (Zeta23.zetaZeroConfig.mult ρ : ℝ) * -((‖u‖ ^ 2 + ‖v‖ ^ 2) / 2) := by ring
    _ ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) * (u * (starRingEnd ℂ) v).re :=
        mul_le_mul_of_nonneg_left hbd hm

/-- The floor at a given depth bound and a given logarithmic density of the sample points. -/
private theorem floorCoreFrom {σ A₁ Csamp : ℝ}
    (hdepthAll : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, |(spectralSample ρ).im| ≤ σ)
    (hcount : ∀ (S : Finset Zeta23.zetaZeroConfig.carrier) (n : ℤ),
      (∑ q ∈ S.filter fun q : Zeta23.zetaZeroConfig.carrier =>
          (n : ℝ) ≤ -(((q : ℂ)).im / (2 * π)) ∧ -(((q : ℂ)).im / (2 * π)) ≤ (n : ℝ) + 1,
        (Zeta23.zetaZeroConfig.mult (q : ℂ) : ℝ)) ≤ A₁ * Real.log (|(n : ℝ)| + 3))
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hb : ∀ (s : Finset Zeta23.zetaZeroConfig.carrier)
        (pt : Zeta23.zetaZeroConfig.carrier → ℂ),
      (∀ ρ ∈ s, |(pt ρ).im| ≤ σ) →
      (∀ n : ℤ, (∑ ρ ∈ s.filter fun ρ : Zeta23.zetaZeroConfig.carrier =>
          (n : ℝ) ≤ (pt ρ).re ∧ (pt ρ).re ≤ (n : ℝ) + 1,
        (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) ≤ A₁ * Real.log (|(n : ℝ)| + 3)) →
      (∑ ρ ∈ s, (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) * ‖fourierAt f (pt ρ)‖ ^ 2) ≤
        Csamp * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) :
    -(Csamp * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
      (Zeta23.zetaZeroConfig.W f f).re := by
  classical
  set g : Zeta23.zetaZeroConfig.carrier → ℝ := fun ρ =>
    (Zeta23.zetaZeroConfig.mult ρ : ℝ) / 2 *
      (‖fourierAt f (spectralSample ρ)‖ ^ 2 +
        ‖fourierAt f ((starRingEnd ℂ) (spectralSample ρ))‖ ^ 2) with hg
  have hgnn : ∀ ρ, 0 ≤ g ρ := by
    intro ρ
    rw [hg]
    have : (0:ℝ) ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) := Nat.cast_nonneg _
    positivity
  have hpart : ∀ s : Finset Zeta23.zetaZeroConfig.carrier,
      (∑ ρ ∈ s, g ρ) ≤ Csamp * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3) := by
    intro s
    have hdepth : ∀ ρ ∈ s, |(spectralSample (ρ : ℂ)).im| ≤ σ := fun ρ _ => hdepthAll ρ ρ.2
    have hdepth' : ∀ ρ ∈ s, |((starRingEnd ℂ) (spectralSample (ρ : ℂ))).im| ≤ σ := by
      intro ρ hρ
      rw [Complex.conj_im, abs_neg]
      exact hdepth ρ hρ
    have hc1 : ∀ n : ℤ,
        (∑ ρ ∈ s.filter fun ρ : Zeta23.zetaZeroConfig.carrier =>
            (n : ℝ) ≤ (spectralSample (ρ : ℂ)).re ∧
            (spectralSample (ρ : ℂ)).re ≤ (n : ℝ) + 1,
          (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) ≤ A₁ * Real.log (|(n : ℝ)| + 3) := by
      intro n
      have h := hcount s n
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr ?_ fun ρ _ => rfl
      refine Finset.filter_congr fun ρ _ => ?_
      rw [spectralSample_re]
    have hc2 : ∀ n : ℤ,
        (∑ ρ ∈ s.filter fun ρ : Zeta23.zetaZeroConfig.carrier =>
            (n : ℝ) ≤ ((starRingEnd ℂ) (spectralSample (ρ : ℂ))).re ∧
            ((starRingEnd ℂ) (spectralSample (ρ : ℂ))).re ≤ (n : ℝ) + 1,
          (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) ≤ A₁ * Real.log (|(n : ℝ)| + 3) := by
      intro n
      refine le_trans (le_of_eq ?_) (hc1 n)
      refine Finset.sum_congr ?_ fun ρ _ => rfl
      refine Finset.filter_congr fun ρ _ => ?_
      rw [Complex.conj_re]
    have hb1 := hb s (fun ρ => spectralSample (ρ : ℂ)) hdepth hc1
    have hb2 := hb s (fun ρ => (starRingEnd ℂ) (spectralSample (ρ : ℂ))) hdepth' hc2
    have hsplit : (∑ ρ ∈ s, g ρ) =
        (∑ ρ ∈ s, (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
            ‖fourierAt f (spectralSample (ρ : ℂ))‖ ^ 2) / 2 +
          (∑ ρ ∈ s, (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
            ‖fourierAt f ((starRingEnd ℂ) (spectralSample (ρ : ℂ)))‖ ^ 2) / 2 := by
      have hpt : ∀ ρ ∈ s, g ρ =
          ((Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
              ‖fourierAt f (spectralSample (ρ : ℂ))‖ ^ 2 +
            (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
              ‖fourierAt f ((starRingEnd ℂ) (spectralSample (ρ : ℂ)))‖ ^ 2) / 2 := by
        intro ρ _
        rw [hg]
        ring
      rw [Finset.sum_congr rfl hpt, ← Finset.sum_div, Finset.sum_add_distrib, add_div]
    rw [hsplit]
    linarith [hb1, hb2]
  have hgsummable : Summable g := summable_of_sum_le (fun ρ => hgnn ρ) hpart
  have hWsummable : Summable fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f ρ :=
    RHTower.summable_Wsummand_of_contDiff_two hf hfc hf hfc
  have hreW : (Zeta23.zetaZeroConfig.W f f).re =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.Wsummand f f ρ).re := by
    rw [Zeta23.ZeroConfig.W]
    exact Complex.re_tsum hWsummable
  have hterm : ∀ ρ : Zeta23.zetaZeroConfig.carrier,
      -g ρ ≤ (Zeta23.zetaZeroConfig.Wsummand f f ρ).re := by
    intro ρ
    rw [hg]
    exact re_Wsummand_ge f ρ
  have htsum : (∑' ρ : Zeta23.zetaZeroConfig.carrier, -g ρ) ≤
      ∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.Wsummand f f ρ).re :=
    Summable.tsum_le_tsum hterm hgsummable.neg (hWsummable.map
      (Complex.reAddGroupHom) (Complex.continuous_re))
  rw [hreW]
  refine le_trans ?_ htsum
  rw [tsum_neg]
  have hle : (∑' ρ : Zeta23.zetaZeroConfig.carrier, g ρ) ≤
      Csamp * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3) :=
    hgsummable.tsum_le_of_sum_le hpart
  linarith

/-- The floor through the trapezoid of plateau `a` and support radius `3a`: the depth rate is
`6πaσ`. -/
private theorem floorCore {a σ A₁ : ℝ} (ha : 0 < a) (hA₁ : 0 ≤ A₁) (hσ0 : 0 ≤ σ)
    (hdepthAll : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, |(spectralSample ρ).im| ≤ σ)
    (hcount : ∀ (S : Finset Zeta23.zetaZeroConfig.carrier) (n : ℤ),
      (∑ q ∈ S.filter fun q : Zeta23.zetaZeroConfig.carrier =>
          (n : ℝ) ≤ -(((q : ℂ)).im / (2 * π)) ∧ -(((q : ℂ)).im / (2 * π)) ≤ (n : ℝ) + 1,
        (Zeta23.zetaZeroConfig.mult (q : ℂ) : ℝ)) ≤ A₁ * Real.log (|(n : ℝ)| + 3))
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0) (hFi : Integrable (𝓕 f))
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) :
    -(((Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * π)) *
        (Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * (3 * A₁ * logKernelConst)))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
      (Zeta23.zetaZeroConfig.W f f).re := by
  have hfcont : Continuous f := hf.continuous
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfc
  exact floorCoreFrom hdepthAll hcount f hf hfc
    (fun s pt hd hc => sum_norm_sq_fourierAt_le ha hA₁ hσ0 hfcont hfint hFi hsupp hint s pt
      (fun ρ => (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) hd (fun _ => Nat.cast_nonneg _) hc)

/-- The floor through the trapezoid of plateau `a` and collar `δ`: the depth rate is
`2π(a + 2δ)σ`, the aperture of the source itself up to the collar. -/
private theorem floorCoreCollar {a δ σ A₁ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA₁ : 0 ≤ A₁)
    (hσ0 : 0 ≤ σ)
    (hdepthAll : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, |(spectralSample ρ).im| ≤ σ)
    (hcount : ∀ (S : Finset Zeta23.zetaZeroConfig.carrier) (n : ℤ),
      (∑ q ∈ S.filter fun q : Zeta23.zetaZeroConfig.carrier =>
          (n : ℝ) ≤ -(((q : ℂ)).im / (2 * π)) ∧ -(((q : ℂ)).im / (2 * π)) ≤ (n : ℝ) + 1,
        (Zeta23.zetaZeroConfig.mult (q : ℂ) : ℝ)) ≤ A₁ * Real.log (|(n : ℝ)| + 3))
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hsupp : ∀ t : ℝ, a < |t| → f t = 0) (hFi : Integrable (𝓕 f))
    (hint : Integrable fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) :
    -(((Real.exp (2 * π * (a + 2 * δ) * σ) * ((4 * (a + δ) + δ⁻¹) * π)) *
        (Real.exp (2 * π * (a + 2 * δ) * σ) *
          ((4 * (a + δ) + δ⁻¹) * (3 * A₁ * logKernelConst)))) *
        ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
      (Zeta23.zetaZeroConfig.W f f).re := by
  have hfcont : Continuous f := hf.continuous
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfc
  exact floorCoreFrom hdepthAll hcount f hf hfc
    (fun s pt hd hc => sum_norm_sq_fourierAt_le_collar ha hδ hA₁ hσ0 hfcont hfint hFi hsupp hint
      s pt (fun ρ => (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) hd (fun _ => Nat.cast_nonneg _) hc)

/-- **The floor at a given depth bound.**  The exponential rate in the aperture is twice the
depth of the sample points, which is the zero width divided by `2π`. -/
theorem exists_re_W_ge_logWeighted_of_depth {a σ : ℝ} (ha : 0 < a) (hσ0 : 0 ≤ σ)
    (hdepthAll : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, |(spectralSample ρ).im| ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
      Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) →
      -(C * Real.exp (12 * π * a * σ) * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
        (Zeta23.zetaZeroConfig.W f f).re := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount Zeta23.zetaZeroConfig hA₀ hloc
  obtain ⟨A₁, hA₁, hcount⟩ := exists_count_spectralSample hLC
  refine ⟨((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) * (3 * A₁ * logKernelConst)), ?_,
    fun f hf hfc hsupp hFi hint => ?_⟩
  · have := logKernelConst_nonneg
    positivity
  · have hcore := floorCore ha hA₁ hσ0 hdepthAll hcount f hf hfc hsupp hFi hint
    refine le_trans (le_of_eq ?_) hcore
    have hsplitexp : Real.exp (6 * π * a * σ) * Real.exp (6 * π * a * σ) =
        Real.exp (12 * π * a * σ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hsplitexp]
    ring

/-- **The unconditional floor.**  With the strip as the depth bound no hypothesis on the zeros is
used at all. -/
theorem exists_re_W_ge_logWeighted {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
      Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) →
      -(C * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
        (Zeta23.zetaZeroConfig.W f f).re := by
  obtain ⟨C, hC, hfloor⟩ := exists_re_W_ge_logWeighted_of_depth ha
    (by positivity : (0:ℝ) ≤ 1 / (4 * π)) (fun ρ hρ => abs_spectralSample_im_le hρ)
  refine ⟨C * Real.exp (12 * π * a * (1 / (4 * π))), by positivity,
    fun f hf hfc hsupp hFi hint => ?_⟩
  have h := hfloor f hf hfc hsupp hFi hint
  refine le_trans (le_of_eq ?_) h
  ring

/-- **The width is the rate of the archimedean-normalised floor.**  Unconditionally, the floor
holds with the exponential rate `6 a · zetaZeroWidth` in the aperture; the rate vanishes exactly
when the Riemann Hypothesis holds, so the rate reading of this floor is selective, while the
inequality itself (at the trivial depth `½`) is not. -/
theorem exists_re_W_ge_logWeighted_rate {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
      Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) →
      -(C * Real.exp (6 * a * zetaZeroWidth) *
          ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
        (Zeta23.zetaZeroConfig.W f f).re := by
  have hw : 0 ≤ zetaZeroWidth := zetaZeroWidth_nonneg
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hdepth : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier,
      |(spectralSample ρ).im| ≤ zetaZeroWidth / (2 * π) := by
    intro ρ hρ
    rw [spectralSample_im, abs_div, abs_of_pos hpi]
    gcongr
    exact abs_re_sub_half_le_zetaZeroWidth hρ
  obtain ⟨C, hC, hfloor⟩ := exists_re_W_ge_logWeighted_of_depth ha
    (by positivity : (0:ℝ) ≤ zetaZeroWidth / (2 * π)) hdepth
  refine ⟨C, hC, fun f hf hfc hsupp hFi hint => ?_⟩
  have h := hfloor f hf hfc hsupp hFi hint
  refine le_trans (le_of_eq ?_) h
  have hexp : Real.exp (6 * a * zetaZeroWidth) =
      Real.exp (12 * π * a * (zetaZeroWidth / (2 * π))) := by
    congr 1
    field_simp
    try ring
  rw [hexp]


/-! ## The sharp rate: the aperture itself, not three times it -/

/-- **The floor at a given depth bound, with the collar rate.**  Through a plateau cutoff of
collar `δ` the exponential rate is `4π(a + 2δ)σ` instead of `12πaσ`. -/
theorem exists_re_W_ge_logWeighted_of_depth_collar {a δ σ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hσ0 : 0 ≤ σ)
    (hdepthAll : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, |(spectralSample ρ).im| ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
      Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) →
      -(C * Real.exp (4 * π * (a + 2 * δ) * σ) *
          ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
        (Zeta23.zetaZeroConfig.W f f).re := by
  classical
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hLC := Zeta23.Tail.LocalCount.ofWindowCount Zeta23.zetaZeroConfig hA₀ hloc
  obtain ⟨A₁, hA₁, hcount⟩ := exists_count_spectralSample hLC
  have hX : (0:ℝ) ≤ 4 * (a + δ) + δ⁻¹ := by
    have := inv_pos.mpr hδ
    linarith
  have hY : (0:ℝ) ≤ 3 * A₁ * logKernelConst :=
    mul_nonneg (by linarith) logKernelConst_nonneg
  refine ⟨((4 * (a + δ) + δ⁻¹) * π) * ((4 * (a + δ) + δ⁻¹) * (3 * A₁ * logKernelConst)),
    mul_nonneg (mul_nonneg hX Real.pi_pos.le) (mul_nonneg hX hY),
    fun f hf hfc hsupp hFi hint => ?_⟩
  have hcore := floorCoreCollar ha hδ hA₁ hσ0 hdepthAll hcount f hf hfc hsupp hFi hint
  refine le_trans (le_of_eq ?_) hcore
  have hsplitexp : Real.exp (2 * π * (a + 2 * δ) * σ) * Real.exp (2 * π * (a + 2 * δ) * σ) =
      Real.exp (4 * π * (a + 2 * δ) * σ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hsplitexp]
  ring

/-- **The unconditional floor at the collar rate.**  For every collar `δ > 0` the archimedean
floor holds with exponential rate `2(a + 2δ) · zetaZeroWidth` in the aperture. -/
theorem exists_re_W_ge_logWeighted_rate_collar {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
      Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) →
      -(C * Real.exp (2 * (a + 2 * δ) * zetaZeroWidth) *
          ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
        (Zeta23.zetaZeroConfig.W f f).re := by
  have hw : 0 ≤ zetaZeroWidth := zetaZeroWidth_nonneg
  have hpi : (0:ℝ) < 2 * π := by positivity
  have hdepth : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier,
      |(spectralSample ρ).im| ≤ zetaZeroWidth / (2 * π) := by
    intro ρ hρ
    rw [spectralSample_im, abs_div, abs_of_pos hpi]
    gcongr
    exact abs_re_sub_half_le_zetaZeroWidth hρ
  obtain ⟨C, hC, hfloor⟩ := exists_re_W_ge_logWeighted_of_depth_collar ha hδ
    (by positivity : (0:ℝ) ≤ zetaZeroWidth / (2 * π)) hdepth
  refine ⟨C, hC, fun f hf hfc hsupp hFi hint => ?_⟩
  have h := hfloor f hf hfc hsupp hFi hint
  refine le_trans (le_of_eq ?_) h
  have hexp : Real.exp (2 * (a + 2 * δ) * zetaZeroWidth) =
      Real.exp (4 * π * (a + 2 * δ) * (zetaZeroWidth / (2 * π))) := by
    congr 1
    field_simp
    try ring
  rw [hexp]

/-- **The rate of the archimedean floor is twice the aperture times the width.**  For every
`ε > 0` the unconditional floor holds with rate `(2a + ε) · zetaZeroWidth` at aperture `a`.  This
is the rate at which the forward arrow reads a floor: a bound `−C e^{2σA}` at aperture `A` forces
the zeros into `|Re ρ − ½| ≤ σ`.  The three-radius trapezoid gave `6a · width`, a factor three
away; the narrow collar removes it, so the two directions of "the rate of the ground-energy path
is twice the width" meet in the same unit, with the collar paid for by the constant. -/
theorem exists_re_W_ge_logWeighted_rate_sharp {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
      Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) →
      -(C * Real.exp ((2 * a + ε) * zetaZeroWidth) *
          ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 * Real.log (|y| + 3)) ≤
        (Zeta23.zetaZeroConfig.W f f).re := by
  obtain ⟨C, hC, hfloor⟩ :=
    exists_re_W_ge_logWeighted_rate_collar (a := a) (δ := ε / 4) ha (by positivity)
  refine ⟨C, hC, fun f hf hfc hsupp hFi hint => ?_⟩
  have h := hfloor f hf hfc hsupp hFi hint
  have hrate : Real.exp (2 * (a + 2 * (ε / 4)) * zetaZeroWidth) =
      Real.exp ((2 * a + ε) * zetaZeroWidth) := by
    congr 1
    ring
  rwa [hrate] at h

/-! ## The on-line terms are free: the weight is the off-line count -/

/-- **The floor with the off-line count as its weight.**  The on-line zeros contribute
nonnegatively, so only the off-line zeros are sampled: the per-window weight that has to be
bounded is the off-line one, and a bound uniform in the height gives the plain `L²`
normalisation. -/
theorem exists_re_W_ge_l2_of_offLineDensity {a σ D : ℝ} (ha : 0 < a) (hσ0 : 0 ≤ σ) (hD : 0 ≤ D)
    (hdepthAll : ∀ ρ ∈ Zeta23.zetaZeroConfig.carrier, |(spectralSample ρ).im| ≤ σ)
    (hcount : ∀ (s : Finset Zeta23.zetaZeroConfig.carrier) (n : ℤ),
      (∑ ρ ∈ (s.filter fun ρ : Zeta23.zetaZeroConfig.carrier => (ρ : ℂ).re ≠ 1 / 2).filter
          (fun ρ : Zeta23.zetaZeroConfig.carrier =>
            (n : ℝ) ≤ -(((ρ : ℂ)).im / (2 * π)) ∧ -(((ρ : ℂ)).im / (2 * π)) ≤ (n : ℝ) + 1),
        (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (∀ t : ℝ, a < |t| → f t = 0) → Integrable (𝓕 f) →
      Integrable (fun y : ℝ => ‖𝓕 f y‖ ^ 2) →
      -(C * Real.exp (12 * π * a * σ) * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2) ≤
        (Zeta23.zetaZeroConfig.W f f).re := by
  classical
  refine ⟨((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) * (3 * D * kernelConst)), ?_,
    fun f hf hfc hsupp hFi hΦ2 => ?_⟩
  · have := kernelConst_nonneg
    positivity
  have hfcont : Continuous f := hf.continuous
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfc
  set Csamp : ℝ := (Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * π)) *
    (Real.exp (6 * π * a * σ) * ((8 * a + a⁻¹) * (3 * D * kernelConst))) with hCs
  set g : Zeta23.zetaZeroConfig.carrier → ℝ := fun ρ =>
    if (ρ : ℂ).re = 1 / 2 then 0 else
      (Zeta23.zetaZeroConfig.mult ρ : ℝ) / 2 *
        (‖fourierAt f (spectralSample ρ)‖ ^ 2 +
          ‖fourierAt f ((starRingEnd ℂ) (spectralSample ρ))‖ ^ 2) with hg
  have hgnn : ∀ ρ, 0 ≤ g ρ := by
    intro ρ
    simp only [hg]
    by_cases hρ : (ρ : ℂ).re = 1 / 2
    · rw [if_pos hρ]
    · rw [if_neg hρ]
      have hm : (0:ℝ) ≤ (Zeta23.zetaZeroConfig.mult ρ : ℝ) := Nat.cast_nonneg _
      positivity
  -- partial sums: only the off-line zeros are sampled
  have hpart : ∀ s : Finset Zeta23.zetaZeroConfig.carrier,
      (∑ ρ ∈ s, g ρ) ≤ Csamp * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 := by
    intro s
    set s' : Finset Zeta23.zetaZeroConfig.carrier :=
      s.filter fun ρ : Zeta23.zetaZeroConfig.carrier => (ρ : ℂ).re ≠ 1 / 2 with hs'
    have hrestrict : (∑ ρ ∈ s, g ρ) = ∑ ρ ∈ s',
        (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) / 2 *
          (‖fourierAt f (spectralSample (ρ : ℂ))‖ ^ 2 +
            ‖fourierAt f ((starRingEnd ℂ) (spectralSample (ρ : ℂ)))‖ ^ 2) := by
      rw [hs', Finset.sum_filter]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [hg]
      by_cases hρ : (ρ : ℂ).re = 1 / 2
      · rw [if_pos hρ, if_neg (not_not_intro hρ)]
      · rw [if_neg hρ, if_pos hρ]
    have hdepth : ∀ ρ ∈ s', |(spectralSample (ρ : ℂ)).im| ≤ σ := fun ρ _ => hdepthAll ρ ρ.2
    have hdepth' : ∀ ρ ∈ s', |((starRingEnd ℂ) (spectralSample (ρ : ℂ))).im| ≤ σ := by
      intro ρ hρ
      rw [Complex.conj_im, abs_neg]
      exact hdepth ρ hρ
    have hc1 : ∀ n : ℤ,
        (∑ ρ ∈ s'.filter fun ρ : Zeta23.zetaZeroConfig.carrier =>
            (n : ℝ) ≤ (spectralSample (ρ : ℂ)).re ∧
            (spectralSample (ρ : ℂ)).re ≤ (n : ℝ) + 1,
          (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) ≤ D := by
      intro n
      have h := hcount s n
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr ?_ fun ρ _ => rfl
      refine Finset.filter_congr fun ρ _ => ?_
      rw [spectralSample_re]
    have hc2 : ∀ n : ℤ,
        (∑ ρ ∈ s'.filter fun ρ : Zeta23.zetaZeroConfig.carrier =>
            (n : ℝ) ≤ ((starRingEnd ℂ) (spectralSample (ρ : ℂ))).re ∧
            ((starRingEnd ℂ) (spectralSample (ρ : ℂ))).re ≤ (n : ℝ) + 1,
          (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) ≤ D := by
      intro n
      refine le_trans (le_of_eq ?_) (hc1 n)
      refine Finset.sum_congr ?_ fun ρ _ => rfl
      refine Finset.filter_congr fun ρ _ => ?_
      rw [Complex.conj_re]
    have hb1 := sum_norm_sq_fourierAt_le_const ha hD hσ0 hfcont hfint hFi hsupp hΦ2 s'
      (fun ρ => spectralSample (ρ : ℂ))
      (fun ρ => (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) hdepth
      (fun ρ => Nat.cast_nonneg _) hc1
    have hb2 := sum_norm_sq_fourierAt_le_const ha hD hσ0 hfcont hfint hFi hsupp hΦ2 s'
      (fun ρ => (starRingEnd ℂ) (spectralSample (ρ : ℂ)))
      (fun ρ => (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ)) hdepth'
      (fun ρ => Nat.cast_nonneg _) hc2
    have hsplit : (∑ ρ ∈ s', (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) / 2 *
          (‖fourierAt f (spectralSample (ρ : ℂ))‖ ^ 2 +
            ‖fourierAt f ((starRingEnd ℂ) (spectralSample (ρ : ℂ)))‖ ^ 2)) =
        (∑ ρ ∈ s', (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
            ‖fourierAt f (spectralSample (ρ : ℂ))‖ ^ 2) / 2 +
          (∑ ρ ∈ s', (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
            ‖fourierAt f ((starRingEnd ℂ) (spectralSample (ρ : ℂ)))‖ ^ 2) / 2 := by
      have hpt : ∀ ρ ∈ s', (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) / 2 *
          (‖fourierAt f (spectralSample (ρ : ℂ))‖ ^ 2 +
            ‖fourierAt f ((starRingEnd ℂ) (spectralSample (ρ : ℂ)))‖ ^ 2) =
          ((Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
              ‖fourierAt f (spectralSample (ρ : ℂ))‖ ^ 2 +
            (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
              ‖fourierAt f ((starRingEnd ℂ) (spectralSample (ρ : ℂ)))‖ ^ 2) / 2 := by
        intro ρ _
        ring
      rw [Finset.sum_congr rfl hpt, ← Finset.sum_div, Finset.sum_add_distrib, add_div]
    rw [hrestrict, hsplit, hCs]
    linarith [hb1, hb2]
  have hgsummable : Summable g := summable_of_sum_le (fun ρ => hgnn ρ) hpart
  have hWsummable : Summable fun ρ : Zeta23.zetaZeroConfig.carrier =>
      Zeta23.zetaZeroConfig.Wsummand f f ρ :=
    RHTower.summable_Wsummand_of_contDiff_two hf hfc hf hfc
  have hreW : (Zeta23.zetaZeroConfig.W f f).re =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.Wsummand f f ρ).re := by
    rw [Zeta23.ZeroConfig.W]
    exact Complex.re_tsum hWsummable
  have hterm : ∀ ρ : Zeta23.zetaZeroConfig.carrier,
      -g ρ ≤ (Zeta23.zetaZeroConfig.Wsummand f f ρ).re := by
    intro ρ
    simp only [hg]
    by_cases hρ : (ρ : ℂ).re = 1 / 2
    · rw [if_pos hρ, neg_zero]
      exact re_Wsummand_nonneg_of_onLine Zeta23.zetaZeroConfig f hρ
    · rw [if_neg hρ]
      exact re_Wsummand_ge f ρ
  have htsum : (∑' ρ : Zeta23.zetaZeroConfig.carrier, -g ρ) ≤
      ∑' ρ : Zeta23.zetaZeroConfig.carrier, (Zeta23.zetaZeroConfig.Wsummand f f ρ).re :=
    Summable.tsum_le_tsum hterm hgsummable.neg (hWsummable.map
      (Complex.reAddGroupHom) (Complex.continuous_re))
  rw [hreW]
  refine le_trans ?_ htsum
  rw [tsum_neg]
  have hle : (∑' ρ : Zeta23.zetaZeroConfig.carrier, g ρ) ≤
      Csamp * ∫ y : ℝ, ‖𝓕 f y‖ ^ 2 := hgsummable.tsum_le_of_sum_le hpart
  have hsplitexp : Real.exp (6 * π * a * σ) * Real.exp (6 * π * a * σ) =
      Real.exp (12 * π * a * σ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hrw : ((8 * a + a⁻¹) * π) * ((8 * a + a⁻¹) * (3 * D * kernelConst)) *
      Real.exp (12 * π * a * σ) = Csamp := by
    rw [hCs, ← hsplitexp]
    ring
  rw [hrw]
  linarith

end

end GaloisForLFunctions.SquareRootThreshold
