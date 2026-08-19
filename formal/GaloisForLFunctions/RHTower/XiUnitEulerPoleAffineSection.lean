import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.ZetaCarrier
import GaloisForLFunctions.RHTower.ArchEnvelope
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.HTGeometry.HorizontalModulusDerivative

/-!
# The unit Euler pole marks the Xi affine origin

Dividing the translated completed function `xi - c` by the archimedean factor gives a punctured
decompletion whose residue at `s = 1` is `1 - 2c`.  The Euler normalization of the zeta pole
therefore selects the untranslated fibre out of the whole constant-translation orbit: the residue
equals one exactly when `c = 0`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The punctured translated decompletion of the completed function. -/
def zetaTranslatedDecompletion (c : ℂ) (s : ℂ) : ℂ := riemannZeta s - c / archFactor s

theorem archFactor_reciprocal {s : ℂ} (hs : s ≠ 1) :
    (s - 1) / archFactor s = 2 / (s * Gammaℝ s) := by
  rw [archFactor]
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rcases eq_or_ne (s * Gammaℝ s) 0 with hz | hz
  · rw [hz]
    have hnum : s * (s - 1) / 2 * Gammaℝ s = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · rw [h]; ring
      · rw [h]; ring
    rw [hnum]
    simp
  · field_simp

/-- **The unit Euler residue.**  The residue of the translated decompletion at the zeta pole is
`1 - 2c`. -/
theorem tendsto_translatedDecompletion_residue (c : ℂ) :
    Tendsto (fun s => (s - 1) * zetaTranslatedDecompletion c s) (𝓝[≠] (1 : ℂ))
      (𝓝 (1 - 2 * c)) := by
  have hres : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    riemannZeta_residue_one
  have hgamma : Tendsto (fun s : ℂ => 2 / (s * Gammaℝ s)) (𝓝[≠] (1 : ℂ)) (𝓝 2) := by
    have hden : Tendsto (fun s : ℂ => s * Gammaℝ s) (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
      have hcont : ContinuousAt (fun s : ℂ => s * Gammaℝ s) 1 := by
        refine continuousAt_id.mul ?_
        exact (hasDerivAt_Gammaℝ_of_re_pos (by norm_num : (0:ℝ) < (1:ℂ).re)).differentiableAt.continuousAt
      have h := hcont.continuousWithinAt (s := {(1 : ℂ)}ᶜ)
      rw [ContinuousWithinAt] at h
      simpa [Complex.Gammaℝ_one] using h
    have h := hden.div tendsto_const_nhds (by norm_num : (1 : ℂ) ≠ 0)
    have hdiv : Tendsto (fun s : ℂ => (2 : ℂ) / (s * Gammaℝ s)) (𝓝[≠] (1 : ℂ))
        (𝓝 (2 / 1)) := Filter.Tendsto.div tendsto_const_nhds hden (by norm_num)
    simpa using hdiv
  have hcomb := hres.sub (hgamma.const_mul c)
  have hval : (1 : ℂ) - c * 2 = 1 - 2 * c := by ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  rw [zetaTranslatedDecompletion, mul_sub]
  congr 1
  rw [mul_comm (s - 1) (c / archFactor s), div_mul_eq_mul_div, mul_div_assoc,
    archFactor_reciprocal hs1]

/-- **The affine section.**  The residue is the unit exactly on the untranslated fibre. -/
theorem translatedDecompletion_residue_eq_one_iff (c : ℂ) :
    (1 : ℂ) - 2 * c = 1 ↔ c = 0 := by
  constructor
  · intro h
    have : (2 : ℂ) * c = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  · intro h
    rw [h]
    ring

/-! ## The translated value-fibre Bezoutian -/

/-- The centered translated value fibre `X_c(w) = xi(1/2 + w) - c`. -/
def xiTranslatedCentered (c : ℂ) (w : ℂ) : ℂ := xi (1 / 2 + w) - c

theorem differentiable_xiTranslatedCentered (c : ℂ) :
    Differentiable ℂ (xiTranslatedCentered c) := by
  have haff : Differentiable ℂ (fun w : ℂ => (1 : ℂ) / 2 + w) := by fun_prop
  exact (xi_differentiable.comp haff).sub_const c

theorem analyticOnNhd_xiTranslatedCentered (c : ℂ) :
    AnalyticOnNhd ℂ (xiTranslatedCentered c) Set.univ :=
  (differentiable_xiTranslatedCentered c).differentiableOn.analyticOnNhd isOpen_univ

/-- The Hermitian translated Bezoutian of the value fibre. -/
def xiTranslatedBezoutian (c : ℂ) (w v : ℂ) : ℂ :=
  (deriv (xiTranslatedCentered c) w * (starRingEnd ℂ) (xiTranslatedCentered c v) +
      xiTranslatedCentered c w * (starRingEnd ℂ) (deriv (xiTranslatedCentered c) v)) /
    (w + (starRingEnd ℂ) v)

/-- **The Bezoutian diagonal.**  On the open right half plane the diagonal value is the squared
modulus times the real part of the logarithmic derivative, divided by the abscissa. -/
theorem xiTranslatedBezoutian_self (c : ℂ) {w : ℂ} (hw : 0 < w.re)
    (hX : xiTranslatedCentered c w ≠ 0) :
    xiTranslatedBezoutian c w w =
      ((Complex.normSq (xiTranslatedCentered c w) *
        (logDeriv (xiTranslatedCentered c) w).re / w.re : ℝ) : ℂ) := by
  set X : ℂ := xiTranslatedCentered c w with hXdef
  set X' : ℂ := deriv (xiTranslatedCentered c) w with hX'def
  have hden : w + (starRingEnd ℂ) w = ((2 * w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> (simp; try ring)
  have hnum : X' * (starRingEnd ℂ) X + X * (starRingEnd ℂ) X' =
      ((2 * (X' * (starRingEnd ℂ) X).re : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  have hlog : (logDeriv (xiTranslatedCentered c) w) = X' / X := rfl
  have hre : (X' * (starRingEnd ℂ) X).re =
      Complex.normSq X * (X' / X).re := by
    have hfac : X' * (starRingEnd ℂ) X = (X' / X) * (X * (starRingEnd ℂ) X) := by
      field_simp
    rw [hfac, Complex.mul_conj]
    simp [Complex.mul_re]
    ring
  rw [xiTranslatedBezoutian, ← hXdef, ← hX'def, hnum, hden, hlog, hre]
  rw [← Complex.ofReal_div]
  congr 1
  have hwne : w.re ≠ 0 := hw.ne'
  field_simp

/-- The translated fibre is not identically zero: the completed function is nonconstant. -/
theorem xiTranslatedCentered_ne_zero_somewhere (c : ℂ) :
    ∃ w : ℂ, xiTranslatedCentered c w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, _, _, _, _, hzero, _⟩ := exists_two_distinct_positive_real_XiC_zeros
  have hval : ∀ z : ℂ, xi (1 / 2 + z) = c := by
    intro z
    have := hcon z
    rw [xiTranslatedCentered, sub_eq_zero] at this
    exact this
  have h1 : xi (1 / 2 + ((x : ℝ) : ℂ) * Complex.I) = c := hval _
  have h2 : xi (1 / 2 + (0 : ℂ)) = c := hval 0
  have hxi1 : XiC ((x : ℝ) : ℂ) = c := h1
  have hxi0 : XiC 0 = c := by
    rw [XiC]
    simpa using h2
  rw [hzero] at hxi1
  exact XiC_zero_ne (by rw [hxi0, ← hxi1])

/-- **The Bezoutian classifier, necessity.**  Positivity of the translated Bezoutian on the open
right half plane places the whole selected value fibre on the critical line. -/
theorem re_eq_half_of_xiTranslatedBezoutian_nonneg {c : ℂ}
    (hpos : ∀ w : ℂ, 0 < w.re → 0 ≤ (xiTranslatedBezoutian c w w).re)
    {s : ℂ} (hs : xi s = c) : s.re = 1 / 2 := by
  have hX : ∀ w : ℂ, 0 < w.re →
      0 ≤ (deriv (xiTranslatedCentered c) w *
        (starRingEnd ℂ) (xiTranslatedCentered c w)).re := by
    intro w hw
    by_cases hzero : xiTranslatedCentered c w = 0
    · rw [hzero]
      simp
    · have hval := hpos w hw
      rw [xiTranslatedBezoutian_self c hw hzero, Complex.ofReal_re] at hval
      have hns : 0 < Complex.normSq (xiTranslatedCentered c w) :=
        Complex.normSq_pos.mpr hzero
      have hlogre : 0 ≤ (logDeriv (xiTranslatedCentered c) w).re := by
        by_contra hcon
        push Not at hcon
        have : Complex.normSq (xiTranslatedCentered c w) *
            (logDeriv (xiTranslatedCentered c) w).re / w.re < 0 := by
          apply div_neg_of_neg_of_pos _ hw
          nlinarith
        linarith
      have hre : (deriv (xiTranslatedCentered c) w *
          (starRingEnd ℂ) (xiTranslatedCentered c w)).re =
          Complex.normSq (xiTranslatedCentered c w) *
            (logDeriv (xiTranslatedCentered c) w).re := by
        have hfac : deriv (xiTranslatedCentered c) w *
            (starRingEnd ℂ) (xiTranslatedCentered c w) =
            (logDeriv (xiTranslatedCentered c) w) *
              (xiTranslatedCentered c w * (starRingEnd ℂ) (xiTranslatedCentered c w)) := by
          have hl : logDeriv (xiTranslatedCentered c) w =
              deriv (xiTranslatedCentered c) w / xiTranslatedCentered c w := rfl
          rw [hl]
          field_simp
        rw [hfac, Complex.mul_conj]
        simp [Complex.mul_re]
        ring
      rw [hre]
      nlinarith
  -- evenness of the translated fibre
  have heven : ∀ w : ℂ, xiTranslatedCentered c (-w) = xiTranslatedCentered c w := by
    intro w
    rw [xiTranslatedCentered, xiTranslatedCentered]
    congr 1
    have harg : (1 : ℂ) / 2 + -w = 1 - (1 / 2 + w) := by ring
    rw [harg, xi_one_sub]
  have hkey : ∀ w : ℂ, 0 < w.re → xiTranslatedCentered c w ≠ 0 := by
    intro w hw hzero
    have hmono := HTGeometry.monotoneOn_normSq_horizontal_of_re_nonneg
      (xiTranslatedCentered c) w.im (convex_Ici (w.re / 2))
      (fun t _ => (differentiable_xiTranslatedCentered c) _)
      (fun t ht => hX _ (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
        have : w.re / 2 ≤ t := ht
        linarith))
    have hwpt : ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I = w := by
      apply Complex.ext <;> simp
    have hall : ∀ t : ℝ, w.re / 2 ≤ t → t ≤ w.re →
        Complex.normSq (xiTranslatedCentered c ((t : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I)) = 0 := by
      intro t ht1 ht2
      have hle : Complex.normSq (xiTranslatedCentered c
          ((t : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I)) ≤
          Complex.normSq (xiTranslatedCentered c
            (((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I)) :=
        hmono (Set.mem_Ici.mpr ht1) (Set.mem_Ici.mpr (by linarith)) ht2
      rw [hwpt, hzero] at hle
      simp only [map_zero] at hle
      exact le_antisymm hle (Complex.normSq_nonneg _)
    -- a whole horizontal segment of zeros
    have hseq : ∀ n : ℕ, xiTranslatedCentered c
        (((w.re - w.re / (2 * (n + 2)) : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I) = 0 := by
      intro n
      have hn : (0 : ℝ) < 2 * ((n : ℝ) + 2) := by positivity
      have h1 : w.re / 2 ≤ w.re - w.re / (2 * ((n : ℝ) + 2)) := by
        have hdiv : w.re / (2 * ((n : ℝ) + 2)) ≤ w.re / 2 := by
          apply div_le_div_of_nonneg_left hw.le (by norm_num) (by linarith)
        linarith
      have h2 : w.re - w.re / (2 * ((n : ℝ) + 2)) ≤ w.re := by
        have : 0 < w.re / (2 * ((n : ℝ) + 2)) := by positivity
        linarith
      have := hall _ h1 h2
      exact Complex.normSq_eq_zero.mp this
    have hanalytic : AnalyticOnNhd ℂ (xiTranslatedCentered c) Set.univ :=
      analyticOnNhd_xiTranslatedCentered c
    have htend : Filter.Tendsto (fun n : ℕ =>
        (((w.re - w.re / (2 * ((n : ℝ) + 2)) : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I))
        Filter.atTop (nhds w) := by
      have hreal : Filter.Tendsto (fun n : ℕ => w.re - w.re / (2 * ((n : ℝ) + 2)))
          Filter.atTop (nhds w.re) := by
        have h0 : Filter.Tendsto (fun n : ℕ => w.re / (2 * ((n : ℝ) + 2)))
            Filter.atTop (nhds 0) := by
          apply Filter.Tendsto.div_atTop tendsto_const_nhds
          exact Filter.Tendsto.const_mul_atTop (by norm_num)
            (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
        simpa using tendsto_const_nhds.sub h0
      have hcont : Continuous (fun x : ℝ => ((x : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I) := by
        fun_prop
      have := (hcont.tendsto w.re).comp hreal
      rwa [hwpt] at this
    have hne : ∀ n : ℕ, (((w.re - w.re / (2 * ((n : ℝ) + 2)) : ℝ) : ℂ) +
        ((w.im : ℝ) : ℂ) * Complex.I) ≠ w := by
      intro n hcon
      have hre := congrArg Complex.re hcon
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
      have hn : (0 : ℝ) < w.re / (2 * ((n : ℝ) + 2)) := by positivity
      linarith
    have hwithin : Filter.Tendsto (fun n : ℕ =>
        (((w.re - w.re / (2 * ((n : ℝ) + 2)) : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I))
        Filter.atTop (nhdsWithin w {w}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
        (Filter.Eventually.of_forall fun n => hne n)
    have hfreq : ∃ᶠ z in nhdsWithin w {w}ᶜ, xiTranslatedCentered c z = 0 :=
      hwithin.frequently (Filter.Eventually.of_forall hseq).frequently
    have hzeroAll := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ w) hfreq
    obtain ⟨v, hv⟩ := xiTranslatedCentered_ne_zero_somewhere c
    exact hv (hzeroAll (Set.mem_univ v))
  -- conclude
  set w₀ : ℂ := s - 1 / 2 with hw₀
  have hXzero : xiTranslatedCentered c w₀ = 0 := by
    rw [xiTranslatedCentered, hw₀]
    have harg : (1 : ℂ) / 2 + (s - 1 / 2) = s := by ring
    rw [harg, hs, sub_self]
  have hre : w₀.re = 0 := by
    rcases lt_trichotomy w₀.re 0 with hneg | hzero | hpos
    · exfalso
      have hnegw : 0 < (-w₀).re := by simp only [Complex.neg_re]; linarith
      exact hkey (-w₀) hnegw (by rw [heven]; exact hXzero)
    · exact hzero
    · exact absurd hXzero (hkey w₀ hpos)
  have : s.re - 1 / 2 = 0 := by
    rw [hw₀] at hre
    simpa using hre
  linarith

end

end RHTower
