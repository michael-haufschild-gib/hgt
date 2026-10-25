import GaloisForLFunctions.ArithmeticOrientationGeometry.CorrectorsInTheDampingParameter
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationIndexOfACycle
import GaloisForLFunctions.SquareRootThreshold.EveryWidthDecidesTheCriticalLine

/-!
# The orbit of the cubic spline decides the critical line

The orbit laws `riemannHypothesis_iff_hasseWeil_of_generic`,
`zeta_orbitCorr_rate_iff_zetaZeroWidth_le` and `riemannHypothesis_iff_forall_damped_bounded` read
RH and the zero width from the translation orbit of a spectrally generic test. Such tests exist by
a countable-exclusion argument (`exists_realSpectrallyGeneric`), but none is named.

These laws only use the transform at off-line zeros (`OffLineGeneric`). The cubic spline
`B = U_1^{⋆4}` has transform `(sin z/z)⁴`, which vanishes only on the real axis, while every
off-line zero has a non-real spectral point. So one explicit orbit decides RH and reads the width:

* `riemannHypothesis_iff_splineOrbit_hasseWeil`: RH iff the orbit of `B` satisfies Hasse–Weil at
  every scale;
* `zeta_splineOrbit_rate_iff_zetaZeroWidth_le`: `|W(B, B(· − t))| ≤ K e^{σt}` for all `t ≥ 0` iff
  the zero width is at most `σ`;
* `riemannHypothesis_iff_splineOrbit_subexponential`: RH iff that orbit correlation is
  `O(e^{εt})` for every `ε > 0`;
* `zeta_splineOrbit_negIndex_law`: the negative index of the prime-side Weil Gram matrices of
  finitely many translates of `B` reaches `n` iff `ζ` has at least `n` distinct zeros right of the
  line; RH iff all these matrices are positive semidefinite
  (`riemannHypothesis_iff_splineOrbit_weilGram_negIndex_eq_zero`).
-/

open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  im_gammaOf_ne_zero)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline paperFT_cubicSpline_ne_zero)
open GaloisForLFunctions.HTGeometry (hermNegIndex)

/-- A real test whose transform vanishes at the spectral point of no off-line zero. -/
def OffLineGeneric (Z : ZeroConfig) (f : ℝ → ℝ) : Prop :=
  ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (cx f) (gammaOf ρ) ≠ 0

theorem re_reflect_ne_half {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) : (reflect ρ).re ≠ 1 / 2 := by
  simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
  intro h
  exact hρ (by linarith)

/-- An off-line generic test is blind off the line only when there are no off-line zeros. -/
theorem onLine_iff_blindOffLine_of_offLineGeneric (Z : ZeroConfig) {f : ℝ → ℝ}
    (hgen : OffLineGeneric Z f) : BlindOffLine Z f ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  constructor
  · intro hb ρ hρ
    by_contra hre
    rcases hb ρ hρ hre with h | h
    · exact hgen ρ hρ hre h
    · rw [← gammaOf_reflect] at h
      exact hgen _ (Z.reflect_mem _ hρ) (re_reflect_ne_half hre) h
  · intro hon ρ hρ hre
    exact absurd (hon ρ hρ) hre

/-- At a nonnegative rate, an off-line generic test is blind above `σ` iff every zero has depth
at most `σ`. -/
theorem blindAbove_iff_of_offLineGeneric (Z : ZeroConfig) {f : ℝ → ℝ} (hgen : OffLineGeneric Z f)
    {σ : ℝ} (hσ : 0 ≤ σ) : BlindAbove Z σ f ↔ ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ σ := by
  constructor
  · intro hb ρ hρ
    by_contra hdeep
    push Not at hdeep
    have hre : ρ.re ≠ 1 / 2 := fun h => by rw [h, sub_self, abs_zero] at hdeep; linarith
    rcases hb ρ hρ hdeep with h | h
    · exact hgen ρ hρ hre h
    · rw [← gammaOf_reflect] at h
      exact hgen _ (Z.reflect_mem _ hρ) (re_reflect_ne_half hre) h
  · intro hall ρ hρ hdeep
    exact absurd (hall ρ hρ) (not_le.mpr hdeep)

/-- **One off-line generic orbit decides RH.** -/
theorem riemannHypothesis_iff_hasseWeil_of_offLineGeneric (x : ScalingCycle)
    (hgen : OffLineGeneric zetaZeroConfig x.2.2) :
    RiemannHypothesis ↔ ∀ t : ℝ, zetaScalingDatum.HasseWeilAt x t := by
  rw [zeta_orientation_iff, onLine_iff_blindOffLine_of_offLineGeneric _ hgen]
  exact SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine

/-- **One off-line generic orbit reads the zero width.** -/
theorem zeta_orbitCorr_rate_iff_zetaZeroWidth_le_of_offLineGeneric (x : ScalingCycle)
    (hgen : OffLineGeneric zetaZeroConfig x.2.2) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → |zetaScalingDatum.orbitCorr x t| ≤ K * Real.exp (σ * t)) ↔
      SquareRootThreshold.zetaZeroWidth ≤ σ := by
  simp only [← configScalingDatum_zeta_orbitCorr]
  rw [orbitCorr_rate_iff_blindAbove zetaZeroConfig temperedConfig_zetaZeroConfig
    fesSymmetric_zetaZeroConfig hσ x, blindAbove_iff_of_offLineGeneric _ hgen hσ,
    SquareRootThreshold.zetaZeroWidth_le_iff_re_le hσ]
  constructor
  · intro h ρ hρ; linarith [(abs_le.mp (h ρ hρ)).2]
  · intro h ρ hρ
    refine abs_le.mpr ⟨?_, by linarith [h ρ hρ]⟩
    have hr := h _ (zetaZeroConfig.reflect_mem _ hρ)
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    linarith

/-- **One off-line generic orbit decides RH through its damped energies.** -/
theorem riemannHypothesis_iff_forall_damped_bounded_of_offLineGeneric (x : ScalingCycle)
    (hgen : OffLineGeneric zetaZeroConfig x.2.2) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
      |zetaScalingDatum.orbitCorr x t| ≤ K * Real.exp (ε * t) := by
  have hT := dampedEnergy_tfae zetaZeroConfig temperedConfig_zetaZeroConfig x
    fesSymmetric_zetaZeroConfig
  rw [riemannHypothesis_iff_hasseWeil_of_offLineGeneric x hgen]
  have h1 : (∀ t : ℝ, zetaScalingDatum.HasseWeilAt x t) ↔
      ∀ t : ℝ, (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).HasseWeilAt x t :=
    forall_congr' fun t => zeta_hasseWeilAt_iff x t
  refine h1.trans ((hT.out 0 2).trans (forall₂_congr fun ε _ => ?_))
  rw [dampedEnergy_lt_top_iff]
  simp only [configScalingDatum_zeta_orbitCorr]

/-! ## The cubic spline orbit -/

/-- The cubic spline sees every off-line zero of every configuration. -/
theorem offLineGeneric_cubicSpline (Z : ZeroConfig) : OffLineGeneric Z cubicSpline :=
  fun _ _ hre => paperFT_cubicSpline_ne_zero (im_gammaOf_ne_zero hre)

/-- The scaling cycle of the cubic spline `U_1^{⋆4}`. -/
noncomputable def splineCycle : ScalingCycle :=
  (0, 0, ⟨cubicSpline, contDiff_cubicSpline, hasCompactSupport_cubicSpline⟩)

/-- **RH is the Hasse–Weil bound along the orbit of the cubic spline.** -/
theorem riemannHypothesis_iff_splineOrbit_hasseWeil :
    RiemannHypothesis ↔ ∀ t : ℝ, zetaScalingDatum.HasseWeilAt splineCycle t :=
  riemannHypothesis_iff_hasseWeil_of_offLineGeneric splineCycle
    (offLineGeneric_cubicSpline zetaZeroConfig)

/-- **The orbit of the cubic spline reads the zero width.** For `σ ≥ 0`,
`|W(B, B(· − t))| ≤ K e^{σt}` for some `K` and all `t ≥ 0` iff `zetaZeroWidth ≤ σ`. -/
theorem zeta_splineOrbit_rate_iff_zetaZeroWidth_le {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
      |zetaScalingDatum.orbitCorr splineCycle t| ≤ K * Real.exp (σ * t)) ↔
      SquareRootThreshold.zetaZeroWidth ≤ σ :=
  zeta_orbitCorr_rate_iff_zetaZeroWidth_le_of_offLineGeneric splineCycle
    (offLineGeneric_cubicSpline zetaZeroConfig) hσ

/-- **RH is subexponential growth of the cubic spline orbit.** -/
theorem riemannHypothesis_iff_splineOrbit_subexponential :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t →
      |zetaScalingDatum.orbitCorr splineCycle t| ≤ K * Real.exp (ε * t) :=
  riemannHypothesis_iff_forall_damped_bounded_of_offLineGeneric splineCycle
    (offLineGeneric_cubicSpline zetaZeroConfig)

/-! ## The orbit of the cubic spline counts the right zeros -/

/-- The cubic spline sees every zero right of the line. -/
theorem seenRightZeros_cubicSpline (Z : ZeroConfig) :
    seenRightZeros Z cubicSpline = {ρ ∈ Z.carrier | 1 / 2 < ρ.re} := by
  ext ρ
  simp only [seenRightZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hre : ρ.re ≠ 1 / 2 := ne_of_gt h2
    refine ⟨h1, h2, paperFT_cubicSpline_ne_zero (im_gammaOf_ne_zero hre),
      paperFT_cubicSpline_ne_zero ?_⟩
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr (im_gammaOf_ne_zero hre)

/-- **The cubic spline orbit counts the right zeros of `ζ`.** For shifts `D` dense in `[0, ∞)`,
some finite family of translates `B(· − s)`, `s ∈ D`, has a prime-side Weil Gram matrix with at
least `n` negative squares iff `ζ` has at least `n` distinct zeros right of the critical line. -/
theorem zeta_splineOrbit_negIndex_law {D : Set ℝ} (hD : DenseShifts D) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ D ∧ n ≤ hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx cubicSpline))) ↔
      (n : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  rw [← seenRightZeros_cubicSpline]
  exact zeta_orientationIndex_law ⟨contDiff_cubicSpline, hasCompactSupport_cubicSpline⟩ hD n

theorem riemannHypothesis_iff_no_rightZero :
    RiemannHypothesis ↔ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re} = ∅ := by
  rw [SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine]
  constructor
  · intro h
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    exact fun hρ => (h ρ hρ).le
  · intro h ρ hρ
    have hle : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 := fun ρ hρ => by
      by_contra hlt
      have : ρ ∈ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re} := ⟨hρ, not_le.mp hlt⟩
      rw [h] at this
      exact this
    have hr := hle _ (zetaZeroConfig.reflect_mem _ hρ)
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    linarith [hle ρ hρ]

/-- **RH is positivity of the prime-side Gram matrices of one explicit orbit.** -/
theorem riemannHypothesis_iff_splineOrbit_weilGram_negIndex_eq_zero {D : Set ℝ}
    (hD : DenseShifts D) :
    RiemannHypothesis ↔ ∀ S : Finset ℝ, ↑S ⊆ D → hermNegIndex (weilGram
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) fun s : S =>
        ArithmeticCastelnuovoSeveri.translate s (cx cubicSpline)) = 0 := by
  rw [riemannHypothesis_iff_no_rightZero]
  constructor
  · intro h S hS
    by_contra hne
    obtain := (zeta_splineOrbit_negIndex_law hD 1).mp ⟨S, hS, Nat.one_le_iff_ne_zero.mpr hne⟩
    rw [h, Set.encard_empty] at *
    simp_all
  · intro h
    by_contra hne
    obtain ⟨S, hS, hn⟩ := (zeta_splineOrbit_negIndex_law hD 1).mpr
      (Set.one_le_encard_iff_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hne))
    rw [h S hS] at hn
    exact absurd hn (by norm_num)

end GaloisForLFunctions.ArithmeticOrientationGeometry
