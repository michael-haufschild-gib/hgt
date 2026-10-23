import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.RHTower.WeilPrimeFreeTest
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-!
# The infinite genus law: Weil's form has no radical

Over `𝔽_q` the defect of the Frobenius span of a unitary curve datum is positive semidefinite with
an **exact radical**: the multiples of the reduced characteristic polynomial, present on every
window longer than the number of eigenvalues (`toeplitz_pos_on_window_iff`). The genus is finite,
so the span has sections.

Over `ℚ` the genus is infinite in the strongest sense. A compactly supported test `f` has an
entire transform `h_f` of exponential type, hence `O(T)` zeros up to height `T`; `ζ` has
`≫ T log T` simple zeros on the critical line, unconditionally. So **no nonzero test has a
transform vanishing at all but finitely many simple critical zeros** (`eq_zero_of_paperFT_vanish`).
Under RH Weil's form is `Σ_ρ m_ρ |h_f(γ_ρ)|²`; a test with `W(f, f) = 0` would vanish at every
zero. Hence (`riemannHypothesis_iff_weil_positive_definite`)

    RH  ⟺  W(f, f) > 0 for every nonzero `C²` compactly supported test.

The arithmetic surface has no sections at any degree: the contact window of the `𝔽_q` span
becomes infinite, and the radical is replaced by the near-radical, whose dimension is the
Landau–Widom count.
-/

open Complex MeasureTheory Set Filter
open scoped ComplexConjugate FourierTransform
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The multiplicative half-density profile `g(y) = f(log y)/√y` of an additive test
(`g = 0` on `y ≤ 0`, where `√y = 0`). -/
def multiplicativeProfile (f : ℝ → ℂ) (y : ℝ) : ℂ := f (Real.log y) * ((Real.sqrt y : ℝ) : ℂ)⁻¹

theorem weilCriticalLogProfile_multiplicativeProfile (f : ℝ → ℂ) :
    RHTower.weilCriticalLogProfile (multiplicativeProfile f) = f := by
  funext x
  rw [RHTower.weilCriticalLogProfile, multiplicativeProfile, Real.log_exp]
  have h : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]; ring_nf
  rw [h]
  have hne : ((Real.exp (x / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  field_simp

theorem multiplicativeProfile_eq_zero {f : ℝ → ℂ} {a : ℝ} (hfs : tsupport f ⊆ Icc (-a) a)
    {y : ℝ} (hy : y < Real.exp (-a)) : multiplicativeProfile f y = 0 := by
  rcases le_or_gt y 0 with h0 | h0
  · simp [multiplicativeProfile, Real.sqrt_eq_zero'.mpr h0]
  · have hlog : Real.log y < -a := by
      rw [Real.log_lt_iff_lt_exp h0]; exact hy
    have : f (Real.log y) = 0 := image_eq_zero_of_notMem_tsupport fun h => by
      have := (hfs h).1; linarith
    simp [multiplicativeProfile, this]

theorem continuous_multiplicativeProfile {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ}
    (hfs : tsupport f ⊆ Icc (-a) a) : Continuous (multiplicativeProfile f) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_or_ge y (Real.exp (-a)) with hy | hy
  · have hev : multiplicativeProfile f =ᶠ[nhds y] fun _ => 0 :=
      (Iio_mem_nhds hy).mono fun z hz => multiplicativeProfile_eq_zero hfs hz
    exact (continuousAt_const).congr hev.symm
  · have hpos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
    have hsq : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
    exact (hf.continuousAt.comp (Real.continuousAt_log hpos.ne')).mul
      ((Complex.continuous_ofReal.continuousAt.comp Real.continuous_sqrt.continuousAt).inv₀ hsq)

theorem support_multiplicativeProfile_subset {f : ℝ → ℂ} {a : ℝ} (hfs : tsupport f ⊆ Icc (-a) a) :
    Function.support (multiplicativeProfile f) ⊆ Icc (Real.exp (-a)) (Real.exp a) := by
  intro y hy
  have hy0 : multiplicativeProfile f y ≠ 0 := hy
  have hlow : Real.exp (-a) ≤ y := by
    by_contra h; push Not at h; exact hy0 (multiplicativeProfile_eq_zero hfs h)
  have hpos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hlow
  refine ⟨hlow, ?_⟩
  by_contra h
  push Not at h
  have hlog : a < Real.log y := by rw [Real.lt_log_iff_exp_lt hpos]; exact h
  have : f (Real.log y) = 0 := image_eq_zero_of_notMem_tsupport fun hm => by
    have := (hfs hm).2; linarith
  exact hy0 (by simp [multiplicativeProfile, this])

/-- The critical-line Mellin transform of the profile is the transform of the test. -/
theorem mellin_multiplicativeProfile (f : ℝ → ℂ) (t : ℝ) :
    mellin (multiplicativeProfile f) ((1 / 2 : ℂ) + (t : ℂ) * I) = paperFT f t := by
  rw [RHTower.mellin_criticalLine_eq_fourier_weilCriticalLogProfile,
    weilCriticalLogProfile_multiplicativeProfile, RHTower.WeilDeletion.fourier_eq_paperFT]
  congr 1
  push_cast
  field_simp

/-- **Infinite genus.** A continuous test supported in `[−a, a]` whose transform vanishes at all
but finitely many simple critical zeros of `ζ` is zero. -/
theorem eq_zero_of_paperFT_vanish {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a)
    (hfs : tsupport f ⊆ Icc (-a) a) (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → RHTower.xi (RHTower.linePt t) = 0 →
      (analyticOrderAt RHTower.xi (RHTower.linePt t)).toNat = 1 → paperFT f t = 0) :
    f = 0 := by
  have hg := RHTower.weilTest_eq_zero_of_cofinite_simpleCritical_mellin_zero ha
    (multiplicativeProfile f) (continuous_multiplicativeProfile hf hfs)
    (support_multiplicativeProfile_subset hfs) E (fun t htE htpos hxi hord => by
      rw [mellin_multiplicativeProfile]; exact hvanish t htE htpos hxi hord)
  rw [← weilCriticalLogProfile_multiplicativeProfile f, hg]
  funext x
  simp [RHTower.weilCriticalLogProfile]

/-- A simple critical zero of `ξ` is a nontrivial zero of `ζ`. -/
theorem linePt_mem_carrier {t : ℝ} (hxi : RHTower.xi (RHTower.linePt t) = 0) :
    RHTower.linePt t ∈ zetaZeroConfig.carrier := by
  have hre : (RHTower.linePt t).re = 1 / 2 := by simp [RHTower.linePt]
  have hne : RHTower.linePt t ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  rw [zetaZeroConfig_carrier]
  refine ⟨(RHTower.xi_eq_zero_iff (by rw [hre]; norm_num) hne).mp hxi, ?_, ?_⟩ <;> rw [hre] <;>
    norm_num

/-- **Under RH Weil's form is positive definite.** -/
theorem re_W_pos_of_riemannHypothesis (hRH : RiemannHypothesis) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : f ≠ 0) : 0 < (zetaZeroConfig.W f f).re := by
  rw [RHTower.WeilConditional.re_W_eq_tsum_zeroTerm hRH hf hfc]
  have hsum := RHTower.WeilConditional.summable_zeroTerm hRH hf hfc
  refine lt_of_le_of_ne (tsum_nonneg fun ρ => RHTower.WeilConditional.zeroTerm_nonneg f ρ) ?_
  intro h0
  have hall : ∀ ρ, RHTower.WeilConditional.zeroTerm f ρ = 0 := fun ρ =>
    le_antisymm (by
      have := hsum.le_tsum ρ fun j _ => RHTower.WeilConditional.zeroTerm_nonneg f j
      linarith) (RHTower.WeilConditional.zeroTerm_nonneg f ρ)
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hfs : tsupport f ⊆ Icc (-|R|) |R| := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact ⟨by linarith [neg_abs_le x, le_abs_self R], (le_abs_self x).trans (this.trans (le_abs_self R))⟩
  apply hf0
  refine eq_zero_of_paperFT_vanish hf.continuous (abs_nonneg R) hfs ∅ fun t _ _ hxi _ => ?_
  have hmem := linePt_mem_carrier hxi
  have h1 := hall ⟨_, hmem⟩
  have hm : 1 ≤ zetaZeroConfig.mult (RHTower.linePt t) := zetaZeroConfig.one_le_mult _ hmem
  have him : (RHTower.linePt t).im = t := by simp [RHTower.linePt]
  simp only [RHTower.WeilConditional.zeroTerm, him] at h1
  have hm' : (0 : ℝ) < zetaZeroConfig.mult (RHTower.linePt t) := by exact_mod_cast hm
  have := (mul_eq_zero.mp h1).resolve_left hm'.ne'
  simpa using this

/-- **RH is the positive definiteness of Weil's form.** -/
theorem riemannHypothesis_iff_weil_positive_definite :
    RiemannHypothesis ↔ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → f ≠ 0 →
      0 < (zetaZeroConfig.W f f).re := by
  refine ⟨fun hRH f hf hfc hf0 => re_W_pos_of_riemannHypothesis hRH hf hfc hf0, fun h => ?_⟩
  refine RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
  rw [← RHTower.zeta_W_eq_weilFullFunctional_mixed hf hfc hf hfc]
  by_cases hf0 : f = 0
  · subst hf0
    simp [ZeroConfig.W, ZeroConfig.Wsummand, paperFT]
  · exact (h f hf hfc hf0).le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
