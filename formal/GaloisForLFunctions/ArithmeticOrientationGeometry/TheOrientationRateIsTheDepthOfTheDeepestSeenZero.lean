import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime

/-!
# The orientation rate of a cycle is the depth of the deepest zero it sees

The orientation theorem says that a cycle is oriented — its orbit correlation stays bounded by
its value at `0` — exactly when it is blind to the off-line zeros. The graded form measures how far
a cycle is from orientation by the exponential growth rate of its orbit correlation.

A real test `f` is **blind above depth `σ`** (`BlindAbove`) when its transform vanishes at one of
the two points `γ_ρ, γ̄_ρ` of every zero with `|Re ρ − ½| > σ`. Blindness above `0` is blindness to
the off-line zeros.

* **Upper rate** (`orbitCorr_le_of_blindAbove`, every tempered configuration). A cycle blind above
  depth `σ` has `|c_f(t)| ≤ (Σ_ρ |w_ρ(f)|) e^{σ |t|}`.
* **Lower rate** (`blindAbove_of_orbitCorr_le`, symmetric configurations). If
  `|c_f(t)| ≤ K e^{σ t}` for `t ≥ 0`, then `f` is blind above depth `σ`. A seen zero deeper than `σ`
  is a top pole of the Laplace transform of the orbit correlation beyond the abscissa `σ`
  (Square-Root Threshold, `exists_minor_gt_of_top`).
* **The orientation rate theorem** (`orbitCorr_rate_iff_blindAbove`): on a symmetric tempered
  configuration, the orbit correlation of `f` grows at most like `e^{σ t}` iff `f` sees no zero
  deeper than `σ`. The exponent of a cycle is the depth of the deepest zero it sees; `σ = 0` is the
  orientation theorem.
* **For `ζ`, a generic cycle reads the zero width** (`zeta_orbitCorr_rate_iff_zetaZeroWidth_le`):
  for a spectrally generic real test, `|W(f, f(· − t))| ≤ K e^{σ t}` for some `K` iff
  `zetaZeroWidth ≤ σ`. The orbit of one cycle is a receiver of the zero width; its first
  improvement below `σ = ½` is a zero-free strip.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  lagStructure offLineWeight exists_top_at_height exists_minor_gt_of_top
  exists_radius_of_hasCompactSupport zetaZeroWidth)

/-- A real test is **blind above depth `σ`** when its transform vanishes at one point of every
reflection pair of zeros with `|Re ρ − ½| > σ`. -/
def BlindAbove (Z : ZeroConfig) (σ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ρ ∈ Z.carrier, σ < |ρ.re - 1 / 2| →
    paperFT (cx f) (gammaOf ρ) = 0 ∨ paperFT (cx f) (conj (gammaOf ρ)) = 0

theorem blindAbove_zero_iff (Z : ZeroConfig) (f : ℝ → ℝ) :
    BlindAbove Z 0 f ↔ BlindOffLine Z f := by
  refine forall₂_congr fun ρ _ => ?_
  constructor
  · intro h hre; exact h (abs_pos.mpr (sub_ne_zero.mpr hre))
  · intro h hpos; exact h fun hre => by rw [hre, sub_self, abs_zero] at hpos; exact lt_irrefl _ hpos

/-- The Weil summand vanishes at every zero a blind test does not see. -/
theorem Wsummand_eq_zero_of_blindAbove {Z : ZeroConfig} {σ : ℝ} {f : ℝ → ℝ}
    (hb : BlindAbove Z σ f) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hdeep : σ < |ρ.re - 1 / 2|) :
    Z.Wsummand (cx f) (cx f) ρ = 0 := by
  rcases hb ρ hρ hdeep with h | h
  · rw [ZeroConfig.Wsummand, h, mul_zero, zero_mul]
  · rw [ZeroConfig.Wsummand, h, map_zero, mul_zero]

theorem norm_cexp_mul_sub_half_le (t : ℝ) (ρ : ℂ) :
    ‖cexp (t * (ρ - 1 / 2))‖ ≤ Real.exp (|t| * |ρ.re - 1 / 2|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h : (↑t * (ρ - 1 / 2)).re = t * (ρ.re - 1 / 2) := by
    rw [Complex.re_ofReal_mul]; simp
  rw [h, ← abs_mul]
  exact le_abs_self _

/-- **Upper rate.** On every tempered configuration a cycle blind above depth `σ` has
`|c_f(t)| ≤ (Σ_ρ |w_ρ|) e^{σ|t|}`. -/
theorem orbitCorr_le_of_blindAbove (Z : ZeroConfig) (hZ : TemperedConfig Z) {σ : ℝ}
    (x : ScalingCycle) (hb : BlindAbove Z σ x.2.2) (t : ℝ) :
    |(configScalingDatum Z hZ).orbitCorr x t| ≤
      (∑' ρ : Z.carrier, ‖Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖) * Real.exp (σ * |t|) := by
  have hf := x.2.2.2
  have hs := summable_norm_Wsummand Z hZ (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
    (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)
  have hbd : ∀ ρ : Z.carrier,
      ‖cexp (t * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖ ≤
        ‖Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖ * Real.exp (σ * |t|) := by
    intro ρ
    by_cases hdeep : σ < |(ρ : ℂ).re - 1 / 2|
    · rw [Wsummand_eq_zero_of_blindAbove hb ρ.2 hdeep]; simp
    · push Not at hdeep
      rw [norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ((norm_cexp_mul_sub_half_le t ρ).trans
        (Real.exp_le_exp.mpr ?_)) (norm_nonneg _)
      rw [mul_comm σ]
      exact mul_le_mul_of_nonneg_left hdeep (abs_nonneg t)
  have hsum := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd (hs.mul_right _)
  rw [configScalingDatum_orbitCorr_eq]
  calc _ ≤ ‖∑' ρ : Z.carrier, cexp (t * ((ρ : ℂ) - 1 / 2)) *
        Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' ρ : Z.carrier, ‖cexp (t * ((ρ : ℂ) - 1 / 2)) *
        Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' ρ : Z.carrier, ‖Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖ * Real.exp (σ * |t|) :=
        Summable.tsum_le_tsum hbd hsum (hs.mul_right _)
    _ = _ := tsum_mul_right

/-- **Lower rate.** On a symmetric tempered configuration, if `|c_f(t)| ≤ K e^{σt}` for `t ≥ 0`
with `σ ≥ 0`, then `f` sees no zero deeper than `σ`. -/
theorem blindAbove_of_orbitCorr_le (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {σ : ℝ} (hσ : 0 ≤ σ) (x : ScalingCycle) {K : ℝ}
    (hK : ∀ t : ℝ, 0 ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (σ * t)) :
    BlindAbove Z σ x.2.2 := by
  set f : ℝ → ℝ := (x.2.2 : ℝ → ℝ) with hfdef
  have hf : f ∈ realTests := x.2.2.2
  set b : ℝ → ℂ := cx f with hbdef
  intro ρ hρ hdeep
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hw : ∀ t ∈ Z.carrier, paperFT b (gammaOf t) ≠ 0 → paperFT b (conj (gammaOf t)) ≠ 0 →
      offLineWeight b (Z.mult t) t ≠ 0 := fun t ht ha hb' => by
    rw [offLineWeight_eq_Wsummand, ZeroConfig.Wsummand]
    have hm : (Z.mult t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := Z.one_le_mult t ht; omega)
    exact mul_ne_zero (mul_ne_zero hm ha) ((map_ne_zero _).mpr hb')
  -- a seen zero right of the line, deeper than `σ`
  obtain ⟨t, ht, htσ, hqt⟩ : ∃ t ∈ SquareRootThreshold.rightZeros Z, σ < t.re - 1 / 2 ∧
      offLineWeight b (Z.mult t) t ≠ 0 := by
    rcases le_or_gt ρ.re (1 / 2) with hle | hgt
    · have hre' : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
      rw [abs_of_nonpos (by linarith)] at hdeep
      refine ⟨reflect ρ, ⟨Z.reflect_mem _ hρ, by rw [hre']; linarith⟩, by rw [hre']; linarith, ?_⟩
      refine hw _ (Z.reflect_mem _ hρ) ?_ ?_
      · rwa [gammaOf_reflect]
      · rwa [gammaOf_reflect, conj_conj]
    · rw [abs_of_pos (by linarith)] at hdeep
      exact ⟨ρ, ⟨hρ, hgt⟩, hdeep, hw ρ hρ h1 h2⟩
  obtain ⟨t₀, ht₀, him₀, hq₀, htop⟩ := exists_top_at_height Z ht
    (fun z => offLineWeight b (Z.mult z) z ≠ 0) hqt
  have ht₀σ : σ < t₀.re - 1 / 2 := by linarith [htop t ht rfl hqt]
  obtain ⟨A, -, hA⟩ := exists_radius_of_hasCompactSupport (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ A := fun u hu => by
    by_contra h
    exact hu (hA u (not_le.mp h))
  set S : ℝ → ℂ := fun w => Z.W (cx (scaleShift w f)) (cx f) with hS
  have hcorr : ∀ w, (configScalingDatum Z hZ).orbitCorr x w = (S w).re := fun w => by
    rw [configScalingDatum_orbitCorr_eq, tsum_exp_Wsummand_eq_W]
  set c0 := (configScalingDatum Z hZ).orbitCorr x 0 with hc0
  obtain ⟨v, hv0, hv⟩ := exists_minor_gt_of_top Z hZ (cx_contDiff hf.1) hbs ht₀ hq₀
    (fun t' ht' him' hq' => htop t' ht' (him'.trans him₀) hq') hσ ht₀σ (2 * K + 2 * |c0|)
  have hlag : ∀ w, lagStructure Z b w = S w := fun w => by
    rw [hbdef, lagStructure_eq Z hf, tsum_exp_Wsummand_eq_W]
  have hreal : ∀ w, conj (S w) = S w := fun w => W_real_of_fes Z hFE _ _
  have hneg : S (-v) = S v := by
    rw [hS]
    dsimp only
    rw [W_scaleShift_neg_eq, ← W_conj_symm Z (cx f) (cx (scaleShift v f)), W_real_of_fes Z hFE]
  rw [hlag, hlag, hlag, hneg, hreal] at hv
  have hSv : S v = ((S v).re : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im (S v)]
    have him : (S v).im = 0 := by
      have := congrArg Complex.im (hreal v)
      rw [Complex.conj_im] at this
      linarith
    rw [him]; simp
  rw [← two_mul, norm_mul, hSv, Complex.norm_real, Real.norm_eq_abs] at hv
  have hKv := hK v hv0
  rw [hcorr] at hKv hc0
  have hS0 : (S 0).re = c0 := hc0.symm
  have he : 1 ≤ Real.exp (σ * v) := Real.one_le_exp (mul_nonneg hσ hv0)
  have habs : -|c0| ≤ c0 := neg_abs_le c0
  norm_num at hv
  nlinarith [abs_nonneg c0]

/-- **The orientation rate theorem.** On a symmetric tempered configuration, for `σ ≥ 0`, the orbit
correlation of a cycle grows at most like `e^{σ t}` iff the cycle sees no zero deeper than `σ`. -/
theorem orbitCorr_rate_iff_blindAbove (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {σ : ℝ} (hσ : 0 ≤ σ) (x : ScalingCycle) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (σ * t)) ↔
      BlindAbove Z σ x.2.2 := by
  constructor
  · rintro ⟨K, hK⟩; exact blindAbove_of_orbitCorr_le Z hZ hFE hσ x hK
  · intro hb
    refine ⟨∑' ρ : Z.carrier, ‖Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖, fun t ht => ?_⟩
    have h := orbitCorr_le_of_blindAbove Z hZ x hb t
    rwa [abs_of_nonneg ht] at h

/-- A spectrally generic test is blind above `σ` iff every zero has depth at most `σ`. -/
theorem blindAbove_iff_of_generic (Z : ZeroConfig) {f : ℝ → ℝ} (hgen : RealSpectrallyGeneric Z f)
    (σ : ℝ) : BlindAbove Z σ f ↔ ∀ ρ ∈ Z.carrier, |ρ.re - 1 / 2| ≤ σ := by
  constructor
  · intro hb ρ hρ
    by_contra hdeep
    push Not at hdeep
    rcases hb ρ hρ hdeep with h | h
    · exact hgen ρ hρ h
    · rw [← gammaOf_reflect] at h
      exact hgen _ (Z.reflect_mem _ hρ) h
  · intro hall ρ hρ hdeep
    exact absurd (hall ρ hρ) (not_le.mpr hdeep)

/-- **For `ζ`, one generic orbit reads the zero width.** For a spectrally generic real test and
`σ ≥ 0`: `|W(f, f(· − t))| ≤ K e^{σt}` for some `K` and all `t ≥ 0` iff `zetaZeroWidth ≤ σ`. -/
theorem zeta_orbitCorr_rate_iff_zetaZeroWidth_le (x : ScalingCycle)
    (hgen : RealSpectrallyGeneric zetaZeroConfig x.2.2) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → |zetaScalingDatum.orbitCorr x t| ≤ K * Real.exp (σ * t)) ↔
      zetaZeroWidth ≤ σ := by
  simp only [← configScalingDatum_zeta_orbitCorr]
  rw [orbitCorr_rate_iff_blindAbove zetaZeroConfig temperedConfig_zetaZeroConfig
    fesSymmetric_zetaZeroConfig hσ x, blindAbove_iff_of_generic _ hgen,
    SquareRootThreshold.zetaZeroWidth_le_iff_re_le hσ]
  constructor
  · intro h ρ hρ; linarith [(abs_le.mp (h ρ hρ)).2]
  · intro h ρ hρ
    refine abs_le.mpr ⟨?_, by linarith [h ρ hρ]⟩
    have hr := h _ (zetaZeroConfig.reflect_mem _ hρ)
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at hr
    linarith

end GaloisForLFunctions.ArithmeticOrientationGeometry
