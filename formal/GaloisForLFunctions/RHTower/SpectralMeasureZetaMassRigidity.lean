import GaloisForLFunctions.RHTower.OddWeilFunctionRigidity

/-!
# ζ-mass rigidity for spectral measures

Spectral data `(X, ν, c, t)` (`SpectralMeasureData`) consist of a measure space, measurable weights
`c`, ordinates `t ≥ 1` and `∫ |c|/t² dν < ∞`.  A signed spectral measure `μ` on `[1, ∞)` is the case
`ν = |μ|`, `c = dμ/d|μ|`; atomic spectra are the case of counting measure.  The Weil function is
`Φ(s) = (2(s − ½)/π) ∫ c/((s − ½)² + t²) dν` (`spectralMeasureSeries`), an odd Weil function.

Suppose `Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = Φ(s)` on `Re s > 1`.  If the ζ-weighted spectral mass
is sublinear, `∫_{t ≤ T} |c| |ζ(½ + it)| dν = o(T)`, then `lam(n) = Λ(n)` for all `n ≥ 2` and the
Riemann hypothesis holds (`zeta_mass_sublinear_rigidity_measure_of_truncated`).  Finite ζ-mass is a
special case (`zeta_mass_rigidity_measure`).  No positivity is used.

* The thin-strip defect is the `ν`-integral of the atom jumps
  `(c/π)(Λ(ρ)/2 · x^{−ρ/2} + Λ(ρ̄)/2 · x^{−ρ̄/2})`, `ρ = ½ + it` (`weilDefect_spectralMeasureSeries`),
  by Fubini on each line.
* Its Laplace transform is `−∫ (c/π)(atomLaplace ρ τ + atomLaplace ρ̄ τ) dν`
  (`spectralMeasureDefect_laplace`), holomorphic on `Re τ > 0` and bounded by the damped ζ-mass
  `(3/π)|τ|^{−½} ∫ |c| |ζ(½ + it)| e^{−t Re τ/|τ|} dν`.
* The counting form implies the Abel form by a layer-cake bound in `lintegral`
  (`dampedZetaMassMeasure_le_of_truncated`).
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

/-- At distance at least `d ∈ (0, 1]` from the critical line the atom denominators are bounded below:
`‖(w − ½)² + u²‖ ≥ d² u²/(4(|Im w| + 1)²)` for `u ≥ 1`. -/
theorem norm_atomDenom_ge_of_dist {u : ℝ} (hu : 1 ≤ u) {w : ℂ} {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hw : d ≤ |w.re - 1 / 2|) :
    d ^ 2 * u ^ 2 / (4 * (|w.im| + 1) ^ 2) ≤ ‖(w - 1 / 2) ^ 2 + (u : ℂ) ^ 2‖ := by
  rw [← sub_atomPoint_mul_sub_atomMirror, norm_mul]
  have hP1 : d ≤ ‖w - atomPoint u‖ := by
    have := Complex.abs_re_le_norm (w - atomPoint u)
    rw [Complex.sub_re, atomPoint_re] at this
    linarith
  have hQ1 : d ≤ ‖w - atomMirror u‖ := by
    have := Complex.abs_re_le_norm (w - atomMirror u)
    rw [Complex.sub_re, atomMirror_re] at this
    linarith
  have hP2 := norm_sub_atomPoint_ge (t := u) w
  have hQ2 := norm_sub_atomMirror_ge (t := u) w
  set M := |w.im| + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg w.im; linarith
  have hMpos : 0 < 4 * M ^ 2 := by positivity
  rw [div_le_iff₀ hMpos]
  have hP0 : 0 ≤ ‖w - atomPoint u‖ := norm_nonneg _
  have hQ0 : 0 ≤ ‖w - atomMirror u‖ := norm_nonneg _
  by_cases hbig : 2 * M ≤ u
  · have ha : u - |w.im| ≤ |w.im - u| := by
      have := abs_sub_abs_le_abs_sub u w.im
      rw [abs_of_pos (by linarith : (0 : ℝ) < u), abs_sub_comm] at this
      exact this
    have hb : u - |w.im| ≤ |w.im + u| := by
      have := abs_sub_abs_le_abs_sub u (-w.im)
      rw [abs_of_pos (by linarith : (0 : ℝ) < u), abs_neg, sub_neg_eq_add, add_comm] at this
      exact this
    have h1 : u / 2 ≤ ‖w - atomPoint u‖ := by linarith
    have h2 : u / 2 ≤ ‖w - atomMirror u‖ := by linarith
    have hprod : u / 2 * (u / 2) ≤ ‖w - atomPoint u‖ * ‖w - atomMirror u‖ :=
      mul_le_mul h1 h2 (by linarith) hP0
    have hd2 : d ^ 2 ≤ M ^ 2 := by nlinarith
    nlinarith
  · push Not at hbig
    have hprod : d * d ≤ ‖w - atomPoint u‖ * ‖w - atomMirror u‖ :=
      mul_le_mul hP1 hQ1 hd.le hP0
    have hu2 : u ^ 2 ≤ 4 * M ^ 2 := by nlinarith
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith

/-- Spectral data on a measure space: measurable weights `c`, ordinates `t ≥ 1`, and
`∫ |c|/t² dν < ∞`.  A signed spectral measure `μ` on `[1, ∞)` is `c · ν` with `ν = |μ|`. -/
structure SpectralMeasureData {X : Type*} [MeasurableSpace X] (ν : Measure X) (c t : X → ℝ) :
    Prop where
  measurable_c : Measurable c
  measurable_t : Measurable t
  one_le : ∀ x, 1 ≤ t x
  integrable : Integrable (fun x => |c x| / t x ^ 2) ν

/-- The Weil function of a spectral measure:
`Φ(s) = (2(s − ½)/π) ∫ c(x)/((s − ½)² + t(x)²) dν(x)`. -/
noncomputable def spectralMeasureSeries {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (c t : X → ℝ) (s : ℂ) : ℂ :=
  2 * (s - 1 / 2) / (Real.pi : ℂ) * ∫ x, (c x : ℂ) / ((s - 1 / 2) ^ 2 + (t x : ℂ) ^ 2) ∂ν

section SpectralMeasure

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {c t : X → ℝ}

theorem SpectralMeasureData.measurable_integrand (h : SpectralMeasureData ν c t) (s : ℂ) :
    Measurable fun x => (c x : ℂ) / ((s - 1 / 2) ^ 2 + (t x : ℂ) ^ 2) :=
  (Complex.measurable_ofReal.comp h.measurable_c).div
    (measurable_const.add ((Complex.measurable_ofReal.comp h.measurable_t).pow_const 2))

theorem SpectralMeasureData.norm_integrand_le (h : SpectralMeasureData ν c t) {w : ℂ} {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hw : d ≤ |w.re - 1 / 2|) (x : X) :
    ‖(c x : ℂ) / ((w - 1 / 2) ^ 2 + (t x : ℂ) ^ 2)‖ ≤
      4 * (|w.im| + 1) ^ 2 / d ^ 2 * (|c x| / t x ^ 2) := by
  have hden := norm_atomDenom_ge_of_dist (h.one_le x) hd hd1 hw
  have ht2 : 0 < t x ^ 2 := by have := h.one_le x; positivity
  have hpos : 0 < ‖(w - 1 / 2) ^ 2 + (t x : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hden
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hpos]
  have hM : 0 < 4 * (|w.im| + 1) ^ 2 := by positivity
  have htx : t x ≠ 0 := by have := h.one_le x; positivity
  calc |c x| = 4 * (|w.im| + 1) ^ 2 / d ^ 2 * (|c x| / t x ^ 2) *
        (d ^ 2 * t x ^ 2 / (4 * (|w.im| + 1) ^ 2)) := by
        field_simp
    _ ≤ 4 * (|w.im| + 1) ^ 2 / d ^ 2 * (|c x| / t x ^ 2) *
        ‖(w - 1 / 2) ^ 2 + (t x : ℂ) ^ 2‖ := by gcongr

theorem SpectralMeasureData.integrable_integrand (h : SpectralMeasureData ν c t) {w : ℂ}
    (hw : w.re ≠ 1 / 2) :
    Integrable (fun x => (c x : ℂ) / ((w - 1 / 2) ^ 2 + (t x : ℂ) ^ 2)) ν := by
  set d := min |w.re - 1 / 2| 1 with hd
  have hd0 : 0 < d := lt_min (abs_pos.mpr (sub_ne_zero.mpr hw)) one_pos
  exact Integrable.mono' (h.integrable.const_mul _) (h.measurable_integrand w).aestronglyMeasurable
    (Eventually.of_forall fun x =>
      h.norm_integrand_le hd0 (min_le_right _ _) (min_le_left _ _) x)

theorem spectralMeasureSeries_one_sub (ν : Measure X) (c t : X → ℝ) (s : ℂ) :
    spectralMeasureSeries ν c t (1 - s) = -spectralMeasureSeries ν c t s := by
  unfold spectralMeasureSeries
  have e : ∀ x, (c x : ℂ) / ((1 - s - 1 / 2) ^ 2 + (t x : ℂ) ^ 2) =
      (c x : ℂ) / ((s - 1 / 2) ^ 2 + (t x : ℂ) ^ 2) := by
    intro x; congr 1; ring
  simp only [e]
  ring

theorem norm_spectralMeasureSeries_le (h : SpectralMeasureData ν c t) {w : ℂ}
    (hw1 : 1 / 4 ≤ |w.re - 1 / 2|) (hw2 : |w.re - 1 / 2| ≤ 1) :
    ‖spectralMeasureSeries ν c t w‖ ≤
      128 / Real.pi * (|w.im| + 1) ^ 3 * ∫ x, |c x| / t x ^ 2 ∂ν := by
  set M := |w.im| + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have := abs_nonneg w.im; linarith
  have hpi := Real.pi_pos
  have hint : ‖∫ x, (c x : ℂ) / ((w - 1 / 2) ^ 2 + (t x : ℂ) ^ 2) ∂ν‖ ≤
      64 * M ^ 2 * ∫ x, |c x| / t x ^ 2 ∂ν := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (h.integrable.const_mul _)
      (Eventually.of_forall fun x => ?_)
    have := h.norm_integrand_le (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) hw1 x
    calc ‖(c x : ℂ) / ((w - 1 / 2) ^ 2 + (t x : ℂ) ^ 2)‖
        ≤ 4 * M ^ 2 / (1 / 4) ^ 2 * (|c x| / t x ^ 2) := this
      _ = 64 * M ^ 2 * (|c x| / t x ^ 2) := by ring
  have hwh : ‖w - 1 / 2‖ ≤ M := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (w - 1 / 2)
    simp at h1
    rw [hM]; linarith
  unfold spectralMeasureSeries
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi, norm_mul,
    Complex.norm_two]
  have hS0 : 0 ≤ ∫ x, |c x| / t x ^ 2 ∂ν := integral_nonneg fun x => by positivity
  calc 2 * ‖w - 1 / 2‖ / Real.pi * ‖∫ x, (c x : ℂ) / ((w - 1 / 2) ^ 2 + (t x : ℂ) ^ 2) ∂ν‖
      ≤ 2 * M / Real.pi * (64 * M ^ 2 * ∫ x, |c x| / t x ^ 2 ∂ν) := by gcongr
    _ = 128 / Real.pi * M ^ 3 * ∫ x, |c x| / t x ^ 2 ∂ν := by ring

theorem differentiableOn_spectralMeasureSeries (h : SpectralMeasureData ν c t) :
    DifferentiableOn ℂ (spectralMeasureSeries ν c t) {s : ℂ | 1 / 2 < s.re} := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_re_gt _
  have hne : ∀ s : ℂ, 1 / 2 < s.re → ∀ u : ℝ, (s - 1 / 2) ^ 2 + (u : ℂ) ^ 2 ≠ 0 := by
    intro s hs u h0
    rw [← sub_atomPoint_mul_sub_atomMirror] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · have := congrArg Complex.re h1
      rw [Complex.sub_re, atomPoint_re] at this; simp at this; linarith
    · have := congrArg Complex.re h1
      rw [Complex.sub_re, atomMirror_re] at this; simp at this; linarith
  have hI : DifferentiableOn ℂ (fun s => ∫ x, (c x : ℂ) / ((s - 1 / 2) ^ 2 + (t x : ℂ) ^ 2) ∂ν)
      {s : ℂ | 1 / 2 < s.re} := by
    refine differentiableOn_integral_of_locally_bounded hU (fun x => ?_)
      (fun z _ => (h.measurable_integrand z).aestronglyMeasurable) (fun s₀ hs₀ => ?_)
    · intro s hs
      refine DifferentiableAt.differentiableWithinAt ?_
      exact DifferentiableAt.div (differentiableAt_const _) (by fun_prop) (hne s hs (t x))
    · have hs₀' : 1 / 2 < s₀.re := hs₀
      set d₀ := min (s₀.re - 1 / 2) 1 with hd₀
      have hd₀pos : 0 < d₀ := lt_min (by linarith) one_pos
      have hd₀le : d₀ ≤ s₀.re - 1 / 2 := min_le_left _ _
      have hd₀1 : d₀ ≤ 1 := min_le_right _ _
      refine ⟨d₀ / 2, by positivity, fun z hz => ?_, fun x =>
        4 * (|s₀.im| + 2) ^ 2 / (d₀ / 2) ^ 2 * (|c x| / t x ^ 2),
        h.integrable.const_mul _, fun x z hz => ?_⟩
      · rw [mem_closedBall, dist_eq_norm] at hz
        have := (Complex.abs_re_le_norm (z - s₀)).trans hz
        rw [Complex.sub_re] at this
        show 1 / 2 < z.re
        have := (abs_le.mp this).1
        linarith
      · rw [mem_closedBall, dist_eq_norm] at hz
        have hre := (Complex.abs_re_le_norm (z - s₀)).trans hz
        have him := (Complex.abs_im_le_norm (z - s₀)).trans hz
        rw [Complex.sub_re] at hre
        rw [Complex.sub_im] at him
        have hdz : d₀ / 2 ≤ |z.re - 1 / 2| := by
          rw [abs_of_nonneg (by linarith [(abs_le.mp hre).1])]
          linarith [(abs_le.mp hre).1]
        have hb := h.norm_integrand_le (by positivity) (by linarith) hdz x
        have hzim : |z.im| + 1 ≤ |s₀.im| + 2 := by
          have := abs_sub_abs_le_abs_sub z.im s₀.im
          linarith
        calc ‖(c x : ℂ) / ((z - 1 / 2) ^ 2 + (t x : ℂ) ^ 2)‖
            ≤ 4 * (|z.im| + 1) ^ 2 / (d₀ / 2) ^ 2 * (|c x| / t x ^ 2) := hb
          _ ≤ 4 * (|s₀.im| + 2) ^ 2 / (d₀ / 2) ^ 2 * (|c x| / t x ^ 2) := by
              gcongr
  unfold spectralMeasureSeries
  exact ((by fun_prop : Differentiable ℂ fun s : ℂ => 2 * (s - 1 / 2) / (Real.pi : ℂ)).differentiableOn).mul hI

theorem SpectralMeasureData.oddWeilFunction (h : SpectralMeasureData ν c t) :
    OddWeilFunction (spectralMeasureSeries ν c t) where
  differentiableOn := differentiableOn_spectralMeasureSeries h
  one_sub := spectralMeasureSeries_one_sub ν c t
  growth := ⟨128 / Real.pi * ∫ x, |c x| / t x ^ 2 ∂ν,
    mul_nonneg (by positivity) (integral_nonneg fun x => by positivity),
    fun w hw1 hw2 => (norm_spectralMeasureSeries_le h hw1 hw2).trans (le_of_eq (by ring))⟩

end SpectralMeasure


section SpectralMeasureDefect

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {c t : X → ℝ}

/-- The thin-strip defect of a spectral measure:
`K(x) = −∫ (c/π)((Λ(ρ)/2) x^{-ρ/2} + (Λ(ρ̄)/2) x^{-ρ̄/2}) dν`, `ρ = ½ + i t`. -/
noncomputable def spectralMeasureDefect (ν : Measure X) (c t : X → ℝ) (x : ℝ) : ℂ :=
  -∫ y, (c y : ℂ) / Real.pi *
    (completedRiemannZeta (atomPoint (t y)) / 2 * (x : ℂ) ^ (-(atomPoint (t y) / 2)) +
      completedRiemannZeta (atomMirror (t y)) / 2 * (x : ℂ) ^ (-(atomMirror (t y) / 2))) ∂ν

theorem spectralMeasureSeries_eq_integral_atomPairFactor {s : ℂ} (hs : s.re ≠ 1 / 2) :
    spectralMeasureSeries ν c t s = ∫ y, (c y : ℂ) / Real.pi * atomPairFactor (t y) s ∂ν := by
  have hn : ∀ y, s ≠ atomPoint (t y) ∧ s ≠ atomMirror (t y) := fun y =>
    ⟨fun h => hs (by rw [h, atomPoint_re]), fun h => hs (by rw [h, atomMirror_re])⟩
  unfold spectralMeasureSeries
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [atomPairFactor_eq (hn y).1 (hn y).2]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **The thin-strip defect of a spectral measure** is the `ν`-integral of the atom jumps. -/
theorem weilDefect_spectralMeasureSeries [SFinite ν] (h : SpectralMeasureData ν c t) {x : ℝ}
    (hx : 0 < x) : weilDefect (spectralMeasureSeries ν c t) x = spectralMeasureDefect ν c t x := by
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := exists_bound_completedRiemannZeta_mul_cube
  have hpi := Real.pi_pos
  set F : ℝ → ℝ → X → ℂ := fun σ τ y => (x : ℂ) ^ (-((σ : ℂ) + τ * I)) *
    (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
      ((c y : ℂ) / Real.pi * atomPairFactor (t y) (2 * ((σ : ℂ) + τ * I)))) with hF
  have hline : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → ∀ τ : ℝ,
      1 / 4 ≤ |(2 * ((σ : ℂ) + τ * I)).re - 1 / 2| ∧ |(2 * ((σ : ℂ) + τ * I)).re - 1 / 2| ≤ 1 ∧
      1 / 4 ≤ (2 * ((σ : ℂ) + τ * I)).re ∧ (2 * ((σ : ℂ) + τ * I)).re ≤ 3 / 4 := by
    intro σ hσ τ
    have : (2 * ((σ : ℂ) + τ * I)).re = 2 * σ := by simp
    rw [this]
    rcases hσ with h | h <;> subst h <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  have him2 : ∀ (σ τ : ℝ), (2 * ((σ : ℂ) + τ * I)).im = 2 * τ := by intro σ τ; simp
  have hbound : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → ∀ τ y,
      ‖F σ τ y‖ ≤ (x ^ (-σ) * (128 / Real.pi * CΛ) * (1 + τ ^ 2)⁻¹) * (|c y| / t y ^ 2) := by
    intro σ hσ τ y
    obtain ⟨hl1, hl2, hl3, hl4⟩ := hline σ hσ τ
    have hP := norm_atomPairFactor_le_off_line (h.one_le y) hl1 hl2
    have hΛ := hCΛ _ hl3 hl4
    rw [him2] at hP hΛ
    have ht2 : 0 < t y ^ 2 := by have := h.one_le y; positivity
    have hden : 1 + τ ^ 2 ≤ 1 + (2 * τ) ^ 2 := by nlinarith
    simp only [hF]
    rw [norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpi, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-((σ : ℂ) + τ * I)).re = -σ := by simp
    rw [hre]
    calc x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
          (|c y| / Real.pi * ‖atomPairFactor (t y) (2 * ((σ : ℂ) + τ * I))‖))
        ≤ x ^ (-σ) * (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ *
          (|c y| / Real.pi * (128 * (|2 * τ| + 1) ^ 3 / t y ^ 2))) := by gcongr
      _ = x ^ (-σ) * (|c y| / t y ^ 2) * (128 / Real.pi) *
          (‖completedRiemannZeta (2 * ((σ : ℂ) + τ * I))‖ * (|2 * τ| + 1) ^ 3) := by
          field_simp
      _ ≤ x ^ (-σ) * (|c y| / t y ^ 2) * (128 / Real.pi) * (CΛ / (1 + (2 * τ) ^ 2)) := by
          gcongr
      _ ≤ x ^ (-σ) * (|c y| / t y ^ 2) * (128 / Real.pi) * (CΛ / (1 + τ ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hmeasF : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) →
      Measurable (Function.uncurry (F σ)) := by
    intro σ hσ
    have hreg : ∀ τ : ℝ, 2 * ((σ : ℂ) + τ * I) ∈ zetaRegular := by
      intro τ
      obtain ⟨_, _, hl3, hl4⟩ := hline σ hσ τ
      simp only [zetaRegular, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro h; rw [h] at hl3; norm_num at hl3
      · intro h; rw [h] at hl4; norm_num at hl4
    have hoff : ∀ (τ u : ℝ), 2 * ((σ : ℂ) + τ * I) - atomPoint u ≠ 0 ∧
        2 * ((σ : ℂ) + τ * I) - atomMirror u ≠ 0 := by
      intro τ u
      obtain ⟨hl1, _, _, _⟩ := hline σ hσ τ
      constructor
      · intro h0; have := congrArg Complex.re h0
        rw [Complex.sub_re, atomPoint_re] at this; simp at this
        rcases hσ with h | h <;> subst h <;> norm_num at this
      · intro h0; have := congrArg Complex.re h0
        rw [Complex.sub_re, atomMirror_re] at this; simp at this
        rcases hσ with h | h <;> subst h <;> norm_num at this
    have hΛc : Continuous fun τ : ℝ => completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) := by
      rw [continuous_iff_continuousAt]
      intro τ
      exact (differentiableOn_completedRiemannZeta_regular.differentiableAt
        (isOpen_zetaRegular.mem_nhds (hreg τ))).continuousAt.comp
        (f := fun τ : ℝ => 2 * ((σ : ℂ) + τ * I)) (by fun_prop)
    set H : ℝ × ℝ × ℝ → ℂ := fun q => (x : ℂ) ^ (-((σ : ℂ) + q.1 * I)) *
      (completedRiemannZeta (2 * ((σ : ℂ) + q.1 * I)) *
        ((q.2.1 : ℂ) / Real.pi * (1 / (2 * ((σ : ℂ) + q.1 * I) - atomPoint q.2.2) +
          1 / (2 * ((σ : ℂ) + q.1 * I) - atomMirror q.2.2)))) with hH
    have hHc : Continuous H := by
      simp only [hH]
      refine Continuous.mul (Continuous.const_cpow (by fun_prop)
        (Or.inl (by exact_mod_cast hx.ne'))) (Continuous.mul (hΛc.comp continuous_fst)
        (Continuous.mul (by fun_prop) (Continuous.add ?_ ?_)))
      · exact continuous_const.div (by unfold atomPoint; fun_prop) (fun q => (hoff q.1 q.2.2).1)
      · exact continuous_const.div (by unfold atomMirror; fun_prop) (fun q => (hoff q.1 q.2.2).2)
    have hcomp : Function.uncurry (F σ) = H ∘ fun p : ℝ × X => (p.1, c p.2, t p.2) := by
      funext p
      simp only [Function.uncurry, hF, hH, Function.comp, atomPairFactor]
    rw [hcomp]
    exact hHc.measurable.comp (measurable_fst.prodMk
      ((h.measurable_c.comp measurable_snd).prodMk (h.measurable_t.comp measurable_snd)))
  have hintF : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) →
      Integrable (Function.uncurry (F σ)) (volume.prod ν) := by
    intro σ hσ
    have hdom := ((integrable_inv_one_add_sq).const_mul
      (x ^ (-σ) * (128 / Real.pi * CΛ))).mul_prod h.integrable
    refine Integrable.mono' hdom (hmeasF σ hσ).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    have := hbound σ hσ p.1 p.2
    simpa [Function.uncurry, mul_assoc] using this
  -- the pointwise identity on each line
  have hpt : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → ∀ τ : ℝ,
      (x : ℂ) ^ (-((σ : ℂ) + τ * I)) * (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
        spectralMeasureSeries ν c t (2 * ((σ : ℂ) + τ * I))) = ∫ y, F σ τ y ∂ν := by
    intro σ hσ τ
    obtain ⟨hl1, _, _, _⟩ := hline σ hσ τ
    have hoffline : (2 * ((σ : ℂ) + τ * I)).re ≠ 1 / 2 := by
      intro h0; rw [h0] at hl1; norm_num at hl1
    rw [spectralMeasureSeries_eq_integral_atomPairFactor hoffline, ← integral_const_mul,
      ← integral_const_mul]
  have hswap : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) →
      (∫ τ : ℝ, (x : ℂ) ^ (-((σ : ℂ) + τ * I)) * (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
          spectralMeasureSeries ν c t (2 * ((σ : ℂ) + τ * I)))) =
        ∫ y, (∫ τ : ℝ, F σ τ y) ∂ν := by
    intro σ hσ
    rw [integral_congr_ae (Eventually.of_forall (hpt σ hσ))]
    exact integral_integral_swap (hintF σ hσ)
  have hinty : ∀ σ : ℝ, (σ = 3 / 8 ∨ σ = 1 / 8) → Integrable (fun y => ∫ τ : ℝ, F σ τ y) ν :=
    fun σ hσ => (hintF σ hσ).integral_prod_right
  have hatom : ∀ y, (1 / (2 * Real.pi) : ℝ) • ((∫ τ : ℝ, F (3 / 8) τ y) - ∫ τ : ℝ, F (1 / 8) τ y) =
      (c y : ℂ) / Real.pi *
        (completedRiemannZeta (atomPoint (t y)) / 2 * (x : ℂ) ^ (-(atomPoint (t y) / 2)) +
          completedRiemannZeta (atomMirror (t y)) / 2 * (x : ℂ) ^ (-(atomMirror (t y) / 2))) := by
    intro y
    have hat := atom_thin_strip (t y) hx
    have hc : ∀ σ : ℝ, (∫ τ : ℝ, F σ τ y) = (c y : ℂ) / Real.pi * ∫ τ : ℝ,
        (x : ℂ) ^ (-((σ : ℂ) + τ * I)) * (completedRiemannZeta (2 * ((σ : ℂ) + τ * I)) *
          atomPairFactor (t y) (2 * ((σ : ℂ) + τ * I))) := by
      intro σ
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [hF]
      ring
    rw [hc, hc, ← mul_sub, Complex.real_smul] at *
    rw [← hat]
    ring
  unfold weilDefect
  rw [hswap _ (Or.inl rfl), hswap _ (Or.inr rfl),
    ← integral_sub (hinty _ (Or.inl rfl)) (hinty _ (Or.inr rfl)), ← integral_smul,
    spectralMeasureDefect]
  congr 1
  exact integral_congr_ae (Eventually.of_forall hatom)

end SpectralMeasureDefect


theorem atomMirror_eq_atomPoint_neg (u : ℝ) : atomMirror u = atomPoint (-u) := by
  rw [atomMirror_eq, atomPoint_eq]

theorem continuous_atomPoint : Continuous atomPoint := by
  rw [show atomPoint = fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * I from funext atomPoint_eq]
  fun_prop

theorem continuous_completedRiemannZeta_atomPoint :
    Continuous fun u : ℝ => completedRiemannZeta (atomPoint u) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (differentiableOn_completedRiemannZeta_regular.differentiableAt
    (isOpen_zetaRegular.mem_nhds (mem_zetaRegular_of_re_eq_half (atomPoint_re u)))).continuousAt.comp
    continuous_atomPoint.continuousAt

theorem continuous_riemannZeta_atomPoint : Continuous fun u : ℝ => riemannZeta (atomPoint u) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hne : atomPoint u ≠ 1 := ne_one_of_re_eq_half (atomPoint_re u)
  exact (differentiableAt_riemannZeta hne).continuousAt.comp continuous_atomPoint.continuousAt

theorem continuous_Gamma_one_sub_atomPoint_half :
    Continuous fun u : ℝ => Complex.Gamma (1 - atomPoint u / 2) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hG : DifferentiableAt ℂ Complex.Gamma (1 - atomPoint u / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have := congrArg Complex.re hm
    rw [Complex.sub_re, Complex.div_re, atomPoint_re] at this
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    simp at this
    norm_num at this
    linarith
  exact hG.continuousAt.comp (f := fun u : ℝ => 1 - atomPoint u / 2)
    ((continuous_const.sub (continuous_atomPoint.div_const 2)).continuousAt)

theorem continuous_atomLaplace_atomPoint {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous fun u : ℝ => atomLaplace (atomPoint u) τ := by
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (pow_ne_zero 2 hτ)
  unfold atomLaplace
  exact ((continuous_completedRiemannZeta_atomPoint.div_const 2).mul
    continuous_Gamma_one_sub_atomPoint_half).mul (continuous_const.mul
      (Continuous.const_cpow ((continuous_const.sub (continuous_atomPoint.div_const 2)).neg)
        (Or.inl hz0)))

theorem continuous_atomLaplace_atomMirror {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous fun u : ℝ => atomLaplace (atomMirror u) τ := by
  simp only [atomMirror_eq_atomPoint_neg]
  exact (continuous_atomLaplace_atomPoint hτ).comp continuous_neg

section SpectralMeasureLaplace

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {c t : X → ℝ}

/-- The Laplace transform of the spectral-measure defect, continued to `Re τ > 0`. -/
noncomputable def spectralMeasureLaplace (ν : Measure X) (c t : X → ℝ) (τ : ℂ) : ℂ :=
  -∫ y, (c y : ℂ) / Real.pi *
    (atomLaplace (atomPoint (t y)) τ + atomLaplace (atomMirror (t y)) τ) ∂ν

/-- The damped ζ-mass of a spectral measure: `∫ |c| |ζ(½ + it)| e^{−δ t} dν`. -/
noncomputable def dampedZetaMassMeasure (ν : Measure X) (c t : X → ℝ) (δ : ℝ) : ℝ :=
  ∫ y, |c y| * ‖riemannZeta (atomPoint (t y))‖ * Real.exp (-(δ * t y)) ∂ν

theorem SpectralMeasureData.measurable_zetaWeight (h : SpectralMeasureData ν c t) (δ : ℝ) :
    Measurable fun y => |c y| * ‖riemannZeta (atomPoint (t y))‖ * Real.exp (-(δ * t y)) :=
  ((h.measurable_c.abs).mul ((continuous_norm.comp continuous_riemannZeta_atomPoint).measurable.comp
    h.measurable_t)).mul (Real.measurable_exp.comp ((measurable_const.mul h.measurable_t).neg))

theorem SpectralMeasureData.integrable_zetaWeight (h : SpectralMeasureData ν c t) {δ : ℝ}
    (hδ : 0 < δ) :
    Integrable (fun y => |c y| * ‖riemannZeta (atomPoint (t y))‖ * Real.exp (-(δ * t y))) ν := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_riemannZeta_atomPoint_le
  refine Integrable.mono' (h.integrable.const_mul (B * (6 / δ ^ 3)))
    (h.measurable_zetaWeight δ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have ht := h.one_le y
  have htpos : 0 < t y := by linarith
  have hexp : (δ * t y) ^ 3 / 6 ≤ Real.exp (δ * t y) := by
    have := Real.pow_div_factorial_le_exp (δ * t y) (by positivity) 3
    simpa [Nat.factorial] using this
  have hcube : t y ^ 3 * Real.exp (-(δ * t y)) ≤ 6 / δ ^ 3 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith [mul_pow δ (t y) 3]
  have hζ := hB (t y) ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc |c y| * ‖riemannZeta (atomPoint (t y))‖ * Real.exp (-(δ * t y))
      ≤ |c y| * (B * t y) * Real.exp (-(δ * t y)) := by gcongr
    _ = B * (|c y| / t y ^ 2) * (t y ^ 3 * Real.exp (-(δ * t y))) := by
        field_simp
    _ ≤ B * (|c y| / t y ^ 2) * (6 / δ ^ 3) := by gcongr
    _ = B * (6 / δ ^ 3) * (|c y| / t y ^ 2) := by ring

theorem dampedZetaMassMeasure_antitone (h : SpectralMeasureData ν c t) {δ₁ δ₂ : ℝ} (h1 : 0 < δ₁)
    (h12 : δ₁ ≤ δ₂) : dampedZetaMassMeasure ν c t δ₂ ≤ dampedZetaMassMeasure ν c t δ₁ := by
  refine integral_mono (h.integrable_zetaWeight (h1.trans_le h12)) (h.integrable_zetaWeight h1)
    (fun y => ?_)
  have ht : 0 ≤ t y := by linarith [h.one_le y]
  dsimp only
  gcongr

/-- The atom-pair Laplace kernel with its weight, and its damped bound. -/
theorem norm_atomPair_laplace_le (h : SpectralMeasureData ν c t) {τ : ℂ} (hτ : 0 < τ.re) (y : X) :
    ‖(c y : ℂ) / Real.pi * (atomLaplace (atomPoint (t y)) τ + atomLaplace (atomMirror (t y)) τ)‖ ≤
      3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * (|c y| * ‖riemannZeta (atomPoint (t y))‖ *
        Real.exp (-(τ.re / ‖τ‖ * t y))) := by
  have hpi := Real.pi_pos
  obtain ⟨h1, h2⟩ := norm_atomLaplace_le_decay (t y) hτ
  have habs : |t y| = t y := abs_of_pos (by linarith [h.one_le y])
  rw [habs, mul_comm (t y)] at h1 h2
  rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hpi]
  calc |c y| / Real.pi * ‖atomLaplace (atomPoint (t y)) τ + atomLaplace (atomMirror (t y)) τ‖
      ≤ |c y| / Real.pi * (3 / 2 * ‖riemannZeta (atomPoint (t y))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(τ.re / ‖τ‖ * t y)) +
          3 / 2 * ‖riemannZeta (atomPoint (t y))‖ * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(τ.re / ‖τ‖ * t y))) := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

theorem SpectralMeasureData.measurable_atomPair_laplace (h : SpectralMeasureData ν c t) {τ : ℂ}
    (hτ : τ ≠ 0) :
    Measurable fun y => (c y : ℂ) / Real.pi *
      (atomLaplace (atomPoint (t y)) τ + atomLaplace (atomMirror (t y)) τ) :=
  ((Complex.measurable_ofReal.comp h.measurable_c).div_const _).mul
    (((continuous_atomLaplace_atomPoint hτ).measurable.comp h.measurable_t).add
      ((continuous_atomLaplace_atomMirror hτ).measurable.comp h.measurable_t))

/-- **The measure Laplace transform is bounded by the damped ζ-mass.** -/
theorem norm_spectralMeasureLaplace_le (h : SpectralMeasureData ν c t) {τ : ℂ} (hτ : 0 < τ.re) :
    ‖spectralMeasureLaplace ν c t τ‖ ≤
      3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * dampedZetaMassMeasure ν c t (τ.re / ‖τ‖) := by
  have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ
  have hδ : 0 < τ.re / ‖τ‖ := div_pos hτ (norm_pos_iff.mpr hτ0)
  rw [spectralMeasureLaplace, norm_neg, dampedZetaMassMeasure, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((h.integrable_zetaWeight hδ).const_mul _)
    (Eventually.of_forall fun y => ?_)
  exact norm_atomPair_laplace_le h hτ y

/-- `J` is holomorphic on `Re τ > 0`. -/
theorem differentiableOn_spectralMeasureLaplace (h : SpectralMeasureData ν c t) :
    DifferentiableOn ℂ (spectralMeasureLaplace ν c t) {τ : ℂ | 0 < τ.re} := by
  have hpi := Real.pi_pos
  have hI : DifferentiableOn ℂ (fun τ => ∫ y, (c y : ℂ) / Real.pi *
      (atomLaplace (atomPoint (t y)) τ + atomLaplace (atomMirror (t y)) τ) ∂ν)
      {τ : ℂ | 0 < τ.re} := by
    refine differentiableOn_integral_of_locally_bounded (isOpen_lt continuous_const
      Complex.continuous_re) (fun y => ?_) (fun τ hτ => ?_) (fun τ₀ hτ₀ => ?_)
    · intro τ hτ
      exact ((differentiableAt_const _).mul ((differentiableAt_atomLaplace _ hτ).add
        (differentiableAt_atomLaplace _ hτ))).differentiableWithinAt
    · have hτ0 : τ ≠ 0 := by intro h0; rw [h0] at hτ; simp at hτ
      exact (h.measurable_atomPair_laplace hτ0).aestronglyMeasurable
    · have hτ₀' : 0 < τ₀.re := hτ₀
      set r := τ₀.re / 2 with hr
      have hr0 : 0 < r := by rw [hr]; linarith
      set δ₀ := r / (‖τ₀‖ + r) with hδ₀
      have hδ₀pos : 0 < δ₀ := div_pos hr0 (by positivity)
      refine ⟨r / 2, by positivity, fun z hz => ?_, fun y => 3 / Real.pi * (r / 2) ^ (-(1 / 2 : ℝ)) *
        (|c y| * ‖riemannZeta (atomPoint (t y))‖ * Real.exp (-(δ₀ * t y))),
        (h.integrable_zetaWeight hδ₀pos).const_mul _, fun y z hz => ?_⟩
      · rw [mem_closedBall, dist_eq_norm] at hz
        have := (Complex.abs_re_le_norm (z - τ₀)).trans hz
        rw [Complex.sub_re] at this
        show 0 < z.re
        have := (abs_le.mp this).1
        rw [hr] at *; linarith
      · rw [mem_closedBall, dist_eq_norm] at hz
        have hre' := (Complex.abs_re_le_norm (z - τ₀)).trans hz
        rw [Complex.sub_re] at hre'
        have hzre : r / 2 ≤ z.re := by
          have := (abs_le.mp hre').1; rw [hr] at *; linarith
        have hzpos : 0 < z.re := by linarith
        have hz0 : z ≠ 0 := by intro h0; rw [h0] at hzpos; simp at hzpos
        have hnpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        have hnle : ‖z‖ ≤ ‖τ₀‖ + r := by
          have := norm_sub_norm_le z τ₀
          linarith
        have hnge : r / 2 ≤ ‖z‖ := hzre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
        have hpow : ‖z‖ ^ (-(1 / 2 : ℝ)) ≤ (r / 2) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hnge (by norm_num)
        have hδ : δ₀ ≤ z.re / ‖z‖ := by
          rw [hδ₀, div_le_div_iff₀ (by positivity) hnpos]
          have h1 : r * ‖z‖ ≤ r * (‖τ₀‖ + r) := mul_le_mul_of_nonneg_left hnle hr0.le
          have h2 : r * (‖τ₀‖ + r) ≤ z.re * (‖τ₀‖ + r) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [hr] at *
            have := (abs_le.mp hre').1
            linarith
          linarith
        have hexp : Real.exp (-(z.re / ‖z‖ * t y)) ≤ Real.exp (-(δ₀ * t y)) := by
          apply Real.exp_le_exp.mpr
          have := h.one_le y
          nlinarith
        refine (norm_atomPair_laplace_le h hzpos y).trans ?_
        dsimp only
        gcongr
  unfold spectralMeasureLaplace
  exact hI.neg

end SpectralMeasureLaplace


section SpectralMeasureLaplaceIdentity

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {c t : X → ℝ}

/-- **Laplace transform of the spectral-measure defect.**  For real `τ > 0`, `K(x) e^{-πτ²x}` is
integrable on `(0, ∞)` and `τ ∫₀^∞ K(x) e^{-πτ²x} dx = J(τ)`. -/
theorem spectralMeasureDefect_laplace [SFinite ν] (h : SpectralMeasureData ν c t) {τ : ℝ}
    (hτ : 0 < τ) :
    IntegrableOn (fun x : ℝ => spectralMeasureDefect ν c t x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
    spectralMeasureLaplace ν c t τ = τ * ∫ x in Ioi (0 : ℝ), spectralMeasureDefect ν c t x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) := by
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := exists_bound_completedRiemannZeta_mul_cube
  have hpi := Real.pi_pos
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) with he
  have hΛat : ∀ u : ℝ, 1 ≤ u → ‖completedRiemannZeta (atomPoint u)‖ ≤ CΛ / u ^ 2 ∧
      ‖completedRiemannZeta (atomMirror u)‖ ≤ CΛ / u ^ 2 := by
    intro u hu
    have hu2 : 0 < u ^ 2 := by positivity
    have key : ∀ s : ℂ, s.re = 1 / 2 → |s.im| = u → ‖completedRiemannZeta s‖ ≤ CΛ / u ^ 2 := by
      intro s hs hsu
      have h := hCΛ s (by rw [hs]; norm_num) (by rw [hs]; norm_num)
      rw [hsu] at h
      have hsq : s.im ^ 2 = u ^ 2 := by rw [← sq_abs, hsu]
      rw [hsq] at h
      have h1 : 1 ≤ (u + 1) ^ 3 := by nlinarith
      have h2 : CΛ / (1 + u ^ 2) ≤ CΛ / u ^ 2 := by gcongr; linarith
      nlinarith [norm_nonneg (completedRiemannZeta s)]
    exact ⟨key _ (atomPoint_re u) (by simp [atomPoint]; linarith),
      key _ (atomMirror_re u) (by simp [atomMirror]; linarith)⟩
  set G : ℝ × X → ℂ := fun p => -((c p.2 : ℂ) / Real.pi *
    (completedRiemannZeta (atomPoint (t p.2)) / 2 * (p.1 : ℂ) ^ (-(atomPoint (t p.2) / 2)) +
      completedRiemannZeta (atomMirror (t p.2)) / 2 * (p.1 : ℂ) ^ (-(atomMirror (t p.2) / 2)))) *
    e p.1 with hG
  have hmeasG : Measurable G := by
    have hM : Continuous fun u : ℝ => completedRiemannZeta (atomMirror u) := by
      simp only [atomMirror_eq_atomPoint_neg]
      exact continuous_completedRiemannZeta_atomPoint.comp continuous_neg
    have hcM : Continuous fun u : ℝ => -(atomMirror u / 2) := by
      simp only [atomMirror_eq_atomPoint_neg]
      exact ((continuous_atomPoint.comp continuous_neg).div_const 2).neg
    have hcP : Continuous fun u : ℝ => -(atomPoint u / 2) := (continuous_atomPoint.div_const 2).neg
    have hx : Measurable fun p : ℝ × X => ((p.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp measurable_fst
    have ht' : Measurable fun p : ℝ × X => t p.2 := h.measurable_t.comp measurable_snd
    simp only [hG, he]
    refine (((Complex.measurable_ofReal.comp (h.measurable_c.comp measurable_snd)).div_const _).mul
      ((((continuous_completedRiemannZeta_atomPoint.measurable.comp ht').div_const 2).mul
        (hx.pow (hcP.measurable.comp ht'))).add
      (((hM.measurable.comp ht').div_const 2).mul (hx.pow (hcM.measurable.comp ht'))))).neg.mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul measurable_fst)))
  have hbd : ∀ p : ℝ × X, p.1 ∈ Ioi (0 : ℝ) → ‖G p‖ ≤
      (CΛ / Real.pi * (p.1 ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * p.1))) *
        (|c p.2| / t p.2 ^ 2) := by
    rintro ⟨x, y⟩ hx
    have hx0 : (0 : ℝ) < x := hx
    obtain ⟨hP, hM⟩ := hΛat (t y) (h.one_le y)
    have hn1 : ‖(x : ℂ) ^ (-(atomPoint (t y) / 2)) * e x‖ =
        x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, he, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      congr 2; simp [atomPoint]; norm_num
    have hn2 : ‖(x : ℂ) ^ (-(atomMirror (t y) / 2)) * e x‖ =
        x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, he, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      congr 2; simp [atomMirror]; norm_num
    have hsplit : G (x, y) = -((c y : ℂ) / Real.pi) *
        (completedRiemannZeta (atomPoint (t y)) / 2 * ((x : ℂ) ^ (-(atomPoint (t y) / 2)) * e x) +
          completedRiemannZeta (atomMirror (t y)) / 2 *
            ((x : ℂ) ^ (-(atomMirror (t y) / 2)) * e x)) := by
      simp only [hG]; ring
    rw [hsplit, norm_mul, norm_neg, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpi]
    have hq : 0 ≤ x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x) := by positivity
    calc |c y| / Real.pi *
        ‖completedRiemannZeta (atomPoint (t y)) / 2 * ((x : ℂ) ^ (-(atomPoint (t y) / 2)) * e x) +
          completedRiemannZeta (atomMirror (t y)) / 2 *
            ((x : ℂ) ^ (-(atomMirror (t y) / 2)) * e x)‖
        ≤ |c y| / Real.pi * (CΛ / t y ^ 2 / 2 *
            (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x)) +
          CΛ / t y ^ 2 / 2 * (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x))) := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, norm_div, Complex.norm_two, hn1]; gcongr
          · rw [norm_mul, norm_div, Complex.norm_two, hn2]; gcongr
      _ = _ := by ring
  have hfx : IntegrableOn (fun x : ℝ => CΛ / Real.pi *
      (x ^ (-(1 / 4 : ℝ)) * Real.exp (-(Real.pi * τ ^ 2) * x))) (Ioi 0) := by
    have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 4 : ℝ)) (p := 1)
      (by norm_num) le_rfl (show 0 < Real.pi * τ ^ 2 by positivity)
    simp only [Real.rpow_one, neg_mul] at h0
    exact IntegrableOn.congr_fun (h0.const_mul (CΛ / Real.pi)) (fun x _ => by simp only [neg_mul])
      measurableSet_Ioi
  have hprod : (volume.restrict (Ioi (0 : ℝ))).prod ν =
      (volume.prod ν).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set X)) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hGint : Integrable G ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
    have hdom := hfx.integrable.mul_prod h.integrable
    refine Integrable.mono' hdom hmeasG.aestronglyMeasurable ?_
    rw [hprod]
    refine (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
      (Eventually.of_forall fun p hp => ?_)
    exact hbd p hp.1
  -- the defect is the `y`-integral of `G`
  have hdef : ∀ x : ℝ, spectralMeasureDefect ν c t x * e x = ∫ y, G (x, y) ∂ν := by
    intro x
    simp only [spectralMeasureDefect, hG]
    rw [integral_mul_const, integral_neg, neg_mul]
  have hKint : IntegrableOn (fun x : ℝ => spectralMeasureDefect ν c t x * e x) (Ioi 0) := by
    have := hGint.integral_prod_left
    exact this.congr (Eventually.of_forall fun x => (hdef x).symm)
  refine ⟨hKint, ?_⟩
  -- Fubini and the one-atom Laplace integrals
  have hswap : (∫ x in Ioi (0 : ℝ), spectralMeasureDefect ν c t x * e x) =
      ∫ y, (∫ x in Ioi (0 : ℝ), G (x, y)) ∂ν := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hdef x)]
    exact integral_integral_swap (f := fun x y => G (x, y)) hGint
  have hval : ∀ y, (∫ x in Ioi (0 : ℝ), G (x, y)) = -((c y : ℂ) / Real.pi *
      (completedRiemannZeta (atomPoint (t y)) / 2 * (Complex.Gamma (1 - atomPoint (t y) / 2) *
        ((Real.pi : ℂ) * (τ : ℂ) ^ 2) ^ (-(1 - atomPoint (t y) / 2))) +
      completedRiemannZeta (atomMirror (t y)) / 2 * (Complex.Gamma (1 - atomMirror (t y) / 2) *
        ((Real.pi : ℂ) * (τ : ℂ) ^ 2) ^ (-(1 - atomMirror (t y) / 2))))) := by
    intro y
    have hLP := laplace_cpow_neg_half (atomPoint_re (t y)) hτ
    have hLM := laplace_cpow_neg_half (atomMirror_re (t y)) hτ
    rw [← hLP.2.2, ← hLM.2.2, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hLP.1.const_mul _) (hLM.1.const_mul _), ← integral_const_mul,
      ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [hG, he]
    ring
  rw [hswap, integral_congr_ae (Eventually.of_forall hval), spectralMeasureLaplace,
    ← integral_const_mul, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [atomLaplace]
  ring

end SpectralMeasureLaplaceIdentity


section SpectralMeasureRigidity

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {c t : X → ℝ}

/-- **Radial vanishing of the measure perturbation** under the Abel ζ-mass condition. -/
theorem tendsto_mul_spectralMeasureLaplace_radial (h : SpectralMeasureData ν c t)
    (hA : Tendsto (fun δ => δ * dampedZetaMassMeasure ν c t δ) (𝓝[>] 0) (𝓝 0)) (m : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * spectralMeasureLaplace ν c t ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine squeeze_zero_norm'
      (a := fun ε : ℝ => 3 / Real.pi * dampedZetaMassMeasure ν c t 1 * ε ^ (1 / 2 : ℝ)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : 0 < ε := hε
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have hre : 0 < ((ε : ℂ)).re := by simpa using hε'
      have hb := norm_spectralMeasureLaplace_le h hre
      have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
      rw [hn, Complex.ofReal_re, div_self hε'.ne'] at hb
      rw [norm_mul, hn]
      have e : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hε'.le (by norm_num)]; norm_num
      calc ε * ‖spectralMeasureLaplace ν c t ε‖
          ≤ ε * (3 / Real.pi * ε ^ (-(1 / 2 : ℝ)) * dampedZetaMassMeasure ν c t 1) := by gcongr
        _ = 3 / Real.pi * dampedZetaMassMeasure ν c t 1 * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
        _ = 3 / Real.pi * dampedZetaMassMeasure ν c t 1 * ε ^ (1 / 2 : ℝ) := by rw [e]
    · have h := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
      rw [Real.zero_rpow (by norm_num)] at h
      simpa using (h.mono_left nhdsWithin_le_nhds).const_mul (3 / Real.pi * dampedZetaMassMeasure ν c t 1)
  · set κ : ℝ := (m : ℝ) + 1 with hκdef
    have hκ : 0 < κ := by positivity
    have hA' : Tendsto (fun ε : ℝ => ε / κ * dampedZetaMassMeasure ν c t (ε / κ)) (𝓝[>] 0) (𝓝 0) := by
      have hmap : Tendsto (fun ε : ℝ => ε / κ) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have := (continuous_id.div_const κ).tendsto (0 : ℝ)
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact div_pos hε hκ
      exact hA.comp hmap
    refine squeeze_zero_norm'
      (a := fun ε : ℝ => 3 / Real.pi * κ * (ε / κ * dampedZetaMassMeasure ν c t (ε / κ))) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with
        ε hε hε1
      have hε' : 0 < ε := hε
      set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
      have hre : τ.re = ε := by simp [hτ]
      have him : τ.im = m := by simp [hτ]
      have hτre : 0 < τ.re := by rw [hre]; exact hε'
      have hb := norm_spectralMeasureLaplace_le h hτre
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hn1 : 1 ≤ ‖τ‖ := by
        have := Complex.abs_im_le_norm τ
        rw [him, abs_of_nonneg (by positivity)] at this
        linarith
      have hn2 : ‖τ‖ ≤ κ := by
        have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε', norm_mul, Complex.norm_natCast,
          Complex.norm_I, mul_one] at h
        have := hε1.2
        rw [hκdef]
        linarith
      have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
      have hδ : ε / κ ≤ τ.re / ‖τ‖ := by
        rw [hre]; exact div_le_div_of_nonneg_left hε'.le (by linarith) hn2
      have hmono := dampedZetaMassMeasure_antitone h (div_pos hε' hκ) hδ
      have hM0 : 0 ≤ dampedZetaMassMeasure ν c t (τ.re / ‖τ‖) := integral_nonneg (fun y => by positivity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
      calc ε * ‖spectralMeasureLaplace ν c t τ‖
          ≤ ε * (3 / Real.pi * ‖τ‖ ^ (-(1 / 2 : ℝ)) * dampedZetaMassMeasure ν c t (τ.re / ‖τ‖)) := by
            gcongr
        _ ≤ ε * (3 / Real.pi * 1 * dampedZetaMassMeasure ν c t (ε / κ)) := by gcongr
        _ = 3 / Real.pi * κ * (ε / κ * dampedZetaMassMeasure ν c t (ε / κ)) := by field_simp
    · simpa using hA'.const_mul (3 / Real.pi * κ)


/-- The truncated ζ-mass of a spectral measure: `∫_{t ≤ T} |c| |ζ(½ + it)| dν`. -/
noncomputable def truncatedZetaMassMeasure (ν : Measure X) (c t : X → ℝ) (T : ℝ) : ℝ :=
  ∫ y, (if t y ≤ T then |c y| * ‖riemannZeta (atomPoint (t y))‖ else 0) ∂ν

theorem SpectralMeasureData.integrable_truncated (h : SpectralMeasureData ν c t) (T : ℝ) :
    Integrable (fun y => if t y ≤ T then |c y| * ‖riemannZeta (atomPoint (t y))‖ else 0) ν := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_riemannZeta_atomPoint_le
  have hmeas : Measurable fun y => if t y ≤ T then |c y| * ‖riemannZeta (atomPoint (t y))‖ else 0 :=
    Measurable.ite (measurableSet_le h.measurable_t measurable_const)
      ((h.measurable_c.abs).mul ((continuous_norm.comp continuous_riemannZeta_atomPoint).measurable.comp
        h.measurable_t)) measurable_const
  refine Integrable.mono' (h.integrable.const_mul (B * max T 1 ^ 3)) hmeas.aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  split_ifs with hT
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have ht := h.one_le y
    have htpos : 0 < t y := by linarith
    have hζ := hB (t y) ht
    have hT' : t y ≤ max T 1 := hT.trans (le_max_left _ _)
    calc |c y| * ‖riemannZeta (atomPoint (t y))‖ ≤ |c y| * (B * t y) := by gcongr
      _ = B * t y ^ 3 * (|c y| / t y ^ 2) := by field_simp
      _ ≤ B * max T 1 ^ 3 * (|c y| / t y ^ 2) := by gcongr
  · rw [norm_zero]; positivity

/-- **Abelian bound for spectral measures.**  If `∫_{t ≤ k+1} |c||ζ(½ + it)| dν ≤ η(k + 1) + C` for
every `k`, then the damped ζ-mass is at most `η/(1 − e^{−δ}) + C`. -/
theorem dampedZetaMassMeasure_le_of_truncated (h : SpectralMeasureData ν c t) {η C : ℝ}
    (hS : ∀ k : ℕ, truncatedZetaMassMeasure ν c t ((k : ℝ) + 1) ≤ η * ((k : ℝ) + 1) + C)
    {δ : ℝ} (hδ : 0 < δ) :
    dampedZetaMassMeasure ν c t δ ≤ η / (1 - Real.exp (-δ)) + C := by
  set r := Real.exp (-δ) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h1r : 0 < 1 - r := by linarith
  set a : X → ℝ := fun y => |c y| * ‖riemannZeta (atomPoint (t y))‖ with ha
  have ha0 : ∀ y, 0 ≤ a y := fun y => by positivity
  set G : ℕ → X → ℝ := fun k y => r ^ k * (1 - r) * (if t y ≤ (k : ℝ) + 1 then a y else 0) with hG
  have hG0 : ∀ k y, 0 ≤ G k y := by
    intro k y; simp only [hG]
    exact mul_nonneg (mul_nonneg (pow_nonneg hr0 _) h1r.le) (by split_ifs <;> [exact ha0 y; rfl])
  have hGint : ∀ k, Integrable (G k) ν := fun k => (h.integrable_truncated _).const_mul _
  have hGval : ∀ k, ∫ y, G k y ∂ν = r ^ k * (1 - r) * truncatedZetaMassMeasure ν c t ((k : ℝ) + 1) := by
    intro k; simp only [hG]; rw [integral_const_mul]; rfl
  have hSnn : ∀ T, 0 ≤ truncatedZetaMassMeasure ν c t T := fun T =>
    integral_nonneg (fun y => by dsimp only; split_ifs <;> positivity)
  have hgeo1 : Summable fun k : ℕ => (k : ℝ) * r ^ k := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    simpa using this
  have hgeo0 := summable_geometric_of_lt_one hr0 hr1
  have hmaj : Summable fun k : ℕ => r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C) := by
    have : (fun k : ℕ => r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C)) =
        fun k : ℕ => ((1 - r) * η) * ((k : ℝ) * r ^ k) + ((1 - r) * (η + C)) * r ^ k := by
      ext k; ring
    rw [this]
    exact (hgeo1.mul_left _).add (hgeo0.mul_left _)
  have hcols : Summable fun k => ∫ y, G k y ∂ν := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (hG0 k)) (fun k => ?_) hmaj
    rw [hGval k]
    exact mul_le_mul_of_nonneg_left (hS k) (mul_nonneg (pow_nonneg hr0 _) h1r.le)
  have hpt : ∀ y, a y * Real.exp (-(δ * t y)) ≤ ∑' k, G k y := by
    intro y
    have hx := exp_neg_mul_le_tsum_indicator hδ (x := t y) (by linarith [h.one_le y])
    have e : ∑' k, G k y = a y * ∑' k : ℕ, (if t y ≤ (k : ℝ) + 1 then
        Real.exp (-δ) ^ k * (1 - Real.exp (-δ)) else 0) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp only [hG, hr]
      split_ifs <;> ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hx (ha0 y)
  have hGsum : ∀ y, Summable fun k => G k y := by
    intro y
    refine Summable.of_nonneg_of_le (fun k => hG0 k y) (fun k => ?_)
      ((hgeo0.mul_right (1 - r)).mul_right (a y))
    simp only [hG]
    split_ifs
    · exact le_rfl
    · rw [mul_zero]; exact mul_nonneg (mul_nonneg (pow_nonneg hr0 _) h1r.le) (ha0 y)
  have hGmeas : ∀ k, AEMeasurable (fun y => ENNReal.ofReal (G k y)) ν :=
    fun k => (hGint k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hMint := h.integrable_zetaWeight hδ
  have key : ENNReal.ofReal (dampedZetaMassMeasure ν c t δ) ≤
      ENNReal.ofReal (∑' k, ∫ y, G k y ∂ν) := by
    rw [dampedZetaMassMeasure, ofReal_integral_eq_lintegral_ofReal hMint
      (Eventually.of_forall fun y => by positivity)]
    calc ∫⁻ y, ENNReal.ofReal (|c y| * ‖riemannZeta (atomPoint (t y))‖ *
          Real.exp (-(δ * t y))) ∂ν
        ≤ ∫⁻ y, ENNReal.ofReal (∑' k, G k y) ∂ν :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpt y)
      _ = ∫⁻ y, ∑' k, ENNReal.ofReal (G k y) ∂ν := by
          congr 1; funext y
          exact ENNReal.ofReal_tsum_of_nonneg (fun k => hG0 k y) (hGsum y)
      _ = ∑' k, ∫⁻ y, ENNReal.ofReal (G k y) ∂ν := lintegral_tsum hGmeas
      _ = ∑' k, ENNReal.ofReal (∫ y, G k y ∂ν) := by
          congr 1; funext k
          exact (ofReal_integral_eq_lintegral_ofReal (hGint k)
            (Eventually.of_forall fun y => hG0 k y)).symm
      _ = ENNReal.ofReal (∑' k, ∫ y, G k y ∂ν) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg (hG0 k)) hcols).symm
  have hle : dampedZetaMassMeasure ν c t δ ≤ ∑' k, ∫ y, G k y ∂ν :=
    (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg fun k => integral_nonneg (hG0 k))).mp key
  have hgeo_sum : ∑' k : ℕ, r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C) = η / (1 - r) + C := by
    have e1 : (fun k : ℕ => r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C)) =
        fun k : ℕ => ((1 - r) * η) * ((k : ℝ) * r ^ k) + ((1 - r) * (η + C)) * r ^ k := by
      ext k; ring
    rw [e1, Summable.tsum_add (hgeo1.mul_left _) (hgeo0.mul_left _), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_lt_one hr0 hr1]
    have e2 := tsum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
      (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    rw [e2]
    field_simp
    ring
  calc dampedZetaMassMeasure ν c t δ ≤ ∑' k, ∫ y, G k y ∂ν := hle
    _ ≤ ∑' k : ℕ, r ^ k * (1 - r) * (η * ((k : ℝ) + 1) + C) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hcols hmaj
        rw [hGval k]
        exact mul_le_mul_of_nonneg_left (hS k) (mul_nonneg (pow_nonneg hr0 _) h1r.le)
    _ = η / (1 - r) + C := hgeo_sum

/-- **Sublinear truncated ζ-mass gives the Abel condition** for spectral measures. -/
theorem tendsto_mul_dampedZetaMassMeasure_of_sublinear (h : SpectralMeasureData ν c t)
    (hT : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → truncatedZetaMassMeasure ν c t T ≤ η * T + C) :
    Tendsto (fun δ => δ * dampedZetaMassMeasure ν c t δ) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨C, hC⟩ := hT (ε / 4) (by positivity)
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨min 1 (ε / (4 * (C' + 1))), lt_min one_pos (by positivity), fun δ hδ hdist => ?_⟩
  have hδ0 : 0 < δ := hδ
  rw [Real.dist_eq, sub_zero, abs_of_pos hδ0] at hdist
  have hδ1 : δ < 1 := hdist.trans_le (min_le_left _ _)
  have hδ2 : δ < ε / (4 * (C' + 1)) := hdist.trans_le (min_le_right _ _)
  have hS : ∀ k : ℕ, truncatedZetaMassMeasure ν c t ((k : ℝ) + 1) ≤ ε / 4 * ((k : ℝ) + 1) + C' := by
    intro k
    have := hC ((k : ℝ) + 1) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    linarith [le_max_left C 0]
  have hb := dampedZetaMassMeasure_le_of_truncated h hS hδ0
  have hM0 : 0 ≤ dampedZetaMassMeasure ν c t δ := integral_nonneg (fun y => by positivity)
  have hden : δ / 2 ≤ 1 - Real.exp (-δ) := by
    have h2 : Real.exp (-δ) ≤ 1 / (1 + δ) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp δ])
    have h3 : 1 / (1 + δ) ≤ 1 - δ / 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hdpos : 0 < 1 - Real.exp (-δ) := by linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hq : δ / (1 - Real.exp (-δ)) ≤ 2 := by
    rw [div_le_iff₀ hdpos]; linarith
  have hCδ : C' * δ < ε / 4 := by
    have : (C' + 1) * δ < ε / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hδ2
      nlinarith
    nlinarith
  calc δ * dampedZetaMassMeasure ν c t δ ≤ δ * (ε / 4 / (1 - Real.exp (-δ)) + C') :=
        mul_le_mul_of_nonneg_left hb hδ0.le
    _ = ε / 4 * (δ / (1 - Real.exp (-δ))) + C' * δ := by ring
    _ ≤ ε / 4 * 2 + C' * δ := by gcongr
    _ < ε := by linarith

/-- **Sublinear ζ-mass rigidity for spectral measures (Abel form).**  Let `(X, ν, c, t)` be spectral
data with `Γ̃(s) + 1/(s − 1) − Σ lam(n) n^{−s} = (2(s − ½)/π) ∫ c/((s − ½)² + t²) dν` on `Re s > 1`.
If `δ ∫ |c| |ζ(½ + it)| e^{−δ t} dν → 0` as `δ → 0⁺`, then `lam(n) = Λ(n)` for `n ≥ 2` and RH holds. -/
theorem zeta_mass_sublinear_rigidity_measure [SFinite ν] {lam : ℕ → ℝ}
    (h : SpectralMeasureData ν c t)
    (hA : Tendsto (fun δ => δ * dampedZetaMassMeasure ν c t δ) (𝓝[>] 0) (𝓝 0))
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = spectralMeasureSeries ν c t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  refine weil_defect_rigidity h.oddWeilFunction hsl hid
    (differentiableOn_spectralMeasureLaplace h) (fun τ hτ => ?_)
    (tendsto_mul_spectralMeasureLaplace_radial h hA)
  have hK : (fun x : ℝ => weilDefect (spectralMeasureSeries ν c t) x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) =ᶠ[ae (volume.restrict (Ioi 0))]
      fun x : ℝ => spectralMeasureDefect ν c t x * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    dsimp only
    rw [weilDefect_spectralMeasureSeries h hx]
  obtain ⟨hint, hJ⟩ := spectralMeasureDefect_laplace h hτ
  refine ⟨hint.congr_fun_ae hK.symm, ?_⟩
  rw [hJ, integral_congr_ae hK]

/-- **Sublinear ζ-mass rigidity for spectral measures (counting form).**  With
`∫_{t ≤ T} |c| |ζ(½ + it)| dν = o(T)`, `lam(n) = Λ(n)` for `n ≥ 2` and RH holds. -/
theorem zeta_mass_sublinear_rigidity_measure_of_truncated [SFinite ν] {lam : ℕ → ℝ}
    (h : SpectralMeasureData ν c t)
    (hT : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → truncatedZetaMassMeasure ν c t T ≤ η * T + C)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = spectralMeasureSeries ν c t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis :=
  zeta_mass_sublinear_rigidity_measure h (tendsto_mul_dampedZetaMassMeasure_of_sublinear h hT)
    hsl hid

/-- **ζ-mass rigidity for spectral measures.**  Finite ζ-mass `∫ |c| |ζ(½ + it)| dν < ∞` forces
`lam(n) = Λ(n)` for `n ≥ 2` and RH. -/
theorem zeta_mass_rigidity_measure [SFinite ν] {lam : ℕ → ℝ} (h : SpectralMeasureData ν c t)
    (hZ : Integrable (fun y => |c y| * ‖riemannZeta (atomPoint (t y))‖) ν)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => (lam n : ℂ)) s = spectralMeasureSeries ν c t s) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  refine zeta_mass_sublinear_rigidity_measure h ?_ hsl hid
  set M := ∫ y, |c y| * ‖riemannZeta (atomPoint (t y))‖ ∂ν with hM
  have hbd : ∀ δ : ℝ, 0 < δ → dampedZetaMassMeasure ν c t δ ≤ M := by
    intro δ hδ
    refine integral_mono (h.integrable_zetaWeight hδ) hZ (fun y => ?_)
    have ht : 0 ≤ t y := by linarith [h.one_le y]
    have he : Real.exp (-(δ * t y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    dsimp only
    have : 0 ≤ |c y| * ‖riemannZeta (atomPoint (t y))‖ := by positivity
    nlinarith
  have hup : Tendsto (fun δ : ℝ => δ * M) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_id.mul continuous_const).tendsto (0 : ℝ) (f := fun δ : ℝ => δ * M))
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' ?_ ?_ hup
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_nonneg (le_of_lt hδ) (integral_nonneg fun y => by positivity)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_le_mul_of_nonneg_left (hbd δ hδ) (le_of_lt hδ)

end SpectralMeasureRigidity

end RHTower
