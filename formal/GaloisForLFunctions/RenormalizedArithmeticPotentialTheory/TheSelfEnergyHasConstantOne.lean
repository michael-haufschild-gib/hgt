import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheMatchedStabilityLaw

/-!
# The self-energy has constant one

The archimedean Lévy density `ω(x) = e^{−x/2}/(1 − e^{−2x})` is `1/(2x) + O(1)` at `0`. AES bounds it
by `e^{−1/2}/(2x)` on all of `(0, 1]`, which puts a constant `e^{−1/2}` in front of the self-energy of
an atom. The shifts that separate the atoms `log n`, `n ≤ N`, are at most `δ_N/2`, and there
`ω(x) ≥ e^{−δ_N/4}/(2x)`.

* **Sharp Lévy density** (`archLevyDensity_ge_of_le`): `ω(x) ≥ e^{−s/2}/(2x)` on `(0, s]`.
* **Sharp Lévy gain** (`levyEnergy_ge_of_disjoint_shifts_sharp`, `levyEnergy_atomicTest_ge_sharp`):
  `levyEnergy f ≥ e^{−s/2} log(s/w) ∫ f²` when every shift in `(w, s]` moves the support off
  itself; on atomic tests the gain is `e^{−δ_N/4} log(δ_N/(2w)) ∫ f²`, constant `1 − O(1/N)`.
* **The stability law with constant one** (`markovEnergy_atomicTest_ge_sharp`,
  `sharpAtomicGain_nonneg`, `markovEnergy_atomicTest_nonneg_sharp`): the Markov form of an atomic
  test is nonnegative at every width `w ≤ sharpAtomicWidth N = (δ_N/4) exp(−e^{δ_N/4}(log N + C₀))`.
* **Width exponent one** (`sharpAtomicWidth_ge`): `sharpAtomicWidth N ≥ (δ_N/4) e^{−(3C₀ + 1)/2}/N`.

So the covariant counterterm `log N + O(1)` and the self-energy `log(δ_N/w) + O(1)` are matched with
the same constant, and the admissible width is `c δ_N/N` (AES: `δ_N N^{−2e^{1/2}}`). The remaining
factor `N` is `1/δ_N` itself: the self-energy is counted relative to the spacing because the shifts
beyond `δ_N/2` make distinct atoms overlap. Reaching the spacing means counting the archimedean
interaction between distinct atoms against the prime form.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticEffectivityTheory

/-- **Sharp Lévy density**: `ω(x) ≥ e^{−s/2}/(2x)` on `(0, s]`. -/
theorem archLevyDensity_ge_of_le {x s : ℝ} (hx0 : 0 < x) (hxs : x ≤ s) :
    Real.exp (-(s / 2)) / (2 * x) ≤ archLevyDensity x := by
  unfold archLevyDensity
  have hnum : Real.exp (-(s / 2)) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have hden_pos : 0 < 1 - Real.exp (-2 * x) := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hden : 1 - Real.exp (-2 * x) ≤ 2 * x := by
    have := Real.add_one_le_exp (-2 * x)
    linarith
  rw [div_le_div_iff₀ (by positivity) hden_pos]
  calc Real.exp (-(s / 2)) * (1 - Real.exp (-2 * x))
      ≤ Real.exp (-x / 2) * (2 * x) := by gcongr

/-- **Sharp Lévy gain of disjoint shifts**: `levyEnergy f ≥ e^{−s/2} log(s/w) ∫ f²` when every
shift by `x ∈ (w, s]` moves the support of `f` off itself. -/
theorem levyEnergy_ge_of_disjoint_shifts_sharp {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w s : ℝ} (hw0 : 0 < w) (hws : w ≤ s)
    (hdisj : ∀ x ∈ Set.Ioc w s, ∀ u, f u * f (u + x) = 0) :
    Real.exp (-(s / 2)) * Real.log (s / w) * ∫ u, f u ^ 2 ≤ levyEnergy f := by
  set M : ℝ := ∫ u, f u ^ 2
  set L : ℝ → ℝ := fun x => archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2
  have hLint : IntegrableOn L (Set.Ioi 0) := integrableOn_levyIntegrand hf hfc
  have hsub : Set.Ioc w s ⊆ Set.Ioi 0 := fun x hx => lt_trans hw0 hx.1
  have hstep1 : ∫ x in Set.Ioc w s, L x ≤ ∫ x in Set.Ioi 0, L x :=
    setIntegral_mono_set hLint (levyIntegrand_nonneg f) (Filter.Eventually.of_forall hsub)
  -- on `(w, s]` the integrand is at least `e^{−s/2} M/x`
  have hlow : ∀ x ∈ Set.Ioc w s, Real.exp (-(s / 2)) * M * x⁻¹ ≤ L x := by
    intro x hx
    have hx0 : 0 < x := lt_trans hw0 hx.1
    have hinner := integral_sq_sub_shift_of_disjoint hf.continuous hfc (hdisj x hx)
    have hdens := archLevyDensity_ge_of_le hx0 hx.2
    simp only [L]
    rw [hinner]
    calc Real.exp (-(s / 2)) * M * x⁻¹ = Real.exp (-(s / 2)) / (2 * x) * (2 * M) := by
          field_simp
      _ ≤ archLevyDensity x * (2 * M) := by
          gcongr
  have hcont : ContinuousOn (fun x : ℝ => Real.exp (-(s / 2)) * M * x⁻¹) (Set.Icc w s) :=
    continuousOn_const.mul (continuousOn_inv₀.mono fun x hx => ne_of_gt (lt_of_lt_of_le hw0 hx.1))
  have hlint : IntegrableOn (fun x : ℝ => Real.exp (-(s / 2)) * M * x⁻¹) (Set.Ioc w s) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hstep2 : ∫ x in Set.Ioc w s, Real.exp (-(s / 2)) * M * x⁻¹ ≤ ∫ x in Set.Ioc w s, L x :=
    setIntegral_mono_on hlint (hLint.mono_set hsub) measurableSet_Ioc hlow
  have hval : ∫ x in Set.Ioc w s, Real.exp (-(s / 2)) * M * x⁻¹ =
      Real.exp (-(s / 2)) * Real.log (s / w) * M := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hws,
      integral_inv_of_pos hw0 (lt_of_lt_of_le hw0 hws)]
    ring
  unfold levyEnergy
  rw [← hval]
  exact hstep2.trans hstep1

variable {g : ℝ → ℝ} {w : ℝ}

/-- **Sharp Lévy gain of an atomic test**: for `w ≤ δ_N/4`,
`levyEnergy f ≥ e^{−δ_N/4} log(δ_N/(2w)) ∫ f²`. -/
theorem levyEnergy_atomicTest_ge_sharp (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    Real.exp (-(atomSpacing N / 4)) * Real.log (atomSpacing N / 2 / w) *
        ∫ u, atomicTest N x g u ^ 2 ≤ levyEnergy (atomicTest N x g) := by
  have hδ := atomSpacing_pos hN
  -- shifts in `(w, δ_N/2]` separate the atoms
  have hdisj : ∀ y ∈ Set.Ioc w (atomSpacing N / 2), ∀ u,
      atomicTest N x g u * atomicTest N x g (u + y) = 0 := by
    intro y hy u
    rw [atomicTest, atomicTest, sum_mul_sum]
    refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
    rw [show x m * g (u - Real.log m) * (x n * g (u + y - Real.log n)) =
      x m * x n * (g (u - Real.log m) * g (u + y - Real.log n)) by ring]
    refine mul_eq_zero_of_right _ ?_
    by_contra hne
    have h1 : u - Real.log m ∈ Set.Icc 0 w := by
      by_contra h
      apply hne
      simp only [hgsupp _ h, zero_mul]
    have h2 : u + y - Real.log n ∈ Set.Icc 0 w := by
      by_contra h
      apply hne
      simp only [hgsupp _ h, mul_zero]
    rw [Set.mem_Icc] at h1 h2
    obtain ⟨hy1, hy2⟩ := hy
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · have := atomSpacing_le_log_sub (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 hlt
      linarith
    · linarith
    · have := atomSpacing_le_log_sub (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 hgt
      linarith
  have h := levyEnergy_ge_of_disjoint_shifts_sharp (contDiff_atomicTest hg N x)
    (hasCompactSupport_atomicTest hgsupp N x) hw0 (by linarith) hdisj
  rwa [show atomSpacing N / 2 / 2 = atomSpacing N / 4 by ring] at h

/-- **The stability law with constant one, quantitative form**:
`M(f) ≥ (2θ′(0) + e^{−δ_N/4} log(δ_N/(2w)) − log N − log 4 − 4) ∫ f²`. -/
theorem markovEnergy_atomicTest_ge_sharp (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomSpacing N / 4) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.exp (-(atomSpacing N / 4)) *
        Real.log (atomSpacing N / 2 / w) - (Real.log N + (Real.log 4 + 4))) *
        ∫ u, atomicTest N x g u ^ 2 ≤
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hδ := atomSpacing_pos hN
  have hw' : w < atomSpacing N := by linarith
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hg hgc hgsupp hw' x]
  have hlevy := levyEnergy_atomicTest_ge_sharp hg hgsupp hN hw0 hw x
  have hsq := integral_atomicTest_sq hg hgc hgsupp hw' x
  have hW := atomicWeilForm_le_log N x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hprime : (∫ u, g u ^ 2) * atomicWeilForm N x ≤
      (Real.log N + (Real.log 4 + 4)) * ∫ u, atomicTest N x g u ^ 2 := by
    rw [hsq]
    calc (∫ u, g u ^ 2) * atomicWeilForm N x
        ≤ (∫ u, g u ^ 2) * ((Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
          mul_le_mul_of_nonneg_left hW hG
      _ = _ := by ring
  nlinarith

/-- The **sharp atomic width** `(δ_N/4) exp(−e^{δ_N/4}(log N + log 4 + 4 + 2|θ′(0)|))`. -/
def sharpAtomicWidth (N : ℕ) : ℝ :=
  atomSpacing N / 4 * Real.exp (-(Real.exp (atomSpacing N / 4) *
    (Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0|)))

theorem sharpAtomicWidth_pos {N : ℕ} (hN : 1 ≤ N) : 0 < sharpAtomicWidth N :=
  mul_pos (by linarith [atomSpacing_pos hN]) (Real.exp_pos _)

/-- **The gain beats the covariant counterterm** at every width `0 < w ≤ sharpAtomicWidth N`. -/
theorem sharpAtomicGain_nonneg {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ sharpAtomicWidth N) :
    w ≤ atomSpacing N / 4 ∧ 0 ≤ 2 * gammaHardyPhaseRate 0 + Real.exp (-(atomSpacing N / 4)) *
      Real.log (atomSpacing N / 2 / w) - (Real.log N + (Real.log 4 + 4)) := by
  have hδ := atomSpacing_pos hN
  set X := Real.exp (atomSpacing N / 4) *
    (Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0|)
  have hX : 0 ≤ X := by
    have := Real.log_natCast_nonneg N
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hexp : Real.exp (-X) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ⟨hw.trans (by rw [sharpAtomicWidth]; nlinarith [Real.exp_pos (-X)]), ?_⟩
  have hlog : X ≤ Real.log (atomSpacing N / 2 / w) := by
    have hle : atomSpacing N / 2 / sharpAtomicWidth N ≤ atomSpacing N / 2 / w :=
      div_le_div_of_nonneg_left (by positivity) hw0 hw
    have hval : atomSpacing N / 2 / sharpAtomicWidth N = 2 * Real.exp X := by
      rw [sharpAtomicWidth, Real.exp_neg]
      field_simp
      ring
    have h2 : X ≤ Real.log (2 * Real.exp X) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos X).ne', Real.log_exp]
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
    exact h2.trans (Real.log_le_log (by positivity) (hval ▸ hle))
  have he : Real.exp (-(atomSpacing N / 4)) * Real.exp (atomSpacing N / 4) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Real.exp (-(atomSpacing N / 4)) * X ≤
      Real.exp (-(atomSpacing N / 4)) * Real.log (atomSpacing N / 2 / w) :=
    mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
  have h4 : Real.exp (-(atomSpacing N / 4)) * X =
      Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0| := by
    simp only [X]; rw [← mul_assoc, he, one_mul]
  linarith [neg_abs_le (gammaHardyPhaseRate 0)]

/-- **The stability law with constant one**: every atomic test of width at most
`sharpAtomicWidth N` at the points `log n`, `n ≤ N`, has nonnegative Markov form. -/
theorem markovEnergy_atomicTest_nonneg_sharp (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ sharpAtomicWidth N) (x : ℕ → ℝ) :
    0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  obtain ⟨hw4, hcoef⟩ := sharpAtomicGain_nonneg hN hw0 hw
  have h := markovEnergy_atomicTest_ge_sharp hg hgc hgsupp hN hw0 hw4 x
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg hcoef hint) h

/-- **Width exponent one**: `sharpAtomicWidth N ≥ (δ_N/4) e^{−(3C₀ + 1)/2}/N` with
`C₀ = log 4 + 4 + 2|θ′(0)|`. -/
theorem sharpAtomicWidth_ge {N : ℕ} (hN : 1 ≤ N) :
    atomSpacing N / 4 *
        Real.exp (-((3 * (Real.log 4 + 4 + 2 * |gammaHardyPhaseRate 0|) + 1) / 2)) / N ≤
      sharpAtomicWidth N := by
  unfold sharpAtomicWidth
  set C₀ := Real.log 4 + 4 + 2 * |gammaHardyPhaseRate 0|
  have hC : Real.log 4 + 4 + 2 * |gammaHardyPhaseRate 0| = C₀ := rfl
  set δ := atomSpacing N
  have hδ : 0 < δ := atomSpacing_pos hN
  have hδ1 : δ ≤ 1 := atomSpacing_le_one hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hC₀ : 0 ≤ C₀ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    positivity
  -- `δ_N ≤ 1/N` and `log N ≤ N`
  have hδN : δ ≤ 1 / N := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
    simp only [δ, atomSpacing]
    linarith
  have hlogN : Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN'
  -- `e^{δ/4} ≤ 1 + δ/2`, from `e^{−δ/4} ≥ 1 − δ/4`
  have hexp : Real.exp (δ / 4) ≤ 1 + δ / 2 := by
    have h1 := Real.add_one_le_exp (-(δ / 4))
    have h2 : Real.exp (δ / 4) * Real.exp (-(δ / 4)) = 1 := by rw [← Real.exp_add]; simp
    have h3 : Real.exp (δ / 4) * (1 - δ / 4) ≤ 1 := by
      nlinarith [Real.exp_pos (δ / 4)]
    nlinarith [Real.exp_pos (δ / 4)]
  -- `e^{δ/4}(log N + C₀) ≤ log N + (3C₀ + 1)/2`
  have hkey : Real.exp (δ / 4) * (Real.log N + C₀) ≤ Real.log N + (3 * C₀ + 1) / 2 := by
    have h1 : δ * Real.log N ≤ 1 := by
      calc δ * Real.log N ≤ 1 / N * N := mul_le_mul hδN hlogN hlog0 (by positivity)
        _ = 1 := by field_simp
    have h2 : δ * C₀ ≤ C₀ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ Real.log N + C₀)]
  rw [show Real.log N + (Real.log 4 + 4) + 2 * |gammaHardyPhaseRate 0| = Real.log N + C₀ by
    rw [← hC]; ring, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  calc Real.exp (-((3 * C₀ + 1) / 2))
      ≤ Real.exp (Real.log N - Real.exp (δ / 4) * (Real.log N + C₀)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(Real.exp (δ / 4) * (Real.log N + C₀))) * N := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
        ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
