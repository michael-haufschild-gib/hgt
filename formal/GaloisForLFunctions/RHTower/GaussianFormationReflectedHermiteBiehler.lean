import GaloisForLFunctions.RHTower.GaussianFormationAnchorContinuity
import GaloisForLFunctions.RHTower.HorizontalLogDerivReflectionDominance
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# Hermite–Biehler dominance of the Gaussian Euler–continuum formation

Let `Φₓ(s) = h∞(s) exp(Lₓ(s) + Cₓ(s))` be the zero-free Gaussian Euler–continuum formation, with
`h∞(s) = ½ s π^{-s/2} Γ(s/2)`.  On `Re s > 0`,

`Φₓ'/Φₓ = h∞'/h∞ − Jₓ + Mₓ`,   `h∞'/h∞(s) = 1/s − ½ log π + ½ ψ(s/2)`,

and on the closed right half-plane the Gaussian prime and continuum currents are bounded by the
fixed masses `Kₓ = Σ Λ(n) e^{-πxn²}` and `M⁰ₓ = ∫₁^∞ e^{-πxu²} du`, because `|n^{-s}| ≤ 1`.  The
digamma asymptotic `Re ψ(z) ≥ log |z| − 3/|z|` gives `Re h∞'/h∞(s) ≥ ½ log(|t|/2) − O(1)`.  Hence,
above the height `T₀(x) = 2π exp(2 + 2Kₓ + 2M⁰ₓ)`:

* `Re Φₓ'/Φₓ > 0` on the whole right half-plane;
* `σ ↦ |Φₓ(σ+it)|` is strictly increasing on `(0, ∞)`;
* the reflected formation `Ξₓ(s) = Φₓ(s) + Φₓ(1-s)`, which satisfies `Ξₓ(1-s) = Ξₓ(s)`, has no
  zero in the critical strip off `Re s = ½`, and its zeros on `Re s = ½` are simple;
* for every boundary-phase datum of `Ξₓ` on a disc in the right half-strip, the Hardy relative
  index and the cubic trace of the boundary-phase pair vanish.

The mechanism is an exact positive split: the archimedean rate `½ log |t|` grows, while every
Gaussian-damped prime datum is bounded uniformly in height.
-/

open Complex Filter Topology Set MeasureTheory Metric

namespace RHTower

noncomputable section

/-- Logarithmic derivative of the archimedean half-completion `h∞(s) = ½ s π^{-s/2} Γ(s/2)`. -/
theorem logDeriv_gaussianArchimedeanHalfFactor_eq {s : ℂ} (hs : 0 < s.re) :
    logDeriv gaussianArchimedeanHalfFactor s =
      1 / s - Complex.log (Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hhalf : 0 < (s / 2).re := by
    rw [Complex.div_re]; simp; positivity
  have hGne : ∀ m : ℕ, s / 2 ≠ -↑m := by
    intro m h
    have := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re] at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf1 : (fun z : ℂ => (1/2 : ℂ) * z) s ≠ 0 := by simp [hs0]
  have hf2 : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s ≠ 0 := by
    simp only; exact Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hf3 : (fun z : ℂ => Complex.Gamma (z / 2)) s ≠ 0 := Complex.Gamma_ne_zero hGne
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => (1/2 : ℂ) * z) s := by fun_prop
  have hpowd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
    simpa using this
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    hpowd.differentiableAt
  have hGd : DifferentiableAt ℂ Complex.Gamma (s / 2) := Complex.differentiableAt_Gamma _ hGne
  have hd3 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    hGd.comp s (differentiableAt_id.div_const 2)
  have hfun : gaussianArchimedeanHalfFactor =
      fun z => ((1/2 : ℂ) * z * (Real.pi : ℂ) ^ (-z / 2)) * Complex.Gamma (z / 2) := by
    funext z; rw [gaussianArchimedeanHalfFactor]
  rw [hfun, logDeriv_mul (f := fun z => (1/2 : ℂ) * z * (Real.pi : ℂ) ^ (-z / 2)) s
      (mul_ne_zero hf1 hf2) hf3 (hd1.mul hd2) hd3,
    logDeriv_mul (f := fun z => (1/2 : ℂ) * z) s hf1 hf2 hd1 hd2,
    logDeriv_const_mul s _ (by norm_num), show (fun z : ℂ => z) = id from rfl, logDeriv_id]
  have hl2 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -(Complex.log (Real.pi : ℂ) / 2) := by
    rw [logDeriv_apply, hpowd.deriv]
    field_simp [hf2]
  have hl3 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s = Complex.digamma (s / 2) / 2 := by
    have hc := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z / 2) hGd
      (differentiableAt_id.div_const 2)
    have hdg : deriv (fun z : ℂ => z / 2) s = 1 / 2 := by
      rw [deriv_div_const, deriv_id'']
    simp only [Function.comp_def] at hc
    rw [hc, hdg, Complex.digamma_def]
    ring
  rw [hl2, hl3]
  ring


/-- On `Re s > 0`, `|Im s| ≥ 4`: `Re (h∞'/h∞)(s) ≥ ½ log(|Im s|/2) − 3/|Im s| − ½ log π`. -/
theorem re_logDeriv_gaussianArchimedeanHalfFactor_ge {s : ℂ} (hs : 0 < s.re)
    (ht : 4 ≤ |s.im|) :
    Real.log (|s.im| / 2) / 2 - 3 / |s.im| - Real.log Real.pi / 2 ≤
      (logDeriv gaussianArchimedeanHalfFactor s).re := by
  rw [logDeriv_gaussianArchimedeanHalfFactor_eq hs]
  have hhalf : 0 < (s / 2).re := by
    rw [Complex.div_re]; simp; positivity
  have hnorm : |s.im| / 2 ≤ ‖s / 2‖ := by
    rw [norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm s) (by norm_num)
  have hnorm2 : 2 ≤ ‖s / 2‖ := by linarith
  have hdg := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hhalf hnorm2
  have hre : (Complex.log (s / 2)).re - 3 / ‖s / 2‖ ≤ (Complex.digamma (s / 2)).re := by
    have := (Complex.re_le_norm (Complex.log (s / 2) - Complex.digamma (s / 2)))
    rw [← norm_neg, neg_sub] at this
    have h2 : (Complex.log (s / 2) - Complex.digamma (s / 2)).re ≤ 3 / ‖s / 2‖ :=
      this.trans hdg
    rw [Complex.sub_re] at h2
    linarith
  rw [Complex.log_re] at hre
  have hlog : Real.log (|s.im| / 2) ≤ Real.log ‖s / 2‖ :=
    Real.log_le_log (by linarith) hnorm
  have hinv : 3 / ‖s / 2‖ ≤ 6 / |s.im| := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hone : 0 ≤ (1 / s).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg hs.le (Complex.normSq_nonneg s)
  have hpi : (Complex.log (Real.pi : ℂ) / 2).re = Real.log Real.pi / 2 := by
    rw [Complex.div_re]
    simp [Complex.log_ofReal_re]
    ring
  have hdg2 : (Complex.digamma (s / 2) / 2).re = (Complex.digamma (s / 2)).re / 2 := by
    rw [Complex.div_re]; simp; ring
  rw [Complex.add_re, Complex.sub_re, hpi, hdg2]
  have h6 : 3 / |s.im| = (6 / |s.im|) / 2 := by ring
  rw [h6]
  linarith

/-- Total Gaussian prime-power mass `Kₓ = Σ Λ(n) e^{-πxn²}`. -/
def gaussianVonMangoldtMass (x : ℝ) : ℝ :=
  ∑' n : GaussianEulerIndex, ArithmeticFunction.vonMangoldt n.1 *
    Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2)

theorem gaussianVonMangoldtMass_nonneg (x : ℝ) : 0 ≤ gaussianVonMangoldtMass x :=
  tsum_nonneg fun _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le

/-- `‖Jₓ(s)‖ ≤ Kₓ` on the closed right half-plane. -/
theorem norm_gaussianVonMangoldtCurrent_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖gaussianVonMangoldtCurrent x s‖ ≤ gaussianVonMangoldtMass x := by
  have hbound : ∀ n : GaussianEulerIndex,
      ‖(ArithmeticFunction.vonMangoldt n.1 : ℂ) * (Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) : ℂ) *
          (n.1 : ℂ) ^ (-s)‖ ≤
        ArithmeticFunction.vonMangoldt n.1 * Real.exp (-Real.pi * x * (n.1 : ℝ) ^ 2) := by
    intro n
    have hn1 : (1 : ℝ) ≤ n.1 := by exact_mod_cast le_trans (by norm_num) n.2
    have hc := norm_natCast_cpow_neg_le_one hn1 hs
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.exp_pos _).le) hc
  have hsum := summable_vonMangoldt_mul_gaussian hx
  rw [gaussianVonMangoldtCurrent_eq_tsum_cpow]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsum
  · exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsum).tsum_le_tsum hbound hsum

/-- Continuum Gaussian mass `M⁰ₓ = ∫₁^∞ e^{-πxu²} du`. -/
def gaussianContinuumMass (x : ℝ) : ℝ :=
  ∫ u in Ici (1 : ℝ), Real.exp (-Real.pi * x * u ^ 2)

theorem gaussianContinuumMass_nonneg (x : ℝ) : 0 ≤ gaussianContinuumMass x :=
  setIntegral_nonneg measurableSet_Ici fun _ _ => (Real.exp_pos _).le

/-- `‖Mₓ(s)‖ ≤ M⁰ₓ` on the closed right half-plane. -/
theorem norm_gaussianContinuumCurrent_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖gaussianContinuumCurrent x s‖ ≤ gaussianContinuumMass x := by
  rw [gaussianContinuumCurrent]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on (integrableOn_gaussianContinuumIntegrand hx hs).norm
    (integrableOn_gaussian hx) measurableSet_Ici fun u hu => ?_
  rw [gaussianContinuumIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_natCast_cpow_neg_le_one hu hs)

/-- Dominance height `T₀(x) = 2π exp(2 + 2Kₓ + 2M⁰ₓ)`. -/
def gaussianFormationDominanceHeight (x : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (2 + 2 * gaussianVonMangoldtMass x + 2 * gaussianContinuumMass x)

theorem four_lt_gaussianFormationDominanceHeight (x : ℝ) :
    4 < gaussianFormationDominanceHeight x := by
  have hK := gaussianVonMangoldtMass_nonneg x
  have hM := gaussianContinuumMass_nonneg x
  have he : (1 : ℝ) ≤ Real.exp (2 + 2 * gaussianVonMangoldtMass x + 2 * gaussianContinuumMass x) :=
    Real.one_le_exp (by linarith)
  have hpi := Real.pi_gt_three
  rw [gaussianFormationDominanceHeight]
  nlinarith

/-- **Source-side Hermite–Biehler dominance.**  Above the height `T₀(x)` the Gaussian formation has
logarithmic derivative with positive real part on the whole open right half-plane: the archimedean
growth `½ log |t|` beats the bounded Gaussian prime and continuum currents. -/
theorem re_logDeriv_gaussianFormation_pos {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re)
    (ht : gaussianFormationDominanceHeight x ≤ |s.im|) :
    0 < (logDeriv (gaussianEulerContinuumFormation x) s).re := by
  have h4 := four_lt_gaussianFormationDominanceHeight x
  have hh := re_logDeriv_gaussianArchimedeanHalfFactor_ge hs (by linarith)
  have hJ := norm_gaussianVonMangoldtCurrent_le hx hs.le
  have hM := norm_gaussianContinuumCurrent_le hx hs.le
  have hJre := Complex.re_le_norm (gaussianVonMangoldtCurrent x s)
  have hMre : -‖gaussianContinuumCurrent x s‖ ≤ (gaussianContinuumCurrent x s).re := by
    have := Complex.abs_re_le_norm (gaussianContinuumCurrent x s)
    linarith [neg_abs_le (gaussianContinuumCurrent x s).re]
  set K := gaussianVonMangoldtMass x
  set M := gaussianContinuumMass x
  have hpi := Real.pi_pos
  have hlog : Real.log Real.pi + (2 + 2 * K + 2 * M) ≤ Real.log (|s.im| / 2) := by
    have hle : Real.pi * Real.exp (2 + 2 * K + 2 * M) ≤ |s.im| / 2 := by
      rw [gaussianFormationDominanceHeight] at ht; linarith
    have := Real.log_le_log (by positivity) hle
    rwa [Real.log_mul hpi.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have hinv : 3 / |s.im| < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  rw [logDeriv_gaussianEulerContinuumFormation hx hs, Complex.add_re, Complex.sub_re]
  linarith


/-! ## Instantiation of reflection dominance above `T₀(x)` -/

theorem gaussianFormation_differentiableAt {x : ℝ} (hx : 0 < x) :
    ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (gaussianEulerContinuumFormation x) s :=
  fun _ hs => differentiableAt_gaussianEulerContinuumFormation hx hs

theorem gaussianFormation_ne_zero' (x : ℝ) :
    ∀ s : ℂ, 0 < s.re → gaussianEulerContinuumFormation x s ≠ 0 :=
  fun _ hs => gaussianEulerContinuumFormation_ne_zero x hs

theorem gaussianFormation_conj' {x : ℝ} (hx : 0 < x) :
    ∀ s : ℂ, gaussianEulerContinuumFormation x ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (gaussianEulerContinuumFormation x s) :=
  fun s => gaussianEulerContinuumFormation_conj hx s

theorem gaussianFormation_dominance {x : ℝ} (hx : 0 < x) :
    ∀ s : ℂ, 0 < s.re → gaussianFormationDominanceHeight x ≤ |s.im| →
      0 < (logDeriv (gaussianEulerContinuumFormation x) s).re :=
  fun _ hs ht => re_logDeriv_gaussianFormation_pos hx hs ht

/-- **Horizontal monotonicity above the dominance height.**  For `|t| ≥ T₀(x)` the modulus
`σ ↦ ‖Φₓ(σ+it)‖` is strictly increasing on `(0, ∞)`. -/
theorem strictMonoOn_norm_gaussianFormation_horizontal {x : ℝ} (hx : 0 < x) {t : ℝ}
    (ht : gaussianFormationDominanceHeight x ≤ |t|) :
    StrictMonoOn (fun u : ℝ => ‖gaussianEulerContinuumFormation x ((u : ℂ) + t * I)‖)
      (Ioi 0) :=
  ReflectionDominance.strictMonoOn_norm_horizontal (gaussianFormation_differentiableAt hx)
    (gaussianFormation_ne_zero' x) (gaussianFormation_dominance hx) ht

/-- The reflected Gaussian formation `Ξₓ(s) = Φₓ(s) + Φₓ(1 - s)`; it satisfies `Ξₓ(1-s) = Ξₓ(s)`. -/
def gaussianReflectedFormation (x : ℝ) : ℂ → ℂ :=
  ReflectionDominance.reflected (gaussianEulerContinuumFormation x)

theorem gaussianReflectedFormation_one_sub (x : ℝ) (s : ℂ) :
    gaussianReflectedFormation x (1 - s) = gaussianReflectedFormation x s :=
  ReflectionDominance.reflected_one_sub _ s

/-- **The reflected Gaussian formation satisfies the Riemann hypothesis above `T₀(x)`.**  In the
critical strip at height `|Im s| ≥ T₀(x)`, every zero of `Ξₓ` lies on `Re s = ½`. -/
theorem gaussianReflectedFormation_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1) (hhalf : s.re ≠ 1 / 2) (ht : gaussianFormationDominanceHeight x ≤ |s.im|) :
    gaussianReflectedFormation x s ≠ 0 :=
  ReflectionDominance.reflected_ne_zero (gaussianFormation_differentiableAt hx)
    (gaussianFormation_ne_zero' x) (gaussianFormation_conj' hx) (gaussianFormation_dominance hx)
    h0 h1 hhalf ht

/-- **Simple critical-line zeros above `T₀(x)`.** -/
theorem deriv_gaussianReflectedFormation_ne_zero_of_line {x : ℝ} (hx : 0 < x) {t : ℝ}
    (ht : gaussianFormationDominanceHeight x ≤ |t|)
    (hz : gaussianReflectedFormation x (1 / 2 + t * I) = 0) :
    deriv (gaussianReflectedFormation x) (1 / 2 + t * I) ≠ 0 :=
  ReflectionDominance.deriv_reflected_ne_zero_of_line (gaussianFormation_differentiableAt hx)
    (gaussianFormation_ne_zero' x) (gaussianFormation_conj' hx) (gaussianFormation_dominance hx)
    ht hz

/-- **TG sub-unit gate for the reflected source model above `T₀(x)`.** -/
theorem gaussianReflectedFormation_relativeIndex_eq_zero {x : ℝ} (hx : 0 < x)
    (D : DiscArgumentDatum) (hF : D.F = gaussianReflectedFormation x)
    (hball : ball D.c D.t ⊆
      ReflectionDominance.dominanceRegion (gaussianFormationDominanceHeight x)) :
    restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
        D.circlePhase.datum.projection = 0 ∧
      ContinuousLinearMap.opTrace (restrictedProjectionCubicDefect
        D.circlePhase.datum.conjugateProjection D.circlePhase.datum.projection) = 0 :=
  ReflectionDominance.reflected_relativeIndex_eq_zero (gaussianFormation_differentiableAt hx)
    (gaussianFormation_ne_zero' x) (gaussianFormation_conj' hx) (gaussianFormation_dominance hx)
    D hF hball

/-- **Off-line zeros of the reflected source sit at prime resonances.**  If `Ξₓ(s) = 0` with
`0 < Re s < 1`, `Re s ≠ ½`, `|Im s| ≥ 4`, then on the open horizontal segment between `s` and
`1 - s̄` the Gaussian prime current reaches the archimedean rate:
`Re Jₓ(u+it) ≥ ½ log(|t|/2) − 3/|t| − ½ log π − M⁰ₓ`. -/
theorem exists_resonance_of_gaussianReflectedFormation_eq_zero {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hhalf : s.re ≠ 1 / 2) (ht : 4 ≤ |s.im|)
    (hz : gaussianReflectedFormation x s = 0) :
    ∃ u : ℝ, min s.re (1 - s.re) < u ∧ u < max s.re (1 - s.re) ∧
      Real.log (|s.im| / 2) / 2 - 3 / |s.im| - Real.log Real.pi / 2 - gaussianContinuumMass x ≤
        (gaussianVonMangoldtCurrent x ((u : ℂ) + s.im * I)).re := by
  obtain ⟨u, hu1, hu2, hle⟩ :=
    ReflectionDominance.exists_segment_re_logDeriv_nonpos_of_reflected_eq_zero
      (gaussianFormation_differentiableAt hx) (gaussianFormation_ne_zero' x)
      (gaussianFormation_conj' hx) h0 h1 hhalf hz
  refine ⟨u, hu1, hu2, ?_⟩
  have hu0 : 0 < u := lt_of_le_of_lt (le_min h0.le (by linarith)) hu1
  set w : ℂ := (u : ℂ) + s.im * I with hw
  have hwre : 0 < w.re := by simp [hw, hu0]
  have hwim : w.im = s.im := by simp [hw]
  have hh := re_logDeriv_gaussianArchimedeanHalfFactor_ge hwre (by rw [hwim]; exact ht)
  rw [hwim] at hh
  have hM := norm_gaussianContinuumCurrent_le hx hwre.le
  have hMre : -‖gaussianContinuumCurrent x w‖ ≤ (gaussianContinuumCurrent x w).re := by
    have := Complex.abs_re_le_norm (gaussianContinuumCurrent x w)
    linarith [neg_abs_le (gaussianContinuumCurrent x w).re]
  rw [logDeriv_gaussianEulerContinuumFormation hx hwre, Complex.add_re, Complex.sub_re] at hle
  linarith

/-! ## All heights: the Paley–Wiener tilt -/

/-- On the whole right half-plane, `Re (h∞'/h∞)(s) > -2`.  The factor `s` of `h∞` cancels the pole
of `ψ(s/2)` at `0`: `h∞'/h∞(s) = ψ(s/2+2)/2 − 1/(s+2) − ½ log π`. -/
theorem neg_two_lt_re_logDeriv_gaussianArchimedeanHalfFactor {s : ℂ} (hs : 0 < s.re) :
    -2 < (logDeriv gaussianArchimedeanHalfFactor s).re := by
  rw [logDeriv_gaussianArchimedeanHalfFactor_eq hs]
  set z : ℂ := s / 2 with hz
  have hzre : 0 < z.re := by rw [hz, Complex.div_re]; simp; positivity
  have hne : ∀ w : ℂ, 0 < w.re → ∀ m : ℕ, w ≠ -↑m := by
    intro w hw m h
    have := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hz1re : 0 < (z + 1).re := by simp; linarith
  have hψ1 := Complex.digamma_apply_add_one z (hne z hzre)
  have hψ2 := Complex.digamma_apply_add_one (z + 1) (hne _ hz1re)
  have hz2re : 2 < (z + 1 + 1).re := by simp; linarith
  have hz2norm : 2 ≤ ‖z + 1 + 1‖ := le_trans hz2re.le (Complex.re_le_norm _)
  have hdg := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos
    (by linarith) hz2norm
  have hre : Real.log ‖z + 1 + 1‖ - 3 / ‖z + 1 + 1‖ ≤ (Complex.digamma (z + 1 + 1)).re := by
    have := Complex.re_le_norm (Complex.log (z + 1 + 1) - Complex.digamma (z + 1 + 1))
    rw [← norm_neg, neg_sub] at this
    have h2 := this.trans hdg
    rw [Complex.sub_re, Complex.log_re] at h2
    linarith
  have hlog2 : Real.log 2 ≤ Real.log ‖z + 1 + 1‖ := Real.log_le_log (by norm_num) hz2norm
  have hinv : 3 / ‖z + 1 + 1‖ ≤ 3 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hz0 : z ≠ 0 := by rw [hz]; exact div_ne_zero hs0 two_ne_zero
  have hz10 : z + 1 ≠ 0 := by intro h; rw [h] at hz1re; simp at hz1re
  have hident : 1 / s - Complex.log (Real.pi : ℂ) / 2 + Complex.digamma z / 2 =
      Complex.digamma (z + 1 + 1) / 2 - (z + 1)⁻¹ / 2 - Complex.log (Real.pi : ℂ) / 2 := by
    rw [hψ2, hψ1, hz]
    field_simp
    ring
  rw [hident]
  have hw1 : ((z + 1)⁻¹ / 2).re ≤ 1 / 2 := by
    have hnorm1 : 1 ≤ ‖z + 1‖ := le_trans (by simp; linarith) (Complex.re_le_norm (z + 1))
    have hinv1 : ‖z + 1‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnorm1
    have hle := Complex.re_le_norm ((z + 1)⁻¹ / 2)
    rw [norm_div, norm_inv, Complex.norm_two] at hle
    linarith
  have hpi : (Complex.log (Real.pi : ℂ) / 2).re = Real.log Real.pi / 2 := by
    rw [Complex.div_re]; simp [Complex.log_ofReal_re]; ring
  have hdg2 : (Complex.digamma (z + 1 + 1) / 2).re = (Complex.digamma (z + 1 + 1)).re / 2 := by
    rw [Complex.div_re]; simp; ring
  rw [Complex.sub_re, Complex.sub_re, hpi, hdg2]
  have hlogpi : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi3 := Real.pi_lt_d2
  have hlog2 := Real.log_two_gt_d9
  linarith

/-- Tilt threshold `λₓ = 2 + Kₓ + M⁰ₓ`. -/
def gaussianFormationTiltThreshold (x : ℝ) : ℝ :=
  2 + gaussianVonMangoldtMass x + gaussianContinuumMass x

/-- The Paley–Wiener tilted formation `Φₓ,λ(s) = e^{λ(s-½)} Φₓ(s)`. -/
def tiltedGaussianFormation (x l : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((l : ℂ) * (s - 1 / 2)) * gaussianEulerContinuumFormation x s

theorem tiltedGaussianFormation_differentiableAt {x : ℝ} (hx : 0 < x) (l : ℝ) :
    ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (tiltedGaussianFormation x l) s := by
  intro s hs
  have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((l : ℂ) * (w - 1 / 2))) s := by
    fun_prop
  exact he.mul (differentiableAt_gaussianEulerContinuumFormation hx hs)

theorem tiltedGaussianFormation_ne_zero (x l : ℝ) :
    ∀ s : ℂ, 0 < s.re → tiltedGaussianFormation x l s ≠ 0 :=
  fun _ hs => mul_ne_zero (Complex.exp_ne_zero _) (gaussianEulerContinuumFormation_ne_zero x hs)

theorem tiltedGaussianFormation_conj {x : ℝ} (hx : 0 < x) (l : ℝ) :
    ∀ s : ℂ, tiltedGaussianFormation x l ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (tiltedGaussianFormation x l s) := by
  intro s
  rw [tiltedGaussianFormation, tiltedGaussianFormation, gaussianEulerContinuumFormation_conj hx,
    map_mul, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, map_sub, map_div₀, map_one, map_ofNat]

theorem logDeriv_tiltedGaussianFormation {x : ℝ} (hx : 0 < x) (l : ℝ) {s : ℂ}
    (hs : 0 < s.re) :
    logDeriv (tiltedGaussianFormation x l) s =
      l + logDeriv (gaussianEulerContinuumFormation x) s := by
  have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((l : ℂ) * (w - 1 / 2))) s := by
    fun_prop
  rw [show tiltedGaussianFormation x l = fun w => Complex.exp ((l : ℂ) * (w - 1 / 2)) *
      gaussianEulerContinuumFormation x w from rfl,
    logDeriv_mul (f := fun w : ℂ => Complex.exp ((l : ℂ) * (w - 1 / 2)))
      (g := gaussianEulerContinuumFormation x) s (Complex.exp_ne_zero _)
      (gaussianEulerContinuumFormation_ne_zero x hs) he
      (differentiableAt_gaussianEulerContinuumFormation hx hs)]
  congr 1
  rw [logDeriv_apply]
  have hd : HasDerivAt (fun w : ℂ => Complex.exp ((l : ℂ) * (w - 1 / 2)))
      (Complex.exp ((l : ℂ) * (s - 1 / 2)) * (l : ℂ)) s := by
    have := ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_mul (l : ℂ)
    simpa using this.cexp
  rw [hd.deriv]
  field_simp [Complex.exp_ne_zero]

/-- **All-height source dominance.**  For every tilt `λ ≥ λₓ`, the tilted formation has
logarithmic derivative with positive real part on the whole open right half-plane. -/
theorem re_logDeriv_tiltedGaussianFormation_pos {x : ℝ} (hx : 0 < x) {l : ℝ}
    (hl : gaussianFormationTiltThreshold x ≤ l) {s : ℂ} (hs : 0 < s.re) :
    0 < (logDeriv (tiltedGaussianFormation x l) s).re := by
  have hh := neg_two_lt_re_logDeriv_gaussianArchimedeanHalfFactor hs
  have hJ := norm_gaussianVonMangoldtCurrent_le hx hs.le
  have hM := norm_gaussianContinuumCurrent_le hx hs.le
  have hJre := Complex.re_le_norm (gaussianVonMangoldtCurrent x s)
  have hMre : -‖gaussianContinuumCurrent x s‖ ≤ (gaussianContinuumCurrent x s).re := by
    have := Complex.abs_re_le_norm (gaussianContinuumCurrent x s)
    linarith [neg_abs_le (gaussianContinuumCurrent x s).re]
  rw [gaussianFormationTiltThreshold] at hl
  rw [logDeriv_tiltedGaussianFormation hx l hs, logDeriv_gaussianEulerContinuumFormation hx hs,
    Complex.add_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re]
  linarith

/-- The reflected tilted formation
`Ξₓ,λ(s) = e^{λ(s-½)} Φₓ(s) + e^{λ(½-s)} Φₓ(1-s)`, with `Ξₓ,λ(1-s) = Ξₓ,λ(s)`. -/
def tiltedGaussianReflectedFormation (x l : ℝ) : ℂ → ℂ :=
  ReflectionDominance.reflected (tiltedGaussianFormation x l)

/-- **The tilted reflected formation satisfies the Riemann hypothesis at every height.**  For
`λ ≥ λₓ`, every zero of `Ξₓ,λ` in the open critical strip lies on `Re s = ½`. -/
theorem tiltedGaussianReflectedFormation_ne_zero {x : ℝ} (hx : 0 < x) {l : ℝ}
    (hl : gaussianFormationTiltThreshold x ≤ l) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hhalf : s.re ≠ 1 / 2) : tiltedGaussianReflectedFormation x l s ≠ 0 :=
  ReflectionDominance.reflected_ne_zero (T₀ := 0) (tiltedGaussianFormation_differentiableAt hx l)
    (tiltedGaussianFormation_ne_zero x l) (tiltedGaussianFormation_conj hx l)
    (fun _ hs _ => re_logDeriv_tiltedGaussianFormation_pos hx hl hs) h0 h1 hhalf (abs_nonneg _)

/-- Every critical-line zero of the tilted reflected formation is simple. -/
theorem deriv_tiltedGaussianReflectedFormation_ne_zero_of_line {x : ℝ} (hx : 0 < x) {l : ℝ}
    (hl : gaussianFormationTiltThreshold x ≤ l) {t : ℝ}
    (hz : tiltedGaussianReflectedFormation x l (1 / 2 + t * I) = 0) :
    deriv (tiltedGaussianReflectedFormation x l) (1 / 2 + t * I) ≠ 0 :=
  ReflectionDominance.deriv_reflected_ne_zero_of_line (T₀ := 0)
    (tiltedGaussianFormation_differentiableAt hx l) (tiltedGaussianFormation_ne_zero x l)
    (tiltedGaussianFormation_conj hx l)
    (fun _ hs _ => re_logDeriv_tiltedGaussianFormation_pos hx hl hs) (abs_nonneg _) hz

/-- **TG sub-unit gate at every height.**  Every Hardy boundary-phase pair of `Ξₓ,λ`, `λ ≥ λₓ`, on
a disc in the right half of the critical strip has vanishing relative index and cubic trace. -/
theorem tiltedGaussianReflectedFormation_relativeIndex_eq_zero {x : ℝ} (hx : 0 < x) {l : ℝ}
    (hl : gaussianFormationTiltThreshold x ≤ l) (D : DiscArgumentDatum)
    (hF : D.F = tiltedGaussianReflectedFormation x l)
    (hball : ball D.c D.t ⊆ ReflectionDominance.dominanceRegion 0) :
    restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
        D.circlePhase.datum.projection = 0 ∧
      ContinuousLinearMap.opTrace (restrictedProjectionCubicDefect
        D.circlePhase.datum.conjugateProjection D.circlePhase.datum.projection) = 0 :=
  ReflectionDominance.reflected_relativeIndex_eq_zero
    (tiltedGaussianFormation_differentiableAt hx l) (tiltedGaussianFormation_ne_zero x l)
    (tiltedGaussianFormation_conj hx l)
    (fun _ hs _ => re_logDeriv_tiltedGaussianFormation_pos hx hl hs) D hF hball

end

end RHTower
