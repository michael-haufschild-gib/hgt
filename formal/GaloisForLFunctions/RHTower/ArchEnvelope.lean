/-
Derivatives of the archimedean envelopes on the critical strip.

On the strip the χ-twisted envelope collapses, `archFactor·χ = archFactor(1−·)`, so both
envelopes of the completed carrier's oscillation decomposition are the single function
`archFactor` at reflected arguments.  Its derivative has the closed logarithmic form through
the digamma function, `Γ_ℝ′(s) = Γ_ℝ(s)·(ψ(s/2) − log π)/2`, giving the canonical derivative
`archFactorDeriv` and discharging every differentiability and derivative-continuity face of
the carrier first-moment bound.  What remains of the first-moment cancellation face are sup
bounds for `archFactor` and `archFactorDeriv` along the line — digamma-scale data — and the
single non-oscillating resonance moment.
-/
import GaloisForLFunctions.RHTower.FirstMoment

open Complex Metric

namespace RHTower

/-- On the strip the χ-twisted envelope collapses to the reflected envelope:
`archFactor·χ = archFactor(1−·)` wherever `Γ_ℝ ≠ 0`. -/
theorem archFactor_mul_zetaChi {s : ℂ} (hG : Complex.Gammaℝ s ≠ 0) :
    archFactor s * zetaChi s = archFactor (1 - s) := by
  unfold archFactor zetaChi
  field_simp
  ring

/-- Real part of the half point. -/
theorem re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [Complex.div_re]
  simp
  ring

/-- The digamma function is continuous on the right half plane (no poles of `Γ` there). -/
theorem digamma_continuousOn_re_pos :
    ContinuousOn Complex.digamma {z : ℂ | 0 < z.re} := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m hc
    rw [hc] at hz
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hz
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
    fun z hz => (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have hderivcont : ContinuousOn (deriv Complex.Gamma) {z : ℂ | 0 < z.re} :=
    (hΓdiff.analyticOnNhd hUopen).deriv.continuousOn
  have hΓne : ∀ z ∈ {z : ℂ | 0 < z.re}, Complex.Gamma z ≠ 0 :=
    fun z hz => Complex.Gamma_ne_zero (hne z hz)
  have hdef : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
    funext z
    rw [Complex.digamma_def, logDeriv_apply]
  rw [hdef]
  exact hderivcont.div hΓdiff.continuousOn hΓne

/-- **Logarithmic derivative of `Γ_ℝ`.**  On the right half plane,
`Γ_ℝ′(s) = Γ_ℝ(s)·(ψ(s/2) − log π)/2`. -/
theorem hasDerivAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Complex.Gammaℝ
      (Complex.Gammaℝ s *
        (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)) s := by
  have h2 : 0 < (s / 2).re := by
    rw [re_div_two]
    linarith
  have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hc
    rw [hc] at h2
    simp only [Complex.neg_re, Complex.natCast_re] at h2
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hpole
  have hGdiff : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ hpole
  have hψ : deriv Complex.Gamma (s / 2) =
      Complex.Gamma (s / 2) * Complex.digamma (s / 2) := by
    rw [show Complex.digamma (s / 2) = logDeriv Complex.Gamma (s / 2) from
      congrFun Complex.digamma_def _, logDeriv_apply]
    field_simp
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have hΓcomp : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
      (Complex.Gamma (s / 2) * Complex.digamma (s / 2) * ((1 : ℂ) / 2)) s := by
    have hcomp := HasDerivAt.comp s hGdiff.hasDerivAt hhalf
    simpa [Function.comp, hψ] using hcomp
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hlin : HasDerivAt (fun z : ℂ => Complex.log (Real.pi : ℂ) * (-z / 2))
      (Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2)) s := by
    simpa using
      ((hasDerivAt_id s).neg.div_const (2 : ℂ)).const_mul (Complex.log (Real.pi : ℂ))
  have hpow : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * (Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2))) s := by
    have hfun : (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) =
        fun z : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-z / 2)) := by
      funext z
      rw [Complex.cpow_def_of_ne_zero hπ0]
    rw [hfun, show (Real.pi : ℂ) ^ (-s / 2) =
      Complex.exp (Complex.log (Real.pi : ℂ) * (-s / 2)) from
      Complex.cpow_def_of_ne_zero hπ0 _]
    exact hlin.cexp
  have hmul := hpow.mul hΓcomp
  have hval : ((Real.pi : ℂ) ^ (-s / 2) * (Complex.log (Real.pi : ℂ) * (-(1 : ℂ) / 2))) *
        Complex.Gamma (s / 2) +
      (Real.pi : ℂ) ^ (-s / 2) *
        (Complex.Gamma (s / 2) * Complex.digamma (s / 2) * ((1 : ℂ) / 2)) =
      Complex.Gammaℝ s *
        (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) := by
    rw [Complex.Gammaℝ_def, show Complex.log (Real.pi : ℂ) =
      ((Real.log Real.pi : ℝ) : ℂ) from (Complex.ofReal_log Real.pi_pos.le).symm]
    ring
  have hfn := hval ▸ hmul
  exact hfn.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun z => Complex.Gammaℝ_def z)

/-- The canonical derivative of `archFactor`: product rule through the logarithmic derivative
of `Γ_ℝ`. -/
noncomputable def archFactorDeriv (s : ℂ) : ℂ :=
  (2 * s - 1) / 2 * Complex.Gammaℝ s +
    s * (s - 1) / 2 *
      (Complex.Gammaℝ s * (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2))

theorem hasDerivAt_archFactor_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt archFactor (archFactorDeriv s) s := by
  have hpoly : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((2 * s - 1) / 2) s := by
    have h1 : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
      (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
    have h2 := h1.div_const (2 : ℂ)
    convert h2 using 1
    ring
  have hmul := hpoly.mul (hasDerivAt_Gammaℝ_of_re_pos hs)
  unfold archFactor
  convert hmul using 1

/-- The completed archimedean envelope is analytic on the open right half plane. -/
theorem archFactor_analyticOnNhd_re_pos :
    AnalyticOnNhd ℂ archFactor {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
  exact (hasDerivAt_archFactor_of_re_pos hz).differentiableAt.differentiableWithinAt

/-- Continuity of the canonical envelope derivative on the right half plane. -/
theorem continuousOn_archFactorDeriv :
    ContinuousOn archFactorDeriv {z : ℂ | 0 < z.re} := by
  have hΓℝ : ContinuousOn Complex.Gammaℝ {z : ℂ | 0 < z.re} := fun z hz =>
    (hasDerivAt_Gammaℝ_of_re_pos hz).differentiableAt.continuousAt.continuousWithinAt
  have hmaps : Set.MapsTo (fun z : ℂ => z / 2) {z : ℂ | 0 < z.re} {z : ℂ | 0 < z.re} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [re_div_two]
    linarith
  have hψ : ContinuousOn (fun z : ℂ => Complex.digamma (z / 2)) {z : ℂ | 0 < z.re} :=
    digamma_continuousOn_re_pos.comp (continuous_id.div_const (2 : ℂ)).continuousOn hmaps
  unfold archFactorDeriv
  exact (((by fun_prop : Continuous fun z : ℂ => (2 * z - 1) / 2).continuousOn).mul hΓℝ).add
    (((by fun_prop : Continuous fun z : ℂ => z * (z - 1) / 2).continuousOn).mul
      (hΓℝ.mul ((hψ.div_const 2).sub continuousOn_const)))

/-- The critical line as a differentiable path: `d/du linePt u = i`. -/
theorem hasDerivAt_linePt (u : ℝ) : HasDerivAt (fun u : ℝ => linePt u) Complex.I u := by
  unfold linePt
  simpa using
    (((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_add
      (((1 / 2 : ℝ) : ℂ)))

/-- Line derivative of the direct envelope. -/
theorem hasDerivAt_archFactor_line (u : ℝ) :
    HasDerivAt (fun u : ℝ => archFactor (linePt u))
      (archFactorDeriv (linePt u) * Complex.I) u := by
  have hre : 0 < (linePt u).re := by
    rw [linePt_re]
    norm_num
  have hcomp := HasDerivAt.comp u (hasDerivAt_archFactor_of_re_pos hre) (hasDerivAt_linePt u)
  simpa [Function.comp] using hcomp

/-- Line derivative of the reflected envelope. -/
theorem hasDerivAt_archFactor_line_reflected (u : ℝ) :
    HasDerivAt (fun u : ℝ => archFactor (1 - linePt u))
      (archFactorDeriv (1 - linePt u) * -Complex.I) u := by
  have hre : 0 < (1 - linePt u).re := by
    simp [Complex.sub_re, linePt_re]
    norm_num
  have hinner : HasDerivAt (fun u : ℝ => 1 - linePt u) (-Complex.I) u :=
    (hasDerivAt_linePt u).const_sub 1
  have hcomp := HasDerivAt.comp u (hasDerivAt_archFactor_of_re_pos hre) hinner
  simpa [Function.comp] using hcomp

/-- **First-moment bound for the completed carrier from sup data only.**  All
differentiability faces are discharged by the canonical envelope calculus: the certificate
inputs are two sup bounds for `archFactor` and two for `archFactorDeriv` along the line and
its reflection, and one bound `Cmain` for the non-oscillating resonance moment. -/
theorem abs_integral_re_completedGN_line_le_of_sups {N : ℕ} (hN : 1 ≤ N) {α β : ℝ}
    (hαβ : α ≤ β) {M₀ M₁ Cmain : ℝ}
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc α β, ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hCmain : ‖(∫ u in α..β, archFactor (linePt u)) +
        ∫ u in α..β, archFactor (1 - linePt u)‖ ≤ Cmain) :
    |∫ u in α..β, (completedGN N (linePt u)).re| ≤
      Cmain + ∑ n ∈ Finset.Ioc 1 N, (n : ℝ) ^ (-(1/2 : ℝ)) *
        (2 * (2 * M₀ + (β - α) * M₁) / Real.log n) := by
  have hGne : ∀ u : ℝ, Complex.Gammaℝ (linePt u) ≠ 0 := fun u =>
    Gammaℝ_ne_zero_of_re_pos (by rw [linePt_re]; norm_num)
  have hrefl_eq : (fun u : ℝ => archFactor (linePt u) * zetaChi (linePt u)) =
      fun u : ℝ => archFactor (1 - linePt u) :=
    funext fun u => archFactor_mul_zetaChi (hGne u)
  have hlineC : Continuous fun u : ℝ => linePt u := by
    unfold linePt
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hmaps_line : Set.MapsTo (fun u : ℝ => linePt u) (Set.uIcc α β)
      {z : ℂ | 0 < z.re} := by
    intro u _
    simp only [Set.mem_setOf_eq, linePt_re]
    norm_num
  have hmaps_refl : Set.MapsTo (fun u : ℝ => 1 - linePt u) (Set.uIcc α β)
      {z : ℂ | 0 < z.re} := by
    intro u _
    simp [Complex.sub_re, linePt_re]
    norm_num
  have hdirC : ContinuousOn (fun u : ℝ => archFactorDeriv (linePt u) * Complex.I)
      (Set.uIcc α β) :=
    (continuousOn_archFactorDeriv.comp hlineC.continuousOn hmaps_line).mul continuousOn_const
  have hrefC : ContinuousOn (fun u : ℝ => archFactorDeriv (1 - linePt u) * -Complex.I)
      (Set.uIcc α β) :=
    (continuousOn_archFactorDeriv.comp
      (continuous_const.sub hlineC).continuousOn hmaps_refl).mul continuousOn_const
  have hCmain' : ‖(∫ u in α..β, archFactor (linePt u)) +
      ∫ u in α..β, archFactor (linePt u) * zetaChi (linePt u)‖ ≤ Cmain := by
    rw [show (∫ u in α..β, archFactor (linePt u) * zetaChi (linePt u)) =
      ∫ u in α..β, archFactor (1 - linePt u) from
      intervalIntegral.integral_congr fun u _ => archFactor_mul_zetaChi (hGne u)]
    exact hCmain
  refine abs_integral_re_completedGN_line_le hN hαβ
    (fun u _ => hasDerivAt_archFactor_line u)
    (fun u _ => hrefl_eq.symm ▸ hasDerivAt_archFactor_line_reflected u)
    hdirC hrefC hM₀ ?_ ?_ ?_ hCmain'
  · intro u hu
    rw [archFactor_mul_zetaChi (hGne u)]
    exact hM₀r u hu
  · intro u hu
    rw [norm_mul, Complex.norm_I, mul_one]
    exact hM₁ u hu
  · intro u hu
    rw [norm_mul, norm_neg, Complex.norm_I, mul_one]
    exact hM₁r u hu

/-- Named-budget form of `abs_integral_re_completedGN_line_le_of_sups`. -/
theorem abs_integral_re_completedGN_line_le_firstMomentBudget_of_sups
    {N : ℕ} (hN : 1 ≤ N) {α β : ℝ} (hαβ : α ≤ β) {M₀ M₁ Cmain : ℝ}
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc α β, ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hCmain : ‖(∫ u in α..β, archFactor (linePt u)) +
        ∫ u in α..β, archFactor (1 - linePt u)‖ ≤ Cmain) :
    |∫ u in α..β, (completedGN N (linePt u)).re| ≤
      completedGNFirstMomentBudget N (β - α) M₀ M₁ Cmain := by
  simpa [completedGNFirstMomentBudget] using
    abs_integral_re_completedGN_line_le_of_sups hN hαβ hM₀ hM₀r hM₁ hM₁r hCmain

/-- Monotone named-budget form of `abs_integral_re_completedGN_line_le_of_sups`: after proving
the analytic estimate with sharp scalar inputs, the target first-moment budget may use any larger
length, envelope, derivative, and resonance scalars. -/
theorem abs_integral_re_completedGN_line_le_firstMomentBudget_of_sups_mono
    {N : ℕ} (hN : 1 ≤ N) {α β L M₀ M₀' M₁ M₁' Cmain Cmain' : ℝ}
    (hαβ : α ≤ β)
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀)
    (hM₀r : ∀ u ∈ Set.Icc α β, ‖archFactor (1 - linePt u)‖ ≤ M₀)
    (hM₁ : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (linePt u)‖ ≤ M₁)
    (hM₁r : ∀ u ∈ Set.Icc α β, ‖archFactorDeriv (1 - linePt u)‖ ≤ M₁)
    (hCmain : ‖(∫ u in α..β, archFactor (linePt u)) +
        ∫ u in α..β, archFactor (1 - linePt u)‖ ≤ Cmain)
    (hL : β - α ≤ L) (hM₀le : M₀ ≤ M₀') (hM₁le : M₁ ≤ M₁')
    (hCmainle : Cmain ≤ Cmain') :
    |∫ u in α..β, (completedGN N (linePt u)).re| ≤
      completedGNFirstMomentBudget N L M₀' M₁' Cmain' := by
  have hbase :=
    abs_integral_re_completedGN_line_le_firstMomentBudget_of_sups
      hN hαβ hM₀ hM₀r hM₁ hM₁r hCmain
  have hM₁0 : 0 ≤ M₁ := by
    exact le_trans (norm_nonneg _) (hM₁ α ⟨le_rfl, hαβ⟩)
  exact le_trans hbase
    (completedGNFirstMomentBudget_mono N (by linarith) hL hM₀le hM₁0 hM₁le hCmainle)

end RHTower

namespace RHTower

/-- The digamma function is analytic on the right half plane: it is the quotient of the
analytic `Γ′` by the nonvanishing analytic `Γ`. -/
theorem digamma_analyticOnNhd_re_pos :
    AnalyticOnNhd ℂ Complex.digamma {z : ℂ | 0 < z.re} := by
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ z ∈ {z : ℂ | 0 < z.re}, ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro z hz m hc
    rw [hc] at hz
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re] at hz
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
    fun z hz => (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have hΓan : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
    hΓdiff.analyticOnNhd hUopen
  have hdef : Complex.digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
    funext z
    rw [Complex.digamma_def, logDeriv_apply]
  rw [hdef]
  exact hΓan.deriv.div hΓan (fun z hz => Complex.Gamma_ne_zero (hne z hz))

/-- Continuity of the trigamma layer `ψ′ = deriv digamma` on the right half plane. -/
theorem continuousOn_deriv_digamma_re_pos :
    ContinuousOn (deriv Complex.digamma) {z : ℂ | 0 < z.re} :=
  digamma_analyticOnNhd_re_pos.deriv.continuousOn

/-- The canonical second derivative of `archFactor`: substituting `Γ_ℝ′ = Γ_ℝ·Ψ` with
`Ψ = ψ(s/2)/2 − (log π)/2` into the product rule collapses everything onto the single factor
`Γ_ℝ`. -/
noncomputable def archFactorDeriv2 (s : ℂ) : ℂ :=
  Complex.Gammaℝ s *
    (1 + (2 * s - 1) * (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
      + s * (s - 1) / 2 * (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) ^ 2
      + s * (s - 1) / 2 * deriv Complex.digamma (s / 2) / 4)

theorem hasDerivAt_archFactorDeriv_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt archFactorDeriv (archFactorDeriv2 s) s := by
  have h2 : 0 < (s / 2).re := by
    rw [re_div_two]
    linarith
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have hψat : HasDerivAt Complex.digamma (deriv Complex.digamma (s / 2)) (s / 2) :=
    (digamma_analyticOnNhd_re_pos (s / 2) h2).differentiableAt.hasDerivAt
  have hψcomp : HasDerivAt (fun z : ℂ => Complex.digamma (z / 2))
      (deriv Complex.digamma (s / 2) * ((1 : ℂ) / 2)) s := by
    have hcomp := HasDerivAt.comp s hψat hhalf
    simpa [Function.comp] using hcomp
  have hΨ : HasDerivAt
      (fun z : ℂ => Complex.digamma (z / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
      (deriv Complex.digamma (s / 2) * ((1 : ℂ) / 2) / 2) s :=
    (hψcomp.div_const 2).sub_const _
  have hG' := hasDerivAt_Gammaℝ_of_re_pos hs
  have hpoly1 : HasDerivAt (fun z : ℂ => (2 * z - 1) / 2) ((1 : ℂ)) s := by
    have h1 : HasDerivAt (fun z : ℂ => 2 * z - 1) ((2 : ℂ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).sub_const (1 : ℂ)
    simpa using h1.div_const (2 : ℂ)
  have hpoly2 : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((2 * s - 1) / 2) s := by
    have h1 : HasDerivAt (fun z : ℂ => z * (z - 1)) (1 * (s - 1) + s * 1) s :=
      (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
    have h2' := h1.div_const (2 : ℂ)
    convert h2' using 1
    ring
  have hA := hpoly1.mul hG'
  have hB := hpoly2.mul (hG'.mul hΨ)
  have htotal := hA.add hB
  unfold archFactorDeriv
  convert htotal using 1
  unfold archFactorDeriv2
  simp only [Pi.mul_apply]
  ring

end RHTower
