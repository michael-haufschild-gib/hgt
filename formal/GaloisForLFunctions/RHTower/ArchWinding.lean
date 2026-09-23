/-
The archimedean winding phase on the critical line.

Along the line the envelope `archFactor(linePt u)` never vanishes, so its logarithmic
derivative `w = archFactor′/archFactor` is defined and continuous; the real part of `w` is the
instantaneous winding rate of the envelope's phase.  Integrating the rate gives a global phase
primitive, and dividing the envelope by the resulting unimodular character leaves a function
whose derivative is controlled by `Im w` alone — the modulus variation.  Van der Corput's
first-derivative bound then converts a floor on the winding rate into cancellation of the
envelope's first moment: the resonance moment of the completed carrier decays like the
reciprocal winding rate, `≈ 2/log(u/2π)` by the digamma vertical bounds.
-/
import GaloisForLFunctions.RHTower.ArchEnvelope

open Complex Metric

namespace RHTower

/-- The envelope never vanishes on the critical line. -/
theorem archFactor_linePt_ne_zero (u : ℝ) : archFactor (linePt u) ≠ 0 := by
  apply archFactor_ne_zero
  · intro h0
    have h := congrArg Complex.re h0
    rw [linePt_re] at h
    norm_num at h
  · intro h1
    have h := congrArg Complex.re h1
    rw [linePt_re] at h
    norm_num at h
  · exact Gammaℝ_ne_zero_of_re_pos (by rw [linePt_re]; norm_num)

/-- Line derivative of the canonical envelope derivative. -/
theorem hasDerivAt_archFactorDeriv_line (u : ℝ) :
    HasDerivAt (fun u : ℝ => archFactorDeriv (linePt u))
      (archFactorDeriv2 (linePt u) * Complex.I) u := by
  have hre : 0 < (linePt u).re := by
    rw [linePt_re]
    norm_num
  have hcomp :=
    HasDerivAt.comp u (hasDerivAt_archFactorDeriv_of_re_pos hre) (hasDerivAt_linePt u)
  simpa [Function.comp] using! hcomp

/-- The complex winding datum `w = archFactor′/archFactor` along the line. -/
noncomputable def archWinding (u : ℝ) : ℂ :=
  archFactorDeriv (linePt u) / archFactor (linePt u)

/-- Derivative of the winding datum along the line. -/
noncomputable def archWindingDeriv (u : ℝ) : ℂ :=
  Complex.I * (archFactorDeriv2 (linePt u) * archFactor (linePt u)
    - archFactorDeriv (linePt u) ^ (2 : ℕ)) / archFactor (linePt u) ^ (2 : ℕ)

theorem hasDerivAt_archWinding (u : ℝ) :
    HasDerivAt archWinding (archWindingDeriv u) u := by
  have hdiv := (hasDerivAt_archFactorDeriv_line u).div (hasDerivAt_archFactor_line u)
    (archFactor_linePt_ne_zero u)
  have hval : (archFactorDeriv2 (linePt u) * Complex.I * archFactor (linePt u)
      - archFactorDeriv (linePt u) * (archFactorDeriv (linePt u) * Complex.I))
      / archFactor (linePt u) ^ (2 : ℕ) = archWindingDeriv u := by
    unfold archWindingDeriv
    ring
  unfold archWinding
  exact hval ▸ hdiv

/-- The envelope's derivative is the envelope times the winding datum. -/
theorem archFactorDeriv_eq_mul_archWinding (u : ℝ) :
    archFactorDeriv (linePt u) = archFactor (linePt u) * archWinding u := by
  unfold archWinding
  rw [mul_comm, div_mul_cancel₀ _ (archFactor_linePt_ne_zero u)]

/-- The winding rate: the phase velocity of the envelope along the line. -/
noncomputable def windingRate (u : ℝ) : ℝ := (archWinding u).re

/-- Curvature of the winding: the derivative of the winding rate. -/
noncomputable def windingRateDeriv (u : ℝ) : ℝ := (archWindingDeriv u).re

theorem hasDerivAt_windingRate (u : ℝ) :
    HasDerivAt windingRate (windingRateDeriv u) u := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_archWinding u)
  unfold windingRate windingRateDeriv
  simpa [Function.comp] using! h

theorem continuous_windingRate : Continuous windingRate := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (hasDerivAt_windingRate u).continuousAt

/-- The winding phase: the primitive of the winding rate from a basepoint. -/
noncomputable def windingPhase (γ u : ℝ) : ℝ := ∫ t in γ..u, windingRate t

theorem hasDerivAt_windingPhase (γ u : ℝ) :
    HasDerivAt (windingPhase γ) (windingRate u) u := by
  show HasDerivAt (fun u : ℝ => ∫ t in γ..u, windingRate t) (windingRate u) u
  exact (continuous_windingRate.integral_hasStrictDerivAt γ u).hasDerivAt

/-- Continuity of `Γ_ℝ` on the right half plane. -/
theorem continuousOn_Gammaℝ_re_pos :
    ContinuousOn Complex.Gammaℝ {z : ℂ | 0 < z.re} := fun _ hz =>
  (hasDerivAt_Gammaℝ_of_re_pos hz).differentiableAt.continuousAt.continuousWithinAt

/-- Continuity of the canonical second derivative on the right half plane. -/
theorem continuousOn_archFactorDeriv2 :
    ContinuousOn archFactorDeriv2 {z : ℂ | 0 < z.re} := by
  have hmaps : Set.MapsTo (fun z : ℂ => z / 2) {z : ℂ | 0 < z.re} {z : ℂ | 0 < z.re} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [re_div_two]
    linarith
  have hψ : ContinuousOn (fun z : ℂ => Complex.digamma (z / 2)) {z : ℂ | 0 < z.re} :=
    digamma_continuousOn_re_pos.comp (continuous_id.div_const (2 : ℂ)).continuousOn hmaps
  have hψ' : ContinuousOn (fun z : ℂ => deriv Complex.digamma (z / 2)) {z : ℂ | 0 < z.re} :=
    continuousOn_deriv_digamma_re_pos.comp (continuous_id.div_const (2 : ℂ)).continuousOn hmaps
  have hΨc : ContinuousOn
      (fun z : ℂ => Complex.digamma (z / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
      {z : ℂ | 0 < z.re} := (hψ.div_const 2).sub continuousOn_const
  unfold archFactorDeriv2
  exact continuousOn_Gammaℝ_re_pos.mul
    (((continuousOn_const.add
      (((by fun_prop : Continuous fun z : ℂ => 2 * z - 1).continuousOn).mul hΨc)).add
      (((by fun_prop : Continuous fun z : ℂ => z * (z - 1) / 2).continuousOn).mul
        (hΨc.pow 2))).add
      ((((by fun_prop : Continuous fun z : ℂ => z * (z - 1) / 2).continuousOn).mul
        hψ').div_const 4))

theorem continuous_windingRateDeriv : Continuous windingRateDeriv := by
  rw [continuous_iff_continuousAt]
  intro u
  have hUopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : linePt u ∈ {z : ℂ | 0 < z.re} := by
    simp only [Set.mem_setOf_eq, linePt_re]
    norm_num
  have hlineCA : ContinuousAt (fun u : ℝ => linePt u) u := by
    have hlineC : Continuous fun u : ℝ => linePt u := by
      unfold linePt
      exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact hlineC.continuousAt
  have h2 : ContinuousAt (fun u : ℝ => archFactorDeriv2 (linePt u)) u :=
    ((continuousOn_archFactorDeriv2 (linePt u) hmem).continuousAt
      (hUopen.mem_nhds hmem)).comp hlineCA
  have h1 : ContinuousAt (fun u : ℝ => archFactorDeriv (linePt u)) u :=
    (hasDerivAt_archFactorDeriv_line u).continuousAt
  have h0 : ContinuousAt (fun u : ℝ => archFactor (linePt u)) u :=
    (hasDerivAt_archFactor_line u).continuousAt
  have hinner : ContinuousAt (fun u : ℝ => Complex.I *
      (archFactorDeriv2 (linePt u) * archFactor (linePt u)
        - archFactorDeriv (linePt u) ^ (2 : ℕ)) / archFactor (linePt u) ^ (2 : ℕ)) u :=
    (continuousAt_const.mul ((h2.mul h0).sub (h1.pow 2))).div (h0.pow 2)
      (pow_ne_zero 2 (archFactor_linePt_ne_zero u))
  exact Complex.continuous_re.continuousAt.comp hinner

/-- **Cancellation of the envelope's first moment from a winding-rate floor.**  If the phase
velocity of the archimedean envelope stays above `m > 0` on the segment, its first moment obeys
the van der Corput bound with amplitude data given by the envelope sup `M₀`, the modulus
variation `Mim ≥ ‖archFactor‖·|Im w|`, and the winding curvature `Mp ≥ |windingRateDeriv|`. -/
theorem norm_integral_archFactor_line_le_of_winding_floor
    {α β m M₀ Mim Mp : ℝ} (hαβ : α ≤ β) (hm : 0 < m)
    (hfloor : ∀ u ∈ Set.uIcc α β, m ≤ |windingRate u|)
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀)
    (hMim : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ * |(archWinding u).im| ≤ Mim)
    (hMp : ∀ u ∈ Set.Icc α β, |windingRateDeriv u| ≤ Mp) :
    ‖∫ u in α..β, archFactor (linePt u)‖ ≤
      2 * (M₀ / m) + (β - α) * (Mim / m + M₀ * Mp / m ^ (2 : ℕ)) := by
  have hg : ∀ u ∈ Set.uIcc α β, HasDerivAt
      (fun u : ℝ => archFactor (linePt u) *
        Complex.exp (-(Complex.I * (windingPhase α u : ℂ))))
      (Complex.exp (-(Complex.I * (windingPhase α u : ℂ))) *
        (Complex.I * (archFactorDeriv (linePt u) -
          archFactor (linePt u) * ((windingRate u : ℝ) : ℂ)))) u := by
    intro u _
    have hexp : HasDerivAt
        (fun u : ℝ => Complex.exp (-(Complex.I * (windingPhase α u : ℂ))))
        (Complex.exp (-(Complex.I * (windingPhase α u : ℂ))) *
          (-(Complex.I * ((windingRate u : ℝ) : ℂ)))) u :=
      ((((hasDerivAt_windingPhase α u).ofReal_comp).const_mul Complex.I).neg).cexp
    have hprod := (hasDerivAt_archFactor_line u).mul hexp
    convert! hprod using 1
    ring
  have hg'norm : ∀ u ∈ Set.Icc α β,
      ‖Complex.exp (-(Complex.I * (windingPhase α u : ℂ))) *
        (Complex.I * (archFactorDeriv (linePt u) -
          archFactor (linePt u) * ((windingRate u : ℝ) : ℂ)))‖ ≤ Mim := by
    intro u hu
    have hexp1 : ‖Complex.exp (-(Complex.I * (windingPhase α u : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
    have hkey : archFactorDeriv (linePt u) -
        archFactor (linePt u) * ((windingRate u : ℝ) : ℂ) =
        archFactor (linePt u) * (((archWinding u).im : ℝ) * Complex.I) := by
      rw [archFactorDeriv_eq_mul_archWinding u]
      unfold windingRate
      linear_combination (-(archFactor (linePt u))) * Complex.re_add_im (archWinding u)
    rw [norm_mul, hexp1, one_mul, norm_mul, Complex.norm_I, one_mul, hkey, norm_mul,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hMim u hu
  have hg'c : ContinuousOn
      (fun u : ℝ => Complex.exp (-(Complex.I * (windingPhase α u : ℂ))) *
        (Complex.I * (archFactorDeriv (linePt u) -
          archFactor (linePt u) * ((windingRate u : ℝ) : ℂ))))
      (Set.uIcc α β) := by
    have hφcont : Continuous (windingPhase α) := by
      rw [continuous_iff_continuousAt]
      intro u
      exact (hasDerivAt_windingPhase α u).continuousAt
    have h1 : Continuous fun u : ℝ => archFactorDeriv (linePt u) := by
      rw [continuous_iff_continuousAt]
      intro u
      exact (hasDerivAt_archFactorDeriv_line u).continuousAt
    have h0 : Continuous fun u : ℝ => archFactor (linePt u) := by
      rw [continuous_iff_continuousAt]
      intro u
      exact (hasDerivAt_archFactor_line u).continuousAt
    exact ((Complex.continuous_exp.comp
      ((continuous_const.mul (Complex.continuous_ofReal.comp hφcont)).neg)).mul
      (continuous_const.mul (h1.sub (h0.mul
        (Complex.continuous_ofReal.comp continuous_windingRate))))).continuousOn
  have hcongr : (∫ u in α..β, archFactor (linePt u)) =
      ∫ u in α..β, (archFactor (linePt u) *
        Complex.exp (-(Complex.I * (windingPhase α u : ℂ)))) *
        Complex.exp (Complex.I * ((windingPhase α u : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [hcongr]
  have hM₀' : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u) *
      Complex.exp (-(Complex.I * (windingPhase α u : ℂ)))‖ ≤ M₀ := by
    intro u hu
    have hexp1 : ‖Complex.exp (-(Complex.I * (windingPhase α u : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re]
    rw [norm_mul, hexp1, mul_one]
    exact hM₀ u hu
  exact norm_integral_mul_exp_phase_le hαβ hm hg
    (fun u _ => hasDerivAt_windingPhase α u)
    (fun u _ => hasDerivAt_windingRate u)
    hg'c continuous_windingRateDeriv.continuousOn hfloor hM₀' hg'norm hMp

end RHTower
