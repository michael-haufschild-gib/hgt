import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeArchResidue

/-!
# Exact direct-prime contour reduction for physical theta--Abel energy

This module upgrades the pointwise prime/archimedean source decomposition to
an exact rectangle-integral identity.  Boundary admissibility supplies the
missing integrability of both meromorphic channels.  After normalization, a
rectangle crossing the centered archimedean pole equals the literal continued
prime-flux contour plus one explicit positive square.
-/

open Complex Filter Topology Set intervalIntegral MeasureTheory

namespace RHTower

noncomputable section

private theorem continuedSource_eq_logDeriv_XiC_of_admissible
    {z : ℂ} (hz : XiExplicitAdmissible z) :
    continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    hz.re_pos hz.ne_one hz.zeta_ne]
  exact (logDeriv_XiC_eq_relativeResolventTrace
    (XiC_ne_zero_of_admissible hz)).symm

private theorem analyticAt_logDeriv_XiC_of_admissible
    {z : ℂ} (hz : XiExplicitAdmissible z) :
    AnalyticAt ℂ (logDeriv XiC) z := by
  have hXi : AnalyticAt ℂ XiC z := XiC_analytic z (Set.mem_univ z)
  exact hXi.deriv.div hXi (XiC_ne_zero_of_admissible hz)

private theorem intervalIntegrable_weighted_continuedSource_comp
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {e : ℝ → ℂ} {u v : ℝ} (he : Continuous e)
    (hadm : ∀ x ∈ uIcc u v, XiExplicitAdmissible (e x)) :
    IntervalIntegrable
      (fun x => g (e x) * continuedPrimeArchSourceRelativeTrace (e x))
      MeasureTheory.volume u v := by
  have hcont : ContinuousOn (fun x : ℝ =>
      g (e x) * logDeriv XiC (e x)) (uIcc u v) := by
    intro x hx
    have han : AnalyticAt ℂ (fun z => g z * logDeriv XiC z) (e x) :=
      (hg (e x) (Set.mem_univ _)).mul
        (analyticAt_logDeriv_XiC_of_admissible (hadm x hx))
    have hc := ContinuousAt.comp (f := e) han.continuousAt he.continuousAt
    simpa [Function.comp_def] using hc.continuousWithinAt
  refine hcont.intervalIntegrable.congr ?_
  intro x hx
  have hx' : x ∈ uIcc u v := uIoc_subset_uIcc hx
  change g (e x) * logDeriv XiC (e x) =
    g (e x) * continuedPrimeArchSourceRelativeTrace (e x)
  rw [continuedSource_eq_logDeriv_XiC_of_admissible (hadm x hx')]

private theorem analyticAt_centeredArchLogDeriv_of_admissible
    {z : ℂ} (hz : XiExplicitAdmissible z) :
    AnalyticAt ℂ
      (logDeriv (fun w => archFactor (xiMassCenteredArchPoint w))) z := by
  have hs : AnalyticAt ℂ xiMassCenteredArchPoint z := by
    unfold xiMassCenteredArchPoint
    fun_prop
  have haf : AnalyticAt ℂ
      (fun w => archFactor (xiMassCenteredArchPoint w)) z :=
    AnalyticAt.comp (g := archFactor) (f := xiMassCenteredArchPoint) (x := z)
      (archFactor_analyticOnNhd_re_pos _ hz.re_pos) hs
  have hs0 : xiMassCenteredArchPoint z ≠ 0 := by
    intro h
    have h' : 1 / 2 + z * I = 0 := by
      simpa [xiMassCenteredArchPoint] using h
    have hzpos := hz.re_pos
    rw [h', Complex.zero_re] at hzpos
    exact (lt_irrefl 0 hzpos)
  have hG : Gammaℝ (xiMassCenteredArchPoint z) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hz.re_pos
  have haf0 : archFactor (xiMassCenteredArchPoint z) ≠ 0 :=
    archFactor_ne_zero hs0 hz.ne_one hG
  exact haf.deriv.div haf haf0

private theorem intervalIntegrable_weighted_archSource_comp
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {e : ℝ → ℂ} {u v : ℝ} (he : Continuous e)
    (hadm : ∀ x ∈ uIcc u v, XiExplicitAdmissible (e x)) :
    IntervalIntegrable (fun x => g (e x) *
      (I * logDeriv archFactor (1 / 2 + e x * I)))
      MeasureTheory.volume u v := by
  have hcont : ContinuousOn (fun x : ℝ => g (e x) *
      logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) (e x))
      (uIcc u v) := by
    intro x hx
    have han : AnalyticAt ℂ (fun z => g z *
        logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z) (e x) :=
      (hg (e x) (Set.mem_univ _)).mul
        (analyticAt_centeredArchLogDeriv_of_admissible (hadm x hx))
    have hc := ContinuousAt.comp (f := e) han.continuousAt he.continuousAt
    simpa [Function.comp_def] using hc.continuousWithinAt
  refine hcont.intervalIntegrable.congr ?_
  intro x hx
  have hx' : x ∈ uIcc u v := uIoc_subset_uIcc hx
  change g (e x) *
      logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) (e x) =
    g (e x) * (I * logDeriv archFactor (1 / 2 + e x * I))
  rw [logDeriv_centeredArchFactor_eq_I_mul]
  · rfl
  · simpa [xiMassCenteredArchPoint] using (hadm x hx').re_pos

private theorem intervalIntegrable_weighted_primeSource_comp
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {e : ℝ → ℂ} {u v : ℝ} (he : Continuous e)
    (hadm : ∀ x ∈ uIcc u v, XiExplicitAdmissible (e x)) :
    IntervalIntegrable (fun x => g (e x) *
      (-I * infinitePrimeFlux (1 / 2 + e x * I)))
      MeasureTheory.volume u v := by
  have hs := intervalIntegrable_weighted_continuedSource_comp hg he hadm
  have ha := intervalIntegrable_weighted_archSource_comp hg he hadm
  refine (hs.sub ha).congr ?_
  intro x _hx
  change g (e x) * continuedPrimeArchSourceRelativeTrace (e x) -
      g (e x) * (I * logDeriv archFactor (1 / 2 + e x * I)) =
    g (e x) * (-I * infinitePrimeFlux (1 / 2 + e x * I))
  rw [continuedPrimeArchSourceRelativeTrace]
  ring

/-- Exact contour-level split into direct continued prime flux and completed
archimedean channels. -/
theorem rectIntegral_physicalThetaAbelEnergy_source_eq_prime_add_arch
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    rectIntegral (fun z =>
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ) *
          continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      rectIntegral (fun z =>
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ) *
          (-I * infinitePrimeFlux (1 / 2 + z * I))) z₁ z₂ +
      rectIntegral (fun z =>
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ) *
          (I * logDeriv archFactor (1 / 2 + z * I))) z₁ z₂ := by
  let g : ℂ → ℂ := fun z =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ)
  let p : ℂ → ℂ := fun z =>
    g z * (-I * infinitePrimeFlux (1 / 2 + z * I))
  let r : ℂ → ℂ := fun z =>
    g z * (I * logDeriv archFactor (1 / 2 + z * I))
  have hg := xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd L A c a
  have hbP := intervalIntegrable_weighted_primeSource_comp hg (by fun_prop) hbot
  have hbR := intervalIntegrable_weighted_archSource_comp hg (by fun_prop) hbot
  have htP := intervalIntegrable_weighted_primeSource_comp hg (by fun_prop) htop
  have htR := intervalIntegrable_weighted_archSource_comp hg (by fun_prop) htop
  have hrP := intervalIntegrable_weighted_primeSource_comp hg (by fun_prop) hright
  have hrR := intervalIntegrable_weighted_archSource_comp hg (by fun_prop) hright
  have hlP := intervalIntegrable_weighted_primeSource_comp hg (by fun_prop) hleft
  have hlR := intervalIntegrable_weighted_archSource_comp hg (by fun_prop) hleft
  have hadd := rectIntegral_add (g₁ := p) (g₂ := r) (z₁ := z₁) (z₂ := z₂)
    hbP hbR htP htR hrP hrR hlP hlR
  have hcongr : rectIntegral (fun z =>
      g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      rectIntegral (fun z => p z + r z) z₁ z₂ := by
    apply rectIntegral_congr (S := Set.univ)
    · intro z _
      exact physicalThetaAbelEnergy_sourceIntegrand_eq_prime_add_arch
        L A c a z
    all_goals simp
  simpa only [g, p, r] using hcongr.trans hadd

/-- Normalized direct continued-prime channel of the physical-energy source
contour. -/
def xiPhysicalThetaAbelEnergyNormalizedPrimeSourceContour
    (L A c a : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * rectIntegral (fun z =>
    xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ) *
      (-I * infinitePrimeFlux (1 / 2 + z * I))) z₁ z₂

/-- Exact normalized source split on every admissible rectangle. -/
theorem xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_prime_add_arch
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    xiPhysicalThetaAbelEnergyNormalizedSourceContour L A c a z₁ z₂ =
      xiPhysicalThetaAbelEnergyNormalizedPrimeSourceContour L A c a z₁ z₂ +
      xiPhysicalThetaAbelEnergyNormalizedArchSourceContour L A c a z₁ z₂ := by
  rw [xiPhysicalThetaAbelEnergyNormalizedSourceContour,
    xiPhysicalThetaAbelEnergyNormalizedPrimeSourceContour,
    xiPhysicalThetaAbelEnergyNormalizedArchSourceContour,
    rectIntegral_physicalThetaAbelEnergy_source_eq_prime_add_arch
      hbot htop hright hleft]
  ring

/-- Direct prime contour with its fully evaluated completed-archimedean
residue restored. -/
def xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour
    (L A c a : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  xiPhysicalThetaAbelEnergyNormalizedPrimeSourceContour L A c a z₁ z₂ +
    ((Real.exp (a / 2) * 2 * (1 - Real.exp (-(L / 2))) * c * A : ℝ) : ℂ) ^ (2 : ℕ)

/-- On an admissible rectangle crossing the unique centered archimedean pole,
the full source contour is exactly the direct prime contour plus one explicit
positive square. -/
theorem xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_correctedPrime
    {L A c a : ℝ} {z₁ z₂ : ℂ}
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htopAdm : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hrightAdm : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleftAdm : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (him : z₁.im < z₂.im)
    (hleft : z₁.re < 0) (hright : 0 < z₂.re)
    (hbelow : z₁.im < -(1 / 2)) (habove : -(1 / 2) < z₂.im)
    (htop : z₂.im < 1 / 2) :
    xiPhysicalThetaAbelEnergyNormalizedSourceContour L A c a z₁ z₂ =
      xiPhysicalThetaAbelEnergyCorrectedPrimeSourceContour
        L A c a z₁ z₂ := by
  rw [xiPhysicalThetaAbelEnergyNormalizedSourceContour_eq_prime_add_arch
      hbot htopAdm hrightAdm hleftAdm,
    xiPhysicalThetaAbelEnergyNormalizedArchSourceContour_eq_explicit
      him hleft hright hbelow habove htop]
  rfl

end

end RHTower
