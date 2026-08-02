import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw

/-!
# Cofinal collapse and inverse conditioning of the complete Riemann source

At every finite shell base, the complete largest-valuation resolution is an
injective mass-one source embedding and contains a channel preserving the
completed zeta divisor.  Cofinally, however, all source vectors converge in
their canonical `ℓ¹` norm to the same point section.

This module proves the resulting conditioning law.  Distinct spectral points
remain distinct at every finite base, but their inverse source separation
diverges.  Consequently every uniformly Lipschitz family of observers loses
all fixed spectral separation.  No linearity, positivity, or label-blindness
is assumed for the observers.
-/

open Complex Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Exact longitudinal/tail split of the distance from the universal point
section. -/
theorem norm_completeResolutionSourceVector_sub_pointSection
    (K : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖completeResolutionSourceVector K s hs -
        sourceFusionPointSection 1‖ =
      ‖(riemannZeta ((K : ℂ) * s))⁻¹ - 1‖ +
        ∑' j : ℕ, ‖shellMultiplier (K + j) s‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  norm_num
  rw [tsum_eq_zero_add' (by
    simpa [completeResolutionMultiplier, sourceFusionPointSection,
      lp.single_apply, Nat.add_comm] using
      ((summable_nat_add_iff K).2
        (summable_shellMultiplier hs).norm))]
  simp [completeResolutionMultiplier, sourceFusionPointSection,
    lp.single_apply]

/-- Every fixed spectral point collapses to the same coordinate section
when the complete source resolution is moved cofinally through shell depth. -/
theorem tendsto_completeResolutionSourceVector_pointSection
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto
      (fun K : ℕ =>
        completeResolutionSourceVector K s hs)
      atTop (nhds (sourceFusionPointSection 1)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hheadRaw :=
    tendsto_inv_riemannZeta_nat_dilation_one (K := 0) hs
  have hhead :
      Tendsto
        (fun K : ℕ =>
          ‖(riemannZeta ((K : ℂ) * s))⁻¹ - 1‖)
        atTop (nhds 0) := by
    have h := (hheadRaw.sub_const 1).norm
    simpa using h
  have htail :
      Tendsto
        (fun K : ℕ =>
          ∑' j : ℕ, ‖shellMultiplier (K + j) s‖)
        atTop (nhds 0) := by
    simpa [Nat.add_comm] using
      (tendsto_sum_nat_add
        (fun m : ℕ => ‖shellMultiplier m s‖))
  have hsum := hhead.add htail
  simpa only [norm_completeResolutionSourceVector_sub_pointSection,
    zero_add] using hsum

/-- Any two fixed spectral points become indistinguishable in the canonical
`ℓ¹` norm when the shell base is moved cofinally. -/
theorem tendsto_completeResolutionSourceVector_sub_zero
    (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re) :
    Tendsto
      (fun K : ℕ =>
        completeResolutionSourceVector K s hs -
          completeResolutionSourceVector K t ht)
      atTop (nhds 0) := by
  have h :=
    (tendsto_completeResolutionSourceVector_pointSection s hs).sub
      (tendsto_completeResolutionSourceVector_pointSection t ht)
  simpa using h

theorem tendsto_norm_completeResolutionSourceVector_sub_zero
    (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re) :
    Tendsto
      (fun K : ℕ =>
        ‖completeResolutionSourceVector K s hs -
          completeResolutionSourceVector K t ht‖)
      atTop (nhds 0) := by
  simpa using
    (tendsto_completeResolutionSourceVector_sub_zero s t hs ht).norm

/-- Distinct spectral points remain distinct at every finite shell base,
although their source separation converges to zero. -/
theorem norm_completeResolutionSourceVector_sub_pos
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) (hst : s ≠ t)
    (K : ℕ) :
    0 <
      ‖completeResolutionSourceVector K s hs -
        completeResolutionSourceVector K t ht‖ := by
  rw [norm_pos_iff]
  intro hzero
  have hvector :
      completeResolutionSourceEmbedding K ⟨s, hs⟩ =
        completeResolutionSourceEmbedding K ⟨t, ht⟩ := by
    exact sub_eq_zero.mp hzero
  have hpoint :=
    completeResolutionSourceEmbedding_injective K hvector
  exact hst (congrArg Subtype.val hpoint)

/-- **Cofinal inverse-conditioning law.**  Recovering any two distinct
spectral points from the complete source requires a sensitivity which
diverges along the cofinal shell base. -/
theorem tendsto_inv_norm_completeResolutionSourceVector_sub_atTop
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) (hst : s ≠ t) :
    Tendsto
      (fun K : ℕ =>
        ‖completeResolutionSourceVector K s hs -
          completeResolutionSourceVector K t ht‖⁻¹)
      atTop atTop := by
  apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_norm_completeResolutionSourceVector_sub_zero s t hs ht,
    Filter.Eventually.of_forall
      (norm_completeResolutionSourceVector_sub_pos hs ht hst)⟩

/-- Every family of observers with one uniform Lipschitz bound loses all
fixed spectral separation along the cofinal source resolution.  Observers
may be nonlinear and label-sensitive. -/
theorem tendsto_uniformLipschitz_completeResolutionObserver_separation_zero
    {F : Type*} [PseudoMetricSpace F]
    (s t : ℂ) (hs : 0 < s.re) (ht : 0 < t.re)
    (C : ℝ) (T : ℕ → CompleteResolutionSourceSpace → F)
    (hLip : ∀ K x y,
      dist (T K x) (T K y) ≤ C * ‖x - y‖) :
    Tendsto
      (fun K : ℕ =>
        dist
          (T K (completeResolutionSourceVector K s hs))
          (T K (completeResolutionSourceVector K t ht)))
      atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun K => dist_nonneg
  · exact fun K => hLip K _ _
  · have hconst :
        Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    simpa using hconst.mul
      (tendsto_norm_completeResolutionSourceVector_sub_zero s t hs ht)

/-- No uniformly Lipschitz observer family can retain a fixed positive
separation between two spectral points at all cofinal source depths. -/
theorem no_uniformLipschitz_completeResolutionObserver_fixedSeparation
    {F : Type*} [PseudoMetricSpace F]
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re)
    (C κ : ℝ) (hκ : 0 < κ)
    (T : ℕ → CompleteResolutionSourceSpace → F)
    (hLip : ∀ K x y,
      dist (T K x) (T K y) ≤ C * ‖x - y‖)
    (hseparate : ∀ K,
      κ ≤
        dist
          (T K (completeResolutionSourceVector K s hs))
          (T K (completeResolutionSourceVector K t ht))) :
    False := by
  have hlimit :=
    tendsto_uniformLipschitz_completeResolutionObserver_separation_zero
      s t hs ht C T hLip
  rw [Metric.tendsto_atTop] at hlimit
  obtain ⟨N, hN⟩ := hlimit κ hκ
  have hsmall := hN N le_rfl
  have hlarge := hseparate N
  have houtnonneg :
      0 ≤
        dist
          (T N (completeResolutionSourceVector N s hs))
          (T N (completeResolutionSourceVector N t ht)) :=
    dist_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg houtnonneg] at hsmall
  linarith

/-- Functional-equation reflection displacement is nonzero at every finite
base off the critical line, but collapses to zero in the cofinal `ℓ¹`
topology. -/
theorem tendsto_completeResolutionReflectionSourceDisplacement_zero
    (s : CompleteResolutionOpenCriticalStrip) :
    Tendsto
      (fun K : ℕ =>
        completeResolutionReflectionSourceDisplacement K s)
      atTop (nhds 0) := by
  let reflected : ℂ := 1 - star s.1
  have hreflected : 0 < reflected.re := by
    dsimp only [reflected]
    have hstarRe : (star s.1).re = s.1.re := by simp
    simp only [sub_re, one_re]
    rw [hstarRe]
    linarith [s.2.2]
  simpa [completeResolutionReflectionSourceDisplacement,
    completeResolutionSourceEmbedding, reflected] using
    tendsto_completeResolutionSourceVector_sub_zero
      s.1 reflected s.2.1 hreflected

/-- Off the critical line, the inverse norm of the actual reflected source
displacement diverges.  This is the exact conditioning cost which any
regular common-test factorization must pay. -/
theorem tendsto_inv_norm_completeResolutionReflectionSourceDisplacement_atTop
    (s : CompleteResolutionOpenCriticalStrip)
    (hoff : s.1.re ≠ 1 / 2) :
    Tendsto
      (fun K : ℕ =>
        ‖completeResolutionReflectionSourceDisplacement K s‖⁻¹)
      atTop atTop := by
  apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
  rw [tendsto_nhdsWithin_iff]
  refine ⟨by
    simpa using
      (tendsto_completeResolutionReflectionSourceDisplacement_zero s).norm,
    Filter.Eventually.of_forall fun K => ?_⟩
  exact norm_pos_iff.mpr
    ((not_congr
      (completeResolutionReflectionSourceDisplacement_eq_zero_iff K s)).mpr
        hoff)

/-- **Cofinal conservation--singularity law.**  The complete source
simultaneously has unit mass, preserves a full Xi conormal channel at every
finite depth, collapses to a universal atom cofinally, and forces divergent
inverse conditioning between distinct spectral points. -/
theorem completeResolution_cofinalConservationSingularity_law
    {rho sigma : ℂ}
    (hrho : 1 / 2 ≤ rho.re)
    (hsigma : 0 < sigma.re)
    (hne : rho ≠ sigma) :
    (∀ K : ℕ,
      sourceFusionCodiagonal
          (completeResolutionSourceVector K rho (by linarith)) = 1) ∧
      (∀ K : ℕ, 12 ≤ K →
        ∃ j : ℕ,
          completeResolutionMultiplier K j rho ≠ 0 ∧
            analyticOrderAt
                (fun z => xi z * completeResolutionMultiplier K j z) rho =
              analyticOrderAt xi rho) ∧
      Tendsto
        (fun K : ℕ =>
          completeResolutionSourceVector K rho (by linarith))
        atTop (nhds (sourceFusionPointSection 1)) ∧
      Tendsto
        (fun K : ℕ =>
          ‖completeResolutionSourceVector K rho (by linarith) -
            completeResolutionSourceVector K sigma hsigma‖⁻¹)
        atTop atTop := by
  have hrhoPos : 0 < rho.re := by linarith
  refine ⟨fun K => ?_, fun K hK => ?_, ?_, ?_⟩
  · simpa [completeResolutionSourceEmbedding] using
      sourceFusionCodiagonal_completeResolutionSourceEmbedding
        K (⟨rho, hrhoPos⟩ : CompleteResolutionRightHalfPlane)
  · exact (completeResolution_summable_conormalLanding hK hrho).2.2
  · exact tendsto_completeResolutionSourceVector_pointSection rho hrhoPos
  · exact
      tendsto_inv_norm_completeResolutionSourceVector_sub_atTop
        hrhoPos hsigma hne

/-- Canonical two-clock projective chart on the vanishing shell tail. -/
def completeResolutionCofinalBlowupChart
    (K : ℕ) (s : ℂ) : ℂ × ℂ :=
  (normalizedShellAdjacentTransfer K s,
    normalizedShellSecondAtomAdjacentTransfer K s)

/-- The first blow-up coordinate is a literal adjacent ratio of the
complete source vector's first two shell channels. -/
theorem completeResolutionCofinalBlowupChart_fst_eq_sourceRatio
    (K : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (completeResolutionCofinalBlowupChart K s).1 =
      (Real.sqrt 2 : ℂ) *
        (completeResolutionSourceVector K s hs 2 /
          completeResolutionSourceVector K s hs 1) := by
  simp [completeResolutionCofinalBlowupChart,
    normalizedShellAdjacentTransfer, shellAdjacentTransfer,
    completeResolutionMultiplier]

/-- **Two-clock blow-up resolution.**  Although the source vectors
themselves collapse to one atom, their canonical projective normal chart
converges to the injective prime-two/prime-three spectral character. -/
theorem tendsto_completeResolutionCofinalBlowupChart
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto
      (fun K : ℕ => completeResolutionCofinalBlowupChart K s)
      atTop (nhds (twoPrimeShellTransferSpectrum s)) := by
  have h :=
    (tendsto_normalizedShellAdjacentTransfer hs).prodMk
      (tendsto_normalizedShellSecondAtomAdjacentTransfer hs)
  simpa [completeResolutionCofinalBlowupChart,
    twoPrimeShellTransferSpectrum,
    shellTransferCharacter_eq_leastAtomTransferCharacter,
    shellSecondAtomTransferCharacter,
    GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter] using h

/-- The limiting blow-up chart retains the entire complex spectral
coordinate. -/
theorem completeResolutionCofinalBlowupLimit_injective :
    Function.Injective twoPrimeShellTransferSpectrum :=
  twoPrimeShellTransferSpectrum_injective

/-- **Collapse/blow-up duality.**  Ordinary `ℓ¹` observation collapses the
complete source to one point, while the canonical two-clock projective
normal chart converges and remains spectrally faithful. -/
theorem completeResolution_collapseBlowup_duality
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto
        (fun K : ℕ => completeResolutionSourceVector K s hs)
        atTop (nhds (sourceFusionPointSection 1)) ∧
      Tendsto
        (fun K : ℕ => completeResolutionCofinalBlowupChart K s)
        atTop (nhds (twoPrimeShellTransferSpectrum s)) ∧
      Function.Injective twoPrimeShellTransferSpectrum :=
  ⟨tendsto_completeResolutionSourceVector_pointSection s hs,
    tendsto_completeResolutionCofinalBlowupChart s hs,
    completeResolutionCofinalBlowupLimit_injective⟩

/-- **Inevitable singularity of faithful cofinal recovery.**  For every
distinct pair of spectral points, source distance tends to zero while the
two-clock blow-up distance tends to a strictly positive limit.  Hence the
blow-up chart cannot obey any shell-independent Lipschitz estimate on the
source image. -/
theorem no_uniformLipschitz_completeResolutionCofinalBlowupChart_pair
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) (hst : s ≠ t)
    (C : ℝ)
    (hLip : ∀ K : ℕ,
      dist
          (completeResolutionCofinalBlowupChart K s)
          (completeResolutionCofinalBlowupChart K t) ≤
        C * ‖completeResolutionSourceVector K s hs -
          completeResolutionSourceVector K t ht‖) :
    False := by
  let δ : ℝ :=
    dist (twoPrimeShellTransferSpectrum s)
      (twoPrimeShellTransferSpectrum t)
  have hspectrumNe :
      twoPrimeShellTransferSpectrum s ≠
        twoPrimeShellTransferSpectrum t := by
    intro h
    exact hst (twoPrimeShellTransferSpectrum_injective h)
  have hδ : 0 < δ := by
    exact dist_pos.mpr hspectrumNe
  have hout :
      Tendsto
        (fun K : ℕ =>
          dist
            (completeResolutionCofinalBlowupChart K s)
            (completeResolutionCofinalBlowupChart K t))
        atTop (nhds δ) := by
    exact
      (tendsto_completeResolutionCofinalBlowupChart s hs).dist
        (tendsto_completeResolutionCofinalBlowupChart t ht)
  have hin :
      Tendsto
        (fun K : ℕ =>
          C * ‖completeResolutionSourceVector K s hs -
            completeResolutionSourceVector K t ht‖)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_norm_completeResolutionSourceVector_sub_zero
          s t hs ht))
  rw [Metric.tendsto_atTop] at hout hin
  obtain ⟨Nout, hNout⟩ := hout (δ / 2) (half_pos hδ)
  obtain ⟨Nin, hNin⟩ := hin (δ / 2) (half_pos hδ)
  let N := max Nout Nin
  have houtClose := hNout N (le_max_left _ _)
  have hinClose := hNin N (le_max_right _ _)
  rw [Real.dist_eq] at houtClose hinClose
  have houtLower :
      δ / 2 <
        dist
          (completeResolutionCofinalBlowupChart N s)
          (completeResolutionCofinalBlowupChart N t) := by
    linarith [((abs_lt.mp houtClose).1)]
  have hinUpper :
      C * ‖completeResolutionSourceVector N s hs -
        completeResolutionSourceVector N t ht‖ < δ / 2 := by
    linarith [((abs_lt.mp hinClose).2)]
  linarith [hLip N]

end

end RHTower
