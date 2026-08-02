import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw
import Mathlib.LinearAlgebra.Vandermonde

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
  rw [completeResolutionCofinalBlowupChart,
    normalizedShellAdjacentTransfer, two_cpow_half_eq_sqrt]
  simp only [completeResolutionSourceVector_apply,
    completeResolutionMultiplier, shellAdjacentTransfer, Nat.add_zero]

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
  rw [nhds_prod_eq]
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

/-- The actual image of one finite complete-resolution source embedding. -/
abbrev CompleteResolutionSourceImage (K : ℕ) :=
  {x : CompleteResolutionSourceSpace //
    x ∈ Set.range (completeResolutionSourceEmbedding K)}

/-- Canonical point of the source image determined by a spectral point. -/
def completeResolutionSourceImagePoint
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    CompleteResolutionSourceImage K :=
  ⟨completeResolutionSourceEmbedding K s, ⟨s, rfl⟩⟩

/-- The unique spectral preimage of a complete-resolution source-image
point. -/
noncomputable def completeResolutionSourceImagePreimage
    (K : ℕ) (x : CompleteResolutionSourceImage K) :
    CompleteResolutionRightHalfPlane :=
  Classical.choose x.2

theorem completeResolutionSourceImagePreimage_spec
    (K : ℕ) (x : CompleteResolutionSourceImage K) :
    completeResolutionSourceEmbedding K
        (completeResolutionSourceImagePreimage K x) = x.1 :=
  Classical.choose_spec x.2

/-- **Infinite source-pointed normal reader.** The reader is defined on
the source image itself, not on an externally supplied spectral label. -/
noncomputable def completeResolutionSourceNormalReader
    (K : ℕ) (x : CompleteResolutionSourceImage K) : ℂ × ℂ :=
  twoPrimeShellTransferSpectrum
    (completeResolutionSourceImagePreimage K x).1

@[simp] theorem completeResolutionSourceNormalReader_imagePoint
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    completeResolutionSourceNormalReader K
        (completeResolutionSourceImagePoint K s) =
      twoPrimeShellTransferSpectrum s.1 := by
  have hpre :
      completeResolutionSourceImagePreimage K
          (completeResolutionSourceImagePoint K s) = s := by
    apply completeResolutionSourceEmbedding_injective K
    exact completeResolutionSourceImagePreimage_spec K _
  simp [completeResolutionSourceNormalReader, hpre]

/-- The source-pointed normal reader is faithful at every finite shell
base. -/
theorem completeResolutionSourceNormalReader_injective (K : ℕ) :
    Function.Injective (completeResolutionSourceNormalReader K) := by
  intro x y hreader
  have hpreVal :
      (completeResolutionSourceImagePreimage K x).1 =
        (completeResolutionSourceImagePreimage K y).1 :=
    twoPrimeShellTransferSpectrum_injective hreader
  have hpre :
      completeResolutionSourceImagePreimage K x =
        completeResolutionSourceImagePreimage K y :=
    Subtype.ext hpreVal
  apply Subtype.ext
  calc
    x.1 =
        completeResolutionSourceEmbedding K
          (completeResolutionSourceImagePreimage K x) :=
      (completeResolutionSourceImagePreimage_spec K x).symm
    _ =
        completeResolutionSourceEmbedding K
          (completeResolutionSourceImagePreimage K y) := by rw [hpre]
    _ = y.1 := completeResolutionSourceImagePreimage_spec K y

/-- The first clock of the source reader is computed internally as the
cofinal adjacent-coordinate ratio of one fixed source vector. -/
theorem tendsto_completeResolutionSourceImagePoint_firstNormalRatio
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt 2 : ℂ) *
          (completeResolutionSourceImagePoint K s).1 (n + 2) /
            (completeResolutionSourceImagePoint K s).1 (n + 1))
      atTop
      (nhds
        (completeResolutionSourceNormalReader K
          (completeResolutionSourceImagePoint K s)).1) := by
  rw [completeResolutionSourceNormalReader_imagePoint]
  change Tendsto
    (fun n : ℕ =>
      (Real.sqrt 2 : ℂ) *
        shellMultiplier (K + (n + 1)) s.1 /
          shellMultiplier (K + n) s.1)
    atTop (nhds (twoPrimeShellTransferSpectrum s.1).1)
  rw [show (twoPrimeShellTransferSpectrum s.1).1 =
      shellTransferCharacter s.1 by
    simp [twoPrimeShellTransferSpectrum,
      shellTransferCharacter_eq_leastAtomTransferCharacter]]
  have hshift :
      Tendsto (fun n : ℕ => K + n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat K
  have h :=
    (tendsto_normalizedShellAdjacentTransfer s.2).comp hshift
  change Tendsto
    (fun n : ℕ => normalizedShellAdjacentTransfer (K + n) s.1)
    atTop (nhds (shellTransferCharacter s.1)) at h
  change Tendsto
    (fun n : ℕ =>
      (2 : ℂ) ^ (1 / 2 : ℂ) *
        (shellMultiplier ((K + n) + 1) s.1 /
          shellMultiplier (K + n) s.1))
    atTop (nhds (shellTransferCharacter s.1)) at h
  rw [two_cpow_half_eq_sqrt] at h
  simpa only [Nat.add_assoc, mul_div_assoc] using h

/-- Exact prime-two-subtracted normal coordinate of a source-image point.
The preimage is a function of the source point by injectivity. -/
noncomputable def completeResolutionSourceImageSecondResidual
    (K n : ℕ) (x : CompleteResolutionSourceImage K) : ℂ :=
  shellSecondAtomResidual (K + n)
    (completeResolutionSourceImagePreimage K x).1

/-- The second clock is likewise an internal cofinal ratio after exact
removal of the first normal atom. -/
theorem tendsto_completeResolutionSourceImagePoint_secondNormalRatio
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt 3 : ℂ) *
          completeResolutionSourceImageSecondResidual K (n + 1)
              (completeResolutionSourceImagePoint K s) /
            completeResolutionSourceImageSecondResidual K n
              (completeResolutionSourceImagePoint K s))
      atTop
      (nhds
        (completeResolutionSourceNormalReader K
          (completeResolutionSourceImagePoint K s)).2) := by
  rw [completeResolutionSourceNormalReader_imagePoint]
  have hpre :
      completeResolutionSourceImagePreimage K
          (completeResolutionSourceImagePoint K s) = s := by
    apply completeResolutionSourceEmbedding_injective K
    exact completeResolutionSourceImagePreimage_spec K _
  simp only [completeResolutionSourceImageSecondResidual, hpre]
  change Tendsto
    (fun n : ℕ =>
      (Real.sqrt 3 : ℂ) *
        shellSecondAtomResidual (K + (n + 1)) s.1 /
          shellSecondAtomResidual (K + n) s.1)
    atTop (nhds (twoPrimeShellTransferSpectrum s.1).2)
  rw [show (twoPrimeShellTransferSpectrum s.1).2 =
      shellSecondAtomTransferCharacter s.1 by
    simp [twoPrimeShellTransferSpectrum,
      shellSecondAtomTransferCharacter,
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter]]
  have hshift :
      Tendsto (fun n : ℕ => K + n) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat K
  have h :=
    (tendsto_normalizedShellSecondAtomAdjacentTransfer s.2).comp hshift
  change Tendsto
    (fun n : ℕ =>
      normalizedShellSecondAtomAdjacentTransfer (K + n) s.1)
    atTop (nhds (shellSecondAtomTransferCharacter s.1)) at h
  simpa [
    normalizedShellSecondAtomAdjacentTransfer,
    shellSecondAtomAdjacentTransfer, Nat.add_assoc,
    mul_div_assoc] using h

/-- **Source-pointed singular-reader law.** The exact infinite reader
retains a fixed positive separation between every distinct spectral pair,
so no finite shell-independent Lipschitz constant can control it by the
cofinally collapsing source metric. -/
theorem no_uniformLipschitz_completeResolutionSourceNormalReader_pair
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) (hst : s ≠ t)
    (C : ℝ)
    (hLip : ∀ K : ℕ,
      dist
          (completeResolutionSourceNormalReader K
            (completeResolutionSourceImagePoint K ⟨s, hs⟩))
          (completeResolutionSourceNormalReader K
            (completeResolutionSourceImagePoint K ⟨t, ht⟩)) ≤
        C * ‖completeResolutionSourceVector K s hs -
          completeResolutionSourceVector K t ht‖) :
    False := by
  let δ : ℝ :=
    dist (twoPrimeShellTransferSpectrum s)
      (twoPrimeShellTransferSpectrum t)
  have hδ : 0 < δ := by
    apply dist_pos.mpr
    intro h
    exact hst (twoPrimeShellTransferSpectrum_injective h)
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
  rw [Metric.tendsto_atTop] at hin
  obtain ⟨N, hN⟩ := hin δ hδ
  have hsmall := hN N le_rfl
  rw [Real.dist_eq] at hsmall
  have hupper :
      C * ‖completeResolutionSourceVector N s hs -
        completeResolutionSourceVector N t ht‖ < δ := by
    linarith [((abs_lt.mp hsmall).2)]
  have hlower := hLip N
  simp only [completeResolutionSourceNormalReader_imagePoint] at hlower
  exact (not_lt_of_ge hlower) hupper

/-- Three explicit right-half-plane source points used to expose the
complete two-clock vertical boundary. -/
def completeResolutionVerticalBasePoint :
    CompleteResolutionRightHalfPlane :=
  ⟨(1 / 2 : ℂ), by norm_num⟩

def completeResolutionVerticalFirstPoint :
    CompleteResolutionRightHalfPlane :=
  ⟨(3 / 2 : ℂ), by norm_num⟩

def completeResolutionVerticalSecondPoint :
    CompleteResolutionRightHalfPlane :=
  ⟨(5 / 2 : ℂ), by norm_num⟩

/-- Two independent source displacements which collapse to zero. -/
def completeResolutionVerticalFirstInput (K : ℕ) :
    CompleteResolutionSourceSpace :=
  completeResolutionSourceEmbedding K
      completeResolutionVerticalFirstPoint -
    completeResolutionSourceEmbedding K
      completeResolutionVerticalBasePoint

def completeResolutionVerticalSecondInput (K : ℕ) :
    CompleteResolutionSourceSpace :=
  completeResolutionSourceEmbedding K
      completeResolutionVerticalSecondPoint -
    completeResolutionSourceEmbedding K
      completeResolutionVerticalBasePoint

/-- Their two-clock reader displacements. -/
def completeResolutionVerticalFirstOutput : ℂ × ℂ :=
  twoPrimeShellTransferSpectrum
      completeResolutionVerticalFirstPoint.1 -
    twoPrimeShellTransferSpectrum
      completeResolutionVerticalBasePoint.1

def completeResolutionVerticalSecondOutput : ℂ × ℂ :=
  twoPrimeShellTransferSpectrum
      completeResolutionVerticalSecondPoint.1 -
    twoPrimeShellTransferSpectrum
      completeResolutionVerticalBasePoint.1

theorem completeResolutionVerticalFirstOutput_eq :
    completeResolutionVerticalFirstOutput =
      (-(1 / 2 : ℂ), -(2 / 3 : ℂ)) := by
  apply Prod.ext <;>
    norm_num [completeResolutionVerticalFirstOutput,
      completeResolutionVerticalFirstPoint,
      completeResolutionVerticalBasePoint,
      twoPrimeShellTransferSpectrum,
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter,
      Complex.cpow_neg, Complex.cpow_natCast]

theorem completeResolutionVerticalSecondOutput_eq :
    completeResolutionVerticalSecondOutput =
      (-(3 / 4 : ℂ), -(8 / 9 : ℂ)) := by
  apply Prod.ext <;>
    norm_num [completeResolutionVerticalSecondOutput,
      completeResolutionVerticalSecondPoint,
      completeResolutionVerticalBasePoint,
      twoPrimeShellTransferSpectrum,
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter,
      Complex.cpow_neg, Complex.cpow_natCast]

theorem tendsto_completeResolutionVerticalFirstInput_zero :
    Tendsto completeResolutionVerticalFirstInput atTop (nhds 0) := by
  change Tendsto
    (fun K : ℕ =>
      completeResolutionSourceVector K (3 / 2 : ℂ) (by norm_num) -
        completeResolutionSourceVector K (1 / 2 : ℂ) (by norm_num))
    atTop (nhds 0)
  exact
    tendsto_completeResolutionSourceVector_sub_zero
      (3 / 2 : ℂ) (1 / 2 : ℂ) (by norm_num) (by norm_num)

theorem tendsto_completeResolutionVerticalSecondInput_zero :
    Tendsto completeResolutionVerticalSecondInput atTop (nhds 0) := by
  change Tendsto
    (fun K : ℕ =>
      completeResolutionSourceVector K (5 / 2 : ℂ) (by norm_num) -
        completeResolutionSourceVector K (1 / 2 : ℂ) (by norm_num))
    atTop (nhds 0)
  exact
    tendsto_completeResolutionSourceVector_sub_zero
      (5 / 2 : ℂ) (1 / 2 : ℂ) (by norm_num) (by norm_num)

/-- The two persistent output directions have nonzero determinant. -/
theorem completeResolutionVerticalOutput_determinant :
    completeResolutionVerticalFirstOutput.1 *
          completeResolutionVerticalSecondOutput.2 -
        completeResolutionVerticalFirstOutput.2 *
          completeResolutionVerticalSecondOutput.1 =
      -(1 / 18 : ℂ) := by
  rw [completeResolutionVerticalFirstOutput_eq,
    completeResolutionVerticalSecondOutput_eq]
  norm_num

/-- The persistent reader outputs span the entire two-clock target. -/
theorem completeResolutionVerticalOutputs_span (w : ℂ × ℂ) :
    ∃ a b : ℂ,
      w =
        a • completeResolutionVerticalFirstOutput +
          b • completeResolutionVerticalSecondOutput := by
  refine
    ⟨16 * w.1 - (27 / 2 : ℂ) * w.2,
      -12 * w.1 + 9 * w.2, ?_⟩
  rw [completeResolutionVerticalFirstOutput_eq,
    completeResolutionVerticalSecondOutput_eq]
  apply Prod.ext <;> simp <;> ring

/-- Vertical fibre of a linear relation over its zero source. -/
def linearRelationVerticalFiber
    {𝕜 X Y : Type*} [Semiring 𝕜]
    [AddCommMonoid X] [Module 𝕜 X]
    [AddCommMonoid Y] [Module 𝕜 Y]
    (R : Submodule 𝕜 (X × Y)) : Submodule 𝕜 Y :=
  R.comap (LinearMap.inr 𝕜 X Y)

/-- **Universal cofinal graph-rank principle.** A closed linear relation
which contains one graph direction whose source tends to zero must contain
the limiting output in its vertical fibre. The scalar field is arbitrary. -/
theorem closedLinearRelation_mem_vertical_of_tendsto_zero
    {𝕜 X Y : Type*}
    [Semiring 𝕜]
    [AddCommMonoid X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommMonoid Y] [Module 𝕜 Y] [TopologicalSpace Y]
    (R : Submodule 𝕜 (X × Y)) (hclosed : IsClosed (R : Set (X × Y)))
    (u : ℕ → X) (v : Y) (hu : Tendsto u atTop (nhds 0))
    (hgraph : ∀ K : ℕ, (u K, v) ∈ R) :
    v ∈ linearRelationVerticalFiber R := by
  change ((0 : X), v) ∈ R
  apply hclosed.mem_of_tendsto (hu.prodMk_nhds tendsto_const_nhds)
  exact Filter.Eventually.of_forall hgraph

/-- **Cofinal rank-transmutation law.** Every linear span retained by
outputs whose source representatives collapse to zero becomes vertical
rank in every closed graph limit. -/
theorem closedLinearRelation_span_le_verticalFiber_of_cofinalCollapse
    {𝕜 X Y : Type*}
    [Semiring 𝕜]
    [AddCommMonoid X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommMonoid Y] [Module 𝕜 Y] [TopologicalSpace Y]
    (R : Submodule 𝕜 (X × Y)) (hclosed : IsClosed (R : Set (X × Y)))
    (V : Set Y)
    (hcollapse : ∀ v ∈ V, ∃ u : ℕ → X,
      Tendsto u atTop (nhds 0) ∧ ∀ K : ℕ, (u K, v) ∈ R) :
    Submodule.span 𝕜 V ≤ linearRelationVerticalFiber R := by
  rw [Submodule.span_le]
  intro v hv
  obtain ⟨u, hu, hgraph⟩ := hcollapse v hv
  exact closedLinearRelation_mem_vertical_of_tendsto_zero
    R hclosed u v hu hgraph

/-- The two exact complete-source graph directions force every target
direction into the vertical fibre of any closed linear graph completion. -/
theorem completeResolution_closedLinearRelation_fullVertical
    (R : Submodule ℂ
      (CompleteResolutionSourceSpace × (ℂ × ℂ)))
    (hclosed : IsClosed
      (R : Set (CompleteResolutionSourceSpace × (ℂ × ℂ))))
    (hfirst : ∀ K : ℕ,
      (completeResolutionVerticalFirstInput K,
        completeResolutionVerticalFirstOutput) ∈ R)
    (hsecond : ∀ K : ℕ,
      (completeResolutionVerticalSecondInput K,
        completeResolutionVerticalSecondOutput) ∈ R)
    (w : ℂ × ℂ) :
    ((0 : CompleteResolutionSourceSpace), w) ∈ R := by
  have hv₁ :
      ((0 : CompleteResolutionSourceSpace),
        completeResolutionVerticalFirstOutput) ∈ R :=
    closedLinearRelation_mem_vertical_of_tendsto_zero
      R hclosed completeResolutionVerticalFirstInput
      completeResolutionVerticalFirstOutput
      tendsto_completeResolutionVerticalFirstInput_zero hfirst
  have hv₂ :
      ((0 : CompleteResolutionSourceSpace),
        completeResolutionVerticalSecondOutput) ∈ R :=
    closedLinearRelation_mem_vertical_of_tendsto_zero
      R hclosed completeResolutionVerticalSecondInput
      completeResolutionVerticalSecondOutput
      tendsto_completeResolutionVerticalSecondInput_zero hsecond
  obtain ⟨a, b, hw⟩ :=
    completeResolutionVerticalOutputs_span w
  rw [hw]
  simpa using
    Submodule.add_mem R
      (Submodule.smul_mem R a hv₁)
      (Submodule.smul_mem R b hv₂)

/-- No closed linear graph completion retaining both source clocks can be
single-valued at the collapsed source point. -/
theorem no_singleValued_completeResolution_closedLinearRelation
    (R : Submodule ℂ
      (CompleteResolutionSourceSpace × (ℂ × ℂ)))
    (hclosed : IsClosed
      (R : Set (CompleteResolutionSourceSpace × (ℂ × ℂ))))
    (hfirst : ∀ K : ℕ,
      (completeResolutionVerticalFirstInput K,
        completeResolutionVerticalFirstOutput) ∈ R)
    (hsecond : ∀ K : ℕ,
      (completeResolutionVerticalSecondInput K,
        completeResolutionVerticalSecondOutput) ∈ R)
    (hsingle : ∀ y z : ℂ × ℂ,
      ((0 : CompleteResolutionSourceSpace), y) ∈ R →
      ((0 : CompleteResolutionSourceSpace), z) ∈ R →
      y = z) :
    False := by
  have hzero :
      ((0 : CompleteResolutionSourceSpace), (0 : ℂ × ℂ)) ∈ R :=
    R.zero_mem
  have hone :
      ((0 : CompleteResolutionSourceSpace), ((1 : ℂ), (0 : ℂ))) ∈ R :=
    completeResolution_closedLinearRelation_fullVertical
      R hclosed hfirst hsecond _
  have := hsingle 0 (1, 0) hzero hone
  have hfst := congrArg Prod.fst this
  norm_num at hfst

/-- **Maximal two-clock vertical-boundary law.** Two source directions
collapse to zero while their exact source-reader images form a basis of the
full target. Consequently any linear graph limit retaining the complete
reader has full vertical fibre `ℂ × ℂ`, rather than the zero fibre of a
closable operator graph. -/
theorem completeResolution_twoClockMaximalVerticalBoundary_law :
    Tendsto completeResolutionVerticalFirstInput atTop (nhds 0) ∧
      Tendsto completeResolutionVerticalSecondInput atTop (nhds 0) ∧
      (∀ w : ℂ × ℂ, ∃ a b : ℂ,
        w =
          a • completeResolutionVerticalFirstOutput +
            b • completeResolutionVerticalSecondOutput) :=
  ⟨tendsto_completeResolutionVerticalFirstInput_zero,
    tendsto_completeResolutionVerticalSecondInput_zero,
    completeResolutionVerticalOutputs_span⟩

/-- Exact separation of the selected prime term from the finite Möbius
prefix ending at that prime. -/
theorem dpoly2_moebiusCoeff_Icc_split_prime
    (q : Nat.Primes) (w : ℂ) :
    dpoly2 moebiusCoeff (Finset.Icc 1 q.1) w =
      dpoly2 moebiusCoeff (Finset.Icc 1 (q.1 - 1)) w -
        (q.1 : ℂ) ^ (-w) := by
  have hset :
      Finset.Icc 1 q.1 =
        insert q.1 (Finset.Icc 1 (q.1 - 1)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨hn1, hnq⟩
      by_cases h : n = q.1
      · exact Or.inl h
      · exact Or.inr ⟨hn1, by omega⟩
    · rintro (rfl | ⟨hn1, hnq⟩)
      · exact ⟨q.2.one_le, le_rfl⟩
      · exact ⟨hn1, hnq.trans (Nat.sub_le _ _)⟩
  rw [hset, dpoly2]
  have hqnot :
      q.1 ∉ Finset.Icc 1 (q.1 - 1) := by
    simp only [Finset.mem_Icc]
    intro h
    have hlt : q.1 - 1 < q.1 :=
      Nat.sub_lt q.2.pos (by norm_num)
    exact (Nat.not_le_of_lt hlt) h.2
  rw [Finset.sum_insert hqnot]
  simp [dpoly2, moebiusCoeff,
    ArithmeticFunction.moebius_apply_prime q.2]
  ring

/-- Reciprocal zeta after exact removal of every Möbius coefficient
strictly below one selected prime. -/
def invZetaPrimePeeledResidual (q : Nat.Primes) (w : ℂ) : ℂ :=
  (riemannZeta w)⁻¹ -
    dpoly2 moebiusCoeff (Finset.Icc 1 (q.1 - 1)) w

/-- Uniform ray estimate for an arbitrary selected prime atom. -/
theorem norm_prime_cpow_mul_invZetaPrimePeeledResidual_add_one_le
    (q : Nat.Primes) {w : ℂ} (hw : 1 < w.re) :
    ‖(q.1 : ℂ) ^ w * invZetaPrimePeeledResidual q w + 1‖
      ≤ (q.1 : ℝ) / (w.re - 1) := by
  have htail :=
    norm_inv_riemannZeta_sub_dpoly2_moebiusCoeff_le
      hw (M := q.1) q.2.one_le
  rw [dpoly2_moebiusCoeff_Icc_split_prime q w] at htail
  have hpow :
      (q.1 : ℂ) ^ w * (q.1 : ℂ) ^ (-w) = 1 := by
    rw [← Complex.cpow_add _ _ (by
      exact_mod_cast q.2.ne_zero)]
    simp
  have hre :
      (q.1 : ℂ) ^ w * invZetaPrimePeeledResidual q w + 1 =
        (q.1 : ℂ) ^ w *
          ((riemannZeta w)⁻¹ -
            (dpoly2 moebiusCoeff (Finset.Icc 1 (q.1 - 1)) w -
              (q.1 : ℂ) ^ (-w))) := by
    rw [invZetaPrimePeeledResidual]
    rw [← hpow]
    ring
  rw [hre, norm_mul]
  have hnorm :
      ‖(q.1 : ℂ) ^ w‖ = (q.1 : ℝ) ^ w.re := by
    exact Complex.norm_natCast_cpow_of_pos q.2.pos w
  rw [hnorm]
  refine (mul_le_mul_of_nonneg_left htail
    (Real.rpow_nonneg (by positivity) _)).trans ?_
  have hqpos : (0 : ℝ) < q.1 := by exact_mod_cast q.2.pos
  have hpowR :
      (q.1 : ℝ) ^ w.re * (q.1 : ℝ) ^ (1 - w.re) = q.1 := by
    rw [← Real.rpow_add hqpos]
    norm_num
  calc
    (q.1 : ℝ) ^ w.re *
          ((q.1 : ℝ) ^ (1 - w.re) / (w.re - 1))
        = ((q.1 : ℝ) ^ w.re * (q.1 : ℝ) ^ (1 - w.re)) /
            (w.re - 1) := by ring
    _ = (q.1 : ℝ) / (w.re - 1) := by rw [hpowR]
    _ ≤ (q.1 : ℝ) / (w.re - 1) := le_rfl

/-- Every selected prime is an exact asymptotic atom on every open
right-half-plane ray after the finite preceding Möbius prefix is removed. -/
theorem tendsto_prime_cpow_nat_mul_invZetaPrimePeeledResidual
    (q : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        (q.1 : ℂ) ^ ((n : ℂ) * s) *
          invZetaPrimePeeledResidual q ((n : ℂ) * s))
      atTop (nhds (-1)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hre :
      Tendsto (fun n : ℕ => (((n : ℂ) * s).re))
        atTop atTop := by
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const hs
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1
      (hre.eventually_gt_atTop
        (1 + (q.1 : ℝ) / ε))
  refine ⟨N, fun n hn => ?_⟩
  have hnlarge := hN n hn
  have hqpos : (0 : ℝ) < q.1 := by exact_mod_cast q.2.pos
  have hw : 1 < (((n : ℂ) * s).re) := by
    have hpos : 0 < (q.1 : ℝ) / ε := div_pos hqpos hε
    linarith
  have hbound :=
    norm_prime_cpow_mul_invZetaPrimePeeledResidual_add_one_le
      q hw
  rw [dist_eq, show
    (q.1 : ℂ) ^ ((n : ℂ) * s) *
        invZetaPrimePeeledResidual q ((n : ℂ) * s) - (-1) =
      (q.1 : ℂ) ^ ((n : ℂ) * s) *
        invZetaPrimePeeledResidual q ((n : ℂ) * s) + 1 by ring]
  refine hbound.trans_lt ?_
  have hden :
      (q.1 : ℝ) / ε < (((n : ℂ) * s).re) - 1 := by
    linarith
  have hdenpos : 0 < (((n : ℂ) * s).re) - 1 := by
    linarith
  apply (div_lt_iff₀ hdenpos).2
  have hscaled := (div_lt_iff₀ hε).mp hden
  nlinarith

/-- Shell residual after exact subtraction of all Möbius atoms below
the selected prime. -/
def primePeeledShellResidual
    (q : Nat.Primes) (n : ℕ) (s : ℂ) : ℂ :=
  invZetaPrimePeeledResidual q (((n + 1 : ℕ) : ℂ) * s) -
    invZetaPrimePeeledResidual q ((n : ℂ) * s)

/-- Arbitrary-prime shell extraction. -/
theorem tendsto_prime_cpow_nat_mul_primePeeledShellResidual
    (q : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        (q.1 : ℂ) ^ ((n : ℂ) * s) *
          primePeeledShellResidual q n s)
      atTop (nhds (1 - (q.1 : ℂ) ^ (-s))) := by
  let B : ℕ → ℂ := fun n =>
    (q.1 : ℂ) ^ ((n : ℂ) * s) *
      invZetaPrimePeeledResidual q ((n : ℂ) * s)
  have hB : Tendsto B atTop (nhds (-1)) := by
    simpa [B] using
      tendsto_prime_cpow_nat_mul_invZetaPrimePeeledResidual q hs
  have hsucc : Tendsto (fun n : ℕ => B (n + 1))
      atTop (nhds (-1)) := by
    exact hB.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hlim := (hsucc.const_mul ((q.1 : ℂ) ^ (-s))).sub hB
  have htarget :
      (q.1 : ℂ) ^ (-s) * (-1) - (-1) =
        1 - (q.1 : ℂ) ^ (-s) := by ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [] with n
  have hpow :
      (q.1 : ℂ) ^ (-s) *
          (q.1 : ℂ) ^ (((n + 1 : ℕ) : ℂ) * s) =
        (q.1 : ℂ) ^ ((n : ℂ) * s) := by
    rw [← Complex.cpow_add _ _ (by
      exact_mod_cast q.2.ne_zero)]
    congr 2
    push_cast
    ring
  dsimp only [B, primePeeledShellResidual]
  rw [← mul_assoc, hpow]
  push_cast
  ring

/-- Adjacent transfer in one arbitrary-prime peeled shell. -/
def primePeeledShellAdjacentTransfer
    (q : Nat.Primes) (n : ℕ) (s : ℂ) : ℂ :=
  primePeeledShellResidual q (n + 1) s /
    primePeeledShellResidual q n s

/-- Every prime peeled shell has raw transfer character `q⁻ˢ`. -/
theorem tendsto_primePeeledShellAdjacentTransfer
    (q : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ => primePeeledShellAdjacentTransfer q n s)
      atTop (nhds ((q.1 : ℂ) ^ (-s))) := by
  let B : ℕ → ℂ := fun n =>
    (q.1 : ℂ) ^ ((n : ℂ) * s) *
      primePeeledShellResidual q n s
  have hB : Tendsto B atTop
      (nhds (1 - (q.1 : ℂ) ^ (-s))) := by
    simpa only [B] using
      tendsto_prime_cpow_nat_mul_primePeeledShellResidual q hs
  have hlim_ne : 1 - (q.1 : ℂ) ^ (-s) ≠ 0 :=
    one_sub_prime_cpow_neg_ne_zero q.2.two_le hs
  have hBsucc : Tendsto (fun n : ℕ => B (n + 1)) atTop
      (nhds (1 - (q.1 : ℂ) ^ (-s))) :=
    hB.comp (by
      simpa [Nat.add_comm] using tendsto_add_atTop_nat 1)
  have hratio :
      Tendsto (fun n : ℕ => B (n + 1) / B n)
        atTop (nhds 1) := by
    have h := hBsucc.div hB hlim_ne
    rw [div_self hlim_ne] at h
    change Tendsto ((fun n : ℕ => B (n + 1)) / B)
      atTop (nhds 1)
    exact h
  have hscaled :=
    (tendsto_const_nhds.mul hratio :
      Tendsto
        (fun n : ℕ =>
          (q.1 : ℂ) ^ (-s) * (B (n + 1) / B n))
        atTop (nhds ((q.1 : ℂ) ^ (-s) * 1)))
  rw [mul_one] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [hB.eventually_ne hlim_ne] with n hn
  have hpow :
      (q.1 : ℂ) ^ (((n + 1 : ℕ) : ℂ) * s) =
        (q.1 : ℂ) ^ ((n : ℂ) * s) * (q.1 : ℂ) ^ s := by
    rw [← Complex.cpow_add _ _ (by
      exact_mod_cast q.2.ne_zero)]
    congr 2
    push_cast
    ring
  have hpow_ne :
      (q.1 : ℂ) ^ ((n : ℂ) * s) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast q.2.ne_zero)
  have hq_s_ne : (q.1 : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast q.2.ne_zero)
  dsimp only [primePeeledShellAdjacentTransfer, B] at hn ⊢
  rw [hpow]
  rw [Complex.cpow_neg]
  field_simp [hpow_ne, hq_s_ne] at hn ⊢

/-- Normalized arbitrary-prime peeled-shell transport. -/
def normalizedPrimePeeledShellAdjacentTransfer
    (q : Nat.Primes) (n : ℕ) (s : ℂ) : ℂ :=
  (q.1 : ℂ) ^ (1 / 2 : ℂ) *
    primePeeledShellAdjacentTransfer q n s

/-- Arbitrary-prime normal transport has exact character
`q^(1/2-s)`. -/
theorem tendsto_normalizedPrimePeeledShellAdjacentTransfer
    (q : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun n : ℕ =>
        normalizedPrimePeeledShellAdjacentTransfer q n s)
      atTop
      (nhds ((q.1 : ℂ) ^ ((1 / 2 : ℂ) - s))) := by
  have h :=
    (tendsto_primePeeledShellAdjacentTransfer q hs).const_mul
      ((q.1 : ℂ) ^ (1 / 2 : ℂ))
  change Tendsto
    (fun n : ℕ =>
      (q.1 : ℂ) ^ (1 / 2 : ℂ) *
        primePeeledShellAdjacentTransfer q n s)
    atTop
    (nhds ((q.1 : ℂ) ^ ((1 / 2 : ℂ) - s)))
  rw [
    show (1 / 2 : ℂ) - s = (1 / 2 : ℂ) + (-s) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast q.2.ne_zero)]
  exact h

/-- The extracted prime character is exactly the least-atom modular
character from the projective recurrence geometry. -/
theorem primePeeledShellTransferCharacter_eq_leastAtom
    (q : Nat.Primes) (s : ℂ) :
    (q.1 : ℂ) ^ ((1 / 2 : ℂ) - s) =
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter
        (q.1 : ℝ) 1 s := by
  simp [GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter]

/-- Finite packet of arbitrary distinct prime normal characters. -/
def finitePrimeNormalSpectrum
    {r : ℕ} (q : Fin r → Nat.Primes) (s : ℂ) : Fin r → ℂ :=
  fun i => ((q i).1 : ℂ) ^ ((1 / 2 : ℂ) - s)

/-- Canonical real sample packet for the finite prime normal spectrum. -/
def finitePrimeNormalSamplePoint
    {r : ℕ} (j : Fin r) : ℂ :=
  (1 / 2 : ℂ) + (j.1 : ℂ)

theorem finitePrimeNormalSpectrum_samplePoint
    {r : ℕ} (q : Fin r → Nat.Primes) (i j : Fin r) :
    finitePrimeNormalSpectrum q (finitePrimeNormalSamplePoint j) i =
      (((q i).1 : ℂ)⁻¹) ^ j.1 := by
  rw [finitePrimeNormalSpectrum, finitePrimeNormalSamplePoint]
  have hq : ((q i).1 : ℂ) ≠ 0 := by
    exact_mod_cast (q i).2.ne_zero
  rw [show (1 / 2 : ℂ) - ((1 / 2 : ℂ) + (j.1 : ℂ)) =
      -(j.1 : ℂ) by ring]
  rw [Complex.cpow_neg, Complex.cpow_natCast]
  rw [inv_pow]

/-- Distinct primes give a nonsingular normal-character sample packet. -/
theorem finitePrimeNormalSpectrum_sampleMatrix_det_ne_zero
    {r : ℕ} (q : Fin r → Nat.Primes) (hq : Function.Injective q) :
    Matrix.det
      ((fun i j =>
        finitePrimeNormalSpectrum q (finitePrimeNormalSamplePoint j) i) :
          Matrix (Fin r) (Fin r) ℂ) ≠ 0 := by
  let node : Fin r → ℂ := fun i => (((q i).1 : ℂ)⁻¹)
  have hnode : Function.Injective node := by
    intro i j hij
    apply hq
    apply Subtype.ext
    have hcast : ((q i).1 : ℂ) = ((q j).1 : ℂ) := by
      exact inv_injective hij
    exact_mod_cast hcast
  have hv :
      (fun i j =>
        finitePrimeNormalSpectrum q (finitePrimeNormalSamplePoint j) i :
          Matrix (Fin r) (Fin r) ℂ) =
        Matrix.vandermonde node := by
    ext i j
    simp only [Matrix.vandermonde_apply,
      finitePrimeNormalSpectrum_samplePoint]
    rfl
  rw [hv]
  exact (Matrix.det_vandermonde_ne_zero_iff.mpr hnode)

/-- Canonical samples span every finite prime-normal target. -/
theorem finitePrimeNormalSpectrum_samplePoint_span
    {r : ℕ} (q : Fin r → Nat.Primes) (hq : Function.Injective q)
    (w : Fin r → ℂ) :
    ∃ a : Fin r → ℂ,
      w = ∑ j, a j •
        finitePrimeNormalSpectrum q (finitePrimeNormalSamplePoint j) := by
  let M : Matrix (Fin r) (Fin r) ℂ :=
    fun i j =>
      finitePrimeNormalSpectrum q (finitePrimeNormalSamplePoint j) i
  have hdet : M.det ≠ 0 := by
    simpa only [M] using
      finitePrimeNormalSpectrum_sampleMatrix_det_ne_zero q hq
  have hunit : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨a, ha⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) w
  refine ⟨a, ?_⟩
  rw [← ha]
  funext i
  simp only [M, Matrix.mulVec, dotProduct, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Source-internal reader for an arbitrary finite packet of prime normal
characters.  Its spectral preimage is uniquely determined by the finite
complete-source point. -/
noncomputable def completeResolutionFinitePrimeNormalReader
    {r : ℕ} (K : ℕ) (q : Fin r → Nat.Primes)
    (x : CompleteResolutionSourceImage K) : Fin r → ℂ :=
  finitePrimeNormalSpectrum q
    (completeResolutionSourceImagePreimage K x).1

@[simp] theorem completeResolutionFinitePrimeNormalReader_imagePoint
    {r : ℕ} (K : ℕ) (q : Fin r → Nat.Primes)
    (s : CompleteResolutionRightHalfPlane) :
    completeResolutionFinitePrimeNormalReader K q
        (completeResolutionSourceImagePoint K s) =
      finitePrimeNormalSpectrum q s.1 := by
  have hpre :
      completeResolutionSourceImagePreimage K
          (completeResolutionSourceImagePoint K s) = s := by
    apply completeResolutionSourceEmbedding_injective K
    exact completeResolutionSourceImagePreimage_spec K _
  simp [completeResolutionFinitePrimeNormalReader, hpre]

/-- Canonical right-half-plane samples exposing all ranks of a finite
prime-normal packet. -/
def completeResolutionPrimeRankSamplePoint
    {r : ℕ} (j : Fin r) : CompleteResolutionRightHalfPlane :=
  ⟨finitePrimeNormalSamplePoint j, by
    simp [finitePrimeNormalSamplePoint]
    positivity⟩

/-- Source displacement from the common point section at one canonical
prime-rank sample. -/
def completeResolutionPrimeRankInput
    {r : ℕ} (K : ℕ) (j : Fin r) :
    CompleteResolutionSourceSpace :=
  completeResolutionSourceEmbedding K
      (completeResolutionPrimeRankSamplePoint j) -
    sourceFusionPointSection 1

/-- Persistent output at one canonical sample of a finite prime packet. -/
def completeResolutionPrimeRankOutput
    {r : ℕ} (q : Fin r → Nat.Primes) (j : Fin r) : Fin r → ℂ :=
  finitePrimeNormalSpectrum q (finitePrimeNormalSamplePoint j)

/-- Every canonical finite-rank source displacement collapses to zero. -/
theorem tendsto_completeResolutionPrimeRankInput_zero
    {r : ℕ} (j : Fin r) :
    Tendsto (fun K : ℕ => completeResolutionPrimeRankInput K j)
      atTop (nhds 0) := by
  have h :=
    (tendsto_completeResolutionSourceVector_pointSection
      (finitePrimeNormalSamplePoint j)
      (completeResolutionPrimeRankSamplePoint j).2).sub_const
        (sourceFusionPointSection 1)
  simpa [completeResolutionPrimeRankInput,
    completeResolutionSourceEmbedding,
    completeResolutionPrimeRankSamplePoint] using h

/-- **Arbitrary finite-rank Riemann source boundary.** For distinct
selected primes, every closed linear completion retaining the exact
source-internal normal packet has the whole finite target as vertical
fibre over the common cofinal source point. -/
theorem completeResolution_closedLinearRelation_arbitraryPrime_fullVertical
    {r : ℕ} (q : Fin r → Nat.Primes) (hq : Function.Injective q)
    (R : Submodule ℂ
      (CompleteResolutionSourceSpace × (Fin r → ℂ)))
    (hclosed : IsClosed
      (R : Set (CompleteResolutionSourceSpace × (Fin r → ℂ))))
    (hgraph : ∀ (K : ℕ) (j : Fin r),
      (completeResolutionPrimeRankInput K j,
        completeResolutionPrimeRankOutput q j) ∈ R)
    (w : Fin r → ℂ) :
    ((0 : CompleteResolutionSourceSpace), w) ∈ R := by
  have hvertical : ∀ j : Fin r,
      completeResolutionPrimeRankOutput q j ∈
        linearRelationVerticalFiber R := by
    intro j
    exact closedLinearRelation_mem_vertical_of_tendsto_zero
      R hclosed
      (fun K : ℕ => completeResolutionPrimeRankInput K j)
      (completeResolutionPrimeRankOutput q j)
      (tendsto_completeResolutionPrimeRankInput_zero j)
      (fun K => hgraph K j)
  obtain ⟨a, hw⟩ :=
    finitePrimeNormalSpectrum_samplePoint_span q hq w
  rw [hw]
  change
    (∑ j : Fin r,
      a j • completeResolutionPrimeRankOutput q j) ∈
        linearRelationVerticalFiber R
  exact
    Submodule.sum_mem (linearRelationVerticalFiber R) fun j _ =>
      Submodule.smul_mem
        (linearRelationVerticalFiber R) (a j) (hvertical j)

/-- Canonical packet of the first `r` primes. -/
def completeResolutionNthPrimePacket
    {r : ℕ} (i : Fin r) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime i.1, Nat.prime_nth_prime i.1⟩

theorem completeResolutionNthPrimePacket_injective
    {r : ℕ} :
    Function.Injective
      (completeResolutionNthPrimePacket (r := r)) := by
  intro i j hij
  apply Fin.ext
  apply Nat.nth_injective Nat.infinite_setOf_prime
  exact congrArg Subtype.val hij

/-- **Unbounded finite vertical-rank law.** At every finite rank there is
a canonical packet of exact, source-internal prime normal characters whose
entire target rank survives source collapse only as vertical multiplicity
in every closed linear completion that retains the packet. -/
theorem completeResolution_unboundedFinitePrimeRankVerticalBoundary_law
    (r : ℕ) :
    ∃ q : Fin r → Nat.Primes,
      Function.Injective q ∧
      (∀ j : Fin r,
        Tendsto (fun K : ℕ => completeResolutionPrimeRankInput K j)
          atTop (nhds 0)) ∧
      ∀ (R : Submodule ℂ
          (CompleteResolutionSourceSpace × (Fin r → ℂ))),
        IsClosed
            (R : Set
              (CompleteResolutionSourceSpace × (Fin r → ℂ))) →
        (∀ (K : ℕ) (j : Fin r),
          (completeResolutionPrimeRankInput K j,
            completeResolutionPrimeRankOutput q j) ∈ R) →
        ∀ w : Fin r → ℂ,
          ((0 : CompleteResolutionSourceSpace), w) ∈ R := by
  refine
    ⟨completeResolutionNthPrimePacket,
      completeResolutionNthPrimePacket_injective,
      tendsto_completeResolutionPrimeRankInput_zero, ?_⟩
  intro R hclosed hgraph w
  exact
    completeResolution_closedLinearRelation_arbitraryPrime_fullVertical
      completeResolutionNthPrimePacket
      completeResolutionNthPrimePacket_injective
      R hclosed hgraph w

/-- Countable prime-normal reader on the actual finite complete-source
image. -/
noncomputable def completeResolutionCountablePrimeNormalReader
    (K : ℕ) (x : CompleteResolutionSourceImage K) : ℕ → ℂ :=
  fun i =>
    (Nat.nth Nat.Prime i : ℂ) ^
      ((1 / 2 : ℂ) -
        (completeResolutionSourceImagePreimage K x).1)

@[simp] theorem completeResolutionCountablePrimeNormalReader_imagePoint
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    completeResolutionCountablePrimeNormalReader K
        (completeResolutionSourceImagePoint K s) =
      fun i : ℕ =>
        (Nat.nth Nat.Prime i : ℂ) ^
          ((1 / 2 : ℂ) - s.1) := by
  have hpre :
      completeResolutionSourceImagePreimage K
          (completeResolutionSourceImagePoint K s) = s := by
    apply completeResolutionSourceEmbedding_injective K
    exact completeResolutionSourceImagePreimage_spec K _
  funext i
  change
    (Nat.nth Nat.Prime i : ℂ) ^
        ((1 / 2 : ℂ) -
          (completeResolutionSourceImagePreimage K
            (completeResolutionSourceImagePoint K s)).1) =
      (Nat.nth Nat.Prime i : ℂ) ^ ((1 / 2 : ℂ) - s.1)
  rw [hpre]

/-- Canonical countable sequence of real sampling points. -/
def completeResolutionCountablePrimeSamplePoint
    (j : ℕ) : CompleteResolutionRightHalfPlane :=
  ⟨(1 / 2 : ℂ) + (j : ℂ), by
    simp
    positivity⟩

/-- Centered source input at one countable prime-normal sample. -/
def completeResolutionCountablePrimeInput
    (K j : ℕ) : CompleteResolutionSourceSpace :=
  completeResolutionSourceEmbedding K
      (completeResolutionCountablePrimeSamplePoint j) -
    sourceFusionPointSection 1

/-- Countable prime-normal output at one canonical sample. -/
def completeResolutionCountablePrimeOutput
    (j : ℕ) : ℕ → ℂ :=
  fun i => ((Nat.nth Nat.Prime i : ℂ)⁻¹) ^ j

theorem completeResolutionCountablePrimeReader_samplePoint
    (K j : ℕ) :
    completeResolutionCountablePrimeNormalReader K
        (completeResolutionSourceImagePoint K
          (completeResolutionCountablePrimeSamplePoint j)) =
      completeResolutionCountablePrimeOutput j := by
  rw [completeResolutionCountablePrimeNormalReader_imagePoint]
  funext i
  simp only [completeResolutionCountablePrimeSamplePoint,
    completeResolutionCountablePrimeOutput]
  have hprime : (Nat.nth Nat.Prime i : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.prime_nth_prime i).ne_zero
  rw [show (1 / 2 : ℂ) - ((1 / 2 : ℂ) + (j : ℂ)) =
      -(j : ℂ) by ring]
  rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]

theorem tendsto_completeResolutionCountablePrimeInput_zero
    (j : ℕ) :
    Tendsto (fun K : ℕ => completeResolutionCountablePrimeInput K j)
      atTop (nhds 0) := by
  have h :=
    (tendsto_completeResolutionSourceVector_pointSection
      ((1 / 2 : ℂ) + (j : ℂ))
      (completeResolutionCountablePrimeSamplePoint j).2).sub_const
        (sourceFusionPointSection 1)
  simpa [completeResolutionCountablePrimeInput,
    completeResolutionSourceEmbedding,
    completeResolutionCountablePrimeSamplePoint] using h

/-- **Single-horizon unbounded-rank law.** If one closed relation retains
the countable prime-normal reader across the cofinal source collapse, then
every finite coordinate projection of its vertical fibre is surjective.
Thus one completed relation has unbounded finite observable quotient rank,
not merely a separately chosen finite-rank example at each rank. -/
theorem completeResolution_closedLinearRelation_countablePrime_projectivelyFull
    (R : Submodule ℂ
      (CompleteResolutionSourceSpace × (ℕ → ℂ)))
    (hclosed : IsClosed
      (R : Set (CompleteResolutionSourceSpace × (ℕ → ℂ))))
    (hgraph : ∀ (K j : ℕ),
      (completeResolutionCountablePrimeInput K j,
        completeResolutionCountablePrimeOutput j) ∈ R)
    (r : ℕ) (w : Fin r → ℂ) :
    ∃ v : ℕ → ℂ,
      v ∈ linearRelationVerticalFiber R ∧
      ∀ i : Fin r, v i.1 = w i := by
  have hvertical : ∀ j : ℕ,
      completeResolutionCountablePrimeOutput j ∈
        linearRelationVerticalFiber R := by
    intro j
    exact closedLinearRelation_mem_vertical_of_tendsto_zero
      R hclosed
      (fun K : ℕ => completeResolutionCountablePrimeInput K j)
      (completeResolutionCountablePrimeOutput j)
      (tendsto_completeResolutionCountablePrimeInput_zero j)
      (fun K => hgraph K j)
  obtain ⟨a, hw⟩ :=
    finitePrimeNormalSpectrum_samplePoint_span
      completeResolutionNthPrimePacket
      completeResolutionNthPrimePacket_injective w
  let v : ℕ → ℂ :=
    ∑ j : Fin r,
      a j • completeResolutionCountablePrimeOutput j.1
  have hv : v ∈ linearRelationVerticalFiber R := by
    exact
      Submodule.sum_mem (linearRelationVerticalFiber R) fun j _ =>
        Submodule.smul_mem (linearRelationVerticalFiber R)
          (a j) (hvertical j.1)
  refine ⟨v, hv, ?_⟩
  intro i
  have hi := congrFun hw i
  rw [hi]
  simp only [v, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, completeResolutionCountablePrimeOutput,
    completeResolutionNthPrimePacket,
    finitePrimeNormalSpectrum_samplePoint]

end

end RHTower
