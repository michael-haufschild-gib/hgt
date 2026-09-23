import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeLogMeshPhaseEscape

/-!
# Physical direct-prime weighted-pole escape

An off-line Xi zero cannot be hidden by the phase of an actual physical two-edge test.  On
cofinally many exact natural logarithmic apertures, the physical square is nonzero at the zero.
The direct infinite-prime source then has its full divisor residue.  Approaching opposite to that
complex residue forces the real part of the weighted source below every level in every
neighborhood.

The final theorem is an exact RH criterion using only eventual local lower boundedness of the
literal physical square times the direct infinite-prime flux.  No completed Gamma source or
contour correction occurs in the predicate.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- A nonzero complex simple-pole residue forces the real part below every level in every
punctured neighborhood, by approaching opposite to the residue direction. -/
theorem exists_realPart_lt_near_of_punctured_residue
    {f : ℂ → ℂ} {alpha C : ℂ} (hC : C ≠ 0)
    (hres : Tendsto (fun z : ℂ ↦ (z - alpha) * f z)
      (nhdsWithin alpha ({alpha}ᶜ)) (nhds C)) :
    ∀ r : ℝ, 0 < r → ∀ B : ℝ, ∃ z : ℂ,
      z ≠ alpha ∧ f z ≠ 0 ∧ dist z alpha < r ∧ (f z).re < B := by
  intro r hr B
  let epsilon : ℕ → ℝ := fun n ↦ (((n + 1 : ℕ) : ℝ)⁻¹)
  let z : ℕ → ℂ := fun n ↦ alpha - (epsilon n : ℂ) * C
  have hepsilonPos (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
    dsimp only [epsilon]
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hzTend : Tendsto z atTop (nhds alpha) := by
    have hcast : Tendsto (fun n ↦ (epsilon n : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hepsilonZero
    simpa [z] using tendsto_const_nhds.sub (hcast.mul_const C)
  have hzNe (n : ℕ) : z n ≠ alpha := by
    intro h
    have hzero : (epsilon n : ℂ) * C = 0 := by
      exact sub_eq_self.mp (by simpa only [z] using h)
    exact (mul_ne_zero (ofReal_ne_zero.mpr (hepsilonPos n).ne') hC) hzero
  have hzWithin : Tendsto z atTop (nhdsWithin alpha ({alpha}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzTend, Eventually.of_forall fun n ↦ by
      simpa only [mem_compl_iff, mem_singleton_iff] using hzNe n⟩
  have hresSeq : Tendsto (fun n ↦ (z n - alpha) * f (z n))
      atTop (nhds C) := by
    change Tendsto ((fun z : ℂ ↦ (z - alpha) * f z) ∘ z) atTop (nhds C)
    exact hres.comp hzWithin
  have hscaled : Tendsto (fun n ↦ (epsilon n : ℂ) * f (z n))
      atTop (nhds (-1 : ℂ)) := by
    have h := (hresSeq.div_const C).neg
    convert h using 1
    · funext n
      rw [show z n - alpha = -(epsilon n : ℂ) * C by simp [z]]
      field_simp [hC]
    · field_simp [hC]
  have hscaledRe : Tendsto (fun n ↦ epsilon n * (f (z n)).re)
      atTop (nhds (-1 : ℝ)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp hscaled
    simpa [Function.comp_def, Complex.mul_re] using h
  have hevScaled : ∀ᶠ n in atTop,
      epsilon n * (f (z n)).re < -1 / 2 :=
    hscaledRe.eventually (eventually_lt_nhds (by norm_num))
  have hBScaled : Tendsto (fun n ↦ epsilon n * B) atTop (nhds 0) :=
    by simpa using hepsilonZero.mul_const B
  have hevB : ∀ᶠ n in atTop, -1 / 2 < epsilon n * B :=
    hBScaled.eventually (eventually_gt_nhds (by norm_num))
  have hevNear : ∀ᶠ n in atTop, z n ∈ ball alpha r :=
    hzTend (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hevProdNe : ∀ᶠ n in atTop, (z n - alpha) * f (z n) ≠ 0 :=
    hresSeq.eventually_ne hC
  obtain ⟨n, hnScaled, hnB, hnNear, hnProdNe⟩ :=
    (hevScaled.and (hevB.and (hevNear.and hevProdNe))).exists
  have hfNe : f (z n) ≠ 0 := fun hf ↦ hnProdNe (by rw [hf, mul_zero])
  have hfLt : (f (z n)).re < B := by
    nlinarith [hepsilonPos n]
  exact ⟨z n, hzNe n, hfNe, by simpa only [mem_ball] using hnNear, hfLt⟩

/-- Neighborhood form of directional simple-pole escape. -/
theorem exists_realPart_lt_in_nhds_of_punctured_residue
    {f : ℂ → ℂ} {alpha C : ℂ} (hC : C ≠ 0)
    (hres : Tendsto (fun z : ℂ ↦ (z - alpha) * f z)
      (nhdsWithin alpha ({alpha}ᶜ)) (nhds C))
    {U : Set ℂ} (hU : U ∈ nhds alpha) (B : ℝ) :
    ∃ z : ℂ, z ≠ alpha ∧ f z ≠ 0 ∧ z ∈ U ∧ (f z).re < B := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨z, hzne, hfne, hzball, hzlt⟩ :=
    exists_realPart_lt_near_of_punctured_residue hC hres r hr B
  exact ⟨z, hzne, hfne, hball (by simpa only [mem_ball] using hzball), hzlt⟩

/-- Direct infinite-prime source weighted by the square of an actual physical two-edge test. -/
def xiPhysicalThetaAbelEnergyPrimeWeightedSource
    (L A c a : ℝ) (z : ℂ) : ℂ :=
  xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ) *
    (-I * infinitePrimeFlux (1 / 2 + z * I))

/-- Exact local residue of the physical square times the direct infinite-prime source. -/
theorem tendsto_xiPhysicalThetaAbelEnergyPrimeWeightedSource_normalizedResidue
    (L A c a : ℝ) {alpha : ℂ}
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2) :
    Tendsto
      (fun z : ℂ ↦ (z - alpha) *
        xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c a z)
      (nhdsWithin alpha ({alpha}ᶜ))
      (nhds (((analyticOrderAt xi (1 / 2 + alpha * I)).toNat : ℂ) *
        xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a alpha ^ (2 : ℕ))) := by
  let sigma : ℂ := 1 / 2 + alpha * I
  let coord : ℂ → ℂ := fun z ↦ 1 / 2 + z * I
  have hsigmaRe : sigma.re = 1 / 2 - alpha.im := by
    simp [sigma, Complex.mul_re, sub_eq_add_neg]
  have hsigmaStrip : 0 < sigma.re ∧ sigma.re < 1 := by
    rw [hsigmaRe]
    constructor <;> linarith
  have hcoordTend : Tendsto coord (nhds alpha) (nhds sigma) := by
    exact (continuousAt_const.add (continuousAt_id.mul continuousAt_const)).tendsto
  have hcoordNe : ∀ z : ℂ, z ≠ alpha → coord z ≠ sigma := by
    intro z hzne heq
    apply hzne
    have hmul : (z - alpha) * I = 0 := by
      dsimp only [coord, sigma] at heq
      linear_combination heq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right I_ne_zero)
  have hcoordWithin : Tendsto coord (nhdsWithin alpha ({alpha}ᶜ))
      (nhdsWithin sigma ({sigma}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcoordTend.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [mem_compl_iff, mem_singleton_iff] using hcoordNe z (by
      simpa only [mem_compl_iff, mem_singleton_iff] using hz)
  have hbase :=
    (riemannZeta_normalizedLogDeriv_tendsto_xi_order_of_mem_strip sigma
      hsigmaStrip).comp hcoordWithin
  have hprime : Tendsto
      (fun z : ℂ ↦ (z - alpha) *
        (-I * infinitePrimeFlux (1 / 2 + z * I)))
      (nhdsWithin alpha ({alpha}ᶜ))
      (nhds ((analyticOrderAt xi sigma).toNat : ℂ)) := by
    rw [show (fun z : ℂ ↦ (z - alpha) *
        (-I * infinitePrimeFlux (1 / 2 + z * I))) =
      (fun z : ℂ ↦ (coord z - sigma) * logDeriv riemannZeta (coord z)) by
        funext z
        rw [infinitePrimeFlux]
        dsimp only [coord, sigma]
        ring]
    change Tendsto ((fun s : ℂ ↦ (s - sigma) * logDeriv riemannZeta s) ∘ coord)
      (nhdsWithin alpha ({alpha}ᶜ))
      (nhds ((analyticOrderAt xi sigma).toNat : ℂ))
    exact hbase
  have hweight : Tendsto
      (fun z : ℂ ↦ xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ))
      (nhdsWithin alpha ({alpha}ᶜ))
      (nhds (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a alpha ^ (2 : ℕ))) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      ((xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd L A c a
        alpha (mem_univ alpha)).continuousAt.tendsto)
  have hmul := hweight.mul hprime
  convert hmul using 1
  · funext z
    rw [xiPhysicalThetaAbelEnergyPrimeWeightedSource]
    ring
  · dsimp only [sigma]
    rw [mul_comm]

/-- Every centered upper-half-strip point has cofinally many exact natural apertures at which the
physical two-edge weight is nonzero (indeed nonreal). -/
theorem xiPhysicalThetaAbelEnergyTwoEdgeTransform_logMesh_cofinally_nonreal_at_centeredUpperStrip
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {alpha : ℂ} (hare : 0 < alpha.re)
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2) alpha).im ≠ 0 := by
  let w : ℂ := I * alpha
  have hwre : w.re < 0 := by
    dsimp only [w]
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub]
    linarith
  have hwim : 0 < w.im := by
    dsimp only [w]
    simp only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add]
    exact hare
  have hnegwre : (-w).re = alpha.im := by
    simp [w, Complex.mul_re]
  have hQ : xiPhysicalThetaAbelEntireModeAmplitude L A c (-w) ≠ 0 := by
    apply xiPhysicalThetaAbelEntireModeAmplitude_ne_zero_of_openStrip hL hA hc
    · rw [hnegwre]
      linarith
    · rw [hnegwre]
      exact haimhalf
    · rw [hnegwre]
      exact ne_of_gt haim
  intro N
  obtain ⟨n, hnN, hnim⟩ :=
    twoEdgeExponentialMode_logMesh_cofinally_nonreal hwre hwim hQ N
  refine ⟨n, hnN, ?_⟩
  rw [xiPhysicalThetaAbelEnergyTwoEdgeTransform_eq_twoEdgeExponentialMode]
  exact hnim

/-- **Physical direct-prime pole escape.** A centered upper-half-strip Xi zero selects cofinally
many exact natural apertures. At each selected aperture, the actual physical square times the
direct infinite-prime source has real part below every level in every neighborhood of the zero. -/
theorem exists_logMesh_physicalPrimeWeightedSource_cofinally_unboundedBelow_near_of_xiZero
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    {alpha : ℂ} (hare : 0 < alpha.re)
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2)
    (haXi : XiC alpha = 0) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ r : ℝ, 0 < r → ∀ B : ℝ, ∃ z : ℂ,
        0 < z.re ∧ 0 < z.im ∧ z.im < 1 / 2 ∧ XiC z ≠ 0 ∧
        dist z alpha < r ∧
        (xiPhysicalThetaAbelEnergyPrimeWeightedSource
          L A c (Real.log n / 2) z).re < B := by
  intro N
  obtain ⟨n, hnN, hTim⟩ :=
    xiPhysicalThetaAbelEnergyTwoEdgeTransform_logMesh_cofinally_nonreal_at_centeredUpperStrip
      hL hA hc hare haim haimhalf N
  refine ⟨n, hnN, ?_⟩
  let a : ℝ := Real.log n / 2
  let sigma : ℂ := 1 / 2 + alpha * I
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  let Talpha : ℂ := xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a alpha
  let C : ℂ := (m : ℂ) * Talpha ^ (2 : ℕ)
  let f : ℂ → ℂ := xiPhysicalThetaAbelEnergyPrimeWeightedSource L A c a
  have hTalphaNe : Talpha ≠ 0 := by
    intro hzero
    apply hTim
    simp only [a, Talpha, hzero, zero_im]
  have hsigmaZero : xi sigma = 0 := by
    simpa only [XiC, sigma] using haXi
  have hmPos : 0 < m :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hsigmaZero)
  have hmCNe : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmPos)
  have hC : C ≠ 0 :=
    mul_ne_zero hmCNe (pow_ne_zero 2 hTalphaNe)
  have hres : Tendsto (fun z : ℂ ↦ (z - alpha) * f z)
      (nhdsWithin alpha ({alpha}ᶜ)) (nhds C) := by
    simpa only [f, C, Talpha, m, sigma, a] using
      (tendsto_xiPhysicalThetaAbelEnergyPrimeWeightedSource_normalizedResidue
        L A c a haim haimhalf)
  intro r hr B
  let U : Set ℂ :=
    ((ball alpha r ∩ {z : ℂ | 0 < z.re}) ∩ {z : ℂ | 0 < z.im}) ∩
      {z : ℂ | z.im < 1 / 2}
  have hballNh : ball alpha r ∈ nhds alpha :=
    isOpen_ball.mem_nhds (mem_ball_self hr)
  have hreNh : {z : ℂ | 0 < z.re} ∈ nhds alpha :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hare
  have himNh : {z : ℂ | 0 < z.im} ∈ nhds alpha :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds haim
  have himHalfNh : {z : ℂ | z.im < 1 / 2} ∈ nhds alpha :=
    (isOpen_lt Complex.continuous_im continuous_const).mem_nhds haimhalf
  have hU : U ∈ nhds alpha := by
    exact inter_mem (inter_mem (inter_mem hballNh hreNh) himNh) himHalfNh
  obtain ⟨z, _hzNe, hfNe, hzU, hzLt⟩ :=
    exists_realPart_lt_in_nhds_of_punctured_residue hC hres hU B
  have hzBall : z ∈ ball alpha r := hzU.1.1.1
  have hzRe : 0 < z.re := hzU.1.1.2
  have hzIm : 0 < z.im := hzU.1.2
  have hzImHalf : z.im < 1 / 2 := hzU.2
  have hzXi : XiC z ≠ 0 := by
    intro hXiZero
    let s : ℂ := 1 / 2 + z * I
    have hsRe : s.re = 1 / 2 - z.im := by
      simp [s, Complex.mul_re, sub_eq_add_neg]
    have hsPos : 0 < s.re := by rw [hsRe]; linarith
    have hsLt : s.re < 1 := by rw [hsRe]; linarith
    have hsNeOne : s ≠ 1 := by
      intro hsOne
      have hreOne := congrArg Complex.re hsOne
      rw [one_re, hsRe] at hreOne
      linarith
    have hzetaZero : riemannZeta s = 0 :=
      (xi_eq_zero_iff hsPos hsNeOne).mp (by
        simpa only [XiC, s] using hXiZero)
    apply hfNe
    dsimp only [f]
    rw [xiPhysicalThetaAbelEnergyPrimeWeightedSource]
    change xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c a z ^ (2 : ℕ) *
      (-I * infinitePrimeFlux s) = 0
    simp [infinitePrimeFlux, logDeriv_apply, hzetaZero]
  exact ⟨z, hzRe, hzIm, hzImHalf, hzXi,
    by simpa only [mem_ball] using hzBall, by simpa only [f, a] using hzLt⟩

/-- Pointwise local lower boundedness of every exact natural-aperture physical direct-prime
integrand throughout the centered upper open half-strip. -/
def XiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow
    (L A c : ℝ) : Prop :=
  ∀ n : ℕ, ∀ alpha : ℂ, 0 < alpha.re → 0 < alpha.im → alpha.im < 1 / 2 →
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ z : ℂ, dist z alpha < r →
      B ≤ (xiPhysicalThetaAbelEnergyPrimeWeightedSource
        L A c (Real.log n / 2) z).re

/-- RH makes every exact natural-aperture direct-prime integrand locally bounded below. -/
theorem xiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow_of_riemannHypothesis
    (L A c : ℝ) (hRH : RiemannHypothesis) :
    XiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow L A c := by
  intro n alpha _hare haim haimhalf
  let s : ℂ := 1 / 2 + alpha * I
  have hsRe : s.re = 1 / 2 - alpha.im := by
    simp [s, Complex.mul_re, sub_eq_add_neg]
  have hsPos : 0 < s.re := by rw [hsRe]; linarith
  have hsLt : s.re < 1 := by rw [hsRe]; linarith
  have hsNeOne : s ≠ 1 := by
    intro hsOne
    have hreOne := congrArg Complex.re hsOne
    rw [one_re, hsRe] at hreOne
    linarith
  have hXi : XiC alpha ≠ 0 :=
    XiC_ne_zero_upperHalf_of_rh hRH (by
      simpa only [xiCenteredUpperHalfPlane, mem_setOf_eq] using haim)
  have hzeta : riemannZeta s ≠ 0 := by
    intro hzetaZero
    apply hXi
    rw [XiC]
    exact (xi_eq_zero_iff hsPos hsNeOne).mpr hzetaZero
  have hzetaAn : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s hsNeOne
  have hflux : ContinuousAt infinitePrimeFlux s := by
    rw [show infinitePrimeFlux = fun w : ℂ ↦
        -(deriv riemannZeta w / riemannZeta w) by
      funext w
      rw [infinitePrimeFlux, logDeriv_apply]]
    exact (hzetaAn.deriv.continuousAt.div hzetaAn.continuousAt hzeta).neg
  have hcoord : ContinuousAt (fun z : ℂ ↦ 1 / 2 + z * I) alpha := by
    fun_prop
  change ContinuousAt infinitePrimeFlux (1 / 2 + alpha * I) at hflux
  have hweight : ContinuousAt
      (fun z : ℂ ↦ xiPhysicalThetaAbelEnergyTwoEdgeTransform
        L A c (Real.log n / 2) z ^ (2 : ℕ)) alpha :=
    (xiPhysicalThetaAbelEnergyTwoEdgeTransform_sq_analyticOnNhd
      L A c (Real.log n / 2) alpha (mem_univ alpha)).continuousAt
  have hfluxCoord : ContinuousAt
      (fun z : ℂ ↦ infinitePrimeFlux (1 / 2 + z * I)) alpha := by
    exact ContinuousAt.comp (x := alpha)
      (f := fun z : ℂ ↦ 1 / 2 + z * I) (g := infinitePrimeFlux) hflux hcoord
  have hsource : ContinuousAt
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource
        L A c (Real.log n / 2)) alpha := by
    change ContinuousAt (fun z : ℂ ↦
      xiPhysicalThetaAbelEnergyTwoEdgeTransform L A c (Real.log n / 2) z ^ (2 : ℕ) *
        (-I * infinitePrimeFlux (1 / 2 + z * I))) alpha
    exact hweight.mul (continuousAt_const.mul hfluxCoord)
  have hsourceRe : Tendsto (fun z : ℂ ↦
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource
        L A c (Real.log n / 2) z).re)
      (nhds alpha)
      (nhds (xiPhysicalThetaAbelEnergyPrimeWeightedSource
        L A c (Real.log n / 2) alpha).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hsource.tendsto
  let B : ℝ :=
    (xiPhysicalThetaAbelEnergyPrimeWeightedSource
      L A c (Real.log n / 2) alpha).re - 1
  have hB : B <
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource
        L A c (Real.log n / 2) alpha).re := by
    dsimp only [B]
    linarith
  have hev : {z : ℂ | B <
      (xiPhysicalThetaAbelEnergyPrimeWeightedSource
        L A c (Real.log n / 2) z).re} ∈ nhds alpha :=
    hsourceRe.eventually (eventually_gt_nhds hB)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r, hr, B, ?_⟩
  intro z hz
  exact (hball (by simpa only [mem_ball] using hz)).le

/-- Local lower boundedness of every exact natural-aperture physical direct-prime integrand
excludes every off-line Xi zero. -/
theorem riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hlocal : XiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow L A c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hRH
  let alpha : ℂ := (starRingEnd ℂ) (xiSpectralPoint q.1.1)
  have hare : 0 < alpha.re := by
    simpa only [alpha, Complex.conj_re, xiRightCenteredZero, mul_im, I_re, zero_mul,
      I_im, one_mul, zero_add] using q.2
  have haim : 0 < alpha.im := by
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using q.1.2
  have haimhalf : alpha.im < 1 / 2 := by
    have h := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using h
  have haXi : XiC alpha = 0 := by
    dsimp only [alpha]
    rw [XiC_conj, XiC_xiSpectralPoint_eq_zero, map_zero]
  obtain ⟨n, _hn, hescape⟩ :=
    exists_logMesh_physicalPrimeWeightedSource_cofinally_unboundedBelow_near_of_xiZero
      hL hA hc hare haim haimhalf haXi 0
  obtain ⟨r, hr, B, hB⟩ := hlocal n alpha hare haim haimhalf
  obtain ⟨z, _hzRe, _hzIm, _hzImHalf, _hzXi, hzDist, hzLt⟩ :=
    hescape r hr B
  exact (not_lt_of_ge (hB z hzDist)) hzLt

/-- Exact physical direct-prime local boundedness criterion for RH, on the natural logarithmic
aperture mesh. -/
theorem xiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow L A c ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow
      hL hA hc,
    xiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow_of_riemannHypothesis L A c⟩

/-- Closed unit-window physical direct-prime local criterion. -/
theorem unitPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow 1 1 1 ↔
      RiemannHypothesis :=
  xiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow_iff_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

/-- Eventual-in-aperture local lower boundedness of the actual physical direct-prime integrand. -/
def XiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow
    (L A c : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ alpha : ℂ,
    0 < alpha.re → 0 < alpha.im → alpha.im < 1 / 2 →
      ∃ r : ℝ, 0 < r ∧ ∃ B : ℝ, ∀ z : ℂ, dist z alpha < r →
        B ≤ (xiPhysicalThetaAbelEnergyPrimeWeightedSource
          L A c (Real.log n / 2) z).re

theorem xiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow_of_riemannHypothesis
    (L A c : ℝ) (hRH : RiemannHypothesis) :
    XiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow L A c := by
  refine ⟨0, ?_⟩
  intro n _hn
  exact xiPhysicalThetaAbelEnergyPrimeLogMeshLocallyBoundedBelow_of_riemannHypothesis
    L A c hRH n

/-- Cofinal aperture escape makes eventual local boundedness sufficient for RH. -/
theorem riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c)
    (hlocal : XiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow L A c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_of_not_riemannHypothesis hRH
  let alpha : ℂ := (starRingEnd ℂ) (xiSpectralPoint q.1.1)
  have hare : 0 < alpha.re := by
    simpa only [alpha, Complex.conj_re, xiRightCenteredZero, mul_im, I_re, zero_mul,
      I_im, one_mul, zero_add] using q.2
  have haim : 0 < alpha.im := by
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using q.1.2
  have haimhalf : alpha.im < 1 / 2 := by
    have h := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
    simpa only [alpha, Complex.conj_im, xiRightCenteredZero, mul_re, I_re, zero_mul,
      I_im, one_mul, zero_sub] using h
  have haXi : XiC alpha = 0 := by
    dsimp only [alpha]
    rw [XiC_conj, XiC_xiSpectralPoint_eq_zero, map_zero]
  obtain ⟨N, hN⟩ := hlocal
  obtain ⟨n, hn, hescape⟩ :=
    exists_logMesh_physicalPrimeWeightedSource_cofinally_unboundedBelow_near_of_xiZero
      hL hA hc hare haim haimhalf haXi N
  obtain ⟨r, hr, B, hB⟩ := hN n hn alpha hare haim haimhalf
  obtain ⟨z, _hzRe, _hzIm, _hzImHalf, _hzXi, hzDist, hzLt⟩ :=
    hescape r hr B
  exact (not_lt_of_ge (hB z hzDist)) hzLt

/-- **Exact cofinal natural-aperture direct-prime criterion.** RH is equivalent to eventual local
lower boundedness of the actual physical square times the literal infinite-prime flux. -/
theorem xiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow_iff_riemannHypothesis
    {L A c : ℝ} (hL : 0 < L) (hA : 0 < A) (hc : 0 < c) :
    XiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow L A c ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow
      hL hA hc,
    xiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow_of_riemannHypothesis
      L A c⟩

/-- Closed unit-window cofinal physical direct-prime criterion. -/
theorem unitPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow_iff_riemannHypothesis :
    XiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow 1 1 1 ↔
      RiemannHypothesis :=
  xiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow_iff_riemannHypothesis
    (by norm_num) (by norm_num) (by norm_num)

end

end RHTower
