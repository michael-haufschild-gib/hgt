import GaloisForLFunctions.RHTower.ThetaWignerCenterMix
import GaloisForLFunctions.RHTower.ThetaWignerEisensteinSymbol
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberTranslation
import GaloisForLFunctions.RHTower.HedenmalmGaussianHankelRH
import GaloisForLFunctions.RHTower.HedenmalmAutocorrelationPath

/-!
# Exact product-fibre normal form for the theta Wigner current

This file recenters each ordered pair of actual completed theta-source atoms before any sign
estimate.  The recentering separates the product scale `n * m` from the divisor-ratio phase
`log n - log m`.  Consequently a complete fixed-product packet factors into one universal radial
transform and one finite divisor trace.  No Riemann-hypothesis or positivity premise is used.
-/

open Complex Real MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Common radial scale of an ordered source pair after logarithmic recentering. -/
def thetaCuspWignerAtomScale (n m : ℕ) (u : ℝ) : ℝ :=
  2 * Real.pi * n * m * Real.exp (2 * u)

/-- Ratio-centered difference coordinate of an ordered source pair. -/
def thetaCuspWignerAtomCenteredCoordinate (n m : ℕ) (t : ℝ) : ℝ :=
  t + (Real.log n - Real.log m) / 2

/-- Universal radial profile left after product/ratio separation of two actual source atoms. -/
def thetaCuspWignerRadialProfile (c v : ℝ) : ℝ :=
  (c ^ 4 - 6 * c ^ 3 * Real.cosh (2 * v) + 9 * c ^ 2) *
    Real.exp (-c * Real.cosh (2 * v))

/-- **Actual atom-pair product/ratio separation.**  The source-pair amplitude depends on the
indices through their product in `c`; their ratio appears only as a translation of `t`. -/
theorem thetaCuspSourceTerm_mul_reflect_eq_wignerRadialProfile
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (u t : ℝ) :
    thetaCuspSourceTerm (u + t) n * thetaCuspSourceTerm (u - t) m =
      Real.exp u *
        thetaCuspWignerRadialProfile
          (thetaCuspWignerAtomScale n m u)
          (thetaCuspWignerAtomCenteredCoordinate n m t) := by
  let c : ℝ := thetaCuspWignerAtomScale n m u
  let v : ℝ := thetaCuspWignerAtomCenteredCoordinate n m t
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hevPlus :
      Real.exp (2 * v) =
        Real.exp (2 * t) * (n : ℝ) / (m : ℝ) := by
    dsimp only [v, thetaCuspWignerAtomCenteredCoordinate]
    rw [show 2 * (t + (Real.log n - Real.log m) / 2) =
        2 * t + Real.log n - Real.log m by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hnR, Real.exp_log hmR]
  have hevMinus :
      Real.exp (-2 * v) =
        Real.exp (-2 * t) * (m : ℝ) / (n : ℝ) := by
    dsimp only [v, thetaCuspWignerAtomCenteredCoordinate]
    rw [show -2 * (t + (Real.log n - Real.log m) / 2) =
        -2 * t + Real.log m - Real.log n by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hnR, Real.exp_log hmR]
  have heu : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [show 2 * u = u + u by ring, Real.exp_add]
  have het : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
  have hnegt : Real.exp (-2 * t) =
      1 / (Real.exp t * Real.exp t) := by
    rw [show -2 * t = -(t + t) by ring, Real.exp_neg, Real.exp_add]
    ring
  have hplus :
      2 * Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ 2 =
        c * Real.exp (2 * v) := by
    change 2 * Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ 2 =
      (2 * Real.pi * n * m * Real.exp (2 * u)) * Real.exp (2 * v)
    rw [Real.exp_add, heu, hevPlus, het]
    field_simp [hmR.ne']
  have hminus :
      2 * Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ 2 =
        c * Real.exp (-2 * v) := by
    change 2 * Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ 2 =
      (2 * Real.pi * n * m * Real.exp (2 * u)) * Real.exp (-2 * v)
    rw [Real.exp_sub, heu, hevMinus, hnegt]
    have het0 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    field_simp [hnR.ne', hmR.ne', het0]
  have hseed (x : ℝ) :
      thetaCuspSeed x =
        ((2 * Real.pi * x ^ 2) ^ 2 - 3 * (2 * Real.pi * x ^ 2)) *
          Real.exp (-Real.pi * x ^ 2) := by
    unfold thetaCuspSeed
    ring
  rw [thetaCuspSourceTerm, thetaCuspSourceTerm, hseed, hseed]
  have hhalf :
      Real.exp ((u + t) / 2) * Real.exp ((u - t) / 2) =
        Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hgauss :
      Real.exp (-Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ 2) *
          Real.exp (-Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ 2) =
        Real.exp (-c * Real.cosh (2 * v)) := by
    rw [← Real.exp_add]
    congr 1
    have hp : Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ 2 =
        (c * Real.exp (2 * v)) / 2 := by linarith [hplus]
    have hm' : Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ 2 =
        (c * Real.exp (-2 * v)) / 2 := by linarith [hminus]
    rw [Real.cosh_eq]
    rw [show -(2 * v) = -2 * v by ring]
    linarith
  have hpolyPlus :
      (c * Real.exp (2 * v)) ^ 2 - 3 * (c * Real.exp (2 * v)) =
        c ^ 2 * Real.exp (4 * v) - 3 * c * Real.exp (2 * v) := by
    rw [show Real.exp (4 * v) =
      Real.exp (2 * v) * Real.exp (2 * v) by
        rw [show 4 * v = 2 * v + 2 * v by ring, Real.exp_add]]
    ring
  have hpolyMinus :
      (c * Real.exp (-2 * v)) ^ 2 - 3 * (c * Real.exp (-2 * v)) =
        c ^ 2 * Real.exp (-4 * v) - 3 * c * Real.exp (-2 * v) := by
    rw [show Real.exp (-4 * v) =
      Real.exp (-2 * v) * Real.exp (-2 * v) by
        rw [show -4 * v = -2 * v + -2 * v by ring, Real.exp_add]]
    ring
  calc
    _ = (Real.exp ((u + t) / 2) * Real.exp ((u - t) / 2)) *
        (((c * Real.exp (2 * v)) ^ 2 -
            3 * (c * Real.exp (2 * v))) *
          ((c * Real.exp (-2 * v)) ^ 2 -
            3 * (c * Real.exp (-2 * v)))) *
        (Real.exp (-Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ 2) *
          Real.exp (-Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ 2)) := by
      rw [hplus, hminus]
      ring
    _ = Real.exp u *
        thetaCuspWignerRadialProfile c v := by
      rw [hhalf, hgauss, hpolyPlus, hpolyMinus]
      unfold thetaCuspWignerRadialProfile
      rw [thetaWignerAtomPair_polynomial c v]
      ring
    _ = _ := rfl

/-- Universal Fourier transform of the recentered radial atom-pair profile. -/
def thetaCuspWignerRadialTransform (c b : ℝ) : ℂ :=
  ∫ v : ℝ,
    (thetaCuspWignerRadialProfile c v : ℂ) *
      thetaWignerDifferencePhase b v

/-- Wigner contribution of one ordered pair of actual source atoms. -/
def thetaCuspSourcePairWigner (n m : ℕ) (u b : ℝ) : ℂ :=
  ∫ t : ℝ,
    (thetaCuspSourceTerm (u + t) n *
      thetaCuspSourceTerm (u - t) m : ℂ) *
        thetaWignerDifferencePhase b t

/-- The divisor-ratio phase carried by one ordered positive pair. -/
def thetaCuspWignerDivisorRatioPhase (n m : ℕ) (b : ℝ) : ℂ :=
  Complex.exp
    (-(((b * (Real.log n - Real.log m) : ℝ) : ℂ) * I))

/-- **Ordered-pair Wigner factorization.**  After translation, every ordered pair is a common
radial transform at product scale times its divisor-ratio phase. -/
theorem thetaCuspSourcePairWigner_eq_phase_mul_radial
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (u b : ℝ) :
    thetaCuspSourcePairWigner n m u b =
      (Real.exp u : ℂ) *
        thetaCuspWignerDivisorRatioPhase n m b *
          thetaCuspWignerRadialTransform
            (thetaCuspWignerAtomScale n m u) b := by
  let δ : ℝ := Real.log n - Real.log m
  let F : ℝ → ℂ := fun t =>
    (thetaCuspSourceTerm (u + t) n *
      thetaCuspSourceTerm (u - t) m : ℂ) *
        thetaWignerDifferencePhase b t
  have hshift :=
    MeasureTheory.integral_add_right_eq_self (μ := volume) F (-δ / 2)
  rw [thetaCuspSourcePairWigner]
  change (∫ t : ℝ, F t) = _
  rw [← hshift]
  rw [show (fun t : ℝ => F (t + -δ / 2)) =
      fun t =>
        ((Real.exp u : ℂ) *
          thetaCuspWignerDivisorRatioPhase n m b) *
            ((thetaCuspWignerRadialProfile
              (thetaCuspWignerAtomScale n m u) t : ℂ) *
                thetaWignerDifferencePhase b t) by
    funext t
    dsimp only [F]
    have hpair := congrArg (fun x : ℝ => (x : ℂ))
      (thetaCuspSourceTerm_mul_reflect_eq_wignerRadialProfile
        hn hm u (t + -δ / 2))
    simp only [Complex.ofReal_mul] at hpair
    rw [hpair]
    have hcenter :
        thetaCuspWignerAtomCenteredCoordinate n m (t + -δ / 2) = t := by
      dsimp only [thetaCuspWignerAtomCenteredCoordinate, δ]
      ring
    rw [hcenter]
    have hphase :
        thetaWignerDifferencePhase b (t + -δ / 2) =
          thetaCuspWignerDivisorRatioPhase n m b *
            thetaWignerDifferencePhase b t := by
      unfold thetaWignerDifferencePhase thetaCuspWignerDivisorRatioPhase
      rw [← Complex.exp_add]
      congr 1
      dsimp only [δ]
      simp only [Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_neg]
      norm_num
      ring
    rw [hphase]
    ring]
  rw [integral_const_mul]
  rfl

/-- The universal radial profile is even in its centered difference coordinate. -/
theorem thetaCuspWignerRadialProfile_neg (c v : ℝ) :
    thetaCuspWignerRadialProfile c (-v) =
      thetaCuspWignerRadialProfile c v := by
  simp [thetaCuspWignerRadialProfile]

/-- The recentered radial transform is real.  Complex transverse phases cancel by reflection in
the difference coordinate before the arithmetic divisor sum is considered. -/
theorem conj_thetaCuspWignerRadialTransform (c b : ℝ) :
    (starRingEnd ℂ) (thetaCuspWignerRadialTransform c b) =
      thetaCuspWignerRadialTransform c b := by
  let F : ℝ → ℂ := fun v =>
    (thetaCuspWignerRadialProfile c v : ℂ) *
      thetaWignerDifferencePhase b v
  change (starRingEnd ℂ) (∫ v : ℝ, F v) = ∫ v : ℝ, F v
  rw [← integral_conj]
  rw [← MeasureTheory.integral_neg_eq_self
    (fun v : ℝ => (starRingEnd ℂ) (F v)) volume]
  apply integral_congr_ae
  filter_upwards with v
  dsimp only [F]
  rw [map_mul, Complex.conj_ofReal,
    thetaCuspWignerRadialProfile_neg]
  unfold thetaWignerDifferencePhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem thetaCuspWignerRadialTransform_im_zero (c b : ℝ) :
    (thetaCuspWignerRadialTransform c b).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_thetaCuspWignerRadialTransform c b)

/-- Finite divisor-character trace on one positive product fibre. -/
def thetaCuspWignerProductFiberDivisorTrace (k : ℕ) (b : ℝ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspWignerDivisorRatioPhase (q.1 + 1) (q.2 + 1) b

/-- Divisor reflection conjugates the ratio phase. -/
theorem conj_thetaCuspWignerDivisorRatioPhase
    (n m : ℕ) (b : ℝ) :
    (starRingEnd ℂ) (thetaCuspWignerDivisorRatioPhase n m b) =
      thetaCuspWignerDivisorRatioPhase m n b := by
  unfold thetaCuspWignerDivisorRatioPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The complete divisor-character trace is real only after the full fixed-product packet is
summed. -/
theorem conj_thetaCuspWignerProductFiberDivisorTrace
    (k : ℕ) (b : ℝ) :
    (starRingEnd ℂ) (thetaCuspWignerProductFiberDivisorTrace k b) =
      thetaCuspWignerProductFiberDivisorTrace k b := by
  let s := thetaPositiveFactorPairs k
  have hswap :
      (∑ q ∈ s,
        thetaCuspWignerDivisorRatioPhase (q.2 + 1) (q.1 + 1) b) =
      ∑ q ∈ s,
        thetaCuspWignerDivisorRatioPhase (q.1 + 1) (q.2 + 1) b := by
    refine Finset.sum_bij' (fun q _ => q.swap) (fun q _ => q.swap)
      ?_ ?_ ?_ ?_ ?_
    · intro q hq
      exact thetaPositiveFactorPairs_swap_mem hq
    · intro q hq
      exact thetaPositiveFactorPairs_swap_mem hq
    · intro q _hq
      exact Prod.swap_swap q
    · intro q _hq
      exact Prod.swap_swap q
    · intro q _hq
      simp
  calc
    (starRingEnd ℂ) (thetaCuspWignerProductFiberDivisorTrace k b) =
        ∑ q ∈ thetaPositiveFactorPairs k,
          (starRingEnd ℂ)
            (thetaCuspWignerDivisorRatioPhase
              (q.1 + 1) (q.2 + 1) b) := by
      unfold thetaCuspWignerProductFiberDivisorTrace
      rw [map_sum]
    _ = ∑ q ∈ thetaPositiveFactorPairs k,
          thetaCuspWignerDivisorRatioPhase
            (q.2 + 1) (q.1 + 1) b := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact conj_thetaCuspWignerDivisorRatioPhase _ _ _
    _ = thetaCuspWignerProductFiberDivisorTrace k b := by
      unfold thetaCuspWignerProductFiberDivisorTrace
      simpa only [s] using hswap

theorem thetaCuspWignerProductFiberDivisorTrace_im_zero
    (k : ℕ) (b : ℝ) :
    (thetaCuspWignerProductFiberDivisorTrace k b).im = 0 :=
  Complex.conj_eq_iff_im.mp
    (conj_thetaCuspWignerProductFiberDivisorTrace k b)

/-- Complete ordered-pair Wigner packet on one positive product fibre. -/
def thetaCuspWignerProductFiber (k : ℕ) (u b : ℝ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspSourcePairWigner (q.1 + 1) (q.2 + 1) u b

/-- **Fixed-product divisor summation law.**  All transverse ratio phases are summed before any
sign estimate.  The result is one divisor trace times a radial transform depending only on `k`. -/
theorem thetaCuspWignerProductFiber_eq_divisorTrace_mul_radial
    (k : ℕ) (u b : ℝ) :
    thetaCuspWignerProductFiber k u b =
      (Real.exp u : ℂ) *
        thetaCuspWignerProductFiberDivisorTrace k b *
          thetaCuspWignerRadialTransform
            (2 * Real.pi * k * Real.exp (2 * u)) b := by
  unfold thetaCuspWignerProductFiber
  rw [show (∑ q ∈ thetaPositiveFactorPairs k,
      thetaCuspSourcePairWigner (q.1 + 1) (q.2 + 1) u b) =
      ∑ q ∈ thetaPositiveFactorPairs k,
        (Real.exp u : ℂ) *
          thetaCuspWignerDivisorRatioPhase (q.1 + 1) (q.2 + 1) b *
            thetaCuspWignerRadialTransform
              (2 * Real.pi * k * Real.exp (2 * u)) b by
    apply Finset.sum_congr rfl
    intro q hq
    have hprod : (q.1 + 1) * (q.2 + 1) = k := by
      have hmem :
          (q.1 < k ∧ q.2 < k) ∧ (q.1 + 1) * (q.2 + 1) = k := by
        simpa [thetaPositiveFactorPairs] using hq
      exact hmem.2
    have hprodR :
        ((q.1 + 1 : ℕ) : ℝ) * ((q.2 + 1 : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast hprod
    have hscale :
        thetaCuspWignerAtomScale (q.1 + 1) (q.2 + 1) u =
          2 * Real.pi * k * Real.exp (2 * u) := by
      unfold thetaCuspWignerAtomScale
      rw [show
        2 * Real.pi * ((q.1 + 1 : ℕ) : ℝ) *
            ((q.2 + 1 : ℕ) : ℝ) * Real.exp (2 * u) =
          2 * Real.pi *
            (((q.1 + 1 : ℕ) : ℝ) * ((q.2 + 1 : ℕ) : ℝ)) *
              Real.exp (2 * u) by ring,
        hprodR]
    rw [thetaCuspSourcePairWigner_eq_phase_mul_radial
      (Nat.succ_pos q.1) (Nat.succ_pos q.2), hscale]]
  unfold thetaCuspWignerProductFiberDivisorTrace
  rw [Finset.mul_sum, Finset.sum_mul]

/-- **Actual-current radial Wigner identity.**  The Hedenmalm current is twice the real radial
Wigner current.  This closes the normalization between the Fourier/autocorrelation definition and
the center-first product-fibre coordinate used above. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_two_mul_re_radialWigner
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg ha0]; linarith) b =
      2 * (∫ r : ℝ in Set.Ioi 0,
        (r * Real.sinh (a * r) : ℝ) *
          thetaWignerDistribution thetaCuspComplexSource (r / 2) b).re := by
  let ha : |a| < 1 := by
    rw [abs_of_nonneg ha0]
    linarith
  let C : ℝ → ℂ := fun t => (thetaCuspCenterMixedDensity a t : ℂ)
  let F : ℝ → ℂ := fun x =>
    Complex.exp (((-b * x : ℝ) : ℂ) * I) * C (x / 2)
  have hfourier :
      FourierTransform.fourier
          (thetaCuspHorizontalAutocorrelationTangent a ha)
          (b / (2 * Real.pi)) =
        ∫ x : ℝ, F x := by
    change FourierTransform.fourier
      (fun x : ℝ => thetaCuspHorizontalAutocorrelationTangent a ha x)
      (b / (2 * Real.pi)) = _
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    rw [thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity ha x]
    change Complex.exp
        (↑(-2 * Real.pi * x * (b / (2 * Real.pi))) * I) *
          C (x / 2) = F x
    dsimp only [F]
    congr 2
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  have hscale :
      (∫ x : ℝ, F x) =
        2 * ∫ t : ℝ,
          Complex.exp (((-2 * b * t : ℝ) : ℂ) * I) * C t := by
    have hs := MeasureTheory.Measure.integral_comp_mul_left F 2
    norm_num at hs
    have hcomp :
        (fun t : ℝ => F (2 * t)) =
          fun t =>
            Complex.exp (((-2 * b * t : ℝ) : ℂ) * I) * C t := by
      funext t
      dsimp only [F]
      congr 2 <;> ring
    rw [hcomp] at hs
    rw [hs]
    ring
  have hphase :
      (∫ t : ℝ,
          Complex.exp (((-2 * b * t : ℝ) : ℂ) * I) * C t) =
        ∫ t : ℝ,
          C t * thetaWignerDifferencePhase b t := by
    let G : ℝ → ℂ := fun t =>
      C t * thetaWignerDifferencePhase b t
    have href := MeasureTheory.integral_neg_eq_self G volume
    calc
      (∫ t : ℝ,
          Complex.exp (((-2 * b * t : ℝ) : ℂ) * I) * C t) =
          ∫ t : ℝ, G (-t) := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [G, C]
        rw [thetaCuspCenterMixedDensity_even]
        unfold thetaWignerDifferencePhase
        ring_nf
      _ = ∫ t : ℝ, G t := href
      _ = _ := rfl
  have hWigner :=
    integral_thetaWignerCenterMixedDensity_mul_phase_thetaCusp
      (a := a) (b := b) ha0 haHalf
  rw [thetaCuspCenterMixedFourierCurrent]
  change
    (FourierTransform.fourier
      (thetaCuspHorizontalAutocorrelationTangent a ha)
      (b / (2 * Real.pi))).re = _
  rw [hfourier, hscale, hphase]
  have hcenterIntegral :
      (∫ t : ℝ, C t * thetaWignerDifferencePhase b t) =
        ∫ t : ℝ,
          thetaWignerCenterMixedDensity thetaCuspComplexSource a t *
            thetaWignerDifferencePhase b t := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [C]
    rw [thetaWignerCenterMixedDensity_thetaCusp_eq_ofReal]
  rw [hcenterIntegral, hWigner]
  norm_num [Complex.mul_re]

end

end RHTower
