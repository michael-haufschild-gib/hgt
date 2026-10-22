import GaloisForLFunctions.RHTower.ThetaWignerCenterMix
import GaloisForLFunctions.RHTower.ThetaWignerEisensteinSymbol
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberTranslation
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelRH
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmAutocorrelationPath
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspKernelLogConcavity

/-!
# Exact product-fibre normal form for the theta Wigner current

This file recenters each ordered pair of actual completed theta-source atoms before any sign
estimate.  The recentering separates the product scale `n * m` from the divisor-ratio phase
`log n - log m`.  Consequently a complete fixed-product packet factors into one universal radial
transform and one finite divisor trace.  No Riemann-hypothesis or positivity premise is used.
-/

open Complex Real MeasureTheory Set
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
  (c ^ (4 : ℕ) - 6 * c ^ (3 : ℕ) * Real.cosh (2 * v) + 9 * c ^ (2 : ℕ)) *
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
      2 * Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ (2 : ℕ) =
        c * Real.exp (2 * v) := by
    change 2 * Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ (2 : ℕ) =
      (2 * Real.pi * n * m * Real.exp (2 * u)) * Real.exp (2 * v)
    rw [Real.exp_add, heu, hevPlus, het]
    field_simp [hmR.ne']
  have hminus :
      2 * Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ (2 : ℕ) =
        c * Real.exp (-2 * v) := by
    change 2 * Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ (2 : ℕ) =
      (2 * Real.pi * n * m * Real.exp (2 * u)) * Real.exp (-2 * v)
    rw [Real.exp_sub, heu, hevMinus, hnegt]
    have het0 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    field_simp [hnR.ne', hmR.ne', het0]
  have hseed (x : ℝ) :
      thetaCuspSeed x =
        ((2 * Real.pi * x ^ (2 : ℕ)) ^ (2 : ℕ) - 3 * (2 * Real.pi * x ^ (2 : ℕ))) *
          Real.exp (-Real.pi * x ^ (2 : ℕ)) := by
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
      Real.exp (-Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ (2 : ℕ)) *
          Real.exp (-Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ (2 : ℕ)) =
        Real.exp (-c * Real.cosh (2 * v)) := by
    rw [← Real.exp_add]
    congr 1
    have hp : Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ (2 : ℕ) =
        (c * Real.exp (2 * v)) / 2 := by linarith [hplus]
    have hm' : Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ (2 : ℕ) =
        (c * Real.exp (-2 * v)) / 2 := by linarith [hminus]
    rw [Real.cosh_eq]
    rw [show -(2 * v) = -2 * v by ring]
    linarith
  have hpolyPlus :
      (c * Real.exp (2 * v)) ^ (2 : ℕ) - 3 * (c * Real.exp (2 * v)) =
        c ^ (2 : ℕ) * Real.exp (4 * v) - 3 * c * Real.exp (2 * v) := by
    rw [show Real.exp (4 * v) =
      Real.exp (2 * v) * Real.exp (2 * v) by
        rw [show 4 * v = 2 * v + 2 * v by ring, Real.exp_add]]
    ring
  have hpolyMinus :
      (c * Real.exp (-2 * v)) ^ (2 : ℕ) - 3 * (c * Real.exp (-2 * v)) =
        c ^ (2 : ℕ) * Real.exp (-4 * v) - 3 * c * Real.exp (-2 * v) := by
    rw [show Real.exp (-4 * v) =
      Real.exp (-2 * v) * Real.exp (-2 * v) by
        rw [show -4 * v = -2 * v + -2 * v by ring, Real.exp_add]]
    ring
  calc
    _ = (Real.exp ((u + t) / 2) * Real.exp ((u - t) / 2)) *
        (((c * Real.exp (2 * v)) ^ (2 : ℕ) -
            3 * (c * Real.exp (2 * v))) *
          ((c * Real.exp (-2 * v)) ^ (2 : ℕ) -
            3 * (c * Real.exp (-2 * v)))) *
        (Real.exp (-Real.pi * ((n : ℝ) * Real.exp (u + t)) ^ (2 : ℕ)) *
          Real.exp (-Real.pi * ((m : ℝ) * Real.exp (u - t)) ^ (2 : ℕ))) := by
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

/-! ## Cofinally completed positive shells

The raw atom `thetaCuspSourceTerm x n` is not a positive shell when `x < 0`; modular reflection
only repairs its infinite sum.  For product-fibre summation the canonical absolutely convergent
decomposition is instead obtained by reflecting each positive-half-line shell.  This is the
decomposition already implicit in `thetaCuspShellEvenPhaseValue`.
-/

/-- Positive completed shell, indexed from zero: shell `n` is source atom `n + 1` reflected
evenly from the positive logarithmic half-line. -/
def thetaCuspCompletedPositiveShell (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspSourceTerm |x| (n + 1)

theorem thetaCuspCompletedPositiveShell_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ thetaCuspCompletedPositiveShell n x := by
  by_cases hx : x = 0
  · subst x
    unfold thetaCuspCompletedPositiveShell
    simp only [abs_zero]
    rw [thetaCuspSourceTerm]
    apply mul_nonneg (Real.exp_pos _).le
    apply (thetaCuspSeed_pos ?_).le
    norm_num [Nat.cast_add, Nat.cast_one]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hn2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (2 : ℕ) := by nlinarith
    have hmul :
        2 * Real.pi * 1 ≤
          2 * Real.pi * (((n : ℝ) + 1) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hn2 (by positivity)
    exact (show 3 < 2 * Real.pi by
      nlinarith [Real.pi_gt_three]).trans_le (by simpa using hmul)
  · exact thetaCuspSourceTerm_nonneg_of_pos
      (abs_pos.mpr hx) (n + 1)

theorem summable_thetaCuspCompletedPositiveShell (x : ℝ) :
    Summable (fun n : ℕ => thetaCuspCompletedPositiveShell n x) := by
  simpa only [thetaCuspCompletedPositiveShell] using
    (summable_nat_add_iff 1).mpr (summable_thetaCuspSourceTerm |x|)

/-- The reflected positive shells reassemble the actual source pointwise and absolutely. -/
theorem tsum_thetaCuspCompletedPositiveShell_eq_fullSource (x : ℝ) :
    (∑' n : ℕ, thetaCuspCompletedPositiveShell n x) =
      thetaCuspFullSource x := by
  have hs := summable_thetaCuspSourceTerm |x|
  have hsplit := hs.sum_add_tsum_nat_add 1
  have hzero : thetaCuspSourceTerm |x| 0 = 0 := by
    simp [thetaCuspSourceTerm, thetaCuspSeed]
  have htail :
      (∑' n : ℕ, thetaCuspSourceTerm |x| (n + 1)) =
        thetaCuspFullSource |x| := by
    rw [thetaCuspFullSource, ← hsplit]
    simp [hzero]
  rw [show (∑' n : ℕ, thetaCuspCompletedPositiveShell n x) =
      ∑' n : ℕ, thetaCuspSourceTerm |x| (n + 1) by rfl,
    htail]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), thetaCuspFullSource_neg]

/-- Ordered Wigner contribution of two cofinally completed positive shells. -/
def thetaCuspCompletedShellPairWigner
    (q : ℕ × ℕ) (u b : ℝ) : ℂ :=
  ∫ t : ℝ,
    (thetaCuspCompletedPositiveShell q.1 (u + t) *
      thetaCuspCompletedPositiveShell q.2 (u - t) : ℂ) *
        thetaWignerDifferencePhase b t

/-- Full fixed-product packet of completed positive shells. -/
def thetaCuspCompletedWignerProductFiber
    (k : ℕ) (u b : ℝ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspCompletedShellPairWigner q u b

private theorem abs_add_add_abs_sub_ge_two_abs_right (u t : ℝ) :
    2 * |t| ≤ |u + t| + |u - t| := by
  calc
    2 * |t| = |(u + t) - (u - t)| := by
      rw [show (u + t) - (u - t) = 2 * t by ring, abs_mul]
      norm_num
    _ ≤ |u + t| + |u - t| := abs_sub _ _

private theorem integrable_thetaCuspFullSource_reflectedProduct
    (u b : ℝ) :
    Integrable (fun t : ℝ =>
      (thetaCuspFullSource (u + t) *
        thetaCuspFullSource (u - t) : ℂ) *
          thetaWignerDifferencePhase b t) := by
  let C : ℝ := thetaCuspDerivativeExpConstant 0
  have hC : 0 ≤ C := thetaCuspDerivativeExpConstant_nonneg 0
  have hmajor :
      Integrable (fun t : ℝ => C ^ (2 : ℕ) * Real.exp (-|t|)) :=
    integrable_exp_neg_abs.const_mul _
  apply hmajor.mono
  · have hsource : Continuous thetaCuspFullSource :=
      contDiff_thetaCuspFullSource.continuous
    exact ((Complex.continuous_ofReal.comp
        (hsource.comp (continuous_const.add continuous_id))).mul
      (Complex.continuous_ofReal.comp
        (hsource.comp (continuous_const.sub continuous_id)))).mul
      (by
        unfold thetaWignerDifferencePhase
        fun_prop) |>.aestronglyMeasurable
  · filter_upwards with t
    have hplus := abs_thetaCuspFullSource_le_exp_neg_abs (u + t)
    have hminus := abs_thetaCuspFullSource_le_exp_neg_abs (u - t)
    have hgeom := abs_add_add_abs_sub_ge_two_abs_right u t
    have hexp :
        Real.exp (-|u + t|) * Real.exp (-|u - t|) ≤
          Real.exp (-|t|) := by
      rw [← Real.exp_add]
      apply (Real.exp_le_exp.mpr ?_)
      linarith [abs_nonneg t]
    have hbound :
        ‖(thetaCuspFullSource (u + t) *
            thetaCuspFullSource (u - t) : ℂ) *
          thetaWignerDifferencePhase b t‖ ≤
            C ^ (2 : ℕ) * Real.exp (-|t|) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        thetaWignerDifferencePhase, Complex.norm_exp]
      simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
        sub_self, Real.exp_zero, mul_one]
      calc
        |thetaCuspFullSource (u + t)| *
            |thetaCuspFullSource (u - t)| ≤
          (C * Real.exp (-|u + t|)) *
            (C * Real.exp (-|u - t|)) := by gcongr
        _ = C ^ (2 : ℕ) *
            (Real.exp (-|u + t|) * Real.exp (-|u - t|)) := by ring
        _ ≤ C ^ (2 : ℕ) * Real.exp (-|t|) := by gcongr
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg C) (Real.exp_pos _).le)] using hbound

/-- The completed-shell Wigner expansion is absolutely summable before product-fibre
regrouping. -/
theorem hasSum_thetaCuspCompletedShellPairWigner
    (u b : ℝ) :
    HasSum (fun q : ℕ × ℕ =>
      thetaCuspCompletedShellPairWigner q u b)
      (thetaWignerDistribution thetaCuspComplexSource u b) := by
  let F : (ℕ × ℕ) → ℝ → ℂ := fun q t =>
    (thetaCuspCompletedPositiveShell q.1 (u + t) *
      thetaCuspCompletedPositiveShell q.2 (u - t) : ℂ) *
        thetaWignerDifferencePhase b t
  have hFmeas : ∀ q, AEStronglyMeasurable (F q) volume := by
    intro q
    exact ((by
      dsimp only [F, thetaCuspCompletedPositiveShell]
      unfold thetaCuspSourceTerm thetaCuspSeed thetaWignerDifferencePhase
      fun_prop : Continuous (F q))).aestronglyMeasurable
  have hBoundSummable :
      ∀ᵐ t ∂volume, Summable (fun q : ℕ × ℕ => ‖F q t‖) := by
    filter_upwards with t
    let A : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (u + t)
    let B : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (u - t)
    have hA : Summable A := summable_thetaCuspCompletedPositiveShell _
    have hB : Summable B := summable_thetaCuspCompletedPositiveShell _
    have hpair : Summable (fun q : ℕ × ℕ => A q.1 * B q.2) :=
      summable_mul_of_summable_norm hA.norm hB.norm
    apply hpair.congr
    intro q
    dsimp only [F, A, B]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      thetaWignerDifferencePhase, Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      sub_self, Real.exp_zero, mul_one]
    rw [abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _),
      abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _)]
  have hNormEq : ∀ᵐ t ∂volume,
      (∑' q : ℕ × ℕ, ‖F q t‖) =
        ‖(thetaCuspFullSource (u + t) *
            thetaCuspFullSource (u - t) : ℂ) *
          thetaWignerDifferencePhase b t‖ := by
    filter_upwards with t
    let A : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (u + t)
    let B : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (u - t)
    have hA : Summable A := summable_thetaCuspCompletedPositiveShell _
    have hB : Summable B := summable_thetaCuspCompletedPositiveShell _
    have hnorm (q : ℕ × ℕ) : ‖F q t‖ = A q.1 * B q.2 := by
      dsimp only [F, A, B]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        thetaWignerDifferencePhase, Complex.norm_exp]
      simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
        sub_self, Real.exp_zero, mul_one]
      rw [abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _),
        abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _)]
    calc
      (∑' q : ℕ × ℕ, ‖F q t‖) =
          ∑' q : ℕ × ℕ, A q.1 * B q.2 := tsum_congr hnorm
      _ = (∑' n, A n) * (∑' n, B n) :=
        (tsum_mul_tsum_of_summable_norm hA.norm hB.norm).symm
      _ = thetaCuspFullSource (u + t) *
          thetaCuspFullSource (u - t) := by
        rw [show (∑' n, A n) = thetaCuspFullSource (u + t) by
              exact tsum_thetaCuspCompletedPositiveShell_eq_fullSource _,
          show (∑' n, B n) = thetaCuspFullSource (u - t) by
              exact tsum_thetaCuspCompletedPositiveShell_eq_fullSource _]
      _ = ‖(thetaCuspFullSource (u + t) *
              thetaCuspFullSource (u - t) : ℂ) *
            thetaWignerDifferencePhase b t‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          thetaWignerDifferencePhase, Complex.norm_exp]
        simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
          sub_self, Real.exp_zero, mul_one]
        rw [abs_of_nonneg (thetaCuspFullSource_nonneg _),
          abs_of_nonneg (thetaCuspFullSource_nonneg _)]
  have hBoundIntegrable :
      Integrable (fun t => ∑' q : ℕ × ℕ, ‖F q t‖) volume := by
    exact (integrable_thetaCuspFullSource_reflectedProduct u b).norm.congr
      (hNormEq.mono fun _ ht => ht.symm)
  have hLim : ∀ᵐ t ∂volume,
      HasSum (fun q : ℕ × ℕ => F q t)
        ((thetaCuspFullSource (u + t) *
            thetaCuspFullSource (u - t) : ℂ) *
          thetaWignerDifferencePhase b t) := by
    filter_upwards with t
    let A : ℕ → ℂ := fun n =>
      (thetaCuspCompletedPositiveShell n (u + t) : ℂ)
    let B : ℕ → ℂ := fun n =>
      (thetaCuspCompletedPositiveShell n (u - t) : ℂ)
    have hA : Summable A :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).summable
        (summable_thetaCuspCompletedPositiveShell _)
    have hB : Summable B :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).summable
        (summable_thetaCuspCompletedPositiveShell _)
    have hpairSummable :
        Summable (fun q : ℕ × ℕ => A q.1 * B q.2) :=
      summable_mul_of_summable_norm hA.norm hB.norm
    have hpair : HasSum (fun q : ℕ × ℕ => A q.1 * B q.2)
        ((∑' n, A n) * (∑' n, B n)) := by
      rw [tsum_mul_tsum_of_summable_norm hA.norm hB.norm]
      exact hpairSummable.hasSum
    have hphase := hpair.mul_right (thetaWignerDifferencePhase b t)
    have hAsum : (∑' n, A n) =
            (thetaCuspFullSource (u + t) : ℂ) := by
      change (∑' n : ℕ,
        (thetaCuspCompletedPositiveShell n (u + t) : ℂ)) = _
      rw [← Complex.ofReal_tsum,
        tsum_thetaCuspCompletedPositiveShell_eq_fullSource]
    have hBsum : (∑' n, B n) =
            (thetaCuspFullSource (u - t) : ℂ) := by
      change (∑' n : ℕ,
        (thetaCuspCompletedPositiveShell n (u - t) : ℂ)) = _
      rw [← Complex.ofReal_tsum,
        tsum_thetaCuspCompletedPositiveShell_eq_fullSource]
    rw [hAsum, hBsum] at hphase
    simpa only [F, A, B] using hphase
  have h := hasSum_integral_of_dominated_convergence
    (fun q t => ‖F q t‖) hFmeas
    (fun q => Filter.Eventually.of_forall fun t => le_rfl)
    hBoundSummable hBoundIntegrable hLim
  simpa [F, thetaCuspCompletedShellPairWigner,
    thetaWignerDistribution, thetaCuspComplexSource,
    Complex.conj_ofReal] using h

theorem summable_thetaCuspCompletedShellPairWigner (u b : ℝ) :
    Summable (fun q : ℕ × ℕ =>
      thetaCuspCompletedShellPairWigner q u b) :=
  (hasSum_thetaCuspCompletedShellPairWigner u b).summable

/-- **Full cofinal product-fibre Wigner expansion.**  The actual Wigner distribution is the
absolutely convergent sum of completed positive-shell packets, grouped only after both divisor
orientations are present. -/
theorem thetaWignerDistribution_thetaCusp_eq_tsum_completedProductFiber
    (u b : ℝ) :
    thetaWignerDistribution thetaCuspComplexSource u b =
      ∑' k : ℕ, thetaCuspCompletedWignerProductFiber k u b := by
  rw [← (hasSum_thetaCuspCompletedShellPairWigner u b).tsum_eq]
  exact tsum_eq_tsum_thetaPositiveFactorPairs _
    (summable_thetaCuspCompletedShellPairWigner u b)

/-- Divisor reflection conjugates completed-shell Wigner pairs. -/
theorem conj_thetaCuspCompletedShellPairWigner
    (q : ℕ × ℕ) (u b : ℝ) :
    (starRingEnd ℂ) (thetaCuspCompletedShellPairWigner q u b) =
      thetaCuspCompletedShellPairWigner q.swap u b := by
  let F : ℝ → ℂ := fun t =>
    (thetaCuspCompletedPositiveShell q.1 (u + t) *
      thetaCuspCompletedPositiveShell q.2 (u - t) : ℂ) *
        thetaWignerDifferencePhase b t
  change (starRingEnd ℂ) (∫ t : ℝ, F t) = _
  rw [← integral_conj]
  rw [← MeasureTheory.integral_neg_eq_self
    (fun t : ℝ => (starRingEnd ℂ) (F t)) volume]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [F]
  rcases q with ⟨n, m⟩
  simp only [Prod.swap]
  rw [show u + -t = u - t by ring, show u - -t = u + t by ring]
  unfold thetaWignerDifferencePhase
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I]
  rw [show (((2 * b * -t : ℝ) : ℂ) * -I) =
      (((2 * b * t : ℝ) : ℂ) * I) by
    push_cast
    ring]
  ring_nf

/-- Transverse complex parts cancel only after the complete divisor packet is summed. -/
theorem conj_thetaCuspCompletedWignerProductFiber
    (k : ℕ) (u b : ℝ) :
    (starRingEnd ℂ) (thetaCuspCompletedWignerProductFiber k u b) =
      thetaCuspCompletedWignerProductFiber k u b := by
  let s := thetaPositiveFactorPairs k
  have hswap :
      (∑ q ∈ s, thetaCuspCompletedShellPairWigner q.swap u b) =
        ∑ q ∈ s, thetaCuspCompletedShellPairWigner q u b := by
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
    (starRingEnd ℂ) (thetaCuspCompletedWignerProductFiber k u b) =
        ∑ q ∈ thetaPositiveFactorPairs k,
          (starRingEnd ℂ)
            (thetaCuspCompletedShellPairWigner q u b) := by
      unfold thetaCuspCompletedWignerProductFiber
      rw [map_sum]
    _ = ∑ q ∈ thetaPositiveFactorPairs k,
          thetaCuspCompletedShellPairWigner q.swap u b := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact conj_thetaCuspCompletedShellPairWigner q u b
    _ = thetaCuspCompletedWignerProductFiber k u b := by
      unfold thetaCuspCompletedWignerProductFiber
      simpa only [s] using hswap

theorem thetaCuspCompletedWignerProductFiber_im_zero
    (k : ℕ) (u b : ℝ) :
    (thetaCuspCompletedWignerProductFiber k u b).im = 0 :=
  Complex.conj_eq_iff_im.mp
    (conj_thetaCuspCompletedWignerProductFiber k u b)

/-- Nonnegative completed-shell amplitude on one product fibre before the common Fourier phase
is applied. -/
def thetaCuspCompletedProductFiberAmplitude
    (k : ℕ) (u t : ℝ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspCompletedPositiveShell q.1 (u + t) *
      thetaCuspCompletedPositiveShell q.2 (u - t)

theorem thetaCuspCompletedProductFiberAmplitude_nonneg
    (k : ℕ) (u t : ℝ) :
    0 ≤ thetaCuspCompletedProductFiberAmplitude k u t := by
  unfold thetaCuspCompletedProductFiberAmplitude
  apply Finset.sum_nonneg
  intro q _hq
  exact mul_nonneg
    (thetaCuspCompletedPositiveShell_nonneg _ _)
    (thetaCuspCompletedPositiveShell_nonneg _ _)

/-- Divisor reflection makes the completed product-fibre amplitude even in the transverse
coordinate.  This equality fails termwise unless the two shell indices agree. -/
theorem thetaCuspCompletedProductFiberAmplitude_neg
    (k : ℕ) (u t : ℝ) :
    thetaCuspCompletedProductFiberAmplitude k u (-t) =
      thetaCuspCompletedProductFiberAmplitude k u t := by
  let s := thetaPositiveFactorPairs k
  have hswap :
      (∑ q ∈ s,
        thetaCuspCompletedPositiveShell q.2 (u + t) *
          thetaCuspCompletedPositiveShell q.1 (u - t)) =
        ∑ q ∈ s,
          thetaCuspCompletedPositiveShell q.1 (u + t) *
            thetaCuspCompletedPositiveShell q.2 (u - t) := by
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
  unfold thetaCuspCompletedProductFiberAmplitude
  rw [show (∑ q ∈ thetaPositiveFactorPairs k,
      thetaCuspCompletedPositiveShell q.1 (u + -t) *
        thetaCuspCompletedPositiveShell q.2 (u - -t)) =
      ∑ q ∈ thetaPositiveFactorPairs k,
        thetaCuspCompletedPositiveShell q.2 (u + t) *
          thetaCuspCompletedPositiveShell q.1 (u - t) by
    apply Finset.sum_congr rfl
    intro q _hq
    rw [show u + -t = u - t by ring,
      show u - -t = u + t by ring]
    ring]
  simpa only [s] using hswap

/-- Positive-wedge symmetry: after divisor summation, exchanging center and transverse
coordinates does not change the completed amplitude. -/
theorem thetaCuspCompletedProductFiberAmplitude_comm
    (k : ℕ) (u t : ℝ) :
    thetaCuspCompletedProductFiberAmplitude k u t =
      thetaCuspCompletedProductFiberAmplitude k t u := by
  unfold thetaCuspCompletedProductFiberAmplitude
  apply Finset.sum_congr rfl
  intro q _hq
  rw [show u + t = t + u by ring]
  unfold thetaCuspCompletedPositiveShell
  rw [abs_sub_comm]

/-- The common-phase integrand of one completed product fibre. -/
def thetaCuspCompletedProductFiberWignerIntegrand
    (k : ℕ) (u b t : ℝ) : ℂ :=
  (thetaCuspCompletedProductFiberAmplitude k u t : ℂ) *
    thetaWignerDifferencePhase b t

/-- **Transverse divisor-cancellation law.**  The positive and negative transverse legs combine
to a real cosine against a nonnegative fibre amplitude.  Cancellation occurs only after the full
divisor packet is present. -/
theorem thetaCuspCompletedProductFiberWignerIntegrand_add_neg
    (k : ℕ) (u b t : ℝ) :
    thetaCuspCompletedProductFiberWignerIntegrand k u b t +
        thetaCuspCompletedProductFiberWignerIntegrand k u b (-t) =
      (2 * thetaCuspCompletedProductFiberAmplitude k u t *
        Real.cos (2 * b * t) : ℝ) := by
  rw [thetaCuspCompletedProductFiberWignerIntegrand,
    thetaCuspCompletedProductFiberWignerIntegrand,
    thetaCuspCompletedProductFiberAmplitude_neg]
  unfold thetaWignerDifferencePhase
  rw [show ((((2 * b * -t : ℝ) : ℂ) * I)) =
      -((((2 * b * t : ℝ) : ℂ) * I)) by
    push_cast
    ring]
  have hcos := Complex.two_cos (((2 * b * t : ℝ) : ℂ))
  rw [← Complex.ofReal_cos] at hcos
  have hcos' :
      Complex.exp ((((2 * b * t : ℝ) : ℂ) * I)) +
          Complex.exp (-((((2 * b * t : ℝ) : ℂ) * I))) =
        2 * (Real.cos (2 * b * t) : ℂ) := by
    simpa only [neg_mul] using hcos.symm
  calc
    (thetaCuspCompletedProductFiberAmplitude k u t : ℂ) *
          Complex.exp ((((2 * b * t : ℝ) : ℂ) * I)) +
        (thetaCuspCompletedProductFiberAmplitude k u t : ℂ) *
          Complex.exp (-((((2 * b * t : ℝ) : ℂ) * I))) =
      (thetaCuspCompletedProductFiberAmplitude k u t : ℂ) *
        (Complex.exp ((((2 * b * t : ℝ) : ℂ) * I)) +
          Complex.exp (-((((2 * b * t : ℝ) : ℂ) * I)))) := by ring
    _ = (thetaCuspCompletedProductFiberAmplitude k u t : ℂ) *
        (2 * (Real.cos (2 * b * t) : ℂ)) := by rw [hcos']
    _ = (2 * thetaCuspCompletedProductFiberAmplitude k u t *
        Real.cos (2 * b * t) : ℝ) := by
      push_cast
      ring

/-! ## Cofinal amplitude and coupled cone obstruction -/

/-- Product fibres remain absolutely summable before any oscillatory phase is applied. -/
theorem summable_thetaCuspCompletedProductFiberAmplitude
    (u t : ℝ) :
    Summable (fun k : ℕ =>
      thetaCuspCompletedProductFiberAmplitude k u t) := by
  let A : ℕ → ℝ := fun n => thetaCuspCompletedPositiveShell n (u + t)
  let B : ℕ → ℝ := fun n => thetaCuspCompletedPositiveShell n (u - t)
  let F : ℕ × ℕ → ℝ := fun q => A q.1 * B q.2
  have hA : Summable A := summable_thetaCuspCompletedPositiveShell _
  have hB : Summable B := summable_thetaCuspCompletedPositiveShell _
  have hpair : Summable F := by
    exact summable_mul_of_summable_norm hA.norm hB.norm
  have hfiberRaw :=
    hpair.hasSum.tsum_fiberwise thetaPositivePairProduct
  rw [show (fun k : ℕ =>
      thetaCuspCompletedProductFiberAmplitude k u t) =
    fun k : ℕ =>
      ∑' q : thetaPositivePairProduct ⁻¹' {k}, F q by
    funext k
    rw [thetaPositivePairProduct_fiber]
    exact (Finset.tsum_subtype' (thetaPositiveFactorPairs k) F).symm]
  exact hfiberRaw.summable

/-- **Cofinal amplitude collapse.**  After every product fibre is summed, the positive amplitude
is exactly the reflected product of the actual completed theta source. -/
theorem tsum_thetaCuspCompletedProductFiberAmplitude_eq_fullSourceProduct
    (u t : ℝ) :
    (∑' k : ℕ, thetaCuspCompletedProductFiberAmplitude k u t) =
      thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) := by
  let A : ℕ → ℝ := fun n => thetaCuspCompletedPositiveShell n (u + t)
  let B : ℕ → ℝ := fun n => thetaCuspCompletedPositiveShell n (u - t)
  let F : ℕ × ℕ → ℝ := fun q => A q.1 * B q.2
  have hA : Summable A := summable_thetaCuspCompletedPositiveShell _
  have hB : Summable B := summable_thetaCuspCompletedPositiveShell _
  have hpair : Summable F := by
    exact summable_mul_of_summable_norm hA.norm hB.norm
  calc
    (∑' k : ℕ, thetaCuspCompletedProductFiberAmplitude k u t) =
        ∑' q : ℕ × ℕ, F q := by
      symm
      simpa only [F, A, B, thetaCuspCompletedProductFiberAmplitude] using
        tsum_eq_tsum_thetaPositiveFactorPairs F hpair
    _ = (∑' n : ℕ, A n) * (∑' n : ℕ, B n) := by
      rw [tsum_mul_tsum_of_summable_norm hA.norm hB.norm]
    _ = thetaCuspFullSource (u + t) *
        thetaCuspFullSource (u - t) := by
      rw [show (∑' n : ℕ, A n) = thetaCuspFullSource (u + t) by
          exact tsum_thetaCuspCompletedPositiveShell_eq_fullSource _,
        show (∑' n : ℕ, B n) = thetaCuspFullSource (u - t) by
          exact tsum_thetaCuspCompletedPositiveShell_eq_fullSource _]

/-! ## Full positive-quadrant and coupled-cone current -/

/-- Real current kernel after the transverse conjugate pair has been combined, before radial
rescaling or folding the positive quadrant along its diagonal. -/
def thetaCuspPositiveQuadrantCenterMixKernel
    (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * Real.sinh (a * p.1) *
    (thetaCuspFullSource (p.1 / 2 + p.2) *
      thetaCuspFullSource (p.1 / 2 - p.2)) *
        Real.cos (2 * b * p.2)

private theorem integrable_positiveQuadrant_comp_mul_fst
    (f : ℝ × ℝ → ℝ) (hf : Integrable f
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))))
    (hf_cont : Continuous f) {c : ℝ} (hc : 0 < c) :
    Integrable (fun p : ℝ × ℝ => f (c * p.1, p.2))
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi 0)
  let g : ℝ × ℝ → ℝ := fun p => f (c * p.1, p.2)
  have hg_cont : Continuous g := by
    exact hf_cont.comp
      ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hg_meas : AEStronglyMeasurable g (mu.prod mu) :=
    hg_cont.aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff' hg_meas]
  constructor
  · filter_upwards [hf.prod_left_ae] with t ht
    change Integrable (fun u : ℝ => f (c * u, t)) mu
    change IntegrableOn (fun u : ℝ => f (c * u, t)) (Set.Ioi 0)
    rw [MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => f (u, t)) 0 hc]
    simpa only [MeasureTheory.IntegrableOn, mul_zero] using ht
  · have hnorm := hf.integral_norm_prod_right
    have heq :
        (fun t : ℝ => ∫ u : ℝ, ‖g (u, t)‖ ∂mu) =
          fun t : ℝ => c⁻¹ * ∫ r : ℝ, ‖f (r, t)‖ ∂mu := by
      funext t
      have hscale := MeasureTheory.integral_comp_mul_left_Ioi
        (fun r : ℝ => ‖f (r, t)‖) 0 hc
      simpa only [g, mu, mul_zero, smul_eq_mul] using hscale
    rw [heq]
    exact hnorm.const_mul c⁻¹

/-- The full real positive-quadrant kernel is absolutely integrable throughout the critical
aperture.  This is inherited from the already established complex center-mix majorant. -/
theorem integrable_thetaCuspPositiveQuadrantCenterMixKernel
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    Integrable (thetaCuspPositiveQuadrantCenterMixKernel a b)
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hfull :=
    integrable_thetaWignerCenterMixKernel (b := b) ha0 haHalf
  have hrestricted :
      Integrable
        (thetaWignerCenterMixKernel thetaCuspComplexSource a b)
        (mu.prod (volume.restrict (Set.Ioi 0))) := by
    have hres := hfull.integrableOn
      (s := (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ))
    change Integrable
      (thetaWignerCenterMixKernel thetaCuspComplexSource a b)
      (((volume.restrict (Set.Ioi 0)).prod volume).restrict
        ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ))) at hres
    rw [← Measure.prod_restrict] at hres
    simpa only [Measure.restrict_univ, mu] using hres
  have hre := hrestricted.re
  exact hre.congr (Filter.Eventually.of_forall fun p => by
    unfold thetaWignerCenterMixKernel thetaCuspComplexSource
      thetaWignerDifferencePhase
    simp only [Complex.conj_ofReal]
    change Complex.re
      (((p.1 * Real.sinh (a * p.1) : ℝ) : ℂ) *
        ((thetaCuspFullSource (p.1 / 2 + p.2) : ℂ) *
          (thetaCuspFullSource (p.1 / 2 - p.2) : ℂ)) *
        Complex.exp ((((2 * b * p.2 : ℝ) : ℂ) * I))) =
      thetaCuspPositiveQuadrantCenterMixKernel a b p
    simp only [Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    unfold thetaCuspPositiveQuadrantCenterMixKernel
    ring)

/-- Radially normalized positive-quadrant kernel.  The factor `1/2` absorbs one of the two
Jacobian factors created by `r = 2u`; unfolding gives
`u sinh (2au) φ(u+t) φ(u-t) cos (2bt)`. -/
def thetaCuspPositiveQuadrantCoupledKernel
    (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    thetaCuspPositiveQuadrantCenterMixKernel a b (2 * p.1, p.2)

theorem thetaCuspPositiveQuadrantCoupledKernel_eq
    (a b u t : ℝ) :
    thetaCuspPositiveQuadrantCoupledKernel a b (u, t) =
      u * Real.sinh (2 * a * u) *
        (thetaCuspFullSource (u + t) *
          thetaCuspFullSource (u - t)) *
            Real.cos (2 * b * t) := by
  unfold thetaCuspPositiveQuadrantCoupledKernel
    thetaCuspPositiveQuadrantCenterMixKernel
  rw [show 2 * u / 2 + t = u + t by ring,
    show 2 * u / 2 - t = u - t by ring,
    show a * (2 * u) = 2 * a * u by ring]
  ring

theorem integrable_thetaCuspPositiveQuadrantCoupledKernel
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    Integrable (thetaCuspPositiveQuadrantCoupledKernel a b)
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0))) := by
  have hK :=
    integrable_thetaCuspPositiveQuadrantCenterMixKernel ha0 haHalf b
  have hcomp := integrable_positiveQuadrant_comp_mul_fst
    (thetaCuspPositiveQuadrantCenterMixKernel a b) hK
    (by
      have hsource : Continuous thetaCuspFullSource :=
        contDiff_thetaCuspFullSource.continuous
      unfold thetaCuspPositiveQuadrantCenterMixKernel
      fun_prop)
    (show (0 : ℝ) < 2 by norm_num)
  exact hcomp.const_mul (1 / 2 : ℝ)

/-- Strict lower triangle in the positive quadrant.  Positivity of both coordinates is carried
by the ambient restricted product measure. -/
def thetaCuspPositiveLowerCone : Set (ℝ × ℝ) :=
  {p | p.2 < p.1}

private def thetaCuspPositiveUpperCone : Set (ℝ × ℝ) :=
  {p | p.1 < p.2}

private def thetaCuspPositiveConeDiagonal : Set (ℝ × ℝ) :=
  {p | p.1 = p.2}

theorem measurableSet_thetaCuspPositiveLowerCone :
    MeasurableSet thetaCuspPositiveLowerCone :=
  measurableSet_lt measurable_snd measurable_fst

private theorem measurableSet_thetaCuspPositiveUpperCone :
    MeasurableSet thetaCuspPositiveUpperCone :=
  measurableSet_lt measurable_fst measurable_snd

private theorem measurableSet_thetaCuspPositiveConeDiagonal :
    MeasurableSet thetaCuspPositiveConeDiagonal := by
  simpa only [thetaCuspPositiveConeDiagonal, diagonal, mem_setOf_eq] using
    (measurableSet_diagonal : MeasurableSet (diagonal ℝ))

private theorem measure_thetaCuspPositiveConeDiagonal_zero :
    ((volume.restrict (Set.Ioi 0)).prod
      (volume.restrict (Set.Ioi 0)))
        thetaCuspPositiveConeDiagonal = 0 := by
  rw [MeasureTheory.Measure.measure_prod_null
    measurableSet_thetaCuspPositiveConeDiagonal]
  filter_upwards with x
  have hsection :
      Prod.mk x ⁻¹' thetaCuspPositiveConeDiagonal =
        ({x} : Set ℝ) := by
    ext y
    simp only [mem_singleton_iff]
    exact eq_comm
  rw [hsection]
  apply bot_unique
  calc
    (volume.restrict (Set.Ioi 0)) ({x} : Set ℝ) ≤
        volume ({x} : Set ℝ) :=
      Measure.restrict_le_self _
    _ = 0 := measure_singleton x

private theorem thetaCuspPositiveLower_union_upper_ae_univ :
    (thetaCuspPositiveLowerCone ∪ thetaCuspPositiveUpperCone :
      Set (ℝ × ℝ)) =ᵐ[
        (volume.restrict (Set.Ioi 0)).prod
          (volume.restrict (Set.Ioi 0))] Set.univ := by
  rw [ae_eq_univ]
  apply measure_mono_null (t := thetaCuspPositiveConeDiagonal)
  · intro p hp
    simp only [mem_compl_iff, mem_union, mem_setOf_eq,
      thetaCuspPositiveLowerCone, thetaCuspPositiveUpperCone,
      not_or, not_lt] at hp
    exact le_antisymm hp.1 hp.2
  · exact measure_thetaCuspPositiveConeDiagonal_zero

private theorem integral_thetaCuspPositiveUpperCone_eq_swap_lowerCone
    (f : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ in thetaCuspPositiveUpperCone, f p
      ∂((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0)))) =
      ∫ p : ℝ × ℝ in thetaCuspPositiveLowerCone, f p.swap
        ∂((volume.restrict (Set.Ioi 0)).prod
          (volume.restrict (Set.Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi 0)
  let g : ℝ × ℝ → ℝ := thetaCuspPositiveUpperCone.indicator f
  have hswap := MeasureTheory.integral_prod_swap
    (μ := mu) (ν := mu) g
  rw [← integral_indicator measurableSet_thetaCuspPositiveUpperCone]
  rw [← integral_indicator measurableSet_thetaCuspPositiveLowerCone]
  rw [← hswap]
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [g]
  by_cases hp : p ∈ thetaCuspPositiveLowerCone
  · rw [indicator_of_mem hp]
    rw [indicator_of_mem]
    exact hp
  · rw [indicator_of_notMem hp]
    rw [indicator_of_notMem]
    exact hp

private theorem integral_positiveQuadrant_eq_lowerCone_add_swap
    (f : ℝ × ℝ → ℝ)
    (hf : Integrable f
      ((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0)))) :
    (∫ p : ℝ × ℝ, f p
      ∂((volume.restrict (Set.Ioi 0)).prod
        (volume.restrict (Set.Ioi 0)))) =
      ∫ p : ℝ × ℝ in thetaCuspPositiveLowerCone,
        (f p + f p.swap)
        ∂((volume.restrict (Set.Ioi 0)).prod
          (volume.restrict (Set.Ioi 0))) := by
  let m : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ioi 0)).prod
      (volume.restrict (Set.Ioi 0))
  have hflower : IntegrableOn f thetaCuspPositiveLowerCone m :=
    hf.integrableOn
  have hfupper : IntegrableOn f thetaCuspPositiveUpperCone m :=
    hf.integrableOn
  have hdisj :
      Disjoint thetaCuspPositiveLowerCone
        thetaCuspPositiveUpperCone := by
    rw [Set.disjoint_left]
    intro p hpL hpU
    change p.2 < p.1 at hpL
    change p.1 < p.2 at hpU
    exact lt_asymm hpL hpU
  have hdecomp := MeasureTheory.setIntegral_union
    hdisj measurableSet_thetaCuspPositiveUpperCone hflower hfupper
  have hfull :
      (∫ p : ℝ × ℝ, f p ∂m) =
        ∫ p : ℝ × ℝ in
          thetaCuspPositiveLowerCone ∪ thetaCuspPositiveUpperCone,
          f p ∂m := by
    rw [← setIntegral_univ]
    exact setIntegral_congr_set
      (by simpa only [m] using
        thetaCuspPositiveLower_union_upper_ae_univ.symm)
  rw [hfull, hdecomp,
    integral_thetaCuspPositiveUpperCone_eq_swap_lowerCone]
  have hfswap :
      IntegrableOn (fun p : ℝ × ℝ => f p.swap)
        thetaCuspPositiveLowerCone m := by
    exact hf.swap.integrableOn
  rw [← integral_add hflower hfswap]

/-- The two triangle contributions obtained after exchanging center and transverse coordinates. -/
def thetaCuspCoupledConeBracket (a b u t : ℝ) : ℝ :=
  u * Real.sinh (2 * a * u) * Real.cos (2 * b * t) +
    t * Real.sinh (2 * a * t) * Real.cos (2 * b * u)

theorem thetaCuspCoupledConeBracket_comm
    (a b u t : ℝ) :
    thetaCuspCoupledConeBracket a b u t =
      thetaCuspCoupledConeBracket a b t u := by
  unfold thetaCuspCoupledConeBracket
  ring

/-- Fully summed source kernel on the positive cone. -/
def thetaCuspCofinalCoupledConeKernel (a b u t : ℝ) : ℝ :=
  thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t) *
    thetaCuspCoupledConeBracket a b u t

theorem thetaCuspCofinalCoupledConeKernel_comm
    (a b u t : ℝ) :
    thetaCuspCofinalCoupledConeKernel a b u t =
      thetaCuspCofinalCoupledConeKernel a b t u := by
  unfold thetaCuspCofinalCoupledConeKernel
  rw [thetaCuspCoupledConeBracket_comm]
  rw [show t + u = u + t by ring,
    show t - u = -(u - t) by ring,
    thetaCuspFullSource_neg]

theorem thetaCuspPositiveQuadrantCoupledKernel_add_swap
    (a b u t : ℝ) :
    thetaCuspPositiveQuadrantCoupledKernel a b (u, t) +
        thetaCuspPositiveQuadrantCoupledKernel a b (t, u) =
      thetaCuspCofinalCoupledConeKernel a b u t := by
  rw [thetaCuspPositiveQuadrantCoupledKernel_eq,
    thetaCuspPositiveQuadrantCoupledKernel_eq]
  unfold thetaCuspCofinalCoupledConeKernel
    thetaCuspCoupledConeBracket
  rw [show t + u = u + t by ring,
    show t - u = -(u - t) by ring,
    thetaCuspFullSource_neg]
  ring

/-- **Pointwise cone-sign no-go.**  At every positive aperture and frequency, the fully summed
coupled bracket is strictly negative at an interior point of the positive cone.  Therefore the
remaining Hedenmalm sign, if true, is an integrated source-mass cancellation theorem and cannot
come from pointwise positivity after divisor/product-fibre completion. -/
theorem thetaCuspCoupledConeBracket_negative_witness
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    thetaCuspCoupledConeBracket a b
        (3 * Real.pi / (2 * b)) (Real.pi / (2 * b)) < 0 := by
  have hu : 0 < 3 * Real.pi / (2 * b) := by positivity
  have ht : 0 < Real.pi / (2 * b) := by positivity
  have hsinhU :
      0 < Real.sinh (2 * a * (3 * Real.pi / (2 * b))) :=
    Real.sinh_pos_iff.mpr (mul_pos (mul_pos (by norm_num) ha) hu)
  have hsinhT :
      0 < Real.sinh (2 * a * (Real.pi / (2 * b))) :=
    Real.sinh_pos_iff.mpr (mul_pos (mul_pos (by norm_num) ha) ht)
  have hphaseT :
      Real.cos (2 * b * (Real.pi / (2 * b))) = -1 := by
    rw [show 2 * b * (Real.pi / (2 * b)) = Real.pi by
      field_simp [hb.ne']]
    exact Real.cos_pi
  have hphaseU :
      Real.cos (2 * b * (3 * Real.pi / (2 * b))) = -1 := by
    rw [show 2 * b * (3 * Real.pi / (2 * b)) = 3 * Real.pi by
      field_simp [hb.ne']]
    rw [show 3 * Real.pi = Real.pi + (1 : ℤ) * (2 * Real.pi) by
      norm_num
      ring,
      Real.cos_add_int_mul_two_pi, Real.cos_pi]
  unfold thetaCuspCoupledConeBracket
  rw [hphaseT, hphaseU]
  nlinarith [mul_pos hu hsinhU, mul_pos ht hsinhT]

/-- The pointwise failure survives the actual cofinal theta amplitude, which is strictly
positive at the witness. -/
theorem thetaCuspCofinalCoupledConeKernel_negative_witness
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    thetaCuspCofinalCoupledConeKernel a b
        (3 * Real.pi / (2 * b)) (Real.pi / (2 * b)) < 0 := by
  have hbracket :=
    thetaCuspCoupledConeBracket_negative_witness ha hb
  have hsource :
      0 < thetaCuspFullSource
            (3 * Real.pi / (2 * b) + Real.pi / (2 * b)) *
          thetaCuspFullSource
            (3 * Real.pi / (2 * b) - Real.pi / (2 * b)) :=
    mul_pos (thetaCuspFullSource_pos_all _)
      (thetaCuspFullSource_pos_all _)
  unfold thetaCuspCofinalCoupledConeKernel
  exact mul_neg_of_pos_of_neg hsource hbracket

/-- Product-space center-mix contribution of one ordered pair of completed positive shells. -/
def thetaCuspCompletedShellPairCenterMixIntegral
    (q : ℕ × ℕ) (a b : ℝ) : ℂ :=
  ∫ p : ℝ × ℝ,
    (p.1 * Real.sinh (a * p.1) : ℝ) *
      ((thetaCuspCompletedPositiveShell q.1 (p.1 / 2 + p.2) : ℂ) *
        (thetaCuspCompletedPositiveShell q.2 (p.1 / 2 - p.2) : ℂ)) *
          thetaWignerDifferencePhase b p.2
      ∂((volume.restrict (Set.Ioi 0)).prod volume)

/-- Complete divisor packet after center mixing.  Both transverse orientations are included
before a real part or sign is read. -/
def thetaCuspCompletedProductFiberCenterMixIntegral
    (k : ℕ) (a b : ℝ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspCompletedShellPairCenterMixIntegral q a b

/-- Absolute completed-shell reassembly on the full center/difference product space. -/
theorem hasSum_thetaCuspCompletedShellPairCenterMixIntegral
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    HasSum (fun q : ℕ × ℕ =>
      thetaCuspCompletedShellPairCenterMixIntegral q a b)
      (∫ p : ℝ × ℝ,
        thetaWignerCenterMixKernel thetaCuspComplexSource a b p
          ∂((volume.restrict (Set.Ioi 0)).prod volume)) := by
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Set.Ioi 0)).prod volume
  let F : (ℕ × ℕ) → (ℝ × ℝ) → ℂ := fun q p =>
    (p.1 * Real.sinh (a * p.1) : ℝ) *
      ((thetaCuspCompletedPositiveShell q.1 (p.1 / 2 + p.2) : ℂ) *
        (thetaCuspCompletedPositiveShell q.2 (p.1 / 2 - p.2) : ℂ)) *
          thetaWignerDifferencePhase b p.2
  have hFmeas : ∀ q, AEStronglyMeasurable (F q) mu := by
    intro q
    exact ((by
      dsimp only [F, thetaCuspCompletedPositiveShell]
      unfold thetaCuspSourceTerm thetaCuspSeed thetaWignerDifferencePhase
      fun_prop : Continuous (F q))).aestronglyMeasurable
  have hBoundSummable :
      ∀ᵐ p ∂mu, Summable (fun q : ℕ × ℕ => ‖F q p‖) := by
    filter_upwards with p
    let A : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (p.1 / 2 + p.2)
    let B : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (p.1 / 2 - p.2)
    let w : ℝ := p.1 * Real.sinh (a * p.1)
    have hA : Summable A := summable_thetaCuspCompletedPositiveShell _
    have hB : Summable B := summable_thetaCuspCompletedPositiveShell _
    have hpair : Summable (fun q : ℕ × ℕ => A q.1 * B q.2) :=
      summable_mul_of_summable_norm hA.norm hB.norm
    have hscaled :
        Summable (fun q : ℕ × ℕ => |w| * (A q.1 * B q.2)) :=
      hpair.mul_left |w|
    apply hscaled.congr
    intro q
    dsimp only [F, A, B, w]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      thetaWignerDifferencePhase, Complex.norm_exp, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, mul_zero, sub_self, Real.exp_zero, mul_one]
    rw [abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _),
      abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _)]
    rw [abs_mul]
  have hNormEq : ∀ᵐ p ∂mu,
      (∑' q : ℕ × ℕ, ‖F q p‖) =
        ‖thetaWignerCenterMixKernel thetaCuspComplexSource a b p‖ := by
    filter_upwards with p
    let A : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (p.1 / 2 + p.2)
    let B : ℕ → ℝ := fun n =>
      thetaCuspCompletedPositiveShell n (p.1 / 2 - p.2)
    let w : ℝ := p.1 * Real.sinh (a * p.1)
    have hA : Summable A := summable_thetaCuspCompletedPositiveShell _
    have hB : Summable B := summable_thetaCuspCompletedPositiveShell _
    have hnorm (q : ℕ × ℕ) :
        ‖F q p‖ = |w| * (A q.1 * B q.2) := by
      dsimp only [F, A, B, w]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        thetaWignerDifferencePhase, Complex.norm_exp, mul_re, ofReal_re,
        ofReal_im, I_re, I_im, mul_zero, sub_self, Real.exp_zero, mul_one]
      rw [abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _),
        abs_of_nonneg (thetaCuspCompletedPositiveShell_nonneg _ _)]
      rw [abs_mul]
    calc
      (∑' q : ℕ × ℕ, ‖F q p‖) =
          ∑' q : ℕ × ℕ, |w| * (A q.1 * B q.2) :=
        tsum_congr hnorm
      _ = |w| * (∑' q : ℕ × ℕ, A q.1 * B q.2) := by
        rw [tsum_mul_left]
      _ = |w| * ((∑' n, A n) * (∑' n, B n)) := by
        rw [tsum_mul_tsum_of_summable_norm hA.norm hB.norm]
      _ = |w| *
          (thetaCuspFullSource (p.1 / 2 + p.2) *
            thetaCuspFullSource (p.1 / 2 - p.2)) := by
        rw [show (∑' n, A n) =
              thetaCuspFullSource (p.1 / 2 + p.2) by
                exact tsum_thetaCuspCompletedPositiveShell_eq_fullSource _,
          show (∑' n, B n) =
              thetaCuspFullSource (p.1 / 2 - p.2) by
                exact tsum_thetaCuspCompletedPositiveShell_eq_fullSource _]
      _ = ‖thetaWignerCenterMixKernel
            thetaCuspComplexSource a b p‖ := by
        unfold thetaWignerCenterMixKernel thetaCuspComplexSource
        dsimp only [w]
        simp only [Complex.conj_ofReal, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, thetaWignerDifferencePhase, Complex.norm_exp,
          mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, sub_self,
          Real.exp_zero, mul_one]
        rw [abs_of_nonneg (thetaCuspFullSource_nonneg _),
          abs_of_nonneg (thetaCuspFullSource_nonneg _)]
        rw [abs_mul]
  have hBoundIntegrable :
      Integrable (fun p => ∑' q : ℕ × ℕ, ‖F q p‖) mu := by
    exact (integrable_thetaWignerCenterMixKernel ha0 haHalf).norm.congr
      (hNormEq.mono fun _ hp => hp.symm)
  have hLim : ∀ᵐ p ∂mu,
      HasSum (fun q : ℕ × ℕ => F q p)
        (thetaWignerCenterMixKernel thetaCuspComplexSource a b p) := by
    filter_upwards with p
    let A : ℕ → ℂ := fun n =>
      (thetaCuspCompletedPositiveShell n (p.1 / 2 + p.2) : ℂ)
    let B : ℕ → ℂ := fun n =>
      (thetaCuspCompletedPositiveShell n (p.1 / 2 - p.2) : ℂ)
    let w : ℂ := (p.1 * Real.sinh (a * p.1) : ℝ)
    have hA : Summable A :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).summable
        (summable_thetaCuspCompletedPositiveShell _)
    have hB : Summable B :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).summable
        (summable_thetaCuspCompletedPositiveShell _)
    have hpairSummable :
        Summable (fun q : ℕ × ℕ => A q.1 * B q.2) :=
      summable_mul_of_summable_norm hA.norm hB.norm
    have hpair : HasSum (fun q : ℕ × ℕ => A q.1 * B q.2)
        ((∑' n, A n) * (∑' n, B n)) := by
      rw [tsum_mul_tsum_of_summable_norm hA.norm hB.norm]
      exact hpairSummable.hasSum
    have hphase :=
      (hpair.mul_left w).mul_right (thetaWignerDifferencePhase b p.2)
    have hAsum : (∑' n, A n) =
        (thetaCuspFullSource (p.1 / 2 + p.2) : ℂ) := by
      change (∑' n : ℕ,
        (thetaCuspCompletedPositiveShell n (p.1 / 2 + p.2) : ℂ)) = _
      rw [← Complex.ofReal_tsum,
        tsum_thetaCuspCompletedPositiveShell_eq_fullSource]
    have hBsum : (∑' n, B n) =
        (thetaCuspFullSource (p.1 / 2 - p.2) : ℂ) := by
      change (∑' n : ℕ,
        (thetaCuspCompletedPositiveShell n (p.1 / 2 - p.2) : ℂ)) = _
      rw [← Complex.ofReal_tsum,
        tsum_thetaCuspCompletedPositiveShell_eq_fullSource]
    rw [hAsum, hBsum] at hphase
    simpa [F, A, B, w, thetaWignerCenterMixKernel,
      thetaCuspComplexSource] using hphase
  have h := hasSum_integral_of_dominated_convergence
    (fun q p => ‖F q p‖) hFmeas
    (fun q => Filter.Eventually.of_forall fun p => le_rfl)
    hBoundSummable hBoundIntegrable hLim
  simpa only [mu, F, thetaCuspCompletedShellPairCenterMixIntegral] using h

theorem summable_thetaCuspCompletedShellPairCenterMixIntegral
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    Summable (fun q : ℕ × ℕ =>
      thetaCuspCompletedShellPairCenterMixIntegral q a b) :=
  (hasSum_thetaCuspCompletedShellPairCenterMixIntegral ha0 haHalf b).summable

private theorem integral_thetaWignerCenterMixKernel_eq_radialWigner
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    (∫ p : ℝ × ℝ,
      thetaWignerCenterMixKernel thetaCuspComplexSource a b p
        ∂((volume.restrict (Set.Ioi 0)).prod volume)) =
      ∫ r : ℝ in Set.Ioi 0,
        (r * Real.sinh (a * r) : ℝ) *
          thetaWignerDistribution thetaCuspComplexSource (r / 2) b := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hInt :=
    integrable_thetaWignerCenterMixKernel (b := b) ha0 haHalf
  rw [MeasureTheory.integral_prod _ hInt]
  apply integral_congr_ae
  filter_upwards with r
  rw [thetaWignerDistribution, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [thetaWignerCenterMixKernel]
  push_cast
  ring

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

/-- **Exact cosine coordinate for the actual Hedenmalm current.**  Evenness of the center-mixed
density removes the imaginary Fourier component before any divisor or product-fibre estimate is
made.  Thus the remaining sign problem is exactly the cosine transform of the fully coupled
positive spatial density. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_cosine
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg ha0]; linarith) b =
      4 * ∫ t : ℝ in Set.Ioi 0,
        thetaCuspCenterMixedDensity a t * Real.cos (2 * b * t) := by
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
  let G : ℝ → ℂ := fun t =>
    Complex.exp (((-2 * b * t : ℝ) : ℂ) * I) * C t
  have hC : Integrable C := by
    exact (integrable_thetaCuspCenterMixedDensity_of_abs_lt_one ha).ofReal
  have hG : Integrable G := by
    have hraw : Integrable (fun t =>
        C t * Complex.exp (((-2 * b * t : ℝ) : ℂ) * I)) := by
      apply hC.mul_bdd (c := 1)
      · fun_prop
      · filter_upwards with t
        exact le_of_eq (Complex.norm_exp_ofReal_mul_I (-2 * b * t))
    exact hraw.congr (Filter.Eventually.of_forall fun t => by
      dsimp only [G]
      ring)
  have hsplit := integral_eq_integral_Ioi_add_reflect hG
  have hpair :
      ∀ t : ℝ, (G t + G (-t)).re =
        2 * thetaCuspCenterMixedDensity a t * Real.cos (2 * b * t) := by
    intro t
    dsimp only [G, C]
    rw [thetaCuspCenterMixedDensity_even]
    rw [show (((-2 * b * t : ℝ) : ℂ) * I) =
        ((-(2 * b * t) : ℝ) : ℂ) * I by
      push_cast
      ring,
      show (((-2 * b * -t : ℝ) : ℂ) * I) =
        ((2 * b * t : ℝ) : ℂ) * I by
      push_cast
      ring]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re]
    rw [Real.cos_neg]
    ring
  have hpairInt :
      IntegrableOn (fun t : ℝ => G t + G (-t)) (Set.Ioi 0) :=
    hG.integrableOn.add hG.comp_neg.integrableOn
  have hre :
      (∫ t : ℝ in Set.Ioi 0, G t + G (-t)).re =
        ∫ t : ℝ in Set.Ioi 0,
          2 * thetaCuspCenterMixedDensity a t * Real.cos (2 * b * t) := by
    calc
      (∫ t : ℝ in Set.Ioi 0, G t + G (-t)).re =
          ∫ t : ℝ in Set.Ioi 0, (G t + G (-t)).re :=
        (integral_re hpairInt).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with t
        exact hpair t
  rw [thetaCuspCenterMixedFourierCurrent]
  change
    (FourierTransform.fourier
      (thetaCuspHorizontalAutocorrelationTangent a ha)
      (b / (2 * Real.pi))).re = _
  rw [hfourier, hscale]
  norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  rw [hsplit, hre]
  have hfactor :
      (fun t : ℝ =>
        2 * thetaCuspCenterMixedDensity a t * Real.cos (2 * b * t)) =
      fun t : ℝ =>
        2 * (thetaCuspCenterMixedDensity a t * Real.cos (2 * b * t)) := by
    funext t
    ring
  rw [hfactor, integral_const_mul]
  ring

/-- **Exact positive-quadrant current.**  After both transverse orientations are combined, the
actual Hedenmalm current is four times the absolutely convergent positive-quadrant integral.
No pointwise sign is asserted: the cosine factor remains inside the coupled integral. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_positiveQuadrant
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg ha0]; linarith) b =
      4 * ∫ p : ℝ × ℝ,
        thetaCuspPositiveQuadrantCenterMixKernel a b p
          ∂((volume.restrict (Set.Ioi 0)).prod
            (volume.restrict (Set.Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hK :=
    integrable_thetaCuspPositiveQuadrantCenterMixKernel ha0 haHalf b
  have hK' : Integrable
      (Function.uncurry fun r t =>
        thetaCuspPositiveQuadrantCenterMixKernel a b (r, t))
      (mu.prod mu) := hK
  have hswap := MeasureTheory.integral_integral_swap hK'
  rw [thetaCuspCenterMixedFourierCurrent_eq_cosine ha0 haHalf b]
  congr 1
  rw [MeasureTheory.integral_prod _ hK, hswap]
  apply integral_congr_ae
  filter_upwards with t
  rw [thetaCuspCenterMixedDensity, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with r
  unfold thetaCuspPositiveQuadrantCenterMixKernel
  ring

/-- **Radially normalized positive-quadrant current.**  The exact substitution `r = 2u`
turns the actual current into sixteen times the coupled source kernel on the positive quadrant. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_positiveQuadrantCoupled
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg ha0]; linarith) b =
      16 * ∫ p : ℝ × ℝ,
        thetaCuspPositiveQuadrantCoupledKernel a b p
          ∂((volume.restrict (Set.Ioi 0)).prod
            (volume.restrict (Set.Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi 0)
  let K : ℝ × ℝ → ℝ :=
    thetaCuspPositiveQuadrantCenterMixKernel a b
  let S : ℝ × ℝ → ℝ :=
    thetaCuspPositiveQuadrantCoupledKernel a b
  have hK : Integrable K (mu.prod mu) :=
    integrable_thetaCuspPositiveQuadrantCenterMixKernel ha0 haHalf b
  have hS : Integrable S (mu.prod mu) :=
    integrable_thetaCuspPositiveQuadrantCoupledKernel ha0 haHalf b
  have hinner :
      (fun u : ℝ => ∫ t : ℝ, S (u, t) ∂mu) =
        fun u : ℝ => (1 / 2 : ℝ) * ∫ t : ℝ, K (2 * u, t) ∂mu := by
    funext u
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rfl
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (fun r : ℝ => ∫ t : ℝ, K (r, t) ∂mu) 0
    (show (0 : ℝ) < 2 by norm_num)
  have hscale' :
      (∫ u : ℝ in Set.Ioi 0, ∫ t : ℝ, K (2 * u, t) ∂mu) =
        (1 / 2 : ℝ) * ∫ r : ℝ in Set.Ioi 0,
          ∫ t : ℝ, K (r, t) ∂mu := by
    simp only [mul_zero, smul_eq_mul] at hscale
    norm_num at hscale ⊢
    exact hscale
  have hscaledIntegral :
      (∫ p : ℝ × ℝ, S p ∂mu.prod mu) =
        (1 / 4 : ℝ) * ∫ p : ℝ × ℝ, K p ∂mu.prod mu := by
    rw [MeasureTheory.integral_prod _ hS,
      MeasureTheory.integral_prod _ hK, hinner,
      integral_const_mul, hscale']
    ring
  rw [thetaCuspCenterMixedFourierCurrent_eq_positiveQuadrant
    ha0 haHalf b]
  change 4 * (∫ p : ℝ × ℝ, K p ∂mu.prod mu) =
    16 * ∫ p : ℝ × ℝ, S p ∂mu.prod mu
  rw [hscaledIntegral]
  ring

/-- **Exact full coupled cone current.**  Divisor/product-fibre completion, transverse conjugate
pairing, radial normalization, and diagonal folding leave one source-specific signed integral.
The two transverse terms are summed before any sign is read, so cancellation between them is
retained exactly. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_coupledCone
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg ha0]; linarith) b =
      16 * ∫ p : ℝ × ℝ in thetaCuspPositiveLowerCone,
        thetaCuspCofinalCoupledConeKernel a b p.1 p.2
          ∂((volume.restrict (Set.Ioi 0)).prod
            (volume.restrict (Set.Ioi 0))) := by
  have hS :=
    integrable_thetaCuspPositiveQuadrantCoupledKernel ha0 haHalf b
  rw [
    thetaCuspCenterMixedFourierCurrent_eq_sixteen_mul_positiveQuadrantCoupled
      ha0 haHalf b,
    integral_positiveQuadrant_eq_lowerCone_add_swap _ hS]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun
    measurableSet_thetaCuspPositiveLowerCone
  intro p _hp
  exact thetaCuspPositiveQuadrantCoupledKernel_add_swap
    a b p.1 p.2

/-- **Full coupled Hedenmalm current after divisor/product-fibre summation.**  Absolute
reassembly is performed in product space; transverse conjugate orientations cancel inside each
finite divisor packet before the current is read. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_tsum_completedProductFiber
    {a : ℝ} (ha0 : 0 ≤ a) (haHalf : a < 1 / 2) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a
        (by rw [abs_of_nonneg ha0]; linarith) b =
      ∑' k : ℕ,
        2 * (thetaCuspCompletedProductFiberCenterMixIntegral k a b).re := by
  have hpair :=
    hasSum_thetaCuspCompletedShellPairCenterMixIntegral ha0 haHalf b
  have hpairSummable := hpair.summable
  have hfiber :
      (∑' q : ℕ × ℕ,
        thetaCuspCompletedShellPairCenterMixIntegral q a b) =
        ∑' k : ℕ,
          thetaCuspCompletedProductFiberCenterMixIntegral k a b := by
    exact tsum_eq_tsum_thetaPositiveFactorPairs _ hpairSummable
  have hsum :
      (∫ r : ℝ in Set.Ioi 0,
        (r * Real.sinh (a * r) : ℝ) *
          thetaWignerDistribution thetaCuspComplexSource (r / 2) b) =
        ∑' k : ℕ,
          thetaCuspCompletedProductFiberCenterMixIntegral k a b := by
    rw [← hfiber, hpair.tsum_eq,
      integral_thetaWignerCenterMixKernel_eq_radialWigner ha0 haHalf]
  rw [thetaCuspCenterMixedFourierCurrent_eq_two_mul_re_radialWigner
    ha0 haHalf b, hsum]
  have hfiberSummable :
      Summable (fun k : ℕ =>
        thetaCuspCompletedProductFiberCenterMixIntegral k a b) := by
    have hfiberRaw :=
      hpairSummable.hasSum.tsum_fiberwise thetaPositivePairProduct
    rw [show (fun k : ℕ =>
        thetaCuspCompletedProductFiberCenterMixIntegral k a b) =
      fun k : ℕ =>
        ∑' q : thetaPositivePairProduct ⁻¹' {k},
          thetaCuspCompletedShellPairCenterMixIntegral q a b by
      funext k
      rw [thetaPositivePairProduct_fiber]
      exact (Finset.tsum_subtype' (thetaPositiveFactorPairs k)
        (fun q =>
          thetaCuspCompletedShellPairCenterMixIntegral q a b)).symm]
    exact hfiberRaw.summable
  rw [Complex.re_tsum hfiberSummable, tsum_mul_left]

end

end RHTower
