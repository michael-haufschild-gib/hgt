import GaloisForLFunctions.RHTower.XiMassCriticalSafeEulerGreenWeld

/-!
# Global zero-rate prime-tail Green potential

The atomwise Green--Stokes realization of the critical Weil pairing can be assembled before
integration.  The resulting source is one locally finite causal potential, not a formal sum of
pairings.  Absolute Fubini at critical half-density follows by extracting a strict exponent
`e > 1/2` from the mass-profile decay and retaining the residual exponent `d-e > 0` for the
Green-time integral.

This also identifies the potential with the source-fixed zero-rate Dirichlet branch of the
reflection-folded prime-tail resolvent.  No divisor specialization or homogeneous datum enters.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal Topology

namespace RHTower

noncomputable section

/-- One assembled, locally finite, source-fixed zero-rate prime-tail Green potential. -/
def criticalPrimeTailZeroGreenPotential (L : ℝ) : ℂ :=
  ∑' n : DeningerPrimePowerIndex, criticalPrimeTailZeroGreenAtom n L

/-- At every finite time, the global potential is the literal finite causal source sum. -/
theorem criticalPrimeTailZeroGreenPotential_eq_sum (L : ℝ) :
    criticalPrimeTailZeroGreenPotential L =
      ∑ n ∈ primeFoldBelowFinset L, criticalPrimeTailZeroGreenAtom n L := by
  rw [criticalPrimeTailZeroGreenPotential]
  refine tsum_eq_sum ?_
  intro n hn
  have htime : ¬ deningerPrimePowerTime n < L := by simpa using hn
  exact criticalPrimeTailZeroGreenAtom_eq_indicator n |>.symm ▸ by
    simp [Set.indicator, htime]

/-- No source has arrived below the first ordinary-integer time. -/
theorem criticalPrimeTailZeroGreenPotential_eq_zero_of_le_log_two
    {L : ℝ} (hL : L ≤ Real.log 2) :
    criticalPrimeTailZeroGreenPotential L = 0 := by
  rw [criticalPrimeTailZeroGreenPotential]
  have hzero : ∀ n : DeningerPrimePowerIndex,
      criticalPrimeTailZeroGreenAtom n L = 0 := by
    intro n
    rw [criticalPrimeTailZeroGreenAtom, if_neg]
    exact not_lt.mpr (hL.trans (log_two_le_deningerPrimePowerTime n))
  simp [hzero]

/-- Each zero-rate Green atom is the time primitive of the rate-zero causal resolvent atom. -/
theorem criticalPrimeTailZeroGreenAtom_eq_neg_sub_mul_primeFoldCausalAtom_zero
    (n : DeningerPrimePowerIndex) (L : ℝ) :
    criticalPrimeTailZeroGreenAtom n L =
      -(((L - deningerPrimePowerTime n : ℝ) : ℂ) *
        primeFoldCausalAtom 0 n L) := by
  by_cases hL : deningerPrimePowerTime n < L
  · simp [criticalPrimeTailZeroGreenAtom, primeFoldCausalAtom, hL]
    ring
  · simp [criticalPrimeTailZeroGreenAtom, primeFoldCausalAtom, hL]

/-- Integrable residual Green-time majorant after extracting exponent `e` from depth `d`. -/
def xiMassGlobalZeroGreenMajorant
    (sigma d e u : ℝ) (L : ℝ) : ℝ :=
  Set.indicator (Ioi (0 : ℝ))
    (fun L : ℝ =>
      (Real.exp (|u| * d) *
        (∫ x : ℝ, Real.exp (-(sigma / 2 * |x|)))) *
      (2 * xiMassShiftedMomentConstant sigma d 1 * L +
        xiMassShiftedMomentConstant sigma d 2 * L ^ 2) *
      Real.exp (-((d - e) * L))) L

theorem xiMassGlobalZeroGreenMajorant_nonneg
    {sigma d e : ℝ} (hsigma : 0 < sigma) (_hd : 0 ≤ d) (u L : ℝ) :
    0 ≤ xiMassGlobalZeroGreenMajorant sigma d e u L := by
  rw [xiMassGlobalZeroGreenMajorant]
  by_cases hL : L ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hL]
    have hL0 : 0 ≤ L := (mem_Ioi.mp hL).le
    have hJ : 0 ≤ ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|)) :=
      integral_nonneg fun _ => Real.exp_nonneg _
    have hC1 : 0 ≤ xiMassShiftedMomentConstant sigma d 1 := by
      unfold xiMassShiftedMomentConstant
      positivity
    have hC2 : 0 ≤ xiMassShiftedMomentConstant sigma d 2 := by
      unfold xiMassShiftedMomentConstant
      positivity
    positivity
  · rw [Set.indicator_of_notMem hL]

theorem integrable_xiMassGlobalZeroGreenMajorant
    {sigma d e : ℝ} (_hsigma : 0 < sigma) (hed : e < d) (u : ℝ) :
    Integrable (xiMassGlobalZeroGreenMajorant sigma d e u) := by
  let A : ℝ := Real.exp (|u| * d) *
    (∫ x : ℝ, Real.exp (-(sigma / 2 * |x|)))
  let C1 : ℝ := xiMassShiftedMomentConstant sigma d 1
  let C2 : ℝ := xiMassShiftedMomentConstant sigma d 2
  have hr : 0 < d - e := sub_pos.mpr hed
  have h1 := integrableOn_pow_mul_exp_neg_real_green 1 hr
  have h2 := integrableOn_pow_mul_exp_neg_real_green 2 hr
  have hbase : IntegrableOn (fun L : ℝ =>
      A * ((2 * C1) * (L ^ 1 * Real.exp (-(d - e) * L)) +
        C2 * (L ^ 2 * Real.exp (-(d - e) * L)))) (Ioi 0) :=
    ((h1.const_mul (2 * C1)).add (h2.const_mul C2)).const_mul A
  change Integrable (Set.indicator (Ioi (0 : ℝ))
    (fun L : ℝ =>
      (Real.exp (|u| * d) *
        (∫ x : ℝ, Real.exp (-(sigma / 2 * |x|)))) *
      (2 * xiMassShiftedMomentConstant sigma d 1 * L +
        xiMassShiftedMomentConstant sigma d 2 * L ^ 2) *
      Real.exp (-((d - e) * L))))
  rw [integrable_indicator_iff measurableSet_Ioi]
  refine hbase.congr ?_
  filter_upwards with L
  dsimp only [A, C1, C2]
  ring_nf

/-- Every atomwise Green integrand is genuinely integrable on the whole line. -/
theorem integrable_xiMassPositionSecond_mul_zeroGreenAtom
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u : ℝ)
    (n : DeningerPrimePowerIndex) :
    Integrable (fun L : ℝ =>
      xiMassPrimeTailPositionProfileSecond a sigma u L *
        criticalPrimeTailZeroGreenAtom n L) := by
  let d : ℝ := a / 2
  let t : ℝ := deningerPrimePowerTime n
  have hd : 0 < d := by dsimp only [d]; linarith
  have hda : d < a := by dsimp only [d]; linarith
  have ht : 0 ≤ t := (deningerPrimePowerTime_pos n).le
  have hbase := integrableOn_sub_mul_xiMassPrimeTailPositionProfileSecond
    hd hda hsigma u ht
  rw [criticalPrimeTailZeroGreenAtom_eq_indicator]
  have hind := (integrable_indicator_iff measurableSet_Ioi).mpr
    (hbase.const_mul (-(criticalPrimeTailAtomWeight n : ℂ)))
  refine hind.congr ?_
  filter_upwards with L
  by_cases hL : L ∈ Ioi t
  · rw [Set.indicator_of_mem hL, Set.indicator_of_mem hL]
    ring
  · rw [Set.indicator_of_notMem hL, Set.indicator_of_notMem hL, mul_zero]

/-- Pointwise critical Green integrand is dominated by an extracted Dirichlet coefficient times
one common integrable Green-time majorant. -/
theorem norm_xiMassPositionSecond_mul_zeroGreenAtom_le
    {a sigma d e : ℝ} (hd0 : 0 ≤ d) (hda : d < a) (hsigma : 0 < sigma)
    (he0 : 0 ≤ e) (_hed : e < d) (u : ℝ) (n : DeningerPrimePowerIndex) (L : ℝ) :
    ‖xiMassPrimeTailPositionProfileSecond a sigma u L *
        criticalPrimeTailZeroGreenAtom n L‖ ≤
      (criticalPrimeTailAtomWeight n *
        Real.exp (-(e * deningerPrimePowerTime n))) *
        xiMassGlobalZeroGreenMajorant sigma d e u L := by
  let t : ℝ := deningerPrimePowerTime n
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma / 2 * |x|))
  let C1 : ℝ := xiMassShiftedMomentConstant sigma d 1
  let C2 : ℝ := xiMassShiftedMomentConstant sigma d 2
  have ht0 : 0 ≤ t := (deningerPrimePowerTime_pos n).le
  have hw0 : 0 ≤ criticalPrimeTailAtomWeight n := criticalPrimeTailAtomWeight_nonneg n
  by_cases hLt : t < L
  · have hL0 : 0 ≤ L := ht0.trans (le_of_lt hLt)
    have hM1 := norm_xiMassSpectralCrossMoment_deepShift_le
      hd0 hda hsigma u 1 hL0
    have hM2 := norm_xiMassSpectralCrossMoment_deepShift_le
      hd0 hda hsigma u 2 hL0
    have hJ0 : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
    have hC1 : 0 ≤ C1 := by dsimp only [C1, xiMassShiftedMomentConstant]; positivity
    have hC2 : 0 ≤ C2 := by dsimp only [C2, xiMassShiftedMomentConstant]; positivity
    have hprofile :
        ‖xiMassPrimeTailPositionProfileSecond a sigma u L‖ ≤
          Real.exp (|u| * d - L * d) * J * (2 * C1 + L * C2) := by
      rw [xiMassPrimeTailPositionProfileSecond]
      calc
        ‖2 * xiMassSpectralCrossMoment a sigma u 1 L +
            (L : ℂ) * xiMassSpectralCrossMoment a sigma u 2 L‖ ≤
            ‖2 * xiMassSpectralCrossMoment a sigma u 1 L‖ +
              ‖(L : ℂ) * xiMassSpectralCrossMoment a sigma u 2 L‖ :=
          norm_add_le _ _
        _ = 2 * ‖xiMassSpectralCrossMoment a sigma u 1 L‖ +
              L * ‖xiMassSpectralCrossMoment a sigma u 2 L‖ := by
          rw [norm_mul, norm_mul, norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hL0]
        _ ≤ 2 * (Real.exp (|u| * d - L * d) * C1 * J) +
              L * (Real.exp (|u| * d - L * d) * C2 * J) := by
          gcongr
        _ = Real.exp (|u| * d - L * d) * J * (2 * C1 + L * C2) := by
          ring
    have hsub : 0 ≤ L - t := sub_nonneg.mpr (le_of_lt hLt)
    have hsubLe : L - t ≤ L := by linarith
    have hemono : Real.exp (-(e * L)) ≤ Real.exp (-(e * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hexp : Real.exp (|u| * d - L * d) =
        Real.exp (|u| * d) * Real.exp (-(e * L)) *
          Real.exp (-((d - e) * L)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [criticalPrimeTailZeroGreenAtom, if_pos hLt, norm_mul, norm_neg,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsub,
      xiMassGlobalZeroGreenMajorant, Set.indicator_of_mem (show L ∈ Ioi 0 by
        exact mem_Ioi.mpr (lt_of_lt_of_le (deningerPrimePowerTime_pos n) (le_of_lt hLt)))]
    rw [hexp] at hprofile
    have hpoly :
        (L - t) * (2 * C1 + L * C2) ≤ 2 * C1 * L + C2 * L ^ 2 := by
      calc
        (L - t) * (2 * C1 + L * C2) ≤
            L * (2 * C1 + L * C2) :=
          mul_le_mul_of_nonneg_right hsubLe
            (add_nonneg (mul_nonneg (by norm_num) hC1) (mul_nonneg hL0 hC2))
        _ = 2 * C1 * L + C2 * L ^ 2 := by ring
    have hpoly0 : 0 ≤ 2 * C1 * L + C2 * L ^ 2 := by positivity
    have hcore :
        Real.exp (-(e * L)) * ((L - t) * (2 * C1 + L * C2)) ≤
          Real.exp (-(e * t)) * (2 * C1 * L + C2 * L ^ 2) := by
      calc
        Real.exp (-(e * L)) * ((L - t) * (2 * C1 + L * C2)) ≤
            Real.exp (-(e * L)) * (2 * C1 * L + C2 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)
        _ ≤ Real.exp (-(e * t)) * (2 * C1 * L + C2 * L ^ 2) :=
          mul_le_mul_of_nonneg_right hemono hpoly0
    have hcommon0 :
        0 ≤ criticalPrimeTailAtomWeight n * Real.exp (|u| * d) *
          Real.exp (-((d - e) * L)) * J := by positivity
    have hweighted := mul_le_mul_of_nonneg_left hcore hcommon0
    calc
      ‖xiMassPrimeTailPositionProfileSecond a sigma u L‖ *
          (criticalPrimeTailAtomWeight n * (L - t)) ≤
        (Real.exp (|u| * d) * Real.exp (-(e * L)) *
            Real.exp (-((d - e) * L)) * J * (2 * C1 + L * C2)) *
          (criticalPrimeTailAtomWeight n * (L - t)) :=
        mul_le_mul_of_nonneg_right hprofile (mul_nonneg hw0 hsub)
      _ ≤ (criticalPrimeTailAtomWeight n * Real.exp (-(e * t))) *
          ((Real.exp (|u| * d) * J) *
            (2 * C1 * L + C2 * L ^ 2) * Real.exp (-((d - e) * L))) := by
        calc
          (Real.exp (|u| * d) * Real.exp (-(e * L)) *
                Real.exp (-((d - e) * L)) * J * (2 * C1 + L * C2)) *
              (criticalPrimeTailAtomWeight n * (L - t)) =
            (criticalPrimeTailAtomWeight n * Real.exp (|u| * d) *
              Real.exp (-((d - e) * L)) * J) *
              (Real.exp (-(e * L)) * ((L - t) * (2 * C1 + L * C2))) := by ring
          _ ≤ (criticalPrimeTailAtomWeight n * Real.exp (|u| * d) *
              Real.exp (-((d - e) * L)) * J) *
              (Real.exp (-(e * t)) * (2 * C1 * L + C2 * L ^ 2)) := hweighted
          _ = (criticalPrimeTailAtomWeight n * Real.exp (-(e * t))) *
              ((Real.exp (|u| * d) * J) *
                (2 * C1 * L + C2 * L ^ 2) * Real.exp (-((d - e) * L))) := by ring
      _ = (criticalPrimeTailAtomWeight n * Real.exp (-(e * t))) *
          ((Real.exp (|u| * d) * J) *
            (2 * C1 * L + C2 * L ^ 2) * Real.exp (-((d - e) * L))) := rfl
  · rw [criticalPrimeTailZeroGreenAtom, if_neg hLt, mul_zero, norm_zero]
    exact mul_nonneg
      (mul_nonneg hw0 (Real.exp_nonneg _))
      (xiMassGlobalZeroGreenMajorant_nonneg hsigma hd0 u L)

/-- Extracted critical half-density coefficients are absolutely summable exactly because
`e > 1/2`. -/
theorem summable_criticalPrimeTailAtomWeight_mul_exp_neg
    {e : ℝ} (he : 1 / 2 < e) :
    Summable (fun n : DeningerPrimePowerIndex =>
      criticalPrimeTailAtomWeight n *
        Real.exp (-(e * deningerPrimePowerTime n))) := by
  let z : ℂ := (1 / 2 : ℂ) + (e : ℂ)
  have hz : 1 < z.re := by dsimp only [z]; simp; linarith
  have hs := summable_criticalPrimeTailDirichletCoefficient hz
  have hcomplex : Summable (fun n : DeningerPrimePowerIndex =>
      (criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (-((e : ℂ) * (deningerPrimePowerTime n : ℂ)))) := by
    refine hs.congr ?_
    intro n
    have h := criticalPrimeTail_prefactor_mul_coefficient z n 0
    dsimp only [z, criticalPrimeTailTransportRate] at h
    change criticalPrimeTailDirichletCoefficient ((1 / 2 : ℂ) + (e : ℂ)) n = _
    simpa using h
  refine hcomplex.norm.congr ?_
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (criticalPrimeTailAtomWeight_nonneg n), Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

/-- Absolute Fubini gate for the assembled critical Green potential. -/
theorem summable_integral_norm_xiMassPositionSecond_mul_zeroGreenAtom
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Summable (fun n : DeningerPrimePowerIndex =>
      ∫ L : ℝ, ‖xiMassPrimeTailPositionProfileSecond a sigma u L *
        criticalPrimeTailZeroGreenAtom n L‖) := by
  let d : ℝ := (a + 1 / 2) / 2
  let e : ℝ := (d + 1 / 2) / 2
  let B : ℝ := ∫ L : ℝ, xiMassGlobalZeroGreenMajorant sigma d e u L
  have hd0 : 0 ≤ d := by dsimp only [d]; linarith
  have hda : d < a := by dsimp only [d]; linarith
  have hed : e < d := by dsimp only [e, d]; linarith
  have hehalf : 1 / 2 < e := by dsimp only [e, d]; linarith
  have he0 : 0 ≤ e := le_trans (by norm_num) hehalf.le
  have hBint := integrable_xiMassGlobalZeroGreenMajorant hsigma hed u
  have hB0 : 0 ≤ B := integral_nonneg fun L =>
    xiMassGlobalZeroGreenMajorant_nonneg hsigma hd0 u L
  have hcoef := summable_criticalPrimeTailAtomWeight_mul_exp_neg hehalf
  have hcoefB := hcoef.mul_right B
  apply Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _) _ hcoefB
  intro n
  have hFint := integrable_xiMassPositionSecond_mul_zeroGreenAtom
    (lt_trans (by norm_num) ha) hsigma u n
  have hmajor := norm_xiMassPositionSecond_mul_zeroGreenAtom_le
    hd0 hda hsigma he0 hed u n
  calc
    (∫ L : ℝ, ‖xiMassPrimeTailPositionProfileSecond a sigma u L *
        criticalPrimeTailZeroGreenAtom n L‖) ≤
      ∫ L : ℝ,
        (criticalPrimeTailAtomWeight n *
          Real.exp (-(e * deningerPrimePowerTime n))) *
          xiMassGlobalZeroGreenMajorant sigma d e u L := by
      apply integral_mono_ae hFint.norm
        (hBint.const_mul (criticalPrimeTailAtomWeight n *
          Real.exp (-(e * deningerPrimePowerTime n))))
      exact Filter.Eventually.of_forall hmajor
    _ = (criticalPrimeTailAtomWeight n *
          Real.exp (-(e * deningerPrimePowerTime n))) * B := by
      rw [MeasureTheory.integral_const_mul]

/-- **C41 global Green assembly.**  Atomwise Green pairings may be summed before integration. -/
theorem integral_xiMassPositionSecond_mul_zeroGreenPotential_eq_greenCurrent
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    (∫ L : ℝ, xiMassPrimeTailPositionProfileSecond a sigma u L *
      criticalPrimeTailZeroGreenPotential L) =
        xiMassCriticalPrimeTailGreenCurrent a sigma u := by
  let f : DeningerPrimePowerIndex → ℝ → ℂ := fun n L =>
    xiMassPrimeTailPositionProfileSecond a sigma u L *
      criticalPrimeTailZeroGreenAtom n L
  have hFint : ∀ n, Integrable (f n) := fun n =>
    integrable_xiMassPositionSecond_mul_zeroGreenAtom
      (lt_trans (by norm_num) ha) hsigma u n
  have hsum := summable_integral_norm_xiMassPositionSecond_mul_zeroGreenAtom ha hsigma u
  rw [show (fun L : ℝ => xiMassPrimeTailPositionProfileSecond a sigma u L *
      criticalPrimeTailZeroGreenPotential L) = fun L : ℝ => ∑' n, f n L by
    funext L
    rw [criticalPrimeTailZeroGreenPotential, tsum_mul_left]]
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hFint hsum]
  rfl

/-- Safe Euler integral is the negative pairing with one assembled causal Green potential. -/
theorem xiMassBottomPrimeIntegral_eq_neg_globalPrimeTailGreenPairing
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    xiMassBottomPrimeIntegral a c ((sigma : ℂ) + (u : ℂ) * I) =
      -(∫ L : ℝ, xiMassPrimeTailPositionProfileSecond a sigma u L *
        criticalPrimeTailZeroGreenPotential L) := by
  rw [integral_xiMassPositionSecond_mul_zeroGreenPotential_eq_greenCurrent
      (lt_trans hhalf hca) hsigma,
    xiMassBottomPrimeIntegral_eq_neg_primeTailGreenCurrent hhalf hca hsigma]

/-- RH is equivalent to boundedness of one literal global source Green--Stokes pairing. -/
theorem riemannHypothesis_iff_xiMassGlobalPrimeTailGreenPairingLineBound
    {a c sigma : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (hsigma : 0 < sigma) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
        ‖∫ L : ℝ, xiMassPrimeTailPositionProfileSecond a sigma u L *
          criticalPrimeTailZeroGreenPotential L‖ ≤ C := by
  rw [riemannHypothesis_iff_xiMassBottomPrimeIntegralLineBound hhalf hca hsigma]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u hu => by
      rw [← norm_neg,
        ← xiMassBottomPrimeIntegral_eq_neg_globalPrimeTailGreenPairing
          hhalf hca hsigma]
      exact hC u hu⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u hu => by
      rw [xiMassBottomPrimeIntegral_eq_neg_globalPrimeTailGreenPairing
          hhalf hca hsigma,
        norm_neg]
      exact hC u hu⟩

end

end RHTower
