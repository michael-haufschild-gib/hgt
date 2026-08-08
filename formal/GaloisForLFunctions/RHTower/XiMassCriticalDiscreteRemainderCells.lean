import GaloisForLFunctions.RHTower.XiMassCriticalDiscreteRemainderCone

/-!
# Exact logarithmic-cell atomization of the discrete critical Xi mass current

The outgoing operator is exactly the negative derivative of the exponentially damped mass Fourier
profile.  On each logarithmic cell `[log n, log (n+1))`, the raw remainder
`R(floor(exp h))` is constant.  The actual cell integral is therefore an adjacent boundary
difference, with the exceptional upper endpoint removed by its null measure.

Summing cells and applying finite Abel summation gives an exact second normal form: centered atoms
`Lambda(n)-1` paired with the damped mass profile, plus one terminal remainder flux.  This theorem
identifies the oscillatory discrete norm that a source proof must control; no approximation,
numerical computation, or remainder hypothesis is used.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Exponentially damped mass Fourier profile whose negative derivative is the outgoing kernel. -/
noncomputable def xiMassCriticalDampedFourierProfile (a sigma u h : ℝ) : ℂ :=
  (Real.exp (-h / 2) : ℂ) *
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)

/-- Exact differential factorization
`K'_u(h) = -exp(-h/2) * ((1/2)F_u(h)-F'_u(h))`. -/
theorem hasDerivAt_xiMassCriticalDampedFourierProfile
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u h : ℝ) :
    HasDerivAt (xiMassCriticalDampedFourierProfile a sigma u)
      (-((Real.exp (-h / 2) : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h)) h := by
  have hlin : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2 : ℝ) h := by
    simpa using (hasDerivAt_id h).neg.div_const (2 : ℝ)
  have hreal : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
      ((-1 / 2 : ℝ) * Real.exp (-h / 2)) h := by
    have hraw : HasDerivAt (Real.exp ∘ fun x : ℝ => -x / 2)
        ((-1 / 2 : ℝ) * Real.exp (-h / 2)) h :=
      ((Real.hasDerivAt_exp (-h / 2)).comp h hlin).congr_deriv (by ring_nf)
    apply hraw.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hw : HasDerivAt (fun x : ℝ => (Real.exp (-x / 2) : ℂ))
      ((-1 / 2 : ℂ) * (Real.exp (-h / 2) : ℂ)) h := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_one, Complex.ofReal_ofNat] using hreal.ofReal_comp
  have hF := hasDerivAt_xiMassRealFourierProfile ha hsigma u h
  have hprod := hw.mul hF
  change HasDerivAt (xiMassCriticalDampedFourierProfile a sigma u)
    (((-1 / 2 : ℂ) * (Real.exp (-h / 2) : ℂ)) *
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) +
      (Real.exp (-h / 2) : ℂ) * xiMassFourierDerivative a sigma u h) h at hprod
  refine hprod.congr_deriv ?_
  rw [xiMassCriticalOutgoingDerivative]
  ring_nf

/-- The exponential has natural floor `n` in the `n`th logarithmic cell. -/
theorem natFloor_exp_eq_of_log_mem {n : ℕ} (hn : 1 ≤ n) {h : ℝ}
    (hlow : Real.log (n : ℝ) ≤ h)
    (hhigh : h < Real.log ((n : ℝ) + 1)) :
    ⌊Real.exp h⌋₊ = n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply (Nat.floor_eq_iff (Real.exp_pos h).le).mpr
  constructor
  · rw [← Real.exp_log hnpos]
    exact Real.exp_le_exp.mpr hlow
  · rw [← Real.exp_log (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
    exact Real.exp_lt_exp.mpr hhigh

/-- Actual discrete-remainder current on one logarithmic cell. -/
noncomputable def xiMassCriticalDiscreteRemainderCellFlux
    (a sigma u : ℝ) (n : ℕ) : ℂ :=
  ∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
    xiMassCriticalDiscreteRemainderDensity a sigma u h

/-- Exact cell law: the raw remainder multiplies one adjacent damped-profile difference. -/
theorem xiMassCriticalDiscreteRemainderCellFlux_eq_boundaryDifference
    {a sigma u : ℝ} {n : ℕ}
    (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (hn : 1 ≤ n) :
    xiMassCriticalDiscreteRemainderCellFlux a sigma u n =
      (psiRemainder n : ℂ) *
        (xiMassCriticalDampedFourierProfile a sigma u (Real.log n) -
          xiMassCriticalDampedFourierProfile a sigma u
            (Real.log ((n : ℝ) + 1))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    exact Real.log_le_log hnpos (by linarith)
  have hcell : xiMassCriticalDiscreteRemainderCellFlux a sigma u n =
      ∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
        (psiRemainder n : ℂ) *
          ((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h) := by
    rw [xiMassCriticalDiscreteRemainderCellFlux]
    apply intervalIntegral.integral_congr_ae
    have hnull : (volume : Measure ℝ) {Real.log ((n : ℝ) + 1)} = 0 :=
      measure_singleton _
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (fun h hh => ?_) hnull
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hh
    obtain ⟨hmem, hne⟩ := hh
    rw [Set.uIoc_of_le hlogle, Set.mem_Ioc] at hmem
    rw [Set.mem_singleton_iff]
    by_contra hnot
    apply hne
    have hlt : h < Real.log ((n : ℝ) + 1) :=
      lt_of_le_of_ne hmem.2 hnot
    have hfloor := natFloor_exp_eq_of_log_mem hn hmem.1.le hlt
    rw [xiMassCriticalDiscreteRemainderDensity, hfloor]
    push_cast
    ring_nf
  rw [hcell]
  have hderiv : ∀ h ∈ Set.uIcc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)),
      HasDerivAt (xiMassCriticalDampedFourierProfile a sigma u)
        (-((Real.exp (-h / 2) : ℂ) *
          xiMassCriticalOutgoingDerivative a sigma u h)) h :=
    fun h _ => hasDerivAt_xiMassCriticalDampedFourierProfile
      (lt_trans (by norm_num) hhalf) hsigma u h
  have hcont : Continuous (fun h : ℝ =>
      -((Real.exp (-h / 2) : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h)) := by
    have hwcont : Continuous (fun h : ℝ => (Real.exp (-h / 2) : ℂ)) := by
      fun_prop
    exact (hwcont.mul (continuous_xiMassCriticalOutgoingDerivative
      (lt_trans (by norm_num) hhalf) hsigma u)).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)
  have hval : (∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
      ((Real.exp (-h / 2) : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h)) =
      xiMassCriticalDampedFourierProfile a sigma u (Real.log n) -
        xiMassCriticalDampedFourierProfile a sigma u
          (Real.log ((n : ℝ) + 1)) := by
    calc
      (∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          ((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h)) =
        -(∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          -((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h)) := by
          rw [intervalIntegral.integral_neg]
          ring_nf
      _ = -(xiMassCriticalDampedFourierProfile a sigma u
          (Real.log ((n : ℝ) + 1)) -
            xiMassCriticalDampedFourierProfile a sigma u (Real.log n)) := by
        rw [hFTC]
      _ = _ := by ring_nf
  calc
    (∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
        (psiRemainder n : ℂ) *
          ((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h)) =
      (psiRemainder n : ℂ) *
        ∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          ((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by rw [hval]

/-- A logarithmic prefix is the exact sum of its actual cell currents. -/
theorem integral_xiMassCriticalDiscreteRemainderDensity_eq_sum_cells
    {a sigma u : ℝ} (N : ℕ) (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) :
    (∫ h in (0 : ℝ)..Real.log ((N : ℝ) + 1),
      xiMassCriticalDiscreteRemainderDensity a sigma u h) =
      ∑ k ∈ Finset.range N,
        xiMassCriticalDiscreteRemainderCellFlux a sigma u (k + 1) := by
  let b : ℕ → ℝ := fun k => Real.log ((k : ℝ) + 1)
  have hfull := integrableOn_xiMassCriticalDiscreteRemainderDensity
    (a := a) (sigma := sigma) hhalf hsigma u
  have hadj : ∀ k < N, IntervalIntegrable
      (xiMassCriticalDiscreteRemainderDensity a sigma u) volume (b k) (b (k + 1)) := by
    intro k _hk
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle : b k ≤ b (k + 1) := by
      dsimp [b]
      apply Real.log_le_log hkpos
      push_cast
      linarith
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    apply hfull.mono_set
    intro h hh
    have hbnonneg : 0 ≤ b k := by
      apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    exact hbnonneg.trans_lt hh.1
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hadj
  have hb0 : b 0 = 0 := by simp [b]
  have hbN : b N = Real.log ((N : ℝ) + 1) := by rfl
  rw [hb0, hbN] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [xiMassCriticalDiscreteRemainderCellFlux]
  dsimp [b]
  push_cast
  rfl

/-- Boundary-difference form of every finite logarithmic prefix. -/
theorem integral_xiMassCriticalDiscreteRemainderDensity_eq_boundarySum
    {a sigma u : ℝ} (N : ℕ) (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) :
    (∫ h in (0 : ℝ)..Real.log ((N : ℝ) + 1),
      xiMassCriticalDiscreteRemainderDensity a sigma u h) =
      ∑ k ∈ Finset.range N,
        (psiRemainder (k + 1) : ℂ) *
          (xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 1)) -
            xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 2))) := by
  rw [integral_xiMassCriticalDiscreteRemainderDensity_eq_sum_cells N hhalf hsigma]
  apply Finset.sum_congr rfl
  intro k hk
  rw [xiMassCriticalDiscreteRemainderCellFlux_eq_boundaryDifference
    hhalf hsigma (by omega : 1 ≤ k + 1)]
  push_cast
  ring_nf

/-- Finite Abel identity for adjacent boundary differences. -/
theorem sum_range_mul_adjacent_sub (A K : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1),
      A (k + 1) * (K (k + 1) - K (k + 2))) =
      A 1 * K 1 +
        (∑ k ∈ Finset.range N, (A (k + 2) - A (k + 1)) * K (k + 2)) -
        A (N + 1) * K (N + 2) := by
  induction N with
  | zero =>
      simp
      ring_nf
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring_nf

theorem psiRemainder_one : psiRemainder 1 = -1 := by
  rw [psiRemainder, chebyshevPsi]
  norm_num [ArithmeticFunction.vonMangoldt]

/-- **Centered-atom normal form.**  Every finite current prefix is an exact sum of
`Lambda(n)-1` mass atoms, with initial and terminal boundary fluxes. -/
theorem integral_xiMassCriticalDiscreteRemainderDensity_eq_centeredAtoms
    {a sigma u : ℝ} (N : ℕ) (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) :
    (∫ h in (0 : ℝ)..Real.log ((N : ℝ) + 2),
      xiMassCriticalDiscreteRemainderDensity a sigma u h) =
      -xiMassCriticalDampedFourierProfile a sigma u 0 +
        (∑ k ∈ Finset.range N,
          ((ArithmeticFunction.vonMangoldt (k + 2) - 1 : ℝ) : ℂ) *
            xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 2))) -
        (psiRemainder (N + 1) : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u
            (Real.log ((N : ℝ) + 2)) := by
  have hprefix := integral_xiMassCriticalDiscreteRemainderDensity_eq_boundarySum
    (u := u) (N + 1) hhalf hsigma
  push_cast at hprefix
  rw [show ((N : ℝ) + 1 + 1) = (N : ℝ) + 2 by ring_nf] at hprefix
  rw [hprefix]
  let A : ℕ → ℂ := fun n => (psiRemainder n : ℂ)
  let K : ℕ → ℂ := fun n =>
    xiMassCriticalDampedFourierProfile a sigma u (Real.log (n : ℝ))
  have hAbel := sum_range_mul_adjacent_sub A K N
  have hsumform :
      (∑ k ∈ Finset.range (N + 1),
        (psiRemainder (k + 1) : ℂ) *
          (xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 1)) -
            xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 2)))) =
      (psiRemainder 1 : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u (Real.log 1) +
        (∑ k ∈ Finset.range N,
          ((psiRemainder (k + 2) : ℂ) - (psiRemainder (k + 1) : ℂ)) *
            xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 2))) -
        (psiRemainder (N + 1) : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u
            (Real.log ((N : ℝ) + 2)) := by
    dsimp only [A, K] at hAbel
    push_cast at hAbel
    simpa only [Nat.cast_one] using hAbel
  rw [hsumform, psiRemainder_one]
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
    Real.log_one]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  have hstep := psiRemainder_succ_sub (k + 1)
  have hstepC := congrArg (fun x : ℝ => (x : ℂ)) hstep
  push_cast at hstepC
  have hkadd : k + 1 + 1 = k + 2 := by omega
  rw [hkadd] at hstepC
  rw [hstepC]
  push_cast
  ring_nf

end


end RHTower
