import GaloisForLFunctions.RHTower.XiMassCriticalCenteredAtomCone

/-!
# Exact bounded integer face and sparse prime cone

Logarithmic-cell FTC separates the deterministic counting-measure face from the
centered `Λ - 1` cone.  The dense integer face is an exact sum of a half-weighted
polar integral, the floor sawtooth, and one damped endpoint.  Analytic strip
shift bounds all three uniformly on the moving supercritical cone.  Hence the
centered open core is equivalent, without loss, to a genuinely prime-power-
supported `Λ` cone.

Every integral is an actual Bochner or interval integral.  No numerical
computation, asymptotic hypothesis, or admitted source estimate is used.
-/

open Complex Filter MeasureTheory Set Topology

namespace RHTower

noncomputable section

noncomputable def xiMassCriticalIntegerDensity
    (a sigma u h : ℝ) : ℂ :=
  ((Real.exp (-h / 2) * (⌊Real.exp h⌋₊ : ℝ) : ℝ) : ℂ) *
    xiMassCriticalOutgoingDerivative a sigma u h

theorem xiMassCriticalIntegerDensity_eq_main_add_floor
    (a sigma u h : ℝ) :
    xiMassCriticalIntegerDensity a sigma u h =
      (Real.exp (h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h +
        xiMassCriticalFloorSawtoothDensity a sigma u h := by
  rw [xiMassCriticalIntegerDensity,
    xiMassCriticalFloorSawtoothDensity]
  have hexp : Real.exp (-h / 2) * Real.exp h = Real.exp (h / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcoef :
      ((Real.exp (-h / 2) * (⌊Real.exp h⌋₊ : ℝ) : ℝ) : ℂ) =
        (Real.exp (h / 2) : ℂ) +
          ((Real.exp (-h / 2) *
            ((⌊Real.exp h⌋₊ : ℝ) - Real.exp h) : ℝ) : ℂ) := by
    exact_mod_cast (show
      Real.exp (-h / 2) * (⌊Real.exp h⌋₊ : ℝ) =
        Real.exp (h / 2) + Real.exp (-h / 2) *
          ((⌊Real.exp h⌋₊ : ℝ) - Real.exp h) by rw [← hexp]; ring)
  rw [hcoef]
  ring

noncomputable def xiMassCriticalIntegerCellFlux
    (a sigma u : ℝ) (n : ℕ) : ℂ :=
  ∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
    xiMassCriticalIntegerDensity a sigma u h

theorem xiMassCriticalIntegerCellFlux_eq_boundaryDifference
    {a sigma u : ℝ} {n : ℕ}
    (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (hn : 1 ≤ n) :
    xiMassCriticalIntegerCellFlux a sigma u n =
      (n : ℂ) *
        (xiMassCriticalDampedFourierProfile a sigma u (Real.log n) -
          xiMassCriticalDampedFourierProfile a sigma u
            (Real.log ((n : ℝ) + 1))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    exact Real.log_le_log hnpos (by linarith)
  have hcell : xiMassCriticalIntegerCellFlux a sigma u n =
      ∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
        (n : ℂ) *
          ((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h) := by
    rw [xiMassCriticalIntegerCellFlux]
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
    rw [xiMassCriticalIntegerDensity, hfloor]
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
        (n : ℂ) *
          ((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h)) =
      (n : ℂ) *
        ∫ h in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1),
          ((Real.exp (-h / 2) : ℂ) *
            xiMassCriticalOutgoingDerivative a sigma u h) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by rw [hval]

theorem integral_xiMassCriticalIntegerDensity_eq_sum_cells
    {a sigma u : ℝ} (N : ℕ) (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) :
    (∫ h in (0 : ℝ)..Real.log ((N : ℝ) + 1),
      xiMassCriticalIntegerDensity a sigma u h) =
      ∑ k ∈ Finset.range N,
        xiMassCriticalIntegerCellFlux a sigma u (k + 1) := by
  let b : ℕ → ℝ := fun k => Real.log ((k : ℝ) + 1)
  have hadj : ∀ k < N, IntervalIntegrable
      (xiMassCriticalIntegerDensity a sigma u) volume (b k) (b (k + 1)) := by
    intro k _hk
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle : b k ≤ b (k + 1) := by
      dsimp [b]
      apply Real.log_le_log hkpos
      push_cast
      linarith
    have hmain : IntervalIntegrable
        (fun h : ℝ => (Real.exp (h / 2) : ℂ) *
          xiMassCriticalOutgoingDerivative a sigma u h) volume (b k) (b (k + 1)) := by
      exact ((by fun_prop : Continuous (fun h : ℝ => (Real.exp (h / 2) : ℂ))).mul
        (continuous_xiMassCriticalOutgoingDerivative
          (lt_trans (by norm_num) hhalf) hsigma u)).intervalIntegrable _ _
    have hfloor : IntervalIntegrable
        (xiMassCriticalFloorSawtoothDensity a sigma u) volume (b k) (b (k + 1)) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      have hfull := integrableOn_xiMassCriticalFloorSawtoothDensity
        (lt_trans (by norm_num) hhalf) hsigma u
      apply hfull.mono_set
      intro h hh
      have hbnonneg : 0 ≤ b k := by
        apply Real.log_nonneg
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      exact hbnonneg.trans_lt hh.1
    have hadd := hmain.add hfloor
    refine hadd.congr ?_
    intro h hh
    exact (xiMassCriticalIntegerDensity_eq_main_add_floor a sigma u h).symm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hadj
  have hb0 : b 0 = 0 := by simp [b]
  have hbN : b N = Real.log ((N : ℝ) + 1) := by rfl
  rw [hb0, hbN] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [xiMassCriticalIntegerCellFlux]
  dsimp [b]
  push_cast
  rfl

noncomputable def xiMassCriticalIntegerAtomSum
    (a sigma u : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N,
    xiMassCriticalDampedFourierProfile a sigma u (Real.log ((k : ℝ) + 2))

theorem integral_xiMassCriticalIntegerDensity_eq_atoms
    {a sigma u : ℝ} (N : ℕ) (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) :
    (∫ h in (0 : ℝ)..Real.log ((N : ℝ) + 2),
      xiMassCriticalIntegerDensity a sigma u h) =
      xiMassCriticalDampedFourierProfile a sigma u 0 +
        xiMassCriticalIntegerAtomSum a sigma u N -
        ((N + 1 : ℕ) : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u
            (Real.log ((N : ℝ) + 2)) := by
  have hprefix := integral_xiMassCriticalIntegerDensity_eq_sum_cells
    (a := a) (sigma := sigma) (u := u) (N + 1) hhalf hsigma
  push_cast at hprefix
  rw [show ((N : ℝ) + 1 + 1) = (N : ℝ) + 2 by ring_nf] at hprefix
  rw [hprefix]
  let A : ℕ → ℂ := fun n => (n : ℂ)
  let K : ℕ → ℂ := fun n =>
    xiMassCriticalDampedFourierProfile a sigma u (Real.log (n : ℝ))
  have hAbel := sum_range_mul_adjacent_sub A K N
  have hdiffsum :
      (∑ k ∈ Finset.range N,
        ((k : ℂ) + 2 - ((k : ℂ) + 1)) *
          xiMassCriticalDampedFourierProfile a sigma u
            (Real.log ((k : ℝ) + 2))) =
        xiMassCriticalIntegerAtomSum a sigma u N := by
    rw [xiMassCriticalIntegerAtomSum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hsumform :
      (∑ k ∈ Finset.range (N + 1),
        ((k + 1 : ℕ) : ℂ) *
          (xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 1)) -
            xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 2)))) =
      xiMassCriticalDampedFourierProfile a sigma u 0 +
        xiMassCriticalIntegerAtomSum a sigma u N -
        ((N + 1 : ℕ) : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u
            (Real.log ((N : ℝ) + 2)) := by
    dsimp only [A, K] at hAbel
    push_cast at hAbel
    rw [show Real.log (1 : ℝ) = 0 by norm_num] at hAbel
    rw [hdiffsum] at hAbel
    simpa only [one_mul, Nat.cast_add, Nat.cast_one] using hAbel
  rw [show (∑ k ∈ Finset.range (N + 1),
        xiMassCriticalIntegerCellFlux a sigma u (k + 1)) =
      ∑ k ∈ Finset.range (N + 1),
        ((k + 1 : ℕ) : ℂ) *
          (xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 1)) -
            xiMassCriticalDampedFourierProfile a sigma u
              (Real.log ((k : ℝ) + 2))) by
    apply Finset.sum_congr rfl
    intro k hk
    rw [xiMassCriticalIntegerCellFlux_eq_boundaryDifference
      hhalf hsigma (by omega : 1 ≤ k + 1)]
    push_cast
    ring_nf]
  exact hsumform

noncomputable def xiMassCriticalGrowingFourierProfile
    (a sigma u h : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) *
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)

theorem hasDerivAt_xiMassCriticalGrowingFourierProfile
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u h : ℝ) :
    HasDerivAt (xiMassCriticalGrowingFourierProfile a sigma u)
      ((Real.exp (h / 2) : ℂ) *
        ((1 / 2 : ℂ) *
          stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) +
          xiMassFourierDerivative a sigma u h)) h := by
  have hlin : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) h := by
    simpa using (hasDerivAt_id h).div_const (2 : ℝ)
  have hreal : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
      ((1 / 2 : ℝ) * Real.exp (h / 2)) h := by
    have hraw : HasDerivAt (Real.exp ∘ fun x : ℝ => x / 2)
        ((1 / 2 : ℝ) * Real.exp (h / 2)) h :=
      ((Real.hasDerivAt_exp (h / 2)).comp h hlin).congr_deriv (by ring_nf)
    apply hraw.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hw : HasDerivAt (fun x : ℝ => (Real.exp (x / 2) : ℂ))
      ((1 / 2 : ℂ) * (Real.exp (h / 2) : ℂ)) h := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using hreal.ofReal_comp
  have hF := hasDerivAt_xiMassRealFourierProfile ha hsigma u h
  have hprod := hw.mul hF
  change HasDerivAt (xiMassCriticalGrowingFourierProfile a sigma u)
    (((1 / 2 : ℂ) * (Real.exp (h / 2) : ℂ)) *
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) +
      (Real.exp (h / 2) : ℂ) * xiMassFourierDerivative a sigma u h) h at hprod
  refine hprod.congr_deriv ?_
  ring

theorem integral_xiMassCriticalHalfWeightedOutgoing_eq
    {a sigma : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (u w : ℝ) :
    (∫ h in (0 : ℝ)..w,
      (Real.exp (h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h) =
      (∫ h in (0 : ℝ)..w,
        xiMassCriticalGrowingFourierProfile a sigma u h) -
        xiMassCriticalGrowingFourierProfile a sigma u w +
        xiMassCriticalGrowingFourierProfile a sigma u 0 := by
  let G : ℝ → ℂ := xiMassCriticalGrowingFourierProfile a sigma u
  let G' : ℝ → ℂ := fun h =>
    (Real.exp (h / 2) : ℂ) *
      ((1 / 2 : ℂ) *
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) +
        xiMassFourierDerivative a sigma u h)
  have hderiv : ∀ h ∈ Set.uIcc (0 : ℝ) w, HasDerivAt G (G' h) h :=
    fun h _ => hasDerivAt_xiMassCriticalGrowingFourierProfile ha hsigma u h
  have hG'cont : Continuous G' := by
    dsimp only [G']
    have hwcont : Continuous (fun h : ℝ => (Real.exp (h / 2) : ℂ)) := by fun_prop
    have hFcont : Continuous (fun h : ℝ =>
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro h
      exact (hasDerivAt_xiMassRealFourierProfile ha hsigma u h).continuousAt
    exact hwcont.mul ((hFcont.const_mul _).add
      (continuous_xiMassFourierDerivative ha hsigma u))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hG'cont.intervalIntegrable _ _)
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassCriticalGrowingFourierProfile
      ha hsigma u h).continuousAt
  have hpoint : ∀ h : ℝ,
      (Real.exp (h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h =
        G h - G' h := by
    intro h
    rw [xiMassCriticalOutgoingDerivative]
    dsimp only [G, G', xiMassCriticalGrowingFourierProfile]
    ring
  calc
    (∫ h in (0 : ℝ)..w,
      (Real.exp (h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h) =
        ∫ h in (0 : ℝ)..w, (G h - G' h) := by
      apply intervalIntegral.integral_congr
      intro h hh
      exact hpoint h
    _ = (∫ h in (0 : ℝ)..w, G h) - ∫ h in (0 : ℝ)..w, G' h := by
      rw [intervalIntegral.integral_sub
        (hGcont.intervalIntegrable _ _) (hG'cont.intervalIntegrable _ _)]
    _ = (∫ h in (0 : ℝ)..w, G h) - (G w - G 0) := by rw [hFTC]
    _ = _ := by dsimp only [G]; ring

theorem xiMassCriticalIntegerAtomSum_eq_integral
    {a sigma u : ℝ} (N : ℕ) (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) :
    let w := Real.log ((N : ℝ) + 2)
    xiMassCriticalIntegerAtomSum a sigma u N =
      (∫ h in (0 : ℝ)..w,
        xiMassCriticalGrowingFourierProfile a sigma u h) +
      (∫ h in (0 : ℝ)..w,
        xiMassCriticalFloorSawtoothDensity a sigma u h) -
      xiMassCriticalDampedFourierProfile a sigma u w := by
  dsimp only
  let w : ℝ := Real.log ((N : ℝ) + 2)
  change xiMassCriticalIntegerAtomSum a sigma u N =
      (∫ h in (0 : ℝ)..w,
        xiMassCriticalGrowingFourierProfile a sigma u h) +
      (∫ h in (0 : ℝ)..w,
        xiMassCriticalFloorSawtoothDensity a sigma u h) -
      xiMassCriticalDampedFourierProfile a sigma u w
  have hwpos : 0 < w := Real.log_pos (by
    exact_mod_cast (show 1 < N + 2 by omega))
  have hmain := integral_xiMassCriticalHalfWeightedOutgoing_eq
    (lt_trans (by norm_num) hhalf) hsigma u w
  have hmainInt : IntervalIntegrable
      (fun h : ℝ => (Real.exp (h / 2) : ℂ) *
        xiMassCriticalOutgoingDerivative a sigma u h) volume 0 w := by
    exact ((by fun_prop : Continuous (fun h : ℝ => (Real.exp (h / 2) : ℂ))).mul
      (continuous_xiMassCriticalOutgoingDerivative
        (lt_trans (by norm_num) hhalf) hsigma u)).intervalIntegrable _ _
  have hfloorInt : IntervalIntegrable
      (xiMassCriticalFloorSawtoothDensity a sigma u) volume 0 w := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hwpos.le]
    exact (integrableOn_xiMassCriticalFloorSawtoothDensity
      (lt_trans (by norm_num) hhalf) hsigma u).mono_set (Ioc_subset_Ioi_self)
  have hsplit :
      (∫ h in (0 : ℝ)..w, xiMassCriticalIntegerDensity a sigma u h) =
        (∫ h in (0 : ℝ)..w,
          (Real.exp (h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h) +
        ∫ h in (0 : ℝ)..w,
          xiMassCriticalFloorSawtoothDensity a sigma u h := by
    calc
      _ = ∫ h in (0 : ℝ)..w,
          ((Real.exp (h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h +
            xiMassCriticalFloorSawtoothDensity a sigma u h) := by
        apply intervalIntegral.integral_congr
        intro h hh
        exact xiMassCriticalIntegerDensity_eq_main_add_floor a sigma u h
      _ = _ := by rw [intervalIntegral.integral_add hmainInt hfloorInt]
  have hatom := integral_xiMassCriticalIntegerDensity_eq_atoms
    (a := a) (sigma := sigma) (u := u) N hhalf hsigma
  change (∫ h in (0 : ℝ)..w,
      xiMassCriticalIntegerDensity a sigma u h) =
        xiMassCriticalDampedFourierProfile a sigma u 0 +
          xiMassCriticalIntegerAtomSum a sigma u N -
          ((N + 1 : ℕ) : ℂ) *
            xiMassCriticalDampedFourierProfile a sigma u w at hatom
  have hzero :
      xiMassCriticalGrowingFourierProfile a sigma u 0 =
        xiMassCriticalDampedFourierProfile a sigma u 0 := by
    rw [xiMassCriticalGrowingFourierProfile,
      xiMassCriticalDampedFourierProfile]
    norm_num
  have hexpw : Real.exp w = (N : ℝ) + 2 := by
    dsimp only [w]
    rw [Real.exp_log (by positivity : (0 : ℝ) < (N : ℝ) + 2)]
  have hscale : ((N : ℝ) + 2) * Real.exp (-w / 2) = Real.exp (w / 2) := by
    rw [← hexpw, ← Real.exp_add]
    congr 1
    ring
  have hterminal :
      ((N + 1 : ℕ) : ℂ) *
          xiMassCriticalDampedFourierProfile a sigma u w -
        xiMassCriticalGrowingFourierProfile a sigma u w =
      -xiMassCriticalDampedFourierProfile a sigma u w := by
    rw [xiMassCriticalDampedFourierProfile,
      xiMassCriticalGrowingFourierProfile]
    have hscaleC : (((N : ℝ) + 2 : ℝ) : ℂ) *
        (Real.exp (-w / 2) : ℂ) = (Real.exp (w / 2) : ℂ) := by
      exact_mod_cast hscale
    push_cast at hscaleC ⊢
    rw [← hscaleC]
    ring
  rw [hsplit, hmain] at hatom
  rw [hzero] at hatom
  have hsolve := hatom
  linear_combination -hsolve + hterminal

theorem norm_xiMassPolarTail_at_cone_le
    {a sigma d u w : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    (hu : 0 ≤ u)
    (hw : d * u / (d - 1 / 2) ≤ w) :
    ‖∫ h in Ioi w,
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) *
          (2 * Real.cosh (h / 2) : ℂ)‖ ≤
      2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  let delta : ℝ := d - 1 / 2
  let b : ℝ := 1 / 2 - d
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hb : b < 0 := by dsimp [b]; linarith
  have hJ : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
  have hH0 : 0 ≤ d * u / (d - 1 / 2) := by positivity
  have hw0 : 0 ≤ w := hH0.trans hw
  let Q : ℝ → ℂ := fun h =>
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) *
      (2 * Real.cosh (h / 2) : ℂ)
  have hleft : IntegrableOn (fun h => ‖Q h‖) (Ioi w) := by
    have hfull := integrableOn_xiMassPolarKernel
      (lt_trans hdhalf hda) hsigma u
    exact ((hfull.mono_set (Ioi_subset_Ioi hw0)).norm)
  have hright : IntegrableOn
      (fun h : ℝ => (2 * J * Real.exp (d * u)) * Real.exp (b * h)) (Ioi w) :=
    (integrableOn_exp_mul_Ioi hb w).const_mul _
  have hpoint : ∀ h ∈ Ioi w,
      ‖Q h‖ ≤ (2 * J * Real.exp (d * u)) * Real.exp (b * h) := by
    intro h hh
    have hh0 : 0 ≤ h := hw0.trans hh.le
    have hF := norm_stripFourier_xiMass_deepShift_le
      (a := a) (σ := sigma) (d := d) (by linarith) hda hsigma u h
    rw [abs_of_nonneg hu] at hF
    have hcosh0 : 0 ≤ 2 * Real.cosh (h / 2) := by positivity
    have hcosh : 2 * Real.cosh (h / 2) ≤ 2 * Real.exp (h / 2) := by
      rw [Real.cosh_eq]
      have hexp := Real.exp_le_exp.mpr (show -(h / 2) ≤ h / 2 by linarith)
      linarith
    have hnormcosh : ‖(2 * Real.cosh (h / 2) : ℂ)‖ =
        2 * Real.cosh (h / 2) := by
      calc
        ‖(2 : ℂ) * (Real.cosh (h / 2) : ℂ)‖ =
            ‖(2 : ℂ)‖ * ‖(Real.cosh (h / 2) : ℂ)‖ := norm_mul _ _
        _ = 2 * |Real.cosh (h / 2)| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          norm_num
        _ = 2 * Real.cosh (h / 2) := by
          rw [abs_of_nonneg (by positivity)]
    dsimp only [Q]
    rw [norm_mul, hnormcosh]
    calc
      ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * I)) (h : ℂ)‖ *
          (2 * Real.cosh (h / 2)) ≤
        (Real.exp (u * d - h * d) * J) * (2 * Real.exp (h / 2)) :=
          mul_le_mul (by simpa only [J] using hF) hcosh
            (by positivity) (mul_nonneg (Real.exp_nonneg _) hJ)
      _ = (2 * J * Real.exp (d * u)) * Real.exp (b * h) := by
        rw [show (Real.exp (u * d - h * d) * J) * (2 * Real.exp (h / 2)) =
            2 * J * (Real.exp (u * d - h * d) * Real.exp (h / 2)) by ring,
          show (2 * J * Real.exp (d * u)) * Real.exp (b * h) =
            2 * J * (Real.exp (d * u) * Real.exp (b * h)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        dsimp only [b]
        congr 1
        ring
  have hmono :
      (∫ h in Ioi w, ‖Q h‖) ≤
        ∫ h in Ioi w, (2 * J * Real.exp (d * u)) * Real.exp (b * h) := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    exact hpoint h hh
  have hexponent : d * u + b * w ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hw hdelta.le
    dsimp only [delta] at hmul
    have hcancel : (d - 1 / 2) * (d * u / (d - 1 / 2)) = d * u := by
      have hne : d - 1 / 2 ≠ 0 := ne_of_gt hdelta
      calc
        (d - 1 / 2) * (d * u / (d - 1 / 2)) =
            (d * u / (d - 1 / 2)) * (d - 1 / 2) := by ring
        _ = d * u := div_mul_cancel₀ _ hne
    rw [hcancel] at hmul
    dsimp only [b]
    linarith
  calc
    ‖∫ h in Ioi w, Q h‖ ≤ ∫ h in Ioi w, ‖Q h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi w,
        (2 * J * Real.exp (d * u)) * Real.exp (b * h) := hmono
    _ = (2 * J * Real.exp (d * u)) * (-Real.exp (b * w) / b) := by
      rw [integral_const_mul, integral_exp_mul_Ioi hb w]
    _ = (2 * J / delta) * Real.exp (d * u + b * w) := by
      have hbdelta : b = -delta := by dsimp [b, delta]; ring
      rw [hbdelta, show -Real.exp (-delta * w) / -delta =
          Real.exp (-delta * w) / delta by ring]
      rw [show (2 * J * Real.exp (d * u)) *
          (Real.exp (-delta * w) / delta) =
        (2 * J / delta) * (Real.exp (d * u) * Real.exp (-delta * w)) by ring]
      rw [← Real.exp_add]
    _ ≤ 2 * J / delta := by
      have hcoef : 0 ≤ 2 * J / delta := div_nonneg (mul_nonneg (by norm_num) hJ) hdelta.le
      have hexp : Real.exp (d * u + b * w) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hexponent
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hcoef
    _ = 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) := by rfl

theorem norm_xiMassPolarPartialSource_at_cone_le
    {a sigma d u w : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    (hu : 0 ≤ u)
    (hw : d * u / (d - 1 / 2) ≤ w) :
    ‖xiMassPolarPartialSource a sigma u w‖ ≤
      2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) := by
  let Q : ℝ → ℂ := fun h =>
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) *
      (2 * Real.cosh (h / 2) : ℂ)
  have hH0 : 0 ≤ d * u / (d - 1 / 2) := by positivity
  have hw0 : 0 ≤ w := hH0.trans hw
  have hfull : IntegrableOn Q (Ioi 0) := by
    simpa only [Q] using integrableOn_xiMassPolarKernel
      (lt_trans hdhalf hda) hsigma u
  have hhead : IntegrableOn Q (Ioc 0 w) :=
    hfull.mono_set Ioc_subset_Ioi_self
  have htail : IntegrableOn Q (Ioi w) :=
    hfull.mono_set (Ioi_subset_Ioi hw0)
  have hsplit :
      (∫ h in Ioi (0 : ℝ), Q h) =
        (∫ h in Ioc (0 : ℝ) w, Q h) + ∫ h in Ioi w, Q h := by
    rw [← Ioc_union_Ioi_eq_Ioi hw0,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hhead htail]
  have hfullNorm : ‖∫ h in Ioi (0 : ℝ), Q h‖ ≤ 2 * Real.pi := by
    have heq := norm_integral_xiMassPolarInfinite_eq
      (lt_trans hdhalf hda) hsigma u
    change ‖∫ h in Ioi (0 : ℝ), Q h‖ = _ at heq
    rw [heq]
    have hfreq := xiMassArchPoleFrequency_pos (lt_trans hdhalf hda)
    have hexp : Real.exp (-sigma * xiMassArchPoleFrequency a) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsigma.le) hfreq.le
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2 * Real.pi by positivity)
  have htailNorm := norm_xiMassPolarTail_at_cone_le
    hdhalf hda hsigma hu hw
  rw [xiMassPolarPartialSource]
  have hheadEq : (∫ h in Ioc (0 : ℝ) w, Q h) =
      (∫ h in Ioi (0 : ℝ), Q h) - ∫ h in Ioi w, Q h := by
    calc
      (∫ h in Ioc (0 : ℝ) w, Q h) =
          ((∫ h in Ioc (0 : ℝ) w, Q h) + ∫ h in Ioi w, Q h) -
            ∫ h in Ioi w, Q h := by ring
      _ = (∫ h in Ioi (0 : ℝ), Q h) - ∫ h in Ioi w, Q h := by rw [hsplit]
  change ‖∫ h in Ioc (0 : ℝ) w, Q h‖ ≤ _
  rw [hheadEq]
  calc
    ‖(∫ h in Ioi (0 : ℝ), Q h) - ∫ h in Ioi w, Q h‖ ≤
        ‖∫ h in Ioi (0 : ℝ), Q h‖ + ‖∫ h in Ioi w, Q h‖ := norm_sub_le _ _
    _ ≤ 2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) :=
      add_le_add hfullNorm htailNorm

theorem norm_integral_xiMassCriticalDampedFourierProfile_le
    {a sigma u w : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (hw : 0 ≤ w) :
    ‖∫ h in (0 : ℝ)..w, xiMassCriticalDampedFourierProfile a sigma u h‖ ≤
      2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  let K : ℝ → ℂ := xiMassCriticalDampedFourierProfile a sigma u
  let B : ℝ → ℝ := fun h => J * Real.exp ((-1 / 2 : ℝ) * h)
  have hJ : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
  have hKcont : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassCriticalDampedFourierProfile ha hsigma u h).continuousAt
  have hKint : IntervalIntegrable K volume 0 w := hKcont.intervalIntegrable _ _
  have hleft : IntegrableOn (fun h => ‖K h‖) (Ioc 0 w) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hw]
    exact hKint.norm
  have hrightFull : IntegrableOn B (Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0).const_mul J
  have hright : IntegrableOn B (Ioc 0 w) :=
    hrightFull.mono_set Ioc_subset_Ioi_self
  have hpoint : ∀ h ∈ Ioc (0 : ℝ) w, ‖K h‖ ≤ B h := by
    intro h hh
    have hF := norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u h
    dsimp only [K, B]
    rw [xiMassCriticalDampedFourierProfile, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-h / 2) *
          ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * I)) (h : ℂ)‖ ≤
        Real.exp (-h / 2) * J :=
          mul_le_mul_of_nonneg_left (by simpa only [J] using hF) (Real.exp_nonneg _)
      _ = J * Real.exp ((-1 / 2 : ℝ) * h) := by ring
  have hmono : (∫ h in Ioc (0 : ℝ) w, ‖K h‖) ≤ ∫ h in Ioc (0 : ℝ) w, B h := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    exact hpoint h hh
  have hsetmono : (∫ h in Ioc (0 : ℝ) w, B h) ≤ ∫ h in Ioi (0 : ℝ), B h := by
    apply setIntegral_mono_set hrightFull
    · exact Filter.Eventually.of_forall fun h => mul_nonneg hJ (Real.exp_nonneg _)
    · exact Filter.Eventually.of_forall fun h hh => hh.1
  calc
    ‖∫ h in (0 : ℝ)..w, K h‖ ≤ ∫ h in (0 : ℝ)..w, ‖K h‖ :=
      intervalIntegral.norm_integral_le_integral_norm hw
    _ = ∫ h in Ioc (0 : ℝ) w, ‖K h‖ := by
      rw [intervalIntegral.integral_of_le hw]
    _ ≤ ∫ h in Ioc (0 : ℝ) w, B h := hmono
    _ ≤ ∫ h in Ioi (0 : ℝ), B h := hsetmono
    _ = J * 2 := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0]
      norm_num [B]
    _ = 2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by dsimp [J]; ring

theorem norm_integral_xiMassCriticalFloorSawtoothDensity_le
    {a sigma u w : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (hw : 0 ≤ w) :
    ‖∫ h in (0 : ℝ)..w, xiMassCriticalFloorSawtoothDensity a sigma u h‖ ≤
      2 * xiMassCriticalOutgoingZeroShiftBound sigma := by
  let J : ℝ := xiMassCriticalOutgoingZeroShiftBound sigma
  let Q : ℝ → ℂ := xiMassCriticalFloorSawtoothDensity a sigma u
  let B : ℝ → ℝ := fun h => J * Real.exp ((-1 / 2 : ℝ) * h)
  have hJ : 0 ≤ J := xiMassCriticalOutgoingZeroShiftBound_nonneg sigma
  have hleftFull : IntegrableOn (fun h => ‖Q h‖) (Ioi 0) :=
    (integrableOn_xiMassCriticalFloorSawtoothDensity ha hsigma u).norm
  have hleft : IntegrableOn (fun h => ‖Q h‖) (Ioc 0 w) :=
    hleftFull.mono_set Ioc_subset_Ioi_self
  have hrightFull : IntegrableOn B (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0).const_mul J
  have hright : IntegrableOn B (Ioc 0 w) :=
    hrightFull.mono_set Ioc_subset_Ioi_self
  have hpoint : ∀ h ∈ Ioc (0 : ℝ) w, ‖Q h‖ ≤ B h := by
    intro h hh
    dsimp only [Q, B]
    rw [xiMassCriticalFloorSawtoothDensity, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hfloor := abs_natFloor_exp_sub_le_one h
    have hD := norm_xiMassCriticalOutgoingDerivative_le_zeroShift ha hsigma u h
    calc
      Real.exp (-h / 2) * |(⌊Real.exp h⌋₊ : ℝ) - Real.exp h| *
          ‖xiMassCriticalOutgoingDerivative a sigma u h‖ ≤
        Real.exp (-h / 2) * 1 *
          ‖xiMassCriticalOutgoingDerivative a sigma u h‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfloor (Real.exp_pos _).le) (norm_nonneg _)
      _ ≤ Real.exp (-h / 2) * 1 * J :=
        mul_le_mul_of_nonneg_left (by simpa only [J] using hD)
          (mul_nonneg (Real.exp_pos _).le zero_le_one)
      _ = J * Real.exp ((-1 / 2 : ℝ) * h) := by ring
  have hmono : (∫ h in Ioc (0 : ℝ) w, ‖Q h‖) ≤ ∫ h in Ioc (0 : ℝ) w, B h := by
    apply integral_mono_ae hleft hright
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    exact hpoint h hh
  have hsetmono : (∫ h in Ioc (0 : ℝ) w, B h) ≤ ∫ h in Ioi (0 : ℝ), B h := by
    apply setIntegral_mono_set hrightFull
    · exact Filter.Eventually.of_forall fun h => mul_nonneg hJ (Real.exp_nonneg _)
    · exact Filter.Eventually.of_forall fun h hh => hh.1
  have hQint : IntervalIntegrable Q volume 0 w := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hw]
    exact (integrableOn_xiMassCriticalFloorSawtoothDensity ha hsigma u).mono_set
      Ioc_subset_Ioi_self
  calc
    ‖∫ h in (0 : ℝ)..w, Q h‖ ≤ ∫ h in (0 : ℝ)..w, ‖Q h‖ :=
      intervalIntegral.norm_integral_le_integral_norm hw
    _ = ∫ h in Ioc (0 : ℝ) w, ‖Q h‖ := by
      rw [intervalIntegral.integral_of_le hw]
    _ ≤ ∫ h in Ioc (0 : ℝ) w, B h := hmono
    _ ≤ ∫ h in Ioi (0 : ℝ), B h := hsetmono
    _ = J * 2 := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 0]
      norm_num [B]
    _ = 2 * xiMassCriticalOutgoingZeroShiftBound sigma := by dsimp [J]; ring

theorem norm_xiMassCriticalDampedFourierProfile_le
    {a sigma u w : ℝ} (ha : 0 < a) (hsigma : 0 < sigma) (hw : 0 ≤ w) :
    ‖xiMassCriticalDampedFourierProfile a sigma u w‖ ≤
      ∫ x : ℝ, Real.exp (-(sigma * |x|)) := by
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have hF := norm_stripFourier_xiMassAnalyticTest_vertical_le ha hsigma u w
  rw [xiMassCriticalDampedFourierProfile, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-w / 2) *
        ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ↑u * I)) (w : ℂ)‖ ≤
      Real.exp (-w / 2) * J :=
        mul_le_mul_of_nonneg_left (by simpa only [J] using hF) (Real.exp_nonneg _)
    _ ≤ 1 * J := by
      exact mul_le_mul_of_nonneg_right
        (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith))
        (integral_nonneg fun _ => Real.exp_nonneg _)
    _ = ∫ x : ℝ, Real.exp (-(sigma * |x|)) := by simp only [J, one_mul]

theorem xiMassPolarKernel_eq_growing_add_damped
    (a sigma u h : ℝ) :
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I)) (h : ℂ) *
        (2 * Real.cosh (h / 2) : ℂ) =
      xiMassCriticalGrowingFourierProfile a sigma u h +
        xiMassCriticalDampedFourierProfile a sigma u h := by
  rw [xiMassCriticalGrowingFourierProfile,
    xiMassCriticalDampedFourierProfile]
  have hcosh : Real.exp (h / 2) + Real.exp (-h / 2) =
      2 * Real.cosh (h / 2) := by
    rw [Real.cosh_eq]
    ring
  have hcoshC : (Real.exp (h / 2) : ℂ) + (Real.exp (-h / 2) : ℂ) =
      (2 * Real.cosh (h / 2) : ℂ) := by exact_mod_cast hcosh
  rw [← hcoshC]
  ring

theorem norm_integral_xiMassCriticalGrowingFourierProfile_at_cone_le
    {a sigma d u w : ℝ}
    (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    (hu : 0 ≤ u)
    (hw : d * u / (d - 1 / 2) ≤ w) :
    ‖∫ h in (0 : ℝ)..w,
        xiMassCriticalGrowingFourierProfile a sigma u h‖ ≤
      2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
  let G : ℝ → ℂ := xiMassCriticalGrowingFourierProfile a sigma u
  let K : ℝ → ℂ := xiMassCriticalDampedFourierProfile a sigma u
  have hH0 : 0 ≤ d * u / (d - 1 / 2) := by positivity
  have hw0 : 0 ≤ w := hH0.trans hw
  have hGcont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassCriticalGrowingFourierProfile
      (lt_trans (by norm_num) (lt_trans hdhalf hda)) hsigma u h).continuousAt
  have hKcont : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro h
    exact (hasDerivAt_xiMassCriticalDampedFourierProfile
      (lt_trans (by norm_num) (lt_trans hdhalf hda)) hsigma u h).continuousAt
  have hrel : xiMassPolarPartialSource a sigma u w =
      (∫ h in (0 : ℝ)..w, G h) + ∫ h in (0 : ℝ)..w, K h := by
    rw [xiMassPolarPartialSource, ← intervalIntegral.integral_of_le hw0,
      ← intervalIntegral.integral_add
        (hGcont.intervalIntegrable _ _) (hKcont.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro h hh
    exact xiMassPolarKernel_eq_growing_add_damped a sigma u h
  have hpolar := norm_xiMassPolarPartialSource_at_cone_le
    hdhalf hda hsigma hu hw
  have hdamped := norm_integral_xiMassCriticalDampedFourierProfile_le
    (u := u) (lt_trans (by norm_num) (lt_trans hdhalf hda)) hsigma hw0
  have hsolve : (∫ h in (0 : ℝ)..w, G h) =
      xiMassPolarPartialSource a sigma u w - ∫ h in (0 : ℝ)..w, K h := by
    calc
      (∫ h in (0 : ℝ)..w, G h) =
          ((∫ h in (0 : ℝ)..w, G h) + ∫ h in (0 : ℝ)..w, K h) -
            ∫ h in (0 : ℝ)..w, K h := by ring
      _ = xiMassPolarPartialSource a sigma u w -
            ∫ h in (0 : ℝ)..w, K h := by rw [hrel]
  change ‖∫ h in (0 : ℝ)..w, G h‖ ≤ _
  rw [hsolve]
  calc
    ‖xiMassPolarPartialSource a sigma u w - ∫ h in (0 : ℝ)..w, K h‖ ≤
        ‖xiMassPolarPartialSource a sigma u w‖ +
          ‖∫ h in (0 : ℝ)..w, K h‖ := norm_sub_le _ _
    _ ≤ (2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2)) +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) :=
      add_le_add hpolar hdamped
    _ = 2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) := rfl

theorem norm_xiMassCriticalIntegerAtomSum_at_cone_le
    {a sigma d u w : ℝ} (N : ℕ)
    (hhalf : 1 / 2 < a) (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d)
    (hda : d < a) (hu : 0 ≤ u)
    (hwdef : w = Real.log ((N : ℝ) + 2))
    (hw : d * u / (d - 1 / 2) ≤ w) :
    ‖xiMassCriticalIntegerAtomSum a sigma u N‖ ≤
      2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
        3 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
        2 * xiMassCriticalOutgoingZeroShiftBound sigma := by
  have hw0 : 0 ≤ w := (show 0 ≤ d * u / (d - 1 / 2) by positivity).trans hw
  have hexact := xiMassCriticalIntegerAtomSum_eq_integral
    (a := a) (sigma := sigma) (u := u) N hhalf hsigma
  dsimp only at hexact
  rw [← hwdef] at hexact
  have hG := norm_integral_xiMassCriticalGrowingFourierProfile_at_cone_le
    hdhalf hda hsigma hu hw
  have hS := norm_integral_xiMassCriticalFloorSawtoothDensity_le
    (u := u) (lt_trans (by norm_num) hhalf) hsigma hw0
  have hK := norm_xiMassCriticalDampedFourierProfile_le
    (u := u) (lt_trans (by norm_num) hhalf) hsigma hw0
  rw [hexact]
  calc
    ‖(∫ h in (0 : ℝ)..w,
          xiMassCriticalGrowingFourierProfile a sigma u h) +
        (∫ h in (0 : ℝ)..w,
          xiMassCriticalFloorSawtoothDensity a sigma u h) -
        xiMassCriticalDampedFourierProfile a sigma u w‖ ≤
      (‖∫ h in (0 : ℝ)..w,
          xiMassCriticalGrowingFourierProfile a sigma u h‖ +
        ‖∫ h in (0 : ℝ)..w,
          xiMassCriticalFloorSawtoothDensity a sigma u h‖) +
        ‖xiMassCriticalDampedFourierProfile a sigma u w‖ := by
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2 * Real.pi +
          2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
          2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
          2 * xiMassCriticalOutgoingZeroShiftBound sigma) +
        (∫ x : ℝ, Real.exp (-(sigma * |x|))) := by
      exact add_le_add (add_le_add hG hS) hK
    _ = 2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
        3 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
        2 * xiMassCriticalOutgoingZeroShiftBound sigma := by ring

noncomputable def xiMassCriticalIntegerConeSum
    (a sigma d u : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    xiMassCriticalDampedFourierProfile a sigma u (Real.log ((k : ℝ) + 2))

theorem norm_xiMassCriticalIntegerConeSum_le
    {a sigma d u : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma)
    (hdhalf : 1 / 2 < d) (hda : d < a) (hu : 0 ≤ u) :
    ‖xiMassCriticalIntegerConeSum a sigma d u‖ ≤
      2 * Real.pi +
        2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
        3 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
        2 * xiMassCriticalOutgoingZeroShiftBound sigma := by
  let H : ℝ := d * u / (d - 1 / 2)
  let M : ℕ := ⌊Real.exp H⌋₊
  let N : ℕ := M - 1
  let w : ℝ := Real.log ((M : ℝ) + 1)
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hMone : 1 ≤ M := by
    apply Nat.le_floor
    simpa only [Nat.cast_one, ← Real.exp_zero] using Real.exp_le_exp.mpr hH0
  have hupper : Real.exp H < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hHw : H ≤ w := by
    have hlog := Real.log_lt_log (Real.exp_pos H) hupper
    have : H < w := by simpa only [Real.log_exp, w] using hlog
    exact this.le
  have hcast : ((N : ℝ) + 2) = (M : ℝ) + 1 := by
    dsimp only [N]
    rw [Nat.cast_sub hMone]
    push_cast
    ring
  have hwdef : w = Real.log ((N : ℝ) + 2) := by rw [hcast]
  have hbound := norm_xiMassCriticalIntegerAtomSum_at_cone_le
    (a := a) (sigma := sigma) (u := u) N hhalf hsigma hdhalf hda hu hwdef hHw
  simpa only [xiMassCriticalIntegerConeSum,
    xiMassCriticalIntegerAtomSum, H, M, N] using hbound

/-- Prime-power-supported critical atom sum at the rounded moving cone. -/
noncomputable def xiMassCriticalPrimeAtomConeSum
    (a sigma d u : ℝ) : ℂ :=
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  ∑ k ∈ Finset.range (M - 1),
    ((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log ((k : ℝ) + 2))

theorem xiMassCriticalCentered_add_integer_eq_primeAtomConeSum
    (a sigma d u : ℝ) :
    xiMassCriticalCenteredAtomConeSum a sigma d u +
        xiMassCriticalIntegerConeSum a sigma d u =
      xiMassCriticalPrimeAtomConeSum a sigma d u := by
  simp only [xiMassCriticalCenteredAtomConeSum,
    xiMassCriticalIntegerConeSum,
    xiMassCriticalPrimeAtomConeSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring

def XiMassCriticalPrimeAtomConeLineBound (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalPrimeAtomConeSum a sigma d u‖ ≤ C

theorem xiMassCriticalCenteredAtomConeLineBound_iff_primeAtomCone
    {a sigma d : ℝ} (hhalf : 1 / 2 < a) (hsigma : 0 < sigma)
    (hdhalf : 1 / 2 < d) (hda : d < a) :
    XiMassCriticalCenteredAtomConeLineBound a sigma d ↔
      XiMassCriticalPrimeAtomConeLineBound a sigma d := by
  let B : ℝ := 2 * Real.pi +
    2 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) / (d - 1 / 2) +
    3 * (∫ x : ℝ, Real.exp (-(sigma * |x|))) +
    2 * xiMassCriticalOutgoingZeroShiftBound sigma
  have hB : ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalIntegerConeSum a sigma d u‖ ≤ B :=
    fun u hu => by
      simpa only [B] using norm_xiMassCriticalIntegerConeSum_le
        hhalf hsigma hdhalf hda hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hrel := xiMassCriticalCentered_add_integer_eq_primeAtomConeSum
      a sigma d u
    rw [← hrel]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (hB u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hrel := xiMassCriticalCentered_add_integer_eq_primeAtomConeSum
      a sigma d u
    have hsolve : xiMassCriticalCenteredAtomConeSum a sigma d u =
        xiMassCriticalPrimeAtomConeSum a sigma d u -
          xiMassCriticalIntegerConeSum a sigma d u := by
      calc
        xiMassCriticalCenteredAtomConeSum a sigma d u =
            (xiMassCriticalCenteredAtomConeSum a sigma d u +
              xiMassCriticalIntegerConeSum a sigma d u) -
                xiMassCriticalIntegerConeSum a sigma d u := by ring
        _ = _ := by rw [hrel]
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (hB u hu))

theorem riemannHypothesis_iff_xiMassCriticalPrimeAtomConeLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔ XiMassCriticalPrimeAtomConeLineBound a sigma d := by
  exact (riemannHypothesis_iff_xiMassCriticalCenteredAtomConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalCenteredAtomConeLineBound_iff_primeAtomCone
        (lt_trans hdhalf hda) hsigma hdhalf hda)

end

end RHTower

