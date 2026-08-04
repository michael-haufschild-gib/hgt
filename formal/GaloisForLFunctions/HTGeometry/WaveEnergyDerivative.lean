import GaloisForLFunctions.HTGeometry.WaveEnergyFlux
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.ODE.Gronwall

/-!
# The derivative of the energy

The energy of a wave field on a time slice is the integral of its energy density. Differentiating
it means differentiating under the integral sign, which is legitimate here for the simplest possible
reason: the field has spatial support in a fixed compact set, so on any bounded time interval the
time derivative of the energy density is a continuous function on a compact set, and the constant
that bounds it there — read as a function supported on that compact set — is integrable.

Together with the flux identity of the previous file this gives the derivative of the energy in the
form the estimate needs: no derivative of the field survives in it.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Energy

variable {d : ℕ} {u V : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

/-- The energy of a wave field on the slice at a given time. -/
noncomputable def waveEnergy (u : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Fin d → ℝ, energyDensity u (t, x)

/-- The time slice of a field is differentiable in time, with the directional derivative as its
derivative. -/
theorem hasDerivAt_timeSlice (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Fin d → ℝ) :
    HasDerivAt (fun s : ℝ => u (s, x)) (waveDirDeriv (timeDir d) u (t, x)) t := by
  have hmap : HasFDerivAt (fun s : ℝ => ((s, x) : ℝ × (Fin d → ℝ)))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const x t)
  have hcomp := (differentiableAt_of_contDiff_infty' hu (t, x)).hasFDerivAt.comp t hmap
  have hval : ((fderiv ℝ u (t, x)).comp ((ContinuousLinearMap.id ℝ ℝ).prod 0)) 1
      = waveDirDeriv (timeDir d) u (t, x) := by
    simp [waveDirDeriv, timeDir]
  have := hcomp.hasDerivAt
  rwa [hval] at this

theorem contDiff_energyDensity (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (energyDensity u) := by
  refine ContDiff.add (ContDiff.add ((contDiff_dirDeriv hu _).pow 2) ?_) (hu.pow 2)
  exact ContDiff.sum fun i _ => (contDiff_dirDeriv hu _).pow 2

theorem energyDensity_zero_of_notMem (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (p : ℝ × (Fin d → ℝ)) (hp : p.2 ∉ K) :
    energyDensity u p = 0 := by
  have h0 : waveDirDeriv (timeDir d) u p = 0 := waveDirDeriv_zero_of_notMem hK hzero _ p hp
  have hi : ∀ i : Fin d, waveDirDeriv (spaceDir d i) u p = 0 := fun i =>
    waveDirDeriv_zero_of_notMem hK hzero _ p hp
  rw [energyDensity, h0, Finset.sum_congr rfl fun i _ => by rw [hi i], hzero p hp]
  simp

theorem hasCompactSupport_energyDensity_slice (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (t : ℝ) :
    HasCompactSupport fun x : Fin d → ℝ => energyDensity u (t, x) :=
  HasCompactSupport.intro hK fun x hx => energyDensity_zero_of_notMem hK hzero (t, x) hx

/-- **The energy is differentiable, and its derivative is the integral of the time derivative of
the energy density.** -/
theorem hasDerivAt_waveEnergy (hu : ContDiff ℝ ∞ u) (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (t : ℝ) :
    HasDerivAt (waveEnergy u)
      (∫ x : Fin d → ℝ, waveDirDeriv (timeDir d) (energyDensity u) (t, x)) t := by
  classical
  have hEcd : ContDiff ℝ ∞ (energyDensity u) := contDiff_energyDensity hu
  have hE0 : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → energyDensity u p = 0 :=
    energyDensity_zero_of_notMem hK hzero
  have hF'cont : Continuous (waveDirDeriv (timeDir d) (energyDensity u)) :=
    (contDiff_dirDeriv hEcd _).continuous
  have hF'0 : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → waveDirDeriv (timeDir d) (energyDensity u) p = 0 :=
    fun p hp => waveDirDeriv_zero_of_notMem hK hE0 _ p hp
  -- a uniform bound on a compact time interval
  have hScompact : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn hF'cont.continuousOn
  have hbound_int : Integrable (Set.indicator K fun _ : Fin d → ℝ => C)
      (volume : Measure (Fin d → ℝ)) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact integrableOn_const hK.measure_lt_top.ne
  have hbound : ∀ᵐ x : Fin d → ℝ ∂(volume : Measure (Fin d → ℝ)),
      ∀ s ∈ Metric.ball t 1,
        ‖waveDirDeriv (timeDir d) (energyDensity u) (s, x)‖
          ≤ Set.indicator K (fun _ : Fin d → ℝ => C) x := by
    filter_upwards with x
    intro s hs
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      refine hC (s, x) ⟨?_, hx⟩
      have hsabs : |s - t| < 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hs
        exact hs
      have h1 : t - 1 ≤ s := by
        have := abs_lt.mp hsabs
        linarith [this.1]
      have h2 : s ≤ t + 1 := by
        have := abs_lt.mp hsabs
        linarith [this.2]
      exact ⟨h1, h2⟩
    · rw [Set.indicator_of_notMem hx, hF'0 (s, x) hx, norm_zero]
  have hFmeas : ∀ᶠ s in nhds t, AEStronglyMeasurable
      (fun x : Fin d → ℝ => energyDensity u (s, x)) (volume : Measure (Fin d → ℝ)) := by
    filter_upwards with s
    have hcont : Continuous fun x : Fin d → ℝ => energyDensity u (s, x) := by
      have hmap : Continuous fun x : Fin d → ℝ => ((s, x) : ℝ × (Fin d → ℝ)) := by fun_prop
      exact hEcd.continuous.comp hmap
    exact hcont.aestronglyMeasurable
  have hFint : Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
      (volume : Measure (Fin d → ℝ)) := by
    have hcont : Continuous fun x : Fin d → ℝ => energyDensity u (t, x) := by
      have hmap : Continuous fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
      exact hEcd.continuous.comp hmap
    exact hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_energyDensity_slice hK hzero t)
  have hF'meas : AEStronglyMeasurable
      (fun x : Fin d → ℝ => waveDirDeriv (timeDir d) (energyDensity u) (t, x))
      (volume : Measure (Fin d → ℝ)) := by
    have hmap : Continuous fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
    exact (hF'cont.comp hmap).aestronglyMeasurable
  have hdiff : ∀ᵐ x : Fin d → ℝ ∂(volume : Measure (Fin d → ℝ)), ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun r : ℝ => energyDensity u (r, x))
        (waveDirDeriv (timeDir d) (energyDensity u) (s, x)) s := by
    filter_upwards with x
    intro s _
    exact hasDerivAt_timeSlice hEcd s x
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s : ℝ => fun x : Fin d → ℝ => energyDensity u (s, x))
    (F' := fun s : ℝ => fun x : Fin d → ℝ => waveDirDeriv (timeDir d) (energyDensity u) (s, x))
    (bound := Set.indicator K fun _ : Fin d → ℝ => C)
    (Metric.ball_mem_nhds t one_pos) hFmeas hFint hF'meas hbound hbound_int hdiff).2

/-! ## The estimate -/

theorem energyDensity_nonneg (u : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) :
    0 ≤ energyDensity u p := by
  have hsum : 0 ≤ ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u p) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [energyDensity]
  nlinarith [sq_nonneg (waveDirDeriv (timeDir d) u p), sq_nonneg (u p)]

theorem waveEnergy_nonneg (u : ℝ × (Fin d → ℝ) → ℝ) (t : ℝ) : 0 ≤ waveEnergy u t :=
  integral_nonneg fun x => energyDensity_nonneg u (t, x)

theorem integrable_energyDensity_slice (hu : ContDiff ℝ ∞ u) (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (t : ℝ) :
    Integrable (fun x : Fin d → ℝ => energyDensity u (t, x)) (volume : Measure (Fin d → ℝ)) := by
  have hmap : Continuous fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
  exact ((contDiff_energyDensity hu).continuous.comp hmap).integrable_of_hasCompactSupport
    (hasCompactSupport_energyDensity_slice hK hzero t)

/-- **The energy dominates the flux.** -/
theorem abs_integral_flux_le (hu : ContDiff ℝ ∞ u) (hV : Continuous V) (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) {M : ℝ} (hM : ∀ p, |V p| ≤ M) (t : ℝ) :
    |2 * ∫ x : Fin d → ℝ, (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
      ≤ (M + 1) * waveEnergy u t := by
  have hpt : ∀ x : Fin d → ℝ,
      |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
        ≤ (M + 1) / 2 * energyDensity u (t, x) := by
    intro x
    have h1 : |V (t, x) + 1| ≤ M + 1 := by
      have hMle := abs_le.mp (hM (t, x))
      rw [abs_le]
      constructor <;> linarith [hMle.1, hMle.2]
    have hsq : 2 * (|u (t, x)| * |waveDirDeriv (timeDir d) u (t, x)|)
        ≤ (u (t, x)) ^ 2 + (waveDirDeriv (timeDir d) u (t, x)) ^ 2 := by
      have h := two_mul_le_add_sq |u (t, x)| |waveDirDeriv (timeDir d) u (t, x)|
      rw [sq_abs, sq_abs] at h
      linarith
    have hdens : (u (t, x)) ^ 2 + (waveDirDeriv (timeDir d) u (t, x)) ^ 2
        ≤ energyDensity u (t, x) := by
      have hsum : 0 ≤ ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u (t, x)) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [energyDensity]
      linarith
    have h2 : |u (t, x)| * |waveDirDeriv (timeDir d) u (t, x)| ≤ energyDensity u (t, x) / 2 := by
      linarith
    calc |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
        = |V (t, x) + 1| * (|u (t, x)| * |waveDirDeriv (timeDir d) u (t, x)|) := by
          rw [abs_mul, abs_mul]
      _ ≤ (M + 1) * (energyDensity u (t, x) / 2) := by
          refine mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
          have := hM (t, x)
          have habs := abs_nonneg (V (t, x))
          linarith
      _ = (M + 1) / 2 * energyDensity u (t, x) := by ring
  have hfluxint : Integrable
      (fun x : Fin d → ℝ => (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)))
      (volume : Measure (Fin d → ℝ)) := by
    have hmap : Continuous fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
    have hVc : Continuous fun x : Fin d → ℝ => V (t, x) := hV.comp hmap
    have huc : Continuous fun x : Fin d → ℝ => u (t, x) := hu.continuous.comp hmap
    have hvc : Continuous fun x : Fin d → ℝ => waveDirDeriv (timeDir d) u (t, x) :=
      (contDiff_dirDeriv hu _).continuous.comp hmap
    have hcont : Continuous fun x : Fin d → ℝ =>
        (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)) :=
      (hVc.add continuous_const).mul (huc.mul hvc)
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK fun x hx => ?_
    show (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)) = 0
    rw [hzero (t, x) hx, zero_mul, mul_zero]
  have hdensint := integrable_energyDensity_slice hu hK hzero t
  have hmono : (∫ x : Fin d → ℝ,
      |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|)
      ≤ ∫ x : Fin d → ℝ, (M + 1) / 2 * energyDensity u (t, x) :=
    integral_mono hfluxint.abs (hdensint.const_mul _) hpt
  have hnorm : |∫ x : Fin d → ℝ, (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
      ≤ ∫ x : Fin d → ℝ, |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))| := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (f := fun x : Fin d → ℝ => (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)))
  rw [integral_const_mul] at hmono
  rw [abs_mul, abs_two]
  have hfin : |∫ x : Fin d → ℝ, (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
      ≤ (M + 1) / 2 * waveEnergy u t := le_trans hnorm hmono
  rw [waveEnergy] at hfin ⊢
  linarith

/-- **The energy estimate.** The energy of a classical solution with spatially compact support grows
at most exponentially, at a rate fixed by the size of the potential. -/
theorem waveEnergy_le_exp (hu : ContDiff ℝ ∞ u) (hV : Continuous V) (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (hsolve : SolvesWaveEq u V)
    {M : ℝ} (hM : ∀ p, |V p| ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    waveEnergy u t ≤ waveEnergy u 0 * Real.exp ((M + 1) * t) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (0, 0))
  have hKne : (M + 1) ≠ 0 := by linarith
  have hderiv : ∀ s : ℝ, HasDerivAt (waveEnergy u)
      (2 * ∫ x : Fin d → ℝ, (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x))) s := by
    intro s
    have h := hasDerivAt_waveEnergy hu hK hzero s
    rwa [integral_dirDeriv_energyDensity hu hV hK hzero hsolve s] at h
  have hcont : ContinuousOn (waveEnergy u) (Set.Icc 0 t) :=
    fun s _ => ((hderiv s).continuousAt).continuousWithinAt
  have ha : ‖waveEnergy u 0‖ ≤ waveEnergy u 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (waveEnergy_nonneg u 0)]
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖2 * ∫ x : Fin d → ℝ, (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x))‖
        ≤ (M + 1) * ‖waveEnergy u s‖ + 0 := by
    intro s _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (waveEnergy_nonneg u s), add_zero]
    exact abs_integral_flux_le hu hV hK hzero hM s
  have hgb := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s _ => (hderiv s).hasDerivWithinAt) ha hbound t (Set.mem_Icc.mpr ⟨ht, le_rfl⟩)
  rw [gronwallBound_of_K_ne_0 hKne, Real.norm_eq_abs,
    abs_of_nonneg (waveEnergy_nonneg u t)] at hgb
  simpa using hgb

/-! ## Vanishing -/

theorem energyDensity_eq_zero_of_waveEnergy_eq_zero (hu : ContDiff ℝ ∞ u) (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) {t : ℝ} (h : waveEnergy u t = 0)
    (x : Fin d → ℝ) : energyDensity u (t, x) = 0 := by
  have hmap : Continuous fun y : Fin d → ℝ => ((t, y) : ℝ × (Fin d → ℝ)) := by fun_prop
  have hcont : Continuous fun y : Fin d → ℝ => energyDensity u (t, y) :=
    (contDiff_energyDensity hu).continuous.comp hmap
  have hae : (fun y : Fin d → ℝ => energyDensity u (t, y))
      =ᵐ[(volume : Measure (Fin d → ℝ))] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun y => energyDensity_nonneg u (t, y)) ?_).mp h
    exact integrable_energyDensity_slice hu hK hzero t
  have heq : (fun y : Fin d → ℝ => energyDensity u (t, y)) = 0 :=
    (hcont.ae_eq_iff_eq (volume : Measure (Fin d → ℝ)) continuous_zero).mp hae
  exact congrFun heq x

/-- **A solution whose energy vanishes at one time vanishes at every later time.** This is the
uniqueness half of the estimate: for the difference of two solutions with the same Cauchy data the
energy starts at zero. -/
theorem eq_zero_of_waveEnergy_zero (hu : ContDiff ℝ ∞ u) (hV : Continuous V) (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (hsolve : SolvesWaveEq u V)
    {M : ℝ} (hM : ∀ p, |V p| ≤ M) (h0 : waveEnergy u 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (x : Fin d → ℝ) : u (t, x) = 0 := by
  have hle := waveEnergy_le_exp hu hV hK hzero hsolve hM ht
  rw [h0, zero_mul] at hle
  have ht0 : waveEnergy u t = 0 := le_antisymm hle (waveEnergy_nonneg u t)
  have hden := energyDensity_eq_zero_of_waveEnergy_eq_zero hu hK hzero ht0 x
  have hsum : 0 ≤ ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u (t, x)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [energyDensity] at hden
  have hsq : (u (t, x)) ^ 2 = 0 := by
    nlinarith [sq_nonneg (waveDirDeriv (timeDir d) u (t, x)), sq_nonneg (u (t, x))]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

end Energy

end GaloisForLFunctions.HTGeometry
