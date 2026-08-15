import GaloisForLFunctions.RHTower.Sieve.InghamDetectorAdmissibleContour
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity

/-!
# Exact cancellation of the detector pole-clearing gauge

The entire detector is `(s - 1)²` times Ingham's classical meromorphic detector away from the
zeta pole.  Estimating those factors edge by edge would introduce a false height-growth cost.
This file proves that the complete weighted Littlewood functional is additive and that the
pole-clearing square contributes exactly the fixed charge `4π(1-c)`.

Zeros on the left edge are allowed.  Logarithmic factorization there holds away from a finite set,
which is enough for the interval integral.
-/

open Complex Filter MeasureTheory intervalIntegral Set Topology

namespace RHTower

noncomputable section

/-- Exact weighted Littlewood charge of the square pole-clearing gauge when its zero lies in the
interior of the rectangle. -/
theorem weightedLittlewoodBoundary_poleGauge_sq
    {c d T₁ T₂ : ℝ} (hc1 : c < 1) (h1d : 1 < d)
    (hT₁ : T₁ < 0) (hT₂ : 0 < T₂) :
    weightedLittlewoodBoundary (fun s : ℂ => (s - 1) ^ 2) c d T₁ T₂ =
      4 * Real.pi * (1 - c) := by
  let p : ℂ → ℂ := fun s => (s - 1) ^ 2
  have hcd : c < d := hc1.trans h1d
  have hT : T₁ < T₂ := hT₁.trans hT₂
  have hp : AnalyticOnNhd ℂ p Set.univ := by
    intro z _
    exact (analyticAt_id.sub analyticAt_const).pow 2
  have hpne : ∃ z : ℂ, p z ≠ 0 := ⟨0, by norm_num [p]⟩
  have hbot : ∀ x ∈ Set.uIcc c d, p ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x _ hz
    have heq : (x : ℂ) + (T₁ : ℂ) * I = 1 := by
      apply sub_eq_zero.mp
      exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hz
    have him := congrArg Complex.im heq
    simp at him
    linarith
  have htop : ∀ x ∈ Set.uIcc c d, p ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x _ hz
    have heq : (x : ℂ) + (T₂ : ℂ) * I = 1 := by
      apply sub_eq_zero.mp
      exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hz
    have him := congrArg Complex.im heq
    simp at him
    linarith
  have hright : ∀ t ∈ Set.uIcc T₁ T₂, p ((d : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _ hz
    have heq : (d : ℂ) + (t : ℂ) * I = 1 := by
      apply sub_eq_zero.mp
      exact (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hz
    have hre := congrArg Complex.re heq
    simp at hre
    linarith
  obtain ⟨Z, hmem, hboundary⟩ :=
    exists_entire_weighted_littlewood_rectangle_left_boundary_zeros
      hp hpne hcd hT hbot htop hright
  have hZ : Z = {1} := by
    ext z
    rw [Finset.mem_singleton]
    constructor
    · intro hz
      have hz0 := ((hmem z).mp hz).2
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hz0)
    · intro hz
      subst z
      apply (hmem 1).mpr
      constructor
      · apply Complex.mem_reProdIm.mpr
        rw [Set.uIcc_of_le hcd.le, Set.uIcc_of_le hT.le]
        constructor <;> simp only [Complex.one_re, Complex.one_im, Set.mem_Icc] <;>
          constructor <;> linarith
      · simp [p]
  have hlin : AnalyticAt ℂ (fun s : ℂ => s - 1) 1 :=
    analyticAt_id.sub analyticAt_const
  have hlinOrder : analyticOrderAt (fun s : ℂ => s - 1) 1 = 1 := by
    exact hlin.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) (by simp)
  have hpOrder : analyticOrderAt p 1 = 2 := by
    change analyticOrderAt ((fun s : ℂ => s - 1) ^ 2) 1 = 2
    rw [analyticOrderAt_pow hlin, hlinOrder]
    rfl
  have hsum :
      (∑ w ∈ Z, ((analyticOrderAt p w).toNat : ℝ) * (w.re - c)) =
        2 * (1 - c) := by
    rw [hZ]
    simp [hpOrder]
  rw [hsum] at hboundary
  calc
    weightedLittlewoodBoundary (fun s : ℂ => (s - 1) ^ 2) c d T₁ T₂ =
        weightedLittlewoodBoundary p c d T₁ T₂ := rfl
    _ = 2 * Real.pi * (2 * (1 - c)) := hboundary.symm
    _ = 4 * Real.pi * (1 - c) := by ring

end

end RHTower

namespace RHTower.Sieve

noncomputable section

/-- Ingham's classical meromorphic detector before pole clearing. -/
noncomputable def inghamClassicalDetector (X : ℕ) (s : ℂ) : ℂ :=
  1 - (riemannZeta s * inghamMollifier X s - 1) ^ 2

/-- Weighted Littlewood boundary of the classical meromorphic detector. -/
noncomputable def inghamClassicalLittlewoodBoundary
    (X : ℕ) (c d T₁ T₂ : ℝ) : ℝ :=
  weightedLittlewoodBoundary (inghamClassicalDetector X) c d T₁ T₂

private theorem analyticAt_inghamClassicalDetector
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (inghamClassicalDetector X) s := by
  exact analyticAt_const.sub ((((analyticAt_riemannZeta_of_ne_one hs).mul
    (analyticAt_inghamMollifier X s)).sub analyticAt_const).pow 2)

private theorem analyticAt_logDeriv_of_ne {f : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f s) (hs : f s ≠ 0) :
    AnalyticAt ℂ (logDeriv f) s := by
  have h := hf.deriv.div hf hs
  exact h.congr (by
    filter_upwards with z
    simp only [Pi.div_apply, logDeriv_apply])

private theorem logDeriv_congr_of_eventuallyEq
    {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[nhds s] g) :
    logDeriv f s = logDeriv g s := by
  rw [logDeriv, logDeriv]
  simp only [Pi.div_apply]
  rw [h.deriv_eq, h.eq_of_nhds]

private theorem intervalIntegrable_log_norm_vertical_of_analytic
    {f : ℂ → ℂ} {a T₁ T₂ : ℝ}
    (hf : ∀ t ∈ Set.uIcc T₁ T₂,
      AnalyticAt ℂ f ((a : ℂ) + (t : ℂ) * I)) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖f ((a : ℂ) + (t : ℂ) * I)‖)
      volume T₁ T₂ := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t ht
  have hpath : AnalyticAt ℝ (fun u : ℝ => (a : ℂ) + (u : ℂ) * I) t := by
    exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  exact AnalyticAt.comp (f := fun u : ℝ => (a : ℂ) + (u : ℂ) * I)
    (hf t ht).restrictScalars hpath |>.meromorphicAt

private theorem intervalIntegrable_re_logDeriv_vertical
    {f : ℂ → ℂ} {a T₁ T₂ : ℝ}
    (hf : ∀ t ∈ Set.uIcc T₁ T₂,
      AnalyticAt ℂ f ((a : ℂ) + (t : ℂ) * I))
    (hne : ∀ t ∈ Set.uIcc T₁ T₂,
      f ((a : ℂ) + (t : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun t : ℝ => (logDeriv f ((a : ℂ) + (t : ℂ) * I)).re)
      volume T₁ T₂ := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hpath : ContinuousAt (fun u : ℝ => (a : ℂ) + (u : ℂ) * I) t := by
    fun_prop
  have hcomp : ContinuousAt
      (fun u : ℝ => logDeriv f ((a : ℂ) + (u : ℂ) * I)) t :=
    (analyticAt_logDeriv_of_ne (hf t ht) (hne t ht)).continuousAt.comp_of_eq
      hpath rfl
  exact (Complex.continuous_re.continuousAt.comp hcomp).continuousWithinAt

private theorem intervalIntegrable_weighted_im_logDeriv_horizontal
    {f : ℂ → ℂ} {c d T : ℝ}
    (hf : ∀ x ∈ Set.uIcc c d,
      AnalyticAt ℂ f ((x : ℂ) + (T : ℂ) * I))
    (hne : ∀ x ∈ Set.uIcc c d,
      f ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun x : ℝ => (x - c) * (logDeriv f ((x : ℂ) + (T : ℂ) * I)).im)
      volume c d := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hpath : ContinuousAt (fun y : ℝ => (y : ℂ) + (T : ℂ) * I) x := by
    fun_prop
  have hcomp : ContinuousAt
      (fun y : ℝ => logDeriv f ((y : ℂ) + (T : ℂ) * I)) x :=
    (analyticAt_logDeriv_of_ne (hf x hx) (hne x hx)).continuousAt.comp_of_eq
      hpath rfl
  exact ((continuousAt_id.sub continuousAt_const).mul
    (Complex.continuous_im.continuousAt.comp hcomp)).continuousWithinAt

private theorem eventuallyEq_inghamDetector_factor
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    inghamDetector X =ᶠ[nhds s]
      (fun z => (z - 1) ^ 2 * inghamClassicalDetector X z) := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
  simpa only [inghamClassicalDetector] using
    inghamDetector_eq_poleCleared X (by simpa using hz)

private theorem inghamClassicalDetector_ne_zero_of_detector_ne_zero
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) (hH : inghamDetector X s ≠ 0) :
    inghamClassicalDetector X s ≠ 0 := by
  intro hh
  have hfactor := inghamDetector_eq_poleCleared X hs
  rw [show 1 - (riemannZeta s * inghamMollifier X s - 1) ^ 2 =
      inghamClassicalDetector X s by rfl, hh, mul_zero] at hfactor
  exact hH hfactor

private theorem log_norm_inghamDetector_eq_gauge_add_classical
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) (hH : inghamDetector X s ≠ 0) :
    Real.log ‖inghamDetector X s‖ =
      Real.log ‖(s - 1) ^ 2‖ + Real.log ‖inghamClassicalDetector X s‖ := by
  have hp : (s - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs)
  have hh := inghamClassicalDetector_ne_zero_of_detector_ne_zero X hs hH
  rw [inghamDetector_eq_poleCleared X hs,
    show 1 - (riemannZeta s * inghamMollifier X s - 1) ^ 2 =
      inghamClassicalDetector X s by rfl,
    norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hp) (norm_ne_zero_iff.mpr hh)]

private theorem logDeriv_inghamDetector_eq_gauge_add_classical
    (X : ℕ) {s : ℂ} (hs : s ≠ 1) (hH : inghamDetector X s ≠ 0) :
    logDeriv (inghamDetector X) s =
      logDeriv (fun z : ℂ => (z - 1) ^ 2) s +
        logDeriv (inghamClassicalDetector X) s := by
  rw [logDeriv_congr_of_eventuallyEq (eventuallyEq_inghamDetector_factor X hs)]
  exact logDeriv_mul s
    (pow_ne_zero 2 (sub_ne_zero.mpr hs))
    (inghamClassicalDetector_ne_zero_of_detector_ne_zero X hs hH)
    ((analyticAt_id.sub analyticAt_const).pow 2).differentiableAt
    (analyticAt_inghamClassicalDetector X hs).differentiableAt

/-- The complete pole-cleared detector boundary equals the classical meromorphic detector boundary
plus the fixed double-pole charge.  In particular pole clearing adds no height-dependent loss. -/
theorem inghamLittlewoodBoundary_eq_classical_add_poleCharge
    (X : ℕ) {c d T₁ T₂ : ℝ}
    (hc1 : c < 1) (h1d : 1 < d) (hT₁ : T₁ < 0) (hT₂ : 0 < T₂)
    (hbot : ∀ x ∈ Set.uIcc c d,
      inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ Set.uIcc c d,
      inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0)
    (hright : ∀ t ∈ Set.uIcc T₁ T₂,
      inghamDetector X ((d : ℂ) + (t : ℂ) * I) ≠ 0) :
    inghamLittlewoodBoundary X c d T₁ T₂ =
      inghamClassicalLittlewoodBoundary X c d T₁ T₂ +
        4 * Real.pi * (1 - c) := by
  classical
  let p : ℂ → ℂ := fun s => (s - 1) ^ 2
  let h : ℂ → ℂ := inghamClassicalDetector X
  let H : ℂ → ℂ := inghamDetector X
  have hcd : c < d := hc1.trans h1d
  have hT : T₁ < T₂ := hT₁.trans hT₂
  have hc_ne (t : ℝ) : (c : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith
  have hd_ne (t : ℝ) : (d : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp at hre
    linarith
  have hbot_ne (x : ℝ) : (x : ℂ) + (T₁ : ℂ) * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp at him
    linarith
  have htop_ne (x : ℝ) : (x : ℂ) + (T₂ : ℂ) * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp at him
    linarith
  have hbotP : ∀ x ∈ Set.uIcc c d, p ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x _
    exact pow_ne_zero 2 (sub_ne_zero.mpr (hbot_ne x))
  have htopP : ∀ x ∈ Set.uIcc c d, p ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x _
    exact pow_ne_zero 2 (sub_ne_zero.mpr (htop_ne x))
  have hrightP : ∀ t ∈ Set.uIcc T₁ T₂, p ((d : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _
    exact pow_ne_zero 2 (sub_ne_zero.mpr (hd_ne t))
  have hbot_h : ∀ x ∈ Set.uIcc c d, h ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    exact inghamClassicalDetector_ne_zero_of_detector_ne_zero X
      (hbot_ne x) (hbot x hx)
  have htop_h : ∀ x ∈ Set.uIcc c d, h ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    exact inghamClassicalDetector_ne_zero_of_detector_ne_zero X
      (htop_ne x) (htop x hx)
  have hright_h : ∀ t ∈ Set.uIcc T₁ T₂, h ((d : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t ht
    exact inghamClassicalDetector_ne_zero_of_detector_ne_zero X
      (hd_ne t) (hright t ht)
  let z₁ : ℂ := (c : ℂ) + (T₁ : ℂ) * I
  let z₂ : ℂ := (d : ℂ) + (T₂ : ℂ) * I
  let Kzero : Set ℂ :=
    {z ∈ (Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im) | H z = 0}
  have hKfinite : Kzero.Finite := by
    exact entire_zeros_closedRectangle_finite (inghamDetector_analyticOnNhd_univ X)
      ⟨(d : ℂ) + (T₁ : ℂ) * I, hright T₁ left_mem_uIcc⟩ z₁ z₂
  let S : Set ℝ := {t | t ∈ Set.uIcc T₁ T₂ ∧ H ((c : ℂ) + (t : ℂ) * I) = 0}
  have hSfinite : S.Finite := by
    apply (hKfinite.image Complex.im).subset
    intro t ht
    obtain ⟨htI, htzero⟩ := ht
    refine ⟨(c : ℂ) + (t : ℂ) * I, ?_, by simp⟩
    constructor
    · apply Complex.mem_reProdIm.mpr
      simpa [z₁, z₂, Set.uIcc_of_le hcd.le, Set.uIcc_of_le hT.le] using
        And.intro (show c ∈ Set.Icc c d from ⟨le_rfl, hcd.le⟩)
          (show t ∈ Set.Icc T₁ T₂ by simpa [Set.uIcc_of_le hT.le] using htI)
    · exact htzero
  have haeNotS : ∀ᵐ t : ℝ ∂volume, t ∉ S := by
    rw [ae_iff]
    simpa using hSfinite.measure_zero volume
  have hpLcInt : IntervalIntegrable
      (fun t : ℝ => Real.log ‖p ((c : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ :=
    intervalIntegrable_log_norm_vertical_of_analytic
      (fun _ _ => (analyticAt_id.sub analyticAt_const).pow 2)
  have hhLcInt : IntervalIntegrable
      (fun t : ℝ => Real.log ‖h ((c : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ :=
    intervalIntegrable_log_norm_vertical_of_analytic
      (fun t _ => analyticAt_inghamClassicalDetector X (hc_ne t))
  have hLc :
      (∫ t in T₁..T₂, Real.log ‖H ((c : ℂ) + (t : ℂ) * I)‖) =
        (∫ t in T₁..T₂, Real.log ‖p ((c : ℂ) + (t : ℂ) * I)‖) +
        ∫ t in T₁..T₂, Real.log ‖h ((c : ℂ) + (t : ℂ) * I)‖ := by
    calc
      (∫ t in T₁..T₂, Real.log ‖H ((c : ℂ) + (t : ℂ) * I)‖) =
          ∫ t in T₁..T₂,
            (Real.log ‖p ((c : ℂ) + (t : ℂ) * I)‖ +
              Real.log ‖h ((c : ℂ) + (t : ℂ) * I)‖) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [haeNotS] with t htS htI
        have htIcc : t ∈ Set.uIcc T₁ T₂ := Set.uIoc_subset_uIcc htI
        have hHne : inghamDetector X ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
          intro hz
          exact htS ⟨htIcc, hz⟩
        exact log_norm_inghamDetector_eq_gauge_add_classical X (hc_ne t) hHne
      _ = _ := intervalIntegral.integral_add hpLcInt hhLcInt
  have hpLdInt : IntervalIntegrable
      (fun t : ℝ => Real.log ‖p ((d : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ :=
    intervalIntegrable_log_norm_vertical_of_analytic
      (fun _ _ => (analyticAt_id.sub analyticAt_const).pow 2)
  have hhLdInt : IntervalIntegrable
      (fun t : ℝ => Real.log ‖h ((d : ℂ) + (t : ℂ) * I)‖) volume T₁ T₂ :=
    intervalIntegrable_log_norm_vertical_of_analytic
      (fun t _ => analyticAt_inghamClassicalDetector X (hd_ne t))
  have hLd :
      (∫ t in T₁..T₂, Real.log ‖H ((d : ℂ) + (t : ℂ) * I)‖) =
        (∫ t in T₁..T₂, Real.log ‖p ((d : ℂ) + (t : ℂ) * I)‖) +
        ∫ t in T₁..T₂, Real.log ‖h ((d : ℂ) + (t : ℂ) * I)‖ := by
    calc
      (∫ t in T₁..T₂, Real.log ‖H ((d : ℂ) + (t : ℂ) * I)‖) =
          ∫ t in T₁..T₂,
            (Real.log ‖p ((d : ℂ) + (t : ℂ) * I)‖ +
              Real.log ‖h ((d : ℂ) + (t : ℂ) * I)‖) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact log_norm_inghamDetector_eq_gauge_add_classical X
          (hd_ne t) (hright t ht)
      _ = _ := intervalIntegral.integral_add hpLdInt hhLdInt
  have hpRInt := intervalIntegrable_re_logDeriv_vertical
    (f := p) (a := d) (T₁ := T₁) (T₂ := T₂)
    (fun _ _ => (analyticAt_id.sub analyticAt_const).pow 2) hrightP
  have hhRInt := intervalIntegrable_re_logDeriv_vertical
    (f := h) (a := d) (T₁ := T₁) (T₂ := T₂)
    (fun t _ => analyticAt_inghamClassicalDetector X (hd_ne t)) hright_h
  have hR :
      (∫ t in T₁..T₂, (logDeriv H ((d : ℂ) + (t : ℂ) * I)).re) =
        (∫ t in T₁..T₂, (logDeriv p ((d : ℂ) + (t : ℂ) * I)).re) +
        ∫ t in T₁..T₂, (logDeriv h ((d : ℂ) + (t : ℂ) * I)).re := by
    calc
      (∫ t in T₁..T₂, (logDeriv H ((d : ℂ) + (t : ℂ) * I)).re) =
          ∫ t in T₁..T₂,
            ((logDeriv p ((d : ℂ) + (t : ℂ) * I)).re +
              (logDeriv h ((d : ℂ) + (t : ℂ) * I)).re) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hsplit := logDeriv_inghamDetector_eq_gauge_add_classical X
          (hd_ne t) (hright t ht)
        simpa only [H, p, h, Complex.add_re] using congrArg Complex.re hsplit
      _ = _ := intervalIntegral.integral_add hpRInt hhRInt
  have hpBotInt := intervalIntegrable_weighted_im_logDeriv_horizontal
    (f := p) (c := c) (d := d) (T := T₁)
    (fun _ _ => (analyticAt_id.sub analyticAt_const).pow 2) hbotP
  have hhBotInt := intervalIntegrable_weighted_im_logDeriv_horizontal
    (f := h) (c := c) (d := d) (T := T₁)
    (fun x _ => analyticAt_inghamClassicalDetector X (hbot_ne x)) hbot_h
  have hBot :
      (∫ x in c..d, (x - c) * (logDeriv H ((x : ℂ) + (T₁ : ℂ) * I)).im) =
        (∫ x in c..d, (x - c) * (logDeriv p ((x : ℂ) + (T₁ : ℂ) * I)).im) +
        ∫ x in c..d, (x - c) * (logDeriv h ((x : ℂ) + (T₁ : ℂ) * I)).im := by
    calc
      (∫ x in c..d, (x - c) * (logDeriv H ((x : ℂ) + (T₁ : ℂ) * I)).im) =
          ∫ x in c..d,
            ((x - c) * (logDeriv p ((x : ℂ) + (T₁ : ℂ) * I)).im +
              (x - c) * (logDeriv h ((x : ℂ) + (T₁ : ℂ) * I)).im) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hsplit := logDeriv_inghamDetector_eq_gauge_add_classical X
          (hbot_ne x) (hbot x hx)
        have him :
            (logDeriv H ((x : ℂ) + (T₁ : ℂ) * I)).im =
              (logDeriv p ((x : ℂ) + (T₁ : ℂ) * I)).im +
                (logDeriv h ((x : ℂ) + (T₁ : ℂ) * I)).im := by
          simpa only [H, p, h, Complex.add_im] using congrArg Complex.im hsplit
        change (x - c) * (logDeriv H ((x : ℂ) + (T₁ : ℂ) * I)).im =
          (x - c) * (logDeriv p ((x : ℂ) + (T₁ : ℂ) * I)).im +
            (x - c) * (logDeriv h ((x : ℂ) + (T₁ : ℂ) * I)).im
        rw [him]
        ring
      _ = _ := intervalIntegral.integral_add hpBotInt hhBotInt
  have hpTopInt := intervalIntegrable_weighted_im_logDeriv_horizontal
    (f := p) (c := c) (d := d) (T := T₂)
    (fun _ _ => (analyticAt_id.sub analyticAt_const).pow 2) htopP
  have hhTopInt := intervalIntegrable_weighted_im_logDeriv_horizontal
    (f := h) (c := c) (d := d) (T := T₂)
    (fun x _ => analyticAt_inghamClassicalDetector X (htop_ne x)) htop_h
  have hTop :
      (∫ x in c..d, (x - c) * (logDeriv H ((x : ℂ) + (T₂ : ℂ) * I)).im) =
        (∫ x in c..d, (x - c) * (logDeriv p ((x : ℂ) + (T₂ : ℂ) * I)).im) +
        ∫ x in c..d, (x - c) * (logDeriv h ((x : ℂ) + (T₂ : ℂ) * I)).im := by
    calc
      (∫ x in c..d, (x - c) * (logDeriv H ((x : ℂ) + (T₂ : ℂ) * I)).im) =
          ∫ x in c..d,
            ((x - c) * (logDeriv p ((x : ℂ) + (T₂ : ℂ) * I)).im +
              (x - c) * (logDeriv h ((x : ℂ) + (T₂ : ℂ) * I)).im) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hsplit := logDeriv_inghamDetector_eq_gauge_add_classical X
          (htop_ne x) (htop x hx)
        have him :
            (logDeriv H ((x : ℂ) + (T₂ : ℂ) * I)).im =
              (logDeriv p ((x : ℂ) + (T₂ : ℂ) * I)).im +
                (logDeriv h ((x : ℂ) + (T₂ : ℂ) * I)).im := by
          simpa only [H, p, h, Complex.add_im] using congrArg Complex.im hsplit
        change (x - c) * (logDeriv H ((x : ℂ) + (T₂ : ℂ) * I)).im =
          (x - c) * (logDeriv p ((x : ℂ) + (T₂ : ℂ) * I)).im +
            (x - c) * (logDeriv h ((x : ℂ) + (T₂ : ℂ) * I)).im
        rw [him]
        ring
      _ = _ := intervalIntegral.integral_add hpTopInt hhTopInt
  have hpBoundary := RHTower.weightedLittlewoodBoundary_poleGauge_sq hc1 h1d hT₁ hT₂
  change weightedLittlewoodBoundary H c d T₁ T₂ =
    weightedLittlewoodBoundary h c d T₁ T₂ + 4 * Real.pi * (1 - c)
  rw [← hpBoundary]
  simp only [weightedLittlewoodBoundary]
  rw [hLc, hLd, hR, hBot, hTop]
  ring

/-- Unconditional selected-contour zero-mass inequality in the classical meromorphic detector
representation.  All pole clearing has been reduced to the fixed charge `4π(1-c)`. -/
theorem eventually_exists_zetaZeroMass_le_inghamClassicalBoundary_add_poleCharge :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ H : ℝ,
      ∃ T₁ ∈ Set.Ioo (-|H| - 2) (-|H| - 1),
        ∃ T₂ ∈ Set.Ioo |H| (|H| + 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((inghamPowerSavingRightEdge : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            inghamClassicalLittlewoodBoundary X inghamFixedGabrielSigma
              inghamPowerSavingRightEdge T₁ T₂ +
                4 * Real.pi * (1 - inghamFixedGabrielSigma) := by
  filter_upwards [eventually_exists_inghamDetector_admissibleContour] with X hcontour
  intro H
  obtain ⟨T₁, hT₁, T₂, hT₂, hbot, htop, hright, hmass⟩ := hcontour H
  have hT₁neg : T₁ < 0 := by
    have := abs_nonneg H
    linarith [hT₁.2]
  have hT₂pos : 0 < T₂ := by
    exact lt_of_le_of_lt (abs_nonneg H) hT₂.1
  have hgauge := inghamLittlewoodBoundary_eq_classical_add_poleCharge X
    (c := inghamFixedGabrielSigma) (d := inghamPowerSavingRightEdge)
    (T₁ := T₁) (T₂ := T₂)
    (by norm_num [inghamFixedGabrielSigma])
    (by norm_num [inghamPowerSavingRightEdge]) hT₁neg hT₂pos hbot htop hright
  rw [hgauge] at hmass
  exact ⟨T₁, hT₁, T₂, hT₂, hmass⟩

/-- Far-right counting-edge form.  The zero-counting rectangle uses `Re s = 2`, independently of
the `181/180` edge used to prove the center moment.  This preserves the zero mass while exposing
rapidly decaying absolute Dirichlet tails on the counting edge. -/
theorem eventually_exists_zetaZeroMass_le_inghamClassicalBoundary_farRightTwo :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ H : ℝ,
      ∃ T₁ ∈ Set.Ioo (-|H| - 2) (-|H| - 1),
        ∃ T₂ ∈ Set.Ioo |H| (|H| + 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((2 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            inghamClassicalLittlewoodBoundary X inghamFixedGabrielSigma
              2 T₁ T₂ + 4 * Real.pi * (1 - inghamFixedGabrielSigma) := by
  filter_upwards [eventually_exists_inghamDetector_admissibleContour_at_rightEdge
    (c := inghamFixedGabrielSigma) (beta := 2)
    (by norm_num [inghamFixedGabrielSigma]) (by norm_num)] with X hcontour
  intro H
  obtain ⟨T₁, hT₁, T₂, hT₂, hbot, htop, hright, hmass⟩ := hcontour H
  have hT₁neg : T₁ < 0 := by
    have := abs_nonneg H
    linarith [hT₁.2]
  have hT₂pos : 0 < T₂ := lt_of_le_of_lt (abs_nonneg H) hT₂.1
  have hgauge := inghamLittlewoodBoundary_eq_classical_add_poleCharge X
    (c := inghamFixedGabrielSigma) (d := 2) (T₁ := T₁) (T₂ := T₂)
    (by norm_num [inghamFixedGabrielSigma]) (by norm_num)
    hT₁neg hT₂pos hbot htop hright
  rw [hgauge] at hmass
  exact ⟨T₁, hT₁, T₂, hT₂, hmass⟩

end


end RHTower.Sieve
