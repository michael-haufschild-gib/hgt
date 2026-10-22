import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity

/-!
# Vacuum-regular nonlinear source transport cannot manufacture HB clock covariance

The surviving HB producer asks literal source-functional-equation transport to commute with one
source-predeclared nonzero centered-QNM clock step. Earlier rigidity killed diagonal gauges,
clock-preserving gauges, and arbitrary static complex-linear source-fixed mixing. This module
removes linearity and invertibility completely.

A packet map is required only to be vacuum-regular along vanishing one-coordinate source
sequences. On a tilted Xi reflection orbit, the two centered-QNM clock multipliers have reciprocal
norms: one is strictly contracting and the other strictly expanding. Any clock-commuting
vacuum-regular map preserves the stable set. Literal BM source exchange instead carries the
nonzero source on the stable axis to the nonzero reflected source on the unstable axis. Iteration
then makes the same image converge to zero and remain uniformly separated from zero, a
contradiction.

Thus no static continuous nonlinear reparametrization can repair HB covariance while retaining
literal sources and the fixed physical clock. The pointwise existence condition is exactly the
critical wall, and its universal form is exactly RH. A surviving producer must lose vacuum
regularity, change the literal source, or be genuinely time-dependent Einstein--Teukolsky
dynamics rather than a coordinate gauge.

`[NEW] [HB NO-GO] [NONLINEAR] [STABLE/UNSTABLE RIGIDITY] [LEAN-PROVED]`
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- One-step multiplier of the source-predeclared centered-QNM physical clock. -/
def hbXiPeierlsCenteredQNMPhysicalClockMultiplier
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp
    (-Complex.I * (t : ℂ) * hbXiPeierlsCenteredQNMFrequency n q)

theorem norm_hbXiPeierlsCenteredQNMPhysicalClockMultiplier
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    ‖hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q‖ =
      Real.exp (t * ((1 / 2 - (q.1 : ℂ).re) / 2)) := by
  rw [hbXiPeierlsCenteredQNMPhysicalClockMultiplier, Complex.norm_exp]
  congr 1
  calc
    (-Complex.I * (t : ℂ) * hbXiPeierlsCenteredQNMFrequency n q).re =
        t * (hbXiPeierlsCenteredQNMFrequency n q).im := by
          simp [Complex.mul_re, Complex.mul_im]
    _ = t * ((1 / 2 - (q.1 : ℂ).re) / 2) := by
      rw [hbXiPeierlsCenteredQNMFrequency_im_eq]

theorem norm_hbXiPeierlsCenteredQNMPhysicalClockMultiplier_reflect
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) :
    ‖hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t
        (xiZeroCopyReflectEquiv q)‖ =
      Real.exp (-(t * ((1 / 2 - (q.1 : ℂ).re) / 2))) := by
  rw [norm_hbXiPeierlsCenteredQNMPhysicalClockMultiplier,
    xiZeroCopyReflect_re_eq_one_sub]
  congr 1
  ring_nf

/-- Literal unit BM source on the direct coordinate of one Xi copy. -/
def hbXiPeierlsUnitSourcePacket (q : XiZeroCopy) : HBXiPeierlsPacket :=
  Finsupp.single q (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)

/-- Minimal vacuum regularity needed by the nonlinear no-go: every vanishing one-coordinate
source sequence has coefficientwise vanishing image. -/
def HBXiPeierlsSourceAxisVacuumRegular
    (T : HBXiPeierlsPacket → HBXiPeierlsPacket) : Prop :=
  ∀ (q : XiZeroCopy) (c : ℕ → ℂ),
    Tendsto c atTop (nhds 0) →
      ∀ r : XiZeroCopy,
        Tendsto (fun k => T (Finsupp.single q (c k)) r) atTop (nhds 0)

/-- A packet map exchanges both literal sources on one FE-reflection orbit. -/
def HBXiPeierlsUnitSourceReflectionExchangeAt
    (T : HBXiPeierlsPacket → HBXiPeierlsPacket) (q : XiZeroCopy) : Prop :=
  T (hbXiPeierlsUnitSourcePacket q) =
      hbXiPeierlsUnitSourcePacket (xiZeroCopyReflectEquiv q) ∧
    T (hbXiPeierlsUnitSourcePacket (xiZeroCopyReflectEquiv q)) =
      hbXiPeierlsUnitSourcePacket q

/-- A possibly nonlinear packet map commutes with one fixed physical clock step. -/
def HBXiPeierlsNonlinearPhysicalClockStepCovariant
    (T : HBXiPeierlsPacket → HBXiPeierlsPacket) (n : ℕ) (t : ℝ) : Prop :=
  ∀ x : HBXiPeierlsPacket,
    T (hbXiPeierlsCenteredQNMPhysicalClockStep n t x) =
      hbXiPeierlsCenteredQNMPhysicalClockStep n t (T x)

/-- Existence of a vacuum-regular nonlinear source exchange commuting with one clock step on one
functional-equation orbit. -/
def HBXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt
    (n : ℕ) (t : ℝ) (q : XiZeroCopy) : Prop :=
  ∃ T : HBXiPeierlsPacket → HBXiPeierlsPacket,
    HBXiPeierlsSourceAxisVacuumRegular T ∧
    HBXiPeierlsUnitSourceReflectionExchangeAt T q ∧
    HBXiPeierlsNonlinearPhysicalClockStepCovariant T n t

private theorem hbXiPeierlsUnitSourcePacket_ne_zero_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 :=
  (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).not.mpr hoff

private theorem xiZeroCopyReflect_re_ne_half_of_ne_half_nonlinear
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≠ 1 / 2 := by
  rw [xiZeroCopyReflect_re_eq_one_sub]
  intro h
  apply hoff
  linarith

private theorem hbXiPeierls_clock_commuting_source_swap_impossible_of_norms
    (T : HBXiPeierlsPacket → HBXiPeierlsPacket)
    (n : ℕ) (t : ℝ) (q : XiZeroCopy)
    (hregular : HBXiPeierlsSourceAxisVacuumRegular T)
    (hexchange : HBXiPeierlsUnitSourceReflectionExchangeAt T q)
    (hclock : HBXiPeierlsNonlinearPhysicalClockStepCovariant T n t)
    (hcontract : ‖hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q‖ < 1)
    (hexpand : 1 < ‖hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t
      (xiZeroCopyReflectEquiv q)‖)
    (hsourceR : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
      (xiZeroCopyReflectEquiv q) ≠ 0) : False := by
  let mu := hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q
  let nu := hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t
    (xiZeroCopyReflectEquiv q)
  let A := d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q
  let B := d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
    (xiZeroCopyReflectEquiv q)
  have hiter : ∀ k : ℕ,
      T (Finsupp.single q (mu ^ k * A)) =
        Finsupp.single (xiZeroCopyReflectEquiv q) (nu ^ k * B) := by
    intro k
    induction k with
    | zero => simpa [mu, nu, A, B, hbXiPeierlsUnitSourcePacket] using hexchange.1
    | succ k ih =>
        have h := hclock (Finsupp.single q (mu ^ k * A))
        rw [hbXiPeierlsCenteredQNMPhysicalClockStep_single, ih,
          hbXiPeierlsCenteredQNMPhysicalClockStep_single] at h
        change T (Finsupp.single q (mu * (mu ^ k * A))) =
          Finsupp.single (xiZeroCopyReflectEquiv q) (nu * (nu ^ k * B)) at h
        calc
          T (Finsupp.single q (mu ^ (k + 1) * A)) =
              T (Finsupp.single q (mu * (mu ^ k * A))) := by
                congr 1
                rw [pow_succ]
                ring_nf
          _ = Finsupp.single (xiZeroCopyReflectEquiv q)
                (nu * (nu ^ k * B)) := h
          _ = Finsupp.single (xiZeroCopyReflectEquiv q)
                (nu ^ (k + 1) * B) := by
                congr 1
                rw [pow_succ]
                ring_nf
  have hpow : Tendsto (fun k : ℕ => mu ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hcontract
  have hinput : Tendsto (fun k : ℕ => mu ^ k * A) atTop (nhds 0) := by
    simpa using hpow.mul_const A
  have himage := hregular q (fun k : ℕ => mu ^ k * A) hinput
    (xiZeroCopyReflectEquiv q)
  have hunstable : Tendsto (fun k : ℕ => nu ^ k * B) atTop (nhds 0) := by
    apply himage.congr'
    exact Filter.Eventually.of_forall fun k => by
      have hk := congrArg
        (fun x : HBXiPeierlsPacket => x (xiZeroCopyReflectEquiv q)) (hiter k)
      simpa using hk
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hsourceR
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hunstable) ‖B‖ hBpos
  have hsmall := hN N le_rfl
  rw [dist_zero_right, norm_mul, norm_pow] at hsmall
  have hlarge : ‖B‖ ≤ ‖nu‖ ^ N * ‖B‖ := by
    nlinarith [one_le_pow₀ hexpand.le (n := N)]
  exact (not_lt_of_ge hlarge) hsmall

/-- **Continuous/nonlinear HB route kill.** On a tilted Xi orbit, no source-axis vacuum-regular
map can exchange the two literal BM sources and commute with any nonzero physical clock step. -/
theorem not_exists_hbXiPeierls_vacuumRegular_sourceExchange_clockCovariant_of_offLine
    (n : ℕ) {t : ℝ} (ht : t ≠ 0) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ HBXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt n t q := by
  rintro ⟨T, hregular, hexchange, hclock⟩
  have htilt : t * ((1 / 2 - (q.1 : ℂ).re) / 2) ≠ 0 := by
    apply mul_ne_zero ht
    intro h
    apply hoff
    linarith
  have hsource : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 :=
    hbXiPeierlsUnitSourcePacket_ne_zero_of_offLine q hoff
  have hoffR := xiZeroCopyReflect_re_ne_half_of_ne_half_nonlinear q hoff
  have hsourceR : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
      (xiZeroCopyReflectEquiv q) ≠ 0 :=
    hbXiPeierlsUnitSourcePacket_ne_zero_of_offLine (xiZeroCopyReflectEquiv q) hoffR
  rcases lt_or_gt_of_ne htilt with hneg | hpos
  · apply hbXiPeierls_clock_commuting_source_swap_impossible_of_norms
      T n t q hregular hexchange hclock
    · rw [norm_hbXiPeierlsCenteredQNMPhysicalClockMultiplier,
        Real.exp_lt_one_iff]
      exact hneg
    · rw [norm_hbXiPeierlsCenteredQNMPhysicalClockMultiplier_reflect,
        Real.one_lt_exp_iff]
      linarith
    · exact hsourceR
  · apply hbXiPeierls_clock_commuting_source_swap_impossible_of_norms
      T n t (xiZeroCopyReflectEquiv q) hregular
      ⟨by simpa using hexchange.2, by simpa using hexchange.1⟩ hclock
    · rw [norm_hbXiPeierlsCenteredQNMPhysicalClockMultiplier,
        xiZeroCopyReflect_re_eq_one_sub, Real.exp_lt_one_iff]
      linarith
    · simpa only [xiZeroCopyReflectEquiv_apply_apply] using
        (show 1 < ‖hbXiPeierlsCenteredQNMPhysicalClockMultiplier n t q‖ by
          rw [norm_hbXiPeierlsCenteredQNMPhysicalClockMultiplier,
            Real.one_lt_exp_iff]
          exact hpos)
    · simpa only [xiZeroCopyReflectEquiv_apply_apply] using hsource

/-- Exact nonlinear classification: at any nonzero physical time, a vacuum-regular source
exchange commuting with the centered-QNM clock exists exactly on the critical wall. -/
theorem hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff
    (n : ℕ) {t : ℝ} (ht : t ≠ 0) (q : XiZeroCopy) :
    HBXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt n t q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hexists
    by_contra hoff
    exact not_exists_hbXiPeierls_vacuumRegular_sourceExchange_clockCovariant_of_offLine
      n ht q hoff hexists
  · intro hline
    have hsource : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0 :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    have hlineR : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 := by
      rw [xiZeroCopyReflect_re_eq_one_sub, hline]
      norm_num
    have hsourceR : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
        (xiZeroCopyReflectEquiv q) = 0 :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero
        (xiZeroCopyReflectEquiv q)).mpr hlineR
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro r c hc s
      exact tendsto_const_nhds
    · simp [HBXiPeierlsUnitSourceReflectionExchangeAt,
        hbXiPeierlsUnitSourcePacket, hsource, hsourceR]
    · intro x
      simp

/-- Universal existence of even an arbitrary vacuum-regular nonlinear source exchange at one
nonzero fixed clock time is exactly RH. -/
theorem forall_hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff_rh
    (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (∀ q : XiZeroCopy,
      HBXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt n t q) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
      n).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mpr
    exact (hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff n ht q).mp (h q)
  · intro hRH q
    apply (hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff n ht q).mpr
    have hselector :=
      (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
        n).mpr hRH q
    exact (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff n q).mp hselector

/-- Closed certificate killing every static vacuum-regular nonlinear source transport as an HB
producer. The only survivors must lose vacuum regularity, change literal sources, or depend on
time rather than commute with its predeclared clock. -/
def D4HBVacuumRegularNonlinearSourceGaugeClockCovarianceRouteKilled : Prop :=
  (∀ (n : ℕ) (t : ℝ), t ≠ 0 → ∀ q : XiZeroCopy,
    HBXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt n t q ↔
      (q.1 : ℂ).re = 1 / 2) ∧
  ∀ (n : ℕ) (t : ℝ), t ≠ 0 →
    ((∀ q : XiZeroCopy,
      HBXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt n t q) ↔
      RiemannHypothesis)

theorem d4HBVacuumRegularNonlinearSourceGaugeClockCovarianceRouteKilled :
    D4HBVacuumRegularNonlinearSourceGaugeClockCovarianceRouteKilled := by
  exact ⟨fun n t ht q =>
      hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff n ht q,
    fun n t ht =>
      forall_hbXiPeierlsExistsVacuumRegularNonlinearSourceExchangeAt_iff_rh n ht⟩

end

end RHTower
