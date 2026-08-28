import GaloisForLFunctions.RHTower.JointAncestryActualThetaClosedUnboundedGradeSynthesis

/-!
# JAS actual-theta adjacent-grade shift escape

The actual completed-theta ladder grows too quickly for any bounded grade-successor action.
Every translated unit interval contains positive theta-source square mass, so the norm of grade
`r` dominates an exponential with any prescribed base.  If all adjacent norm quotients had one
finite ceiling, iteration would impose one fixed exponential upper bound.  These statements are
incompatible.

Consequently no bounded operator advances every literal completed-theta Mellin grade, and no
bounded operator advances every corresponding critical prime-Poisson amplified packet.  Thus a
JAS completion that encodes prime-support cardinality by theta grade cannot represent insertion
by a bounded shift.  The surviving source-linear completion must be genuinely unbounded and
cross-coordinate; separable bounded grade shifting is closed negatively.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace RHTower

noncomputable section

/-- Positive theta-source square mass on an arbitrary translated unit interval. -/
def jasActualThetaIntervalMass (A : ℝ) : ℝ :=
  ∫ x in Set.Icc A (A + 1), thetaCuspFullSource x ^ 2

theorem jasActualThetaIntervalMass_pos (A : ℝ) :
    0 < jasActualThetaIntervalMass A := by
  have hcont : Continuous (fun x : ℝ => thetaCuspFullSource x ^ 2) :=
    contDiff_thetaCuspFullSource.continuous.pow 2
  have hint : IntegrableOn (fun x : ℝ => thetaCuspFullSource x ^ 2)
      (Set.Icc A (A + 1)) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  rw [jasActualThetaIntervalMass,
    setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg (thetaCuspFullSource x)) hint]
  have hsupp : Function.support (fun x : ℝ => thetaCuspFullSource x ^ 2) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact pow_ne_zero 2 (ne_of_gt (thetaCuspFullSource_pos x))
  rw [hsupp, Set.univ_inter]
  simp

private theorem integrable_jasActualThetaGradeNormSq_for_shiftEscape (r : ℕ) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * (r : ℝ) * x) * thetaCuspFullSource x ^ 2) := by
  let f : ℝ → ℂ := fun x =>
    ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
          contDiff_thetaCuspFullSource.continuous)
  have hnorm : Integrable (fun x => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hfcont.aestronglyMeasurable).1
      (jointAncestry_thetaCuspFullSource_expWeight_memLp r)
  refine hnorm.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only [f]
  norm_cast
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (thetaCuspFullSource_pos x)]
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring_nf

/-- Every translated positive interval supplies its own exponential lower bound for all actual
completed-theta grade norms. -/
theorem exp_mul_sqrt_jasActualThetaIntervalMass_le_norm
    (A : ℝ) (r : ℕ) :
    Real.exp ((r : ℝ) * A) * Real.sqrt (jasActualThetaIntervalMass A) ≤
      ‖jointAncestryCompletedThetaGradeL2 r‖ := by
  have hmassNonneg : 0 ≤ jasActualThetaIntervalMass A :=
    (jasActualThetaIntervalMass_pos A).le
  have hsourceInt : IntegrableOn (fun x : ℝ => thetaCuspFullSource x ^ 2)
      (Set.Icc A (A + 1)) :=
    (contDiff_thetaCuspFullSource.continuous.pow 2).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hlowInt : IntegrableOn (fun x : ℝ =>
      Real.exp (2 * (r : ℝ) * A) * thetaCuspFullSource x ^ 2)
      (Set.Icc A (A + 1)) := hsourceInt.const_mul _
  have hfullInt := integrable_jasActualThetaGradeNormSq_for_shiftEscape r
  have hsq : Real.exp (2 * (r : ℝ) * A) * jasActualThetaIntervalMass A ≤
      ‖jointAncestryCompletedThetaGradeL2 r‖ ^ 2 := by
    rw [norm_sq_jointAncestryCompletedThetaGradeL2]
    calc
      Real.exp (2 * (r : ℝ) * A) * jasActualThetaIntervalMass A =
          ∫ x in Set.Icc A (A + 1),
            Real.exp (2 * (r : ℝ) * A) * thetaCuspFullSource x ^ 2 := by
        rw [jasActualThetaIntervalMass, MeasureTheory.integral_const_mul]
      _ ≤ ∫ x in Set.Icc A (A + 1),
          Real.exp (2 * (r : ℝ) * x) * thetaCuspFullSource x ^ 2 := by
        apply setIntegral_mono_on hlowInt hfullInt.integrableOn measurableSet_Icc
        intro x hx
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply Real.exp_le_exp.mpr
        have hr : 0 ≤ (r : ℝ) := by positivity
        nlinarith [hx.1, hr]
      _ ≤ ∫ x : ℝ,
          Real.exp (2 * (r : ℝ) * x) * thetaCuspFullSource x ^ 2 := by
        exact setIntegral_le_integral hfullInt
          (Filter.Eventually.of_forall fun x => by positivity)
  have hexpSq : Real.exp ((r : ℝ) * A) ^ 2 =
      Real.exp (2 * (r : ℝ) * A) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrtSq : Real.sqrt (jasActualThetaIntervalMass A) ^ 2 =
      jasActualThetaIntervalMass A := Real.sq_sqrt hmassNonneg
  have hleftNonneg :
      0 ≤ Real.exp ((r : ℝ) * A) * Real.sqrt (jasActualThetaIntervalMass A) :=
    mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hrightNonneg : 0 ≤ ‖jointAncestryCompletedThetaGradeL2 r‖ := norm_nonneg _
  nlinarith [sq_nonneg
    (‖jointAncestryCompletedThetaGradeL2 r‖ -
      Real.exp ((r : ℝ) * A) * Real.sqrt (jasActualThetaIntervalMass A))]

/-- **Supergeometric actual-grade escape.** No finite scalar bounds every adjacent quotient of
actual completed-theta grade norms. -/
theorem jointAncestryCompletedThetaGradeNorm_adjacentRatio_unbounded
    (C : ℝ) :
    ∃ r : ℕ, C * ‖jointAncestryCompletedThetaGradeL2 r‖ <
      ‖jointAncestryCompletedThetaGradeL2 (r + 1)‖ := by
  by_cases hC : 0 < C
  · by_contra hnone
    push Not at hnone
    have hiter : ∀ r : ℕ,
        ‖jointAncestryCompletedThetaGradeL2 r‖ ≤
          C ^ r * ‖jointAncestryCompletedThetaGradeL2 0‖ := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          calc
            ‖jointAncestryCompletedThetaGradeL2 (r + 1)‖ ≤
                C * ‖jointAncestryCompletedThetaGradeL2 r‖ := hnone r
            _ ≤ C * (C ^ r * ‖jointAncestryCompletedThetaGradeL2 0‖) := by
              exact mul_le_mul_of_nonneg_left ih hC.le
            _ = C ^ (r + 1) * ‖jointAncestryCompletedThetaGradeL2 0‖ := by ring
    let A : ℝ := Real.log C + 1
    have hmass : 0 < Real.sqrt (jasActualThetaIntervalMass A) :=
      Real.sqrt_pos.2 (jasActualThetaIntervalMass_pos A)
    have hexp : Filter.Tendsto (fun r : ℕ => Real.exp (r : ℝ))
        Filter.atTop Filter.atTop :=
      Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
    have hgrow : Filter.Tendsto
        (fun r : ℕ => Real.exp (r : ℝ) * Real.sqrt (jasActualThetaIntervalMass A))
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_const hmass hexp
    obtain ⟨r, hr⟩ :=
      (hgrow.eventually_gt_atTop ‖jointAncestryCompletedThetaGradeL2 0‖).exists
    have hlower := exp_mul_sqrt_jasActualThetaIntervalMass_le_norm A r
    have hupper := hiter r
    have hpow : Real.exp ((r : ℝ) * A) = C ^ r * Real.exp (r : ℝ) := by
      dsimp only [A]
      rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hC]
      norm_num
    rw [hpow] at hlower
    have hCpow : 0 < C ^ r := pow_pos hC r
    nlinarith
  · refine ⟨0, ?_⟩
    have hzero : 0 < ‖jointAncestryCompletedThetaGradeL2 0‖ :=
      norm_pos_iff.mpr (jointAncestryCompletedThetaGradeL2_ne_zero 0)
    have hone : 0 < ‖jointAncestryCompletedThetaGradeL2 1‖ :=
      norm_pos_iff.mpr (jointAncestryCompletedThetaGradeL2_ne_zero 1)
    have hCle : C ≤ 0 := le_of_not_gt hC
    norm_num
    nlinarith

/-- A bounded operator advancing every literal completed-theta Mellin grade. -/
def JASActualThetaBoundedGradeSuccessor : Prop :=
  ∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
    ∀ r : ℕ,
      T (jointAncestryCompletedThetaGradeL2 r) =
        jointAncestryCompletedThetaGradeL2 (r + 1)

/-- The actual singular-Mellin grade ladder has no bounded successor realization. -/
theorem not_JASActualThetaBoundedGradeSuccessor :
    ¬ JASActualThetaBoundedGradeSuccessor := by
  rintro ⟨T, hT⟩
  obtain ⟨r, hr⟩ :=
    jointAncestryCompletedThetaGradeNorm_adjacentRatio_unbounded ‖T‖
  have hop := T.le_opNorm (jointAncestryCompletedThetaGradeL2 r)
  rw [hT r] at hop
  exact (not_lt_of_ge hop) hr

theorem norm_jointAncestryCriticalPrimeThetaGradePacket
    (t : ℝ) (r : ℕ) :
    ‖jointAncestryCriticalPrimeThetaGradePacket t r‖ =
      ‖jointAncestryCompletedThetaGradeL2 r‖ *
        ‖ContinuousMap.toLp 2
          (GaloisForLFunctions.HTGeometry.primePoissonMeasure
            (1 / 2 : ℝ) t (by norm_num)) ℂ
          (1 : C(GaloisForLFunctions.HTGeometry.PrimeTorus, ℂ))‖ := by
  rw [jointAncestryCriticalPrimeThetaGradePacket,
    GaloisForLFunctions.HTGeometry.l2Single_apply,
    lp.norm_single (by norm_num),
    jointAncestryCriticalPrimeThetaGradePayload, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]

/-- A bounded successor on the actual critical prime-Poisson amplified grade packets. -/
def JASActualThetaBoundedAmplifiedGradeSuccessor (t : ℝ) : Prop :=
  ∃ T : GaloisForLFunctions.HTGeometry.L2Amplification ℕ
        (JASCriticalPrimePoissonL2 t) →L[ℂ]
      GaloisForLFunctions.HTGeometry.L2Amplification ℕ
        (JASCriticalPrimePoissonL2 t),
    ∀ r : ℕ,
      T (jointAncestryCriticalPrimeThetaGradePacket t r) =
        jointAncestryCriticalPrimeThetaGradePacket t (r + 1)

/-- The bounded grade-successor obstruction survives the literal critical prime-Poisson JAS
amplification. -/
theorem not_JASActualThetaBoundedAmplifiedGradeSuccessor (t : ℝ) :
    ¬ JASActualThetaBoundedAmplifiedGradeSuccessor t := by
  rintro ⟨T, hT⟩
  obtain ⟨r, hr⟩ :=
    jointAncestryCompletedThetaGradeNorm_adjacentRatio_unbounded ‖T‖
  have hop := T.le_opNorm (jointAncestryCriticalPrimeThetaGradePacket t r)
  rw [hT r, norm_jointAncestryCriticalPrimeThetaGradePacket,
    norm_jointAncestryCriticalPrimeThetaGradePacket] at hop
  have hone : 0 <
      ‖ContinuousMap.toLp 2
        (GaloisForLFunctions.HTGeometry.primePoissonMeasure
          (1 / 2 : ℝ) t (by norm_num)) ℂ
        (1 : C(GaloisForLFunctions.HTGeometry.PrimeTorus, ℂ))‖ :=
    norm_pos_iff.mpr
      (GaloisForLFunctions.HTGeometry.primePoisson_half_continuousOne_toLp_ne_zero t)
  nlinarith

end

end RHTower
