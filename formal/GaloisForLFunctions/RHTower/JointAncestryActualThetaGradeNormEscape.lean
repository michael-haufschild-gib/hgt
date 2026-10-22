import GaloisForLFunctions.RHTower.JointAncestryCriticalMixedPrimeGradeIncidence
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional

/-!
# JAS actual completed-theta grade norm escape

The actual completed-theta Mellin grades cannot replace the normalized packets in the canonical
injective JAS synthesis. Their `L²` norms tend to infinity: on any fixed positive interval, grade
`r` multiplies the strictly positive completed-theta source by at least `exp r`.

Consequently no bounded operator from `ell²(Primes)` sends every coordinate basis vector to the
critical singleton prime character in its canonical grade with the actual completed-theta grade
norm. Thus the normalized injective survivor does not admit a bounded coefficient-faithful
identification with the actual all-grade chain. A viable JAS successor must use a genuinely closed
unbounded, support-cutting completion.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Fixed positive-interval mass used to expose actual theta-grade norm escape. -/
def jasActualThetaPositiveIntervalMass : ℝ :=
  ∫ x in Set.Icc (1 : ℝ) 2, thetaCuspFullSource x ^ 2

private theorem continuous_thetaCuspFullSource_for_grade_escape :
    Continuous thetaCuspFullSource := by
  rw [show thetaCuspFullSource = fun x =>
      thetaCuspTailDerivative 2 x - (1 / 4 : ℝ) * thetaCuspTailDerivative 0 x by
    funext x
    exact thetaCuspFullSource_eq_tail_second_sub x]
  exact (differentiable_thetaCuspTailDerivative 2).continuous.sub
    (continuous_const.mul (differentiable_thetaCuspTailDerivative 0).continuous)

/-- The completed theta source carries strictly positive square mass on `[1,2]`. -/
theorem jasActualThetaPositiveIntervalMass_pos :
    0 < jasActualThetaPositiveIntervalMass := by
  have hcont : Continuous (fun x : ℝ => thetaCuspFullSource x ^ 2) :=
    continuous_thetaCuspFullSource_for_grade_escape.pow 2
  have hint : IntegrableOn (fun x : ℝ => thetaCuspFullSource x ^ 2)
      (Set.Icc (1 : ℝ) 2) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  rw [jasActualThetaPositiveIntervalMass,
    setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg (thetaCuspFullSource x)) hint]
  have hsupp : Function.support (fun x : ℝ => thetaCuspFullSource x ^ 2) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact pow_ne_zero 2 (ne_of_gt (thetaCuspFullSource_pos x))
  rw [hsupp, Set.univ_inter]
  norm_num

/-- Exact integral formula for the squared norm of an actual completed-theta grade. -/
theorem norm_sq_jointAncestryCompletedThetaGradeL2 (r : ℕ) :
    ‖jointAncestryCompletedThetaGradeL2 r‖ ^ 2 =
      ∫ x : ℝ, Real.exp (2 * (r : ℝ) * x) * thetaCuspFullSource x ^ 2 := by
  rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [jointAncestryCompletedThetaGradeL2_coeFn r] with x hx
  rw [hx]
  norm_cast
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (thetaCuspFullSource_pos x)]
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring_nf

private theorem integrable_jasActualThetaGradeNormSq (r : ℕ) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * (r : ℝ) * x) * thetaCuspFullSource x ^ 2) := by
  let f : ℝ → ℂ := fun x =>
    ((Real.exp ((r : ℝ) * x) * thetaCuspFullSource x : ℝ) : ℂ)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul
          continuous_thetaCuspFullSource_for_grade_escape)
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

/-- A fixed positive interval gives an exponential lower bound for every actual grade norm. -/
theorem exp_mul_jasActualThetaPositiveIntervalMass_le_norm_sq (r : ℕ) :
    Real.exp (2 * (r : ℝ)) * jasActualThetaPositiveIntervalMass ≤
      ‖jointAncestryCompletedThetaGradeL2 r‖ ^ 2 := by
  rw [norm_sq_jointAncestryCompletedThetaGradeL2]
  have hsourceInt : IntegrableOn (fun x : ℝ => thetaCuspFullSource x ^ 2)
      (Set.Icc (1 : ℝ) 2) :=
    (continuous_thetaCuspFullSource_for_grade_escape.pow 2).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hlowInt : IntegrableOn (fun x : ℝ =>
      Real.exp (2 * (r : ℝ)) * thetaCuspFullSource x ^ 2)
      (Set.Icc (1 : ℝ) 2) := hsourceInt.const_mul _
  have hfullInt := integrable_jasActualThetaGradeNormSq r
  calc
    Real.exp (2 * (r : ℝ)) * jasActualThetaPositiveIntervalMass =
        ∫ x in Set.Icc (1 : ℝ) 2,
          Real.exp (2 * (r : ℝ)) * thetaCuspFullSource x ^ 2 := by
      rw [jasActualThetaPositiveIntervalMass, MeasureTheory.integral_const_mul]
    _ ≤ ∫ x in Set.Icc (1 : ℝ) 2,
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

theorem exp_mul_sqrt_jasActualThetaPositiveIntervalMass_le_norm (r : ℕ) :
    Real.exp (r : ℝ) * Real.sqrt jasActualThetaPositiveIntervalMass ≤
      ‖jointAncestryCompletedThetaGradeL2 r‖ := by
  have hmassNonneg : 0 ≤ jasActualThetaPositiveIntervalMass :=
    jasActualThetaPositiveIntervalMass_pos.le
  have hsq := exp_mul_jasActualThetaPositiveIntervalMass_le_norm_sq r
  have hexpSq : Real.exp (r : ℝ) ^ 2 = Real.exp (2 * (r : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrtSq : Real.sqrt jasActualThetaPositiveIntervalMass ^ 2 =
      jasActualThetaPositiveIntervalMass := Real.sq_sqrt hmassNonneg
  have hleftNonneg :
      0 ≤ Real.exp (r : ℝ) * Real.sqrt jasActualThetaPositiveIntervalMass :=
    mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hrightNonneg : 0 ≤ ‖jointAncestryCompletedThetaGradeL2 r‖ := norm_nonneg _
  nlinarith [sq_nonneg
    (‖jointAncestryCompletedThetaGradeL2 r‖ -
      Real.exp (r : ℝ) * Real.sqrt jasActualThetaPositiveIntervalMass)]

/-- Actual completed-theta grade norms escape every bounded set. -/
theorem tendsto_norm_jointAncestryCompletedThetaGradeL2_atTop :
    Filter.Tendsto (fun r : ℕ => ‖jointAncestryCompletedThetaGradeL2 r‖)
      Filter.atTop Filter.atTop := by
  have hsqrtPos : 0 < Real.sqrt jasActualThetaPositiveIntervalMass :=
    Real.sqrt_pos.2 jasActualThetaPositiveIntervalMass_pos
  have hexp : Filter.Tendsto (fun r : ℕ => Real.exp (r : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hlow : Filter.Tendsto
      (fun r : ℕ => Real.exp (r : ℝ) *
        Real.sqrt jasActualThetaPositiveIntervalMass)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hsqrtPos hexp
  exact Filter.tendsto_atTop_mono' Filter.atTop
    (Filter.Eventually.of_forall fun r =>
      exp_mul_sqrt_jasActualThetaPositiveIntervalMass_le_norm r)
    hlow

/-- Canonical prime grading carrying the norm of the corresponding actual completed-theta
Mellin grade. -/
def jointAncestryCriticalPrimeActualThetaInjectiveGradePacket
    (t : ℝ) (p : Nat.Primes) :
    L2Amplification ℕ (JASCriticalPrimePoissonL2 t) :=
  l2Single (natEquivPrimes.symm p)
    ((‖jointAncestryCompletedThetaGradeL2 (natEquivPrimes.symm p)‖ : ℂ) •
      criticalPrimeSingletonCharacterL2 t p)

theorem norm_jointAncestryCriticalPrimeActualThetaInjectiveGradePacket
    (t : ℝ) (p : Nat.Primes) :
    ‖jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p‖ =
      ‖jointAncestryCompletedThetaGradeL2 (natEquivPrimes.symm p)‖ := by
  rw [jointAncestryCriticalPrimeActualThetaInjectiveGradePacket,
    l2Single_apply, lp.norm_single (by norm_num), norm_smul,
    GaloisForLFunctions.HTGeometry.norm_criticalPrimeSingletonCharacterL2]
  simp

/-- Bounded synthesis of all actual theta-weighted canonical injective prime packets. -/
def JASCriticalPrimeActualThetaInjectiveGradeSynthesis (t : ℝ) : Prop :=
  ∃ T : HTGeometry.IndexedEllTwo Nat.Primes →L[ℂ]
      L2Amplification ℕ (JASCriticalPrimePoissonL2 t),
    ∀ p, T (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      jointAncestryCriticalPrimeActualThetaInjectiveGradePacket t p

/-- Closed JAS no-go: the canonical injective normalized synthesis cannot be upgraded to the
actual completed-theta grade norms by any bounded operator. -/
theorem not_JASCriticalPrimeActualThetaInjectiveGradeSynthesis (t : ℝ) :
    ¬ JASCriticalPrimeActualThetaInjectiveGradeSynthesis t := by
  rintro ⟨T, hT⟩
  have hbound : ∀ r : ℕ,
      ‖jointAncestryCompletedThetaGradeL2 r‖ ≤ ‖T‖ := by
    intro r
    let p : Nat.Primes := natEquivPrimes r
    have hop := T.le_opNorm (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)
    rw [hT, norm_jointAncestryCriticalPrimeActualThetaInjectiveGradePacket,
      show natEquivPrimes.symm p = r by simp [p],
      (HTGeometry.ellTwoCoordinateBasis Nat.Primes).orthonormal.norm_eq_one,
      mul_one] at hop
    exact hop
  obtain ⟨r, hr⟩ :=
    (tendsto_norm_jointAncestryCompletedThetaGradeL2_atTop.eventually_gt_atTop ‖T‖).exists
  exact (not_lt_of_ge (hbound r)) hr

end

end RHTower
