import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo

/-!
# Hawking--Teukolsky mediator pole multiplicity

The functional-reflection mediator lies at a collision of the two Birmingham--Mokhtari QNM
branches, so its physical boundary Green function has a double pole. The reflected real-pair
mediator has the same double pole exactly on the critical line and a simple pole when tilted.

This is an exact hypergeometric scattering statement. It does not assert that the full reduced
second-order Teukolsky source excites either principal part.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

lemma d4BMXiReflectedMediatorRadialB_eq (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialB
        (d4BMXiReflectedRealPairFrequency n q)
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) =
      (((q.1 : ℂ).re - 3 / 2 - 2 * n : ℝ) : ℂ) := by
  rw [d4BMXiReflectedRealPairFrequency_eq_mediatorQNM,
    thetaCuspHawkingHypergeometricRadialB_qnmPlus,
    d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4BMXiReflectedMediatorRadialB_ne_neg_nat_of_tilt
    (n m : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    thetaCuspHawkingHypergeometricRadialB
        (d4BMXiReflectedRealPairFrequency n q)
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) ≠ -(m : ℂ) := by
  rw [d4BMXiReflectedMediatorRadialB_eq]
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hmloR : ((2 * n : ℕ) : ℝ) < (m : ℝ) := by
    push_cast at hre ⊢
    linarith
  have hmhiR : (m : ℝ) < ((2 * n + 2 : ℕ) : ℝ) := by
    push_cast at hre ⊢
    linarith
  have hmlo : 2 * n < m := by exact_mod_cast hmloR
  have hmhi : m < 2 * n + 2 := by exact_mod_cast hmhiR
  have hm : m = 2 * n + 1 := by omega
  subst m
  norm_num at hre
  apply htilt
  linarith

lemma d4BMXiReflectedMediatorJostMinus_ne_zero_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    thetaCuspHawkingHypergeometricJostMinus
        (d4BMXiReflectedRealPairFrequency n q)
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) ≠ 0 := by
  unfold thetaCuspHawkingHypergeometricJostMinus
    GaloisForLFunctions.reciprocalGammaEntire
  exact inv_ne_zero (Complex.Gamma_ne_zero fun m =>
    d4BMXiReflectedMediatorRadialB_ne_neg_nat_of_tilt n m q htilt)

lemma d4BMXiReflectedMediatorJostMinus_order_eq_zero_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricJostMinus omega
          (d4BMXiReflectedRealPairMediatorSpectralPoint q))
        (d4BMXiReflectedRealPairFrequency n q) = 0 := by
  have han := thetaCuspHawkingHypergeometricAnalyticAt_jostMinus
    (d4BMXiReflectedRealPairFrequency n q)
    (d4BMXiReflectedRealPairMediatorSpectralPoint q)
  rw [han.meromorphicOrderAt_eq,
    (han.analyticOrderAt_eq_zero).mpr
      (d4BMXiReflectedMediatorJostMinus_ne_zero_of_tilt n q htilt)]
  rfl

lemma d4BMXiReflectedMediatorJostPlus_order_eq_one
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricJostPlus omega
          (d4BMXiReflectedRealPairMediatorSpectralPoint q))
        (d4BMXiReflectedRealPairFrequency n q) = (1 : ℤ) := by
  rw [d4BMXiReflectedRealPairFrequency_eq_mediatorQNM]
  exact thetaCuspHawkingHypergeometricOrder_jostPlus_qnm (2 * n) _

lemma d4BMXiReflectedMediatorFullJost_order_eq_one_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricJost omega
          (d4BMXiReflectedRealPairMediatorSpectralPoint q))
        (d4BMXiReflectedRealPairFrequency n q) = (1 : ℤ) := by
  let omega := d4BMXiReflectedRealPairFrequency n q
  let z := d4BMXiReflectedRealPairMediatorSpectralPoint q
  have hp := (thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega z).meromorphicAt
  have hm := (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega z).meromorphicAt
  change meromorphicOrderAt
    ((fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w z) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w z)) omega = _
  rw [meromorphicOrderAt_mul hp hm,
    d4BMXiReflectedMediatorJostPlus_order_eq_one,
    d4BMXiReflectedMediatorJostMinus_order_eq_zero_of_tilt n q htilt]
  rfl

lemma d4BMXiReflectedMediatorRadialC_eq (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialC
        (d4BMXiReflectedRealPairFrequency n q) =
      (((q.1 : ℂ).re - 4 * n - 2 : ℝ) : ℂ) := by
  rw [d4BMXiReflectedRealPairFrequency_eq]
  unfold thetaCuspHawkingHypergeometricRadialC
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4BMXiReflectedMediatorRadialC_ne_neg_nat
    (n m : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingHypergeometricRadialC
        (d4BMXiReflectedRealPairFrequency n q) ≠ -(m : ℂ) := by
  rw [d4BMXiReflectedMediatorRadialC_eq]
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hmloR : ((4 * n + 1 : ℕ) : ℝ) < (m : ℝ) := by
    push_cast at hre ⊢
    linarith
  have hmhiR : (m : ℝ) < ((4 * n + 2 : ℕ) : ℝ) := by
    push_cast at hre ⊢
    linarith
  have hmlo : 4 * n + 1 < m := by exact_mod_cast hmloR
  have hmhi : m < 4 * n + 2 := by exact_mod_cast hmhiR
  omega

lemma d4BMXiReflectedMediatorPhysicalGammaPrefactor_order_eq_zero
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
        Complex.Gamma (1 / 2 : ℂ))
      (d4BMXiReflectedRealPairFrequency n q) = 0 := by
  let omega := d4BMXiReflectedRealPairFrequency n q
  have hanC := thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
    (d4BMXiReflectedMediatorRadialC_ne_neg_nat n · q)
  have han : AnalyticAt ℂ
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
        Complex.Gamma (1 / 2 : ℂ)) omega := hanC.mul analyticAt_const
  have hne : Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
      Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
    mul_ne_zero
      (Complex.Gamma_ne_zero (d4BMXiReflectedMediatorRadialC_ne_neg_nat n · q))
      thetaCuspHawkingHypergeometricGamma_half_ne_zero
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).mpr hne]
  rfl

/-- Tilted reflected mediator has one physical Green pole, not a branch collision. -/
theorem d4BMXiReflectedMediatorPhysicalJost_order_eq_one_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q))
      (d4BMXiReflectedRealPairFrequency n q) = (1 : ℤ) := by
  let omega := d4BMXiReflectedRealPairFrequency n q
  let z := d4BMXiReflectedRealPairMediatorSpectralPoint q
  have hpref : MeromorphicAt
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
        Complex.Gamma (1 / 2 : ℂ)) omega :=
    (thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
      (d4BMXiReflectedMediatorRadialC_ne_neg_nat n · q) |>.mul analyticAt_const).meromorphicAt
  have hJost : MeromorphicAt
      (fun w : ℂ => thetaCuspHawkingHypergeometricJost w z) omega :=
    ((thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega z).mul
      (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega z)).meromorphicAt
  change meromorphicOrderAt
    ((fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
      Complex.Gamma (1 / 2 : ℂ)) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJost w z)) omega = _
  rw [meromorphicOrderAt_mul hpref hJost,
    d4BMXiReflectedMediatorPhysicalGammaPrefactor_order_eq_zero,
    d4BMXiReflectedMediatorFullJost_order_eq_one_of_tilt n q htilt]
  rfl

/-- Universal mediator is simultaneously a plus QNM and the next minus QNM. -/
lemma d4BMFunctionalMediatorFrequency_eq_qnmMinus (n : ℕ) :
    d4BMFunctionalReflectionMediatorFrequency n n =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus (2 * n + 1)
        d4BMFunctionalReflectionMediatorSpectralPoint := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    d4BMFunctionalReflectionMediatorSpectralPoint_angularMomentum]
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4BMFunctionalReflectionMediatorFrequency]
  push_cast
  ring

lemma d4BMFunctionalMediatorFullJost_order_eq_two (n : ℕ) :
    meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricJost omega
          d4BMFunctionalReflectionMediatorSpectralPoint)
        (d4BMFunctionalReflectionMediatorFrequency n n) = (2 : ℤ) := by
  let omega := d4BMFunctionalReflectionMediatorFrequency n n
  let z := d4BMFunctionalReflectionMediatorSpectralPoint
  have hp := (thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega z).meromorphicAt
  have hm := (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega z).meromorphicAt
  have hop : meromorphicOrderAt
      (fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w z) omega = (1 : ℤ) := by
    dsimp [omega, z]
    rw [d4BMFunctionalReflectionMediatorFrequency_eq_qnmPlus]
    exact thetaCuspHawkingHypergeometricOrder_jostPlus_qnm (n + n) _
  have hom : meromorphicOrderAt
      (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w z) omega = (1 : ℤ) := by
    dsimp [omega, z]
    rw [d4BMFunctionalMediatorFrequency_eq_qnmMinus]
    exact thetaCuspHawkingHypergeometricOrder_jostMinus_qnm (2 * n + 1) _
  change meromorphicOrderAt
    ((fun w : ℂ => thetaCuspHawkingHypergeometricJostPlus w z) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJostMinus w z)) omega = _
  rw [meromorphicOrderAt_mul hp hm, hop, hom]
  rfl

lemma d4BMFunctionalMediatorRadialC_eq (n : ℕ) :
    thetaCuspHawkingHypergeometricRadialC
        (d4BMFunctionalReflectionMediatorFrequency n n) =
      (-((4 * n : ℕ) : ℂ) - 3 / 2) := by
  unfold thetaCuspHawkingHypergeometricRadialC
    d4BMFunctionalReflectionMediatorFrequency
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4BMFunctionalMediatorRadialC_ne_neg_nat (n m : ℕ) :
    thetaCuspHawkingHypergeometricRadialC
        (d4BMFunctionalReflectionMediatorFrequency n n) ≠ -(m : ℂ) := by
  rw [d4BMFunctionalMediatorRadialC_eq]
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hmloR : ((4 * n + 1 : ℕ) : ℝ) < (m : ℝ) := by
    push_cast at hre ⊢
    linarith
  have hmhiR : (m : ℝ) < ((4 * n + 2 : ℕ) : ℝ) := by
    push_cast at hre ⊢
    linarith
  have hmlo : 4 * n + 1 < m := by exact_mod_cast hmloR
  have hmhi : m < 4 * n + 2 := by exact_mod_cast hmhiR
  omega

lemma d4BMFunctionalMediatorPhysicalGammaPrefactor_order_eq_zero (n : ℕ) :
    meromorphicOrderAt
      (fun omega : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
        Complex.Gamma (1 / 2 : ℂ))
      (d4BMFunctionalReflectionMediatorFrequency n n) = 0 := by
  let omega := d4BMFunctionalReflectionMediatorFrequency n n
  have hanC := thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
    (d4BMFunctionalMediatorRadialC_ne_neg_nat n)
  have han : AnalyticAt ℂ
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
        Complex.Gamma (1 / 2 : ℂ)) omega := hanC.mul analyticAt_const
  have hne : Complex.Gamma (thetaCuspHawkingHypergeometricRadialC omega) *
      Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
    mul_ne_zero
      (Complex.Gamma_ne_zero (d4BMFunctionalMediatorRadialC_ne_neg_nat n))
      thetaCuspHawkingHypergeometricGamma_half_ne_zero
  rw [han.meromorphicOrderAt_eq, (han.analyticOrderAt_eq_zero).mpr hne]
  rfl

/-- Universal functional mediator is a physical double Jost zero. -/
theorem d4BMFunctionalMediatorPhysicalJost_order_eq_two (n : ℕ) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
        d4BMFunctionalReflectionMediatorSpectralPoint)
      (d4BMFunctionalReflectionMediatorFrequency n n) = (2 : ℤ) := by
  let omega := d4BMFunctionalReflectionMediatorFrequency n n
  let z := d4BMFunctionalReflectionMediatorSpectralPoint
  have hpref : MeromorphicAt
      (fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
        Complex.Gamma (1 / 2 : ℂ)) omega :=
    (thetaCuspHawkingHypergeometricAnalyticAt_gammaRadialC_of_ne_neg_nat omega
      (d4BMFunctionalMediatorRadialC_ne_neg_nat n) |>.mul analyticAt_const).meromorphicAt
  have hJost : MeromorphicAt
      (fun w : ℂ => thetaCuspHawkingHypergeometricJost w z) omega :=
    ((thetaCuspHawkingHypergeometricAnalyticAt_jostPlus omega z).mul
      (thetaCuspHawkingHypergeometricAnalyticAt_jostMinus omega z)).meromorphicAt
  change meromorphicOrderAt
    ((fun w : ℂ => Complex.Gamma (thetaCuspHawkingHypergeometricRadialC w) *
      Complex.Gamma (1 / 2 : ℂ)) *
      (fun w : ℂ => thetaCuspHawkingHypergeometricJost w z)) omega = _
  rw [meromorphicOrderAt_mul hpref hJost,
    d4BMFunctionalMediatorPhysicalGammaPrefactor_order_eq_zero,
    d4BMFunctionalMediatorFullJost_order_eq_two]
  rfl

lemma d4BMXiReflectedMediatorSpectralPoint_eq_functional_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    d4BMXiReflectedRealPairMediatorSpectralPoint q =
      d4BMFunctionalReflectionMediatorSpectralPoint := by
  simp [d4BMXiReflectedRealPairMediatorSpectralPoint,
    d4BMFunctionalReflectionMediatorSpectralPoint, hline]
  ring

lemma d4BMXiReflectedMediatorPhysicalJost_order_eq_two_of_re_eq_half
    (n : ℕ) (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q))
      (d4BMXiReflectedRealPairFrequency n q) = (2 : ℤ) := by
  rw [(d4BMXiReflectedRealPairFrequency_eq_functionalMediator_iff n q).mpr hline,
    d4BMXiReflectedMediatorSpectralPoint_eq_functional_of_re_eq_half q hline]
  exact d4BMFunctionalMediatorPhysicalJost_order_eq_two n

/-- Reflected mediator is a double Jost zero exactly on the critical line. -/
theorem d4BMXiReflectedMediatorPhysicalJost_order_eq_two_iff
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q))
      (d4BMXiReflectedRealPairFrequency n q) = (2 : ℤ) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro horder
    by_contra htilt
    have hone := d4BMXiReflectedMediatorPhysicalJost_order_eq_one_of_tilt n q htilt
    rw [hone] at horder
    norm_num at horder
  · exact d4BMXiReflectedMediatorPhysicalJost_order_eq_two_of_re_eq_half n q

lemma d4BMXiReflectedMediatorPhysicalGreen_order_eq_neg_one_of_tilt
    (n : ℕ) (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q))
      (d4BMXiReflectedRealPairFrequency n q) = ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
      (d4BMXiReflectedRealPairMediatorSpectralPoint q))⁻¹) _ = _
  rw [meromorphicOrderAt_inv,
    d4BMXiReflectedMediatorPhysicalJost_order_eq_one_of_tilt n q htilt]
  rfl

/-- Reflected mediator has a physical double Green pole exactly on the critical line. -/
theorem d4BMXiReflectedMediatorPhysicalGreen_order_eq_neg_two_iff
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q))
      (d4BMXiReflectedRealPairFrequency n q) = ((-2 : ℤ) : WithTop ℤ) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro horder
    by_contra htilt
    have hone := d4BMXiReflectedMediatorPhysicalGreen_order_eq_neg_one_of_tilt n q htilt
    rw [hone] at horder
    norm_num at horder
  · intro hline
    change meromorphicOrderAt
      ((fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
        (d4BMXiReflectedRealPairMediatorSpectralPoint q))⁻¹) _ = _
    rw [meromorphicOrderAt_inv,
      d4BMXiReflectedMediatorPhysicalJost_order_eq_two_of_re_eq_half n q hline]
    rfl

lemma d4BMFunctionalMediatorPhysicalGreen_order_eq_neg_two (n : ℕ) :
    meromorphicOrderAt
      (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega
        d4BMFunctionalReflectionMediatorSpectralPoint)
      (d4BMFunctionalReflectionMediatorFrequency n n) = ((-2 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt
    ((fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega
      d4BMFunctionalReflectionMediatorSpectralPoint)⁻¹) _ = _
  rw [meromorphicOrderAt_inv, d4BMFunctionalMediatorPhysicalJost_order_eq_two]
  rfl

/-- The two quadratic mediator channels have equal physical pole multiplicity exactly on-line. -/
theorem d4BMXiMediatorPhysicalGreen_orders_eq_iff (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega
          (d4BMXiReflectedRealPairMediatorSpectralPoint q))
        (d4BMXiReflectedRealPairFrequency n q) =
      meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega
          d4BMFunctionalReflectionMediatorSpectralPoint)
        (d4BMFunctionalReflectionMediatorFrequency n n) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMFunctionalMediatorPhysicalGreen_order_eq_neg_two]
  exact d4BMXiReflectedMediatorPhysicalGreen_order_eq_neg_two_iff n q

/-- Global equality of the two mediator pole multiplicities at one overtone. -/
def D4BMXiMediatorPhysicalPoleMultiplicityMatches (n : ℕ) : Prop :=
  ∀ q : XiZeroCopy,
    meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega
          (d4BMXiReflectedRealPairMediatorSpectralPoint q))
        (d4BMXiReflectedRealPairFrequency n q) =
      meromorphicOrderAt
        (fun omega : ℂ => thetaCuspHawkingHypergeometricPhysicalBoundaryGreen omega
          d4BMFunctionalReflectionMediatorSpectralPoint)
        (d4BMFunctionalReflectionMediatorFrequency n n)

/-- RH iff reflected and functional quadratic mediators have matching physical pole order. -/
theorem riemannHypothesis_iff_d4BMXiMediatorPhysicalPoleMultiplicityMatches (n : ℕ) :
    RiemannHypothesis ↔ D4BMXiMediatorPhysicalPoleMultiplicityMatches n := by
  constructor
  · intro hRH q
    exact (d4BMXiMediatorPhysicalGreen_orders_eq_iff n q).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)
  · intro hmatch
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline := (d4BMXiMediatorPhysicalGreen_orders_eq_iff n q).1 (hmatch q)
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [xiSpectralPoint, hline]

end

end RHTower
