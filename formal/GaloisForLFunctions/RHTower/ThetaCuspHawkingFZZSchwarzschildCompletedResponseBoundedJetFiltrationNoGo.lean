import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildCompletedResponseRealAxisAnchorNoGo
import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityTomography

/-!
# FZZ--Schwarzschild completed-response bounded-jet filtration no-go

This module kills every fixed finite complex-order jet repair of the completed FZZ response
interpolation route.  The prior anchored Gamma-null core `W` vanishes at every natural response
order and has the exact value `i` at one fixed interior off-critical response point.  For arbitrary
jet depth `N`, the positive gauge

`G_N(z) = 1 + W(z)^(4N+2)`

has contact order `4N+2` at every natural node, is strictly positive on the full real axis,
preserves response reflection, Schwarz reality, order-one growth, and all three completed anchors,
but vanishes at the same off-critical point.  Thus `X G_N` and canonical completed Xi have equal
complex-order derivatives through depth `N` at every physical response order while their nonreal
divisors differ.

The positive survivor is a descending contact filtration inside the anchored positive square-gauge
cone.  Every bounded local-jet observer annihilates a nonzero level.  Only unbounded/full analytic
germ data or genuinely nonlocal complex-order data can survive this obstruction.

**[FALSIFIED] [ROUTE KILL] [PAPER-PROVED] [LEAN-PROVED]** For any fixed finite depth,
completed physical response jets plus the strongest prior real-axis package control nonreal zeros.

**[NOVELTY AUDIT]** Multiple/Hermite sampling and contact powers are classical.  Corpus and
literature searches through 2026-08-30 found no theorem combining the full natural response ladder,
completed FZZ symmetries and anchors, global positive real-axis phase, order-one growth, arbitrary
bounded complex-order jet depth, and an invisible interior off-critical quartet.  Novelty is this
uniform route kill and its exact contact-filtration boundary.
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- A zero of an entire function propagates to contact order `q` in its `q`-th power. -/
theorem iteratedDeriv_pow_eq_zero_before_order
    {W : ℂ → ℂ} (hW : Differentiable ℂ W) {z : ℂ} (hWz : W z = 0) :
    ∀ q j : ℕ, j < q → iteratedDeriv j (fun u => W u ^ q) z = 0 := by
  intro q
  induction q with
  | zero =>
      intro j hj
      omega
  | succ q ih =>
      intro j hj
      have hfun : (fun u => W u ^ (q + 1)) = fun u => W u ^ q * W u := by
        funext u
        rw [pow_succ]
      rw [hfun]
      refine complex_iteratedDeriv_mul_eq_zero_before_add_order
        ((hW.pow q).contDiff.contDiffAt) hW.contDiff.contDiffAt
        (fun r hr => ih r hr) (fun r hr => ?_) (by omega)
      have hr0 : r = 0 := by omega
      subst r
      simpa [iteratedDeriv_zero] using hWz

/-- Multiplication by `1 + W^q` is invisible to every jet below `q` at a zero of `W`. -/
theorem iteratedDeriv_mul_one_add_pow_eq_of_zero
    {F W : ℂ → ℂ} (hF : Differentiable ℂ F) (hW : Differentiable ℂ W)
    {z : ℂ} (hWz : W z = 0) {q j : ℕ} (hj : j < q) :
    iteratedDeriv j (fun u => F u * (1 + W u ^ q)) z = iteratedDeriv j F z := by
  have hpow : Differentiable ℂ (fun u => W u ^ q) := hW.pow q
  have hprod : Differentiable ℂ (fun u => F u * W u ^ q) := hF.mul hpow
  have hzero : iteratedDeriv j (fun u => F u * W u ^ q) z = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      hF.contDiff.contDiffAt hpow.contDiff.contDiffAt
      (m := 0) (n := q) (fun r hr => by omega)
      (fun r hr => iteratedDeriv_pow_eq_zero_before_order hW hWz q r hr) (by omega)
  have hfun : (fun u => F u * (1 + W u ^ q)) =
      fun u => F u + F u * W u ^ q := by
    funext u
    ring
  have hsum : (fun u => F u + F u * W u ^ q) =
      F + fun u => F u * W u ^ q := rfl
  rw [hfun, hsum,
    iteratedDeriv_add hF.contDiff.contDiffAt hprod.contDiff.contDiffAt,
    hzero, add_zero]

/-- Anchored Gamma-null contact core, normalized to take value `i` at the fixed target. -/
def completedResponseContactCore (z : ℂ) : ℂ :=
  positiveSquareInterpolationPolynomial z * anchoredSymmetricJetNullGenerator z

/-- Multiplier whose positive square gauge occupies filtration level `4N+2`. -/
def completedResponseHigherContactMultiplier (N : ℕ) (z : ℂ) : ℂ :=
  positiveSquareInterpolationPolynomial z * completedResponseContactCore z ^ (2 * N)

/-- Positive completed-response gauge invisible through every complex-order jet depth `N`. -/
def completedResponseBoundedJetGauge (N : ℕ) (z : ℂ) : ℂ :=
  completedResponsePositiveSquareGauge (completedResponseHigherContactMultiplier N) z

theorem completedResponseContactCore_nonrealInteriorResponsePoint :
    completedResponseContactCore nonrealInteriorResponsePoint = I := by
  rw [completedResponseContactCore,
    positiveSquareInterpolationPolynomial_nonrealInteriorResponsePoint,
    positiveSquareInterpolationTarget]
  exact div_mul_cancel₀ I anchoredSymmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero

theorem completedResponseContactCore_nat (m : ℕ) :
    completedResponseContactCore (m : ℂ) = 0 := by
  simp [completedResponseContactCore, anchoredSymmetricJetNullGenerator_nat]

theorem differentiable_completedResponseContactCore :
    Differentiable ℂ completedResponseContactCore := by
  exact differentiable_positiveSquareInterpolationPolynomial.mul
    differentiable_anchoredSymmetricJetNullGenerator

theorem completedResponseContactCore_reflection (z : ℂ) :
    completedResponseContactCore (-3 - z) = completedResponseContactCore z := by
  simp [completedResponseContactCore,
    positiveSquareInterpolationPolynomial_reflection,
    anchoredSymmetricJetNullGenerator_reflection]

theorem completedResponseContactCore_conj (z : ℂ) :
    completedResponseContactCore ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedResponseContactCore z) := by
  simp [completedResponseContactCore,
    positiveSquareInterpolationPolynomial_conj,
    anchoredSymmetricJetNullGenerator_conj, map_mul]

/-- The order-one envelope is closed under every fixed natural power. -/
theorem orderOneEnvelope_function_pow {F : ℂ → ℂ}
    (hF : OrderOneEnvelope F) :
    ∀ n : ℕ, OrderOneEnvelope (fun z => F z ^ n) := by
  intro n
  induction n with
  | zero =>
      exact (orderOneEnvelope_const 1).congr fun z => by simp
  | succ n ih =>
      exact (ih.mul hF).congr fun z => by simp [pow_succ]

theorem orderOneEnvelope_completedResponseContactCore :
    OrderOneEnvelope completedResponseContactCore := by
  exact (orderOneEnvelope_positiveSquareInterpolationPolynomial.mul
    orderOneEnvelope_anchoredSymmetricJetNullGenerator).congr fun z => rfl

theorem differentiable_completedResponseHigherContactMultiplier (N : ℕ) :
    Differentiable ℂ (completedResponseHigherContactMultiplier N) := by
  exact differentiable_positiveSquareInterpolationPolynomial.mul
    (differentiable_completedResponseContactCore.pow (2 * N))

theorem completedResponseHigherContactMultiplier_reflection (N : ℕ) (z : ℂ) :
    completedResponseHigherContactMultiplier N (-3 - z) =
      completedResponseHigherContactMultiplier N z := by
  simp [completedResponseHigherContactMultiplier,
    positiveSquareInterpolationPolynomial_reflection,
    completedResponseContactCore_reflection]

theorem completedResponseHigherContactMultiplier_conj (N : ℕ) (z : ℂ) :
    completedResponseHigherContactMultiplier N ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedResponseHigherContactMultiplier N z) := by
  simp [completedResponseHigherContactMultiplier,
    positiveSquareInterpolationPolynomial_conj,
    completedResponseContactCore_conj, map_mul, map_pow]

theorem orderOneEnvelope_completedResponseHigherContactMultiplier (N : ℕ) :
    OrderOneEnvelope (completedResponseHigherContactMultiplier N) := by
  exact (orderOneEnvelope_positiveSquareInterpolationPolynomial.mul
    (orderOneEnvelope_function_pow
      orderOneEnvelope_completedResponseContactCore (2 * N))).congr fun z => rfl

theorem completedResponseHigherContactMultiplier_mul_generator
    (N : ℕ) (z : ℂ) :
    completedResponseHigherContactMultiplier N z * anchoredSymmetricJetNullGenerator z =
      completedResponseContactCore z ^ (2 * N + 1) := by
  rw [completedResponseHigherContactMultiplier,
    completedResponseContactCore, pow_succ]
  ring

/-- Exact contact-filtration normal form of the depth-`N` positive gauge. -/
theorem completedResponseBoundedJetGauge_eq (N : ℕ) (z : ℂ) :
    completedResponseBoundedJetGauge N z =
      1 + completedResponseContactCore z ^ (4 * N + 2) := by
  rw [completedResponseBoundedJetGauge, completedResponsePositiveSquareGauge,
    completedResponseHigherContactMultiplier_mul_generator]
  rw [← pow_mul]
  congr 2
  omega

/-- Every filtration level preserves the full anchored positive real-axis gauge package. -/
theorem completedResponseBoundedJetGauge_package (N : ℕ) :
    IsCompletedResponsePositiveSquareGauge (completedResponseBoundedJetGauge N) := by
  exact completedResponsePositiveSquareGauge_package
    (differentiable_completedResponseHigherContactMultiplier N)
    (completedResponseHigherContactMultiplier_reflection N)
    (completedResponseHigherContactMultiplier_conj N)
    (orderOneEnvelope_completedResponseHigherContactMultiplier N)

theorem completedResponseBoundedJetGauge_nonrealInteriorResponsePoint_zero (N : ℕ) :
    completedResponseBoundedJetGauge N nonrealInteriorResponsePoint = 0 := by
  rw [completedResponseBoundedJetGauge_eq,
    completedResponseContactCore_nonrealInteriorResponsePoint]
  have hpow : I ^ (4 * N + 2) = (-1 : ℂ) := by
    rw [show 4 * N + 2 = 2 * (2 * N + 1) by omega, pow_mul, Complex.I_sq]
    rw [pow_succ]
    have heven : (-1 : ℂ) ^ (2 * N) = 1 := by
      rw [pow_mul]
      norm_num
    rw [heven]
    ring
  rw [hpow]
  ring

/-- Completed response at filtration level `N`. -/
def boundedJetResponseCountermodel (N : ℕ) (z : ℂ) : ℂ :=
  completedBlackHoleJetInterpolation z * completedResponseBoundedJetGauge N z

theorem differentiable_boundedJetResponseCountermodel (N : ℕ) :
    Differentiable ℂ (boundedJetResponseCountermodel N) := by
  exact differentiable_completedBlackHoleJetInterpolation.mul
    (completedResponseBoundedJetGauge_package N).1

theorem boundedJetResponseCountermodel_nat (N : ℕ) (scaleLog : ℂ) (m : ℕ) :
    boundedJetResponseCountermodel N (m : ℂ) =
      completedBlackHoleJetSample scaleLog m := by
  rw [boundedJetResponseCountermodel,
    (completedResponseBoundedJetGauge_package N).2.1 m, mul_one,
    completedBlackHoleJetInterpolation_nat]

theorem boundedJetResponseCountermodel_reflection (N : ℕ) (z : ℂ) :
    boundedJetResponseCountermodel N (-3 - z) =
      boundedJetResponseCountermodel N z := by
  rw [boundedJetResponseCountermodel, boundedJetResponseCountermodel,
    completedBlackHoleJetInterpolation_reflection,
    (completedResponseBoundedJetGauge_package N).2.2.2.2.2.1]

theorem boundedJetResponseCountermodel_conj (N : ℕ) (z : ℂ) :
    boundedJetResponseCountermodel N ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (boundedJetResponseCountermodel N z) := by
  rw [boundedJetResponseCountermodel, boundedJetResponseCountermodel,
    completedBlackHoleJetInterpolation_conj,
    (completedResponseBoundedJetGauge_package N).2.2.2.2.2.2.1, map_mul]

theorem orderOneEnvelope_boundedJetResponseCountermodel (N : ℕ) :
    OrderOneEnvelope (boundedJetResponseCountermodel N) := by
  exact (orderOneEnvelope_completedBlackHoleJetInterpolation.mul
    (completedResponseBoundedJetGauge_package N).2.2.2.2.2.2.2.1).congr fun z => rfl

theorem boundedJetResponseCountermodel_neg_two (N : ℕ) :
    boundedJetResponseCountermodel N (-2) =
      completedBlackHoleJetInterpolation (-2) := by
  rw [boundedJetResponseCountermodel,
    (completedResponseBoundedJetGauge_package N).2.2.1, mul_one]

theorem boundedJetResponseCountermodel_neg_three_halves (N : ℕ) :
    boundedJetResponseCountermodel N (-(3 / 2 : ℂ)) =
      completedBlackHoleJetInterpolation (-(3 / 2 : ℂ)) := by
  rw [boundedJetResponseCountermodel,
    (completedResponseBoundedJetGauge_package N).2.2.2.1, mul_one]

theorem boundedJetResponseCountermodel_neg_one (N : ℕ) :
    boundedJetResponseCountermodel N (-1) =
      completedBlackHoleJetInterpolation (-1) := by
  rw [boundedJetResponseCountermodel,
    (completedResponseBoundedJetGauge_package N).2.2.2.2.1, mul_one]

theorem boundedJetResponseCountermodel_real_positiveMultiple (N : ℕ) (σ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      boundedJetResponseCountermodel N (σ : ℂ) =
        (r : ℂ) * completedBlackHoleJetInterpolation (σ : ℂ) := by
  obtain ⟨r, hr, hG⟩ :=
    (completedResponseBoundedJetGauge_package N).2.2.2.2.2.2.2.2 σ
  refine ⟨r, hr, ?_⟩
  rw [boundedJetResponseCountermodel, hG]
  ring

theorem boundedJetResponseCountermodel_real_ne_zero (N : ℕ) (σ : ℝ) :
    boundedJetResponseCountermodel N (σ : ℂ) ≠ 0 := by
  obtain ⟨r, hr, hF⟩ :=
    boundedJetResponseCountermodel_real_positiveMultiple N σ
  rw [hF]
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt hr
  · rw [completedBlackHoleJetInterpolation]
    convert xi_ne_zero_of_ofReal (σ + 2) using 1
    push_cast
    ring

theorem boundedJetResponseCountermodel_realAxis_package
    (N : ℕ) (scaleLog : ℂ) :
    IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog
      (boundedJetResponseCountermodel N) := by
  exact ⟨⟨differentiable_boundedJetResponseCountermodel N,
      boundedJetResponseCountermodel_nat N scaleLog,
      boundedJetResponseCountermodel_reflection N,
      boundedJetResponseCountermodel_conj N,
      orderOneEnvelope_boundedJetResponseCountermodel N⟩,
    boundedJetResponseCountermodel_neg_two N,
    boundedJetResponseCountermodel_neg_three_halves N,
    boundedJetResponseCountermodel_neg_one N,
    boundedJetResponseCountermodel_real_ne_zero N,
    boundedJetResponseCountermodel_real_positiveMultiple N⟩

/-- Every complex-order jet through depth `N` agrees at every natural response order. -/
theorem boundedJetResponseCountermodel_iteratedDeriv_nat
    (N m j : ℕ) (hj : j ≤ N) :
    iteratedDeriv j (boundedJetResponseCountermodel N) (m : ℂ) =
      iteratedDeriv j completedBlackHoleJetInterpolation (m : ℂ) := by
  have hfun : boundedJetResponseCountermodel N = fun z =>
      completedBlackHoleJetInterpolation z *
        (1 + completedResponseContactCore z ^ (4 * N + 2)) := by
    funext z
    rw [boundedJetResponseCountermodel, completedResponseBoundedJetGauge_eq]
  rw [hfun]
  exact iteratedDeriv_mul_one_add_pow_eq_of_zero
    differentiable_completedBlackHoleJetInterpolation
    differentiable_completedResponseContactCore
    (completedResponseContactCore_nat m) (by omega)

/-- Strongest prior real-axis package plus bounded complex-order jets at the full natural ladder. -/
def IsBoundedJetRealAxisAnchoredCompletedBlackHoleJetPackage
    (N : ℕ) (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog F ∧
    ∀ (m j : ℕ), j ≤ N →
      iteratedDeriv j F (m : ℂ) =
        iteratedDeriv j completedBlackHoleJetInterpolation (m : ℂ)

/-- Constructive positive survivor: every finite contact quotient has a noncanonical member. -/
theorem boundedJetResponseCountermodel_package (N : ℕ) (scaleLog : ℂ) :
    IsBoundedJetRealAxisAnchoredCompletedBlackHoleJetPackage N scaleLog
      (boundedJetResponseCountermodel N) := by
  exact ⟨boundedJetResponseCountermodel_realAxis_package N scaleLog,
    boundedJetResponseCountermodel_iteratedDeriv_nat N⟩

theorem boundedJetResponseCountermodel_nonrealInteriorResponsePoint_zero (N : ℕ) :
    boundedJetResponseCountermodel N nonrealInteriorResponsePoint = 0 := by
  rw [boundedJetResponseCountermodel,
    completedResponseBoundedJetGauge_nonrealInteriorResponsePoint_zero, mul_zero]

theorem boundedJetResponseCountermodel_ne_canonical (N : ℕ) :
    boundedJetResponseCountermodel N ≠ completedBlackHoleJetInterpolation := by
  have hXne : completedBlackHoleJetInterpolation ≠ 0 := by
    intro hzero
    have hz := congrFun hzero 0
    exact (xi_ne_zero_of_ofReal 2)
      (by simpa [completedBlackHoleJetInterpolation] using hz)
  have hGsubd : Differentiable ℂ
      (fun z => completedResponseBoundedJetGauge N z - 1) :=
    (completedResponseBoundedJetGauge_package N).1.sub (differentiable_const 1)
  have hGsubne : (fun z => completedResponseBoundedJetGauge N z - 1) ≠ 0 := by
    intro hzero
    have hz := congrFun hzero nonrealInteriorResponsePoint
    rw [completedResponseBoundedJetGauge_nonrealInteriorResponsePoint_zero] at hz
    norm_num at hz
  have hprodne := differentiable_mul_ne_zero
    differentiable_completedBlackHoleJetInterpolation hGsubd hXne hGsubne
  intro hcanonical
  apply hprodne
  funext z
  have hz := congrFun hcanonical z
  rw [boundedJetResponseCountermodel] at hz
  change completedBlackHoleJetInterpolation z *
    (completedResponseBoundedJetGauge N z - 1) = 0
  linear_combination hz

/-- **Bounded-local-jet FZZ route kill.**  For every finite depth, even exact complex-order jets at
every physical order plus all prior global real-axis constraints admit an off-critical quartet. -/
theorem completed_response_boundedJet_route_noGo (scaleLog : ℂ) (N : ℕ) :
    ∃ F : ℂ → ℂ, ∃ z : ℂ,
      IsBoundedJetRealAxisAnchoredCompletedBlackHoleJetPackage N scaleLog F ∧
      0 < (z + 2).re ∧ (z + 2).re < 1 ∧
      (z + 2).re ≠ 1 / 2 ∧ (z + 2).im ≠ 0 ∧
      F z = 0 ∧ F ≠ completedBlackHoleJetInterpolation := by
  refine ⟨boundedJetResponseCountermodel N, nonrealInteriorResponsePoint,
    boundedJetResponseCountermodel_package N scaleLog, ?_, ?_, ?_, ?_,
    boundedJetResponseCountermodel_nonrealInteriorResponsePoint_zero N,
    boundedJetResponseCountermodel_ne_canonical N⟩
  all_goals norm_num [nonrealInteriorResponsePoint]

end RHTower
