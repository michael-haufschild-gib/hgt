import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildDyadicLogDensityNoGo


/-!
# FZZ arbitrary finite normalized logarithmic-density no-go

The existing dyadic FZZ countermodel shows that membership in one critical `R log R` contact
class does not determine the completed response. A possible repair was to demand a larger
type-normalized density constant. This module closes every finite constant at once.

For every natural amplification `A`, raise the Schwarz-real dyadic divisor to power `A + 1`
before inserting it into the completed positive-square gauge. Fixed powers remain entire of order
one because this corpus class permits an arbitrary finite growth constant. A real-coefficient
FE-even quadratic renormalizes the powered divisor at one fixed interior point, so the gauge still
vanishes there. Meanwhile its contact depth at the dyadic stratum `2^j(2n+1)` becomes
`2(A+1)2^j`, with exact disjoint-window budget `2(A+1)K2^(K-1)`.

Thus, for every finite real threshold, one completed response beats that normalized logarithmic
contact coefficient while preserving all physical samples, completed anchors, FE reflection,
Schwarz reality, order-one growth, and positive real-axis phase, yet retains an interior off-line
zero. No finite density constant can restore FZZ response uniqueness.

The positive survivor must couple density to a fixed external growth norm/type constant, impose
genuinely supercritical contact, use nonlocal or off-lattice source data, or leave the entire
order-one category.

`[NEW] [FZZ-P ROUTE KILL] [ARBITRARY FINITE DENSITY] [ORDER ONE]
[HERMITE CONTACT] [FOUR-ROUTE WARD] [LEAN-PROVED]`
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- A germ vanishing through order `m - 1` has its `q`th power vanishing through
order `q * m - 1`. -/
theorem iteratedDeriv_pow_eq_zero_before_mul_order
    {W : ℂ → ℂ} (hW : Differentiable ℂ W) {z : ℂ} {m : ℕ}
    (hzero : ∀ r < m, iteratedDeriv r W z = 0) :
    ∀ q r : ℕ, r < q * m → iteratedDeriv r (fun u => W u ^ q) z = 0 := by
  intro q
  induction q with
  | zero =>
      intro r hr
      omega
  | succ q ih =>
      intro r hr
      have hfun : (fun u => W u ^ (q + 1)) = fun u => W u ^ q * W u := by
        funext u
        rw [pow_succ]
      rw [hfun]
      refine complex_iteratedDeriv_mul_eq_zero_before_add_order
        ((hW.pow q).contDiff.contDiffAt) hW.contDiff.contDiffAt
        (m := q * m) (n := m)
        (fun k hk => ih k hk) hzero ?_
      simpa [Nat.succ_mul, Nat.add_mul, Nat.one_mul] using hr

/-- Target for the powered dyadic divisor inserted in the positive-square gauge. -/
def dyadicLogAmplifiedInterpolationTarget (A : ℕ) : ℂ :=
  I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
    dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ^ (A + 1))

/-- The unique real-coefficient FE-even quadratic taking the powered target value at the
fixed interior point. -/
def dyadicLogAmplifiedInterpolationPolynomial (A : ℕ) (z : ℂ) : ℂ :=
  ((dyadicLogAmplifiedInterpolationTarget A).re : ℂ) +
    ((2 * (dyadicLogAmplifiedInterpolationTarget A).im : ℝ) : ℂ) *
      ((z + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16)

theorem dyadicLogAmplifiedInterpolationPolynomial_target (A : ℕ) :
    dyadicLogAmplifiedInterpolationPolynomial A nonrealInteriorResponsePoint =
      dyadicLogAmplifiedInterpolationTarget A := by
  have hu : (nonrealInteriorResponsePoint + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16 = I / 2 := by
    rw [nonrealInteriorResponsePoint]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [dyadicLogAmplifiedInterpolationPolynomial, hu]
  apply Complex.ext
  · simp
  · simp
    ring

theorem differentiable_dyadicLogAmplifiedInterpolationPolynomial (A : ℕ) :
    Differentiable ℂ (dyadicLogAmplifiedInterpolationPolynomial A) := by
  unfold dyadicLogAmplifiedInterpolationPolynomial
  fun_prop

theorem dyadicLogAmplifiedInterpolationPolynomial_reflection
    (A : ℕ) (z : ℂ) :
    dyadicLogAmplifiedInterpolationPolynomial A (-3 - z) =
      dyadicLogAmplifiedInterpolationPolynomial A z := by
  unfold dyadicLogAmplifiedInterpolationPolynomial
  ring

theorem dyadicLogAmplifiedInterpolationPolynomial_conj
    (A : ℕ) (z : ℂ) :
    dyadicLogAmplifiedInterpolationPolynomial A ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (dyadicLogAmplifiedInterpolationPolynomial A z) := by
  simp only [dyadicLogAmplifiedInterpolationPolynomial, map_add, map_mul, map_pow,
    map_ofNat, map_div₀, Complex.conj_ofReal]

theorem orderOneEnvelope_dyadicLogAmplifiedInterpolationPolynomial (A : ℕ) :
    OrderOneEnvelope (dyadicLogAmplifiedInterpolationPolynomial A) := by
  have hid : OrderOneEnvelope (fun z : ℂ => z) := orderOneEnvelope_id
  have hc : OrderOneEnvelope (fun z : ℂ => z + (3 / 2 : ℂ)) :=
    hid.add (orderOneEnvelope_const (3 / 2))
  have hsq : OrderOneEnvelope (fun z : ℂ => (z + (3 / 2 : ℂ)) ^ (2 : ℕ)) :=
    (hc.mul hc).congr fun z => by ring
  have hoff : OrderOneEnvelope (fun z : ℂ =>
      (z + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16) :=
    hsq.add (orderOneEnvelope_const (15 / 16))
  exact ((orderOneEnvelope_const
      ((dyadicLogAmplifiedInterpolationTarget A).re : ℂ)).add
    ((orderOneEnvelope_const
      ((2 * (dyadicLogAmplifiedInterpolationTarget A).im : ℝ) : ℂ)).mul
      hoff)).congr fun z => by
        simp [dyadicLogAmplifiedInterpolationPolynomial]

def dyadicLogAmplifiedDensityMultiplier (A : ℕ) (z : ℂ) : ℂ :=
  dyadicLogAmplifiedInterpolationPolynomial A z *
    dyadicLogSchwarzEvenProduct z ^ (A + 1)

theorem differentiable_dyadicLogAmplifiedDensityMultiplier (A : ℕ) :
    Differentiable ℂ (dyadicLogAmplifiedDensityMultiplier A) := by
  exact (differentiable_dyadicLogAmplifiedInterpolationPolynomial A).mul
    (differentiable_dyadicLogSchwarzEvenProduct.pow (A + 1))

theorem dyadicLogAmplifiedDensityMultiplier_reflection
    (A : ℕ) (z : ℂ) :
    dyadicLogAmplifiedDensityMultiplier A (-3 - z) =
      dyadicLogAmplifiedDensityMultiplier A z := by
  simp [dyadicLogAmplifiedDensityMultiplier,
    dyadicLogAmplifiedInterpolationPolynomial_reflection,
    dyadicLogSchwarzEvenProduct_reflection]

theorem dyadicLogAmplifiedDensityMultiplier_conj
    (A : ℕ) (z : ℂ) :
    dyadicLogAmplifiedDensityMultiplier A ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (dyadicLogAmplifiedDensityMultiplier A z) := by
  simp [dyadicLogAmplifiedDensityMultiplier,
    dyadicLogAmplifiedInterpolationPolynomial_conj,
    dyadicLogSchwarzEvenProduct_conj, map_mul, map_pow]

theorem orderOneEnvelope_dyadicLogAmplifiedDensityMultiplier (A : ℕ) :
    OrderOneEnvelope (dyadicLogAmplifiedDensityMultiplier A) := by
  exact ((orderOneEnvelope_dyadicLogAmplifiedInterpolationPolynomial A).mul
    (orderOneEnvelope_function_pow
      orderOneEnvelope_dyadicLogSchwarzEvenProduct (A + 1))).congr fun z => rfl

theorem dyadicLogAmplifiedDensityMultiplier_mul_generator_target (A : ℕ) :
    dyadicLogAmplifiedDensityMultiplier A nonrealInteriorResponsePoint *
      anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint = I := by
  rw [dyadicLogAmplifiedDensityMultiplier,
    dyadicLogAmplifiedInterpolationPolynomial_target,
    dyadicLogAmplifiedInterpolationTarget]
  have hden : anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
      dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ^ (A + 1) ≠ 0 :=
    mul_ne_zero anchoredSymmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero
      (pow_ne_zero _ dyadicLogSchwarzEvenProduct_nonrealInteriorResponsePoint_ne_zero)
  calc
    I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
        dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ^ (A + 1)) *
        dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ^ (A + 1) *
        anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint =
      I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
        dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ^ (A + 1)) *
        (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
          dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ^ (A + 1)) := by ring
    _ = I := div_mul_cancel₀ I hden

def dyadicLogAmplifiedDensityGauge (A : ℕ) (z : ℂ) : ℂ :=
  completedResponsePositiveSquareGauge
    (dyadicLogAmplifiedDensityMultiplier A) z

theorem dyadicLogAmplifiedDensityGauge_package (A : ℕ) :
    IsCompletedResponsePositiveSquareGauge
      (dyadicLogAmplifiedDensityGauge A) := by
  exact completedResponsePositiveSquareGauge_package
    (differentiable_dyadicLogAmplifiedDensityMultiplier A)
    (dyadicLogAmplifiedDensityMultiplier_reflection A)
    (dyadicLogAmplifiedDensityMultiplier_conj A)
    (orderOneEnvelope_dyadicLogAmplifiedDensityMultiplier A)

theorem dyadicLogAmplifiedDensityGauge_target_zero (A : ℕ) :
    dyadicLogAmplifiedDensityGauge A nonrealInteriorResponsePoint = 0 := by
  rw [dyadicLogAmplifiedDensityGauge, completedResponsePositiveSquareGauge,
    dyadicLogAmplifiedDensityMultiplier_mul_generator_target, Complex.I_sq]
  ring

def dyadicLogAmplifiedDensityResponse (A : ℕ) (z : ℂ) : ℂ :=
  completedBlackHoleJetInterpolation z * dyadicLogAmplifiedDensityGauge A z

theorem differentiable_dyadicLogAmplifiedDensityResponse (A : ℕ) :
    Differentiable ℂ (dyadicLogAmplifiedDensityResponse A) :=
  differentiable_completedBlackHoleJetInterpolation.mul
    (dyadicLogAmplifiedDensityGauge_package A).1

theorem dyadicLogAmplifiedDensityResponse_nat
    (A : ℕ) (scaleLog : ℂ) (m : ℕ) :
    dyadicLogAmplifiedDensityResponse A (m : ℂ) =
      completedBlackHoleJetSample scaleLog m := by
  rw [dyadicLogAmplifiedDensityResponse,
    (dyadicLogAmplifiedDensityGauge_package A).2.1 m, mul_one,
    completedBlackHoleJetInterpolation_nat]

theorem dyadicLogAmplifiedDensityResponse_reflection (A : ℕ) (z : ℂ) :
    dyadicLogAmplifiedDensityResponse A (-3 - z) =
      dyadicLogAmplifiedDensityResponse A z := by
  rw [dyadicLogAmplifiedDensityResponse,
    dyadicLogAmplifiedDensityResponse,
    completedBlackHoleJetInterpolation_reflection,
    (dyadicLogAmplifiedDensityGauge_package A).2.2.2.2.2.1]

theorem dyadicLogAmplifiedDensityResponse_conj (A : ℕ) (z : ℂ) :
    dyadicLogAmplifiedDensityResponse A ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (dyadicLogAmplifiedDensityResponse A z) := by
  rw [dyadicLogAmplifiedDensityResponse,
    dyadicLogAmplifiedDensityResponse,
    completedBlackHoleJetInterpolation_conj,
    (dyadicLogAmplifiedDensityGauge_package A).2.2.2.2.2.2.1, map_mul]

theorem orderOneEnvelope_dyadicLogAmplifiedDensityResponse (A : ℕ) :
    OrderOneEnvelope (dyadicLogAmplifiedDensityResponse A) := by
  exact (orderOneEnvelope_completedBlackHoleJetInterpolation.mul
    (dyadicLogAmplifiedDensityGauge_package A).2.2.2.2.2.2.2.1).congr
      fun z => rfl

theorem dyadicLogAmplifiedDensityResponse_real_positiveMultiple
    (A : ℕ) (sigma : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      dyadicLogAmplifiedDensityResponse A (sigma : ℂ) =
        (r : ℂ) * completedBlackHoleJetInterpolation (sigma : ℂ) := by
  obtain ⟨r, hr, hG⟩ :=
    (dyadicLogAmplifiedDensityGauge_package A).2.2.2.2.2.2.2.2 sigma
  refine ⟨r, hr, ?_⟩
  rw [dyadicLogAmplifiedDensityResponse, hG]
  ring

theorem dyadicLogAmplifiedDensityResponse_real_ne_zero
    (A : ℕ) (sigma : ℝ) :
    dyadicLogAmplifiedDensityResponse A (sigma : ℂ) ≠ 0 := by
  obtain ⟨r, hr, hF⟩ :=
    dyadicLogAmplifiedDensityResponse_real_positiveMultiple A sigma
  rw [hF]
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt hr
  · rw [completedBlackHoleJetInterpolation]
    convert xi_ne_zero_of_ofReal (sigma + 2) using 1
    push_cast
    ring

theorem dyadicLogAmplifiedDensityResponse_realAxis_package
    (A : ℕ) (scaleLog : ℂ) :
    IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog
      (dyadicLogAmplifiedDensityResponse A) := by
  exact ⟨⟨differentiable_dyadicLogAmplifiedDensityResponse A,
      dyadicLogAmplifiedDensityResponse_nat A scaleLog,
      dyadicLogAmplifiedDensityResponse_reflection A,
      dyadicLogAmplifiedDensityResponse_conj A,
      orderOneEnvelope_dyadicLogAmplifiedDensityResponse A⟩,
    by rw [dyadicLogAmplifiedDensityResponse,
      (dyadicLogAmplifiedDensityGauge_package A).2.2.1, mul_one],
    by rw [dyadicLogAmplifiedDensityResponse,
      (dyadicLogAmplifiedDensityGauge_package A).2.2.2.1, mul_one],
    by rw [dyadicLogAmplifiedDensityResponse,
      (dyadicLogAmplifiedDensityGauge_package A).2.2.2.2.1, mul_one],
    dyadicLogAmplifiedDensityResponse_real_ne_zero A,
    dyadicLogAmplifiedDensityResponse_real_positiveMultiple A⟩

/-- Powering the dyadic divisor amplifies contact depth by an arbitrary finite factor. -/
theorem dyadicLogAmplifiedDensityResponse_iteratedDeriv
    (A j n r : ℕ) (hr : r < 2 * ((A + 1) * 2 ^ j)) :
    iteratedDeriv r (dyadicLogAmplifiedDensityResponse A)
        (dyadicLogPhysicalNode j n) =
      iteratedDeriv r completedBlackHoleJetInterpolation
        (dyadicLogPhysicalNode j n) := by
  let Q : ℂ → ℂ := dyadicLogSchwarzEvenProduct
  let Qp : ℂ → ℂ := fun z => Q z ^ (A + 1)
  let H : ℂ → ℂ := fun z =>
    completedBlackHoleJetInterpolation z *
      (dyadicLogAmplifiedInterpolationPolynomial A z *
        anchoredSymmetricJetNullGenerator z) ^ (2 : ℕ)
  have hQ : Differentiable ℂ Q := differentiable_dyadicLogSchwarzEvenProduct
  have hQp : Differentiable ℂ Qp := hQ.pow (A + 1)
  have hH : Differentiable ℂ H := by
    dsimp [H]
    exact differentiable_completedBlackHoleJetInterpolation.mul
      (((differentiable_dyadicLogAmplifiedInterpolationPolynomial A).mul
        differentiable_anchoredSymmetricJetNullGenerator).pow 2)
  have hQzero : ∀ k < 2 ^ j,
      iteratedDeriv k Q (dyadicLogPhysicalNode j n) = 0 := by
    intro k hk
    exact dyadicLogSchwarzEvenProduct_iteratedDeriv_zero j n k hk
  have hQpzero : ∀ k < (A + 1) * 2 ^ j,
      iteratedDeriv k Qp (dyadicLogPhysicalNode j n) = 0 := by
    intro k hk
    exact iteratedDeriv_pow_eq_zero_before_mul_order hQ hQzero
      (A + 1) k hk
  have hQpsq : Differentiable ℂ (fun z => Qp z ^ (2 : ℕ)) := hQp.pow 2
  have hQpsqzero : ∀ k < 2 * ((A + 1) * 2 ^ j),
      iteratedDeriv k (fun z => Qp z ^ (2 : ℕ)) (dyadicLogPhysicalNode j n) = 0 := by
    intro k hk
    exact iteratedDeriv_pow_eq_zero_before_mul_order hQp hQpzero 2 k hk
  have hprod : Differentiable ℂ (fun z => H z * Qp z ^ (2 : ℕ)) := hH.mul hQpsq
  have hzero : iteratedDeriv r (fun z => H z * Qp z ^ (2 : ℕ))
      (dyadicLogPhysicalNode j n) = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      hH.contDiff.contDiffAt hQpsq.contDiff.contDiffAt
      (m := 0) (n := 2 * ((A + 1) * 2 ^ j))
      (fun k hk => by omega) hQpsqzero (by simpa using hr)
  have hcounter : dyadicLogAmplifiedDensityResponse A = fun z =>
      completedBlackHoleJetInterpolation z + H z * Qp z ^ (2 : ℕ) := by
    funext z
    rw [dyadicLogAmplifiedDensityResponse,
      dyadicLogAmplifiedDensityGauge,
      completedResponsePositiveSquareGauge,
      dyadicLogAmplifiedDensityMultiplier]
    dsimp [H, Qp, Q]
    ring
  rw [hcounter]
  have hsum : (fun z => completedBlackHoleJetInterpolation z + H z * Qp z ^ (2 : ℕ)) =
      completedBlackHoleJetInterpolation + (fun z => H z * Qp z ^ (2 : ℕ)) := rfl
  rw [hsum, iteratedDeriv_add
    differentiable_completedBlackHoleJetInterpolation.contDiff.contDiffAt
    hprod.contDiff.contDiffAt, hzero, add_zero]

def IsArbitraryFiniteLogDensityCompletedBlackHoleJetPackage
    (A : ℕ) (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog F ∧
    ∀ (j n r : ℕ), r < 2 * ((A + 1) * 2 ^ j) →
      iteratedDeriv r F (dyadicLogPhysicalNode j n) =
        iteratedDeriv r completedBlackHoleJetInterpolation
          (dyadicLogPhysicalNode j n)

theorem dyadicLogAmplifiedDensityResponse_package
    (A : ℕ) (scaleLog : ℂ) :
    IsArbitraryFiniteLogDensityCompletedBlackHoleJetPackage A scaleLog
      (dyadicLogAmplifiedDensityResponse A) := by
  exact ⟨dyadicLogAmplifiedDensityResponse_realAxis_package A scaleLog,
    dyadicLogAmplifiedDensityResponse_iteratedDeriv A⟩

theorem dyadicLogAmplifiedDensityResponse_target_zero (A : ℕ) :
    dyadicLogAmplifiedDensityResponse A nonrealInteriorResponsePoint = 0 := by
  rw [dyadicLogAmplifiedDensityResponse,
    dyadicLogAmplifiedDensityGauge_target_zero, mul_zero]

theorem dyadicLogAmplifiedDensityResponse_ne_canonical (A : ℕ) :
    dyadicLogAmplifiedDensityResponse A ≠ completedBlackHoleJetInterpolation := by
  have hXne : completedBlackHoleJetInterpolation ≠ 0 := by
    intro hzero
    have hz := congrFun hzero 0
    exact (xi_ne_zero_of_ofReal 2)
      (by simpa [completedBlackHoleJetInterpolation] using hz)
  have hGsubd : Differentiable ℂ
      (fun z => dyadicLogAmplifiedDensityGauge A z - 1) :=
    (dyadicLogAmplifiedDensityGauge_package A).1.sub (differentiable_const 1)
  have hGsubne : (fun z => dyadicLogAmplifiedDensityGauge A z - 1) ≠ 0 := by
    intro hzero
    have hz := congrFun hzero nonrealInteriorResponsePoint
    rw [dyadicLogAmplifiedDensityGauge_target_zero] at hz
    norm_num at hz
  have hprodne := differentiable_mul_ne_zero
    differentiable_completedBlackHoleJetInterpolation hGsubd hXne hGsubne
  intro hcanonical
  apply hprodne
  funext z
  have hz := congrFun hcanonical z
  rw [dyadicLogAmplifiedDensityResponse] at hz
  change completedBlackHoleJetInterpolation z *
    (dyadicLogAmplifiedDensityGauge A z - 1) = 0
  linear_combination hz

def amplifiedDyadicLogWindowWeight
    (A : ℕ) {K : ℕ} (q : DyadicLogWindowIndex K) : ℕ :=
  2 * (A + 1) * dyadicLogWindowWeight q

theorem sum_amplifiedDyadicLogWindowWeight_eq
    (A K : ℕ) :
    ∑ q : DyadicLogWindowIndex K, amplifiedDyadicLogWindowWeight A q =
      (2 * (A + 1)) * (K * 2 ^ (K - 1)) := by
  simp only [amplifiedDyadicLogWindowWeight]
  rw [← Finset.mul_sum, sum_dyadicLogWindowWeight_eq_logBudget]

def FZZArbitraryFiniteLogDensityConstantRouteKilled : Prop :=
  ∀ (A : ℕ) (scaleLog : ℂ),
    ∃ F : ℂ → ℂ, ∃ z : ℂ,
      IsArbitraryFiniteLogDensityCompletedBlackHoleJetPackage A scaleLog F ∧
      (∀ K : ℕ,
        ∑ q : DyadicLogWindowIndex K, amplifiedDyadicLogWindowWeight A q =
          (2 * (A + 1)) * (K * 2 ^ (K - 1))) ∧
      0 < (z + 2).re ∧ (z + 2).re < 1 ∧
      (z + 2).re ≠ 1 / 2 ∧ (z + 2).im ≠ 0 ∧
      F z = 0 ∧ F ≠ completedBlackHoleJetInterpolation

theorem fzzArbitraryFiniteLogDensityConstantRouteKilled :
    FZZArbitraryFiniteLogDensityConstantRouteKilled := by
  intro A scaleLog
  refine ⟨dyadicLogAmplifiedDensityResponse A,
    nonrealInteriorResponsePoint,
    dyadicLogAmplifiedDensityResponse_package A scaleLog,
    sum_amplifiedDyadicLogWindowWeight_eq A,
    ?_, ?_, ?_, ?_,
    dyadicLogAmplifiedDensityResponse_target_zero A,
    dyadicLogAmplifiedDensityResponse_ne_canonical A⟩
  all_goals norm_num [nonrealInteriorResponsePoint]

theorem exists_dyadicLogAmplificationCoefficient_gt (C : ℝ) :
    ∃ A : ℕ, C < ((2 * (A + 1) : ℕ) : ℝ) := by
  obtain ⟨A, hA⟩ := exists_nat_gt C
  refine ⟨A, hA.trans_le ?_⟩
  exact_mod_cast (show A ≤ 2 * (A + 1) by omega)

def FZZEveryFiniteNormalizedLogDensityThresholdRouteKilled : Prop :=
  ∀ (C : ℝ) (scaleLog : ℂ),
    ∃ A : ℕ, ∃ F : ℂ → ℂ, ∃ z : ℂ,
      C < ((2 * (A + 1) : ℕ) : ℝ) ∧
      IsArbitraryFiniteLogDensityCompletedBlackHoleJetPackage A scaleLog F ∧
      (∀ K : ℕ,
        ∑ q : DyadicLogWindowIndex K, amplifiedDyadicLogWindowWeight A q =
          (2 * (A + 1)) * (K * 2 ^ (K - 1))) ∧
      0 < (z + 2).re ∧ (z + 2).re < 1 ∧
      (z + 2).re ≠ 1 / 2 ∧ (z + 2).im ≠ 0 ∧
      F z = 0 ∧ F ≠ completedBlackHoleJetInterpolation

theorem fzzEveryFiniteNormalizedLogDensityThresholdRouteKilled :
    FZZEveryFiniteNormalizedLogDensityThresholdRouteKilled := by
  intro C scaleLog
  obtain ⟨A, hA⟩ := exists_dyadicLogAmplificationCoefficient_gt C
  obtain ⟨F, z, hpackage, hbudget, hstrip0, hstrip1, htilt, hnonreal,
      hzero, hne⟩ :=
    fzzArbitraryFiniteLogDensityConstantRouteKilled A scaleLog
  exact ⟨A, F, z, hA, hpackage, hbudget, hstrip0, hstrip1, htilt,
    hnonreal, hzero, hne⟩

end RHTower

