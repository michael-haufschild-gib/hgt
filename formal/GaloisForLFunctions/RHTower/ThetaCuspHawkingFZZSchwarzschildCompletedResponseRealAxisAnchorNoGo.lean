import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildCompletedResponseSymmetryNoGo

/-!
# FZZ--Schwarzschild completed-response real-axis anchor no-go

This module kills the strongest purely real-axis repair of the completed FZZ-P source
interpolation route.  In response coordinate `z = s - 2`, let `X(z)=xi(z+2)` and let `K` be
the symmetric reciprocal-Gamma generator already proved invisible to every physical response
order.  The anchor polynomial

`A(z) = (z+1)(z+2)(z+3/2)^2`

also fixes the canonical completed values at `s=0,1/2,1`.  For every entire, order-one,
reflection-even, Schwarz-real multiplier `P`, the square gauge

`G_P(z) = 1 + (P(z) A(z) K(z))^2`

equals one at all completed physical samples and the three anchors, and is a strictly positive
real number on the full real axis.  This is the exact positive survivor: an infinite cone of
sample-and-anchor-invisible positive gauges.

A two-real-parameter centered polynomial is chosen to make `P(a)A(a)K(a)=i` at
`a=-5/4+i`.  Consequently `X G_P` has a zero at completed point `s=3/4+i`, while preserving
the full package above.  No value or nonvanishing assertion about `xi(3/4+i)` is used.
Noncanonicity follows instead from the no-zero-divisor theorem for entire functions.

Thus

`completed samples + FE + Schwarz + order one + canonical 0,1/2,1 anchors`
`+ full real-axis zero-freeness and canonical phase ray`

does not imply nonreal Xi zero control and cannot reach the corpus completed Ward-bound
equivalence to RH.  Any surviving FZZ-P producer must add genuinely off-lattice/nonlocal
complex source information.

**[FALSIFIED] [ROUTE KILL] [PAPER-PROVED] [LEAN-PROVED]**

**[NOVELTY AUDIT]** Carlson-type uniqueness under strict exponential-type hypotheses,
reciprocal-Gamma interpolation, and positive real entire gauges are classical.  Corpus searches
found the two-ladder null ideal and generic positive quartet gauges separately, but not their
anchor-preserving intersection.  Targeted literature searches through 2026-08-30 found no
theorem preserving Solon's exact completed Schwarzschild response samples, the three canonical
Xi anchors, and the full real positive ray while implanting an interior off-critical quartet.
-/


open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

def canonicalCompletedResponseAnchorPolynomial (z : ℂ) : ℂ :=
  (z + 1) * (z + 2) * (z + (3 / 2 : ℂ)) ^ 2

def anchoredSymmetricJetNullGenerator (z : ℂ) : ℂ :=
  canonicalCompletedResponseAnchorPolynomial z * symmetricJetNullGenerator z

def nonrealInteriorResponsePoint : ℂ := (-5 / 4 : ℂ) + I

theorem canonicalCompletedResponseAnchorPolynomial_nonrealInteriorResponsePoint_ne_zero :
    canonicalCompletedResponseAnchorPolynomial nonrealInteriorResponsePoint ≠ 0 := by
  unfold canonicalCompletedResponseAnchorPolynomial
  apply mul_ne_zero
  · apply mul_ne_zero
    · intro hzero
      have him := congrArg Complex.im hzero
      norm_num [nonrealInteriorResponsePoint] at him
    · intro hzero
      have him := congrArg Complex.im hzero
      norm_num [nonrealInteriorResponsePoint] at him
  · apply pow_ne_zero
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num [nonrealInteriorResponsePoint] at him

theorem symmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero :
    symmetricJetNullGenerator nonrealInteriorResponsePoint ≠ 0 := by
  rw [symmetricJetNullGenerator]
  apply mul_ne_zero
  · unfold reciprocalGammaEntire
    apply inv_ne_zero
    intro hzero
    rw [Complex.Gamma_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    have him := congrArg Complex.im hn
    norm_num [nonrealInteriorResponsePoint] at him
  · unfold reciprocalGammaEntire
    apply inv_ne_zero
    intro hzero
    rw [Complex.Gamma_eq_zero_iff] at hzero
    obtain ⟨n, hn⟩ := hzero
    have him := congrArg Complex.im hn
    norm_num [nonrealInteriorResponsePoint] at him

theorem anchoredSymmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero :
    anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint ≠ 0 := by
  exact mul_ne_zero
    canonicalCompletedResponseAnchorPolynomial_nonrealInteriorResponsePoint_ne_zero
    symmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero

theorem differentiable_canonicalCompletedResponseAnchorPolynomial :
    Differentiable ℂ canonicalCompletedResponseAnchorPolynomial := by
  unfold canonicalCompletedResponseAnchorPolynomial
  fun_prop

theorem canonicalCompletedResponseAnchorPolynomial_reflection (z : ℂ) :
    canonicalCompletedResponseAnchorPolynomial (-3 - z) =
      canonicalCompletedResponseAnchorPolynomial z := by
  unfold canonicalCompletedResponseAnchorPolynomial
  ring

theorem canonicalCompletedResponseAnchorPolynomial_conj (z : ℂ) :
    canonicalCompletedResponseAnchorPolynomial ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (canonicalCompletedResponseAnchorPolynomial z) := by
  simp only [canonicalCompletedResponseAnchorPolynomial, map_mul, map_add, map_pow,
    map_one, map_ofNat, map_div₀]

theorem orderOneEnvelope_canonicalCompletedResponseAnchorPolynomial :
    OrderOneEnvelope canonicalCompletedResponseAnchorPolynomial := by
  have hid : OrderOneEnvelope (fun z : ℂ => z) := orderOneEnvelope_id
  have h1 : OrderOneEnvelope (fun z : ℂ => z + 1) :=
    hid.add (orderOneEnvelope_const 1)
  have h2 : OrderOneEnvelope (fun z : ℂ => z + 2) :=
    hid.add (orderOneEnvelope_const 2)
  have h3 : OrderOneEnvelope (fun z : ℂ => z + (3 / 2 : ℂ)) :=
    hid.add (orderOneEnvelope_const (3 / 2))
  exact ((h1.mul h2).mul (h3.mul h3)).congr fun z => by
    simp only [canonicalCompletedResponseAnchorPolynomial]
    ring

theorem differentiable_anchoredSymmetricJetNullGenerator :
    Differentiable ℂ anchoredSymmetricJetNullGenerator := by
  exact differentiable_canonicalCompletedResponseAnchorPolynomial.mul
    differentiable_symmetricJetNullGenerator

theorem anchoredSymmetricJetNullGenerator_reflection (z : ℂ) :
    anchoredSymmetricJetNullGenerator (-3 - z) =
      anchoredSymmetricJetNullGenerator z := by
  rw [anchoredSymmetricJetNullGenerator, anchoredSymmetricJetNullGenerator,
    canonicalCompletedResponseAnchorPolynomial_reflection,
    symmetricJetNullGenerator_reflection]

theorem anchoredSymmetricJetNullGenerator_conj (z : ℂ) :
    anchoredSymmetricJetNullGenerator ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (anchoredSymmetricJetNullGenerator z) := by
  rw [anchoredSymmetricJetNullGenerator, anchoredSymmetricJetNullGenerator,
    canonicalCompletedResponseAnchorPolynomial_conj,
    symmetricJetNullGenerator_conj, map_mul]

theorem orderOneEnvelope_anchoredSymmetricJetNullGenerator :
    OrderOneEnvelope anchoredSymmetricJetNullGenerator := by
  exact (orderOneEnvelope_canonicalCompletedResponseAnchorPolynomial.mul
    orderOneEnvelope_symmetricJetNullGenerator).congr fun z => rfl

theorem anchoredSymmetricJetNullGenerator_nat (m : ℕ) :
    anchoredSymmetricJetNullGenerator (m : ℂ) = 0 := by
  rw [anchoredSymmetricJetNullGenerator, symmetricJetNullGenerator_nat, mul_zero]

theorem anchoredSymmetricJetNullGenerator_neg_two :
    anchoredSymmetricJetNullGenerator (-2) = 0 := by
  norm_num [anchoredSymmetricJetNullGenerator,
    canonicalCompletedResponseAnchorPolynomial]

theorem anchoredSymmetricJetNullGenerator_neg_one :
    anchoredSymmetricJetNullGenerator (-1) = 0 := by
  norm_num [anchoredSymmetricJetNullGenerator,
    canonicalCompletedResponseAnchorPolynomial]

theorem anchoredSymmetricJetNullGenerator_neg_three_halves :
    anchoredSymmetricJetNullGenerator (-(3 / 2 : ℂ)) = 0 := by
  norm_num [anchoredSymmetricJetNullGenerator,
    canonicalCompletedResponseAnchorPolynomial]

/-- Positive square gauge built from the anchored two-ladder null generator. -/
def completedResponsePositiveSquareGauge (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 + (P z * anchoredSymmetricJetNullGenerator z) ^ 2

theorem differentiable_completedResponsePositiveSquareGauge
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) :
    Differentiable ℂ (completedResponsePositiveSquareGauge P) := by
  unfold completedResponsePositiveSquareGauge
  exact (differentiable_const 1).add
    ((hP.mul differentiable_anchoredSymmetricJetNullGenerator).pow 2)

theorem completedResponsePositiveSquareGauge_reflection
    {P : ℂ → ℂ} (hP : ∀ z : ℂ, P (-3 - z) = P z) (z : ℂ) :
    completedResponsePositiveSquareGauge P (-3 - z) =
      completedResponsePositiveSquareGauge P z := by
  rw [completedResponsePositiveSquareGauge, completedResponsePositiveSquareGauge,
    hP, anchoredSymmetricJetNullGenerator_reflection]

theorem completedResponsePositiveSquareGauge_conj
    {P : ℂ → ℂ}
    (hP : ∀ z : ℂ, P ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P z)) (z : ℂ) :
    completedResponsePositiveSquareGauge P ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (completedResponsePositiveSquareGauge P z) := by
  rw [completedResponsePositiveSquareGauge, completedResponsePositiveSquareGauge,
    hP, anchoredSymmetricJetNullGenerator_conj, map_add, map_one, map_pow, map_mul]

theorem orderOneEnvelope_completedResponsePositiveSquareGauge
    {P : ℂ → ℂ} (hP : OrderOneEnvelope P) :
    OrderOneEnvelope (completedResponsePositiveSquareGauge P) := by
  have hPB : OrderOneEnvelope
      (fun z => P z * anchoredSymmetricJetNullGenerator z) :=
    hP.mul orderOneEnvelope_anchoredSymmetricJetNullGenerator
  exact ((orderOneEnvelope_const 1).add (hPB.mul hPB)).congr fun z => by
    simp only [completedResponsePositiveSquareGauge]
    ring

theorem completedResponsePositiveSquareGauge_nat (P : ℂ → ℂ) (m : ℕ) :
    completedResponsePositiveSquareGauge P (m : ℂ) = 1 := by
  rw [completedResponsePositiveSquareGauge,
    anchoredSymmetricJetNullGenerator_nat, mul_zero, zero_pow (by norm_num), add_zero]

theorem completedResponsePositiveSquareGauge_neg_two (P : ℂ → ℂ) :
    completedResponsePositiveSquareGauge P (-2) = 1 := by
  rw [completedResponsePositiveSquareGauge,
    anchoredSymmetricJetNullGenerator_neg_two, mul_zero, zero_pow (by norm_num), add_zero]

theorem completedResponsePositiveSquareGauge_neg_one (P : ℂ → ℂ) :
    completedResponsePositiveSquareGauge P (-1) = 1 := by
  rw [completedResponsePositiveSquareGauge,
    anchoredSymmetricJetNullGenerator_neg_one, mul_zero, zero_pow (by norm_num), add_zero]

theorem completedResponsePositiveSquareGauge_neg_three_halves (P : ℂ → ℂ) :
    completedResponsePositiveSquareGauge P (-(3 / 2 : ℂ)) = 1 := by
  rw [completedResponsePositiveSquareGauge,
    anchoredSymmetricJetNullGenerator_neg_three_halves,
    mul_zero, zero_pow (by norm_num), add_zero]

theorem completedResponsePositiveSquareGauge_real_positive
    {P : ℂ → ℂ}
    (hP : ∀ z : ℂ, P ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P z))
    (σ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      completedResponsePositiveSquareGauge P (σ : ℂ) = (r : ℂ) := by
  let w : ℂ := P (σ : ℂ) * anchoredSymmetricJetNullGenerator (σ : ℂ)
  have hPstar : (starRingEnd ℂ) (P (σ : ℂ)) = P (σ : ℂ) := by
    rw [← hP]
    simp
  have hBstar :
      (starRingEnd ℂ) (anchoredSymmetricJetNullGenerator (σ : ℂ)) =
        anchoredSymmetricJetNullGenerator (σ : ℂ) := by
    rw [← anchoredSymmetricJetNullGenerator_conj]
    simp
  have hwstar : (starRingEnd ℂ) w = w := by
    simp only [w, map_mul, hPstar, hBstar]
  have hwim : w.im = 0 := by
    have hi := congrArg Complex.im hwstar
    simp at hi
    linarith
  refine ⟨1 + w.re ^ 2, by positivity, ?_⟩
  change 1 + w ^ 2 = (((1 + w.re ^ 2 : ℝ) : ℂ))
  apply Complex.ext
  · simp [pow_two, mul_re, hwim]
  · simp [pow_two, mul_im, hwim]

/-- Exact positive survivor package for the full anchored square-gauge cone. -/
def IsCompletedResponsePositiveSquareGauge (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧
    (∀ m : ℕ, G (m : ℂ) = 1) ∧
    G (-2) = 1 ∧ G (-(3 / 2 : ℂ)) = 1 ∧ G (-1) = 1 ∧
    (∀ z : ℂ, G (-3 - z) = G z) ∧
    (∀ z : ℂ, G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G z)) ∧
    OrderOneEnvelope G ∧
    ∀ σ : ℝ, ∃ r : ℝ, 0 < r ∧ G (σ : ℂ) = (r : ℂ)

/-- Every entire, order-one, response-reflection-even, Schwarz-real multiplier produces an
anchored gauge invisible to all physical samples and strictly positive on the full real axis. -/
theorem completedResponsePositiveSquareGauge_package
    {P : ℂ → ℂ} (hPd : Differentiable ℂ P)
    (hPr : ∀ z : ℂ, P (-3 - z) = P z)
    (hPc : ∀ z : ℂ, P ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P z))
    (hPo : OrderOneEnvelope P) :
    IsCompletedResponsePositiveSquareGauge
      (completedResponsePositiveSquareGauge P) := by
  exact ⟨differentiable_completedResponsePositiveSquareGauge hPd,
    completedResponsePositiveSquareGauge_nat P,
    completedResponsePositiveSquareGauge_neg_two P,
    completedResponsePositiveSquareGauge_neg_three_halves P,
    completedResponsePositiveSquareGauge_neg_one P,
    completedResponsePositiveSquareGauge_reflection hPr,
    completedResponsePositiveSquareGauge_conj hPc,
    orderOneEnvelope_completedResponsePositiveSquareGauge hPo,
    completedResponsePositiveSquareGauge_real_positive hPc⟩

def positiveSquareInterpolationTarget : ℂ :=
  I / anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint

def positiveSquareInterpolationPolynomial (z : ℂ) : ℂ :=
  (positiveSquareInterpolationTarget.re : ℂ) +
    ((2 * positiveSquareInterpolationTarget.im : ℝ) : ℂ) *
      ((z + (3 / 2 : ℂ)) ^ 2 + 15 / 16)

theorem positiveSquareInterpolationPolynomial_nonrealInteriorResponsePoint :
    positiveSquareInterpolationPolynomial nonrealInteriorResponsePoint =
      positiveSquareInterpolationTarget := by
  have hu :
      (nonrealInteriorResponsePoint + (3 / 2 : ℂ)) ^ 2 + 15 / 16 = I / 2 := by
    rw [nonrealInteriorResponsePoint]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [positiveSquareInterpolationPolynomial, hu]
  apply Complex.ext
  · simp
  · simp
    ring

theorem differentiable_positiveSquareInterpolationPolynomial :
    Differentiable ℂ positiveSquareInterpolationPolynomial := by
  unfold positiveSquareInterpolationPolynomial
  fun_prop

theorem positiveSquareInterpolationPolynomial_reflection (z : ℂ) :
    positiveSquareInterpolationPolynomial (-3 - z) =
      positiveSquareInterpolationPolynomial z := by
  unfold positiveSquareInterpolationPolynomial
  ring

theorem positiveSquareInterpolationPolynomial_conj (z : ℂ) :
    positiveSquareInterpolationPolynomial ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (positiveSquareInterpolationPolynomial z) := by
  simp only [positiveSquareInterpolationPolynomial, map_add, map_mul, map_pow,
    map_ofNat, map_div₀, Complex.conj_ofReal]

theorem orderOneEnvelope_positiveSquareInterpolationPolynomial :
    OrderOneEnvelope positiveSquareInterpolationPolynomial := by
  have hid : OrderOneEnvelope (fun z : ℂ => z) := orderOneEnvelope_id
  have hc : OrderOneEnvelope (fun z : ℂ => z + (3 / 2 : ℂ)) :=
    hid.add (orderOneEnvelope_const (3 / 2))
  have hsq : OrderOneEnvelope (fun z : ℂ => (z + (3 / 2 : ℂ)) ^ 2) := by
    exact (hc.mul hc).congr fun z => by ring
  have hoff : OrderOneEnvelope
      (fun z : ℂ => (z + (3 / 2 : ℂ)) ^ 2 + 15 / 16) :=
    hsq.add (orderOneEnvelope_const (15 / 16))
  have hscaled : OrderOneEnvelope
      (fun z : ℂ => ((2 * positiveSquareInterpolationTarget.im : ℝ) : ℂ) *
        ((z + (3 / 2 : ℂ)) ^ 2 + 15 / 16)) :=
    hoff.const_mul ((2 * positiveSquareInterpolationTarget.im : ℝ) : ℂ)
  exact ((orderOneEnvelope_const (positiveSquareInterpolationTarget.re : ℂ)).add
    hscaled).congr fun z => rfl

def positiveAnchoredResponseGauge (z : ℂ) : ℂ :=
  completedResponsePositiveSquareGauge positiveSquareInterpolationPolynomial z

theorem positiveAnchoredResponseGauge_nonrealInteriorResponsePoint_zero :
    positiveAnchoredResponseGauge nonrealInteriorResponsePoint = 0 := by
  rw [positiveAnchoredResponseGauge, completedResponsePositiveSquareGauge,
    positiveSquareInterpolationPolynomial_nonrealInteriorResponsePoint,
    positiveSquareInterpolationTarget]
  rw [div_mul_cancel₀ I
    anchoredSymmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero]
  rw [Complex.I_sq]
  ring

theorem positiveAnchoredResponseGauge_package :
    IsCompletedResponsePositiveSquareGauge positiveAnchoredResponseGauge := by
  exact completedResponsePositiveSquareGauge_package
    differentiable_positiveSquareInterpolationPolynomial
    positiveSquareInterpolationPolynomial_reflection
    positiveSquareInterpolationPolynomial_conj
    orderOneEnvelope_positiveSquareInterpolationPolynomial

/-- Completed response with all physical samples and real-axis phase preserved by a positive
multiplier, but with an inserted nonreal off-critical zero. -/
def realAxisAnchoredResponseCountermodel (z : ℂ) : ℂ :=
  completedBlackHoleJetInterpolation z * positiveAnchoredResponseGauge z

theorem differentiable_realAxisAnchoredResponseCountermodel :
    Differentiable ℂ realAxisAnchoredResponseCountermodel := by
  exact differentiable_completedBlackHoleJetInterpolation.mul
    positiveAnchoredResponseGauge_package.1

theorem realAxisAnchoredResponseCountermodel_nat (scaleLog : ℂ) (m : ℕ) :
    realAxisAnchoredResponseCountermodel (m : ℂ) =
      completedBlackHoleJetSample scaleLog m := by
  rw [realAxisAnchoredResponseCountermodel,
    positiveAnchoredResponseGauge_package.2.1 m, mul_one,
    completedBlackHoleJetInterpolation_nat]

theorem realAxisAnchoredResponseCountermodel_reflection (z : ℂ) :
    realAxisAnchoredResponseCountermodel (-3 - z) =
      realAxisAnchoredResponseCountermodel z := by
  rw [realAxisAnchoredResponseCountermodel, realAxisAnchoredResponseCountermodel,
    completedBlackHoleJetInterpolation_reflection,
    positiveAnchoredResponseGauge_package.2.2.2.2.2.1]

theorem realAxisAnchoredResponseCountermodel_conj (z : ℂ) :
    realAxisAnchoredResponseCountermodel ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (realAxisAnchoredResponseCountermodel z) := by
  rw [realAxisAnchoredResponseCountermodel, realAxisAnchoredResponseCountermodel,
    completedBlackHoleJetInterpolation_conj,
    positiveAnchoredResponseGauge_package.2.2.2.2.2.2.1, map_mul]

theorem orderOneEnvelope_realAxisAnchoredResponseCountermodel :
    OrderOneEnvelope realAxisAnchoredResponseCountermodel := by
  exact (orderOneEnvelope_completedBlackHoleJetInterpolation.mul
    positiveAnchoredResponseGauge_package.2.2.2.2.2.2.2.1).congr fun z => rfl

theorem realAxisAnchoredResponseCountermodel_neg_two :
    realAxisAnchoredResponseCountermodel (-2) =
      completedBlackHoleJetInterpolation (-2) := by
  rw [realAxisAnchoredResponseCountermodel,
    positiveAnchoredResponseGauge_package.2.2.1, mul_one]

theorem realAxisAnchoredResponseCountermodel_neg_three_halves :
    realAxisAnchoredResponseCountermodel (-(3 / 2 : ℂ)) =
      completedBlackHoleJetInterpolation (-(3 / 2 : ℂ)) := by
  rw [realAxisAnchoredResponseCountermodel,
    positiveAnchoredResponseGauge_package.2.2.2.1, mul_one]

theorem realAxisAnchoredResponseCountermodel_neg_one :
    realAxisAnchoredResponseCountermodel (-1) =
      completedBlackHoleJetInterpolation (-1) := by
  rw [realAxisAnchoredResponseCountermodel,
    positiveAnchoredResponseGauge_package.2.2.2.2.1, mul_one]

theorem realAxisAnchoredResponseCountermodel_real_positiveMultiple (σ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      realAxisAnchoredResponseCountermodel (σ : ℂ) =
        (r : ℂ) * completedBlackHoleJetInterpolation (σ : ℂ) := by
  obtain ⟨r, hr, hG⟩ :=
    positiveAnchoredResponseGauge_package.2.2.2.2.2.2.2.2 σ
  refine ⟨r, hr, ?_⟩
  rw [realAxisAnchoredResponseCountermodel, hG]
  ring

theorem realAxisAnchoredResponseCountermodel_real_ne_zero (σ : ℝ) :
    realAxisAnchoredResponseCountermodel (σ : ℂ) ≠ 0 := by
  obtain ⟨r, hr, hF⟩ :=
    realAxisAnchoredResponseCountermodel_real_positiveMultiple σ
  rw [hF]
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt hr
  · rw [completedBlackHoleJetInterpolation]
    convert xi_ne_zero_of_ofReal (σ + 2) using 1
    push_cast
    ring

theorem realAxisAnchoredResponseCountermodel_nonrealInteriorResponsePoint_zero :
    realAxisAnchoredResponseCountermodel nonrealInteriorResponsePoint = 0 := by
  rw [realAxisAnchoredResponseCountermodel,
    positiveAnchoredResponseGauge_nonrealInteriorResponsePoint_zero, mul_zero]

theorem realAxisAnchoredResponseCountermodel_ne_canonical :
    realAxisAnchoredResponseCountermodel ≠ completedBlackHoleJetInterpolation := by
  have hXne : completedBlackHoleJetInterpolation ≠ 0 := by
    intro hzero
    have hz := congrFun hzero 0
    exact (xi_ne_zero_of_ofReal 2) (by simpa [completedBlackHoleJetInterpolation] using hz)
  have hGsubd : Differentiable ℂ
      (fun z => positiveAnchoredResponseGauge z - 1) :=
    positiveAnchoredResponseGauge_package.1.sub (differentiable_const 1)
  have hGsubne : (fun z => positiveAnchoredResponseGauge z - 1) ≠ 0 := by
    intro hzero
    have hz := congrFun hzero nonrealInteriorResponsePoint
    rw [positiveAnchoredResponseGauge_nonrealInteriorResponsePoint_zero] at hz
    norm_num at hz
  have hprodne := differentiable_mul_ne_zero
    differentiable_completedBlackHoleJetInterpolation hGsubd hXne hGsubne
  intro hcanonical
  apply hprodne
  funext z
  have hz := congrFun hcanonical z
  rw [realAxisAnchoredResponseCountermodel] at hz
  change completedBlackHoleJetInterpolation z *
    (positiveAnchoredResponseGauge z - 1) = 0
  linear_combination hz

/-- Strongest natural real-axis repair package for completed physical-response interpolation. -/
def IsRealAxisAnchoredCompletedBlackHoleJetPackage
    (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  IsCompletedBlackHoleJetAnalyticPackage scaleLog F ∧
    F (-2) = completedBlackHoleJetInterpolation (-2) ∧
    F (-(3 / 2 : ℂ)) = completedBlackHoleJetInterpolation (-(3 / 2 : ℂ)) ∧
    F (-1) = completedBlackHoleJetInterpolation (-1) ∧
    (∀ σ : ℝ, F (σ : ℂ) ≠ 0) ∧
    ∀ σ : ℝ, ∃ r : ℝ, 0 < r ∧
      F (σ : ℂ) = (r : ℂ) * completedBlackHoleJetInterpolation (σ : ℂ)

theorem realAxisAnchoredResponseCountermodel_package (scaleLog : ℂ) :
    IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog
      realAxisAnchoredResponseCountermodel := by
  exact ⟨⟨differentiable_realAxisAnchoredResponseCountermodel,
      realAxisAnchoredResponseCountermodel_nat scaleLog,
      realAxisAnchoredResponseCountermodel_reflection,
      realAxisAnchoredResponseCountermodel_conj,
      orderOneEnvelope_realAxisAnchoredResponseCountermodel⟩,
    realAxisAnchoredResponseCountermodel_neg_two,
    realAxisAnchoredResponseCountermodel_neg_three_halves,
    realAxisAnchoredResponseCountermodel_neg_one,
    realAxisAnchoredResponseCountermodel_real_ne_zero,
    realAxisAnchoredResponseCountermodel_real_positiveMultiple⟩

/-- **Real-axis anchored completed-response route kill.** Completed physical response samples,
functional equation, Schwarz reality, order-one growth, exact endpoint/center values, full
real-axis zero-freeness, and even the canonical real-axis phase ray do not control nonreal zeros. -/
theorem completed_response_anchors_realAxis_route_noGo (scaleLog : ℂ) :
    ∃ F : ℂ → ℂ, ∃ z : ℂ,
      IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog F ∧
      0 < (z + 2).re ∧ (z + 2).re < 1 ∧
      (z + 2).re ≠ 1 / 2 ∧ (z + 2).im ≠ 0 ∧
      F z = 0 ∧ F ≠ completedBlackHoleJetInterpolation := by
  refine ⟨realAxisAnchoredResponseCountermodel, nonrealInteriorResponsePoint,
    realAxisAnchoredResponseCountermodel_package scaleLog, ?_, ?_, ?_, ?_,
    realAxisAnchoredResponseCountermodel_nonrealInteriorResponsePoint_zero,
    realAxisAnchoredResponseCountermodel_ne_canonical⟩
  all_goals norm_num [nonrealInteriorResponsePoint]

end RHTower
