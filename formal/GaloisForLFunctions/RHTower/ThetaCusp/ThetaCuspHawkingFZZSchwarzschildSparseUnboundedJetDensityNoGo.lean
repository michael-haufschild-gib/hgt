import GaloisForLFunctions.HTGeometry.SparseUnboundedMultiplicityCanonicalProduct
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZSchwarzschildCompletedResponseBoundedJetFiltrationNoGo
import GaloisForLFunctions.RHTower.DeBrangesFiniteOrderRigidity
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm
import GaloisForLFunctions.HTGeometry.EntireMultiplicityFactor

/-!
# FZZ completed-response sparse unbounded-jet density no-go

This module kills the strongest still-local repair of the FZZ-P source-selection chain.  One fixed
completed response matches Xi through complex-order jet depth `k` at physical response order
`(k+1)^(3 : ℕ)` for every `k`, while preserving the completed functional equation, Schwarz reality,
order-one growth, all three completed anchors, natural response samples, and the strictly positive
real-axis phase ray.  The same response nevertheless has an interior off-critical zero.

The construction uses an order-one canonical product with exact multiplicity `k+1` at cubic-spaced
centered nodes, response-reflection symmetrization, corpus Schwarz-sharp symmetrization, and the
anchored positive-square Gamma-null gauge.  Its difference from Xi contains the square of the
Schwarz product and therefore vanishes to order at least `4(k+1)` at the `k`-th sparse node.

**[FALSIFIED] [ROUTE KILL] [PAPER-PROVED] [LEAN-PROVED]** Unbounded pointwise-finite physical
response jets, without a cumulative weighted density condition, determine the completed response
or its nonreal divisor.

The exact positive survivor is cumulative multiplicity density: the construction spends only
summable first reciprocal mass and has cumulative multiplicity `O(R^(2/3))`.  Any surviving local
FZZ selector must prove a genuine uniqueness-density theorem, not merely unbounded jet depth.
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Exact analytic order gives vanishing of mathlib's Fréchet `iteratedDeriv` below that order. -/
theorem iteratedDeriv_eq_zero_before_analyticOrderAt_eq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {n r : ℕ}
    (horder : analyticOrderAt f c = ((n : ℕ) : ℕ∞)) (hr : r < n) :
    iteratedDeriv r f c = 0 := by
  have hfan : ∀ z, AnalyticAt ℂ f z :=
    fun z => (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf) z (Set.mem_univ z)
  obtain ⟨g, hg, _hgne, hfac⟩ :=
    exists_entire_factor_of_analyticOrderAt_eq hfan c n horder
  have hlin : Differentiable ℂ (fun z : ℂ => z - c) := by fun_prop
  have hgdiff : Differentiable ℂ g := by
    intro z
    exact (hg z).differentiableAt
  have hzero : iteratedDeriv r (fun z => (z - c) ^ n * g z) c = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      (hlin.pow n).contDiff.contDiffAt hgdiff.contDiff.contDiffAt
      (m := n) (n := 0)
      (fun j hj => iteratedDeriv_pow_eq_zero_before_order hlin (by simp) n j hj)
      (fun j hj => by omega) (by omega)
  have hfun : f = fun z => (z - c) ^ n * g z := by
    funext z
    exact hfac z
  rw [hfun]
  exact hzero

/-- Reflection-even raw product obtained by centering the sparse divisor at response `-3/2`. -/
def sparseJetRawEvenProduct (z : ℂ) : ℂ :=
  sparseJetCanonicalProduct (z + (3 / 2 : ℂ)) *
    sparseJetCanonicalProduct (-z - (3 / 2 : ℂ))

/-- Schwarz-real, response-reflection-even product carrying twice the raw multiplicity. -/
def sparseJetSchwarzEvenProduct (z : ℂ) : ℂ :=
  sparseJetRawEvenProduct z *
    GaloisForLFunctions.RHTower.suzukiEntireSharp sparseJetRawEvenProduct z

theorem differentiable_sparseJetRawEvenProduct :
    Differentiable ℂ sparseJetRawEvenProduct := by
  have hplus : Differentiable ℂ (fun z : ℂ => z + (3 / 2 : ℂ)) := by fun_prop
  have hminus : Differentiable ℂ (fun z : ℂ => -z - (3 / 2 : ℂ)) := by fun_prop
  intro z
  exact (differentiable_sparseJetCanonicalProduct.comp hplus z).mul
    (differentiable_sparseJetCanonicalProduct.comp hminus z)

theorem sparseJetRawEvenProduct_reflection (z : ℂ) :
    sparseJetRawEvenProduct (-3 - z) = sparseJetRawEvenProduct z := by
  unfold sparseJetRawEvenProduct
  have h1 : -3 - z + (3 / 2 : ℂ) = -z - (3 / 2 : ℂ) := by ring
  have h2 : -(-3 - z) - (3 / 2 : ℂ) = z + (3 / 2 : ℂ) := by ring
  rw [h1, h2]
  exact mul_comm _ _

theorem differentiable_sparseJetSchwarzEvenProduct :
    Differentiable ℂ sparseJetSchwarzEvenProduct := by
  have hrawAnalytic : AnalyticOnNhd ℂ sparseJetRawEvenProduct Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_sparseJetRawEvenProduct
  have hsharpAnalytic :=
    GaloisForLFunctions.RHTower.analyticOnNhd_suzukiEntireSharp hrawAnalytic
  exact differentiable_sparseJetRawEvenProduct.mul
    (Complex.analyticOnNhd_univ_iff_differentiable.mp hsharpAnalytic)

theorem sparseJetSchwarzEvenProduct_reflection (z : ℂ) :
    sparseJetSchwarzEvenProduct (-3 - z) = sparseJetSchwarzEvenProduct z := by
  rw [sparseJetSchwarzEvenProduct, sparseJetSchwarzEvenProduct,
    sparseJetRawEvenProduct_reflection]
  unfold GaloisForLFunctions.RHTower.suzukiEntireSharp
  have harg : (starRingEnd ℂ) (-3 - z) = -3 - (starRingEnd ℂ) z := by
    apply Complex.ext <;> simp
  rw [harg, sparseJetRawEvenProduct_reflection]

theorem sparseJetSchwarzEvenProduct_conj (z : ℂ) :
    sparseJetSchwarzEvenProduct ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (sparseJetSchwarzEvenProduct z) := by
  have hreal := GaloisForLFunctions.RHTower.schwarzReal_mul_sharp
    sparseJetRawEvenProduct ((starRingEnd ℂ) z)
  simpa [sparseJetSchwarzEvenProduct,
    GaloisForLFunctions.RHTower.suzukiEntireSharp] using hreal.symm

theorem orderOneEnvelope_sparseJetRawEvenProduct :
    OrderOneEnvelope sparseJetRawEvenProduct := by
  exact ((orderOneEnvelope_sparseJetCanonicalProduct.comp_affine 1 (3 / 2)).mul
    (orderOneEnvelope_sparseJetCanonicalProduct.comp_affine (-1) (-(3 / 2)))).congr
      fun z => by
        unfold sparseJetRawEvenProduct
        congr 1 <;> ring

theorem orderOneEnvelope_suzukiEntireSharp_sparseJetRawEvenProduct :
    OrderOneEnvelope
      (GaloisForLFunctions.RHTower.suzukiEntireSharp sparseJetRawEvenProduct) := by
  obtain ⟨C, hC, hb⟩ := orderOneEnvelope_sparseJetRawEvenProduct
  refine ⟨C, hC, fun z => ?_⟩
  simpa [GaloisForLFunctions.RHTower.suzukiEntireSharp, orderOneWeight] using
    hb ((starRingEnd ℂ) z)

theorem orderOneEnvelope_sparseJetSchwarzEvenProduct :
    OrderOneEnvelope sparseJetSchwarzEvenProduct := by
  exact (orderOneEnvelope_sparseJetRawEvenProduct.mul
    orderOneEnvelope_suzukiEntireSharp_sparseJetRawEvenProduct).congr fun z => rfl

theorem sparseJetRawEvenProduct_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    sparseJetRawEvenProduct z ≠ 0 := by
  apply mul_ne_zero
  · apply sparseJetCanonicalProduct_ne_zero
    intro k h
    have him := congrArg Complex.im h
    simp at him
    exact hz him
  · apply sparseJetCanonicalProduct_ne_zero
    intro k h
    have him := congrArg Complex.im h
    simp at him
    exact hz (by linarith)

theorem sparseJetSchwarzEvenProduct_nonrealInteriorResponsePoint_ne_zero :
    sparseJetSchwarzEvenProduct nonrealInteriorResponsePoint ≠ 0 := by
  apply mul_ne_zero
  · apply sparseJetRawEvenProduct_ne_zero_of_im_ne_zero
    norm_num [nonrealInteriorResponsePoint]
  · unfold GaloisForLFunctions.RHTower.suzukiEntireSharp
    have hraw : sparseJetRawEvenProduct ((starRingEnd ℂ) nonrealInteriorResponsePoint) ≠ 0 := by
      apply sparseJetRawEvenProduct_ne_zero_of_im_ne_zero
      have ha : nonrealInteriorResponsePoint.im ≠ 0 := by
        norm_num [nonrealInteriorResponsePoint]
      simpa using neg_ne_zero.mpr ha
    exact (map_ne_zero (starRingEnd ℂ)).2 hraw

theorem analyticOrderAt_sparseJetRawEvenProduct (k : ℕ) :
    analyticOrderAt sparseJetRawEvenProduct (sparseJetPhysicalNode k : ℂ) =
      ((k + 1 : ℕ) : ℕ∞) := by
  let m : ℂ := (sparseJetPhysicalNode k : ℂ)
  have harg : m + (3 / 2 : ℂ) = (sparseJetCenteredNode k : ℂ) := by
    dsimp [m, sparseJetCenteredNode]
    push_cast
    ring
  have hplus : Differentiable ℂ (fun z : ℂ => z + (3 / 2 : ℂ)) := by fun_prop
  have hminus : Differentiable ℂ (fun z : ℂ => -z - (3 / 2 : ℂ)) := by fun_prop
  have hfirstDiff : Differentiable ℂ
      (fun z : ℂ => sparseJetCanonicalProduct (z + (3 / 2 : ℂ))) := by
    intro z
    exact differentiable_sparseJetCanonicalProduct.comp hplus z
  have hsecondDiff : Differentiable ℂ
      (fun z : ℂ => sparseJetCanonicalProduct (-z - (3 / 2 : ℂ))) := by
    intro z
    exact differentiable_sparseJetCanonicalProduct.comp hminus z
  have hfirstAnalytic : AnalyticAt ℂ
      (fun z : ℂ => sparseJetCanonicalProduct (z + (3 / 2 : ℂ))) m :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hfirstDiff) m (Set.mem_univ m)
  have hsecondAnalytic : AnalyticAt ℂ
      (fun z : ℂ => sparseJetCanonicalProduct (-z - (3 / 2 : ℂ))) m :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hsecondDiff) m (Set.mem_univ m)
  have hfirst : analyticOrderAt
      (fun z : ℂ => sparseJetCanonicalProduct (z + (3 / 2 : ℂ))) m =
        ((k + 1 : ℕ) : ℕ∞) := by
    have hcomp := analyticOrderAt_comp_affine (f := sparseJetCanonicalProduct)
      (μ := (1 : ℂ)) (ν := (3 / 2 : ℂ)) (z := m) (n := k + 1)
      (by norm_num)
      (by
        simp only [one_mul]
        rw [harg]
        exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
          differentiable_sparseJetCanonicalProduct) _ (Set.mem_univ _))
      (by simpa [one_mul, harg] using analyticOrderAt_sparseJetCanonicalProduct k)
    simpa using hcomp
  have hsecondNe : sparseJetCanonicalProduct (-m - (3 / 2 : ℂ)) ≠ 0 := by
    apply sparseJetCanonicalProduct_ne_zero
    intro l h
    have hre := congrArg Complex.re h
    dsimp [m, sparseJetCenteredNode, sparseJetPhysicalNode] at hre
    norm_num at hre
    have hkpos : 0 < ((k : ℝ) + 1) ^ (3 : ℕ) := by positivity
    have hlpos : 0 < ((l : ℝ) + 1) ^ (3 : ℕ) := by positivity
    nlinarith
  have hfun : (fun z : ℂ => sparseJetCanonicalProduct (z + (3 / 2 : ℂ)) *
      sparseJetCanonicalProduct (-z - (3 / 2 : ℂ))) =
      (fun z : ℂ => sparseJetCanonicalProduct (z + (3 / 2 : ℂ))) *
        (fun z : ℂ => sparseJetCanonicalProduct (-z - (3 / 2 : ℂ))) := rfl
  change analyticOrderAt
      (fun z : ℂ => sparseJetCanonicalProduct (z + (3 / 2 : ℂ)) *
        sparseJetCanonicalProduct (-z - (3 / 2 : ℂ))) m = _
  rw [hfun, analyticOrderAt_mul hfirstAnalytic hsecondAnalytic, hfirst,
    hsecondAnalytic.analyticOrderAt_eq_zero.mpr hsecondNe, add_zero]

theorem analyticOrderAt_sparseJetSchwarzEvenProduct (k : ℕ) :
    analyticOrderAt sparseJetSchwarzEvenProduct (sparseJetPhysicalNode k : ℂ) =
      ((2 * (k + 1) : ℕ) : ℕ∞) := by
  let m : ℂ := (sparseJetPhysicalNode k : ℂ)
  have hrawAnalytic : AnalyticAt ℂ sparseJetRawEvenProduct m :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      differentiable_sparseJetRawEvenProduct) m (Set.mem_univ m)
  have hsharpAnalytic : AnalyticAt ℂ
      (GaloisForLFunctions.RHTower.suzukiEntireSharp sparseJetRawEvenProduct) m :=
    (GaloisForLFunctions.RHTower.analyticOnNhd_suzukiEntireSharp
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        differentiable_sparseJetRawEvenProduct)) m (Set.mem_univ m)
  have hsharp : analyticOrderAt
      (GaloisForLFunctions.RHTower.suzukiEntireSharp sparseJetRawEvenProduct) m =
        ((k + 1 : ℕ) : ℕ∞) := by
    have hs := GaloisForLFunctions.RHTower.analyticOrderAt_suzukiEntireSharp_conj
      differentiable_sparseJetRawEvenProduct m
    have hmstar : star m = m := by simp [m]
    rw [hmstar, analyticOrderAt_sparseJetRawEvenProduct] at hs
    exact hs
  change analyticOrderAt
      (fun z => sparseJetRawEvenProduct z *
        GaloisForLFunctions.RHTower.suzukiEntireSharp sparseJetRawEvenProduct z) m = _
  have hfun : (fun z => sparseJetRawEvenProduct z *
      GaloisForLFunctions.RHTower.suzukiEntireSharp sparseJetRawEvenProduct z) =
      sparseJetRawEvenProduct *
        GaloisForLFunctions.RHTower.suzukiEntireSharp sparseJetRawEvenProduct := rfl
  rw [hfun, analyticOrderAt_mul hrawAnalytic hsharpAnalytic,
    analyticOrderAt_sparseJetRawEvenProduct, hsharp]
  norm_cast
  omega

/-- Target value for the centered real quadratic after inserting the sparse divisor. -/
def sparseJetInterpolationTarget : ℂ :=
  I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
    sparseJetSchwarzEvenProduct nonrealInteriorResponsePoint)

/-- Real-coefficient centered quadratic interpolating `sparseJetInterpolationTarget`. -/
def sparseJetInterpolationPolynomial (z : ℂ) : ℂ :=
  (sparseJetInterpolationTarget.re : ℂ) +
    ((2 * sparseJetInterpolationTarget.im : ℝ) : ℂ) *
      ((z + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16)

theorem sparseJetInterpolationPolynomial_nonrealInteriorResponsePoint :
    sparseJetInterpolationPolynomial nonrealInteriorResponsePoint =
      sparseJetInterpolationTarget := by
  have hu :
      (nonrealInteriorResponsePoint + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16 = I / 2 := by
    rw [nonrealInteriorResponsePoint]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [sparseJetInterpolationPolynomial, hu]
  apply Complex.ext
  · simp
  · simp
    ring

theorem differentiable_sparseJetInterpolationPolynomial :
    Differentiable ℂ sparseJetInterpolationPolynomial := by
  unfold sparseJetInterpolationPolynomial
  fun_prop

theorem sparseJetInterpolationPolynomial_reflection (z : ℂ) :
    sparseJetInterpolationPolynomial (-3 - z) = sparseJetInterpolationPolynomial z := by
  unfold sparseJetInterpolationPolynomial
  ring

theorem sparseJetInterpolationPolynomial_conj (z : ℂ) :
    sparseJetInterpolationPolynomial ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (sparseJetInterpolationPolynomial z) := by
  simp only [sparseJetInterpolationPolynomial, map_add, map_mul, map_pow,
    map_ofNat, map_div₀, Complex.conj_ofReal]

theorem orderOneEnvelope_sparseJetInterpolationPolynomial :
    OrderOneEnvelope sparseJetInterpolationPolynomial := by
  have hid : OrderOneEnvelope (fun z : ℂ => z) := orderOneEnvelope_id
  have hc : OrderOneEnvelope (fun z : ℂ => z + (3 / 2 : ℂ)) :=
    hid.add (orderOneEnvelope_const (3 / 2))
  have hsq : OrderOneEnvelope (fun z : ℂ => (z + (3 / 2 : ℂ)) ^ (2 : ℕ)) := by
    exact (hc.mul hc).congr fun z => by ring
  have hoff : OrderOneEnvelope
      (fun z : ℂ => (z + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16) :=
    hsq.add (orderOneEnvelope_const (15 / 16))
  exact ((orderOneEnvelope_const (sparseJetInterpolationTarget.re : ℂ)).add
    (((orderOneEnvelope_const ((2 * sparseJetInterpolationTarget.im : ℝ) : ℂ))).mul
      hoff)).congr fun z => by simp [sparseJetInterpolationPolynomial]

/-- Order-one, FE-even, Schwarz-real multiplier inserted into the completed positive gauge. -/
def sparseUnboundedJetMultiplier (z : ℂ) : ℂ :=
  sparseJetInterpolationPolynomial z * sparseJetSchwarzEvenProduct z

theorem differentiable_sparseUnboundedJetMultiplier :
    Differentiable ℂ sparseUnboundedJetMultiplier :=
  differentiable_sparseJetInterpolationPolynomial.mul
    differentiable_sparseJetSchwarzEvenProduct

theorem sparseUnboundedJetMultiplier_reflection (z : ℂ) :
    sparseUnboundedJetMultiplier (-3 - z) = sparseUnboundedJetMultiplier z := by
  simp [sparseUnboundedJetMultiplier, sparseJetInterpolationPolynomial_reflection,
    sparseJetSchwarzEvenProduct_reflection]

theorem sparseUnboundedJetMultiplier_conj (z : ℂ) :
    sparseUnboundedJetMultiplier ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (sparseUnboundedJetMultiplier z) := by
  simp [sparseUnboundedJetMultiplier, sparseJetInterpolationPolynomial_conj,
    sparseJetSchwarzEvenProduct_conj, map_mul]

theorem orderOneEnvelope_sparseUnboundedJetMultiplier :
    OrderOneEnvelope sparseUnboundedJetMultiplier := by
  exact (orderOneEnvelope_sparseJetInterpolationPolynomial.mul
    orderOneEnvelope_sparseJetSchwarzEvenProduct).congr fun z => rfl

theorem sparseUnboundedJetMultiplier_mul_generator_target :
    sparseUnboundedJetMultiplier nonrealInteriorResponsePoint *
      anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint = I := by
  rw [sparseUnboundedJetMultiplier,
    sparseJetInterpolationPolynomial_nonrealInteriorResponsePoint,
    sparseJetInterpolationTarget]
  have hden : anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
      sparseJetSchwarzEvenProduct nonrealInteriorResponsePoint ≠ 0 :=
    mul_ne_zero anchoredSymmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero
      sparseJetSchwarzEvenProduct_nonrealInteriorResponsePoint_ne_zero
  calc
    I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
        sparseJetSchwarzEvenProduct nonrealInteriorResponsePoint) *
        sparseJetSchwarzEvenProduct nonrealInteriorResponsePoint *
        anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint =
      I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
        sparseJetSchwarzEvenProduct nonrealInteriorResponsePoint) *
        (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
          sparseJetSchwarzEvenProduct nonrealInteriorResponsePoint) := by ring
    _ = I := div_mul_cancel₀ I hden

/-- One fixed completed positive-square gauge carrying every sparse jet depth simultaneously. -/
def sparseUnboundedJetGauge (z : ℂ) : ℂ :=
  completedResponsePositiveSquareGauge sparseUnboundedJetMultiplier z

theorem sparseUnboundedJetGauge_package :
    IsCompletedResponsePositiveSquareGauge sparseUnboundedJetGauge := by
  exact completedResponsePositiveSquareGauge_package
    differentiable_sparseUnboundedJetMultiplier
    sparseUnboundedJetMultiplier_reflection
    sparseUnboundedJetMultiplier_conj
    orderOneEnvelope_sparseUnboundedJetMultiplier

theorem sparseUnboundedJetGauge_nonrealInteriorResponsePoint_zero :
    sparseUnboundedJetGauge nonrealInteriorResponsePoint = 0 := by
  rw [sparseUnboundedJetGauge, completedResponsePositiveSquareGauge,
    sparseUnboundedJetMultiplier_mul_generator_target, Complex.I_sq]
  ring

/-- Completed FZZ response with sparse unbounded complex-order jet contact. -/
def sparseUnboundedJetResponseCountermodel (z : ℂ) : ℂ :=
  completedBlackHoleJetInterpolation z * sparseUnboundedJetGauge z

theorem differentiable_sparseUnboundedJetResponseCountermodel :
    Differentiable ℂ sparseUnboundedJetResponseCountermodel := by
  exact differentiable_completedBlackHoleJetInterpolation.mul
    sparseUnboundedJetGauge_package.1

theorem sparseUnboundedJetResponseCountermodel_nat (scaleLog : ℂ) (m : ℕ) :
    sparseUnboundedJetResponseCountermodel (m : ℂ) =
      completedBlackHoleJetSample scaleLog m := by
  rw [sparseUnboundedJetResponseCountermodel,
    sparseUnboundedJetGauge_package.2.1 m, mul_one,
    completedBlackHoleJetInterpolation_nat]

theorem sparseUnboundedJetResponseCountermodel_reflection (z : ℂ) :
    sparseUnboundedJetResponseCountermodel (-3 - z) =
      sparseUnboundedJetResponseCountermodel z := by
  rw [sparseUnboundedJetResponseCountermodel,
    sparseUnboundedJetResponseCountermodel,
    completedBlackHoleJetInterpolation_reflection,
    sparseUnboundedJetGauge_package.2.2.2.2.2.1]

theorem sparseUnboundedJetResponseCountermodel_conj (z : ℂ) :
    sparseUnboundedJetResponseCountermodel ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (sparseUnboundedJetResponseCountermodel z) := by
  rw [sparseUnboundedJetResponseCountermodel,
    sparseUnboundedJetResponseCountermodel,
    completedBlackHoleJetInterpolation_conj,
    sparseUnboundedJetGauge_package.2.2.2.2.2.2.1, map_mul]

theorem orderOneEnvelope_sparseUnboundedJetResponseCountermodel :
    OrderOneEnvelope sparseUnboundedJetResponseCountermodel := by
  exact (orderOneEnvelope_completedBlackHoleJetInterpolation.mul
    sparseUnboundedJetGauge_package.2.2.2.2.2.2.2.1).congr fun z => rfl

theorem sparseUnboundedJetResponseCountermodel_neg_two :
    sparseUnboundedJetResponseCountermodel (-2) =
      completedBlackHoleJetInterpolation (-2) := by
  rw [sparseUnboundedJetResponseCountermodel,
    sparseUnboundedJetGauge_package.2.2.1, mul_one]

theorem sparseUnboundedJetResponseCountermodel_neg_three_halves :
    sparseUnboundedJetResponseCountermodel (-(3 / 2 : ℂ)) =
      completedBlackHoleJetInterpolation (-(3 / 2 : ℂ)) := by
  rw [sparseUnboundedJetResponseCountermodel,
    sparseUnboundedJetGauge_package.2.2.2.1, mul_one]

theorem sparseUnboundedJetResponseCountermodel_neg_one :
    sparseUnboundedJetResponseCountermodel (-1) =
      completedBlackHoleJetInterpolation (-1) := by
  rw [sparseUnboundedJetResponseCountermodel,
    sparseUnboundedJetGauge_package.2.2.2.2.1, mul_one]

theorem sparseUnboundedJetResponseCountermodel_real_positiveMultiple (σ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      sparseUnboundedJetResponseCountermodel (σ : ℂ) =
        (r : ℂ) * completedBlackHoleJetInterpolation (σ : ℂ) := by
  obtain ⟨r, hr, hG⟩ := sparseUnboundedJetGauge_package.2.2.2.2.2.2.2.2 σ
  refine ⟨r, hr, ?_⟩
  rw [sparseUnboundedJetResponseCountermodel, hG]
  ring

theorem sparseUnboundedJetResponseCountermodel_real_ne_zero (σ : ℝ) :
    sparseUnboundedJetResponseCountermodel (σ : ℂ) ≠ 0 := by
  obtain ⟨r, hr, hF⟩ :=
    sparseUnboundedJetResponseCountermodel_real_positiveMultiple σ
  rw [hF]
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt hr
  · rw [completedBlackHoleJetInterpolation]
    convert xi_ne_zero_of_ofReal (σ + 2) using 1
    push_cast
    ring

theorem sparseUnboundedJetResponseCountermodel_realAxis_package (scaleLog : ℂ) :
    IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog
      sparseUnboundedJetResponseCountermodel := by
  exact ⟨⟨differentiable_sparseUnboundedJetResponseCountermodel,
      sparseUnboundedJetResponseCountermodel_nat scaleLog,
      sparseUnboundedJetResponseCountermodel_reflection,
      sparseUnboundedJetResponseCountermodel_conj,
      orderOneEnvelope_sparseUnboundedJetResponseCountermodel⟩,
    sparseUnboundedJetResponseCountermodel_neg_two,
    sparseUnboundedJetResponseCountermodel_neg_three_halves,
    sparseUnboundedJetResponseCountermodel_neg_one,
    sparseUnboundedJetResponseCountermodel_real_ne_zero,
    sparseUnboundedJetResponseCountermodel_real_positiveMultiple⟩

theorem sparseJetSchwarzEvenProduct_sq_iteratedDeriv_zero
    (k r : ℕ) (hr : r < 4 * (k + 1)) :
    iteratedDeriv r (fun z => sparseJetSchwarzEvenProduct z ^ (2 : ℕ))
      (sparseJetPhysicalNode k : ℂ) = 0 := by
  let m : ℂ := (sparseJetPhysicalNode k : ℂ)
  have hQzero : ∀ j < 2 * (k + 1),
      iteratedDeriv j sparseJetSchwarzEvenProduct m = 0 := by
    intro j hj
    exact iteratedDeriv_eq_zero_before_analyticOrderAt_eq
      differentiable_sparseJetSchwarzEvenProduct
      (analyticOrderAt_sparseJetSchwarzEvenProduct k) hj
  have hmul : iteratedDeriv r
      (fun z => sparseJetSchwarzEvenProduct z * sparseJetSchwarzEvenProduct z) m = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      differentiable_sparseJetSchwarzEvenProduct.contDiff.contDiffAt
      differentiable_sparseJetSchwarzEvenProduct.contDiff.contDiffAt
      (m := 2 * (k + 1)) (n := 2 * (k + 1)) hQzero hQzero (by omega)
  simpa [m, pow_two] using hmul

/-- The single countermodel agrees with Xi through depth `k` at cubic physical node `(k+1)^(3 : ℕ)`. -/
theorem sparseUnboundedJetResponseCountermodel_iteratedDeriv
    (k j : ℕ) (hj : j ≤ k) :
    iteratedDeriv j sparseUnboundedJetResponseCountermodel
        (sparseJetPhysicalNode k : ℂ) =
      iteratedDeriv j completedBlackHoleJetInterpolation
        (sparseJetPhysicalNode k : ℂ) := by
  let H : ℂ → ℂ := fun z =>
    completedBlackHoleJetInterpolation z *
      (sparseJetInterpolationPolynomial z * anchoredSymmetricJetNullGenerator z) ^ (2 : ℕ)
  have hH : Differentiable ℂ H := by
    dsimp [H]
    exact differentiable_completedBlackHoleJetInterpolation.mul
      ((differentiable_sparseJetInterpolationPolynomial.mul
        differentiable_anchoredSymmetricJetNullGenerator).pow 2)
  have hQsq : Differentiable ℂ (fun z => sparseJetSchwarzEvenProduct z ^ (2 : ℕ)) :=
    differentiable_sparseJetSchwarzEvenProduct.pow 2
  have hprod : Differentiable ℂ
      (fun z => H z * sparseJetSchwarzEvenProduct z ^ (2 : ℕ)) := hH.mul hQsq
  have hzero : iteratedDeriv j
      (fun z => H z * sparseJetSchwarzEvenProduct z ^ (2 : ℕ))
        (sparseJetPhysicalNode k : ℂ) = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      hH.contDiff.contDiffAt hQsq.contDiff.contDiffAt
      (m := 0) (n := 4 * (k + 1)) (fun r hr => by omega)
      (fun r hr => sparseJetSchwarzEvenProduct_sq_iteratedDeriv_zero k r hr)
      (by omega)
  have hcounter : sparseUnboundedJetResponseCountermodel = fun z =>
      completedBlackHoleJetInterpolation z +
        H z * sparseJetSchwarzEvenProduct z ^ (2 : ℕ) := by
    funext z
    rw [sparseUnboundedJetResponseCountermodel, sparseUnboundedJetGauge,
      completedResponsePositiveSquareGauge, sparseUnboundedJetMultiplier]
    dsimp [H]
    ring
  rw [hcounter]
  have hsum : (fun z => completedBlackHoleJetInterpolation z +
      H z * sparseJetSchwarzEvenProduct z ^ (2 : ℕ)) =
      completedBlackHoleJetInterpolation +
        (fun z => H z * sparseJetSchwarzEvenProduct z ^ (2 : ℕ)) := rfl
  rw [hsum, iteratedDeriv_add
    differentiable_completedBlackHoleJetInterpolation.contDiff.contDiffAt
    hprod.contDiff.contDiffAt, hzero, add_zero]

/-- Strongest prior completed real-axis package plus one fixed unbounded sparse jet ladder. -/
def IsSparseUnboundedJetRealAxisAnchoredCompletedBlackHoleJetPackage
    (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog F ∧
    ∀ (k j : ℕ), j ≤ k →
      iteratedDeriv j F (sparseJetPhysicalNode k : ℂ) =
        iteratedDeriv j completedBlackHoleJetInterpolation
          (sparseJetPhysicalNode k : ℂ)

theorem sparseUnboundedJetResponseCountermodel_package (scaleLog : ℂ) :
    IsSparseUnboundedJetRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog
      sparseUnboundedJetResponseCountermodel := by
  exact ⟨sparseUnboundedJetResponseCountermodel_realAxis_package scaleLog,
    sparseUnboundedJetResponseCountermodel_iteratedDeriv⟩

theorem sparseUnboundedJetResponseCountermodel_nonrealInteriorResponsePoint_zero :
    sparseUnboundedJetResponseCountermodel nonrealInteriorResponsePoint = 0 := by
  rw [sparseUnboundedJetResponseCountermodel,
    sparseUnboundedJetGauge_nonrealInteriorResponsePoint_zero, mul_zero]

theorem sparseUnboundedJetResponseCountermodel_ne_canonical :
    sparseUnboundedJetResponseCountermodel ≠ completedBlackHoleJetInterpolation := by
  have hXne : completedBlackHoleJetInterpolation ≠ 0 := by
    intro hzero
    have hz := congrFun hzero 0
    exact (xi_ne_zero_of_ofReal 2)
      (by simpa [completedBlackHoleJetInterpolation] using hz)
  have hGsubd : Differentiable ℂ (fun z => sparseUnboundedJetGauge z - 1) :=
    sparseUnboundedJetGauge_package.1.sub (differentiable_const 1)
  have hGsubne : (fun z => sparseUnboundedJetGauge z - 1) ≠ 0 := by
    intro hzero
    have hz := congrFun hzero nonrealInteriorResponsePoint
    rw [sparseUnboundedJetGauge_nonrealInteriorResponsePoint_zero] at hz
    norm_num at hz
  have hprodne := differentiable_mul_ne_zero
    differentiable_completedBlackHoleJetInterpolation hGsubd hXne hGsubne
  intro hcanonical
  apply hprodne
  funext z
  have hz := congrFun hcanonical z
  rw [sparseUnboundedJetResponseCountermodel] at hz
  change completedBlackHoleJetInterpolation z * (sparseUnboundedJetGauge z - 1) = 0
  linear_combination hz

/-- **Sparse-unbounded-local-jet FZZ route kill.**  Arbitrarily deep finite jets on a sparse
physical subsequence, even with every prior completed real-axis constraint, do not control the
nonreal divisor.  A surviving local selector must impose cumulative weighted density. -/
theorem completed_response_sparseUnboundedJet_route_noGo (scaleLog : ℂ) :
    ∃ F : ℂ → ℂ, ∃ z : ℂ,
      IsSparseUnboundedJetRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog F ∧
      0 < (z + 2).re ∧ (z + 2).re < 1 ∧
      (z + 2).re ≠ 1 / 2 ∧ (z + 2).im ≠ 0 ∧
      F z = 0 ∧ F ≠ completedBlackHoleJetInterpolation := by
  refine ⟨sparseUnboundedJetResponseCountermodel, nonrealInteriorResponsePoint,
    sparseUnboundedJetResponseCountermodel_package scaleLog, ?_, ?_, ?_, ?_,
    sparseUnboundedJetResponseCountermodel_nonrealInteriorResponsePoint_zero,
    sparseUnboundedJetResponseCountermodel_ne_canonical⟩
  all_goals norm_num [nonrealInteriorResponsePoint]

end RHTower
