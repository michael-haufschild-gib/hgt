import GaloisForLFunctions.HTGeometry.DyadicSincLogDensityCanonicalProduct
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildSparseUnboundedJetDensityNoGo
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationEntire

/-!
# FZZ completed-response logarithmic-density saturation no-go

The dyadic sinc cascade places multiplicity `2^j` on every odd multiple of `2^j`.  Below centered
radius `2^K` these disjoint strata carry total jet weight `K * 2^(K-1)`, while the cascade remains
entire of order one.  After FE centering, Schwarz symmetrization, and insertion in the completed
positive-square Gamma-null gauge, one fixed response keeps this full logarithmic-density ladder
and every prior completed real-axis condition, yet has an interior off-critical zero.
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Centered dyadic cascade, even for completed-response reflection `z ↦ -3-z`. -/
def dyadicLogRawEvenProduct (z : ℂ) : ℂ :=
  dyadicSincCascade (z + (3 / 2 : ℂ))

/-- Schwarz-real dyadic logarithmic-density product. -/
def dyadicLogSchwarzEvenProduct (z : ℂ) : ℂ :=
  dyadicLogRawEvenProduct z *
    GaloisForLFunctions.RHTower.suzukiEntireSharp dyadicLogRawEvenProduct z

theorem differentiable_dyadicLogRawEvenProduct :
    Differentiable ℂ dyadicLogRawEvenProduct := by
  exact differentiable_dyadicSincCascade.comp (by fun_prop)

theorem dyadicLogRawEvenProduct_reflection (z : ℂ) :
    dyadicLogRawEvenProduct (-3 - z) = dyadicLogRawEvenProduct z := by
  unfold dyadicLogRawEvenProduct
  rw [show -3 - z + (3 / 2 : ℂ) = -(z + (3 / 2 : ℂ)) by ring,
    dyadicSincCascade_even]

theorem differentiable_dyadicLogSchwarzEvenProduct :
    Differentiable ℂ dyadicLogSchwarzEvenProduct := by
  have hraw : AnalyticOnNhd ℂ dyadicLogRawEvenProduct Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_dyadicLogRawEvenProduct
  exact differentiable_dyadicLogRawEvenProduct.mul
    (Complex.analyticOnNhd_univ_iff_differentiable.mp
      (GaloisForLFunctions.RHTower.analyticOnNhd_suzukiEntireSharp hraw))

theorem dyadicLogSchwarzEvenProduct_reflection (z : ℂ) :
    dyadicLogSchwarzEvenProduct (-3 - z) = dyadicLogSchwarzEvenProduct z := by
  rw [dyadicLogSchwarzEvenProduct, dyadicLogSchwarzEvenProduct,
    dyadicLogRawEvenProduct_reflection]
  unfold GaloisForLFunctions.RHTower.suzukiEntireSharp
  have harg : (starRingEnd ℂ) (-3 - z) = -3 - (starRingEnd ℂ) z := by
    apply Complex.ext <;> simp
  rw [harg, dyadicLogRawEvenProduct_reflection]

theorem dyadicLogSchwarzEvenProduct_conj (z : ℂ) :
    dyadicLogSchwarzEvenProduct ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (dyadicLogSchwarzEvenProduct z) := by
  have hreal := GaloisForLFunctions.RHTower.schwarzReal_mul_sharp
    dyadicLogRawEvenProduct ((starRingEnd ℂ) z)
  simpa [dyadicLogSchwarzEvenProduct,
    GaloisForLFunctions.RHTower.suzukiEntireSharp] using hreal.symm

theorem orderOneEnvelope_dyadicLogRawEvenProduct :
    OrderOneEnvelope dyadicLogRawEvenProduct := by
  exact (orderOneEnvelope_dyadicSincCascade.comp_affine 1 (3 / 2)).congr
    fun z => by simp [dyadicLogRawEvenProduct]

theorem orderOneEnvelope_suzukiEntireSharp_dyadicLogRawEvenProduct :
    OrderOneEnvelope
      (GaloisForLFunctions.RHTower.suzukiEntireSharp dyadicLogRawEvenProduct) := by
  obtain ⟨C, hC, hb⟩ := orderOneEnvelope_dyadicLogRawEvenProduct
  refine ⟨C, hC, fun z => ?_⟩
  simpa [GaloisForLFunctions.RHTower.suzukiEntireSharp, orderOneWeight] using
    hb ((starRingEnd ℂ) z)

theorem orderOneEnvelope_dyadicLogSchwarzEvenProduct :
    OrderOneEnvelope dyadicLogSchwarzEvenProduct := by
  exact (orderOneEnvelope_dyadicLogRawEvenProduct.mul
    orderOneEnvelope_suzukiEntireSharp_dyadicLogRawEvenProduct).congr fun z => rfl

theorem dyadicLogRawEvenProduct_ne_zero_of_centered_im_ne_zero
    {z : ℂ} (hz : (z + (3 / 2 : ℂ)).im ≠ 0) :
    dyadicLogRawEvenProduct z ≠ 0 := by
  exact dyadicSincCascade_ne_zero_of_im_ne_zero hz

theorem dyadicLogSchwarzEvenProduct_nonrealInteriorResponsePoint_ne_zero :
    dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ≠ 0 := by
  apply mul_ne_zero
  · apply dyadicLogRawEvenProduct_ne_zero_of_centered_im_ne_zero
    norm_num [nonrealInteriorResponsePoint]
  · unfold GaloisForLFunctions.RHTower.suzukiEntireSharp
    apply (map_ne_zero (starRingEnd ℂ)).2
    apply dyadicLogRawEvenProduct_ne_zero_of_centered_im_ne_zero
    have ha : nonrealInteriorResponsePoint.im ≠ 0 := by
      norm_num [nonrealInteriorResponsePoint]
    simpa using neg_ne_zero.mpr ha

/-- Target for the FE-even real quadratic after insertion of the dyadic divisor. -/
def dyadicLogInterpolationTarget : ℂ :=
  I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
    dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint)

def dyadicLogInterpolationPolynomial (z : ℂ) : ℂ :=
  (dyadicLogInterpolationTarget.re : ℂ) +
    ((2 * dyadicLogInterpolationTarget.im : ℝ) : ℂ) *
      ((z + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16)

theorem dyadicLogInterpolationPolynomial_nonrealInteriorResponsePoint :
    dyadicLogInterpolationPolynomial nonrealInteriorResponsePoint =
      dyadicLogInterpolationTarget := by
  have hu : (nonrealInteriorResponsePoint + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16 = I / 2 := by
    rw [nonrealInteriorResponsePoint]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [dyadicLogInterpolationPolynomial, hu]
  apply Complex.ext
  · simp
  · simp
    ring

theorem differentiable_dyadicLogInterpolationPolynomial :
    Differentiable ℂ dyadicLogInterpolationPolynomial := by
  unfold dyadicLogInterpolationPolynomial
  fun_prop

theorem dyadicLogInterpolationPolynomial_reflection (z : ℂ) :
    dyadicLogInterpolationPolynomial (-3 - z) = dyadicLogInterpolationPolynomial z := by
  unfold dyadicLogInterpolationPolynomial
  ring

theorem dyadicLogInterpolationPolynomial_conj (z : ℂ) :
    dyadicLogInterpolationPolynomial ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (dyadicLogInterpolationPolynomial z) := by
  simp only [dyadicLogInterpolationPolynomial, map_add, map_mul, map_pow,
    map_ofNat, map_div₀, Complex.conj_ofReal]

theorem orderOneEnvelope_dyadicLogInterpolationPolynomial :
    OrderOneEnvelope dyadicLogInterpolationPolynomial := by
  have hid : OrderOneEnvelope (fun z : ℂ => z) := orderOneEnvelope_id
  have hc : OrderOneEnvelope (fun z : ℂ => z + (3 / 2 : ℂ)) :=
    hid.add (orderOneEnvelope_const (3 / 2))
  have hsq : OrderOneEnvelope (fun z : ℂ => (z + (3 / 2 : ℂ)) ^ (2 : ℕ)) :=
    (hc.mul hc).congr fun z => by ring
  have hoff : OrderOneEnvelope (fun z : ℂ =>
      (z + (3 / 2 : ℂ)) ^ (2 : ℕ) + 15 / 16) :=
    hsq.add (orderOneEnvelope_const (15 / 16))
  exact ((orderOneEnvelope_const (dyadicLogInterpolationTarget.re : ℂ)).add
    ((orderOneEnvelope_const ((2 * dyadicLogInterpolationTarget.im : ℝ) : ℂ)).mul
      hoff)).congr fun z => by simp [dyadicLogInterpolationPolynomial]

def dyadicLogDensityMultiplier (z : ℂ) : ℂ :=
  dyadicLogInterpolationPolynomial z * dyadicLogSchwarzEvenProduct z

theorem differentiable_dyadicLogDensityMultiplier :
    Differentiable ℂ dyadicLogDensityMultiplier :=
  differentiable_dyadicLogInterpolationPolynomial.mul
    differentiable_dyadicLogSchwarzEvenProduct

theorem dyadicLogDensityMultiplier_reflection (z : ℂ) :
    dyadicLogDensityMultiplier (-3 - z) = dyadicLogDensityMultiplier z := by
  simp [dyadicLogDensityMultiplier, dyadicLogInterpolationPolynomial_reflection,
    dyadicLogSchwarzEvenProduct_reflection]

theorem dyadicLogDensityMultiplier_conj (z : ℂ) :
    dyadicLogDensityMultiplier ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (dyadicLogDensityMultiplier z) := by
  simp [dyadicLogDensityMultiplier, dyadicLogInterpolationPolynomial_conj,
    dyadicLogSchwarzEvenProduct_conj, map_mul]

theorem orderOneEnvelope_dyadicLogDensityMultiplier :
    OrderOneEnvelope dyadicLogDensityMultiplier := by
  exact (orderOneEnvelope_dyadicLogInterpolationPolynomial.mul
    orderOneEnvelope_dyadicLogSchwarzEvenProduct).congr fun z => rfl

theorem dyadicLogDensityMultiplier_mul_generator_target :
    dyadicLogDensityMultiplier nonrealInteriorResponsePoint *
      anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint = I := by
  rw [dyadicLogDensityMultiplier,
    dyadicLogInterpolationPolynomial_nonrealInteriorResponsePoint,
    dyadicLogInterpolationTarget]
  have hden : anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
      dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint ≠ 0 :=
    mul_ne_zero anchoredSymmetricJetNullGenerator_nonrealInteriorResponsePoint_ne_zero
      dyadicLogSchwarzEvenProduct_nonrealInteriorResponsePoint_ne_zero
  calc
    I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
        dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint) *
        dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint *
        anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint =
      I / (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
        dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint) *
        (anchoredSymmetricJetNullGenerator nonrealInteriorResponsePoint *
          dyadicLogSchwarzEvenProduct nonrealInteriorResponsePoint) := by ring
    _ = I := div_mul_cancel₀ I hden

def dyadicLogDensityGauge (z : ℂ) : ℂ :=
  completedResponsePositiveSquareGauge dyadicLogDensityMultiplier z

theorem dyadicLogDensityGauge_package :
    IsCompletedResponsePositiveSquareGauge dyadicLogDensityGauge := by
  exact completedResponsePositiveSquareGauge_package
    differentiable_dyadicLogDensityMultiplier
    dyadicLogDensityMultiplier_reflection
    dyadicLogDensityMultiplier_conj
    orderOneEnvelope_dyadicLogDensityMultiplier

theorem dyadicLogDensityGauge_nonrealInteriorResponsePoint_zero :
    dyadicLogDensityGauge nonrealInteriorResponsePoint = 0 := by
  rw [dyadicLogDensityGauge, completedResponsePositiveSquareGauge,
    dyadicLogDensityMultiplier_mul_generator_target, Complex.I_sq]
  ring

def dyadicLogDensityResponseCountermodel (z : ℂ) : ℂ :=
  completedBlackHoleJetInterpolation z * dyadicLogDensityGauge z

theorem differentiable_dyadicLogDensityResponseCountermodel :
    Differentiable ℂ dyadicLogDensityResponseCountermodel :=
  differentiable_completedBlackHoleJetInterpolation.mul dyadicLogDensityGauge_package.1

theorem dyadicLogDensityResponseCountermodel_nat (scaleLog : ℂ) (m : ℕ) :
    dyadicLogDensityResponseCountermodel (m : ℂ) =
      completedBlackHoleJetSample scaleLog m := by
  rw [dyadicLogDensityResponseCountermodel,
    dyadicLogDensityGauge_package.2.1 m, mul_one,
    completedBlackHoleJetInterpolation_nat]

theorem dyadicLogDensityResponseCountermodel_reflection (z : ℂ) :
    dyadicLogDensityResponseCountermodel (-3 - z) =
      dyadicLogDensityResponseCountermodel z := by
  rw [dyadicLogDensityResponseCountermodel, dyadicLogDensityResponseCountermodel,
    completedBlackHoleJetInterpolation_reflection,
    dyadicLogDensityGauge_package.2.2.2.2.2.1]

theorem dyadicLogDensityResponseCountermodel_conj (z : ℂ) :
    dyadicLogDensityResponseCountermodel ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (dyadicLogDensityResponseCountermodel z) := by
  rw [dyadicLogDensityResponseCountermodel, dyadicLogDensityResponseCountermodel,
    completedBlackHoleJetInterpolation_conj,
    dyadicLogDensityGauge_package.2.2.2.2.2.2.1, map_mul]

theorem orderOneEnvelope_dyadicLogDensityResponseCountermodel :
    OrderOneEnvelope dyadicLogDensityResponseCountermodel := by
  exact (orderOneEnvelope_completedBlackHoleJetInterpolation.mul
    dyadicLogDensityGauge_package.2.2.2.2.2.2.2.1).congr fun z => rfl

theorem dyadicLogDensityResponseCountermodel_real_positiveMultiple (σ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ dyadicLogDensityResponseCountermodel (σ : ℂ) =
      (r : ℂ) * completedBlackHoleJetInterpolation (σ : ℂ) := by
  obtain ⟨r, hr, hG⟩ := dyadicLogDensityGauge_package.2.2.2.2.2.2.2.2 σ
  refine ⟨r, hr, ?_⟩
  rw [dyadicLogDensityResponseCountermodel, hG]
  ring

theorem dyadicLogDensityResponseCountermodel_real_ne_zero (σ : ℝ) :
    dyadicLogDensityResponseCountermodel (σ : ℂ) ≠ 0 := by
  obtain ⟨r, hr, hF⟩ := dyadicLogDensityResponseCountermodel_real_positiveMultiple σ
  rw [hF]
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt hr
  · rw [completedBlackHoleJetInterpolation]
    convert xi_ne_zero_of_ofReal (σ + 2) using 1
    push_cast
    ring

theorem dyadicLogDensityResponseCountermodel_realAxis_package (scaleLog : ℂ) :
    IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog
      dyadicLogDensityResponseCountermodel := by
  exact ⟨⟨differentiable_dyadicLogDensityResponseCountermodel,
      dyadicLogDensityResponseCountermodel_nat scaleLog,
      dyadicLogDensityResponseCountermodel_reflection,
      dyadicLogDensityResponseCountermodel_conj,
      orderOneEnvelope_dyadicLogDensityResponseCountermodel⟩,
    by rw [dyadicLogDensityResponseCountermodel,
      dyadicLogDensityGauge_package.2.2.1, mul_one],
    by rw [dyadicLogDensityResponseCountermodel,
      dyadicLogDensityGauge_package.2.2.2.1, mul_one],
    by rw [dyadicLogDensityResponseCountermodel,
      dyadicLogDensityGauge_package.2.2.2.2.1, mul_one],
    dyadicLogDensityResponseCountermodel_real_ne_zero,
    dyadicLogDensityResponseCountermodel_real_positiveMultiple⟩

/-! ## Logarithmic-density contact ladder -/

/-- Odd-multiple stratum: centered node `2^j(2n+1)`, shifted to response coordinate. -/
def dyadicLogPhysicalNode (j n : ℕ) : ℂ :=
  dyadicSincNode j (2 * n) - (3 / 2 : ℂ)

theorem analyticOrderAt_dyadicLogRawEvenProduct_ge (j n : ℕ) :
    ((2 ^ j : ℕ) : ℕ∞) ≤
      analyticOrderAt dyadicLogRawEvenProduct (dyadicLogPhysicalNode j n) := by
  let m : ℂ := dyadicLogPhysicalNode j n
  let w : ℂ := dyadicSincNode j (2 * n)
  have hmw : m + (3 / 2 : ℂ) = w := by
    dsimp [m, w, dyadicLogPhysicalNode]
    ring
  have hfinite : analyticOrderAt dyadicSincCascade w ≠ ⊤ := by
    apply GaloisForLFunctions.analyticOrderAt_ne_top_of_entire
      differentiable_dyadicSincCascade (z₁ := 0)
    · rw [dyadicSincCascade_zero]
      norm_num
  obtain ⟨ord, hord⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hcomp := analyticOrderAt_comp_affine (f := dyadicSincCascade)
    (μ := (1 : ℂ)) (ν := (3 / 2 : ℂ)) (z := m) (n := ord)
    (by norm_num)
    (by simpa [one_mul, hmw] using
      analyticOnNhd_dyadicSincCascade w (Set.mem_univ w))
    (by simpa [one_mul, hmw] using hord.symm)
  have hbase := analyticOrderAt_dyadicSincCascade_ge j (2 * n)
  rw [← hord] at hbase
  change ((2 ^ j : ℕ) : ℕ∞) ≤ analyticOrderAt
    (fun z : ℂ => dyadicSincCascade (z + (3 / 2 : ℂ))) m
  have hout := hbase.trans_eq hcomp.symm
  simpa only [one_mul] using hout

theorem analyticOrderAt_dyadicLogSchwarzEvenProduct_ge (j n : ℕ) :
    ((2 ^ j : ℕ) : ℕ∞) ≤
      analyticOrderAt dyadicLogSchwarzEvenProduct (dyadicLogPhysicalNode j n) := by
  let m : ℂ := dyadicLogPhysicalNode j n
  have hraw : AnalyticAt ℂ dyadicLogRawEvenProduct m :=
    differentiable_dyadicLogRawEvenProduct.analyticAt m
  have hsharp : AnalyticAt ℂ
      (GaloisForLFunctions.RHTower.suzukiEntireSharp dyadicLogRawEvenProduct) m :=
    (GaloisForLFunctions.RHTower.analyticOnNhd_suzukiEntireSharp
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        differentiable_dyadicLogRawEvenProduct)) m (Set.mem_univ m)
  change ((2 ^ j : ℕ) : ℕ∞) ≤ analyticOrderAt
    (fun z => dyadicLogRawEvenProduct z *
      GaloisForLFunctions.RHTower.suzukiEntireSharp dyadicLogRawEvenProduct z) m
  have hfun : (fun z => dyadicLogRawEvenProduct z *
      GaloisForLFunctions.RHTower.suzukiEntireSharp dyadicLogRawEvenProduct z) =
      dyadicLogRawEvenProduct *
        GaloisForLFunctions.RHTower.suzukiEntireSharp dyadicLogRawEvenProduct := rfl
  rw [hfun, analyticOrderAt_mul hraw hsharp]
  exact (analyticOrderAt_dyadicLogRawEvenProduct_ge j n).trans
    (le_add_right (le_refl (analyticOrderAt dyadicLogRawEvenProduct m)))

theorem dyadicLogSchwarzEvenProduct_iteratedDeriv_zero
    (j n r : ℕ) (hr : r < 2 ^ j) :
    iteratedDeriv r dyadicLogSchwarzEvenProduct (dyadicLogPhysicalNode j n) = 0 := by
  let m : ℂ := dyadicLogPhysicalNode j n
  have hfinite : analyticOrderAt dyadicLogSchwarzEvenProduct m ≠ ⊤ := by
    apply GaloisForLFunctions.analyticOrderAt_ne_top_of_entire
      differentiable_dyadicLogSchwarzEvenProduct
      (z₁ := nonrealInteriorResponsePoint)
    exact dyadicLogSchwarzEvenProduct_nonrealInteriorResponsePoint_ne_zero
  obtain ⟨ord, hord⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hlower := analyticOrderAt_dyadicLogSchwarzEvenProduct_ge j n
  change ((2 ^ j : ℕ) : ℕ∞) ≤ analyticOrderAt dyadicLogSchwarzEvenProduct m at hlower
  rw [← hord] at hlower
  have hnat : 2 ^ j ≤ ord := by exact_mod_cast hlower
  exact iteratedDeriv_eq_zero_before_analyticOrderAt_eq
    differentiable_dyadicLogSchwarzEvenProduct hord.symm (lt_of_lt_of_le hr hnat)

theorem dyadicLogSchwarzEvenProduct_sq_iteratedDeriv_zero
    (j n r : ℕ) (hr : r < 2 * 2 ^ j) :
    iteratedDeriv r (fun z => dyadicLogSchwarzEvenProduct z ^ (2 : ℕ))
      (dyadicLogPhysicalNode j n) = 0 := by
  let m : ℂ := dyadicLogPhysicalNode j n
  have hQzero : ∀ k < 2 ^ j,
      iteratedDeriv k dyadicLogSchwarzEvenProduct m = 0 := by
    intro k hk
    exact dyadicLogSchwarzEvenProduct_iteratedDeriv_zero j n k hk
  have hmul : iteratedDeriv r
      (fun z => dyadicLogSchwarzEvenProduct z * dyadicLogSchwarzEvenProduct z) m = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      differentiable_dyadicLogSchwarzEvenProduct.contDiff.contDiffAt
      differentiable_dyadicLogSchwarzEvenProduct.contDiff.contDiffAt
      (m := 2 ^ j) (n := 2 ^ j) hQzero hQzero ?_
    simpa [two_mul] using hr
  simpa [m, pow_two] using hmul

theorem dyadicLogDensityResponseCountermodel_iteratedDeriv
    (j n r : ℕ) (hr : r < 2 ^ j) :
    iteratedDeriv r dyadicLogDensityResponseCountermodel (dyadicLogPhysicalNode j n) =
      iteratedDeriv r completedBlackHoleJetInterpolation (dyadicLogPhysicalNode j n) := by
  let H : ℂ → ℂ := fun z =>
    completedBlackHoleJetInterpolation z *
      (dyadicLogInterpolationPolynomial z * anchoredSymmetricJetNullGenerator z) ^ (2 : ℕ)
  have hH : Differentiable ℂ H := by
    dsimp [H]
    exact differentiable_completedBlackHoleJetInterpolation.mul
      ((differentiable_dyadicLogInterpolationPolynomial.mul
        differentiable_anchoredSymmetricJetNullGenerator).pow 2)
  have hQsq : Differentiable ℂ (fun z => dyadicLogSchwarzEvenProduct z ^ (2 : ℕ)) :=
    differentiable_dyadicLogSchwarzEvenProduct.pow 2
  have hprod : Differentiable ℂ
      (fun z => H z * dyadicLogSchwarzEvenProduct z ^ (2 : ℕ)) := hH.mul hQsq
  have hzero : iteratedDeriv r
      (fun z => H z * dyadicLogSchwarzEvenProduct z ^ (2 : ℕ))
        (dyadicLogPhysicalNode j n) = 0 := by
    refine complex_iteratedDeriv_mul_eq_zero_before_add_order
      hH.contDiff.contDiffAt hQsq.contDiff.contDiffAt
      (m := 0) (n := 2 * 2 ^ j) (fun k hk => by omega)
      (fun k hk => dyadicLogSchwarzEvenProduct_sq_iteratedDeriv_zero j n k hk)
      (by omega)
  have hcounter : dyadicLogDensityResponseCountermodel = fun z =>
      completedBlackHoleJetInterpolation z +
        H z * dyadicLogSchwarzEvenProduct z ^ (2 : ℕ) := by
    funext z
    rw [dyadicLogDensityResponseCountermodel, dyadicLogDensityGauge,
      completedResponsePositiveSquareGauge, dyadicLogDensityMultiplier]
    dsimp [H]
    ring
  rw [hcounter]
  have hsum : (fun z => completedBlackHoleJetInterpolation z +
      H z * dyadicLogSchwarzEvenProduct z ^ (2 : ℕ)) =
      completedBlackHoleJetInterpolation +
        (fun z => H z * dyadicLogSchwarzEvenProduct z ^ (2 : ℕ)) := rfl
  rw [hsum, iteratedDeriv_add
    differentiable_completedBlackHoleJetInterpolation.contDiff.contDiffAt
    hprod.contDiff.contDiffAt, hzero, add_zero]

/-- Prior completed package plus the full dyadic logarithmic-density jet ladder. -/
def IsDyadicLogDensityRealAxisAnchoredCompletedBlackHoleJetPackage
    (scaleLog : ℂ) (F : ℂ → ℂ) : Prop :=
  IsRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog F ∧
    ∀ (j n r : ℕ), r < 2 ^ j →
      iteratedDeriv r F (dyadicLogPhysicalNode j n) =
        iteratedDeriv r completedBlackHoleJetInterpolation (dyadicLogPhysicalNode j n)

theorem dyadicLogDensityResponseCountermodel_package (scaleLog : ℂ) :
    IsDyadicLogDensityRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog
      dyadicLogDensityResponseCountermodel := by
  exact ⟨dyadicLogDensityResponseCountermodel_realAxis_package scaleLog,
    dyadicLogDensityResponseCountermodel_iteratedDeriv⟩

theorem dyadicLogDensityResponseCountermodel_nonrealInteriorResponsePoint_zero :
    dyadicLogDensityResponseCountermodel nonrealInteriorResponsePoint = 0 := by
  rw [dyadicLogDensityResponseCountermodel,
    dyadicLogDensityGauge_nonrealInteriorResponsePoint_zero, mul_zero]

theorem dyadicLogDensityResponseCountermodel_ne_canonical :
    dyadicLogDensityResponseCountermodel ≠ completedBlackHoleJetInterpolation := by
  have hXne : completedBlackHoleJetInterpolation ≠ 0 := by
    intro hzero
    have hz := congrFun hzero 0
    exact (xi_ne_zero_of_ofReal 2)
      (by simpa [completedBlackHoleJetInterpolation] using hz)
  have hGsubd : Differentiable ℂ (fun z => dyadicLogDensityGauge z - 1) :=
    dyadicLogDensityGauge_package.1.sub (differentiable_const 1)
  have hGsubne : (fun z => dyadicLogDensityGauge z - 1) ≠ 0 := by
    intro hzero
    have hz := congrFun hzero nonrealInteriorResponsePoint
    rw [dyadicLogDensityGauge_nonrealInteriorResponsePoint_zero] at hz
    norm_num at hz
  have hprodne := differentiable_mul_ne_zero
    differentiable_completedBlackHoleJetInterpolation hGsubd hXne hGsubne
  intro hcanonical
  apply hprodne
  funext z
  have hz := congrFun hcanonical z
  rw [dyadicLogDensityResponseCountermodel] at hz
  change completedBlackHoleJetInterpolation z * (dyadicLogDensityGauge z - 1) = 0
  linear_combination hz

/-- Every dyadic window has the exact `R log R` jet budget used by the countermodel. -/
theorem dyadicLogDensityResponseCountermodel_budget (K : ℕ) :
    dyadicLogJetBudget K = K * 2 ^ (K - 1) :=
  dyadicLogJetBudget_eq K

/-- Disjoint odd-multiple strata below the dyadic window `2^K`. -/
abbrev DyadicLogWindowIndex (K : ℕ) :=
  Σ j : Fin K, Fin (2 ^ (K - (j + 1)))

def dyadicLogWindowNode {K : ℕ} (q : DyadicLogWindowIndex K) : ℕ :=
  2 ^ (q.1 : ℕ) * (2 * (q.2 : ℕ) + 1)

def dyadicLogWindowWeight {K : ℕ} (q : DyadicLogWindowIndex K) : ℕ :=
  2 ^ (q.1 : ℕ)

private theorem padicValNat_two_pow_mul_odd (j n : ℕ) :
    padicValNat 2 (2 ^ j * (2 * n + 1)) = j := by
  have hpow : 2 ^ j ≠ 0 := pow_ne_zero _ (by omega)
  have hoddpos : 2 * n + 1 ≠ 0 := by omega
  have hnodd : ¬2 ∣ 2 * n + 1 := by
    intro h
    obtain ⟨k, hk⟩ := h
    omega
  rw [padicValNat.mul hpow hoddpos, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hnodd, add_zero]

/-- Odd-multiple strata are genuinely disjoint; the budget never double-counts a node. -/
theorem dyadicLogWindowNode_injective (K : ℕ) :
    Function.Injective (@dyadicLogWindowNode K) := by
  intro a b h
  have hv := congrArg (padicValNat 2) h
  simp only [dyadicLogWindowNode] at hv
  rw [padicValNat_two_pow_mul_odd, padicValNat_two_pow_mul_odd] at hv
  cases a with
  | mk ja na =>
    cases b with
    | mk jb nb =>
      dsimp at hv h ⊢
      have hj : ja = jb := Fin.ext hv
      subst jb
      have hodd : 2 * (na : ℕ) + 1 = 2 * (nb : ℕ) + 1 := by
        exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) _) h
      have hn : na = nb := Fin.ext (by omega)
      cases hn
      rfl

theorem dyadicLogWindowNode_le_two_pow {K : ℕ} (q : DyadicLogWindowIndex K) :
    dyadicLogWindowNode q ≤ 2 ^ K := by
  rcases q with ⟨j, n⟩
  have hj : (j : ℕ) < K := j.isLt
  have hn : (n : ℕ) < 2 ^ (K - ((j : ℕ) + 1)) := n.isLt
  have hodd : 2 * (n : ℕ) + 1 < 2 * 2 ^ (K - ((j : ℕ) + 1)) := by
    omega
  have hexp : K - ((j : ℕ) + 1) + 1 = K - (j : ℕ) := by omega
  have hodd' : 2 * (n : ℕ) + 1 < 2 ^ (K - (j : ℕ)) := by
    rw [← hexp, pow_succ]
    simpa [mul_comm] using hodd
  change 2 ^ (j : ℕ) * (2 * (n : ℕ) + 1) ≤ 2 ^ K
  have hmul : 2 ^ (j : ℕ) * (2 * (n : ℕ) + 1) <
      2 ^ (j : ℕ) * 2 ^ (K - (j : ℕ)) := by
    exact Nat.mul_lt_mul_of_pos_left hodd' (pow_pos (by omega) _)
  calc
    2 ^ (j : ℕ) * (2 * (n : ℕ) + 1) ≤
        2 ^ (j : ℕ) * 2 ^ (K - (j : ℕ)) := hmul.le
    _ = 2 ^ K := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ K := le_rfl

/-- Exact total weight of the disjoint dyadic window. -/
theorem sum_dyadicLogWindowWeight_eq (K : ℕ) :
    ∑ q : DyadicLogWindowIndex K, dyadicLogWindowWeight q =
      dyadicLogJetBudget K := by
  rw [Fintype.sum_sigma]
  simp_rw [dyadicLogWindowWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hsum := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => 2 ^ (K - (j + 1)) * 2 ^ j) K
  simpa [dyadicLogJetBudget] using hsum

theorem sum_dyadicLogWindowWeight_eq_logBudget (K : ℕ) :
    ∑ q : DyadicLogWindowIndex K, dyadicLogWindowWeight q =
      K * 2 ^ (K - 1) := by
  rw [sum_dyadicLogWindowWeight_eq, dyadicLogJetBudget_eq]

/--
**Logarithmic-density FZZ route kill.**  One fixed order-one completed response has contact depth
`2^j` on every odd-multiple stratum `2^j(2n+1)`.  The disjoint dyadic budget below radius `2^K`
is `K·2^(K-1) = Θ(R log R)`, yet the response retains an interior off-critical zero.  Thus every
local cumulative repair specified only by membership in the critical `Θ(R log R)` density class is
insufficient.  A survivor must impose a sharper type-normalized density constant, force a
supercritical/identity-theorem density, use off-lattice or nonlocal source data, or leave the entire
order-one category.
-/
theorem completed_response_dyadicLogDensity_route_noGo (scaleLog : ℂ) :
    ∃ F : ℂ → ℂ, ∃ z : ℂ,
      IsDyadicLogDensityRealAxisAnchoredCompletedBlackHoleJetPackage scaleLog F ∧
      (∀ K : ℕ, dyadicLogJetBudget K = K * 2 ^ (K - 1)) ∧
      0 < (z + 2).re ∧ (z + 2).re < 1 ∧
      (z + 2).re ≠ 1 / 2 ∧ (z + 2).im ≠ 0 ∧
      F z = 0 ∧ F ≠ completedBlackHoleJetInterpolation := by
  refine ⟨dyadicLogDensityResponseCountermodel, nonrealInteriorResponsePoint,
    dyadicLogDensityResponseCountermodel_package scaleLog,
    dyadicLogDensityResponseCountermodel_budget, ?_, ?_, ?_, ?_,
    dyadicLogDensityResponseCountermodel_nonrealInteriorResponsePoint_zero,
    dyadicLogDensityResponseCountermodel_ne_canonical⟩
  all_goals norm_num [nonrealInteriorResponsePoint]

end RHTower
