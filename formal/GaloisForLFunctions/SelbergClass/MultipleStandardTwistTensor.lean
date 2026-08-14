import GaloisForLFunctions.SelbergClass.MultipleStandardTwistHolomorphy
import GaloisForLFunctions.RHTower.SelbergClass.Basic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Multiple standard-twist tensor

This module formalizes Kaczorowski--Perelli (2026), equations (1.3), (3.2),
and (3.3): the exact undamped multiple twist on its initial half-space, its
absolute convergence for concrete extended Selberg-class inputs, the entire
damped approximants, and recovery of the undamped tensor as `X → ∞`.

`MultipleStandardTwistData` contains only published source data and the
weighted-degree normalization. It deliberately contains no continuation
provider.
-/

open Complex Filter Set
open scoped BigOperators Topology

namespace GaloisForLFunctions.SelbergClass

noncomputable def multipleStandardTwistPhase {N : ℕ} (κ : Fin N → ℝ)
    (α : ℝ) (n : Fin N → ℕ+) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * (α : ℂ) * I) *
    (multipleIndexPower κ n : ℂ))

theorem norm_multipleStandardTwistPhase {N : ℕ} (κ : Fin N → ℝ)
    (α : ℝ) (n : Fin N → ℕ+) :
    ‖multipleStandardTwistPhase κ α n‖ = 1 := by
  rw [multipleStandardTwistPhase, Complex.norm_exp]
  simp

noncomputable def multipleStandardTwistTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) : ℂ :=
  (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
    multipleStandardTwistPhase κ α n

noncomputable def multipleStandardTwist {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) : ℂ :=
  ∑' n : Fin N → ℕ+, multipleStandardTwistTerm a κ α s n

theorem summable_norm_pnat_dirichletTerm {a : ℕ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) :
    Summable fun n : ℕ+ => ‖a (n : ℕ) * (((n : ℕ) : ℂ) ^ (-s))‖ := by
  have hnorm : Summable fun n : ℕ => ‖LSeries.term a s n‖ := ha.norm
  have hcomp := hnorm.comp_injective (i := PNat.val) (fun _ _ h => PNat.eq h)
  apply hcomp.congr
  intro n
  change ‖LSeries.term a s (n : ℕ)‖ = _
  apply congrArg norm
  simp [LSeries.term, div_eq_mul_inv, ← Complex.cpow_neg]

theorem summable_norm_multipleStandardTwistTerm_of_lSeries {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (ha : ∀ i, LSeriesSummable (a i) (s i)) :
    Summable fun n : Fin N → ℕ+ =>
      ‖multipleStandardTwistTerm a κ α s n‖ := by
  let major : Fin N → ℕ+ → ℝ := fun i n =>
    ‖a i (n : ℕ) * (((n : ℕ) : ℂ) ^ (-s i))‖
  have hmajor_nonneg : ∀ i n, 0 ≤ major i n := fun _ _ => norm_nonneg _
  have hmajor_sum : ∀ i, Summable (major i) := fun i =>
    summable_norm_pnat_dirichletTerm (ha i)
  have hmajor : Summable fun n : Fin N → ℕ+ => ∏ i, major i (n i) :=
    summable_pi_prod_nonneg N ℕ+ major hmajor_nonneg hmajor_sum
  simpa only [multipleStandardTwistTerm, norm_mul, norm_prod,
    norm_multipleStandardTwistPhase, mul_one, major] using hmajor

theorem summable_multipleStandardTwistTerm_of_lSeries {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (ha : ∀ i, LSeriesSummable (a i) (s i)) :
    Summable fun n : Fin N → ℕ+ =>
      multipleStandardTwistTerm a κ α s n :=
  (summable_norm_multipleStandardTwistTerm_of_lSeries a κ α s ha).of_norm

theorem summable_norm_multipleStandardTwistTerm_extendedSelberg {N : ℕ}
    (F : Fin N → RHTower.ExtendedSelbergClass) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (hs : ∀ i, 1 < (s i).re) :
    Summable fun n : Fin N → ℕ+ =>
      ‖multipleStandardTwistTerm (fun i n => (F i).coeff n) κ α s n‖ :=
  summable_norm_multipleStandardTwistTerm_of_lSeries
    (fun i n => (F i).coeff n) κ α s (fun i => (F i).lSeriesSummable (s i) (hs i))

theorem ExtendedSelbergClass.exists_coeffPolynomialBound
    (F : RHTower.ExtendedSelbergClass) :
    ∃ C : ℝ, ∀ n : ℕ+,
      ‖F.coeff (n : ℕ)‖ ≤ C * ((n : ℕ) : ℝ) ^ (2 : ℝ) := by
  have hs : LSeriesSummable F.coeff (2 : ℂ) :=
    F.lSeriesSummable 2 (by norm_num)
  obtain ⟨C, hC⟩ := hs.le_const_mul_rpow
  refine ⟨C, fun n => ?_⟩
  simpa using hC (n : ℕ) (Nat.ne_of_gt n.property)

theorem extendedSelbergFamily_exists_coeffPolynomialBound {N : ℕ}
    (F : Fin N → RHTower.ExtendedSelbergClass) :
    ∃ C : Fin N → ℝ, ∀ (i : Fin N) (n : ℕ+),
      ‖(F i).coeff (n : ℕ)‖ ≤ C i * ((n : ℕ) : ℝ) ^ (2 : ℝ) := by
  choose C hC using fun i => ExtendedSelbergClass.exists_coeffPolynomialBound (F i)
  exact ⟨C, hC⟩

/-- Every finite family of concrete `S♯` carriers gives an entire damped
multiple standard twist. No separate coefficient-growth premise remains. -/
theorem differentiable_dampedMultipleStandardTwist_extendedSelberg {N : ℕ}
    (hN : 0 < N) (F : Fin N → RHTower.ExtendedSelbergClass)
    (κ : Fin N → ℝ) (hκ : ∀ i, 0 < κ i)
    {α X : ℝ} (hα : 0 < α) (hX : 0 < X) :
    Differentiable ℂ
      (dampedMultipleStandardTwist (fun i n => (F i).coeff n) κ α X) := by
  obtain ⟨C, hC⟩ := extendedSelbergFamily_exists_coeffPolynomialBound F
  exact differentiable_dampedMultipleStandardTwist hN
    (fun i n => (F i).coeff n) C (fun _ => 2) κ hC hκ hα hX

theorem tendsto_multipleTwistDampingParameter_atTop (α : ℝ) :
    Tendsto (multipleTwistDampingParameter α) atTop
      (𝓝 (2 * (Real.pi : ℂ) * (α : ℂ) * I)) := by
  have hinv : Tendsto (fun X : ℝ => (((1 / X : ℝ) : ℂ))) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.ofReal :
      Tendsto (fun X : ℝ => ((X⁻¹ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ))) using 1 <;>
      simp [one_div]
  change Tendsto
    (fun X : ℝ => 2 * (Real.pi : ℂ) * (α : ℂ) * ((((1 / X : ℝ) : ℂ)) + I))
    atTop (𝓝 (2 * (Real.pi : ℂ) * (α : ℂ) * I))
  simpa only [zero_add, mul_zero] using
    (tendsto_const_nhds.mul (hinv.add tendsto_const_nhds))

theorem tendsto_dampedMultipleStandardTwistTerm_atTop {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    Tendsto (fun X : ℝ => dampedMultipleStandardTwistTerm a κ α X s n) atTop
      (𝓝 (multipleStandardTwistTerm a κ α s n)) := by
  have hz := tendsto_multipleTwistDampingParameter_atTop α
  have hexp : Tendsto
      (fun X : ℝ => Complex.exp
        (-multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)))
      atTop
      (𝓝 (multipleStandardTwistPhase κ α n)) := by
    have harg := hz.neg.mul_const (multipleIndexPower κ n : ℂ)
    have := Complex.continuous_exp.continuousAt.tendsto.comp harg
    rw [multipleStandardTwistPhase]
    change Tendsto
      (Complex.exp ∘ fun X : ℝ =>
        -multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ))
      atTop
      (𝓝 (Complex.exp
        (-(2 * (Real.pi : ℂ) * (α : ℂ) * I) * (multipleIndexPower κ n : ℂ))))
    exact this
  simpa only [dampedMultipleStandardTwistTerm, multipleStandardTwistTerm] using
    tendsto_const_nhds.mul hexp

theorem norm_dampedMultipleStandardTwistTerm_le_undamped {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hα : 0 ≤ α) (hX : 0 < X) (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    ‖dampedMultipleStandardTwistTerm a κ α X s n‖ ≤
      ‖multipleStandardTwistTerm a κ α s n‖ := by
  rw [dampedMultipleStandardTwistTerm, multipleStandardTwistTerm,
    norm_mul, norm_mul, norm_multipleStandardTwistPhase,
    norm_exp_multipleTwistDamping, mul_one]
  have hexp : Real.exp (-(2 * Real.pi * α / X) * multipleIndexPower κ n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hpower : 0 ≤ multipleIndexPower κ n := by
      exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hrate : 0 ≤ 2 * Real.pi * α / X := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrate) hpower
  calc
    ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))‖ *
          Real.exp (-(2 * Real.pi * α / X) * multipleIndexPower κ n)
        ≤ ‖∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))‖ * 1 :=
      mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ = _ := mul_one _

theorem tendsto_dampedMultipleStandardTwist_atTop_of_lSeries {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (s : Fin N → ℂ) (ha : ∀ i, LSeriesSummable (a i) (s i)) :
    Tendsto (fun X : ℝ => dampedMultipleStandardTwist a κ α X s) atTop
      (𝓝 (multipleStandardTwist a κ α s)) := by
  have hsum := summable_norm_multipleStandardTwistTerm_of_lSeries a κ α s ha
  apply tendsto_tsum_of_dominated_convergence hsum
  · exact fun n => tendsto_dampedMultipleStandardTwistTerm_atTop a κ α s n
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX n
    exact norm_dampedMultipleStandardTwistTerm_le_undamped a κ hα hX s n

/-- Exact input datum for the Kaczorowski--Perelli multiple standard twist.
It contains only the published `S♯` inputs and normalization (1.3), never a
continuation provider. -/
structure MultipleStandardTwistData (N : ℕ) where
  two_le_card : 2 ≤ N
  factors : Fin N → RHTower.ExtendedSelbergClass
  kappa : Fin N → ℝ
  kappa_pos : ∀ i, 0 < kappa i
  degree_pos : ∀ i, 0 < (factors i).gammaData.degree
  weightedDegree : ∑ i, (factors i).gammaData.degree * kappa i = 1
  alpha : ℝ
  alpha_pos : 0 < alpha

namespace MultipleStandardTwistData

def coeff {N : ℕ} (D : MultipleStandardTwistData N) : Fin N → ℕ → ℂ :=
  fun i n => (D.factors i).coeff n

noncomputable def initial {N : ℕ} (D : MultipleStandardTwistData N)
    (s : Fin N → ℂ) : ℂ :=
  multipleStandardTwist D.coeff D.kappa D.alpha s

noncomputable def damped {N : ℕ} (D : MultipleStandardTwistData N)
    (X : ℝ) (s : Fin N → ℂ) : ℂ :=
  dampedMultipleStandardTwist D.coeff D.kappa D.alpha X s

theorem summable_norm_initialTerm {N : ℕ} (D : MultipleStandardTwistData N)
    (s : Fin N → ℂ) (hs : ∀ i, 1 < (s i).re) :
    Summable fun n : Fin N → ℕ+ =>
      ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha s n‖ :=
  summable_norm_multipleStandardTwistTerm_extendedSelberg
    D.factors D.kappa D.alpha s hs

theorem differentiable_damped {N : ℕ} (D : MultipleStandardTwistData N)
    {X : ℝ} (hX : 0 < X) : Differentiable ℂ (D.damped X) := by
  exact differentiable_dampedMultipleStandardTwist_extendedSelberg
    (lt_of_lt_of_le (by norm_num) D.two_le_card) D.factors D.kappa
    D.kappa_pos D.alpha_pos hX

theorem tendsto_damped_atTop {N : ℕ} (D : MultipleStandardTwistData N)
    (s : Fin N → ℂ) (hs : ∀ i, 1 < (s i).re) :
    Tendsto (fun X : ℝ => D.damped X s) atTop (𝓝 (D.initial s)) := by
  exact tendsto_dampedMultipleStandardTwist_atTop_of_lSeries
    D.coeff D.kappa D.alpha_pos.le s
    (fun i => (D.factors i).lSeriesSummable (s i) (hs i))

end MultipleStandardTwistData

end GaloisForLFunctions.SelbergClass

