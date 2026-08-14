import GaloisForLFunctions.SelbergClass.MultipleStandardTwistDamping
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Joint holomorphy of damped multiple standard twists

This module formalizes the next analytic step behind Kaczorowski--Perelli,
*Multiple standard twists of L-functions* (2026): the exact damped Cartesian
series from equation (3.1) is jointly Fréchet-holomorphic on `ℂ^N`.

The proof derives the termwise Fréchet derivative, constructs a summable
majorant uniform on a ball around every point, and applies the Banach-space
termwise differentiation theorem. No continuation or holomorphy provider is
assumed.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

noncomputable def multipleLogLinear {N : ℕ} (n : Fin N → ℕ+) :
    (Fin N → ℂ) →L[ℂ] ℂ :=
  ∑ i, (-(Real.log ((n i : ℕ) : ℝ) : ℂ)) •
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i)

@[simp] theorem multipleLogLinear_apply {N : ℕ} (n : Fin N → ℕ+)
    (s : Fin N → ℂ) :
    multipleLogLinear n s =
      ∑ i, (-(Real.log ((n i : ℕ) : ℝ) : ℂ)) * s i := by
  simp [multipleLogLinear]

noncomputable def dampedMultipleStandardTwistExpTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) : ℂ :=
  (∏ i, a i (n i : ℕ)) * Complex.exp (multipleLogLinear n s) *
    Complex.exp
      (-multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ))

theorem hasFDerivAt_dampedMultipleStandardTwistExpTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    HasFDerivAt (fun z => dampedMultipleStandardTwistExpTerm a κ α X z n)
      (((∏ i, a i (n i : ℕ)) * Complex.exp (multipleLogLinear n s) *
          Complex.exp (-multipleTwistDampingParameter α X *
            (multipleIndexPower κ n : ℂ))) • multipleLogLinear n) s := by
  unfold dampedMultipleStandardTwistExpTerm
  have hexp : HasFDerivAt
      (fun z : Fin N → ℂ => Complex.exp (multipleLogLinear n z))
      (Complex.exp (multipleLogLinear n s) • multipleLogLinear n) s :=
    (multipleLogLinear n).hasFDerivAt.cexp
  have hcoeff := hexp.const_mul (∏ i, a i (n i : ℕ))
  have hphase := hcoeff.mul_const
    (Complex.exp (-multipleTwistDampingParameter α X *
      (multipleIndexPower κ n : ℂ)))
  simpa only [smul_smul, mul_comm] using hphase

theorem dampedMultipleStandardTwistExpTerm_eq_term {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    dampedMultipleStandardTwistExpTerm a κ α X s n =
      dampedMultipleStandardTwistTerm a κ α X s n := by
  rw [dampedMultipleStandardTwistExpTerm, dampedMultipleStandardTwistTerm]
  congr 1
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [multipleLogLinear_apply, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Complex.cpow_def_of_ne_zero (by
    have hn : (n i : ℕ) ≠ 0 := Nat.ne_of_gt (n i).property
    exact_mod_cast hn)]
  rw [← Complex.natCast_log]
  congr 1
  ring

theorem norm_multipleLogLinear_le {N : ℕ} (n : Fin N → ℕ+) :
    ‖multipleLogLinear n‖ ≤ (N : ℝ) * multipleIndexPower (fun _ => 1) n := by
  have hn_one : ∀ i, (1 : ℝ) ≤ ((n i : ℕ) : ℝ) := by
    intro i
    exact_mod_cast (n i).property
  have hprod_nonneg : 0 ≤ multipleIndexPower (fun _ => 1) n := by
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hprod_nonneg) ?_
  intro z
  rw [multipleLogLinear_apply]
  calc
    ‖∑ i, (-(Real.log ((n i : ℕ) : ℝ) : ℂ)) * z i‖
        ≤ ∑ i, ‖(-(Real.log ((n i : ℕ) : ℝ) : ℂ)) * z i‖ := norm_sum_le _ _
    _ = ∑ i, Real.log ((n i : ℕ) : ℝ) * ‖z i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (hn_one i))]
    _ ≤ ∑ i, ((n i : ℕ) : ℝ) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (Real.log_le_self (zero_le_one.trans (hn_one i)))
        (norm_le_pi_norm z i) (norm_nonneg _) (zero_le_one.trans (hn_one i))
    _ ≤ ∑ _i : Fin N, multipleIndexPower (fun _ => 1) n * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        ((n i : ℕ) : ℝ) = ∏ j ∈ {i}, ((n j : ℕ) : ℝ) := by simp
        _ ≤ ∏ j ∈ Finset.univ, ((n j : ℕ) : ℝ) :=
          Finset.prod_le_prod_of_subset_of_one_le
            (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
            (fun j _ => zero_le_one.trans (hn_one j))
            (fun j _ _ => hn_one j)
        _ = multipleIndexPower (fun _ => 1) n := by
          simp [multipleIndexPower]
    _ = ((N : ℝ) * multipleIndexPower (fun _ => 1) n) * ‖z‖ := by
      simp [mul_assoc]

noncomputable def dampedMultipleStandardTwistFDeriv {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) : (Fin N → ℂ) →L[ℂ] ℂ :=
  ((∏ i, a i (n i : ℕ)) * Complex.exp (multipleLogLinear n s) *
    Complex.exp (-multipleTwistDampingParameter α X *
      (multipleIndexPower κ n : ℂ))) • multipleLogLinear n

theorem hasFDerivAt_dampedMultipleStandardTwistExpTerm' {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    HasFDerivAt (fun z => dampedMultipleStandardTwistExpTerm a κ α X z n)
      (dampedMultipleStandardTwistFDeriv a κ α X s n) s :=
  hasFDerivAt_dampedMultipleStandardTwistExpTerm a κ α X s n

theorem norm_dampedMultipleStandardTwistExpTerm_mul_index_le_shift {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s₀ z : Fin N → ℂ) (n : Fin N → ℕ+)
    (hz : z ∈ Metric.ball s₀ 1) :
    ‖dampedMultipleStandardTwistExpTerm a κ α X z n‖ *
        multipleIndexPower (fun _ => 1) n ≤
      ‖dampedMultipleStandardTwistTerm a κ α X (fun i => s₀ i - 2) n‖ := by
  have hdist : ‖z - s₀‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hcoord : ∀ i, (s₀ i).re - 1 < (z i).re := by
    intro i
    have hcoordnorm : ‖z i - s₀ i‖ < 1 := by
      apply lt_of_le_of_lt _ hdist
      simpa only [Pi.sub_apply] using norm_le_pi_norm (z - s₀) i
    have hreabs : |(z i).re - (s₀ i).re| < 1 := by
      apply lt_of_le_of_lt _ hcoordnorm
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z i - s₀ i)
    linarith [neg_lt_of_abs_lt hreabs]
  rw [dampedMultipleStandardTwistExpTerm_eq_term]
  simp only [dampedMultipleStandardTwistTerm, norm_mul]
  calc
    ‖∏ i, a i (n i : ℕ) * ((n i : ℂ) ^ (-z i))‖ *
          ‖Complex.exp (-multipleTwistDampingParameter α X *
            (multipleIndexPower κ n : ℂ))‖ * multipleIndexPower (fun _ => 1) n
        = (‖∏ i, a i (n i : ℕ) * ((n i : ℂ) ^ (-z i))‖ *
            multipleIndexPower (fun _ => 1) n) *
          ‖Complex.exp (-multipleTwistDampingParameter α X *
            (multipleIndexPower κ n : ℂ))‖ := by ring
    _ ≤ ‖∏ i, a i (n i : ℕ) * ((n i : ℂ) ^ (-(s₀ i - 2)))‖ *
          ‖Complex.exp (-multipleTwistDampingParameter α X *
            (multipleIndexPower κ n : ℂ))‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [norm_prod, norm_prod, multipleIndexPower]
      simp only [Real.rpow_one, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod (fun i _ => mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
      intro i hi
      rw [norm_mul, norm_mul,
        Complex.norm_natCast_cpow_of_pos (n := (n i : ℕ)) (n i).property (-z i),
        Complex.norm_natCast_cpow_of_pos (n := (n i : ℕ)) (n i).property (-(s₀ i - 2))]
      have hnpos : (0 : ℝ) < ((n i : ℕ) : ℝ) := by
        exact_mod_cast (n i).property
      have hone : (1 : ℝ) ≤ ((n i : ℕ) : ℝ) := by
        exact_mod_cast (n i).property
      have hexponent : (-z i).re + 1 ≤ (-(s₀ i - 2)).re := by
        norm_num [Complex.sub_re]
        linarith [hcoord i]
      calc
        (‖a i (n i : ℕ)‖ * ((n i : ℕ) : ℝ) ^ (-z i).re) *
              ((n i : ℕ) : ℝ)
            = ‖a i (n i : ℕ)‖ *
                (((n i : ℕ) : ℝ) ^ (-z i).re * ((n i : ℕ) : ℝ) ^ (1 : ℝ)) := by
                  rw [Real.rpow_one]
                  ring
        _ = ‖a i (n i : ℕ)‖ *
              ((n i : ℕ) : ℝ) ^ ((-z i).re + 1) := by
                rw [Real.rpow_add hnpos]
        _ ≤ ‖a i (n i : ℕ)‖ *
              ((n i : ℕ) : ℝ) ^ (-(s₀ i - 2)).re := by
                exact mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow_of_exponent_le hone hexponent) (norm_nonneg _)

theorem norm_dampedMultipleStandardTwistFDeriv_le_shift {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α X : ℝ)
    (s₀ z : Fin N → ℂ) (n : Fin N → ℕ+)
    (hz : z ∈ Metric.ball s₀ 1) :
    ‖dampedMultipleStandardTwistFDeriv a κ α X z n‖ ≤
      (N : ℝ) *
        ‖dampedMultipleStandardTwistTerm a κ α X (fun i => s₀ i - 2) n‖ := by
  rw [dampedMultipleStandardTwistFDeriv, norm_smul]
  change ‖dampedMultipleStandardTwistExpTerm a κ α X z n‖ *
      ‖multipleLogLinear n‖ ≤ _
  calc
    ‖dampedMultipleStandardTwistExpTerm a κ α X z n‖ *
          ‖multipleLogLinear n‖
        ≤ ‖dampedMultipleStandardTwistExpTerm a κ α X z n‖ *
            ((N : ℝ) * multipleIndexPower (fun _ => 1) n) :=
          mul_le_mul_of_nonneg_left (norm_multipleLogLinear_le n) (norm_nonneg _)
    _ = (N : ℝ) *
          (‖dampedMultipleStandardTwistExpTerm a κ α X z n‖ *
            multipleIndexPower (fun _ => 1) n) := by ring
    _ ≤ (N : ℝ) *
          ‖dampedMultipleStandardTwistTerm a κ α X (fun i => s₀ i - 2) n‖ :=
      mul_le_mul_of_nonneg_left
        (norm_dampedMultipleStandardTwistExpTerm_mul_index_le_shift
          a κ α X s₀ z n hz) (Nat.cast_nonneg _)

/-- The damped multiple standard twist is jointly holomorphic on `ℂ^N`.
This is Fréchet differentiability over `ℂ`, not merely separate
coordinatewise holomorphy. -/
theorem differentiable_dampedMultipleStandardTwist {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℕ → ℂ) (C B κ : Fin N → ℝ)
    (ha : ∀ (i : Fin N) (n : ℕ+),
      ‖a i (n : ℕ)‖ ≤ C i * ((n : ℕ) : ℝ) ^ B i)
    (hκ : ∀ i, 0 < κ i) {α X : ℝ} (hα : 0 < α) (hX : 0 < X) :
    Differentiable ℂ (dampedMultipleStandardTwist a κ α X) := by
  intro s₀
  let shifted : Fin N → ℂ := fun i => s₀ i - 2
  let u : (Fin N → ℕ+) → ℝ := fun n =>
    (N : ℝ) * ‖dampedMultipleStandardTwistTerm a κ α X shifted n‖
  have hu : Summable u := by
    exact (summable_norm_dampedMultipleStandardTwistTerm
      hN a C B κ ha hκ hα hX shifted).mul_left (N : ℝ)
  have hf0 : Summable fun n : Fin N → ℕ+ =>
      dampedMultipleStandardTwistExpTerm a κ α X s₀ n := by
    simpa only [dampedMultipleStandardTwistExpTerm_eq_term] using
      summable_dampedMultipleStandardTwistTerm hN a C B κ ha hκ hα hX s₀
  have hderiv := hasFDerivAt_tsum_of_isPreconnected
    (s := Metric.ball s₀ 1) (x₀ := s₀) (x := s₀)
    hu Metric.isOpen_ball (convex_ball s₀ 1).isPreconnected
    (fun n z hz => hasFDerivAt_dampedMultipleStandardTwistExpTerm' a κ α X z n)
    (fun n z hz => by
      exact norm_dampedMultipleStandardTwistFDeriv_le_shift a κ α X s₀ z n hz)
    (Metric.mem_ball_self zero_lt_one) hf0 (Metric.mem_ball_self zero_lt_one)
  change DifferentiableAt ℂ
    (fun y => ∑' n : Fin N → ℕ+,
      dampedMultipleStandardTwistTerm a κ α X y n) s₀
  simpa only [dampedMultipleStandardTwistExpTerm_eq_term] using
    hderiv.differentiableAt

end GaloisForLFunctions.SelbergClass

