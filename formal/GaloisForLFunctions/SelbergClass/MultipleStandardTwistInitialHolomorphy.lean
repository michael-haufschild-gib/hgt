import GaloisForLFunctions.SelbergClass.MultipleStandardTwistTensor
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Joint holomorphy on the initial multiple-twist domain

The undamped Kaczorowski--Perelli tensor is jointly Fréchet-holomorphic on
`{s : ℂ^N | ∀ ν, 1 < Re(s ν)}`. The proof works uniformly up to every local
boundary distance: logarithmic derivatives are absorbed by fractional powers,
then termwise differentiation is justified by a summable Cartesian majorant.
-/

open Complex Filter Set
open scoped BigOperators Topology

namespace GaloisForLFunctions.SelbergClass

theorem norm_multipleLogLinear_le_rpow {N : ℕ} (n : Fin N → ℕ+)
    {r : ℝ} (hr : 0 < r) :
    ‖multipleLogLinear n‖ ≤
      ((N : ℝ) / r) * multipleIndexPower (fun _ => r) n := by
  have hn_one : ∀ i, (1 : ℝ) ≤ ((n i : ℕ) : ℝ) := by
    intro i
    exact_mod_cast (n i).property
  have hprod_nonneg : 0 ≤ multipleIndexPower (fun _ => r) n := by
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hconstant_nonneg : 0 ≤ ((N : ℝ) / r) *
      multipleIndexPower (fun _ => r) n := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hconstant_nonneg ?_
  intro z
  rw [multipleLogLinear_apply]
  let P : ℝ := multipleIndexPower (fun _ => r) n
  have hcoord : ∀ i, ((n i : ℕ) : ℝ) ^ r ≤ P := by
    intro i
    calc
      ((n i : ℕ) : ℝ) ^ r =
          ∏ j ∈ {i}, ((n j : ℕ) : ℝ) ^ r := by simp
      _ ≤ ∏ j ∈ Finset.univ, ((n j : ℕ) : ℝ) ^ r :=
        Finset.prod_le_prod_of_subset_of_one_le
          (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
          (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (fun j _ _ => Real.one_le_rpow (hn_one j) hr.le)
      _ = P := rfl
  calc
    ‖∑ i, (-(Real.log ((n i : ℕ) : ℝ) : ℂ)) * z i‖
        ≤ ∑ i, ‖(-(Real.log ((n i : ℕ) : ℝ) : ℂ)) * z i‖ := norm_sum_le _ _
    _ = ∑ i, Real.log ((n i : ℕ) : ℝ) * ‖z i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (hn_one i))]
    _ ≤ ∑ i, ((((n i : ℕ) : ℝ) ^ r) / r) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (Real.log_le_rpow_div (Nat.cast_nonneg _) hr)
        (norm_le_pi_norm z i) (norm_nonneg _) (by positivity)
    _ ≤ ∑ _i : Fin N, (P / r) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hcoord i) hr.le) (norm_nonneg _)
    _ = (((N : ℝ) / r) * multipleIndexPower (fun _ => r) n) * ‖z‖ := by
      dsimp [P]
      simp
      ring

noncomputable def multipleStandardTwistExpTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) : ℂ :=
  (∏ i, a i (n i : ℕ)) * Complex.exp (multipleLogLinear n s) *
    multipleStandardTwistPhase κ α n

theorem multipleStandardTwistExpTerm_eq_term {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    multipleStandardTwistExpTerm a κ α s n =
      multipleStandardTwistTerm a κ α s n := by
  rw [multipleStandardTwistExpTerm, multipleStandardTwistTerm]
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

noncomputable def multipleStandardTwistFDeriv {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) : (Fin N → ℂ) →L[ℂ] ℂ :=
  ((∏ i, a i (n i : ℕ)) * Complex.exp (multipleLogLinear n s) *
    multipleStandardTwistPhase κ α n) • multipleLogLinear n

theorem hasFDerivAt_multipleStandardTwistExpTerm {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    HasFDerivAt (fun z => multipleStandardTwistExpTerm a κ α z n)
      (multipleStandardTwistFDeriv a κ α s n) s := by
  have hexp : HasFDerivAt
      (fun z : Fin N → ℂ => Complex.exp (multipleLogLinear n z))
      (Complex.exp (multipleLogLinear n s) • multipleLogLinear n) s :=
    (multipleLogLinear n).hasFDerivAt.cexp
  have hcoeff := hexp.const_mul (∏ i, a i (n i : ℕ))
  have hphase := hcoeff.mul_const (multipleStandardTwistPhase κ α n)
  simpa only [multipleStandardTwistExpTerm, multipleStandardTwistFDeriv,
    smul_smul, mul_comm] using hphase

theorem norm_multipleStandardTwistExpTerm_mul_index_le_shift {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s₀ z : Fin N → ℂ) (n : Fin N → ℕ+) {r : ℝ}
    (hz : z ∈ Metric.ball s₀ r) :
    ‖multipleStandardTwistExpTerm a κ α z n‖ *
        multipleIndexPower (fun _ => r) n ≤
      ‖multipleStandardTwistTerm a κ α
        (fun i => s₀ i - (2 * r : ℝ)) n‖ := by
  have hdist : ‖z - s₀‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hcoord : ∀ i, (s₀ i).re - r < (z i).re := by
    intro i
    have hcoordnorm : ‖z i - s₀ i‖ < r := by
      apply lt_of_le_of_lt _ hdist
      simpa only [Pi.sub_apply] using norm_le_pi_norm (z - s₀) i
    have hreabs : |(z i).re - (s₀ i).re| < r := by
      apply lt_of_le_of_lt _ hcoordnorm
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z i - s₀ i)
    linarith [neg_lt_of_abs_lt hreabs]
  rw [multipleStandardTwistExpTerm_eq_term]
  simp only [multipleStandardTwistTerm, norm_mul,
    norm_multipleStandardTwistPhase, mul_one]
  rw [norm_prod, norm_prod, multipleIndexPower]
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
    (fun i _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  intro i hi
  rw [norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (n := (n i : ℕ)) (n i).property (-z i),
    Complex.norm_natCast_cpow_of_pos (n := (n i : ℕ)) (n i).property
      (-(s₀ i - (2 * r : ℝ)))]
  have hnpos : (0 : ℝ) < ((n i : ℕ) : ℝ) := by
    exact_mod_cast (n i).property
  have hone : (1 : ℝ) ≤ ((n i : ℕ) : ℝ) := by
    exact_mod_cast (n i).property
  have hexponent : (-z i).re + r ≤ (-(s₀ i - (2 * r : ℝ))).re := by
    norm_num [Complex.sub_re]
    linarith [hcoord i]
  calc
    (‖a i (n i : ℕ)‖ * ((n i : ℕ) : ℝ) ^ (-z i).re) *
          ((n i : ℕ) : ℝ) ^ r
        = ‖a i (n i : ℕ)‖ *
            (((n i : ℕ) : ℝ) ^ (-z i).re * ((n i : ℕ) : ℝ) ^ r) := by ring
    _ = ‖a i (n i : ℕ)‖ *
          ((n i : ℕ) : ℝ) ^ ((-z i).re + r) := by
            rw [Real.rpow_add hnpos]
    _ ≤ ‖a i (n i : ℕ)‖ *
          ((n i : ℕ) : ℝ) ^ (-(s₀ i - (2 * r : ℝ))).re := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hone hexponent) (norm_nonneg _)

theorem norm_multipleStandardTwistFDeriv_le_shift {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s₀ z : Fin N → ℂ) (n : Fin N → ℕ+) {r : ℝ} (hr : 0 < r)
    (hz : z ∈ Metric.ball s₀ r) :
    ‖multipleStandardTwistFDeriv a κ α z n‖ ≤
      ((N : ℝ) / r) *
        ‖multipleStandardTwistTerm a κ α
          (fun i => s₀ i - (2 * r : ℝ)) n‖ := by
  rw [multipleStandardTwistFDeriv, norm_smul]
  change ‖multipleStandardTwistExpTerm a κ α z n‖ *
      ‖multipleLogLinear n‖ ≤ _
  calc
    ‖multipleStandardTwistExpTerm a κ α z n‖ * ‖multipleLogLinear n‖
        ≤ ‖multipleStandardTwistExpTerm a κ α z n‖ *
            (((N : ℝ) / r) * multipleIndexPower (fun _ => r) n) :=
      mul_le_mul_of_nonneg_left (norm_multipleLogLinear_le_rpow n hr) (norm_nonneg _)
    _ = ((N : ℝ) / r) *
          (‖multipleStandardTwistExpTerm a κ α z n‖ *
            multipleIndexPower (fun _ => r) n) := by ring
    _ ≤ ((N : ℝ) / r) *
          ‖multipleStandardTwistTerm a κ α
            (fun i => s₀ i - (2 * r : ℝ)) n‖ :=
      mul_le_mul_of_nonneg_left
        (norm_multipleStandardTwistExpTerm_mul_index_le_shift
          a κ α s₀ z n hz) (by positivity)

theorem differentiableAt_multipleStandardTwist_of_shift {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ) (s₀ : Fin N → ℂ)
    {r : ℝ} (hr : 0 < r)
    (ha : ∀ i, LSeriesSummable (a i) (s₀ i - (2 * r : ℝ))) :
    DifferentiableAt ℂ (multipleStandardTwist a κ α) s₀ := by
  let shifted : Fin N → ℂ := fun i => s₀ i - (2 * r : ℝ)
  let u : (Fin N → ℕ+) → ℝ := fun n =>
    ((N : ℝ) / r) * ‖multipleStandardTwistTerm a κ α shifted n‖
  have hu : Summable u := by
    exact (summable_norm_multipleStandardTwistTerm_of_lSeries
      a κ α shifted ha).mul_left ((N : ℝ) / r)
  have ha0 : ∀ i, LSeriesSummable (a i) (s₀ i) := by
    intro i
    apply (ha i).of_re_le_re
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hf0 : Summable fun n : Fin N → ℕ+ =>
      multipleStandardTwistExpTerm a κ α s₀ n := by
    simpa only [multipleStandardTwistExpTerm_eq_term] using
      summable_multipleStandardTwistTerm_of_lSeries a κ α s₀ ha0
  have hderiv := hasFDerivAt_tsum_of_isPreconnected
    (s := Metric.ball s₀ r) (x₀ := s₀) (x := s₀)
    hu Metric.isOpen_ball (convex_ball s₀ r).isPreconnected
    (fun n z hz => hasFDerivAt_multipleStandardTwistExpTerm a κ α z n)
    (fun n z hz => by
      exact norm_multipleStandardTwistFDeriv_le_shift a κ α s₀ z n hr hz)
    (Metric.mem_ball_self hr) hf0 (Metric.mem_ball_self hr)
  change DifferentiableAt ℂ
    (fun y => ∑' n : Fin N → ℕ+, multipleStandardTwistTerm a κ α y n) s₀
  simpa only [multipleStandardTwistExpTerm_eq_term] using hderiv.differentiableAt

def multipleStandardTwistInitialDomain (N : ℕ) : Set (Fin N → ℂ) :=
  {s | ∀ i, 1 < (s i).re}

theorem differentiableOn_multipleStandardTwist_extendedSelberg {N : ℕ}
    (hN : 0 < N) (F : Fin N → RHTower.ExtendedSelbergClass)
    (κ : Fin N → ℝ) (α : ℝ) :
    DifferentiableOn ℂ
      (multipleStandardTwist (fun i n => (F i).coeff n) κ α)
      (multipleStandardTwistInitialDomain N) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  intro s hs
  let gaps : Finset ℝ := Finset.univ.image (fun i : Fin N => (s i).re - 1)
  have hgaps_nonempty : gaps.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let m : ℝ := gaps.min' hgaps_nonempty
  have hm_pos : 0 < m := by
    have hm_mem := Finset.min'_mem gaps hgaps_nonempty
    rcases Finset.mem_image.mp hm_mem with ⟨i, hi, him⟩
    change 0 < gaps.min' hgaps_nonempty
    rw [← him]
    exact sub_pos.mpr (hs i)
  have hm_le : ∀ i, m ≤ (s i).re - 1 := by
    intro i
    exact Finset.min'_le gaps ((s i).re - 1)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let r : ℝ := m / 4
  have hr : 0 < r := by positivity
  have hshift : ∀ i, 1 < (s i - (2 * r : ℝ)).re := by
    intro i
    simp only [Complex.sub_re, Complex.ofReal_re]
    dsimp [r]
    linarith [hm_le i]
  exact (differentiableAt_multipleStandardTwist_of_shift
    (fun i n => (F i).coeff n) κ α s hr
    (fun i => (F i).lSeriesSummable _ (hshift i))).differentiableWithinAt

theorem MultipleStandardTwistData.differentiableOn_initial {N : ℕ}
    (D : MultipleStandardTwistData N) :
    DifferentiableOn ℂ D.initial (multipleStandardTwistInitialDomain N) := by
  exact differentiableOn_multipleStandardTwist_extendedSelberg
    (lt_of_lt_of_le (by norm_num) D.two_le_card) D.factors D.kappa D.alpha

end GaloisForLFunctions.SelbergClass

