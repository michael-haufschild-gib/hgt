import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne
import GaloisForLFunctions.HTGeometry.MultiIndexGeometricTail
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaProduct

/-!
# The zero-nome degeneration of the multiple elliptic Gamma product

When every nome is at most `t ≤ 1/2`, the backward product collapses to its zero multi-index factor
`1 - x` and the forward product collapses to `1`, both with an error linear in `t`.

The two ingredients are the multi-index tail bound — every nonzero multi-index carries at least one
factor of `t` — and the estimate that a product of factors near one is near one, applied with the
zero multi-index as the distinguished factor.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- On the unit interval the exponential is at most `1 + 2y`. -/
theorem exp_sub_one_le_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y - 1 ≤ 2 * y := by
  have habs : |y| ≤ 1 := by
    rw [abs_of_nonneg hy0]
    exact hy1
  have hb := Real.exp_bound habs (n := 1) (by norm_num)
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one, Nat.succ_eq_add_one] at hb
  have hle : Real.exp y - 1 ≤ |Real.exp y - 1| := le_abs_self _
  rw [abs_of_nonneg hy0] at hb
  norm_num at hb
  linarith

omit [DecidableEq ι] in
/-- The multi-index mass of the backward arguments beyond the zero index. -/
theorem tsum_backwardArgument_tail_le {τ : ι → ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hq : ∀ i, ‖ellipticNome (τ i)‖ ≤ t) (z : ℂ) :
    ∑' n : ι → ℕ, (if n = 0 then 0
        else ‖multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
          (multipleEllipticGammaCoordinate z) n‖)
      ≤ (2 * multiIndexHalfSum ι) * ‖multipleEllipticGammaCoordinate z‖ * t := by
  classical
  have hpnn : ∀ i, 0 ≤ ‖ellipticNome (τ i)‖ := fun i => norm_nonneg _
  have hnorm : ∀ n : ι → ℕ,
      (if n = 0 then 0
        else ‖multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
          (multipleEllipticGammaCoordinate z) n‖)
      = (if n = 0 then 0 else ∏ i : ι, ‖ellipticNome (τ i)‖ ^ n i)
        * ‖multipleEllipticGammaCoordinate z‖ := by
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, zero_mul]
    · rw [if_neg hn, if_neg hn, multipleEllipticGammaBackwardArgument, norm_mul, norm_prod]
      simp only [norm_pow]
  have hsumIte : Summable (fun n : ι → ℕ =>
      (if n = 0 then 0 else ∏ i : ι, ‖ellipticNome (τ i)‖ ^ n i)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_multiIndexMonomial hpnn fun i => lt_of_le_of_lt (le_trans (hq i) ht) (by norm_num))
    · by_cases h : n = 0
      · rw [if_pos h]
      · rw [if_neg h]
        exact Finset.prod_nonneg fun i _ => pow_nonneg (hpnn i) _
    · by_cases h : n = 0
      · rw [if_pos h]
        exact Finset.prod_nonneg fun i _ => pow_nonneg (hpnn i) _
      · rw [if_neg h]
  have hval : ∑' n : ι → ℕ, (if n = 0 then 0
      else ‖multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n‖)
      = (∑' n : ι → ℕ, (if n = 0 then 0 else ∏ i : ι, ‖ellipticNome (τ i)‖ ^ n i))
        * ‖multipleEllipticGammaCoordinate z‖ := by
    rw [← tsum_mul_right]
    exact tsum_congr hnorm
  rw [hval]
  have htail := tsum_multiIndex_tail_le (a := fun i => ‖ellipticNome (τ i)‖) hpnn hq ht0 ht
  have hxnn : (0 : ℝ) ≤ ‖multipleEllipticGammaCoordinate z‖ := norm_nonneg _
  nlinarith

omit [DecidableEq ι] in
/-- **The backward product degenerates to its zero multi-index factor.** -/
theorem norm_backwardProduct_sub_le {τ : ι → ℂ} {t : ℝ} (hτ : ∀ i, 0 < (τ i).im)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hq : ∀ i, ‖ellipticNome (τ i)‖ ≤ t) (z : ℂ)
    (hmass : (2 * multiIndexHalfSum ι) * ‖multipleEllipticGammaCoordinate z‖ * t ≤ 1) :
    ‖multipleEllipticGammaBackwardProduct τ z - (1 - multipleEllipticGammaCoordinate z)‖
      ≤ ‖1 - multipleEllipticGammaCoordinate z‖
        * (2 * ((2 * multiIndexHalfSum ι) * ‖multipleEllipticGammaCoordinate z‖ * t)) := by
  classical
  have hpnorm : ∀ i, ‖ellipticNome (τ i)‖ < 1 := fun i => norm_ellipticNome_lt_one (hτ i)
  have hsumArg : Summable (fun n : ι → ℕ =>
      ‖multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n‖) :=
    summable_norm_multipleEllipticGammaBackwardArgument hpnorm
  have hsumv : Summable (fun n : ι → ℕ =>
      ‖-(multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n)‖) := by
    refine hsumArg.congr fun n => ?_
    rw [norm_neg]
  have hmult : Multipliable (fun n : ι → ℕ =>
      1 + -(multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n)) :=
    Complex.multipliable_one_add_of_summable (Summable.of_norm hsumv)
  have hfeq : (fun n : ι → ℕ => multipleEllipticGammaBackwardFactor τ n z)
      = fun n : ι → ℕ => 1 + -(multipleEllipticGammaBackwardArgument
        (fun i => ellipticNome (τ i)) (multipleEllipticGammaCoordinate z) n) := by
    funext n
    rw [multipleEllipticGammaBackwardFactor]
    ring
  have hP : HasProd (fun n : ι → ℕ =>
      1 + -(multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n))
      (multipleEllipticGammaBackwardProduct τ z) := by
    rw [multipleEllipticGammaBackwardProduct, hfeq]
    exact hmult.hasProd
  have hzero : 1 + -(multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
      (multipleEllipticGammaCoordinate z) (0 : ι → ℕ))
      = 1 - multipleEllipticGammaCoordinate z := by
    rw [multipleEllipticGammaBackwardArgument]
    have hone : ∏ i : ι, (ellipticNome (τ i)) ^ ((0 : ι → ℕ) i) = 1 :=
      Finset.prod_eq_one fun i _ => by rw [Pi.zero_apply, pow_zero]
    rw [hone, one_mul]
    ring
  have hSbound : ∑' n : ι → ℕ, (if n = 0 then 0
      else ‖-(multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n)‖)
      ≤ (2 * multiIndexHalfSum ι) * ‖multipleEllipticGammaCoordinate z‖ * t := by
    have hcongr : ∀ n : ι → ℕ, (if n = 0 then 0
        else ‖-(multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
          (multipleEllipticGammaCoordinate z) n)‖)
        = (if n = 0 then 0
          else ‖multipleEllipticGammaBackwardArgument (fun i => ellipticNome (τ i))
            (multipleEllipticGammaCoordinate z) n‖) := by
      intro n
      by_cases hn : n = 0
      · rw [if_pos hn, if_pos hn]
      · rw [if_neg hn, if_neg hn, norm_neg]
    rw [tsum_congr hcongr]
    exact tsum_backwardArgument_tail_le ht0 ht hq z
  have hmain := norm_hasProd_sub_single_le (0 : ι → ℕ) hP hsumv hSbound
  rw [hzero] at hmain
  refine le_trans hmain ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hS0 : (0 : ℝ) ≤ (2 * multiIndexHalfSum ι) * ‖multipleEllipticGammaCoordinate z‖ * t := by
    have hhalf := multiIndexHalfSum_nonneg (ι := ι)
    have hxnn : (0 : ℝ) ≤ ‖multipleEllipticGammaCoordinate z‖ := norm_nonneg _
    positivity
  exact exp_sub_one_le_two_mul hS0 hmass

omit [DecidableEq ι] in
/-- **The forward product degenerates to one.** -/
theorem norm_forwardProduct_sub_one_le [Nonempty ι] {τ : ι → ℂ} {t : ℝ} (hτ : ∀ i, 0 < (τ i).im)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) (hq : ∀ i, ‖ellipticNome (τ i)‖ ≤ t) (z : ℂ)
    (hmass : multiIndexHalfSum ι * (t / ‖multipleEllipticGammaCoordinate z‖) ≤ 1) :
    ‖multipleEllipticGammaForwardProduct τ z - 1‖
      ≤ 2 * (multiIndexHalfSum ι * (t / ‖multipleEllipticGammaCoordinate z‖)) := by
  classical
  have hpnn : ∀ i, 0 ≤ ‖ellipticNome (τ i)‖ := fun i => norm_nonneg _
  have hpnorm : ∀ i, ‖ellipticNome (τ i)‖ < 1 := fun i => norm_ellipticNome_lt_one (hτ i)
  have hxpos : (0 : ℝ) < ‖multipleEllipticGammaCoordinate z‖ :=
    norm_pos_iff.mpr (multipleEllipticGammaCoordinate_ne_zero z)
  have hsumArg : Summable (fun n : ι → ℕ =>
      ‖multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n‖) :=
    summable_norm_multipleEllipticGammaForwardArgument hpnorm
  have hsumw : Summable (fun n : ι → ℕ =>
      ‖-(multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n)‖) := by
    refine hsumArg.congr fun n => ?_
    rw [norm_neg]
  have hmult : Multipliable (fun n : ι → ℕ =>
      1 + -(multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n)) :=
    Complex.multipliable_one_add_of_summable (Summable.of_norm hsumw)
  have hfeq : (fun n : ι → ℕ => multipleEllipticGammaForwardFactor τ n z)
      = fun n : ι → ℕ => 1 + -(multipleEllipticGammaForwardArgument
        (fun i => ellipticNome (τ i)) (multipleEllipticGammaCoordinate z) n) := by
    funext n
    rw [multipleEllipticGammaForwardFactor]
    ring
  have hP : HasProd (fun n : ι → ℕ =>
      1 + -(multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n))
      (multipleEllipticGammaForwardProduct τ z) := by
    rw [multipleEllipticGammaForwardProduct, hfeq]
    exact hmult.hasProd
  -- the total mass of the forward arguments
  have hprodle : (∏ i : ι, ‖ellipticNome (τ i)‖) ≤ t := by
    have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    have hstep : (∏ i : ι, ‖ellipticNome (τ i)‖) ≤ ∏ _i : ι, t :=
      Finset.prod_le_prod (fun i _ => hpnn i) fun i _ => hq i
    have hpow : (∏ _i : ι, t) = t ^ Fintype.card ι := by
      rw [Finset.prod_const, Finset.card_univ]
    have hmono : t ^ Fintype.card ι ≤ t ^ (1 : ℕ) :=
      pow_le_pow_of_le_one ht0 (by linarith) hcard
    rw [hpow] at hstep
    rw [pow_one] at hmono
    linarith
  have hnormw : ∀ n : ι → ℕ,
      ‖-(multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n)‖
      = (∏ i : ι, ‖ellipticNome (τ i)‖ ^ n i)
        * ((∏ i : ι, ‖ellipticNome (τ i)‖) / ‖multipleEllipticGammaCoordinate z‖) := by
    intro n
    rw [norm_neg, multipleEllipticGammaForwardArgument, norm_div, norm_prod]
    have hsplit : ∏ i : ι, ‖ellipticNome (τ i) ^ (n i + 1)‖
        = (∏ i : ι, ‖ellipticNome (τ i)‖ ^ n i) * ∏ i : ι, ‖ellipticNome (τ i)‖ := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [norm_pow, pow_succ]
    rw [hsplit]
    ring
  have hSbound : ∑' n : ι → ℕ,
      ‖-(multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
        (multipleEllipticGammaCoordinate z) n)‖
      ≤ multiIndexHalfSum ι * (t / ‖multipleEllipticGammaCoordinate z‖) := by
    have hc0 : (0 : ℝ) ≤ (∏ i : ι, ‖ellipticNome (τ i)‖) / ‖multipleEllipticGammaCoordinate z‖ := by
      have : (0 : ℝ) ≤ ∏ i : ι, ‖ellipticNome (τ i)‖ := Finset.prod_nonneg fun i _ => hpnn i
      positivity
    have hval : ∑' n : ι → ℕ,
        ‖-(multipleEllipticGammaForwardArgument (fun i => ellipticNome (τ i))
          (multipleEllipticGammaCoordinate z) n)‖
        = (∑' n : ι → ℕ, ∏ i : ι, ‖ellipticNome (τ i)‖ ^ n i)
          * ((∏ i : ι, ‖ellipticNome (τ i)‖) / ‖multipleEllipticGammaCoordinate z‖) := by
      rw [← tsum_mul_right]
      exact tsum_congr hnormw
    rw [hval]
    have hG := tsum_multiIndexMonomial_le_half (a := fun i => ‖ellipticNome (τ i)‖) hpnn
      fun i => le_trans (hq i) ht
    have hcle : (∏ i : ι, ‖ellipticNome (τ i)‖) / ‖multipleEllipticGammaCoordinate z‖
        ≤ t / ‖multipleEllipticGammaCoordinate z‖ :=
      div_le_div_of_nonneg_right hprodle hxpos.le
    have hGnn : (0 : ℝ) ≤ multiIndexHalfSum ι := multiIndexHalfSum_nonneg
    have hsum0 : (0 : ℝ) ≤ ∑' n : ι → ℕ, ∏ i : ι, ‖ellipticNome (τ i)‖ ^ n i :=
      tsum_nonneg fun n => Finset.prod_nonneg fun i _ => pow_nonneg (hpnn i) _
    nlinarith
  have hmain := norm_tprod_one_add_sub_one_le hP hsumw hSbound
  refine le_trans hmain ?_
  have hS0 : (0 : ℝ) ≤ multiIndexHalfSum ι * (t / ‖multipleEllipticGammaCoordinate z‖) := by
    have hGnn : (0 : ℝ) ≤ multiIndexHalfSum ι := multiIndexHalfSum_nonneg
    positivity
  exact exp_sub_one_le_two_mul hS0 hmass

end

end GaloisForLFunctions.HTGeometry
