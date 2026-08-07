import GaloisForLFunctions.HTGeometry.PowerMomentRatioEscape
import GaloisForLFunctions.HTGeometry.ToeplitzPolynomialGraph
import GaloisForLFunctions.HTGeometry.WeightedBivariateMarginalLock

/-!
# Moment-ratio obstruction to regular Toeplitz realizations

If adjacent ratios of a positive moment sequence vanish, the canonical Toeplitz counterweights
cancelling successive Hankel openings cannot be uniformly bounded.  The resulting symmetric
Toeplitz matrix has neither a bounded realization on `ℓ²(ℕ)` nor an operator realization from the
canonical finite-support core into `ℓ²(ℕ)`.
-/

open Filter
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private lemma reverse_ratio_le_pow
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n) {eps : ℝ} {N : ℕ}
    (hratio : ∀ n, N ≤ n → a n / a (n + 1) ≤ eps) :
    ∀ s k : ℕ, N ≤ s → a s / a (s + k) ≤ eps ^ k := by
  intro s k hs
  induction k generalizing s with
  | zero => simp [ha s |>.ne']
  | succ k ih =>
      have hfirst := hratio s hs
      have hrest := ih (s + 1) (by omega)
      have hpos : 0 < a (s + 1) := ha _
      have hend : 0 < a (s + 1 + k) := ha _
      rw [pow_succ]
      calc
        a s / a (s + (k + 1)) =
            (a s / a (s + 1)) * (a (s + 1) / a (s + 1 + k)) := by
              rw [show s + (k + 1) = s + 1 + k by omega]
              field_simp
        _ ≤ eps * eps ^ k :=
          mul_le_mul hfirst hrest (div_nonneg hpos.le hend.le)
            (le_trans (div_pos (ha s) hpos).le hfirst)
        _ = eps ^ k * eps := by ring

private lemma sum_fin_reverse_pow_le_two_mul
    {eps : ℝ} (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 2) (n : ℕ) :
    (∑ i : Fin (n + 1), eps ^ ((n + 1) - (i : ℕ))) ≤ 2 * eps := by
  rw [show (∑ i : Fin (n + 1), eps ^ ((n + 1) - (i : ℕ))) =
      ∑ i ∈ Finset.range (n + 1), eps ^ ((n + 1) - i) from
    Fin.sum_univ_eq_sum_range (fun i : ℕ => eps ^ ((n + 1) - i)) (n + 1)]
  have hreflect := Finset.sum_range_reflect (fun i : ℕ => eps ^ (i + 1)) (n + 1)
  have hreindex :
      (∑ i ∈ Finset.range (n + 1), eps ^ ((n + 1) - i)) =
        ∑ i ∈ Finset.range (n + 1), eps ^ (i + 1) := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    congr 1
    omega
  rw [hreindex]
  calc
    (∑ i ∈ Finset.range (n + 1), eps ^ (i + 1)) =
        eps * ∑ i ∈ Finset.range (n + 1), eps ^ i := by
          simp_rw [pow_succ']
          rw [Finset.mul_sum]
    _ ≤ eps * ∑ i ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ i := by
      gcongr with i hi
    _ ≤ eps * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) heps0
    _ = 2 * eps := by ring

/-- Counterweights cancelling every Hankel opening cannot stay bounded when adjacent moment
ratios vanish. -/
theorem hankelToeplitzCounterweight_not_bounded_of_ratio_tendsto_zero
    (moment : ℕ → ℝ) (hpos : ∀ n, 0 < moment n)
    (hratio : Tendsto (fun n => moment n / moment (n + 1)) atTop (nhds 0)) :
    ¬ ∃ B : ℝ, ∀ n, |hankelToeplitzCounterweight moment n| ≤ B := by
  rintro ⟨B, hB⟩
  have hBone : 1 ≤ B := by
    simpa [hankelToeplitzCounterweight] using hB 0
  let eps : ℝ := 1 / (8 * B)
  have heps0 : 0 < eps := by dsimp [eps]; positivity
  have hepshalf : eps ≤ 1 / 2 := by
    dsimp [eps]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hevent : ∀ᶠ n : ℕ in atTop, moment n / moment (n + 1) < eps :=
    (tendsto_order.1 hratio).2 eps heps0
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let n := N
  have hopen := hankelToeplitzCounterweight_opening_cancellation moment n (hpos _).ne'
  have hratioN : ∀ j, N ≤ j → moment j / moment (j + 1) ≤ eps := by
    intro j hj
    exact (hN j hj).le
  have hterm : ∀ i : Fin (n + 1),
      moment ((n + 1) + (i : ℕ) + 2) / moment (2 * (n + 1) + 2) ≤
        eps ^ ((n + 1) - (i : ℕ)) := by
    intro i
    have hs : N ≤ (n + 1) + (i : ℕ) + 2 := by dsimp [n]; omega
    have h := reverse_ratio_le_pow hpos hratioN
      ((n + 1) + (i : ℕ) + 2) ((n + 1) - (i : ℕ)) hs
    rw [show 2 * (n + 1) + 2 =
      (n + 1) + (i : ℕ) + 2 + ((n + 1) - (i : ℕ)) by omega]
    exact h
  have hsumratio :
      (∑ i : Fin (n + 1),
        moment ((n + 1) + (i : ℕ) + 2) / moment (2 * (n + 1) + 2)) ≤ 2 * eps := by
    exact le_trans (Finset.sum_le_sum fun i _ => hterm i)
      (sum_fin_reverse_pow_le_two_mul heps0.le hepshalf n)
  have hmq : 0 < moment (2 * (n + 1) + 2) := hpos _
  have habs :
      moment (2 * (n + 1) + 2) ≤
        2 * B * ∑ i : Fin (n + 1), moment ((n + 1) + (i : ℕ) + 2) := by
    rw [← neg_eq_iff_add_eq_zero] at hopen
    calc
      moment (2 * (n + 1) + 2) = |-moment (2 * (n + 1) + 2)| := by
            rw [abs_neg, abs_of_pos hmq]
      _ =
          |2 * ∑ i : Fin (n + 1),
            hankelToeplitzCounterweight moment ((n + 1) - (i : ℕ)) *
              moment ((n + 1) + (i : ℕ) + 2)| := by
            rw [hopen]
      _ ≤ 2 * ∑ i : Fin (n + 1),
          |hankelToeplitzCounterweight moment ((n + 1) - (i : ℕ))| *
            moment ((n + 1) + (i : ℕ) + 2) := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
              gcongr
              exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
                apply Finset.sum_congr rfl
                intro i hi
                rw [abs_mul, abs_of_pos (hpos _)])
      _ ≤ 2 * ∑ i : Fin (n + 1),
          B * moment ((n + 1) + (i : ℕ) + 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2)
            exact Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (hB _) (hpos _).le
      _ = 2 * B * ∑ i : Fin (n + 1), moment ((n + 1) + (i : ℕ) + 2) := by
            rw [← Finset.mul_sum]
            ring
  have hdiv : 1 ≤ 2 * B *
      (∑ i : Fin (n + 1),
        moment ((n + 1) + (i : ℕ) + 2) / moment (2 * (n + 1) + 2)) := by
    calc
      1 = moment (2 * (n + 1) + 2) / moment (2 * (n + 1) + 2) := by
        field_simp
      _ ≤ (2 * B * ∑ i : Fin (n + 1), moment ((n + 1) + (i : ℕ) + 2)) /
          moment (2 * (n + 1) + 2) :=
        div_le_div_of_nonneg_right habs hmq.le
      _ = 2 * B *
          (∑ i : Fin (n + 1),
            moment ((n + 1) + (i : ℕ) + 2) / moment (2 * (n + 1) + 2)) := by
        rw [← Finset.sum_div]
        ring
  have : 1 ≤ 4 * B * eps :=
    le_trans hdiv (by
      calc
        2 * B * (∑ i : Fin (n + 1),
            moment ((n + 1) + (i : ℕ) + 2) / moment (2 * (n + 1) + 2)) ≤
            2 * B * (2 * eps) :=
          mul_le_mul_of_nonneg_left hsumratio (by positivity)
        _ = 4 * B * eps := by ring)
  dsimp [eps] at this
  field_simp at this
  linarith

/-- Absolute diagonal offset of a Toeplitz matrix. -/
def toeplitzOffset (i j : ℕ) : ℕ := if i ≤ j then j - i else i - j

@[simp] theorem toeplitzOffset_zero_right (i : ℕ) : toeplitzOffset i 0 = i := by
  rw [toeplitzOffset]
  split_ifs with h
  · omega
  · omega

/-- A bounded `ℓ²` realization of the symmetric Toeplitz matrix generated by `d`. -/
def HasBoundedToeplitzL2Realization (d : ℕ → ℝ) : Prop :=
  ∃ T : CoefficientL2 →L[ℂ] CoefficientL2,
    ∀ i j : ℕ, T (lp.single 2 j 1) i = (d (toeplitzOffset i j) : ℂ)

/-- A realization on the canonical finite-support core, with values in `ℓ²`. -/
def HasFiniteCoreToeplitzL2Realization (d : ℕ → ℝ) : Prop :=
  ∃ T : (ℕ →₀ ℂ) →ₗ[ℂ] CoefficientL2,
    ∀ i j : ℕ, T (Finsupp.single j 1) i = (d (toeplitzOffset i j) : ℂ)

theorem not_hasFiniteCoreToeplitzL2Realization_of_not_bounded
    {d : ℕ → ℝ} (hd : ¬ ∃ B : ℝ, ∀ n, |d n| ≤ B) :
    ¬ HasFiniteCoreToeplitzL2Realization d := by
  rintro ⟨T, hT⟩
  apply hd
  refine ⟨‖T (Finsupp.single 0 1)‖, fun n => ?_⟩
  have hcoord := lp.norm_apply_le_norm (show (2 : ENNReal) ≠ 0 by norm_num)
    (T (Finsupp.single 0 1)) n
  rw [hT n 0] at hcoord
  simpa [Complex.norm_real, Real.norm_eq_abs] using hcoord

theorem not_hasBoundedToeplitzL2Realization_of_not_bounded
    {d : ℕ → ℝ} (hd : ¬ ∃ B : ℝ, ∀ n, |d n| ≤ B) :
    ¬ HasBoundedToeplitzL2Realization d := by
  rintro ⟨T, hT⟩
  apply hd
  refine ⟨‖T‖, fun n => ?_⟩
  have hcoord := lp.norm_apply_le_norm (show (2 : ENNReal) ≠ 0 by norm_num)
    (T (lp.single 2 0 1)) n
  have hop := T.le_opNorm (lp.single 2 0 1)
  rw [hT n 0] at hcoord
  rw [lp.norm_single (show (0 : ENNReal) < 2 by norm_num), norm_one, mul_one] at hop
  have hcoord' : |d n| ≤ ‖T (lp.single 2 0 1)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hcoord
  exact hcoord'.trans hop

end

end GaloisForLFunctions.HTGeometry
