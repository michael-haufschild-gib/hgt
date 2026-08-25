import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepFullDerivativeIdentity
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectDerivativeTruncation

/-!
# Quantitative truncation of the deep differentiated displaced AFE

The coupled deep reflected edge gives a fixed `(n+1)^(-9/2)` derivative
majorant.  Its finite tail is therefore `O(L^(-7/2))`, with polynomial height
growth coming only from the fixed-line `chi` bound.
-/

noncomputable section

open Complex MeasureTheory

namespace RHTower

theorem smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField_eq_I_mul_height
    (d x tau : ℝ) :
    smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField d x tau =
      I * smoothAFEZetaDisplacedDirectHeightDerivativeSourceField d x tau := by
  unfold smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField
    smoothAFEZetaDisplacedDirectHeightDerivativeSourceField
  calc
    (∑' n : ℕ,
        smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n) =
        ∑' n : ℕ,
          I * smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n := by
      apply tsum_congr
      exact fun n =>
        smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm_eq_I_mul_height
          d x tau n
    _ = I * ∑' n : ℕ,
        smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n := by
      rw [tsum_mul_left]

theorem exists_norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField_sub_sum_le
    {d x : ℝ} (hdhalf : d < 1 / 2) (hx : 0 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (tau : ℝ) (L : ℕ), 1 ≤ L →
      ‖smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n‖ ≤
        C * (L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hheight⟩ :=
    exists_norm_smoothAFEZetaDisplacedDirectHeightDerivativeSourceField_sub_sum_le
      hdhalf hx
  refine ⟨C, hC, fun tau L hL => ?_⟩
  have hsource :=
    smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField_eq_I_mul_height
      d x tau
  have hsum :
      (∑ n ∈ Finset.range L,
          smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n) =
        I * ∑ n ∈ Finset.range L,
          smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x tau n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    exact
      smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm_eq_I_mul_height
        d x tau n
  rw [hsource, hsum, ← mul_sub, norm_mul, norm_I, one_mul]
  exact hheight tau L hL

/-- Polynomial-height, fixed-power bound for every deep derivative coefficient. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepCoefficientDerivative_poly_le
    {x : ℝ} (hx : 0 < x) :
    ∃ (D : ℝ) (N : ℕ), 0 ≤ D ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 2 →
      ∀ tau : ℝ, ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n‖ ≤
        D * (1 + |tau|) ^ N *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨K, N, hK, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepIntegrandDerivative_le hx
  let J : ℝ := ∫ v : ℝ, (1 + |v|) ^ N * Real.exp (-(v ^ 2))
  let c : ℝ := 1 / (2 * Real.pi)
  let D : ℝ := c * K * J
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun v => by positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, N, hD, fun d hd0 hdhalf tau n => ?_⟩
  let a : ℝ := 1 + |tau|
  let b : ℝ := 1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)
  let M : ℝ := K * b * a ^ N
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hshift : ∀ v : ℝ,
      1 + |tau| + |v| ≤ a * (1 + |v|) := by
    intro v
    dsimp only [a]
    nlinarith [abs_nonneg tau, abs_nonneg v,
      mul_nonneg (abs_nonneg tau) (abs_nonneg v)]
  have hmajor : Integrable (fun v : ℝ =>
      M * ((1 + |v|) ^ N * Real.exp (-(v ^ 2)))) :=
    (integrable_shifted_pow_mul_exp_neg_sq 1 N).const_mul M
  have hint :
      ‖∫ v : ℝ, smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v‖ ≤
        ∫ v : ℝ, M * ((1 + |v|) ^ N * Real.exp (-(v ^ 2))) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor
    exact Filter.Eventually.of_forall fun v => by
      calc
        ‖smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v‖ ≤
            K * b * ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))) := by
          simpa only [b] using hpoint d hd0 hdhalf tau n v
        _ ≤ K * b *
            ((a * (1 + |v|)) ^ N * Real.exp (-(v ^ 2))) := by
          gcongr
          exact hshift v
        _ = M * ((1 + |v|) ^ N * Real.exp (-(v ^ 2))) := by
          dsimp only [M]
          rw [mul_pow]
          ring
  unfold smoothAFEZetaDisplacedDeepCoefficientDerivative
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    c * ‖∫ v : ℝ,
        smoothAFEZetaDisplacedDeepIntegrandDerivative d x tau n v‖
      ≤ c * ∫ v : ℝ,
          M * ((1 + |v|) ^ N * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hint hc
    _ = D * (1 + |tau|) ^ N *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
      rw [integral_const_mul]
      dsimp only [D, M, J, a, b]
      ring

/-- Explicit `L^(-7/2)` tail of the deep reflected derivative series. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepCoefficientDerivative_tsum_sub_sum_le
    {x : ℝ} (hx : 0 < x) :
    ∃ (D : ℝ) (N : ℕ), 0 ≤ D ∧
      ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 2 → ∀ tau : ℝ,
      ∀ L : ℕ, 1 ≤ L →
      ‖(∑' n : ℕ,
          smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n‖ ≤
        D * (1 + |tau|) ^ N *
          ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
  obtain ⟨D, N, hD, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepCoefficientDerivative_poly_le hx
  refine ⟨D, N, hD, fun d hd0 hdhalf tau L hL => ?_⟩
  let f : ℕ → ℂ := fun n =>
    smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n
  let A : ℝ := D * (1 + |tau|) ^ N
  have hnorm : Summable (fun n : ℕ => ‖f n‖) := by
    have hbase := summable_smoothAFEZetaMajorant
      (p := (9 / 2 : ℝ)) (by norm_num)
    have hmajor : Summable (fun n : ℕ =>
        A * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) := hbase.mul_left A
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      dsimp only [f, A]
      exact hpoint d hd0 hdhalf tau n) hmajor
  have hsum : Summable f := Summable.of_norm hnorm
  have hsplit := hsum.sum_add_tsum_nat_add L
  have heq :
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n =
        ∑' j : ℕ, f (j + L) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [show (fun n : ℕ =>
      smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) = f by rfl,
    heq]
  have hnormTail : Summable (fun j : ℕ => ‖f (j + L)‖) :=
    (summable_nat_add_iff L).2 hnorm
  have hpow : Summable (fun j : ℕ =>
      (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ))) := by
    have hbase := Real.summable_nat_rpow.mpr
      (show (-(9 / 2 : ℝ)) < -1 by norm_num)
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (L + 1)).2 hbase
  have hmajor : Summable (fun j : ℕ =>
      A * (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ))) :=
    hpow.mul_left A
  calc
    ‖∑' j : ℕ, f (j + L)‖ ≤ ∑' j : ℕ, ‖f (j + L)‖ :=
      norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ,
        A * (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ)) := by
      exact Summable.tsum_le_tsum (fun j => by
        have h := hpoint d hd0 hdhalf tau (j + L)
        have hcast :
            ((j + L : ℕ) : ℝ) + 1 = ((j + L + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcast] at h
        rw [one_div, ← Real.rpow_neg (by positivity :
          (0 : ℝ) ≤ ((j + L + 1 : ℕ) : ℝ))] at h
        simpa only [f, A, Nat.cast_add, Nat.cast_one, add_assoc] using h)
        hnormTail hmajor
    _ = A * ∑' j : ℕ,
        (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ)) := by
      rw [tsum_mul_left]
    _ ≤ A * ((L : ℝ) ^ ((1 : ℝ) - 9 / 2) / ((9 : ℝ) / 2 - 1)) := by
      have hA : 0 ≤ A := by dsimp only [A]; positivity
      exact mul_le_mul_of_nonneg_left
        (Sieve.tsum_tail_rpow_neg_le
          (show (1 : ℝ) < 9 / 2 by norm_num) hL) hA
    _ = D * (1 + |tau|) ^ N *
        ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
      dsimp only [A]
      ring_nf

def smoothAFEZetaDisplacedDeepFiniteDisplacementDerivative
    (d x tau : ℝ) (L : ℕ) : ℂ :=
  -((∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n) -
    (∑ n ∈ Finset.range L,
      smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) -
    smoothAFEZetaDisplacedPoleResidueDisplacementDerivative d x tau)

/-- Finite sharp differentiated AFE: direct tail `L^(-3/4)`, reflected tail
`L^(-7/2)`, and no omitted pole term. -/
theorem exists_norm_deriv_riemannZeta_displaced_sub_deepFinite_le
    {d x : ℝ} (hd : 0 < d) (hdq : d < 1 / 4) (hx : 0 < x) :
    ∃ (C D : ℝ) (N : ℕ), 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (tau : ℝ) (L : ℕ), 1 ≤ L →
      ‖deriv riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedDeepFiniteDisplacementDerivative d x tau L‖ ≤
        C * (L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
        D * (1 + |tau|) ^ N *
          ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
  obtain ⟨C, hC, hdirect⟩ :=
    exists_norm_smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField_sub_sum_le
      (hdq.trans (by norm_num)) hx
  obtain ⟨D, N, hD, hdual⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepCoefficientDerivative_tsum_sub_sum_le hx
  refine ⟨C, D, N, hC, hD, fun tau L hL => ?_⟩
  have hderiv := deriv_riemannZeta_displaced_eq_neg_deep_smoothAFE
    hd hdq hx tau
  have hdecomp :
      deriv riemannZeta (displacedLinePt d tau) -
          smoothAFEZetaDisplacedDeepFiniteDisplacementDerivative d x tau L =
        -((smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField d x tau -
            ∑ n ∈ Finset.range L,
              smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n) -
          ((∑' n : ℕ,
              smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) -
            ∑ n ∈ Finset.range L,
              smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n)) := by
    rw [hderiv]
    unfold smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField
      smoothAFEZetaDisplacedDeepFiniteDisplacementDerivative
    ring
  rw [hdecomp, norm_neg]
  calc
    ‖(smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n) -
        ((∑' n : ℕ,
            smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n)‖ ≤
      ‖smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField d x tau -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDirectDisplacementDerivativeTerm d x tau n‖ +
        ‖(∑' n : ℕ,
            smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n‖ :=
        norm_sub_le _ _
    _ ≤ C * (L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
        D * (1 + |tau|) ^ N *
          ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
      gcongr
      · exact hdirect tau L hL
      · exact hdual d hd.le (by linarith [hdq]) tau L hL

end RHTower
