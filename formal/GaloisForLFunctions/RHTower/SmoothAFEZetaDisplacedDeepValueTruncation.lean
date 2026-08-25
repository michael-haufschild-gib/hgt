import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepCoefficientIdentification
import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError

/-!
# Quantitative truncation of the deep displaced zeta value edge

Moving the reflected contour to depth `4-d` fixes every coefficient at
`(n+1)^(-9/2)`.  The resulting value coefficients have a polynomial-height
envelope and an explicit `L^(-7/2)` tail.
-/

noncomputable section

open Complex MeasureTheory

namespace RHTower

/-- Polynomial-height, fixed-power bound for every deep value coefficient. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepCoefficient_poly_le
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4) :
    ∃ (D : ℝ) (N : ℕ), 0 ≤ D ∧
      ∀ tau : ℝ, ∀ n : ℕ,
      ‖smoothAFEZetaDisplacedDeepCoefficient d tau x n‖ ≤
        D * (1 + |tau|) ^ N *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨C, N, hC, hchi⟩ :=
    exists_norm_zetaChi_neg_seven_halves_poly_le
  let K : ℝ := x ^ (d - 4) *
    (Real.exp ((d - 4) ^ 2) / |d - 4|) * C
  let J : ℝ := ∫ v : ℝ, (1 + |v|) ^ N * Real.exp (-(v ^ 2))
  let c : ℝ := 1 / (2 * Real.pi)
  let D : ℝ := c * K * J
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hC0 : 0 ≤ C := by
    have hzero := hchi 0
    simpa using (le_trans (norm_nonneg
      (zetaChi (((-7 / 2 : ℝ) : ℂ) + (0 : ℂ) * I))) hzero)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hJ : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun v => by positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, N, hD, fun tau n => ?_⟩
  let a : ℝ := 1 + |tau|
  let b : ℝ := 1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)
  let M : ℝ := K * b * a ^ N
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
      ‖∫ v : ℝ,
          smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
            (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        ∫ v : ℝ, M * ((1 + |v|) ^ N * Real.exp (-(v ^ 2))) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hmajor
    exact Filter.Eventually.of_forall fun v => by
      calc
        ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
            (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
            K * b *
              ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2))) := by
          have h := norm_smoothAFEZetaReflectedTerm_displaced_deep_le
            hx hd hdq hchi tau n v
          dsimp only [K, b]
          convert h using 1
          · ring
        _ ≤ K * b *
            ((a * (1 + |v|)) ^ N * Real.exp (-(v ^ 2))) := by
          gcongr
          exact hshift v
        _ = M * ((1 + |v|) ^ N * Real.exp (-(v ^ 2))) := by
          dsimp only [M]
          rw [mul_pow]
          ring
  unfold smoothAFEZetaDisplacedDeepCoefficient
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc]
  calc
    c * ‖∫ v : ℝ,
        smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n
          (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ c * ∫ v : ℝ,
          M * ((1 + |v|) ^ N * Real.exp (-(v ^ 2))) :=
        mul_le_mul_of_nonneg_left hint hc
    _ = D * (1 + |tau|) ^ N *
          (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
      rw [integral_const_mul]
      dsimp only [D, M, J, a, b]
      ring

/-- Explicit `L^(-7/2)` tail of the deep reflected value series. -/
theorem exists_norm_smoothAFEZetaDisplacedDeepCoefficient_tsum_sub_sum_le
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdq : d ≤ 1 / 4) :
    ∃ (D : ℝ) (N : ℕ), 0 ≤ D ∧
      ∀ tau : ℝ, ∀ L : ℕ, 1 ≤ L →
      ‖(∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficient d tau x n) -
          ∑ n ∈ Finset.range L,
            smoothAFEZetaDisplacedDeepCoefficient d tau x n‖ ≤
        D * (1 + |tau|) ^ N *
          ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
  obtain ⟨D, N, hD, hpoint⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepCoefficient_poly_le hx hd hdq
  refine ⟨D, N, hD, fun tau L hL => ?_⟩
  let f : ℕ → ℂ := fun n =>
    smoothAFEZetaDisplacedDeepCoefficient d tau x n
  let A : ℝ := D * (1 + |tau|) ^ N
  have hnorm : Summable (fun n : ℕ => ‖f n‖) := by
    have hbase := summable_smoothAFEZetaMajorant
      (p := (9 / 2 : ℝ)) (by norm_num)
    have hmajor : Summable (fun n : ℕ =>
        A * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) := hbase.mul_left A
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      dsimp only [f, A]
      exact hpoint tau n) hmajor
  have hsum : Summable f := Summable.of_norm hnorm
  have hsplit := hsum.sum_add_tsum_nat_add L
  have heq :
      (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n =
        ∑' j : ℕ, f (j + L) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [show (fun n : ℕ =>
      smoothAFEZetaDisplacedDeepCoefficient d tau x n) = f by rfl, heq]
  have hnormTail : Summable (fun j : ℕ => ‖f (j + L)‖) :=
    (summable_nat_add_iff L).2 hnorm
  have hp : (-(9 / 2 : ℝ)) < -1 := by norm_num
  have hpow : Summable (fun j : ℕ =>
      (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ))) := by
    have hbase := Real.summable_nat_rpow.mpr hp
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff (L + 1)).2 hbase
  have hmajor : Summable (fun j : ℕ =>
      A * (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ))) :=
    hpow.mul_left A
  calc
    ‖∑' j : ℕ, f (j + L)‖ ≤
        ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hnormTail
    _ ≤ ∑' j : ℕ,
        A * (((j + L + 1 : ℕ) : ℝ)) ^ (-(9 / 2 : ℝ)) := by
      exact Summable.tsum_le_tsum (fun j => by
        have h := hpoint tau (j + L)
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
      exact mul_le_mul_of_nonneg_left
        (Sieve.tsum_tail_rpow_neg_le
          (show (1 : ℝ) < 9 / 2 by norm_num) hL)
        (by dsimp only [A]; positivity)
    _ = D * (1 + |tau|) ^ N *
        ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) := by
      dsimp only [A]
      ring_nf

end RHTower
