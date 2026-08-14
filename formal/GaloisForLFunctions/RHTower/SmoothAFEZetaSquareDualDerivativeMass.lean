import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualTwoSidedDerivativeBound
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import GaloisForLFunctions.RHTower.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

def smoothAFEZetaSquareDualDerivativeCoefficient
    (T r t : ℝ) (n : ℕ) : ℂ :=
  ((n + 1).divisors.card : ℂ) *
    (n + 1 : ℂ) ^ (linePt t - 1) *
      deriv (fun u : ℝ =>
        smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r

theorem norm_natSucc_cpow_linePt_sub_one_dualMass
    (n : ℕ) (t : ℝ) :
    ‖(n + 1 : ℂ) ^ (linePt t - 1)‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hcast : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [hcast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1
  simp [linePt]
  ring

theorem norm_smoothAFEZetaSquareDualDerivativeCoefficient
    (T r t : ℝ) (n : ℕ) :
    ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ =
      ((n + 1).divisors.card : ℝ) *
        (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          ‖deriv (fun u : ℝ =>
            smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r‖ := by
  rw [smoothAFEZetaSquareDualDerivativeCoefficient, norm_mul, norm_mul,
    Complex.norm_natCast, norm_natSucc_cpow_linePt_sub_one_dualMass]

/-- Exact two-sided pointwise envelope for one square-dual derivative coefficient. -/
theorem exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T r t : ℝ} {n : ℕ}, 4 ≤ r → 0 < T →
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤
          ((n + 1).divisors.card : ℝ) *
            (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
              min
                (C * ((n + 1 : ℝ) * T) ^ (1 / 4 : ℝ) /
                  (r * (r ^ (1 / 4 : ℝ)) ^ 2))
                (C * (1 + r) / ((n + 1 : ℝ) * T)) := by
  obtain ⟨C, hC, hderiv⟩ :=
    exists_norm_deriv_smoothAFEZetaSquareDualWeight_le_two_sided
  refine ⟨C, hC, ?_⟩
  intro T r t n hr hT
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hY : 0 < (n + 1 : ℝ) * T := mul_pos hn hT
  rw [norm_smoothAFEZetaSquareDualDerivativeCoefficient]
  exact mul_le_mul_of_nonneg_left (hderiv hr hY)
    (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _))

private theorem dualDerivative_large_algebra
    {x C D r T : ℝ} (hx : 0 < x) :
    D * x ^ (1 / 400 : ℝ) * x ^ (-(1 / 2 : ℝ)) *
          (C * (1 + r) / (x * T)) =
      (D * C * (1 + r) / T) * x ^ (-(599 / 400 : ℝ)) := by
  simp only [div_eq_mul_inv, mul_inv]
  rw [← Real.rpow_neg_one x]
  calc
    D * x ^ (1 / 400 : ℝ) * x ^ (-(1 / 2 : ℝ)) *
          (C * (1 + r) * (x ^ (-1 : ℝ) * T⁻¹)) =
        (D * C * (1 + r) * T⁻¹) *
          ((x ^ (1 / 400 : ℝ) * x ^ (-(1 / 2 : ℝ))) * x ^ (-1 : ℝ)) := by
      ring
    _ = (D * C * (1 + r) * T⁻¹) * x ^ (-(599 / 400 : ℝ)) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      congr 1
      ring

/-- The large-scale branch plus the divisor bound produces the exact
`(n+1)^(-599/400)` coefficient envelope. -/
theorem exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_large_power :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T r t : ℝ} {n : ℕ}, 4 ≤ r → 0 < T →
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤
          (K * (1 + r) / T) *
            (n + 1 : ℝ) ^ (-(599 / 400 : ℝ)) := by
  obtain ⟨C, hC, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le
  obtain ⟨D, hD, hdivisor⟩ :=
    card_divisors_le_const_mul_rpow (show (0 : ℝ) < 1 / 400 by norm_num)
  refine ⟨D * C, mul_nonneg hD.le hC, ?_⟩
  intro T r t n hr hT
  have hx : 0 < (n + 1 : ℝ) := by positivity
  have hfactor : 0 ≤ ((n + 1).divisors.card : ℝ) *
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx.le _)
  have hlarge := (hcoefficient (T := T) (r := r) (t := t) (n := n) hr hT).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hfactor)
  calc
    ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤
        ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C * (1 + r) / ((n + 1 : ℝ) * T)) := hlarge
    _ ≤ (D * (n + 1 : ℝ) ^ (1 / 400 : ℝ)) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C * (1 + r) / ((n + 1 : ℝ) * T)) := by
      gcongr
      simpa [Nat.cast_add, Nat.cast_one] using hdivisor (n + 1) (by omega)
    _ = ((D * C) * (1 + r) / T) *
          (n + 1 : ℝ) ^ (-(599 / 400 : ℝ)) := by
      rw [dualDerivative_large_algebra hx]

private theorem dualDerivative_large_square_algebra
    {x K r T : ℝ} (hx : 0 < x) :
    ((K * (1 + r) / T) * x ^ (-(599 / 400 : ℝ))) ^ 2 =
      (K ^ 2 * (1 + r) ^ 2 / T ^ 2) *
        x ^ (-(599 / 200 : ℝ)) := by
  rw [mul_pow, ← Real.rpow_natCast
    (x ^ (-(599 / 400 : ℝ))) 2, ← Real.rpow_mul hx.le]
  ring

private theorem dualDerivative_small_algebra
    {x N C D : ℝ} (hx : 0 < x) (hN : 0 < N) :
    D * x ^ (1 / 400 : ℝ) * x ^ (-(1 / 2 : ℝ)) *
        (C * (x * N) ^ (1 / 4 : ℝ) /
          (N * (N ^ (1 / 4 : ℝ)) ^ 2)) =
      (D * C) * x ^ (-(99 / 400 : ℝ)) * N ^ (-(5 / 4 : ℝ)) := by
  have hden : N * (N ^ (1 / 4 : ℝ)) ^ 2 = N ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (N ^ (1 / 4 : ℝ)) 2,
      ← Real.rpow_mul hN.le]
    calc
      N * N ^ ((1 / 4 : ℝ) * (2 : ℝ)) =
          N ^ (1 : ℝ) * N ^ ((1 / 4 : ℝ) * (2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) + (1 / 4 : ℝ) * (2 : ℝ)) := by
        rw [Real.rpow_add hN]
      _ = N ^ (3 / 2 : ℝ) := by
        congr 1
        ring
  rw [Real.mul_rpow hx.le hN.le, hden]
  simp only [div_eq_mul_inv]
  rw [← Real.rpow_neg hN.le]
  calc
    D * x ^ (1 / 400 : ℝ) * x ^ (-(1 / 2 : ℝ)) *
          (C * (x ^ (1 / 4 : ℝ) * N ^ (1 / 4 : ℝ)) *
            N ^ (-(3 / 2 : ℝ))) =
        (D * C) *
          ((x ^ (1 / 400 : ℝ) * x ^ (-(1 / 2 : ℝ))) *
            x ^ (1 / 4 : ℝ)) *
          (N ^ (1 / 4 : ℝ) * N ^ (-(3 / 2 : ℝ))) := by
      ring
    _ = (D * C) * x ^ (-(99 / 400 : ℝ)) *
          N ^ (-(5 / 4 : ℝ)) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx,
        ← Real.rpow_add hN]
      ring_nf

/-- The small-scale branch gives the complementary
`(n+1)^(-99/400) T^(-5/4)` envelope whenever `T ≤ r`. -/
theorem exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_small_power :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T r t : ℝ} {n : ℕ}, 4 ≤ r → 0 < T → T ≤ r →
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤
          K * (n + 1 : ℝ) ^ (-(99 / 400 : ℝ)) *
            T ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨C, hC, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le
  obtain ⟨D, hD, hdivisor⟩ :=
    card_divisors_le_const_mul_rpow (show (0 : ℝ) < 1 / 400 by norm_num)
  refine ⟨D * C, mul_nonneg hD.le hC, ?_⟩
  intro T r t n hr hT hTr
  have hx : 0 < (n + 1 : ℝ) := by positivity
  have hquarter : T ^ (1 / 4 : ℝ) ≤ r ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hT.le hTr (by norm_num)
  have hqpow : (T ^ (1 / 4 : ℝ)) ^ 2 ≤
      (r ^ (1 / 4 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hT.le _) hquarter 2
  have hden : T * (T ^ (1 / 4 : ℝ)) ^ 2 ≤
      r * (r ^ (1 / 4 : ℝ)) ^ 2 :=
    mul_le_mul hTr hqpow (sq_nonneg _) (by linarith)
  have hnum : 0 ≤ C * ((n + 1 : ℝ) * T) ^ (1 / 4 : ℝ) := by
    positivity
  have hsmallReplace :
      C * ((n + 1 : ℝ) * T) ^ (1 / 4 : ℝ) /
          (r * (r ^ (1 / 4 : ℝ)) ^ 2) ≤
        C * ((n + 1 : ℝ) * T) ^ (1 / 4 : ℝ) /
          (T * (T ^ (1 / 4 : ℝ)) ^ 2) :=
    div_le_div_of_nonneg_left hnum (by positivity) hden
  have hfactor : 0 ≤ ((n + 1).divisors.card : ℝ) *
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hsmall :=
    (hcoefficient (T := T) (r := r) (t := t) (n := n) hr hT).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hfactor)
  calc
    ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ≤
        ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C * ((n + 1 : ℝ) * T) ^ (1 / 4 : ℝ) /
              (r * (r ^ (1 / 4 : ℝ)) ^ 2)) := hsmall
    _ ≤ ((n + 1).divisors.card : ℝ) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C * ((n + 1 : ℝ) * T) ^ (1 / 4 : ℝ) /
              (T * (T ^ (1 / 4 : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsmallReplace hfactor
    _ ≤ (D * (n + 1 : ℝ) ^ (1 / 400 : ℝ)) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (C * ((n + 1 : ℝ) * T) ^ (1 / 4 : ℝ) /
              (T * (T ^ (1 / 4 : ℝ)) ^ 2)) := by
      gcongr
      simpa [Nat.cast_add, Nat.cast_one] using hdivisor (n + 1) (by omega)
    _ = (D * C) * (n + 1 : ℝ) ^ (-(99 / 400 : ℝ)) *
          T ^ (-(5 / 4 : ℝ)) :=
      dualDerivative_small_algebra hx hT

private theorem dualDerivative_small_square_algebra
    {x T K : ℝ} (hx : 0 < x) (hT : 0 < T) :
    (K * x ^ (-(99 / 400 : ℝ)) * T ^ (-(5 / 4 : ℝ))) ^ 2 =
      K ^ 2 * x ^ (-(99 / 200 : ℝ)) * T ^ (-(5 / 2 : ℝ)) := by
  rw [mul_pow, mul_pow,
    ← Real.rpow_natCast (x ^ (-(99 / 400 : ℝ))) 2,
    ← Real.rpow_natCast (T ^ (-(5 / 4 : ℝ))) 2,
    ← Real.rpow_mul hx.le, ← Real.rpow_mul hT.le]
  ring_nf

/-- Squared small-scale envelope. -/
theorem exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_small_power :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T r t : ℝ} {n : ℕ}, 4 ≤ r → 0 < T → T ≤ r →
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ^ 2 ≤
          K * (n + 1 : ℝ) ^ (-(99 / 200 : ℝ)) *
            T ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_small_power
  refine ⟨K ^ 2, sq_nonneg K, ?_⟩
  intro T r t n hr hT hTr
  have hx : 0 < (n + 1 : ℝ) := by positivity
  calc
    ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ^ 2 ≤
        (K * (n + 1 : ℝ) ^ (-(99 / 400 : ℝ)) *
          T ^ (-(5 / 4 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hcoefficient hr hT hTr) 2
    _ = K ^ 2 * (n + 1 : ℝ) ^ (-(99 / 200 : ℝ)) *
          T ^ (-(5 / 2 : ℝ)) :=
      dualDerivative_small_square_algebra hx hT

/-- Squared coefficient envelope at exponent `599/200`. -/
theorem exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_large_power :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T r t : ℝ} {n : ℕ}, 4 ≤ r → 0 < T →
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ^ 2 ≤
          (K * (1 + r) ^ 2 / T ^ 2) *
            (n + 1 : ℝ) ^ (-(599 / 200 : ℝ)) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_le_large_power
  refine ⟨K ^ 2, sq_nonneg K, ?_⟩
  intro T r t n hr hT
  have hx : 0 < (n + 1 : ℝ) := by positivity
  calc
    ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ^ 2 ≤
        ((K * (1 + r) / T) *
          (n + 1 : ℝ) ^ (-(599 / 400 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hcoefficient hr hT) 2
    _ = (K ^ 2 * (1 + r) ^ 2 / T ^ 2) *
          (n + 1 : ℝ) ^ (-(599 / 200 : ℝ)) :=
      dualDerivative_large_square_algebra hx

/-- Both square masses needed by the infinite affine mean-square theorem are
unconditionally summable. -/
theorem summable_smoothAFEZetaSquareDualDerivativeCoefficient_masses
    {T r t : ℝ} (hr : 4 ≤ r) (hT : 0 < T) :
    Summable (fun n : ℕ ↦
      ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ^ 2) ∧
    Summable (fun n : ℕ ↦
      (n + 1 : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ^ 2) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_large_power
  have hplainBase : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-(599 / 200 : ℝ))) := by
    have h := Real.summable_nat_rpow.mpr
      (show (-(599 / 200 : ℝ)) < -1 by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ ↦
        (n : ℝ) ^ (-(599 / 200 : ℝ))) 1).mpr h
  have hweightedBase : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-(399 / 200 : ℝ))) := by
    have h := Real.summable_nat_rpow.mpr
      (show (-(399 / 200 : ℝ)) < -1 by norm_num)
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ ↦
        (n : ℝ) ^ (-(399 / 200 : ℝ))) 1).mpr h
  let A : ℝ := K * (1 + r) ^ 2 / T ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  constructor
  · refine Summable.of_nonneg_of_le (fun n ↦ sq_nonneg _) (fun n ↦ ?_)
      (hplainBase.mul_left A)
    exact hcoefficient hr hT
  · refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (by positivity) (sq_nonneg _))
      (fun n ↦ ?_) (hweightedBase.mul_left A)
    have hx : 0 < (n + 1 : ℝ) := by positivity
    calc
      (n + 1 : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeCoefficient T r t n‖ ^ 2 ≤
          (n + 1 : ℝ) *
            (A * (n + 1 : ℝ) ^ (-(599 / 200 : ℝ))) := by
        gcongr
        exact hcoefficient hr hT
      _ = A * ((n + 1 : ℝ) ^ (1 : ℝ) *
          (n + 1 : ℝ) ^ (-(599 / 200 : ℝ))) := by
        rw [Real.rpow_one]
        ring
      _ = A * (n + 1 : ℝ) ^ (-(399 / 200 : ℝ)) := by
        rw [← Real.rpow_add hx]
        congr 1
        congr 1
        ring

/-- The large-index tail already has the sharp plain square-mass decay. -/
theorem exists_tsum_smoothAFEZetaSquareDualDerivativeCoefficient_sq_tail_le :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r t : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        ∑' i : ℕ,
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
          9 * K * ((N : ℝ) ^ (-(399 / 200 : ℝ)) / (399 / 200 : ℝ)) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_large_power
  refine ⟨K, hK, ?_⟩
  intro N r t hN hr
  rcases hr with ⟨hrlower, hrupper⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hr4 : (4 : ℝ) ≤ r := hN4real.trans hrlower
  have hthree : 1 + r ≤ 3 * (N : ℝ) := by
    linarith
  have hone : 0 ≤ 1 + r := by
    linarith
  have hsquare : (1 + r) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hone hthree 2
  have hconstant : K * (1 + r) ^ 2 / (N : ℝ) ^ 2 ≤ 9 * K := by
    apply (div_le_iff₀ (sq_pos_of_pos hN0)).2
    have hmul := mul_le_mul_of_nonneg_left hsquare hK
    nlinarith
  have hbase : Summable (fun i : ℕ ↦
      ((i + (N + 1) : ℕ) : ℝ) ^ (-(599 / 200 : ℝ))) := by
    have h := Real.summable_nat_rpow.mpr
      (show (-(599 / 200 : ℝ)) < -1 by norm_num)
    exact (summable_nat_add_iff (f := fun n : ℕ ↦
      (n : ℝ) ^ (-(599 / 200 : ℝ))) (N + 1)).mpr h
  have hmajor : Summable (fun i : ℕ ↦
      9 * K * ((i + (N + 1) : ℕ) : ℝ) ^ (-(599 / 200 : ℝ))) :=
    hbase.mul_left (9 * K)
  have hpoint : ∀ i : ℕ,
      ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
        9 * K * ((i + (N + 1) : ℕ) : ℝ) ^ (-(599 / 200 : ℝ)) := by
    intro i
    calc
      ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
          (K * (1 + r) ^ 2 / (N : ℝ) ^ 2) *
            ((i + N) + 1 : ℝ) ^ (-(599 / 200 : ℝ)) :=
        by
          simpa [Nat.cast_add, Nat.cast_one] using
            hcoefficient (T := (N : ℝ)) (r := r) (t := t) (n := i + N) hr4 hN0
      _ ≤ 9 * K *
            ((i + (N + 1) : ℕ) : ℝ) ^ (-(599 / 200 : ℝ)) := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
          mul_le_mul_of_nonneg_right hconstant
            (Real.rpow_nonneg (show (0 : ℝ) ≤ ((i + N) + 1 : ℕ) by positivity) _)
  have hleft : Summable (fun i : ℕ ↦
      ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i ↦ sq_nonneg _) hpoint hmajor
  calc
    ∑' i : ℕ,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
        ∑' i : ℕ,
          9 * K * ((i + (N + 1) : ℕ) : ℝ) ^ (-(599 / 200 : ℝ)) := by
      exact Summable.tsum_le_tsum hpoint hleft hmajor
    _ = 9 * K * ∑' i : ℕ,
          ((i + (N + 1) : ℕ) : ℝ) ^ (-(599 / 200 : ℝ)) := by
      rw [tsum_mul_left]
    _ ≤ 9 * K *
          ((N : ℝ) ^ (1 - (599 / 200 : ℝ)) /
            ((599 / 200 : ℝ) - 1)) := by
      gcongr
      exact tsum_add_rpow_neg_le
        (show (1 : ℝ) < 599 / 200 by norm_num) hN1
    _ = 9 * K * ((N : ℝ) ^ (-(399 / 200 : ℝ)) /
          (399 / 200 : ℝ)) := by
      congr 2 <;> norm_num

/-- The small-index head has its exact integral-comparison mass. Its bracket is
`O(N^(101/200))`, hence the total exponent is `-399/200`. -/
theorem exists_sum_range_smoothAFEZetaSquareDualDerivativeCoefficient_sq_head_le :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r t : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        ∑ n ∈ Finset.range N,
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
          (K * (N : ℝ) ^ (-(5 / 2 : ℝ))) *
            (1 + (((N : ℝ) ^ (101 / 200 : ℝ) - 1) /
                (101 / 200 : ℝ)) +
              (N : ℝ) ^ (-(99 / 200 : ℝ))) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_small_power
  refine ⟨K, hK, ?_⟩
  intro N r t hN hr
  rcases hr with ⟨hrlower, hrupper⟩
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hr4 : (4 : ℝ) ≤ r := hN4real.trans hrlower
  have hreindex : ∀ f : ℕ → ℝ,
      ∑ n ∈ Finset.range N, f (n + 1) = ∑ k ∈ Finset.Icc 1 N, f k := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N (c := 1)]
    simp only [Finset.Ico_add_one_right_eq_Icc, zero_add]
  calc
    ∑ n ∈ Finset.range N,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
        ∑ n ∈ Finset.range N,
          K * (n + 1 : ℝ) ^ (-(99 / 200 : ℝ)) *
            (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcoefficient hr4 hN0 hrlower
    _ = (K * (N : ℝ) ^ (-(5 / 2 : ℝ))) *
          ∑ n ∈ Finset.range N,
            (n + 1 : ℝ) ^ (-(99 / 200 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (K * (N : ℝ) ^ (-(5 / 2 : ℝ))) *
          ∑ k ∈ Finset.Icc 1 N,
            (k : ℝ) ^ (-(99 / 200 : ℝ)) := by
      congr 1
      simpa [Nat.cast_add, Nat.cast_one] using
        hreindex (fun k : ℕ ↦ (k : ℝ) ^ (-(99 / 200 : ℝ)))
    _ ≤ (K * (N : ℝ) ^ (-(5 / 2 : ℝ))) *
          (1 + (((N : ℝ) ^ (101 / 200 : ℝ) - 1) /
              (101 / 200 : ℝ)) +
            (N : ℝ) ^ (-(99 / 200 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (Real.rpow_nonneg hN0.le _))
      have hsum := RHTower.Sieve.sum_rpow_neg_le_of_lt_one
        (show (0 : ℝ) < 99 / 200 by norm_num)
        (show (99 / 200 : ℝ) < 1 by norm_num)
        (show 2 ≤ N by omega)
      simpa only [show (1 : ℝ) - 99 / 200 = 101 / 200 by norm_num] using hsum

private theorem dualDerivative_head_bracket_le_four
    {N : ℕ} (hN : 1 ≤ N) :
    1 + (((N : ℝ) ^ (101 / 200 : ℝ) - 1) /
        (101 / 200 : ℝ)) +
      (N : ℝ) ^ (-(99 / 200 : ℝ)) ≤
        4 * (N : ℝ) ^ (101 / 200 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlarge : (1 : ℝ) ≤ (N : ℝ) ^ (101 / 200 : ℝ) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hsmall : (N : ℝ) ^ (-(99 / 200 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hNreal (by norm_num)
  nlinarith

/-- Sharp head exponent after simplifying the integral-comparison bracket. -/
theorem exists_sum_range_smoothAFEZetaSquareDualDerivativeCoefficient_sq_head_le_power :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r t : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        ∑ n ∈ Finset.range N,
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
          K * (N : ℝ) ^ (-(399 / 200 : ℝ)) := by
  obtain ⟨K, hK, hhead⟩ :=
    exists_sum_range_smoothAFEZetaSquareDualDerivativeCoefficient_sq_head_le
  refine ⟨4 * K, by positivity, ?_⟩
  intro N r t hN hr
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbracket := dualDerivative_head_bracket_le_four (show 1 ≤ N by omega)
  calc
    ∑ n ∈ Finset.range N,
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
        (K * (N : ℝ) ^ (-(5 / 2 : ℝ))) *
          (1 + (((N : ℝ) ^ (101 / 200 : ℝ) - 1) /
              (101 / 200 : ℝ)) +
            (N : ℝ) ^ (-(99 / 200 : ℝ))) := hhead hN hr
    _ ≤ (K * (N : ℝ) ^ (-(5 / 2 : ℝ))) *
          (4 * (N : ℝ) ^ (101 / 200 : ℝ)) := by
      gcongr
    _ = (4 * K) * ((N : ℝ) ^ (-(5 / 2 : ℝ)) *
          (N : ℝ) ^ (101 / 200 : ℝ)) := by
      ring
    _ = (4 * K) * (N : ℝ) ^ (-(399 / 200 : ℝ)) := by
      rw [← Real.rpow_add hN0]
      congr 1
      congr 1
      ring

/-- Sharp `n`-weighted head exponent required by Montgomery--Vaughan. -/
theorem exists_sum_range_smoothAFEZetaSquareDualDerivativeCoefficient_weighted_sq_head_le_power :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r t : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        ∑ n ∈ Finset.range N,
            (n + 1 : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
          K * (N : ℝ) ^ (-(199 / 200 : ℝ)) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_small_power
  refine ⟨K, hK, ?_⟩
  intro N r t hN hr
  rcases hr with ⟨hrlower, hrupper⟩
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hr4 : (4 : ℝ) ≤ r := hN4real.trans hrlower
  calc
    ∑ n ∈ Finset.range N,
        (n + 1 : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
        ∑ n ∈ Finset.range N,
          K * (N : ℝ) ^ (101 / 200 : ℝ) *
            (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnx : (n + 1 : ℕ) ≤ N := by
        exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
      have hnxReal : (n + 1 : ℝ) ≤ N := by exact_mod_cast hnx
      have hx : 0 < (n + 1 : ℝ) := by positivity
      have hpower : (n + 1 : ℝ) ^ (101 / 200 : ℝ) ≤
          (N : ℝ) ^ (101 / 200 : ℝ) :=
        Real.rpow_le_rpow hx.le hnxReal (by norm_num)
      calc
        (n + 1 : ℝ) *
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 ≤
            (n + 1 : ℝ) *
              (K * (n + 1 : ℝ) ^ (-(99 / 200 : ℝ)) *
                (N : ℝ) ^ (-(5 / 2 : ℝ))) := by
          gcongr
          exact hcoefficient hr4 hN0 hrlower
        _ = K * (n + 1 : ℝ) ^ (101 / 200 : ℝ) *
              (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
          calc
            (n + 1 : ℝ) *
                (K * (n + 1 : ℝ) ^ (-(99 / 200 : ℝ)) *
                  (N : ℝ) ^ (-(5 / 2 : ℝ))) =
                K * ((n + 1 : ℝ) ^ (1 : ℝ) *
                  (n + 1 : ℝ) ^ (-(99 / 200 : ℝ))) *
                    (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
              rw [Real.rpow_one]
              ring
            _ = K * (n + 1 : ℝ) ^ (101 / 200 : ℝ) *
                  (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
              rw [← Real.rpow_add hx]
              congr 2
              ring
        _ ≤ K * (N : ℝ) ^ (101 / 200 : ℝ) *
              (N : ℝ) ^ (-(5 / 2 : ℝ)) := by
          gcongr
    _ = (N : ℝ) *
          (K * (N : ℝ) ^ (101 / 200 : ℝ) *
            (N : ℝ) ^ (-(5 / 2 : ℝ))) := by
      simp
    _ = K * (N : ℝ) ^ (-(199 / 200 : ℝ)) := by
      calc
        (N : ℝ) *
            (K * (N : ℝ) ^ (101 / 200 : ℝ) *
              (N : ℝ) ^ (-(5 / 2 : ℝ))) =
            K * ((N : ℝ) ^ (1 : ℝ) *
              (N : ℝ) ^ (101 / 200 : ℝ) *
                (N : ℝ) ^ (-(5 / 2 : ℝ))) := by
          rw [Real.rpow_one]
          ring
        _ = K * (N : ℝ) ^ (-(199 / 200 : ℝ)) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
          congr 1
          congr 1
          ring

/-- Sharp `n`-weighted large-index tail. -/
theorem exists_tsum_smoothAFEZetaSquareDualDerivativeCoefficient_weighted_sq_tail_le :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {N : ℕ} {r t : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        ∑' i : ℕ,
            ((i + N) + 1 : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
          9 * K * ((N : ℝ) ^ (-(199 / 200 : ℝ)) / (199 / 200 : ℝ)) := by
  obtain ⟨K, hK, hcoefficient⟩ :=
    exists_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_large_power
  refine ⟨K, hK, ?_⟩
  intro N r t hN hr
  rcases hr with ⟨hrlower, hrupper⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hr4 : (4 : ℝ) ≤ r := hN4real.trans hrlower
  have hthree : 1 + r ≤ 3 * (N : ℝ) := by linarith
  have hone : 0 ≤ 1 + r := by linarith
  have hsquare : (1 + r) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hone hthree 2
  have hconstant : K * (1 + r) ^ 2 / (N : ℝ) ^ 2 ≤ 9 * K := by
    apply (div_le_iff₀ (sq_pos_of_pos hN0)).2
    have hmul := mul_le_mul_of_nonneg_left hsquare hK
    nlinarith
  have hbase : Summable (fun i : ℕ ↦
      ((i + (N + 1) : ℕ) : ℝ) ^ (-(399 / 200 : ℝ))) := by
    have h := Real.summable_nat_rpow.mpr
      (show (-(399 / 200 : ℝ)) < -1 by norm_num)
    exact (summable_nat_add_iff (f := fun n : ℕ ↦
      (n : ℝ) ^ (-(399 / 200 : ℝ))) (N + 1)).mpr h
  have hmajor : Summable (fun i : ℕ ↦
      9 * K * ((i + (N + 1) : ℕ) : ℝ) ^ (-(399 / 200 : ℝ))) :=
    hbase.mul_left (9 * K)
  have hpoint : ∀ i : ℕ,
      ((i + N) + 1 : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
        9 * K * ((i + (N + 1) : ℕ) : ℝ) ^ (-(399 / 200 : ℝ)) := by
    intro i
    have hx : 0 < (((i + N) + 1 : ℕ) : ℝ) := by positivity
    calc
      ((i + N) + 1 : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
          ((i + N) + 1 : ℝ) *
            ((K * (1 + r) ^ 2 / (N : ℝ) ^ 2) *
              ((i + N) + 1 : ℝ) ^ (-(599 / 200 : ℝ))) := by
        gcongr
        simpa [Nat.cast_add, Nat.cast_one] using
          hcoefficient (T := (N : ℝ)) (r := r) (t := t) (n := i + N) hr4 hN0
      _ = (K * (1 + r) ^ 2 / (N : ℝ) ^ 2) *
            ((i + N) + 1 : ℝ) ^ (-(399 / 200 : ℝ)) := by
        calc
          ((i + N) + 1 : ℝ) *
              ((K * (1 + r) ^ 2 / (N : ℝ) ^ 2) *
                ((i + N) + 1 : ℝ) ^ (-(599 / 200 : ℝ))) =
              (K * (1 + r) ^ 2 / (N : ℝ) ^ 2) *
                ((((i + N) + 1 : ℝ) ^ (1 : ℝ)) *
                  ((i + N) + 1 : ℝ) ^ (-(599 / 200 : ℝ))) := by
            rw [Real.rpow_one]
            ring
          _ = (K * (1 + r) ^ 2 / (N : ℝ) ^ 2) *
                ((i + N) + 1 : ℝ) ^ (-(399 / 200 : ℝ)) := by
            rw [← Real.rpow_add
              (show 0 < (i : ℝ) + (N : ℝ) + 1 by positivity)]
            congr 1
            congr 1
            ring
      _ ≤ 9 * K *
            ((i + (N + 1) : ℕ) : ℝ) ^ (-(399 / 200 : ℝ)) := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
          mul_le_mul_of_nonneg_right hconstant
            (Real.rpow_nonneg hx.le (-(399 / 200 : ℝ)))
  have hleft : Summable (fun i : ℕ ↦
      ((i + N) + 1 : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i ↦ mul_nonneg (by positivity) (sq_nonneg _)) hpoint hmajor
  calc
    ∑' i : ℕ,
        ((i + N) + 1 : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2 ≤
        ∑' i : ℕ,
          9 * K * ((i + (N + 1) : ℕ) : ℝ) ^ (-(399 / 200 : ℝ)) :=
      Summable.tsum_le_tsum hpoint hleft hmajor
    _ = 9 * K * ∑' i : ℕ,
          ((i + (N + 1) : ℕ) : ℝ) ^ (-(399 / 200 : ℝ)) := by
      rw [tsum_mul_left]
    _ ≤ 9 * K *
          ((N : ℝ) ^ (1 - (399 / 200 : ℝ)) /
            ((399 / 200 : ℝ) - 1)) := by
      gcongr
      exact tsum_add_rpow_neg_le
        (show (1 : ℝ) < 399 / 200 by norm_num) hN1
    _ = 9 * K * ((N : ℝ) ^ (-(199 / 200 : ℝ)) /
          (199 / 200 : ℝ)) := by
      congr 2 <;> norm_num

/-- **Localized derivative mass law.** On every dyadic height block, the full
plain and `n`-weighted square masses have the sharp powers needed by the
infinite affine mean-square theorem. -/
theorem exists_tsum_smoothAFEZetaSquareDualDerivativeCoefficient_masses_le_dyadic :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ {N : ℕ} {r t : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
        (∑' n : ℕ,
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2) ≤
            A * (N : ℝ) ^ (-(399 / 200 : ℝ)) ∧
        (∑' n : ℕ,
            (n + 1 : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2) ≤
            B * (N : ℝ) ^ (-(199 / 200 : ℝ)) := by
  obtain ⟨Ah, hAh, hhead⟩ :=
    exists_sum_range_smoothAFEZetaSquareDualDerivativeCoefficient_sq_head_le_power
  obtain ⟨At, hAt, htail⟩ :=
    exists_tsum_smoothAFEZetaSquareDualDerivativeCoefficient_sq_tail_le
  obtain ⟨Bh, hBh, hweightedHead⟩ :=
    exists_sum_range_smoothAFEZetaSquareDualDerivativeCoefficient_weighted_sq_head_le_power
  obtain ⟨Bt, hBt, hweightedTail⟩ :=
    exists_tsum_smoothAFEZetaSquareDualDerivativeCoefficient_weighted_sq_tail_le
  let A : ℝ := Ah + 9 * At / (399 / 200 : ℝ)
  let B : ℝ := Bh + 9 * Bt / (199 / 200 : ℝ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro N r t hN hr
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r := by
    have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
    exact hN4real.trans hr.1
  obtain ⟨hplainSummable, hweightedSummable⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeCoefficient_masses hr4 hN0
  constructor
  · have hsplit := hplainSummable.sum_add_tsum_nat_add N
    calc
      ∑' n : ℕ,
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 =
          (∑ n ∈ Finset.range N,
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2) +
          (∑' i : ℕ,
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2) :=
        by
          simpa [Nat.cast_add, Nat.cast_one] using hsplit.symm
      _ ≤ Ah * (N : ℝ) ^ (-(399 / 200 : ℝ)) +
          9 * At * ((N : ℝ) ^ (-(399 / 200 : ℝ)) /
            (399 / 200 : ℝ)) :=
        add_le_add (hhead hN hr) (htail hN hr)
      _ = A * (N : ℝ) ^ (-(399 / 200 : ℝ)) := by
        dsimp only [A]
        ring
  · have hsplit := hweightedSummable.sum_add_tsum_nat_add N
    calc
      ∑' n : ℕ,
          (n + 1 : ℝ) *
            ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2 =
          (∑ n ∈ Finset.range N,
            (n + 1 : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t n‖ ^ 2) +
          (∑' i : ℕ,
            ((i + N) + 1 : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r t (i + N)‖ ^ 2) :=
        by
          simpa [Nat.cast_add, Nat.cast_one] using hsplit.symm
      _ ≤ Bh * (N : ℝ) ^ (-(199 / 200 : ℝ)) +
          9 * Bt * ((N : ℝ) ^ (-(199 / 200 : ℝ)) /
            (199 / 200 : ℝ)) :=
        add_le_add (hweightedHead hN hr) (hweightedTail hN hr)
      _ = B * (N : ℝ) ^ (-(199 / 200 : ℝ)) := by
        dsimp only [B]
        ring

end RHTower
