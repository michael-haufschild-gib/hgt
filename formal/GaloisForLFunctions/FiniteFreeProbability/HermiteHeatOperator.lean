import GaloisForLFunctions.FiniteFreeProbability.JensenDictionary

/-!
# The heat operator is finite free convolution with a Hermite polynomial

On polynomials of degree `≤ d` the operator `e^{sD²}` is the finite sum
`Σ_{k ≤ d} (s^k/k!) D^{2k}`. By the Jensen dictionary it is `⊞_d` against the Hermite polynomial
`He_{d,s} = e^{sD²} X^d`: for `s < 0` the finite free semicircle (forward heat), for `s > 0` its
formal inverse (backward heat).

On the binomial `(1 + aX)^d`, the building block of every moment-represented Jensen polynomial,
`e^{sD²}` acts by `Σ_k (s^k/k!) a^{2k} d^{(2k)} (1 + aX)^{d−2k}`.
-/

open Polynomial Finset

namespace FiniteFreeProbability

noncomputable section

variable {K : Type*} [Field K]

/-- The symbol `Σ_{k ≤ d} (s^k/k!) X^{2k}` of `e^{sD²}` truncated for degree `≤ d`. -/
def heatSymbol (s : K) (d : ℕ) : K[X] :=
  ∑ k ∈ range (d + 1), C (s ^ k / (k.factorial : K)) * X ^ (2 * k)

/-- The heat operator `e^{sD²}` on polynomials of degree `≤ d`. -/
def heatOp (s : K) (d : ℕ) (p : K[X]) : K[X] :=
  diffOp (heatSymbol s d) p

theorem heatOp_eq_sum (s : K) (d : ℕ) (p : K[X]) :
    heatOp s d p = ∑ k ∈ range (d + 1), C (s ^ k / (k.factorial : K)) * derivative^[2 * k] p := by
  simp [heatOp, diffOp, heatSymbol, map_sum, LinearMap.sum_apply, Module.End.pow_apply,
    Module.algebraMap_end_apply, smul_eq_C_mul]

theorem heatOp_add (s : K) (d : ℕ) (p q : K[X]) :
    heatOp s d (p + q) = heatOp s d p + heatOp s d q := map_add _ _ _

theorem heatOp_C_mul (s : K) (d : ℕ) (a : K) (p : K[X]) :
    heatOp s d (C a * p) = C a * heatOp s d p := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul]; exact map_smul _ _ _

theorem heatOp_sum {ι : Type*} (s : K) (d : ℕ) (t : Finset ι) (f : ι → K[X]) :
    heatOp s d (∑ i ∈ t, f i) = ∑ i ∈ t, heatOp s d (f i) := map_sum _ _ _

/-- The heat operator commutes with ring maps of the coefficients. -/
theorem heatOp_map {L : Type*} [Field L] (φ : K →+* L) (s : K) (d : ℕ) (p : K[X]) :
    (heatOp s d p).map φ = heatOp (φ s) d (p.map φ) := by
  simp [heatOp_eq_sum, Polynomial.map_sum, iterate_derivative_map, map_div₀]

/-- `D^n (1 + aX)^m = a^n m^{(n)} (1 + aX)^{m−n}`. -/
theorem iterate_derivative_one_add_C_mul_X_pow (a : K) (m n : ℕ) :
    derivative^[n] ((1 + C a * X) ^ m) =
      C (a ^ n * (m.descFactorial n : K)) * (1 + C a * X) ^ (m - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_pow]
    have hd : derivative (1 + C a * X : K[X]) = C a := by simp
    rw [hd, Nat.descFactorial_succ, show m - n - 1 = m - (n + 1) by omega]
    simp only [map_mul, map_pow, map_natCast, Nat.cast_mul, pow_succ]
    ring

/-- `e^{sD²}` on the binomial `(1 + aX)^d`, evaluated at `w`. -/
theorem eval_heatOp_one_add_C_mul_X_pow (s a w : K) (d : ℕ) :
    (heatOp s d ((1 + C a * X) ^ d)).eval w =
      ∑ k ∈ range (d + 1), s ^ k / (k.factorial : K) * a ^ (2 * k) *
        (d.descFactorial (2 * k) : K) * (1 + a * w) ^ (d - 2 * k) := by
  rw [heatOp_eq_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [iterate_derivative_one_add_C_mul_X_pow]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_one, eval_X]
  ring

/-- The Hermite polynomial `He_{d,s} = e^{sD²} X^d`. -/
def hermiteFF (s : K) (d : ℕ) : K[X] := heatOp s d (X ^ d)

/-- **Heat is finite free convolution with a Hermite polynomial.** -/
theorem heatOp_eq_ffConv [CharZero K] {s : K} {d : ℕ} {p : K[X]} (hp : p.natDegree ≤ d) :
    heatOp s d p = ffConv d p (hermiteFF s d) :=
  (ffConv_diffOp_X_pow_right hp _).symm

end

end FiniteFreeProbability
