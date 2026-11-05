import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Finite free additive convolution

For polynomials of degree at most `d` the finite free additive convolution is

`p ⊞_d q = (1/d!) Σ_{j ≤ d} q^{(d-j)}(0) · p^{(j)}`,

the constant-coefficient differential operator whose symbol `S_q` satisfies `S_q(D) X^d = q`,
applied to `p`.

Evaluated at a point `z`, it is the apolarity pairing `Σ_{i+j=d} i! j! f_i q_j` of the Taylor
expansion `f = p(z + ·)` with `q`, divided by `d!`. Peeling a linear factor `X − μ` off `q` turns
the pairing at degree `d + 1` into the pairing at degree `d` of the polar derivative
`(d+1) f − (X + μ) f'`. Iterating this over the roots of `q` is the engine of Walsh's theorem.
-/

open Polynomial Finset

namespace FiniteFreeProbability

noncomputable section

variable {K : Type*} [Field K]

/-- The finite free additive convolution `p ⊞_d q = (1/d!) Σ_j (d-j)!·q_{d-j} · p^{(j)}`. -/
def ffConv (d : ℕ) (p q : K[X]) : K[X] :=
  ∑ j ∈ range (d + 1),
    C (q.coeff (d - j) * ((d - j).factorial : K) / (d.factorial : K)) * derivative^[j] p

theorem natDegree_ffConv_le (d : ℕ) (p q : K[X]) (hp : p.natDegree ≤ d) :
    (ffConv d p q).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative p j).trans (by omega))

/-- `⊞_d` commutes with ring maps of the coefficients. -/
theorem ffConv_map {L : Type*} [Field L] (φ : K →+* L) (d : ℕ) (p q : K[X]) :
    (ffConv d p q).map φ = ffConv d (p.map φ) (q.map φ) := by
  simp [ffConv, Polynomial.map_sum, iterate_derivative_map, coeff_map, map_div₀]

/-- The apolarity pairing `Σ_{i+j=d} i! j! f_i q_j`. -/
def apolarPairing (d : ℕ) (f q : K[X]) : K :=
  ∑ ij ∈ antidiagonal d,
    (ij.1.factorial : K) * (ij.2.factorial : K) * f.coeff ij.1 * q.coeff ij.2

/-- The polar derivative `m g − (X − ζ) g'` of `g`, read at formal degree `m`, with pole `ζ`. -/
def polarDeriv (m : ℕ) (ζ : K) (g : K[X]) : K[X] :=
  C (m : K) * g - (X - C ζ) * derivative g

theorem coeff_polarDeriv (m : ℕ) (ζ : K) (g : K[X]) (i : ℕ) :
    (polarDeriv m ζ g).coeff i =
      ((m : K) - i) * g.coeff i + ζ * ((i : K) + 1) * g.coeff (i + 1) := by
  have hX : (X * derivative g).coeff i = (i : K) * g.coeff i := by
    rcases i with _ | k
    · simp
    · rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  simp only [polarDeriv, sub_mul, coeff_sub, coeff_C_mul, hX, coeff_derivative]
  ring

/-- The `j`-th derivative at `z` is `j!` times the `j`-th Taylor coefficient at `z`. -/
theorem eval_iterate_derivative_eq (j : ℕ) (p : K[X]) (z : K) :
    (derivative^[j] p).eval z = (j.factorial : K) * (taylor z p).coeff j := by
  rw [taylor_coeff, ← factorial_smul_hasseDeriv]
  simp [nsmul_eq_mul]

/-- **Evaluation is an apolarity pairing.** `(p ⊞_d q)(z) = ⟨p(z + ·), q⟩_d / d!`. -/
theorem eval_ffConv (d : ℕ) (p q : K[X]) (z : K) :
    (ffConv d p q).eval z = apolarPairing d (taylor z p) q / (d.factorial : K) := by
  rw [ffConv, eval_finsetSum, apolarPairing,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, eval_iterate_derivative_eq]
  ring

/-- Against a constant only the top Taylor coefficient survives. -/
theorem apolarPairing_C (d : ℕ) (f : K[X]) (a : K) :
    apolarPairing d f (C a) = (d.factorial : K) * f.coeff d * a := by
  rw [apolarPairing, Finset.sum_eq_single (d, 0)]
  · simp
  · rintro ⟨i, j⟩ hij hne
    rcases j with _ | j
    · exact absurd (by simpa using (mem_antidiagonal.1 hij)) hne
    · simp
  · intro h
    exact absurd (mem_antidiagonal.2 (by simp)) h

/-- **Peeling a root.** For `deg q ≤ d`,
`⟨f, (X − μ) q⟩_{d+1} = ⟨(d+1) f − (X + μ) f', q⟩_d`. -/
theorem apolarPairing_X_sub_C_mul (d : ℕ) (f q : K[X]) (μ : K) (hq : q.natDegree ≤ d) :
    apolarPairing (d + 1) f ((X - C μ) * q) = apolarPairing d (polarDeriv (d + 1) (-μ) f) q := by
  have hcoeff : ∀ k, ((X - C μ) * q).coeff k = (X * q).coeff k - μ * q.coeff k := by
    intro k; simp [sub_mul, coeff_C_mul]
  have hsplit : apolarPairing (d + 1) f ((X - C μ) * q) =
      (∑ ij ∈ antidiagonal (d + 1),
        (ij.1.factorial : K) * (ij.2.factorial : K) * f.coeff ij.1 * (X * q).coeff ij.2) -
      μ * ∑ ij ∈ antidiagonal (d + 1),
        (ij.1.factorial : K) * (ij.2.factorial : K) * f.coeff ij.1 * q.coeff ij.2 := by
    rw [apolarPairing, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [hcoeff]; ring
  have hA : (∑ ij ∈ antidiagonal (d + 1),
        (ij.1.factorial : K) * (ij.2.factorial : K) * f.coeff ij.1 * (X * q).coeff ij.2) =
      ∑ ij ∈ antidiagonal d,
        (ij.1.factorial : K) * ((ij.2 + 1).factorial : K) * f.coeff ij.1 * q.coeff ij.2 := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp [coeff_X_mul]
  have hB : (∑ ij ∈ antidiagonal (d + 1),
        (ij.1.factorial : K) * (ij.2.factorial : K) * f.coeff ij.1 * q.coeff ij.2) =
      ∑ ij ∈ antidiagonal d,
        ((ij.1 + 1).factorial : K) * (ij.2.factorial : K) * f.coeff (ij.1 + 1) * q.coeff ij.2 := by
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp [coeff_eq_zero_of_natDegree_lt (show q.natDegree < d + 1 by omega)]
  rw [hsplit, hA, hB, apolarPairing, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hsum : (ij.1 : K) + ij.2 = d := by rw [← Nat.cast_add, mem_antidiagonal.1 hij]
  rw [coeff_polarDeriv]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hd : (d : K) + 1 - ij.1 = ij.2 + 1 := by rw [← hsum]; ring
  rw [hd]
  ring

end

end FiniteFreeProbability
