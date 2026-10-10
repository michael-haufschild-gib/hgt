import GaloisForLFunctions.RHTower.JointAncestryTwistedKroneckerDomination
import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorBlindBand

/-!
# Pole gluing as a similarity law

At a prime `p` and dressing `c`, the local parameters of the explicit-formula sector of `ρ` are
`A = p^{-(ρ+c)}` and `B = p^{-(1-ρ+c)}`.  Their product `AB = p^{-1-2c}` does not depend on `ρ`; this
is the pole gluing `μ_ρ ∗ (−)_*μ_{1-ρ̄} = μ_1` read at one prime.  Writing `q = p^{-(1/2+c)}` and
`ε = p^{1/2-ρ}` one has `A = qε`, `B = q/ε`, hence:

* **Local densities.**  On the unit circle the sector density is the critical Poisson kernel
  `P_q(z) = (1 - q²)/((1 - qz)(1 - q/z))` evaluated at the rotated point `εw`:
  `ℓ_{A,B}(w) = P_q(εw)`.  The rotation is a rotation of the circle exactly when `|ε| = 1`, i.e. on
  the critical line; an off-line zero evaluates the same kernel on the circle of radius
  `p^{1/2 - Re ρ}`.
* **Bernoulli matrices.**  The local Bernoulli Gram `[[1, B], [A, 1]]` equals
  `diag(1, ε) · [[1, q], [q, 1]] · diag(1, ε)⁻¹`: every zero's local matrix is similar to the critical
  one, with the zero-independent determinant `1 - q²` and trace `2`.  The similarity is unitary iff
  `Re ρ = 1/2`.

So all zeros share one local spectrum; they differ only by the similarity `diag(1, p^{1/2-ρ})`, and
the dressed aggregate is a compression of the zero form by these similarities.
-/

open Complex Matrix
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- The critical Poisson kernel `P_q(z) = (1 - q²)/((1 - qz)(1 - q/z))`. -/
def jasCriticalPoisson (q : ℝ) (z : ℂ) : ℂ := (1 - (q : ℂ) ^ 2) / ((1 - q * z) * (1 - q / z))

/-- The critical radius as a complex number: `p^{-(1/2+c)}`. -/
theorem jasCriticalRadius_eq (c : ℝ) (p : Nat.Primes) :
    ((jasCriticalRadius c p : ℝ) : ℂ) = cexp (-((1 / 2 : ℂ) + c) * (Real.log p : ℂ)) := by
  rw [jasCriticalRadius, Complex.ofReal_exp]; push_cast; ring_nf

/-- The similarity parameter `ε = p^{1/2 - ρ}`. -/
def jasSimilarity (ρ : ℂ) (p : Nat.Primes) : ℂ := cexp ((1 / 2 - ρ) * (Real.log p : ℂ))

theorem jasSimilarity_ne_zero (ρ : ℂ) (p : Nat.Primes) : jasSimilarity ρ p ≠ 0 :=
  Complex.exp_ne_zero _

theorem norm_jasSimilarity (ρ : ℂ) (p : Nat.Primes) :
    ‖jasSimilarity ρ p‖ = Real.exp ((1 / 2 - ρ.re) * Real.log p) := by
  rw [jasSimilarity, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.sub_re]
  norm_num

/-- The similarity is a rotation exactly on the critical line. -/
theorem norm_jasSimilarity_eq_one_iff (ρ : ℂ) (p : Nat.Primes) :
    ‖jasSimilarity ρ p‖ = 1 ↔ ρ.re = 1 / 2 := by
  rw [norm_jasSimilarity, Real.exp_eq_one_iff, mul_eq_zero, or_iff_left (log_prime_pos p).ne']
  constructor <;> intro h <;> linarith

theorem jasHoloA_dressed_eq (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasHoloA (ρ + c) p = (jasCriticalRadius c p : ℂ) * jasSimilarity ρ p := by
  rw [jasCriticalRadius_eq, jasSimilarity, jasHoloA, ← Complex.exp_add]
  congr 1; ring

theorem jasHoloB_dressed_eq (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasHoloB (ρ - c) p = (jasCriticalRadius c p : ℂ) / jasSimilarity ρ p := by
  rw [jasCriticalRadius_eq, jasSimilarity, jasHoloB, div_eq_mul_inv, ← Complex.exp_neg,
    ← Complex.exp_add]
  congr 1; ring

/-- **Pole gluing at one prime**: `A·B = p^{-1-2c}` for every zero. -/
theorem jasHoloA_mul_jasHoloB_dressed (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasHoloA (ρ + c) p * jasHoloB (ρ - c) p = (jasCriticalRadius c p : ℂ) ^ 2 := by
  rw [jasHoloA_dressed_eq, jasHoloB_dressed_eq]
  field_simp [jasSimilarity_ne_zero ρ p]

theorem jasHoloLocal_eq_div {a b w : ℂ} (hw : ‖w‖ = 1) (ha : 1 - a * w ≠ 0)
    (hb : 1 - b * conj w ≠ 0) :
    jasHoloLocal a b w = (1 - a * b) / ((1 - a * w) * (1 - b * conj w)) := by
  have hww : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; simp
  have hden : (1 - a * w) * (1 - b * conj w) ≠ 0 := mul_ne_zero ha hb
  have e1 : (1 - a * w)⁻¹ * ((1 - a * w) * (1 - b * conj w)) = 1 - b * conj w := by
    field_simp
  have e2 : (1 - b * conj w)⁻¹ * ((1 - a * w) * (1 - b * conj w)) = 1 - a * w := by
    field_simp
  rw [jasHoloLocal, eq_div_iff hden, sub_mul, add_mul, e1, e2]
  linear_combination (-(a * b)) * hww

/-- **Similarity law for local densities.**  On the unit circle the dressed sector density of any
strip point is the critical Poisson kernel at the point `εw`, `ε = p^{1/2-ρ}`. -/
theorem jasHoloLocal_dressed_eq_criticalPoisson {ρ : ℂ} {c : ℝ} (h0 : 0 < ρ.re + c)
    (h1 : 0 < 1 - ρ.re + c) (p : Nat.Primes) {w : ℂ} (hw : ‖w‖ = 1) :
    jasHoloLocal (jasHoloA (ρ + c) p) (jasHoloB (ρ - c) p) w =
      jasCriticalPoisson (jasCriticalRadius c p) (jasSimilarity ρ p * w) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; exact zero_ne_one hw
  have hconj : conj w = w⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hw]; simp
  have hA : ‖jasHoloA (ρ + c) p * w‖ < 1 := by
    rw [norm_mul, hw, mul_one, norm_jasHoloA, Real.exp_lt_one_iff]
    simp only [Complex.add_re, Complex.ofReal_re]
    nlinarith [log_prime_pos p]
  have hB : ‖jasHoloB (ρ - c) p * conj w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj, hw, mul_one, jasHoloB, Complex.norm_exp,
      Real.exp_lt_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.neg_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [log_prime_pos p]
  have hA0 : 1 - jasHoloA (ρ + c) p * w ≠ 0 := fun h => by
    have : jasHoloA (ρ + c) p * w = 1 := by linear_combination -h
    rw [this, norm_one] at hA; exact lt_irrefl 1 hA
  have hB0 : 1 - jasHoloB (ρ - c) p * conj w ≠ 0 := fun h => by
    have : jasHoloB (ρ - c) p * conj w = 1 := by linear_combination -h
    rw [this, norm_one] at hB; exact lt_irrefl 1 hB
  rw [jasHoloLocal_eq_div hw hA0 hB0, jasHoloA_mul_jasHoloB_dressed, jasCriticalPoisson,
    jasHoloA_dressed_eq, jasHoloB_dressed_eq, hconj]
  congr 2
  · ring
  · field_simp [jasSimilarity_ne_zero ρ p, hw0]

/-- The local Bernoulli Gram `[[1, B], [A, 1]]` of a dressed sector. -/
def jasLocalBernoulliMatrix (ρ : ℂ) (c : ℝ) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, jasHoloB (ρ - c) p; jasHoloA (ρ + c) p, 1]

/-- The critical local Gram `[[1, q], [q, 1]]`. -/
def jasCriticalBernoulliMatrix (c : ℝ) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, (jasCriticalRadius c p : ℂ); (jasCriticalRadius c p : ℂ), 1]

/-- The similarity `diag(1, ε)`. -/
def jasSimilarityMatrix (ρ : ℂ) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, jasSimilarity ρ p]

/-- Its inverse `diag(1, ε⁻¹)`. -/
def jasSimilarityMatrixInv (ρ : ℂ) (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, (jasSimilarity ρ p)⁻¹]

theorem jasSimilarityMatrix_mul_inv (ρ : ℂ) (p : Nat.Primes) :
    jasSimilarityMatrix ρ p * jasSimilarityMatrixInv ρ p = 1 := by
  rw [jasSimilarityMatrix, jasSimilarityMatrixInv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two,
    mul_inv_cancel₀ (jasSimilarity_ne_zero ρ p)]

/-- **Similarity law for Bernoulli matrices.**  Every zero's local Bernoulli Gram is similar to the
critical one: `[[1, B], [A, 1]] = diag(1, ε) · [[1, q], [q, 1]] · diag(1, ε)⁻¹`. -/
theorem jasLocalBernoulliMatrix_eq_similarity (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasLocalBernoulliMatrix ρ c p =
      jasSimilarityMatrix ρ p * jasCriticalBernoulliMatrix c p * jasSimilarityMatrixInv ρ p := by
  rw [jasLocalBernoulliMatrix, jasSimilarityMatrix, jasCriticalBernoulliMatrix,
    jasSimilarityMatrixInv, jasHoloA_dressed_eq, jasHoloB_dressed_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv,
    mul_inv_cancel₀ (jasSimilarity_ne_zero ρ p)]
  ring

/-- The local spectrum does not depend on the zero: determinant `1 - q²`. -/
theorem det_jasLocalBernoulliMatrix (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    (jasLocalBernoulliMatrix ρ c p).det = 1 - (jasCriticalRadius c p : ℂ) ^ 2 := by
  rw [jasLocalBernoulliMatrix, Matrix.det_fin_two_of, mul_comm (jasHoloB _ p),
    jasHoloA_mul_jasHoloB_dressed]
  ring

/-- ... and trace `2`. -/
theorem trace_jasLocalBernoulliMatrix (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    (jasLocalBernoulliMatrix ρ c p).trace = 2 := by
  rw [jasLocalBernoulliMatrix, Matrix.trace_fin_two_of]; norm_num

/-- The local Bernoulli Gram is Hermitian exactly on the critical line. -/
theorem jasLocalBernoulliMatrix_isHermitian_iff (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    (jasLocalBernoulliMatrix ρ c p).IsHermitian ↔ ρ.re = 1 / 2 := by
  rw [← norm_jasSimilarity_eq_one_iff ρ p]
  have hq : (0 : ℝ) < jasCriticalRadius c p := Real.exp_pos _
  have hε := jasSimilarity_ne_zero ρ p
  constructor
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    simp only [Matrix.conjTranspose_apply, jasLocalBernoulliMatrix, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, RCLike.star_def] at h10
    rw [jasHoloA_dressed_eq, jasHoloB_dressed_eq, map_div₀, Complex.conj_ofReal] at h10
    have hq0 : (jasCriticalRadius c p : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hc : conj (jasSimilarity ρ p) ≠ 0 := by simpa using hε
    have h2 : (jasCriticalRadius c p : ℂ) =
        (jasCriticalRadius c p : ℂ) * jasSimilarity ρ p * conj (jasSimilarity ρ p) := by
      rw [← h10]; field_simp
    have h3 : jasSimilarity ρ p * conj (jasSimilarity ρ p) = 1 :=
      mul_left_cancel₀ hq0 (by rw [mul_one, ← mul_assoc]; exact h2.symm)
    rw [Complex.mul_conj] at h3
    have h4 : Complex.normSq (jasSimilarity ρ p) = 1 := by exact_mod_cast h3
    rw [Complex.normSq_eq_norm_sq] at h4
    nlinarith [norm_nonneg (jasSimilarity ρ p)]
  · intro h
    have hconj : conj (jasSimilarity ρ p) = (jasSimilarity ρ p)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]; simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, jasLocalBernoulliMatrix, jasHoloA_dressed_eq,
        jasHoloB_dressed_eq, hconj, div_eq_mul_inv]

end

end RHTower
