import GaloisForLFunctions.HTGeometry.Thermofield.PrimeLogApplications
import GaloisForLFunctions.HilbertMetric.Spectral.DiagonalCutoff
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Vacuum-column recovery from imaginary time

Imaginary time gives a positive diagonal observation of the vacuum-to-prime
transitions. The cutoff argument of Hong (arXiv:2611.16596, Theorem 5.2)
separates amplified noise from missing spectral energy. The inverse loses
uniform stability as the prime energies grow.
-/

open scoped BigOperators NNReal

namespace GaloisForLFunctions.HTGeometry.Thermofield

open HilbertMetric.DiagonalCutoff

noncomputable section

private abbrev Depth := Set.Ioi (0 : ℝ)

/-- The actual vacuum column of the imaginary-time evolved observable. -/
def primeLogBoundaryColumn (P : Finset Nat.Primes) (τ : Depth)
    (A : Matrix (Option P) (Option P) ℂ) (p : P) : ℂ :=
  evolve (primeLogKMSFiniteEnergy P) (Complex.I * (τ : ℝ)) A (some p) none

private def boundaryGain (τ : Depth) (p : Nat.Primes) : Set.Ioi (0 : ℝ) :=
  ⟨Real.exp (-(τ : ℝ) * primeLogSupport p), Real.exp_pos _⟩

/-- A transition of energy `log p` is attenuated by `exp (-τ log p)`. -/
theorem primeLogBoundaryColumn_eq (P : Finset Nat.Primes) (τ : Depth)
    (A : Matrix (Option P) (Option P) ℂ) (p : P) :
    primeLogBoundaryColumn P τ A p =
      Real.exp (-(τ : ℝ) * primeLogSupport p.1) • A (some p) none := by
  unfold primeLogBoundaryColumn evolve
  rw [primeLogKMSFiniteEnergy_gap, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.real_smul]

/-- Exact agreement of boundary data determines the undamped vacuum column. -/
theorem primeLogBoundaryColumn_eq_iff (P : Finset Nat.Primes) (τ : Depth)
    (A B : Matrix (Option P) (Option P) ℂ) :
    primeLogBoundaryColumn P τ A = primeLogBoundaryColumn P τ B ↔
      (fun p : P => A (some p) none) = (fun p : P => B (some p) none) := by
  have h (M : Matrix (Option P) (Option P) ℂ) :
      primeLogBoundaryColumn P τ M = fun p : P => (boundaryGain τ p.1 : ℝ) • M (some p) none :=
    funext (primeLogBoundaryColumn_eq P τ M)
  rw [h A, h B]
  exact (measure_injective (fun p : P => boundaryGain τ p.1)).eq_iff

/-- Invert the attenuation on prime energies at or below the resolution cutoff. -/
def recoverPrimeLogBoundaryColumn (P : Finset Nat.Primes) (τ : Depth) (R : ℝ)
    (data : P → ℂ) : P → ℂ :=
  recover (Finset.univ.filter fun p : P => primeLogSupport p.1 ≤ R)
    (fun p => boundaryGain τ p.1) data

/-- The squared error retains the exact spectral multiplier on the measurement noise. -/
theorem recoverPrimeLogBoundaryColumn_error
    (P : Finset Nat.Primes) (τ : Depth) (R : ℝ)
    (A : Matrix (Option P) (Option P) ℂ) (noise : P → ℂ) :
    (∑ p : P, ‖recoverPrimeLogBoundaryColumn P τ R
        (fun j => primeLogBoundaryColumn P τ A j + noise j) p - A (some p) none‖ ^ 2) =
      (∑ p : P with primeLogSupport p.1 ≤ R,
        Real.exp (2 * (τ : ℝ) * primeLogSupport p.1) * ‖noise p‖ ^ 2) +
      (∑ p : P with R < primeLogSupport p.1, ‖A (some p) none‖ ^ 2) := by
  simp only [primeLogBoundaryColumn_eq, recoverPrimeLogBoundaryColumn]
  change (∑ p ∈ Finset.univ, ‖recover _ (fun p : P => boundaryGain τ p.1)
      (fun j => (boundaryGain τ j.1 : ℝ) • A (some j) none + noise j) p -
        A (some p) none‖ ^ 2) = _
  rw [squared_error]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [boundaryGain, neg_mul, Real.exp_neg, inv_inv, pow_two, ← Real.exp_add]
  rw [show (τ : ℝ) * primeLogSupport p.1 + (τ : ℝ) * primeLogSupport p.1 =
    2 * (τ : ℝ) * primeLogSupport p.1 by ring]

/-- A first spectral moment bounds the discarded squared signal, while retained
noise is amplified by at most `exp (2τR)`. -/
theorem recoverPrimeLogBoundaryColumn_bound
    (P : Finset Nat.Primes) (τ : Depth) (R : ℝ≥0)
    (A : Matrix (Option P) (Option P) ℂ) (noise : P → ℂ) :
    (∑ p : P, ‖recoverPrimeLogBoundaryColumn P τ R
        (fun j => primeLogBoundaryColumn P τ A j + noise j) p - A (some p) none‖ ^ 2) ≤
      Real.exp (2 * (τ : ℝ) * R) * (∑ p : P, ‖noise p‖ ^ 2) +
      ((1 + (R : ℝ)) ^ 2)⁻¹ * (∑ p : P, (1 + primeLogSupport p.1) ^ 2 * ‖A (some p) none‖ ^ 2) := by
  rw [recoverPrimeLogBoundaryColumn_error]
  have hτ : 0 < (τ : ℝ) := τ.2
  apply add_le_add
  · rw [Finset.mul_sum]
    calc
      _ ≤ ∑ p : P with primeLogSupport p.1 ≤ (R : ℝ),
          Real.exp (2 * (τ : ℝ) * R) * ‖noise p‖ ^ 2 := by
        refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hp).2 (by positivity : 0 ≤ 2 * (τ : ℝ)))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro p _ _
        positivity)
  · rw [Finset.mul_sum]
    calc
      _ ≤ ∑ p : P with (R : ℝ) < primeLogSupport p.1,
          ((1 + (R : ℝ)) ^ 2)⁻¹ * ((1 + primeLogSupport p.1) ^ 2 * ‖A (some p) none‖ ^ 2) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hR : 0 < 1 + (R : ℝ) := by positivity
        have hle : 1 + (R : ℝ) ≤ 1 + primeLogSupport p.1 :=
          add_le_add le_rfl (Finset.mem_filter.mp hp).2.le
        have hs := (sq_le_sq₀ hR.le (hR.le.trans hle)).mpr hle
        rw [inv_mul_eq_div, le_div_iff₀ (sq_pos_of_pos hR), mul_comm (‖A (some p) none‖ ^ 2)]
        exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro p _ _
        positivity)

/-- There are unit vacuum transitions with arbitrarily small observed amplitude,
even on a spectrum consisting of the vacuum and one prime. -/
theorem exists_weak_primeLogBoundaryColumn (τ : Depth) (ε : Set.Ioi (0 : ℝ)) :
    ∃ (p : Nat.Primes) (A : Matrix (Option (↑({p} : Finset Nat.Primes)))
        (Option (↑({p} : Finset Nat.Primes))) ℂ),
      let i : (↑({p} : Finset Nat.Primes)) := ⟨p, Finset.mem_singleton_self p⟩
      A.IsHermitian ∧ A (some i) none = 1 ∧ ‖primeLogBoundaryColumn {p} τ A i‖ < (ε : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (-Real.log (ε : ℝ) / (τ : ℝ)))
  obtain ⟨m, hnm, hm⟩ := Nat.exists_infinite_primes n
  let p : Nat.Primes := ⟨m, hm⟩
  have hml : Real.exp (-Real.log (ε : ℝ) / (τ : ℝ)) < (m : ℝ) :=
    hn.trans_le (by exact_mod_cast hnm)
  have hp : -Real.log (ε : ℝ) / (τ : ℝ) < primeLogSupport p := by
    exact (Real.lt_log_iff_exp_lt ((Real.exp_pos _).trans hml)).mpr hml
  have hτ : 0 < (τ : ℝ) := τ.2
  have hgap : -(τ : ℝ) * primeLogSupport p < Real.log (ε : ℝ) := by
    have h := (div_lt_iff₀ hτ).mp hp
    linarith only [h]
  let A : Matrix (Option (↑({p} : Finset Nat.Primes))) (Option (↑({p} : Finset Nat.Primes))) ℂ :=
    fun j k => if j = k then 0 else 1
  have hA : A.IsHermitian := by
    ext j k
    by_cases h : j = k
    · simp [A, Matrix.conjTranspose_apply, h]
    · simp [A, Matrix.conjTranspose_apply, h, Ne.symm h]
  refine ⟨p, A, hA, by simp [A], ?_⟩
  rw [primeLogBoundaryColumn_eq, show A (some _) none = 1 by simp [A],
    norm_smul, norm_one, mul_one,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_log ε.2]
  exact Real.exp_lt_exp.mpr hgap

#print axioms primeLogBoundaryColumn_eq_iff
#print axioms recoverPrimeLogBoundaryColumn_bound
#print axioms exists_weak_primeLogBoundaryColumn

end

end GaloisForLFunctions.HTGeometry.Thermofield
