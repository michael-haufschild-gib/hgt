import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Core

/-! # The canonical bosonic commutator selects the isometric line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open CoassociativeSplitting ModeCapacities
open scoped ComplexConjugate

def number (K : Kernel) (p : Nat.Primes) := (raise K p).comp (lower K p)

def bracket (T U : Core →ₗ[ℂ] Core) := T.comp U - U.comp T

theorem number_ket (K : Kernel) (p : Nat.Primes) (m : Occupation) :
    number K p (ket m) = ((‖ladder K p (m p)‖ ^ 2 : ℝ):ℂ) • ket m := by
  rw [number, LinearMap.comp_apply, lower_ket, map_smul, raise_ket]
  by_cases h : m p = 0
  · simp only [h, ladder, zero_smul, norm_zero, zero_pow two_ne_zero, Complex.ofReal_zero]
  · rw [sub_count, Nat.sub_one_add_one h, restore h, smul_smul, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem reverse_ket (K : Kernel) (p : Nat.Primes) (m : Occupation) :
    lower K p (raise K p (ket m)) = ((‖ladder K p (m p+1)‖ ^ 2 : ℝ):ℂ) • ket m := by
  rw [raise_ket, map_smul, lower_ket, add_count, add_tsub_cancel_right, smul_smul, Complex.conj_mul',
    Complex.ofReal_pow]

/-- The commutator eigenvalues are the consecutive differences of the
measured number eigenvalues, including the zero occupation. -/
theorem bracket_ket (K : Kernel) (p : Nat.Primes) (m : Occupation) :
    bracket (lower K p) (raise K p) (ket m) =
      ((‖ladder K p (m p+1)‖ ^ 2 - ‖ladder K p (m p)‖ ^ 2 : ℝ):ℂ) • ket m := by
  change lower K p (raise K p (ket m)) - number K p (ket m) = _
  rw [reverse_ket, number_ket, Complex.ofReal_sub, sub_smul]

/-- On the vacuum-based ladder the canonical bracket determines the
complete number spectrum, including the zero eigenvalue. -/
theorem bracket_iff_counts (K : Kernel) (p : Nat.Primes) :
    bracket (lower K p) (raise K p) = LinearMap.id ↔ ∀ k : ℕ, ‖ladder K p k‖ ^ 2 = (k:ℝ) := by
  constructor
  · intro h k
    induction k with
    | zero => simp [ladder]
    | succ k ih =>
      let m : Occupation := Finsupp.single p k
      have c : m p = k := Finsupp.single_eq_same
      have H := LinearMap.congr_fun h (ket m)
      rw [bracket_ket,c,LinearMap.id_apply] at H
      have value := congrArg (fun f : Core => f m) H
      simp only [Finsupp.smul_apply,ket,Finsupp.single_eq_same,smul_eq_mul,mul_one] at value
      have inc : ‖ladder K p (k+1)‖ ^ 2 - ‖ladder K p k‖ ^ 2 = 1 := by exact_mod_cast value
      rw [Nat.cast_succ]
      linarith only [inc,ih]
  · intro mass
    apply core_ext
    intro m
    rw [bracket_ket, mass, mass,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_left, Complex.ofReal_one, one_smul,LinearMap.id_apply]

/-- The identity on the entire finite-particle core is detected already
by the singly occupied state of any one physical prime. -/
theorem canonical_iff (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    bracket (lower (kernel s u v) p) (raise (kernel s u v) p) = LinearMap.id ↔ s.re = 1/2 := by
  rw [bracket_iff_counts]
  refine ⟨fun mass => (first_increment_iff s hu hv p).mp ?_,fun line => counts_on_line s hu hv p line⟩
  rw [mass,mass]
  norm_num

theorem canonical_iff_isometric (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    bracket (lower (kernel s u v) p) (raise (kernel s u v) p) = LinearMap.id ↔ isometric (kernel s u v) := by
  rw [canonical_iff s hu hv p, conserving_iff s hu hv]

#print axioms number_ket
#print axioms bracket_ket
#print axioms bracket_iff_counts
#print axioms canonical_iff
#print axioms canonical_iff_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
