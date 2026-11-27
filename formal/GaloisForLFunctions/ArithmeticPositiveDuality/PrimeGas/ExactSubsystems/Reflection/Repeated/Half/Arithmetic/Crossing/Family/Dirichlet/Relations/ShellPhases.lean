import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.AlgebraicShell

/-! # Transporting shell relations through finite-order prime phases -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Finset MvPolynomial Real

/-- Product of the elementary prime phases with the occupations of the shell. -/
def shellPhase (χ : Nat.Primes → ℂ) (n : ℕ+) : ℂ :=
  (label.symm n).prod (fun p k => χ p ^ k)

/-- All composite shells inherit the same exponent bound as the prime phases. -/
theorem shellPhase_pow (χ : Nat.Primes → ℂ) {m : ℕ} (h : ∀ p, χ p^m=1) (n : ℕ+) :
    shellPhase χ n^m=1 := by
  classical
  unfold shellPhase Finsupp.prod
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro p _
  rw [← pow_mul,mul_comm, pow_mul,h,one_pow]

theorem phase_norm {z : ℂ} {m : ℕ} (hm : 0 < m) (h : z^m=1) : ‖z‖=1 := by
  apply (pow_left_inj₀ (norm_nonneg _) zero_le_one hm.ne').mp
  rw [← norm_pow,h,norm_one,one_pow]

/-- Twisting the prime coordinates changes the shell monomial by precisely
the product of their phases. -/
theorem eval_twisted_atom (χ : Nat.Primes → ℂ) (s : ℝ) (n : ℕ+) :
    aeval (fun p => χ p*(coordinates s p : ℂ)) (atom n)=
      shellPhase χ n*(shellPower s n : ℂ) := by
  have product := monomial_power (label.symm n) s
  rw [Equiv.apply_symm_apply] at product
  rw [atom,aeval_monomial,map_one,one_mul,← product]
  simp only [Finsupp.prod,shellPhase,mul_pow,Finset.prod_mul_distrib,Complex.ofReal_prod,Complex.ofReal_pow]

theorem shellPower_pos (v : ℝ) (n : ℕ+) : 0<shellPower v n :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr n.pos) _

/-- At a signed target every original prime polynomial relation has one
complex specialization, with a compatible finite-order phase on every shell. -/
theorem twisted_evaluation {m : ℕ} {t v : ℝ} (h : TorsionSpecialization m t v) :
    ∃ (e : PolynomialRing →ₐ[ℤ] ℂ) (ω : ℕ+ → ℂ), (∀ n, (ω n)^m=1) ∧
      (∀ n, e (atom n)=ω n*(shellPower v n : ℂ)) ∧ ∀ P, value t P=0 → e P=0 := by
  obtain ⟨χ,unit,relations⟩ := h
  exact ⟨_,shellPhase χ,shellPhase_pow χ unit,eval_twisted_atom χ v,relations⟩

#print axioms shellPhase_pow
#print axioms twisted_evaluation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
