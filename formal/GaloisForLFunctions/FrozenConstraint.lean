import Mathlib.Tactic

/-!
# Frozen finite constraint model

This is a finite proof-lab abstraction of the Wheeler-DeWitt slogan
`constraint, not flow`.  It does not formalize quantum gravity.  The only model
is a linear constraint operator `C`; physical states are the kernel of `C`.

The key point is algebraic: on a physical state, every positive power of `C`
vanishes, so any finite polynomial in `C` acts by its constant term.  In
particular, a constraint-generated finite "evolution" with constant term `1`
is gauge-trivial on physical states.
-/

open scoped BigOperators

namespace GaloisForLFunctions

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Physical states for a finite constraint operator: the kernel of `C`. -/
def PhysicalState (C : Module.End R M) (ψ : M) : Prop :=
  C ψ = 0

/-- A finite polynomial action `sum_{n<=N} a_n C^n ψ`. -/
def finiteConstraintPolynomialAction (C : Module.End R M) (a : ℕ → R) (N : ℕ) (ψ : M) : M :=
  ∑ n ∈ Finset.range (N + 1), a n • ((C ^ n) ψ)

/-- Positive powers of a constraint kill physical states. -/
@[aesop safe]
theorem constraint_power_succ_apply_eq_zero (C : Module.End R M) {ψ : M}
    (hψ : PhysicalState C ψ) (n : ℕ) :
    (C ^ (n + 1)) ψ = 0 := by
  rw [pow_succ]
  simp [PhysicalState] at hψ
  simp [hψ]

/-- On physical states, a finite polynomial in the constraint acts by its constant term. -/
@[aesop safe]
theorem finiteConstraintPolynomialAction_eq_constant (C : Module.End R M) {ψ : M}
    (hψ : PhysicalState C ψ) (a : ℕ → R) (N : ℕ) :
    finiteConstraintPolynomialAction C a N ψ = a 0 • ψ := by
  unfold finiteConstraintPolynomialAction
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n _ hne
    cases n with
    | zero => exact (hne rfl).elim
    | succ k => simp [constraint_power_succ_apply_eq_zero C hψ k]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.succ_pos N))).elim

/-- A constraint-generated finite evolution with constant term `1` is trivial on physical states. -/
@[aesop safe]
theorem finiteConstraintEvolution_eq_self (C : Module.End R M) {ψ : M}
    (hψ : PhysicalState C ψ) (a : ℕ → R) (N : ℕ) (ha0 : a 0 = 1) :
    finiteConstraintPolynomialAction C a N ψ = ψ := by
  rw [finiteConstraintPolynomialAction_eq_constant C hψ a N, ha0, one_smul]

/-- A linear observable commuting with the constraint preserves the physical-state subspace. -/
@[aesop safe]
theorem preserves_physicalState_of_commute (C A : Module.End R M)
    (hcomm : C * A = A * C) {ψ : M} (hψ : PhysicalState C ψ) :
    PhysicalState C (A ψ) := by
  unfold PhysicalState at hψ ⊢
  have happ := congrArg (fun F : Module.End R M => F ψ) hcomm
  simpa [hψ] using happ

end GaloisForLFunctions
