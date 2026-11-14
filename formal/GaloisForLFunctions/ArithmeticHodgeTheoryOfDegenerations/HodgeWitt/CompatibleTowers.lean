import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Compatible towers have no transition-power torsion

A backward orbit for an endomorphism `T` satisfies `T xₙ₊₁ = xₙ`.
Thus `T^r xₙ₊ᵣ = xₙ`: a uniform power of `T` can kill the whole orbit
only when the orbit is zero. For multiplication by `p`, this is the
torsion-freeness argument for the Tate module in §5 of Yang's
*Finite torsion in Hodge--Witt cohomology groups*.
-/

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The inverse limit of the constant system with transition map `T`. -/
def backwardOrbits (T : Module.End R M) : Submodule R (ℕ → M) where
  carrier := {x | ∀ n, T (x (n + 1)) = x n}
  zero_mem' := fun _ => T.map_zero
  add_mem' := by
    intro x y hx hy n
    exact (T.map_add _ _).trans (congrArg₂ (· + ·) (hx n) (hy n))
  smul_mem' := by
    intro a x hx n
    exact (T.map_smul a _).trans (congrArg (a • ·) (hx n))

/-- Iterated compatibility recovers a coordinate from every later coordinate. -/
theorem backwardOrbits_pow_apply (T : Module.End R M) (x : backwardOrbits T) (r n : ℕ) :
    (T ^ r) (x.1 (n + r)) = x.1 n := by
  induction r generalizing n with
  | zero => simp only [pow_zero, Nat.add_zero, Module.End.one_apply]
  | succ r ih =>
      rw [pow_succ', Module.End.mul_apply,
        show n + (r + 1) = (n + 1) + r from Nat.add_right_comm n r 1,
        ih, x.2 n]

/-- No nonzero compatible tower is killed coordinatewise by a uniform power of `T`. -/
theorem backwardOrbits_uniform_torsion_iff (T : Module.End R M)
    (x : backwardOrbits T) (r : ℕ) :
    (∀ n, (T ^ r) (x.1 n) = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    funext n
    exact (backwardOrbits_pow_apply T x r n).symm.trans (h (n + r))
  · rintro rfl
    intro n
    exact map_zero _

/-- On backward orbits, coordinatewise transition is an automorphism with inverse shift. -/
def backwardTransitionEquiv (T : Module.End R M) : backwardOrbits T ≃ₗ[R] backwardOrbits T where
  toFun x := ⟨fun n => T (x.1 n), fun n => congrArg T (x.2 n)⟩
  invFun x := ⟨fun n => x.1 (n + 1), fun n => x.2 (n + 1)⟩
  left_inv x := Subtype.ext (funext x.2)
  right_inv x := Subtype.ext (funext x.2)
  map_add' x y := Subtype.ext (funext fun n => T.map_add (x.1 n) (y.1 n))
  map_smul' a x := Subtype.ext (funext fun n => T.map_smul a (x.1 n))

/-- An invertible operator has exactly one backward orbit through each initial value. -/
def backwardOrbitsEquiv (e : M ≃ₗ[R] M) : backwardOrbits e.toLinearMap ≃ₗ[R] M where
  toFun x := x.1 0
  invFun y := ⟨fun n => (e.symm.toLinearMap ^ n) y, by
    intro n
    change e ((e.symm.toLinearMap ^ (n + 1)) y) = (e.symm.toLinearMap ^ n) y
    rw [pow_succ', Module.End.mul_apply]
    exact e.apply_symm_apply _⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    change (e.symm.toLinearMap ^ n) (x.1 0) = x.1 n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        apply e.injective
        exact (e.apply_symm_apply _).trans (x.2 n).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every coordinate of an infinitely divisible orbit belongs to every iterated image. -/
theorem backwardOrbits_mem_stableImage (T : Module.End R M)
    (x : backwardOrbits T) (n : ℕ) : x.1 n ∈ ⨅ r : ℕ, LinearMap.range (T ^ r) := by
  apply (Submodule.mem_iInf _).mpr
  intro r
  exact ⟨x.1 (n + r), backwardOrbits_pow_apply T x r n⟩

/-- The actual Tate tower: compatible division points, with the `n`th point killed by `pⁿ`. -/
def tateTower (p : ℕ) (A : Type*) [AddCommGroup A] : Submodule ℤ (ℕ → A) where
  carrier := {x | (∀ n, p • x (n + 1) = x n) ∧ (∀ n, p ^ n • x n = 0)}
  zero_mem' := ⟨fun _ => smul_zero _, fun _ => smul_zero _⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · intro n
      exact (smul_add _ _ _).trans (congrArg₂ (· + ·) (hx.1 n) (hy.1 n))
    · intro n
      rw [Pi.add_apply, smul_add, hx.2 n, hy.2 n, add_zero]
  smul_mem' := by
    intro a x hx
    constructor
    · intro n
      change p • (a • x (n + 1)) = a • x n
      rw [smul_comm, hx.1 n]
    · intro n
      change p ^ n • (a • x n) = 0
      rw [smul_comm, hx.2 n, smul_zero]

/-- Every coordinate is recovered by multiplying a later division point by `pʳ`. -/
theorem tateTower_pow_smul (p : ℕ) {A : Type*} [AddCommGroup A]
    (x : tateTower p A) (r n : ℕ) : p ^ r • x.1 (n + r) = x.1 n := by
  induction r generalizing n with
  | zero => simp only [pow_zero, Nat.add_zero, one_smul]
  | succ r ih =>
      rw [pow_succ', mul_smul,
        show n + (r + 1) = (n + 1) + r from Nat.add_right_comm n r 1,
        ih, x.2.1 n]

/-- A Tate tower has no nonzero `p`-power torsion, even when its individual levels do. -/
theorem tateTower_pow_smul_eq_zero_iff (p : ℕ) {A : Type*} [AddCommGroup A]
    (x : tateTower p A) (r : ℕ) : p ^ r • x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    funext n
    have hn := congrArg (fun y : tateTower p A => y.1 (n + r)) h
    exact (tateTower_pow_smul p x r n).symm.trans hn
  · rintro rfl
    exact smul_zero _

#print axioms backwardOrbits_uniform_torsion_iff
#print axioms backwardTransitionEquiv
#print axioms backwardOrbitsEquiv
#print axioms tateTower_pow_smul_eq_zero_iff

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
