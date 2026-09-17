import GaloisForLFunctions.RHTower.SuzukiPhysicalLogGradeNuclearSummability

/-!
# Hyperoctahedral blindness of the physical prime--Gamma word coefficient

The physical inverse-log word carrier uses a `Bool` orientation label, but its scalar coefficient
is the Volterra factor times the product of prime-power weights.  It therefore ignores every
orientation bit and every ordering of a fixed word.  This closes a concrete attempted SP-E source
bridge: neither the scalar physical word coefficient nor its associated inverse-log profile can
provide the required signed type-B descent action or distinguish the first `3142`/`3241` collision.

The result is deliberately limited to this scalar/profile carrier.  A surviving signed-Eulerian
source must act before this commutative product, retaining ordered pair incidence or a
support-valued/matrix-valued history.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The physical word coefficient is independent of every orientation assignment on fixed
prime-power labels. -/
theorem suzukiWordCoefficient_orientation_independent
    {k : ℕ} (ν : Fin k → Nat.Primes × ℕ) (ε η : Fin k → Bool) :
    suzukiWordCoefficient k (fun i => (ν i, ε i)) =
      suzukiWordCoefficient k (fun i => (ν i, η i)) := by
  simp [suzukiWordCoefficient]

/-- The physical word coefficient is invariant under reordering its labelled positions. -/
theorem suzukiWordCoefficient_reindex
    {k : ℕ} (ν : Fin k → (Nat.Primes × ℕ) × Bool) (σ : Equiv.Perm (Fin k)) :
    suzukiWordCoefficient k (fun i => ν (σ i)) = suzukiWordCoefficient k ν := by
  unfold suzukiWordCoefficient
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

/-- Full signed-permutation blindness of the scalar physical word coefficient: it is invariant
under arbitrary coordinate permutation and independently chosen output orientation bits. -/
theorem suzukiWordCoefficient_hyperoctahedral_invariant
    {k : ℕ} (ν : Fin k → Nat.Primes × ℕ) (ε η : Fin k → Bool)
    (σ : Equiv.Perm (Fin k)) :
    suzukiWordCoefficient k (fun i => (ν (σ i), ε i)) =
      suzukiWordCoefficient k (fun i => (ν i, η i)) := by
  calc
    suzukiWordCoefficient k (fun i => (ν (σ i), ε i)) =
        suzukiWordCoefficient k (fun i => (ν (σ i), η (σ i))) :=
      suzukiWordCoefficient_orientation_independent (fun i => ν (σ i)) ε
        (fun i => η (σ i))
    _ = suzukiWordCoefficient k (fun i => (ν i, η i)) :=
      suzukiWordCoefficient_reindex (fun i => (ν i, η i)) σ

/-- The two ordered four-label lists realizing the first type-B top-fibre collision, with prime
power labels supplied in increasing reference order. -/
def suzukiPhysicalPrimeWord3142
    (ν : Fin 4 → Nat.Primes × ℕ) (ε : Fin 4 → Bool) :
    Fin 4 → (Nat.Primes × ℕ) × Bool :=
  fun i => (![ν 2, ν 0, ν 3, ν 1] i, ε i)

/-- The companion order of the first type-B top-fibre collision. -/
def suzukiPhysicalPrimeWord3241
    (ν : Fin 4 → Nat.Primes × ℕ) (ε : Fin 4 → Bool) :
    Fin 4 → (Nat.Primes × ℕ) × Bool :=
  fun i => (![ν 2, ν 1, ν 3, ν 0] i, ε i)

/-- The existing physical word coefficient cannot distinguish the `3142` and `3241` histories,
even when their orientation labels are assigned independently. -/
theorem suzukiWordCoefficient_3142_eq_3241
    (ν : Fin 4 → Nat.Primes × ℕ) (ε η : Fin 4 → Bool) :
    suzukiWordCoefficient 4 (suzukiPhysicalPrimeWord3142 ν ε) =
      suzukiWordCoefficient 4 (suzukiPhysicalPrimeWord3241 ν η) := by
  unfold suzukiPhysicalPrimeWord3142 suzukiPhysicalPrimeWord3241
  let a : Fin 4 → Nat.Primes × ℕ := ![ν 2, ν 0, ν 3, ν 1]
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 3
  calc
    suzukiWordCoefficient 4 (fun i => (a i, ε i)) =
        suzukiWordCoefficient 4 (fun i => (a (σ i), η i)) :=
      (suzukiWordCoefficient_hyperoctahedral_invariant a η ε σ).symm
    _ = suzukiWordCoefficient 4 (fun i => (![ν 2, ν 1, ν 3, ν 0] i, η i)) := by
      congr 1
      funext i
      fin_cases i <;> simp [a, σ, Equiv.swap_apply_def]

/-- The physical inverse-log profile retains exactly the same signed-permutation blindness as
its scalar word coefficient. -/
theorem suzukiGradeProfile_hyperoctahedral_invariant
    {k : ℕ} (ν : Fin k → Nat.Primes × ℕ) (ε η : Fin k → Bool)
    (σ : Equiv.Perm (Fin k)) (C L : ℝ) :
    suzukiGradeProfile
        (C * suzukiWordCoefficient k (fun i => (ν (σ i), ε i))) k L =
      suzukiGradeProfile
        (C * suzukiWordCoefficient k (fun i => (ν i, η i))) k L := by
  rw [suzukiWordCoefficient_hyperoctahedral_invariant]

end

end GaloisForLFunctions.RHTower
