import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# Sequential sharpness for prime counting

Closed application of the sequential-touch mechanism from arXiv:2603.03257 to the corpus's
monotone prime-counting function.
-/

namespace GaloisForLFunctions.HTGeometry

/-- On an integer block, either prime counting increases at every possible unit rate, or a
specific unit step has no new prime.  The first branch is exact because a unit interval can add at
most one prime. -/
theorem primeCounting_fullGrowth_or_exists_stall (N t : ℕ) :
    Nat.primeCounting (N + t) = Nat.primeCounting N + t ∨
      ∃ i < t, Nat.primeCounting (N + (i + 1)) = Nat.primeCounting (N + i) := by
  have hupper : ∀ i : ℕ, Nat.primeCounting (N + i) ≤ Nat.primeCounting N + i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        calc
          Nat.primeCounting (N + (i + 1)) = Nat.primeCounting ((N + i) + 1) := by
            exact congrArg Nat.primeCounting (by omega)
          _ ≤ Nat.primeCounting (N + i) + 1 := primeCounting_succ_le (N + i)
          _ ≤ Nat.primeCounting N + (i + 1) := by
            simpa [Nat.add_assoc] using Nat.add_le_add_right ih 1
  rcases accumulates_touches_or_exists_stall
      (fun i ↦ Nat.primeCounting (N + i)) t
      (fun _i _j hij ↦ primeCounting_mono (Nat.add_le_add_left hij N)) with hgrow | hstall
  · left
    have := hupper t
    simp only [Nat.add_zero] at hgrow
    omega
  · right
    simpa [Nat.add_assoc] using hstall

end GaloisForLFunctions.HTGeometry
