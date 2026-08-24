import GaloisForLFunctions.RHTower.EulerCutoffConstraintAlgebra
import GaloisForLFunctions.RHTower.RouteRFixedTraceTailRoos

/-!
# No stagewise Euler-cutoff exhaustion of the tail--Roos tower

The finite Euler cutoff tower has surjective bonding maps.  The fixed-tail Roos tower does not:
zero-prepending misses every summable sequence with a nonzero head coordinate.  A levelwise
surjective natural transformation carries surjective source bonds to surjective target bonds.
Consequently the tail--Roos obstruction cannot be the ordinary stagewise quotient of the Euler
cutoff tower.

This is a source-exhaustion no-go, not an RH criterion.  Any arithmetic comparison capable of
carrying the completion defect must retain a relative/mapping-cone component; an ordinary
commuting tower of epimorphisms necessarily launders precisely the nonzero Roos class.
-/

open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- Surjective bonds descend through a levelwise-surjective natural transformation. -/
theorem targetBond_surjective_of_surjective_towerDescent
    {A B : ℕ → Type*}
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℂ (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module ℂ (B n)]
    (sourceBond : ∀ n, A (n + 1) →ₗ[ℂ] A n)
    (targetBond : ∀ n, B (n + 1) →ₗ[ℂ] B n)
    (comparison : ∀ n, A n →ₗ[ℂ] B n)
    (hsource : ∀ n, Function.Surjective (sourceBond n))
    (hcomparison : ∀ n, Function.Surjective (comparison n))
    (hnatural : ∀ n (x : A (n + 1)),
      comparison n (sourceBond n x) =
        targetBond n (comparison (n + 1) x)) :
    ∀ n, Function.Surjective (targetBond n) := by
  intro n y
  obtain ⟨x, hx⟩ := hcomparison n y
  obtain ⟨x', hx'⟩ := hsource n x
  refine ⟨comparison (n + 1) x', ?_⟩
  calc
    targetBond n (comparison (n + 1) x') =
        comparison n (sourceBond n x') := (hnatural n x').symm
    _ = comparison n x := by rw [hx']
    _ = y := hx

/-- Every fixed-tail restricted Roos bond misses a one-head summable sequence. -/
theorem routeRTailRoosRestrictedBond_not_surjective (n : ℕ) :
    ¬Function.Surjective (routeRTailRoosRestrictedBond n) := by
  intro hsurjective
  let head : routeRSummableSequenceIdeal :=
    routeRDiagonalMismatchInIdeal (fun _ => 1) n
  obtain ⟨x, hx⟩ := hsurjective head
  have hzero := congrArg
    (fun z : routeRSummableSequenceIdeal => (z : RouteRTraceSequence) 0) hx
  simp [routeRTailRoosRestrictedBond, head,
    routeRDiagonalMismatchInIdeal] at hzero

/-- The actual surjective finite Euler cutoff tower cannot exhaust the fixed-tail Roos tower by
levelwise-surjective commuting comparison maps.  Thus the completion anomaly is not an ordinary
stagewise quotient of finite Euler constraints. -/
theorem no_eulerCutoff_stagewiseSurjective_tailRoosDescent :
    ¬ ∃ comparison : ∀ n,
        (AddMonoidAlgebra ℂ ℂ ⧸ GaloisForLFunctions.RHTower.eulerJ n) →ₗ[ℂ]
          routeRSummableSequenceIdeal,
      (∀ n, Function.Surjective (comparison n)) ∧
      (∀ n (x : AddMonoidAlgebra ℂ ℂ ⧸
          GaloisForLFunctions.RHTower.eulerJ (n + 1)),
        comparison n
            ((GaloisForLFunctions.RHTower.eulerCutoffTransition
              (N := n) (M := n + 1)
              (Nat.le_succ n)).toLinearMap x) =
          routeRTailRoosRestrictedBond n (comparison (n + 1) x)) := by
  rintro ⟨comparison, hcomparison, hnatural⟩
  have htarget := targetBond_surjective_of_surjective_towerDescent
    (fun n => (GaloisForLFunctions.RHTower.eulerCutoffTransition
      (N := n) (M := n + 1)
      (Nat.le_succ n)).toLinearMap)
    routeRTailRoosRestrictedBond comparison
    (fun n => GaloisForLFunctions.RHTower.eulerCutoffTransition_surjective
      (Nat.le_succ n))
    hcomparison hnatural 0
  exact routeRTailRoosRestrictedBond_not_surjective 0 htarget

end

end RHTower
