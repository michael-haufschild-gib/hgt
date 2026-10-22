import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.RHTower.LevinsonOddFiberDensity
import GaloisForLFunctions.RHTower.XiHorizontalCollisionChargeEndpoint
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixShellPrincipalIdeal

/-!
# Sequential-touch alternatives for arithmetic census processes

Closed applications of the one-touch-at-a-time mechanism from arXiv:2603.03257 to monotone
integer-valued processes already present in the corpus.
-/

namespace RHTower

/-- Across `t` successive integer height samples, the odd Xi-fibre census either gains at least
`t` or one unit-height step adds no odd-fibre contribution. -/
theorem xiOddFiberCount_grows_or_exists_integer_stall (N t : ℕ) :
    xiOddFiberCount (N : ℝ) + t ≤ xiOddFiberCount (N + t : ℕ) ∨
      ∃ i < t,
        xiOddFiberCount (N + (i + 1) : ℕ) = xiOddFiberCount (N + i : ℕ) := by
  have hmono : Monotone (fun i : ℕ ↦ xiOddFiberCount (N + i : ℕ)) := by
    intro i j hij
    apply xiOddFiberCount_mono
    exact_mod_cast Nat.add_le_add_left hij N
  simpa [Nat.add_assoc] using
    (GaloisForLFunctions.HTGeometry.accumulates_touches_or_exists_stall
      (fun i : ℕ ↦ xiOddFiberCount (N + i : ℕ)) t hmono)

/-- Across `t` successive integer height samples, horizontal Xi collision charge either gains at
least `t` or one unit-height step creates no new multiplicity-weighted collision. -/
theorem xiHorizontalCollisionCharge_grows_or_exists_integer_stall (N t : ℕ) :
    xiHorizontalCollisionCharge (N : ℝ) + t ≤ xiHorizontalCollisionCharge (N + t : ℕ) ∨
      ∃ i < t,
        xiHorizontalCollisionCharge (N + (i + 1) : ℕ) =
          xiHorizontalCollisionCharge (N + i : ℕ) := by
  have hmono : Monotone (fun i : ℕ ↦ xiHorizontalCollisionCharge (N + i : ℕ)) := by
    intro i j hij
    apply xiHorizontalCollisionCharge_mono
    exact_mod_cast Nat.add_le_add_left hij N
  simpa [Nat.add_assoc] using
    (GaloisForLFunctions.HTGeometry.accumulates_touches_or_exists_stall
      (fun i : ℕ ↦ xiHorizontalCollisionCharge (N + i : ℕ)) t hmono)

/-- Across `t` consecutive integer scales, the base-six shell depth either rises by at least `t`
or one scale increment remains in the same shell. -/
theorem deningerGammaSixShellDepth_grows_or_exists_stall (N t : ℕ) :
    deningerGammaSixShellDepth N + t ≤ deningerGammaSixShellDepth (N + t) ∨
      ∃ i < t,
        deningerGammaSixShellDepth (N + (i + 1)) =
          deningerGammaSixShellDepth (N + i) := by
  have hmono : Monotone (fun i ↦ deningerGammaSixShellDepth (N + i)) := by
    intro i j hij
    exact deningerGammaSixShellDepth_mono (Nat.add_le_add_left hij N)
  simpa [Nat.add_assoc] using
    (GaloisForLFunctions.HTGeometry.accumulates_touches_or_exists_stall
      (fun i ↦ deningerGammaSixShellDepth (N + i)) t hmono)

/-- Iterating the base-six Wold coordinate collects exactly one new shell per step. -/
theorem deningerGammaSixShellDepth_iterate_wold (n t : ℕ) :
    deningerGammaSixShellDepth ((deningerGammaSixWoldCoordinate^[t]) n) =
      deningerGammaSixShellDepth n + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', deningerGammaSixShellDepth_wold, ih]
      omega

/-- Iterating the base-six Wold coordinate retains exactly a `1 / 6` fraction of its shell
eigenvalue at every step. -/
theorem deningerGammaSixShellEigenvalue_iterate_wold (n t : ℕ) :
    deningerGammaSixShellEigenvalue ((deningerGammaSixWoldCoordinate^[t]) n) =
      (1 / 6 : ℝ) ^ t * deningerGammaSixShellEigenvalue n := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply', deningerGammaSixShellEigenvalue_wold, ih, pow_succ]
      ring

end RHTower
