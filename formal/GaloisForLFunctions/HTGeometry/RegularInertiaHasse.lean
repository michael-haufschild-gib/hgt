import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.RegularInertiaAmplification

/-!
# Hasse separation by finite regular-inertia matrices

Finite cyclic regular representations are noncommutative local observations of an integral
translation charge.  Their complete profile is faithful, and every pair of unequal charges is
already separated by one finite permutation matrix.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite cyclic stages of order at least two. -/
abbrev RegularInertiaPlace := {n : ℕ // 2 ≤ n}

/-- Finite regular-inertia matrices form a Hasse family for integral translation charges. -/
def regularInertiaHasseFamily : HasseFamily ℤ RegularInertiaPlace where
  Local n := Matrix (ZMod n.1) (ZMod n.1) ℂ
  profile q n := regularInertia n.1 q
  profile_injective := by
    intro q r h
    apply (complete_marked_regularTower_injective q r).mp
    intro n hn
    exact congrFun h ⟨n, hn⟩

/-- Integral charges agree exactly when all finite regular-inertia matrices agree. -/
theorem regularInertia_congr_hasse_iff (q r : ℤ) :
    (∀ n : ℕ, 2 ≤ n → regularInertia n q = regularInertia n r) ↔ q = r :=
  complete_marked_regularTower_injective q r

/-- Unequal integral charges differ at one finite cyclic regular-representation stage. -/
theorem regularInertia_ne_iff_exists_finite_stage_ne (q r : ℤ) :
    q ≠ r ↔ ∃ n : ℕ, ∃ _hn : 2 ≤ n, regularInertia n q ≠ regularInertia n r := by
  rw [regularInertiaHasseFamily.ne_iff_exists_local_ne]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n.1, n.2, hn⟩
  · rintro ⟨n, hn, hne⟩
    exact ⟨⟨n, hn⟩, hne⟩

end


end GaloisForLFunctions.HTGeometry
