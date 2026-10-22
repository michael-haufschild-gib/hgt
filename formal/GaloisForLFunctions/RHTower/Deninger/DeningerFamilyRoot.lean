import GaloisForLFunctions.RHTower.Deninger.DeningerFamilyHomology

/-!
# The scheduled roots in the colimit

At each stage the scheduled member acquires the scheduled root, which becomes the new value of the
family at that index, so in the colimit the image of a scheduled member is the corresponding power
of the image of its successor.

* `deningerFamilyEmbed_root` : the root at a stage.
* `deningerFamilyColimit_root` : the root in the colimit.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- **The scheduled member acquires the scheduled root at the next stage.** -/
theorem deningerFamilyEmbed_root (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ) :
    ((deningerFamilyTower S₀ sched (n + 1)).fam (sched n).1) ^ (sched n).2 =
      deningerFamilyEmbed S₀ sched n ((deningerFamilyTower S₀ sched n).fam (sched n).1) := by
  have hfam : (deningerFamilyTower S₀ sched (n + 1)).fam (sched n).1 =
      deningerRootElt (deningerFamilyTower S₀ sched n).carrier
        ((deningerFamilyTower S₀ sched n).fam (sched n).1) (sched n).2 := by
    show (if (sched n).1 = (sched n).1 then _ else _) = _
    rw [if_pos rfl]
  rw [hfam]
  exact deningerRootElt_zpow (deningerFamilyTower S₀ sched n).carrier
    ((deningerFamilyTower S₀ sched n).fam (sched n).1) (sched n).2

/-- **The scheduled root in the colimit.** -/
theorem deningerFamilyColimit_root (S₀ : DeningerFamilyStage.{u}) (sched : ℕ → ℕ × ℤ) (n : ℕ) :
    (deningerFamilyIota S₀ sched (n + 1)
        ((deningerFamilyTower S₀ sched (n + 1)).fam (sched n).1)) ^ (sched n).2 =
      deningerFamilyIota S₀ sched n ((deningerFamilyTower S₀ sched n).fam (sched n).1) := by
  rw [← map_zpow, deningerFamilyEmbed_root, deningerFamilyIota_step]

end RootAdjunction

end RHTower
