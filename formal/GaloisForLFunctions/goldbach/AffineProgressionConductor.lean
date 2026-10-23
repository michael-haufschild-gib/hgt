import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-! Affine substitution multiplies the progression step by its slope. -/

set_option autoImplicit false

namespace GaloisForLFunctions.Goldbach

/-- The image of `r + mℤ` under `a ↦ b * a - T`. -/
def affineProgression (b m r T : ℤ) : Set ℤ :=
  Set.range fun k : ℤ => b * (r + m * k) - T

/-- The full step is `b * m`, including when the slope is fixed. -/
theorem mem_affineProgression_iff_dvd (b m r T h : ℤ) :
    h ∈ affineProgression b m r T ↔ b * m ∣ h - (b * r - T) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      b * (r + m * k) - T = (b * r - T) + b * m * k := by ring
      _ = h := by rw [← hk]; ring

/-- Affine progressions are exactly the corresponding residue classes. -/
theorem mem_affineProgression_iff_modEq (b m r T h : ℤ) :
    h ∈ affineProgression b m r T ↔ Int.ModEq (b * m) (b * r - T) h := by
  rw [Int.modEq_iff_dvd, mem_affineProgression_iff_dvd]

/-- Translation preserves the progression exactly for multiples of its full step. -/
theorem affineProgression_period_iff (b m r T δ : ℤ) :
    (∀ h : ℤ, h + δ ∈ affineProgression b m r T ↔
      h ∈ affineProgression b m r T) ↔ b * m ∣ δ := by
  constructor
  · intro hperiod
    have hbase : b * r - T ∈ affineProgression b m r T := ⟨0, by ring⟩
    have hshift := (hperiod (b * r - T)).mpr hbase
    rcases (mem_affineProgression_iff_dvd b m r T _).mp hshift with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      δ = (b * r - T + δ) - (b * r - T) := by ring
      _ = b * m * k := hk
  · rintro ⟨k, hk⟩ h
    rw [mem_affineProgression_iff_dvd, mem_affineProgression_iff_dvd]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j - k, ?_⟩
      calc
        h - (b * r - T) = (h + δ - (b * r - T)) - δ := by ring
        _ = b * m * j - b * m * k := by rw [hj, hk]
        _ = b * m * (j - k) := by ring
    · rintro ⟨j, hj⟩
      refine ⟨j + k, ?_⟩
      calc
        h + δ - (b * r - T) = (h - (b * r - T)) + δ := by ring
        _ = b * m * j + b * m * k := by rw [hj, hk]
        _ = b * m * (j + k) := by ring

#print axioms mem_affineProgression_iff_dvd
#print axioms mem_affineProgression_iff_modEq
#print axioms affineProgression_period_iff

end GaloisForLFunctions.Goldbach
