import GaloisForLFunctions.RHTower.Deninger.DeningerDomainSpace
import GaloisForLFunctions.HTGeometry.DbarCoordinateProduct

/-!
# The coordinate divisor and its inclusion

The divisor of the last coordinate in an open subset of `ℂ^{n+1}` is the image of an open subset of
`ℂ^n` under the map appending a zero.  That map is a closed embedding, it is complex linear, and it
commutes with the coordinate slices used to define the antiholomorphic derivatives — so pulling a
form back along it is again a form, and its Dolbeault operator is the restriction of the ambient
one.

* `RHTower.deningerDivisorMap` : appending a zero last coordinate.
* `RHTower.deningerDivisorInclusion` : the inclusion of the divisor as a map of spaces.
* `RHTower.dzbarAt_comp_divisorMap` : the antiholomorphic derivatives restrict.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite TopCat Complex HTGeometry

section DivisorMap

variable {n : ℕ}

/-- **Appending a zero last coordinate**: the parametrisation of the divisor of the last
coordinate. -/
def deningerDivisorMap (w : Fin n → ℂ) : Fin (n + 1) → ℂ := Fin.snoc w 0

@[simp] theorem deningerDivisorMap_castSucc (w : Fin n → ℂ) (j : Fin n) :
    deningerDivisorMap w j.castSucc = w j := by simp [deningerDivisorMap]

@[simp] theorem deningerDivisorMap_last (w : Fin n → ℂ) :
    deningerDivisorMap w (Fin.last n) = 0 := by simp [deningerDivisorMap]

theorem deningerDivisorMap_injective : Function.Injective (deningerDivisorMap (n := n)) := by
  intro w w' h
  funext j
  rw [← deningerDivisorMap_castSucc w j, ← deningerDivisorMap_castSucc w' j, h]

theorem continuous_deningerDivisorMap : Continuous (deningerDivisorMap (n := n)) := by
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ ?_ i
  · simpa only [deningerDivisorMap_last] using continuous_const
  · intro j
    simpa only [deningerDivisorMap_castSucc] using (continuous_apply j)

/-- Appending a zero commutes with updating a coordinate. -/
theorem deningerDivisorMap_update (w : Fin n → ℂ) (j : Fin n) (t : ℂ) :
    deningerDivisorMap (Function.update w j t)
      = Function.update (deningerDivisorMap w) j.castSucc t := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [deningerDivisorMap_last,
      Function.update_of_ne (by exact fun h => absurd h.symm (Fin.castSucc_lt_last j).ne),
      deningerDivisorMap_last]
  · intro k
    rw [deningerDivisorMap_castSucc]
    by_cases hjk : k = j
    · subst hjk
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hjk,
        Function.update_of_ne (fun h => hjk (Fin.castSucc_injective n h)),
        deningerDivisorMap_castSucc]

/-- **The antiholomorphic derivatives restrict to the divisor**: the slice of a pullback is the
pullback of a slice, so `∂̄_j` of the restriction is `∂̄_{j}` of the function read at the divisor. -/
theorem dzbarAt_comp_divisorMap (F : (Fin (n + 1) → ℂ) → ℂ) (j : Fin n) (w : Fin n → ℂ) :
    dzbarAt (fun x => F (deningerDivisorMap x)) j w
      = dzbarAt F j.castSucc (deningerDivisorMap w) := by
  have hslice : dbarSlice (fun x => F (deningerDivisorMap x)) j w
      = dbarSlice F j.castSucc (deningerDivisorMap w) := by
    funext t
    show F (deningerDivisorMap (Function.update w j t))
      = F (Function.update (deningerDivisorMap w) j.castSucc t)
    rw [deningerDivisorMap_update]
  show dzbar (dbarSlice (fun x => F (deningerDivisorMap x)) j w) (w j) = _
  rw [hslice]
  show _ = dzbar (dbarSlice F j.castSucc (deningerDivisorMap w))
    (deningerDivisorMap w j.castSucc)
  rw [deningerDivisorMap_castSucc]

/-- A form pulled back to the divisor. -/
noncomputable def deningerDivisorPullback (g : SetForm (n + 1)) : SetForm n :=
  fun S w => if S = ∅ then g ∅ (deningerDivisorMap w) else 0

@[simp] theorem deningerDivisorPullback_empty (g : SetForm (n + 1)) (w : Fin n → ℂ) :
    deningerDivisorPullback g ∅ w = g ∅ (deningerDivisorMap w) := if_pos rfl

@[simp] theorem deningerDivisorPullback_ne (g : SetForm (n + 1)) {S : Finset (Fin n)}
    (hS : S ≠ ∅) (w : Fin n → ℂ) : deningerDivisorPullback g S w = 0 := if_neg hS

theorem deningerDivisorPullback_smooth {g : SetForm (n + 1)} (hg : SmoothSetForm g) :
    SmoothSetForm (deningerDivisorPullback g) := by
  intro S
  by_cases hS : S = ∅
  · subst hS
    refine (hg ∅).comp ?_
    exact contDiff_pi.2 fun i => Fin.lastCases (by
      simpa only [deningerDivisorMap_last] using contDiff_const) (fun j => by
      simpa only [deningerDivisorMap_castSucc] using contDiff_coord j) i
  · simpa only [show deningerDivisorPullback g S = fun _ => (0 : ℂ) from
      funext fun w => deningerDivisorPullback_ne g hS w] using contDiff_const

theorem deningerDivisorPullback_deg (g : SetForm (n + 1)) :
    SetFormDeg 0 (deningerDivisorPullback g) := by
  intro S hS w
  exact deningerDivisorPullback_ne g (fun h => hS (by rw [h]; rfl)) w

/-- **The Dolbeault operator of a pullback reads the ambient one.**  In degree zero only the terms
of a singleton index survive, and each is the corresponding ambient derivative at the divisor. -/
theorem setDbar_deningerDivisorPullback (g : SetForm (n + 1)) (S : Finset (Fin n))
    (w : Fin n → ℂ) :
    setDbar (deningerDivisorPullback g) S w
      = ∑ k ∈ S, insertSign k (S.erase k) *
        (if S.erase k = ∅ then dzbarAt (g ∅) k.castSucc (deningerDivisorMap w) else 0) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  refine congrArg (fun z => insertSign k (S.erase k) * z) ?_
  by_cases hk : S.erase k = ∅
  · rw [if_pos hk, hk,
      show deningerDivisorPullback g ∅ = fun w => g ∅ (deningerDivisorMap w) from
        funext fun w => deningerDivisorPullback_empty g w,
      dzbarAt_comp_divisorMap]
  · rw [if_neg hk,
      show deningerDivisorPullback g (S.erase k) = fun _ => (0 : ℂ) from
        funext fun w => deningerDivisorPullback_ne g hk w]
    exact dzbarAt_zero k w

end DivisorMap

end RHTower
