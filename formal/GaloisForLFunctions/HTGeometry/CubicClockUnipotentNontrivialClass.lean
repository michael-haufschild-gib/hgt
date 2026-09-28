import GaloisForLFunctions.HTGeometry.CubicClockExtensionLiftingObstruction
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# A split extension with nonzero cubic-clock lifting class

The nontriviality example of the cubic clock extension lifting obstruction, realized as a genuine
`CubicClockCompletion`: `X = I = Q = ℂ`, `E = ℂ²` with ideal the first coordinate, quotient the
second coordinate, identity source clock, and unipotent total clock `D_E(v, w) = (v + w, w)`.
The underlying vector-space extension splits, yet the cubic-clock lifting class of *every* lift
of the identity landing is nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

namespace UnipotentCubicClock

/-- The completion ideal: the first coordinate `{(v, 0)}`. -/
def ideal : Submodule ℂ (ℂ × ℂ) := LinearMap.ker (LinearMap.snd ℂ ℂ ℂ)

theorem mem_ideal (z : ℂ × ℂ) : z ∈ ideal ↔ z.2 = 0 := LinearMap.mem_ker

theorem ideal_le_comap : ideal ≤ ideal.comap unipotentCompletionClock := by
  intro z hz
  rw [Submodule.mem_comap, mem_ideal, unipotentCompletionClock_apply]
  exact (mem_ideal z).mp hz

/-- The unipotent clock preserves the ideal and induces the quotient clock. -/
def quotientClock : ((ℂ × ℂ) ⧸ ideal) →ₗ[ℂ] ((ℂ × ℂ) ⧸ ideal) :=
  ideal.mapQ ideal unipotentCompletionClock ideal_le_comap

/-- Identity landing in the second coordinate. -/
def landing : ℂ →ₗ[ℂ] ((ℂ × ℂ) ⧸ ideal) :=
  ideal.mkQ.comp (LinearMap.inr ℂ ℂ ℂ)

theorem mkQ_eq_mkQ_iff (y z : ℂ × ℂ) : ideal.mkQ y = ideal.mkQ z ↔ y.2 = z.2 := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_ideal,
    Prod.snd_sub, sub_eq_zero]

/-- The split unipotent completion as a cubic clock completion datum. -/
def completion : CubicClockCompletion (X := ℂ) (E := ℂ × ℂ) where
  ideal := ideal
  sourceClock := LinearMap.id
  totalClock := unipotentCompletionClock
  quotientClock := quotientClock
  quotientLanding := landing
  quotientClock_mkQ y := by
    simp [quotientClock, Submodule.mapQ_apply]
  quotientLanding_cubic := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, linearClockCube_apply, landing, quotientClock,
      Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
    change ideal.mkQ _ = ideal.mkQ _
    rw [mkQ_eq_mkQ_iff]
    simp

/-- The ordinary vector-space extension splits: the second-coordinate inclusion is a lift. -/
def splitLift : completion.Lift where
  toLinearMap := LinearMap.inr ℂ ℂ ℂ
  mkQ_comp := rfl

/-- **Nontriviality.** No lift of the identity landing is cubic-clock equivariant. -/
theorem cubicDefect_ne_zero (F : completion.Lift) : F.cubicDefect ≠ 0 := by
  intro hF
  have h1 : F.ambientCubicDefect 1 = 0 := by
    have := congrArg (fun G : ℂ →ₗ[ℂ] completion.ideal => (G 1 : ℂ × ℂ)) hF
    exact this
  have hsnd : (F.toLinearMap 1).2 = 1 := by
    have := LinearMap.congr_fun F.mkQ_comp 1
    change ideal.mkQ (F.toLinearMap 1) = ideal.mkQ ((0 : ℂ), (1 : ℂ)) at this
    simpa using (mkQ_eq_mkQ_iff _ _).mp this
  rw [CubicClockCompletion.Lift.ambientCubicDefect_apply] at h1
  have hfst := congrArg Prod.fst h1
  change ((F.toLinearMap 1).1 + (F.toLinearMap 1).2 + (F.toLinearMap 1).2 +
      (F.toLinearMap 1).2) - (F.toLinearMap 1).1 = 0 at hfst
  rw [hsnd] at hfst
  have : (3 : ℂ) = 0 := by linear_combination hfst
  norm_num at this

/-- **Nontriviality.** The cubic-clock lifting class of every lift is nonzero, although the
underlying linear extension splits (`splitLift`). -/
theorem cubicLiftingClass_ne_zero (F : completion.Lift) : F.cubicLiftingClass ≠ 0 := by
  intro h
  obtain ⟨H, hH⟩ := (CubicClockCompletion.Lift.cubicLiftingClass_eq_zero_iff F).mp h
  exact cubicDefect_ne_zero _ hH

end UnipotentCubicClock

end GaloisForLFunctions.HTGeometry
