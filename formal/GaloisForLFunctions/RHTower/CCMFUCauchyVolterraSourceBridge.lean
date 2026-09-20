import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalRemainderVariation
import GaloisForLFunctions.RHTower.CCMFUCauchyVolterraLiteralProfile

/-!
# Literal source attachment for the CCM-FU Cauchy--Volterra profile

The positive Cauchy--Volterra profile is not an auxiliary surrogate: after the forced
square-root-clock normalization, it is exactly the literal Suzuki critical multiplier on every
finite arithmetic cell.  This identity retains the prime--polar cell coefficient unchanged.
-/

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- The literal Suzuki critical multiplier, divided by its exact cell coordinate, is the
Cauchy--Volterra FU profile at the square-root clock. -/
theorem suzukiCheckpointCriticalTriangularMultiplier_div_eq_cauchyVolterraFUProfile
    (H : ℝ) (n : ℕ) :
    suzukiCheckpointCriticalTriangularMultiplier H n / ((n + 3 : ℕ) : ℝ) =
      cauchyVolterraFUProfile H (Real.sqrt ((n + 3 : ℕ) : ℝ)) := by
  let x : ℝ := (n : ℝ) + 3
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlogsqrt : Real.log (Real.sqrt x) = Real.log x / 2 :=
    Real.log_sqrt hx.le
  unfold suzukiCheckpointCriticalTriangularMultiplier
    ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
    cauchyVolterraFUProfile
  simp only [Nat.cast_add, Nat.cast_ofNat]
  change Real.sqrt x * (32 / Real.log x ^ 3 * (1 - Real.log x / H)) / x =
    4 / (Real.sqrt x * Real.log (Real.sqrt x) ^ 3) *
      (1 - 2 * Real.log (Real.sqrt x) / H)
  rw [hlogsqrt]
  have hxsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  field_simp [hx.ne', hsqrt.ne']
  rw [hxsq]
  ring

end

end RHTower
