import GaloisForLFunctions.RHTower.SuzukiVolterraCartesianPhaseDefect

/-!
# Odd-phase diagonal no-go

For every reflection-compatible causal operator, the self-adjoint phase coordinate sends an odd
source to the even sector. Its diagonal quadratic readout therefore vanishes identically. Any
source-faithful orientation mechanism must use an off-diagonal or affine channel.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The phase quadratic form vanishes on every odd source under a reflection-compatible causal
operator. Thus a diagonal phase energy cannot orient the signed connection current. -/
theorem inner_volterraPhase_apply_odd_eq_zero
    {T R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hinv : R * R = 1) (h : R * T * R = adjoint T) {u : H} (hu : R u = -u) :
    inner ℂ u ((volterraPhase T) u) = 0 := by
  have hv : R ((volterraPhase T) u) = (volterraPhase T) u :=
    volterraPhase_apply_odd hR hinv h hu
  have hinner : inner ℂ (R u) ((volterraPhase T) u) =
      inner ℂ u (R ((volterraPhase T) u)) := by
    calc
      inner ℂ (R u) ((volterraPhase T) u) =
          inner ℂ ((adjoint R) u) ((volterraPhase T) u) := by
        rw [hR.adjoint_eq]
      _ = inner ℂ u (R ((volterraPhase T) u)) :=
        ContinuousLinearMap.adjoint_inner_left R _ _
  have hneg : -(inner ℂ u ((volterraPhase T) u)) =
      inner ℂ u ((volterraPhase T) u) := by
    simpa [hu, hv] using hinner
  let z : ℂ := inner ℂ u ((volterraPhase T) u)
  have hnegz : -z = z := hneg
  have hsum : z + z = 0 := by
    calc
      z + z = -z + z := by rw [hnegz]
      _ = 0 := neg_add_cancel z
  have htwo : (2 : ℂ) * z = 0 := by
    calc
      (2 : ℂ) * z = z + z := by ring
      _ = 0 := hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end

end RHTower
