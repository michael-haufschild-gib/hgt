import GaloisForLFunctions.HTGeometry.HankelTangentSpace
import GaloisForLFunctions.HTGeometry.HankelSecantUnmixed

/-!
# `Sing(C_k) = C_{k+1}`

The Hankel secant variety `V_{s+1} = V(I_{s+1}) ⊆ K^N` (`2(s+1) < N`) has dimension `2(s+1)`, and a
point `p ∈ V_{s+1}` is smooth — its Zariski tangent space has dimension `2(s+1)` — exactly when
`p ∉ V_s`; on `V_s` the tangent space is all of `K^N`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type) [Field K] [CharZero K]

/-- **The Hankel secant variety has dimension `2r`.** -/
theorem ringKrullDim_hankelSecantRing {N r : ℕ} (hN : 2 * r ≤ N) :
    ringKrullDim (HankelSecantRing K N r) = ((2 * r : ℕ) : WithBot ℕ∞) := by
  haveI : Infinite K := CharZero.infinite K
  refine le_antisymm (ringKrullDim_hankelSecantQuotient_le K hN) ?_
  obtain ⟨rs, hlen, hreg⟩ := exists_isRegular_finiteHankelSecantIdeal K N r hN
  have hring := isRingRegularSeq_map_mk (RHTower.finiteHankelSecantIdeal K N r) rs hreg
  have := length_le_ringKrullDim_of_isRingRegularSeq _ hring
  rwa [List.length_map, hlen] at this

/-- **`Sing(C_k) = C_{k+1}`.**  A point of `V_{s+1}` has a tangent space of dimension
`dim V_{s+1} = 2(s+1)` exactly when it lies off `V_s`; on `V_s` every direction is tangent. -/
theorem hankel_smooth_iff {N s : ℕ} (hsN : 2 * (s + 1) < N) (p : Fin N → K)
    (hp : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N (s + 1), eval p g = 0) :
    (Module.finrank K (zariskiTangent (RHTower.finiteHankelSecantIdeal K N (s + 1)) p) =
        2 * (s + 1) ↔ ∃ g ∈ RHTower.finiteHankelSecantIdeal K N s, eval p g ≠ 0) ∧
      ((∀ g ∈ RHTower.finiteHankelSecantIdeal K N s, eval p g = 0) →
        zariskiTangent (RHTower.finiteHankelSecantIdeal K N (s + 1)) p = ⊤) ∧
      ringKrullDim (HankelSecantRing K N (s + 1)) = ((2 * (s + 1) : ℕ) : WithBot ℕ∞) := by
  refine ⟨⟨fun hdim => ?_, finrank_zariskiTangent_hankel K hsN p hp⟩,
    zariskiTangent_hankel_eq_top K p, ringKrullDim_hankelSecantRing K hsN.le⟩
  by_contra hall
  push Not at hall
  rw [zariskiTangent_hankel_eq_top K p hall, finrank_top, Module.finrank_fin_fun] at hdim
  omega

end

end GaloisForLFunctions.HTGeometry
