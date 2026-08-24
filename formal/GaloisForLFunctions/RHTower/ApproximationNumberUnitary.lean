import GaloisForLFunctions.RHTower.SoninEulerFiniteL2Lower
import GaloisForLFunctions.RHTower.SchattenApproximation

/-!
# Unitary invariance of approximation numbers

Unitary conjugation preserves finite-rank approximation sets and operator norm.  Consequently it
preserves every approximation number exactly.  This is the coordinate-free transport needed by
spectral normal-form arguments.
-/

namespace RHTower

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A rank bound survives unitary conjugation. -/
theorem HasRankLE.unitaryPush {F : H →L[ℂ] H} {n : ℕ}
    (hF : HasRankLE F n) (u : H ≃ₗᵢ[ℂ] K) :
    HasRankLE (unitaryPush u F) n := by
  rcases hF with ⟨V, hVfinite, hVrank, hFV⟩
  letI : FiniteDimensional ℂ V := hVfinite
  let W : Submodule ℂ K := V.map (u : H →ₗ[ℂ] K)
  have hWfinite : FiniteDimensional ℂ W := by
    have hres : ∀ x ∈ V, (u : H →ₗ[ℂ] K) x ∈ W :=
      fun x hx => Submodule.mem_map_of_mem hx
    refine FiniteDimensional.of_surjective
      ((u : H →ₗ[ℂ] K).restrict hres) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨W, hWfinite, ?_, ?_⟩
  · exact (Submodule.finrank_map_le (u : H →ₗ[ℂ] K) V).trans hVrank
  · intro x
    refine ⟨F (u.symm x), hFV (u.symm x), ?_⟩
    rfl

/-- One direction of unitary invariance, obtained by transporting every finite-rank approximant. -/
theorem approxNumber_unitaryPush_le (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (n : ℕ) :
    approxNumber (unitaryPush u T) n ≤ approxNumber T n := by
  refine le_csInf (approxNumber_set_nonempty T n) ?_
  rintro r ⟨F, hF, rfl⟩
  calc
    approxNumber (unitaryPush u T) n ≤
        ‖unitaryPush u T - unitaryPush u F‖ :=
      approxNumber_le _ _ _ (hF.unitaryPush u)
    _ = ‖unitaryPush u (T - F)‖ := by rw [unitaryPush_sub]
    _ = ‖T - F‖ := norm_unitaryPush u (T - F)

/-- Approximation numbers are exactly invariant under unitary conjugation. -/
theorem approxNumber_unitaryPush (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (n : ℕ) :
    approxNumber (unitaryPush u T) n = approxNumber T n := by
  apply le_antisymm (approxNumber_unitaryPush_le u T n)
  have h := approxNumber_unitaryPush_le u.symm (unitaryPush u T) n
  rwa [unitaryPush_symm_unitaryPush] at h

end

end RHTower
