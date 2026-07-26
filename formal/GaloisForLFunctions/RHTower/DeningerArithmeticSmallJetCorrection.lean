import GaloisForLFunctions.RHTower.DeningerArithmeticLocalQuotientOpenness

/-!
# Small representatives of distant finite jet packets

For every compact-open zero-neighborhood there is a finite Xi window such that any entire source
whose jets vanish in that window can be changed by an actual Xi coboundary into the prescribed
neighborhood.  The corrected source retains every Xi jet, including all jets outside the window.

This is the recursive approximation step for unconditional global Xi-jet interpolation.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/--
An entire source vanishing on a sufficiently large finite Xi packet has an arbitrarily small
representative modulo Xi multiplication.
-/
theorem exists_deningerCompactOpen_small_Xi_correction
    {A : Set DeningerCompactOpenEntire}
    (hA : A ∈ 𝓝 0) :
    ∃ r : ℕ, ∀ F : DeningerCompactOpenEntire,
      (∀ (rho :
          ↥(deningerXiSupportClosedBallFinset (r + 2)))
          (k : DeningerArithmeticJetIndex rho.1),
        deningerCompactOpenJet
            (xiSpectralPointSupport rho.1) k F = 0) →
        ∃ Q : DeningerCompactOpenEntire,
          F - deningerCompactOpenXiMul Q ∈ A := by
  obtain ⟨r, hr⟩ :=
    exists_deningerCompactOpen_ball_eventually_mem hA
  refine ⟨r, fun F hF => ?_⟩
  let S := deningerXiSupportClosedBallFinset (r + 2)
  have hfinite :
      deningerCompactOpenFiniteJets S F = 0 := by
    funext idx
    exact hF idx.1 idx.2
  have hrepresentative :
      deningerCompactOpenFiniteJetRepresentative S F = 0 := by
    rw [deningerCompactOpenFiniteJetRepresentative,
      ContinuousLinearMap.comp_apply, hfinite, map_zero]
  let Q : ℕ → DeningerCompactOpenEntire :=
    fun j =>
      deningerCompactOpenLocalXiQuotientTaylorApprox
        F (r + 1) j
  let G : ℕ → DeningerCompactOpenEntire :=
    fun j => F - deningerCompactOpenXiMul (Q j)
  have hGconv :
      TendstoLocallyUniformlyOn
        (fun j z => G j z) (fun _ => 0)
        atTop (Metric.ball 0 r) := by
    have hpeel :=
      deningerCompactOpenFiniteJetRepresentative_peeling
        F r
    simpa only [S, hrepresentative, sub_zero, G, Q,
      deningerCompactOpenXiMul_apply,
      deningerCompactOpenLocalXiQuotientTaylorApprox_apply,
      Pi.sub_apply] using hpeel
  obtain ⟨j, hj⟩ :=
    (hr G hGconv).exists
  exact ⟨Q j, hj⟩

/-- Small correction preserves the full Xi-jet family. -/
theorem deningerCompactOpenAllJets_sub_XiMul
    (F Q : DeningerCompactOpenEntire) :
    deningerCompactOpenAllJets
        (F - deningerCompactOpenXiMul Q) =
      deningerCompactOpenAllJets F := by
  rw [map_sub]
  have hzero :
      deningerCompactOpenAllJets
          (deningerCompactOpenXiMul Q) = 0 := by
    apply LinearMap.mem_ker.mp
    exact
      deningerCompactOpenXiRange_le_allJets_ker
        ⟨Q, rfl⟩
  rw [hzero, sub_zero]

end

end RHTower
