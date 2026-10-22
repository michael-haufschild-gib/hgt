import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCompactOpenNeighborhoods
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticDenseJets

/-!
# Local openness of the compact-open Xi quotient in jet coordinates

Finite continuous Hermite sections and local Xi-division give the missing inverse-topology
estimate for the descended all-jets map.  Given a quotient neighborhood, split it into two smaller
neighborhoods.  A finite jet representative lies in the first; after peeling by an actual Xi
coboundary, the residual lies in the second.

Consequently the compact-open arithmetic cohomology quotient embeds topologically in the full
product of multiplicity-bounded Xi jets.  No global infinite interpolation theorem is used.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/-- Restrict a full Xi-jet family to one flattened finite packet. -/
def deningerArithmeticFiniteJetRestriction
    (S : Finset XiDivisorSupport) :
    DeningerArithmeticJetProduct →L[ℂ]
      DeningerArithmeticFiniteJetValues S :=
  ContinuousLinearMap.pi fun idx =>
    (ContinuousLinearMap.proj idx.2 :
        (DeningerArithmeticJetIndex idx.1.1 → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj idx.1.1 :
        DeningerArithmeticJetProduct →L[ℂ]
          (DeningerArithmeticJetIndex idx.1.1 → ℂ))

@[simp]
theorem deningerArithmeticFiniteJetRestriction_apply
    (S : Finset XiDivisorSupport)
    (a : DeningerArithmeticJetProduct)
    (idx : DeningerArithmeticFiniteJetCoordinate S) :
    deningerArithmeticFiniteJetRestriction S a idx =
      a idx.1.1 idx.2 :=
  rfl

@[simp]
theorem deningerArithmeticFiniteJetRestriction_allJets
    (S : Finset XiDivisorSupport)
    (F : DeningerCompactOpenEntire) :
    deningerArithmeticFiniteJetRestriction S
        (deningerCompactOpenAllJets F) =
      deningerCompactOpenFiniteJets S F :=
  rfl

/--
Finite jet coordinates control every zero-neighborhood in compact-open arithmetic cohomology.

This is the constructive content of `[DAC_LOCAL_QUOTIENT_OPENNESS]`.
-/
theorem deningerCompactOpenH1AllJets_local_zero_control
    {U : Set DeningerArithmeticCompactOpenH1}
    (hU : U ∈ 𝓝 0) :
    ∃ n : ℕ,
      ∃ W :
          Set
            (DeningerArithmeticFiniteJetValues
              (deningerXiSupportClosedBallFinset (n + 2))),
        W ∈ 𝓝 0 ∧
          ∀ F : DeningerCompactOpenEntire,
            deningerCompactOpenFiniteJets
                (deningerXiSupportClosedBallFinset (n + 2)) F ∈ W →
              deningerArithmeticCompactOpenH1Class F ∈ U := by
  obtain ⟨V, hVopen, hVzero, hVV⟩ :=
    exists_open_nhds_zero_add_subset hU
  have hVnhds :
      V ∈ 𝓝 (0 : DeningerArithmeticCompactOpenH1) :=
    hVopen.mem_nhds hVzero
  let A : Set DeningerCompactOpenEntire :=
    deningerArithmeticCompactOpenH1Class ⁻¹' V
  have hA : A ∈ 𝓝 (0 : DeningerCompactOpenEntire) := by
    have hpre :=
      deningerArithmeticCompactOpenH1Class.continuous.continuousAt
        |>.preimage_mem_nhds hVnhds
    simpa only [map_zero, A] using hpre
  obtain ⟨n, hn⟩ :=
    exists_deningerCompactOpen_ball_eventually_mem hA
  let S := deningerXiSupportClosedBallFinset (n + 2)
  let W :
      Set (DeningerArithmeticFiniteJetValues S) :=
    deningerCompactOpenFiniteJetSection S ⁻¹' A
  have hW :
      W ∈
        𝓝 (0 : DeningerArithmeticFiniteJetValues S) := by
    have htarget :
        A ∈
          𝓝 (deningerCompactOpenFiniteJetSection S
            (0 : DeningerArithmeticFiniteJetValues S)) := by
      simpa only [map_zero] using hA
    have hpre :=
      (deningerCompactOpenFiniteJetSection S).continuous.continuousAt
        |>.preimage_mem_nhds htarget
    simpa only [map_zero, W] using hpre
  refine ⟨n, W, hW, ?_⟩
  intro F hFW
  let P :=
    deningerCompactOpenFiniteJetRepresentative S F
  have hPA : P ∈ A := by
    change
      deningerCompactOpenFiniteJetSection S
          (deningerCompactOpenFiniteJets S F) ∈ A
    exact hFW
  let Q : ℕ → DeningerCompactOpenEntire :=
    fun j =>
      deningerCompactOpenLocalXiQuotientTaylorApprox
        (F - P) (n + 1) j
  let G : ℕ → DeningerCompactOpenEntire :=
    fun j => (F - P) - deningerCompactOpenXiMul (Q j)
  have hGconv :
      TendstoLocallyUniformlyOn
        (fun j z => G j z) (fun _ => 0)
        atTop (Metric.ball 0 n) := by
    have hfun :
        (fun j z => G j z) =
          fun j z =>
            (F - P) z -
              XiC z *
                deningerLocalXiQuotientTaylorApprox
                  (F - P) (n + 1) j z := by
      funext j z
      change
        (F z - P z) -
            deningerCompactOpenXiMul
              (deningerCompactOpenLocalXiQuotientTaylorApprox
                (F - P) (n + 1) j) z =
          (F z - P z) -
            XiC z *
              deningerLocalXiQuotientTaylorApprox
                (F - P) (n + 1) j z
      rw [deningerCompactOpenXiMul_apply,
        deningerCompactOpenLocalXiQuotientTaylorApprox_apply]
    rw [hfun]
    simpa only [P, S] using
      deningerCompactOpenFiniteJetRepresentative_peeling F n
  obtain ⟨j, hGjA⟩ :=
    (hn G hGconv).exists
  have hP_V :
      deningerArithmeticCompactOpenH1Class P ∈ V :=
    hPA
  have hGj_V :
      deningerArithmeticCompactOpenH1Class (G j) ∈ V :=
    hGjA
  have hCoboundary :
      deningerArithmeticCompactOpenH1Class
          (deningerCompactOpenXiMul (Q j)) = 0 := by
    exact
      (DeningerCompactOpenQuotient.mk_eq_zero_iff_mem
        deningerCompactOpenXiRange
        (deningerCompactOpenXiMul (Q j))).mpr
          ⟨Q j, rfl⟩
  have hGclass :
      deningerArithmeticCompactOpenH1Class (G j) =
        deningerArithmeticCompactOpenH1Class (F - P) := by
    calc
      deningerArithmeticCompactOpenH1Class (G j) =
          deningerArithmeticCompactOpenH1Class (F - P) -
            deningerArithmeticCompactOpenH1Class
              (deningerCompactOpenXiMul (Q j)) := by
        exact
          deningerArithmeticCompactOpenH1Class.map_sub
            (F - P) (deningerCompactOpenXiMul (Q j))
      _ = deningerArithmeticCompactOpenH1Class (F - P) := by
        rw [hCoboundary, sub_zero]
  apply hVV
  rw [Set.mem_add]
  refine
    ⟨deningerArithmeticCompactOpenH1Class P, hP_V,
      deningerArithmeticCompactOpenH1Class (F - P), ?_, ?_⟩
  · rw [← hGclass]
    exact hGj_V
  · have hsource : P + (F - P) = F := by
      abel
    exact congrArg deningerArithmeticCompactOpenH1Class hsource

/-- The descended all-jets observation induces exactly the quotient topology. -/
theorem isInducing_deningerCompactOpenH1AllJets :
    IsInducing
      (deningerCompactOpenH1AllJets :
        DeningerArithmeticCompactOpenH1 →
          DeningerArithmeticJetProduct) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  apply le_antisymm
  · have hcont :
        Tendsto
          (deningerCompactOpenH1AllJets :
            DeningerArithmeticCompactOpenH1 →
              DeningerArithmeticJetProduct)
          (𝓝 0) (𝓝 0) := by
      rw [← deningerCompactOpenH1AllJets.map_zero]
      exact
        (deningerCompactOpenH1AllJets.continuous.continuousAt :
          ContinuousAt
            (deningerCompactOpenH1AllJets :
              DeningerArithmeticCompactOpenH1 →
                DeningerArithmeticJetProduct)
            0)
    exact hcont.le_comap
  · intro U hU
    rw [Filter.mem_comap]
    obtain ⟨n, W, hW, hcontrol⟩ :=
      deningerCompactOpenH1AllJets_local_zero_control hU
    let S := deningerXiSupportClosedBallFinset (n + 2)
    let B : Set DeningerArithmeticJetProduct :=
      deningerArithmeticFiniteJetRestriction S ⁻¹' W
    have hB : B ∈ 𝓝 (0 : DeningerArithmeticJetProduct) := by
      have htarget :
          W ∈
            𝓝 (deningerArithmeticFiniteJetRestriction S
              (0 : DeningerArithmeticJetProduct)) := by
        simpa only [map_zero] using hW
      have hpre :=
        (deningerArithmeticFiniteJetRestriction S).continuous.continuousAt
          |>.preimage_mem_nhds htarget
      simpa only [map_zero, B] using hpre
    refine ⟨B, hB, ?_⟩
    intro x hx
    obtain ⟨F, rfl⟩ := Quotient.exists_rep x
    apply hcontrol F
    change
      deningerArithmeticFiniteJetRestriction S
          (deningerCompactOpenH1AllJets
            (deningerArithmeticCompactOpenH1Class F)) ∈ W at hx
    simpa only [deningerCompactOpenH1AllJets_class,
      deningerArithmeticFiniteJetRestriction_allJets] using hx

/-- Compact-open arithmetic cohomology is a topological subspace of the full local jet product. -/
theorem isEmbedding_deningerCompactOpenH1AllJets :
    IsEmbedding
      (deningerCompactOpenH1AllJets :
        DeningerArithmeticCompactOpenH1 →
          DeningerArithmeticJetProduct) :=
  ⟨isInducing_deningerCompactOpenH1AllJets,
    deningerCompactOpenH1AllJets_injective⟩

end

end RHTower
