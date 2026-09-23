import GaloisForLFunctions.HTGeometry.HorizonLinearContactInvariant
import GaloisForLFunctions.HTGeometry.CommutingCyclicHorizonLinearity
import GaloisForLFunctions.HTGeometry.FreeHorizonMaximalCommutatorRank

/-!
# Sharp nonabelian endpoint of the horizon commutator-rank law

In a two-dimensional law space the second exterior power is a line, so the horizon commutator
index takes only the values zero and one.  The crossing cone — the union of the two coordinate
law axes — has index one: the unique projective law plane contains two independent horizon
directions and still escapes the cone, so no nonzero exterior subspace is contact-only.

The free-word realization of the crossing horizon has injective commutator symbol, hence
commutator rank exactly one.  The sharp projective-obstruction law is therefore attained at the
first genuinely noncommutative value by an explicit realization: the reducible quadric horizon
forces exactly one commutator channel, no more and no fewer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The second exterior power of a two-dimensional law space is a line. -/
theorem finrank_exteriorPower_two_pi :
    Module.finrank K (⋀[K]^(2 : ℕ) (Fin 2 → K)) = 1 := by
  rw [exteriorPower.finrank_eq]
  simp

omit [CharZero K] in
/-- The two coordinate axes are linearly independent. -/
theorem linearIndependent_single_pair :
    LinearIndependent K ![(Pi.single 0 1 : Fin 2 → K), (Pi.single 1 1 : Fin 2 → K)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  intro i
  fin_cases i
  · simpa [Fin.sum_univ_two, Pi.single_apply] using h0
  · simpa [Fin.sum_univ_two, Pi.single_apply] using h1

/-- The plane of the two coordinate axes is not linear-contact for the crossing cone: both axes
lie on the cone, they are independent, and their generic superposition escapes. -/
theorem not_linearContactPlane_crossingCone :
    ¬ LinearContactPlane (K := K) (crossingCone K)
      (Pi.single 0 1) (Pi.single 1 1) := by
  rintro (hleft | hright)
  · exact hleft (Pi.single 0 1) (Submodule.subset_span (by simp))
      (Pi.single 1 1) (Submodule.subset_span (by simp))
      (by simp [crossingCone])
      (by simp [crossingCone])
      linearIndependent_single_pair
  · have hmem : (Pi.single 0 1 + Pi.single 1 1 : Fin 2 → K) ∈
        Submodule.span K {(Pi.single 0 1 : Fin 2 → K), Pi.single 1 1} :=
      Submodule.add_mem _
        (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    have hc := hright hmem
    simp [crossingCone] at hc

/-- The crossing cone admits no nonzero contact-only exterior subspace. -/
theorem horizonContactKernelDim_crossingCone :
    horizonContactKernelDim (K := K) (crossingCone K) = 0 := by
  refine Nat.le_zero.mp (csSup_le' (mem_upperBounds.mpr ?_))
  rintro n ⟨U, hU, rfl⟩
  by_contra hpos
  have htop : U = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le U
    rw [finrank_exteriorPower_two_pi] at hle ⊢
    omega
  exact not_linearContactPlane_crossingCone
    (hU (Pi.single 0 1) (Pi.single 1 1) linearIndependent_single_pair
      (htop ▸ Submodule.mem_top))

/-- The crossing cone has horizon commutator index one. -/
theorem horizonCommutatorIndex_crossingCone :
    horizonCommutatorIndex (K := K) (crossingCone K) = 1 := by
  unfold horizonCommutatorIndex
  rw [horizonContactKernelDim_crossingCone, finrank_exteriorPower_two_pi]

omit [CharZero K] in
/-- The zero law direction is always dependent. -/
theorem zero_mem_linearDerivationDependenceHorizon
    {L V : Type*} [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
    (ρ : V →ₗ[K] Derivation K L L) (x : L) :
    (0 : V) ∈ linearDerivationDependenceHorizon ρ x := by
  intro hAI
  have h1 := hAI.ne_zero 1
  apply h1
  show (((ρ 0 : Derivation K L L) : L → L)^[1]) x = 0
  rw [Function.iterate_one, map_zero]
  simp

/-- **Sharp nonabelian endpoint.**  Some realization has the crossing cone as its exact
one-observable dependence horizon and commutator rank exactly equal to the horizon commutator
index — both are one.  The reducible quadric horizon forces exactly one commutator channel. -/
theorem exists_crossingCone_horizon_sharp_commutator_rank :
    ∃ a : CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2) →
        ProjectiveWordState (Fin 2) → K,
      linearDerivationDependenceHorizon (projectiveCompleteLawMap a 3)
          (projectiveCompleteRoot (K := K) (ι := Fin 2)
            (η := CommonDegreeEquationIndex (Fin 2) (fun _ : Fin 1 ↦ 2))) =
        crossingCone K ∧
      Module.finrank K
          (derivationCommutatorMap (projectiveCompleteLawMap a 3)).range =
        horizonCommutatorIndex (K := K) (crossingCone K) := by
  obtain ⟨a, ha⟩ := exists_completeJet_crossingHorizon (K := K)
  refine ⟨a, ?_, ?_⟩
  · ext c
    by_cases hc : ∃ i, c i ≠ 0
    · exact ha c hc
    · push Not at hc
      have hc0 : c = 0 := funext fun i ↦ hc i
      subst hc0
      constructor
      · intro _
        show (0 : Fin 2 → K) ∈ crossingCone K
        simp [crossingCone]
      · intro _
        exact zero_mem_linearDerivationDependenceHorizon _ _
  · rw [horizonCommutatorIndex_crossingCone,
      LinearMap.finrank_range_of_inj (projectiveComplete_commutatorMap_injective a 3)]
    exact finrank_exteriorPower_two_pi

end

end GaloisForLFunctions.HTGeometry
