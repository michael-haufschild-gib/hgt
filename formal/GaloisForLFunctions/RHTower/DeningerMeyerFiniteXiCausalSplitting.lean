import GaloisForLFunctions.RHTower.DeningerMeyerXiCausalChains

/-!
# Invariant finite spectral splittings of literal Meyer cohomology

Causal Xi chains give a source section of every finite full-jet quotient.
Their local jet matrix is triangular with nonzero diagonal, and all other
divisor blocks vanish.  The resulting finite spectral projector commutes
with the actual logarithmic generator.  No global spectral-synthesis,
positivity, simplicity, or RH assumption is used.
-/

open Complex Set
open scoped Classical

namespace RHTower
noncomputable section

/-- Synthesis from the actual causally divided Xi sources. -/
def deningerMeyerFiniteXiCausalSynthesis (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ] DeningerMeyerStrongLogCohomology where
  toFun c := ∑ q : DeningerMeyerFiniteXiJetSlot S,
    c q • deningerMeyerXiJetSource q.1.1 q.2
  map_add' c d := by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Pi.smul_apply, Finset.smul_sum, smul_smul]

@[simp]
theorem deningerMeyerFiniteXiCausalSynthesis_apply (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiCausalSynthesis S c =
      ∑ q : DeningerMeyerFiniteXiJetSlot S, c q • deningerMeyerXiJetSource q.1.1 q.2 := rfl

private theorem finiteXiCausal_jet_kernel (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S)
    (hz : deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalSynthesis S c) = 0) :
    c = 0 := by
  have hc : ∀ n, ∀ q : DeningerMeyerFiniteXiJetSlot S, q.2.val = n → c q = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hq
        have he := congrFun hz q
        simp only [deningerMeyerFiniteXiJetPacketLM_apply,
          deningerMeyerFiniteXiCausalSynthesis_apply, map_sum, map_smul,
          smul_eq_mul, Pi.zero_apply] at he
        have hs : (∑ r : DeningerMeyerFiniteXiJetSlot S,
            c r * deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2
              (deningerMeyerXiJetSource r.1.1 r.2)) =
            c q * deningerMeyerXiSupportJetEvaluationLM q.1.1 q.2
              (deningerMeyerXiJetSource q.1.1 q.2) := by
          apply Finset.sum_eq_single q
          · intro r _ hr
            by_cases hp : r.1 = q.1
            · obtain ⟨qr, qi⟩ := q
              obtain ⟨rr, ri⟩ := r
              dsimp only at hp hr ⊢
              subst rr
              change qi.val = n at hq
              have hneq : ri.val ≠ qi.val := by
                intro hv
                apply hr
                congr 1
                exact Fin.ext hv
              rcases lt_or_gt_of_ne hneq with hl | hl
              · rw [ih ri.val (by omega) ⟨qr, ri⟩ rfl, zero_mul]
              · rw [deningerMeyerXiJetSource_jet_zero qr.1 ri qi hl, mul_zero]
            · rw [deningerMeyerXiJetSource_other_jet_zero r.1.1 q.1.1
                (fun h => hp (Subtype.ext h.symm)) r.2 q.2, mul_zero]
          · simp
        rw [hs] at he
        exact (mul_eq_zero.mp he).resolve_right
          (deningerMeyerXiJetSource_jet_ne_zero q.1.1 q.2)
  funext q
  exact hc q.2.val q rfl

theorem deningerMeyerFiniteXiCausalJetMap_injective (S : Finset XiDivisorSupport) :
    Function.Injective ((deningerMeyerFiniteXiJetPacketLM S).comp
      (deningerMeyerFiniteXiCausalSynthesis S)) := by
  intro c d h
  apply sub_eq_zero.mp
  apply finiteXiCausal_jet_kernel S
  change ((deningerMeyerFiniteXiJetPacketLM S).comp
    (deningerMeyerFiniteXiCausalSynthesis S)) (c - d) = 0
  rw [map_sub, h, sub_self]

/-- No actual Xi chain vector is lost, even when several divisor blocks are combined. -/
theorem deningerMeyerFiniteXiCausalSources_linearIndependent (S : Finset XiDivisorSupport) :
    LinearIndependent ℂ (fun q : DeningerMeyerFiniteXiJetSlot S =>
      deningerMeyerXiJetSource q.1.1 q.2) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc q
  have hz : deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalSynthesis S c) = 0 := by
    rw [deningerMeyerFiniteXiCausalSynthesis_apply, hc, map_zero]
  exact congrFun (finiteXiCausal_jet_kernel S c hz) q

/-- The finite local jet matrix of the canonical actual sources is invertible. -/
def deningerMeyerFiniteXiCausalJetEquiv (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S ≃ₗ[ℂ] DeningerMeyerFiniteXiJetPacket S :=
  LinearEquiv.ofBijective
    ((deningerMeyerFiniteXiJetPacketLM S).comp (deningerMeyerFiniteXiCausalSynthesis S))
    ⟨deningerMeyerFiniteXiCausalJetMap_injective S,
      LinearMap.injective_iff_surjective.mp (deningerMeyerFiniteXiCausalJetMap_injective S)⟩

/-- Source-native section, with range spanned by full actual Xi Jordan chains. -/
def deningerMeyerFiniteXiCausalSection (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ] DeningerMeyerStrongLogCohomology :=
  (deningerMeyerFiniteXiCausalSynthesis S).comp
    (deningerMeyerFiniteXiCausalJetEquiv S).symm.toLinearMap

@[simp]
theorem deningerMeyerFiniteXiCausalSection_jets (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalSection S c) = c :=
  (deningerMeyerFiniteXiCausalJetEquiv S).apply_symm_apply c

/-- Canonical finite spectral projector inside literal Meyer cohomology. -/
def deningerMeyerFiniteXiCausalProjector (S : Finset XiDivisorSupport) :
    Module.End ℂ DeningerMeyerStrongLogCohomology :=
  (deningerMeyerFiniteXiCausalSection S).comp (deningerMeyerFiniteXiJetPacketLM S)

@[simp]
theorem deningerMeyerFiniteXiCausalProjector_jets (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalProjector S u) =
      deningerMeyerFiniteXiJetPacketLM S u :=
  deningerMeyerFiniteXiCausalSection_jets S _

@[simp]
theorem deningerMeyerFiniteXiCausalProjector_idempotent (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerFiniteXiCausalProjector S u) =
      deningerMeyerFiniteXiCausalProjector S u := by
  change deningerMeyerFiniteXiCausalSection S
    (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalProjector S u)) = _
  rw [deningerMeyerFiniteXiCausalProjector_jets]
  rfl

theorem deningerMeyerFiniteXiCausalProjector_synthesis (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerFiniteXiCausalSynthesis S c) =
      deningerMeyerFiniteXiCausalSynthesis S c := by
  change deningerMeyerFiniteXiCausalSynthesis S
    ((deningerMeyerFiniteXiCausalJetEquiv S).symm
      ((deningerMeyerFiniteXiCausalJetEquiv S) c)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem deningerMeyerFiniteXiCausalProjector_mem_range (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiCausalProjector S u ∈
      LinearMap.range (deningerMeyerFiniteXiCausalSynthesis S) :=
  ⟨(deningerMeyerFiniteXiCausalJetEquiv S).symm
    (deningerMeyerFiniteXiJetPacketLM S u), rfl⟩

private theorem finiteXiCausal_source_mem (S : Finset XiDivisorSupport)
    (q : DeningerMeyerFiniteXiJetSlot S) :
    deningerMeyerXiJetSource q.1.1 q.2 ∈
      LinearMap.range (deningerMeyerFiniteXiCausalSynthesis S) := by
  refine ⟨Pi.single q 1, ?_⟩
  simp

theorem deningerMeyerFiniteXiCausalRange_generator (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : u ∈ LinearMap.range (deningerMeyerFiniteXiCausalSynthesis S)) :
    deningerMeyerCohomologyGenerator u ∈
      LinearMap.range (deningerMeyerFiniteXiCausalSynthesis S) := by
  obtain ⟨c, rfl⟩ := hu
  rw [deningerMeyerFiniteXiCausalSynthesis_apply, map_sum]
  apply Submodule.sum_mem
  intro q _
  rw [map_smul]
  apply Submodule.smul_mem
  rw [deningerMeyerXiJetSource_generator]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (finiteXiCausal_source_mem S q)
  · split_ifs with hj
    · exact finiteXiCausal_source_mem S ⟨q.1, ⟨q.2.val + 1, hj⟩⟩
    · exact Submodule.zero_mem _

/-- The complementary full-jet kernel is also invariant under the actual generator. -/
theorem deningerMeyerFiniteXiJetKernel_generator (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology)
    (hu : deningerMeyerFiniteXiJetPacketLM S u = 0) :
    deningerMeyerFiniteXiJetPacketLM S (deningerMeyerCohomologyGenerator u) = 0 := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
      funext q
      have hzero (i : ℕ) (hi : i < xiSupportMultiplicity q.1.1) :
          iteratedDeriv i (deningerMeyerStrongLogMellin g) (q.1.1 : ℂ) = 0 := by
        have h := congrFun hu ⟨q.1, ⟨i, hi⟩⟩
        simpa only [deningerMeyerFiniteXiJetPacketLM_apply,
          deningerMeyerXiSupportJetEvaluationLM_mk,
          deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, Pi.zero_apply] using h
      change deningerMeyerStrongLogMellinJetLM q.2 (q.1.1 : ℂ)
        (deningerMeyerStrongLogGenerator g) = 0
      rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
      have hfun : deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator g) =
          (fun s : ℂ => s) * deningerMeyerStrongLogMellin g := by
        funext s
        exact deningerMeyerStrongLogGenerator_mellin g s
      rw [hfun, iteratedDeriv_mul (by fun_prop)
        (analyticOnNhd_deningerMeyerStrongLogMellin g.property _ (Set.mem_univ _)).contDiffAt]
      apply Finset.sum_eq_zero
      intro i _
      rw [hzero (q.2.val - i) (lt_of_le_of_lt (Nat.sub_le _ _) q.2.isLt)]
      simp

/-- Finite causal spectral localization commutes with the literal logarithmic generator. -/
theorem deningerMeyerFiniteXiCausalProjector_generator (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerCohomologyGenerator u) =
      deningerMeyerCohomologyGenerator (deningerMeyerFiniteXiCausalProjector S u) := by
  have hker : deningerMeyerFiniteXiJetPacketLM S
      (u - deningerMeyerFiniteXiCausalProjector S u) = 0 := by
    rw [map_sub, deningerMeyerFiniteXiCausalProjector_jets, sub_self]
  have hz := deningerMeyerFiniteXiJetKernel_generator S _ hker
  have hP : deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerCohomologyGenerator (u - deningerMeyerFiniteXiCausalProjector S u)) = 0 := by
    change deningerMeyerFiniteXiCausalSection S
      (deningerMeyerFiniteXiJetPacketLM S _) = 0
    rw [hz, map_zero]
  obtain ⟨c, hc⟩ := deningerMeyerFiniteXiCausalRange_generator S _
    (deningerMeyerFiniteXiCausalProjector_mem_range S u)
  rw [map_sub, map_sub, ← hc, deningerMeyerFiniteXiCausalProjector_synthesis] at hP
  exact (sub_eq_zero.mp hP).trans hc

/-- The actual generator transported to a finite full-multiplicity packet. -/
def deningerMeyerFiniteXiPacketGenerator (S : Finset XiDivisorSupport) :
    Module.End ℂ (DeningerMeyerFiniteXiJetPacket S) :=
  (deningerMeyerFiniteXiJetPacketLM S).comp
    (deningerMeyerCohomologyGenerator.comp (deningerMeyerFiniteXiCausalSection S))

theorem deningerMeyerFiniteXiPacketGenerator_jets (S : Finset XiDivisorSupport)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiPacketGenerator S (deningerMeyerFiniteXiJetPacketLM S u) =
      deningerMeyerFiniteXiJetPacketLM S (deningerMeyerCohomologyGenerator u) := by
  change deningerMeyerFiniteXiJetPacketLM S
    (deningerMeyerCohomologyGenerator (deningerMeyerFiniteXiCausalProjector S u)) = _
  rw [← deningerMeyerFiniteXiCausalProjector_generator,
    deningerMeyerFiniteXiCausalProjector_jets]

theorem deningerMeyerFiniteXiCausalSection_generator (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerCohomologyGenerator (deningerMeyerFiniteXiCausalSection S c) =
      deningerMeyerFiniteXiCausalSection S (deningerMeyerFiniteXiPacketGenerator S c) := by
  have hfix : deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerFiniteXiCausalSection S c) = deningerMeyerFiniteXiCausalSection S c := by
    change deningerMeyerFiniteXiCausalSection S
      (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalSection S c)) = _
    rw [deningerMeyerFiniteXiCausalSection_jets]
  change _ = deningerMeyerFiniteXiCausalProjector S
    (deningerMeyerCohomologyGenerator (deningerMeyerFiniteXiCausalSection S c))
  rw [deningerMeyerFiniteXiCausalProjector_generator, hfix]

/-- Every finite packet operator now has an actual source-native realization. -/
def deningerMeyerFiniteXiOperatorLift (S : Finset XiDivisorSupport)
    (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S)) :
    Module.End ℂ DeningerMeyerStrongLogCohomology :=
  (deningerMeyerFiniteXiCausalSection S).comp (B.comp (deningerMeyerFiniteXiJetPacketLM S))

theorem deningerMeyerFiniteXiOperatorLift_comp (S : Finset XiDivisorSupport)
    (B C : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S)) :
    (deningerMeyerFiniteXiOperatorLift S B).comp (deningerMeyerFiniteXiOperatorLift S C) =
      deningerMeyerFiniteXiOperatorLift S (B.comp C) := by
  apply LinearMap.ext
  intro u
  change deningerMeyerFiniteXiCausalSection S
    (B (deningerMeyerFiniteXiJetPacketLM S
      (deningerMeyerFiniteXiCausalSection S (C (deningerMeyerFiniteXiJetPacketLM S u))))) = _
  rw [deningerMeyerFiniteXiCausalSection_jets]
  rfl

theorem deningerMeyerFiniteXiOperatorLift_faithful (S : Finset XiDivisorSupport) :
    Function.Injective (deningerMeyerFiniteXiOperatorLift S) := by
  intro B C h
  apply LinearMap.ext
  intro c
  have he := congrArg (fun F : Module.End ℂ DeningerMeyerStrongLogCohomology =>
    deningerMeyerFiniteXiJetPacketLM S (F (deningerMeyerFiniteXiCausalSection S c))) h
  simpa only [deningerMeyerFiniteXiOperatorLift, LinearMap.comp_apply,
    deningerMeyerFiniteXiCausalSection_jets] using he

theorem deningerMeyerFiniteXiCausalSection_other_jet_zero (S : Finset XiDivisorSupport)
    (rho : XiDivisorSupport) (hrho : rho ∉ S) (j : DeningerArithmeticJetIndex rho)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerXiSupportJetEvaluationLM rho j (deningerMeyerFiniteXiCausalSection S c) = 0 := by
  change deningerMeyerXiSupportJetEvaluationLM rho j
    (deningerMeyerFiniteXiCausalSynthesis S _) = 0
  rw [deningerMeyerFiniteXiCausalSynthesis_apply, map_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [map_smul, deningerMeyerXiJetSource_other_jet_zero q.1.1 rho
    (fun h => hrho (h.symm ▸ q.1.2)) q.2 j, smul_zero]

/-- Disjoint finite divisor packets have mutually annihilating actual spectral projectors. -/
theorem deningerMeyerFiniteXiCausalProjector_disjoint
    (S T : Finset XiDivisorSupport) (hST : Disjoint S T)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerFiniteXiCausalProjector T u) = 0 := by
  have hz : deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalProjector T u) = 0 := by
    funext q
    exact deningerMeyerFiniteXiCausalSection_other_jet_zero T q.1.1
      (fun h => Finset.disjoint_left.mp hST q.1.2 h) q.2 _
  change deningerMeyerFiniteXiCausalSection S
    (deningerMeyerFiniteXiJetPacketLM S _) = 0
  rw [hz, map_zero]

end
end RHTower
