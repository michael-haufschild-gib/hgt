import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerWeakFlow
import GaloisForLFunctions.HTGeometry.RealExponentialPolynomial

/-!
# Finite causal synthesis respects the original Meyer dynamics

Strong orbit differentiation, separation of literal cohomology classes, and
scalar ODE uniqueness remove a possible invisible dynamical defect. Every
finite causal projector commutes with the original dilation flow, and its
section intertwines that flow with the full confluent Xi packet flow.
Consequently arbitrary finite packet operators have an exact original-flow
conjugation law on the actual cohomology.
-/

open Complex Filter Topology
open scoped Classical

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

/-- The already constructed causal projector in the natural topology. -/
def deningerMeyerFiniteXiCausalProjectorCLM (S : Finset XiDivisorSupport) :
    DeningerMeyerStrongLogCohomology →L[ℂ] DeningerMeyerStrongLogCohomology where
  toLinearMap := deningerMeyerFiniteXiCausalProjector S
  cont := (deningerMeyerFiniteXiCausalSection_continuous S).comp
    (deningerMeyerFiniteXiJetPacketLM_continuous S)

private theorem projector_jetSource (S : Finset XiDivisorSupport)
    (rho : XiDivisorSupport) (hrho : rho ∈ S) (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerXiJetSource rho j) =
      deningerMeyerXiJetSource rho j := by
  have h := deningerMeyerFiniteXiCausalProjector_synthesis S
    (Pi.single (⟨⟨rho, hrho⟩, j⟩ : DeningerMeyerFiniteXiJetSlot S) 1)
  simpa using h

private theorem projector_causalClass (S : Finset XiDivisorSupport)
    (rho : XiDivisorSupport) (hrho : rho ∈ S) (k : ℕ)
    (hk : k ≤ xiSupportMultiplicity rho) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerXiCausalClass rho k hk) =
      deningerMeyerXiCausalClass rho k hk := by
  by_cases hk0 : k = 0
  · subst k
    simp
  · let j : DeningerArithmeticJetIndex rho := ⟨xiSupportMultiplicity rho - k, by omega⟩
    have he : xiSupportMultiplicity rho - (xiSupportMultiplicity rho - k) = k := by omega
    simpa only [deningerMeyerXiJetSource, j, he] using projector_jetSource S rho hrho j

/-- Actual flow of every causal chain stays in its chosen finite causal sector. -/
theorem deningerMeyerFiniteXiCausalProjector_flow_causalClass
    (S : Finset XiDivisorSupport) (rho : XiDivisorSupport) (hrho : rho ∈ S)
    (k : ℕ) (hk : k ≤ xiSupportMultiplicity rho) (c : ℝ) :
    deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerStrongLogCohomologyFlow c (deningerMeyerXiCausalClass rho k hk)) =
        deningerMeyerStrongLogCohomologyFlow c (deningerMeyerXiCausalClass rho k hk) := by
  revert hk c
  induction k with
  | zero => intro hk c; simp
  | succ k ih =>
    intro hk c
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    intro ell
    let residual : DeningerMeyerStrongLogCohomology →L[ℂ] ℂ :=
      ell.comp (deningerMeyerFiniteXiCausalProjectorCLM S - ContinuousLinearMap.id ℂ _)
    let f : ℝ → ℂ := fun t => residual
      (deningerMeyerStrongLogCohomologyFlow t (deningerMeyerXiCausalClass rho (k + 1) hk))
    have hprevious (t : ℝ) : residual
        (deningerMeyerStrongLogCohomologyFlow t
          (deningerMeyerXiCausalClass rho k (by omega))) = 0 := by
      change ell (deningerMeyerFiniteXiCausalProjector S
        (deningerMeyerStrongLogCohomologyFlow t (deningerMeyerXiCausalClass rho k (by omega))) -
          deningerMeyerStrongLogCohomologyFlow t (deningerMeyerXiCausalClass rho k (by omega))) = 0
      rw [ih (by omega) t, sub_self, map_zero]
    have hderiv (t : ℝ) : HasDerivAt f ((rho : ℂ) * f t) t := by
      have hd := deningerMeyerStrongLogCohomologyFlow_hasDerivAt_dual residual
        (deningerMeyerXiCausalClass rho (k + 1) hk) t
      rw [deningerMeyerXiCausalClass_generator] at hd
      simpa only [map_add, map_smul, hprevious t, add_zero, smul_eq_mul, f] using hd
    have hzero : f 0 = 0 := by
      dsimp only [f]
      rw [deningerMeyerStrongLogCohomologyFlow_zero]
      change ell (deningerMeyerFiniteXiCausalProjector S (deningerMeyerXiCausalClass rho (k + 1) hk) -
        deningerMeyerXiCausalClass rho (k + 1) hk) = 0
      rw [projector_causalClass S rho hrho, sub_self, map_zero]
    have hsolution := GaloisForLFunctions.HTGeometry.eq_const_mul_exp_of_deriv_eq_smul
      (fun t => (hderiv t).differentiableAt) (fun t => (hderiv t).deriv) c
    rw [hzero, zero_mul] at hsolution
    change ell (deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerStrongLogCohomologyFlow c (deningerMeyerXiCausalClass rho (k + 1) hk)) -
        deningerMeyerStrongLogCohomologyFlow c (deningerMeyerXiCausalClass rho (k + 1) hk)) = 0
      at hsolution
    exact sub_eq_zero.mp (by simpa only [map_sub] using hsolution)

theorem deningerMeyerFiniteXiCausalProjector_flow_synthesis
    (S : Finset XiDivisorSupport) (c : ℝ) (a : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalSynthesis S a)) =
        deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalSynthesis S a) := by
  rw [deningerMeyerFiniteXiCausalSynthesis_apply, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, map_smul]
  congr 1
  exact deningerMeyerFiniteXiCausalProjector_flow_causalClass S q.1.1 q.1.2
    (xiSupportMultiplicity q.1.1 - q.2.val) (Nat.sub_le _ _) c

/-- Full finite causal projectors commute with the original dilation flow. -/
theorem deningerMeyerFiniteXiCausalProjector_flow (S : Finset XiDivisorSupport)
    (c : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFiniteXiCausalProjector S (deningerMeyerStrongLogCohomologyFlow c u) =
      deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalProjector S u) := by
  have hfix : deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalProjector S u)) =
        deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalProjector S u) := by
    obtain ⟨a, ha⟩ := deningerMeyerFiniteXiCausalProjector_mem_range S u
    rw [← ha]
    exact deningerMeyerFiniteXiCausalProjector_flow_synthesis S c a
  have hj : deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalProjector S u)) =
        deningerMeyerFiniteXiCausalProjector S (deningerMeyerStrongLogCohomologyFlow c u) := by
    change deningerMeyerFiniteXiCausalSection S
      (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerStrongLogCohomologyFlow c
        (deningerMeyerFiniteXiCausalProjector S u))) =
      deningerMeyerFiniteXiCausalSection S
        (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerStrongLogCohomologyFlow c u))
    rw [deningerMeyerFiniteXiJetPacketLM_flow, deningerMeyerFiniteXiJetPacketLM_flow,
      deningerMeyerFiniteXiCausalProjector_jets]
  exact hj.symm.trans hfix

/-- Causal synthesis lifts the full confluent packet dynamics to original source dynamics. -/
theorem deningerMeyerFiniteXiCausalSection_flow (S : Finset XiDivisorSupport)
    (c : ℝ) (a : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalSection S a) =
      deningerMeyerFiniteXiCausalSection S (deningerMeyerFiniteXiJetPacketFlow S c a) := by
  have hfix : deningerMeyerFiniteXiCausalProjector S
      (deningerMeyerFiniteXiCausalSection S a) = deningerMeyerFiniteXiCausalSection S a := by
    change deningerMeyerFiniteXiCausalSection S
      (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerFiniteXiCausalSection S a)) = _
    rw [deningerMeyerFiniteXiCausalSection_jets]
  rw [← hfix, ← deningerMeyerFiniteXiCausalProjector_flow]
  change deningerMeyerFiniteXiCausalSection S
    (deningerMeyerFiniteXiJetPacketLM S
      (deningerMeyerStrongLogCohomologyFlow c (deningerMeyerFiniteXiCausalSection S a))) = _
  rw [deningerMeyerFiniteXiJetPacketLM_flow, deningerMeyerFiniteXiCausalSection_jets]

/-- Arbitrary finite packet operators now obey exact original-flow conjugation. -/
theorem deningerMeyerFiniteXiOperatorLift_flow_conjugation (S : Finset XiDivisorSupport)
    (c : ℝ) (B : Module.End ℂ (DeningerMeyerFiniteXiJetPacket S))
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCohomologyFlow c
      (deningerMeyerFiniteXiOperatorLift S B (deningerMeyerStrongLogCohomologyFlow (-c) u)) =
        deningerMeyerFiniteXiOperatorLift S
          ((deningerMeyerFiniteXiJetPacketFlow S c).comp
            (B.comp (deningerMeyerFiniteXiJetPacketFlow S (-c)))) u := by
  change deningerMeyerStrongLogCohomologyFlow c
    (deningerMeyerFiniteXiCausalSection S
      (B (deningerMeyerFiniteXiJetPacketLM S (deningerMeyerStrongLogCohomologyFlow (-c) u)))) = _
  rw [deningerMeyerFiniteXiCausalSection_flow, deningerMeyerFiniteXiJetPacketLM_flow]
  rfl

end
end RHTower
