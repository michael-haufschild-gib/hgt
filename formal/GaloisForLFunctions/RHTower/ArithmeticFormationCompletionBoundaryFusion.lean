import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixCofinalMeyerTateXiGreenBoundary
import GaloisForLFunctions.RHTower.PreDivisorTransverseRamificationRoosTransgression

/-!
# Arithmetic formation--completion boundary fusion

The literal rational-adelic Meyer--Tate finite source graph is dense in the Gamma-six singular
completion, but its vertical line contains only zero at finite level.  Consequently a completed Xi
Green vertical boundary is completion-born exactly off the critical line.  The same condition is
reconstructed by the pre-divisor Roos class and the strict Gamma/Sonin physical transport.

No RH, critical-line, or extra source-effectivity premise is used.  The terminal equivalence says
that universal absence of this arithmetic formation--completion boundary is exactly RH.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Finite cofinal packet admission retains every coefficient. -/
theorem deningerGammaSixCofinalFinitePacketAdmission_injective :
    Function.Injective deningerGammaSixCofinalFinitePacketAdmission := by
  intro c d h
  apply Finsupp.ext
  intro n
  have hn := congrArg (fun x : EllTwo => x n) h
  simpa [deningerGammaSixCofinalFinitePacketAdmission_apply] using hn

/-- The finite arithmetic graph meets the singular vertical line only at zero. -/
theorem smul_deningerGammaSixCofinalGraphSingularVector_mem_finiteGraph_iff
    (a : ℂ) :
    a • deningerGammaSixCofinalGraphSingularVector ∈
        deningerGammaSixCofinalFiniteGraph ↔ a = 0 := by
  constructor
  · intro h
    change a • deningerGammaSixCofinalGraphSingularVector ∈
      LinearMap.range
        ((WithLp.linearEquiv 2 ℂ (EllTwo × ℂ)).symm.toLinearMap.comp
          (deningerGammaSixCofinalFinitePacketAdmission.prod
            deningerGammaSixCofinalFinitePacketTrace)) at h
    obtain ⟨c, hc⟩ := h
    change deningerGammaSixCofinalFiniteGraphAdmission c =
      a • deningerGammaSixCofinalGraphSingularVector at hc
    have hp := congrArg
      (fun z : DeningerGammaSixCofinalSingularGraph => z.ofLp) hc
    have hfirst : deningerGammaSixCofinalFinitePacketAdmission c = 0 := by
      simpa [deningerGammaSixCofinalGraphSingularVector] using
        congrArg Prod.fst hp
    have hc0 : c = 0 :=
      deningerGammaSixCofinalFinitePacketAdmission_injective (by simpa using hfirst)
    subst c
    have hsecond := congrArg Prod.snd hp
    simpa [deningerGammaSixCofinalGraphSingularVector] using hsecond.symm
  · rintro rfl
    simp

/-- Laws born in singular completion but absent from the finite arithmetic source graph. -/
def deningerGammaSixArithmeticFormationCompletionBoundary :
    Set DeningerGammaSixCofinalSingularGraph :=
  (deningerGammaSixCofinalFiniteGraph.topologicalClosure :
      Set DeningerGammaSixCofinalSingularGraph) \
    (deningerGammaSixCofinalFiniteGraph :
      Set DeningerGammaSixCofinalSingularGraph)

/-- Every completed Xi Green vertical boundary lies in closure of the literal finite source graph. -/
theorem deningerGammaSixCofinalXiGreenVerticalBoundary_mem_closure
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
      deningerGammaSixCofinalFiniteGraph.topologicalClosure := by
  rw [deningerGammaSixCofinalFiniteGraph_closure_eq_top]
  exact Submodule.mem_top

/-- Finite arithmetic effectivity of the completed Xi boundary is exactly wall placement. -/
theorem deningerGammaSixCofinalXiGreenVerticalBoundary_mem_finiteGraph_iff
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixCofinalFiniteGraph ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerGammaSixCofinalXiGreenVerticalBoundary,
    smul_deningerGammaSixCofinalGraphSingularVector_mem_finiteGraph_iff,
    reflectedGaussianHorizonGreenProvenance_apply_eq_zero_iff]

/-- Off-line horizontal charge is precisely a law born at formation completion. -/
theorem deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixArithmeticFormationCompletionBoundary ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [deningerGammaSixArithmeticFormationCompletionBoundary, Set.mem_sdiff]
  constructor
  · rintro ⟨_, hnot⟩
    exact fun hline => hnot
      ((deningerGammaSixCofinalXiGreenVerticalBoundary_mem_finiteGraph_iff q).2
        hline)
  · intro hoff
    exact
      ⟨deningerGammaSixCofinalXiGreenVerticalBoundary_mem_closure q,
        fun hmem => hoff
          ((deningerGammaSixCofinalXiGreenVerticalBoundary_mem_finiteGraph_iff q).1
            hmem)⟩

/-- Roos `lim^(1 : ℕ)` reconstructs exactly the arithmetic formation--completion boundary. -/
theorem deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff_roos
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixArithmeticFormationCompletionBoundary ↔
      preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) ≠ 0 := by
  rw [
    deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff,
    preDivisorTransverseDerivedCompletionClass_ne_zero_iff]

/-- Strict Gamma/Sonin physical transport reconstructs the same completion-born boundary. -/
theorem deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff_physical
    (q : XiZeroCopy) :
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
        deningerGammaSixArithmeticFormationCompletionBoundary ↔
      deningerGammaSixCofinalGraphPhysicalTransport
          (2 * (q.1 : ℂ).re - 1)
          (deningerGammaSixCofinalXiGreenVerticalBoundary q) ≠ 0 := by
  rw [
    deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff]
  exact (not_congr
    (deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary_eq_zero_iff q)).symm

/-- No multiplicity-labelled Xi boundary is born only after singular completion. -/
def XiArithmeticFormationCompletionBoundaryFree : Prop :=
  ∀ q : XiZeroCopy,
    deningerGammaSixCofinalXiGreenVerticalBoundary q ∉
      deningerGammaSixArithmeticFormationCompletionBoundary

/-- Universal finite effectivity of the completed arithmetic boundary is exactly RH. -/
theorem xiArithmeticFormationCompletionBoundaryFree_iff_riemannHypothesis :
    XiArithmeticFormationCompletionBoundaryFree ↔ RiemannHypothesis := by
  constructor
  · intro hfree
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    have hpos := xi_divisor_pos_on_support rho
    have hn :
        0 < Int.toNat
          ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      omega
    let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
    have hnot : ¬ ((q.1 : ℂ).re ≠ 1 / 2) := by
      intro hoff
      exact hfree q
        ((deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff
          q).2 hoff)
    simpa [q] using not_ne_iff.mp hnot
  · intro hRH q hboundary
    exact
      ((deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff
        q).1 hboundary)
        (xi_divisor_support_re_eq_half_of_rh hRH q.1)

/-- Closed certificate joining finite effectivity, singular completion, Roos homology, physical
transport, and RH selection. -/
def ArithmeticFormationCompletionBoundaryFusionLaw : Prop :=
  Function.Injective deningerGammaSixCofinalFinitePacketAdmission ∧
    (∀ a : ℂ,
      a • deningerGammaSixCofinalGraphSingularVector ∈
          deningerGammaSixCofinalFiniteGraph ↔ a = 0) ∧
    (∀ q : XiZeroCopy,
      deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
          deningerGammaSixArithmeticFormationCompletionBoundary ↔
        preDivisorTransverseDerivedCompletionClass (q.1 : ℂ) ≠ 0) ∧
    (∀ q : XiZeroCopy,
      deningerGammaSixCofinalXiGreenVerticalBoundary q ∈
          deningerGammaSixArithmeticFormationCompletionBoundary ↔
        deningerGammaSixCofinalGraphPhysicalTransport
            (2 * (q.1 : ℂ).re - 1)
            (deningerGammaSixCofinalXiGreenVerticalBoundary q) ≠ 0) ∧
    (XiArithmeticFormationCompletionBoundaryFree ↔ RiemannHypothesis)

/-- Arithmetic formation--completion boundary fusion law, with no external hypotheses. -/
theorem arithmeticFormationCompletionBoundaryFusion_law :
    ArithmeticFormationCompletionBoundaryFusionLaw := by
  exact ⟨deningerGammaSixCofinalFinitePacketAdmission_injective,
    smul_deningerGammaSixCofinalGraphSingularVector_mem_finiteGraph_iff,
    deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff_roos,
    deningerGammaSixCofinalXiGreenVerticalBoundary_mem_formationCompletionBoundary_iff_physical,
    xiArithmeticFormationCompletionBoundaryFree_iff_riemannHypothesis⟩

end

end RHTower
