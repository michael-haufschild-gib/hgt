import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionFredholm

/-! # Exact reduction of arbitrary convolution equations to finite Xi blocks

The complement of the complete resonant packet is solved by the canonical
bounded repair inverse. Every remaining compatibility condition and every
homogeneous freedom belongs to the original finite full-multiplicity packet.
-/

noncomputable section
open Complex ContinuousLinearMap
open scoped Classical

namespace RHTower

local notation "P" => deningerMeyerConvolutionResonantProjection
local notation "C" => deningerMeyerHilbertConvolution
local notation "B" => deningerMeyerConvolutionFredholmRepair
local notation "R" => deningerMeyerConvolutionFredholmInverse

theorem deningerMeyerConvolutionRepair_projection (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) : P g (B g x) = P g x := by
  apply lp.ext
  funext q
  change deningerHasseBlockProjection _ (B g x) q = deningerHasseBlockProjection _ x q
  rw [deningerHasseBlockProjection_apply, deningerHasseBlockProjection_apply,
    deningerMeyerConvolutionFredholmRepair_apply]
  split_ifs <;> rfl

theorem deningerMeyerConvolution_projection_comm (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) : P g (C g x) = C g (P g x) := by
  exact (congrArg (fun T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert => T x)
    (deningerMeyerHilbertConvolution_comm_blockProjection g
      (deningerMeyerConvolutionResonance g))).symm

theorem deningerMeyerConvolution_projection_sq (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) : P g (P g x) = P g x := by
  exact congrArg (fun T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert => T x)
    (deningerHasseBlockProjection_idempotent (deningerMeyerConvolutionResonance g))

theorem deningerMeyerConvolutionFredholmInverse_projection (g : DeningerMeyerStrongLogTarget)
    (f : DeningerArithmeticJetHilbert) : P g (R g f) = P g f := by
  rw [← deningerMeyerConvolutionRepair_projection g (R g f),
    deningerMeyerConvolutionFredholmInverse_right]

theorem deningerMeyerConvolution_complement_solution (g : DeningerMeyerStrongLogTarget)
    (f : DeningerArithmeticJetHilbert) :
    let x := R g (f-P g f)
    P g x = 0 ∧ x + C g x = f-P g f := by
  dsimp only
  have hp : P g (R g (f-P g f)) = 0 := by
    rw [deningerMeyerConvolutionFredholmInverse_projection, map_sub,
      deningerMeyerConvolution_projection_sq, sub_self]
  refine ⟨hp, ?_⟩
  have h := deningerMeyerConvolutionFredholmInverse_right g (f-P g f)
  change R g (f-P g f) + C g (R g (f-P g f)-P g (R g (f-P g f))) = _ at h
  simpa only [hp, sub_zero] using h

/-- All infinite-dimensional solving is paid; only the finite original block equation remains. -/
theorem deningerMeyerConvolution_equation_iff (g : DeningerMeyerStrongLogTarget)
    (f x : DeningerArithmeticJetHilbert) :
    x + C g x = f ↔
      P g x + C g (P g x) = P g f ∧
      x-P g x = R g (f-P g f) := by
  constructor
  · intro hx
    have hp := congrArg (P g) hx
    rw [map_add, deningerMeyerConvolution_projection_comm] at hp
    refine ⟨hp, ?_⟩
    have hb : B g (x-P g x) = f-P g f := by
      change (x-P g x)+C g ((x-P g x)-P g (x-P g x)) = _
      rw [map_sub (P g), deningerMeyerConvolution_projection_sq, sub_self, sub_zero, map_sub]
      rw [← hp, ← hx]
      abel
    rw [← deningerMeyerConvolutionFredholmInverse_left g (x-P g x), hb]
  · rintro ⟨hp, hx⟩
    have hc := (deningerMeyerConvolution_complement_solution g f).2
    rw [← hx, map_sub] at hc
    have he := congrArg₂ (· + ·) hc hp
    have hl : (x-P g x + (C g x-C g (P g x))) + (P g x+C g (P g x)) = x+C g x := by abel
    have hr : f-P g f+P g f = f := by abel
    simpa only [hl, hr] using he

/-- Homogeneous solutions are exactly the finite resonant full-Hasse solutions. -/
theorem deningerMeyerConvolution_kernel_iff (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) :
    x + C g x = 0 ↔ P g x = x ∧ P g x + C g (P g x) = 0 := by
  rw [deningerMeyerConvolution_equation_iff]
  simp only [map_zero, sub_zero]
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨(sub_eq_zero.mp hx).symm, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨h, by rw [hx, sub_self]⟩

def deningerMeyerConvolutionResonantPacket (g : DeningerMeyerStrongLogTarget) :
    Finset XiDivisorSupport := (deningerMeyerConvolutionResonance_finite g).toFinset

/-- The entire exceptional part of any completed forcing has a literal causal source. -/
theorem deningerMeyerConvolution_projection_realized (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) :
    ∃ u : DeningerMeyerStrongLogCohomology, deningerMeyerHasseHilbertLM u = P g x := by
  let S := deningerMeyerConvolutionResonantPacket g
  let c : DeningerMeyerFiniteXiJetPacket S := fun q =>
    x ⟨q.1.1, q.2⟩ * (q.2.val.factorial : ℂ)
  refine ⟨deningerMeyerFiniteXiCausalSection S c, ?_⟩
  apply lp.ext
  funext q
  change deningerMeyerXiSupportJetEvaluationLM q.1 q.2
    (deningerMeyerFiniteXiCausalSection S c)/(q.2.val.factorial : ℂ) =
      deningerHasseBlockProjection _ x q
  rw [deningerHasseBlockProjection_apply]
  have he : q.1 ∈ deningerMeyerConvolutionResonance g ↔ q.1 ∈ S := by
    simp only [S, deningerMeyerConvolutionResonantPacket, Set.Finite.mem_toFinset]
  by_cases hq : q.1 ∈ S
  · rw [if_pos (he.mpr hq)]
    have hj := congrFun (deningerMeyerFiniteXiCausalSection_jets S c) ⟨⟨q.1, hq⟩, q.2⟩
    change deningerMeyerXiSupportJetEvaluationLM q.1 q.2
      (deningerMeyerFiniteXiCausalSection S c) = x q * (q.2.val.factorial : ℂ) at hj
    rw [hj, mul_div_cancel_right₀]
    exact_mod_cast Nat.factorial_ne_zero q.2.val
  · rw [if_neg (fun h => hq (he.mp h)),
      deningerMeyerFiniteXiCausalSection_other_jet_zero S q.1 hq, zero_div]

/-- The finite correction is the original causal projector on literal cohomology. -/
theorem deningerMeyerConvolution_projection_source (g : DeningerMeyerStrongLogTarget)
    (u : DeningerMeyerStrongLogCohomology) :
    P g (deningerMeyerHasseHilbertLM u) = deningerMeyerHasseHilbertLM
      (deningerMeyerFiniteXiCausalProjector (deningerMeyerConvolutionResonantPacket g) u) := by
  let S := deningerMeyerConvolutionResonantPacket g
  apply lp.ext
  funext q
  change deningerHasseBlockProjection _ (deningerMeyerHasseHilbertLM u) q =
    deningerMeyerXiSupportJetEvaluationLM q.1 q.2
      (deningerMeyerFiniteXiCausalSection S (deningerMeyerFiniteXiJetPacketLM S u)) /
        (q.2.val.factorial : ℂ)
  rw [deningerHasseBlockProjection_apply]
  have he : q.1 ∈ deningerMeyerConvolutionResonance g ↔ q.1 ∈ S := by
    simp only [S, deningerMeyerConvolutionResonantPacket, Set.Finite.mem_toFinset]
  by_cases hq : q.1 ∈ S
  · rw [if_pos (he.mpr hq)]
    have hj := congrFun (deningerMeyerFiniteXiCausalSection_jets S
      (deningerMeyerFiniteXiJetPacketLM S u)) ⟨⟨q.1, hq⟩, q.2⟩
    exact (congrArg (fun z : ℂ => z/(q.2.val.factorial : ℂ)) hj).symm
  · rw [if_neg (fun h => hq (he.mp h)),
      deningerMeyerFiniteXiCausalSection_other_jet_zero S q.1 hq, zero_div]

theorem deningerMeyerConvolutionRepair_source (g : DeningerMeyerStrongLogTarget)
    (u : DeningerMeyerStrongLogCohomology) :
    B g (deningerMeyerHasseHilbertLM u) = deningerMeyerHasseHilbertLM
      (u + deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g)
        (u-deningerMeyerFiniteXiCausalProjector (deningerMeyerConvolutionResonantPacket g) u)) := by
  change deningerMeyerHasseHilbertLM u +
    C g (deningerMeyerHasseHilbertLM u-P g (deningerMeyerHasseHilbertLM u)) = _
  rw [deningerMeyerConvolution_projection_source, ← map_sub,
    deningerMeyerHilbertConvolution_source, map_add]

end RHTower
