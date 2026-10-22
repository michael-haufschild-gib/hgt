/-
# Common-domain causal-depth Gamma--Robin trace no-go

The bounded and weakly bounded `L²` Robin classes do not exhaust fixed-domain
singular constructions: an unbounded ambient observer can become bounded on a
common Hilbert graph domain.  This module closes that survivor when the carrier
enters and exits that graph domain through fixed Hilbert--Schmidt maps.

Weak matrix-coefficient boundedness on the common graph domain gives a uniform
operator-norm bound by the two-level uniform boundedness theorem.  The
Hilbert--Schmidt ideal inequality then bounds the scalar trace correction
uniformly.  The natural Suzuki transition core has Ward defect tending to
minus infinity after subtraction of every correction bounded above, so no
such producer can supply the lower semibound required by the CCM--FU endpoint.

The surviving singular mechanism must therefore leave at least one of these
classes: fixed common graph domain, weak graph boundedness, domain preservation,
or fixed Hilbert--Schmidt ingress/egress.
-/
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaWeakRobinTraceNoGo
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

open Set Filter Complex
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower
open ContinuousLinearMap

variable {D : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

/-- Scalar trace correction emitted by a domain-preserving observer between
fixed Hilbert--Schmidt ingress and egress maps. -/
def suzukiCausalDepthGammaCommonDomainTraceCorrection
    (entry : SuzukiCausalDepthGammaTraceL2 →L[ℂ] D)
    (exit : D →L[ℂ] SuzukiCausalDepthGammaTraceL2)
    (observer : ℕ → D →L[ℂ] D) (N : ℕ) : ℝ :=
  (ContinuousLinearMap.opTrace
    (exit ∘L (observer N ∘L entry))).re

/-- The common-domain trace correction is controlled by the two fixed
Hilbert--Schmidt norms and the graph-domain observer norm. -/
theorem suzukiCausalDepthGammaCommonDomainTraceCorrection_le
    (entry : SuzukiCausalDepthGammaTraceL2 →L[ℂ] D)
    (exit : D →L[ℂ] SuzukiCausalDepthGammaTraceL2)
    (observer : ℕ → D →L[ℂ] D)
    (hentry : ContinuousLinearMap.IsHilbertSchmidt entry)
    (hexit : ContinuousLinearMap.IsHilbertSchmidt exit)
    (N : ℕ) :
    suzukiCausalDepthGammaCommonDomainTraceCorrection entry exit observer N ≤
      ContinuousLinearMap.hsNorm exit *
        (‖observer N‖ * ContinuousLinearMap.hsNorm entry) := by
  have hcomp : ContinuousLinearMap.IsHilbertSchmidt
      (observer N ∘L entry) :=
    hentry.comp_left (observer N)
  calc
    suzukiCausalDepthGammaCommonDomainTraceCorrection entry exit observer N ≤
        |suzukiCausalDepthGammaCommonDomainTraceCorrection
          entry exit observer N| :=
      le_abs_self _
    _ ≤ ‖ContinuousLinearMap.opTrace
          (exit ∘L (observer N ∘L entry))‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ContinuousLinearMap.hsNorm exit *
          ContinuousLinearMap.hsNorm (observer N ∘L entry) :=
      ContinuousLinearMap.norm_opTrace_comp_le hexit hcomp
    _ ≤ ContinuousLinearMap.hsNorm exit *
          (‖observer N‖ * ContinuousLinearMap.hsNorm entry) :=
      mul_le_mul_of_nonneg_left (hentry.hsNorm_comp_left_le (observer N))
        (ContinuousLinearMap.hsNorm_nonneg exit)

/-- Weak graph-domain matrix-coefficient boundedness cannot produce a
lower-semibounded corrected transition-core Ward defect through a fixed
Hilbert--Schmidt sandwich. -/
theorem no_weaklyPointwiseBounded_commonDomainGammaTrace_WardProducer
    (entry : SuzukiCausalDepthGammaTraceL2 →L[ℂ] D)
    (exit : D →L[ℂ] SuzukiCausalDepthGammaTraceL2)
    (hentry : ContinuousLinearMap.IsHilbertSchmidt entry)
    (hexit : ContinuousLinearMap.IsHilbertSchmidt exit) :
    ¬ ∃ (L lower : ℝ) (observer : ℕ → D →L[ℂ] D),
      (∀ x y : D,
        BddAbove (Set.range fun N : ℕ => ‖inner ℂ (observer N x) y‖)) ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiCausalDepthGammaCommonDomainTraceCorrection
              entry exit observer N)
          (8 * n) := by
  rintro ⟨L, lower, observer, hweak, hlower⟩
  obtain ⟨M, _, hM⟩ :=
    uniformlyBounded_of_weaklyPointwiseBounded observer hweak
  have hbound : ∀ N,
      suzukiCausalDepthGammaCommonDomainTraceCorrection
          entry exit observer N ≤
        ContinuousLinearMap.hsNorm exit *
          (M * ContinuousLinearMap.hsNorm entry) := by
    intro N
    exact (suzukiCausalDepthGammaCommonDomainTraceCorrection_le
      entry exit observer hentry hexit N).trans
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hM N)
            (ContinuousLinearMap.hsNorm_nonneg entry))
          (ContinuousLinearMap.hsNorm_nonneg exit))
  have hfall :=
    tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot
      L (correction :=
        suzukiCausalDepthGammaCommonDomainTraceCorrection
          entry exit observer)
      (B := ContinuousLinearMap.hsNorm exit *
        (M * ContinuousLinearMap.hsNorm entry)) hbound
  have hbelow : ∀ᶠ n : ℕ in atTop,
      suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiCausalDepthGammaCommonDomainTraceCorrection
            entry exit observer N)
        (8 * n) ≤ lower - 1 :=
    (tendsto_atBot.1 hfall) (lower - 1)
  rcases (hlower.and hbelow).exists with ⟨n, hlow, hhigh⟩
  linarith

/-- A fixed common graph-domain Ward producer with Hilbert--Schmidt ingress and
egress and weakly bounded graph-domain observers. -/
structure SuzukiCausalDepthGammaCommonDomainWardProducer where
  Graph : Type
  [graphNormedAddCommGroup : NormedAddCommGroup Graph]
  [graphInnerProductSpace : InnerProductSpace ℂ Graph]
  [graphCompleteSpace : CompleteSpace Graph]
  entry : SuzukiCausalDepthGammaTraceL2 →L[ℂ] Graph
  exit : Graph →L[ℂ] SuzukiCausalDepthGammaTraceL2
  entry_hilbertSchmidt : ContinuousLinearMap.IsHilbertSchmidt entry
  exit_hilbertSchmidt : ContinuousLinearMap.IsHilbertSchmidt exit
  observer : ℕ → Graph →L[ℂ] Graph
  observer_weaklyPointwiseBounded : ∀ x y : Graph,
    BddAbove (Set.range fun N : ℕ => ‖inner ℂ (observer N x) y‖)
  wardScale : ℝ
  lowerFloor : ℝ
  eventually_lowerSemibounded : ∀ᶠ n : ℕ in atTop,
    lowerFloor ≤ suzukiRectangularWardDefect wardScale
      (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
        suzukiCausalDepthGammaCommonDomainTraceCorrection
          entry exit observer N)
      (8 * n)

/-- **Common graph-domain Gamma--Robin no-go.**  No fixed common Hilbert graph
domain, Hilbert--Schmidt ingress/egress, and weakly bounded domain-preserving
observer family can lower-semibound the corrected Suzuki transition-core Ward
defect. -/
theorem no_suzukiCausalDepthGammaCommonDomainWardProducer :
    ¬ Nonempty SuzukiCausalDepthGammaCommonDomainWardProducer := by
  rintro ⟨producer⟩
  letI := producer.graphNormedAddCommGroup
  letI := producer.graphInnerProductSpace
  letI := producer.graphCompleteSpace
  exact no_weaklyPointwiseBounded_commonDomainGammaTrace_WardProducer
    producer.entry producer.exit producer.entry_hilbertSchmidt
      producer.exit_hilbertSchmidt
    ⟨producer.wardScale, producer.lowerFloor, producer.observer,
      producer.observer_weaklyPointwiseBounded,
      producer.eventually_lowerSemibounded⟩

end

end RHTower
