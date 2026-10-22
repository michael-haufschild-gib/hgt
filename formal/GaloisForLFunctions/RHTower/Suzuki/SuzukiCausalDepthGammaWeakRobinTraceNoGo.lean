import GaloisForLFunctions.RHTower.BarrelledNoetherReesSuperselection
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaBoundedRobinTraceNoGo

/-!
# Weakly bounded Robin observers cannot close the CCM-FU Gamma-trace producer

The preceding bounded-observer no-go assumes one uniform operator-norm bound.  Here that
hypothesis is removed.  If every fixed matrix coefficient of a bounded-operator family is
bounded over causal depth, two applications of Banach--Steinhaus recover a uniform operator-norm
bound: first for the vector orbit of each source vector, then for the operator family itself.

Consequently every weakly pointwise bounded bounded-operator realization of the fixed positive
Gamma-Schur trace carrier is impossible.  The sharp survivor is forced outside that class: any
family which semibounds the rectangular Ward defect has a single fixed pair of vectors whose
matrix coefficient is unbounded.  In particular, a successful bounded-operator family cannot
remain WOT-bounded.  No RH premise, Xi-zero hypothesis, computation, or added axiom is used.
-/

open Set Filter Complex
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- Banach--Steinhaus upgrades pointwise norm boundedness of a continuous-linear-map family on a
barrelled normed source to one operator-norm bound. -/
theorem exists_uniform_opNorm_bound_of_pointwiseBounded
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [BarrelledSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : ι → E →L[ℂ] F)
    (hpointwise : ∀ x : E, BddAbove (Set.range fun i : ι => ‖T i x‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖T i‖ ≤ C := by
  let pE : Fin 1 → Seminorm ℂ E := fun _ => normSeminorm ℂ E
  let pF : Fin 1 → Seminorm ℂ F := fun _ => normSeminorm ℂ F
  have hpE : WithSeminorms pE := by
    simpa [pE] using (norm_withSeminorms ℂ E)
  have hpF : WithSeminorms pF := by
    simpa [pF] using (norm_withSeminorms ℂ F)
  have hbdd : ∀ (k : Fin 1) (x : E),
      BddAbove (Set.range fun i : ι => pF k (T i x)) := by
    intro _ x
    simpa [pF] using hpointwise x
  have hequi : UniformEquicontinuous ((↑) ∘ T) :=
    hpF.banach_steinhaus hbdd
  have htfae :=
    (hpF.equicontinuous_TFAE (fun i => (T i : E →ₗ[ℂ] F))).out 2 3
  obtain ⟨q, hqcont, hqle⟩ := htfae.mp hequi 0
  obtain ⟨s, C, _, hqC⟩ := Seminorm.bound_of_continuous hpE q hqcont
  have hseminorm : s.sup pE ≤ normSeminorm ℂ E := by
    apply Finset.sup_le
    intro i hi
    rfl
  refine ⟨(C : ℝ), NNReal.coe_nonneg C, fun i => ?_⟩
  apply (T i).opNorm_le_bound (NNReal.coe_nonneg C)
  intro x
  refine (hqle i x).trans ((hqC x).trans ?_)
  simpa [pE, NNReal.smul_def] using
    (mul_le_mul_of_nonneg_left (hseminorm x) (NNReal.coe_nonneg C))

/-- Weak boundedness of every matrix coefficient makes each vector orbit norm bounded. -/
theorem pointwiseBounded_of_weaklyPointwiseBounded
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (T : ι → H →L[ℂ] H)
    (hweak : ∀ x y : H,
      BddAbove (Set.range fun i : ι => ‖inner ℂ (T i x) y‖)) :
    ∀ x : H, BddAbove (Set.range fun i : ι => ‖T i x‖) := by
  intro x
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_opNorm_bound_of_pointwiseBounded
      (fun i => innerSL ℂ (T i x)) (hweak x)
  refine ⟨C, ?_⟩
  rintro _ ⟨i, rfl⟩
  let v := T i x
  by_cases hv : v = 0
  · simp [v, hv, hC]
  · have hop := hbound i
    simpa [v] using hop

/-- Two-level Banach--Steinhaus: boundedness of every fixed matrix coefficient forces a uniform
operator-norm bound for the whole family. -/
theorem uniformlyBounded_of_weaklyPointwiseBounded
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (T : ι → H →L[ℂ] H)
    (hweak : ∀ x y : H,
      BddAbove (Set.range fun i : ι => ‖inner ℂ (T i x) y‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖T i‖ ≤ C := by
  exact exists_uniform_opNorm_bound_of_pointwiseBounded T
    (pointwiseBounded_of_weaklyPointwiseBounded T hweak)

/-- Every matrix coefficient of the causal-depth bounded-operator observer family is bounded. -/
def SuzukiCausalDepthGammaObserverWeaklyPointwiseBounded
    (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) : Prop :=
  ∀ x y : SuzukiCausalDepthGammaTraceL2,
    BddAbove (Set.range fun N : ℕ => ‖inner ℂ (observer N x) y‖)

/-- **Closed producer-class kill.**  No weakly pointwise bounded bounded-operator family on the
fixed positive Gamma-Schur trace carrier can semibound the transition-core Ward defect. -/
theorem no_weaklyPointwiseBounded_causalDepthGammaTrace_WardProducer :
    ¬ ∃ (L lower : ℝ)
      (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
        SuzukiCausalDepthGammaTraceL2),
      SuzukiCausalDepthGammaObserverWeaklyPointwiseBounded observer ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N)
          (8 * n) := by
  rintro ⟨L, lower, observer, hweak, hlower⟩
  obtain ⟨M, _, hM⟩ :=
    uniformlyBounded_of_weaklyPointwiseBounded observer hweak
  exact no_uniformlyBounded_causalDepthGammaTrace_WardProducer
    ⟨L, M, lower, observer, hM, hlower⟩

/-- **Sharp positive survivor.**  Any bounded-operator Gamma-trace observer family which
semibounds the Ward defect has one fixed matrix coefficient unbounded over causal depth. -/
theorem exists_unbounded_causalDepthGammaObserver_matrixCoefficient_of_Ward_bddBelow
    (L : ℝ)
    (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (lower : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N)
        (8 * n)) :
    ∃ x y : SuzukiCausalDepthGammaTraceL2,
      ¬ BddAbove (Set.range fun N : ℕ => ‖inner ℂ (observer N x) y‖) := by
  by_contra hmatrix
  push Not at hmatrix
  exact no_weaklyPointwiseBounded_causalDepthGammaTrace_WardProducer
    ⟨L, lower, observer, hmatrix, hlower⟩

end

end RHTower
