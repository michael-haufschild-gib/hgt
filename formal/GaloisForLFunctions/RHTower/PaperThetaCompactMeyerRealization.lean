import GaloisForLFunctions.RHTower.PaperThetaNativeResolventSpectrum
import GaloisForLFunctions.RHTower.PaperThetaSpatialSolvability

/-! # Original Meyer packets inside the global compact theta resolvent

Every full-multiplicity original source packet embeds faithfully in the actual
uniform space. The global compact operator solves its centered generator
equation, retaining the confluent predecessors rather than semisimplifying.
-/

noncomputable section
open Set Filter Topology Complex
open scoped BoundedContinuousFunction Classical

namespace RHTower.PaperThetaEndpoint

def nativeThetaDivisorJet (rho : XiDivisorSupport) (j : Fin (xiSupportMultiplicity rho)) :
    NativeContinuousSpace :=
  let f : ThetaContinuousBV :=
    ⟨flatParameterJet j.val (xiSpectralPointSupport rho), continuous_flatParameterJet _ _,
      boundedVariationOn_divisor_flatParameterJet rho j⟩
  BoundedContinuousFunction.ofNormedAddCommGroup f f.continuous f.bound f.norm_le

@[simp] theorem nativeThetaDivisorJet_apply (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) (x : ℝ) :
    nativeThetaDivisorJet rho j x = flatParameterJet j.val (xiSpectralPointSupport rho) x := rfl

def nativeFiniteSynthesis (S : Finset XiDivisorSupport) :
    DeningerMeyerFiniteXiJetPacket S →ₗ[ℂ] NativeContinuousSpace :=
  Fintype.linearCombination ℂ (fun q : DeningerMeyerFiniteXiJetSlot S =>
    (q.2.val.factorial : ℂ)⁻¹ • nativeThetaDivisorJet q.1.1 q.2)

theorem nativeFiniteSynthesis_apply (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) (x : ℝ) :
    nativeFiniteSynthesis S c x = ∑ q : DeningerMeyerFiniteXiJetSlot S,
      c q*((q.2.val.factorial : ℂ)⁻¹*flatParameterJet q.2.val (xiSpectralPointSupport q.1.1) x) := by
  simp only [nativeFiniteSynthesis, Fintype.linearCombination_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, nativeThetaDivisorJet_apply]

theorem nativeFiniteSynthesis_coe (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    (nativeFiniteSynthesis S c : ℝ → ℂ) = (thetaFiniteSynthesis S c).val := by
  funext x
  simp only [nativeFiniteSynthesis_apply, thetaFiniteSynthesis, Fintype.linearCombination_apply,
    Submodule.coe_sum, Submodule.coe_smul, thetaRightHasseJet, thetaRightJet,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem nativeFiniteSynthesis_injective (S : Finset XiDivisorSupport) :
    Function.Injective (nativeFiniteSynthesis S) := by
  intro c d h
  apply thetaFiniteSynthesis_injective S
  apply Subtype.ext
  simpa only [nativeFiniteSynthesis_coe] using
    congrArg (fun f : NativeContinuousSpace => (f : ℝ → ℂ)) h

theorem nativeFiniteSynthesis_differentiable (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) : Differentiable ℝ (nativeFiniteSynthesis S c) := by
  have he : (nativeFiniteSynthesis S c : ℝ → ℂ) = fun x =>
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        c q*((q.2.val.factorial : ℂ)⁻¹*flatParameterJet q.2.val (xiSpectralPointSupport q.1.1) x) :=
    funext (nativeFiniteSynthesis_apply S c)
  rw [he]
  exact Differentiable.fun_sum (fun q _ =>
    ((differentiable_flatParameterJet q.2.val (xiSpectralPointSupport q.1.1)).const_mul _).const_mul _)

def nativeFiniteTrace (S : Finset XiDivisorSupport) (c : DeningerMeyerFiniteXiJetPacket S) : ℂ :=
  ∑ q : DeningerMeyerFiniteXiJetSlot S, c q*((q.2.val.factorial : ℂ)⁻¹*parameterEndpointTrace q.2.val)

theorem nativeFiniteSynthesis_atTop (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    Tendsto (nativeFiniteSynthesis S c) atTop (𝓝 (nativeFiniteTrace S c)) := by
  have ht := tendsto_finsetSum (Finset.univ : Finset (DeningerMeyerFiniteXiJetSlot S))
    (fun q _ => ((tendsto_flatParameterJet_atTop q.2.val (xiSpectralPointSupport q.1.1)).const_mul
      ((q.2.val.factorial : ℂ)⁻¹)).const_mul (c q))
  change Tendsto (fun x => nativeFiniteSynthesis S c x) atTop _
  simp only [nativeFiniteSynthesis_apply]
  exact ht

theorem nativeFiniteSynthesis_generator (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    thetaSpatialAction (nativeFiniteSynthesis S c) =
      (nativeFiniteSynthesis S (thetaFinitePacketGenerator S c) : ℝ → ℂ) := by
  rw [nativeFiniteSynthesis_coe, nativeFiniteSynthesis_coe]
  exact congrArg Subtype.val (thetaFiniteSynthesis_generator S c)

theorem nativeCompactResolvent_finite_shift (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    nativeCompactResolvent (nativeFiniteSynthesis S (thetaFinitePacketGenerator S c-I • c)) =
      nativeFiniteSynthesis S c := by
  symm
  apply boundedNativeResolvent_unique nativeCompactParameter _ _ (nativeFiniteTrace S c)
    (nativeFiniteSynthesis_differentiable S c) (nativeFiniteSynthesis_atTop S c)
  intro x
  have ht : thetaTailTrace (nativeFiniteSynthesis S c) = nativeFiniteTrace S c :=
    (nativeFiniteSynthesis_atTop S c).limUnder_eq
  have he := congrFun (nativeFiniteSynthesis_generator S c) x
  rw [thetaSpatialAction, ht] at he
  rw [nativeCompactParameter_val, map_sub, map_smul]
  change deriv (nativeFiniteSynthesis S c) x+
      sourceLogDerivative x*(nativeFiniteSynthesis S c x-nativeFiniteTrace S c)+
      I*I*nativeFiniteSynthesis S c x =
    -I*(nativeFiniteSynthesis S (thetaFinitePacketGenerator S c) x-I*nativeFiniteSynthesis S c x)
  linear_combination (norm := ring_nf) -I*he
  simp only [Complex.I_sq]
  ring

/-- Actual original-source classes, in their full finite multiplicities. -/
def meyerFiniteUniformEmbedding (S : Finset XiDivisorSupport) :
    LinearMap.range (meyerFiniteHedenmalmSynthesis S) →ₗ[ℂ] NativeContinuousSpace :=
  (nativeFiniteSynthesis S).comp (meyerFiniteHedenmalmCoordinates S).symm.toLinearMap

@[simp] theorem meyerFiniteUniformEmbedding_coordinates (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    meyerFiniteUniformEmbedding S (meyerFiniteHedenmalmCoordinates S c) = nativeFiniteSynthesis S c := by
  simp [meyerFiniteUniformEmbedding]

theorem meyerFiniteUniformEmbedding_injective (S : Finset XiDivisorSupport) :
    Function.Injective (meyerFiniteUniformEmbedding S) :=
  (nativeFiniteSynthesis_injective S).comp (meyerFiniteHedenmalmCoordinates S).symm.injective

/-- The same global compact operator inverts every actual finite Meyer shift. -/
theorem nativeCompactResolvent_meyer_shift (S : Finset XiDivisorSupport)
    (u : LinearMap.range (meyerFiniteHedenmalmSynthesis S)) :
    nativeCompactResolvent
      (meyerFiniteUniformEmbedding S (meyerFiniteCenteredGenerator S u-I • u)) =
      meyerFiniteUniformEmbedding S u := by
  obtain ⟨c, rfl⟩ := (meyerFiniteHedenmalmCoordinates S).surjective u
  rw [meyerFiniteCenteredGenerator_coordinates, map_sub, map_smul,
    meyerFiniteUniformEmbedding_coordinates, meyerFiniteUniformEmbedding_coordinates,
    ← map_smul, ← map_sub]
  exact nativeCompactResolvent_finite_shift S c

/-- Every original finite source equation is solved by restriction of the one
global compact Green operator; all full Jordan slots remain injective. -/
theorem nativeCompactResolvent_meyer_realization (S : Finset XiDivisorSupport) :
    Function.Injective (meyerFiniteUniformEmbedding S) ∧
      ∀ u : LinearMap.range (meyerFiniteHedenmalmSynthesis S),
        ∃! v : LinearMap.range (meyerFiniteHedenmalmSynthesis S),
          meyerFiniteCenteredGenerator S v-I • v = u ∧
            nativeCompactResolvent (meyerFiniteUniformEmbedding S u) = meyerFiniteUniformEmbedding S v := by
  refine ⟨meyerFiniteUniformEmbedding_injective S, ?_⟩
  intro u
  obtain ⟨w, hw⟩ := (thetaFiniteSpatialImaginaryShift_bijective S 1).surjective (meyerThetaFiniteEquiv S u)
  let v := (meyerThetaFiniteEquiv S).symm w
  have hv : meyerFiniteCenteredGenerator S v-I • v = u := by
    apply (meyerThetaFiniteEquiv S).injective
    rw [map_sub, map_smul, meyerThetaFiniteEquiv_generator]
    simp only [v, LinearEquiv.apply_symm_apply]
    simp only [Complex.ofReal_one, mul_one] at hw
    change thetaFiniteSpatialGenerator S w-I • w = meyerThetaFiniteEquiv S u at hw
    exact hw
  have hR : nativeCompactResolvent (meyerFiniteUniformEmbedding S u) = meyerFiniteUniformEmbedding S v := by
    rw [← hv]
    exact nativeCompactResolvent_meyer_shift S v
  refine ⟨v, ⟨hv, hR⟩, ?_⟩
  intro v' hv'
  exact (meyerFiniteUniformEmbedding_injective S) (hv'.2.symm.trans hR)

end RHTower.PaperThetaEndpoint
