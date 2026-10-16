import GaloisForLFunctions.RHTower.PaperThetaConfluentNativeSolvability
import GaloisForLFunctions.RHTower.PaperThetaNativeGrushinArithmetic
import GaloisForLFunctions.RHTower.PaperThetaCompactMeyerRealization

/-!
# Native regularity of the confluent solver

The actual Grushin inverse preserves bounded variation, by its spatial
solution and the fixed Green identity. Whole-domain uniqueness identifies
the uniform Green operator with the native BV resolvent. Its powers
intertwine the pencil with the literal repeated spatial theta action.
-/

noncomputable section
open Complex Set Module Filter Topology
open scoped BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint

def nativeShiftAction (z : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => thetaSpatialAction f x-z*f x

theorem nativeShiftAction_compact (z : ℂ) (g : NativeContinuousSpace) :
    nativeShiftAction z (nativeCompactResolvent g) = nativePencil z g := by
  funext x
  have h := boundedNativeResolvent_equation nativeCompactParameter g x
  rw [nativeCompactParameter_val] at h
  change thetaSpatialAction (nativeCompactResolvent g) x-I*nativeCompactResolvent g x=g x at h
  change thetaSpatialAction (nativeCompactResolvent g) x-z*nativeCompactResolvent g x =
    g x+(I-z)*nativeCompactResolvent g x
  linear_combination h

theorem nativePencil_compact_commute (z : ℂ) : Commute (nativePencil z) nativeCompactResolvent := by
  apply ContinuousLinearMap.ext
  intro g
  change nativeCompactResolvent g+(I-z) • nativeCompactResolvent (nativeCompactResolvent g) =
    nativeCompactResolvent (g+(I-z) • nativeCompactResolvent g)
  rw [map_add,map_smul]

theorem nativeShiftAction_iterate_compact (z : ℂ) (n : ℕ) (g : NativeContinuousSpace) :
    (nativeShiftAction z)^[n] ((nativeCompactResolvent^n) g) = (nativePencil z^n) g := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    have hc : nativePencil z ((nativeCompactResolvent^n) g) =
        (nativeCompactResolvent^n) (nativePencil z g) :=
      congrArg (fun A : NativeContinuousSpace →L[ℂ] NativeContinuousSpace => A g)
        ((nativePencil_compact_commute z).pow_right n).eq
    rw [pow_succ',mul_apply_eq_comp,Function.iterate_succ_apply,
      nativeShiftAction_compact,hc,ih,pow_succ,mul_apply_eq_comp]

theorem nativeThetaResolvent_uniform (z : ThetaRegularParameter) (g : ThetaContinuousBV) :
    nativeBVUniform (nativeThetaResolvent z g).toThetaContinuousBV =
      boundedNativeResolvent z (nativeBVUniform g) := by
  apply boundedNativeResolvent_unique z (nativeBVUniform g)
    (nativeBVUniform (nativeThetaResolvent z g).toThetaContinuousBV)
    (thetaTailTrace (nativeThetaResolvent z g))
    (nativeThetaResolvent z g).differentiable (nativeThetaResolvent z g).rightTrace
  intro x
  have h := nativeThetaResolvent_equation z g x
  rw [thetaSpatialAction] at h
  change deriv (nativeThetaResolvent z g) x+
    sourceLogDerivative x*(nativeThetaResolvent z g x-thetaTailTrace (nativeThetaResolvent z g))+
    I*z.val*nativeThetaResolvent z g x = -I*g x
  linear_combination (norm := ring_nf) (-I)*h
  simp [Complex.I_sq]

private theorem native_bv_add {f g : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    (hg : BoundedVariationOn g univ) : BoundedVariationOn (fun x => f x+g x) univ := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf,hg⟩)
  apply iSup_le
  rintro ⟨n,⟨u,hu,hs⟩⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, (edist (f (u (i+1))) (f (u i))+edist (g (u (i+1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i _
      exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i)))+
        ∑ i ∈ Finset.range n, edist (g (u (i+1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hs) (eVariationOn.sum_le hu hs)

def nativeBVSubspace : Submodule ℂ NativeContinuousSpace where
  carrier := {f | BoundedVariationOn f univ}
  zero_mem' := by
    change eVariationOn (fun _ : ℝ => (0 : ℂ)) univ ≠ ⊤
    rw [eVariationOn.constant_on (by
      rintro _ ⟨a,_,rfl⟩ _ ⟨b,_,rfl⟩
      rfl)]
    exact ENNReal.zero_ne_top
  add_mem' hf hg := native_bv_add hf hg
  smul_mem' c f hf := by
    change BoundedVariationOn (fun x => c*f x) univ
    simpa only [zero_add] using boundedVariation_affine hf 0 c

theorem nativeFiniteSynthesis_bv (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) : nativeFiniteSynthesis S c ∈ nativeBVSubspace := by
  unfold nativeFiniteSynthesis
  rw [Fintype.linearCombination_apply]
  apply nativeBVSubspace.sum_mem
  intro q _
  apply nativeBVSubspace.smul_mem
  apply nativeBVSubspace.smul_mem
  exact boundedVariationOn_divisor_flatParameterJet q.1.val q.2

private theorem native_root_bv (rho : XiDivisorSupport) {g : NativeContinuousSpace}
    (hg : g ∈ (nativeResonantChannel rho).rootSpace) : g ∈ nativeBVSubspace := by
  rw [nativeResonantChannel_root,nativeXiRootBlock_eq_original_packet] at hg
  obtain ⟨c,rfl⟩ := hg
  exact nativeFiniteSynthesis_bv {rho} c

def nativeBVOfUniform (g : NativeContinuousSpace) (hg : g ∈ nativeBVSubspace) : ThetaContinuousBV :=
  ⟨g,g.continuous,hg⟩

@[simp] theorem nativeBVUniform_ofUniform (g : NativeContinuousSpace) (hg : g ∈ nativeBVSubspace) :
    nativeBVUniform (nativeBVOfUniform g hg) = g := by
  ext x
  rfl

theorem nativeResonantPartialInverse_bv (z : ℂ) {g : NativeContinuousSpace}
    (hg : g ∈ nativeBVSubspace) : nativeResonantPartialInverse z g ∈ nativeBVSubspace := by
  have he : (⇑(nativeCompactResolvent (nativeResonantPartialInverse z g))) =
      (nativeGrushinBV z (nativeBVOfUniform g hg) 0 : ℝ → ℂ) := by
    funext x
    rw [nativeGrushinBV_apply,nativeBVUniform_ofUniform]
    exact congrArg (fun h : NativeContinuousSpace => h x) (nativeGrushinProfile_eq_solution z g 0)
  have hk : nativeCompactResolvent (nativeResonantPartialInverse z g) ∈ nativeBVSubspace := by
    change BoundedVariationOn _ univ
    rw [he]
    exact (nativeGrushinBV z (nativeBVOfUniform g hg) 0).bv
  have hp := nativeResonantParticular_equation z g
  change nativeResonantPartialInverse z g+(I-z) •
    nativeCompactResolvent (nativeResonantPartialInverse z g) =
    g-(boundedThetaMomentCLM z g/(nativeCounterMass : ℂ)) • nativeCounterSource z at hp
  rw [eq_sub_of_add_eq hp]
  exact nativeBVSubspace.sub_mem
    (nativeBVSubspace.sub_mem hg (nativeBVSubspace.smul_mem _ (nativeCounterSource_boundedVariation z)))
    (nativeBVSubspace.smul_mem _ hk)

theorem nativeResonantChannel_mode_bv (rho : XiDivisorSupport) :
    (nativeResonantChannel rho).mode ∈ nativeBVSubspace := by
  apply native_root_bv rho
  apply ((nativeResonantChannel rho).mem_rootSpace _).mpr
  exact ⟨1,by simpa only [pow_one] using (nativeResonantChannel rho).mode_kernel⟩

theorem nativeConfluentComplementInverse_bv (rho : XiDivisorSupport) {g : NativeContinuousSpace}
    (hg : g ∈ nativeBVSubspace) : (nativeResonantChannel rho).complementInverse g ∈ nativeBVSubspace := by
  rw [(nativeResonantChannel rho).complementInverse_apply]
  exact nativeBVSubspace.sub_mem (nativeResonantPartialInverse_bv _ hg)
    (nativeBVSubspace.smul_mem _ (nativeResonantChannel_mode_bv rho))

theorem nativeConfluentComplementInverse_pow_bv (rho : XiDivisorSupport) (n : ℕ)
    {g : NativeContinuousSpace} (hg : g ∈ nativeBVSubspace) :
    ((nativeResonantChannel rho).complementInverse^n) g ∈ nativeBVSubspace := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [pow_succ',Module.End.mul_apply]
    exact nativeConfluentComplementInverse_bv rho ih

theorem nativeConfluentPowerSolver_bv (rho : XiDivisorSupport) (n : ℕ)
    {g : NativeContinuousSpace} (hg : g ∈ nativeBVSubspace) :
    nativeConfluentPowerSolver rho n g ∈ nativeBVSubspace := by
  change (nativeConfluentPowerSolver rho n).toLinearMap g ∈ nativeBVSubspace
  rw [nativeConfluentPowerSolver_linear]
  change ((nativeResonantChannel rho).complementInverse^n)
    (g-(nativeResonantChannel rho).projection g)+
      (nativeResonantChannel rho).rootPowerLift n g ∈ nativeBVSubspace
  exact nativeBVSubspace.add_mem
    (nativeConfluentComplementInverse_pow_bv rho n
      (nativeBVSubspace.sub_mem hg (native_root_bv rho ((nativeResonantChannel rho).projection_mem g))))
    (native_root_bv rho ((nativeResonantChannel rho).rootPowerLift_mem n g))

theorem nativeCompactResolvent_bv {g : NativeContinuousSpace} (hg : g ∈ nativeBVSubspace) :
    nativeCompactResolvent g ∈ nativeBVSubspace := by
  have h := nativeThetaResolvent_uniform nativeCompactParameter (nativeBVOfUniform g hg)
  rw [nativeBVUniform_ofUniform] at h
  change nativeBVUniform (nativeThetaResolvent nativeCompactParameter (nativeBVOfUniform g hg)).toThetaContinuousBV =
    nativeCompactResolvent g at h
  rw [← h]
  exact (nativeThetaResolvent nativeCompactParameter (nativeBVOfUniform g hg)).bv

theorem nativeCompactResolvent_pow_bv (n : ℕ) {g : NativeContinuousSpace}
    (hg : g ∈ nativeBVSubspace) : (nativeCompactResolvent^n) g ∈ nativeBVSubspace := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact nativeCompactResolvent_bv ih

end RHTower.PaperThetaEndpoint
