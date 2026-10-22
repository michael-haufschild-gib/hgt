import GaloisForLFunctions.RHTower.SoninGammaClockSchwartzLimit
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanNuclearContinuity
import GaloisForLFunctions.RHTower.StrongTraceNormMultiplierLimit
import GaloisForLFunctions.RHTower.TraceNormLimit

/-!
# Original Gamma clock cutoffs in the tested Hardy nuclear ideal

For every fixed Schwartz test g, the literal original clock operator
M_g (U_(eps,R)^* P U_(eps,R)-P) belongs to the genuine Schatten-one ideal.
The exact multiplier product and H=2P-1 identify it with
(1/2) U_(eps,R)^* (delta(U_(eps,R)g)-delta(g) U_(eps,R)).

Original-cutoff Schwartz convergence admits the varying differential in S1.
Bounded strong convergence of the unitaries and their inverses admits both
remaining actions. The resulting trace-norm limit is precisely the original
CCM Gamma tested Hardy projection difference; ordinary cubic traces converge.
Every countably generated cofinal endpoint family has the same limit.

The Schwartz test is retained. This does not assert nuclearity of the bare
projection difference, admit the prime–polar source, identify the completed
joint cubic, or prove the TG strict sub-unit law.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology MeasureTheory ContinuousLinearMap Set
open scoped SchwartzMap
namespace RHTower

private def leftNuclear (A : SoninL2 →L[ℂ] SoninL2) (T : SchattenOneOperator SoninL2) :
    SchattenOneOperator SoninL2 := ⟨A ∘L T.val, memSchattenClass_one_comp_left T.property A⟩

private def rightNuclear (A : SoninL2 →L[ℂ] SoninL2) (T : SchattenOneOperator SoninL2) :
    SchattenOneOperator SoninL2 := ⟨T.val ∘L A, memSchattenClass_one_comp_right T.property A⟩

private theorem leftNuclear_tendsto {ι : Type*} {l : Filter ι}
    {Aι : ι → SoninL2 →L[ℂ] SoninL2} {A : SoninL2 →L[ℂ] SoninL2}
    {Tι : ι → SchattenOneOperator SoninL2} {T : SchattenOneOperator SoninL2}
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᶠ i in l, ‖Aι i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => Aι i x) l (𝓝 (A x))) (hT : Tendsto Tι l (𝓝 T)) :
    Tendsto (fun i => leftNuclear (Aι i) (Tι i)) l (𝓝 (leftNuclear A T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun i => C*‖Tι i-T‖) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_iff_norm_sub_tendsto_zero.mp hT).const_mul C
  have ha := traceNorm_comp_tendsto_of_strong_tendsto_of_uniform_bound
    T.property.one_isTraceClass C hC hbound hA
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_
    (by simpa only [add_zero] using ht.add ha)
  filter_upwards [hbound] with i hi
  have he : leftNuclear (Aι i) (Tι i)-leftNuclear A T =
      leftNuclear (Aι i) (Tι i-T)+leftNuclear (Aι i-A) T := by
    apply SchattenOneOperator.ext
    change Aι i ∘L (Tι i).val-A ∘L T.val =
      Aι i ∘L ((Tι i).val-T.val)+(Aι i-A) ∘L T.val
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  exact (traceNorm_comp_left_le (Tι i-T).summable (Aι i)).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg (Tι i-T)))

private theorem rightNuclear_tendsto {ι : Type*} {l : Filter ι}
    {Aι : ι → SoninL2 →L[ℂ] SoninL2} {A : SoninL2 →L[ℂ] SoninL2}
    (T : SchattenOneOperator SoninL2) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ i in l, ‖Aι i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => ContinuousLinearMap.adjoint (Aι i) x) l
      (𝓝 (ContinuousLinearMap.adjoint A x))) :
    Tendsto (fun i => rightNuclear (Aι i) T) l (𝓝 (rightNuclear A T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := traceNorm_comp_right_tendsto_of_adjoint_strong_tendsto_of_uniform_bound
    T.property.one_isTraceClass C hC hbound hA
  apply ht.congr
  intro i
  change traceNorm SoninL2 (T.val ∘L (Aι i-A)) =
    traceNorm SoninL2 (T.val ∘L Aι i-T.val ∘L A)
  rw [ContinuousLinearMap.comp_sub]

private theorem unitary_norm_le_one (U : SoninL2 ≃ₗᵢ[ℂ] SoninL2) :
    ‖(U : SoninL2 →L[ℂ] SoninL2)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖U x‖ ≤ 1*‖x‖
  rw [U.norm_map, one_mul]

private theorem unitary_inverse_tendsto {ι : Type*} {l : Filter ι}
    {Uι : ι → SoninL2 ≃ₗᵢ[ℂ] SoninL2} {U : SoninL2 ≃ₗᵢ[ℂ] SoninL2}
    (hU : ∀ x, Tendsto (fun i => Uι i x) l (𝓝 (U x))) (x : SoninL2) :
    Tendsto (fun i => (Uι i).symm x) l (𝓝 (U.symm x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp (hU (U.symm x))
  simp only [U.apply_symm_apply] at ht
  apply ht.congr
  intro i
  rw [← (Uι i).norm_map ((Uι i).symm x-U.symm x), map_sub,
    LinearIsometryEquiv.apply_symm_apply, norm_sub_rev]

private theorem unitary_mul_inverse (U : SoninL2 ≃ₗᵢ[ℂ] SoninL2) :
    (U : SoninL2 →L[ℂ] SoninL2)*(U.symm : SoninL2 →L[ℂ] SoninL2)=1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact U.apply_symm_apply x

private theorem unitary_inverse_mul (U : SoninL2 ≃ₗᵢ[ℂ] SoninL2) :
    (U.symm : SoninL2 →L[ℂ] SoninL2)*(U : SoninL2 →L[ℂ] SoninL2)=1 := by
  apply ContinuousLinearMap.ext
  intro x
  exact U.symm_apply_apply x

private theorem multiplier_phase_product
    (U : SoninL2 ≃ₗᵢ[ℂ] SoninL2) (φ : ℝ → ℂ)
    (hU : ∀ x : SoninL2, (U x : ℝ → ℂ) =ᵐ[volume] fun t => φ t*x t)
    (g h : 𝓢(ℝ, ℂ)) (hh : ∀ t, h t=φ t*g t) :
    ccmSchwartzMultiplier h=ccmSchwartzMultiplier g*(U : SoninL2 →L[ℂ] SoninL2) ∧
    ccmSchwartzMultiplier h=(U : SoninL2 →L[ℂ] SoninL2)*ccmSchwartzMultiplier g := by
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    apply Lp.ext
    filter_upwards [ccmSchwartzMultiplier_coeFn h x,
      ccmSchwartzMultiplier_coeFn g (U x),hU x] with t ht hg hu
    change ccmSchwartzMultiplier h x t=ccmSchwartzMultiplier g (U x) t
    rw [ht,hg,hu,hh]
    ring
  · apply ContinuousLinearMap.ext
    intro x
    apply Lp.ext
    filter_upwards [ccmSchwartzMultiplier_coeFn h x,
      hU (ccmSchwartzMultiplier g x),ccmSchwartzMultiplier_coeFn g x] with t ht hu hg
    change ccmSchwartzMultiplier h x t=U (ccmSchwartzMultiplier g x) t
    rw [ht,hu,hg,hh]
    ring

private def testedPhaseNuclear (U : SoninL2 ≃ₗᵢ[ℂ] SoninL2) (g h : 𝓢(ℝ, ℂ)) :
    SchattenOneOperator SoninL2 :=
  (1/2 : ℂ) • leftNuclear (U.symm : SoninL2 →L[ℂ] SoninL2)
    (ccmQuantizedDifferentialNuclear h-
      rightNuclear (U : SoninL2 →L[ℂ] SoninL2) (ccmQuantizedDifferentialNuclear g))

private theorem testedPhaseNuclear_coe (U : SoninL2 ≃ₗᵢ[ℂ] SoninL2) (g h : 𝓢(ℝ, ℂ))
    (hmul : ccmSchwartzMultiplier h=ccmSchwartzMultiplier g*(U : SoninL2 →L[ℂ] SoninL2))
    (hrev : ccmSchwartzMultiplier h=(U : SoninL2 →L[ℂ] SoninL2)*ccmSchwartzMultiplier g) :
    (testedPhaseNuclear U g h : SoninL2 →L[ℂ] SoninL2)=
      ccmSchwartzMultiplier g*((U.symm : SoninL2 →L[ℂ] SoninL2)*
        ccmHardyProjection*(U : SoninL2 →L[ℂ] SoninL2)-ccmHardyProjection) := by
  have hc : (U : SoninL2 →L[ℂ] SoninL2)*ccmSchwartzMultiplier g=
      ccmSchwartzMultiplier g*(U : SoninL2 →L[ℂ] SoninL2) := hrev.symm.trans hmul
  have hci : ccmSchwartzMultiplier g*(U.symm : SoninL2 →L[ℂ] SoninL2)=
      (U.symm : SoninL2 →L[ℂ] SoninL2)*ccmSchwartzMultiplier g := by
    calc
      _ = ((U.symm : SoninL2 →L[ℂ] SoninL2)*(U : SoninL2 →L[ℂ] SoninL2))*
          (ccmSchwartzMultiplier g*(U.symm : SoninL2 →L[ℂ] SoninL2)) := by
        rw [unitary_inverse_mul,one_mul]
      _ = (U.symm : SoninL2 →L[ℂ] SoninL2)*
          ((U : SoninL2 →L[ℂ] SoninL2)*ccmSchwartzMultiplier g)*
          (U.symm : SoninL2 →L[ℂ] SoninL2) := by noncomm_ring
      _ = (U.symm : SoninL2 →L[ℂ] SoninL2)*
          (ccmSchwartzMultiplier g*(U : SoninL2 →L[ℂ] SoninL2))*
          (U.symm : SoninL2 →L[ℂ] SoninL2) := by rw [hc]
      _ = ((U.symm : SoninL2 →L[ℂ] SoninL2)*ccmSchwartzMultiplier g)*
          ((U : SoninL2 →L[ℂ] SoninL2)*(U.symm : SoninL2 →L[ℂ] SoninL2)) := by noncomm_ring
      _ = _ := by rw [unitary_mul_inverse,mul_one]
  have hd : ccmQuantizedDifferential h-
      ccmQuantizedDifferential g*(U : SoninL2 →L[ℂ] SoninL2)=
      ccmSchwartzMultiplier g*(ccmHardyInvolution*(U : SoninL2 →L[ℂ] SoninL2)-
        (U : SoninL2 →L[ℂ] SoninL2)*ccmHardyInvolution) := by
    unfold ccmQuantizedDifferential
    rw [hmul]
    noncomm_ring
  have hp : (1/2 : ℂ) • ((U.symm : SoninL2 →L[ℂ] SoninL2)*
      (ccmHardyInvolution*(U : SoninL2 →L[ℂ] SoninL2)-
        (U : SoninL2 →L[ℂ] SoninL2)*ccmHardyInvolution))=
      (U.symm : SoninL2 →L[ℂ] SoninL2)*ccmHardyProjection*
        (U : SoninL2 →L[ℂ] SoninL2)-ccmHardyProjection := by
    apply ContinuousLinearMap.ext
    intro x
    change (1/2 : ℂ) • (U.symm (ccmHardyInvolution (U x)-U (ccmHardyInvolution x)))=
      U.symm (ccmHardyProjection (U x))-ccmHardyProjection x
    rw [map_sub,U.symm_apply_apply,ccmHardyInvolution_apply,ccmHardyInvolution_apply,
      map_sub,map_smul,U.symm_apply_apply]
    module
  change (1/2 : ℂ) • ((U.symm : SoninL2 →L[ℂ] SoninL2)*
    ((ccmQuantizedDifferentialNuclear h).val-
      (ccmQuantizedDifferentialNuclear g).val*(U : SoninL2 →L[ℂ] SoninL2)))=_
  rw [ccmQuantizedDifferentialNuclear_coe,ccmQuantizedDifferentialNuclear_coe,hd,
    ← mul_assoc,← hci,mul_assoc,← mul_smul_comm,hp]

/-- The literal Schwartz-tested Hardy projection difference for the original finite clock phase. -/
def gammaClockTestedProjectionCutoff (ε R : ℝ) (g : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  ccmSchwartzMultiplier g*((gammaClockScatteringCutoffUnitary ε R).symm.toLinearIsometry.toContinuousLinearMap*
    ccmHardyProjection*(gammaClockScatteringCutoffUnitary ε R).toLinearIsometry.toContinuousLinearMap-
      ccmHardyProjection)

private theorem cutoff_unitary_ae (ε R : ℝ) (x : SoninL2) :
    (gammaClockScatteringCutoffUnitary ε R x : ℝ → ℂ) =ᵐ[volume]
      fun t => gammaClockScatteringCutoffSymbol ε R t*x t := by
  unfold gammaClockScatteringCutoffUnitary
  exact GaloisForLFunctions.RHTower.UnitModulusL2Phase.mulUnitary_ae _ x

private theorem cutoff_nuclear_coe {ε : ℝ} (hε : 0 < ε) (R : ℝ) (g : 𝓢(ℝ, ℂ)) :
    (testedPhaseNuclear (gammaClockScatteringCutoffUnitary ε R) g
      (gammaClockScatteringCutoffSchwartz ε R g) : SoninL2 →L[ℂ] SoninL2)=
        gammaClockTestedProjectionCutoff ε R g := by
  obtain ⟨hmul,hrev⟩ := multiplier_phase_product (gammaClockScatteringCutoffUnitary ε R)
    (gammaClockScatteringCutoffSymbol ε R) (cutoff_unitary_ae ε R) g
    (gammaClockScatteringCutoffSchwartz ε R g) (gammaClockScatteringCutoffSchwartz_apply hε R g)
  exact testedPhaseNuclear_coe _ _ _ hmul hrev

/-- Every positive-endpoint original tested cutoff lies in the genuine nuclear ideal. -/
theorem gammaClockTestedProjectionCutoff_memSchattenClass_one {ε : ℝ} (hε : 0 < ε)
    (R : ℝ) (g : 𝓢(ℝ, ℂ)) : MemSchattenClass 1 (gammaClockTestedProjectionCutoff ε R g) := by
  rw [← cutoff_nuclear_coe hε R g]
  exact (testedPhaseNuclear _ _ _).property

private theorem full_nuclear_coe (g : 𝓢(ℝ, ℂ)) :
    (testedPhaseNuclear ccmArchimedeanScatteringL2Unitary g (ccmArchimedeanScatteringPhaseMul g) :
      SoninL2 →L[ℂ] SoninL2)=ccmSchwartzMultiplier g*
        ((ccmArchimedeanScatteringL2Unitary.symm : SoninL2 →L[ℂ] SoninL2)*
          ccmHardyProjection*(ccmArchimedeanScatteringL2Unitary : SoninL2 →L[ℂ] SoninL2)-
            ccmHardyProjection) :=
  testedPhaseNuclear_coe _ _ _
    (ccmSchwartzMultiplier_scatteringPhaseMul_eq_mul_phase g)
    (ccmSchwartzMultiplier_scatteringPhaseMul_eq_phase_mul g)

private theorem tested_nuclear_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun i => testedPhaseNuclear (gammaClockScatteringCutoffUnitary (ε i) (R i)) g
      (gammaClockScatteringCutoffSchwartz (ε i) (R i) g)) l
      (𝓝 (testedPhaseNuclear ccmArchimedeanScatteringL2Unitary g (ccmArchimedeanScatteringPhaseMul g))) := by
  have hU (x : SoninL2) := gammaClockScatteringCutoffUnitary_tendsto hε hR x
  have hInv (x : SoninL2) := unitary_inverse_tendsto hU x
  have hAdj (x : SoninL2) : Tendsto (fun i => ContinuousLinearMap.adjoint
      (gammaClockScatteringCutoffUnitary (ε i) (R i) : SoninL2 →L[ℂ] SoninL2) x) l
      (𝓝 (ContinuousLinearMap.adjoint (ccmArchimedeanScatteringL2Unitary : SoninL2 →L[ℂ] SoninL2) x)) := by
    simpa only [LinearIsometryEquiv.adjoint_eq_symm,LinearIsometryEquiv.coe_coe''] using hInv x
  have hright := rightNuclear_tendsto (ccmQuantizedDifferentialNuclear g) 1 zero_le_one
    (Eventually.of_forall fun i => unitary_norm_le_one (gammaClockScatteringCutoffUnitary (ε i) (R i))) hAdj
  have hsymbol := continuous_ccmQuantizedDifferentialNuclear.continuousAt.tendsto.comp
    (gammaClockScatteringCutoffSchwartz_tendsto hε hR g)
  have hInvCLM (x : SoninL2) : Tendsto (fun i =>
      ((gammaClockScatteringCutoffUnitary (ε i) (R i)).symm : SoninL2 →L[ℂ] SoninL2) x) l
      (𝓝 ((ccmArchimedeanScatteringL2Unitary.symm : SoninL2 →L[ℂ] SoninL2) x)) := by
    simpa only [LinearIsometryEquiv.coe_coe''] using hInv x
  have hleft := leftNuclear_tendsto
    (A := (ccmArchimedeanScatteringL2Unitary.symm : SoninL2 →L[ℂ] SoninL2)) 1 zero_le_one
    (Eventually.of_forall fun i => unitary_norm_le_one ((gammaClockScatteringCutoffUnitary (ε i) (R i)).symm))
    hInvCLM (hsymbol.sub hright)
  exact hleft.const_smul (1/2 : ℂ)

/-- The actual tested original Gamma projection cutoffs converge in genuine trace norm. -/
theorem gammaClockTestedProjectionCutoff_traceNorm_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun i => traceNorm SoninL2 (gammaClockTestedProjectionCutoff (ε i) (R i) g-
      ccmSchwartzMultiplier g*((ccmArchimedeanScatteringL2Unitary.symm : SoninL2 →L[ℂ] SoninL2)*
        ccmHardyProjection*(ccmArchimedeanScatteringL2Unitary : SoninL2 →L[ℂ] SoninL2)-
          ccmHardyProjection))) l (𝓝 0) := by
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp (tested_nuclear_tendsto hε hR g)
  apply ht.congr'
  filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
  rw [SchattenOneOperator.norm_def,SchattenOneOperator.coe_sub,
    cutoff_nuclear_coe hi (R i) g,full_nuclear_coe g]

private def nuclearCube (T : SchattenOneOperator SoninL2) : SchattenOneOperator SoninL2 :=
  leftNuclear T.val (leftNuclear T.val T)

private theorem nuclearCube_coe (T : SchattenOneOperator SoninL2) :
    (nuclearCube T : SoninL2 →L[ℂ] SoninL2)=T.val^3 := by
  change T.val*(T.val*T.val)=T.val^3
  noncomm_ring

private theorem nuclearCube_tendsto {ι : Type*} {l : Filter ι}
    {Tι : ι → SchattenOneOperator SoninL2} {T : SchattenOneOperator SoninL2}
    (hT : Tendsto Tι l (𝓝 T)) : Tendsto (fun i => nuclearCube (Tι i)) l (𝓝 (nuclearCube T)) := by
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hT
  have hstrong (x : SoninL2) : Tendsto (fun i => (Tι i).val x) l (𝓝 (T.val x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_)
      (by simpa only [zero_mul] using hnorm.mul_const ‖x‖)
    change ‖((Tι i-T).val) x‖ ≤ ‖Tι i-T‖*‖x‖
    exact ((Tι i-T).val.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (Tι i-T).norm_coe_le (norm_nonneg _))
  have hbound : ∀ᶠ i in l, ‖(Tι i).val‖ ≤ ‖T‖+1 := by
    filter_upwards [hT.norm.eventually (Iio_mem_nhds (by linarith : ‖T‖ < ‖T‖+1))] with i hi
    exact (Tι i).norm_coe_le.trans hi.le
  have hC : 0 ≤ ‖T‖+1 := by positivity
  have hsq := leftNuclear_tendsto (‖T‖+1) hC hbound hstrong hT
  exact leftNuclear_tendsto (‖T‖+1) hC hbound hstrong hsq

private theorem nuclearTrace_tendsto {ι : Type*} {l : Filter ι}
    {Tι : ι → SchattenOneOperator SoninL2} {T : SchattenOneOperator SoninL2}
    (hT : Tendsto Tι l (𝓝 T)) :
    Tendsto (fun i => opTrace (Tι i).val) l (𝓝 (opTrace T.val)) := by
  have hd : Tendsto (fun i => opTrace (Tι i).val-opTrace T.val) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) (tendsto_iff_norm_sub_tendsto_zero.mp hT)
    rw [← opTrace_sub_of_memSchattenClass_one (Tι i).property T.property]
    exact norm_opTrace_le_traceNorm (Tι i-T).property
  simpa only [sub_add_cancel,zero_add] using hd.add_const (opTrace T.val)

/-- Ordinary cubic traces of the literal tested Gamma projection cutoffs converge. -/
theorem gammaClockTestedProjectionCutoff_cubic_trace_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {ε R : ι → ℝ} (hε : Tendsto ε l (𝓝[>] 0)) (hR : Tendsto R l atTop) (g : 𝓢(ℝ, ℂ)) :
    Tendsto (fun i => opTrace ((gammaClockTestedProjectionCutoff (ε i) (R i) g)^3)) l
      (𝓝 (opTrace ((ccmSchwartzMultiplier g*
        ((ccmArchimedeanScatteringL2Unitary.symm : SoninL2 →L[ℂ] SoninL2)*
          ccmHardyProjection*(ccmArchimedeanScatteringL2Unitary : SoninL2 →L[ℂ] SoninL2)-
            ccmHardyProjection))^3))) := by
  have ht := nuclearTrace_tendsto (nuclearCube_tendsto (tested_nuclear_tendsto hε hR g))
  rw [nuclearCube_coe,full_nuclear_coe g] at ht
  apply ht.congr'
  filter_upwards [hε.eventually self_mem_nhdsWithin] with i hi
  rw [nuclearCube_coe,cutoff_nuclear_coe hi (R i) g]

end RHTower
