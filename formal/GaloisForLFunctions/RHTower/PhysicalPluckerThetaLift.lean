import GaloisForLFunctions.RHTower.PhysicalPluckerIntegralNuclearDensity
import GaloisForLFunctions.HTGeometry.PrimeHodgeSteinGramian
import GaloisForLFunctions.HTGeometry.HodgeSurvivalShiftDynamics
import GaloisForLFunctions.HTGeometry.SingularBoundaryTransferScaleGerm
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvatureReconstruction
import GaloisForLFunctions.HTGeometry.SourceGaugeObservabilitySpectrum

/-!
# The theta first-exit lift of the physical Plücker density

The forced Mellin-six survival shift `C e_n = √r_n e_{n+1}` acts on the marked rays
`ε_n = δ_n ⊗ Ψ` of `ℓ²(ℕ_θ) ⊗ ℓ²(I) ⊗ H` through the isometry `J e_n = ε_n`:

* **(POINH.10)** `C ε_n = √r_n ε_{n+1}`, and `C J = J C_θ` on the marked span;
* **(POINH.11)** `ind C_θ = -1`, `Tr(C_θ*C_θ - C_θC_θ*) = 1`, and the first-exit weights are
  `⟨C_θⁿ e_0, (I - C_θ*C_θ) C_θⁿ e_0⟩ = w_n`; the first-exit defect is `D̂ = ∑ w_n |ε_n⟩⟨ε_n|`;
* **(POINH.12)** closing the theta history of `D̂` gives `|Ψ⟩⟨Ψ|`, and closing the source record of
  `|Ψ⟩⟨Ψ|` gives `T`;
* **(POINH.13)** `-ind C_θ = Tr(C_θ*C_θ - C_θC_θ*) = ∑ w_n = Tr D̂ = Tr T = 1`.

At the singular completion (§6): `E_ε(T) → I` strongly while `‖E_ε(T) - I‖ = 1` for every `ε > 0`,
and the scaled transfers keep the exact contrast
`limsup_{ε→0+} ‖E_ε(cT) - E_ε(dT)‖ = |√c - √d|/(√c + √d)` (POINH.15).
-/

open Filter Topology
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

/-- The source record carrier `ℓ²(I) ⊗ H`. -/
abbrev PluckerSourceRecord : Type :=
  lp (fun _ : PluckerRayIndex => GammaSewnCriticalPhysicalPluckerHilbert) 2

/-- The marked theta embedding `J e_n = δ_n ⊗ Ψ`. -/
def thetaMarkedEmbedding : ArithmeticDilationHilbert →L[ℂ] HistoryL2 PluckerSourceRecord :=
  gradeEmbedding (fun _ => pluckerPurification) (fun _ => norm_pluckerPurification)

theorem thetaMarkedEmbedding_single (n : ℕ) :
    thetaMarkedEmbedding (lp.single 2 n 1) = historyRay pluckerPurification n := by
  refine lp.ext (funext fun k => ?_)
  rw [thetaMarkedEmbedding, gradeEmbedding_apply, historyRay, lp.single_apply, lp.single_apply]
  by_cases h : k = n
  · subst h
    simp
  · simp [h]

theorem norm_thetaMarkedEmbedding_apply (c : ArithmeticDilationHilbert) :
    ‖thetaMarkedEmbedding c‖ = ‖c‖ :=
  norm_gradeEmbedding_apply _ _ c

theorem adjoint_thetaMarkedEmbedding_comp :
    adjoint thetaMarkedEmbedding ∘L thetaMarkedEmbedding = ContinuousLinearMap.id ℂ _ := by
  refine ext_of_inner_single fun i j => ?_
  rw [comp_apply, adjoint_inner_right, thetaMarkedEmbedding_single, thetaMarkedEmbedding_single,
    historyRay, historyRay, lp.inner_single_left, lp.single_apply, id_apply, lp.inner_single_left,
    lp.single_apply]
  by_cases h : i = j
  · subst h
    simp [inner_self_eq_norm_sq_to_K, norm_pluckerPurification]
  · simp [h]

/-- **(POINH.10).**  The marked theta shift `C = J C_θ J*`. -/
def thetaMarkedShift : HistoryL2 PluckerSourceRecord →L[ℂ] HistoryL2 PluckerSourceRecord :=
  thetaMarkedEmbedding ∘L primeHodgeHistorySurvivalShift ∘L adjoint thetaMarkedEmbedding

theorem thetaMarkedShift_comp_embedding :
    thetaMarkedShift ∘L thetaMarkedEmbedding =
      thetaMarkedEmbedding ∘L primeHodgeHistorySurvivalShift := by
  rw [thetaMarkedShift, comp_assoc, comp_assoc, adjoint_thetaMarkedEmbedding_comp, comp_id]

/-- **(POINH.10).**  `C ε_n = √r_n ε_{n+1}`. -/
theorem thetaMarkedShift_ray (n : ℕ) :
    thetaMarkedShift (historyRay pluckerPurification n) =
      primeHodgeHistorySurvivalWeight n • historyRay pluckerPurification (n + 1) := by
  have h := congrArg (fun A => A (lp.single 2 n (1 : ℂ))) thetaMarkedShift_comp_embedding
  simp only [comp_apply, thetaMarkedEmbedding_single] at h
  rw [h]
  have hb := primeHodgeHistorySurvivalShift_basis n
  rw [HTGeometry.ellTwoCoordinateBasis_apply] at hb
  rw [hb, map_smul, HTGeometry.ellTwoCoordinateBasis_apply, thetaMarkedEmbedding_single]

/-- **(POINH.11).**  `C_θ*C_θ - C_θC_θ*` is the relative curvature operator, of trace one. -/
theorem survivalShift_selfCommutator_eq :
    adjoint primeHodgeHistorySurvivalShift ∘L primeHodgeHistorySurvivalShift -
        primeHodgeHistorySurvivalShift ∘L adjoint primeHodgeHistorySurvivalShift =
      primeHodgeHistoryRelativeCurvatureOperator := by
  rw [primeHodgeHistoryRelativeCurvatureOperator_eq_metric_sub,
    primeHodgeHistoryOutgoingMetric_eq_adjoint_fracture,
    primeHodgeHistoryExitDefect_eq_adjoint_fracture]
  abel

theorem opTrace_survivalShift_selfCommutator :
    opTrace (adjoint primeHodgeHistorySurvivalShift ∘L primeHodgeHistorySurvivalShift -
        primeHodgeHistorySurvivalShift ∘L adjoint primeHodgeHistorySurvivalShift) = 1 := by
  rw [survivalShift_selfCommutator_eq, opTrace_primeHodgeHistoryRelativeCurvatureOperator]

/-- **(POINH.11).**  The first-exit weight of the initial history is `w_n`. -/
theorem survivalShift_firstExit_weight (n : ℕ) :
    ⟪(primeHodgeHistorySurvivalShift ^ n) (historyCoord 0),
      (ContinuousLinearMap.id ℂ ArithmeticDilationHilbert - adjoint primeHodgeHistorySurvivalShift ∘L
        primeHodgeHistorySurvivalShift) ((primeHodgeHistorySurvivalShift ^ n) (historyCoord 0))⟫_ℂ =
      (PrimeHodgeHistory.w n : ℂ) := by
  rw [← primeHodgeHistoryExitDefect_eq_adjoint_fracture]
  exact inner_survivalShift_pow_exitDefect_initial n

/-- **(POINH.11).**  The first-exit defect `D̂ = ∑ w_n |ε_n⟩⟨ε_n|`. -/
def thetaFirstExitDefect : HistoryL2 PluckerSourceRecord →L[ℂ] HistoryL2 PluckerSourceRecord :=
  rayDiagonalHistory pluckerPurification PrimeHodgeHistory.w

theorem opTrace_thetaFirstExitDefect : opTrace thetaFirstExitDefect = 1 := by
  rw [thetaFirstExitDefect, opTrace_rayDiagonalHistory _ PrimeHodgeHistory.summable_w
    (fun n => (PrimeHodgeHistory.w_pos n).le), PrimeHodgeHistory.tsum_w, norm_pluckerPurification]
  norm_num

theorem thetaFirstExitDefect_memSchattenClass_one : MemSchattenClass 1 thetaFirstExitDefect :=
  rayDiagonalHistory_memSchattenClass_one _ PrimeHodgeHistory.summable_w
    (fun n => (PrimeHodgeHistory.w_pos n).le)

/-- **(POINH.12), first closure.**  Closing the theta history gives `|Ψ⟩⟨Ψ|`. -/
theorem thetaFirstExitDefect_isPartialTrace :
    IsPartialTrace thetaFirstExitDefect (rankOne ℂ pluckerPurification pluckerPurification) := by
  have h := rayDiagonalHistory_isPartialTrace pluckerPurification PrimeHodgeHistory.summable_w
    (fun n => (PrimeHodgeHistory.w_pos n).le)
  rwa [PrimeHodgeHistory.tsum_w, Complex.ofReal_one, one_smul] at h

/-- **(POINH.12).**  Closing first the theta history and then the source record recovers `T`. -/
theorem thetaFirstExit_double_closure :
    IsPartialTrace thetaFirstExitDefect (rankOne ℂ pluckerPurification pluckerPurification) ∧
      IsPartialTrace (rankOne ℂ pluckerPurification pluckerPurification)
        normalizedPhysicalPluckerOperator :=
  ⟨thetaFirstExitDefect_isPartialTrace, pluckerPurification_isPartialTrace⟩

/-- **(POINH.13).**  `-ind C_θ = Tr(C_θ*C_θ - C_θC_θ*) = ∑ w_n = Tr D̂ = Tr T = 1`. -/
theorem thetaLift_conservation :
    ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) =
        opTrace (adjoint primeHodgeHistorySurvivalShift ∘L primeHodgeHistorySurvivalShift -
          primeHodgeHistorySurvivalShift ∘L adjoint primeHodgeHistorySurvivalShift) ∧
      opTrace (adjoint primeHodgeHistorySurvivalShift ∘L primeHodgeHistorySurvivalShift -
          primeHodgeHistorySurvivalShift ∘L adjoint primeHodgeHistorySurvivalShift) =
        ((∑' n, PrimeHodgeHistory.w n : ℝ) : ℂ) ∧
      ((∑' n, PrimeHodgeHistory.w n : ℝ) : ℂ) = opTrace thetaFirstExitDefect ∧
      opTrace thetaFirstExitDefect = opTrace normalizedPhysicalPluckerOperator ∧
      opTrace normalizedPhysicalPluckerOperator = 1 := by
  rw [primeHodgeHistorySurvivalShiftIndex_eq_neg_one, opTrace_survivalShift_selfCommutator,
    PrimeHodgeHistory.tsum_w, opTrace_thetaFirstExitDefect,
    opTrace_normalizedPhysicalPluckerOperator]
  norm_num

/-! ## §6: the singular boundary transfer of `T` -/

theorem zero_mem_spectrum_normalizedPhysicalPluckerOperator :
    (0 : ℝ) ∈ spectrum ℝ normalizedPhysicalPluckerOperator := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, zero_smul, zero_sub, IsUnit.neg_iff]
  rintro ⟨u, hu⟩
  apply not_finiteDimensional_pluckerHilbert
  have hcpt := normalizedPhysicalPluckerOperator_isCompact
  have hsurj : Function.Surjective normalizedPhysicalPluckerOperator := by
    intro y
    refine ⟨((u⁻¹ : (_ →L[ℂ] _)ˣ) : _ →L[ℂ] _) y, ?_⟩
    rw [← hu]
    have h := congrArg (fun A : GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert => A y) u.mul_inv
    exact h
  have hclosed : IsClosed (Set.range normalizedPhysicalPluckerOperator) := by
    rw [hsurj.range_eq]
    exact isClosed_univ
  exact GaloisForLFunctions.finiteDimensional_of_compact_injective_isClosed_range _ hcpt
    normalizedPhysicalPluckerOperator_injective hclosed

/-- **§6.**  The boundary transfer of `T` converges strongly to the identity. -/
theorem tendsto_boundaryTransfer_normalizedPhysicalPluckerOperator
    (v : GammaSewnCriticalPhysicalPluckerHilbert) :
    Tendsto (fun ε => positiveBoundaryTransfer normalizedPhysicalPluckerOperator ε v)
      (𝓝[>] 0) (𝓝 v) := by
  haveI : Nontrivial GammaSewnCriticalPhysicalPluckerHilbert := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_finiteDimensional_pluckerHilbert inferInstance
  exact positiveBoundaryTransfer_tendsto_id
    normalizedPhysicalPluckerOperator_isPositive.isSelfAdjoint
    normalizedPhysicalPluckerOperator_injective
    (spectrum_subset_Icc_of_isPositive normalizedPhysicalPluckerOperator_isPositive) v

/-- **§6.**  Norm recovery fails maximally: `‖E_ε(T) - I‖ = 1` at every positive aperture. -/
theorem norm_boundaryTransfer_normalizedPhysicalPluckerOperator_sub_id {ε : ℝ} (hε : 0 < ε) :
    ‖positiveBoundaryTransfer normalizedPhysicalPluckerOperator ε -
      ContinuousLinearMap.id ℂ _‖ = 1 := by
  haveI : Nontrivial GammaSewnCriticalPhysicalPluckerHilbert := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_finiteDimensional_pluckerHilbert inferInstance
  exact norm_positiveBoundaryTransfer_sub_id
    normalizedPhysicalPluckerOperator_isPositive.isSelfAdjoint
    (spectrum_subset_Icc_of_isPositive normalizedPhysicalPluckerOperator_isPositive)
    zero_mem_spectrum_normalizedPhysicalPluckerOperator ε hε

/-- **(POINH.15).**  The scaled transfers of `T` keep the exact contrast at the closing aperture. -/
theorem limsup_scaledBoundaryTransfer_normalizedPhysicalPluckerOperator {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d) :
    limsup (fun ε => ‖positiveBoundaryTransfer (c • normalizedPhysicalPluckerOperator) ε -
      positiveBoundaryTransfer (d • normalizedPhysicalPluckerOperator) ε‖) (𝓝[>] 0) =
        |Real.sqrt c - Real.sqrt d| / (Real.sqrt c + Real.sqrt d) := by
  refine (limsup_norm_scaledTransfer_sub normalizedPhysicalPluckerOperator_isPositive
    normalizedPhysicalPluckerOperator_isCompact normalizedPhysicalPluckerOperator_injective
    not_finiteDimensional_pluckerHilbert hc hd).trans ?_
  rw [germContrast, abs_div, abs_of_pos (by positivity : 0 < Real.sqrt c + Real.sqrt d)]

end RHTower.HedenmalmThetaSource
