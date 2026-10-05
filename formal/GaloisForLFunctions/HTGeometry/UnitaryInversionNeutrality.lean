import GaloisForLFunctions.HTGeometry.UnitarySpectrumClosedRange
import GaloisForLFunctions.HTGeometry.CommutingProjectionIntersectionEnergy

/-!
# Inversion neutrality of the mixed spectral formation

Replacing a unitary `U` by its inverse `U* = U⁻¹` conjugates every eigenvalue,
`H_λ(U*) = H_{λ̄}(U)`, and leaves every spectral subspace and projection unchanged.  Consequently
the atomic and continuous subspaces, the Hilbert–Schmidt fixed space and the atomic pinching, the
atomic and continuous trace masses, the trace-norm convergence criterion, finiteness of the
spectrum and closedness of the transgression range are all the same for `U` and `U*`.

The pinching is identified through its characterization as the Hilbert–Schmidt orthogonal
projection onto the fixed space, which is common to `U` and `U*`.
-/

open Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H ≃ₗᵢ[ℂ] H}

omit [CompleteSpace H] in
/-- `H_λ(U*) = H_{λ̄}(U)`. -/
theorem unitaryEigenspace_symm (c : ℂ) :
    unitaryEigenspace U.symm c = unitaryEigenspace U ((starRingEnd ℂ) c) := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    have hc : ‖c‖ = 1 := norm_eq_one_of_mem_unitaryEigenspace hx hx0
    have h := unitary_symm_apply_of_mem hx hc
    rw [LinearIsometryEquiv.symm_symm] at h
    exact mem_unitaryEigenspace.mpr h
  · intro hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact Submodule.zero_mem _
    have hc : ‖(starRingEnd ℂ) c‖ = 1 := norm_eq_one_of_mem_unitaryEigenspace hx hx0
    have h := unitary_symm_apply_of_mem hx hc
    rw [Complex.conj_conj] at h
    exact mem_unitaryEigenspace.mpr h

omit [CompleteSpace H] in
/-- The eigenvalues of `U*` are the conjugates of those of `U`. -/
theorem mem_unitaryPointSpectrum_symm {c : ℂ} :
    c ∈ unitaryPointSpectrum U.symm ↔ (starRingEnd ℂ) c ∈ unitaryPointSpectrum U := by
  show unitaryEigenspace U.symm c ≠ ⊥ ↔ unitaryEigenspace U ((starRingEnd ℂ) c) ≠ ⊥
  rw [unitaryEigenspace_symm]

omit [CompleteSpace H] in
theorem iSup_unitaryEigenspace_symm :
    ⨆ c, unitaryEigenspace U.symm c = ⨆ c, unitaryEigenspace U c := by
  simp_rw [unitaryEigenspace_symm]
  exact Function.Surjective.iSup_comp (fun z => ⟨(starRingEnd ℂ) z, Complex.conj_conj z⟩)
    (unitaryEigenspace U)

omit [CompleteSpace H] in
/-- **`H_at(U*) = H_at(U)`.** -/
theorem atomicSubspace_symm : atomicSubspace U.symm = atomicSubspace U := by
  rw [atomicSubspace, atomicSubspace, iSup_unitaryEigenspace_symm]

omit [CompleteSpace H] in
/-- **`H_c(U*) = H_c(U)`.** -/
theorem continuousSubspace_symm : continuousSubspace U.symm = continuousSubspace U := by
  rw [continuousSubspace, continuousSubspace, atomicSubspace_symm]

/-- `P_λ(U*) = P_{λ̄}(U)`. -/
theorem eigenproj_symm (c : ℂ) : eigenproj U.symm c = eigenproj U ((starRingEnd ℂ) c) :=
  ContinuousLinearMap.ext (starProjection_congr (unitaryEigenspace_symm c))

/-- **`P_at(U*) = P_at(U)`.** -/
theorem atomproj_symm : atomproj U.symm = atomproj U :=
  ContinuousLinearMap.ext (starProjection_congr atomicSubspace_symm)

/-- **`P_c(U*) = P_c(U)`.** -/
theorem contproj_symm : contproj U.symm = contproj U :=
  ContinuousLinearMap.ext (starProjection_congr continuousSubspace_symm)

omit [CompleteSpace H] in
theorem hsConj_hsConj_symm (U : H ≃ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    hsConj U (hsConj U.symm T) = T := by
  ext x
  simp

omit [CompleteSpace H] in
/-- The Hilbert–Schmidt fixed space is common to `U` and `U*`. -/
theorem hsConj_symm_eq_iff {T : H →L[ℂ] H} : hsConj U.symm T = T ↔ hsConj U T = T := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact hsConj_hsConj_symm U T
  · intro h
    conv_lhs => rw [← h]
    have := hsConj_hsConj_symm U.symm T
    rwa [LinearIsometryEquiv.symm_symm] at this

/-- **The atomic pinching is unchanged by `U ↦ U*`.**  Both pinchings are the Hilbert–Schmidt
orthogonal projection onto the common fixed space. -/
theorem atomicPinch_symm {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    atomicPinch U.symm hT = atomicPinch U hT := by
  have hP' := isHilbertSchmidt_atomicPinch (U := U.symm) hT
  have hproj : (fixedColumns U).starProjection (hsColumns (adaptedBasis U) hT) =
      hsColumns (adaptedBasis U) hP' := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · rw [LinearMap.mem_eqLocus]
      show columnConj (adaptedBasis U) U _ = hsColumns (adaptedBasis U) hP'
      rw [columnConj_hsColumns]
      exact lp.ext (funext fun j => by
        simp only [hsColumns_apply, hsConj_symm_eq_iff.mp (hsConj_atomicPinch hT)])
    · have hfix : hsConj U (columnOperator (adaptedBasis U) w) =
          columnOperator (adaptedBasis U) w :=
        hsConj_columnOperator_of_columnConj hw
      have hF := isHilbertSchmidt_columnOperator (adaptedBasis U) w
      have h := inner_hsColumns_fixed (U := U.symm) (adaptedBasis U) hF
        (hsConj_symm_eq_iff.mpr hfix) hT
      rw [hsColumns_columnOperator] at h
      rw [inner_sub_left, ← inner_conj_symm, h, inner_conj_symm, sub_self]
  rw [atomicPinch_eq_starProjection hT] at hproj
  rw [← columnOperator_hsColumns (adaptedBasis U) hP', ← hproj, columnOperator_hsColumns]

/-- **The atomic mass is unchanged by `U ↦ U*`.** -/
theorem atomicMass_symm (T : H →L[ℂ] H) : atomicMass U.symm T = atomicMass U T := by
  rw [atomicMass, atomicMass, atomproj_symm]

/-- **The continuous mass is unchanged by `U ↦ U*`.** -/
theorem continuousMass_symm (T : H →L[ℂ] H) : continuousMass U.symm T = continuousMass U T := by
  rw [continuousMass, continuousMass, contproj_symm]

/-- **The trace-norm convergence criterion is unchanged by `U ↦ U*`.** -/
theorem tendsto_traceNorm_symm_iff {T : H →L[ℂ] H} (hT : RHTower.MemSchattenClass 1 T)
    (hpos : T.IsPositive) :
    Tendsto (fun N => RHTower.traceNorm H
        (hsCesaro U.symm N T - atomicPinch U.symm hT.one_isHilbertSchmidt)) atTop (𝓝 0) ↔
      Tendsto (fun N => RHTower.traceNorm H
        (hsCesaro U N T - atomicPinch U hT.one_isHilbertSchmidt)) atTop (𝓝 0) := by
  rw [tendsto_traceNorm_iff_continuousMass_eq_zero hT hpos,
    tendsto_traceNorm_iff_continuousMass_eq_zero hT hpos, continuousMass_symm]

omit [CompleteSpace H] in
theorem unitaryPointSpectrum_finite_symm_iff :
    (unitaryPointSpectrum U.symm).Finite ↔ (unitaryPointSpectrum U).Finite := by
  have hinj : Function.Injective (starRingEnd ℂ) := (starRingEnd ℂ).injective
  have key : ∀ V : H ≃ₗᵢ[ℂ] H,
      unitaryPointSpectrum V.symm = (starRingEnd ℂ) ⁻¹' unitaryPointSpectrum V :=
    fun V => Set.ext fun c => mem_unitaryPointSpectrum_symm
  constructor
  · intro h
    have := h.preimage hinj.injOn
    rwa [← key, LinearIsometryEquiv.symm_symm] at this
  · intro h
    rw [key]
    exact h.preimage hinj.injOn

/-- **Finiteness of the spectrum is unchanged by `U ↦ U*`.** -/
theorem spectrum_finite_symm_iff :
    (spectrum ℂ (unitaryCLM U.symm)).Finite ↔ (spectrum ℂ (unitaryCLM U)).Finite := by
  rw [spectrum_finite_iff, spectrum_finite_iff, unitaryPointSpectrum_finite_symm_iff,
    continuousSubspace_symm]

/-- **Closedness of the transgression range is unchanged by `U ↦ U*`.** -/
theorem isClosed_range_columnTransgression_symm_iff {ι : Type*} (b : HilbertBasis ι ℂ H) :
    IsClosed (Set.range
        (columnConj b U.symm - 1 : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2)) ↔
      IsClosed (Set.range
        (columnConj b U - 1 : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2)) := by
  rw [isClosed_range_columnTransgression_iff_finite_spectrum,
    isClosed_range_columnTransgression_iff_finite_spectrum, spectrum_finite_symm_iff]

end GaloisForLFunctions.HTGeometry
