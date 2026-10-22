import GaloisForLFunctions.RHTower.CCM.CCMGammaSoninNormalForm
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseWeilBridge
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import GaloisForLFunctions.RHTower.SoninApertureFourierParityNoGo
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal

/-!
# The Sonin decomposition of the archimedean Weil distribution

On `L²(ℝ)^ev` let `P`, `P̂` be the unit physical and Fourier cutoffs, `S` the projection onto the
Sonin space `ker P ∩ ker P̂`, and

`G = 1 - P - P̂ - S`

the generic part of the pair `(P, P̂)`.  The Connes--Consani archimedean trace formula
`W(H) = Tr(ϑ(H)(P + P̂ - 1))` splits as

`-W(H) = Tr(ϑ(H) S) + Tr(ϑ(H) G)`,

with both terms trace class for every compact Schwartz logarithmic test `H`.  Hence the Sonin-trace
domination `Re Tr(ϑ(H) S) ≤ -Re W(H)` of Connes--Consani (Weil positivity and trace formula, the
archimedean place, Theorem 1, for `H = g ⋆ g★`) is equivalent to `0 ≤ Re Tr(ϑ(H) G)`.

The generic part is self-adjoint and Fourier-invariant, annihilates the Sonin space, anticommutes
with `P - P̂`, and satisfies `G² + (P - P̂)² = 1 - S`: on each two-dimensional block of the pair it
is `±cos θ` against `(P - P̂)² = sin² θ`.  Moreover `G = G² - (P P̂ + P̂ P)`, so

`-W(H) = Tr(ϑ(H) S) + Tr(ϑ(H) G²) - Tr(ϑ(H)(P P̂ + P̂ P))`

with a positive square and the explicit time-band anticommutator.
-/

noncomputable section

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped SchwartzMap

namespace RHTower

/-- The generic part `G = 1 - P - P̂ - S` of the unit physical/Fourier cutoff pair. -/
def ccmSoninGenericPart : evenSubspace →L[ℂ] evenSubspace :=
  1 - evenIndicatorCutoff 1 - evenFourierCutoff 1 - evenCentralSoninProjection 1

/-- `G = -(P + P̂ - 1) - S`, where `P + P̂ - 1` is the Gamma scattering differential. -/
theorem ccmSoninGenericPart_eq :
    ccmSoninGenericPart =
      -ccmArchimedeanGeometricScatteringLogDifferential - evenCentralSoninProjection 1 := by
  rw [ccmArchimedeanGeometricScatteringLogDifferential_eq_cutoffs, ccmSoninGenericPart]
  abel

/-! ## Trace-class splitting of the Weil distribution -/

theorem isTraceClass_mem_hsTraceIdeal {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : T.IsTraceClass) : T ∈ hsTraceIdeal evenSubspace := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT
  exact comp_mem_hsTraceIdeal hA hB

theorem ccmIntegratedScaling_mul_scatteringLogDifferential_mem (g : 𝓢(ℝ, ℂ)) :
    ccmIntegratedScaling (ccmSchwartzLogKernel g) * ccmArchimedeanGeometricScatteringLogDifferential
      ∈ hsTraceIdeal evenSubspace :=
  isTraceClass_mem_hsTraceIdeal
    (ccmIntegratedScaling_mul_geometricScatteringLogDifferential_isTraceClass g)

theorem ccmIntegratedScaling_mul_soninProjection_mem (g : 𝓢(ℝ, ℂ)) :
    ccmIntegratedScaling (ccmSchwartzLogKernel g) * evenCentralSoninProjection 1
      ∈ hsTraceIdeal evenSubspace :=
  isTraceClass_mem_hsTraceIdeal (ccmIntegratedScaling_mul_soninProjection_isTraceClass g le_rfl)

/-- `ϑ(g) G` is trace class for every Schwartz logarithmic kernel. -/
theorem ccmIntegratedScaling_mul_soninGenericPart_mem (g : 𝓢(ℝ, ℂ)) :
    ccmIntegratedScaling (ccmSchwartzLogKernel g) * ccmSoninGenericPart
      ∈ hsTraceIdeal evenSubspace := by
  have h : ccmIntegratedScaling (ccmSchwartzLogKernel g) * ccmSoninGenericPart =
      -(ccmIntegratedScaling (ccmSchwartzLogKernel g) *
          ccmArchimedeanGeometricScatteringLogDifferential) -
        ccmIntegratedScaling (ccmSchwartzLogKernel g) * evenCentralSoninProjection 1 := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ccmSoninGenericPart_eq, mul_apply_eq_comp, _root_.sub_apply, _root_.neg_apply,
      map_sub, map_neg]
  rw [h]
  exact sub_mem (neg_mem (ccmIntegratedScaling_mul_scatteringLogDifferential_mem g))
    (ccmIntegratedScaling_mul_soninProjection_mem g)

/-- **Sonin decomposition of the archimedean Weil distribution.**  For every compact Schwartz
logarithmic test, `-W(H) = Tr(ϑ(H) S) + Tr(ϑ(H) G)`. -/
theorem neg_ccmArchimedeanWeilDistribution_eq_sonin_add_generic (H : CCMCompactSchwartzLogTest) :
    -ccmArchimedeanWeilDistribution H =
      opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) *
          evenCentralSoninProjection 1) +
        opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) *
          ccmSoninGenericPart) := by
  set T := ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap)
  have hD : T * ccmArchimedeanGeometricScatteringLogDifferential =
      -(T * ccmSoninGenericPart) - T * evenCentralSoninProjection 1 := by
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [ccmSoninGenericPart_eq, mul_apply_eq_comp, _root_.sub_apply, _root_.neg_apply,
      map_sub, map_neg, neg_sub]
    abel
  rw [← opTrace_ccmIntegratedScaling_mul_geometricScatteringLogDifferential_eq_weilDistribution H]
  change -opTrace (T * ccmArchimedeanGeometricScatteringLogDifferential) = _
  rw [hD, opTrace_sub_of_mem (neg_mem (ccmIntegratedScaling_mul_soninGenericPart_mem _))
    (ccmIntegratedScaling_mul_soninProjection_mem _), opTrace_neg']
  ring

/-- **Sonin-trace domination is generic-part positivity.**  `Re Tr(ϑ(H) S) ≤ -Re W(H)` holds
exactly when `0 ≤ Re Tr(ϑ(H) G)`. -/
theorem ccmSoninTraceDomination_iff (H : CCMCompactSchwartzLogTest) :
    (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) *
        evenCentralSoninProjection 1)).re ≤ (-ccmArchimedeanWeilDistribution H).re ↔
      0 ≤ (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) *
        ccmSoninGenericPart)).re := by
  rw [neg_ccmArchimedeanWeilDistribution_eq_sonin_add_generic, Complex.add_re]
  constructor <;> intro h <;> linarith

/-! ## Algebra of the generic part -/

theorem evenIndicatorCutoff_one_mul_self :
    evenIndicatorCutoff 1 * evenIndicatorCutoff 1 = evenIndicatorCutoff 1 :=
  (evenIndicatorCutoff_idempotent 1).eq

theorem evenFourierCutoff_one_mul_self :
    evenFourierCutoff 1 * evenFourierCutoff 1 = evenFourierCutoff 1 := by
  rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  calc evenFourierTransform * evenIndicatorCutoff 1 * evenFourierTransform *
        (evenFourierTransform * evenIndicatorCutoff 1 * evenFourierTransform)
      = evenFourierTransform * evenIndicatorCutoff 1 *
          (evenFourierTransform * evenFourierTransform) * evenIndicatorCutoff 1 *
            evenFourierTransform := by noncomm_ring
    _ = evenFourierTransform * evenIndicatorCutoff 1 * evenFourierTransform := by
      rw [evenFourierTransform_mul_self, mul_one, mul_assoc (evenFourierTransform) _ _,
        evenIndicatorCutoff_one_mul_self]

theorem evenCentralSoninProjection_one_mul_self :
    evenCentralSoninProjection 1 * evenCentralSoninProjection 1 = evenCentralSoninProjection 1 := by
  rw [evenCentralSoninProjection_eq_starProjection]
  exact (evenCentralSoninCarrier 1).isIdempotentElem_starProjection.eq

/-- `G` is self-adjoint. -/
theorem adjoint_ccmSoninGenericPart :
    ContinuousLinearMap.adjoint ccmSoninGenericPart = ccmSoninGenericPart := by
  have hP : IsSelfAdjoint (evenIndicatorCutoff 1) :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenIndicatorCutoff 1)
  have hR : IsSelfAdjoint (evenFourierCutoff 1) :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenFourierCutoff 1)
  have hS : IsSelfAdjoint (evenCentralSoninProjection 1) :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mpr (adjoint_evenCentralSoninProjection 1)
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mp
    ((((IsSelfAdjoint.one _).sub hP).sub hR).sub hS)

/-- `G` annihilates the Sonin space. -/
theorem ccmSoninGenericPart_mul_soninProjection :
    ccmSoninGenericPart * evenCentralSoninProjection 1 = 0 := by
  simp only [ccmSoninGenericPart, sub_mul, one_mul,
    evenIndicatorCutoff_mul_evenCentralSoninProjection,
    evenFourierCutoff_mul_evenCentralSoninProjection, evenCentralSoninProjection_one_mul_self]
  abel

theorem soninProjection_mul_ccmSoninGenericPart :
    evenCentralSoninProjection 1 * ccmSoninGenericPart = 0 := by
  simp only [ccmSoninGenericPart, mul_sub, mul_one,
    evenCentralSoninProjection_mul_evenIndicatorCutoff,
    evenCentralSoninProjection_mul_evenFourierCutoff, evenCentralSoninProjection_one_mul_self]
  abel

/-- **Two-projection law.**  `G² + (P - P̂)² = 1 - S`. -/
theorem ccmSoninGenericPart_sq_add_sq :
    ccmSoninGenericPart * ccmSoninGenericPart +
        (evenIndicatorCutoff 1 - evenFourierCutoff 1) *
          (evenIndicatorCutoff 1 - evenFourierCutoff 1) =
      1 - evenCentralSoninProjection 1 := by
  simp only [ccmSoninGenericPart, sub_mul, mul_sub, one_mul, mul_one,
    evenIndicatorCutoff_one_mul_self, evenFourierCutoff_one_mul_self,
    evenCentralSoninProjection_one_mul_self, evenIndicatorCutoff_mul_evenCentralSoninProjection,
    evenFourierCutoff_mul_evenCentralSoninProjection,
    evenCentralSoninProjection_mul_evenIndicatorCutoff,
    evenCentralSoninProjection_mul_evenFourierCutoff]
  abel

/-- **Anticommutation.**  `G` anticommutes with `P - P̂`. -/
theorem ccmSoninGenericPart_anticommute :
    ccmSoninGenericPart * (evenIndicatorCutoff 1 - evenFourierCutoff 1) +
        (evenIndicatorCutoff 1 - evenFourierCutoff 1) * ccmSoninGenericPart = 0 := by
  simp only [ccmSoninGenericPart, sub_mul, mul_sub, one_mul, mul_one,
    evenIndicatorCutoff_one_mul_self, evenFourierCutoff_one_mul_self,
    evenCentralSoninProjection_mul_evenIndicatorCutoff,
    evenCentralSoninProjection_mul_evenFourierCutoff,
    evenIndicatorCutoff_mul_evenCentralSoninProjection,
    evenFourierCutoff_mul_evenCentralSoninProjection]
  abel

/-- **Anticommutator law.**  `G² - G = P P̂ + P̂ P`. -/
theorem ccmSoninGenericPart_sq_sub_self :
    ccmSoninGenericPart * ccmSoninGenericPart - ccmSoninGenericPart =
      evenIndicatorCutoff 1 * evenFourierCutoff 1 +
        evenFourierCutoff 1 * evenIndicatorCutoff 1 := by
  simp only [ccmSoninGenericPart, sub_mul, mul_sub, one_mul, mul_one,
    evenIndicatorCutoff_one_mul_self, evenFourierCutoff_one_mul_self,
    evenCentralSoninProjection_one_mul_self, evenIndicatorCutoff_mul_evenCentralSoninProjection,
    evenFourierCutoff_mul_evenCentralSoninProjection,
    evenCentralSoninProjection_mul_evenIndicatorCutoff,
    evenCentralSoninProjection_mul_evenFourierCutoff]
  abel

/-- **Square--anticommutator form of the Weil distribution.**
`-W(H) = Tr(ϑ(H) S) + Tr(ϑ(H) G²) - Tr(ϑ(H)(P P̂ + P̂ P))`, all three terms trace class. -/
theorem neg_ccmArchimedeanWeilDistribution_eq_sonin_add_square_sub_anticommutator
    (H : CCMCompactSchwartzLogTest) :
    -ccmArchimedeanWeilDistribution H =
      opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) *
          evenCentralSoninProjection 1) +
        opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) *
          (ccmSoninGenericPart * ccmSoninGenericPart)) -
        opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap) *
          (evenIndicatorCutoff 1 * evenFourierCutoff 1 +
            evenFourierCutoff 1 * evenIndicatorCutoff 1)) := by
  set T := ccmIntegratedScaling (ccmSchwartzLogKernel H.toSchwartzMap)
  have hG := ccmIntegratedScaling_mul_soninGenericPart_mem H.toSchwartzMap
  have hG2 : T * (ccmSoninGenericPart * ccmSoninGenericPart) ∈ hsTraceIdeal evenSubspace := by
    rw [← mul_assoc]
    exact hsTraceIdeal_comp_right hG _
  have hA : T * (evenIndicatorCutoff 1 * evenFourierCutoff 1 +
      evenFourierCutoff 1 * evenIndicatorCutoff 1) =
        T * (ccmSoninGenericPart * ccmSoninGenericPart) - T * ccmSoninGenericPart := by
    rw [← ccmSoninGenericPart_sq_sub_self, mul_sub]
  rw [neg_ccmArchimedeanWeilDistribution_eq_sonin_add_generic, hA, opTrace_sub_of_mem hG2 hG]
  ring

/-- **Fourier invariance.**  The cosine transform conjugates `G` to itself. -/
theorem evenFourierTransform_conj_ccmSoninGenericPart :
    evenFourierTransform * ccmSoninGenericPart * evenFourierTransform = ccmSoninGenericPart := by
  have hP : evenFourierTransform * evenIndicatorCutoff 1 * evenFourierTransform =
      evenFourierCutoff 1 := by
    rw [evenFourierCutoff_eq_reflectedCutoff, reflectedCutoff]
  have hR : evenFourierTransform * evenFourierCutoff 1 * evenFourierTransform =
      evenIndicatorCutoff 1 := by
    rw [← hP]
    calc evenFourierTransform *
          (evenFourierTransform * evenIndicatorCutoff 1 * evenFourierTransform) *
          evenFourierTransform
        = (evenFourierTransform * evenFourierTransform) * evenIndicatorCutoff 1 *
            (evenFourierTransform * evenFourierTransform) := by noncomm_ring
      _ = evenIndicatorCutoff 1 := by rw [evenFourierTransform_mul_self, one_mul, mul_one]
  have hS : evenFourierTransform * evenCentralSoninProjection 1 * evenFourierTransform =
      evenCentralSoninProjection 1 := by
    rw [evenFourierTransform_mul_evenCentralSoninProjection, mul_assoc,
      evenFourierTransform_mul_self, mul_one]
  have hexp : evenFourierTransform * ccmSoninGenericPart * evenFourierTransform =
      evenFourierTransform * evenFourierTransform -
        evenFourierTransform * evenIndicatorCutoff 1 * evenFourierTransform -
          evenFourierTransform * evenFourierCutoff 1 * evenFourierTransform -
            evenFourierTransform * evenCentralSoninProjection 1 * evenFourierTransform := by
    simp only [ccmSoninGenericPart, mul_sub, sub_mul, mul_one]
  rw [hexp, hP, hR, hS, evenFourierTransform_mul_self, ccmSoninGenericPart]
  abel

end RHTower
