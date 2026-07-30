import GaloisForLFunctions.RHTower.SemilocalProjectionMixedCurvature
import GaloisForLFunctions.RHTower.SoninEulerQuadraticCorner
import GaloisForLFunctions.RHTower.SoninTimeBandIdeal

/-!
# Constraint--orientation splitting for semilocal projection geometry

For self-adjoint tangents to the idempotent locus, the mixed Hessian records the symmetric
normal Gram, while the compressed commutator records the antisymmetric normal Gram.  Their sum
recovers an oriented normal product exactly.  Thus the Hessian and connection-curvature sectors
are genuinely distinct formal inputs.

The Sonin specialization also rules out a tempting but impossible bridge.  An actual prime
dilation normal is noncompact, so it cannot be the first derivative of a projection family that
is compact relative to its base.  Moreover, if two coordinate normals are the same actual Sonin
prime direction, their mixed derivative cannot be compact.  A viable semilocal construction must
therefore vary in the Calkin algebra at first order and obtain compactness only after an
arithmetic antisymmetric combination.
-/

open Filter Topology

namespace RHTower

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance evenOperatorRealNormedSpace :
    NormedSpace ℝ (evenSubspace →L[ℂ] evenSubspace) :=
  NormedSpace.restrictScalars ℝ ℂ (evenSubspace →L[ℂ] evenSubspace)

local instance evenOperatorRealContinuousSMul :
    ContinuousSMul ℝ (evenSubspace →L[ℂ] evenSubspace) :=
  IsScalarTower.continuousSMul ℂ

omit [CompleteSpace H] in
/-- The projection normal corner is the cutoff cross-boundary operator already used by the
semilocal Sonin theory. -/
theorem projectionNormalCorner_eq_crossBoundary
    (P D : H →L[ℂ] H) :
    projectionNormalCorner P D = crossBoundary P D := rfl

/-- The derivative of a norm-differentiable family whose differences from its base are compact
is compact. -/
theorem isCompactOperator_deriv_of_compact_relative_family
    (F : ℝ → (H →L[ℂ] H)) (D : H →L[ℂ] H)
    (hF : HasDerivAt F D 0)
    (hrelative : ∀ t, IsCompactOperator (F t - F 0)) :
    IsCompactOperator D := by
  let K : ℝ → (H →L[ℂ] H) := fun t => F t - F 0
  have hK : HasDerivAt K D 0 := by
    simpa [K] using hF.sub_const (F 0)
  exact isCompactOperator_deriv_of_compact_operator_family
    K D (by simpa [K] using hrelative) hK

/-- A normal corner of such a compact-relative derivative is compact. -/
theorem projectionNormalCorner_isCompact_of_compact_relative_family
    (P : H →L[ℂ] H) (F : ℝ → (H →L[ℂ] H)) (D : H →L[ℂ] H)
    (hF : HasDerivAt F D 0)
    (hrelative : ∀ t, IsCompactOperator (F t - F 0)) :
    IsCompactOperator (projectionNormalCorner P D) := by
  have hD := isCompactOperator_deriv_of_compact_relative_family F D hF hrelative
  unfold projectionNormalCorner
  change IsCompactOperator (fun x => (1 - P) (D (P x)))
  exact (hD.comp_clm P).clm_comp (1 - P)

/-- The actual central Sonin prime-dilation corner is a projection normal corner. -/
theorem evenCentralSoninDilationCorner_eq_projectionNormalCorner
    (a p : ℝ) (hp : 1 < p) :
    evenCentralSoninDilationCorner a p hp =
      projectionNormalCorner (evenCentralSoninProjection a) (evenDilationSum p hp) := by
  rw [projectionNormalCorner_eq_crossBoundary]
  exact evenCentralSoninDilationCorner_eq_crossBoundary a p hp

/-- Essential transversality: a differentiable family having an actual Sonin prime normal cannot
remain compact relative to its base at every parameter value. -/
theorem exists_noncompact_relative_value_of_evenCentralSonin_normalDerivative
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (F : ℝ → (evenSubspace →L[ℂ] evenSubspace))
    (D : evenSubspace →L[ℂ] evenSubspace)
    (hF : HasDerivAt F D 0)
    (hnormal : projectionNormalCorner (evenCentralSoninProjection a) D =
      evenCentralSoninDilationCorner a p hp) :
    ∃ t, ¬ IsCompactOperator (F t - F 0) := by
  by_contra hno
  have hrelative : ∀ t, IsCompactOperator (F t - F 0) := by
    intro t
    by_contra ht
    exact hno ⟨t, ht⟩
  have hcompact := projectionNormalCorner_isCompact_of_compact_relative_family
    (evenCentralSoninProjection a) F D hF hrelative
  rw [hnormal] at hcompact
  exact evenCentralSoninDilationCorner_not_isCompactOperator a p ha hp hcompact

/-- The same-prime normal Gram is exactly the actual Sonin quadratic corner. -/
theorem actualSoninPrimeNormalGram_eq_quadraticCorner
    (a p : ℝ) (hp : 1 < p) :
    adjoint
        (projectionNormalCorner (evenCentralSoninProjection a) (evenDilationSum p hp)) *
      projectionNormalCorner (evenCentralSoninProjection a) (evenDilationSum p hp) =
        evenCentralSoninQuadraticCorner a p p hp hp := by
  rw [← evenCentralSoninDilationCorner_eq_projectionNormalCorner]
  rfl

/-- The orientation sector of two tangent directions is their compressed commutator. -/
def projectionConnectionCurvature
    (P Ds Dt : H →L[ℂ] H) : H →L[ℂ] H :=
  P * (Dt * Ds - Ds * Dt) * P

/-- For self-adjoint projection tangents, connection curvature is exactly the skew normal Gram. -/
theorem projectionConnectionCurvature_eq_normalSkewGram
    (P Ds Dt : H →L[ℂ] H)
    (hP2 : P * P = P)
    (hPadj : adjoint P = P)
    (hDsadj : adjoint Ds = Ds)
    (hDtadj : adjoint Dt = Dt)
    (hDstan : Ds * P + P * Ds = Ds)
    (hDttan : Dt * P + P * Dt = Dt) :
    projectionConnectionCurvature P Ds Dt =
      adjoint (projectionNormalCorner P Dt) * projectionNormalCorner P Ds -
        adjoint (projectionNormalCorner P Ds) * projectionNormalCorner P Dt := by
  rw [projectionConnectionCurvature]
  have ht := projectionTangent_cross_eq_normalGram
    P Ds Dt hP2 hPadj hDtadj hDttan
  have hs := projectionTangent_cross_eq_normalGram
    P Dt Ds hP2 hPadj hDsadj hDstan
  have hsplit :
      P * (Dt * Ds - Ds * Dt) * P =
        P * Dt * Ds * P - P * Ds * Dt * P := by
    noncomm_ring
  rw [hsplit, ht, hs]

/-- If two normal directions are the actual `p`- and `q`-Sonin corners, their connection
curvature is the antisymmetric difference of the corresponding quadratic corners. -/
theorem projectionConnectionCurvature_eq_actualSoninPrimeSkewGram
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q)
    (P Ds Dt : evenSubspace →L[ℂ] evenSubspace)
    (hP2 : P * P = P)
    (hPadj : adjoint P = P)
    (hDsadj : adjoint Ds = Ds)
    (hDtadj : adjoint Dt = Dt)
    (hDstan : Ds * P + P * Ds = Ds)
    (hDttan : Dt * P + P * Dt = Dt)
    (hnormalS : projectionNormalCorner P Ds =
      evenCentralSoninDilationCorner a q hq)
    (hnormalT : projectionNormalCorner P Dt =
      evenCentralSoninDilationCorner a p hp) :
    projectionConnectionCurvature P Ds Dt =
      evenCentralSoninQuadraticCorner a p q hp hq -
        evenCentralSoninQuadraticCorner a q p hq hp := by
  rw [projectionConnectionCurvature_eq_normalSkewGram P Ds Dt hP2 hPadj hDsadj
    hDtadj hDstan hDttan, hnormalS, hnormalT]
  rfl

/-- The oriented normal product splits into half the negative mixed Hessian plus half the
connection curvature. -/
theorem selfAdjointIdempotentFamily_normalGram_constraint_orientation_split
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (Ds Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t => F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s => F s 0) Ds 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDsadj : adjoint Ds = Ds)
    (hDtadj : adjoint (Dt 0) = Dt 0) :
    adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
        projectionNormalCorner (F 0 0) Ds =
      ((2 : ℂ)⁻¹) •
        (-(F 0 0 * Dst * F 0 0) +
          projectionConnectionCurvature (F 0 0) Ds (Dt 0)) := by
  let P : H →L[ℂ] H := F 0 0
  have hP2 : P * P = P := (hidem 0).eq_of_nhds
  have hDttan : Dt 0 * P + P * Dt 0 = Dt 0 :=
    idempotentFamily_tangent_identity (F 0) (Dt 0) (ht 0) (hidem 0)
  have houterIdem :
      (fun s => F s 0 * F s 0) =ᶠ[nhds 0] (fun s => F s 0) :=
    Filter.Eventually.of_forall fun s => (hidem s).eq_of_nhds
  have hDstan : Ds * P + P * Ds = Ds :=
    idempotentFamily_tangent_identity (fun s => F s 0) Ds hs houterIdem
  have hconstraint := selfAdjointIdempotentFamily_mixed_normalGram_identity
    F Dt Ds Dst ht hidem hs hst hPadj hDsadj hDtadj
  have horientation := projectionConnectionCurvature_eq_normalSkewGram
    P Ds (Dt 0) hP2 hPadj hDsadj hDtadj hDstan hDttan
  change adjoint (projectionNormalCorner P (Dt 0)) * projectionNormalCorner P Ds = _
  change P * Dst * P = _ at hconstraint
  rw [hconstraint, horientation]
  module

/-- If both coordinate normals are the same actual Sonin prime direction, the mixed derivative
cannot be compact.  This is a concrete obstruction to compact-relative projection charts. -/
theorem mixedDerivative_not_isCompact_of_actualSoninPrimeNormals
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (F : ℝ → ℝ → (evenSubspace →L[ℂ] evenSubspace))
    (Dt : ℝ → (evenSubspace →L[ℂ] evenSubspace))
    (Ds Dst : evenSubspace →L[ℂ] evenSubspace)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t => F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s => F s 0) Ds 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDsadj : adjoint Ds = Ds)
    (hDtadj : adjoint (Dt 0) = Dt 0)
    (hnormalS : projectionNormalCorner (F 0 0) Ds =
      evenCentralSoninDilationCorner a p hp)
    (hnormalT : projectionNormalCorner (F 0 0) (Dt 0) =
      evenCentralSoninDilationCorner a p hp) :
    ¬ IsCompactOperator Dst := by
  intro hDst
  have hsum := selfAdjointIdempotentFamily_normalGram_isCompact
    F Dt Ds Dst ht hidem hs hst hPadj hDsadj hDtadj hDst
  rw [hnormalS, hnormalT] at hsum
  have hscaled := hsum.smul ((2 : ℂ)⁻¹)
  have heq :
      ((2 : ℂ)⁻¹) •
          (adjoint (evenCentralSoninDilationCorner a p hp) *
              evenCentralSoninDilationCorner a p hp +
            adjoint (evenCentralSoninDilationCorner a p hp) *
              evenCentralSoninDilationCorner a p hp) =
        evenCentralSoninQuadraticCorner a p p hp hp := by
    change ((2 : ℂ)⁻¹) •
        (evenCentralSoninQuadraticCorner a p p hp hp +
          evenCentralSoninQuadraticCorner a p p hp hp) = _
    module
  have hcompactQ : IsCompactOperator
      (evenCentralSoninQuadraticCorner a p p hp hp : evenSubspace → evenSubspace) := by
    rw [← heq]
    change IsCompactOperator (fun x =>
      ((2 : ℂ)⁻¹) •
        ((adjoint (evenCentralSoninDilationCorner a p hp) *
            evenCentralSoninDilationCorner a p hp +
          adjoint (evenCentralSoninDilationCorner a p hp) *
            evenCentralSoninDilationCorner a p hp) x))
    exact hscaled
  exact evenCentralSoninQuadraticCorner_not_isCompactOperator
    a p p ha hp hp hcompactQ

/-- The actual cross-prime skew Gram and its formal-complement principal skew Gram represent the
same Calkin class.  The stronger conclusion retains the concrete time-band ideal certificate for
their difference. -/
theorem centralSoninSkewGram_sub_principal_mem_timeBandIdeal
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    IsSoninTimeBandIdeal
      ((adjoint (crossBoundary (centralSoninProjection a) (dilationSum p hp)) *
          crossBoundary (centralSoninProjection a) (dilationSum q hq) -
        adjoint (crossBoundary (centralSoninProjection a) (dilationSum q hq)) *
          crossBoundary (centralSoninProjection a) (dilationSum p hp)) -
       (adjoint (centralSoninPrincipalDilationCorner a p hp) *
          centralSoninPrincipalDilationCorner a q hq -
        adjoint (centralSoninPrincipalDilationCorner a q hq) *
          centralSoninPrincipalDilationCorner a p hp)) := by
  let Bp := crossBoundary (centralSoninProjection a) (dilationSum p hp)
  let Bq := crossBoundary (centralSoninProjection a) (dilationSum q hq)
  let Pp := centralSoninPrincipalDilationCorner a p hp
  let Pq := centralSoninPrincipalDilationCorner a q hq
  let Rp := centralSoninDilationCornerResidual a p hp
  let Rq := centralSoninDilationCornerResidual a q hq
  have hRp : IsSoninTimeBandIdeal Rp := by
    simpa [Rp] using centralSoninDilationCornerResidual_mem_timeBandIdeal a p ha hp
  have hRq : IsSoninTimeBandIdeal Rq := by
    simpa [Rq] using centralSoninDilationCornerResidual_mem_timeBandIdeal a q ha hq
  have hBp : Bp = Rp + Pp := by
    simp only [Bp, Rp, Pp, centralSoninDilationCornerResidual]
    abel
  have hBq : Bq = Rq + Pq := by
    simp only [Bq, Rq, Pq, centralSoninDilationCornerResidual]
    abel
  have heq :
      (adjoint Bp * Bq - adjoint Bq * Bp) -
          (adjoint Pp * Pq - adjoint Pq * Pp) =
        (adjoint Rp * Rq + adjoint Rp * Pq + adjoint Pp * Rq) -
          (adjoint Rq * Rp + adjoint Rq * Pp + adjoint Pq * Rp) := by
    rw [hBp, hBq, adjoint_add_soninL2, adjoint_add_soninL2]
    noncomm_ring
  change IsSoninTimeBandIdeal
    ((adjoint Bp * Bq - adjoint Bq * Bp) -
      (adjoint Pp * Pq - adjoint Pq * Pp))
  rw [heq]
  exact (((hRp.adjoint.rightMul Rq).add (hRp.adjoint.rightMul Pq)).add
      (hRq.leftMul (adjoint Pp))).sub
    (((hRq.adjoint.rightMul Rp).add (hRq.adjoint.rightMul Pp)).add
      (hRp.leftMul (adjoint Pq)))

/-- Compact-operator form of the cross-prime skew-Gram principalization theorem. -/
theorem centralSoninSkewGram_sub_principal_isCompactOperator
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    IsCompactOperator
      ((adjoint (crossBoundary (centralSoninProjection a) (dilationSum p hp)) *
          crossBoundary (centralSoninProjection a) (dilationSum q hq) -
        adjoint (crossBoundary (centralSoninProjection a) (dilationSum q hq)) *
          crossBoundary (centralSoninProjection a) (dilationSum p hp)) -
       (adjoint (centralSoninPrincipalDilationCorner a p hp) *
          centralSoninPrincipalDilationCorner a q hq -
        adjoint (centralSoninPrincipalDilationCorner a q hq) *
          centralSoninPrincipalDilationCorner a p hp)) :=
  (centralSoninSkewGram_sub_principal_mem_timeBandIdeal a p q ha hp hq).isCompactOperator

end

end RHTower
