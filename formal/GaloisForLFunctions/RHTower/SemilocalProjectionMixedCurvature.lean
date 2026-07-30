import GaloisForLFunctions.RHTower.CriticalDiscEulerConnectionRigidity
import GaloisForLFunctions.RHTower.SoninCalkinNormBound

/-!
# Mixed curvature of a semilocal projection family

For a two-parameter family of idempotents, differentiating `P² = P` twice and compressing by
the base idempotent identifies the mixed tangential curvature with the negative polarized Gram
of the two normal derivatives.  In particular, a compact mixed derivative forces the finite
two-direction normal Gram to be compact.

The last theorem wires this directly to compact relative families: if every difference from the
base idempotent is compact, norm differentiation supplies the compact mixed derivative
automatically.  This is the finite connection-to-curvature interface needed by semilocal Euler
source constructions.  No Xi zero, RH-equivalent positivity, or limiting divisor measure is used.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## Algebraic differentiation of the idempotent equation -/

/-- A norm derivative tangent to a family of idempotents satisfies the linearized idempotent
equation. -/
theorem idempotentFamily_tangent_identity
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (F : ℝ → A) (D : A)
    (hF : HasDerivAt F D 0)
    (hidem : (fun t => F t * F t) =ᶠ[nhds 0] F) :
    D * F 0 + F 0 * D = D := by
  have hmul := hF.mul hF
  exact ((hidem.hasDerivAt_iff).mp hmul).unique hF

/-- Twice differentiating an idempotent family and compressing by its base point gives the
negative symmetrized product of the two first derivatives. -/
theorem idempotentFamily_mixed_compressed_identity
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (F : ℝ → ℝ → A) (Dt : ℝ → A) (Ds Dst : A)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t => F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s => F s 0) Ds 0)
    (hst : HasDerivAt Dt Dst 0) :
    F 0 0 * Dst * F 0 0 =
      -(F 0 0 * Dt 0 * Ds * F 0 0 +
        F 0 0 * Ds * Dt 0 * F 0 0) := by
  let P : ℝ → A := fun s => F s 0
  have hrel : (fun s => Dt s * P s + P s * Dt s) = Dt := by
    funext s
    exact idempotentFamily_tangent_identity (F s) (Dt s) (ht s) (hidem s)
  have hderiv : HasDerivAt (fun s => Dt s * P s + P s * Dt s)
      ((Dst * P 0 + Dt 0 * Ds) + (Ds * Dt 0 + P 0 * Dst)) 0 := by
    exact (hst.mul hs).add (hs.mul hst)
  have hsecond :
      (Dst * P 0 + Dt 0 * Ds) + (Ds * Dt 0 + P 0 * Dst) = Dst := by
    exact (hrel ▸ hderiv).unique hst
  have hP2 : P 0 * P 0 = P 0 := by
    exact (hidem 0).eq_of_nhds
  change P 0 * Dst * P 0 =
    -(P 0 * Dt 0 * Ds * P 0 + P 0 * Ds * Dt 0 * P 0)
  have hc := congrArg (fun X : A => P 0 * X * P 0) hsecond
  have hc' :
      (P 0 * (Dst * (P 0 * P 0)) +
        (P 0 * Dt 0 * Ds * P 0 + P 0 * Ds * Dt 0 * P 0)) +
          P 0 * (P 0 * (Dst * P 0)) = P 0 * Dst * P 0 := by
    simpa only [mul_add, add_mul, mul_assoc, add_assoc] using hc
  have hfirst : P 0 * (Dst * (P 0 * P 0)) = P 0 * Dst * P 0 := by
    calc
      P 0 * (Dst * (P 0 * P 0)) = P 0 * (Dst * P 0) := by rw [hP2]
      _ = P 0 * Dst * P 0 := (mul_assoc _ _ _).symm
  have hlast : P 0 * (P 0 * (Dst * P 0)) = P 0 * Dst * P 0 := by
    calc
      P 0 * (P 0 * (Dst * P 0)) = (P 0 * P 0) * (Dst * P 0) :=
        (mul_assoc _ _ _).symm
      _ = P 0 * (Dst * P 0) := by rw [hP2]
      _ = P 0 * Dst * P 0 := (mul_assoc _ _ _).symm
  rw [hfirst, hlast] at hc'
  have hzero :
      P 0 * Dst * P 0 +
          (P 0 * Dt 0 * Ds * P 0 + P 0 * Ds * Dt 0 * P 0) = 0 := by
    apply add_right_cancel (b := P 0 * Dst * P 0)
    simpa only [zero_add] using hc'
  exact eq_neg_of_add_eq_zero_left hzero

/-! ## Normal corners and their polarized Gram -/

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normal corner of a tangent operator relative to an idempotent. -/
def projectionNormalCorner (P D : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 - P) * D * P

/-- A tangent to the idempotent locus has zero diagonal compression. -/
theorem idempotentTangent_compressed_eq_zero
    (P D : H →L[ℂ] H) (hP2 : P * P = P)
    (htan : D * P + P * D = D) :
    P * D * P = 0 := by
  have hc := congrArg (fun X : H →L[ℂ] H => P * X * P) htan
  have hc' :
      P * (D * (P * P)) + P * (P * (D * P)) = P * D * P := by
    simpa only [mul_add, add_mul, mul_assoc] using hc
  have hfirst : P * (D * (P * P)) = P * D * P := by
    calc
      P * (D * (P * P)) = P * (D * P) := by rw [hP2]
      _ = P * D * P := (mul_assoc _ _ _).symm
  have hdiag : P * (P * (D * P)) = P * D * P := by
    calc
      P * (P * (D * P)) = (P * P) * (D * P) := (mul_assoc _ _ _).symm
      _ = P * (D * P) := by rw [hP2]
      _ = P * D * P := (mul_assoc _ _ _).symm
  rw [hfirst, hdiag] at hc'
  have hcancel : P * D * P + P * D * P = P * D * P + 0 := by
    simpa only [add_zero] using hc'
  exact add_left_cancel hcancel

/-- The adjoint of the normal corner is the opposite normal corner. -/
theorem adjoint_projectionNormalCorner
    (P D : H →L[ℂ] H)
    (hPadj : adjoint P = P) (hDadj : adjoint D = D) :
    adjoint (projectionNormalCorner P D) = P * (D * (1 - P)) := by
  rw [projectionNormalCorner]
  change adjoint (((1 - P) * D) ∘L P) = _
  rw [adjoint_comp]
  change adjoint P ∘L adjoint ((1 - P) ∘L D) = _
  rw [adjoint_comp, adjoint_one_sub hPadj, hPadj, hDadj]
  rfl

/-- The compressed cross product of a self-adjoint tangent and any second direction is exactly
their normal Gram corner. -/
theorem projectionTangent_cross_eq_normalGram
    (P Ds Dt : H →L[ℂ] H)
    (hP2 : P * P = P)
    (hPadj : adjoint P = P)
    (hDtadj : adjoint Dt = Dt)
    (hDttan : Dt * P + P * Dt = Dt) :
    P * Dt * Ds * P =
      adjoint (projectionNormalCorner P Dt) * projectionNormalCorner P Ds := by
  have ht0 : P * Dt * P = 0 :=
    idempotentTangent_compressed_eq_zero P Dt hP2 hDttan
  rw [adjoint_projectionNormalCorner P Dt hPadj hDtadj]
  simp only [projectionNormalCorner]
  calc
    P * Dt * Ds * P = P * Dt * (1 : H →L[ℂ] H) * Ds * P := by simp
    _ = P * Dt * (P + (1 - P)) * Ds * P := by
      congr 3
      abel
    _ = P * Dt * (1 - P) * Ds * P := by
      simp only [mul_add, mul_assoc, ht0, zero_add]
    _ = (P * Dt * (1 - P)) * ((1 - P) * Ds * P) := by
      have hQ2 : (1 - P) * (1 - P) = 1 - P := by
        calc
          (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
          _ = 1 - P - P + P := by rw [hP2]
          _ = 1 - P := by abel
      have hgram :
          (P * Dt * (1 - P)) * ((1 - P) * Ds * P) =
            P * Dt * (1 - P) * Ds * P := by
        calc
          (P * Dt * (1 - P)) * ((1 - P) * Ds * P) =
              P * Dt * ((1 - P) * (1 - P)) * Ds * P := by
                simp only [mul_assoc]
          _ = P * Dt * (1 - P) * Ds * P := by rw [hQ2]
      exact hgram.symm

/-! ## Exact mixed curvature and compactness transfer -/

/-- For a self-adjoint idempotent family, mixed tangential curvature is the negative
polarized Gram of the two normal derivatives. -/
theorem selfAdjointIdempotentFamily_mixed_normalGram_identity
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (Ds Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t => F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s => F s 0) Ds 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDsadj : adjoint Ds = Ds)
    (hDtadj : adjoint (Dt 0) = Dt 0) :
    F 0 0 * Dst * F 0 0 =
      -(adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
          projectionNormalCorner (F 0 0) Ds +
        adjoint (projectionNormalCorner (F 0 0) Ds) *
          projectionNormalCorner (F 0 0) (Dt 0)) := by
  let P : H →L[ℂ] H := F 0 0
  have hP2 : P * P = P := (hidem 0).eq_of_nhds
  have hDttan : Dt 0 * P + P * Dt 0 = Dt 0 :=
    idempotentFamily_tangent_identity (F 0) (Dt 0) (ht 0) (hidem 0)
  have houterIdem :
      (fun s => F s 0 * F s 0) =ᶠ[nhds 0] (fun s => F s 0) :=
    Filter.Eventually.of_forall fun s => (hidem s).eq_of_nhds
  have hDstan : Ds * P + P * Ds = Ds :=
    idempotentFamily_tangent_identity (fun s => F s 0) Ds hs houterIdem
  have hcross_t_s :
      P * Dt 0 * Ds * P =
        adjoint (projectionNormalCorner P (Dt 0)) * projectionNormalCorner P Ds :=
    projectionTangent_cross_eq_normalGram P Ds (Dt 0)
      hP2 hPadj hDtadj hDttan
  have hcross_s_t :
      P * Ds * Dt 0 * P =
        adjoint (projectionNormalCorner P Ds) * projectionNormalCorner P (Dt 0) :=
    projectionTangent_cross_eq_normalGram P (Dt 0) Ds
      hP2 hPadj hDsadj hDstan
  have hmixed := idempotentFamily_mixed_compressed_identity F Dt Ds Dst ht hidem hs hst
  change P * Dst * P = _
  change P * Dst * P = -(P * Dt 0 * Ds * P + P * Ds * Dt 0 * P) at hmixed
  rw [hcross_t_s, hcross_s_t] at hmixed
  exact hmixed

/-- Compact mixed connection curvature forces compact polarized normal Gram curvature. -/
theorem selfAdjointIdempotentFamily_normalGram_isCompact
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (Ds Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t => F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s => F s 0) Ds 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDsadj : adjoint Ds = Ds)
    (hDtadj : adjoint (Dt 0) = Dt 0)
    (hDst : IsCompactOperator Dst) :
    IsCompactOperator
      (adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
          projectionNormalCorner (F 0 0) Ds +
        adjoint (projectionNormalCorner (F 0 0) Ds) *
          projectionNormalCorner (F 0 0) (Dt 0)) := by
  let G : H →L[ℂ] H :=
    adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
        projectionNormalCorner (F 0 0) Ds +
      adjoint (projectionNormalCorner (F 0 0) Ds) *
        projectionNormalCorner (F 0 0) (Dt 0)
  have hidentity := selfAdjointIdempotentFamily_mixed_normalGram_identity
    F Dt Ds Dst ht hidem hs hst hPadj hDsadj hDtadj
  have hcorner : IsCompactOperator (F 0 0 * Dst * F 0 0) := by
    simpa only [mul_assoc] using! (hDst.comp_clm (F 0 0)).clm_comp (F 0 0)
  have hEq : G = -(F 0 0 * Dst * F 0 0) := by
    have hneg := congrArg Neg.neg hidentity
    change -(F 0 0 * Dst * F 0 0) = -(-G) at hneg
    simpa only [neg_neg] using hneg.symm
  change IsCompactOperator G
  rw [hEq]
  exact hcorner.neg

/-- If the idempotent family varies compactly relative to its base point, the polarized normal
Gram is compact without a separate mixed-curvature hypothesis. -/
theorem selfAdjointIdempotentFamily_normalGram_isCompact_of_relativeFamily
    (F : ℝ → ℝ → (H →L[ℂ] H)) (Dt : ℝ → (H →L[ℂ] H))
    (Ds Dst : H →L[ℂ] H)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t => F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s => F s 0) Ds 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDsadj : adjoint Ds = Ds)
    (hDtadj : adjoint (Dt 0) = Dt 0)
    (hrelative : ∀ s t, IsCompactOperator (F s t - F 0 0)) :
    IsCompactOperator
      (adjoint (projectionNormalCorner (F 0 0) (Dt 0)) *
          projectionNormalCorner (F 0 0) Ds +
        adjoint (projectionNormalCorner (F 0 0) Ds) *
          projectionNormalCorner (F 0 0) (Dt 0)) := by
  let K : ℝ → ℝ → (H →L[ℂ] H) := fun s t => F s t - F 0 0
  have hKinner : ∀ s, HasDerivAt (K s) (Dt s) 0 := by
    intro s
    simpa [K] using (ht s).sub_const (F 0 0)
  have hcompactDst : IsCompactOperator Dst :=
    isCompactOperator_mixedDeriv_of_compact_operator_family
      K Dt Dst (by simpa [K] using hrelative) hKinner hst
  exact selfAdjointIdempotentFamily_normalGram_isCompact
    F Dt Ds Dst ht hidem hs hst hPadj hDsadj hDtadj hcompactDst

end

end RHTower
