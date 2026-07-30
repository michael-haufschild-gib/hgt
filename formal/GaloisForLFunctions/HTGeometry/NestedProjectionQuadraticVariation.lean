import GaloisForLFunctions.HTGeometry.FiniteClockResolutionVariance

/-!
# Quadratic variation and flatness of nested consequence projections

For nested orthogonal projections, the layer removed by restriction is itself an orthogonal
projection.  Passing a self-adjoint operator through that layer produces a positive Gram square.
These squares obey an exact compressed cocycle, so every diamond contained in one fixed carrier is
path-flat.

The identities are standard operator algebra.  Their role here is a no-go boundary for the
event-created-spacetime programme: nonzero force curvature cannot be obtained merely by supplying
one Hilbert carrier and a family of nested consequence projections.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Layer removed when the surviving carrier decreases from `P` to `Q`. -/
def nestedProjectionLostLayer
    (P Q : E →L[𝕜] E) : E →L[𝕜] E :=
  P - Q

/-- Passage through the layer removed between two nested consequence projections. -/
def nestedProjectionLostTransition
    (P Q D : E →L[𝕜] E) : E →L[𝕜] E :=
  (P - Q) * D * Q

/-- Positive-candidate quadratic variation created by the layer between `P` and `Q`. -/
def nestedProjectionQuadraticVariation
    (P Q D : E →L[𝕜] E) : E →L[𝕜] E :=
  Q * D * (P - Q) * D * Q

/-- Quadratic corner that leaves the carrier `P` and returns to it. -/
def nestedProjectionOffCarrierCorner
    (P D : E →L[𝕜] E) : E →L[𝕜] E :=
  P * D * (1 - P) * D * P

/-- The difference of two nested idempotents is idempotent when both absorption laws hold. -/
theorem nestedProjectionLostLayer_mul_self
    (P Q : E →L[𝕜] E)
    (hP2 : P * P = P) (hQ2 : Q * Q = Q)
    (hPQ : P * Q = Q) (hQP : Q * P = Q) :
    nestedProjectionLostLayer P Q * nestedProjectionLostLayer P Q =
      nestedProjectionLostLayer P Q := by
  unfold nestedProjectionLostLayer
  noncomm_ring [hP2, hQ2, hPQ, hQP]

/-- The layer between two self-adjoint projections is self-adjoint. -/
theorem adjoint_nestedProjectionLostLayer
    (P Q : E →L[𝕜] E)
    [CompleteSpace E]
    (hPadj : P.adjoint = P) (hQadj : Q.adjoint = Q) :
    (nestedProjectionLostLayer P Q).adjoint =
      nestedProjectionLostLayer P Q := by
  unfold nestedProjectionLostLayer
  rw [ContinuousLinearMap.adjoint.map_sub, hPadj, hQadj]

/-- **Exact restriction-defect law.** Restricting an off-carrier quadratic corner from `P` to an
absorbed carrier `Q` creates exactly the variation through the lost layer `P - Q`. -/
theorem nestedProjectionOffCarrierCorner_restrictionDefect
    (P Q D : E →L[𝕜] E)
    (hPQ : P * Q = Q) (hQP : Q * P = Q) :
    nestedProjectionOffCarrierCorner Q D -
        Q * nestedProjectionOffCarrierCorner P D * Q =
      nestedProjectionQuadraticVariation P Q D := by
  have hcompress :
      Q * (P * D * (1 - P) * D * P) * Q =
        Q * D * (1 - P) * D * Q := by
    calc
      Q * (P * D * (1 - P) * D * P) * Q =
          (Q * P) * D * (1 - P) * D * (P * Q) := by noncomm_ring
      _ = Q * D * (1 - P) * D * Q := by rw [hQP, hPQ]
  unfold nestedProjectionOffCarrierCorner
  unfold nestedProjectionQuadraticVariation
  rw [hcompress]
  noncomm_ring

/-- Adjoint of a self-adjoint transition through a self-adjoint lost layer. -/
theorem adjoint_nestedProjectionLostTransition
    (P Q D : E →L[𝕜] E)
    [CompleteSpace E]
    (hPadj : P.adjoint = P) (hQadj : Q.adjoint = Q)
    (hDadj : D.adjoint = D) :
    (nestedProjectionLostTransition P Q D).adjoint =
      Q * D * (P - Q) := by
  unfold nestedProjectionLostTransition
  change ContinuousLinearMap.adjoint (((P - Q) ∘L D) ∘L Q) =
    Q * D * (P - Q)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint.map_sub, hPadj, hQadj, hDadj]
  rfl

/-- **Lost-layer Gram law.** Under orthogonal nesting, quadratic variation is exactly the
adjoint square of the transition through the removed layer. -/
theorem nestedProjectionQuadraticVariation_eq_adjoint_mul
    (P Q D : E →L[𝕜] E)
    [CompleteSpace E]
    (hP2 : P * P = P) (hQ2 : Q * Q = Q)
    (hPQ : P * Q = Q) (hQP : Q * P = Q)
    (hPadj : P.adjoint = P) (hQadj : Q.adjoint = Q)
    (hDadj : D.adjoint = D) :
    nestedProjectionQuadraticVariation P Q D =
      (nestedProjectionLostTransition P Q D).adjoint *
        nestedProjectionLostTransition P Q D := by
  rw [adjoint_nestedProjectionLostTransition P Q D hPadj hQadj hDadj]
  unfold nestedProjectionQuadraticVariation
  unfold nestedProjectionLostTransition
  have hL := nestedProjectionLostLayer_mul_self P Q hP2 hQ2 hPQ hQP
  unfold nestedProjectionLostLayer at hL
  calc
    Q * D * (P - Q) * D * Q =
        Q * D * ((P - Q) * (P - Q)) * D * Q := by rw [hL]
    _ = (Q * D * (P - Q)) * ((P - Q) * D * Q) := by noncomm_ring

/-- **Compressed quadratic-variation cocycle.** Variation across a two-step restriction is the
last-step variation plus the earlier variation transported to the final carrier. -/
theorem nestedProjectionQuadraticVariation_compressed_cocycle
    (P Q R D : E →L[𝕜] E)
    (hQR : Q * R = R) (hRQ : R * Q = R) :
    nestedProjectionQuadraticVariation P R D =
      nestedProjectionQuadraticVariation Q R D +
        R * nestedProjectionQuadraticVariation P Q D * R := by
  have hcompress :
      R * (Q * D * (P - Q) * D * Q) * R =
        R * D * (P - Q) * D * R := by
    calc
      R * (Q * D * (P - Q) * D * Q) * R =
          (R * Q) * D * (P - Q) * D * (Q * R) := by noncomm_ring
      _ = R * D * (P - Q) * D * R := by rw [hRQ, hQR]
  unfold nestedProjectionQuadraticVariation
  rw [hcompress]
  noncomm_ring

/-- **Fixed-carrier diamond flatness.** Any two intermediate absorbed carriers give the same
transported quadratic variation between common endpoints. -/
theorem nestedProjectionQuadraticVariation_diamond_flat
    (P Q₁ Q₂ R D : E →L[𝕜] E)
    (hQ₁R : Q₁ * R = R) (hRQ₁ : R * Q₁ = R)
    (hQ₂R : Q₂ * R = R) (hRQ₂ : R * Q₂ = R) :
    nestedProjectionQuadraticVariation Q₁ R D +
        R * nestedProjectionQuadraticVariation P Q₁ D * R =
      nestedProjectionQuadraticVariation Q₂ R D +
        R * nestedProjectionQuadraticVariation P Q₂ D * R := by
  rw [← nestedProjectionQuadraticVariation_compressed_cocycle
      P Q₁ R D hQ₁R hRQ₁,
    ← nestedProjectionQuadraticVariation_compressed_cocycle
      P Q₂ R D hQ₂R hRQ₂]

/-- Ordinary additive curvature of three quadratic-variation edges. -/
def nestedProjectionQuadraticCurvature
    (P Q R D : E →L[𝕜] E) : E →L[𝕜] E :=
  nestedProjectionQuadraticVariation P R D -
    nestedProjectionQuadraticVariation P Q D -
      nestedProjectionQuadraticVariation Q R D

/-- Triple curvature is compression minus identity of the variation on the first edge. -/
theorem nestedProjectionQuadraticCurvature_eq_compression_sub_self
    (P Q R D : E →L[𝕜] E)
    (hQR : Q * R = R) (hRQ : R * Q = R) :
    nestedProjectionQuadraticCurvature P Q R D =
      R * nestedProjectionQuadraticVariation P Q D * R -
        nestedProjectionQuadraticVariation P Q D := by
  have hcocycle :=
    nestedProjectionQuadraticVariation_compressed_cocycle
      P Q R D hQR hRQ
  unfold nestedProjectionQuadraticCurvature
  rw [hcocycle]
  abel

/-- A projection compression equal to the compressed projection forces both absorption laws. -/
theorem projection_absorption_of_compression_eq_self
    (Q R : E →L[𝕜] E)
    [CompleteSpace E]
    (hQ2 : Q * Q = Q) (hR2 : R * R = R)
    (hQadj : Q.adjoint = Q) (hRadj : R.adjoint = R)
    (hRQR : R * Q * R = R) :
    Q * R = R ∧ R * Q = R := by
  let X : E →L[𝕜] E := (1 - Q) * R
  have hQcomp2 : (1 - Q) * (1 - Q) = 1 - Q := by
    noncomm_ring [hQ2]
  have hXadj : X.adjoint = R * (1 - Q) := by
    dsimp only [X]
    change ContinuousLinearMap.adjoint ((1 - Q) ∘L R) = R * (1 - Q)
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint.map_sub,
      ContinuousLinearMap.adjoint_one, hQadj, hRadj]
    rfl
  have hXstar : X.adjoint * X = 0 := by
    rw [hXadj]
    dsimp only [X]
    calc
      (R * (1 - Q)) * ((1 - Q) * R) =
          R * ((1 - Q) * (1 - Q)) * R := by noncomm_ring
      _ = R * (1 - Q) * R := by rw [hQcomp2]
      _ = 0 := by noncomm_ring [hRQR, hR2]
  have hXzero : X = 0 := by
    rw [← ContinuousLinearMap.star_eq_adjoint] at hXstar
    exact (CStarRing.star_mul_self_eq_zero_iff X).mp hXstar
  have hQR : Q * R = R := by
    dsimp only [X] at hXzero
    have hdiff : R - Q * R = 0 := by
      simpa only [sub_mul, one_mul] using hXzero
    exact (sub_eq_zero.mp hdiff).symm
  have hadj := congrArg ContinuousLinearMap.adjoint hQR
  have hRQ : R * Q = R := by
    change ContinuousLinearMap.adjoint (Q ∘L R) =
      ContinuousLinearMap.adjoint R at hadj
    rw [ContinuousLinearMap.adjoint_comp, hQadj, hRadj] at hadj
    exact hadj
  exact ⟨hQR, hRQ⟩

/-- **Unit flatness detects absorption.** For orthogonal projections, the quadratic cocycle with
unit top carrier and unit passage is flat exactly when `R` is absorbed by `Q` on both sides. -/
theorem nestedProjectionQuadraticVariation_unit_flat_iff_absorption
    (Q R : E →L[𝕜] E)
    [CompleteSpace E]
    (hQ2 : Q * Q = Q) (hR2 : R * R = R)
    (hQadj : Q.adjoint = Q) (hRadj : R.adjoint = R) :
    nestedProjectionQuadraticVariation 1 R 1 =
        nestedProjectionQuadraticVariation Q R 1 +
          R * nestedProjectionQuadraticVariation 1 Q 1 * R ↔
      Q * R = R ∧ R * Q = R := by
  constructor
  · intro hflat
    have htopR : nestedProjectionQuadraticVariation 1 R 1 = 0 := by
      unfold nestedProjectionQuadraticVariation
      noncomm_ring [hR2]
    have htopQ : nestedProjectionQuadraticVariation 1 Q 1 = 0 := by
      unfold nestedProjectionQuadraticVariation
      noncomm_ring [hQ2]
    have hmiddle :
        nestedProjectionQuadraticVariation Q R 1 =
          R * Q * R - R := by
      unfold nestedProjectionQuadraticVariation
      noncomm_ring [hR2]
    have hRQR : R * Q * R = R := by
      rw [htopR, htopQ, hmiddle] at hflat
      simp only [mul_zero, zero_mul, add_zero] at hflat
      exact sub_eq_zero.mp hflat.symm
    exact projection_absorption_of_compression_eq_self
      Q R hQ2 hR2 hQadj hRadj hRQR
  · rintro ⟨hQR, hRQ⟩
    exact nestedProjectionQuadraticVariation_compressed_cocycle
      1 Q R 1 hQR hRQ

end

end GaloisForLFunctions.HTGeometry
