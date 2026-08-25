import GaloisForLFunctions.RHTower.PositiveSchattenDiagonalJensen
import GaloisForLFunctions.HTGeometry.DeterminantCompletionNaturality

/-!
# Positive Schatten responses along bounded packets

Compressing a positive Schatten operator through any bounded synthesis map preserves positivity
and the same Schatten exponent.  Applying the positive diagonal Jensen theorem to the compression
shows that every bounded image of an orthonormal packet has summable positive `q`-responses.
-/

open ContinuousLinearMap

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Same-space compression of `T` through a bounded packet synthesis map `A`. -/
def positiveSchattenPacketCompression (A T : H →L[ℂ] H) : H →L[ℂ] H :=
  adjoint A ∘L T ∘L A

/-- A bounded compression of a positive operator remains positive. -/
theorem positiveSchattenPacketCompression_nonneg
    {A T : H →L[ℂ] H} (hT : 0 ≤ T) :
    0 ≤ positiveSchattenPacketCompression A T := by
  have hpos : T.IsPositive := by
    rw [ContinuousLinearMap.le_def, sub_zero] at hT
    exact hT
  have h := hpos.conj_adjoint (adjoint A)
  rw [adjoint_adjoint] at h
  rw [ContinuousLinearMap.le_def, sub_zero]
  simpa [positiveSchattenPacketCompression, ContinuousLinearMap.comp_assoc] using h

/-- A bounded compression preserves every positive Schatten exponent. -/
theorem positiveSchattenPacketCompression_memSchattenClass
    {A T : H →L[ℂ] H} {q : ℝ} (hq : 0 < q)
    (hT : MemSchattenClass q T) :
    MemSchattenClass q (positiveSchattenPacketCompression A T) := by
  unfold positiveSchattenPacketCompression
  exact GaloisForLFunctions.HTGeometry.memSchattenClass_comp_left hq
    (GaloisForLFunctions.HTGeometry.memSchattenClass_comp_right hq hT)

/-- Positive responses of a Schatten-`q` operator along any bounded image of an orthonormal packet
are `q`-summable.  No orthogonality of the image packet is required. -/
theorem summable_rpow_bounded_packet_response_of_nonneg_of_memSchattenClass
    {A T : H →L[ℂ] H} {ι : Type*} {q : ℝ} (hq : 1 ≤ q) (hT : 0 ≤ T)
    (hSch : MemSchattenClass q T) (g : ι → H)
    (hg : ∀ i, g i = 0 ∨ ‖g i‖ = 1)
    (hgo : ∀ i j, i ≠ j → inner ℂ (g i) (g j) = 0) :
    Summable fun i =>
      RCLike.re (inner ℂ (A (g i)) (T (A (g i))) : ℂ) ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcompNonneg := positiveSchattenPacketCompression_nonneg (A := A) hT
  have hcompSch := positiveSchattenPacketCompression_memSchattenClass
    (A := A) hq0 hSch
  have hsum :=
    ContinuousLinearMap.summable_rpow_re_inner_apply_of_nonneg_of_memSchattenClass
      hq hcompNonneg hcompSch g hg hgo
  simpa [positiveSchattenPacketCompression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right] using hsum

end

end RHTower
