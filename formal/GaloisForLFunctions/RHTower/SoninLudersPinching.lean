import GaloisForLFunctions.RHTower.CCMSoninResolventCommutator

/-!
# Lüders pinching removes cutoff-commutation hypotheses

For an idempotent cutoff `e`, the nonselective two-outcome measurement channel

`D_e(X) = eXe + (1-e)X(1-e)`

deletes both off-diagonal cutoff corners.  Consequently `D_e(X)` commutes with `e` for every
input `X`.  The exact identity

`X + (1-2e)X(1-2e) = 2 D_e(X)`

also identifies this Lüders channel with the finite `Z₂` parity twirl whenever division by two is
available.

The final theorem substitutes the pinched observable into the existing resolvent-dressed Sonin
commutator formula.  It removes that theorem's assumed commutation with the physical cutoff; the
only surviving anomaly channel is again the Fourier-edge commutator.
-/

namespace RHTower

noncomputable section

variable {R : Type*} [Ring R]

/-- The nonselective two-outcome Lüders pinching associated with an idempotent cutoff. -/
def ludersPinching (e X : R) : R :=
  e * X * e + (1 - e) * X * (1 - e)

/-- The parity involution associated with a two-sector cutoff. -/
def cutoffParity (e : R) : R :=
  1 - 2 * e

/-- The Lüders channel is exactly the normalized `Z₂` parity twirl, stated without division:
the parity-orbit sum is twice the pinching.  This polynomial identity does not itself require
idempotence. -/
theorem parityTwirlNumerator_eq_two_mul_ludersPinching (e X : R) :
    X + cutoffParity e * X * cutoffParity e = 2 * ludersPinching e X := by
  simp only [cutoffParity, ludersPinching]
  noncomm_ring

/-- The disturbance deleted by a nonselective Lüders measurement is exactly the sum of the two
off-diagonal cutoff corners already used by the RHTower boundary calculus.  This block identity
does not require idempotence. -/
theorem sub_ludersPinching_eq_crossBoundary_add_upperBoundary (e X : R) :
    X - ludersPinching e X = crossBoundary e X + upperBoundary e X := by
  simp only [ludersPinching, crossBoundary, upperBoundary]
  noncomm_ring

/-- Every observable splits exactly into its cutoff-commuting Lüders block and the two native
RHTower boundary channels. -/
theorem ludersPinching_add_boundaries_eq (e X : R) :
    ludersPinching e X + (crossBoundary e X + upperBoundary e X) = X := by
  rw [← sub_ludersPinching_eq_crossBoundary_add_upperBoundary e X]
  abel

/-- The lower measurement-disturbance corner is the right cutoff block of the cutoff
commutator. -/
theorem crossBoundary_eq_ccmCommutator_mul_cutoff
    {e : R} (he : IsIdempotentElem e) (X : R) :
    crossBoundary e X = ccmCommutator X e * e := by
  have hee : e * e = e := he
  simp only [crossBoundary, ccmCommutator, sub_mul]
  rw [show X * e * e = X * e by rw [mul_assoc, hee]]
  noncomm_ring

/-- The upper measurement-disturbance corner is the negative left cutoff block of the cutoff
commutator. -/
theorem upperBoundary_eq_neg_cutoff_mul_ccmCommutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    upperBoundary e X = -(e * ccmCommutator X e) := by
  have hee : e * e = e := he
  simp only [upperBoundary, ccmCommutator, mul_sub]
  rw [show e * (e * X) = e * X by rw [← mul_assoc, hee]]
  noncomm_ring

/-- **Pure-dephasing double-commutator law.**  For an idempotent measurement cutoff, the part
deleted by the nonselective Lüders channel is exactly the double commutator with that cutoff. -/
theorem sub_ludersPinching_eq_doubleCommutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    X - ludersPinching e X = ccmCommutator e (ccmCommutator e X) := by
  have hee : e * e = e := he
  simp only [ludersPinching, ccmCommutator, mul_sub, sub_mul]
  rw [show e * (e * X) = e * X by rw [← mul_assoc, hee],
    show X * e * e = X * e by rw [mul_assoc, hee]]
  noncomm_ring

/-- The same dephasing disturbance is the reverse-oriented double commutator.  This form makes
compactness propagate directly from essential commutation with the cutoff. -/
theorem sub_ludersPinching_eq_reverseDoubleCommutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    X - ludersPinching e X = ccmCommutator (ccmCommutator X e) e := by
  rw [sub_ludersPinching_eq_crossBoundary_add_upperBoundary,
    crossBoundary_eq_ccmCommutator_mul_cutoff he,
    upperBoundary_eq_neg_cutoff_mul_ccmCommutator he]
  simp only [ccmCommutator]
  abel

/-- An idempotent cutoff acts on the left of its pinching by selecting the cutoff block. -/
theorem mul_ludersPinching_eq_cutoffBlock
    {e : R} (he : IsIdempotentElem e) (X : R) :
    e * ludersPinching e X = e * X * e := by
  have hee : e * e = e := he
  have hec : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, hee, sub_self]
  simp only [ludersPinching, mul_add, ← mul_assoc, hee, hec, zero_mul, add_zero]

/-- An idempotent cutoff acts on the right of its pinching by selecting the same cutoff block. -/
theorem ludersPinching_mul_eq_cutoffBlock
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ludersPinching e X * e = e * X * e := by
  have hee : e * e = e := he
  have hce : (1 - e) * e = 0 := by
    rw [sub_mul, one_mul, hee, sub_self]
  simp only [ludersPinching, add_mul, mul_assoc, hee, hce, mul_zero, add_zero]

/-- A nonselective Lüders pinching commutes with the measured cutoff, with no premise on the
unpinched observable. -/
theorem ccmCommutator_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ccmCommutator (ludersPinching e X) e = 0 := by
  rw [ccmCommutator, ludersPinching_mul_eq_cutoffBlock he,
    mul_ludersPinching_eq_cutoffBlock he, sub_self]

/-- The cutoff commutator of an observable is exactly the cutoff commutator of the part deleted
by the Lüders channel.  Thus all failure of cutoff commutation lives in measurement disturbance,
not in the block-diagonal measured observable. -/
theorem ccmCommutator_eq_ludersDisturbance_commutator
    {e : R} (he : IsIdempotentElem e) (X : R) :
    ccmCommutator X e = ccmCommutator (X - ludersPinching e X) e := by
  have hzero := ccmCommutator_ludersPinching_eq_zero he X
  rw [ccmCommutator] at hzero
  have hpinched : ludersPinching e X * e = e * ludersPinching e X :=
    sub_eq_zero.mp hzero
  simp only [ccmCommutator, sub_mul, mul_sub]
  rw [hpinched]
  abel

/-- The Lüders pinching deletes the lower cutoff-boundary corner of every observable. -/
theorem crossBoundary_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    crossBoundary e (ludersPinching e X) = 0 := by
  apply crossBoundary_eq_zero_of_commute he
  exact sub_eq_zero.mp (ccmCommutator_ludersPinching_eq_zero he X)

/-- The Lüders pinching also deletes the upper cutoff-boundary corner. -/
theorem upperBoundary_ludersPinching_eq_zero
    {e : R} (he : IsIdempotentElem e) (X : R) :
    upperBoundary e (ludersPinching e X) = 0 := by
  apply upperBoundary_eq_zero_of_commute he
  exact sub_eq_zero.mp (ccmCommutator_ludersPinching_eq_zero he X)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A commutator is compact when its left entry is compact. -/
theorem isCompactOperator_ccmCommutator_of_leftCompact
    (K Y : H →L[ℂ] H) (hK : IsCompactOperator K) :
    IsCompactOperator (ccmCommutator K Y : H →L[ℂ] H) := by
  rw [ccmCommutator]
  exact (hK.comp_clm Y).sub (hK.clm_comp Y)

/-- **Compact disturbance/essential commutation equivalence.**  For an idempotent measurement
cutoff, compactness of the Lüders disturbance is equivalent to commutation with the cutoff modulo
compact operators.  This replaces an operator-algebra premise by the directly measurable
dephasing residual `X - D_e(X)`. -/
theorem isCompactOperator_ludersDisturbance_iff_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e) :
    IsCompactOperator (X - ludersPinching e X : H →L[ℂ] H) ↔
      IsCompactOperator (ccmCommutator X e : H →L[ℂ] H) := by
  constructor
  · intro hdist
    rw [ccmCommutator_eq_ludersDisturbance_commutator he]
    exact isCompactOperator_ccmCommutator_of_leftCompact _ _ hdist
  · intro hcomm
    rw [sub_ludersPinching_eq_reverseDoubleCommutator he]
    exact isCompactOperator_ccmCommutator_of_leftCompact _ _ hcomm

/-- Essential commutation with a projection makes its lower Lüders disturbance corner compact. -/
theorem isCompactOperator_crossBoundary_of_compact_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (hcomm : IsCompactOperator (ccmCommutator X e : H →L[ℂ] H)) :
    IsCompactOperator (crossBoundary e X : H →L[ℂ] H) := by
  simpa only [crossBoundary_eq_ccmCommutator_mul_cutoff he] using hcomm.comp_clm e

/-- Essential commutation with a projection also makes its upper Lüders disturbance corner
compact. -/
theorem isCompactOperator_upperBoundary_of_compact_cutoffCommutator
    (e X : H →L[ℂ] H) (he : IsIdempotentElem e)
    (hcomm : IsCompactOperator (ccmCommutator X e : H →L[ℂ] H)) :
    IsCompactOperator (upperBoundary e X : H →L[ℂ] H) := by
  simpa only [upperBoundary_eq_neg_cutoff_mul_ccmCommutator he] using
    (hcomm.clm_comp e).neg

variable [CompleteSpace H]

/-- **Pinched Sonin commutator law.**  Replacing an arbitrary observable by its nonselective
Lüders pinching at the physical cutoff removes the commutation premise from the exact
resolvent-dressed Sonin formula. -/
theorem ccmCommutator_ludersPinching_soninIntersectionProjection
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    ccmCommutator X₀ (soninIntersectionProjection A B) =
      -E * V *
        (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
            B.starProjection +
          B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
            B.starProjection +
          ccmCommutator X₀ B.starProjection) * E := by
  dsimp
  exact ccmCommutator_soninIntersectionProjection A B hT _
    (ccmCommutator_ludersPinching_eq_zero
      A.isIdempotentElem_starProjection X)

/-- **Hypothesis-free Sonin boundary split for the original observable.**  An arbitrary `X`
decomposes into its Lüders block, whose exact Sonin commutator is controlled solely by the
Fourier-edge commutator, and its two physical-cutoff boundary corners.  Thus the former assumed
commutation with the physical cutoff is replaced by an explicit residual in the boundary
language already consumed throughout RHTower. -/
theorem ccmCommutator_soninIntersectionProjection_ludersBoundarySplit
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H) :
    let X₀ := ludersPinching A.starProjection X
    let Xoff := crossBoundary A.starProjection X + upperBoundary A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    ccmCommutator X (soninIntersectionProjection A B) =
      -E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E +
        ccmCommutator Xoff (soninIntersectionProjection A B) := by
  dsimp
  have hsplit : X = ludersPinching A.starProjection X +
      (crossBoundary A.starProjection X + upperBoundary A.starProjection X) := by
    exact (ludersPinching_add_boundaries_eq A.starProjection X).symm
  nth_rw 1 [hsplit]
  have hadd : ∀ Y Z P : H →L[ℂ] H,
      ccmCommutator (Y + Z) P = ccmCommutator Y P + ccmCommutator Z P := by
    intro Y Z P
    simp only [ccmCommutator, add_mul, mul_add]
    abel
  nth_rw 1 [hadd]
  rw [ccmCommutator_ludersPinching_soninIntersectionProjection A B hT X]

omit [CompleteSpace H] in
/-- Compact physical-cutoff corners make the complete Lüders disturbance term compact after
commutation with the exact Sonin projection. -/
theorem isCompactOperator_soninLudersBoundaryResidual
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (X : H →L[ℂ] H)
    (hlower : IsCompactOperator
      (crossBoundary A.starProjection X : H →L[ℂ] H))
    (hupper : IsCompactOperator
      (upperBoundary A.starProjection X : H →L[ℂ] H)) :
    IsCompactOperator
      (ccmCommutator
        (crossBoundary A.starProjection X + upperBoundary A.starProjection X)
        (soninIntersectionProjection A B) : H →L[ℂ] H) := by
  exact isCompactOperator_ccmCommutator_of_leftCompact _ _ (hlower.add hupper)

/-- **Calkin-level Sonin formula without cutoff commutation.**  If the two physical-cutoff
corners of an arbitrary observable are compact, then its exact Sonin commutator differs by a
compact operator from the Fourier-edge dressed formula of its Lüders block.  This is the direct
consumer of the boundary split in the existing compact-operator layer. -/
theorem isCompactOperator_soninCommutator_sub_ludersDressed
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H)
    (hlower : IsCompactOperator
      (crossBoundary A.starProjection X : H →L[ℂ] H))
    (hupper : IsCompactOperator
      (upperBoundary A.starProjection X : H →L[ℂ] H)) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    IsCompactOperator
      (ccmCommutator X (soninIntersectionProjection A B) -
        (-E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E) : H →L[ℂ] H) := by
  dsimp
  let D : H →L[ℂ] H :=
    -A.orthogonal.starProjection * soninProjectionResolvent A B hT *
      (ccmCommutator (ludersPinching A.starProjection X) B.starProjection *
            A.starProjection * B.starProjection * soninProjectionResolvent A B hT *
            B.starProjection +
        B.starProjection * A.starProjection *
            ccmCommutator (ludersPinching A.starProjection X) B.starProjection *
            soninProjectionResolvent A B hT * B.starProjection +
        ccmCommutator (ludersPinching A.starProjection X) B.starProjection) *
      A.orthogonal.starProjection
  let L : H →L[ℂ] H :=
    ccmCommutator X (soninIntersectionProjection A B) - D
  let K : H →L[ℂ] H :=
    ccmCommutator
      (crossBoundary A.starProjection X + upperBoundary A.starProjection X)
      (soninIntersectionProjection A B)
  change IsCompactOperator (fun x : H => L x)
  have hresidual := isCompactOperator_soninLudersBoundaryResidual
    A B X hlower hupper
  change IsCompactOperator (fun x : H => K x) at hresidual
  have hsplit :=
    ccmCommutator_soninIntersectionProjection_ludersBoundarySplit A B hT X
  dsimp at hsplit
  have hdiff : L = K := by
    dsimp only [L, K, D]
    rw [hsplit]
    abel
  have hfun : (fun x : H => L x) = fun x : H => K x := by
    funext x
    rw [hdiff]
  rw [hfun]
  exact hresidual

/-- **Essential-commutation Sonin/Calkin law.**  The two separate compact-corner premises collapse
to the single physics-native assumption that `X` commutes with the physical cutoff modulo compact
operators.  Under that premise, the arbitrary-observable Sonin commutator still equals the
Lüders-block Fourier-edge dressed formula in the Calkin algebra. -/
theorem isCompactOperator_soninCommutator_sub_ludersDressed_of_cutoffCommutator
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H)
    (hcomm : IsCompactOperator
      (ccmCommutator X A.starProjection : H →L[ℂ] H)) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    IsCompactOperator
      (ccmCommutator X (soninIntersectionProjection A B) -
        (-E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E) : H →L[ℂ] H) := by
  apply isCompactOperator_soninCommutator_sub_ludersDressed A B hT X
  · exact isCompactOperator_crossBoundary_of_compact_cutoffCommutator
      A.starProjection X A.isIdempotentElem_starProjection hcomm
  · exact isCompactOperator_upperBoundary_of_compact_cutoffCommutator
      A.starProjection X A.isIdempotentElem_starProjection hcomm

/-- **Measurement-disturbance Sonin/Calkin law.**  Compactness of the observable part erased by
the physical-cutoff Lüders measurement is sufficient for the exact Calkin-level Sonin formula.
This is the dephasing-native form of essential cutoff commutation. -/
theorem isCompactOperator_soninCommutator_sub_ludersDressed_of_compactDisturbance
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection]
    [(A.orthogonal ⊓ B.orthogonal).HasOrthogonalProjection]
    (hT : ‖soninAlternatingBlock A B‖ < 1)
    (X : H →L[ℂ] H)
    (hdist : IsCompactOperator
      (X - ludersPinching A.starProjection X : H →L[ℂ] H)) :
    let X₀ := ludersPinching A.starProjection X
    let E := A.orthogonal.starProjection
    let V := soninProjectionResolvent A B hT
    IsCompactOperator
      (ccmCommutator X (soninIntersectionProjection A B) -
        (-E * V *
          (ccmCommutator X₀ B.starProjection * A.starProjection * B.starProjection * V *
              B.starProjection +
            B.starProjection * A.starProjection * ccmCommutator X₀ B.starProjection * V *
              B.starProjection +
            ccmCommutator X₀ B.starProjection) * E) : H →L[ℂ] H) := by
  exact isCompactOperator_soninCommutator_sub_ludersDressed_of_cutoffCommutator
    A B hT X
    ((isCompactOperator_ludersDisturbance_iff_cutoffCommutator
      A.starProjection X A.isIdempotentElem_starProjection).mp hdist)

/-- **Concrete central-cutoff Sonin/Calkin law.**  For a positive central time-frequency cutoff,
compactness of the physical-cutoff commutator is the only remaining operator hypothesis.  The
strict-contraction premise is discharged by the concrete time-band geometry, while Lüders
pinching discharges both separate compact-corner premises. -/
theorem isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_cutoffCommutator
    (a : ℝ) (ha : 0 < a)
    (X : SoninL2 →L[ℂ] SoninL2)
    (hcomm : IsCompactOperator
      (ccmCommutator X (centralPhysicalForbidden a).starProjection :
        SoninL2 →L[ℂ] SoninL2)) :
    let hT := norm_centralSoninAlternatingBlock_lt_one a ha
    let X₀ := ludersPinching (centralPhysicalForbidden a).starProjection X
    let E := (centralPhysicalForbidden a).orthogonal.starProjection
    let V := soninProjectionResolvent
      (centralPhysicalForbidden a) (centralFourierForbidden a) hT
    IsCompactOperator
      (ccmCommutator X (centralSoninProjection a) -
        (-E * V *
          (ccmCommutator X₀ (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                ccmCommutator X₀ (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            ccmCommutator X₀ (centralFourierForbidden a).starProjection) * E) :
        SoninL2 →L[ℂ] SoninL2) := by
  dsimp only
  exact isCompactOperator_soninCommutator_sub_ludersDressed_of_cutoffCommutator
    (centralPhysicalForbidden a) (centralFourierForbidden a)
    (norm_centralSoninAlternatingBlock_lt_one a ha) X hcomm

/-- **Concrete central measurement-disturbance law.**  For a positive central time-frequency
cutoff, compactness of the part erased by the physical Lüders measurement is the sole operator
premise needed for the Calkin-level Sonin formula. -/
theorem isCompactOperator_centralSoninCommutator_sub_ludersDressed_of_compactDisturbance
    (a : ℝ) (ha : 0 < a)
    (X : SoninL2 →L[ℂ] SoninL2)
    (hdist : IsCompactOperator
      (X - ludersPinching (centralPhysicalForbidden a).starProjection X :
        SoninL2 →L[ℂ] SoninL2)) :
    let hT := norm_centralSoninAlternatingBlock_lt_one a ha
    let X₀ := ludersPinching (centralPhysicalForbidden a).starProjection X
    let E := (centralPhysicalForbidden a).orthogonal.starProjection
    let V := soninProjectionResolvent
      (centralPhysicalForbidden a) (centralFourierForbidden a) hT
    IsCompactOperator
      (ccmCommutator X (centralSoninProjection a) -
        (-E * V *
          (ccmCommutator X₀ (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            (centralFourierForbidden a).starProjection *
                (centralPhysicalForbidden a).starProjection *
                ccmCommutator X₀ (centralFourierForbidden a).starProjection * V *
                (centralFourierForbidden a).starProjection +
            ccmCommutator X₀ (centralFourierForbidden a).starProjection) * E) :
        SoninL2 →L[ℂ] SoninL2) := by
  dsimp only
  exact isCompactOperator_soninCommutator_sub_ludersDressed_of_compactDisturbance
    (centralPhysicalForbidden a) (centralFourierForbidden a)
    (norm_centralSoninAlternatingBlock_lt_one a ha) X hdist

end

end RHTower
