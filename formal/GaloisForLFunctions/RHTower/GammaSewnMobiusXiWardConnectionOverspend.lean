import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift

/-!
# Four-unit connection overspend for the continued Xi Ward column

At a zero strictly to the right of the critical line, the adapted continued-Xi
Ward column is too large to be represented by a connection vector of squared
norm at most four against a source father with the Möbius boundary norm budget.

Consequently, an orthogonal connection correction cannot produce a four-unit
source lift.  Any nonorthogonal correction that does stay inside the four-unit
budget must cancel the transported detail by a quantitatively strict negative
interference term.  More decisively, if the transported detail remains
orthogonal to the father—as it does for the doubled Möbius source—no
connection correction can satisfy both the adapted Ward column and the
four-unit bound, irrespective of interference between the two detail terms.
-/

open Complex

namespace RHTower

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Adapted Ward connection overspend.**

If a source father obeys the Möbius boundary norm budget at a strict-right Xi
zero and a connection vector represents the continued-Xi Ward column there,
then the connection alone has squared norm strictly greater than four. -/
theorem norm_connection_sq_gt_four_of_adaptedWardColumn
    (q : XiRightUpperZeroCopy) (father connection : K)
    (hfather :
      ‖father‖ ^ 2 ≤
        (2 * (xiRightCenteredZero q.1).re)⁻¹)
    (hcolumn :
      inner ℂ father connection =
        continuedXiAntiCausalWardResponse
          ((starRingEnd ℂ) (xiRightCenteredZero q.1))) :
    4 < ‖connection‖ ^ 2 := by
  let a := (xiRightCenteredZero q.1).re
  have ha : 0 < a := xiRightCenteredZero_re_pos q.1
  have hr :=
    normSq_continuedXiAntiCausalWardResponse_at_adaptedNode_gt q
  have hr' :
      2 * a⁻¹ < ‖inner ℂ father connection‖ ^ 2 := by
    rw [hcolumn, Complex.sq_norm]
    simpa only [a] using hr
  have hinner := norm_inner_le_norm (𝕜 := ℂ) father connection
  have hinnerSq :
      ‖inner ℂ father connection‖ ^ 2 ≤
        (‖father‖ * ‖connection‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
  have hfactor :
      (2 * a)⁻¹ = (1 / 2 : ℝ) * a⁻¹ := by
    field_simp [ha.ne']
  have hproduct :
      ‖father‖ ^ 2 * ‖connection‖ ^ 2 ≤
        ((1 / 2 : ℝ) * a⁻¹) * ‖connection‖ ^ 2 := by
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_right hfather (sq_nonneg _)
  have hexpand :
      (‖father‖ * ‖connection‖) ^ 2 =
        ‖father‖ ^ 2 * ‖connection‖ ^ 2 := by
    ring
  rw [hexpand] at hinnerSq
  have hainv : 0 < a⁻¹ := inv_pos.mpr ha
  nlinarith

/-- No Hilbert-space detail of squared norm at most four can represent the
adapted continued-Xi Ward column against a father obeying the Möbius boundary
norm budget.  This statement has no orthogonality or decomposition premise. -/
theorem not_exists_fourUnit_adaptedWardDetail
    (q : XiRightUpperZeroCopy) :
    ¬ ∃ father detail : K,
      ‖father‖ ^ 2 ≤
          (2 * (xiRightCenteredZero q.1).re)⁻¹ ∧
        inner ℂ father detail =
          continuedXiAntiCausalWardResponse
            ((starRingEnd ℂ) (xiRightCenteredZero q.1)) ∧
        ‖detail‖ ^ 2 ≤ 4 := by
  rintro ⟨father, detail, hfather, hcolumn, hdetail⟩
  exact (not_lt_of_ge hdetail)
    (norm_connection_sq_gt_four_of_adaptedWardColumn
      q father detail hfather hcolumn)

/-- An orthogonal connection carrying the adapted Ward column necessarily
pushes the augmented detail strictly beyond the four-unit source budget. -/
theorem norm_orthogonal_connection_augmentedDetail_sq_gt_four
    (q : XiRightUpperZeroCopy) (father transported connection : K)
    (hfather :
      ‖father‖ ^ 2 ≤
        (2 * (xiRightCenteredZero q.1).re)⁻¹)
    (hcolumn :
      inner ℂ father connection =
        continuedXiAntiCausalWardResponse
          ((starRingEnd ℂ) (xiRightCenteredZero q.1)))
    (horth : inner ℂ transported connection = 0) :
    4 < ‖transported + connection‖ ^ 2 := by
  have hc :=
    norm_connection_sq_gt_four_of_adaptedWardColumn
      q father connection hfather hcolumn
  have hpyth :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      transported connection horth
  calc
    4 < ‖connection‖ ^ 2 := hc
    _ ≤ ‖transported‖ ^ 2 + ‖connection‖ ^ 2 := by
      exact le_add_of_nonneg_left (sq_nonneg _)
    _ = ‖transported + connection‖ ^ 2 := by
      simpa only [pow_two] using hpyth.symm

/-- Universal four-unit cancellation law: a correction whose own squared norm
exceeds four can keep the corrected vector inside the four-unit ball only by
strictly negative interference with the original vector. -/
theorem four_unit_connection_forces_strict_negative_interference
    (transported connection : K)
    (hconnection : 4 < ‖connection‖ ^ 2)
    (htotal : ‖transported + connection‖ ^ 2 ≤ 4) :
    2 * re (inner ℂ transported connection) <
      -(‖transported‖ ^ 2) := by
  have hsum := norm_add_sq (𝕜 := ℂ) transported connection
  have hsum' :
      ‖transported + connection‖ ^ 2 =
        ‖transported‖ ^ 2 +
          2 * re (inner ℂ transported connection) +
            ‖connection‖ ^ 2 := by
    simpa using hsum
  linarith

/-- At a strict-right Xi zero, every four-unit source lift carrying the adapted
Ward column has quantitatively forced destructive interference. -/
theorem adaptedWardConnection_forces_strict_negative_interference
    (q : XiRightUpperZeroCopy) (father transported connection : K)
    (hfather :
      ‖father‖ ^ 2 ≤
        (2 * (xiRightCenteredZero q.1).re)⁻¹)
    (hcolumn :
      inner ℂ father connection =
        continuedXiAntiCausalWardResponse
          ((starRingEnd ℂ) (xiRightCenteredZero q.1)))
    (htotal : ‖transported + connection‖ ^ 2 ≤ 4) :
    2 * re (inner ℂ transported connection) <
      -(‖transported‖ ^ 2) := by
  exact four_unit_connection_forces_strict_negative_interference
    transported connection
    (norm_connection_sq_gt_four_of_adaptedWardColumn
      q father connection hfather hcolumn)
    htotal

/-- **Connection-escape closure for the doubled Möbius geometry.**

If the directly transported detail remains father-orthogonal, adding an
arbitrary connection cannot simultaneously create the adapted Ward column and
stay inside the four-unit ball.  No orthogonality between the transported and
connection terms is assumed: destructive interference between them does not
evade the obstruction. -/
theorem
    not_exists_fourUnit_adaptedWardConnection_of_father_orthogonal_transport
    (q : XiRightUpperZeroCopy) :
    ¬ ∃ father transported connection : K,
      ‖father‖ ^ 2 ≤
          (2 * (xiRightCenteredZero q.1).re)⁻¹ ∧
        inner ℂ father transported = 0 ∧
        inner ℂ father connection =
          continuedXiAntiCausalWardResponse
            ((starRingEnd ℂ) (xiRightCenteredZero q.1)) ∧
        ‖transported + connection‖ ^ 2 ≤ 4 := by
  rintro ⟨father, transported, connection,
    hfather, horth, hcolumn, htotal⟩
  have htotalColumn :
      inner ℂ father (transported + connection) =
        continuedXiAntiCausalWardResponse
          ((starRingEnd ℂ) (xiRightCenteredZero q.1)) := by
    rw [inner_add_right, horth, hcolumn, zero_add]
  exact (not_lt_of_ge htotal)
    (norm_connection_sq_gt_four_of_adaptedWardColumn
      q father (transported + connection) hfather htotalColumn)

/-- **Singular/cofinal connection-escape closure.**

At an adapted strict-right Xi zero, there is no sequence of Hilbert-space
father/detail pairs whose father diagonal converges to the Hardy diagonal,
whose codiagonal converges to the continued Ward value, and whose detail
diagonal stays bounded by four.  The theorem assumes no bounded transport,
finite rank, direct/connection decomposition, or convergence of either vector:
only the three Gram entries used by the proposed singular Julia lift occur. -/
theorem not_exists_cofinal_fourUnit_adaptedWardLift
    (q : XiRightUpperZeroCopy) :
    ¬ ∃ father detail : ℕ → K,
      Filter.Tendsto
          (fun n => ‖father n‖ ^ 2)
          Filter.atTop
          (nhds ((2 * (xiRightCenteredZero q.1).re)⁻¹)) ∧
        Filter.Tendsto
          (fun n => inner ℂ (father n) (detail n))
          Filter.atTop
          (nhds (continuedXiAntiCausalWardResponse
            ((starRingEnd ℂ) (xiRightCenteredZero q.1)))) ∧
        (∀ n, ‖detail n‖ ^ 2 ≤ 4) := by
  rintro ⟨father, detail, hfather, hcolumn, hdetail⟩
  let a := (xiRightCenteredZero q.1).re
  let r :=
    continuedXiAntiCausalWardResponse
      ((starRingEnd ℂ) (xiRightCenteredZero q.1))
  have hpoint (n : ℕ) :
      ‖inner ℂ (father n) (detail n)‖ ^ 2 -
          4 * ‖father n‖ ^ 2 ≤ 0 := by
    have hinner := norm_inner_le_norm (𝕜 := ℂ) (father n) (detail n)
    have hinnerSq :
        ‖inner ℂ (father n) (detail n)‖ ^ 2 ≤
          (‖father n‖ * ‖detail n‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hinner
    have hmul :
        ‖father n‖ ^ 2 * ‖detail n‖ ^ 2 ≤
          ‖father n‖ ^ 2 * 4 :=
      mul_le_mul_of_nonneg_left (hdetail n) (sq_nonneg _)
    have hexpand :
        (‖father n‖ * ‖detail n‖) ^ 2 =
          ‖father n‖ ^ 2 * ‖detail n‖ ^ 2 := by
      ring
    rw [hexpand] at hinnerSq
    nlinarith
  have hleft :
      Filter.Tendsto
        (fun n => ‖inner ℂ (father n) (detail n)‖ ^ 2)
        Filter.atTop (nhds (‖r‖ ^ 2)) := by
    simpa only [r] using hcolumn.norm.pow 2
  have hright :
      Filter.Tendsto
        (fun n => 4 * ‖father n‖ ^ 2)
        Filter.atTop (nhds (4 * (2 * a)⁻¹)) := by
    simpa only [a] using hfather.const_mul 4
  have hlimit :
      ‖r‖ ^ 2 - 4 * (2 * a)⁻¹ ≤ 0 :=
    le_of_tendsto (hleft.sub hright)
      (Filter.Eventually.of_forall hpoint)
  have ha : 0 < a := xiRightCenteredZero_re_pos q.1
  have hr :
      2 * a⁻¹ < ‖r‖ ^ 2 := by
    rw [Complex.sq_norm]
    simpa only [a, r] using
      normSq_continuedXiAntiCausalWardResponse_at_adaptedNode_gt q
  have hfactor : 4 * (2 * a)⁻¹ = 2 * a⁻¹ := by
    field_simp [ha.ne']
    norm_num
  rw [hfactor] at hlimit
  linarith

/-- There is no orthogonal four-unit connection lift of the adapted
continued-Xi Ward column at a strict-right zero. -/
theorem not_exists_orthogonal_fourUnit_adaptedWardConnection
    (q : XiRightUpperZeroCopy) :
    ¬ ∃ father transported connection : K,
      ‖father‖ ^ 2 ≤
          (2 * (xiRightCenteredZero q.1).re)⁻¹ ∧
        inner ℂ father connection =
          continuedXiAntiCausalWardResponse
            ((starRingEnd ℂ) (xiRightCenteredZero q.1)) ∧
        inner ℂ transported connection = 0 ∧
        ‖transported + connection‖ ^ 2 ≤ 4 := by
  rintro ⟨father, transported, connection,
    hfather, hcolumn, horth, htotal⟩
  exact (not_lt_of_ge htotal)
    (norm_orthogonal_connection_augmentedDetail_sq_gt_four
      q father transported connection hfather hcolumn horth)

end

end RHTower
