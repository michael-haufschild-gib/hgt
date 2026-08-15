/-
# Positive-source nonselection for the full Guinand--Weil observer

The full `2N+1` finite source quotient does not become faithful after restricting event weights to
the interior of the positive cone.  When `R>2N+1`, split a nonzero kernel vector into its positive
and negative parts and add the same strictly positive baseline to both.  This produces distinct
strictly positive event-weight vectors with identical full source coordinates and identical whole
CCM event matrices.

It follows that no decoder, even a nonlinear one, can recover every indexed source-weight vector
from the finite CCM matrix.  For injective horizon placement the two weight vectors represent
distinct positive atomic sources.  Thus positivity cannot replace the pre-quotient arithmetic
selection required by CCM-FU.
-/
import GaloisForLFunctions.RHTower.CCMGuinandWeilFullSourceObserver

noncomputable section

open scoped BigOperators

namespace RHTower

open Matrix

/-- Finite event-packet formation is additive under subtraction of source weights. -/
theorem ccmGuinandWeilFiniteEventPacketMatrix_sub {N R : ℕ}
    (left right horizon : Fin R → ℝ) :
    ccmGuinandWeilFiniteEventPacketMatrix (N := N) (left - right) horizon =
      ccmGuinandWeilFiniteEventPacketMatrix (N := N) left horizon -
        ccmGuinandWeilFiniteEventPacketMatrix (N := N) right horizon := by
  ext i j
  simp [ccmGuinandWeilFiniteEventPacketMatrix, sub_smul,
    Finset.sum_sub_distrib]

/-- **Strict-positive whole-matrix ambiguity.** Above full observer dimension there are distinct
strictly positive event-weight vectors with the same complete source coordinates and the same
entire finite CCM matrix. -/
theorem ccmGuinandWeilFiniteSource_exists_distinct_strictlyPositive_same_observation
    {N R : ℕ} (hNR : 2 * N + 1 < R) (horizon : Fin R → ℝ) :
    ∃ left right : Fin R → ℝ,
      left ≠ right ∧
      (∀ i, 0 < left i) ∧
      (∀ i, 0 < right i) ∧
      ccmGuinandWeilFiniteSourceCoordinateObserver (N := N) horizon left =
        ccmGuinandWeilFiniteSourceCoordinateObserver (N := N) horizon right ∧
      ccmGuinandWeilFiniteEventPacketMatrix (N := N) left horizon =
        ccmGuinandWeilFiniteEventPacketMatrix (N := N) right horizon := by
  obtain ⟨weight, hweight, hobserver⟩ :=
    ccmGuinandWeilFiniteSourceCoordinateObserver_exists_nonzero_kernel hNR horizon
  have hpacket :=
    ccmGuinandWeilFiniteSourceCoordinateObserver_zero_implies_packet_zero
      weight horizon hobserver
  let left : Fin R → ℝ := fun i => 1 + (weight i)⁺
  let right : Fin R → ℝ := fun i => 1 + (weight i)⁻
  have hdecomp : left - right = weight := by
    funext i
    simp only [left, right, Pi.sub_apply]
    linarith [posPart_sub_negPart (weight i)]
  have hne : left ≠ right := by
    intro heq
    apply hweight
    rw [← hdecomp, heq, sub_self]
  refine ⟨left, right, hne, ?_, ?_, ?_, ?_⟩
  · intro i
    exact add_pos_of_pos_of_nonneg zero_lt_one (posPart_nonneg (weight i))
  · intro i
    exact add_pos_of_pos_of_nonneg zero_lt_one (negPart_nonneg (weight i))
  · apply sub_eq_zero.mp
    rw [← LinearMap.map_sub, hdecomp, hobserver]
  · have hzero :
        ccmGuinandWeilFiniteEventPacketMatrix (N := N) left horizon -
          ccmGuinandWeilFiniteEventPacketMatrix (N := N) right horizon = 0 := by
      rw [← ccmGuinandWeilFiniteEventPacketMatrix_sub, hdecomp, hpacket]
    exact sub_eq_zero.mp hzero

/-- **No post-matrix source decoder.** Above observer dimension no function from finite CCM
matrices back to indexed event weights can be a left inverse of packet formation.  Linearity or
continuity of the proposed decoder is not assumed. -/
theorem ccmGuinandWeilFiniteEventPacketMatrix_no_source_decoder
    {N R : ℕ} (hNR : 2 * N + 1 < R) (horizon : Fin R → ℝ) :
    ¬ ∃ recover : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ → (Fin R → ℝ),
      Function.LeftInverse recover
        (fun weight =>
          ccmGuinandWeilFiniteEventPacketMatrix (N := N) weight horizon) := by
  obtain ⟨left, right, hne, _hl, _hr, _hobserver, heq⟩ :=
    ccmGuinandWeilFiniteSource_exists_distinct_strictlyPositive_same_observation
      hNR horizon
  rintro ⟨recover, hrecover⟩
  apply hne
  calc
    left = recover
        (ccmGuinandWeilFiniteEventPacketMatrix (N := N) left horizon) :=
      (hrecover left).symm
    _ = recover
        (ccmGuinandWeilFiniteEventPacketMatrix (N := N) right horizon) :=
      congrArg recover heq
    _ = right := hrecover right

end RHTower
