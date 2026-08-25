import GaloisForLFunctions.RHTower.ReciprocalAtomCounterterm

/-!
# Sign rigidity of reciprocal-atom counterterms

An arbitrary counterterm can repair a negative reciprocal-form direction only
by feeding positive energy directly into that direction.  This module makes
that statement exact on the conjugation-compatible atom isolators that already
characterize RH.

The resulting boundary is sharper than counterterm vanishing.  If a globally
nonnegative repaired form has a counterterm which is merely nonpositive on all
admissible atom isolators, then RH follows.  Conversely, under failure of RH,
every globally nonnegative repair must contain an admissible atom isolator on
which the counterterm is strictly positive and pays at least the full negative
bare-form bill.  The existing atom-fed rank-one counterterm attains exact
cancellation on each such negative direction.

This does not assert that a canonical arithmetic counterterm is nonfeeding.
It isolates that sign/admissibility statement as the exact producer needed to
exclude external anomaly inflow from a source-internal positive completion.
-/

noncomputable section

namespace RHTower

open Complex
open scoped ComplexOrder

/-- A counterterm is nonfeeding on reciprocal atoms when its contribution is
nonpositive on every conjugation-compatible atom isolator. -/
def XiAtomCountertermNonfeeding (C : (ℂ → ℂ) → ℝ) : Prop :=
  ∀ (q : XiZeroCopy) (ζ : ℂ),
    (xiZeroCopyReciprocalSquare q =
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) →
      ζ = (starRingEnd ℂ) ζ) →
    C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) ≤ 0

/-- A globally positive repair by an atom-nonfeeding counterterm forces RH.
Vanishing on isolators is unnecessary; the one-sided sign condition suffices. -/
theorem riemannHypothesis_of_repaired_nonneg_of_counterterm_nonfeeding
    (C : (ℂ → ℂ) → ℝ)
    (hC : XiAtomCountertermNonfeeding C)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm C f) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_forall_xiAtomIsolator_nonneg.mpr ?_
  intro q ζ hζ
  have hrepair := hpos
    (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)
  rw [xiRepairedForm] at hrepair
  calc
    0 ≤ (xiQZero
          (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re +
        C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) := hrepair
    _ ≤ (xiQZero
          (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re + 0 :=
      by linarith [hC q ζ hζ]
    _ = (xiQZero
          (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re := add_zero _

/-- Quantitative local bill: a positive repair must compensate every negative
atom-isolator direction by at least the magnitude of its bare-form deficit. -/
theorem counterterm_local_bill_of_negative_atomIsolator
    (C : (ℂ → ℂ) → ℝ)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm C f)
    {q : XiZeroCopy} {ζ : ℂ}
    (hneg : (xiQZero
      (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re < 0) :
    -(xiQZero
        (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re ≤
      C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) ∧
    0 < C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) := by
  have hrepair := hpos
    (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)
  rw [xiRepairedForm] at hrepair
  constructor <;> linarith

/-- Off RH, every globally positive repair necessarily injects strictly
positive counterterm energy into an admissible divisor-isolating mode. -/
theorem exists_positive_counterterm_atomIsolator_of_repaired_nonneg_of_not_riemannHypothesis
    (C : (ℂ → ℂ) → ℝ)
    (hpos : ∀ f : ℂ → ℂ, 0 ≤ xiRepairedForm C f)
    (hnot : ¬ RiemannHypothesis) :
    ∃ (q : XiZeroCopy) (ζ : ℂ),
      (xiZeroCopyReciprocalSquare q =
          (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) →
        ζ = (starRingEnd ℂ) ζ) ∧
      -(xiQZero
          (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re ≤
        C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) ∧
      0 < C (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ) := by
  have hfail : ¬ ∀ (q : XiZeroCopy) (ζ : ℂ),
      (xiZeroCopyReciprocalSquare q =
          (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) →
        ζ = (starRingEnd ℂ) ζ) →
      0 ≤ (xiQZero
        (xiAtomIsolator (xiZeroCopyReciprocalSquare q) ζ)).re := by
    intro h
    exact hnot
      (riemannHypothesis_iff_forall_xiAtomIsolator_nonneg.mpr h)
  push Not at hfail
  obtain ⟨q, ζ, hζ, hneg⟩ := hfail
  obtain ⟨hbill, hfeed⟩ :=
    counterterm_local_bill_of_negative_atomIsolator C hpos hneg
  exact ⟨q, ζ, hζ, hbill, hfeed⟩

/-- Sharpness: on a negative atom direction, the canonical rank-one atom-fed
counterterm is strictly positive and cancels the bare form exactly. -/
theorem xiAtomFedCounterterm_positive_inflow_and_exact_cancel_of_negative
    {a ζ : ℂ}
    (hneg : (xiQZero (xiAtomIsolator a ζ)).re < 0) :
    0 < xiAtomFedCounterterm a (xiAtomIsolator a ζ) ∧
      xiRepairedForm (xiAtomFedCounterterm a) (xiAtomIsolator a ζ) = 0 := by
  constructor
  · rw [xiAtomFedCounterterm]
    simp only [xiAtomIsolator, if_pos]
    exact neg_pos.mpr hneg
  · exact xiAtomFedCounterterm_cancels a ζ

end RHTower
