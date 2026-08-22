import GaloisForLFunctions.HTGeometry.FinitePhaseTrigProduct
import GaloisForLFunctions.HTGeometry.PhaseSeedCollisionMoments

/-!
# First two moments of the collision of a cubic eighth-root phase seed

The pairing of a cubic phase seed with a family vector is a character combination in the eighth-root
model, exactly as the continuous phase pairing is one on the torus.  The quartic collision and its
square are therefore character combinations whose frequencies are supported on at most eight Boolean
points with entries of absolute value at most four, so their means agree with the continuous ones.
The continuous mean and variance bounds transfer verbatim.
-/

open Finset Matrix MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {J : Type*} [Fintype J] [DecidableEq J]

section Amplitude

variable {m : ℕ}

theorem norm_charFinite (n : (ι → Bool) → ℤ) (c : MonLe ι m → ZMod 8) :
    ‖charFinite n c‖ = 1 := by
  rw [charFinite, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem charFinite_neg_index (n : (ι → Bool) → ℤ) (c : MonLe ι m → ZMod 8) :
    charFinite (-n) c = (starRingEnd ℂ) (charFinite n c) := by
  have hnorm := norm_charFinite n c
  rw [← Complex.inv_eq_conj hnorm]
  have hz : charFinite n c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have h1 : charFinite (-n) c * charFinite n c = 1 := by
    rw [← charFinite_add_index, neg_add_cancel, charFinite_zero]
  field_simp at h1 ⊢
  exact h1

/-- The pairing of the eighth-root phase seed with one family vector. -/
def finPhaseAmp (e : J → (ι → Bool) → ℂ) (j : J) (c : MonLe ι m → ZMod 8) : ℂ :=
  trigFinite (Finset.univ : Finset (ι → Bool)) (fun a => -(Pi.single a 1)) (e j) c

/-- The conjugate pairing, again a character combination. -/
def finPhaseAmpConj (e : J → (ι → Bool) → ℂ) (j : J) (c : MonLe ι m → ZMod 8) : ℂ :=
  trigFinite (Finset.univ : Finset (ι → Bool)) (fun a => Pi.single a 1)
    (fun a => (starRingEnd ℂ) (e j a)) c

theorem finPhaseAmpConj_eq (e : J → (ι → Bool) → ℂ) (j : J) (c : MonLe ι m → ZMod 8) :
    finPhaseAmpConj e j c = (starRingEnd ℂ) (finPhaseAmp e j c) := by
  rw [finPhaseAmpConj, finPhaseAmp, trigFinite, trigFinite, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, charFinite_neg_index, Complex.conj_conj]

theorem sq_finPhaseAmp (e : J → (ι → Bool) → ℂ) (j : J) (c : MonLe ι m → ZMod 8) :
    (finPhaseAmp e j c) ^ 2 =
      ∑ p : (ι → Bool) × (ι → Bool), (e j p.1 * e j p.2) *
        charFinite (-(Pi.single p.1 1) + -(Pi.single p.2 1)) c := by
  rw [sq, finPhaseAmp, trigFinite, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [charFinite_add_index]
  ring

theorem sq_finPhaseAmpConj (e : J → (ι → Bool) → ℂ) (j : J) (c : MonLe ι m → ZMod 8) :
    (finPhaseAmpConj e j c) ^ 2 =
      ∑ p : (ι → Bool) × (ι → Bool),
        ((starRingEnd ℂ) (e j p.1) * (starRingEnd ℂ) (e j p.2)) *
          charFinite (Pi.single p.1 1 + Pi.single p.2 1) c := by
  rw [sq, finPhaseAmpConj, trigFinite, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [charFinite_add_index]
  ring

/-- The unnormalized collision of the eighth-root seed with a family. -/
def finQuarticSum (e : J → (ι → Bool) → ℂ) (c : MonLe ι m → ZMod 8) : ℂ :=
  ∑ j, (finPhaseAmp e j c * finPhaseAmpConj e j c) ^ 2

/-- The real collision of the eighth-root seed with a family. -/
def finCollision (e : J → (ι → Bool) → ℂ) (c : MonLe ι m → ZMod 8) : ℝ :=
  ∑ j, ‖finPhaseAmp e j c‖ ^ 4

theorem finQuarticSum_eq_ofReal (e : J → (ι → Bool) → ℂ) (c : MonLe ι m → ZMod 8) :
    finQuarticSum e c = ((finCollision e c : ℝ) : ℂ) := by
  rw [finQuarticSum, finCollision, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finPhaseAmpConj_eq, Complex.mul_conj]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.sq_norm]
  push_cast
  ring

theorem finCollision_nonneg (e : J → (ι → Bool) → ℂ) (c : MonLe ι m → ZMod 8) :
    0 ≤ finCollision e c :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **The eighth-root collision is a character combination** with the same frequencies and
coefficients as the continuous one. -/
theorem finQuarticSum_eq_trigFinite (e : J → (ι → Bool) → ℂ) :
    finQuarticSum (m := m) e =
      trigFinite (Finset.univ :
          Finset (J × (((ι → Bool) × (ι → Bool)) × ((ι → Bool) × (ι → Bool)))))
        (fun q => quarticFreq q.2) (quarticCoeff e) := by
  classical
  funext c
  rw [finQuarticSum, trigFinite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hR : (∑ p : ((ι → Bool) × (ι → Bool)) × ((ι → Bool) × (ι → Bool)),
      quarticCoeff e (j, p) * charFinite (quarticFreq p) c) =
      ∑ p : (ι → Bool) × (ι → Bool), ∑ q : (ι → Bool) × (ι → Bool),
        quarticCoeff e (j, (p, q)) * charFinite (quarticFreq (p, q)) c :=
    Fintype.sum_prod_type _
  rw [hR, mul_pow, sq_finPhaseAmp, sq_finPhaseAmpConj, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfreq : charFinite (quarticFreq (p, q)) c =
      charFinite (-(Pi.single p.1 1)) c * charFinite (-(Pi.single p.2 1)) c *
        charFinite (Pi.single q.1 1 + Pi.single q.2 1) c := by
    rw [quarticFreq, charFinite_add_index, charFinite_add_index]
  rw [hfreq, quarticCoeff,
    charFinite_add_index (-(Pi.single p.1 1)) (-(Pi.single p.2 1)) c]
  ring

end Amplitude

section Transfer

/-- The number of cubic phase seeds. -/
def cubicSeedCount (ι : Type*) [Fintype ι] [DecidableEq ι] : ℕ :=
  Fintype.card (MonLe ι 3 → ZMod 8)

theorem cubicSeedCount_ne_zero : (cubicSeedCount ι : ℂ) ≠ 0 := by
  rw [cubicSeedCount]
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (MonLe ι 3 → ZMod 8) ≠ 0)

theorem cubicSeedCount_pos : 0 < (cubicSeedCount ι : ℝ) := by
  rw [cubicSeedCount]
  exact_mod_cast Fintype.card_pos

/-- **The mean collision transfers.** -/
theorem average_finQuarticSum (e : J → (ι → Bool) → ℂ) :
    ((cubicSeedCount ι : ℂ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, finQuarticSum e c =
      ∫ x in torusBox (ι → Bool), quarticSum e x := by
  classical
  rw [finQuarticSum_eq_trigFinite, quarticSum_eq_trigLift, cubicSeedCount]
  refine average_trigFinite_eq_integral_box_trigLift _ _ _ (fun q _ => ?_) (fun q _ b hb => ?_)
  · exact lt_of_le_of_lt (card_support_quarticFreq_le q.2) (by norm_num)
  · refine eq_zero_of_abs_le_seven_of_cast_eq_zero ?_ hb
    exact le_trans (abs_quarticFreq_le q.2 b) (by norm_num)

/-- **The second moment of the collision transfers.** -/
theorem average_finQuarticSum_sq (e : J → (ι → Bool) → ℂ) :
    ((cubicSeedCount ι : ℂ))⁻¹ * ∑ c : MonLe ι 3 → ZMod 8, (finQuarticSum e c) ^ 2 =
      ∫ x in torusBox (ι → Bool), (quarticSum e x) ^ 2 := by
  classical
  have hfin : ∀ c : MonLe ι 3 → ZMod 8, (finQuarticSum e c) ^ 2 =
      trigFinite (Finset.univ ×ˢ Finset.univ)
        (fun qq => quarticFreq qq.1.2 + quarticFreq qq.2.2)
        (fun qq => quarticCoeff e qq.1 * quarticCoeff e qq.2) c := by
    intro c
    rw [sq]
    have h := finQuarticSum_eq_trigFinite (m := 3) e
    rw [h]
    exact trigFinite_mul _ _ _ _ _ _ c
  have hcont : ∀ x : (ι → Bool) → ℝ, (quarticSum e x) ^ 2 =
      trigLift (Finset.univ ×ˢ Finset.univ)
        (fun qq => quarticFreq qq.1.2 + quarticFreq qq.2.2)
        (fun qq => quarticCoeff e qq.1 * quarticCoeff e qq.2) x := by
    intro x
    rw [sq, quarticSum_eq_trigLift]
    exact finiteTrigLift_mul _ _ _ _ _ _ x
  simp only [hfin]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_torusBox fun x _ => hcont x]
  refine average_trigFinite_eq_integral_box_trigLift _ _ _ (fun qq _ => ?_) (fun qq _ b hb => ?_)
  · exact lt_of_le_of_lt (card_support_add_quarticFreq_le qq.1.2 qq.2.2) (by norm_num)
  · refine eq_zero_of_abs_le_seven_of_cast_eq_zero ?_ hb
    exact le_trans (abs_add_quarticFreq_le qq.1.2 qq.2.2 b) (by norm_num)

end Transfer

end GaloisForLFunctions.HTGeometry
