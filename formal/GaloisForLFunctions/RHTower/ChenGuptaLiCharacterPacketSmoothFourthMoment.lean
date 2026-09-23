/-
# Chen--Gupta--Li smooth fourth-moment packet decomposition

This module puts the smooth CGL Fourier multiplier on the exact finite
character-product expansion of the fourth packet moment.  The product
configurations split into the source energy configurations, whose additive
pair-frequency is at most one, and a far part.  The near contribution is
bounded by the literal energy; the far contribution has an arbitrary-order
polynomial tail, with the finite `R^(4 : ℕ)` configuration count made explicit.

No RH, GRH, smoothness, energy, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketSmoothKernel

open Complex MeasureTheory Set Filter

noncomputable section

namespace RHTower

/-- Product-compatible pair-pairs in the CGL fourth moment. -/
def cglCharacterPacketProductIndexSet {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) :
    Finset (CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R) :=
  Finset.univ.filter fun pq =>
    cglCharacterPacketPairCharacter w pq.1 = cglCharacterPacketPairCharacter w pq.2

/-- Additive pair-frequency of a CGL fourth-moment configuration. -/
def cglCharacterPacketPairFrequency {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1))
    (pq : CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R) : ℝ :=
  cglCharacterPacketPairOrdinate w pq.1 - cglCharacterPacketPairOrdinate w pq.2

/-- Product-compatible configurations outside the unit additive-energy window. -/
def cglCharacterPacketFarProductIndexSet {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) :
    Finset (CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R) :=
  (cglCharacterPacketProductIndexSet w).filter fun pq =>
    1 < |cglCharacterPacketPairFrequency w pq|

/-- Smooth-multiplier fourth-moment contribution over all compatible pair-pairs. -/
noncomputable def cglCharacterPacketSmoothFourthMomentContribution {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (X : NNReal) : ℂ :=
  ∑ pq ∈ cglCharacterPacketProductIndexSet w,
    ((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X
      (cglCharacterPacketPairFrequency w pq)

/-- Smooth-multiplier contribution over CGL's additive-multiplicative energy. -/
noncomputable def cglCharacterPacketSmoothNearContribution {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (X : NNReal) : ℂ :=
  ∑ pq ∈ cglCharacterPacketEnergyIndexSet w,
    ((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X
      (cglCharacterPacketPairFrequency w pq)

/-- Smooth-multiplier contribution from the complementary far configurations. -/
noncomputable def cglCharacterPacketSmoothFarContribution {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (X : NNReal) : ℂ :=
  ∑ pq ∈ cglCharacterPacketFarProductIndexSet w,
    ((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X
      (cglCharacterPacketPairFrequency w pq)

/-- Exact near/far decomposition of the smooth CGL fourth-moment packet sum. -/
theorem cglCharacterPacketSmoothFourthMomentContribution_eq_near_add_far {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (X : NNReal) :
    cglCharacterPacketSmoothFourthMomentContribution w X =
      cglCharacterPacketSmoothNearContribution w X +
        cglCharacterPacketSmoothFarContribution w X := by
  let f : (CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R) → ℂ :=
    fun pq => ((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X
      (cglCharacterPacketPairFrequency w pq)
  let P : (CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R) → Prop :=
    fun pq => |cglCharacterPacketPairFrequency w pq| ≤ 1
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := cglCharacterPacketProductIndexSet w) (p := P) f
  have hnear : (cglCharacterPacketProductIndexSet w).filter P =
      cglCharacterPacketEnergyIndexSet w := by
    ext pq
    simp [cglCharacterPacketProductIndexSet, cglCharacterPacketEnergyIndexSet, P,
      cglCharacterPacketPairFrequency]
  have hfar : (cglCharacterPacketProductIndexSet w).filter (fun pq => ¬ P pq) =
      cglCharacterPacketFarProductIndexSet w := by
    ext pq
    simp [cglCharacterPacketFarProductIndexSet, P, not_le]
  change (∑ x ∈ cglCharacterPacketProductIndexSet w, f x) = _
  rw [← hsplit, hnear, hfar]
  rfl

/-- The smooth near contribution is bounded by the literal CGL energy times
the smoothing scale. -/
theorem exists_norm_cglCharacterPacketSmoothNearContribution_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q R : ℕ)
      (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (X : NNReal),
      ‖cglCharacterPacketSmoothNearContribution w X‖ ≤
        ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) * ((X : ℝ) * C) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_cglCharacterPacketSmoothMultiplier_le 0
  refine ⟨C, hC0, fun q R w X => ?_⟩
  unfold cglCharacterPacketSmoothNearContribution cglCharacterPacketEnergy
  calc
    ‖∑ pq ∈ cglCharacterPacketEnergyIndexSet w,
        ((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X
          (cglCharacterPacketPairFrequency w pq)‖
      ≤ ∑ pq ∈ cglCharacterPacketEnergyIndexSet w,
        ‖((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X
          (cglCharacterPacketPairFrequency w pq)‖ := norm_sum_le _ _
    _ ≤ ∑ _pq ∈ cglCharacterPacketEnergyIndexSet w,
        ((q + 1).totient : ℝ) * ((X : ℝ) * C) := by
      apply Finset.sum_le_sum
      intro pq hpq
      rw [norm_mul, norm_natCast]
      have hmult : ‖cglCharacterPacketSmoothMultiplier X
          (cglCharacterPacketPairFrequency w pq)‖ ≤ (X : ℝ) * C := by
        simpa using hC X (cglCharacterPacketPairFrequency w pq)
      exact mul_le_mul_of_nonneg_left hmult (by positivity)
    _ = ((q + 1).totient : ℝ) *
        ((cglCharacterPacketEnergyIndexSet w).card : ℝ) * ((X : ℝ) * C) := by
      simp
      ring

/-- Positive large smoothing scales, encoded as certified data. -/
def CGLCharacterPacketLargeScale := {X : NNReal // (1 : ℝ) ≤ X}

/-- The far CGL configuration set is a subcount of the four row labels. -/
theorem card_cglCharacterPacketFarProductIndexSet_le_fourthPower {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) :
    (cglCharacterPacketFarProductIndexSet w).card ≤ R ^ 4 := by
  calc
    (cglCharacterPacketFarProductIndexSet w).card ≤
        (cglCharacterPacketProductIndexSet w).card := Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset (CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R)).card :=
      Finset.card_filter_le _ _
    _ = R ^ 4 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Finset.card_univ]
      ring

set_option maxHeartbeats 1000000 in
/-- At every prescribed decay order, the CGL far contribution has the
corresponding closed polynomial bound. -/
theorem exists_norm_cglCharacterPacketSmoothFarContribution_le (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q R : ℕ)
      (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (X : CGLCharacterPacketLargeScale),
      ‖cglCharacterPacketSmoothFarContribution w X.1‖ ≤
        ((q + 1).totient : ℝ) * (R ^ 4 : ℝ) *
          ((X.1 : ℝ) * C / (1 + (X.1 : ℝ)) ^ k) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_cglCharacterPacketSmoothMultiplier_le k
  refine ⟨C, hC0, fun q R w X => ?_⟩
  have hpoint : ∀ pq ∈ cglCharacterPacketFarProductIndexSet w,
      ‖cglCharacterPacketSmoothMultiplier X.1 (cglCharacterPacketPairFrequency w pq)‖ ≤
        (X.1 : ℝ) * C / (1 + (X.1 : ℝ)) ^ k := by
    intro pq hpq
    have hpqfar : 1 < |cglCharacterPacketPairFrequency w pq| :=
      (Finset.mem_filter.mp hpq).2
    have hraw := hC X.1 (cglCharacterPacketPairFrequency w pq)
    have hscale0 : (0 : ℝ) ≤ (X.1 : ℝ) := X.1.2
    have hfreq : (X.1 : ℝ) ≤ (X.1 : ℝ) * |cglCharacterPacketPairFrequency w pq| := by
      have := mul_le_mul_of_nonneg_left (le_of_lt hpqfar) hscale0
      nlinarith
    have hden : (1 + (X.1 : ℝ)) ^ k ≤
        (1 + |(X.1 : ℝ) * cglCharacterPacketPairFrequency w pq|) ^ k := by
      rw [abs_mul, abs_of_nonneg hscale0]
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    exact hraw.trans (div_le_div_of_nonneg_left (mul_nonneg hscale0 hC0)
      (by positivity) hden)
  have hcard : ((cglCharacterPacketFarProductIndexSet w).card : ℝ) ≤ R ^ 4 := by
    exact_mod_cast card_cglCharacterPacketFarProductIndexSet_le_fourthPower w
  unfold cglCharacterPacketSmoothFarContribution
  calc
    ‖∑ pq ∈ cglCharacterPacketFarProductIndexSet w,
        ((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X.1
          (cglCharacterPacketPairFrequency w pq)‖
      ≤ ∑ pq ∈ cglCharacterPacketFarProductIndexSet w,
        ‖((q + 1).totient : ℂ) * cglCharacterPacketSmoothMultiplier X.1
          (cglCharacterPacketPairFrequency w pq)‖ := norm_sum_le _ _
    _ ≤ ∑ _pq ∈ cglCharacterPacketFarProductIndexSet w,
        ((q + 1).totient : ℝ) * ((X.1 : ℝ) * C / (1 + (X.1 : ℝ)) ^ k) := by
      apply Finset.sum_le_sum
      intro pq hpq
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hpoint pq hpq) (by positivity)
    _ = ((q + 1).totient : ℝ) *
        ((cglCharacterPacketFarProductIndexSet w).card : ℝ) *
          ((X.1 : ℝ) * C / (1 + (X.1 : ℝ)) ^ k) := by
      simp
      ring
    _ ≤ ((q + 1).totient : ℝ) * (R ^ 4 : ℝ) *
          ((X.1 : ℝ) * C / (1 + (X.1 : ℝ)) ^ k) := by
      gcongr

end RHTower
