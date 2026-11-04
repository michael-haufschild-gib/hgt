import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMixedMoments

/-!
# A common normalized cost for complete mixed remainders

An ordinary moment at most `4NV` and a harmonic moment at most
`(log N+1)V` control the complete remainder against every unit neutral
receiver by `C c⁶(log N+1)V` after physical normalization.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory

/-- Two small moment costs control the unnormalized complete mixed remainder. -/
theorem exists_complete_packet_bilinear_moment_cost {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c V W : ℝ),
      1 ≤ N → 1 ≤ c → c / N ≤ 1 / 3 → 0 ≤ V → 0 ≤ W →
      ∀ F G : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
      (∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) →
      (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * V →
      (∑ n ∈ Icc 1 N, G n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * W →
      (∑ n ∈ Icc 1 N, F n ^ 2) ≤ 4 * (N : ℝ) * V →
      (∑ n ∈ Icc 1 N, G n ^ 2) ≤ 4 * (N : ℝ) * W →
      |completePacketPairing φ c N F G - jumpPairing N F G| ≤
        C * c ^ 3 * (Real.log N + 1) * (V + W) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_bilinear_moment_bound hφ hφ0 hsupp hM
  refine ⟨(A + 4 * B) / 2, by positivity, ?_⟩
  intro N c V W hN hc hw hV hW F G hF hG hHF hHG hOF hOG
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [h]
  have hH : (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
      (∑ n ∈ Icc 1 N, G n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * (V + W) :=
    (add_le_add hHF hHG).trans_eq (by ring)
  have hO : (∑ n ∈ Icc 1 N, F n ^ 2) +
      (∑ n ∈ Icc 1 N, G n ^ 2) ≤ 4 * (N : ℝ) * (V + W) :=
    (add_le_add hOF hOG).trans_eq (by ring)
  refine (hbound c N hc hN hw F G hF hG).trans ?_
  calc
    _ ≤ (A * c ^ 2 * ((Real.log N + 1) * (V + W)) +
        (B * c ^ 3 * (Real.log N + 1) / N) * (4 * (N : ℝ) * (V + W))) / 2 :=
      div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_left hH (by positivity))
          (mul_le_mul_of_nonneg_left hO (by positivity))) zero_le_two
    _ ≤ (A * c ^ 3 * ((Real.log N + 1) * (V + W)) +
        (B * c ^ 3 * (Real.log N + 1) / N) * (4 * (N : ℝ) * (V + W))) / 2 :=
      div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc23 hA) (by positivity)) le_rfl) zero_le_two
    _ = _ := by field_simp [hN0.ne']

/-- The same two scalar moments control complete mixed errors of scalar and coprime-fibre packets. -/
theorem exists_complete_packet_normalized_moment_cost {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c V : ℝ),
      1 ≤ N → 1 ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 → 0 ≤ V →
      ∀ F G : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
      (∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) → ‖packetVector G N‖ ≤ 1 →
      (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * V →
      (∑ n ∈ Icc 1 N, F n ^ 2) ≤ 4 * (N : ℝ) * V →
      (completePacketPairing φ c N F G - jumpPairing N F G) ^ 2 / Real.log N ≤
        C * c ^ 6 * (Real.log N + 1) * V := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_mixed_moment_bound hφ hφ0 hsupp hM
  refine ⟨2 * (1 + A + B) * (A + 4 * B), by positivity, ?_⟩
  intro N c V hN hL hc hw hV F G hF hG hunit hH hO
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [h]
  have hc3 : 1 ≤ c ^ 3 := (show 1 ≤ c ^ 2 by nlinarith only [hc]).trans hc23
  have hweight : 1 ≤ c ^ 3 * (Real.log N + 1) := by
    have h := mul_le_mul hc3 (show 1 ≤ Real.log N + 1 by linarith only [hL])
      zero_le_one (by positivity : 0 ≤ c ^ 3)
    simpa only [one_mul] using h
  have hcost : A * c ^ 2 * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
      (B * c ^ 3 * (Real.log N + 1) / N) * ∑ n ∈ Icc 1 N, F n ^ 2 ≤
        (A + 4 * B) * c ^ 3 * (Real.log N + 1) * V := by
    calc
      _ ≤ A * c ^ 2 * ((Real.log N + 1) * V) +
          (B * c ^ 3 * (Real.log N + 1) / N) * (4 * (N : ℝ) * V) :=
        add_le_add (mul_le_mul_of_nonneg_left hH (by positivity))
          (mul_le_mul_of_nonneg_left hO (by positivity))
      _ ≤ A * c ^ 3 * ((Real.log N + 1) * V) +
          (B * c ^ 3 * (Real.log N + 1) / N) * (4 * (N : ℝ) * V) :=
        add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc23 hA) (by positivity)) le_rfl
      _ = _ := by field_simp [hN0.ne']
  have hfactor : 1 + A * c ^ 2 + B * c ^ 3 * (Real.log N + 1) ≤
      (1 + A + B) * c ^ 3 * (Real.log N + 1) := by
    have hAterm : A * c ^ 2 ≤ A * c ^ 3 * (Real.log N + 1) := by
      calc
        _ ≤ A * c ^ 3 := mul_le_mul_of_nonneg_left hc23 hA
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith only [hL])
    nlinarith only [hweight, hAterm]
  have h := (hbound c N hc hN hw F G hF hG hunit).trans
    (mul_le_mul hfactor hcost (by positivity) (by positivity))
  have hratio : (Real.log N + 1) ^ 2 / Real.log N ≤ 2 * (Real.log N + 1) := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith only [hL, sq_nonneg (Real.log N - 1)]
  refine (div_le_div_of_nonneg_right h hL0.le).trans ?_
  calc
    _ = (1 + A + B) * (A + 4 * B) * c ^ 6 * V *
        ((Real.log N + 1) ^ 2 / Real.log N) := by ring
    _ ≤ (1 + A + B) * (A + 4 * B) * c ^ 6 * V * (2 * (Real.log N + 1)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

#print axioms exists_complete_packet_normalized_moment_cost
#print axioms exists_complete_packet_bilinear_moment_cost

end GaloisForLFunctions.ArithmeticCouplingTheory
