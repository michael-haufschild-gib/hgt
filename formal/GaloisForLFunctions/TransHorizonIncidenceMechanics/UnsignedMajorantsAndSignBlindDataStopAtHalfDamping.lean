import GaloisForLFunctions.TransHorizonIncidenceMechanics.HalfDampingIsTheExactThresholdOfTheParityPair

/-!
# Unsigned majorants and sign-blind data stop at half damping

Three statements about the damped Möbius receiver on the class `𝒞(K, ε) = {|c(d)| ≤ K d^{−ε}}` are
usually kept apart: the unsigned (absolute-convergence) majorant of the receiver, the decidability of
receiver boundedness from the Ramanujan amplitudes, and its decidability from the coefficient
magnitudes `|c(d)|`, the data an `ℓ²`-class bound can see. They are one threshold.

* `uniformReceiverBound_iff_half_lt`: one constant bounds the receiver on all of `𝒞(K, ε)` iff
  `ε > 1/2`. Above half damping the absolute majorant `|A_c(n)| ≤ K C_ε n^{1−ε}` converges; at and
  below it the positive twin of the character modulo four diverges.
* `uniformReceiverBound_iff_amplitudeInvariant`: the unsigned majorant exists iff receiver
  boundedness is a function of the amplitudes `|W_c(e)|`.
* `receiverBounded_magnitudeInvariant_iff`: receiver boundedness is a function of the magnitudes
  `|c(d)|` iff `ε > 1/2`. Below half damping the weights `K χ₄(d) d^{−ε}` and `K 1_{odd}(d) d^{−ε}`
  have the same magnitudes and opposite receivers.

So the absolute-convergence boundary, the parity barrier and the blindness of magnitude-only
(`ℓ²`) inputs are the same line `ε = 1/2` in the receiver's own coordinates.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### 1. The unsigned majorant is the amplitude threshold -/

/-- **One constant bounds every receiver on the damped class iff `ε > 1/2`.** -/
theorem uniformReceiverBound_iff_half_lt {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    (∃ E : ℝ, ∀ c : ℕ → ℝ, DampedClass K ε c → ∀ T : ℕ,
      weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) ↔ 1 / 2 < ε := by
  constructor
  · rintro ⟨E, hE⟩
    exact (receiverBounded_amplitudeInvariant_iff hK hε).mp
      ⟨fun _ => True, fun c hc => iff_true_intro ⟨E, hE c hc⟩⟩
  · exact exists_uniform_weightPronicEnergy_bound

/-- **The unsigned majorant exists iff the receiver is decided by the amplitudes.** -/
theorem uniformReceiverBound_iff_amplitudeInvariant {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    (∃ E : ℝ, ∀ c : ℕ → ℝ, DampedClass K ε c → ∀ T : ℕ,
      weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E) ↔
      ∃ Φ : (ℕ → ℝ) → Prop, ∀ c : ℕ → ℝ, DampedClass K ε c →
        (ReceiverBounded c ↔ Φ (fun e => |weightRamanujanCoeff c e|)) :=
  (uniformReceiverBound_iff_half_lt hK hε).trans (receiverBounded_amplitudeInvariant_iff hK hε).symm

/-! ### 2. Magnitudes are blind below half damping -/

/-- `|χ₄(d)|` is the odd indicator. -/
theorem abs_chiFour_eq_oddIndicator (d : ℕ) : |chiFour d| = oddIndicator d := by
  rw [chiFour_eq]; unfold oddIndicator
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · simp [h]
  · have h0 : d % 2 ≠ 0 := by omega
    rw [if_neg h0, if_pos h]
    split_ifs <;> norm_num

/-- The character weight `K χ₄(d) d^{−ε}` lies in the damped class. -/
theorem dampedClass_mul_chiFour {K ε : ℝ} (hK : 0 < K) :
    DampedClass K ε (fun d => K * dampedSignWeight chiFour ε d) := fun d => by
  have hr : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have h1 : |chiFour d| ≤ 1 := by rw [chiFour_eq]; split_ifs <;> norm_num
  dsimp only
  rw [dampedSignWeight, abs_mul, abs_mul, abs_of_pos hK, abs_of_nonneg hr]
  calc K * (|chiFour d| * (d : ℝ) ^ (-ε)) ≤ K * (1 * (d : ℝ) ^ (-ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hr) hK.le
    _ = K * (d : ℝ) ^ (-ε) := by ring

/-- The odd weight `K 1_{odd}(d) d^{−ε}` lies in the damped class. -/
theorem dampedClass_mul_oddIndicator {K ε : ℝ} (hK : 0 < K) :
    DampedClass K ε (fun d => K * dampedSignWeight oddIndicator ε d) := fun d => by
  have hr : 0 ≤ (d : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  have h1 : oddIndicator d ≤ 1 := by unfold oddIndicator; split_ifs <;> norm_num
  have h0 : 0 ≤ oddIndicator d := by unfold oddIndicator; split_ifs <;> norm_num
  dsimp only
  rw [dampedSignWeight, abs_mul, abs_mul, abs_of_pos hK, abs_of_nonneg hr, abs_of_nonneg h0]
  calc K * (oddIndicator d * (d : ℝ) ^ (-ε)) ≤ K * (1 * (d : ℝ) ^ (-ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hr) hK.le
    _ = K * (d : ℝ) ^ (-ε) := by ring

/-- The character weight and the odd weight have the same magnitudes. -/
theorem abs_mul_chiFour_eq_abs_mul_oddIndicator (K ε : ℝ) :
    (fun d => |K * dampedSignWeight chiFour ε d|) =
      fun d => |K * dampedSignWeight oddIndicator ε d| := by
  funext d
  have h0 : 0 ≤ oddIndicator d := by unfold oddIndicator; split_ifs <;> norm_num
  simp only [dampedSignWeight, abs_mul, abs_chiFour_eq_oddIndicator, abs_of_nonneg h0]

/-- The odd weight has divergent receiver at and below half damping: it is a positive multiple of
the positive twin of the character modulo four. -/
theorem not_receiverBounded_oddIndicator {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight oddIndicator ε) := by
  obtain ⟨-, -, -, -, hdiv⟩ := chiFour_parityPair hε hε2
  have hκ : 0 < chiFourDampedMass ε / oddDampedMass ε :=
    div_pos (chiFourDampedMass_pos hε) (oddDampedMass_pos hε)
  have htwin : oddDampedTwinWeight ε =
      fun d => chiFourDampedMass ε / oddDampedMass ε * dampedSignWeight oddIndicator ε d := rfl
  rw [← receiverBounded_smul_iff hκ.ne', ← htwin]
  rintro ⟨E', hE'⟩
  rw [(hasSum_oddDampedTwinWeight_div hε).tsum_eq] at hE'
  obtain ⟨T, hT⟩ := (hdiv.eventually_gt_atTop E').exists
  exact absurd (hE' T) (not_le.mpr hT)

/-- **Receiver boundedness is a function of the coefficient magnitudes `|c(d)|` iff `ε > 1/2`.**
Below half damping the magnitudes cannot tell the bounded character weight from the divergent odd
weight; above it one constant bounds the whole class. -/
theorem receiverBounded_magnitudeInvariant_iff {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    (∃ Φ : (ℕ → ℝ) → Prop, ∀ c : ℕ → ℝ, DampedClass K ε c →
      (ReceiverBounded c ↔ Φ (fun d => |c d|))) ↔ 1 / 2 < ε := by
  constructor
  · rintro ⟨Φ, hΦ⟩
    by_contra hle
    have hε2 : ε ≤ 1 / 2 := not_lt.mp hle
    obtain ⟨-, -, -, ⟨E, hE⟩, -⟩ := chiFour_parityPair hε hε2
    have hbound : ReceiverBounded (fun d => K * dampedSignWeight chiFour ε d) :=
      (receiverBounded_smul_iff hK.ne' _).mpr ⟨E, hE⟩
    have hunb : ¬ ReceiverBounded (fun d => K * dampedSignWeight oddIndicator ε d) := by
      rw [receiverBounded_smul_iff hK.ne']
      exact not_receiverBounded_oddIndicator hε hε2
    have h1 := hΦ _ (dampedClass_mul_chiFour (ε := ε) hK)
    have h2 := hΦ _ (dampedClass_mul_oddIndicator (ε := ε) hK)
    rw [abs_mul_chiFour_eq_abs_mul_oddIndicator] at h1
    exact hunb (h2.mpr (h1.mp hbound))
  · intro hε2
    obtain ⟨E, hE⟩ := exists_uniform_weightPronicEnergy_bound (K := K) hε2
    exact ⟨fun _ => True, fun c hc => iff_true_intro ⟨E, hE c hc⟩⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
