import GaloisForLFunctions.BiarithmeticGeometry.GeometricTowerDigitReceiver
import GaloisForLFunctions.BiarithmeticGeometry.PaidSourcePerturbations
import GaloisForLFunctions.BiarithmeticGeometry.GoldenArithmeticSource

/-!
# The exact admission threshold for a positive geometric tower

The critical geometric tower already has unbounded receiver energy. Exact digit
monotonicity transports this obstruction to every larger positive tower, while the
critical Wiener bound pays every smaller tower.
-/

noncomputable section
open Finset GaloisForLFunctions
open ArithmeticOrientationTheory TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Every digit is nonnegative, so increasing a nonnegative evaluation parameter increases the row. -/
theorem fiveDigitRow_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    fiveDigitRow a n ≤ fiveDigitRow b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; rw [fiveDigitRow_zero, fiveDigitRow_zero]
    · rw [fiveDigitRow_rec a n, fiveDigitRow_rec b n]
      exact add_le_add le_rfl (mul_le_mul hab (ih (n / 5) (by omega))
        (fiveDigitRow_nonneg a ha _) (ha.trans hab))

/-- Exact receiver energies increase with a nonnegative tower parameter below five. -/
theorem fiveTower_energy_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 5)
    (T : ℕ) :
    weightPronicEnergy (localFactorInverse 5 a) (∑' n : ℕ, localFactorInverse 5 a n / n) T ≤
      weightPronicEnergy (localFactorInverse 5 b) (∑' n : ℕ, localFactorInverse 5 b n / n) T := by
  have ha5 : a < 5 := hab.trans_lt hb
  have hb0 : 0 ≤ b := ha.trans hab
  have hfactor : a / (5 - a) ≤ b / (5 - b) := by
    apply (div_le_div_iff₀ (by linarith only [ha5]) (by linarith only [hb])).mpr
    nlinarith only [hab]
  unfold weightPronicEnergy
  refine sum_le_sum fun n _ => div_le_div_of_nonneg_right ?_ (by positivity)
  rw [fiveTower_actualPrefix_eq_digitRow a (by rwa [abs_of_nonneg ha]),
    fiveTower_actualPrefix_eq_digitRow b (by rwa [abs_of_nonneg hb0])]
  have hmul : (a / (5 - a)) * fiveDigitRow a n ≤
      (b / (5 - b)) * fiveDigitRow b n :=
    mul_le_mul hfactor (fiveDigitRow_mono ha hab n) (fiveDigitRow_nonneg a ha n)
      (div_nonneg hb0 (by linarith only [hb]))
  have hnon : 0 ≤ (a / (5 - a)) * fiveDigitRow a n :=
    mul_nonneg (div_nonneg ha (by linarith only [ha5])) (fiveDigitRow_nonneg a ha n)
  simpa only [neg_mul, neg_sq] using pow_le_pow_left₀ hnon hmul 2

private theorem critical_fiveTower_eq :
    localFactorInverse 5 (Real.sqrt 5) = criticalGeometricWeight 5 := by
  funext n
  by_cases hn : ∃ r, n = 5 ^ r
  · obtain ⟨r, rfl⟩ := hn
    rw [localFactorInverse_pow (by omega : 1 < 5),
      criticalGeometricWeight_pow (by norm_num : Nat.Prime 5)]
    norm_num only [Nat.cast_ofNat]
  · have hnot : ∀ r, n ≠ 5 ^ r := fun r hr => hn ⟨r, hr⟩
    rw [localFactorInverse_eq_zero _ hnot, criticalGeometricWeight_eq_zero hnot]

/-- The critical endpoint is genuinely unpaid, by the source's existing sharpness theorem. -/
theorem not_receiverBounded_critical_fiveTower :
    ¬ ReceiverBounded (localFactorInverse 5 (Real.sqrt 5)) := by
  rw [critical_fiveTower_eq, ReceiverBounded,
    (hasSum_criticalGeometricWeight_div (by norm_num : Nat.Prime 5)).tsum_eq]
  exact (criticalLine_sharpness (by norm_num : Nat.Prime 5)).2

/-- The positive geometric tower is paid exactly below the square-root threshold. -/
theorem receiverBounded_fiveTower_iff (a : ℝ) (ha : 0 ≤ a) (ha5 : a < 5) :
    ReceiverBounded (localFactorInverse 5 a) ↔ a < Real.sqrt 5 := by
  constructor
  · intro h
    by_contra hs
    have hsa : Real.sqrt 5 ≤ a := le_of_not_gt hs
    apply not_receiverBounded_critical_fiveTower
    obtain ⟨B, hB⟩ := h
    exact ⟨B, fun T => (fiveTower_energy_mono (Real.sqrt_nonneg _) hsa ha5 T).trans (hB T)⟩
  · intro h
    exact receiverBounded_of_criticalWiener _
      ((criticalWiener_localFactorInverse_iff (by norm_num : Nat.Prime 5) a).mpr
        (by rwa [abs_of_nonneg ha]))

/-- The actual golden source has precisely the primary tower's admission threshold. -/
theorem receiverBounded_goldenArithmeticSource_iff (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ReceiverBounded (goldenArithmeticSource t) ↔ goldenPrimaryRoot * t < Real.sqrt 5 := by
  have ha0 : 0 ≤ goldenPrimaryRoot * t := mul_nonneg golden_root_bounds.1.le ht0
  have ha5 : goldenPrimaryRoot * t < 5 :=
    (mul_le_of_le_one_right golden_root_bounds.1.le ht1).trans_lt golden_root_bounds.2.1
  have haabs : |goldenPrimaryRoot * t| < 5 := by rwa [abs_of_nonneg ha0]
  calc
    _ ↔ (1 : WienerAlgebraAt (1 / 2)) ∈ paidIdeal (goldenArithmeticSource t)
        (summable_abs_goldenArithmeticSource_div t ht0 ht1) :=
      (one_mem_paidIdeal_iff _ _).symm
    _ ↔ (1 : WienerAlgebraAt (1 / 2)) ∈ paidIdeal (localFactorInverse 5 (goldenPrimaryRoot * t))
        (summable_abs_fiveTower_div _ haabs) := by rw [paidIdeal_goldenArithmeticSource t ht0 ht1]
    _ ↔ ReceiverBounded (localFactorInverse 5 (goldenPrimaryRoot * t)) := one_mem_paidIdeal_iff _ _
    _ ↔ _ := receiverBounded_fiveTower_iff _ ha0 ha5

end GaloisForLFunctions.BiarithmeticGeometry
