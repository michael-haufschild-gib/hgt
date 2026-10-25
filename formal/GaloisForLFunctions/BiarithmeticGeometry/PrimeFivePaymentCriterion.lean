import GaloisForLFunctions.BiarithmeticGeometry.WeightedDigitPronicEnergy
import GaloisForLFunctions.BiarithmeticGeometry.DigitCofactorConvolution
import GaloisForLFunctions.BiarithmeticGeometry.FiveTowerKernelLift
import GaloisForLFunctions.BiarithmeticGeometry.CofactorPaymentCriterion
import GaloisForLFunctions.BiarithmeticGeometry.GeometricTowerDigitReceiver

/-!
# The exact prime-five payment criterion

The actual geometric receiver is a digit row. Every prime-five kernel acts by
causal convolution on its digit coefficients. The exact digit-energy domain
and paid mean correction identify payment with weighted square summability of
the kernel's partial pole sums.
-/

noncomputable section
open Finset RHTower
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem digitEnergy_succ_eq_sq_norm (x : ℕ → ℝ) (T : ℕ) :
    fiveDigitPronicEnergyTo x (T + 1) = pronicNorm (fiveWeightedDigitRow x) T ^ 2 := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity),
    fiveDigitPronicEnergyTo, Ico_add_one_right_eq_Icc]

/-- The digit-energy criterion in the receiver's finite pronic norm. -/
theorem bounded_fiveWeightedDigitRow_pronicNorm_iff (x : ℕ → ℝ) :
    (∃ C : ℝ, ∀ T : ℕ, pronicNorm (fiveWeightedDigitRow x) T ≤ C) ↔
      Summable (fun l : ℕ => x l ^ 2 / (5 : ℝ) ^ l) := by
  rw [← bounded_fiveDigitPronicEnergy_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C ^ 2, fun N => ?_⟩
    cases N with
    | zero => simpa only [fiveDigitPronicEnergyTo, Ico_eq_empty (by omega : ¬(1 : ℕ) < 0),
        sum_empty] using sq_nonneg C
    | succ T =>
      rw [digitEnergy_succ_eq_sq_norm]
      exact pow_le_pow_left₀ (pronicNorm_nonneg _ T) (hC T) 2
  · rintro ⟨B, hB⟩
    refine ⟨Real.sqrt B, fun T => ?_⟩
    have h := hB (T + 1)
    rw [fiveDigitPronicEnergyTo, Ico_add_one_right_eq_Icc] at h
    exact Real.sqrt_le_sqrt h

/-- The actual cofactor packet has exactly the convolved digit coefficients. -/
theorem cofactorPrefixAction_fiveTowerKernelLift (a : ℝ) (ha : |a| < 5)
    (f : ℕ → ℝ) (n : ℕ) :
    cofactorPrefixAction (localFactorInverse 5 a) (fiveTowerKernelLift f) n =
      -(a / (5 - a)) *
        fiveWeightedDigitRow (fun l => finiteGeometricConvolution a f l) n := by
  unfold cofactorPrefixAction
  simp_rw [fiveTower_actualPrefix_eq_digitRow a ha]
  calc
    _ = -(a / (5 - a)) *
        ∑ j ∈ Icc 1 n, fiveTowerKernelLift f j * fiveDigitRow a (n / j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [fiveTowerKernelLift_cofactor_sum f (fiveDigitRow a) (fiveDigitRow_zero a),
        ← fiveWeightedDigitRow_convolution]

/-- Every critical prime-five kernel repairs exactly when its weighted partial pole sums lie in `ell2`. -/
theorem receiverBounded_fiveTowerKernelLift_iff (a : ℝ) (ha0 : a ≠ 0) (ha : |a| < 5)
    (f : ℕ → ℝ) (hf : Summable fun r : ℕ => |f r| / Real.sqrt 5 ^ r) :
    ReceiverBounded (dirichletConv (fiveTowerKernelLift f) (localFactorInverse 5 a)) ↔
      Summable (fun l : ℕ => (a ^ 2 / 5) ^ l *
        (∑ r ∈ range (l + 1), f r / a ^ r) ^ 2) := by
  have ha5 : a < 5 := (le_abs_self a).trans_lt ha
  have hk := (criticalWiener_fiveTowerKernelLift_iff f).mpr hf
  have hc := summable_abs_fiveTower_div a ha
  have hq : 0 < |-(a / (5 - a))| :=
    abs_pos.mpr (neg_ne_zero.mpr (div_ne_zero ha0 (sub_pos.mpr ha5).ne'))
  have hpacket : cofactorPrefixAction (localFactorInverse 5 a) (fiveTowerKernelLift f) =
      fun n => -(a / (5 - a)) *
        fiveWeightedDigitRow (fun l => finiteGeometricConvolution a f l) n :=
    funext (cofactorPrefixAction_fiveTowerKernelLift a ha f)
  calc
    _ ↔ ∃ C : ℝ, ∀ T : ℕ,
        pronicNorm (cofactorPrefixAction (localFactorInverse 5 a) (fiveTowerKernelLift f)) T ≤ C :=
      receiverBounded_dirichletConv_iff_cofactorNorm _ _ hc hk
    _ ↔ ∃ C : ℝ, ∀ T : ℕ,
        pronicNorm (fiveWeightedDigitRow (fun l => finiteGeometricConvolution a f l)) T ≤ C := by
      simp only [hpacket, pronicNorm_smul]
      constructor
      · rintro ⟨C, hC⟩
        refine ⟨C / |-(a / (5 - a))|, fun T => (le_div_iff₀ hq).mpr ?_⟩
        simpa only [mul_comm] using hC T
      · rintro ⟨C, hC⟩
        exact ⟨|-(a / (5 - a))| * C,
          fun T => mul_le_mul_of_nonneg_left (hC T) hq.le⟩
    _ ↔ Summable (fun l : ℕ => finiteGeometricConvolution a f l ^ 2 / (5 : ℝ) ^ l) :=
      bounded_fiveWeightedDigitRow_pronicNorm_iff _
    _ ↔ _ := by
      have he : (fun l : ℕ => finiteGeometricConvolution a f l ^ 2 / (5 : ℝ) ^ l) =
          fun l : ℕ => (a ^ 2 / 5) ^ l * (∑ r ∈ range (l + 1), f r / a ^ r) ^ 2 := by
        funext l
        rw [finiteGeometricConvolution_eq_partialPoleSum a ha0 f l,
          mul_pow, div_pow, ← pow_mul, Nat.mul_comm l 2, pow_mul]
        ring
      rw [he]

/-- Normalize a coefficient sequence so its `ell1` mass is the critical Wiener mass. -/
def fiveCriticalKernelLift (g : ℕ → ℝ) : ℕ → ℝ :=
  fiveTowerKernelLift (fun r => Real.sqrt 5 ^ r * g r)

theorem criticalWiener_fiveCriticalKernelLift_iff (g : ℕ → ℝ) :
    CriticalWiener (fiveCriticalKernelLift g) ↔ Summable (fun r => |g r|) := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [fiveCriticalKernelLift, criticalWiener_fiveTowerKernelLift_iff]
  have he (r : ℕ) : |Real.sqrt 5 ^ r * g r| / Real.sqrt 5 ^ r = |g r| := by
    rw [abs_mul, abs_of_pos (pow_pos hs r)]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hs.ne')
  simp only [he]

/-- At critical contact, actual arithmetic payment is exactly square summability of coefficient partial sums. -/
theorem receiverBounded_critical_fiveTower_iff_partialSums (g : ℕ → ℝ)
    (hg : Summable fun r => |g r|) :
    ReceiverBounded (dirichletConv (fiveCriticalKernelLift g) (localFactorInverse 5 (Real.sqrt 5))) ↔
      Summable (fun l : ℕ => (∑ r ∈ range (l + 1), g r) ^ 2) := by
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs5 : Real.sqrt 5 < 5 := by nlinarith only [hs2, hs]
  have hf := (criticalWiener_fiveCriticalKernelLift_iff g).mpr hg
  rw [fiveCriticalKernelLift, criticalWiener_fiveTowerKernelLift_iff] at hf
  rw [fiveCriticalKernelLift, receiverBounded_fiveTowerKernelLift_iff _ hs.ne'
    (by rwa [abs_of_pos hs]) _ hf]
  have he (r : ℕ) : (Real.sqrt 5 ^ r * g r) / Real.sqrt 5 ^ r = g r :=
    mul_div_cancel_left₀ _ (pow_ne_zero _ hs.ne')
  simp only [hs2, div_self (by norm_num : (5 : ℝ) ≠ 0), one_pow, one_mul, he]

end GaloisForLFunctions.BiarithmeticGeometry
