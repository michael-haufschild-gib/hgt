import GaloisForLFunctions.BiScaleUncertainty.SieveVisibilityPerturbations

/-! Linear raw-array control under radial scaling of actual sieve weights. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
open ValuationPhase ParityNeighborhood
set_option autoImplicit false

/-- A radial perturbation has uniformly linear coordinate error. -/
theorem radial_coordinate_error (N : ℕ) (b : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) (q : ℕ) :
    |selbergMultiplesCoord N b q-selbergMultiplesCoord N (fun d => (1+t)*b d) q| ≤
      coordinateBudget N b*t := by
  rw [coordinate_scale]
  rw [show selbergMultiplesCoord N b q-(1+t)*selbergMultiplesCoord N b q =
      -t*selbergMultiplesCoord N b q by ring, abs_mul, abs_neg, abs_of_nonneg ht]
  calc
    _ ≤ t*coordinateBudget N b := mul_le_mul_of_nonneg_left (coordinate_le_budget N b q) ht
    _ = _ := mul_comm _ _

/-- Radial perturbations stay in a controlled physical neighborhood. -/
theorem radial_near_base (N : ℕ) (b : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |sieveSeq N (fun d => (1+t)*b d) n-sieveSeq N b n| ≤
      ((∑ q ∈ Icc 1 N, (q.totient : ℝ))*coordinateBudget N b)*t := by
  have hh := sieveSeq_error_le_totient_sum N (fun d => (1+t)*b d) b (coordinateBudget N b*t)
    (fun q _ => by simpa only [abs_sub_comm] using radial_coordinate_error N b t ht q) n
  simpa only [mul_assoc] using hh

/-- Bounded radial scaling changes the complete fifth/sixth arrays only linearly. -/
theorem radial_raw_error (N : ℕ) (b : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (m : ℕ) (hm : m ≤ 6) (v : Fin m → ℕ) :
    |translatedMoment N b v-translatedMoment N (fun d => (1+t)*b d) v| ≤
      ((N.factorial : ℝ)^6*6*(2*coordinateBudget N b)^6*coordinateBudget N b)*t := by
  let M : ℝ := coordinateBudget N b
  have hM : 1 ≤ M := coordinateBudget_one_le N b
  have hM0 : 0 ≤ M := by linarith
  have h2M : 1 ≤ 2*M := by linarith
  have hbase (q : ℕ) : |selbergMultiplesCoord N b q| ≤ 2*M :=
    (coordinate_le_budget N b q).trans (by linarith)
  have hscaled (q : ℕ) : |selbergMultiplesCoord N (fun d => (1+t)*b d) q| ≤ 2*M := by
    rw [coordinate_scale, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1+t)]
    calc
      _ ≤ (1+t)*M := mul_le_mul_of_nonneg_left (coordinate_le_budget N b q) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : 1+t ≤ 2) hM0
  have hprod (r : Fin m → ZMod N.factorial) :
      |(∏ i, selbergMultiplesCoord N b (addOrderOf (r i)))-
        (∏ i, selbergMultiplesCoord N (fun d => (1+t)*b d) (addOrderOf (r i)))| ≤
        6*(2*M)^6*(M*t) := by
    apply bounded_product_error univ _ _ (2*M) (M*t)
      (by simpa using hm) h2M (by positivity)
    · intro i _; exact hbase _
    · intro i _; exact hscaled _
    · intro i _; exact radial_coordinate_error N b t ht _
  have hP : 1 ≤ (N.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ N.factorial from Nat.factorial_pos N)
  calc
    _ ≤ (N.factorial : ℝ)^m*(6*(2*M)^6*(M*t)) :=
      raw_error_of_resonant_products N b (fun d => (1+t)*b d) m _ (by positivity)
        (fun r _ => hprod r) v
    _ ≤ (N.factorial : ℝ)^6*(6*(2*M)^6*(M*t)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP hm) (by positivity)
    _ = _ := by dsimp [M]; ring

/-- Every nonzero coordinate admits a positive normalization of magnitude two. -/
theorem normalize_coordinate (N : ℕ) (b : ℕ → ℝ) (q : ℕ)
    (hb : selbergMultiplesCoord N b q ≠ 0) :
    ∃ scl : ℝ, 0 < scl ∧ |selbergMultiplesCoord N (fun d => scl*b d) q| = 2 := by
  let scl : ℝ := 2/|selbergMultiplesCoord N b q|
  have hscl : 0 < scl := by dsimp [scl]; positivity
  refine ⟨scl, hscl, ?_⟩
  rw [coordinate_scale, abs_mul, abs_of_pos hscl]
  exact div_mul_cancel₀ _ (abs_ne_zero.mpr hb)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
