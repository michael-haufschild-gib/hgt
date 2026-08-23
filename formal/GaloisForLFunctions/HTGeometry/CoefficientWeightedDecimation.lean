import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Weighted coefficient decimation

On positive-index complex sequences, coefficient decimation by `q` has weighted squared-energy
bound `q^(2α)` and weighted norm bound `q^α`.  This is the exact `H_α` reindexing law; the proof
uses only positivity and injectivity of multiplication by `q`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Positive-index coefficient decimation. -/
def positiveDecimate (q : ℕ) (hq : 0 < q) (a : ℕ+ → ℂ) : ℕ+ → ℂ :=
  fun n => a ⟨q * n, Nat.mul_pos hq n.2⟩

/-- Squared `H_alpha` coefficient norm on positive indices. -/
def weightedCoefficientEnergy (alpha : ℝ) (a : ℕ+ → ℂ) : ℝ :=
  ∑' n : ℕ+, ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * alpha)

/-- Weighted coefficient norm. -/
def weightedCoefficientNorm (alpha : ℝ) (a : ℕ+ → ℂ) : ℝ :=
  Real.sqrt (weightedCoefficientEnergy alpha a)

theorem weightedCoefficientTerm_positiveDecimate
    (alpha : ℝ) (a : ℕ+ → ℂ) (q : ℕ) (hq : 0 < q) (n : ℕ+) :
    ‖positiveDecimate q hq a n‖ ^ 2 * (n : ℝ) ^ (-2 * alpha) =
      (q : ℝ) ^ (2 * alpha) *
        (‖a ⟨q * n, Nat.mul_pos hq n.2⟩‖ ^ 2 *
          ((⟨q * n, Nat.mul_pos hq n.2⟩ : ℕ+) : ℝ) ^ (-2 * alpha)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast n.2
  have hcast : ((⟨q * n, Nat.mul_pos hq n.2⟩ : ℕ+) : ℝ) = (q : ℝ) * (n : ℝ) := by
    norm_num
  have hmul : ((q : ℝ) * (n : ℝ)) ^ (-2 * alpha) =
      (q : ℝ) ^ (-2 * alpha) * (n : ℝ) ^ (-2 * alpha) :=
    Real.mul_rpow hqR.le hnR.le
  have hcancel : (q : ℝ) ^ (2 * alpha) * (q : ℝ) ^ (-2 * alpha) = 1 := by
    rw [← Real.rpow_add hqR]
    ring_nf
    simp
  rw [positiveDecimate, hcast, hmul]
  calc
    ‖a ⟨q * n, Nat.mul_pos hq n.2⟩‖ ^ 2 * (n : ℝ) ^ (-2 * alpha) =
        1 * (‖a ⟨q * n, Nat.mul_pos hq n.2⟩‖ ^ 2 *
          (n : ℝ) ^ (-2 * alpha)) := by rw [one_mul]
    _ = ((q : ℝ) ^ (2 * alpha) * (q : ℝ) ^ (-2 * alpha)) *
        (‖a ⟨q * n, Nat.mul_pos hq n.2⟩‖ ^ 2 *
          (n : ℝ) ^ (-2 * alpha)) := by rw [hcancel]
    _ = (q : ℝ) ^ (2 * alpha) *
        (‖a ⟨q * n, Nat.mul_pos hq n.2⟩‖ ^ 2 *
          ((q : ℝ) ^ (-2 * alpha) * (n : ℝ) ^ (-2 * alpha))) := by ac_rfl

/-- Multiplication by a positive integer is injective on positive indices. -/
theorem positiveIndex_mul_injective (q : ℕ) (hq : 0 < q) :
    Function.Injective (fun n : ℕ+ => (⟨q * n, Nat.mul_pos hq n.2⟩ : ℕ+)) := by
  intro m n h
  apply Subtype.ext
  simp only [Subtype.mk.injEq] at h ⊢
  exact Nat.eq_of_mul_eq_mul_left hq h

/-- Squared weighted norm of decimation is bounded by `q^(2 alpha)`. -/
theorem weightedCoefficientEnergy_positiveDecimate_le
    {alpha : ℝ} {a : ℕ+ → ℂ}
    (ha : Summable (fun n : ℕ+ => ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * alpha)))
    (q : ℕ) (hq : 0 < q) :
    weightedCoefficientEnergy alpha (positiveDecimate q hq a) ≤
      (q : ℝ) ^ (2 * alpha) * weightedCoefficientEnergy alpha a := by
  let f : ℕ+ → ℝ := fun n => ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * alpha)
  let i : ℕ+ → ℕ+ := fun n => ⟨q * n, Nat.mul_pos hq n.2⟩
  have hnonneg : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hinj : Function.Injective i := positiveIndex_mul_injective q hq
  have hsub : ∑' n, f (i n) ≤ ∑' n, f n := by
    exact tsum_comp_le_tsum_of_inj ha hnonneg hinj
  rw [weightedCoefficientEnergy]
  simp_rw [weightedCoefficientTerm_positiveDecimate alpha a q hq]
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hsub (Real.rpow_nonneg (by positivity) _)

/-- Decimation is bounded on `H_alpha` by the exact factor `q^alpha`. -/
theorem weightedCoefficientNorm_positiveDecimate_le
    {alpha : ℝ} {a : ℕ+ → ℂ}
    (ha : Summable (fun n : ℕ+ => ‖a n‖ ^ 2 * (n : ℝ) ^ (-2 * alpha)))
    (q : ℕ) (hq : 0 < q) :
    weightedCoefficientNorm alpha (positiveDecimate q hq a) ≤
      (q : ℝ) ^ alpha * weightedCoefficientNorm alpha a := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have henergy := weightedCoefficientEnergy_positiveDecimate_le ha q hq
  have hbase : 0 ≤ weightedCoefficientEnergy alpha a := by
    rw [weightedCoefficientEnergy]
    exact tsum_nonneg fun n => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by positivity) _)
  have hdec : 0 ≤ weightedCoefficientEnergy alpha (positiveDecimate q hq a) := by
    rw [weightedCoefficientEnergy]
    exact tsum_nonneg fun n => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by positivity) _)
  rw [weightedCoefficientNorm, weightedCoefficientNorm]
  have hpow : ((q : ℝ) ^ alpha) ^ 2 = (q : ℝ) ^ (2 * alpha) := by
    rw [← Real.rpow_mul_natCast hqR.le]
    norm_num
    ring_nf
  have hsqrtBase := Real.sq_sqrt hbase
  have hsqrtDec := Real.sq_sqrt hdec
  have hqpow : 0 ≤ (q : ℝ) ^ alpha := Real.rpow_nonneg hqR.le _
  have hright : ((q : ℝ) ^ alpha * Real.sqrt (weightedCoefficientEnergy alpha a)) ^ 2 =
      (q : ℝ) ^ (2 * alpha) * weightedCoefficientEnergy alpha a := by
    rw [mul_pow, hpow, hsqrtBase]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hqpow (Real.sqrt_nonneg _))).mp
  rw [hsqrtDec, hright]
  exact henergy

end GaloisForLFunctions.HTGeometry
