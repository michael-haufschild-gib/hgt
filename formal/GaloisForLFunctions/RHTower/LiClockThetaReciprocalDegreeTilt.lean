import GaloisForLFunctions.RHTower.LiClockThetaReciprocalRawGerm
import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence

/-!
# The raw degree tilt of the reciprocal germ

For `z > 0` the raw coefficients of `Q_z(u) = Φ(z/(1-zu))/Φ(z)` are `a_n = z^n 𝒜_n/Φ(z)` with
`𝒜_n = Σ_j w_{n,j}`, `w_{n,j} = c_j z^{2j} C(2j+n-1, n)` (`c_j = ν_j/(2j)!`, `w_{n,0} = 0` for
`n ≥ 1`).  Let `P_n(j) = w_{n,j}/𝒜_n` and `μ_n = E_n[2j-1]`.

* (A2) `a_{n+1}/(z a_n) = 1 + μ_n/(n+1)`;
* (A3) `μ_{n+1} - μ_n = Var_n(2j-1)/(n+1+μ_n) > 0` for `n ≥ 1`;
* (A4) every fixed degree head escapes and `μ_n → ∞`;
* (A5, A6) `ν_{j+1} ≤ j ν_j` and `w_{n,j+1} ≤ z²(2j+n+1)²/(16j³) w_{n,j}` for `j ≥ 1`;
* (A7) `μ_n/(n+1) → 0`;
* (A8) `a_{n+1}/a_n > z` for `n ≥ 1`, `a_{n+1}/a_n → z` and `(n+1)(a_{n+1}/(z a_n) - 1) = μ_n → ∞`;
* (A9) `b_n = Σ_{m=1}^n ((-1)^{m+1}/m) Σ_{k_1+⋯+k_m = n, k_i ≥ 1} a_{k_1}⋯a_{k_m}`.
-/

open Set Filter Topology

noncomputable section

namespace RHTower

local notation "Φ" => liClockThetaGeneratorReal
local notation "ν" => thetaCuspNormalizedEvenMoment
local notation "a" => liClockReciprocalGermCoeff

/-- `w_{n,j} = c_j z^{2j} C(2j+n-1, n)`. -/
def liClockReciprocalDegreeWeight (z : ℝ) (n j : ℕ) : ℝ :=
  liClockThetaGeneratorCoeff j * z ^ (2 * j) * (((2 * j + n - 1).choose n : ℕ) : ℝ)

/-- `𝒜_n = Σ_j w_{n,j}`. -/
def liClockReciprocalDegreeMass (z : ℝ) (n : ℕ) : ℝ := ∑' j, liClockReciprocalDegreeWeight z n j

/-- The degree law `P_n(j) = w_{n,j}/𝒜_n`. -/
def liClockReciprocalDegreeLaw (z : ℝ) (n j : ℕ) : ℝ :=
  liClockReciprocalDegreeWeight z n j / liClockReciprocalDegreeMass z n

/-- The degree mean `μ_n = E_n[2j-1]`. -/
def liClockReciprocalDegreeMean (z : ℝ) (n : ℕ) : ℝ :=
  (∑' j : ℕ, (2 * (j : ℝ) - 1) * liClockReciprocalDegreeWeight z n j) / liClockReciprocalDegreeMass z n

/-- The degree variance `Var_n(2j-1) = E_n[(2j-1)²] - μ_n²`. -/
def liClockReciprocalDegreeVariance (z : ℝ) (n : ℕ) : ℝ :=
  (∑' j : ℕ, (2 * (j : ℝ) - 1) ^ 2 * liClockReciprocalDegreeWeight z n j) /
    liClockReciprocalDegreeMass z n - liClockReciprocalDegreeMean z n ^ 2

local notation "w" => liClockReciprocalDegreeWeight
local notation "𝒜" => liClockReciprocalDegreeMass
local notation "pr" => liClockReciprocalDegreeLaw
local notation "μ" => liClockReciprocalDegreeMean
local notation "V" => liClockReciprocalDegreeVariance

/-! ## The weights -/

theorem liClockReciprocalDegreeWeight_nonneg {z : ℝ} (hz : 0 ≤ z) (n j : ℕ) : 0 ≤ w z n j := by
  unfold liClockReciprocalDegreeWeight
  have := liClockThetaGeneratorCoeff_pos j
  positivity

theorem liClockReciprocalDegreeWeight_zero_index (z : ℝ) {n : ℕ} (hn : 1 ≤ n) : w z n 0 = 0 := by
  simp [liClockReciprocalDegreeWeight, Nat.choose_eq_zero_of_lt (show n - 1 < n by omega)]

theorem liClockReciprocalDegreeWeight_pos {z : ℝ} (hz : 0 < z) (n : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    0 < w z n j := by
  unfold liClockReciprocalDegreeWeight
  have := liClockThetaGeneratorCoeff_pos j
  have hc : 0 < (((2 * j + n - 1).choose n : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  positivity

theorem liClockReciprocalDegreeWeight_two_mul (z : ℝ) (n j : ℕ) :
    w (2 * z) n j = 4 ^ j * w z n j := by
  unfold liClockReciprocalDegreeWeight
  rw [mul_pow, pow_mul, pow_mul]
  norm_num
  ring

/-- `(n+1) w_{n+1,j} = (2j+n) w_{n,j}`. -/
theorem liClockReciprocalDegreeWeight_succ (z : ℝ) (n j : ℕ) :
    ((n : ℝ) + 1) * w z (n + 1) j = (2 * j + n) * w z n j := by
  unfold liClockReciprocalDegreeWeight
  have hc : ((n : ℝ) + 1) * (((2 * j + (n + 1) - 1).choose (n + 1) : ℕ) : ℝ) =
      (2 * j + n) * (((2 * j + n - 1).choose n : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (2 * j + n) with h0 | hpos
    · have hj : j = 0 := by omega
      have hn : n = 0 := by omega
      subst hj hn
      simp
    · obtain ⟨m, hm⟩ : ∃ m, 2 * j + n = m + 1 := ⟨2 * j + n - 1, by omega⟩
      have h := Nat.add_one_mul_choose_eq m n
      rw [show 2 * j + (n + 1) - 1 = m + 1 by omega, show 2 * j + n - 1 = m by omega]
      have h' : ((m + 1 : ℕ) : ℝ) * ((m.choose n : ℕ) : ℝ) =
          (((m + 1).choose (n + 1) : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h
      have e : (2 * (j : ℝ) + n) = ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hm
      rw [e, h']
      push_cast
      ring
  calc ((n : ℝ) + 1) * (liClockThetaGeneratorCoeff j * z ^ (2 * j) *
        (((2 * j + (n + 1) - 1).choose (n + 1) : ℕ) : ℝ)) =
        liClockThetaGeneratorCoeff j * z ^ (2 * j) *
          (((n : ℝ) + 1) * (((2 * j + (n + 1) - 1).choose (n + 1) : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hc]; ring

private theorem pow_le_factorial_mul_four_pow (k j : ℕ) :
    (j : ℝ) ^ k ≤ k.factorial * 4 ^ j := by
  have h := Real.pow_div_factorial_le_exp (j : ℝ) j.cast_nonneg k
  have he : Real.exp (j : ℝ) ≤ 4 ^ j := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le
      (by have := Real.exp_one_lt_d9; linarith) j
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hf] at h
  nlinarith

/-- Every polynomially weighted row is summable: `Σ_j j^k w_{n,j} < ∞`. -/
theorem summable_pow_mul_liClockReciprocalDegreeWeight {z : ℝ} (hz : 0 ≤ z) (n k : ℕ) :
    Summable fun j : ℕ => (j : ℝ) ^ k * w z n j := by
  have h2 : Summable fun j => w (2 * z) n j :=
    summable_liClockGermCoeffSeries (by linarith) n
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg j.cast_nonneg k)
    (liClockReciprocalDegreeWeight_nonneg hz n j)) (fun j => ?_) (h2.mul_left (k.factorial : ℝ))
  rw [liClockReciprocalDegreeWeight_two_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_le_factorial_mul_four_pow k j)
    (liClockReciprocalDegreeWeight_nonneg hz n j)

theorem summable_liClockReciprocalDegreeWeight {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    Summable (w z n) := by
  simpa using summable_pow_mul_liClockReciprocalDegreeWeight hz n 0

theorem summable_poly_mul_liClockReciprocalDegreeWeight {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    Summable (fun j : ℕ => (2 * (j : ℝ) - 1) * w z n j) ∧
      Summable (fun j : ℕ => (2 * (j : ℝ) - 1) ^ 2 * w z n j) := by
  have h0 := summable_pow_mul_liClockReciprocalDegreeWeight hz n 0
  have h1 := summable_pow_mul_liClockReciprocalDegreeWeight hz n 1
  have h2 := summable_pow_mul_liClockReciprocalDegreeWeight hz n 2
  refine ⟨((h1.mul_left 2).sub h0).congr fun j => by simp; ring,
    (((h2.mul_left 4).sub (h1.mul_left 4)).add h0).congr fun j => by simp; ring⟩

/-- `a_n = z^n 𝒜_n/Φ(z)`. -/
theorem liClockReciprocalGermCoeff_eq_mass (z : ℝ) (n : ℕ) : a z n = z ^ n / Φ z * 𝒜 z n := rfl

theorem liClockReciprocalDegreeMass_pos {z : ℝ} (hz : 0 < z) (n : ℕ) : 0 < 𝒜 z n :=
  lt_of_lt_of_le (liClockReciprocalDegreeWeight_pos hz n le_rfl)
    ((summable_liClockReciprocalDegreeWeight hz.le n).le_tsum 1 fun j _ =>
      liClockReciprocalDegreeWeight_nonneg hz.le n j)

/-! ## The degree law -/

/-- `P_n` is a probability carried by `j ≥ 1` (for `n ≥ 1`). -/
theorem liClockReciprocalDegreeLaw_hasSum {z : ℝ} (hz : 0 < z) (n : ℕ) :
    HasSum (pr z n) 1 ∧ (∀ j, 0 ≤ pr z n j) ∧ (1 ≤ n → pr z n 0 = 0) := by
  have hA := liClockReciprocalDegreeMass_pos hz n
  refine ⟨?_, fun j => div_nonneg (liClockReciprocalDegreeWeight_nonneg hz.le n j) hA.le,
    fun hn => by simp [liClockReciprocalDegreeLaw, liClockReciprocalDegreeWeight_zero_index z hn]⟩
  have h : HasSum (fun j => w z n j / 𝒜 z n) (𝒜 z n / 𝒜 z n) :=
    (summable_liClockReciprocalDegreeWeight hz.le n).hasSum.div_const _
  rwa [div_self hA.ne'] at h

/-- `μ_n = Σ_j (2j-1) P_n(j)` and `E_n[(2j-1)²] = V_n + μ_n²`. -/
theorem liClockReciprocalDegreeLaw_moments {z : ℝ} (hz : 0 < z) (n : ℕ) :
    HasSum (fun j : ℕ => (2 * (j : ℝ) - 1) * pr z n j) (μ z n) ∧
      HasSum (fun j : ℕ => (2 * (j : ℝ) - 1) ^ 2 * pr z n j) (V z n + μ z n ^ 2) := by
  obtain ⟨h1, h2⟩ := summable_poly_mul_liClockReciprocalDegreeWeight hz.le n
  unfold liClockReciprocalDegreeLaw liClockReciprocalDegreeVariance liClockReciprocalDegreeMean
  simp only [← mul_div_assoc]
  refine ⟨h1.hasSum.div_const _, ?_⟩
  rw [sub_add_cancel]
  exact h2.hasSum.div_const _

/-- `μ_n ≥ 1` for `n ≥ 1`. -/
theorem one_le_liClockReciprocalDegreeMean {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ μ z n := by
  obtain ⟨h1, hnn, h0⟩ := liClockReciprocalDegreeLaw_hasSum hz n
  refine hasSum_le (fun j => ?_) h1 (liClockReciprocalDegreeLaw_moments hz n).1
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [h0 hn]; simp
  · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith [hnn j]

/-- `Var_n(2j-1) = Σ_j (2j-1-μ_n)² P_n(j)`. -/
theorem liClockReciprocalDegreeVariance_hasSum {z : ℝ} (hz : 0 < z) (n : ℕ) :
    HasSum (fun j : ℕ => (2 * (j : ℝ) - 1 - μ z n) ^ 2 * pr z n j) (V z n) := by
  obtain ⟨h1, -, -⟩ := liClockReciprocalDegreeLaw_hasSum hz n
  obtain ⟨hm1, hm2⟩ := liClockReciprocalDegreeLaw_moments hz n
  have h := (hm2.sub (hm1.mul_left (2 * μ z n))).add (h1.mul_left (μ z n ^ 2))
  have e : ∀ j : ℕ, (2 * (j : ℝ) - 1) ^ 2 * pr z n j - 2 * μ z n * ((2 * (j : ℝ) - 1) * pr z n j) +
      μ z n ^ 2 * pr z n j = (2 * (j : ℝ) - 1 - μ z n) ^ 2 * pr z n j := fun j => by ring
  simp only [e] at h
  have hv : V z n + μ z n ^ 2 - 2 * μ z n * μ z n + μ z n ^ 2 * 1 = V z n := by ring
  rwa [hv] at h

/-- The variance is strictly positive for `n ≥ 1`: the degrees `j = 1, 2` both carry mass. -/
theorem liClockReciprocalDegreeVariance_pos {z : ℝ} (hz : 0 < z) (n : ℕ) : 0 < V z n := by
  have h := liClockReciprocalDegreeVariance_hasSum hz n
  have hA := liClockReciprocalDegreeMass_pos hz n
  have hp : ∀ j, 1 ≤ j → 0 < pr z n j := fun j hj =>
    div_pos (liClockReciprocalDegreeWeight_pos hz n hj) hA
  have hnn : ∀ j : ℕ, 0 ≤ (2 * (j : ℝ) - 1 - μ z n) ^ 2 * pr z n j := fun j =>
    mul_nonneg (sq_nonneg _) ((liClockReciprocalDegreeLaw_hasSum hz n).2.1 j)
  have hle := sum_le_hasSum ({1, 2} : Finset ℕ) (fun j _ => hnn j) h
  rw [Finset.sum_pair (by norm_num)] at hle
  have h1 := hp 1 le_rfl
  have h2 := hp 2 (by norm_num)
  push_cast at hle
  by_contra hV
  rw [not_lt] at hV
  have e1 : (2 * (1 : ℝ) - 1 - μ z n) ^ 2 * pr z n 1 = 0 := by
    nlinarith [mul_nonneg (sq_nonneg (2 * (1 : ℝ) - 1 - μ z n)) h1.le,
      mul_nonneg (sq_nonneg (2 * (2 : ℝ) - 1 - μ z n)) h2.le]
  have e2 : (2 * (2 : ℝ) - 1 - μ z n) ^ 2 * pr z n 2 = 0 := by
    nlinarith [mul_nonneg (sq_nonneg (2 * (1 : ℝ) - 1 - μ z n)) h1.le,
      mul_nonneg (sq_nonneg (2 * (2 : ℝ) - 1 - μ z n)) h2.le]
  rcases mul_eq_zero.1 e1 with e1 | e1
  · rcases mul_eq_zero.1 e2 with e2 | e2
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e1
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 e2
      linarith
    · linarith
  · linarith

/-! ## (A2, A3) The degree transport -/

private theorem mass_succ {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ((n : ℝ) + 1) * 𝒜 z (n + 1) = ((n : ℝ) + 1) * 𝒜 z n + μ z n * 𝒜 z n := by
  have hA := liClockReciprocalDegreeMass_pos hz n
  obtain ⟨h1, -⟩ := summable_poly_mul_liClockReciprocalDegreeWeight hz.le n
  have hs := summable_liClockReciprocalDegreeWeight hz.le n
  unfold liClockReciprocalDegreeMean
  rw [div_mul_cancel₀ _ hA.ne']
  unfold liClockReciprocalDegreeMass
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hs.mul_left _).tsum_add h1]
  refine tsum_congr fun j => ?_
  rw [liClockReciprocalDegreeWeight_succ]
  ring

/-- **(A2)** `a_{n+1}/(z a_n) = 1 + μ_n/(n+1)`. -/
theorem liClockReciprocalGermCoeff_succ_div {z : ℝ} (hz : 0 < z) (n : ℕ) :
    a z (n + 1) / (z * a z n) = 1 + μ z n / (n + 1) := by
  have hA := liClockReciprocalDegreeMass_pos hz n
  have hΦ : 0 < Φ z := lt_of_lt_of_le one_pos (one_le_liClockThetaGeneratorReal z)
  have hm := mass_succ hz n
  rw [liClockReciprocalGermCoeff_eq_mass, liClockReciprocalGermCoeff_eq_mass]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have e : 𝒜 z (n + 1) = 𝒜 z n * (1 + μ z n / (n + 1)) := by
    field_simp
    linarith
  rw [e, pow_succ]
  field_simp

/-- **(A3)** `μ_{n+1} - μ_n = Var_n(2j-1)/(n+1+μ_n) > 0` for `n ≥ 1`. -/
theorem liClockReciprocalDegreeMean_succ_sub {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 1 ≤ n) :
    μ z (n + 1) - μ z n = V z n / (n + 1 + μ z n) ∧ 0 < μ z (n + 1) - μ z n := by
  have hA := liClockReciprocalDegreeMass_pos hz n
  have hA1 := liClockReciprocalDegreeMass_pos hz (n + 1)
  have hμ := one_le_liClockReciprocalDegreeMean hz hn
  have hV := liClockReciprocalDegreeVariance_pos hz n
  obtain ⟨h1, h2⟩ := summable_poly_mul_liClockReciprocalDegreeWeight hz.le n
  have hm := mass_succ hz n
  have hd : ((n : ℝ) + 1) * ∑' j : ℕ, (2 * (j : ℝ) - 1) * w z (n + 1) j =
      ((n : ℝ) + 1) * ∑' j : ℕ, (2 * (j : ℝ) - 1) * w z n j +
        ∑' j : ℕ, (2 * (j : ℝ) - 1) ^ 2 * w z n j := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (h1.mul_left _).tsum_add h2]
    refine tsum_congr fun j => ?_
    have := liClockReciprocalDegreeWeight_succ z n j
    calc ((n : ℝ) + 1) * ((2 * (j : ℝ) - 1) * w z (n + 1) j) =
        (2 * (j : ℝ) - 1) * (((n : ℝ) + 1) * w z (n + 1) j) := by ring
      _ = _ := by rw [this]; ring
  have hS1 : ∑' j : ℕ, (2 * (j : ℝ) - 1) * w z n j = μ z n * 𝒜 z n := by
    unfold liClockReciprocalDegreeMean; rw [div_mul_cancel₀ _ hA.ne']
  have hS2 : ∑' j : ℕ, (2 * (j : ℝ) - 1) ^ 2 * w z n j = (V z n + μ z n ^ 2) * 𝒜 z n := by
    unfold liClockReciprocalDegreeVariance; rw [sub_add_cancel, div_mul_cancel₀ _ hA.ne']
  have hS1' : ∑' j : ℕ, (2 * (j : ℝ) - 1) * w z (n + 1) j = μ z (n + 1) * 𝒜 z (n + 1) := by
    unfold liClockReciprocalDegreeMean; rw [div_mul_cancel₀ _ hA1.ne']
  rw [hS1, hS2, hS1'] at hd
  have hden : (0 : ℝ) < n + 1 + μ z n := by positivity
  have key : μ z (n + 1) * (n + 1 + μ z n) = (n + 1) * μ z n + (V z n + μ z n ^ 2) := by
    have h3 : ((n : ℝ) + 1) * 𝒜 z (n + 1) = (n + 1 + μ z n) * 𝒜 z n := by linarith
    have : (n + 1 + μ z n) * 𝒜 z n * μ z (n + 1) =
        (((n : ℝ) + 1) * μ z n + (V z n + μ z n ^ 2)) * 𝒜 z n := by
      rw [← h3]; linear_combination hd
    exact mul_right_cancel₀ hA.ne' (by linarith)
  have hres : μ z (n + 1) - μ z n = V z n / (n + 1 + μ z n) := by
    rw [eq_div_iff hden.ne']
    linarith
  exact ⟨hres, by rw [hres]; positivity⟩

/-! ## (A4) Escape of every fixed degree head -/

private theorem choose_upper (j n : ℕ) (hj : 1 ≤ j) :
    (((2 * j + n - 1).choose n : ℕ) : ℝ) ≤ ((2 * j + n - 1 : ℕ) : ℝ) ^ (2 * j - 1) := by
  rw [Nat.choose_symm_of_eq_add (show 2 * j + n - 1 = n + (2 * j - 1) by omega)]
  have h := Nat.choose_le_pow_div (α := ℝ) (2 * j - 1) (2 * j + n - 1)
  have hf : (1 : ℝ) ≤ ((2 * j - 1).factorial : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos _)
  exact h.trans (div_le_self (by positivity) hf)

private theorem choose_lower (J n : ℕ) :
    ((n : ℝ) + 1) ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ) ≤
      (((2 * (J + 1) + n - 1).choose n : ℕ) : ℝ) := by
  rw [Nat.choose_symm_of_eq_add (show 2 * (J + 1) + n - 1 = n + (2 * J + 1) by omega)]
  have h := Nat.pow_le_choose (α := ℝ) (2 * J + 1) (2 * (J + 1) + n - 1)
  rw [show 2 * (J + 1) + n - 1 + 1 - (2 * J + 1) = n + 1 by omega] at h
  push_cast at h
  exact h

/-- The ratio `w_{n,j}/w_{n,J+1} → 0` for every fixed `j ≤ J`. -/
private theorem tendsto_weight_div_next {z : ℝ} (hz : 0 < z) {J j : ℕ} (hjJ : j ≤ J) :
    Tendsto (fun n => w z n j / w z n (J + 1)) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [liClockReciprocalDegreeWeight_zero_index z hn, zero_div]
  · set K : ℝ := liClockThetaGeneratorCoeff j * z ^ (2 * j) * (2 * J + 1 : ℝ) ^ (2 * j - 1) *
        ((2 * J + 1).factorial : ℝ) / (liClockThetaGeneratorCoeff (J + 1) * z ^ (2 * (J + 1)))
    have hcJ := liClockThetaGeneratorCoeff_pos (J + 1)
    have hcj := liClockThetaGeneratorCoeff_pos j
    have hK : 0 ≤ K := by positivity
    have hlim : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => div_nonneg (liClockReciprocalDegreeWeight_nonneg hz.le n j)
        (liClockReciprocalDegreeWeight_nonneg hz.le n (J + 1))) (fun n => ?_)
    have hwJ := liClockReciprocalDegreeWeight_pos hz n (show 1 ≤ J + 1 by omega)
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    rw [div_le_div_iff₀ hwJ hn1]
    unfold liClockReciprocalDegreeWeight
    have hup := choose_upper j n hj
    have hlow := choose_lower J n
    have hbase : ((2 * j + n - 1 : ℕ) : ℝ) ≤ (2 * J + 1) * ((n : ℝ) + 1) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      have : (j : ℝ) ≤ J := by exact_mod_cast hjJ
      nlinarith
    have hpow : ((2 * j + n - 1 : ℕ) : ℝ) ^ (2 * j - 1) ≤
        (2 * J + 1 : ℝ) ^ (2 * j - 1) * ((n : ℝ) + 1) ^ (2 * j - 1) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hbase _
    have hexp : ((n : ℝ) + 1) ^ (2 * j - 1) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ (2 * J + 1) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    have hf : (0 : ℝ) < ((2 * J + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [div_le_iff₀ hf] at hlow
    unfold K
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc liClockThetaGeneratorCoeff j * z ^ (2 * j) * (((2 * j + n - 1).choose n : ℕ) : ℝ) *
          ((n : ℝ) + 1) * (liClockThetaGeneratorCoeff (J + 1) * z ^ (2 * (J + 1)))
        ≤ liClockThetaGeneratorCoeff j * z ^ (2 * j) *
          ((2 * J + 1 : ℝ) ^ (2 * j - 1) * ((n : ℝ) + 1) ^ (2 * j - 1)) * ((n : ℝ) + 1) *
            (liClockThetaGeneratorCoeff (J + 1) * z ^ (2 * (J + 1))) := by
          gcongr; exact hup.trans hpow
      _ ≤ liClockThetaGeneratorCoeff j * z ^ (2 * j) * (2 * J + 1 : ℝ) ^ (2 * j - 1) *
          ((n : ℝ) + 1) ^ (2 * J + 1) *
            (liClockThetaGeneratorCoeff (J + 1) * z ^ (2 * (J + 1))) := by
          have := mul_le_mul_of_nonneg_left hexp (by positivity :
            (0 : ℝ) ≤ liClockThetaGeneratorCoeff j * z ^ (2 * j) * (2 * J + 1 : ℝ) ^ (2 * j - 1) *
              (liClockThetaGeneratorCoeff (J + 1) * z ^ (2 * (J + 1))))
          nlinarith [this]
      _ ≤ liClockThetaGeneratorCoeff j * z ^ (2 * j) * (2 * J + 1 : ℝ) ^ (2 * j - 1) *
          ((((2 * (J + 1) + n - 1).choose n : ℕ) : ℝ) * ((2 * J + 1).factorial : ℝ)) *
            (liClockThetaGeneratorCoeff (J + 1) * z ^ (2 * (J + 1))) := by gcongr
      _ = _ := by ring

/-- **(A4)** Every fixed degree head escapes: `P_n(j ≤ J) → 0`. -/
theorem tendsto_liClockReciprocalDegreeLaw_head {z : ℝ} (hz : 0 < z) (J : ℕ) :
    Tendsto (fun n => ∑ j ∈ Finset.range (J + 1), pr z n j) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ∑ j ∈ Finset.range (J + 1), w z n j / w z n (J + 1)) atTop
      (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range (J + 1)) fun j hj =>
      tendsto_weight_div_next hz (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => Finset.sum_nonneg fun j _ => (liClockReciprocalDegreeLaw_hasSum hz n).2.1 j)
    (fun n => Finset.sum_le_sum fun j _ => ?_)
  have hA := liClockReciprocalDegreeMass_pos hz n
  have hwJ := liClockReciprocalDegreeWeight_pos hz n (show 1 ≤ J + 1 by omega)
  have hle : w z n (J + 1) ≤ 𝒜 z n :=
    (summable_liClockReciprocalDegreeWeight hz.le n).le_tsum _ fun i _ =>
      liClockReciprocalDegreeWeight_nonneg hz.le n i
  exact div_le_div_of_nonneg_left (liClockReciprocalDegreeWeight_nonneg hz.le n j) hwJ hle

/-- **(A4)** `μ_n ≥ (2J+1)(1 - P_n(j ≤ J))` for `n ≥ 1`. -/
theorem liClockReciprocalDegreeMean_ge_head {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 1 ≤ n) (J : ℕ) :
    (2 * J + 1) * (1 - ∑ j ∈ Finset.range (J + 1), pr z n j) ≤ μ z n := by
  classical
  obtain ⟨h1, hnn, h0⟩ := liClockReciprocalDegreeLaw_hasSum hz n
  have hfin : HasSum (fun j => if j ∈ Finset.range (J + 1) then pr z n j else 0)
      (∑ j ∈ Finset.range (J + 1), (if j ∈ Finset.range (J + 1) then pr z n j else 0)) :=
    hasSum_sum_of_ne_finset_zero fun j hj => by simp only [hj, if_false]
  have hsum : ∑ j ∈ Finset.range (J + 1), (if j ∈ Finset.range (J + 1) then pr z n j else 0) =
      ∑ j ∈ Finset.range (J + 1), pr z n j :=
    Finset.sum_congr rfl fun j hj => by simp only [hj, if_true]
  rw [hsum] at hfin
  have hg := (h1.sub hfin).mul_left (2 * (J : ℝ) + 1)
  refine hasSum_le (fun j => ?_) hg (liClockReciprocalDegreeLaw_moments hz n).1
  by_cases hj : j ∈ Finset.range (J + 1)
  · simp only [hj, if_true, sub_self, mul_zero]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [h0 hn, mul_zero]
    · have : (1 : ℝ) ≤ j := by exact_mod_cast hj0
      nlinarith [hnn j]
  · simp only [hj, if_false, sub_zero]
    have : (J : ℝ) + 1 ≤ j := by
      exact_mod_cast (show J + 1 ≤ j by simpa using hj)
    nlinarith [hnn j]

/-- **(A4)** `μ_n → ∞`. -/
theorem tendsto_liClockReciprocalDegreeMean_atTop {z : ℝ} (hz : 0 < z) :
    Tendsto (μ z) atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * |M|)
  filter_upwards [(tendsto_order.1 (tendsto_liClockReciprocalDegreeLaw_head hz J)).2 (1 / 2)
    (by norm_num), eventually_ge_atTop 1] with n hh hn
  have h := liClockReciprocalDegreeMean_ge_head hz hn J
  have hM : M ≤ |M| := le_abs_self M
  have hJ' : (0 : ℝ) ≤ J := J.cast_nonneg
  nlinarith

/-! ## (A5, A6) The actual Ward row ratio -/

/-- **(A5)** `ν_{j+1} ≤ j ν_j` for `j ≥ 1`. -/
theorem thetaCuspNormalizedEvenMoment_succ_le_mul {j : ℕ} (hj : 1 ≤ j) :
    ν (j + 1) ≤ j * ν j := by
  have h := thetaCuspNormalizedEvenMoment_succ_le_score j
  have hν := thetaCuspNormalizedEvenMoment_pos j
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  nlinarith

/-- The exact row ratio: `w_{n,j+1} (2j)(2j+1)²(2j+2) ν_j = w_{n,j} z² ν_{j+1} (2j+n)(2j+n+1)`. -/
theorem liClockReciprocalDegreeWeight_succ_index (z : ℝ) (n : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    w z n (j + 1) * ((2 * j) * (2 * j + 1) ^ 2 * (2 * j + 2) * ν j) =
      w z n j * (z ^ 2 * ν (j + 1) * ((2 * j + n) * (2 * j + n + 1))) := by
  have c1 := Nat.choose_mul_succ_eq (2 * j + n - 1) n
  have c2 := Nat.choose_mul_succ_eq (2 * j + n) n
  rw [show 2 * j + n - 1 + 1 = 2 * j + n by omega, show 2 * j + n - n = 2 * j by omega] at c1
  rw [show 2 * j + n + 1 - n = 2 * j + 1 by omega] at c2
  have c1' : (((2 * j + n - 1).choose n : ℕ) : ℝ) * (2 * j + n) =
      (((2 * j + n).choose n : ℕ) : ℝ) * (2 * j) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) c1
    push_cast [Nat.cast_sub (show 1 ≤ 2 * j + n by omega)] at this ⊢
    linarith
  have c2' : (((2 * j + n).choose n : ℕ) : ℝ) * (2 * j + n + 1) =
      (((2 * j + n + 1).choose n : ℕ) : ℝ) * (2 * j + 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) c2
    push_cast at this ⊢
    linarith
  have hf : ((2 * (j + 1)).factorial : ℝ) = (2 * j + 2) * (2 * j + 1) * ((2 * j).factorial : ℝ) := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hf0 : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  unfold liClockReciprocalDegreeWeight liClockThetaGeneratorCoeff
  rw [show 2 * (j + 1) + n - 1 = 2 * j + n + 1 by omega, hf]
  have e : (((2 * j + n + 1).choose n : ℕ) : ℝ) * (2 * j + 1) * (2 * j) =
      (((2 * j + n - 1).choose n : ℕ) : ℝ) * (2 * j + n) * (2 * j + n + 1) := by
    rw [← c2', mul_assoc, mul_comm (2 * j + n + 1 : ℝ), ← mul_assoc, ← c1']
  field_simp
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  linear_combination (ν (j + 1) * ν j * z ^ (2 * j) * z ^ 2) * e

/-- **(A6)** `w_{n,j+1} ≤ z²(2j+n+1)²/(16j³) w_{n,j}` for `j ≥ 1`. -/
theorem liClockReciprocalDegreeWeight_succ_index_le {z : ℝ} (hz : 0 < z) (n : ℕ) {j : ℕ}
    (hj : 1 ≤ j) : w z n (j + 1) ≤ z ^ 2 * (2 * j + n + 1) ^ 2 / (16 * j ^ 3) * w z n j := by
  have he := liClockReciprocalDegreeWeight_succ_index z n hj
  have hν := thetaCuspNormalizedEvenMoment_pos j
  have hA5 := thetaCuspNormalizedEvenMoment_succ_le_mul hj
  have hw := liClockReciprocalDegreeWeight_nonneg hz.le n j
  have hw1 := liClockReciprocalDegreeWeight_nonneg hz.le n (j + 1)
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hq : (2 * (j : ℝ) + n) * (2 * j + n + 1) ≤ (2 * j + n + 1) ^ 2 := by nlinarith
  have hR : w z n j * (z ^ 2 * ν (j + 1) * ((2 * j + n) * (2 * j + n + 1))) ≤
      w z n j * (z ^ 2 * j * (2 * j + n + 1) ^ 2) * ν j := by
    have h1 : ν (j + 1) * ((2 * j + n) * (2 * j + n + 1)) ≤ j * ν j * (2 * j + n + 1) ^ 2 :=
      mul_le_mul hA5 hq (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hw (sq_nonneg z))
    nlinarith [this]
  rw [← he] at hR
  have hD : w z n (j + 1) * ((2 * j) * (2 * j + 1) ^ 2 * (2 * j + 2)) ≤
      w z n j * (z ^ 2 * j * (2 * j + n + 1) ^ 2) :=
    le_of_mul_le_mul_right (by linarith) hν
  have hD16 : 16 * (j : ℝ) ^ 4 ≤ (2 * j) * (2 * j + 1) ^ 2 * (2 * j + 2) := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h4 : w z n (j + 1) * (16 * (j : ℝ) ^ 4) ≤ w z n j * (z ^ 2 * j * (2 * j + n + 1) ^ 2) :=
    (mul_le_mul_of_nonneg_left hD16 hw1).trans hD
  have hj0 : (0 : ℝ) < j := by linarith
  nlinarith [h4]

/-! ## (A7) The degree mean is sublinear -/

private theorem tsum_mul_le_of_halving {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (hs : Summable f)
    (hs1 : Summable fun j : ℕ => (j : ℝ) * f j) {J : ℕ}
    (hJ : ∀ j, J ≤ j → f (j + 1) ≤ f j / 2) :
    ∑' j : ℕ, (j : ℝ) * f j ≤ (J + 2) * ∑' j, f j := by
  have hk : ∀ k, f (k + J) ≤ (1 / 2) ^ k * f J := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      have := hJ (k + J) (by omega)
      rw [show k + 1 + J = k + J + 1 by ring, pow_succ]
      nlinarith [hf (k + J)]
  have hsJ : Summable fun k => f (k + J) := (summable_nat_add_iff J).2 hs
  have hs1J : Summable fun k => ((k + J : ℕ) : ℝ) * f (k + J) :=
    (summable_nat_add_iff J (f := fun j : ℕ => (j : ℝ) * f j)).2 hs1
  have hkf : Summable fun k : ℕ => (k : ℝ) * f (k + J) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg k.cast_nonneg (hf _))
      (fun k => mul_le_mul_of_nonneg_right (by push_cast; linarith) (hf _)) hs1J
  have hgeo : ∑' k : ℕ, (k : ℝ) * ((1 / 2) ^ k * f J) = 2 * f J := by
    have h := tsum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    rw [show (∑' k : ℕ, (k : ℝ) * ((1 / 2) ^ k * f J)) = (∑' k : ℕ, (k : ℝ) * (1 / 2) ^ k) * f J by
      rw [← tsum_mul_right]; exact tsum_congr fun k => by ring, h]
    norm_num
  have hgeoS : Summable fun k : ℕ => (k : ℝ) * ((1 / 2) ^ k * f J) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)).mul_right
      (f J)
    exact this.congr fun k => by ring
  have htail : ∑' k : ℕ, (k : ℝ) * f (k + J) ≤ 2 * f J := by
    rw [← hgeo]
    exact Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hk k) k.cast_nonneg) hkf hgeoS
  have hfJ : f J ≤ ∑' k, f (k + J) := by
    simpa using hsJ.le_tsum 0 fun k _ => hf _
  have hsplit := hs1.sum_add_tsum_nat_add J
  have hsplit0 := hs.sum_add_tsum_nat_add J
  have hhead : ∑ i ∈ Finset.range J, (i : ℝ) * f i ≤ J * ∑ i ∈ Finset.range J, f i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Finset.mem_range.1 hi).le) (hf i)
  have hshift : ∑' k : ℕ, ((k + J : ℕ) : ℝ) * f (k + J) =
      ∑' k : ℕ, (k : ℝ) * f (k + J) + J * ∑' k, f (k + J) := by
    rw [← tsum_mul_left, ← hkf.tsum_add (hsJ.mul_left _)]
    exact tsum_congr fun k => by push_cast; ring
  rw [← hsplit, ← hsplit0, hshift]
  have hhead0 : 0 ≤ ∑ i ∈ Finset.range J, f i := Finset.sum_nonneg fun i _ => hf i
  nlinarith

theorem liClockReciprocalDegreeMean_eq {z : ℝ} (hz : 0 < z) (n : ℕ) :
    μ z n = 2 * (∑' j : ℕ, (j : ℝ) * w z n j) / 𝒜 z n - 1 := by
  have hA := liClockReciprocalDegreeMass_pos hz n
  have h1 := summable_pow_mul_liClockReciprocalDegreeWeight hz.le n 1
  have hs := summable_liClockReciprocalDegreeWeight hz.le n
  unfold liClockReciprocalDegreeMean
  have e : ∑' j : ℕ, (2 * (j : ℝ) - 1) * w z n j = 2 * ∑' j : ℕ, (j : ℝ) * w z n j - 𝒜 z n := by
    rw [← tsum_mul_left, liClockReciprocalDegreeMass, ← ((h1.congr fun j => by simp).mul_left
      2).tsum_sub hs]
    exact tsum_congr fun j => by ring
  rw [e]
  field_simp

/-- **(A7)** `μ_n/(n+1) → 0`. -/
theorem tendsto_liClockReciprocalDegreeMean_div_atTop {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => μ z n / (n + 1)) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun η hη => ?_, fun η hη => ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact lt_of_lt_of_le hη (div_nonneg (by linarith [one_le_liClockReciprocalDegreeMean hz hn])
      (by positivity))
  · set ε := η / 4 with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (z ^ 2 * (3 + 1 / ε) ^ 2 / (8 * ε) + 10 / η)
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hnN : (N₀ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    set J := max 1 ⌈ε * n⌉₊ with hJdef
    have hJ1 : 1 ≤ J := le_max_left _ _
    have hJε : ε * n ≤ J := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have hJup : (J : ℝ) ≤ ε * n + 1 := by
      rcases le_total 1 ⌈ε * n⌉₊ with h | h
      · rw [hJdef, max_eq_right h]
        exact (Nat.ceil_lt_add_one (by positivity)).le
      · rw [hJdef, max_eq_left h]; push_cast; linarith [mul_pos hε hnpos]
    have hhalf : ∀ j, J ≤ j → w z n (j + 1) ≤ w z n j / 2 := by
      intro j hj
      have hj1 : 1 ≤ j := hJ1.trans hj
      have hjr : ε * n ≤ j := hJε.trans (by exact_mod_cast hj)
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hratio : (2 * (j : ℝ) + n + 1) ≤ (3 + 1 / ε) * j := by
        have : (n : ℝ) ≤ j / ε := by rw [le_div_iff₀ hε]; linarith
        have h1ε : (n : ℝ) ≤ (1 / ε) * j := by rw [one_div_mul_eq_div]; exact this
        nlinarith
      have hcoef : z ^ 2 * (2 * j + n + 1) ^ 2 / (16 * j ^ 3) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        have hsq : (2 * (j : ℝ) + n + 1) ^ 2 ≤ ((3 + 1 / ε) * j) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hratio 2
        have hbig : z ^ 2 * (3 + 1 / ε) ^ 2 / (8 * ε) ≤ n := by linarith [hN₀, hnN,
          (by positivity : (0 : ℝ) ≤ 10 / η)]
        rw [div_le_iff₀ (by positivity)] at hbig
        have hεn : 8 * ε * n ≤ 8 * j := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg z), sq_nonneg (3 + 1 / ε),
          mul_pos hj0 hj0]
      have := liClockReciprocalDegreeWeight_succ_index_le hz n hj1
      nlinarith [liClockReciprocalDegreeWeight_nonneg hz.le n j]
    have htail := tsum_mul_le_of_halving (liClockReciprocalDegreeWeight_nonneg hz.le n)
      (summable_liClockReciprocalDegreeWeight hz.le n)
      ((summable_pow_mul_liClockReciprocalDegreeWeight hz.le n 1).congr fun j => by simp) hhalf
    have hA := liClockReciprocalDegreeMass_pos hz n
    have hμ : μ z n ≤ 2 * J + 3 := by
      rw [liClockReciprocalDegreeMean_eq hz, sub_le_iff_le_add, div_le_iff₀ hA]
      have : ∑' j, w z n j = 𝒜 z n := rfl
      rw [this] at htail
      nlinarith
    have hn1' : (0 : ℝ) < n + 1 := by positivity
    rw [div_lt_iff₀ hn1']
    have h10 : 10 / η < n + 1 := by linarith [hN₀, hnN,
      (by positivity : (0 : ℝ) ≤ z ^ 2 * (3 + 1 / ε) ^ 2 / (8 * ε))]
    rw [div_lt_iff₀ hη] at h10
    nlinarith

/-! ## (A8) The raw ratios -/

/-- **(A8)** `a_{n+1}/a_n > z` for every `n ≥ 1`. -/
theorem lt_liClockReciprocalGermCoeff_succ_div {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 1 ≤ n) :
    z < a z (n + 1) / a z n := by
  have ha := liClockReciprocalGermCoeff_pos hz n
  have h := liClockReciprocalGermCoeff_succ_div hz n
  have hμ := one_le_liClockReciprocalDegreeMean hz hn
  rw [div_eq_iff (by positivity)] at h
  rw [lt_div_iff₀ ha, h]
  have : 0 < μ z n / (n + 1) := by positivity
  nlinarith [mul_pos this (mul_pos hz ha)]

/-- **(A8)** `a_{n+1}/a_n → z`. -/
theorem tendsto_liClockReciprocalGermCoeff_succ_div {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n => a z (n + 1) / a z n) atTop (𝓝 z) := by
  have h := ((tendsto_liClockReciprocalDegreeMean_div_atTop hz).const_add 1).const_mul z
  rw [add_zero, mul_one] at h
  refine h.congr fun n => ?_
  have ha := liClockReciprocalGermCoeff_pos hz n
  rw [← liClockReciprocalGermCoeff_succ_div hz n]
  field_simp

/-- **(A8)** `(n+1)(a_{n+1}/(z a_n) - 1) = μ_n → ∞`. -/
theorem liClockReciprocalGermCoeff_succ_div_correction {z : ℝ} (hz : 0 < z) :
    (∀ n : ℕ, ((n : ℝ) + 1) * (a z (n + 1) / (z * a z n) - 1) = μ z n) ∧
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (a z (n + 1) / (z * a z n) - 1)) atTop atTop := by
  have e : ∀ n : ℕ, ((n : ℝ) + 1) * (a z (n + 1) / (z * a z n) - 1) = μ z n := fun n => by
    rw [liClockReciprocalGermCoeff_succ_div hz n]
    field_simp
    ring
  exact ⟨e, (tendsto_liClockReciprocalDegreeMean_atTop hz).congr fun n => (e n).symm⟩

/-! ## (A9) The alternating composition form of the logarithmic coefficients -/

/-- The positive-degree part `F(X) = Σ_{k≥1} a_k X^k` of the raw germ. -/
def liClockReciprocalGermTail (z : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => if k = 0 then 0 else a z k

/-- The composition sum `Σ_{k_1+⋯+k_m = n} a_{k_1}⋯a_{k_m}` over `m` positive degrees: tuples with a
zero part contribute `0`. -/
def liClockReciprocalCompositionSum (z : ℝ) (m n : ℕ) : ℝ :=
  ∑ l ∈ (Finset.range m).finsuppAntidiag n,
    ∏ i ∈ Finset.range m, (if l i = 0 then 0 else a z (l i))

local notation "𝔽" => liClockReciprocalGermTail
local notation "b" => liClockReciprocalLogCoeff

theorem coeff_pow_liClockReciprocalGermTail (z : ℝ) (m n : ℕ) :
    PowerSeries.coeff n (𝔽 z ^ m) = liClockReciprocalCompositionSum z m n := by
  unfold liClockReciprocalCompositionSum
  rw [PowerSeries.coeff_pow]
  simp only [liClockReciprocalGermTail, PowerSeries.coeff_mk]

private theorem germTail_eq_X_mul (z : ℝ) :
    𝔽 z = PowerSeries.X * PowerSeries.mk fun k => a z (k + 1) := by
  ext k
  rcases k with _ | k
  · simp [liClockReciprocalGermTail]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [liClockReciprocalGermTail]

private theorem coeff_pow_germTail_of_lt (z : ℝ) {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (𝔽 z ^ m) = 0 := by
  rw [germTail_eq_X_mul, mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_mul_pow_germTail_of_lt (z : ℝ) (g : PowerSeries ℝ) {m n : ℕ} (h : n < m) :
    PowerSeries.coeff n (g * 𝔽 z ^ m) = 0 := by
  rw [germTail_eq_X_mul, mul_pow, mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_one_add_germTail (z : ℝ) (k : ℕ) :
    PowerSeries.coeff k (1 + 𝔽 z) = a z k := by
  rcases k with _ | k
  · simp [liClockReciprocalGermTail, liClockReciprocalGermCoeff_zero]
  · simp [liClockReciprocalGermTail, PowerSeries.coeff_one]

/-- The alternating composition coefficients `β_n = Σ_{m=1}^n ((-1)^{m+1}/m) [X^n] F^m`. -/
private def compLog (z : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 n, (-1 : ℝ) ^ (m + 1) / (m : ℝ) * PowerSeries.coeff n (𝔽 z ^ m)

private def logSeries (z : ℝ) (N : ℕ) : PowerSeries ℝ :=
  ∑ m ∈ Finset.Icc 1 N, PowerSeries.C ((-1 : ℝ) ^ (m + 1) / (m : ℝ)) * 𝔽 z ^ m

private theorem coeff_logSeries (z : ℝ) {N n : ℕ} (hn : n ≤ N) :
    PowerSeries.coeff n (logSeries z N) = compLog z n := by
  unfold logSeries compLog
  rw [map_sum]
  simp only [PowerSeries.coeff_C_mul]
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right hn) fun m hm hm' => ?_
  rw [coeff_pow_germTail_of_lt z (show n < m by
    simp only [Finset.mem_Icc, not_and, not_le] at hm hm'; exact hm' hm.1), mul_zero]

private theorem derivative_logSeries (z : ℝ) (N : ℕ) :
    PowerSeries.derivative ℝ (logSeries z N) =
      (∑ i ∈ Finset.range N, (-𝔽 z) ^ i) * PowerSeries.derivative ℝ (𝔽 z) := by
  unfold logSeries
  rw [map_sum, Finset.sum_mul]
  rw [show Finset.Icc 1 N = (Finset.range N).map ⟨(· + 1), add_left_injective 1⟩ by
    ext m; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk]; constructor
    · rintro ⟨h1, h2⟩; exact ⟨m - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C, smul_zero, add_zero,
    add_tsub_cancel_right, nsmul_eq_mul, smul_eq_mul, smul_eq_mul, neg_pow (𝔽 z)]
  have hi : ((i + 1 : ℕ) : PowerSeries ℝ) * PowerSeries.C ((-1 : ℝ) ^ (i + 1 + 1) / ((i + 1 : ℕ) : ℝ)) =
      (-1 : PowerSeries ℝ) ^ i := by
    rw [← map_natCast (PowerSeries.C (R := ℝ)), ← map_mul,
      show (-1 : PowerSeries ℝ) ^ i = PowerSeries.C ((-1 : ℝ) ^ i) by
        rw [map_pow, map_neg, map_one]]
    congr 1
    have : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  linear_combination (𝔽 z ^ i * PowerSeries.derivative ℝ (𝔽 z)) * hi

private theorem compLog_recurrence (z : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * a z (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (k + 1) * compLog z (k + 1) * a z (n - k) := by
  set N := n + 2
  have hgeom : (∑ i ∈ Finset.range N, (-𝔽 z) ^ i) * (1 + 𝔽 z) = 1 - (-𝔽 z) ^ N := by
    have h := geom_sum_mul (-𝔽 z) N
    linear_combination -h
  have key : PowerSeries.derivative ℝ (logSeries z N) * (1 + 𝔽 z) =
      PowerSeries.derivative ℝ (𝔽 z) - PowerSeries.derivative ℝ (𝔽 z) * (-𝔽 z) ^ N := by
    rw [derivative_logSeries, mul_right_comm, hgeom]
    ring
  have hc := congrArg (PowerSeries.coeff n) key
  have hz0 : PowerSeries.coeff n (PowerSeries.derivative ℝ (𝔽 z) * (-𝔽 z) ^ N) = 0 := by
    rw [neg_pow, ← mul_assoc]
    exact coeff_mul_pow_germTail_of_lt z _ (by omega)
  rw [map_sub, hz0, sub_zero, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (PowerSeries.derivative ℝ (logSeries z N)) *
        PowerSeries.coeff j (1 + 𝔽 z)) n] at hc
  simp only [PowerSeries.coeff_derivative, coeff_one_add_germTail] at hc
  have hF : PowerSeries.coeff (n + 1) (𝔽 z) = a z (n + 1) := by
    simp [liClockReciprocalGermTail]
  rw [hF] at hc
  rw [show ((n : ℝ) + 1) * a z (n + 1) = a z (n + 1) * (n + 1) by ring, ← hc]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coeff_logSeries z (show k + 1 ≤ N by have := Finset.mem_range.1 hk; omega)]
  ring

private theorem logCoeff_eq_compLog {z : ℝ} (hz : 0 < z) (m : ℕ) :
    b z (m + 1) = compLog z (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h1 := liClockReciprocalGermCoeff_recurrence hz m
    have h2 := compLog_recurrence z m
    rw [Finset.sum_range_succ] at h1 h2
    have hsame : ∑ k ∈ Finset.range m, ((k : ℝ) + 1) * b z (k + 1) * a z (m - k) =
        ∑ k ∈ Finset.range m, ((k : ℝ) + 1) * compLog z (k + 1) * a z (m - k) :=
      Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.1 hk)]
    rw [Nat.sub_self, liClockReciprocalGermCoeff_zero] at h1 h2
    have : ((m : ℝ) + 1) * b z (m + 1) = ((m : ℝ) + 1) * compLog z (m + 1) := by linarith
    exact mul_left_cancel₀ (by positivity) this

/-- **(A9)** For `n ≥ 1`,
`b_n = Σ_{m=1}^n ((-1)^{m+1}/m) Σ_{k_1+⋯+k_m = n, k_i ≥ 1} a_{k_1}⋯a_{k_m}`. -/
theorem liClockReciprocalLogCoeff_eq_compositionSum {z : ℝ} (hz : 0 < z) {n : ℕ} (hn : 1 ≤ n) :
    b z n = ∑ m ∈ Finset.Icc 1 n, (-1) ^ (m + 1) / m * liClockReciprocalCompositionSum z m n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [logCoeff_eq_compLog hz m]
  unfold compLog
  simp only [coeff_pow_liClockReciprocalGermTail]

end RHTower
