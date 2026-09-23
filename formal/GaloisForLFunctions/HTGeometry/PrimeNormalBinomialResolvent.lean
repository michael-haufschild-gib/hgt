import Mathlib

/-!
# The prime-only normal profile and its binomial resolvent

The differentiated prime-only physical boundary normal equation

`(2L − t) F'(L) + F(L) = 0`

has, in the spectral coordinate, the explicit solution `F_β(L) = β (L − t/2)^{−1/2}`, whose
half-log trace is `β` exactly.  Expanding the square root produces the central binomial
coefficients graded by `8^{-k}`, which is the card's resolvent expansion.
-/

open Filter Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The prime-only normal profile with half-log trace `β`, in the scalar spectral coordinate. -/
noncomputable def primeNormalProfile (t β L : ℝ) : ℝ := β * (L - t / 2) ^ (-(1:ℝ)/2)

/-- **The profile solves the differentiated prime-only normal equation `(1)`.** -/
theorem hasDerivAt_primeNormalProfile {t β L : ℝ} (hL : t / 2 < L) :
    HasDerivAt (primeNormalProfile t β)
      (-(β / 2) * (L - t / 2) ^ (-(3:ℝ)/2)) L := by
  have hpos : (0:ℝ) < L - t / 2 := by linarith
  have hbase : HasDerivAt (fun x : ℝ => x - t / 2) 1 L := by
    simpa using (hasDerivAt_id L).sub_const (t / 2)
  have h := (Real.hasDerivAt_rpow_const (p := -(1:ℝ)/2) (Or.inl (ne_of_gt hpos))).comp L hbase
  have hval : (-(1:ℝ)/2 * (L - t/2) ^ (-(1:ℝ)/2 - 1)) * 1
      = -(1/2) * (L - t / 2) ^ (-(3:ℝ)/2) := by
    norm_num
  rw [hval] at h
  have hfin := h.const_mul β
  have hv : β * (-(1/2) * (L - t / 2) ^ (-(3:ℝ)/2))
      = -(β / 2) * (L - t / 2) ^ (-(3:ℝ)/2) := by ring
  rw [hv] at hfin
  exact hfin

/-- **The equation `(1)` holds:** `(2L − t) F' + F = 0`. -/
theorem primeNormalProfile_equation {t β L : ℝ} (hL : t / 2 < L) :
    (2 * L - t) * (-(β / 2) * (L - t / 2) ^ (-(3:ℝ)/2)) + primeNormalProfile t β L = 0 := by
  have hpos : (0:ℝ) < L - t / 2 := by linarith
  unfold primeNormalProfile
  have hrw : (L - t / 2) * (L - t / 2) ^ (-(3:ℝ)/2) = (L - t / 2) ^ (-(1:ℝ)/2) := by
    nth_rewrite 1 [← Real.rpow_one (L - t / 2)]
    rw [← Real.rpow_add hpos]
    norm_num
  rw [← hrw]
  ring

/-- **The half-log trace of the profile is `β`**, the card's `(3)`. -/
theorem tendsto_sqrt_mul_primeNormalProfile (t β : ℝ) :
    Tendsto (fun L => Real.sqrt L * primeNormalProfile t β L) atTop (nhds β) := by
  have hratio : Tendsto (fun L : ℝ => (L - t / 2) / L) atTop (nhds 1) := by
    have h : Tendsto (fun L : ℝ => 1 - (t / 2) / L) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub (Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    field_simp
  have hsq : Tendsto (fun L : ℝ => Real.sqrt ((L - t / 2) / L)) atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hratio
    rwa [Real.sqrt_one] at h
  have hinv : Tendsto (fun L : ℝ => (Real.sqrt ((L - t / 2) / L))⁻¹) atTop (nhds 1) := by
    have h := hsq.inv₀ (by norm_num)
    rwa [inv_one] at h
  have hfin := hinv.const_mul β
  rw [mul_one] at hfin
  refine hfin.congr' ?_
  filter_upwards [eventually_gt_atTop (max (0:ℝ) (t / 2))] with L hL
  have hL0 : (0:ℝ) < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hLt : t / 2 < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hpos : (0:ℝ) < L - t / 2 := by linarith
  unfold primeNormalProfile
  have hp : (L - t / 2) ^ (-(1:ℝ)/2) = (Real.sqrt (L - t / 2))⁻¹ := by
    rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hpos.le, Real.sqrt_eq_rpow]
  have hs : Real.sqrt ((L - t / 2) / L) = Real.sqrt (L - t / 2) / Real.sqrt L :=
    Real.sqrt_div hpos.le L
  have hsq1 : 0 < Real.sqrt (L - t / 2) := Real.sqrt_pos.mpr hpos
  have hsq2 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  rw [hp, hs]
  field_simp


/-- The binomial expansion coefficient of the card's `(4)`. -/
noncomputable def primeNormalCoeff (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) / 8 ^ k

theorem primeNormalCoeff_zero : primeNormalCoeff 0 = 1 := by
  unfold primeNormalCoeff
  simp [Nat.centralBinom]

theorem primeNormalCoeff_pos (k : ℕ) : 0 < primeNormalCoeff k := by
  unfold primeNormalCoeff
  have h := Nat.centralBinom_pos k
  positivity

/-- The coefficients are `binom(2k,k)/4^k` scaled by `2^{-k}`, matching `(4)`'s `L^{-k}` grading. -/
theorem primeNormalCoeff_eq (k : ℕ) :
    primeNormalCoeff k = ((Nat.centralBinom k : ℝ) / 4 ^ k) * (1 / 2) ^ k := by
  unfold primeNormalCoeff
  rw [show (8:ℝ) = 4 * 2 by norm_num, mul_pow]
  field_simp
  rw [mul_assoc, ← mul_pow, show (2:ℝ) * (1/2) = 1 by norm_num, one_pow, mul_one]


/-- The `Ring.choose` successor identity in a characteristic-zero field. -/
theorem ringChoose_succ (r : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.choose r (n + 1) = Ring.choose r n * (r - n) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose (R := ℝ) r (n + 1)
  have h2 := Ring.descPochhammer_eq_factorial_smul_choose (R := ℝ) r n
  rw [descPochhammer_succ_right, smeval_mul, smeval_sub, smeval_X, smeval_natCast, h2] at h1
  rw [Nat.factorial_succ] at h1
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_succ, npow_one] at h1
  have hfac : ((Nat.factorial n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp at h1 ⊢
  nlinarith [h1]

/-- **The half-integer binomial coefficient is the central binomial coefficient.**  This is the
coefficient identity behind the card's `(13)`. -/
theorem ringChoose_neg_half_primeNormalBinomialResolvent (n : ℕ) :
    Ring.choose (-(1 : ℝ) / 2) n = (-1) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ih =>
      have hstep := ringChoose_succ (-(1 : ℝ) / 2) n
      rw [ih] at hstep
      have hcb : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
          = 2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by
        have := Nat.succ_mul_centralBinom_succ n
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
      have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
      field_simp at hstep ⊢
      refine mul_left_cancel₀ (show ((n : ℝ) + 1) * 2 ≠ 0 by positivity) ?_
      linear_combination (4 : ℝ) * hstep - 2 * (-1 : ℝ) ^ (n + 1) * hcb

/-- **The central binomial series `(13)`:** `(1 − z)^(−1/2) = Σ binom(2k,k) z^k / 4^k`. -/
theorem hasSum_centralBinom_rpow {z : ℝ} (hz : |z| < 1) :
    HasSum (fun k : ℕ => (Nat.centralBinom k : ℝ) / 4 ^ k * z ^ k) ((1 - z) ^ (-(1 : ℝ) / 2)) := by
  have hball := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -(1 : ℝ) / 2)
  have hmem : (-z : ℝ) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right]
    simpa [enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] using hz
  have hs := hball.hasSum hmem
  simp only [zero_add] at hs
  have hsq : ((-1 : ℝ)) ^ 0 = 1 := by norm_num
  have hcoef : ∀ n : ℕ, (binomialSeries ℝ (-(1 : ℝ) / 2)) n (fun _ => (-z))
      = (Nat.centralBinom n : ℝ) / 4 ^ n * z ^ n := by
    intro n
    rw [binomialSeries_apply]
    have hp : ((List.ofFn (fun _ : Fin n => (-z))).prod) = (-z) ^ n := by simp
    have hneg : ((-z : ℝ)) ^ n = (-1) ^ n * z ^ n := by rw [← neg_one_mul, mul_pow]
    rw [hp, smul_eq_mul, ringChoose_neg_half_primeNormalBinomialResolvent, hneg]
    have hone : ((-1 : ℝ)) ^ n * ((-1 : ℝ)) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc (-1 : ℝ) ^ n * (Nat.centralBinom n : ℝ) / 4 ^ n * ((-1) ^ n * z ^ n)
        = ((-1 : ℝ) ^ n * (-1) ^ n) * ((Nat.centralBinom n : ℝ) / 4 ^ n * z ^ n) := by ring
      _ = (Nat.centralBinom n : ℝ) / 4 ^ n * z ^ n := by rw [hone, one_mul]
  simp only [hcoef] at hs
  rwa [show (1 : ℝ) + -z = 1 - z by ring] at hs


/-- **The grade recurrence `(14)`:** `theta_(k+1)/theta_k = (2k+1)/(4k+4)`. -/
theorem primeNormalCoeff_succ (k : ℕ) :
    (4 * (k : ℝ) + 4) * primeNormalCoeff (k + 1) = (2 * k + 1) * primeNormalCoeff k := by
  have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
      = 2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by
    have := Nat.succ_mul_centralBinom_succ k
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) this
  unfold primeNormalCoeff
  have h8 : (8 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  linear_combination (8 : ℝ) ^ k * 4 * hcb

/-- `theta_1 = 1/4`, the card's `(16)`. -/
theorem primeNormalCoeff_one : primeNormalCoeff 1 = 1 / 4 := by
  unfold primeNormalCoeff
  norm_num [Nat.centralBinom]

/-- **The uniform majorant `(16)`:** `theta_k <= 2^(-k)`. -/
theorem primeNormalCoeff_le_two_pow (k : ℕ) : primeNormalCoeff k ≤ (1 / 2 : ℝ) ^ k := by
  unfold primeNormalCoeff
  have hcb : (Nat.centralBinom k : ℝ) ≤ 4 ^ k := by
    exact_mod_cast Nat.centralBinom_le_four_pow k
  rw [div_le_iff₀ (by positivity)]
  calc (Nat.centralBinom k : ℝ) ≤ 4 ^ k := hcb
    _ = (1 / 2 : ℝ) ^ k * 8 ^ k := by
        rw [← mul_pow]; norm_num

/-- **The grade sum `(19)`:** `sum theta_k (M/L)^k = (1 - M/(2L))^(-1/2)`. -/
theorem hasSum_primeNormalCoeff {M L : ℝ} (hM : 0 ≤ M) (hL : M / 2 < L) :
    HasSum (fun k : ℕ => primeNormalCoeff k * (M / L) ^ k)
      ((1 - M / (2 * L)) ^ (-(1 : ℝ) / 2)) := by
  have hL0 : 0 < L := by linarith
  have hz : |M / (2 * L)| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one (by positivity)]
    linarith
  have h := hasSum_centralBinom_rpow hz
  have heq : ∀ k : ℕ, (Nat.centralBinom k : ℝ) / 4 ^ k * (M / (2 * L)) ^ k
      = primeNormalCoeff k * (M / L) ^ k := by
    intro k
    unfold primeNormalCoeff
    rw [div_pow, div_pow, mul_pow]
    field_simp
    rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
    ring
  simpa only [heq] using h


end GaloisForLFunctions.HTGeometry
