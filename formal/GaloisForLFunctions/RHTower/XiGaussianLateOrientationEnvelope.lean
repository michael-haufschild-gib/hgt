import GaloisForLFunctions.RHTower.XiGaussianThirdOrientationSaving

/-!
# A late-time orientation envelope uniform in polynomial coefficients

At half-time anchoring, the constant monomial has envelope ratio `96`.
Every higher monomial carries at least two further inverse powers of time.
A finite symbolic factorial sum controls the entire correction, for every
finite order. No coefficient or cross term is removed from the actual form.
-/

open scoped Real BigOperators
noncomputable section

namespace RHTower

def xiGaussianOrientationHalfOrderFactor (j : ℕ) : ℝ :=
  2 * (j : ℝ) ^ 2 + 8 * (2 * (j : ℝ) + 4) * (2 * (j : ℝ) + 3)

def xiGaussianOrientationHalfTailCap (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, xiGaussianOrientationHalfOrderFactor (j + 1) *
    ((2 * (j + 1) + 2).factorial : ℝ)

def xiGaussianOrientationLateTime (n : ℕ) : ℝ :=
  4 * (1 + xiGaussianOrientationHalfTailCap n)

theorem xiGaussianOrientationHalfOrderFactor_nonneg (j : ℕ) :
    0 ≤ xiGaussianOrientationHalfOrderFactor j := by
  unfold xiGaussianOrientationHalfOrderFactor
  positivity

theorem xiGaussianOrientationHalfTailCap_nonneg (n : ℕ) :
    0 ≤ xiGaussianOrientationHalfTailCap n :=
  Finset.sum_nonneg fun _ _ => mul_nonneg
    (xiGaussianOrientationHalfOrderFactor_nonneg _) (Nat.cast_nonneg _)

theorem four_le_xiGaussianOrientationLateTime (n : ℕ) :
    4 ≤ xiGaussianOrientationLateTime n := by
  unfold xiGaussianOrientationLateTime
  linarith only [xiGaussianOrientationHalfTailCap_nonneg n]

theorem xiGaussianOrientationMonomialEnvelope_half (j : ℕ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianOrientationMonomialEnvelope j (xiGaussianHalfHeat t) t =
      xiGaussianOrientationHalfOrderFactor j *
        (((2 * j + 2).factorial : ℝ) * (4 / (t : ℝ)) ^ (2 * j + 2)) := by
  have hfac (k : ℕ) : ((k + 2).factorial : ℝ) =
      ((k : ℝ) + 2) * ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [show k + 2 = k + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have ht : (t : ℝ) ^ 2 / 2 * (4 / (t : ℝ)) ^ 2 = 8 := by
    field_simp [t.property.ne']
    ring
  have hhalf : 2 / ((t : ℝ) / 2) = 4 / (t : ℝ) := by ring
  unfold xiGaussianOrientationMonomialEnvelope xiGaussianOrientationHalfOrderFactor
  change 2 * (j : ℝ) ^ 2 * _ * (2 / ((t : ℝ) / 2)) ^ _ +
    ((t : ℝ) ^ 2 / 2) * _ * (2 / ((t : ℝ) / 2)) ^ _ = _
  rw [hhalf, show 2 * j + 4 = (2 * j + 2) + 2 by omega, hfac (2 * j + 2),
    pow_add (4 / (t : ℝ)) (2 * j + 2) 2]
  push_cast
  calc
    _ = (2 * (j : ℝ) ^ 2 +
        (2 * (j : ℝ) + 4) * (2 * (j : ℝ) + 3) *
          ((t : ℝ) ^ 2 / 2 * (4 / (t : ℝ)) ^ 2)) *
            (((2 * j + 2).factorial : ℝ) * (4 / (t : ℝ)) ^ (2 * j + 2)) := by ring
    _ = _ := by rw [ht]; ring

/-- An explicit inverse-square correction to the order-independent leading ratio. -/
theorem xiGaussianOrientationEnvelope_half_le_correction (n : ℕ)
    (t : {t : ℝ // 4 ≤ t}) :
    xiGaussianOrientationEnvelope (n + 1)
        (xiGaussianHalfHeat ⟨t, by linarith only [t.property]⟩) t ≤
      (96 + xiGaussianOrientationHalfTailCap n * (4 / (t : ℝ)) ^ 2) *
        xiGaussianFourthTraceEnvelope (n + 1)
          (xiGaussianHalfHeat ⟨t, by linarith only [t.property]⟩) := by
  let t₀ : {t : ℝ // 0 < t} := ⟨t, by linarith only [t.property]⟩
  let r : ℝ := 4 / (t : ℝ)
  have ht : 0 < (t : ℝ) := t₀.property
  have hr : 0 ≤ r := div_nonneg (by positivity) ht.le
  have hr1 : r ≤ 1 := (div_le_one ht).mpr t.property
  let b₀ : ℝ := ((2 : ℕ).factorial : ℝ) * r ^ 2
  have hb₀ : r ^ 2 ≤ b₀ := by
    have hfac : (1 : ℝ) ≤ ((2 : ℕ).factorial : ℝ) :=
      by exact_mod_cast Nat.factorial_pos 2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfac (sq_nonneg r)
  have hbase : b₀ ≤ xiGaussianFourthTraceEnvelope (n + 1) (xiGaussianHalfHeat t₀) := by
    unfold xiGaussianFourthTraceEnvelope
    have h := Finset.single_le_sum
      (f := fun j : ℕ => ((2 * j + 2).factorial : ℝ) *
        (2 / ((xiGaussianHalfHeat t₀ : ℝ))) ^ (2 * j + 2))
      (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
        (div_nonneg (by positivity) (xiGaussianHalfHeat t₀).property.le) _))
      (show 0 ∈ Finset.range (n + 1) from Finset.mem_range.mpr (Nat.succ_pos n))
    simpa only [Nat.mul_zero, Nat.zero_add, xiGaussianHalfHeat, t₀, b₀, r,
      show 2 / ((t : ℝ) / 2) = 4 / (t : ℝ) by ring] using h
  have htail : (∑ j ∈ Finset.range n,
      xiGaussianOrientationMonomialEnvelope (j + 1) (xiGaussianHalfHeat t₀) t₀) ≤
        xiGaussianOrientationHalfTailCap n * r ^ 4 := by
    unfold xiGaussianOrientationHalfTailCap
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [xiGaussianOrientationMonomialEnvelope_half]
    have hp : r ^ (2 * (j + 1) + 2) ≤ r ^ 4 :=
      pow_le_pow_of_le_one hr hr1 (by omega)
    have h := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (xiGaussianOrientationHalfOrderFactor_nonneg (j + 1))
        (Nat.cast_nonneg ((2 * (j + 1) + 2).factorial)))
    simpa only [r, t₀, mul_assoc] using h
  have hzero : xiGaussianOrientationMonomialEnvelope 0 (xiGaussianHalfHeat t₀) t₀ =
      96 * b₀ := by
    rw [xiGaussianOrientationMonomialEnvelope_half]
    simp only [xiGaussianOrientationHalfOrderFactor, Nat.cast_zero, Nat.mul_zero, Nat.zero_add]
    dsimp only [b₀, r, t₀]
    ring
  have hsplit : xiGaussianOrientationEnvelope (n + 1) (xiGaussianHalfHeat t₀) t₀ =
      (∑ j ∈ Finset.range n,
        xiGaussianOrientationMonomialEnvelope (j + 1) (xiGaussianHalfHeat t₀) t₀) +
          96 * b₀ := by
    unfold xiGaussianOrientationEnvelope
    rw [Finset.sum_range_succ', hzero]
  have htail' : xiGaussianOrientationHalfTailCap n * r ^ 4 ≤
      (xiGaussianOrientationHalfTailCap n * r ^ 2) *
        xiGaussianFourthTraceEnvelope (n + 1) (xiGaussianHalfHeat t₀) := by
    have h := mul_le_mul_of_nonneg_left (hb₀.trans hbase)
      (mul_nonneg (xiGaussianOrientationHalfTailCap_nonneg n) (sq_nonneg r))
    nlinarith only [h]
  change xiGaussianOrientationEnvelope (n + 1) (xiGaussianHalfHeat t₀) t₀ ≤ _
  rw [hsplit]
  nlinarith only [htail, htail', hbase]

/-- The explicit late-time threshold suppresses the entire higher-degree correction. -/
theorem xiGaussianOrientationHalf_correction_le_one (n : ℕ)
    (t : {t : ℝ // xiGaussianOrientationLateTime n ≤ t}) :
    xiGaussianOrientationHalfTailCap n * (4 / (t : ℝ)) ^ 2 ≤ 1 := by
  have h4 : 4 ≤ (t : ℝ) := (four_le_xiGaussianOrientationLateTime n).trans t.property
  have ht : 0 < (t : ℝ) := by linarith only [h4]
  have hr : 0 ≤ 4 / (t : ℝ) := div_nonneg (by positivity) ht.le
  have hr1 : 4 / (t : ℝ) ≤ 1 := (div_le_one ht).mpr h4
  have hprod : xiGaussianOrientationHalfTailCap n * (4 / (t : ℝ)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one ht]
    have h := t.property
    unfold xiGaussianOrientationLateTime at h
    linarith only [h]
  have h := mul_le_mul_of_nonneg_right hprod hr
  nlinarith only [h, hr1]

/-- A single order-independent ratio works beyond an explicit order-dependent heat time. -/
theorem xiGaussianOrientationEnvelope_half_late_le (n : ℕ)
    (t : {t : ℝ // xiGaussianOrientationLateTime n ≤ t}) :
    xiGaussianOrientationEnvelope (n + 1)
        (xiGaussianHalfHeat ⟨t, lt_of_lt_of_le (by positivity)
          ((four_le_xiGaussianOrientationLateTime n).trans t.property)⟩) t ≤
      97 * xiGaussianFourthTraceEnvelope (n + 1)
        (xiGaussianHalfHeat ⟨t, lt_of_lt_of_le (by positivity)
          ((four_le_xiGaussianOrientationLateTime n).trans t.property)⟩) := by
  have h4 := (four_le_xiGaussianOrientationLateTime n).trans t.property
  have h := xiGaussianOrientationEnvelope_half_le_correction n ⟨t, h4⟩
  have hc := xiGaussianOrientationHalf_correction_le_one n t
  have hb := xiGaussianFourthTraceEnvelope_nonneg (n + 1)
    (xiGaussianHalfHeat ⟨t, lt_of_lt_of_le (by positivity) h4⟩)
  have hp := mul_le_mul_of_nonneg_right (show
      96 + xiGaussianOrientationHalfTailCap n * (4 / (t : ℝ)) ^ 2 ≤ 97
        by linarith only [hc]) hb
  exact h.trans hp

end RHTower
