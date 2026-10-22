import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# Variation bound for the clipped Möbius kernel

The dilation weight is the minimum of a rising square-root profile and a falling,
zero-clipped profile. Capping both at their common envelope controls total variation
without deleting the incomplete terminal block.
-/

noncomputable section

namespace RHTower

open Finset

private theorem sum_min_variation_le (f g : ℕ → ℝ)
    (hf : Monotone f) (hg : Antitone g) (D : ℕ) :
    (∑ d ∈ Icc 1 D, |min (f d) (g d) - min (f (d + 1)) (g (d + 1))|) ≤
      f (D + 1) - f 1 + g 1 - g (D + 1) := by
  have hstep (d : ℕ) :
      |min (f d) (g d) - min (f (d + 1)) (g (d + 1))| ≤
        (f (d + 1) - f d) + (g d - g (d + 1)) := by
    have hfu := hf (Nat.le_succ d)
    have hgd := hg (Nat.le_succ d)
    have h := abs_min_sub_min_le_max (f d) (g d) (f (d + 1)) (g (d + 1))
    rw [abs_of_nonpos (sub_nonpos.mpr hfu), abs_of_nonneg (sub_nonneg.mpr hgd)] at h
    exact h.trans (max_le (by linarith) (by linarith))
  induction D with
  | zero => simp
  | succ D ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ D + 1)]
      have h := hstep (D + 1)
      linarith

/-- The physical tent is a rising profile clipped by its falling endpoint profile. -/
theorem mobiusDilationTentWeight_eq_min (M q d : ℕ) (hq : 1 ≤ q) :
    mobiusDilationTentWeight M q d =
      min (Real.sqrt d * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q))
        (max 0 (Real.sqrt M - Real.sqrt q * Real.sqrt d)) := by
  have ha : 0 ≤ Real.sqrt (q + 1 : ℕ) - Real.sqrt q :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ q))
  have hprod : Real.sqrt (q * d : ℕ) = Real.sqrt q * Real.sqrt d := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg q)]
  have hprod' : Real.sqrt ((q + 1) * d : ℕ) =
      Real.sqrt (q + 1 : ℕ) * Real.sqrt d := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg (q + 1))]
  by_cases hd : 1 ≤ d
  · by_cases hqd : q * d ≤ M - 1
    · have hM : 1 ≤ M := by
        have := Nat.mul_pos (by omega : 0 < q) (by omega : 0 < d)
        omega
      have hv : 0 ≤ Real.sqrt M - Real.sqrt q * Real.sqrt d := by
        rw [← hprod]
        exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast (show q * d ≤ M by omega)))
      rw [mobiusDilationTentWeight, if_pos ⟨hd, hqd⟩, max_eq_right hv]
      by_cases hfull : (q + 1) * d ≤ M
      · rw [divisorDilationClippedAbelWeight_eq_full hd hq hfull, min_eq_left]
        have h := Real.sqrt_le_sqrt (by exact_mod_cast hfull :
          (((q + 1) * d : ℕ) : ℝ) ≤ M)
        rw [hprod'] at h
        nlinarith
      · have hterm : M < (q + 1) * d := by omega
        rw [divisorDilationClippedAbelWeight_eq_terminal hd hq hqd hterm,
          hprod, min_eq_right]
        have h := Real.sqrt_le_sqrt (by exact_mod_cast hterm.le :
          (M : ℝ) ≤ ((q + 1) * d : ℕ))
        rw [hprod'] at h
        nlinarith
    · have hv : Real.sqrt M - Real.sqrt q * Real.sqrt d ≤ 0 := by
        rw [← hprod]
        exact sub_nonpos.mpr (Real.sqrt_le_sqrt (by exact_mod_cast (show M ≤ q * d by omega)))
      rw [mobiusDilationTentWeight, if_neg (by tauto), max_eq_left hv,
        min_eq_right (mul_nonneg (Real.sqrt_nonneg _) ha)]
  · have hd0 : d = 0 := by omega
    simp [hd0, mobiusDilationTentWeight, Real.sqrt_nonneg]

/-- The full and clipped pieces share the envelope `sqrt M / q`. -/
theorem mobiusDilationTentWeight_le (M q d : ℕ) (hq : 1 ≤ q) :
    mobiusDilationTentWeight M q d ≤ Real.sqrt M / q := by
  rw [mobiusDilationTentWeight_eq_min M q d hq]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ha : 0 ≤ Real.sqrt (q + 1 : ℕ) - Real.sqrt q :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ q))
  by_cases hv : Real.sqrt M - Real.sqrt q * Real.sqrt d ≤ 0
  · rw [max_eq_left hv, min_eq_right (mul_nonneg (Real.sqrt_nonneg _) ha)]
    positivity
  · rw [max_eq_right (by linarith : 0 ≤ Real.sqrt M - Real.sqrt q * Real.sqrt d)]
    have hroot : Real.sqrt q * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q) ≤ 1 := by
      have hq := Real.sq_sqrt (Nat.cast_nonneg q)
      have hq1 := Real.sq_sqrt (Nat.cast_nonneg (q + 1))
      have hp := mul_nonneg (Real.sqrt_nonneg (q + 1 : ℕ)) ha
      have hcast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by simp
      nlinarith
    apply (le_div_iff₀ hq0).2
    calc
      min (Real.sqrt d * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q))
          (Real.sqrt M - Real.sqrt q * Real.sqrt d) * q ≤
          (Real.sqrt d * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q)) * q :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hq0.le
      _ = (Real.sqrt q * Real.sqrt d) *
          (Real.sqrt q * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q)) := by
        calc
          _ = (Real.sqrt d * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q)) *
              Real.sqrt q ^ 2 :=
            congrArg (fun x : ℝ =>
              (Real.sqrt d * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q)) * x)
              (Real.sq_sqrt (Nat.cast_nonneg q)).symm
          _ = _ := by ring
      _ ≤ Real.sqrt q * Real.sqrt d := by
        simpa using mul_le_mul_of_nonneg_left hroot
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ ≤ Real.sqrt M := by linarith

/-- Total variation includes the escaped zero coefficient at the physical upper edge. -/
theorem sum_abs_mobiusDilationTentWeight_sub_succ_le (M q D : ℕ) (hq : 1 ≤ q) :
    (∑ d ∈ Icc 1 D,
      |mobiusDilationTentWeight M q d - mobiusDilationTentWeight M q (d + 1)|) ≤
      2 * Real.sqrt M / q := by
  let U : ℝ := Real.sqrt M / q
  let f : ℕ → ℝ := fun d =>
    min (Real.sqrt d * (Real.sqrt (q + 1 : ℕ) - Real.sqrt q)) U
  let g : ℕ → ℝ := fun d =>
    min (max 0 (Real.sqrt M - Real.sqrt q * Real.sqrt d)) U
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have ha : 0 ≤ Real.sqrt (q + 1 : ℕ) - Real.sqrt q :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ q))
  have hf : Monotone f := by
    intro a b hab
    exact min_le_min (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by exact_mod_cast hab)) ha) le_rfl
  have hg : Antitone g := by
    intro a b hab
    apply min_le_min _ le_rfl
    apply max_le_max le_rfl
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hab)) (Real.sqrt_nonneg q)) _
  have heq (d : ℕ) : mobiusDilationTentWeight M q d = min (f d) (g d) := by
    dsimp [f, g]
    rw [min_min_min_comm, min_self, ← mobiusDilationTentWeight_eq_min M q d hq,
      min_eq_left (mobiusDilationTentWeight_le M q d hq)]
  simp_rw [heq]
  have hvar := sum_min_variation_le f g hf hg D
  have hf0 : 0 ≤ f 1 := le_min (mul_nonneg (Real.sqrt_nonneg _) ha) hU
  have hg0 : 0 ≤ g (D + 1) := le_min (le_max_left _ _) hU
  have hfU : f (D + 1) ≤ U := min_le_right _ _
  have hgU : g 1 ≤ U := min_le_right _ _
  calc
    _ ≤ 2 * U := by linarith
    _ = _ := by dsimp [U]; ring

/-- Maximum of the actual Mertens partial sums on the finite dilation range. -/
def mobiusDilationMertensEnvelope (D : ℕ) : ℝ :=
  (Icc 0 D).sup' ⟨0, by simp⟩
    (fun d => |∑ k ∈ Icc 1 d, ((ArithmeticFunction.moebius k : ℤ) : ℝ)|)

theorem abs_mertensSum_le_mobiusDilationMertensEnvelope {d D : ℕ} (hd : d ≤ D) :
    |∑ k ∈ Icc 1 d, ((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤
      mobiusDilationMertensEnvelope D :=
  Finset.le_sup' (f := fun d =>
    |∑ k ∈ Icc 1 d, ((ArithmeticFunction.moebius k : ℤ) : ℝ)|)
    (by simp [hd] : d ∈ Icc 0 D)

theorem mobiusDilationMertensEnvelope_nonneg (D : ℕ) :
    0 ≤ mobiusDilationMertensEnvelope D := by
  simpa using abs_mertensSum_le_mobiusDilationMertensEnvelope (Nat.zero_le D)

/-- Abel summation bounds the signed kernel by its actual finite Mertens envelope. -/
theorem abs_mobiusClippedAbelKernel_le_envelope (M q : ℕ) (hq : 1 ≤ q) :
    |mobiusClippedAbelKernel M q| ≤
      2 * mobiusDilationMertensEnvelope ((M - 1) / q) * Real.sqrt M / q := by
  rw [mobiusClippedAbelKernel_eq_mertensGradient hq]
  calc
    _ ≤ ∑ d ∈ Icc 1 ((M - 1) / q),
        |(∑ k ∈ Icc 1 d, ((ArithmeticFunction.moebius k : ℤ) : ℝ)) *
          (mobiusDilationTentWeight M q d - mobiusDilationTentWeight M q (d + 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 ((M - 1) / q),
        mobiusDilationMertensEnvelope ((M - 1) / q) *
          |mobiusDilationTentWeight M q d - mobiusDilationTentWeight M q (d + 1)| := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (abs_mertensSum_le_mobiusDilationMertensEnvelope (mem_Icc.mp hd).2)
        (abs_nonneg _)
    _ = mobiusDilationMertensEnvelope ((M - 1) / q) *
        ∑ d ∈ Icc 1 ((M - 1) / q),
          |mobiusDilationTentWeight M q d - mobiusDilationTentWeight M q (d + 1)| :=
      (mul_sum _ _ _).symm
    _ ≤ mobiusDilationMertensEnvelope ((M - 1) / q) * (2 * Real.sqrt M / q) :=
      mul_le_mul_of_nonneg_left
        (sum_abs_mobiusDilationTentWeight_sub_succ_le M q ((M - 1) / q) hq)
        (mobiusDilationMertensEnvelope_nonneg _)
    _ = _ := by ring

end RHTower
