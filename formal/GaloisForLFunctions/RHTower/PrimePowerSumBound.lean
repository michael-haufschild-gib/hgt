import GaloisForLFunctions.RHTower.PrimeShellWeightedSum

/-!
# The sub-critical prime power sum

`∑_{p ≤ Y} (log p) p^{−β} ≪_β Y^{1−β}` for `0 < β < 1`, with an explicit constant.

The proof is a halving induction: the top shell `(Y/2, Y]` contributes at most
`(Y/2)^{−β}·θ(Y) ≤ C 2^β Y^{1−β}`, and the rest is the same statement at `Y/2`, which costs a factor
`2^{β−1} < 1`.  No Abel summation and no differentiability of the weight are needed.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Chebyshev's `θ` is monotone. -/
theorem chebyshevTheta_mono : Monotone Chebyshev.theta := by
  intro x y hxy
  rw [Chebyshev.theta, Chebyshev.theta]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · refine Finset.filter_subset_filter _ ?_
    exact Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxy)
  · intro p hp _
    rw [Finset.mem_filter] at hp
    exact log_nonneg_of_prime hp.2

theorem chebyshevTheta_nonneg (x : ℝ) : 0 ≤ Chebyshev.theta x := by
  refine Finset.sum_nonneg fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact log_nonneg_of_prime hp.2

/-- **The Chebyshev linear bound for `θ`.** -/
theorem exists_chebyshevTheta_le_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → Chebyshev.theta x ≤ C * x := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (chebyshevTheta_eventually_relative one_pos)
  refine ⟨max 2 (Chebyshev.theta (max X₁ 1) + 1), by positivity, fun x hx => ?_⟩
  set C : ℝ := max 2 (Chebyshev.theta (max X₁ 1) + 1) with hC
  have hC2 : (2 : ℝ) ≤ C := le_max_left _ _
  have hCθ : Chebyshev.theta (max X₁ 1) + 1 ≤ C := le_max_right _ _
  rcases le_or_gt (max X₁ 1) x with hbig | hsmall
  · have hX : X₁ ≤ x := le_trans (le_max_left _ _) hbig
    have hb := hX₁ x hX
    rw [abs_le] at hb
    have : Chebyshev.theta x ≤ 2 * x := by linarith [hb.2]
    nlinarith [this, hC2, hx]
  · have hmono := chebyshevTheta_mono hsmall.le
    have : Chebyshev.theta x ≤ C := by linarith [hmono, hCθ]
    nlinarith [this, hx, hC2]

/-- **The sub-critical prime power sum.** -/
theorem exists_primeLogSum_rpow_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℝ, 0 ≤ Y →
      primeLogSum (fun t : ℝ => t ^ (-β)) 0 Y ≤ K * Y ^ (1 - β) := by
  obtain ⟨C, hC0, hC⟩ := exists_chebyshevTheta_le_linear
  have hq : (0 : ℝ) < 1 - (2 : ℝ) ^ (β - 1) := by
    have : (2 : ℝ) ^ (β - 1) < 1 := by
      refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  set K : ℝ := C * (2 : ℝ) ^ β / (1 - (2 : ℝ) ^ (β - 1)) with hK
  have h2β : (0 : ℝ) < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  have hK0 : 0 < K := by rw [hK]; positivity
  have hKrec : C * (2 : ℝ) ^ β + K * (2 : ℝ) ^ (β - 1) ≤ K := by
    rw [hK]
    field_simp
    nlinarith [hq, h2β, hC0]
  refine ⟨K, hK0, ?_⟩
  intro Y
  induction' hn : ⌊Y⌋₊ using Nat.strong_induction_on with n ih generalizing Y
  intro hY0
  rcases lt_or_ge Y 2 with hsmall | hbig
  · have hfl : ⌊Y⌋₊ ≤ 1 := by
      have h2 : Y < ((2 : ℕ) : ℝ) := by push_cast; linarith
      have := (Nat.floor_lt hY0).2 h2
      omega
    have hempty : (Finset.Ioc 0 ⌊Y⌋₊).filter (fun p => Nat.Prime p) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun p hp => ?_
      rw [Finset.mem_Ioc] at hp
      intro hprime
      have : 2 ≤ p := hprime.two_le
      omega
    have hzero : primeLogSum (fun t : ℝ => t ^ (-β)) 0 Y = 0 := by
      rw [primeLogSum, Nat.floor_zero, hempty, Finset.sum_empty]
    rw [hzero]
    positivity
  · -- split off the top shell
    have hY0' : (0 : ℝ) < Y := by linarith
    have hhalf : (0 : ℝ) ≤ Y / 2 := by linarith
    have hfl1 : ⌊(0 : ℝ)⌋₊ ≤ ⌊Y / 2⌋₊ := by simp
    have hfl2 : ⌊Y / 2⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono (by linarith)
    have hsplit := primeLogSum_add (f := fun t : ℝ => t ^ (-β)) hfl1 hfl2
    -- the top shell
    have hshell : primeLogSum (fun t : ℝ => t ^ (-β)) (Y / 2) Y
        ≤ (Y / 2) ^ (-β) * (Chebyshev.theta Y - Chebyshev.theta (Y / 2)) := by
      refine primeLogSum_le hhalf hfl2 fun p hprime h1 h2 => ?_
      exact Real.rpow_le_rpow_of_nonpos (by linarith) h1.le (by linarith)
    have hθ : Chebyshev.theta Y - Chebyshev.theta (Y / 2) ≤ C * Y := by
      have h1 := hC Y (by linarith)
      have h2 := chebyshevTheta_nonneg (Y / 2)
      linarith
    have hhalfpow : (Y / 2) ^ (-β) = (2 : ℝ) ^ β * Y ^ (-β) := by
      rw [Real.div_rpow hY0'.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    have htop : primeLogSum (fun t : ℝ => t ^ (-β)) (Y / 2) Y
        ≤ C * (2 : ℝ) ^ β * Y ^ (1 - β) := by
      have hnn : (0 : ℝ) ≤ (Y / 2) ^ (-β) := Real.rpow_nonneg hhalf _
      have hstep : (Y / 2) ^ (-β) * (Chebyshev.theta Y - Chebyshev.theta (Y / 2))
          ≤ (Y / 2) ^ (-β) * (C * Y) := by
        exact mul_le_mul_of_nonneg_left hθ hnn
      have hYm : Y ^ (-β) * Y = Y ^ (1 - β) := by
        have hadd := Real.rpow_add hY0' (-β) 1
        rw [Real.rpow_one] at hadd
        rw [show (1 : ℝ) - β = -β + 1 by ring, hadd]
      have hid : (Y / 2) ^ (-β) * (C * Y) = C * (2 : ℝ) ^ β * Y ^ (1 - β) := by
        rw [hhalfpow, ← hYm]
        ring
      linarith [hshell, hstep, hid.le, hid.ge]
    -- the induction hypothesis at `Y/2`
    have hlt : ⌊Y / 2⌋₊ < n := by
      have h1 : 1 ≤ ⌊Y / 2⌋₊ := Nat.le_floor (by norm_num; linarith)
      have h2 : 2 * ⌊Y / 2⌋₊ ≤ ⌊Y⌋₊ := by
        refine Nat.le_floor ?_
        have := Nat.floor_le hhalf
        push_cast
        linarith
      omega
    have hrec := ih ⌊Y / 2⌋₊ hlt (Y / 2) rfl hhalf
    have hhalfpow2 : (Y / 2) ^ (1 - β) = (2 : ℝ) ^ (β - 1) * Y ^ (1 - β) := by
      rw [Real.div_rpow hY0'.le (by norm_num),
        show β - 1 = -(1 - β) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    rw [hhalfpow2] at hrec
    have hYpow : (0 : ℝ) ≤ Y ^ (1 - β) := Real.rpow_nonneg hY0'.le _
    calc primeLogSum (fun t : ℝ => t ^ (-β)) 0 Y
        = primeLogSum (fun t : ℝ => t ^ (-β)) 0 (Y / 2)
          + primeLogSum (fun t : ℝ => t ^ (-β)) (Y / 2) Y := hsplit.symm
      _ ≤ K * ((2 : ℝ) ^ (β - 1) * Y ^ (1 - β)) + C * (2 : ℝ) ^ β * Y ^ (1 - β) :=
          add_le_add hrec htop
      _ = (K * (2 : ℝ) ^ (β - 1) + C * (2 : ℝ) ^ β) * Y ^ (1 - β) := by ring
      _ ≤ K * Y ^ (1 - β) := by
          refine mul_le_mul_of_nonneg_right ?_ hYpow
          linarith [hKrec]

end

end RHTower
