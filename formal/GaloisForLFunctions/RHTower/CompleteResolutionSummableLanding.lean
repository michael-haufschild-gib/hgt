import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution
import GaloisForLFunctions.RHTower.HighExponentShellLeastAtomAsymptotic

/-!
# Summable landing of the complete positive zeta resolution

The complete positive resolution was previously known to telescope locally normally to one.
The least-prime shell asymptotic gives more: at every point of the open right half-plane its
channel vector is absolutely summable.  Thus the ordered resolution lands in a fixed Hausdorff
sequence space before any divisor point is selected, and its total source coordinate is exactly
one.
-/

open scoped BigOperators

namespace RHTower

open Complex Filter

noncomputable section

/-- The high-exponent shell multipliers are absolutely summable at every point of the open right
half-plane.  The proof uses the exact adjacent-shell ratio `2⁻ˢ`, not a polynomial zeta-tail
bound. -/
theorem summable_shellMultiplier {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => shellMultiplier n s) := by
  have hscaled_ne :
      ∀ᶠ n : ℕ in atTop,
        (2 : ℂ) ^ ((n : ℂ) * s) * shellMultiplier n s ≠ 0 :=
    (tendsto_two_cpow_nat_mul_shellMultiplier hs).eventually_ne
      (one_sub_two_cpow_neg_ne_zero hs)
  have hshell_ne : ∀ᶠ n : ℕ in atTop, shellMultiplier n s ≠ 0 := by
    filter_upwards [hscaled_ne] with n hn
    exact (mul_ne_zero_iff.mp hn).2
  have hnorm_lt : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by simp only [Complex.neg_re]; linarith)
  apply summable_of_ratio_test_tendsto_lt_one hnorm_lt hshell_ne
  simpa [shellAdjacentTransfer, norm_div] using
    (tendsto_shellAdjacentTransfer hs).norm

/-- Every complete-resolution channel vector belongs to `ℓ¹` on the open right half-plane. -/
theorem summable_completeResolutionMultiplier (K : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    Summable (fun j : ℕ => completeResolutionMultiplier K j s) := by
  have hall : Summable (fun n : ℕ => shellMultiplier n s) :=
    summable_shellMultiplier hs
  have htail : Summable (fun n : ℕ => shellMultiplier (K + n) s) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff K).2 hall
  have hshift : Summable
      (fun n : ℕ => completeResolutionMultiplier K (n + 1) s) := by
    simpa [completeResolutionMultiplier] using htail
  exact (summable_nat_add_iff 1).1 (by simpa using hshift)

/-- The absolutely summable complete-resolution vector has total source coordinate one. -/
theorem hasSum_completeResolutionMultiplier_one (K : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    HasSum (fun j : ℕ => completeResolutionMultiplier K j s) 1 := by
  have hsum := summable_completeResolutionMultiplier K hs
  rw [hsum.hasSum_iff_tendsto_nat]
  exact (tendsto_add_atTop_iff_nat 1).1 (by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      tendsto_sum_range_completeResolutionMultiplier_one K hs)

/-- The complete-resolution vector is absolutely summable in norm. -/
theorem summable_norm_completeResolutionMultiplier (K : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    Summable (fun j : ℕ => ‖completeResolutionMultiplier K j s‖) :=
  (summable_completeResolutionMultiplier K hs).norm

/-- No point of the open right half-plane is annihilated by every channel simultaneously. -/
theorem exists_completeResolutionMultiplier_ne_zero (K : ℕ) {s : ℂ}
    (hs : 0 < s.re) :
    ∃ j : ℕ, completeResolutionMultiplier K j s ≠ 0 := by
  by_contra h
  push Not at h
  have hfun :
      (fun j : ℕ => completeResolutionMultiplier K j s) = fun _ => 0 :=
    funext h
  have hone := hasSum_completeResolutionMultiplier_one K hs
  rw [hfun] at hone
  exact one_ne_zero (hone.unique hasSum_zero)

end

end RHTower
