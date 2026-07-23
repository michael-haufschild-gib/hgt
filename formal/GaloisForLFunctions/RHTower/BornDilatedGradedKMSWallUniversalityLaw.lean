import GaloisForLFunctions.RHTower.BornGradedKMSClassification
import GaloisForLFunctions.RHTower.BornSuperKMSCovariance

/-!
# Dilation-universal graded Born KMS phase beyond the Gibbs wall

The Born parity supertrace converges throughout the positive high-temperature strip where the
ungraded Gibbs trace diverges.  Exact dilation covariance transports that graded phase through
every positive dilation channel: each dilated supertrace is summable, strictly positive, and is
the prescribed KMS multiple of the original graded trace.
-/

namespace RHTower

noncomputable section

/-- **Dilation-universal graded wall law.**  Every positive dilation preserves the convergent,
positive, exactly covariant graded trace throughout `0 < β ≤ 2`, even though the ungraded Gibbs
trace diverges there. -/
theorem dilatedBornSuperKMS_beyond_ungraded_wall
    {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2)
    {k : ℕ} (hk : 0 < k) :
    Summable (dilatedBornSupertraceTerm k β) ∧
      ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(β / 2))) ∧
      (∑' n : ℕ, dilatedBornSupertraceTerm k β n) =
        (k : ℝ) ^ (-(β / 2)) * bornSupertrace β ∧
      0 < ∑' n : ℕ, dilatedBornSupertraceTerm k β n := by
  have hwall := gradedOrder_beyond_wall hβ0 hβ2
  have hsum : Summable (dilatedBornSupertraceTerm k β) := by
    exact (hwall.1.mul_left ((k : ℝ) ^ (-(β / 2)))).congr
      (fun n => (dilatedBornSupertraceTerm_eq hk β n).symm)
  have hvalue := tsum_dilatedBornSupertraceTerm hk β
  refine ⟨hsum, hwall.2, hvalue, ?_⟩
  rw [hvalue]
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hk) _) (bornSupertrace_pos hβ0)

/-- Odd dilation channels additionally preserve the parity grading pointwise while remaining in
the same beyond-wall phase. -/
theorem oddDilatedBornSuperKMS_beyond_ungraded_wall
    {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2)
    {k : ℕ} (hk : Odd k) :
    (∀ n : ℕ, ((-1 : ℝ)) ^ (k * n) = (-1) ^ n) ∧
      Summable (dilatedBornSupertraceTerm k β) ∧
      ¬ Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(β / 2))) ∧
      0 < ∑' n : ℕ, dilatedBornSupertraceTerm k β n := by
  have hk0 : 0 < k := hk.pos
  have hphase := dilatedBornSuperKMS_beyond_ungraded_wall hβ0 hβ2 hk0
  exact ⟨gradedSign_mul_odd hk, hphase.1, hphase.2.1, hphase.2.2.2⟩

end

end RHTower
