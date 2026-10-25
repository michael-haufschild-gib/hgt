import GaloisForLFunctions.ArithmeticDefectRigidity.TheAdmittedCofactorKernelIsUnique
import GaloisForLFunctions.ArithmeticDefectRigidity.EnergyQuantilesRetainDiffuseEscape

/-!
# Actual cofactor Grams have vanishing steps

One pronic cell costs at most one in each fixed mixed pairing. The same
bound on receiver energy increments makes normalized Gram steps vanish
on escape. Admission uses the unique full-horizon limit.
-/
section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- One pronic cell has bilinear mass at most one for unit linearly bounded rows. -/
theorem abs_pronicPairing_succ_sub_le (T : ℕ) (u v : ℕ → ℝ)
    (hu : ∀ n, |u n| ≤ (n : ℝ)) (hv : ∀ n, |v n| ≤ (n : ℝ)) :
    |pronicPairing (T + 1) u v - pronicPairing T u v| ≤ 1 := by
  rw [pronicPairing, pronicPairing, sum_Icc_succ_top (Nat.succ_pos T), add_sub_cancel_left]
  have hden : 0 ≤ (((T + 1 : ℕ) : ℝ)) * (((T + 1 : ℕ) : ℝ) + 1) := by
    positivity
  rw [abs_div, abs_mul, abs_of_nonneg hden]
  apply (div_le_one (by positivity)).mpr
  calc
    _ ≤ (((T + 1 : ℕ) : ℝ)) * (((T + 1 : ℕ) : ℝ)) :=
      mul_le_mul (hu (T + 1)) (hv (T + 1)) (abs_nonneg _) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg _)

private theorem abs_normalized_increment_le
    {A B E F R : ℝ} (hE : 0 < E) (hEF : E ≤ F) (hF : F ≤ E + 1)
    (hR : 0 ≤ R) (hA : |A / E| ≤ R) (hBA : |B - A| ≤ 1) :
    |B / F - A / E| ≤ (1 + R) / E := by
  have hFpos : 0 < F := hE.trans_le hEF
  have heq : B / F - A / E = (B - A - (A / E) * (F - E)) / F := by
    field_simp [hE.ne', hFpos.ne']
    ring
  have hincr : |F - E| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hEF)]
    linarith only [hF]
  have hnum : |B - A - (A / E) * (F - E)| ≤ 1 + R := by
    calc
      _ ≤ |B - A| + |(A / E) * (F - E)| := abs_sub _ _
      _ ≤ 1 + R := by
        rw [abs_mul]
        exact add_le_add hBA (by
          simpa only [mul_one] using mul_le_mul hA hincr (abs_nonneg _) hR)
  rw [heq, abs_div, abs_of_pos hFpos]
  exact (div_le_div_of_nonneg_right hnum hFpos.le).trans
    (div_le_div_of_nonneg_left (add_nonneg zero_le_one hR) hE hEF)

/-- Each normalized cofactor coordinate has a reciprocal-energy step bound. -/
theorem abs_cofactorGram_succ_sub_le (ε : SubcriticalDamping) (T : ℕ) (j k : ℕ+) :
    |cofactorGram ε (T + 1) j k - cofactorGram ε T j k| ≤
      (1 + cofactorGramRadius j k) / dampedMobiusEnergy ε (T + 1) := by
  have hrow (p : ℕ+) (n : ℕ) :
      |rowDilate p (pmPowerDampedCenteredDivisorPrefix ε) n| ≤ (n : ℝ) :=
    (abs_receiver_le_cell ε (n / p)).trans (by exact_mod_cast Nat.div_le_self n (p : ℕ))
  exact abs_normalized_increment_le (receiverEnergy_succ_pos ε T)
    (dampedMobiusEnergy_mono ε (Nat.le_succ (T + 1)))
    (receiverEnergy_succ_le ε (T + 1)) (by unfold cofactorGramRadius; positivity)
    (abs_cofactorGram_le ε T j k)
    (abs_pronicPairing_succ_sub_le (T + 1) _ _ (hrow j) (hrow k))

/-- Every actual normalized cofactor coordinate has vanishing successive steps. -/
theorem cofactorGram_succ_sub_tendsto_zero (ε : SubcriticalDamping) (j k : ℕ+) :
    Tendsto (fun T => cofactorGram ε (T + 1) j k - cofactorGram ε T j k)
      atTop (𝓝 0) := by
  rcases ArithmeticCompensationTheory.admits_or_tendsto_atTop (ε : ℝ) with hpaid | hE
  · obtain ⟨K, hK⟩ := exists_cofactorGram_full_limit_of_admits ε hpaid
    have h := ((hK j k).comp (tendsto_add_atTop_nat 1)).sub (hK j k)
    simpa only [Function.comp_apply, sub_self] using h
  · have hbound : Tendsto (fun T => (1 + cofactorGramRadius j k) /
        dampedMobiusEnergy ε (T + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hE.comp (tendsto_add_atTop_nat 1))
    exact squeeze_zero_norm (fun T => by
      simpa only [Real.norm_eq_abs] using abs_cofactorGram_succ_sub_le ε T j k) hbound

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.cofactorGram_succ_sub_tendsto_zero
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.abs_cofactorGram_succ_sub_le
end
end

