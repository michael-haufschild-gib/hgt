import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.PowerTransfer
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockResponse
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockClosure

/-! # Physical optimality of every real-power comparison -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- At each fixed inverse temperature and real order q ≥ 1 the least physical factor at rank r > 0 is r^(q−1). -/
theorem fixed_power_factor_iff (r : ℕ) (β : GibbsExponent) (q : Ici (1:ℝ)) (K : ℝ) :
    (∀ (P Q : Projection) (hP : MissingDimension P (r+1)) (cP : Conserving (projected P))
      (hQ : MissingDimension Q (r+1)) (cQ : Conserving (projected Q)),
      detectorError (powerResponse β) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)^q.val ≤
      K * detectorError (powerResponse (scaledExponent β q)) (physicalSpectrum P hP cP) (physicalSpectrum Q hQ cQ)) ↔
      ((r+1:ℕ):ℝ)^(q.val-1) ≤ K := by
  have hq : 0 ≤ q.val := zero_le_one.trans q.property
  constructor
  · intro h
    have hn (N : ℕ) : normalizedBlock β (r+1) N ^ q.val ≤ K * normalizedBlock (scaledExponent β q) (r+1) N := by
      have he := hot_block_mem_closed_of_physical r N (isClosed_le
        ((Real.continuous_rpow_const hq).comp (continuous_detectorError (powerResponse β) (r+1)))
        (continuous_const.mul (continuous_detectorError (powerResponse (scaledExponent β q)) (r+1)))) (by
          rintro _ ⟨P,hP,cP,rfl⟩ _ ⟨Q,hQ,cQ,rfl⟩
          exact h P Q hP cP hQ cQ)
      change detectorError (powerResponse β) (hotEdge (r+1)) (blockSpectrum N (r+1))^q.val ≤
        K * detectorError (powerResponse (scaledExponent β q)) (hotEdge (r+1)) (blockSpectrum N (r+1)) at he
      simp only [detectorError_block,power_tailCeiling_eq_scaled] at he
      have hnorm : 0 ≤ normalizedBlock β (r+1) N := Finset.sum_nonneg (fun j _ =>
        Real.rpow_nonneg (div_nonneg (occupationWeight_pos _).le (occupationWeight_pos _).le) _)
      rw [Real.mul_rpow (Real.rpow_nonneg (occupationWeight_pos _).le _) hnorm,
        power_scaledExponent β q (occupationWeight_pos N).le,mul_left_comm K] at he
      exact le_of_mul_le_mul_left he (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (occupationWeight_pos _) _) _)
    have ht : Tendsto (fun N => normalizedBlock β (r+1) N^q.val) atTop (𝓝 (((r+1:ℕ):ℝ)^q.val)) :=
      ((Real.continuous_rpow_const hq).tendsto _).comp (normalizedBlock_tendsto β (r+1))
    have hb := le_of_tendsto_of_tendsto ht ((normalizedBlock_tendsto (scaledExponent β q) (r+1)).const_mul K) (Eventually.of_forall hn)
    have hr : 0 < ((r+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos r)
    have he : ((r+1:ℕ):ℝ)^(q.val-1)*((r+1:ℕ):ℝ) = ((r+1:ℕ):ℝ)^q.val := by
      rw [← Real.rpow_add_one hr.ne',sub_add_cancel]
    rw [← he] at hb
    exact le_of_mul_le_mul_right hb hr
  · intro h P Q hP cP hQ cQ
    exact (detector_power_transfer β q _ _).trans (mul_le_mul_of_nonneg_right h (detectorError_nonneg _ _ _))

#print axioms fixed_power_factor_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
