import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.RemoteMass
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Waves
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.TraceAbscissa

/-! # The prescribed wave is exterior to the critical heat range -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

private theorem tailLaw_product (k : ℕ) : tailLaw k = occupationWeight k*occupationWeight (k+1) := by
  simp only [tailLaw,occupationWeight_eq,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

/-- The remote coordinates have infinite inverse-heat moment even when the prescribed levels meet their endpoints. -/
theorem prefixWave_exterior {m : ℕ} (b : PrefixData m) :
    prefixWave b ∉ LinearMap.range criticalOperator.toLinearMap := by
  intro hv
  have hs := (heat_range_iff_summable _).mp hv
  simp only [prefixWave_mass] at hs
  let C := (occupationWeight m-occupationWeight (m+1))^m
  have hC : 0 < C := pow_pos (sub_pos.mpr (occupationWeight_strictAnti (Nat.lt_succ_self m))) _
  have hlow (k : ℕ) (hk : 1 ≤ k) : C*occupationWeight (k+1) ≤ prefixProbability b (m+k)/occupationWeight (m+k) := by
    apply (le_div_iff₀ (occupationWeight_pos _)).mpr
    rw [probability_tail]
    have h := mul_le_mul_of_nonneg_left (remote_residue_lower b k hk) (tailLaw_pos k).le
    apply le_trans _ h
    rw [tailLaw_product]
    calc C*occupationWeight (k+1)*occupationWeight (m+k) ≤ C*occupationWeight (k+1)*occupationWeight k :=
           mul_le_mul_of_nonneg_left (occupationWeight_antitone (Nat.le_add_left _ _)) (mul_nonneg hC.le (occupationWeight_pos _).le)
         _ = _ := by ring
  have ha : Summable (fun k => occupationWeight (k+2)) :=
    (((summable_nat_add_iff (m+1)).mpr hs).mul_left C⁻¹).of_nonneg_of_le (fun k => (occupationWeight_pos _).le) (fun k => by
      have h := mul_le_mul_of_nonneg_left (hlow (k+1) (Nat.succ_pos k)) (inv_nonneg.mpr hC.le)
      simpa only [inv_mul_cancel_left₀ hC.ne',show m+(k+1)=k+(m+1) by omega] using h)
  have hfull := (summable_nat_add_iff 2).mp ha
  exact (lt_irrefl (1:ℝ)) ((summable_band_rpow_iff (hotEdge 1) 1).mp (by simpa only [Real.rpow_one] using hfull))

#print axioms prefixWave_exterior

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
