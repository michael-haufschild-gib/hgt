import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.CertificateScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # The subexponential cost of local simulation -/
open Filter Real
namespace GaloisForLFunctions.HTGeometry.LocalPatches
open IncrementClocks
noncomputable section

/-- Any fixed increase in the time exponent pays the square-root gate overhead. -/
theorem binary_compiler_envelope {γ α : ℝ} (hγ : 0 ≤ γ) (hγα : γ < α) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)*(1+(2:ℝ)^(γ*(N:ℝ)))*2^(5*N.sqrt+17) ≤ (2:ℝ)^(α*(N:ℝ)) := by
  have hh := crossingWidth_exponent_ratio.eventually_const_lt (show 1-(α-γ)<1 by linarith only [hγα])
  filter_upwards [hh,eventually_ge_atTop (64*64)] with N hn hN
  let s := N.sqrt
  have hs : 64 ≤ s := Nat.le_sqrt.mpr hN
  have hsq : s*s ≤ N := Nat.sqrt_le N
  have hbase : 26*s ≤ N := (Nat.mul_le_mul_right s (by omega : 26 ≤ s)).trans hsq
  have hpos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  change 1-(α-γ) < logb 2 (crossingWidth N)/(N:ℝ) at hn
  simp only [crossingWidth,logb_pow,logb_self_eq_one (by norm_num : (1:ℝ)<2),mul_one] at hn
  have hmargin := (lt_div_iff₀ hpos).mp hn
  have hp := ReturnExcursions.dimension_dominates_speed hs
  change 64*(s+1)^2≤2^s at hp
  have hNs : N ≤ (s+1)^2 := by rw [pow_two]; exact (Nat.lt_succ_sqrt N).le
  have hprice : (N:ℝ) ≤ (2:ℝ)^s := by exact_mod_cast hNs.trans (le_trans (by omega) hp)
  let T := (2:ℝ)^(γ*(N:ℝ))
  have hT : 1 ≤ T := one_le_rpow (by norm_num) (mul_nonneg hγ hpos.le)
  have he : ((6*s+18:ℕ):ℝ)+γ*(N:ℝ) ≤ α*(N:ℝ) := by
    have hsmall : ((6*s+18:ℕ):ℝ) ≤ 26*(s:ℝ) := by exact_mod_cast (show 6*s+18 ≤ 26*s by omega)
    change (1-(α-γ))*(N:ℝ) < ((N-26*s:ℕ):ℝ) at hmargin
    rw [Nat.cast_sub hbase,Nat.cast_mul,Nat.cast_ofNat] at hmargin
    linarith only [hsmall,hmargin]
  calc
    _ ≤ ((2:ℝ)^s*(2*T))*2^(5*s+17) := mul_le_mul_of_nonneg_right
      (mul_le_mul hprice (by linarith only [hT]) (by positivity) (by positivity)) (by positivity)
    _ = (2:ℝ)^(6*s+18)*T := by
      rw [show 6*s+18=s+1+(5*s+17) by omega,pow_add (2:ℝ) (s+1) (5*s+17),pow_succ (2:ℝ) s]
      ring
    _ = (2:ℝ)^(((6*s+18:ℕ):ℝ)+γ*(N:ℝ)) := by rw [rpow_add (by norm_num : 0<(2:ℝ)),rpow_natCast]
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) he

#print axioms binary_compiler_envelope
end
end GaloisForLFunctions.HTGeometry.LocalPatches
