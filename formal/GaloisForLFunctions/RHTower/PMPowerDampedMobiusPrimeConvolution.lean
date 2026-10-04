import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeHead
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusBoundaryKernel

/-!
# Signed prime convolution of the actual PM source

The exact prime-head transfer, density-preserving prime tail and actual
boundary kernel identify the full convolution uniformly at square-root
lower cutoffs. This does not supply complete signed energy compensation.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

/-- The complete actual prime convolution, with a freely moving lower cutoff. -/
def pmPowerDampedPrimeConvolution (ε a X : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊X⌋₊,
    (if q.Prime then (q : ℝ)^(-ε) else 0)*
      (pmPowerDampedFermiSource ε ((q : ℝ)/X)).re

/-- Unconditional signed convolution error, retaining both prime density and the
actual boundary jet. The cofactor cutoff is free within the stated range. -/
theorem pmPowerDampedFermiSource_prime_convolution_error {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ c > 0, ∃ K > 0, ∃ R > 0, ∀ᶠ X : ℝ in atTop, ∀ H a : ℝ,
      R ≤ H → H ≤ Real.sqrt X → 2 ≤ a → a ≤ X/H →
      |(Real.log X)^2/X^(1-ε)*pmPowerDampedPrimeConvolution ε a X+
        (pmPowerDampedBoundaryJet ε).re| ≤
      K*(Real.log X/Real.log H^3+1/Real.log H+1/Real.log X+
        (Real.log X)^2*H^(ε+2)*Real.exp (-c*Real.sqrt (Real.log X))+
        (Real.log X)^2/(Real.log a*Real.log H^3)) := by
  obtain ⟨c,hc,K₁,hK₁,he₁⟩ := pmPowerDampedFermiSource_prime_cofactor_transfer hε.le
  obtain ⟨K₂,hK₂,R₂,hR₂,he₂⟩ := pmPowerDampedFermiSource_prime_tail_bound hε hεhalf
  obtain ⟨K₃,hK₃,he₃⟩ := pmPowerDampedBoundaryWeight_kernel_error hε hεhalf
  obtain ⟨R₃,hR₃⟩ := eventually_atTop.mp he₃
  let R := max (max R₂ R₃) (Real.exp 8)
  have hR2 : R₂ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR3 : R₃ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hRexp : Real.exp 8 ≤ R := le_max_right _ _
  have hR0 : 0 < R := hR₂.trans_le hR2
  let K := K₁+K₂+K₃
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨c,hc,K,hK,R,hR0,?_⟩
  filter_upwards [he₁,eventually_ge_atTop (4 : ℝ)] with X heX hX
  intro H a hRH hHX ha haH
  have hX0 : 0 < X := by linarith
  have hH0 : 0 < H := hR0.trans_le hRH
  have hHexp : Real.exp 8 ≤ H := hRexp.trans hRH
  have hH2 : 2 ≤ H := by
    have hh := Real.add_one_le_exp (8 : ℝ)
    linarith
  have hlH : 8 ≤ Real.log H := by
    have hh := Real.log_le_log (Real.exp_pos 8) hHexp
    simpa only [Real.log_exp] using hh
  have hlH0 : 0 < Real.log H := by linarith
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogH : 2*Real.log H ≤ Real.log X := by
    have hh := Real.log_le_log hH0 hHX
    rw [Real.log_sqrt hX0.le] at hh
    linarith
  have hden : Real.log X-Real.log (X/H) = Real.log H := by
    rw [Real.log_div hX0.ne' hH0.ne']
    ring
  have htail := he₂ X a (X/H) ha haH
    (div_le_div_of_nonneg_left hX0.le hR₂ ((hR2.trans hRH))) (by linarith [hden])
  rw [hden] at htail
  let T : ℝ := ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊X/H⌋₊,
    (if q.Prime then (q : ℝ)^(-ε) else 0)*
      (pmPowerDampedFermiSource ε ((q : ℝ)/X)).re
  have hTabs : |T| ≤ K₂*X^(1-ε)/(Real.log a*Real.log H^3) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    refine (Finset.sum_le_sum fun q _ => ?_).trans htail
    split_ifs with hp
    · rw [abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _)
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    · simp
  have hsplit : pmPowerDampedPrimeConvolution ε a X =
      T+pmPowerDampedPrimeConvolution ε (X/H) X := by
    exact (Finset.sum_Ioc_consecutive _ (Nat.floor_mono haH)
      (Nat.floor_mono (div_le_self hX0.le (by linarith : 1 ≤ H)))).symm
  let I : ℝ := ∫ x in Ioc (1 : ℝ) H,
    (pmPowerDampedBoundaryWeight ε x).re/(Real.log X-Real.log x)
  have hhead := heX H hH2 hHX
  change |pmPowerDampedPrimeConvolution ε (X/H) X-X^(1-ε)*I| ≤ _ at hhead
  have hkernel := hR₃ H (hR3.trans hRH) (Real.log X) hlogH
  change |Real.log X^2*I+(pmPowerDampedBoundaryJet ε).re| ≤ _ at hkernel
  let N : ℝ := Real.log X^2/X^(1-ε)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : 0 < X^(1-ε) := Real.rpow_pos_of_pos hX0 _
  have hNT : |N*T| ≤ K₂*(Real.log X^2/(Real.log a*Real.log H^3)) := by
    rw [abs_mul,abs_of_nonneg hN]
    calc
      _ ≤ N*(K₂*X^(1-ε)/(Real.log a*Real.log H^3)) :=
        mul_le_mul_of_nonneg_left hTabs hN
      _ = _ := by dsimp [N]; field_simp
  have hNH : |N*(pmPowerDampedPrimeConvolution ε (X/H) X-X^(1-ε)*I)| ≤
      K₁*(Real.log X^2*H^(ε+2)*Real.exp (-c*Real.sqrt (Real.log X))) := by
    rw [abs_mul,abs_of_nonneg hN]
    calc
      _ ≤ N*(K₁*X^(1-ε)*H^(ε+2)*Real.exp (-c*Real.sqrt (Real.log X))) :=
        mul_le_mul_of_nonneg_left hhead hN
      _ = _ := by dsimp [N]; field_simp
  have heq : N*pmPowerDampedPrimeConvolution ε a X+(pmPowerDampedBoundaryJet ε).re =
      N*T+N*(pmPowerDampedPrimeConvolution ε (X/H) X-X^(1-ε)*I)+
      (Real.log X^2*I+(pmPowerDampedBoundaryJet ε).re) := by
    rw [hsplit]
    dsimp [N]
    field_simp
    ring
  change |N*pmPowerDampedPrimeConvolution ε a X+(pmPowerDampedBoundaryJet ε).re| ≤ _
  rw [heq]
  have ha0 : 0 < Real.log a := Real.log_pos (by linarith)
  have hk0 : 0 ≤ Real.log X/Real.log H^3+1/Real.log H+1/Real.log X := by positivity
  have hh0 : 0 ≤ Real.log X^2*H^(ε+2)*Real.exp (-c*Real.sqrt (Real.log X)) := by positivity
  have ht0 : 0 ≤ Real.log X^2/(Real.log a*Real.log H^3) := by positivity
  calc
    _ ≤ |N*T|+|N*(pmPowerDampedPrimeConvolution ε (X/H) X-X^(1-ε)*I)|+
        |Real.log X^2*I+(pmPowerDampedBoundaryJet ε).re| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K₂*(Real.log X^2/(Real.log a*Real.log H^3))+
        K₁*(Real.log X^2*H^(ε+2)*Real.exp (-c*Real.sqrt (Real.log X)))+
        K₃*(Real.log X/Real.log H^3+1/Real.log H+1/Real.log X) :=
      add_le_add (add_le_add hNT hNH) hkernel
    _ ≤ K*(Real.log X^2/(Real.log a*Real.log H^3))+
        K*(Real.log X^2*H^(ε+2)*Real.exp (-c*Real.sqrt (Real.log X)))+
        K*(Real.log X/Real.log H^3+1/Real.log H+1/Real.log X) := by
      apply add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) ht0
      · exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hh0
      · exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hk0
    _ = _ := by ring

/-- The complete signed prime convolution has the negative boundary-jet limit,
uniformly for every lower cutoff comparable to the square root. -/
theorem pmPowerDampedFermiSource_prime_convolution_uniform_limit {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∀ δ > 0, ∀ᶠ s : ℝ in atTop, ∀ a : ℝ,
      Real.exp (s^5/2)/2 ≤ a → a ≤ Real.exp (s^5/2) →
      |s^10/(Real.exp (s^5))^(1-ε)*
          pmPowerDampedPrimeConvolution ε a (Real.exp (s^5))+
        (pmPowerDampedBoundaryJet ε).re| < δ := by
  obtain ⟨c,hc,K,hK,R,hR,he⟩ :=
    pmPowerDampedFermiSource_prime_convolution_error hε hεhalf
  have hs5 : Tendsto (fun s : ℝ => s^5) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hs2 : Tendsto (fun s : ℝ => s^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hX := Real.tendsto_exp_atTop.comp hs5
  have hH := Real.tendsto_exp_atTop.comp hs2
  have hi1 : Tendsto (fun s : ℝ => 1/s) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0))
  have hi2 : Tendsto (fun s : ℝ => 1/s^2) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hs2
  have hi5 : Tendsto (fun s : ℝ => 1/s^5) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hs5
  have hexp : Tendsto (fun s : ℝ => s^10*Real.exp (-s^2)) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp hs2 using 1
    funext s
    simp only [Function.comp_def]
    congr 1
    ring
  have hbound : Tendsto (fun s : ℝ => K*(5/s+1/s^2+1/s^5+
      s^10*Real.exp (-s^2))) atTop (𝓝 0) := by
    have hh := ((((hi1.const_mul 5).add hi2).add hi5).add hexp).const_mul K
    simpa only [mul_zero,add_zero,mul_one_div] using hh
  intro δ hδ
  have hδevent := hbound.eventually (gt_mem_nhds hδ)
  filter_upwards [hX.eventually he,hH.eventually (eventually_ge_atTop R),
    eventually_ge_atTop (2 : ℝ),eventually_ge_atTop (((ε+3)/c)^2),
    hs5.eventually (eventually_ge_atTop (4*Real.log 2)),hδevent]
    with s hsX hsR hs hsroot hslog hsδ
  intro a ha ha'
  have hs0 : 0 < s := by linarith
  have hs21 : 1 ≤ s^2 := by nlinarith
  have hs3 : 2 ≤ s^3 := by
    have hh := mul_le_mul_of_nonneg_left hs21 hs0.le
    nlinarith
  have hpoly : 2*s^2 ≤ s^5 := by
    calc
      _ ≤ s^3*s^2 := mul_le_mul_of_nonneg_right hs3 (sq_nonneg s)
      _ = _ := by ring
  have hHX : Real.exp (s^2) ≤ Real.sqrt (Real.exp (s^5)) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by simpa using hpoly)
  have hXa : Real.exp (s^5/2) ≤ Real.exp (s^5)/Real.exp (s^2) := by
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    linarith
  have hs5large : 8 ≤ s^5 := by nlinarith [sq_nonneg s]
  have ha2 : 2 ≤ a := by
    have hh := Real.add_one_le_exp (s^5/2)
    linarith
  have hb := hsX (Real.exp (s^2)) a hsR hHX ha2 (ha'.trans hXa)
  simp only [Function.comp_def,Real.log_exp] at hb
  have hratio : s^5/(s^2)^3 = 1/s := by field_simp
  have hpow : (s^5)^2 = s^10 := by ring
  rw [hratio,hpow] at hb
  have hloga : s^5/4 ≤ Real.log a := by
    have hh := Real.log_le_log (by positivity : 0 < Real.exp (s^5/2)/2) ha
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp] at hh
    linarith
  have hlog0 : 0 < Real.log a := Real.log_pos (by linarith)
  have htail : s^10/(Real.log a*(s^2)^3) ≤ 4/s := by
    have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ s^10)
      (by positivity : 0 < (s^5/4)*(s^2)^3)
      (mul_le_mul_of_nonneg_right hloga (by positivity : 0 ≤ (s^2)^3))
    exact hh.trans_eq (by field_simp)
  have hroot : ((ε+3)/c)*s^2 ≤ Real.sqrt (s^5) := by
    apply Real.le_sqrt_of_sq_le
    have hh := mul_le_mul_of_nonneg_right hsroot (by positivity : 0 ≤ s^4)
    nlinarith
  have hexponent : s^2*(ε+2)-c*Real.sqrt (s^5) ≤ -s^2 := by
    have hh := mul_le_mul_of_nonneg_left hroot hc.le
    have heq : c*(((ε+3)/c)*s^2) = (ε+3)*s^2 := by field_simp
    rw [heq] at hh
    nlinarith
  have hhead : s^10*(Real.exp (s^2))^(ε+2)*Real.exp (-c*Real.sqrt (s^5)) ≤
      s^10*Real.exp (-s^2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    rw [mul_assoc,← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (by simpa only [sub_eq_add_neg,neg_mul] using hexponent)) (by positivity)
  calc
    _ ≤ K*(1/s+1/s^2+1/s^5+
        s^10*(Real.exp (s^2))^(ε+2)*Real.exp (-c*Real.sqrt (s^5))+
        s^10/(Real.log a*(s^2)^3)) := hb
    _ ≤ K*(1/s+1/s^2+1/s^5+s^10*Real.exp (-s^2)+4/s) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hhead) htail) hK.le
    _ = K*(5/s+1/s^2+1/s^5+s^10*Real.exp (-s^2)) := by ring
    _ < δ := hsδ

/-- Uniform square-root-cutoff asymptotic at every sufficiently large real
argument, rather than only at a parameterized sequence. -/
theorem pmPowerDampedFermiSource_prime_convolution_asymptotic {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∀ δ > 0, ∀ᶠ X : ℝ in atTop, ∀ a : ℝ,
      Real.sqrt X/2 ≤ a → a ≤ Real.sqrt X →
      |Real.log X^2/X^(1-ε)*pmPowerDampedPrimeConvolution ε a X+
        (pmPowerDampedBoundaryJet ε).re| < δ := by
  intro δ hδ
  have hs : Tendsto (fun X : ℝ => (Real.log X)^((1 : ℝ)/5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/5)).comp Real.tendsto_log_atTop
  filter_upwards [hs.eventually
    (pmPowerDampedFermiSource_prime_convolution_uniform_limit hε hεhalf δ hδ),
    eventually_gt_atTop (1 : ℝ)] with X he hX
  have hX0 : 0 < X := by linarith
  have hlX : 0 < Real.log X := Real.log_pos hX
  have hp : ((Real.log X)^((1 : ℝ)/5))^5 = Real.log X := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hlX.le]
    norm_num
  have hp10 : ((Real.log X)^((1 : ℝ)/5))^10 = Real.log X^2 := by
    rw [show (10 : ℕ) = 5*2 by norm_num,pow_mul,hp]
  have hsqrt : Real.exp (Real.log X/2) = Real.sqrt X := by
    rw [Real.exp_half,Real.exp_log hX0]
  rw [hp,hp10,Real.exp_log hX0,hsqrt] at he
  exact he

end RHTower
