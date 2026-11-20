import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SeparatingEveryPurePowerAtTheCompositeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.LocalizingAPrimeSurplusToAFiniteMidpointWindow

/-!
# The signed square-root bias at the odd balanced composite midpoint

Subtracting the all-integer unitary center leaves the ordinary prime
midpoint plus a positive square-root bias. Its constant is twice the
square-root Mellin gap. The remaining error is uniformly of order
n^(7/16), even with the center's coprimality restriction.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The exact sign of the proper-power correction, with no coprimality
or endpoint term lost in passing to prefixes. -/
theorem composite_midpoint_minus_prime {n : ℕ} (hn : 1≤n) :
    oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n=
      2*fullLogProperPrefix n (3*n:ℕ)-fullLogProperPrefix n (2*n:ℕ)-fullLogProperPrefix n (4*n:ℕ) := by
  have h := odd_smooth_prime_midpoint_exact hn
  have difference (a b : ℕ) (hab : a≤b) : ∑ k ∈ Ioc a b, purePowerLog n k=
      fullLogProperPrefix n b-fullLogProperPrefix n a := by
    simp only [fullLogProperPrefix,Nat.floor_natCast]
    exact eq_sub_of_add_eq' (sum_Ioc_consecutive _ (Nat.zero_le a) hab)
  rw [unitarySignedIntervals,difference _ _ (by omega),difference _ _ (by omega)] at h
  linarith only [h]

private theorem three_full_log_prefix_errors :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 1≤n → ∀ k : ℕ, 1≤k → k≤4 →
      |fullLogProperPrefix n (k*n:ℕ)-2*Real.sqrt k*Real.sqrt n|≤K*(n:ℝ)^(7/16:ℝ) := by
  obtain ⟨C,hC,hprefix⟩ := uniform_square_prefix_of_full_logs
  obtain ⟨M,hM,hθ⟩ := theta_power_envelope_of_zero_sup
    (GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt (by norm_num : (20999/24000:ℝ)<7/8))
    (by norm_num : (1/2:ℝ)≤7/8)
  let t : ℝ := 7/16
  let d : ℝ := 5/12
  refine ⟨4/t+C*(4:ℝ)^d+2*M*(4:ℝ)^t,by dsimp only [t,d]; positivity,?_⟩
  intro n hn k hk h4
  have hn₁ : 1≤(n:ℝ) := Nat.one_le_cast.mpr hn
  have hk₁ : 1≤(k:ℝ) := Nat.one_le_cast.mpr hk
  have hn₀ := zero_lt_one.trans_le hn₁
  have hk₀ := zero_lt_one.trans_le hk₁
  have hx₁ : 1≤((k*n:ℕ):ℝ) := Nat.one_le_cast.mpr (Nat.mul_pos hk hn)
  have hs := hprefix n hn (k*n:ℕ) hx₁
  have hθ' := hθ (Real.sqrt (k*n:ℕ)) (Real.one_le_sqrt.mpr hx₁)
  have hlog := Real.log_le_rpow_div hn₀.le (by norm_num [t] : 0<t)
  have he (a : ℝ) (ha : 0≤a) (hat : a≤t) : ((k*n:ℕ):ℝ)^a≤(4:ℝ)^a*(n:ℝ)^t := by
    rw [Nat.cast_mul,Real.mul_rpow hk₀.le hn₀.le]
    exact mul_le_mul (Real.rpow_le_rpow hk₀.le (by exact_mod_cast h4) ha)
      (Real.rpow_le_rpow_of_exponent_le hn₁ hat) (Real.rpow_nonneg hn₀.le a) (by positivity)
  have hsmall := mul_le_mul_of_nonneg_left (he d (by norm_num [d]) (by norm_num [d,t])) hC
  have hlarge := mul_le_mul_of_nonneg_left (he t (by norm_num [t]) le_rfl) hM
  have hroot : (Real.sqrt (k*n:ℕ))^(7/8:ℝ)=((k*n:ℕ):ℝ)^t := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (zero_le_one.trans hx₁)]
    norm_num [t]
  rw [hroot] at hθ'
  have hsrt : Real.sqrt (k*n:ℕ)=Real.sqrt k*Real.sqrt n := by rw [Nat.cast_mul,Real.sqrt_mul hk₀.le]
  rw [abs_le] at hs hθ' ⊢
  change _ ∧ _≤(4/t+C*(4:ℝ)^d+2*M*(4:ℝ)^t)*(n:ℝ)^t
  rw [show 2*Real.sqrt k*Real.sqrt n=2*Real.sqrt (k*n:ℕ) by rw [hsrt,mul_assoc]]
  dsimp only [d,t] at hlog hsmall hlarge hθ' ⊢
  simp only [div_eq_mul_inv] at hs hlog hsmall hlarge hθ' ⊢
  constructor <;> linarith only [hs.1,hs.2,hθ'.1,hθ'.2,hlog,hsmall,hlarge]

/-- After removing the deterministic square bias, the centered composite
price follows the ordinary-prime midpoint with a uniform power saving. -/
theorem square_bias_of_balanced_composites :
    ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ, 1≤n →
      |oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n-
        2*midpointPowerGap (1/2)*Real.sqrt n|≤K*(n:ℝ)^(7/16:ℝ) := by
  obtain ⟨K,hK,h⟩ := three_full_log_prefix_errors
  refine ⟨4*K,by positivity,fun n hn => ?_⟩
  have h₂ := abs_le.mp (h n hn 2 (by decide) (by decide))
  have h₃ := abs_le.mp (h n hn 3 (by decide) (by decide))
  have h₄ := abs_le.mp (h n hn 4 (by decide) le_rfl)
  rw [composite_midpoint_minus_prime hn,midpointPowerGap,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow,abs_le]
  norm_num only [Nat.cast_ofNat] at h₂ h₃ h₄
  constructor <;> linarith only [h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2]

/-- The old half-plus error has a strictly positive normalized limit
at the endpoint one half. -/
theorem normalized_composite_midpoint_bias :
    Tendsto (fun n : ℕ => (oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n)/Real.sqrt n)
      atTop (𝓝 (2*midpointPowerGap (1/2))) := by
  obtain ⟨K,hK,h⟩ := square_bias_of_balanced_composites
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hz := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/16)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul K
  rw [mul_zero] at hz
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hz.eventually_lt_const hε)
  refine ⟨max 1 N,fun n hn => ?_⟩
  have hn₁ := (le_max_left 1 N).trans hn
  have hn₀ : 0<(n:ℝ) := Nat.cast_pos.mpr hn₁
  have hhalf := Real.sqrt_pos.mpr hn₀
  have hraw := div_le_div_of_nonneg_right (h n hn₁) hhalf.le
  have hscale : (n:ℝ)^(7/16:ℝ)/Real.sqrt n=(n:ℝ)^(-(1/16:ℝ)) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_sub hn₀]
    norm_num
  have hprice (v : ℝ) : v/Real.sqrt n-2*midpointPowerGap (1/2)=
      (v-2*midpointPowerGap (1/2)*Real.sqrt n)/Real.sqrt n := by field_simp [hhalf.ne']
  rw [Real.dist_eq,hprice,abs_div,abs_of_pos hhalf]
  rw [mul_div_assoc,hscale] at hraw
  exact hraw.trans_lt (hN n ((le_max_right 1 N).trans hn))

/-- Both signs of the centered odd-balanced composite price exceed
a constant times √n log log log n infinitely often. -/
theorem littlewood_excursions_of_balanced_composites {c : ℝ} (hc : 0<c)
    (hc' : c < midpointPowerGap (1/2)*(_root_.RHTower.littlewoodConst/28)) :
    ∀ σ : ℝ, (σ=1 ∨ σ= -1) → ∃ᶠ n : ℕ in atTop,
      c*Real.sqrt n*Real.log (Real.log (Real.log n))<σ*(oddSmoothCompositePrice n-unitaryMidpointCenter n) := by
  obtain ⟨q,hcq,hq⟩ := exists_between hc'
  obtain ⟨K,hK,h⟩ := square_bias_of_balanced_composites
  let g := midpointPowerGap (1/2)
  have hg : 0<g := midpointPowerGap_pos ⟨by norm_num,by norm_num⟩
  have hlim := _root_.RHTower.tendsto_logLogLog_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hpaid := hlim.eventually_ge_atTop ((K+2*g)/(q-c))
  intro σ hσ
  have hf := littlewood_excursions_of_integer_prime_midpoints (hc.trans hcq) hq σ hσ
  apply (hf.and_eventually (hpaid.and (eventually_ge_atTop 1))).mono
  rintro n ⟨hprice,hlog,hn⟩
  have hr : 1≤(n:ℝ) := Nat.one_le_cast.mpr hn
  have hθ := abs_le.mp (h n hn)
  have hsmall := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hr
    (by norm_num : (7/16:ℝ)≤1/2)) hK
  rw [←Real.sqrt_eq_rpow] at hsmall
  have hv := (div_le_iff₀ (sub_pos.mpr hcq)).mp hlog
  have hcover := mul_le_mul_of_nonneg_right hv (Real.sqrt_nonneg n)
  have hbonus := mul_nonneg hg.le (Real.sqrt_nonneg n)
  change -(K*(n:ℝ)^(7/16:ℝ)) ≤ oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n-
    2*g*Real.sqrt n ∧ _ ≤ K*(n:ℝ)^(7/16:ℝ) at hθ
  change (K+2*g)*Real.sqrt n ≤ Real.log (Real.log (Real.log n))*(q-c)*Real.sqrt n at hcover
  rcases hσ with rfl | rfl <;> simp only [one_mul,neg_one_mul] at hprice ⊢ <;>
    linarith only [hprice,hθ.1,hθ.2,hcover,hbonus,hsmall]

#print axioms square_bias_of_balanced_composites
#print axioms normalized_composite_midpoint_bias
#print axioms littlewood_excursions_of_balanced_composites

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
