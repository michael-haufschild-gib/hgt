import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSquareRootBiasOfTheOddBalancedComposites

/-!
# The square and cube corrections to the composite midpoint

After both deterministic powers are removed, the integer observation
measures a single real prefix. Its two main terms are the ordinary prime
errors at the square and cube roots. Passing to all real midpoints costs
only the logarithms of the two possible new integers at the middle cut.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def correctedProperPrefix (x : ℝ) :=
  fullLogProperPrefix 1 x-2*x^(1/2:ℝ)-3*x^(1/3:ℝ)

def squareCenteredCompositePrice (n : ℕ) :=
  oddSmoothCompositePrice n-unitaryMidpointCenter n-primeMidpointPrice n-
    2*midpointPowerGap (1/2)*Real.sqrt n

def correctedBalancedCompositePrice (n : ℕ) :=
  squareCenteredCompositePrice n-3*midpointPowerGap (1/3)*(n:ℝ)^(1/3:ℝ)

private theorem first_two_prime_rows {t : ℝ} (ht : 1/4≤t) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n → ∀ x : ℝ, 1≤x →
      |fullLogProperPrefix n x- (2*Chebyshev.theta (x^(1/2:ℝ))+3*Chebyshev.theta (x^(1/3:ℝ)))|
        ≤ 16*Real.log n+C*x^t := by
  obtain ⟨C,hC,h⟩ := uniform_full_log_truncation (J:=4) (by decide) (b:=t)
    (lt_of_lt_of_le (by norm_num) ht)
  have hlog := Real.log_nonneg (by norm_num : (1:ℝ)≤4)
  refine ⟨C+4*Real.log 4,add_nonneg hC (mul_nonneg (by norm_num) hlog),fun n hn x hx => ?_⟩
  have he : Icc 2 4=({2,3,4}:Finset ℕ) := by decide
  have hh := h n hn x hx
  simp only [he,sum_insert (by decide : 2∉({3,4}:Finset ℕ)),sum_insert (by decide : 3∉({4}:Finset ℕ)),
    sum_singleton,Nat.cast_ofNat,show (4:ℝ)^2=16 by norm_num] at hh
  -- The fourth row is bounded at the endpoint itself; only the fifth and later rows need a strict gap.
  have hθ := Chebyshev.theta_nonneg (x^(1/4:ℝ))
  have hu := (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg (zero_le_one.trans hx) (1/4:ℝ))).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ht) hlog)
  rw [abs_le] at hh ⊢
  constructor <;> linarith only [hh.1,hh.2,hθ,hu]

/-- Fourth and higher powers cost at most a quarter power.
The two surviving terms are genuine prime errors at distinct roots. -/
theorem corrected_prefix_prime_errors {t : ℝ} (ht : 1/4≤t) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 1≤x →
      |correctedProperPrefix x - (2*(Chebyshev.theta (x^(1/2:ℝ))-x^(1/2:ℝ))+
        3*(Chebyshev.theta (x^(1/3:ℝ))-x^(1/3:ℝ)))| ≤ C*x^t := by
  obtain ⟨C,hC,h⟩ := first_two_prime_rows ht
  refine ⟨C,hC,fun x hx => ?_⟩
  have he := h 1 (by decide) x hx
  simp only [Nat.cast_one,Real.log_one,mul_zero,zero_add] at he
  convert he using 2
  unfold correctedProperPrefix
  ring

private theorem corrected_profile_midpoint {x : ℝ} (hx : 0≤x) :
    realMidpointObservation correctedProperPrefix x = realMidpointObservation (fullLogProperPrefix 1) x -
      2*midpointPowerGap (1/2)*x^(1/2:ℝ)-3*midpointPowerGap (1/3)*x^(1/3:ℝ) := by
  have h₂ := real_midpoint_of_power (1/2) hx
  have h₃ := real_midpoint_of_power (1/3) hx
  simp only [realMidpointObservation,correctedProperPrefix] at h₂ h₃ ⊢
  linarith only [h₂,h₃]

/-- The coprimality center can be removed from the corrected observation
at the quarter power and every larger power. -/
theorem corrected_composite_price_reads_the_prefix {t : ℝ} (ht : 1/4≤t) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 1≤n →
      |correctedBalancedCompositePrice n-realMidpointObservation correctedProperPrefix n|≤C*(n:ℝ)^t := by
  obtain ⟨C,hC,h⟩ := first_two_prime_rows ht
  have ht₀ : 0<t := (by norm_num : (0:ℝ)<1/4).trans_le ht
  let K := 16/t + 2*C*(4:ℝ)^t
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨4*K,by positivity,fun n hn => ?_⟩
  have hcut (k : ℕ) (hk : 1≤k) (h4 : k≤4) :
      |fullLogProperPrefix n (k*n:ℕ)-fullLogProperPrefix 1 ((k:ℝ)*n)|≤K*(n:ℝ)^t := by
    have hx : 1≤((k*n:ℕ):ℝ) := Nat.one_le_cast.mpr (Nat.mul_pos hk hn)
    have hu := abs_le.mp (h n hn (k*n:ℕ) hx)
    have hv := abs_le.mp (h 1 (by decide) (k*n:ℕ) hx)
    simp only [Nat.cast_one,Real.log_one,mul_zero,zero_add] at hv
    have hk' := Real.rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) k) (by exact_mod_cast h4 : (k:ℝ)≤4) ht₀.le
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk' (Real.rpow_nonneg (Nat.cast_nonneg n) t)) hC
    have hl := Real.log_le_rpow_div (Nat.cast_nonneg (α:=ℝ) n) ht₀
    simp only [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hu hv ⊢
    rw [abs_le]
    dsimp only [K]
    simp only [div_eq_mul_inv] at hl ⊢
    constructor <;> linarith only [hu.1,hu.2,hv.1,hv.2,hh,hl]
  have h₂ := abs_le.mp (hcut 2 (by decide) (by decide))
  have h₃ := abs_le.mp (hcut 3 (by decide) (by decide))
  have h₄ := abs_le.mp (hcut 4 (by decide) le_rfl)
  rw [correctedBalancedCompositePrice,squareCenteredCompositePrice,Real.sqrt_eq_rpow,composite_midpoint_minus_prime hn,
    corrected_profile_midpoint (Nat.cast_nonneg _),
    realMidpointObservation,abs_le]
  simp only [Nat.cast_ofNat] at h₂ h₃ h₄
  constructor <;> linarith only [h₂.1,h₂.2,h₃.1,h₃.2,h₄.1,h₄.2]

private theorem pure_power_price_bounds (k : ℕ) :
    0≤purePowerLog 1 k ∧ purePowerLog 1 k≤Real.log k := by
  unfold purePowerLog
  split <;> exact ⟨by first | exact Real.log_natCast_nonneg _ | exact le_rfl,
    by first | exact le_rfl | exact Real.log_natCast_nonneg _⟩

private theorem proper_prefix_mono : Monotone (fullLogProperPrefix 1) := by
  intro x y hxy
  unfold fullLogProperPrefix
  apply sum_le_sum_of_subset_of_nonneg _ (fun k _ _ => (pure_power_price_bounds k).1)
  intro k hk
  exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2.trans (Nat.floor_mono hxy)⟩

private theorem proper_prefix_increment {a b : ℕ} (hab : a≤b) :
    fullLogProperPrefix 1 b-fullLogProperPrefix 1 a≤((b:ℝ)-a)*Real.log b := by
  simp only [fullLogProperPrefix,Nat.floor_natCast]
  have hs := sum_Ioc_consecutive (purePowerLog 1) (Nat.zero_le a) hab
  rw [←hs,add_sub_cancel_left]
  calc _ ≤ ∑ _k ∈ Ioc a b, Real.log b := by
         apply sum_le_sum
         intro k hk
         exact (pure_power_price_bounds k).2.trans (Real.log_le_log
           (Nat.cast_pos.mpr ((Nat.zero_le a).trans_lt (mem_Ioc.mp hk).1)) (Nat.cast_le.mpr (mem_Ioc.mp hk).2))
       _ = _ := by rw [sum_const,Nat.card_Ioc,nsmul_eq_mul,Nat.cast_sub hab]

/-- The rounded outer cuts have favorable signs. Only the two possible
new full logarithms at the central cut must be paid. -/
theorem corrected_prefix_midpoint_rounding {t : ℝ} (ht : 0<t) {x : ℝ} (hx : 0<x) :
    realMidpointObservation correctedProperPrefix x ≤ realMidpointObservation correctedProperPrefix ⌊x⌋₊ +
      (4*(3:ℝ)^t/t)*x^t := by
  let n := ⌊x⌋₊
  let m := ⌊3*x⌋₊
  have hn : (n:ℝ)≤x := Nat.floor_le hx.le
  have hm : (m:ℝ)≤3*x := Nat.floor_le (by positivity)
  have hu := Nat.lt_floor_add_one x
  have hl : 3*n ≤ m := Nat.le_floor (by push_cast; linarith only [hn])
  have hdiff : (m:ℝ)-(3*n:ℕ)≤2 := by
    have hb : (m:ℝ)<((3*n+3:ℕ):ℝ) := by push_cast; dsimp only [n] at *; linarith only [hm,hu]
    have hh : m≤3*n+2 := by have := (Nat.cast_lt (α:=ℝ)).mp hb; omega
    have hcast := (Nat.cast_le (α:=ℝ)).mpr hh
    push_cast at hcast ⊢
    linarith only [hcast]
  have hlog := (Real.log_le_rpow_div (Nat.cast_nonneg (α:=ℝ) m) ht).trans
    (div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hm ht.le) ht.le)
  have hp := (proper_prefix_increment hl).trans
    (mul_le_mul hdiff hlog (Real.log_natCast_nonneg m) (by norm_num : (0:ℝ)≤2))
  have hfloor : fullLogProperPrefix 1 (3*x)=fullLogProperPrefix 1 m := by simp [fullLogProperPrefix,m]
  have hout (k : ℝ) (hk : 0≤k) := proper_prefix_mono (mul_le_mul_of_nonneg_left hn hk)
  have hpow {b : ℝ} (hb : b∈Set.Ioo (0:ℝ) 1) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) n) hn hb.1.le) (midpointPowerGap_pos hb).le
  have h₂ := hpow (b:=1/2) ⟨by norm_num,by norm_num⟩
  have h₃ := hpow (b:=1/3) ⟨by norm_num,by norm_num⟩
  rw [corrected_profile_midpoint hx.le,corrected_profile_midpoint (Nat.cast_nonneg _)]
  change realMidpointObservation (fullLogProperPrefix 1) x - _ - _ ≤
    realMidpointObservation (fullLogProperPrefix 1) (n:ℝ) - _ - _ + _
  simp only [realMidpointObservation,hfloor]
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num : (0:ℝ)≤3) hx.le] at hp
  simp only [div_eq_mul_inv] at hp h₂ h₃ ⊢
  linarith only [hp,h₂,h₃,hout 2 (by norm_num),hout 4 (by norm_num)]

#print axioms corrected_prefix_prime_errors
#print axioms corrected_composite_price_reads_the_prefix
#print axioms corrected_prefix_midpoint_rounding

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
