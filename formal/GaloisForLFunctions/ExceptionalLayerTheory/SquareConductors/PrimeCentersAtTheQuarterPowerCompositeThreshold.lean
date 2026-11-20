import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheHalfAbscissaOfTheBalancedCompositeRemainder
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeSamplingDownToSevenTwelfths

/-!
# Sampling the corrected composite midpoint only at primes

A displacement of size n^(2/3) moves the square and cube roots by at
most a constant times n^(1/6). Even after charging one logarithm per
crossed integer, this costs at most a quarter power. Prime centers
therefore retain the full half-abscissa of the corrected composite price.
At primes above four its coprimality restriction is exactly redundant.
-/

noncomputable section
open Finset Filter
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- A proper power at most 4p cannot be divisible by the prime p>4. -/
theorem unrestricted_proper_prefix_at_a_prime {p : ℕ} (hp : p.Prime) (hp₄ : 4<p)
    {x : ℝ} (hx : x≤4*(p:ℝ)) : fullLogProperPrefix p x=fullLogProperPrefix 1 x := by
  unfold fullLogProperPrefix
  apply sum_congr rfl
  intro k hk
  by_cases h : ¬k.Prime ∧ k.primeFactors.card=1
  · have hcop : p.Coprime k := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      obtain ⟨q,j,hq,hj,he⟩ := (isPrimePow_nat_iff k).mp (isPrimePow_iff_card_primeFactors_eq_one.mpr h.2)
      have hdiv : p ∣ q^j := he.symm ▸ hd
      have heq : q=p := ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdiv)).symm
      subst q
      have hj₂ : 2≤j := by
        by_contra! hsmall
        obtain rfl : j=1 := by omega
        exact h.1 (he ▸ (by simpa using hp : (p^1).Prime))
      have hlast : k≤4*p := (mem_Ioc.mp hk).2.trans (Nat.floor_le_of_le (by exact_mod_cast hx))
      have hs := Nat.pow_le_pow_right hp.pos hj₂
      rw [he] at hs
      have hbig := Nat.mul_lt_mul_of_pos_right hp₄ hp.pos
      rw [pow_two] at hs
      omega
    rw [purePowerLog,purePowerLog,if_pos (And.intro hcop h),if_pos (And.intro (Nat.coprime_one_left k) h)]
  · have h₁ : ¬(p.Coprime k ∧ ¬k.Prime ∧ k.primeFactors.card=1) := fun he => h he.2
    have h₂ : ¬(Nat.Coprime 1 k ∧ ¬k.Prime ∧ k.primeFactors.card=1) := fun he => h he.2
    rw [purePowerLog,purePowerLog,if_neg h₁,if_neg h₂]

/-- Above the two exceptional primes, the entire signed difference
between the centered composite and prime prices uses one fixed prefix. -/
theorem unrestricted_composite_midpoint_at_a_prime {p : ℕ} (hp : p.Prime) (hp₄ : 4<p) :
    oddSmoothCompositePrice p-unitaryMidpointCenter p-primeMidpointPrice p =
      realMidpointObservation (fullLogProperPrefix 1) p := by
  have cut (k : ℕ) (hk : k≤4) :
      fullLogProperPrefix p (k*p:ℕ)=fullLogProperPrefix 1 ((k:ℝ)*p) := by
    rw [Nat.cast_mul]
    exact unrestricted_proper_prefix_at_a_prime hp hp₄
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (Nat.cast_nonneg p))
  rw [composite_midpoint_minus_prime hp.pos,cut 3 (by decide),cut 2 (by decide),cut 4 le_rfl]
  rfl

/-- At every prime above four, correcting the observed price agrees
exactly with applying the three cuts to the fixed corrected prefix. -/
theorem corrected_composite_is_the_fixed_prefix_at_primes {p : ℕ} (hp : p.Prime) (hp₄ : 4<p) :
    correctedBalancedCompositePrice p=realMidpointObservation correctedProperPrefix p := by
  have hs := real_midpoint_of_power (1/2) (Nat.cast_nonneg (α:=ℝ) p)
  have hc := real_midpoint_of_power (1/3) (Nat.cast_nonneg (α:=ℝ) p)
  rw [correctedBalancedCompositePrice,squareCenteredCompositePrice,unrestricted_composite_midpoint_at_a_prime hp hp₄,
    Real.sqrt_eq_rpow]
  simp only [realMidpointObservation,correctedProperPrefix] at hs hc ⊢
  linarith only [hs,hc]

private theorem root_displacement {x y a : ℝ} (hx : 1≤x) (hxy : x≤y) (hy : y≤x+x^(2/3:ℝ))
    (ha : a≤1/2) : y^a-x^a≤x^(1/6:ℝ) := by
  have hx₀ := zero_lt_one.trans_le hx
  have hy₀ := hx₀.trans_le hxy
  have hrat : 1≤y/x := (one_le_div hx₀).mpr hxy
  have hr := (Real.rpow_le_rpow_of_exponent_le hrat (ha.trans (by norm_num : (1/2:ℝ)≤1))).trans_eq (Real.rpow_one _)
  have he : (y/x)^a*x^a=y^a := by rw [←Real.mul_rpow (div_nonneg hy₀.le hx₀.le) hx₀.le,div_mul_cancel₀ _ hx₀.ne']
  have hcost : x^(2/3:ℝ)*(x^(1/2:ℝ)/x)=x^(1/6:ℝ) := by
    rw [←mul_div_assoc,←Real.rpow_add hx₀]
    calc x^((2/3:ℝ)+1/2)/x = x^((2/3:ℝ)+1/2-1) := by
           rw [Real.rpow_sub hx₀,Real.rpow_one]
         _ = x^(1/6:ℝ) := by norm_num
  calc y^a-x^a ≤ (y/x)*x^a-x^a := by
         rw [←he]
         exact sub_le_sub_right (mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hx₀.le _)) _
       _ = (y-x)*(x^a/x) := by field_simp [hx₀.ne']
       _ ≤ x^(2/3:ℝ)*(x^(1/2:ℝ)/x) := mul_le_mul (by linarith only [hy])
         (div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx ha) hx₀.le)
         (div_nonneg (Real.rpow_nonneg hx₀.le _) hx₀.le) (Real.rpow_nonneg hx₀.le _)
       _ = _ := hcost

private theorem shifted_prime_error_at_a_root {x y k a : ℝ} (hx : 1≤x) (hxy : x≤y)
    (hy : y≤x+x^(2/3:ℝ)) (hk : 1≤k) (hk₄ : k≤4) (ha : 0≤a) (ha' : a≤1/2) :
    |(Chebyshev.theta ((k*y)^a)-(k*y)^a) - (Chebyshev.theta ((k*x)^a)-(k*x)^a)|≤484*x^(1/4:ℝ) := by
  let u := (k*x)^a
  let v := (k*y)^a
  have hx₀ := zero_lt_one.trans_le hx
  have hy₀ := hx₀.trans_le hxy
  have hk₀ := zero_lt_one.trans_le hk
  have huv : u≤v := Real.rpow_le_rpow (mul_nonneg hk₀.le hx₀.le) (mul_le_mul_of_nonneg_left hxy hk₀.le) ha
  have hu₁ : 1≤u := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hk hx) ha
  have hv₁ := hu₁.trans huv
  have ha₁ := ha'.trans (by norm_num : (1/2:ℝ)≤1)
  have hdist : v-u≤4*x^(1/6:ℝ) := by
    change (k*y)^a-(k*x)^a≤_
    rw [Real.mul_rpow hk₀.le hy₀.le,Real.mul_rpow hk₀.le hx₀.le,←mul_sub]
    exact mul_le_mul ((Real.rpow_le_rpow_of_exponent_le hk ha₁).trans ((Real.rpow_one k).le.trans hk₄))
      (root_displacement hx hxy hy ha') (sub_nonneg.mpr (Real.rpow_le_rpow hx₀.le hxy ha)) (by norm_num)
  have hy₂ : y≤2*x := by
    have he := (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (2/3:ℝ)≤1)).trans_eq (Real.rpow_one x)
    linarith only [hy,he]
  have hv : v≤8*x := by
    apply (Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le hk (hx.trans hxy)) ha₁).trans
    rw [Real.rpow_one]
    linarith only [mul_le_mul hk₄ hy₂ hy₀.le (by norm_num : (0:ℝ)≤4)]
  let A := ⌊u⌋₊
  let B := ⌊v⌋₊
  have hB : (B:ℝ)≤v := Nat.floor_le (zero_le_one.trans hv₁)
  have hg : (B:ℝ)-A≤5*x^(1/6:ℝ) := by
    have hA := Nat.lt_floor_add_one u
    have hone := Real.one_le_rpow hx (by norm_num : (0:ℝ)≤1/6)
    dsimp only [A]
    linarith only [hB,hA,hdist,hone]
  have hlog : Real.log B≤96*x^(1/12:ℝ) := by
    have hl := Real.log_le_rpow_div (Nat.cast_nonneg (α:=ℝ) B) (by norm_num : (0:ℝ)<1/12)
    have hb := Real.rpow_le_rpow (Nat.cast_nonneg (α:=ℝ) B) (hB.trans hv) (by norm_num : (0:ℝ)≤1/12)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤8) hx₀.le] at hb
    have hc : (8:ℝ)^(1/12:ℝ)≤8 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (1/12:ℝ)≤1)).trans_eq (Real.rpow_one 8)
    linarith only [hl,hb,mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hx₀.le (1/12:ℝ))]
  have hθ := (theta_integer_interval_bound (Nat.floor_mono huv)).trans
    (mul_le_mul hg hlog (Real.log_natCast_nonneg B) (by positivity))
  have hp : (5*x^(1/6:ℝ))*(96*x^(1/12:ℝ))=480*x^(1/4:ℝ) := by
    rw [show (1/4:ℝ)=1/6+1/12 by norm_num,Real.rpow_add hx₀]
    ring
  rw [hp] at hθ
  have hout : Chebyshev.theta v-Chebyshev.theta u≤480*x^(1/4:ℝ) := by
    rw [Chebyshev.theta_eq_theta_coe_floor v,Chebyshev.theta_eq_theta_coe_floor u]
    exact hθ
  have hd := hdist.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1/6:ℝ)≤1/4)) (by norm_num))
  change |(Chebyshev.theta v-v)-(Chebyshev.theta u-u)|≤_
  rw [abs_le]
  have hpos := Real.rpow_nonneg hx₀.le (1/4:ℝ)
  constructor <;> linarith only [hout,hd,huv,Chebyshev.theta_mono huv,hpos]

/-- The corrected composite price varies by O(n^t), for every t≥1/4,
throughout n ≤ p ≤ n+n^(2/3). The second center can be any integer. -/
theorem corrected_composite_shift_on_two_thirds_window {t : ℝ} (ht : 1/4≤t) :
    ∃ B : ℝ, 0≤B ∧ ∀ {n p : ℕ}, 1≤n → n≤p → (p:ℝ)≤n+(n:ℝ)^(2/3:ℝ) →
      (p:ℝ)≤2*n ∧ |correctedBalancedCompositePrice n-correctedBalancedCompositePrice p|≤B*(n:ℝ)^t := by
  obtain ⟨C,hC,h⟩ := corrected_prefix_prime_errors ht
  obtain ⟨L,hL,hL'⟩ := corrected_composite_price_reads_the_prefix ht
  have ht₀ := (by norm_num : (0:ℝ)<1/4).trans_le ht
  let K := 2*C*(8:ℝ)^t+2420
  have hK : 0≤K := by dsimp only [K]; positivity
  refine ⟨4*K+L*(1+(2:ℝ)^t),by positivity,?_⟩
  intro n p hn hnp hgap
  have hx := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hxy := (Nat.cast_le (α:=ℝ)).mpr hnp
  have hy := hx.trans hxy
  have hy₂ : (p:ℝ)≤2*n := by
    have he := (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (2/3:ℝ)≤1)).trans_eq (Real.rpow_one _)
    linarith only [hgap,he]
  refine ⟨hy₂,?_⟩
  have hquarter := Real.rpow_le_rpow_of_exponent_le hx ht
  have hcut (k : ℝ) (hk : 1≤k) (hk₄ : k≤4) :
      |correctedProperPrefix (k*p)-correctedProperPrefix (k*n)|≤K*(n:ℝ)^t := by
    have he {m : ℕ} (hm : 1≤(m:ℝ)) := h (k*m) (one_le_mul_of_one_le_of_one_le hk hm)
    have hpay {m : ℕ} (hm : (m:ℝ)≤2*n) : C*(k*m)^t≤C*((8:ℝ)^t*(n:ℝ)^t) := by
      rw [←Real.mul_rpow (by norm_num : (0:ℝ)≤8) (Nat.cast_nonneg n)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
        (by linarith only [mul_le_mul hk₄ hm (Nat.cast_nonneg m) (by norm_num : (0:ℝ)≤4)] : k*m≤8*n) ht₀.le) hC
    have hn₂ : (n:ℝ)≤2*n := by linarith only [hx]
    have h₁ := abs_le.mp ((he hx).trans (hpay hn₂))
    have h₂ := abs_le.mp ((he hy).trans (hpay hy₂))
    have hs := abs_le.mp (shifted_prime_error_at_a_root hx hxy hgap hk hk₄ (by norm_num : (0:ℝ)≤1/2) le_rfl)
    have hc := abs_le.mp (shifted_prime_error_at_a_root hx hxy hgap hk hk₄ (by norm_num : (0:ℝ)≤1/3) (by norm_num))
    rw [abs_le]
    dsimp only [K]
    constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hs.1,hs.2,hc.1,hc.2,hquarter]
  have hp := (Real.rpow_le_rpow (Nat.cast_nonneg _) hy₂ ht₀.le).trans_eq (Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg n))
  have hn' := abs_le.mp (hL' n hn)
  have hp' := abs_le.mp ((hL' p (hn.trans hnp)).trans (mul_le_mul_of_nonneg_left hp hL))
  have s₂ := abs_le.mp (hcut 2 (by norm_num) (by norm_num))
  have s₃ := abs_le.mp (hcut 3 (by norm_num) (by norm_num))
  have s₄ := abs_le.mp (hcut 4 (by norm_num) le_rfl)
  simp only [realMidpointObservation] at hn' hp'
  rw [abs_le]
  constructor <;> linarith only [hn'.1,hn'.2,hp'.1,hp'.2,s₂.1,s₂.2,s₃.1,s₃.2,s₄.1,s₄.2]

/-- Every fixed upper power transfers from the prime centers to all
integer centers, including the exact quarter power. -/
theorem composite_power_bound_from_prime_centers {t : ℝ} (ht : 1/4≤t)
    (h : ∃ C : ℝ, ∀ p : ℕ, p.Prime → correctedBalancedCompositePrice p≤C*(p:ℝ)^t) :
    ∃ A : ℝ, ∀ n : ℕ, 1≤n → correctedBalancedCompositePrice n≤A*(n:ℝ)^t := by
  obtain ⟨C,hC⟩ := h
  obtain ⟨B,hB,hshift⟩ := corrected_composite_shift_on_two_thirds_window ht
  have ht₀ : 0<t := (by norm_num : (0:ℝ)<1/4).trans_le ht
  have hh := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (_root_.RHTower.eventually_exists_prime_short_interval_seven_twelfths (by norm_num : (7/12:ℝ)<2/3) (by norm_num))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  let A := ∑ j ∈ range N, |correctedBalancedCompositePrice j|
  have hA : 0≤A := sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨A+B+|C| * (2:ℝ)^t,fun n hn => ?_⟩
  have hx := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hpow := Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) n) t
  by_cases hsmall : n<N
  · have he := single_le_sum (fun j (_ : j∈range N) => abs_nonneg (correctedBalancedCompositePrice j)) (mem_range.mpr hsmall)
    apply ((le_abs_self _).trans he).trans
    change A≤_
    have hh : A≤A+B+|C| * (2:ℝ)^t :=
      (le_add_of_nonneg_right hB).trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg C) (by positivity)))
    exact hh.trans (le_mul_of_one_le_right (hA.trans hh) (Real.one_le_rpow hx ht₀.le))
  · obtain ⟨p,hp,hnp,hgap⟩ := hN n (le_of_not_gt hsmall)
    have hnp' : n<p := by exact_mod_cast hnp
    obtain ⟨hp₂,he⟩ := hshift hn hnp'.le hgap
    have hpow' := (Real.rpow_le_rpow (Nat.cast_nonneg _) hp₂ ht₀.le).trans_eq
      (Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg n))
    have hpaid := (hC p hp).trans (mul_le_mul (le_abs_self C) hpow' (Real.rpow_nonneg (Nat.cast_nonneg p) _) (abs_nonneg C))
    linarith only [(abs_le.mp he).2,hpaid,mul_nonneg hA hpow]

/-- Prime centers alone retain the full half-abscissa of the corrected price. -/
theorem prime_center_composite_half_abscissa {b : ℝ} (hb : 1/4≤b) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ C : ℝ, ∀ p : ℕ, p.Prime → correctedBalancedCompositePrice p≤C*(p:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa≤2*b := by
  rw [←corrected_composite_upper_spectrum_iff hb]
  refine ⟨fun h t hbt hhalf => composite_power_bound_from_prime_centers (hb.trans hbt.le) (h t hbt hhalf),?_⟩
  intro h t hbt hhalf
  obtain ⟨C,hC⟩ := h t hbt hhalf
  exact ⟨C,fun p hp => hC p hp.pos⟩

/-- Every constant at the exact quarter power is exceeded along
arbitrarily large prime centers. The prime-gap displacement costs
only a fixed multiple of the same quarter power. -/
theorem unbounded_quarter_power_at_prime_centers (A : ℝ) :
    ∃ᶠ p : ℕ in atTop, p.Prime ∧ A*(p:ℝ)^(1/4:ℝ)<correctedBalancedCompositePrice p := by
  obtain ⟨B,_,hs⟩ := corrected_composite_shift_on_two_thirds_window (t:=1/4) le_rfl
  have hpr := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (_root_.RHTower.eventually_exists_prime_short_interval_seven_twelfths (by norm_num : (7/12:ℝ)<2/3) (by norm_num))
  have hf := (unbounded_quarter_power_composite_surplus (B+|A| * (2:ℝ)^(1/4:ℝ))).and_eventually
    (hpr.and (eventually_ge_atTop 1))
  rw [frequently_atTop]
  intro N
  obtain ⟨n,hN,he,⟨p,hp,hnp,hgap⟩,hn⟩ := frequently_atTop.mp hf N
  have hnp' : n<p := by exact_mod_cast hnp
  obtain ⟨hp₂,hshift⟩ := hs hn hnp'.le hgap
  have hu := (Real.rpow_le_rpow (Nat.cast_nonneg _) hp₂ (by norm_num : (0:ℝ)≤1/4)).trans_eq
    (Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg n))
  have hpay := mul_le_mul (le_abs_self A) hu (Real.rpow_nonneg (Nat.cast_nonneg p) _) (abs_nonneg A)
  refine ⟨p,hN.trans hnp'.le,hp,?_⟩
  linarith only [he,(abs_le.mp hshift).2,hpay]

/-- Upper quarter-power control sampled at primes characterizes RH. -/
theorem prime_center_quarter_power_iff_riemannHypothesis :
    (∀ t : ℝ, 1/4<t → t<1/2 → ∃ A : ℝ, ∀ p : ℕ, p.Prime →
      correctedBalancedCompositePrice p≤A*(p:ℝ)^t) ↔ RiemannHypothesis :=
  ((prime_center_composite_half_abscissa le_rfl).trans
    (corrected_composite_upper_spectrum_iff le_rfl).symm).trans
      riemannHypothesis_iff_quarter_power_composite_remainder.symm

/-- Three values of one fixed proper-power prefix at each prime center
suffice to test the zero abscissa. -/
theorem fixed_prefix_at_prime_centers_iff {b : ℝ} (hb : 1/4≤b) :
    (∀ t : ℝ, b<t → t<1/2 → ∃ A : ℝ, ∀ p : ℕ, p.Prime →
      realMidpointObservation correctedProperPrefix p≤A*(p:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa≤2*b := by
  rw [←prime_center_composite_half_abscissa hb]
  constructor
  · intro h t ht hu
    obtain ⟨A,hA⟩ := h t ht hu
    obtain ⟨C,_,he⟩ := corrected_composite_price_reads_the_prefix (hb.trans ht.le)
    exact ⟨A+C,fun p hp => by linarith only [(abs_le.mp (he p hp.pos)).2,hA p hp]⟩
  · intro h t ht hu
    obtain ⟨A,hA⟩ := h t ht hu
    obtain ⟨C,_,he⟩ := corrected_composite_price_reads_the_prefix (hb.trans ht.le)
    exact ⟨A+C,fun p hp => by linarith only [(abs_le.mp (he p hp.pos)).1,hA p hp]⟩

/-- The square correction alone at prime centers detects the 11/3
conductor-prefix bound. The cube bias is below every testing power. -/
theorem square_corrected_prime_centers_iff_eleven_thirds :
    (∀ t : ℝ, 5/12<t → t<1/2 → ∃ A : ℝ, ∀ p : ℕ, p.Prime →
      squareCenteredCompositePrice p≤A*(p:ℝ)^t) ↔
      ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N|≤C*(N:ℝ)^(11/3:ℝ) := by
  rw [←five_sixths_iff_seventeenNinthsConductorPrefix,
    show (5/6:ℝ)=2*(5/12) by norm_num,
    ←prime_center_composite_half_abscissa (by norm_num : (1/4:ℝ)≤5/12)]
  let g := 3*midpointPowerGap (1/3)
  have hg : 0≤g := mul_nonneg (by norm_num) (midpointPowerGap_pos ⟨by norm_num,by norm_num⟩).le
  constructor
  · intro h t ht hu
    obtain ⟨A,hA⟩ := h t ht hu
    exact ⟨A,fun p hp => (sub_le_self _ (mul_nonneg hg (Real.rpow_nonneg (Nat.cast_nonneg p) _))).trans (hA p hp)⟩
  · intro h t ht hu
    obtain ⟨A,hA⟩ := h t ht hu
    refine ⟨A+g,fun p hp => ?_⟩
    have he := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (Nat.one_le_cast.mpr hp.pos) ((by norm_num : (1/3:ℝ)≤5/12).trans ht.le)) hg
    have hh := hA p hp
    change squareCenteredCompositePrice p-g*(p:ℝ)^(1/3:ℝ)≤A*(p:ℝ)^t at hh
    linarith only [hh,he]

#print axioms unrestricted_proper_prefix_at_a_prime
#print axioms unrestricted_composite_midpoint_at_a_prime
#print axioms corrected_composite_is_the_fixed_prefix_at_primes
#print axioms corrected_composite_shift_on_two_thirds_window
#print axioms composite_power_bound_from_prime_centers
#print axioms unbounded_quarter_power_at_prime_centers
#print axioms prime_center_composite_half_abscissa
#print axioms prime_center_quarter_power_iff_riemannHypothesis
#print axioms fixed_prefix_at_prime_centers_iff
#print axioms square_corrected_prime_centers_iff_eleven_thirds

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
