import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGreenSeriesOfThePrimeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheStabilityWindowOfIntegerMidpointInversion
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RoughCofactorsAtPrimorialMidpoints

/-!
# One-sided recovery of the ordinary-prime error with an explicit constant

The inverse midpoint operator preserves order. On the power x^s its
unnormalized eigenvalue is 2·3^s−2^s−4^s. Summing the positive Green
kernel transfers an upper bound to the prime error with the reciprocal
of this eigenvalue as coefficient.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def midpointPowerGap (s : ℝ) := 2*(3:ℝ)^s-(2:ℝ)^s-(4:ℝ)^s

theorem midpointPowerGap_eq (s : ℝ) :
    midpointPowerGap s=2*(3:ℝ)^s*(1-ternaryPowerGain s) := by
  unfold midpointPowerGap
  linarith only [ternary_gain_balance s]

theorem midpointPowerGap_pos {s : ℝ} (hs : s∈Set.Ioo (0:ℝ) 1) : 0 < midpointPowerGap s := by
  rw [midpointPowerGap_eq]
  exact mul_pos (by positivity) (sub_pos.mpr ((ternary_gain_phase s).1.mpr hs))

def midpointNormalizedPower (s t : ℝ) := (Real.exp t)^(s-1)

private theorem powerPrice_shift (s t d : ℝ) (hd : 0<d) :
    midpointNormalizedPower s (t+Real.log d)=midpointNormalizedPower s t*d^(s-1) := by
  rw [midpointNormalizedPower,midpointNormalizedPower,Real.exp_add,Real.exp_log hd,Real.mul_rpow (Real.exp_pos _).le hd.le]

private theorem gain_on_prices (s : ℝ) :
    (2/3:ℝ)^(s-1)/3+2*(4/3:ℝ)^(s-1)/3=ternaryPowerGain s := by
  have h (d : ℝ) (hd : 0<d) : d^s=d^(s-1)*d := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hd.ne' (s-1)
  unfold ternaryPowerGain
  rw [h (2/3) (by norm_num),h (4/3) (by norm_num)]
  ring

/-- At every depth a power majorant propagates with exactly the scalar
gain from integer ternary inversion. Signed constants are allowed. -/
private theorem walk_power_bound {f : ℝ → ℝ} (s A : ℝ)
    (hf : ∀ u, f u≤A*midpointNormalizedPower s u) (n : ℕ) (t : ℝ) :
    midpointLogWalk n f t ≤ A*midpointNormalizedPower s t*(ternaryPowerGain s)^n := by
  induction n generalizing t with
  | zero => rw [show midpointLogWalk 0 f t=f t by rfl,pow_zero,mul_one]; exact hf t
  | succ n ih =>
    have h₁ := ih (t+Real.log (2/3:ℝ))
    have h₂ := ih (t+Real.log (4/3:ℝ))
    rw [powerPrice_shift s t (2/3) (by norm_num)] at h₁
    rw [powerPrice_shift s t (4/3) (by norm_num)] at h₂
    rw [midpointLogWalk_succ,pow_succ]
    have he := congrArg (fun z : ℝ => A*midpointNormalizedPower s t*(ternaryPowerGain s)^n*z) (gain_on_prices s)
    linarith only [h₁,h₂,he]

/-- Positive summation transfers two distinct power majorants without
mixing their constants. The second may represent rounding error. -/
theorem two_power_prime_green_bound {s d : ℝ} (hs : s∈Set.Ioo (0:ℝ) 1)
    (hd : d∈Set.Ioo (0:ℝ) 1) (A B : ℝ)
    (h : ∀ t, normalizedPrimeMidpoint t ≤ A*midpointNormalizedPower s t+B*midpointNormalizedPower d t) (t : ℝ) :
    normalizedPrimeError t ≤ A*midpointNormalizedPower s t/(1-ternaryPowerGain s)+
      B*midpointNormalizedPower d t/(1-ternaryPowerGain d) := by
  have geom {r : ℝ} (hr : r∈Set.Ioo (0:ℝ) 1) (C : ℝ) :
      HasSum (fun n : ℕ => C*midpointNormalizedPower r t*ternaryPowerGain r^n)
        (C*midpointNormalizedPower r t/(1-ternaryPowerGain r)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one (ternary_gain_pos r).le ((ternary_gain_phase r).1.mpr hr)).mul_left (C*midpointNormalizedPower r t)
  have hu := (geom hs A).add (geom hd B)
  apply le_of_tendsto_of_tendsto (prime_midpoint_green_series t).tendsto_sum_nat hu.tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  apply sum_le_sum
  intro j _
  exact (midpointLogWalk_le_add h j t).trans (add_le_add
    (walk_power_bound s A (fun _ => le_rfl) j t) (walk_power_bound d B (fun _ => le_rfl) j t))

/-- Three real dilations in the same unnormalized coordinates as D(n). -/
def realMidpointObservation (f : ℝ → ℝ) (y : ℝ) := 2*f (3*y)-f (2*y)-f (4*y)

/-- The power profile pays exactly the Mellin gap, at every scale. -/
theorem real_midpoint_of_power (s : ℝ) {y : ℝ} (hy : 0≤y) :
    realMidpointObservation (fun x => x^s) y=midpointPowerGap s*y^s := by
  simp only [realMidpointObservation,midpointPowerGap,Real.mul_rpow (by norm_num : 0≤(3:ℝ)) hy,
    Real.mul_rpow (by norm_num : 0≤(2:ℝ)) hy,Real.mul_rpow (by norm_num : 0≤(4:ℝ)) hy]
  ring

private theorem divide_power_by_scale (s : ℝ) {x : ℝ} (hx : 0<x) :
    (x/3)^s/(2*x)=x^(s-1)/(2*(3:ℝ)^s) := by
  rw [Real.div_rpow hx.le (by norm_num),
    show x^s=x^(s-1)*x by simpa only [sub_add_cancel] using Real.rpow_add_one hx.ne' (s-1)]
  field_simp [hx.ne',(Real.rpow_pos_of_pos (by norm_num : 0<(3:ℝ)) s).ne']

theorem prime_error_of_two_midpoint_powers {s d : ℝ} (hs : s∈Set.Ioo (0:ℝ) 1)
    (hd : d∈Set.Ioo (0:ℝ) 1) (A B : ℝ)
    (h : ∀ y : ℝ, 0<y → realMidpointObservation Chebyshev.theta y ≤ A*y^s+B*y^d)
    {x : ℝ} (hx : 0<x) :
    Chebyshev.theta x-x ≤ (A/midpointPowerGap s)*x^s+(B/midpointPowerGap d)*x^d := by
  have hf (t : ℝ) : normalizedPrimeMidpoint t ≤ (A/(2*(3:ℝ)^s))*midpointNormalizedPower s t+
      (B/(2*(3:ℝ)^d))*midpointNormalizedPower d t := by
    let y := Real.exp t
    have hy : 0<y := Real.exp_pos _
    have hz := div_le_div_of_nonneg_right (h (y/3) (by positivity)) (by positivity : 0≤2*y)
    have he : realMidpointObservation Chebyshev.theta (y/3)/(2*y)=normalizedPrimeMidpoint t := by
      change (2*Chebyshev.theta (3*(y/3))-Chebyshev.theta (2*(y/3))-Chebyshev.theta (4*(y/3)))/(2*y)=_
      rw [show 3*(y/3)=y by ring,show 2*(y/3)=y*(2/3) by ring,show 4*(y/3)=y*(4/3) by ring]
      rfl
    rw [he,add_div,mul_div_assoc,mul_div_assoc,divide_power_by_scale s hy,divide_power_by_scale d hy] at hz
    change _ ≤ A/(2*(3:ℝ)^s)*y^(s-1)+B/(2*(3:ℝ)^d)*y^(d-1)
    exact hz.trans_eq (by ring)
  have hh := two_power_prime_green_bound hs hd _ _ hf (Real.log x)
  simp only [normalizedPrimeError,midpointNormalizedPower,Real.exp_log hx] at hh
  apply ((div_le_iff₀ hx).mp hh).trans_eq
  have hscale (r C : ℝ) : C/(2*(3:ℝ)^r)*x^(r-1)/(1-ternaryPowerGain r)*x=
      C/midpointPowerGap r*x^r := by
    rw [midpointPowerGap_eq,show x^r=x^(r-1)*x by simpa only [sub_add_cancel] using Real.rpow_add_one hx.ne' (r-1)]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [add_mul,hscale,hscale]

/-- Rounding down the central scale loses at most two integer sites at
the positive endpoint 3y. Movement of the other two endpoints helps the
one-sided estimate. -/
theorem prime_midpoint_rounding_cost {d : ℝ} (hd : 0<d) {y : ℝ} (hy : 0<y) :
    realMidpointObservation Chebyshev.theta y ≤ primeMidpointPrice ⌊y⌋₊+
      (4*(3:ℝ)^d/d)*y^d := by
  let n := ⌊y⌋₊
  let z := ⌊3*y⌋₊
  have hn : (n:ℝ)≤y := Nat.floor_le hy.le
  have hz : (z:ℝ)≤3*y := Nat.floor_le (by positivity)
  have hstep : y<(n:ℝ)+1 := Nat.lt_floor_add_one _
  have hl : 3*n ≤ z := Nat.le_floor (by push_cast; linarith only [hn])
  have hu : z ≤ 3*n+2 := by
    have hr : (z:ℝ)<((3*n+3:ℕ):ℝ) := by push_cast; linarith only [hz,hstep]
    have hn' : z<3*n+3 := by exact_mod_cast hr
    omega
  have hdiff : (z:ℝ)-(3*n:ℕ)≤2 := by
    have hb : (z:ℝ) ≤ ((3*n+2:ℕ):ℝ) := Nat.cast_le.mpr hu
    push_cast at hb ⊢
    linarith only [hb]
  have hlog : Real.log z≤(3*y)^d/d := (Real.log_le_rpow_div (Nat.cast_nonneg _) hd).trans
    (div_le_div_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hz hd.le) hd.le)
  have hpaid := mul_le_mul hdiff hlog (Real.log_natCast_nonneg z) (by norm_num : (0:ℝ)≤2)
  have hc := (theta_integer_interval_bound hl).trans hpaid
  have hcut : Chebyshev.theta (3*y)=Chebyshev.theta (z:ℕ) := Chebyshev.theta_eq_theta_coe_floor _
  have out (k : ℕ) : Chebyshev.theta (k*n:ℕ) ≤ Chebyshev.theta ((k:ℝ)*y) := by
    rw [Nat.cast_mul]
    exact Chebyshev.theta_mono (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _))
  have h₂ := out 2
  have h₄ := out 4
  rw [realMidpointObservation,hcut,prime_midpoint_price_eq]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) hy.le] at hc
  norm_num only [Nat.cast_ofNat] at h₂ h₄
  change 2*Chebyshev.theta (z:ℕ)-Chebyshev.theta (2*y)-Chebyshev.theta (4*y)≤
    2*Chebyshev.theta (3*n:ℕ)-Chebyshev.theta (2*n:ℕ)-Chebyshev.theta (4*n:ℕ)+(4*(3:ℝ)^d/d)*y^d
  simp only [div_eq_mul_inv] at hc ⊢
  linarith only [hc,h₂,h₄]

/-- Any smaller positive power can absorb integer rounding while leaving
the coefficient of the measured power exactly equal to the reciprocal gap. -/
theorem prime_error_from_integer_midpoint {s d : ℝ} (hs : s∈Set.Ioo (0:ℝ) 1)
    (hd : d∈Set.Ioo (0:ℝ) 1) {A : ℝ} (hA : 0≤A)
    (h : ∀ n : ℕ, 0<n → primeMidpointPrice n≤A*(n:ℝ)^s) {x : ℝ} (hx : 0<x) :
    Chebyshev.theta x-x ≤ A/midpointPowerGap s*x^s+
      ((4*(3:ℝ)^d/d)/midpointPowerGap d)*x^d := by
  apply prime_error_of_two_midpoint_powers hs hd _ _ _ hx
  intro y hy
  apply (prime_midpoint_rounding_cost hd.1 hy).trans
  apply add_le_add _ le_rfl
  rcases Nat.eq_zero_or_pos ⌊y⌋₊ with hz | hn
  · simpa only [hz,primeMidpointPrice,Nat.mul_zero,Ioc_self,filter_empty,sum_empty,sub_self] using
      mul_nonneg hA (Real.rpow_nonneg hy.le s)
  · exact (h _ hn).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (Nat.floor_le hy.le) hs.1.le) hA)

#print axioms real_midpoint_of_power
#print axioms prime_error_from_integer_midpoint

/-- The gap above its zero-exponent resonance grows at least linearly
up to half order. The chord bound follows from convexity of exp. -/
theorem half_order_chord_of_ternary_gain {d : ℝ} (hd : 0≤d) (hu : d≤1/2) :
    2*d*(1-ternaryPowerGain (1/2))≤1-ternaryPowerGain d := by
  have chord {a : ℝ} (ha : 0<a) : a^d ≤ (1-2*d)+2*d*a^(1/2:ℝ) := by
    have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (Real.log a/2))
      (show 0≤1-2*d by linarith only [hu]) (show 0≤2*d by linarith only [hd]) (by ring)
    simp only [smul_eq_mul,mul_zero,zero_add,Real.exp_zero,mul_one] at h
    rw [Real.rpow_def_of_pos ha,Real.rpow_def_of_pos ha,
      show Real.log a*d=2*d*(Real.log a/2) by ring,show Real.log a*(1/2)=Real.log a/2 by ring]
    exact h
  unfold ternaryPowerGain
  linarith only [chord (by norm_num : 0<(2/3:ℝ)),chord (by norm_num : 0<(4/3:ℝ))]

private theorem rounding_multiplier {d : ℝ} (hd : 0<d) (hu : d≤1/2) :
    (4*(3:ℝ)^d/d)/midpointPowerGap d ≤ 1/(d^2*(1-ternaryPowerGain (1/2))) := by
  have h₀ : 0<1-ternaryPowerGain d := sub_pos.mpr ((ternary_gain_phase d).1.mpr
    ⟨hd,hu.trans_lt (by norm_num)⟩)
  have h₁ : 0<1-ternaryPowerGain (1/2) := sub_pos.mpr ((ternary_gain_phase _).1.mpr
    ⟨by norm_num,by norm_num⟩)
  have hr : 0<(3:ℝ)^d := by positivity
  have he : (4*(3:ℝ)^d/d)/midpointPowerGap d=2/(d*(1-ternaryPowerGain d)) := by
    rw [midpointPowerGap_eq]
    field_simp [hd.ne',h₀.ne',hr.ne']; ring
  rw [he,div_le_div_iff₀ (mul_pos hd h₀) (mul_pos (sq_pos_of_pos hd) h₁)]
  linarith only [mul_le_mul_of_nonneg_left (half_order_chord_of_ternary_gain hd.le hu) hd.le]

private theorem logarithmic_rounding_choice {x : ℝ} (hx : 0<x) :
    ∃ d ∈ Set.Ioo (0:ℝ) 1, ((4*(3:ℝ)^d/d)/midpointPowerGap d)*x^d ≤
      Real.exp 1/(1-ternaryPowerGain (1/2))*(2+max 0 (Real.log x))^2 := by
  let K := 2+max 0 (Real.log x)
  have h₂ : 2≤K := le_add_of_nonneg_right (le_max_left _ _)
  have hK : 0<K := (by norm_num : (0:ℝ)<2).trans_le h₂
  let d := 1/K
  have hd : 0<d := one_div_pos.mpr hK
  have hu : d≤1/2 := one_div_le_one_div_of_le (by norm_num) h₂
  have hp : x^d≤Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx,Real.exp_le_exp]
    change Real.log x*(1/K)≤1
    rw [mul_one_div,div_le_one hK]
    exact (le_max_right 0 _).trans (le_add_of_nonneg_left (by norm_num))
  refine ⟨d,⟨hd,hu.trans_lt (by norm_num)⟩,?_⟩
  have hg : 0<1-ternaryPowerGain (1/2) := sub_pos.mpr ((ternary_gain_phase _).1.mpr
    ⟨by norm_num,by norm_num⟩)
  apply (mul_le_mul (rounding_multiplier hd hu) hp (Real.rpow_nonneg hx.le d) (by positivity)).trans_eq
  change 1/((1/K)^2*(1-ternaryPowerGain (1/2)))*Real.exp 1=Real.exp 1/(1-ternaryPowerGain (1/2))*K^2
  field_simp [hK.ne',hg.ne']

/-- Integer midpoint data recover the full real prime price with only
a squared logarithmic rounding term, uniformly in the measured exponent
and its constant. The coefficient on x^s is the exact Mellin inverse. -/
theorem prime_error_from_integer_midpoint_log_squared {s A : ℝ}
    (hs : s∈Set.Ioo (0:ℝ) 1) (hA : 0≤A)
    (h : ∀ n : ℕ, 0<n → primeMidpointPrice n≤A*(n:ℝ)^s) {x : ℝ} (hx : 0<x) :
    Chebyshev.theta x-x ≤ A/midpointPowerGap s*x^s+
      Real.exp 1/(1-ternaryPowerGain (1/2))*(2+max 0 (Real.log x))^2 := by
  obtain ⟨d,hd,hround⟩ := logarithmic_rounding_choice hx
  exact (prime_error_from_integer_midpoint hs hd hA h hx).trans (add_le_add le_rfl hround)

#print axioms prime_error_from_integer_midpoint_log_squared

/-- Finite exceptions to the measured power bound change only the
logarithmic remainder. They cannot alter the leading transfer constant. -/
theorem prime_error_from_eventual_integer_midpoint {s A : ℝ} (hs : s∈Set.Ioo (0:ℝ) 1)
    (hA : 0≤A) (h : ∀ᶠ n : ℕ in atTop, primeMidpointPrice n≤A*(n:ℝ)^s) :
    ∃ C : ℝ, ∀ x : ℝ, 0<x → Chebyshev.theta x-x ≤
      A/midpointPowerGap s*x^s+C*(2+max 0 (Real.log x))^2 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let M := ∑ n ∈ range N, |primeMidpointPrice n|
  have hM : 0≤M := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(M+1)*(Real.exp 1/(1-ternaryPowerGain (1/2))),?_⟩
  intro x hx
  obtain ⟨d,hd,hround⟩ := logarithmic_rounding_choice hx
  let R := 4*(3:ℝ)^d/d
  have hR : 1≤R := by
    have h₃ := Real.one_le_rpow (by norm_num : (1:ℝ)≤3) hd.1.le
    apply (le_div_iff₀ hd.1).mpr
    linarith only [h₃,hd.2]
  have hf (y : ℝ) (hy : 0<y) : primeMidpointPrice ⌊y⌋₊≤A*y^s+M*y^d := by
    let n := ⌊y⌋₊
    have hn : (n:ℝ)≤y := Nat.floor_le hy.le
    by_cases hlate : N≤n
    · apply (hN n hlate).trans
      exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hn hs.1.le) hA).trans
        (le_add_of_nonneg_right (mul_nonneg hM (Real.rpow_nonneg hy.le d)))
    · rcases Nat.eq_zero_or_pos n with hn' | hn'
      · change primeMidpointPrice n≤_
        rw [hn']
        simpa [primeMidpointPrice] using add_nonneg (mul_nonneg hA (Real.rpow_nonneg hy.le s))
          (mul_nonneg hM (Real.rpow_nonneg hy.le d))
      · have he : |primeMidpointPrice n|≤M := single_le_sum (fun j _ => abs_nonneg (primeMidpointPrice j))
          (mem_range.mpr (lt_of_not_ge hlate))
        have hv := Real.one_le_rpow ((Nat.one_le_cast.mpr hn').trans hn) hd.1.le
        exact ((le_abs_self _).trans he).trans ((le_mul_of_one_le_right hM hv).trans
          (le_add_of_nonneg_left (mul_nonneg hA (Real.rpow_nonneg hy.le s))))
  have hob (y : ℝ) (hy : 0<y) : realMidpointObservation Chebyshev.theta y ≤
      A*y^s+((M+1)*R)*y^d := by
    have hh := prime_midpoint_rounding_cost hd.1 hy
    change _≤primeMidpointPrice ⌊y⌋₊+R*y^d at hh
    have hm := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hM hR) (Real.rpow_nonneg hy.le d)
    linarith only [hh,hf y hy,hm]
  have he := prime_error_of_two_midpoint_powers hs hd A ((M+1)*R) hob hx
  have hb := mul_le_mul_of_nonneg_left hround (show 0≤M+1 by linarith only [hM])
  change _ ≤ (M+1)*(Real.exp 1/(1-ternaryPowerGain (1/2))*(2+max 0 (Real.log x))^2) at hb
  change (M+1)*(R/midpointPowerGap d*x^d) ≤ _ at hb
  simp only [div_eq_mul_inv] at he hb ⊢
  linarith only [he,hb]

/-- A surplus exceeding the transferred envelope by unbounded multiples
of the squared logarithm requires arbitrarily late midpoint violations.
No finite set of measurements can account for these excursions. -/
theorem arbitrarily_late_midpoints_from_prime_surplus {s A : ℝ}
    (hs : s∈Set.Ioo (0:ℝ) 1) (hA : 0≤A)
    (h : ∀ C : ℝ, ∃ x>0, A/midpointPowerGap s*x^s+C*(2+max 0 (Real.log x))^2 < Chebyshev.theta x-x) :
    ∃ᶠ n : ℕ in atTop, A*(n:ℝ)^s < primeMidpointPrice n := by
  by_contra! hn
  obtain ⟨C,hC⟩ := prime_error_from_eventual_integer_midpoint hs hA hn
  obtain ⟨x,hx,he⟩ := h C
  exact he.not_ge (hC x hx)

#print axioms prime_error_from_eventual_integer_midpoint
#print axioms arbitrarily_late_midpoints_from_prime_surplus

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
