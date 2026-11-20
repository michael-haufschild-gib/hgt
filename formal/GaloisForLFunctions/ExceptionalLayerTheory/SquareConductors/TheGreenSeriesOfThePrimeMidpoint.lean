import GaloisForLFunctions.ArithmeticPositiveDuality.TheLiouvilleLawForTwoCommutingTranslations
import GaloisForLFunctions.RHTower.PrimeHigherMertens
import Mathlib.Analysis.PSeries

/-!
# Recovering the prime error from all real midpoint observations

Dividing the Chebyshev error by scale changes the two midpoint weights
to 1/3 and 2/3 on logarithmic scale. The resulting walk moves to the
right. Its exponentially small left tail and the prime number theorem
make the Green expansion absolutely convergent even with polynomial
weights in the number of steps.
-/

noncomputable section
open Finset Filter
open scoped Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.TranslationLaw
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The midpoint walk on prices already divided by their observation scale. -/
def midpointLogWalk := walk (1/3) (Real.log (2/3:ℝ)) (Real.log (4/3:ℝ))

theorem midpointLogWalk_succ (n : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    midpointLogWalk (n+1) f t = midpointLogWalk n f (t+Real.log (2/3:ℝ))/3+
      2*midpointLogWalk n f (t+Real.log (4/3:ℝ))/3 := by
  change (1/3:ℝ)*midpointLogWalk n f _+(1-1/3)*midpointLogWalk n f _ = _
  ring

private theorem zero_step (f : ℝ → ℝ) (t : ℝ) : midpointLogWalk 0 f t=f t := rfl

theorem midpointLogWalk_one (f : ℝ → ℝ) (t : ℝ) : midpointLogWalk 1 f t=
    f (t+Real.log (2/3:ℝ))/3+2*f (t+Real.log (4/3:ℝ))/3 := by
  simpa only [zero_step] using midpointLogWalk_succ 0 f t

def normalizedPrimeError (t : ℝ) := (Chebyshev.theta (Real.exp t)-Real.exp t)/Real.exp t

/-- At scale x=e^t this is (2θ(x)−θ(2x/3)−θ(4x/3))/(2x). -/
def normalizedPrimeMidpoint (t : ℝ) :=
  (2*Chebyshev.theta (Real.exp t)-Chebyshev.theta (Real.exp t*(2/3))-
    Chebyshev.theta (Real.exp t*(4/3)))/(2*Real.exp t)

theorem prime_midpoint_is_log_walk_defect (t : ℝ) :
    normalizedPrimeMidpoint t=normalizedPrimeError t-midpointLogWalk 1 normalizedPrimeError t := by
  rw [midpointLogWalk_one]
  simp only [normalizedPrimeMidpoint,normalizedPrimeError,Real.exp_add,
    Real.exp_log (by norm_num : 0<(2/3:ℝ)),Real.exp_log (by norm_num : 0<(4/3:ℝ))]
  field_simp [(Real.exp_pos t).ne']; ring

/-- One unaveraged price minus its one-step continuation. -/
def logWalkDefect (f : ℝ → ℝ) (t : ℝ) := f t-midpointLogWalk 1 f t

private theorem transported_defect (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    midpointLogWalk n (logWalkDefect f) t =
      midpointLogWalk n f t-midpointLogWalk (n+1) f t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [midpointLogWalk_succ,ih]
    ring

/-- Each finite reconstruction misses precisely the error carried by its
terminal binomial distribution. -/
theorem finite_midpoint_green (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    (∑ j ∈ range n, midpointLogWalk j (logWalkDefect f) t)+midpointLogWalk n f t=f t := by
  induction n with
  | zero => simp [zero_step]
  | succ n ih => rw [Finset.sum_range_succ,transported_defect]; linarith only [ih]

theorem finite_prime_midpoint_green (n : ℕ) (t : ℝ) :
    (∑ j ∈ range n, midpointLogWalk j normalizedPrimeMidpoint t)+
      midpointLogWalk n normalizedPrimeError t=normalizedPrimeError t := by
  rw [show normalizedPrimeMidpoint=logWalkDefect normalizedPrimeError from funext prime_midpoint_is_log_walk_defect]
  exact finite_midpoint_green _ n t

private theorem walk_abs_le (n : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    |midpointLogWalk n f t| ≤ midpointLogWalk n (fun u => |f u|) t := by
  induction n generalizing t with
  | zero => exact le_rfl
  | succ n ih =>
    rw [midpointLogWalk_succ,midpointLogWalk_succ]
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_div,abs_mul,abs_of_pos (by norm_num : 0<(3:ℝ)),abs_of_pos (by norm_num : 0<(2:ℝ))]
    linarith only [ih (t+Real.log (2/3:ℝ)),ih (t+Real.log (4/3:ℝ))]

theorem midpointLogWalk_le_add {f g h : ℝ → ℝ} (hfg : ∀ t, f t ≤ g t+h t) (n : ℕ) (t : ℝ) :
    midpointLogWalk n f t ≤ midpointLogWalk n g t+midpointLogWalk n h t := by
  induction n generalizing t with
  | zero => exact hfg t
  | succ n ih =>
    simp only [midpointLogWalk_succ]
    linarith only [ih (t+Real.log (2/3:ℝ)),ih (t+Real.log (4/3:ℝ))]

private theorem midpoint_mass_le (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    midpointLogWalk n (fun u => |logWalkDefect f u|) t ≤
      midpointLogWalk n (fun u => |f u|) t+midpointLogWalk (n+1) (fun u => |f u|) t := by
  induction n generalizing t with
  | zero =>
    rw [zero_step,zero_step,logWalkDefect]
    exact (abs_sub _ _).trans (add_le_add le_rfl (walk_abs_le 1 f t))
  | succ n ih =>
    simp only [midpointLogWalk_succ] at *
    linarith only [ih (t+Real.log (2/3:ℝ)),ih (t+Real.log (4/3:ℝ))]

private def halfMoment := Real.exp (-Real.log (2/3:ℝ)/2)/3+2*Real.exp (-Real.log (4/3:ℝ)/2)/3

private theorem halfMoment_mem : halfMoment ∈ Set.Ioo (0:ℝ) 1 := by
  let a := Real.exp (-Real.log (2/3:ℝ)/2)
  let b := Real.exp (-Real.log (4/3:ℝ)/2)
  have sqval {x : ℝ} (hx : 0<x) : Real.exp (-Real.log x/2)^2=x⁻¹ := by
    rw [←Real.exp_nat_mul,Nat.cast_ofNat,show (2:ℝ)*(-Real.log x/2) = -Real.log x by ring,Real.exp_neg,Real.exp_log hx]
  have ha : a^2=3/2 := (sqval (by norm_num : 0<(2/3:ℝ))).trans (by norm_num)
  have hb : b^2=3/4 := (sqval (by norm_num : 0<(4/3:ℝ))).trans (by norm_num)
  have hne : a≠1 := fun h => (by norm_num : (1:ℝ)^2≠3/2) (h ▸ ha)
  change 0<a/3+2*b/3 ∧ a/3+2*b/3<1
  exact ⟨by dsimp only [a,b]; positivity,by nlinarith only [ha,hb,sq_pos_of_ne_zero (sub_ne_zero.mpr hne),sq_nonneg (b-1)]⟩

private theorem walk_envelope {f : ℝ → ℝ} {A B : ℝ}
    (h : ∀ t, f t ≤ A*Real.exp (-t/2)+B) (n : ℕ) (t : ℝ) :
    midpointLogWalk n f t ≤ A*halfMoment^n*Real.exp (-t/2)+B := by
  induction n generalizing t with
  | zero => simpa only [zero_step,pow_zero,mul_one] using h t
  | succ n ih =>
    have shift (s : ℝ) : Real.exp (-(t+s)/2)=Real.exp (-t/2)*Real.exp (-s/2) := by
      rw [←Real.exp_add]; congr 1; ring
    have h₁ := ih (t+Real.log (2/3:ℝ))
    have h₂ := ih (t+Real.log (4/3:ℝ))
    rw [shift] at h₁ h₂
    rw [midpointLogWalk_succ,pow_succ]
    unfold halfMoment at h₁ h₂ ⊢
    linarith only [h₁,h₂]

private theorem normalized_prime_bound (t : ℝ) : |normalizedPrimeError t| ≤ Real.log 4+1 := by
  have ht := Real.exp_pos t
  rw [normalizedPrimeError,abs_div,abs_of_pos ht,div_le_iff₀ ht]
  have h := abs_sub (Chebyshev.theta (Real.exp t)) (Real.exp t)
  rw [abs_of_nonneg (Chebyshev.theta_nonneg _),abs_of_pos ht] at h
  linarith only [h,Chebyshev.theta_le_log4_mul_x ht.le]

private theorem eventual_log_price (j : ℕ) :
    ∀ᶠ y : ℝ in atTop, y^j*|normalizedPrimeError y| ≤ 1 := by
  have h := ((_root_.RHTower.tendsto_logPowDivId_mul_thetaSub j).comp Real.tendsto_exp_atTop).abs
  have h' := h.eventually (gt_mem_nhds (show |(0:ℝ)|<1 by norm_num))
  filter_upwards [h',eventually_ge_atTop (0:ℝ)] with y hy hy₀
  change |(_root_.RHTower.logPowDivId j (Real.exp y))*(Chebyshev.theta (Real.exp y)-Real.exp y)|<1 at hy
  simp only [_root_.RHTower.logPowDivId,Real.log_exp,abs_mul,abs_div,abs_pow,abs_of_nonneg hy₀,
    abs_of_pos (Real.exp_pos y)] at hy
  rw [normalizedPrimeError,abs_div,abs_of_pos (Real.exp_pos y)]
  calc _ = y^j/Real.exp y*|Chebyshev.theta (Real.exp y)-Real.exp y| := by ring
       _ ≤ 1 := hy.le

private theorem positive_log_cut :
    ∃ k r : ℝ, 0<k ∧ r ∈ Set.Ioo (0:ℝ) 1 ∧ Real.exp (k/2)*halfMoment=r := by
  let r := (1+halfMoment)/2
  have hq := halfMoment_mem
  have hr : halfMoment<r := by dsimp only [r]; linarith only [hq.2]
  have hdiv : 1<r/halfMoment := (one_lt_div hq.1).mpr hr
  refine ⟨2*Real.log (r/halfMoment),r,mul_pos (by norm_num) (Real.log_pos hdiv),
    ⟨hq.1.trans hr,by dsimp only [r]; linarith only [hq.2]⟩,?_⟩
  rw [show 2*Real.log (r/halfMoment)/2=Real.log (r/halfMoment) by ring,Real.exp_log (zero_lt_one.trans hdiv),
    div_mul_cancel₀ _ hq.1.ne']

/-- All positive powers of the step count are allowed in the envelope.
Below the dividing line kn, the exponential moment is geometric. Above
it the prime number theorem pays any chosen inverse power of kn. -/
theorem prime_midpoint_terminal_envelope :
    ∃ k r : ℝ, 0<k ∧ r ∈ Set.Ioo (0:ℝ) 1 ∧ ∀ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      midpointLogWalk n (fun u => |normalizedPrimeError u|) t ≤
        (Real.log 4+1)*r^n*Real.exp (-t/2)+1/(k*n)^j := by
  obtain ⟨k,r,hk,hr,hkr⟩ := positive_log_cut
  refine ⟨k,r,hk,hr,fun j => ?_⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventual_log_price j)
  have hinf : Tendsto (fun n : ℕ => k*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hk
  filter_upwards [hinf.eventually_ge_atTop T,eventually_gt_atTop (0:ℕ)] with n hn hn₀
  intro t
  let M := Real.log 4+1
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hkn : 0<k*(n:ℝ) := mul_pos hk (Nat.cast_pos.mpr hn₀)
  have major (u : ℝ) : |normalizedPrimeError u| ≤
      (M*Real.exp (k/2)^n)*Real.exp (-u/2)+1/(k*n)^j := by
    by_cases hu : u ≤ k*n
    · have hfac : 1 ≤ Real.exp (k/2)^n*Real.exp (-u/2) := by
        rw [←Real.exp_nat_mul,←Real.exp_add,Real.one_le_exp_iff]
        linarith only [hu]
      have hpaid := mul_le_mul_of_nonneg_left hfac hM
      calc |normalizedPrimeError u| ≤ M := normalized_prime_bound u
        _ ≤ M*Real.exp (k/2)^n*Real.exp (-u/2) := by linarith only [hpaid]
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have hl := le_of_not_ge hu
      have hlarge := hT u (hn.trans hl)
      have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hkn.le hl j) (abs_nonneg (normalizedPrimeError u))
      have hsmall : |normalizedPrimeError u| ≤ 1/(k*n)^j :=
        (le_div_iff₀ (pow_pos hkn _)).mpr (by linarith only [hp,hlarge])
      exact hsmall.trans (le_add_of_nonneg_left (by positivity))
  have h := walk_envelope major n t
  rw [mul_assoc M,←mul_pow,hkr] at h
  exact h

lemma midpointLogWalk_abs_nonneg (n : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    0 ≤ midpointLogWalk n (fun u => |f u|) t := (abs_nonneg _).trans (walk_abs_le n f t)

/-- Any polynomially weighted sum of terminal absolute prime errors is
finite. Absolute values here precede the average over the 2^n paths. -/
theorem all_prime_midpoint_terminal_moments (p : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => (n:ℝ)^p*midpointLogWalk n (fun u => |normalizedPrimeError u|) t) := by
  obtain ⟨k,r,hk,hr,h⟩ := prime_midpoint_terminal_envelope
  let A := (Real.log 4+1)*Real.exp (-t/2)
  have hgeom := (summable_pow_mul_geometric_of_norm_lt_one p
    (show ‖r‖<1 by simpa only [Real.norm_eq_abs,abs_of_pos hr.1] using hr.2)).mul_left A
  have hpseries := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (1/k^(p+2))
  apply (hgeom.add hpseries).of_norm_bounded_eventually_nat
  filter_upwards [h (p+2),eventually_gt_atTop (0:ℕ)] with n hn hn₀
  have hnr : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn₀.ne'
  have hpaid : (n:ℝ)^p*(1/(k*n)^(p+2))=(1/k^(p+2))*(1/(n:ℝ)^2) := by
    rw [mul_pow,pow_add (n:ℝ) p 2]
    field_simp [hk.ne',hnr]
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (midpointLogWalk_abs_nonneg _ _ _))]
  have he := mul_le_mul_of_nonneg_left (hn t) (show 0 ≤ (n:ℝ)^p by positivity)
  rw [mul_add,hpaid] at he
  dsimp only [A,Pi.add_apply]
  linarith only [he]

/-- The midpoint observations are absolutely summable even before the
paths at the same depth are combined, with any polynomial weight in depth. -/
theorem all_prime_midpoint_green_moments (p : ℕ) (t : ℝ) :
    Summable (fun n : ℕ => (n:ℝ)^p*midpointLogWalk n (fun u => |normalizedPrimeMidpoint u|) t) := by
  let E := fun n : ℕ => midpointLogWalk n (fun u => |normalizedPrimeError u|) t
  have h := all_prime_midpoint_terminal_moments p t
  have hs := (summable_nat_add_iff 1).mpr h
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (midpointLogWalk_abs_nonneg _ _ _)) _ (h.add hs)
  intro n
  have hm := midpoint_mass_le normalizedPrimeError n t
  rw [←show normalizedPrimeMidpoint=logWalkDefect normalizedPrimeError from funext prime_midpoint_is_log_walk_defect] at hm
  have hn := mul_le_mul_of_nonneg_left hm (show 0 ≤ (n:ℝ)^p by positivity)
  have hpow : (n:ℝ)^p ≤ ((n+1:ℕ):ℝ)^p := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ n) _
  have hshift := mul_le_mul_of_nonneg_right hpow (midpointLogWalk_abs_nonneg (n+1) normalizedPrimeError t)
  change _ ≤ (n:ℝ)^p*E n+((n+1:ℕ):ℝ)^p*E (n+1)
  dsimp only [E]
  linarith only [hn,hshift]

/-- Absolute summability of the transported terminal prices implies
absolute summability and exact inversion of their one-step defects. -/
theorem midpoint_green_of_terminal (f : ℝ → ℝ) (t : ℝ)
    (he : Summable (fun n => midpointLogWalk n (fun u => |f u|) t)) :
    HasSum (fun n => midpointLogWalk n (logWalkDefect f) t) (f t) := by
  have hm := he.add ((summable_nat_add_iff 1).mpr he)
  have hs : Summable (fun n => midpointLogWalk n (logWalkDefect f) t) :=
    hm.of_norm_bounded fun n => by
      rw [Real.norm_eq_abs]
      exact (walk_abs_le n (logWalkDefect f) t).trans (midpoint_mass_le f n t)
  have hzero : Tendsto (fun n => midpointLogWalk n f t) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using walk_abs_le n f t) he.tendsto_atTop_zero
  apply hs.hasSum_iff_tendsto_nat.mpr
  have hsum (n : ℕ) : ∑ j ∈ range n, midpointLogWalk j (logWalkDefect f) t=f t-midpointLogWalk n f t := by
    linarith only [finite_midpoint_green f n t]
  simp_rw [hsum]
  simpa only [sub_zero] using (tendsto_const_nhds (x:=f t)).sub hzero

/-- Terminal prices bounded by exp(−t/2) have a geometric error envelope,
including prices with jumps at every positive integer scale. -/
theorem half_power_terminal_moments (f : ℝ → ℝ) {A : ℝ} (h : ∀ t, |f t| ≤ A*Real.exp (-t/2))
    (p : ℕ) (t : ℝ) : Summable (fun n : ℕ => (n:ℝ)^p*midpointLogWalk n (fun u => |f u|) t) := by
  have hq := halfMoment_mem
  have hg := (summable_pow_mul_geometric_of_norm_lt_one p
    (show ‖halfMoment‖ < 1 by simpa only [Real.norm_eq_abs,abs_of_pos hq.1] using hq.2)).mul_left (A*Real.exp (-t/2))
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (midpointLogWalk_abs_nonneg _ _ _)) _ hg
  intro n
  have hb := walk_envelope (B:=0) (fun y => (h y).trans_eq (add_zero _).symm) n t
  rw [add_zero] at hb
  have hv := mul_le_mul_of_nonneg_left hb (show 0 ≤ (n:ℝ)^p by positivity)
  linarith only [hv]

/-- The full ordinary-prime error is reconstructed from the real
midpoint observations, without any zero-free strip assumption. -/
theorem prime_midpoint_green_series (t : ℝ) :
    HasSum (fun n => midpointLogWalk n normalizedPrimeMidpoint t) (normalizedPrimeError t) := by
  rw [show normalizedPrimeMidpoint=logWalkDefect normalizedPrimeError from funext prime_midpoint_is_log_walk_defect]
  apply midpoint_green_of_terminal
  simpa only [pow_zero,one_mul] using all_prime_midpoint_terminal_moments 0 t

#print axioms prime_midpoint_terminal_envelope
#print axioms all_prime_midpoint_green_moments
#print axioms prime_midpoint_green_series

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
