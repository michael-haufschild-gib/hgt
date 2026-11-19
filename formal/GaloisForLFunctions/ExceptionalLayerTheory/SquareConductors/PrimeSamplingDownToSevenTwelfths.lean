import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RoughCofactorsAtPrimorialMidpoints
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths

/-!
# Prime centers of the sharp midpoint down to seven twelfths

A displacement of the center costs at most six times its length times
the largest crossed prime logarithm. Huxley's ordinary-prime interval
and the subpower bound for a logarithm (Fino–Majdoub, arXiv:2611.24340,
Lemma 2.1) allow every transfer exponent strictly above seven twelfths.
-/

noncomputable section
open Filter Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The two signs each involve at most six crossed integer intervals per
unit displacement, regardless of the length of the original midpoint. -/
theorem abs_midpoint_price_shift {n p : ℕ} (hnp : n ≤ p) (hp : 0 < p) :
    |primeMidpointPrice n-primeMidpointPrice p| ≤ 6*((p:ℝ)-n)*Real.log (4*(p:ℝ)) := by
  have step (k : ℕ) := theta_integer_interval_bound (Nat.mul_le_mul_left k hnp)
  have incr (k : ℕ) := Chebyshev.theta_mono
    ((Nat.cast_le (α:=ℝ)).mpr (Nat.mul_le_mul_left k hnp))
  have h2 := step 2
  have h3 := step 3
  have h4 := step 4
  have l2 := incr 2
  have l3 := incr 3
  have l4 := incr 4
  have hp' := (Nat.cast_pos (α:=ℝ)).mpr hp
  have hd : (0:ℝ) ≤ p-n := sub_nonneg.mpr (Nat.cast_le.mpr hnp)
  have log2 := Real.log_le_log (by positivity : 0 < 2*(p:ℝ))
    (by linarith only [hp'] : 2*(p:ℝ) ≤ 4*p)
  have log3 := Real.log_le_log (by positivity : 0 < 3*(p:ℝ))
    (by linarith only [hp'] : 3*(p:ℝ) ≤ 4*p)
  rw [prime_midpoint_price_eq,prime_midpoint_price_eq,abs_le]
  push_cast at h2 h3 h4 l2 l3 l4 ⊢
  constructor
  · linarith only [h3,l2,l4,mul_le_mul_of_nonneg_left log3 hd]
  · linarith only [h2,h4,l3,mul_le_mul_of_nonneg_left log2 hd]

/-- A power-length displacement costs any strictly larger power,
uniformly in the two integer endpoints. -/
theorem midpoint_shift_on_power_window {α t : ℝ} (hαt : α < t) (ht1 : t < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {n p : ℕ}, 1 ≤ n → n < p → (p:ℝ) ≤ n+(n:ℝ)^α →
      (p:ℝ) ≤ 2*n ∧ |primeMidpointPrice n-primeMidpointPrice p| ≤ B*(n:ℝ)^t := by
  let d := t-α
  have hd : 0 < d := sub_pos.mpr hαt
  have h8 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 8)
  refine ⟨6*(Real.log 8+1/d),by positivity,fun {n p} hn1 hnp' hgap => ?_⟩
  have hp : 0 < p := by omega
  have hn' := (Nat.one_le_cast (α:=ℝ)).mpr hn1
  have hn0 := zero_lt_one.trans_le hn'
  have hα1 := (Real.rpow_le_rpow_of_exponent_le hn' (hαt.trans ht1).le).trans_eq (Real.rpow_one _)
  have h2p : (p:ℝ) ≤ 2*n := by linarith only [hgap,hα1]
  have hpos := (Nat.cast_pos (α:=ℝ)).mpr hp
  have hlog := Real.log_le_log (by positivity : 0 < 4*(p:ℝ))
    (by linarith only [h2p] : 4*(p:ℝ) ≤ 8*n)
  rw [Real.log_mul (by norm_num) hn0.ne'] at hlog
  let u := (n:ℝ)^d
  have hu : 1 ≤ u := Real.one_le_rpow hn' hd.le
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hu)
  have he : Real.log u = d*Real.log n := Real.log_rpow hn0 _
  have hx : Real.log n ≤ (1/d)*u := by
    rw [one_div_mul_eq_div,le_div_iff₀ hd]
    linarith only [hl,he]
  have hlog' : Real.log (4*(p:ℝ)) ≤ (Real.log 8+1/d)*u := by
    linarith only [hlog,hx,le_mul_of_one_le_right h8 hu]
  have hscale : (n:ℝ)^α*u=(n:ℝ)^t := by
    rw [show u=(n:ℝ)^d from rfl,←Real.rpow_add hn0,show α+d=t by dsimp only [d]; ring]
  have hl0 : 0 ≤ Real.log (4*(p:ℝ)) := Real.log_nonneg (by
    have h := (Nat.one_le_cast (α:=ℝ)).mpr hp
    linarith only [h])
  have hdist : (p:ℝ)-n ≤ (n:ℝ)^α := by linarith only [hgap]
  have hprod := mul_le_mul hdist hlog' hl0 (Real.rpow_nonneg hn0.le _)
  rw [show (n:ℝ)^α*((Real.log 8+1/d)*u)=(Real.log 8+1/d)*((n:ℝ)^α*u) by ring,
    hscale] at hprod
  exact ⟨h2p,by linarith only [abs_midpoint_price_shift hnp'.le hp,hprod]⟩

/-- At every sufficiently large integer the midpoint and its reading at a
nearby upper prime agree to any power strictly above seven twelfths. -/
theorem nearby_prime_midpoint_at_every_transfer_exponent {t : ℝ} (ht : 7/12 < t) (ht1 : t < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ (p:ℝ) ≤ 2*n ∧
      |primeMidpointPrice n-primeMidpointPrice p| ≤ B*(n:ℝ)^t := by
  obtain ⟨α,hα,hαt⟩ := exists_between ht
  obtain ⟨B,hB,hshift⟩ := midpoint_shift_on_power_window hαt ht1
  refine ⟨B,hB,?_⟩
  have hh := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (_root_.RHTower.eventually_exists_prime_short_interval_seven_twelfths hα (hαt.trans ht1))
  filter_upwards [hh,eventually_ge_atTop 1] with n hn hn1
  obtain ⟨p,hp,hnp,hgap⟩ := hn
  have hnp' : n < p := by exact_mod_cast hnp
  exact ⟨p,hp,hnp',hshift hn1 hnp' hgap⟩

/-- Above the prime-gap threshold a bound on ordinary prime centers alone
detects the full rightmost zero abscissa, including at the threshold. -/
theorem prime_center_upper_spectrum {b : ℝ} (hb : 7/12 ≤ b) :
    (∀ t : ℝ, b<t → t<1 → ∃ C : ℝ, ∀ p : ℕ, p.Prime → primeMidpointPrice p ≤ C*(p:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [← prime_midpoint_upper_spectrum_iff (by linarith only [hb] : 1/2 ≤ b)]
  constructor
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    obtain ⟨B,hB,hh⟩ := nearby_prime_midpoint_at_every_transfer_exponent (hb.trans_lt ht) ht1
    obtain ⟨N,hN⟩ := eventually_atTop.mp hh
    let A := ∑ j ∈ range N, |primeMidpointPrice j|
    have hA : 0 ≤ A := sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨A+2*|C|+B,fun n hn => ?_⟩
    have hn' := (Nat.one_le_cast (α:=ℝ)).mpr hn
    have ht0 : 0 ≤ t := by linarith only [ht,hb]
    have hnt := Real.one_le_rpow hn' ht0
    by_cases hsmall : n < N
    · have hi : |primeMidpointPrice n| ≤ A := single_le_sum
        (fun j (_ : j ∈ range N) => abs_nonneg (primeMidpointPrice j)) (mem_range.mpr hsmall)
      exact ((le_abs_self _).trans hi).trans ((by linarith only [abs_nonneg C,hB] :
        A ≤ A+2*|C|+B).trans (le_mul_of_one_le_right (by positivity) hnt))
    · obtain ⟨p,hp,_,hp2,herr⟩ := hN n (le_of_not_gt hsmall)
      have hp' := Real.rpow_le_rpow (Nat.cast_nonneg p) hp2 ht0
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg n)] at hp'
      have h2t := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ht1.le).trans_eq
        (Real.rpow_one _)
      have hCp := (hC p hp).trans (mul_le_mul (le_abs_self C)
        (hp'.trans (mul_le_mul_of_nonneg_right h2t (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
        (Real.rpow_nonneg (Nat.cast_nonneg p) _) (abs_nonneg C))
      linarith only [(abs_le.mp herr).2,hCp,mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg n) t)]
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    exact ⟨C,fun p hp => hC p hp.one_le⟩

#print axioms abs_midpoint_price_shift
#print axioms nearby_prime_midpoint_at_every_transfer_exponent
#print axioms prime_center_upper_spectrum

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
