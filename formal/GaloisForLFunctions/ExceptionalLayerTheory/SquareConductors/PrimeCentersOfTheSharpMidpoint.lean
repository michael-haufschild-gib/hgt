import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RoughCofactorsAtPrimorialMidpoints
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths

/-!
# Sampling the sharp prime midpoint at prime centers

An upper prime within the two-thirds power moves only the two outer
endpoints adversely. Their total crossed prime mass is bounded by the
number of crossed integers times their largest logarithm.
-/

noncomputable section
open Filter Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem sharp_upper_prime_shift {n p : ℕ} (hle : n ≤ p) (hp : 0 < p) :
    primeMidpointPrice n-primeMidpointPrice p ≤ 6*((p:ℝ)-n)*Real.log (4*(p:ℝ)) := by
  have h2 := theta_integer_interval_bound (Nat.mul_le_mul_left 2 hle)
  have h4 := theta_integer_interval_bound (Nat.mul_le_mul_left 4 hle)
  have h3 := Chebyshev.theta_mono ((Nat.cast_le (α:=ℝ)).mpr (Nat.mul_le_mul_left 3 hle))
  have hp' := (Nat.cast_pos (α:=ℝ)).mpr hp
  have hl := Real.log_le_log (by positivity : 0 < 2*(p:ℝ))
    (by linarith only [hp'] : 2*(p:ℝ) ≤ 4*p)
  rw [prime_midpoint_price_eq,prime_midpoint_price_eq]
  push_cast at h2 h3 h4 ⊢
  have hd : 0 ≤ 2*(p:ℝ)-2*n := by have h := (Nat.cast_le (α:=ℝ)).mpr hle; linarith
  linarith only [h2,h3,h4,mul_le_mul_of_nonneg_left hl hd]

/-- Every sufficiently large integer has a nearby prime center, with the
original three sharp endpoints and an explicit one-sided transfer cost. -/
theorem nearby_upper_prime_midpoint :
    ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ (p:ℝ) ≤ 2*n ∧
      primeMidpointPrice n ≤ primeMidpointPrice p+
        6*(Real.log 8+6)*(n:ℝ)^(5/6:ℝ) := by
  have hh := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (_root_.RHTower.eventually_exists_prime_short_interval_seven_twelfths
      (α:=(2/3:ℝ)) (by norm_num) (by norm_num))
  filter_upwards [hh,eventually_ge_atTop 1] with n hn hn1
  obtain ⟨p,hp,hnp,hgap⟩ := hn
  have hn' := (Nat.one_le_cast (α:=ℝ)).mpr hn1
  have hn0 := zero_lt_one.trans_le hn'
  have hnp' : n < p := by exact_mod_cast hnp
  have hc := (Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (2/3:ℝ) ≤ 1)).trans_eq
    (Real.rpow_one _)
  have h2p : (p:ℝ) ≤ 2*n := by linarith only [hgap,hc]
  have hpos := (Nat.cast_pos (α:=ℝ)).mpr hp.pos
  have hlog := Real.log_le_log (by positivity : 0 < 4*(p:ℝ))
    (by linarith only [h2p] : 4*(p:ℝ) ≤ 8*n)
  rw [Real.log_mul (by norm_num) hn0.ne'] at hlog
  let u := (n:ℝ)^(1/6:ℝ)
  have hu : 1 ≤ u := Real.one_le_rpow hn' (by norm_num)
  have hlogu := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hu)
  have he : Real.log u=(1/6:ℝ)*Real.log n := Real.log_rpow hn0 _
  have hlog' : Real.log (4*(p:ℝ)) ≤ (Real.log 8+6)*u := by
    have h8 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 8)
    linarith only [hlog,hlogu,he,le_mul_of_one_le_right h8 hu]
  have hscale : (n:ℝ)^(2/3:ℝ)*u=(n:ℝ)^(5/6:ℝ) := by
    dsimp only [u]
    rw [←Real.rpow_add hn0]; norm_num
  have hl0 : 0 ≤ Real.log (4*(p:ℝ)) := Real.log_nonneg (by
    have hh := (Nat.one_le_cast (α:=ℝ)).mpr hp.one_le
    linarith only [hh])
  have hprod := mul_le_mul (sub_le_iff_le_add.mpr (by linarith only [hgap] :
      (p:ℝ) ≤ (n:ℝ)^(2/3:ℝ)+n)) hlog' hl0 (Real.rpow_nonneg hn0.le _)
  rw [show (n:ℝ)^(2/3:ℝ)*((Real.log 8+6)*u)=
    (Real.log 8+6)*((n:ℝ)^(2/3:ℝ)*u) by ring,hscale] at hprod
  exact ⟨p,hp,hnp',h2p,by linarith only [sharp_upper_prime_shift hnp'.le hp.pos,hprod]⟩

/-- The eleven-thirds prefix bound is equivalent to upper estimates of the
sharp midpoint tested only at prime centers. -/
theorem prime_centers_iff_eleven_thirds :
    (∀ t : ℝ,5/6<t → t<1 → ∃ C : ℝ,∀ p : ℕ,p.Prime → primeMidpointPrice p ≤ C*(p:ℝ)^t) ↔
      ∃ C : ℝ,0 ≤ C ∧ ∀ N : ℕ, |seventeenNinthsConductorPrefix N| ≤ C*(N:ℝ)^(11/3:ℝ) := by
  rw [←prime_midpoint_iff_eleven_thirds]
  constructor
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    obtain ⟨N,hN⟩ := eventually_atTop.mp nearby_upper_prime_midpoint
    let A := ∑ j ∈ range N,|primeMidpointPrice j|
    let B := 6*(Real.log 8+6)
    have hA : 0 ≤ A := sum_nonneg fun _ _ => abs_nonneg _
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    refine ⟨A + 2 * |C| + B,?_⟩
    intro n hn
    have hn' := (Nat.one_le_cast (α:=ℝ)).mpr hn
    have ht0 : 0 ≤ t := by linarith only [ht]
    have hnt := Real.one_le_rpow hn' ht0
    by_cases hsmall : n<N
    · have hi : |primeMidpointPrice n| ≤ A := single_le_sum
        (fun j (_ : j ∈ range N) => abs_nonneg (primeMidpointPrice j)) (mem_range.mpr hsmall)
      calc primeMidpointPrice n ≤ A := (le_abs_self _).trans hi
           _ ≤ A + 2 * |C| + B := by linarith only [abs_nonneg C,hB]
           _ ≤ _ := le_mul_of_one_le_right (by positivity) hnt
    · obtain ⟨p,hp,_,hp2,hupper⟩ := hN n (le_of_not_gt hsmall)
      have hp' := Real.rpow_le_rpow (Nat.cast_nonneg p) hp2 ht0
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg n)] at hp'
      have h2t := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ht1.le).trans_eq
        (Real.rpow_one _)
      have hCp := (hC p hp).trans (mul_le_mul (le_abs_self C)
        (hp'.trans (mul_le_mul_of_nonneg_right h2t (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
        (Real.rpow_nonneg (Nat.cast_nonneg p) _) (abs_nonneg C))
      have hBn := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn' ht.le) hB
      change primeMidpointPrice n ≤ primeMidpointPrice p+B*(n:ℝ)^(5/6:ℝ) at hupper
      linarith only [hupper,hCp,hBn,mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg n) t)]
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    exact ⟨C,fun p hp => hC p hp.one_le⟩

#print axioms nearby_upper_prime_midpoint
#print axioms prime_centers_iff_eleven_thirds

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
