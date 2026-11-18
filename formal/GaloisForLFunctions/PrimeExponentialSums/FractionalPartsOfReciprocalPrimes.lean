import GaloisForLFunctions.PrimeExponentialSums.ReciprocalPhasesNearTheSquareRoot
import GaloisForLFunctions.RHTower.PoissonSummationPiecewise
import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import GaloisForLFunctions.RHTower.MontgomerySpacedDetectionCore

/-!
# Fractional parts of reciprocal primes

Differences of the periodic second Bernoulli polynomial bracket the centered
fractional part even at a jump. Its absolutely convergent Fourier series transfers
reciprocal prime cancellation to sharp blocks at the original frequency.
-/

noncomputable section

open Filter Finset Topology RHTower ArithmeticFunction
open GaloisForLFunctions.RHTower (hasSum_cos_div_sq sawPrimitive)
open RHTower.Sieve (eventually_const_mul_one_add_log_pow_le_rpow)

namespace GaloisForLFunctions.PrimeExponentialSums

private def quadratic (t : ℝ) : ℝ := (t^2-t)/2

private def bernoulli (t : ℝ) : ℝ := quadratic (Int.fract t) + 1/12

private theorem quadratic_majorant (y : ℝ) : quadratic (Int.fract y) ≤ quadratic y := by
  have hn := Int.fract_nonneg y
  have hl := Int.fract_lt_one y
  have hp := mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.mpr hl.le)
  by_cases hh : 0 ≤ y ∧ y < 1
  · rw [Int.fract_eq_self.mpr hh]
  · dsimp [quadratic]
    rcases lt_or_ge y 0 with h | h
    · nlinarith only [hp,sq_nonneg y,h]
    · have hy : 1 ≤ y := le_of_not_gt (fun hh' => hh ⟨h,hh'⟩)
      nlinarith only [hp,mul_nonneg h (sub_nonneg.mpr hy)]

private theorem bernoulli_difference (t h : ℝ) :
    bernoulli (t+h)-bernoulli t ≤ h*(Int.fract t-1/2)+h^2/2 := by
  have he : Int.fract (t+h) = Int.fract (Int.fract t+h) := by
    rw [show t+h = (Int.fract t+h)+(⌊t⌋ : ℝ) by linarith only [Int.fract_add_floor t],
      Int.fract_add_intCast]
  unfold bernoulli
  rw [he]
  linarith only [quadratic_majorant (Int.fract t+h),
    show quadratic (Int.fract t+h) = quadratic (Int.fract t)+h*(Int.fract t-1/2)+h^2/2 by
      unfold quadratic; ring]

private theorem abs_series_le {f : ℕ → ℝ} {z C T : ℝ} {H : ℕ}
    (hz : HasSum (fun k => f k/(k : ℝ)^2) z) (hH : 1 ≤ H) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (low : ∀ k, 1 ≤ k → k ≤ H → |f k| ≤ C) (high : ∀ k, H < k → |f k| ≤ T) :
    |z| ≤ 2*C+T/(H : ℝ) := by
  let g (k : ℕ) := f k/(k : ℝ)^2
  have box (s : Finset ℕ) (c : ℝ) (hc : ∀ k ∈ s, |f k| ≤ c) :
      |∑ k ∈ s, g k| ≤ c*∑ k ∈ s, 1/(k : ℝ)^2 := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    dsimp [g]
    rw [abs_div,abs_of_nonneg (sq_nonneg (k : ℝ)),mul_one_div]
    exact div_le_div_of_nonneg_right (hc k hk) (sq_nonneg _)
  have hhead : |∑ k ∈ range (H+1), g k| ≤ 2*C := by
    rw [← sum_range_add_sum_Ico g (show 1 ≤ H+1 by omega)]
    simp only [sum_range_one, g, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero,zero_add]
    change |∑ k ∈ Ico 1 (H+1), g k| ≤ _
    rw [show Ico 1 (H+1) = Icc 1 H by ext k; simp only [mem_Ico,mem_Icc]; omega]
    apply (box _ C (fun k hk => low k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2)).trans
    have hi := sum_Icc_inv_sq_le_two H
    simpa only [one_div,mul_comm C] using mul_le_mul_of_nonneg_left hi hC
  apply le_of_tendsto hz.tendsto_sum_nat.abs
  filter_upwards [eventually_ge_atTop (H+1)] with M hM
  change |∑ k ∈ range M, g k| ≤ _
  rw [← sum_range_add_sum_Ico g hM]
  apply (abs_add_le _ _).trans (add_le_add hhead ?_)
  apply (box _ T (fun k hk => high k (mem_Ico.mp hk).1)).trans
  have ht : (∑ k ∈ Ico (H+1) M, 1/(k : ℝ)^2) ≤ 1/(H : ℝ) := by
    apply le_trans _ (sum_inv_sq_tail_le hH M)
    apply sum_le_sum_of_subset_of_nonneg
    · exact fun k hk => mem_Icc.mpr ⟨(mem_Ico.mp hk).1,(mem_Ico.mp hk).2.le⟩
    · exact fun _ _ _ => by positivity
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left ht hT

private def primes (A B : ℕ) := (Ico A B).filter Nat.Prime

private def mass (A B : ℕ) : ℝ := ∑ p ∈ primes A B, Real.log p

private theorem mass_bound {A B : ℕ} (hA : 1 ≤ A) (hB : B ≤ 2*A) : mass A B ≤ 14*A := by
  calc
    mass A B = ∑ p ∈ primes A B, vonMangoldt p := by
      apply sum_congr rfl
      exact fun p hp => (vonMangoldt_apply_prime (mem_filter.mp hp).2).symm
    _ ≤ ∑ p ∈ Icc 1 B, vonMangoldt p := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hl,hu⟩ := mem_Ico.mp (mem_filter.mp hp).1
        exact mem_Icc.mpr ⟨hA.trans hl,hu.le⟩
      · exact fun _ _ _ => vonMangoldt_nonneg
    _ ≤ 7*B := chebyshevPsi_le_seven B
    _ ≤ 14*A := by exact_mod_cast (show 7*B ≤ 14*A by omega)

private def cosineSum (A B : ℕ) (Y h : ℝ) (k : ℕ) :=
  ∑ p ∈ primes A B, Real.log p * Real.cos (2*Real.pi*k*(Y/p+h))

private def bernoulliSum (A B : ℕ) (Y h : ℝ) :=
  ∑ p ∈ primes A B, Real.log p * bernoulli (Y/p+h)

private theorem cosine_series (A B : ℕ) (Y h : ℝ) :
    HasSum (fun k => cosineSum A B Y h k/(k : ℝ)^2) (2*Real.pi^2*bernoulliSum A B Y h) := by
  have hh := hasSum_sum (s := primes A B) fun p _ =>
    (hasSum_cos_div_sq (Y/p+h)).mul_left (Real.log p)
  have he (x : ℝ) : 1/12-sawPrimitive x = bernoulli x := by
    unfold sawPrimitive bernoulli quadratic; ring
  simp only [he] at hh
  have total : 2*Real.pi^2*bernoulliSum A B Y h =
      ∑ p ∈ primes A B, Real.log p*(2*Real.pi^2*bernoulli (Y/p+h)) := by
    unfold bernoulliSum
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  rw [total]
  exact hh.congr_fun fun k => by simp only [cosineSum,sum_div,mul_div_assoc]

private theorem cosine_high (A B : ℕ) (Y h : ℝ) (k : ℕ) :
    |cosineSum A B Y h k| ≤ mass A B := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p _
  rw [abs_mul,abs_of_nonneg (Real.log_natCast_nonneg p)]
  exact mul_le_of_le_one_right (Real.log_natCast_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)

private theorem cosine_low (A B : ℕ) (Y h : ℝ) (k : ℕ) :
    |cosineSum A B Y h k| ≤
      ‖∑ p ∈ primes A B, (Real.log p : ℂ)*reciprocalPhase (2*Real.pi*k*Y) p‖ := by
  let r := 2*Real.pi*k
  let u := Complex.exp (((r*h : ℝ) : ℂ)*Complex.I)
  have hu : ‖u‖ = 1 := by simp [u,Complex.norm_exp]
  let Z := ∑ p ∈ primes A B, (Real.log p : ℂ)*reciprocalPhase (r*Y) p
  have he : (u*Z).re = cosineSum A B Y h k := by
    dsimp only [Z,cosineSum]
    rw [mul_sum, Complex.re_sum]
    apply sum_congr rfl
    intro p _
    have harg : ((r*h : ℝ) : ℂ)*Complex.I+(((r*Y/(p : ℝ) : ℝ) : ℂ))*Complex.I =
        (((r*(Y/p+h) : ℝ) : ℂ))*Complex.I := by push_cast; ring
    have hphase : u*reciprocalPhase (r*Y) p =
        Complex.exp (((r*(Y/p+h) : ℝ) : ℂ)*Complex.I) := by
      dsimp only [u,reciprocalPhase]
      rw [← Complex.exp_add,harg]
    rw [mul_left_comm u, hphase, Complex.re_ofReal_mul, Complex.exp_re]
    simp [r]
  rw [← he]
  simpa only [norm_mul,hu,one_mul] using Complex.abs_re_le_norm (u*Z)

/-- Two shifts of the Bernoulli primitive bound the signed sawtooth even when a
reciprocal argument is an integer. -/
private theorem saw_bound {A B : ℕ} {Y δ M : ℝ} (hδ : 0 < δ)
    (hM : ∀ h, |bernoulliSum A B Y h| ≤ M) :
    |∑ p ∈ primes A B, Real.log p*(Int.fract (Y/p)-1/2)| ≤
      2*M/δ+δ*mass A B/2 := by
  let S := ∑ p ∈ primes A B, Real.log p*(Int.fract (Y/p)-1/2)
  have diff (h : ℝ) : bernoulliSum A B Y h-bernoulliSum A B Y 0 ≤
      h*S+h^2/2*mass A B := by
    simp only [bernoulliSum,S,mass,add_zero,← sum_sub_distrib,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro p _
    have hh := mul_le_mul_of_nonneg_left (bernoulli_difference (Y/p) h) (Real.log_natCast_nonneg p)
    linarith only [hh]
  have hh (h : ℝ) : -(2*M) ≤ h*S+h^2/2*mass A B := by
    linarith only [diff h,(abs_le.mp (hM h)).1,(abs_le.mp (hM 0)).2]
  change |S| ≤ _
  rw [abs_le]
  have hc : (2*M/δ+δ*mass A B/2)*δ = 2*M+δ^2/2*mass A B := by field_simp
  constructor
  · apply le_of_mul_le_mul_right (a := δ) _ hδ
    rw [neg_mul,hc]
    linarith only [hh δ]
  · apply le_of_mul_le_mul_right (a := δ) _ hδ
    rw [hc]
    linarith only [hh (-δ)]

/-- Uniform power saving for the raw fractional part at the reciprocal of each
ordinary prime in any subinterval of the dyadic block. -/
theorem centered_fractional_reciprocal_prime_block :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : ℕ) (Y : ℝ), 1 ≤ A → A ≤ B → B ≤ 2*A →
      (A : ℝ)^(999/500 : ℝ) ≤ Y → Y ≤ (A : ℝ)^(1001/500 : ℝ) →
      |∑ p ∈ (Ico A B).filter Nat.Prime, Real.log p*(Int.fract (Y/p)-1/2)| ≤
        K*(A : ℝ)^(999/1000 : ℝ) := by
  obtain ⟨C,hC,hprime⟩ := reciprocal_ordinary_prime_block
  obtain ⟨L,hL⟩ := eventually_atTop.mp (eventually_const_mul_one_add_log_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1/1000) (show 0 < 2*Real.pi by positivity) 0)
  let K := 4*C+63+14*|L|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,fun A B Y hA hAB hB hY hY' => ?_⟩
  have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have ha0 : (0 : ℝ) < A := zero_lt_one.trans_le ha
  let P (b : ℝ) := (A : ℝ)^b
  have pos (a : ℝ) : 0 < P a := Real.rpow_pos_of_pos ha0 _
  have mono {a b : ℝ} (h : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le ha h
  have mul (a b : ℝ) : P a*P b=P (a+b) := (Real.rpow_add ha0 _ _).symm
  have divide (a b : ℝ) : P a/P b=P (a-b) := (Real.rpow_sub ha0 _ _).symm
  have one : P 1 = A := Real.rpow_one _
  have hm := mass_bound hA hB
  change |∑ p ∈ primes A B, Real.log p*(Int.fract (Y/p)-1/2)| ≤ K*P _
  by_cases hAL : L ≤ A
  · have hc : 2*Real.pi ≤ P (1/1000) := by simpa only [pow_zero,mul_one] using hL _ hAL
    let H := ⌊P (1/250)⌋₊
    have htwo : 2 ≤ P (1/250) :=
      (show 2 ≤ 2*Real.pi by linarith only [Real.pi_gt_three]).trans (hc.trans (mono (by norm_num)))
    have hH : 1 ≤ H := (Nat.one_le_floor_iff _).mpr (by linarith only [htwo])
    have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
    have hHlo : P (1/250) ≤ 2*(H : ℝ) := by linarith only [Nat.lt_floor_add_one (P (1/250)),htwo]
    have hHhi : (H : ℝ) ≤ P (1/250) := Nat.floor_le (pos _).le
    have bern (h : ℝ) : |bernoulliSum A B Y h| ≤ (2*C+28)*P (249/250) := by
      have low (k : ℕ) (hk : 1 ≤ k) (hkH : k ≤ H) : |cosineSum A B Y h k| ≤ C*P (99/100) := by
        apply (cosine_low A B Y h k).trans (hprime A B _ hA hAB hB ?_ ?_)
        · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
          have hf : 1 ≤ 2*Real.pi*k := one_le_mul_of_one_le_of_one_le
            (by linarith only [Real.pi_gt_three]) hk'
          exact ((mono (by norm_num : (199/100 : ℝ) ≤ 999/500)).trans hY).trans
            (le_mul_of_one_le_left ((pos _).le.trans hY) hf)
        · have hk' : (k : ℝ) ≤ P (1/250) := (by exact_mod_cast hkH : (k : ℝ) ≤ H).trans hHhi
          have hs := mul_le_mul (mul_le_mul hc hk' (Nat.cast_nonneg k) (pos _).le)
            hY' ((pos _).le.trans hY) (mul_nonneg (pos _).le (pos _).le)
          apply hs.trans
          rw [mul,mul]; exact mono (by norm_num)
      have hh := abs_series_le (cosine_series A B Y h) hH
        (mul_nonneg hC (pos _).le) (show 0 ≤ 14*(A : ℝ) by positivity) low
        (fun k _ => (cosine_high A B Y h k).trans hm)
      have htail : 14*(A : ℝ)/(H : ℝ) ≤ 28*P (249/250) := by
        rw [show (249/250 : ℝ) = 1-1/250 by norm_num,← divide,one,← mul_div_assoc]
        apply (div_le_div_iff₀ hHr (pos _)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hHlo (show 0 ≤ 14*(A : ℝ) by positivity)]
      have coeff : 1 ≤ 2*Real.pi^2 := by nlinarith only [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
      rw [abs_mul,abs_of_nonneg (zero_le_one.trans coeff)] at hh
      apply (le_mul_of_one_le_left (abs_nonneg _) coeff).trans (hh.trans ?_)
      have hlow := mul_le_mul_of_nonneg_left (mono (by norm_num : (99/100 : ℝ) ≤ 249/250))
        (show 0 ≤ 2*C by positivity)
      linarith only [hlow,htail]
    let δ := P (-(1/1000))
    apply (saw_bound (δ := δ) (pos _) bern).trans
    have h₁ : 2*((2*C+28)*P (249/250))/δ ≤ 2*(2*C+28)*P (999/1000) := by
      calc
        _ = (2*(2*C+28))*(P (249/250)/δ) := by ring
        _ ≤ _ := by
          rw [show P (249/250)/δ = P (249/250-(-(1/1000))) from divide _ _]
          exact mul_le_mul_of_nonneg_left (mono (by norm_num)) (by positivity)
    have h₂ : δ*mass A B/2 ≤ 7*P (999/1000) := by
      have h := mul_le_mul_of_nonneg_left hm (pos (-(1/1000))).le
      have he : δ*(14*A) = 14*P (999/1000) := by
        rw [show (999/1000 : ℝ) = (-(1/1000))+1 by norm_num,← mul,one]; dsimp [δ]; ring
      linarith only [h,he]
    have hcoef : 2*(2*C+28)+7 ≤ K := by dsimp [K]; linarith only [abs_nonneg L]
    apply (add_le_add h₁ h₂).trans
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hcoef (pos _).le
  · have hf (x : ℝ) : |Int.fract x-1/2| ≤ 1 := abs_le.mpr (by
      constructor <;> linarith only [Int.fract_nonneg x,Int.fract_lt_one x])
    have ht : |∑ p ∈ primes A B, Real.log p*(Int.fract (Y/p)-1/2)| ≤ mass A B := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro p _
      rw [abs_mul,abs_of_nonneg (Real.log_natCast_nonneg p)]
      exact mul_le_of_le_one_right (Real.log_natCast_nonneg _) (hf _)
    have hk : 14*(A : ℝ) ≤ K := by dsimp [K]; linarith only [hC,not_le.mp hAL,le_abs_self L]
    exact (ht.trans (hm.trans hk)).trans (le_mul_of_one_le_right hK (Real.one_le_rpow ha (by norm_num)))

#print axioms centered_fractional_reciprocal_prime_block

end GaloisForLFunctions.PrimeExponentialSums
