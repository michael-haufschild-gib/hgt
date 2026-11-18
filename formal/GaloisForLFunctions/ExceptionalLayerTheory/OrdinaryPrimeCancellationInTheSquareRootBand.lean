import GaloisForLFunctions.ExceptionalLayerTheory.CenteringTheFactorialPrimeWeight
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOfReciprocalPrimes
import GaloisForLFunctions.RHTower.Sieve.KubalalikaDyadic

/-!
# Ordinary-prime cancellation in the square-root band

The centered factorial weight tests ordinary primes at finitely many reciprocal
frequencies. Near the square root, the power saving for every sharp prime block
pays the linear coefficient mass and the logarithmic cost of dyadic subdivision.
-/

noncomputable section
open Finset Filter ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The reciprocal-prime theorem applies at every divisor of the centered
factorial weight throughout a fixed band on both sides of the square root. -/
private theorem block_frequency_range {X A d : ℕ}
    (hX : 1 ≤ X) (hd : 1 ≤ d)
    (hlarge : 100000 ≤ (X : ℝ)^(1/10000 : ℝ))
    (hlo : (X : ℝ)^(49999/100000 : ℝ) ≤ A)
    (hhi : (A : ℝ) ≤ 2*(X : ℝ)^(50001/100000 : ℝ))
    (hd' : (d : ℝ) ≤ 16512*(X : ℝ)^(2/100000 : ℝ)) :
    (A : ℝ)^(999/500 : ℝ) ≤ (X : ℝ)/d ∧ (X : ℝ)/d ≤ (A : ℝ)^(1001/500 : ℝ) := by
  let P (b : ℝ) := (X : ℝ)^b
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := zero_lt_one.trans_le hx
  have pos (a : ℝ) : 0 < P a := Real.rpow_pos_of_pos hx0 _
  have mono {a b : ℝ} (h : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx h
  have mul (a b : ℝ) : P a*P b = P (a+b) := (Real.rpow_add hx0 _ _).symm
  have one : P 1 = X := Real.rpow_one _
  have powr (a b : ℝ) : (P a)^b = P (a*b) := (Real.rpow_mul hx0.le _ _).symm
  have ha' : (A : ℝ) ≤ P (1/10000+50001/100000) := by
    rw [← mul]; apply hhi.trans
    exact mul_le_mul_of_nonneg_right (by linarith only [hlarge]) (pos _).le
  have hd'' : (d : ℝ) ≤ P (1/10000+2/100000) := by
    rw [← mul]; apply hd'.trans
    exact mul_le_mul_of_nonneg_right (by linarith only [hlarge]) (pos _).le
  constructor
  · apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
    apply (mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg A) ha' (by norm_num : (0 : ℝ) ≤ 999/500))
      hd'' (Nat.cast_nonneg d) (Real.rpow_nonneg (pos _).le _)).trans
    rw [powr,mul,← one]
    exact mono (by norm_num)
  · have hxx : (X : ℝ)/d ≤ X := div_le_self (Nat.cast_nonneg X) (by exact_mod_cast hd)
    apply hxx.trans
    have h := Real.rpow_le_rpow (pos _).le hlo (by norm_num : (0 : ℝ) ≤ 1001/500)
    rw [powr] at h
    apply le_trans _ h
    rw [← one]
    exact mono (by norm_num)

/-- On a dyadic prime block in the band the centered weight saves a power
of the block length after paying its linear coefficient mass. -/
private theorem centered_prime_block :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R X A B : ℕ, 1 ≤ R → 1 ≤ X → 1 ≤ A → A ≤ B → B ≤ 2*A →
      100000 ≤ (X : ℝ)^(1/10000 : ℝ) →
      (X : ℝ)^(49999/100000 : ℝ) ≤ A → (A : ℝ) ≤ 2*(X : ℝ)^(50001/100000 : ℝ) →
      (R : ℝ) ≤ (X : ℝ)^(1/100000 : ℝ) →
      |∑ p ∈ (Ico A B).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)| ≤
      1000*(1+mass R)*(K*(A : ℝ)^(999/1000 : ℝ)) := by
  obtain ⟨K,hK,hblock⟩ := PrimeExponentialSums.centered_fractional_reciprocal_prime_block
  refine ⟨K,hK,fun R X A B hR hX hA hAB hB hlarge hlo hhi hR' => ?_⟩
  apply abs_centered_block hR X _ _ (by positivity)
  intro d hd
  obtain ⟨h1,h2⟩ := mem_Icc.mp hd
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hs : (R : ℝ)^2 ≤ (X : ℝ)^(2/100000 : ℝ) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg R) hR' 2).trans_eq
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul (zero_le_one.trans hX1)]
    norm_num
  have hc : (d : ℝ) ≤ 128*(128*(R : ℝ)^2+1) := by exact_mod_cast h2
  have hd' : (d : ℝ) ≤ 16512*(X : ℝ)^(2/100000 : ℝ) := by
    linarith only [hc,hs,Real.one_le_rpow hX1 (by norm_num : (0 : ℝ) ≤ 2/100000)]
  obtain ⟨hl,hu⟩ := block_frequency_range hX h1 hlarge hlo hhi hd'
  exact hblock A B ((X : ℝ)/d) hA hAB hB hl hu

/-- Any sharp subinterval of the reciprocal-prime band saves a fixed
power below the square root, uniformly in the factorial cutoff. -/
theorem centered_prime_subinterval :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R X L U : ℕ, 1 ≤ R → 1 ≤ X → 1 ≤ L →
      (R : ℝ) ≤ (X : ℝ)^(1/100000 : ℝ) → (X : ℝ)^(49999/100000 : ℝ) ≤ L →
      (U : ℝ) ≤ 2*(X : ℝ)^(50001/100000 : ℝ) →
      |∑ p ∈ (Ico L U).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)| ≤
        K*(X : ℝ)^(4997/10000 : ℝ) := by
  obtain ⟨C,hC,hblock⟩ := centered_prime_block
  obtain ⟨D,hD,hm⟩ := mass_uniform
  obtain ⟨F,hF,hweight⟩ := centeredPrimeWeight_uniform
  have hthreshold := RHTower.Sieve.eventually_const_mul_one_add_log_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1/10000) (show (0 : ℝ) < 100000 by norm_num) 0
  have hlog := RHTower.Sieve.eventually_const_mul_one_add_log_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1/10000) (show (0 : ℝ) < 1 by norm_num) 1
  obtain ⟨Y,hY⟩ := Filter.eventually_atTop.mp (hthreshold.and hlog)
  let K := 1+8000*(1+D)*C+14*F*(1+|Y|)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,fun R X L U hrlo hX hL hrhi hllo humax => ?_⟩
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hx0 := (zero_lt_one.trans_le hx)
  let P (b : ℝ) := (X : ℝ)^b
  have pos (a : ℝ) : 0 < P a := Real.rpow_pos_of_pos hx0 _
  have one : P 1 = X := Real.rpow_one _
  have mono {a b : ℝ} (h : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx h
  have mul (a b : ℝ) : P a*P b=P (a+b) := (Real.rpow_add hx0 _ _).symm
  have powr (a b : ℝ) : (P a)^b = P (a*b) := (Real.rpow_mul hx0.le _ _).symm
  change (R : ℝ) ≤ P (1/100000) at hrhi
  have huX : (U : ℝ) ≤ 2*X := humax.trans <| mul_le_mul_of_nonneg_left
    ((mono (by norm_num : (50001/100000 : ℝ) ≤ 1)).trans_eq one) (by norm_num)
  by_cases hlu : L ≤ U
  swap
  · rw [Ico_eq_empty (by omega),filter_empty,sum_empty,abs_zero]
    positivity
  have hu0 : (0 : ℝ) < U := by exact_mod_cast hL.trans hlu
  by_cases hXY : Y ≤ X
  · obtain ⟨hbig,hlogX⟩ := hY _ hXY
    simp only [pow_zero,mul_one,pow_one,one_mul] at hbig hlogX
    change 1+Real.log X ≤ P (1/10000) at hlogX
    have hM : 1+mass R ≤ (1+D)*P (1/100000) := by
      have h := (hm R hrlo).trans (mul_le_mul_of_nonneg_left hrhi hD)
      have h1 := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1/100000)
      linarith only [h,h1]
    let E := (50001/100000 : ℝ)*(999/1000)
    have hsub (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2*A) (hLA : L ≤ A) (hBU : B ≤ U) :
        |∑ p ∈ (Ico A B).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)| ≤
        (2000*(1+D)*C)*(P (1/100000)*P E) := by
      have ha : (A : ℝ) ≤ 2*P (50001/100000) :=
        (by exact_mod_cast hAB.trans hBU : (A : ℝ) ≤ U).trans humax
      have hh := hblock R X A B hrlo hX hA hAB hBA hbig
        (hllo.trans (by exact_mod_cast hLA)) ha hrhi
      have hb : (A : ℝ)^(999/1000 : ℝ) ≤ 2*P E := by
        apply (Real.rpow_le_rpow (Nat.cast_nonneg A) ha (by norm_num)).trans
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pos _).le,powr]
        apply mul_le_mul_of_nonneg_right _ (pos _).le
        apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (999/1000 : ℝ) ≤ 1)).trans_eq
        exact Real.rpow_one _
      exact hh.trans ((mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 1000))
        (mul_le_mul_of_nonneg_left hb hC) (mul_nonneg hC (by positivity)) (by positivity)).trans_eq (by ring))
    let f (p : ℕ) := if p.Prime then Real.log p*centeredPrimeWeight R (X/p) else 0
    have htotal := RHTower.Sieve.norm_sum_Ico_le_of_blocks f
      ((2000*(1+D)*C)*(P (1/100000)*P E)) hlu hL (by positivity)
      (fun A B hA hAB hBA hLA hBU => by simpa [f,Real.norm_eq_abs,sum_filter] using hsub A B hA hAB hBA hLA hBU)
    have hlU : 1+Real.log U ≤ 2*P (1/10000) := by
      have hl := Real.log_le_log hu0 huX
      rw [Real.log_mul (by norm_num) hx0.ne'] at hl
      have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [hl,h2,hlogX,Real.log_natCast_nonneg X]
    have ht := htotal.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlU (by norm_num : (0 : ℝ) ≤ 2)) (by positivity))
    have he : P (1/10000)*(P (1/100000)*P E) ≤ P (4997/10000) := by
      rw [mul (1/100000) E,mul]
      apply mono
      dsimp [E]; norm_num
    have hcoef : 8000*(1+D)*C ≤ K := by
      dsimp [K]
      linarith only [show (0 : ℝ) ≤ 14*F*(1+|Y|)^2 by positivity]
    have hf := mul_le_mul hcoef he (by positivity) hK
    calc
      _ ≤ (2*(2*P (1/10000)))*((2000*(1+D)*C)*(P (1/100000)*P E)) := by
        simpa only [f,Real.norm_eq_abs,sum_filter] using ht
      _ = (8000*(1+D)*C)*(P (1/10000)*(P (1/100000)*P E)) := by ring
      _ ≤ _ := hf
  · have hmR : (R : ℝ) ≤ X := hrhi.trans ((mono (by norm_num : (1/100000 : ℝ) ≤ 1)).trans_eq one)
    have hsmall : |∑ p ∈ (Ico L U).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)| ≤
        (F*R)*(7*U) := centered_prime_absolute_bound hrlo hweight hL
    have hY' : (X : ℝ) ≤ 1+|Y| := by linarith only [not_le.mp hXY,le_abs_self Y]
    have hb := mul_le_mul (mul_le_mul_of_nonneg_left (hmR.trans hY') hF)
      (mul_le_mul_of_nonneg_left (huX.trans (mul_le_mul_of_nonneg_left hY' (by norm_num : (0 : ℝ) ≤ 2)))
        (by norm_num : (0 : ℝ) ≤ 7))
      (by positivity) (by positivity)
    have hroot : 1 ≤ P (4997/10000) := Real.one_le_rpow hx (by norm_num)
    apply hsmall.trans (hb.trans _)
    apply le_trans _ (le_mul_of_one_le_right hK hroot)
    dsimp [K]; linarith only [mul_nonneg (show 0 ≤ 8000*(1+D) by positivity) hC]

/-- The whole ordinary-prime band contributes at most square-root error. -/
theorem centered_prime_square_root_band :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X →
      let R := ⌊(X : ℝ)^(1/100000 : ℝ)⌋₊
      let L := ⌈(X : ℝ)^(49999/100000 : ℝ)⌉₊
      let U := ⌊(X : ℝ)^(50001/100000 : ℝ)⌋₊+1
      |∑ p ∈ (Ico L U).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)| ≤ K*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := centered_prime_subinterval
  refine ⟨K,hK,fun X hX => ?_⟩
  intro R L U
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hone (b : ℝ) (hb : 0 ≤ b) := Real.one_le_rpow hx hb
  have hu : (U : ℝ) ≤ 2*(X : ℝ)^(50001/100000 : ℝ) := by
    dsimp [U]; push_cast
    linarith only [Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) (50001/100000 : ℝ)),
      hone (50001/100000) (by norm_num)]
  apply (h R X L U ((Nat.one_le_floor_iff _).mpr (hone _ (by norm_num))) hX
    (Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _))
    (Nat.floor_le (by positivity)) (Nat.le_ceil _) hu).trans
  rw [Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) hK

#print axioms centered_prime_subinterval
#print axioms centered_prime_square_root_band

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
