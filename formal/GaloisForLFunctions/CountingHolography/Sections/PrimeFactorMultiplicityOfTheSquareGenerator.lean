import GaloisForLFunctions.CountingHolography.Sections.ThePrimeExponentsOnTheSquareDiagonal
import GaloisForLFunctions.CountingHolography.Sections.TheLogarithmicMomentOfTheSquarePrimeProfile
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeAbelCutoff

/-! # The excess of numerator prime factors on the square diagonal

Centering the logarithmic prime weights at log(n²) exposes a negative
first moment. After division by (log(n²))² it gives a positive cubic
leading term in the difference of the two prime-factor counts.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticFunction MeasureTheory SquareRootThreshold
open ArithmeticWeightTheory ArithmeticCastelnuovoSeveri _root_.RHTower _root_.RHTower.WeilDeletion

private def lags (n : ℕ) := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
private def T (n : ℕ) := Real.log ((n:ℝ)^2)
private def firstMoment (n : ℕ) := ∑ k ∈ lags n, Real.log k*(Real.log k-T n)*diagonalPrimeProfile n k
private def secondMoment (n : ℕ) := ∑ k ∈ lags n, (Real.log k-T n)^2*diagonalPrimeProfile n k

private theorem profile_test_limit {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => (∑ k ∈ lags n, Real.log k*g (Real.log k-T n)*diagonalPrimeProfile n k)/(n:ℝ)^3)
      atTop (𝓝 (2*∫ u : ℝ, (g u*squareLogProfile u)*Real.exp (u/2))) := by
  refine ((tendsto_diagonal_finite_prime_test hg).const_mul 2).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  let V := fun k : ℕ => Real.log ((k:ℝ)/(n:ℝ)^2)
  let f := fun k : ℕ => Real.log k*(g (V k)*squareLogProfile (V k)/Real.sqrt ((k:ℝ)/(n:ℝ)^2))
  have hsum : (∑ k ∈ lags n, Real.log k*g (Real.log k-T n)*diagonalPrimeProfile n k) =
      (2*(n:ℝ))*(∑ k ∈ lags n, f k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hp := (mem_filter.mp hk).2
    have hl : Real.log k-T n=V k := (Real.log_div (Nat.cast_pos.mpr hp.pos).ne' (sq_pos_of_pos hn').ne').symm
    rw [diagonalPrimeProfile_eq_dilate hn hp.pos,hl]
    dsimp only [f,V]
    ring
  change 2*((∑ k ∈ lags n, f k)/(n:ℝ)^2)=_
  rw [hsum]
  field_simp

private theorem first_limit :
    Tendsto (fun n : ℕ => firstMoment n/(n:ℝ)^3) atTop (𝓝 (-4*Real.log 4*squareAutocorrelationMass)) := by
  have h := profile_test_limit (g := fun u : ℝ => u) continuous_id
  rw [squareLogProfile_first_half_moment,show 2*(-2*Real.log 4*squareAutocorrelationMass)=
    -4*Real.log 4*squareAutocorrelationMass by ring] at h
  exact h

/-- Every bounded continuous test of the actual logarithmically weighted
valuations converges to the difference of two translated positive measures. -/
theorem tendsto_square_generator_prime_test {g : ℝ → ℝ} (hg : Continuous g)
    {B : ℝ} (hB : ∀ u, |g u|≤B) :
    Tendsto (fun n : ℕ => let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
      (∑ k ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)),
        Real.log k*g (Real.log k-Real.log ((n:ℝ)^2))*(deningerRatExp q k:ℝ))/(n:ℝ)^3)
      atTop (𝓝 (4*∫ u : ℝ, (g u-g (u+Real.log 4))*(splineAutoCorr u*Real.exp (u/2)))) := by
  obtain ⟨C,hC,herr⟩ := diagonal_prime_exponent_profile_error
  let e := fun n k : ℕ => (deningerRatExp (ordinaryPrimeGenerator (n • successorSquareTriple n)) k:ℝ)
  let D := fun n : ℕ => ∑ k ∈ lags n,
    Real.log k*g (Real.log k-T n)*(e n k-diagonalPrimeProfile n k)
  have hB₀ := (abs_nonneg (g 0)).trans (hB 0)
  have hlim : Tendsto (fun n : ℕ => D n/(n:ℝ)^3) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (B*C)/(n:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply squeeze_zero_norm' _ h
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
    have hh : |D n|≤B*(C*(n:ℝ)^2) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ k ∈ lags n, B*(|e n k-diagonalPrimeProfile n k| * ArithmeticFunction.vonMangoldt k) :=
            sum_le_sum fun k hk => by
              have hp := (mem_filter.mp hk).2
              have hl := Real.log_natCast_nonneg k
              rw [abs_mul,abs_mul,abs_of_nonneg hl,ArithmeticFunction.vonMangoldt_apply_prime hp]
              exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB _) hl) (abs_nonneg _)).trans_eq (by ring)
        _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (herr hn) hB₀
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos hn' _)]
    exact (div_le_div_of_nonneg_right hh (pow_nonneg hn'.le _)).trans_eq (by field_simp <;> ring)
  have h := (profile_test_limit hg).add hlim
  rw [add_zero,squareLogProfile_test_translation hg] at h
  have hh : ∀ z : ℝ, 2*(2*z)=4*z := fun _ => by ring
  rw [hh] at h
  apply h.congr'
  filter_upwards [] with n
  change _/(n:ℝ)^3+D n/(n:ℝ)^3=_
  dsimp only [D]
  rw [← add_div,← sum_add_distrib]
  exact congrArg (·/(n:ℝ)^3) (sum_congr rfl fun k _ => by dsimp only [e,T]; ring)

private theorem lags_card_negligible :
    Tendsto (fun n : ℕ => ((lags n).card:ℝ)/(n:ℝ)^2) atTop (𝓝 0) := by
  let L := fun n : ℕ => 3*windowEnd ((2*n+1)^2+1)
  have hinf : Tendsto L atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro b
    refine ⟨max 1 b,fun n hn => ?_⟩
    have hn₁ : 1 ≤ (n:ℝ) := by exact_mod_cast (le_max_left 1 b).trans hn
    have hbd := (successorSquareWindowScale_bounds n).1.trans (successorSquareWindowScale_bounds n).2.2
    have hsq : (n:ℝ)≤(n:ℝ)^2 := by nlinarith only [mul_le_mul_of_nonneg_left hn₁ (Nat.cast_nonneg n : 0 ≤ (n:ℝ))]
    have hh : n ≤ windowEnd ((2*n+1)^2+1) := by exact_mod_cast hsq.trans hbd
    dsimp only [L]
    omega
  obtain ⟨A,hA,ha⟩ := successorSquare_window_bound
  have hcount (n : ℕ) : (lags n).card=Nat.primeCounting (L n) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    congr 1
    ext k
    rw [Nat.mem_primesLE]
    change k ∈ (Icc 2 (L n)).filter Nat.Prime ↔ _
    rw [mem_filter,mem_Icc]
    exact ⟨fun h => ⟨h.1.2,h.2⟩,fun h => ⟨⟨h.2.two_le,h.1⟩,h.2⟩⟩
  have h := (GaugeDeformations.tendsto_primeCounting_div_nat_zero.comp hinf).mul_const (A^2)
  rw [zero_mul] at h
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) _ h
  filter_upwards [eventually_gt_atTop 0,hinf.eventually_gt_atTop 0] with n hn hL
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hL' : 0 < (L n:ℝ) := Nat.cast_pos.mpr hL
  rw [hcount]
  change _ ≤ ((Nat.primeCounting (L n):ℝ)/(L n:ℝ))*A^2
  have hb : (L n:ℝ) ≤ A^2*(n:ℝ)^2 := by simpa only [mul_pow] using ha hn
  rw [div_mul_eq_mul_div,div_le_div_iff₀ (sq_pos_of_pos hn') hL']
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Nat.primeCounting (L n)) : (0:ℝ)≤_)

private theorem second_limit : Tendsto (fun n : ℕ => secondMoment n/(n:ℝ)^3) atTop (𝓝 0) := by
  let F := fun t : ℝ => t^2*squareLogProfile t*Real.exp (-t/2)
  have hc : Continuous squareLogProfile := (continuous_const.mul continuous_splineAutoCorr).sub
    (continuous_splineAutoCorr.comp (continuous_id.sub continuous_const))
  have hkH : HasCompactSupport splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact hasCompactSupport_upow 1 7
  have hk : HasCompactSupport squareLogProfile := hkH.mul_left.sub
    (hkH.comp_homeomorph (Homeomorph.subRight (Real.log 4)))
  have hF : Continuous F := ((continuous_id.pow 2).mul hc).mul (by fun_prop)
  obtain ⟨B,hB⟩ := (show HasCompactSupport F from hk.mul_left.mul_right).exists_bound_of_continuous hF
  have hlim := lags_card_negligible.const_mul (2*B)
  rw [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have he {k : ℕ} (hp : k.Prime) :
      (Real.log k-T n)^2*diagonalPrimeProfile n k=2*(n:ℝ)*F (Real.log ((k:ℝ)/(n:ℝ)^2)) := by
    have hk' : 0<(k:ℝ) := Nat.cast_pos.mpr hp.pos
    have hX := div_pos hk' (sq_pos_of_pos hn')
    have hl : Real.log k-T n=Real.log ((k:ℝ)/(n:ℝ)^2) :=
      (Real.log_div hk'.ne' (sq_pos_of_pos hn').ne').symm
    rw [hl,diagonalPrimeProfile_eq_dilate hn hp.pos]
    dsimp only [F]
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hX]
    rw [show -Real.log ((k:ℝ)/(n:ℝ)^2)/2 = -(Real.log ((k:ℝ)/(n:ℝ)^2)*(1/2)) by ring,Real.exp_neg]
    ring
  have hsum : |secondMoment n| ≤ (lags n).card*(2*(n:ℝ)*B) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ _k ∈ lags n, 2*(n:ℝ)*B := sum_le_sum fun k hk => by
              rw [he (mem_filter.mp hk).2,abs_mul,abs_of_nonneg (by positivity : 0≤2*(n:ℝ))]
              exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
      _ = _ := by simp
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (pow_pos hn' 3)]
  exact (div_le_div_of_nonneg_right hsum (pow_nonneg hn'.le _)).trans_eq (by field_simp)

private theorem log_over_power {r : ℝ} (hr : 0<r) :
    Tendsto (fun n : ℕ => T n/(n:ℝ)^r) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul 2
  simpa only [T,Real.log_pow,Nat.cast_ofNat,mul_div_assoc,mul_zero,Function.comp_apply] using h

/-- The two cubic logarithmic heights cancel to every fixed inverse
logarithmic order at the critical prime weight. -/
theorem diagonal_log_negligible_at_every_logarithmic_order (k : ℕ) :
    Tendsto (fun n : ℕ => (Real.log ((n:ℝ)^2))^k*Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)/(n:ℝ)^3)
      atTop (𝓝 0) := by
  obtain ⟨A,hA,ha⟩ := successorSquare_diagonal_log_at_width
  let r := 2*zetaZeroWidth
  have hr : 0≤r := mul_nonneg two_pos.le zetaZeroWidth_nonneg
  have hr' : 0<1-r := by
    dsimp only [r]
    linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths]
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (k:ℝ) hr').tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).const_mul ((2:ℝ)^k)
  have hlog : Tendsto (fun n : ℕ => T n^k/(n:ℝ)^(1-r)) atTop (𝓝 0) := by
    simpa only [T,Real.log_pow,Nat.cast_ofNat,mul_pow,mul_div_assoc,Real.rpow_natCast,mul_zero,Function.comp_apply] using hsmall
  have hlim := hlog.const_mul (A*2^r)
  rw [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans_le hn'
  have hT : 0≤T n := Real.log_nonneg (one_le_pow₀ hn')
  have hh := Real.rpow_le_rpow (by positivity : 0≤(n:ℝ)+1) (by linarith only [hn'] : (n:ℝ)+1≤2*n) hr
  rw [Real.mul_rpow two_pos.le hn₀.le] at hh
  have hb := (ha n hn).trans (mul_le_mul_of_nonneg_left hh (mul_nonneg hA (sq_nonneg _)))
  change ‖T n^k*Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)/(n:ℝ)^3‖ ≤ _
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (pow_nonneg hT k),abs_of_pos (pow_pos hn₀ 3)]
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (pow_nonneg hT k)) (pow_pos hn₀ 3).le).trans_eq ?_
  rw [Real.rpow_sub hn₀,Real.rpow_one]
  field_simp

private theorem comparison_error_limit (C : ℝ) :
    Tendsto (fun n : ℕ => (T n^2/Real.log 2+T n)*(C*(n:ℝ)^2)/(n:ℝ)^3) atTop (𝓝 0) := by
  have h₁ := (log_over_power (by norm_num : (0:ℝ)<1/2)).pow 2
  have h₂ := log_over_power (r := 1) one_pos
  have h := ((h₁.div_const (Real.log 2)).add h₂).const_mul C
  simp only [zero_pow two_ne_zero,zero_div,zero_add,mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  change C*((T n/(n:ℝ)^(1/2:ℝ))^2/Real.log 2+T n/(n:ℝ)^(1:ℝ))=_
  rw [div_pow,← Real.sqrt_eq_rpow,Real.sq_sqrt hn'.le,Real.rpow_one]
  field_simp

/-- The excess of numerator prime factors counted with multiplicity is
asymptotic to a strictly positive constant times n cubed divided by log(n²) squared. -/
theorem tendsto_square_generator_prime_multiplicity :
    Tendsto (fun n : ℕ => let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
      (Real.log ((n:ℝ)^2))^2*((cardFactors q.num.natAbs:ℝ)-cardFactors q.den)/(n:ℝ)^3)
      atTop (𝓝 (4*Real.log 4*squareAutocorrelationMass)) := by
  obtain ⟨C,hC,ha⟩ := diagonal_prime_multiplicity_comparison
  let A := fun n : ℕ => T n^2*(diagonalPrimeMultiplicity n:ℝ)
  let B := fun n : ℕ => T n*Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)
  have hdiff : Tendsto (fun n : ℕ => (A n-B n+firstMoment n-secondMoment n)/(n:ℝ)^3) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (comparison_error_limit C)
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3)]
    exact div_le_div_of_nonneg_right (ha hn) (pow_nonneg (Nat.cast_nonneg _) _)
  have hs : Tendsto (fun n : ℕ => B n/(n:ℝ)^3) atTop (𝓝 0) := by
    simpa only [B,T,pow_one] using diagonal_log_negligible_at_every_logarithmic_order 1
  have h := ((hdiff.add hs).sub first_limit).add second_limit
  have hc : (0:ℝ)+0-(-4*Real.log 4*squareAutocorrelationMass)+0=4*Real.log 4*squareAutocorrelationMass := by ring
  rw [hc] at h
  refine h.congr' ?_
  filter_upwards [] with n
  dsimp only [A,B]
  have hm := congrArg (fun x : ℤ => (x:ℝ)) (diagonalPrimeMultiplicity_eq_cardFactors n)
  simp only [Int.cast_sub,Int.cast_natCast] at hm
  change _ = (T n)^2*((cardFactors _:ℝ)-cardFactors _)/(n:ℝ)^3
  rw [hm]
  ring

/-- At every sufficiently large square conductor the reduced numerator
contains strictly more prime factors than the reduced denominator. -/
theorem eventually_square_generator_more_numerator_factors :
    ∀ᶠ n : ℕ in atTop, let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
      cardFactors q.den < cardFactors q.num.natAbs := by
  have hc : 0<4*Real.log 4*squareAutocorrelationMass :=
    mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) squareAutocorrelationMass_pos
  filter_upwards [tendsto_square_generator_prime_multiplicity.eventually (lt_mem_nhds hc)] with n h
  dsimp only at h ⊢
  by_contra! hn
  have hb : (cardFactors _:ℝ)-cardFactors _ ≤ 0 := sub_nonpos.mpr (Nat.cast_le.mpr hn)
  exact (not_lt_of_ge (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hb)
    (pow_nonneg (Nat.cast_nonneg n) 3))) h

#print axioms diagonal_log_negligible_at_every_logarithmic_order
#print axioms tendsto_square_generator_prime_test
#print axioms tendsto_square_generator_prime_multiplicity
#print axioms eventually_square_generator_more_numerator_factors

end GaloisForLFunctions.CountingHolography.Sections
