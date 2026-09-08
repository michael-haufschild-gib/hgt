import GaloisForLFunctions.RHTower.DivisorContinuousUnitMoment
import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreProfile
import GaloisForLFunctions.RHTower.RouteEEulerDeficitTransport

/-!
# A uniformly positive signed moment through finite prime processing

The complete processed head is the finite Moebius dilation of the literal
continuous unit source. Its integer values and every rational clipped
sample agree with the actual discrete head used in the prime correlation.
The absolutely convergent inverse-cube moment factors as a strictly positive
unit moment times the product of 1-sqrt(p)/p^2. Summable logarithmic deficits
give a strictly positive lower bound independent of the finite prime core.
This is a signed moment invariant, not a prime-correlation sign theorem.
-/

noncomputable section
open MeasureTheory Set Finset
namespace RHTower

/-- Every positive integer dilation agrees with the continuous unit head, including its clip. -/
theorem divisorContinuousUnitHead_dilation (M d : ℕ) (hd : 0 < d) :
    Real.sqrt d * divisorContinuousUnitHead ((M : ℝ)/d) =
      divisorUnsignedDilationChannel M d := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  by_cases hMd : M < d
  · rw [divisorContinuousUnitHead_eq_zero ((div_lt_one hdR).mpr (by exact_mod_cast hMd)).le]
    simp [divisorUnsignedDilationChannel, Finset.Icc_eq_empty_of_lt (by omega : M-1<d)]
  have hq : 1 ≤ M/d := (Nat.le_div_iff_mul_le hd).mpr (by omega)
  have hlo : ((M/d : ℕ):ℝ) ≤ (M:ℝ)/d := by
    rw [le_div_iff₀ hdR]
    exact_mod_cast Nat.div_mul_le_self M d
  have hhi : (M:ℝ)/d ≤ (M/d+1 : ℕ) := by
    rw [div_le_iff₀ hdR]
    exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ M hd).le : M ≤ (M/d+1)*d)
  rw [divisorContinuousUnitHead_between hq hlo hhi]
  have he : d*(M/d)+M%d=M := by have := Nat.mod_add_div M d; omega
  have hc := divisorUnsignedDilationChannel_mul_add d (M/d) (M%d) 1 hd (Nat.mod_lt M hd).le
  simp only [mul_one, Nat.div_one, he] at hc
  rw [hc, Real.sqrt_div (Nat.cast_nonneg M), Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg d)]
  have hn := (Real.sqrt_pos.mpr hdR).ne'
  field_simp

/-- Finite signed dilation of the actual unit source; no sign is imposed on this head. -/
def mobiusDivisorContinuousHead (P : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ (∏ p ∈ P, p).divisors,
    ((ArithmeticFunction.moebius d : ℤ):ℝ) * Real.sqrt d * divisorContinuousUnitHead (x/d)

/-- Divisor representation of the literal processed head at every cutoff. -/
theorem mobiusDivisorSelectionHead_eq_sum_divisors_all
    (M : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mobiusDivisorSelectionFibre M P ∅ =
      ∑ d ∈ (∏ p ∈ P, p).divisors, mobiusDivisorDilationChannel M d := by
  let D := ∏ p ∈ P, p
  have hD : 0<D := prod_pos (fun p hp => (hP p hp).pos)
  have hfac : D.primeFactors=P := Nat.primeFactors_prod hP
  have hlabel {d : ℕ} (hd : d∈D.divisors) : d.primeFactors\P=∅ :=
    sdiff_eq_empty_iff_subset.mpr (by
      rw [← hfac]
      exact Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hD.ne')
  rw [mobiusDivisorSelectionFibre_eq_sum_Icc]
  calc
    _ = ∑ d ∈ (Icc 1 M) ∩ D.divisors,
        if d.primeFactors\P=∅ then mobiusDivisorDilationChannel M d else 0 := by
      symm
      apply sum_subset inter_subset_left
      intro d hd hn
      have hnD : d∉D.divisors := fun h => hn (mem_inter.mpr ⟨hd,h⟩)
      by_cases hs : Squarefree d
      · have hne : d.primeFactors\P≠∅ := by
          intro he
          apply hnD
          apply Nat.mem_divisors.mpr
          refine ⟨?_,hD.ne'⟩
          rw [← Nat.prod_primeFactors_of_squarefree hs]
          exact prod_dvd_prod_of_subset d.primeFactors P id (sdiff_eq_empty_iff_subset.mp he)
        simp [hne]
      · simp [mobiusDivisorDilationChannel_eq_moebius_unsigned,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    _ = ∑ d ∈ (Icc 1 M) ∩ D.divisors, mobiusDivisorDilationChannel M d :=
      sum_congr rfl (fun d hd => if_pos (hlabel (mem_inter.mp hd).2))
    _ = _ := by
      apply sum_subset inter_subset_right
      intro d hd hn
      have hd0 := Nat.pos_of_mem_divisors hd
      have hMd : M<d := by
        by_contra h
        exact hn (mem_inter.mpr ⟨mem_Icc.mpr ⟨hd0,by omega⟩,hd⟩)
      simp [mobiusDivisorDilationChannel,
        Finset.Icc_eq_empty_of_lt (by omega : M-1<d)]

/-- Continuous and discrete processed heads agree at every integer cutoff. -/
theorem mobiusDivisorContinuousHead_nat (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (M : ℕ) :
    mobiusDivisorContinuousHead P M = mobiusDivisorSelectionFibre M P ∅ := by
  rw [mobiusDivisorSelectionHead_eq_sum_divisors_all M P hP, mobiusDivisorContinuousHead]
  apply sum_congr rfl
  intro d hd
  rw [mul_assoc, divisorContinuousUnitHead_dilation M d (Nat.pos_of_mem_divisors hd),
    mobiusDivisorDilationChannel_eq_moebius_unsigned]

/-- Every clipped rational sample in the complete prime correlation is a value
of this same continuous signed head. -/
theorem mobiusDivisorContinuousHead_div (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (M r : ℕ) (hr : 0<r) :
    mobiusDivisorContinuousHead P ((M:ℝ)/r) = mobiusDivisorInterpolatedFibre M r P ∅ := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  apply mul_left_cancel₀ (Real.sqrt_pos.mpr hrR).ne'
  rw [mobiusDivisorContinuousHead, mul_sum, mobiusDivisorInterpolatedFibre,
    mobiusDivisorSelectionHead_eq_sum_divisors_all _ P hP,
    mobiusDivisorSelectionHead_eq_sum_divisors_all _ P hP,
    mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hU := divisorContinuousUnitHead_dilation M (r*d) (Nat.mul_pos hr hd0)
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg r)] at hU
  have hc := divisorUnsignedDilationChannel_prime_interpolation M r d hr
  rw [hc] at hU
  simp only [mobiusDivisorDilationChannel_eq_moebius_unsigned]
  rw [div_div]
  linear_combination ((ArithmeticFunction.moebius d : ℤ):ℝ) * hU

private lemma dilation_integrand (d x : ℝ) (hd : d≠0) :
    divisorContinuousUnitHead (x/d)/x^3 =
      (d^3)⁻¹ * (divisorContinuousUnitHead (d⁻¹*x)/(d⁻¹*x)^3) := by
  rw [div_eq_mul_inv x d, mul_comm x d⁻¹]
  by_cases hx : x=0
  · simp [hx]
  · field_simp

private lemma dilation_integrable {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun x => divisorContinuousUnitHead (x/d)/x^3) (Ioi 0) := by
  have hc := (integrableOn_Ioi_comp_mul_left_iff
    (fun x => divisorContinuousUnitHead x/x^3) 0 (inv_pos.mpr hd)).mpr
    (by simpa using integrable_divisorContinuousUnitHead_moment)
  apply (hc.const_mul (d^3)⁻¹).congr
  filter_upwards with x
  exact (dilation_integrand d x hd.ne').symm

private lemma dilation_integral {d : ℝ} (hd : 0<d) :
    (∫ x in Ioi (0:ℝ), divisorContinuousUnitHead (x/d)/x^3) =
      (d^2)⁻¹ * ∫ x in Ioi (0:ℝ), divisorContinuousUnitHead x/x^3 := by
  simp_rw [dilation_integrand d _ hd.ne']
  rw [integral_const_mul, integral_comp_mul_left_Ioi (fun x => divisorContinuousUnitHead x/x^3) 0 (inv_pos.mpr hd), mul_zero,
    inv_inv, smul_eq_mul]
  field_simp

/-- The complete signed head has an absolutely convergent inverse-cube moment. -/
theorem integrable_mobiusDivisorContinuousHead_moment (P : Finset ℕ) :
    IntegrableOn (fun x => mobiusDivisorContinuousHead P x/x^3) (Ioi 0) := by
  simp only [mobiusDivisorContinuousHead, sum_div, mul_div_assoc]
  exact integrable_finsetSum _ (fun d hd =>
    (dilation_integrable (by exact_mod_cast Nat.pos_of_mem_divisors hd)).const_mul _)

private def momentMobiusAF : ArithmeticFunction ℝ :=
  ⟨fun n => ((ArithmeticFunction.moebius n : ℤ):ℝ)*Real.sqrt n/(n:ℝ)^2, by simp⟩

private lemma momentMobiusAF_mult : momentMobiusAF.IsMultiplicative := by
  constructor
  · simp [momentMobiusAF]
  · intro m n hmn
    simp only [momentMobiusAF, ArithmeticFunction.coe_mk,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      Int.cast_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), mul_pow]
    ring

private lemma moment_euler (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    (∑ d ∈ (∏p∈P,p).divisors,
      ((ArithmeticFunction.moebius d : ℤ):ℝ)*Real.sqrt d/(d:ℝ)^2) =
      ∏p∈P, (1-Real.sqrt p/(p:ℝ)^2) := by
  have h := (momentMobiusAF_mult.mul (ArithmeticFunction.isMultiplicative_zeta.natCast
    (R := ℝ))).map_prod_of_prime P hP
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  change (∑d∈(∏p∈P,p).divisors, momentMobiusAF d) = _
  rw [h]
  apply prod_congr rfl
  intro p hp
  rw [(hP p hp).divisors]
  rw [Finset.sum_pair (Ne.symm (hP p hp).ne_one)]
  simp [momentMobiusAF, ArithmeticFunction.moebius_apply_prime (hP p hp)]
  ring

/-- Exact positive Euler factorization of the full signed source moment. -/
theorem integral_mobiusDivisorContinuousHead_moment (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    (∫ x in Ioi (0:ℝ), mobiusDivisorContinuousHead P x/x^3) =
      (∏p∈P, (1-Real.sqrt p/(p:ℝ)^2)) *
        ∫ x in Ioi (0:ℝ), divisorContinuousUnitHead x/x^3 := by
  simp only [mobiusDivisorContinuousHead, sum_div, mul_div_assoc]
  rw [integral_finsetSum _ (fun d hd =>
    (dilation_integrable (by exact_mod_cast Nat.pos_of_mem_divisors hd)).const_mul _)]
  simp_rw [integral_const_mul]
  calc
    _ = ∑ d ∈ (∏ p∈P,p).divisors,
        (((ArithmeticFunction.moebius d : ℤ):ℝ)*Real.sqrt d/(d:ℝ)^2) *
          ∫ x in Ioi (0:ℝ), divisorContinuousUnitHead x/x^3 := by
      apply sum_congr rfl
      intro d hd
      rw [dilation_integral (by exact_mod_cast Nat.pos_of_mem_divisors hd)]
      ring
    _ = _ := by rw [← sum_mul, moment_euler P hP]

private lemma moment_weight_rpow (n : ℕ) :
    Real.sqrt n/(n:ℝ)^2 = (n:ℝ)^(-3/2:ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (n:ℝ) 2, ← Real.rpow_sub hnR]
  norm_num

private lemma prime_moment_weight_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.sqrt p/(p:ℝ)^2 ∧ Real.sqrt p/(p:ℝ)^2 ≤ 1/2 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hs := Real.sq_sqrt (Nat.cast_nonneg p)
  have hs0 := Real.sqrt_nonneg (p:ℝ)
  constructor
  · positivity
  · rw [div_le_iff₀ (pow_pos (by linarith : (0:ℝ)<p) 2)]
    nlinarith [sq_nonneg ((p:ℝ)-1)]

/-- The Euler factors of the actual moment have a uniform positive lower bound,
independent of the finite prime core. -/
theorem mobiusDivisor_moment_euler_lower (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    Real.exp (-2 * ∑' n : ℕ, (n:ℝ)^(-3/2:ℝ)) ≤
      ∏p∈P, (1-Real.sqrt p/(p:ℝ)^2) := by
  have hp (p : ℕ) (hpP : p∈P) : 0<1-Real.sqrt p/(p:ℝ)^2 := by
    have := (prime_moment_weight_bounds (hP p hpP)).2
    linarith
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-3/2:ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hsum := hs.sum_le_tsum P (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hlog : -2 * ∑' n : ℕ, (n:ℝ)^(-3/2:ℝ) ≤
      Real.log (∏p∈P, (1-Real.sqrt p/(p:ℝ)^2)) := by
    rw [Real.log_prod (fun p hpP => (hp p hpP).ne')]
    calc
      _ ≤ ∑p∈P, -2*(Real.sqrt p/(p:ℝ)^2) := by
        simp_rw [moment_weight_rpow]
        rw [← mul_sum]
        linarith
      _ ≤ _ := by
        apply sum_le_sum
        intro p hpP
        obtain ⟨hu0,hu⟩ := prime_moment_weight_bounds (hP p hpP)
        have hl := neg_log_one_sub_le hu0 hu
        nlinarith
  have he := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (prod_pos hp)] at he

/-- Finite prime processing preserves a fixed strictly positive signed moment. -/
theorem integral_mobiusDivisorContinuousHead_moment_uniform_lower
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    Real.exp (-2 * ∑' n : ℕ, (n:ℝ)^(-3/2:ℝ)) *
        (∫ x in Ioi (0:ℝ), divisorContinuousUnitHead x/x^3) ≤
      ∫ x in Ioi (0:ℝ), mobiusDivisorContinuousHead P x/x^3 := by
  rw [integral_mobiusDivisorContinuousHead_moment P hP]
  exact mul_le_mul_of_nonneg_right (mobiusDivisor_moment_euler_lower P hP)
    integral_divisorContinuousUnitHead_moment_pos.le

/-- Every finite processed core has a strictly positive actual signed moment. -/
theorem integral_mobiusDivisorContinuousHead_moment_pos
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    0 < ∫ x in Ioi (0:ℝ), mobiusDivisorContinuousHead P x/x^3 :=
  (mul_pos (Real.exp_pos _) integral_divisorContinuousUnitHead_moment_pos).trans_le
    (integral_mobiusDivisorContinuousHead_moment_uniform_lower P hP)

/-- The complete signed profile has no source mass at or below one. -/
theorem mobiusDivisorContinuousHead_eq_zero (P : Finset ℕ) {x : ℝ} (hx : x≤1) :
    mobiusDivisorContinuousHead P x=0 := by
  apply sum_eq_zero
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdR : (0:ℝ)<d := by exact_mod_cast hd0
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd0
  rw [divisorContinuousUnitHead_eq_zero ((div_le_one hdR).mpr (hx.trans hd1)), mul_zero]

/-- The positive-ray moment equals the intended moment from one to infinity. -/
theorem integral_mobiusDivisorContinuousHead_moment_Ioi_one (P : Finset ℕ) :
    (∫ x in Ioi (1:ℝ), mobiusDivisorContinuousHead P x/x^3) =
      ∫ x in Ioi (0:ℝ), mobiusDivisorContinuousHead P x/x^3 := by
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  intro x hx
  have hx1 : x≤1 := le_of_not_gt hx.2
  rw [mobiusDivisorContinuousHead_eq_zero P hx1, zero_div]

end RHTower
