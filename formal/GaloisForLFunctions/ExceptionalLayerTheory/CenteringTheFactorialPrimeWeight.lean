import GaloisForLFunctions.ExceptionalLayerTheory.AFactorialCorrectionForTheSquareRootDensity

/-!
# Centering the factorial prime weight

A parity correction beyond the last square-root quotient cell cancels the
constant term. Every divisor test in the resulting prime sum is a centered
reciprocal fractional part, and the total coefficient mass stays linear.
-/

noncomputable section

open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The centered fractional part of the reciprocal with product denominator. -/
def centeredQuotient (X p d : ℕ) : ℝ := Int.fract (((X : ℝ)/d)/p) - 1/2

/-- The centered part of a parity correction applied to a divisor test function. -/
def parityFunctional (a : ℕ) (f : ℕ → ℝ) : ℝ :=
  (-f a+2*f (2*a)) - 64*(-f (64*a)+2*f (2*(64*a)))

private theorem cast_quotient (X p d : ℕ) :
    ((X/p/d : ℕ) : ℝ) = ((X : ℝ)/p)/d - centeredQuotient X p d - 1/2 := by
  rw [Nat.div_div_eq_div_mul,RHTower.natDiv_eq_sub_sawtooth]
  simp only [RHTower.reciprocalSawtooth,centeredQuotient,Nat.cast_mul,← div_div]
  rw [div_right_comm (X : ℝ) p d]
  ring

private theorem correction_centered (a X p : ℕ) :
    parityCorrection a (X/p) = -(63/2)+parityFunctional a (centeredQuotient X p) := by
  simp only [parityCorrection_floors,cast_quotient,parityFunctional,Nat.cast_mul,Nat.cast_ofNat]
  ring

/-- The constant term in the centered fractional-part expansion. -/
def primeWeightMean (R : ℕ) : ℝ := 1+stencil R (fun _ => 1/2)+63/2*momentRatio R

/-- A parity correction supported above the last square-root cell cancels
the constant term without changing any of those cells. -/
def centeredPrimeWeight (R j : ℕ) : ℝ :=
  primeWeight R j+(2/63)*primeWeightMean R*parityCorrection (128*R^2+1) j

theorem centered_weight_moment {R : ℕ} (hR : 1 ≤ R) :
    squareMoment (128*R^2) (centeredPrimeWeight R) = 0 := by
  rw [← primeWeight_moment hR]
  apply sum_congr rfl
  intro j hj
  have hj' := (mem_Ico.mp hj).2
  simp [centeredPrimeWeight,parityCorrection_small hj']

/-- Pairing against an ordinary prime block uses only centered reciprocal
fractional parts at divisors up to 128 times the first exterior cell. -/
theorem centeredPrimeWeight_expansion {R : ℕ} (hR : 1 ≤ R) (X p : ℕ) :
    centeredPrimeWeight R (X/p) =
      stencil R (centeredQuotient X p) -
      momentRatio R*parityFunctional R (centeredQuotient X p) +
      (2/63)*primeWeightMean R*parityFunctional (128*R^2+1) (centeredQuotient X p) := by
  have hB : factorialPrefix R (X/p) =
      -stencil R (centeredQuotient X p)-stencil R (fun _ => 1/2) := by
    simp only [factorialPrefix,cast_quotient,stencil_sub,stencil_linear_quotient hR,zero_sub]
  rw [centeredPrimeWeight,primeWeight,hB,correction_centered,correction_centered]
  unfold primeWeightMean
  ring

/-- The centering coefficient grows at most linearly with the stencil mass. -/
theorem mean_bound {R : ℕ} (hR : 1 ≤ R) : |primeWeightMean R| ≤ 34*(1+mass R) := by
  have hm := abs_stencil_le hR (fun _ => (1/2 : ℝ)) (fun _ _ => (by norm_num : |(1/2 : ℝ)| ≤ 1/2))
  have hh := ratio_bound hR
  have hM := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  unfold primeWeightMean
  apply (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [abs_one,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 63/2)]
  linarith only [hh,hm,hM]

/-- Only divisors between a parity scale and its 128-fold dilation enter. -/
theorem parityFunctional_bound {R : ℕ} {f : ℕ → ℝ} {M : ℝ}
    (hf : ∀ d ∈ Icc R (128*R), |f d| ≤ M) : |parityFunctional R f| ≤ 195*M := by
  have hb (a : ℕ) (ha : R ≤ a) (ha' : 2*a ≤ 128*R) :
      |-f a+2*f (2*a)| ≤ 3*M := by
    apply (abs_add_le _ _).trans
    rw [abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hf a (mem_Icc.mpr ⟨ha,by omega⟩),hf (2*a) (mem_Icc.mpr ⟨by omega,ha'⟩)]
  unfold parityFunctional
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 64)]
  linarith only [hb R le_rfl (by omega),hb (64*R) (by omega) (by omega)]

/-- Taking a finite weighted sum commutes with the parity divisor test. -/
theorem commute_functional {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (f : ι → ℕ → ℝ) (a : ℕ) :
    ∑ i ∈ s, z i*parityFunctional a (f i) =
    parityFunctional a (fun d => ∑ i ∈ s, z i*f i d) := by
  simp only [parityFunctional,mul_sub,mul_add,mul_neg,sum_sub_distrib,sum_add_distrib,
    sum_neg_distrib,mul_left_comm (z _) (2 : ℝ),mul_left_comm (z _) (64 : ℝ),mul_sum]

/-- A bound for all centered reciprocal divisor tests on a block transfers
with linear loss in the factorial cutoff. -/
theorem abs_centered_block {R : ℕ} (hR : 1 ≤ R) (X : ℕ) (S : Finset ℕ) (z : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ d ∈ Icc 1 (128*(128*R^2+1)), |∑ p ∈ S, z p*centeredQuotient X p d| ≤ M) :
    |∑ p ∈ S, z p*centeredPrimeWeight R (X/p)| ≤ 1000*(1+mass R)*M := by
  let F (d : ℕ) := ∑ p ∈ S, z p*centeredQuotient X p d
  have hR' : 128*R ≤ 128*R^2 := Nat.mul_le_mul_left _ (by simpa [sq] using Nat.mul_le_mul_left R hR)
  have ha := abs_stencil_le hR F fun d hd => hs d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,
    by have := (mem_Icc.mp hd).2; omega⟩)
  have hb := parityFunctional_bound (R := R) (f := F) fun d hd => hs d (mem_Icc.mpr ⟨hR.trans (mem_Icc.mp hd).1,
    by have := (mem_Icc.mp hd).2; omega⟩)
  have hc := parityFunctional_bound (R := 128*R^2+1) (f := F) fun d hd =>
    hs d (mem_Icc.mpr ⟨by have := (mem_Icc.mp hd).1; omega,(mem_Icc.mp hd).2⟩)
  have hid : (∑ p ∈ S, z p*centeredPrimeWeight R (X/p)) = stencil R F -
      momentRatio R * parityFunctional R F + (2/63)*primeWeightMean R*parityFunctional (128*R^2+1) F := by
    simp only [centeredPrimeWeight_expansion hR,mul_sub,mul_add,sum_add_distrib,sum_sub_distrib,
      mul_left_comm (z _) (momentRatio R),mul_left_comm (z _) ((2/63)*primeWeightMean R),
      ← mul_sum,stencil_weighted_sum,commute_functional,F]
  rw [hid]
  apply (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) le_rfl).trans ?_)
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/63)]
  have hmass := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hcoeff : 0 ≤ 1+mass R := by linarith
  have hb' := mul_le_mul (ratio_bound hR) hb (abs_nonneg _) hcoeff
  have hc' := mul_le_mul (mul_le_mul_of_nonneg_left (mean_bound hR) (by norm_num : (0 : ℝ) ≤ 2/63))
    hc (abs_nonneg _) (by positivity)
  linarith only [ha,hb',hc',mul_nonneg hmass hM,hM]

theorem centeredPrimeWeight_small {R j : ℕ} (hj : 1 ≤ j) (hlt : j < R) :
    centeredPrimeWeight R j = 0 := by
  have hR : 1 ≤ R := by omega
  have hJ : 128*R ≤ 128*R^2 := Nat.mul_le_mul_left _ (by simpa [sq] using Nat.mul_le_mul_left R hR)
  simp [centeredPrimeWeight,primeWeight_small hj hlt,parityCorrection_small (show j < 128*R^2+1 by omega)]

theorem centeredPrimeWeight_uniform : ∃ F : ℝ, 0 ≤ F ∧ ∀ {R : ℕ}, 1 ≤ R → ∀ j : ℕ,
    |centeredPrimeWeight R j| ≤ F*(R : ℝ) := by
  obtain ⟨C,hC,h⟩ := mass_uniform
  refine ⟨200*(1+C),by positivity,?_⟩
  intro R hR j
  have h1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  let a := 128*R^2+1
  have hg := parityCorrection_bound a j
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hrat : |(2/63)*primeWeightMean R| ≤ (2/63)*(34*(1+mass R)) := by
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/63)]
    exact mul_le_mul_of_nonneg_left (mean_bound hR) (by norm_num)
  have hc := mul_le_mul hrat hg (abs_nonneg _) (by positivity)
  unfold centeredPrimeWeight
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  change |primeWeight R j| + |(2/63)*primeWeightMean R| * |parityCorrection a j| ≤ _
  linarith only [primeWeight_bound hR j,hc,h R hR,h1,hm]

/-- Adding the exterior parity correction leaves the factorial pairing
within a logarithmic error per unit of coefficient mass. -/
theorem centeredPrimeWeight_factorial {R X : ℕ} (hR : 1 ≤ R) (hX : 1 ≤ X) :
    |(Chebyshev.psi X-X)-∑ m ∈ Icc 1 X, vonMangoldt m*centeredPrimeWeight R (X/m)| ≤
        420*(1+mass R)*(3+Real.log (128*(128*R^2+1) : ℕ)+2*Real.log X) := by
  let a := 128*R^2+1
  have hJ : 128*R ≤ 128*R^2 := Nat.mul_le_mul_left _ (by simpa [sq] using Nat.mul_le_mul_left R hR)
  have hl : Real.log (128*R : ℕ) ≤ Real.log (128*a : ℕ) := Real.log_le_log
    (by exact_mod_cast (show 0 < 128*R by omega)) (by exact_mod_cast (show 128*R ≤ 128*a by dsimp [a]; omega))
  let scale := 3+Real.log (128*a : ℕ)+2*Real.log X
  have hL : 0 ≤ scale := by dsimp [scale]; have := Real.log_natCast_nonneg (128*a); have := Real.log_natCast_nonneg X; positivity
  have hM := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hM0 : 0 ≤ 1+mass R := by linarith
  have hf := (primeWeight_factorial hR hX).trans (mul_le_mul_of_nonneg_left
    (show 3+Real.log (128*R : ℕ)+2*Real.log X ≤ scale by dsimp [scale]; linarith only [hl]) (by positivity))
  have hratio : |(2/63)*primeWeightMean R| ≤ (2/63)*(34*(1+mass R)) := by
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/63)]
    exact mul_le_mul_of_nonneg_left (mean_bound hR) (by norm_num)
  have hg := mul_le_mul hratio (correction_pair (R := a) (by dsimp [a]; omega) hX) (abs_nonneg _) (by positivity)
  have hid : (Chebyshev.psi X-X)-∑ m ∈ Icc 1 X, vonMangoldt m*centeredPrimeWeight R (X/m) =
    ((Chebyshev.psi X-X)-∑ m ∈ Icc 1 X, vonMangoldt m*primeWeight R (X/m)) -
      ((2/63)*primeWeightMean R)*(∑ m ∈ Icc 1 X, vonMangoldt m*parityCorrection a (X/m)) := by
    simp only [centeredPrimeWeight,a,mul_add,sum_add_distrib,
      mul_left_comm (vonMangoldt _) ((2/63)*primeWeightMean R),← mul_sum]; ring
  rw [hid]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  change _ ≤ 420*(1+mass R)*scale
  change _ ≤ (2/63)*(34*(1+mass R))*(195*scale) at hg
  linarith only [hf,hg,mul_nonneg hM0 hL]

/-- The absolute cost of a bounded prime-weighted block follows from its
Chebyshev mass. -/
theorem centered_prime_absolute_bound {F : ℝ} {R X L U : ℕ} (hR : 1 ≤ R)
    (hF : ∀ {R : ℕ}, 1 ≤ R → ∀ j, |centeredPrimeWeight R j| ≤ F*(R : ℝ)) (hL : 1 ≤ L) :
    |∑ p ∈ (Ico L U).filter Nat.Prime, Real.log p*centeredPrimeWeight R (X/p)| ≤ (F*R)*(7*U) := by
  have hFR := (abs_nonneg _).trans (hF hR 0)
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ (Ico L U).filter Nat.Prime, (F*R)*vonMangoldt p := by
      apply sum_le_sum
      intro p hp
      rw [abs_mul,abs_of_nonneg (Real.log_natCast_nonneg _),vonMangoldt_apply_prime (mem_filter.mp hp).2,
        mul_comm (F*R)]
      exact mul_le_mul_of_nonneg_left (hF hR _) (Real.log_natCast_nonneg _)
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ hFR
      apply le_trans _ (RHTower.chebyshevPsi_le_seven U)
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hl,hu⟩ := mem_Ico.mp (mem_filter.mp hp).1
        exact mem_Icc.mpr ⟨hL.trans hl,hu.le⟩
      · exact fun _ _ _ => vonMangoldt_nonneg

#print axioms centeredPrimeWeight_factorial

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
