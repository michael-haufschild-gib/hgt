import GaloisForLFunctions.ExceptionalLayerTheory.FirstMeansOfBoundedQuotientClasses
import GaloisForLFunctions.ExceptionalLayerTheory.UniformTailsOfShortDirichletPolynomials
import GaloisForLFunctions.ArithmeticDefectRigidity.TheRenormalizedCofactorActsOnPowerRowsByZeta

/-!
# Integer density of the last quotient class

The divisor hyperbola cuts the count at its square root. The short row
allows the integer parts to be removed at unit cost, while the transposed
row contains only differences of zero-one prefixes. The resulting density
is the harmonic sum of the jumps.
-/

noncomputable section

open Finset ArithmeticFunction Complex

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev row (q : ℕ) : ℕ → ℂ := fun n => (lastClassCoefficients q n : ℂ)

/-- Harmonic density of the quotient class, obtained by continuing the Dirichlet
series of its jumps to one. -/
def lastClassIntegerDensity (q : ℕ) : ℝ := (HeckeLFunctions.growthCont (row q) 0 1).re

private theorem harmonic_prefix (q J : ℕ) :
    (shortDirichletPrefix (row q) J 1).re =
      ∑ n ∈ Icc 1 J, lastClassCoefficients q n / (n:ℝ) := by
  have hz : LSeries.term (row q) 1 0=0 := by simp [LSeries.term]
  rw [shortDirichletPrefix,HeckeLFunctions.sum_range_succ_eq_sum_Icc hz,
    Complex.re_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn0 := Nat.ne_of_gt (mem_Icc.mp hn).1
  simp only [LSeries.term,if_neg hn0,Complex.cpow_one,row]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_div,Complex.ofReal_re]

private theorem harmonic_error (q : ℕ) (hq : 2≤q) {J : ℕ} (hJ : 1≤J) :
    |lastClassIntegerDensity q - ∑ n ∈ Icc 1 J, lastClassCoefficients q n/(n:ℝ)| ≤ 4/(J:ℝ) := by
  have hrow (x : ℝ) (_hx : 1≤x) : ‖∑ n ∈ Icc 1 ⌊x⌋₊, row q n‖ ≤ 1*x^(0:ℝ) := by
    rw [show (∑ n ∈ Icc 1 ⌊x⌋₊, row q n) = ((∑ n ∈ Icc 1 ⌊x⌋₊, lastClassCoefficients q n : ℝ):ℂ)
        from (ofReal_sum ..).symm,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (lastClassCoefficients_prefix_bounds q hq _).1,Real.rpow_zero,mul_one]
    exact (lastClassCoefficients_prefix_bounds q hq _).2
  have ht := norm_growthCont_sub_shortDirichletPrefix (c := row q) (by simp [row])
    le_rfl zero_le_one hrow (s := 1) (by norm_num) hJ
  rw [← harmonic_prefix,lastClassIntegerDensity,← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans (ht.trans_eq ?_)
  norm_num [Real.rpow_neg_one,div_eq_mul_inv]

private theorem integer_hyperbola (q X : ℕ) :
    lastClassIntegerCount q X =
      (∑ n ∈ Icc 1 X.sqrt, lastClassCoefficients q n*((X/n:ℕ):ℝ)) +
      ∑ k ∈ Icc 1 X.sqrt,
        ((∑ d ∈ Icc 1 (X/k), lastClassCoefficients q d)-∑ d ∈ Icc 1 X.sqrt, lastClassCoefficients q d) := by
  have h := ArithmeticDefectRigidity.sum_mul_partialSum_div_eq_hyperbola (row q) (fun _ => 1) X
  simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,Nat.add_sub_cancel,one_mul] at h
  have hz (n : ℕ) : ∑ k ∈ Icc 1 n, (zeta : ArithmeticFunction ℝ) k = (n:ℝ) := by
    calc
      _ = ∑ _k ∈ Icc 1 n, (1:ℝ) := sum_congr rfl fun k hk => by
        simp [ArithmeticFunction.natCoe_apply,zeta_apply,Nat.ne_of_gt (mem_Icc.mp hk).1]
      _ = _ := by simp
  rw [lastClassIntegerCount,mul_comm (zeta : ArithmeticFunction ℝ),_root_.RHTower.sum_Icc_mul_apply]
  simp_rw [hz]
  apply Complex.ofReal_injective
  push_cast
  simpa only [row] using h

private theorem short_row_rounding (q X J : ℕ) :
    |(∑ d ∈ Icc 1 J, lastClassCoefficients q d*((X/d:ℕ):ℝ)) -
      X*(∑ d ∈ Icc 1 J, lastClassCoefficients q d/(d:ℝ))| ≤ J := by
  rw [mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ Icc 1 J, (1:ℝ) := by
      apply sum_le_sum
      intro d hd
      have hd0 := (mem_Icc.mp hd).1
      have hdR : 0<(d:ℝ) := by exact_mod_cast hd0
      have hl := Nat.cast_div_le (α := ℝ) (m := X) (n := d)
      have hu : (X:ℝ)/d ≤ (X/d:ℕ)+1 := (div_le_iff₀ hdR).mpr (by
        exact_mod_cast ((Nat.div_lt_iff_lt_mul hd0).mp (Nat.lt_succ_self (X/d))).le)
      have ha : |lastClassCoefficients q d|≤1 := by
        change |if d=0 then 0 else (if q∣d+1 then (1:ℝ) else 0)-(if q∣d then 1 else 0)| ≤ 1
        split_ifs <;> norm_num
      rw [show (X:ℝ)*(lastClassCoefficients q d/d)=lastClassCoefficients q d*(X/d) by ring,
        ← mul_sub,abs_mul,abs_of_nonpos (sub_nonpos.mpr hl)]
      exact (mul_le_mul ha (by linarith only [hu]) (by linarith only [hl]) zero_le_one).trans_eq (one_mul 1)
    _ = _ := by simp

/-- The integer-density error is bounded by eighteen square roots uniformly in the width. -/
theorem lastClassIntegerCount_density_error (q X : ℕ) (hq : 2≤q) :
    |lastClassIntegerCount q X - X*lastClassIntegerDensity q| ≤ 18*Real.sqrt X := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [lastClassIntegerCount]
  let J := X.sqrt
  have hJ : 1≤J := Nat.sqrt_pos.mpr hX
  have hJR : 1≤(J:ℝ) := by exact_mod_cast hJ
  have hJ0 : 0<(J:ℝ) := zero_lt_one.trans_le hJR
  have hJX : (J:ℝ)≤Real.sqrt X := (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr (by
    exact_mod_cast (by simpa only [J,pow_two] using Nat.sqrt_le X))
  have ht : |∑ k ∈ Icc 1 J, ((∑ d ∈ Icc 1 (X/k), lastClassCoefficients q d)-
      ∑ d ∈ Icc 1 J, lastClassCoefficients q d)| ≤ J := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _k ∈ Icc 1 J, (1:ℝ) := by
        apply sum_le_sum
        intro k _
        have h₁ := lastClassCoefficients_prefix_bounds q hq (X/k)
        have h₂ := lastClassCoefficients_prefix_bounds q hq J
        rw [abs_le]; constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2]
      _ = _ := by simp
  let H := ∑ d ∈ Icc 1 J, lastClassCoefficients q d/(d:ℝ)
  have hh := harmonic_error q hq hJ
  have hsize : (X:ℝ) ≤ 4*(J:ℝ)^2 := by
    have hu : (X:ℝ) < ((J:ℝ)+1)*((J:ℝ)+1) := by exact_mod_cast Nat.lt_succ_sqrt X
    have hb := mul_self_le_mul_self (by positivity : 0≤(J:ℝ)+1) (by linarith only [hJR] : (J:ℝ)+1≤2*J)
    nlinarith only [hu,hb]
  have htail : |(X:ℝ)*H-X*lastClassIntegerDensity q| ≤ 16*J := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg X),abs_sub_comm H]
    apply (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg X)).trans
    rw [← mul_div_assoc,div_le_iff₀ hJ0]
    nlinarith only [hsize]
  have hc := short_row_rounding q X J
  rw [integer_hyperbola]
  calc
    _ ≤ _ := (abs_sub_le _ ((X:ℝ)*H) _)
    _ ≤ (J+J:ℝ)+16*J := by
      apply add_le_add _ htail
      rw [add_sub_right_comm]
      exact (abs_add_le _ _).trans (add_le_add hc ht)
    _ ≤ _ := by linarith only [hJX]

#print axioms lastClassIntegerCount_density_error

end GaloisForLFunctions.ExceptionalLayerTheory
