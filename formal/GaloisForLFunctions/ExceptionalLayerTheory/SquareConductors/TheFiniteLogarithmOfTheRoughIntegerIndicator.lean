import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OppositePrimeTriplesAtTheCubeRootOfTheMidpoint

/-!
# The finite convolution logarithm on rough integers

The derivative of a convolution power counts the possible marked factors.
Binomial inversion leaves a remainder with one rough Mangoldt index and
one nonunit rough index per truncation step. Their product gives the exact
cutoff through which the complete rows recover the prime-power price.
-/

noncomputable section
open ArithmeticFunction Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem rough_power_derivative (Y j : ℕ) :
    logPriceOf (cubicRoughIndicator Y^j) =
      (j:ℝ) • (cubicRoughMangoldt Y*cubicRoughIndicator Y^j) := by
  induction j with
  | zero =>
    rw [pow_zero,Nat.cast_zero,zero_smul]
    ext k
    change (1:ArithmeticFunction ℝ) k*Real.log k=0
    rw [one_apply]
    split_ifs with h
    · simp [h]
    · exact zero_mul _
  | succ j ih =>
    rw [pow_succ,log_price_leibniz,ih,rough_log_price,pow_succ]
    simp only [Algebra.smul_def,Nat.cast_succ,map_add,map_one]
    ring

/-- Coefficient of the (j+1)-fold complete row of a logarithm truncated at L. -/
def roughLogarithmCoefficient (L j : ℕ) : ℝ :=
  (-1:ℝ)^j*L.choose (j+1)/((j:ℝ)+1)

private theorem complete_rough_rows (Y L : ℕ) :
    cubicRoughMangoldt Y-cubicRoughMangoldt Y*(1-cubicRoughIndicator Y)^L=
      ∑ j ∈ range L,roughLogarithmCoefficient L j • logPriceOf (cubicRoughIndicator Y^(j+1)) := by
  let R := cubicRoughIndicator Y
  let A := cubicRoughMangoldt Y
  have hbin : (1-R)^L=1+∑ j ∈ range L,(-R)^(j+1)*(L.choose (j+1):ℕ) := by
    rw [show 1-R= -R+1 by ring,add_pow,sum_range_succ']
    simp only [pow_zero,one_pow,mul_one,Nat.choose_zero_right,Nat.cast_one]
    abel
  change A-A*(1-R)^L=_
  rw [hbin,mul_add,mul_one,mul_sum,show A-(A+∑ j ∈ range L,A*((-R)^(j+1)*(L.choose (j+1):ℕ)))=
    -(∑ j ∈ range L,A*((-R)^(j+1)*(L.choose (j+1):ℕ))) by abel,←sum_neg_distrib]
  apply sum_congr rfl
  intro j _
  rw [rough_power_derivative,smul_smul]
  have hc : roughLogarithmCoefficient L j*((j+1:ℕ):ℝ)=(-1:ℝ)^j*L.choose (j+1) := by
    rw [roughLogarithmCoefficient,Nat.cast_succ,div_mul_cancel₀ _ (by positivity)]
  rw [hc,Algebra.smul_def]
  simp only [map_mul,map_pow,map_neg,map_one,map_natCast]
  change -(A*((-R)^(j+1)*(L.choose (j+1):ℕ)))=
    ((-1:ArithmeticFunction ℝ)^j*(L.choose (j+1):ℕ))*(A*R^(j+1))
  rw [show -R=(-1:ArithmeticFunction ℝ)*R by ring,mul_pow,pow_succ (-1:ArithmeticFunction ℝ)]
  ring

private theorem convolution_zero_below {a b : ℕ} {f g : ArithmeticFunction ℝ}
    (hf : ∀ i<a, f i=0) (hg : ∀ i<b, g i=0) {k : ℕ} (hk : k<a*b) : (f*g) k=0 := by
  rw [mul_apply]
  apply sum_eq_zero
  intro x hx
  by_cases hl : x.1 < a
  · rw [hf _ hl,zero_mul]
  · have hr : x.2 < b := by
      by_contra! h
      exact hk.not_ge ((Nat.mul_le_mul (le_of_not_gt hl) h).trans_eq (Nat.mem_divisorsAntidiagonal.mp hx).1)
    rw [hg _ hr,mul_zero]

private theorem rough_logarithm_remainder {Y L k : ℕ} (hk : k<(Y+1)^(L+1)) :
    (cubicRoughMangoldt Y*(1-cubicRoughIndicator Y)^L : ArithmeticFunction ℝ) k=0 := by
  have hR (j : ℕ) : ∀ i<(Y+1)^j,((1-cubicRoughIndicator Y)^j : ArithmeticFunction ℝ) i=0 := by
    induction j with
    | zero =>
      intro i hi
      rw [pow_zero] at hi ⊢
      exact one_apply_ne (by omega)
    | succ j ih =>
      intro i hi
      rw [pow_succ] at hi ⊢
      apply convolution_zero_below ih _ hi
      intro q hq
      have hz : (cubicRoughIndicator Y-1) q=0 := by
        by_contra hn
        have := cubic_nonunit_index (Or.inl hn)
        omega
      change (cubicRoughIndicator Y) q-(1:ArithmeticFunction ℝ) q=0 at hz
      change (1:ArithmeticFunction ℝ) q-(cubicRoughIndicator Y) q=0
      linarith
  rw [pow_succ,mul_comm] at hk
  apply convolution_zero_below _ (hR L) hk
  intro q hq
  by_contra hn
  have := cubic_nonunit_index (Or.inr hn)
  omega

/-- Up to the next possible product of nonunit rough factors the finite
logarithm is exactly the Mangoldt price on powers of primes above the cut. -/
theorem finite_rough_logarithm {Y L k : ℕ} (hk : k<(Y+1)^(L+1)) :
    cubicRoughMangoldt Y k=
      ∑ j ∈ range L,roughLogarithmCoefficient L j*(cubicRoughIndicator Y^(j+1) : ArithmeticFunction ℝ) k*
        Real.log k := by
  let ev : ArithmeticFunction ℝ →+ ℝ := ⟨⟨fun f => f k,rfl⟩,fun _ _ => rfl⟩
  have he := congrArg ev (complete_rough_rows Y L)
  rw [map_sub,map_sum] at he
  change cubicRoughMangoldt Y k-(cubicRoughMangoldt Y*(1-cubicRoughIndicator Y)^L : ArithmeticFunction ℝ) k=
    ∑ j ∈ range L,ev (roughLogarithmCoefficient L j • logPriceOf (cubicRoughIndicator Y^(j+1))) at he
  rw [rough_logarithm_remainder hk,sub_zero] at he
  exact he.trans (sum_congr rfl fun j _ => by
    change _*((cubicRoughIndicator Y^(j+1) : ArithmeticFunction ℝ) k*Real.log k)=_
    ring)

#print axioms finite_rough_logarithm

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
