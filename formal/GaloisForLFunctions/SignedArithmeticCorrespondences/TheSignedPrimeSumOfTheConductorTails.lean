import GaloisForLFunctions.SignedArithmeticCorrespondences.SeparateConductorEnergiesOnInterleavingSupports

/-!
# Abel summation on both conductor divisors

A price accumulated from its local increments pairs with the quotient
cells exactly as the increments pair with multiplicative tails. For the
Chebyshev error the increments are the centered von Mangoldt weights.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory _root_.RHTower
open scoped ArithmeticFunction.vonMangoldt

/-- Both directed incidences of the actual conductors at multiplication k. -/
def twoSidedMultiple (N k : ℕ) (a b : ℕ → ℤ) : ℝ :=
  ∑ i ∈ Icc 1 N, ((upperDivisor N a i:ℝ)*upperDivisor N b (k*i) +
    (upperDivisor N b i:ℝ)*upperDivisor N a (k*i))

/-- Discrete summation by parts at arbitrary signed prices. The zero
quotient contributes nothing because its accumulated price is zero. -/
theorem quotient_price_by_increments (N : ℕ) (a b : ℕ → ℤ) (p : ℕ → ℝ) :
    (∑ k ∈ range (N+1), twoSidedCoefficient N a b k*(∑ q ∈ Icc 1 k, p q)) =
      ∑ q ∈ Icc 1 N, twoSidedMultiple N q a b*p q := by
  have hp (k : ℕ) (hk : k∈range (N+1)) : ∑ q ∈ Icc 1 k, p q =
      ∑ q ∈ Icc 1 N, if q≤k then p q else 0 := by
    rw [← sum_filter]
    congr 1
    ext j
    simp only [mem_filter,mem_Icc]
    have := mem_range.mp hk
    omega
  rw [sum_congr rfl (fun k hk => congrArg (fun t => twoSidedCoefficient N a b k*t) (hp k hk))]
  simp only [mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun q _ => ?_
  have hs : (range (N+1)).filter (fun k => q≤k)=Icc q N := by
    ext j
    simp only [mem_filter,mem_range,mem_Icc]
    omega
  rw [← sum_filter,hs,← sum_mul]
  exact congrArg (fun t => t*p q) (twoSidedCoefficient_tail N q a b)

/-- The signed finite part admits a local prime-sum comparison with no
positive quotient variation. The real jet and both fractional boundaries
have the same normalization as in Weil's full form. -/
theorem interleaved_centered_prime_sum (N : ℕ) (a b : ℕ → ℤ) :
    interleavedFinitePart N a b =
      -(∑ q ∈ Icc 1 N, twoSidedMultiple N q a b*(Λ q-1))-
        (∫ x in (0:ℝ)..1, mixedJetSection N a b x)/2 := by
  have he (k : ℕ) : psiRemainder k=∑ q ∈ Icc 1 k, (Λ q-1) := by
    simp [psiRemainder,chebyshevPsi,sum_sub_distrib,Nat.card_Icc]
  simp only [interleaved_finite_part,he,quotient_price_by_increments]

/-- The signed price of every accumulated local increment is controlled
by the dual norm of the increments themselves. Only two directed sums
are needed, one for each orientation of divisibility. -/
theorem multiple_increment_price (N : ℕ) (a b : ℕ → ℤ) (r p : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hm : Monotone r) :
    |∑ k ∈ Icc 1 N, twoSidedMultiple N k a b*p k| ≤
      2*conductorNorm N (fun k => 1/r k)*conductorNorm N (fun k => |p k| / r k)*
        conductorNorm N (fun i => r i*upperDivisor N a i)*
        conductorNorm N (fun i => r i*upperDivisor N b i) := by
  let S := Icc 1 N
  let u := fun i => (upperDivisor N a i:ℝ)
  let v := fun i => (upperDivisor N b i:ℝ)
  let w := fun k => |p k|
  have hout (c : ℕ → ℤ) (j : ℕ) (hj : N<j) : (upperDivisor N c j:ℝ)=0 := by
    have he : upperDivisor N c j=0 :=
      sum_eq_zero fun i hi => if_neg (not_le.mpr ((mem_Icc.mp hi).2.trans_lt hj))
    rw [he,Int.cast_zero]
  have h₁ := directedMultipleVariation_le N 0 r w u v hr hm (fun _ => abs_nonneg _)
    (hout a) (hout b)
  have h₂ := directedMultipleVariation_le N 0 r w v u hr hm (fun _ => abs_nonneg _)
    (hout b) (hout a)
  have ht (k : ℕ) : |twoSidedMultiple N k a b| ≤
      (∑ i ∈ S, |u i| * |v (k*i)|)+(∑ i ∈ S, |v i| * |u (k*i)|) := by
    rw [← sum_add_distrib]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    simpa only [abs_mul] using abs_add_le (u i*v (k*i)) (v i*u (k*i))
  calc _ ≤ ∑ k ∈ S, |twoSidedMultiple N k a b*p k| := abs_sum_le_sum_abs _ _
       _ ≤ directedMultipleVariation N 0 u v w+directedMultipleVariation N 0 v u w := by
         simp only [directedMultipleVariation,Nat.add_zero,← sum_add_distrib]
         refine sum_le_sum fun k _ => ?_
         rw [abs_mul,mul_comm,← mul_add]
         exact mul_le_mul_of_nonneg_left (ht k) (abs_nonneg _)
       _ ≤ _ := add_le_add h₁ h₂
       _ = _ := by ring

/-- Pricing the centered von Mangoldt increments directly gives a
separate-energy estimate for the signed finite part. The two fractional
boundaries and common diagonal are removed in its definition. -/
theorem interleaved_signed_increment_energy (N : ℕ) (a b : ℕ → ℤ) (r : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hm : Monotone r) :
    let A := conductorNorm N (fun k => 1/r k)
    let B := conductorNorm N (fun k => |Λ k-1| / r k)
    |interleavedFinitePart N a b| ≤ (2*A*B+A^2)*
      conductorNorm N (fun i => r i*upperDivisor N a i)*
      conductorNorm N (fun i => r i*upperDivisor N b i) := by
  intro A B
  let U := conductorNorm N (fun i => r i*upperDivisor N a i)
  let V := conductorNorm N (fun i => r i*upperDivisor N b i)
  have hZ : conductorNorm N (fun k => (0:ℝ)/r k)=0 := by simp [conductorNorm]
  have hj := interleaved_joint_separate N a b r (fun _ => 0) hr hm (fun _ => le_rfl)
  simp only [zero_mul,sum_const_zero,zero_add,hZ,mul_zero] at hj
  have hp := multiple_increment_price N a b r (fun k => Λ k-1) hr hm
  have hi := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := mixedJetSection N a b) zero_le_one
  rw [interleaved_centered_prime_sum,sub_eq_add_neg]
  calc _ ≤ _ := abs_add_le _ _
       _ ≤ 2*A*B*U*V+A^2*U*V := by
         rw [abs_neg,abs_neg,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
         exact add_le_add hp ((div_le_div_of_nonneg_right hi (by norm_num)).trans hj)
       _ = _ := by ring

#print axioms interleaved_signed_increment_energy
#print axioms multiple_increment_price
#print axioms quotient_price_by_increments
#print axioms interleaved_centered_prime_sum
end GaloisForLFunctions.SignedArithmeticCorrespondences
