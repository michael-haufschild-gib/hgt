import GaloisForLFunctions.SignedArithmeticCorrespondences.TheSharpWeightTestOnOneConductor
import GaloisForLFunctions.ZeroConfigurationGeometry.VonMangoldtMomentDiagonalsVanish

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

/-- Above one half both the reciprocal power weight and the centered
prime increments divided by that weight have finite square mass. -/
theorem centered_prime_power_prices {s : ℝ} (hs : 1/2 < s) :
    let r := powerConductorWeight s
    (∀ k, 0<r k) ∧ Monotone r ∧ Summable (fun k => (1/r k)^2) ∧
      Summable (fun k => (|Λ k-1| / r k)^2) := by
  intro r
  have hpos (k : ℕ) : 0 < ((max k 1:ℕ):ℝ) :=
    Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le (le_max_right _ _))
  have hr (k : ℕ) : 0<r k := Real.rpow_pos_of_pos (hpos k) s
  have hm : Monotone r := fun k l h => Real.rpow_le_rpow (hpos k).le
    (Nat.cast_le.mpr (max_le_max_right 1 h)) (by linarith only [hs])
  have hσ : 1<2*s := by linarith only [hs]
  let t := fun n : ℕ => (n:ℝ)^(-(2*s))
  have ht : Summable t := Real.summable_nat_rpow.mpr (by linarith only [hσ])
  have hΛ : Summable (fun n : ℕ => (Λ n)^2*t n) :=
    ZeroConfigurationGeometry.summable_vonMangoldt_sq_rpow hσ
  have he (n : ℕ) (hn : 1≤n) : (1/r n)^2=t n := by
    change (1/((max n 1:ℕ):ℝ)^s)^2=(n:ℝ)^(-(2*s))
    rw [max_eq_left hn,one_div,inv_pow,Real.rpow_neg (Nat.cast_nonneg _),
      ← Real.rpow_two ((n:ℝ)^s),← Real.rpow_mul (Nat.cast_nonneg _),mul_comm s 2]
  have hA : Summable (fun k => (1/r k)^2) := by
    apply (summable_nat_add_iff 1).mp
    exact ((summable_nat_add_iff 1).mpr ht).congr fun n => (he _ (Nat.succ_pos n)).symm
  have hB : Summable (fun k => (|Λ k-1| / r k)^2) := by
    apply (summable_nat_add_iff 1).mp
    have hmajor := (summable_nat_add_iff 1).mpr ((hΛ.add ht).mul_left 2)
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hmajor
    intro n
    let k := n+1
    change (|Λ k-1| / r k)^2 ≤ 2*((Λ k)^2*t k+t k)
    rw [show |Λ k-1| / r k=|Λ k-1| * (1/r k) by ring,mul_pow,sq_abs,he k (Nat.succ_pos _)]
    have ht₀ : 0≤t k := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc _ ≤ (2*((Λ k)^2+1))*t k := mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (Λ k+1)]) ht₀
         _ = _ := by ring
  exact ⟨hr,hm,hA,hB⟩

/-- Any exponent above one half controls the signed finite part on all
interleaved signed conductors. The bound uses the centered prime
increments and is independent of the cutoff. -/
theorem signed_finite_part_above_half {s : ℝ} (hs : 1/2 < s) :
    ∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ) (a b : ℕ → ℤ), |interleavedFinitePart N a b| ≤
      C*conductorNorm N (fun i => powerConductorWeight s i*upperDivisor N a i)*
        conductorNorm N (fun i => powerConductorWeight s i*upperDivisor N b i) := by
  let r := powerConductorWeight s
  obtain ⟨hr,hm,hA,hB⟩ := centered_prime_power_prices hs
  let A := Real.sqrt (∑' k, (1/r k)^2)
  let B := Real.sqrt (∑' k, (|Λ k-1| / r k)^2)
  refine ⟨2*A*B+A^2,add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (sq_nonneg _),fun N a b => ?_⟩
  have h₁ : conductorNorm N (fun k => 1/r k) ≤ A :=
    Real.sqrt_le_sqrt (hA.sum_le_tsum _ fun _ _ => sq_nonneg _)
  have h₂ : conductorNorm N (fun k => |Λ k-1| / r k) ≤ B :=
    Real.sqrt_le_sqrt (hB.sum_le_tsum _ fun _ _ => sq_nonneg _)
  apply (interleaved_signed_increment_energy N a b r hr hm).trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by norm_num)) h₂
    (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) h₁ 2)

/-- A lower atom against nonnegative multiplicities at composite ratios
with zero prime weight retains at least half their total mass. The
off-diagonal real monomials have degree at least one at these ratios. -/
theorem signed_test_on_zero_prime_ratios {N : ℕ} (hN : 0<N) (m : ℕ → ℕ)
    (hs : ∀ n ∈ Icc 1 N, m n≠0 → 3≤n ∧ Λ n=0) :
    ∃ a b : ℕ → ℤ, (∀ i ∈ Icc 1 N, upperDivisor N a i=if i=1 then 1 else 0) ∧
      (∀ i ∈ Icc 1 N, upperDivisor N b i=(m i:ℤ)) ∧
      (∑ i ∈ Icc 1 N, (m i:ℝ))/2 ≤ interleavedFinitePart N a b := by
  obtain ⟨a,b,ha,hb,ht,_⟩ := conductor_one_profile hN (fun i => (m i:ℤ))
  let S := Icc 1 N
  let M := ∑ i ∈ S, (m i:ℝ)
  have h₁ : 1∈S := mem_Icc.mpr ⟨le_rfl,hN⟩
  have hm₁ : m 1=0 := by
    by_contra h
    have := (hs 1 h₁ h).1
    omega
  have hp : ∑ k ∈ S, twoSidedMultiple N k a b*(Λ k-1) = -M := by
    dsimp only [M]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    have he := (twoSidedCoefficient_tail N k a b).symm.trans (ht k hk)
    change twoSidedMultiple N k a b=_ at he
    simp only [hm₁,Nat.cast_zero,Int.cast_zero,ite_self,add_zero,Int.cast_natCast] at he
    rw [he]
    by_cases h : m k=0
    · simp [h]
    · rw [(hs k hk h).2]; ring
  have hJ : Continuous (mixedJetSection N a b) := by
    change Continuous (fun x : ℝ => ∑ n ∈ S, ∑ i ∈ S.erase n,
      (upperDivisor N a i:ℝ)*upperDivisor N b n*(x^(max i n-min i n-1)+x^(i+n-1)))
    fun_prop
  have hpoint (x : ℝ) (hx : x∈Set.Icc 0 1) : mixedJetSection N a b x ≤ (M*2)*x := by
    change (∑ n ∈ S, ∑ i ∈ S.erase n, (upperDivisor N a i:ℝ)*upperDivisor N b n*
      (x^(max i n-min i n-1)+x^(i+n-1))) ≤ _
    simp only [M,sum_mul]
    refine sum_le_sum fun n hn => ?_
    rw [hb n hn,Int.cast_natCast]
    by_cases h : m n=0
    · simp [h]
    have hn₃ := (hs n hn h).1
    have hm : 1∈S.erase n := mem_erase.mpr ⟨by omega,h₁⟩
    rw [sum_eq_single_of_mem 1 hm]
    · change (upperDivisor N a 1:ℝ)*(m n:ℝ)*(x^(max 1 n-min 1 n-1)+x^(1+n-1)) ≤ (m n:ℝ)*2*x
      have hu1 : (upperDivisor N a 1:ℝ)=1 := by simp [ha 1 h₁]
      rw [hu1,one_mul]
      have hpow (j : ℕ) (hj : 1≤j) : x^j≤x := by
        simpa only [pow_one] using pow_le_pow_of_le_one hx.1 hx.2 hj
      have h := add_le_add (hpow (max 1 n-min 1 n-1) (by omega))
        (hpow (1+n-1) (by omega))
      calc _ ≤ (m n:ℝ)*(x+x) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
           _ = _ := by ring
    · intro i hi he
      simp [ha i (mem_of_mem_erase hi),he]
  have hi := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hJ.intervalIntegrable 0 1)
    ((continuous_const.mul continuous_id).intervalIntegrable 0 1) hpoint
  change (∫ x in (0:ℝ)..1, mixedJetSection N a b x) ≤ ∫ x in (0:ℝ)..1, (M*2)*x at hi
  rw [intervalIntegral.integral_const_mul,integral_id] at hi
  norm_num at hi
  refine ⟨a,b,ha,hb,?_⟩
  rw [interleaved_centered_prime_sum,hp,neg_neg]
  change M/2≤_
  linarith only [hi]

private theorem zero_prime_weight_on_sixes {k : ℕ} (hk : 6∣k) : Λ k=0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpow
  obtain ⟨p,l,hp,_,he⟩ := (isPrimePow_nat_iff _).mp hpow
  rw [← he] at hk
  have h₂ := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow ((by decide : 2∣6).trans hk))
  have h₃ := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow ((by decide : 3∣6).trans hk))
  omega

/-- Exact power threshold for the signed finite part. A conductor-one
atom against multiples of six detects divergence already at one half. -/
theorem signed_finite_part_power_iff (s : ℝ) :
    (∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ) (a b : ℕ → ℤ), |interleavedFinitePart N a b| ≤
      C*conductorNorm N (fun i => powerConductorWeight s i*upperDivisor N a i)*
        conductorNorm N (fun i => powerConductorWeight s i*upperDivisor N b i)) ↔ 1/2 < s := by
  refine ⟨?_,signed_finite_part_above_half⟩
  rintro ⟨C,hC,h⟩
  let r := powerConductorWeight s
  let w := fun k : ℕ => if 6∣k then (1:ℝ) else 0
  have hr (k : ℕ) : 0<r k := Real.rpow_pos_of_pos
    (Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le (le_max_right _ _))) s
  have hw (k : ℕ) : 0≤w k := by dsimp [w]; split <;> norm_num
  have hprice : Summable (fun k => (w k/r k)^2) := by
    apply dual_price_summable_of_integer_tests r w hr hw (B := 2*C) (mul_nonneg (by norm_num) hC)
    intro N hN m
    let v := fun k => if 6∣k then m k else 0
    have hsix (k : ℕ) (hk : k∈Icc 1 N) (hv : v k≠0) : 3≤k ∧ Λ k=0 := by
      have hd : 6∣k := by
        by_contra hn
        exact hv (if_neg hn)
      have h₆ := Nat.le_of_dvd (mem_Icc.mp hk).1 hd
      exact ⟨by omega,zero_prime_weight_on_sixes hd⟩
    obtain ⟨a,b,ha,hb,hvalue⟩ := signed_test_on_zero_prime_ratios hN v hsix
    have h₁ : 1∈Icc 1 N := mem_Icc.mpr ⟨le_rfl,hN⟩
    have hn : conductorNorm N (fun i => r i*upperDivisor N a i)=1 := by
      rw [conductorNorm,sum_eq_single_of_mem 1 h₁]
      · simp [ha 1 h₁,r,powerConductorWeight]
      · intro i hi he
        simp [ha i hi,he]
    have hnorm : conductorNorm N (fun i => r i*upperDivisor N b i) ≤ conductorNorm N (fun i => r i*m i) := by
      apply Real.sqrt_le_sqrt
      apply sum_le_sum
      intro i hi
      change (r i*(upperDivisor N b i:ℝ))^2 ≤ (r i*(m i:ℝ))^2
      rw [hb i hi,Int.cast_natCast]
      by_cases hd : 6∣i
      · simp [v,hd]
      · simpa only [v,if_neg hd,Nat.cast_zero,mul_zero,zero_pow (by decide : 2≠0)] using
          sq_nonneg (r i*(m i:ℝ))
    have he : (∑ k ∈ Icc 1 N, w k*(m k:ℝ))=∑ k ∈ Icc 1 N, (v k:ℝ) := by
      refine sum_congr rfl fun k _ => ?_
      by_cases hd : 6∣k <;> simp [w,v,hd]
    have hup := (le_abs_self _).trans (h N a b)
    change _ ≤ C*conductorNorm N (fun i => r i*upperDivisor N a i)*
      conductorNorm N (fun i => r i*upperDivisor N b i) at hup
    rw [hn,mul_one] at hup
    have ht := hup.trans (mul_le_mul_of_nonneg_left hnorm hC)
    rw [he]
    linarith only [hvalue,ht]
  by_contra! hl
  let g := fun n : ℕ => 6*(n+1)
  have hg : Function.Injective g := fun n m he =>
    Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left (by decide : 0<6) he)
  have hsub := (hprice.comp_injective hg).mul_left 6
  have hH : Summable (fun n : ℕ => 1/((n+1:ℕ):ℝ)) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hsub
    intro n
    have hn : 1≤g n := by dsimp [g]; omega
    have hh : (r (g n))^2≤(g n:ℝ) := by
      change (((max (g n) 1:ℕ):ℝ)^s)^2≤_
      rw [max_eq_left hn,← Real.rpow_two,← Real.rpow_mul (Nat.cast_nonneg _)]
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (show (1:ℝ)≤g n by exact_mod_cast hn) (show s*2≤1 by linarith only [hl])
    change 1/((n+1:ℕ):ℝ) ≤ 6*(w (g n)/r (g n))^2
    rw [show w (g n)=1 from if_pos (dvd_mul_right _ _),div_pow,one_pow]
    have hnr : (0:ℝ)<((n+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
    rw [mul_one_div,div_le_div_iff₀ hnr (sq_pos_of_pos (hr _)),one_mul]
    simpa only [g,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hfull : Summable (fun n : ℕ => 1/(n:ℝ)) := (summable_nat_add_iff 1).mp hH
  exact (lt_irrefl (1:ℝ)) ((Real.summable_one_div_nat_rpow (p := 1)).mp (by simpa using hfull))

#print axioms signed_finite_part_power_iff
#print axioms signed_test_on_zero_prime_ratios
#print axioms signed_finite_part_above_half
#print axioms interleaved_signed_increment_energy
#print axioms multiple_increment_price
#print axioms quotient_price_by_increments
#print axioms interleaved_centered_prime_sum
end GaloisForLFunctions.SignedArithmeticCorrespondences
