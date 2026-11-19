import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFactorialPriceOfDivisibleCofactorRows
import GaloisForLFunctions.RHTower.TruncatedMoebiusResidual

/-!
# Removing a moving initial interval of primitive cofactors

A completed cofactor-divisibility row has a factorial center at the same three
sharp endpoints. Truncated Möbius inversion removes every proper cofactor up
to the cutoff. The unit price records the ordinary prime midpoint.
-/

noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open RHTower (truncMoebiusDivisorSum)
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def allowedPrimes (n Q : ℕ) : Finset ℕ :=
  (Icc 1 (4*n)).filter (fun p => Q < p ∧ p.Prime ∧ ¬p ∣ n)

private def cofactorEndpoint (n Q T v : ℕ) : ℝ :=
  ∑ p ∈ allowedPrimes n Q, if v ≤ T/p then Real.log p else 0

/-- Ordinary prime price for one cofactor. Both intervals are open at the
left, closed at the right, and use the same middle endpoint. -/
def primitiveOrdinaryCofactorRow (n Q v : ℕ) : ℝ :=
  cofactorEndpoint n Q (4*n) v-2*cofactorEndpoint n Q (3*n) v+cofactorEndpoint n Q (2*n) v

private theorem endpoint_multiple_swap {n Q T r : ℕ} (hT : T ≤ 4*n) :
    (∑ v ∈ (Ioc 0 (4*n)).filter (fun v => r ∣ v),cofactorEndpoint n Q T v) =
      ∑ p ∈ allowedPrimes n Q, Real.log p*((T/(p*r):ℕ):ℝ) := by
  simp only [cofactorEndpoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  have hsub : T/p ≤ 4*n := (Nat.div_le_self T p).trans hT
  have hcut : ((Ioc 0 (4*n)).filter (fun v => r ∣ v)).filter (· ≤ T/p) =
      (Ioc 0 (T/p)).filter (fun v => r ∣ v) := by
    ext v
    simp only [mem_filter,mem_Ioc]
    exact ⟨fun h => ⟨⟨h.1.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨⟨h.1.1,h.1.2.trans hsub⟩,h.2⟩,h.1.2⟩⟩
  rw [←sum_filter,hcut,sum_const,Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul,
    Nat.div_div_eq_div_mul,mul_comm]

/-- Swapping actual ordinary prime and cofactor indices recovers the complete
divisible row, even when the divisor moves through the prime cut. -/
theorem price_of_all_cofactor_multiples (n Q : ℕ) {r : ℕ} (hr : 0 < r) :
    (∑ v ∈ (Ioc 0 (4*n)).filter (fun v => r ∣ v),primitiveOrdinaryCofactorRow n Q v) =
      divisibleCofactorPrimePrice n Q r := by
  simp only [primitiveOrdinaryCofactorRow,sum_add_distrib,sum_sub_distrib,←mul_sum]
  rw [endpoint_multiple_swap (by omega),endpoint_multiple_swap (by omega),endpoint_multiple_swap (by omega),
    mul_sum,←sum_sub_distrib,←sum_add_distrib]
  let f (p : ℕ) := Real.log p*midpointFloorWeight n (p*r)
  calc _ = ∑ p ∈ allowedPrimes n Q,f p := by
             exact sum_congr rfl fun p _ => by unfold f midpointFloorWeight; ring
       _ = _ := by
             symm
             apply sum_subset
             · intro p hp
               obtain ⟨hpI,hp⟩ := mem_filter.mp hp
               exact mem_filter.mpr ⟨(Icc_subset_Icc_right (Nat.div_le_self _ _)) hpI,hp⟩
             · intro p hp hnot
               obtain ⟨hpI,hap⟩ := mem_filter.mp hp
               have hcut : 4*n/r < p := lt_of_not_ge (fun h =>
                 hnot (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hpI).1,h⟩,hap⟩))
               have hpr := (Nat.div_lt_iff_lt_mul hr).mp hcut
               have hz (k : ℕ) (hk : k ≤ 4) : k*n/(p*r)=0 :=
                 Nat.div_eq_of_lt ((Nat.mul_le_mul_right n hk).trans_lt hpr)
               simp only [f,midpointFloorWeight,hz 4 (by decide),hz 3 (by decide),hz 2 (by decide),
                 Nat.cast_zero,mul_zero,sub_zero,add_zero]

#print axioms price_of_all_cofactor_multiples

/-- Deterministic factorial center of the signed primitive sum. -/
def primitiveProjectedFactorial (n V : ℕ) : ℝ :=
  ∑ e ∈ Icc 1 V, (μ e:ℝ)*∑ d ∈ n.divisors, (μ d:ℝ)*divisibleCofactorFactorial n (e.lcm d)

/-- Primitive cofactor restrictions and the moving divisor cutoff act on
the same ordinary prime rows. A pair of divisibility tests gives an lcm. -/
theorem primitive_prime_cofactor_projection {n : ℕ} (hn : 0 < n) (Q V : ℕ) :
    (∑ v ∈ (Ioc 0 (4*n)).filter (n.Coprime ·), truncMoebiusDivisorSum V v*
      primitiveOrdinaryCofactorRow n Q v) =
      ∑ e ∈ Icc 1 V, (μ e:ℝ)*∑ d ∈ n.divisors,
        (μ d:ℝ)*divisibleCofactorPrimePrice n Q (e.lcm d) := by
  let f := primitiveOrdinaryCofactorRow n Q
  let U := Ioc 0 (4*n)
  let a (e : ℕ) : ℝ := μ e
  have cell (v : ℕ) :
      (if n.Coprime v then truncMoebiusDivisorSum V v*f v else 0) =
        ∑ e ∈ Icc 1 V, a e*∑ d ∈ n.divisors, a d*(if e.lcm d ∣ v then f v else 0) := by
    have inner (e : ℕ) : a e*(∑ d ∈ n.divisors, a d*(if e.lcm d ∣ v then f v else 0)) =
        (if e ∣ v then a e else 0)*(if n.Coprime v then (1:ℝ) else 0)*f v := by
      rw [reflected_coprime_indicator hn]
      by_cases he : e ∣ v
      · simp only [Nat.lcm_dvd_iff,he,true_and,if_true,mul_assoc,mul_sum,sum_mul]
        exact sum_congr rfl fun d _ => by split_ifs <;> simp [a]
      · simp only [Nat.lcm_dvd_iff,he,false_and,if_false,mul_zero,sum_const_zero,zero_mul]
    simp_rw [inner]
    rw [←sum_mul,←sum_mul,←sum_filter]
    change (if n.Coprime v then _ else _) = truncMoebiusDivisorSum V v*(if n.Coprime v then _ else _)*f v
    split_ifs <;> simp
  rw [sum_filter]
  change (∑ v ∈ U, if n.Coprime v then truncMoebiusDivisorSum V v*f v else 0)=_
  simp only [cell,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  have hl : 0 < e.lcm d := Nat.lcm_pos (mem_Icc.mp he).1 (Nat.pos_of_mem_divisors hd)
  rw [←price_of_all_cofactor_multiples n Q hl,sum_filter,mul_sum,mul_sum]
  exact sum_congr rfl fun _ _ => rfl

#print axioms primitive_prime_cofactor_projection

private theorem unit_endpoint_interval {n Q a b : ℕ} (hn : 0 < n) (ha : n ≤ a)
    (hQ : Q ≤ a) (hab : a ≤ b) (hb : b ≤ 4*n) :
    cofactorEndpoint n Q b 1-cofactorEndpoint n Q a 1 =
      ∑ p ∈ (Ioc a b).filter Nat.Prime,Real.log p := by
  let S := allowedPrimes n Q
  have cut : S.filter (fun p => a < p ∧ p ≤ b)=(Ioc a b).filter Nat.Prime := by
    ext p
    simp only [S,allowedPrimes,mem_filter,mem_Icc,mem_Ioc]
    constructor
    · rintro ⟨⟨_,_,hp,_⟩,hl,hu⟩; exact ⟨⟨hl,hu⟩,hp⟩
    · rintro ⟨⟨hl,hu⟩,hp⟩
      exact ⟨⟨⟨hp.pos,hu.trans hb⟩,hQ.trans_lt hl,hp,Nat.not_dvd_of_pos_of_lt hn (ha.trans_lt hl)⟩,hl,hu⟩
  rw [←cut,sum_filter,cofactorEndpoint,cofactorEndpoint,←sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hp0 := (mem_filter.mp hp).2.2.1.pos
  simp only [Nat.le_div_iff_mul_le hp0,one_mul]
  by_cases h : a < p
  · simp only [h,true_and,not_le.mpr h,if_false,sub_zero]
  · have hpa := le_of_not_gt h
    simp only [h,false_and,if_false,hpa,hpa.trans hab,if_true,sub_self]

/-- The single term omitted in the composite row is the prime midpoint
with negative orientation. -/
theorem prime_cofactor_unit_price {n Q : ℕ} (hn : 0 < n) (hQ : Q ≤ 2*n) :
    primitiveOrdinaryCofactorRow n Q 1= -primeMidpointPrice n := by
  have hleft := unit_endpoint_interval (n:=n) (Q:=Q) (a:=2*n) (b:=3*n) hn (by omega) hQ
    (by omega) (by omega)
  have hright := unit_endpoint_interval (n:=n) (Q:=Q) (a:=3*n) (b:=4*n) hn (by omega)
    (by omega) (by omega) (by omega)
  unfold primitiveOrdinaryCofactorRow primeMidpointPrice
  linarith only [hleft,hright]

#print axioms prime_cofactor_unit_price

private theorem moebius_unit_row (V : ℕ) (hV : 1 ≤ V) :
    truncMoebiusDivisorSum V 1=1 := by
  rw [_root_.RHTower.truncMoebiusDivisorSum_of_le (by decide) hV,if_pos rfl]

/-- Actual prime price on the surviving primitive cofactors, before
subtracting the explicit factorial center. -/
def remainingPrimitivePrimePrice (n Q V : ℕ) : ℝ :=
  ∑ v ∈ (Ioc V (4*n)).filter (n.Coprime ·),
    truncMoebiusDivisorSum V v*primitiveOrdinaryCofactorRow n Q v

private theorem remove_unit_and_small_cofactors {n Q V : ℕ} (hn : 0 < n) (hQ : Q ≤ 2*n)
    (hV : 1 ≤ V) (hcut : V ≤ 4*n) :
    (∑ v ∈ (Ioc 0 (4*n)).filter (n.Coprime ·), truncMoebiusDivisorSum V v*primitiveOrdinaryCofactorRow n Q v) =
      remainingPrimitivePrimePrice n Q V-primeMidpointPrice n := by
  let f (v : ℕ) := if n.Coprime v then truncMoebiusDivisorSum V v*primitiveOrdinaryCofactorRow n Q v else 0
  have first : (∑ v ∈ Ioc 0 V,f v)= -primeMidpointPrice n := by
    rw [sum_eq_single 1]
    · simp only [f,Nat.coprime_one_right,if_true,moebius_unit_row V hV,one_mul,prime_cofactor_unit_price hn hQ]
    · intro v hv hv1
      obtain ⟨hv0,hvV⟩ := mem_Ioc.mp hv
      simp only [f,_root_.RHTower.truncMoebiusDivisorSum_of_le hv0 hvV,if_neg hv1,zero_mul,ite_self]
    · exact fun hx => False.elim (hx (mem_Ioc.mpr ⟨by decide,hV⟩))
  have hs := sum_Ioc_consecutive f (Nat.zero_le V) hcut
  rw [first] at hs
  simp only [sum_filter,remainingPrimitivePrimePrice,sum_filter]
  change (∑ v ∈ Ioc 0 (4*n),f v)=(∑ v ∈ Ioc V (4*n),f v)-_
  linarith only [hs]

/-- The surviving primitive prime rows recover the midpoint at every integer
with one small-factor and proper-power allowance per Möbius divisor pair. -/
theorem remaining_primitive_prime_factorial_bound {n Q V : ℕ} (hn : 0 < n) (hQ : Q ≤ 2*n)
    (hV : 1 ≤ V) (hcut : V ≤ 4*n) :
    |remainingPrimitivePrimePrice n Q V-primitiveProjectedFactorial n V-primeMidpointPrice n| ≤
      V*(squarefreeDivisorMass n*(Chebyshev.psi Q+
        (Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ))+Real.log n)) := by
  let B := Chebyshev.psi Q+(Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ))+Real.log n
  have power (r : ℕ) : Chebyshev.psi (4*n/r:ℕ)-Chebyshev.theta (4*n/r:ℕ) ≤
      Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ) := by
    simp only [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
    exact filter_subset_filter _ (Ioc_subset_Ioc_right (Nat.div_le_self _ _))
  let f (r : ℕ) := divisibleCofactorPrimePrice n Q r-divisibleCofactorFactorial n r
  have hb {r : ℕ} (hr : 0 < r) : |f r| ≤ B :=
    (divisible_cofactor_factorial_error hn hr Q).trans (by dsimp only [B]; linarith only [power r])
  have hproj := primitive_prime_cofactor_projection hn Q V
  rw [remove_unit_and_small_cofactors hn hQ hV hcut] at hproj
  have heq : remainingPrimitivePrimePrice n Q V-primitiveProjectedFactorial n V-primeMidpointPrice n =
      ∑ e ∈ Icc 1 V, (μ e:ℝ)*∑ d ∈ n.divisors,(μ d:ℝ)*f (e.lcm d) := by
    rw [sub_right_comm,hproj,primitiveProjectedFactorial,←sum_sub_distrib]
    apply sum_congr rfl
    intro e _
    rw [←mul_sub,←sum_sub_distrib]
    exact congrArg (fun z : ℝ => (μ e:ℝ)*z)
      (sum_congr rfl fun d _ => (mul_sub (μ d:ℝ) _ _).symm)
  rw [heq]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _ ∈ Icc 1 V, squarefreeDivisorMass n*B := by
             apply sum_le_sum
             intro e he
             have he0 := (mem_Icc.mp he).1
             rw [abs_mul]
             apply (mul_le_of_le_one_left (abs_nonneg _) (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=e))).trans
             apply (abs_sum_le_sum_abs _ _).trans
             rw [squarefreeDivisorMass,sum_mul]
             apply sum_le_sum
             intro d hd
             rw [abs_mul]
             exact mul_le_mul_of_nonneg_left (hb (Nat.lcm_pos he0 (Nat.pos_of_mem_divisors hd))) (abs_nonneg _)
       _ = _ := by simp [Nat.card_Icc,B]

#print axioms remaining_primitive_prime_factorial_bound

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
