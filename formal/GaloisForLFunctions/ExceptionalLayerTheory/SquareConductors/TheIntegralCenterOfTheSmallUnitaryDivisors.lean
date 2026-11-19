import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFactorialCenterOfTheSmallUnitaryDivisors
import GaloisForLFunctions.RHTower.Sieve.DivisorBound

/-!
# The integral center at the square cutoff

The lattice point on the square boundary contributes zero in each
primitive unitary row. The continuous center can therefore start at
the square itself, with just two endpoint errors per divisor progression.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def primitiveThrough (e n T : ℕ) : ℝ :=
  ∑ j ∈ (Icc 1 (T/e)).filter ((e*n).Coprime ·),Real.log (e*j:ℕ)

/-- Primitive log density integrated through an endpoint. -/
def unitaryRowIntegral (e n T : ℕ) : ℝ :=
  ((T:ℝ)*(Real.log T-1))*(e*n).totient/((e:ℝ)*(e*n:ℕ))

private theorem primitive_log_window (e n : ℕ) {a b : ℕ} (h : a ≤ b) :
    (∑ j ∈ (Ioc (a/e) (b/e)).filter ((e*n).Coprime ·),Real.log (e*j:ℕ))=
      primitiveThrough e n b-primitiveThrough e n a := by
  let f := fun j : ℕ => if (e*n).Coprime j then Real.log (e*j:ℕ) else 0
  have hi (T : ℕ) : Icc 1 T=Ioc 0 T := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  simp only [primitiveThrough,sum_filter,hi]
  exact eq_sub_of_add_eq' (sum_Ioc_consecutive f (Nat.zero_le _) (Nat.div_le_div_right h))

private theorem square_has_zero_price {e : ℕ} (he : 0<e) (n : ℕ) :
    primitiveThrough e n (e^2)=primitiveThrough e n (e^2-1) := by
  apply sub_eq_zero.mp
  rw [←primitive_log_window e n (Nat.sub_le (e^2) 1)]
  apply sum_eq_zero
  intro j hj
  obtain ⟨hI,hcop⟩ := mem_filter.mp hj
  have hlo := (Nat.div_lt_iff_lt_mul he).mp (mem_Ioc.mp hI).1
  have hhi := (Nat.le_div_iff_mul_le he).mp (mem_Ioc.mp hI).2
  have hsq := pow_pos he 2
  have hj' : j=e := by
    apply (mul_right_cancel_iff_of_pos he).mp
    rw [←pow_two]
    omega
  subst j
  have hself := (Nat.coprime_mul_iff_left.mp hcop).1
  change e.gcd e=1 at hself
  rw [Nat.gcd_self] at hself
  simp [hself]

private theorem clipped_unitary_row_error {e n T : ℕ} (he : 0<e) (hn : 0<n) (hT : e^2 ≤ T) :
    |(∑ j ∈ (Ioc ((e^2-1)/e) (T/e)).filter ((e*n).Coprime ·),Real.log (e*j:ℕ))-
      (unitaryRowIntegral e n T-unitaryRowIntegral e n (e^2))| ≤
      ((e*n).divisors.card:ℝ)*(6+8*Real.log T) := by
  rw [primitive_log_window e n ((Nat.sub_le _ _).trans hT),←square_has_zero_price he n]
  have ha := primitive_scaled_log_density he hn (e^2)
  have hb := primitive_scaled_log_density he hn T
  change |primitiveThrough e n (e^2)-unitaryRowIntegral e n (e^2)| ≤ _ at ha
  change |primitiveThrough e n T-unitaryRowIntegral e n T| ≤ _ at hb
  have hlog := Real.log_le_log (Nat.cast_pos.mpr (pow_pos he 2)) ((Nat.cast_le (α:=ℝ)).mpr hT)
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) (e*n).divisors.card)
  rw [abs_le]
  constructor <;> linarith only [(abs_le.mp ha).1,(abs_le.mp ha).2,(abs_le.mp hb).1,(abs_le.mp hb).2,hmul]

/-- Sum of the primitive integral rows, each starting at the square of
its small unitary divisor. -/
def smallUnitaryIntegralCenter (w : ℕ → ℝ) (n T : ℕ) : ℝ :=
  ∑ e ∈ (smallDivisorIndices T).filter (n.Coprime ·),w e.primeFactors.card*
    (unitaryRowIntegral e n T-unitaryRowIntegral e n (e^2))

/-- Exact total cost of replacing the factorial center by the actual
square-clipped integral center, for any weight on the small divisor rank. -/
theorem small_unitary_integral_error (w : ℕ → ℝ) {n : ℕ} (hn : 0<n) (T : ℕ) :
    |(∑ k ∈ (Icc 1 T).filter (n.Coprime ·),(∑ S ∈ smallUnitarySubsets k,w S.card)*Real.log k)-
      smallUnitaryIntegralCenter w n T| ≤ (6+8*Real.log T)*
        ∑ e ∈ (smallDivisorIndices T).filter (n.Coprime ·),|w e.primeFactors.card| * (e*n).divisors.card := by
  rw [small_unitary_factorial_center w hn,smallUnitaryIntegralCenter,←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e he
  have hS := mem_filter.mp (mem_filter.mp he).1
  have he0 := (mem_Icc.mp hS.1).1
  rw [←small_unitary_factorial_row he0 hn hS.2,←mul_sub,abs_mul]
  exact (mul_le_mul_of_nonneg_left (clipped_unitary_row_error he0 hn hS.2)
    (abs_nonneg _)).trans_eq (by ring)

#print axioms small_unitary_integral_error

/-- A prime larger than its nontrivial cofactor drops out of every small
ordinary divisor. The full Möbius sum on the cofactor then vanishes. -/
theorem half_moebius_large_prime {p u : ℕ} (hp : p.Prime) (hu : 1 < u) (hup : u < p) :
    halfMoebius (u*p)=0 := by
  have hu0 := zero_lt_one.trans hu
  have hs : (u*p).divisors.filter (fun e => e^2 ≤ u*p)=u.divisors := by
    ext e
    constructor
    · intro he
      obtain ⟨he,hsq⟩ := mem_filter.mp he
      have hep : e < p := by
        by_contra! hge
        have hi := Nat.mul_le_mul hge hge
        have hlt := Nat.mul_lt_mul_of_pos_right hup hp.pos
        rw [pow_two] at hsq
        omega
      have hc := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_mem_divisors he) hep)
      exact Nat.mem_divisors.mpr ⟨hc.symm.dvd_mul_right.mp (Nat.dvd_of_mem_divisors he),hu0.ne'⟩
    · intro he
      have hd := Nat.dvd_of_mem_divisors he
      have hle := Nat.le_of_dvd hu0 hd
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd.trans (dvd_mul_right _ _),(Nat.mul_pos hu0 hp.pos).ne'⟩,
        (pow_two e).symm ▸ Nat.mul_le_mul hle (hle.trans hup.le)⟩
  rw [halfMoebius,hs]
  have hz := _root_.RHTower.Sieve.sum_divisors_moebius_real u
  rw [if_neg hu.ne'] at hz
  exact_mod_cast hz

/-- At every endpoint through four times the midpoint, replacing the
signed parity weight by its square-clipped integral costs a half power
with an arbitrarily small positive exponent loss. -/
theorem unitary_parity_integral_half_power {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, ∀ {n T : ℕ}, 0<n → 1≤T → T≤4*n →
      |(∑ k ∈ (Icc 1 T).filter (n.Coprime ·),(unitaryHalfWeight k:ℝ)*Real.log k)-
        smallUnitaryIntegralCenter (fun r => (-1:ℝ)^r) n T| ≤ C*(n:ℝ)^(1/2+ε) := by
  let a := ε/3
  let H := _root_.RHTower.Sieve.divisorBoundConst a
  have ha : 0<a := by dsimp only [a]; linarith only [hε]
  have hH : 0≤H := (_root_.RHTower.Sieve.divisorBoundConst_pos ha).le
  refine ⟨(6+8/a)*H*(4:ℝ)^(1/2+ε),?_⟩
  intro n T hn hT hcut
  let X := 4*(n:ℝ)
  let S := (smallDivisorIndices T).filter (n.Coprime ·)
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hX : 1 ≤ X := by dsimp only [X]; linarith only [hn1]
  have hX0 := zero_lt_one.trans_le hX
  have hTX : (T:ℝ) ≤ X := by dsimp only [X]; exact_mod_cast hcut
  have hRX := Real.rpow_nonneg hX0.le a
  have hXa := Real.one_le_rpow hX ha.le
  have he {e : ℕ} (h : e ∈ S) := mem_filter.mp (mem_filter.mp h).1
  have hs : S ⊆ Icc 1 ⌊Real.sqrt X⌋₊ := by
    intro e h
    have hsq : (e:ℝ)^2 ≤ X := (by exact_mod_cast (he h).2 : (e:ℝ)^2 ≤ T).trans hTX
    exact mem_Icc.mpr ⟨(mem_Icc.mp (he h).1).1,Nat.le_floor (by
      simpa only [Real.sqrt_sq (Nat.cast_nonneg e)] using Real.sqrt_le_sqrt hsq)⟩
  have hcard : (S.card:ℝ) ≤ Real.sqrt X := by
    have hc := card_le_card hs
    rw [Nat.card_Icc,Nat.add_one_sub_one] at hc
    exact ((Nat.cast_le (α:=ℝ)).mpr hc).trans (Nat.floor_le (Real.sqrt_nonneg X))
  have hvert (e : ℕ) (h : e ∈ S) :
      ((e*n).divisors.card:ℝ) ≤ H*(X^a*X^a) := by
    have hpos := (mem_Icc.mp (he h).1).1
    have heX := ((Nat.cast_le (α:=ℝ)).mpr (mem_Icc.mp (he h).1).2).trans hTX
    have hnX : (n:ℝ) ≤ X := by dsimp only [X]; linarith only [hn1]
    have hh := _root_.RHTower.Sieve.card_divisors_le_rpow ha (Nat.mul_pos hpos hn).ne'
    rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg e) (Nat.cast_nonneg n)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg e) heX ha.le)
      (Real.rpow_le_rpow (Nat.cast_nonneg n) hnX ha.le) (Real.rpow_nonneg (Nat.cast_nonneg n) _) hRX) hH)
  have hsum := sum_le_sum (s:=S) hvert
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hl1 := Real.log_le_log ((Nat.cast_pos (α:=ℝ)).mpr hT) hTX
  have hl2 := Real.log_le_rpow_div hX0.le ha
  have hl : 6+8*Real.log T ≤ (6+8/a)*X^a := by
    calc 6+8*Real.log T ≤ 6*X^a+8*(X^a/a) := by linarith only [hl1,hl2,hXa]
         _ = _ := by ring
  have hh := small_unitary_integral_error (fun r => (-1:ℝ)^r) hn T
  simp only [abs_pow,abs_neg,abs_one,one_pow,one_mul] at hh
  simp only [unitaryHalfWeight,Int.cast_sum,Int.cast_pow,Int.cast_neg,Int.cast_one]
  apply hh.trans ((mul_le_mul hl hsum' (sum_nonneg fun e _ => Nat.cast_nonneg _) (by positivity)).trans_eq ?_)
  rw [Real.sqrt_eq_rpow]
  calc (6+8/a)*X^a*(X^(1/2:ℝ)*(H*(X^a*X^a))) =
      (6+8/a)*H*((X^(1/2:ℝ)*X^a)*X^a*X^a) := by ring
       _ = _ := by
         rw [←Real.rpow_add hX0,←Real.rpow_add hX0,←Real.rpow_add hX0,
           show 1/2+a+a+a=1/2+ε by dsimp only [a]; ring,
           show X^(1/2+ε)=(4:ℝ)^(1/2+ε)*(n:ℝ)^(1/2+ε) from
             Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]
         ring

#print axioms half_moebius_large_prime
#print axioms unitary_parity_integral_half_power

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
