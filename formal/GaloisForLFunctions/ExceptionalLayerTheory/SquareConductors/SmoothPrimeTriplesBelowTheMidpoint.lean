import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OppositePrimeTriplesAtTheCubeRootOfTheMidpoint
import GaloisForLFunctions.RHTower.ThetaDivisorBernsteinGauge
import Mathlib.NumberTheory.SmoothNumbers

/-!
# The smooth prime triples below the sharp midpoint

Beyond the divisor cutoff each complementary factor is small. On three
prime factors the only available divisor is the entire product. The local
Möbius polynomial then distinguishes three distinct primes, a repeated
prime and a pure cube.
-/

noncomputable section
open ArithmeticFunction Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem smooth_moebius_value (Y d : ℕ) :
    cubicSmoothMoebius Y d=if d ∈ Nat.smoothNumbers (Y+1) then (moebius d:ℝ) else 0 := by
  change (if d ∣ primorial Y then (moebius d:ℝ) else 0)=_
  by_cases hd : d ∣ primorial Y
  · have hs := Nat.mem_smoothNumbers'.mpr (fun p hp h => Nat.lt_succ_of_le (hp.dvd_primorial_iff.mp (h.trans hd)))
    rw [if_pos hd,if_pos hs]
  · rw [if_neg hd]
    split_ifs with hs
    · by_cases hsf : Squarefree d
      · apply (hd _).elim
        have hpr := Nat.primeFactors_subset_of_mem_smoothNumbers hs
        rw [←Nat.prod_primeFactors_of_squarefree hsf]
        exact prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).dvd_primorial_iff.mpr
            (Nat.le_of_lt_succ (Nat.mem_primesBelow.mp (hpr hp)).1))
      · rw [moebius_eq_zero_of_not_squarefree hsf,Int.cast_zero]
    · rfl

private theorem smooth_convolution_value (Y d : ℕ) :
    (cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d=
      if d ∈ Nat.smoothNumbers (Y+1) then ((moebius:ArithmeticFunction ℝ)^2 : ArithmeticFunction ℝ) d else 0 := by
  simp only [pow_two,mul_apply]
  by_cases hs : d ∈ Nat.smoothNumbers (Y+1)
  · rw [if_pos hs]
    apply sum_congr rfl
    intro x hx
    have hm := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have h1 := Nat.mem_smoothNumbers_of_dvd hs (Dvd.intro x.2 hm)
    have h2 := Nat.mem_smoothNumbers_of_dvd hs (Dvd.intro_left x.1 hm)
    rw [smooth_moebius_value,smooth_moebius_value,if_pos h1,if_pos h2]
    rfl
  · rw [if_neg hs]
    apply sum_eq_zero
    intro x hx
    rw [smooth_moebius_value,smooth_moebius_value]
    by_cases h : x.1 ∈ Nat.smoothNumbers (Y+1)
    · have h' : x.2 ∉ Nat.smoothNumbers (Y+1) := fun hh => hs
        ((Nat.mem_divisorsAntidiagonal.mp hx).1 ▸ Nat.mul_mem_smoothNumbers h hh)
      rw [if_neg h',mul_zero]
    · rw [if_neg h,zero_mul]

/-- Products in either high-divisor row have every prime at or below the
cut, including integers with repeated primes. -/
theorem high_cubic_rows_are_smooth {n Y d r : ℕ} (hr : 0 < r) (hk : d*r ≤ 4*n)
    (hcut : 4*n/(Y+1) < d)
    (hw : cubicSmoothMoebius Y d ≠ 0 ∨ (cubicSmoothMoebius Y^2 : ArithmeticFunction ℝ) d ≠ 0) :
    d*r ∈ Nat.smoothNumbers (Y+1) := by
  have hd : d ∈ Nat.smoothNumbers (Y+1) := by
    by_contra h
    simpa only [smooth_moebius_value,smooth_convolution_value,if_neg h,ne_self_iff_false,or_self] using hw
  have hrle : r ≤ Y := by
    by_contra! hh
    have hl := (Nat.div_lt_iff_lt_mul (Nat.succ_pos Y)).mp hcut
    exact hl.not_ge ((Nat.mul_le_mul_left d hh).trans hk)
  apply Nat.mul_mem_smoothNumbers hd
  exact Nat.mem_smoothNumbers'.mpr fun p _ hp => Nat.lt_succ_of_le ((Nat.le_of_dvd hr hp).trans hrle)

/-- A proper divisor of a three-prime product uses at most two of its factors. -/
theorem smooth_prime_triple_divisor {Y p q r d : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpY : p ≤ Y) (hqY : q ≤ Y) (hrY : r ≤ Y) (hd : d ∣ p*q*r) (hbig : Y^2 < d) :
    d=p*q*r := by
  obtain ⟨s,hs⟩ := hd
  have hk := Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  rcases eq_or_ne s 1 with rfl | hs1
  · simpa only [Nat.mul_one] using hs.symm
  have h0 : s ≠ 0 := by intro hz; simp only [hz,Nat.mul_zero] at hs; omega
  have ha := Nat.minFac_prime hs1
  have had := Nat.minFac_dvd s
  have hdiv : s.minFac ∣ p*q*r := hs ▸ had.trans (dvd_mul_left s d)
  have hdle : d*s.minFac ≤ p*q*r := hs.symm ▸ Nat.mul_le_mul_left d (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) had)
  have hsq {a b : ℕ} (hA : a ≤ Y) (hB : b ≤ Y) : a*b ≤ Y^2 := by
    rw [pow_two]; exact Nat.mul_le_mul hA hB
  have cancel (a b c : ℕ) (hc : 0 < c) (h : d*c ≤ a*b*c) (hA : a ≤ Y) (hB : b ≤ Y) : False :=
    hbig.not_ge ((Nat.le_of_mul_le_mul_right h hc).trans (hsq hA hB))
  rcases ha.dvd_mul.mp hdiv with hpq | hdr
  · rcases ha.dvd_mul.mp hpq with hdp | hdq
    · rw [(Nat.prime_dvd_prime_iff_eq ha hp).mp hdp] at hdle
      exact (cancel q r p hp.pos (by simpa only [mul_comm,mul_assoc,mul_left_comm] using hdle) hqY hrY).elim
    · rw [(Nat.prime_dvd_prime_iff_eq ha hq).mp hdq] at hdle
      exact (cancel p r q hq.pos (by simpa only [mul_comm,mul_assoc,mul_left_comm] using hdle) hpY hrY).elim
  · rw [(Nat.prime_dvd_prime_iff_eq ha hr).mp hdr] at hdle
    exact (cancel p q r hr.pos hdle hpY hqY).elim

/-- Twice the remaining complete-row coefficient of a smooth prime triple. -/
def twiceSmoothTripleWeight (k : ℕ) : ℝ :=
  4*(moebius k:ℝ)-((moebius:ArithmeticFunction ℝ)^2 : ArithmeticFunction ℝ) k

private theorem square_moebius_at_prime {p : ℕ} (hp : p.Prime) :
    ((moebius:ArithmeticFunction ℝ)^2 : ArithmeticFunction ℝ) p= -2 := by
  have h := _root_.RHTower.moebius_mul_apply_prime_pow (moebius:ArithmeticFunction ℝ) (k:=1) hp one_ne_zero
  simpa only [pow_two,pow_one,Nat.sub_self,pow_zero,intCoe_apply,moebius_apply_prime hp,
    moebius_apply_one,Int.cast_neg,Int.cast_one,show -(1:ℝ)-1= -2 by norm_num] using h

private theorem square_moebius_at_square {p : ℕ} (hp : p.Prime) :
    ((moebius:ArithmeticFunction ℝ)^2 : ArithmeticFunction ℝ) (p^2)=1 := by
  rw [show (moebius:ArithmeticFunction ℝ)^2=moebius*moebius by ring,
    _root_.RHTower.moebius_mul_apply_prime_pow _ hp (by decide)]
  norm_num [intCoe_apply,moebius_apply_prime_pow hp (by decide : (2:ℕ) ≠ 0),moebius_apply_prime hp]

/-- Three different primes receive coefficient two. -/
theorem smooth_triple_distinct {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : twiceSmoothTripleWeight (p*q*r)=4 := by
  have c1 := (Nat.coprime_primes hp hq).mpr hpq
  have c2 := Nat.coprime_mul_iff_left.mpr ⟨(Nat.coprime_primes hp hr).mpr hpr,
    (Nat.coprime_primes hq hr).mpr hqr⟩
  have hm : ((moebius:ArithmeticFunction ℝ)^2).IsMultiplicative := isMultiplicative_moebius.intCast.pow
  rw [twiceSmoothTripleWeight,isMultiplicative_moebius.map_mul_of_coprime c2,
    isMultiplicative_moebius.map_mul_of_coprime c1,hm.map_mul_of_coprime c2,hm.map_mul_of_coprime c1,
    square_moebius_at_prime hp,square_moebius_at_prime hq,square_moebius_at_prime hr,
    moebius_apply_prime hp,moebius_apply_prime hq,moebius_apply_prime hr]
  norm_num

/-- A double prime and a different prime receive coefficient one. -/
theorem smooth_triple_repeated {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    twiceSmoothTripleWeight (p^2*q)=2 := by
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hm : ((moebius:ArithmeticFunction ℝ)^2).IsMultiplicative := isMultiplicative_moebius.intCast.pow
  rw [twiceSmoothTripleWeight,isMultiplicative_moebius.map_mul_of_coprime hc,
    hm.map_mul_of_coprime hc,square_moebius_at_square hp,square_moebius_at_prime hq,
    moebius_apply_prime_pow hp (by decide : (2:ℕ)≠0),moebius_apply_prime hq]
  norm_num

/-- A pure cube has zero complete-row coefficient. -/
theorem smooth_triple_cube {p : ℕ} (hp : p.Prime) : twiceSmoothTripleWeight (p^3)=0 := by
  rw [twiceSmoothTripleWeight,show (moebius:ArithmeticFunction ℝ)^2=moebius*moebius by ring,
    _root_.RHTower.moebius_mul_apply_prime_pow _ hp (by decide)]
  norm_num [intCoe_apply,moebius_apply_prime_pow hp (by decide : (3:ℕ)≠0),
    moebius_apply_prime_pow hp (by decide : (2:ℕ)≠0)]

#print axioms high_cubic_rows_are_smooth
#print axioms smooth_prime_triple_divisor
#print axioms smooth_triple_distinct
#print axioms smooth_triple_repeated
#print axioms smooth_triple_cube

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
