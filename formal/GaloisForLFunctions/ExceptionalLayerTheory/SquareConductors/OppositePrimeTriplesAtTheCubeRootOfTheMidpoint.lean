import GaloisForLFunctions.RHTower.Sieve.SelbergInversion
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Primorial

/-!
# Rough prime triples on the right of the sharp midpoint

The quadratic truncation of the convolution logarithm leaves a positive
three-factor remainder. Between the third and fourth powers of the rough
cut, every factor in that remainder is an ordinary prime.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def primitivePart (m : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun k => if m.Coprime k then f k else 0,by simp⟩

private theorem primitive_part_mul (m : ℕ) (f g : ArithmeticFunction ℝ) :
    primitivePart m (f*g)=primitivePart m f*primitivePart m g := by
  ext k
  have hterm (x : ℕ × ℕ) (hx : x ∈ k.divisorsAntidiagonal) :
      (primitivePart m f) x.1*(primitivePart m g) x.2=
        if m.Coprime k then f x.1*g x.2 else 0 := by
    change (if m.Coprime x.1 then f x.1 else 0)*(if m.Coprime x.2 then g x.2 else 0)=_
    rw [←(Nat.mem_divisorsAntidiagonal.mp hx).1]
    by_cases h : m.Coprime (x.1*x.2)
    · obtain ⟨ha,hb⟩ := Nat.coprime_mul_iff_right.mp h
      rw [if_pos ha,if_pos hb,if_pos h]
    · rw [if_neg h]
      by_cases ha : m.Coprime x.1
      · have hb : ¬m.Coprime x.2 := fun hb => h (Nat.coprime_mul_iff_right.mpr ⟨ha,hb⟩)
        rw [if_neg hb,mul_zero]
      · rw [if_neg ha,zero_mul]
  change (if m.Coprime k then ∑ x ∈ k.divisorsAntidiagonal,f x.1*g x.2 else 0)=
    ∑ x ∈ k.divisorsAntidiagonal,(primitivePart m f) x.1*(primitivePart m g) x.2
  rw [sum_congr rfl hterm,sum_ite_irrel,sum_const_zero]

/-- Indicator of integers having no prime through the chosen cutoff. -/
def cubicRoughIndicator (Y : ℕ) : ArithmeticFunction ℝ := primitivePart (primorial Y) zeta

/-- Von Mangoldt weight restricted to primes and powers above the base-prime cutoff. -/
def cubicRoughMangoldt (Y : ℕ) : ArithmeticFunction ℝ := primitivePart (primorial Y) vonMangoldt

/-- Squarefree inclusion-exclusion coefficients for the primes through the cutoff. -/
def cubicSmoothMoebius (Y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ∣ primorial Y then (moebius d:ℝ) else 0,by simp⟩

/-- The actual rough coefficients are a convolution of smooth Möbius
coefficients with the constant-one sequence. -/
theorem cubic_rough_indicator_eq (Y : ℕ) :
    cubicSmoothMoebius Y*(zeta:ArithmeticFunction ℝ)=cubicRoughIndicator Y := by
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [ArithmeticFunction.map_zero]
  rw [coe_mul_zeta_apply]
  change (∑ d ∈ k.divisors,if d ∣ primorial Y then (moebius d:ℝ) else 0)=
    (if (primorial Y).Coprime k then ((zeta:ArithmeticFunction ℝ) k) else 0)
  rw [←sum_filter]
  have hset : k.divisors.filter (· ∣ primorial Y)=(k.gcd (primorial Y)).divisors := by
    ext d
    simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hk)).ne'⟩,
      fun h => ⟨⟨h.1.1,hk⟩,h.1.2⟩⟩
  rw [hset,_root_.RHTower.Sieve.sum_divisors_moebius_real,natCoe_apply,zeta_apply_ne hk,Nat.cast_one]
  change (if k.gcd (primorial Y)=1 then (1:ℝ) else 0)=
    (if (primorial Y).gcd k=1 then 1 else 0)
  simp only [Nat.gcd_comm k]

private def logPriceOf (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun k => f k*Real.log k,by simp⟩

private theorem log_price_leibniz (f g : ArithmeticFunction ℝ) :
    logPriceOf (f*g)=logPriceOf f*g+f*logPriceOf g := by
  ext k
  change (f*g) k*Real.log k=_
  rw [mul_apply,sum_mul,ArithmeticFunction.add_apply,mul_apply,mul_apply,←sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  obtain ⟨hm,hk⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have h0 : x.1 ≠ 0 := left_ne_zero_of_mul (hm.trans_ne hk)
  have h1 : x.2 ≠ 0 := right_ne_zero_of_mul (hm.trans_ne hk)
  rw [←hm,Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr h0) (Nat.cast_ne_zero.mpr h1)]
  change _=f x.1*Real.log x.1*g x.2+f x.1*(g x.2*Real.log x.2)
  ring

private theorem rough_log_price (Y : ℕ) :
    logPriceOf (cubicRoughIndicator Y)=cubicRoughMangoldt Y*cubicRoughIndicator Y := by
  unfold cubicRoughMangoldt cubicRoughIndicator
  rw [←primitive_part_mul,vonMangoldt_mul_zeta]
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [ArithmeticFunction.map_zero]
  change (if (primorial Y).Coprime k then (zeta:ArithmeticFunction ℝ) k else 0)*Real.log k=
    (if (primorial Y).Coprime k then ArithmeticFunction.log k else 0)
  rw [natCoe_apply,zeta_apply_ne hk,Nat.cast_one,ArithmeticFunction.log_apply]
  split_ifs <;> simp

/-- Twice the rough prime-power price equals the two complete logarithmic
rows plus twice the remainder on three nonunit rough factors. -/
theorem cubic_rough_logarithm_identity (Y : ℕ) :
    2*cubicRoughMangoldt Y=
      4*logPriceOf (cubicRoughIndicator Y)-logPriceOf (cubicRoughIndicator Y^2)+
        2*(cubicRoughMangoldt Y*(cubicRoughIndicator Y-1)^2) := by
  rw [pow_two,log_price_leibniz,rough_log_price]
  ring

private theorem cubic_le_minFac {Y k : ℕ} (hk : 1 < k) (hr : (primorial Y).Coprime k) :
    Y+1 ≤ k.minFac := by
  have hp := Nat.minFac_prime (by omega : k ≠ 1)
  have hc := (hr.of_dvd_right (Nat.minFac_dvd k)).symm
  by_contra! h
  exact (hp.coprime_iff_not_dvd.mp hc) (hp.dvd_primorial_iff.mpr (by omega))

/-- Every term of the three-factor remainder lies above the shared
endpoint, and before the next power of the cut it consists of three primes. -/
theorem cubic_rough_factor_support {n Y a b c : ℕ} (hcut : 3*n < (Y+1)^3)
    (hfour : 4*n < (Y+1)^4) (hcap : a*b*c ≤ 4*n)
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (hra : (primorial Y).Coprime a) (hrb : (primorial Y).Coprime b)
    (hrc : (primorial Y).Coprime c) :
    3*n<a*b*c ∧ a.Prime ∧ b.Prime ∧ c.Prime ∧ Y<a ∧ Y<b ∧ Y<c := by
  have low {u : ℕ} (hu : 1 < u) (hru : (primorial Y).Coprime u) : Y+1 ≤ u :=
    (cubic_le_minFac hu hru).trans (Nat.le_of_dvd (by omega) (Nat.minFac_dvd u))
  have la := low ha hra
  have lb := low hb hrb
  have lc := low hc hrc
  have onlyPrime {u v w : ℕ} (hu : 1 < u) (hru : (primorial Y).Coprime u)
      (hv : Y+1 ≤ v) (hw : Y+1 ≤ w) (h : u*v*w ≤ 4*n) : u.Prime := by
    by_contra hnp
    have hs := (Nat.pow_le_pow_left (cubic_le_minFac hu hru) 2).trans
      (Nat.minFac_sq_le_self (by omega) hnp)
    have hg := Nat.mul_le_mul (Nat.mul_le_mul hs hv) hw
    have he : (Y+1)^4=(Y+1)^2*(Y+1)*(Y+1) := by ring
    exact hfour.not_ge (he.le.trans (hg.trans h))
  have hthree := Nat.mul_le_mul (Nat.mul_le_mul la lb) lc
  rw [←pow_two,←pow_succ] at hthree
  exact ⟨hcut.trans_le hthree,onlyPrime ha hra lb lc hcap,
    onlyPrime hb hrb la lc (by simpa only [mul_comm b a] using hcap),
    onlyPrime hc hrc la lb (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcap),la,lb,lc⟩

#print axioms cubic_rough_indicator_eq
#print axioms cubic_rough_logarithm_identity
#print axioms cubic_rough_factor_support

private def cubicNonunit (Y a : ℕ) : Prop := 1 < a ∧ (primorial Y).Coprime a

open Classical in
/-- Ordinary primes exceeding the base-prime cutoff, each counted once. -/
def cubicPrimeIndicator (Y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun a => if cubicNonunit Y a ∧ a.Prime then 1 else 0,by simp [cubicNonunit]⟩

/-- The convolution cube counts ordered prime triples, including repetitions. -/
theorem cubic_prime_indicator_apply (Y p : ℕ) :
    cubicPrimeIndicator Y p=if p.Prime ∧ Y<p then 1 else 0 := by
  classical
  change (if cubicNonunit Y p ∧ p.Prime then (1:ℝ) else 0)=_
  by_cases hp : p.Prime
  · have hc : (primorial Y).Coprime p ↔ Y<p := by
      rw [Nat.coprime_comm,hp.coprime_iff_not_dvd,hp.dvd_primorial_iff,not_le]
    simp [cubicNonunit,hp,hp.one_lt,hc]
  · simp [hp]

open Classical in
private theorem rough_nonunit_value (Y a : ℕ) :
    (cubicRoughIndicator Y-1) a=if cubicNonunit Y a then (1:ℝ) else 0 := by
  rcases a with _ | _ | a
  · simp [cubicNonunit]
  · change cubicRoughIndicator Y 1-(1:ArithmeticFunction ℝ) 1=_
    simp [cubicNonunit,cubicRoughIndicator,primitivePart]
  · change (if (primorial Y).Coprime (a+2) then (zeta:ArithmeticFunction ℝ) (a+2) else 0) -
        (1:ArithmeticFunction ℝ) (a+2)=_
    simp [cubicNonunit,natCoe_apply,zeta_apply_ne (by omega : a+2≠0),one_apply_ne (by omega : a+2≠1)]

open Classical in
private theorem rough_mangoldt_value (Y a : ℕ) :
    cubicRoughMangoldt Y a=if cubicNonunit Y a then vonMangoldt a else 0 := by
  by_cases ha : 1 < a
  · simp [cubicRoughMangoldt,primitivePart,cubicNonunit,ha]
  · have h : a=0 ∨ a=1 := by omega
    rcases h with rfl | rfl <;> simp [cubicNonunit,cubicRoughMangoldt,primitivePart]

private theorem triple_price_congr {k : ℕ} {f g h F G H : ArithmeticFunction ℝ}
    (he : ∀ a b c : ℕ, a*b*c=k → f a*g b*h c=F a*G b*H c) :
    (f*g*h) k=(F*G*H) k := by
  rw [mul_apply,mul_apply]
  apply sum_congr rfl
  intro x hx
  rw [mul_apply,mul_apply,sum_mul,sum_mul]
  apply sum_congr rfl
  intro z hz
  exact he _ _ _ (by rw [(Nat.mem_divisorsAntidiagonal.mp hz).1,(Nat.mem_divisorsAntidiagonal.mp hx).1])

/-- Through the fourth power of the rough cutoff, the entire remainder
has weight one third of the product logarithm per ordered prime triple. -/
theorem cubic_rough_triple_price {n Y k : ℕ} (hc : 3*n < (Y+1)^3)
    (hf : 4*n < (Y+1)^4) (hk : k ≤ 4*n) :
    3*((cubicRoughMangoldt Y*(cubicRoughIndicator Y-1)^2 : ArithmeticFunction ℝ) k)=
      (cubicPrimeIndicator Y^3 : ArithmeticFunction ℝ) k*Real.log k := by
  classical
  let P := cubicPrimeIndicator Y
  have hrep : (cubicRoughMangoldt Y*(cubicRoughIndicator Y-1)*(cubicRoughIndicator Y-1)) k=
      (logPriceOf P*P*P) k := by
    apply triple_price_congr
    intro a b c he
    rw [rough_mangoldt_value,rough_nonunit_value,rough_nonunit_value]
    change _=(if cubicNonunit Y a ∧ a.Prime then (1:ℝ) else 0)*Real.log a*
      (if cubicNonunit Y b ∧ b.Prime then 1 else 0)*(if cubicNonunit Y c ∧ c.Prime then 1 else 0)
    by_cases ha : cubicNonunit Y a
    · by_cases hb : cubicNonunit Y b
      · by_cases hz : cubicNonunit Y c
        · obtain ⟨_,pa,pb,pc,_⟩ := cubic_rough_factor_support hc hf (he.le.trans hk)
            ha.1 hb.1 hz.1 ha.2 hb.2 hz.2
          simp [ha,hb,hz,pa,pb,pc,vonMangoldt_apply_prime pa]
        · simp [hz]
      · simp [hb]
    · simp [ha]
  have hder : logPriceOf (P^3)=logPriceOf P*P*P+logPriceOf P*P*P+logPriceOf P*P*P := by
    rw [show P^3=P*P*P by ring,log_price_leibniz,log_price_leibniz]
    ring
  have hd := congrArg (fun f : ArithmeticFunction ℝ => f k) hder
  change (P^3) k*Real.log k=(logPriceOf P*P*P) k+(logPriceOf P*P*P) k+(logPriceOf P*P*P) k at hd
  rw [pow_two,←mul_assoc,hrep]
  change _=(P^3) k*Real.log k
  linarith only [hd]

#print axioms cubic_prime_indicator_apply
#print axioms cubic_rough_triple_price

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
