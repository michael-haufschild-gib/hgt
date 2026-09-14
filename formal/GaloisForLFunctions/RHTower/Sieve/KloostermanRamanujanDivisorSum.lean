import GaloisForLFunctions.RHTower.Sieve.StadlmannReciprocalPhaseApplications
import GaloisForLFunctions.RHTower.MobiusCoprimeIncidence
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier

/-!
# Lightweight Ramanujan divisor formula

Möbius inversion of the unit indicator and finite additive-character orthogonality give the exact
gcd--Möbius divisor formula for the Chen--Gupta--Li Ramanujan sum.  This arithmetic proof is kept
independent of later Eisenstein and Hawking constructions so finite Kloosterman modules do not
inherit those analytic dependencies.
-/

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open Complex Finset

namespace RHTower.Sieve

noncomputable section

def ramanujanMultiplesFinEquiv {N d : ℕ} [NeZero N]
    (hN : 0 < N) (hd : d ∈ N.divisors) :
    Fin (N / d) ≃ {a : ZMod N // d ∣ a.val} := by
  have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquotpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdvd) hdpos
  refine
    { toFun := fun b => ⟨((d * b.val : ℕ) : ZMod N), ?_⟩
      invFun := fun a => ⟨a.1.val / d, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hlt : d * b.val < N := by
      calc
        d * b.val < d * (N / d) := (Nat.mul_lt_mul_left hdpos).2 b.isLt
        _ = N := Nat.mul_div_cancel' hdvd
    rw [ZMod.val_natCast_of_lt hlt]
    exact dvd_mul_right d b.val
  · apply (Nat.div_lt_iff_lt_mul hdpos).2
    rw [Nat.div_mul_cancel hdvd]
    exact ZMod.val_lt a.1
  · intro b
    apply Fin.ext
    simp only
    have hlt : d * b.val < N := by
      calc
        d * b.val < d * (N / d) := (Nat.mul_lt_mul_left hdpos).2 b.isLt
        _ = N := Nat.mul_div_cancel' hdvd
    rw [ZMod.val_natCast_of_lt hlt, mul_comm d b.val, Nat.mul_div_left _ hdpos]
  · intro a
    apply Subtype.ext
    have hmul : d * (a.1.val / d) = a.1.val := Nat.mul_div_cancel' a.property
    change ((d * (a.1.val / d) : ℕ) : ZMod N) = a.1
    rw [hmul]
    exact ZMod.natCast_zmod_val a.1

@[simp] lemma ramanujanMultiplesFinEquiv_apply
    {N d : ℕ} [NeZero N] (hN : 0 < N) (hd : d ∈ N.divisors)
    (b : Fin (N / d)) :
    (ramanujanMultiplesFinEquiv hN hd b).1 = ((d * b.val : ℕ) : ZMod N) := rfl

lemma stdAddChar_divisorMultiple
    {N d : ℕ} [NeZero N] [NeZero (N / d)]
    (hN : 0 < N) (hd : d ∈ N.divisors)
    (m : ZMod N) (b : Fin (N / d)) :
    ZMod.stdAddChar (((d * b.val : ℕ) : ZMod N) * m) =
      ZMod.stdAddChar (((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d))) := by
  have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquotpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdvd) hdpos
  have hleft :
      ((d * b.val : ℕ) : ZMod N) * m =
        ((d * b.val * m.val : ℕ) : ZMod N) := by
    calc
      ((d * b.val : ℕ) : ZMod N) * m =
          ((d * b.val : ℕ) : ZMod N) * (m.val : ZMod N) := by
            rw [ZMod.natCast_zmod_val]
      _ = ((d * b.val * m.val : ℕ) : ZMod N) := by
        push_cast
        ring
  have hright :
      ((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d)) =
        ((b.val * m.val : ℕ) : ZMod (N / d)) := by
    push_cast
    ring
  rw [hleft, hright]
  change ZMod.stdAddChar ((d * b.val * m.val : ℕ) : ZMod N) =
    ZMod.stdAddChar ((b.val * m.val : ℕ) : ZMod (N / d))
  rw [show ((d * b.val * m.val : ℕ) : ZMod N) =
      ((d * b.val * m.val : ℤ) : ZMod N) by norm_num,
    show ((b.val * m.val : ℕ) : ZMod (N / d)) =
      ((b.val * m.val : ℤ) : ZMod (N / d)) by norm_num,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  have hqC : ((N / d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hquotpos.ne'
  have hNC : (N : ℂ) = (d : ℂ) * (N / d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
  rw [hNC]
  field_simp

private theorem zmod_finEquiv_val {N : ℕ} [NeZero N] (b : Fin N) :
    (ZMod.finEquiv N b).val = b.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N => rfl

theorem sum_stdAddChar_divisible
    {N d : ℕ} [NeZero N] (hN : 0 < N) (hd : d ∈ N.divisors) (m : ZMod N) :
    (∑ a : ZMod N, if d ∣ a.val then ZMod.stdAddChar (a * m) else 0) =
      if (N / d) ∣ m.val then ((N / d : ℕ) : ℂ) else 0 := by
  have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hquotpos : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdvd) hdpos
  letI : NeZero (N / d) := ⟨hquotpos.ne'⟩
  rw [← Finset.sum_filter]
  have hsub :
      (∑ a ∈ (Finset.univ : Finset (ZMod N)).filter (fun a => d ∣ a.val),
          ZMod.stdAddChar (a * m)) =
        ∑ a : {a : ZMod N // d ∣ a.val}, ZMod.stdAddChar (a.1 * m) := by
    exact Finset.sum_subtype _ (by simp) _
  rw [hsub, ← (ramanujanMultiplesFinEquiv hN hd).sum_comp]
  simp_rw [ramanujanMultiplesFinEquiv_apply]
  rw [show (∑ b : Fin (N / d),
      ZMod.stdAddChar ((((d * b.val : ℕ) : ZMod N)) * m)) =
      ∑ b : Fin (N / d),
        ZMod.stdAddChar (((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d))) by
    apply Finset.sum_congr rfl
    intro b hb
    exact stdAddChar_divisorMultiple hN hd m b]
  rw [show (∑ b : Fin (N / d),
      ZMod.stdAddChar (((b.val : ℕ) : ZMod (N / d)) * (m.val : ZMod (N / d)))) =
      ∑ b : Fin (N / d),
        ZMod.stdAddChar ((ZMod.finEquiv (N / d) b) * (m.val : ZMod (N / d))) by
    apply Finset.sum_congr rfl
    intro b hb
    congr 2
    apply ZMod.val_injective
    rw [zmod_finEquiv_val, ZMod.val_natCast_of_lt b.isLt]]
  change (∑ b : Fin (N / d),
      (fun x : ZMod (N / d) => ZMod.stdAddChar (x * (m.val : ZMod (N / d))))
        ((ZMod.finEquiv (N / d)).toEquiv b)) = _
  calc
    _ = ∑ x : ZMod (N / d),
        ZMod.stdAddChar (x * (m.val : ZMod (N / d))) :=
      Equiv.sum_comp (ZMod.finEquiv (N / d)).toEquiv
        (fun x : ZMod (N / d) => ZMod.stdAddChar (x * (m.val : ZMod (N / d))))
    _ = _ := by
      rw [sum_stdAddChar_mul]
      have hz : ((m.val : ZMod (N / d)) = 0) ↔ (N / d) ∣ m.val := by
        exact ZMod.natCast_eq_zero_iff m.val (N / d)
      by_cases hx : (m.val : ZMod (N / d)) = 0
      · rw [if_pos hx, if_pos (hz.mp hx)]
      · rw [if_neg hx, if_neg (fun hm => hx (hz.mpr hm))]
        norm_num

private theorem cglUnitResidueIndicator_eq_mobiusCommonDivisorKernel_sieve
    (Q : RHTower.CGLPositiveModulus) (a : ZMod Q.value) :
    RHTower.cglUnitResidueIndicator Q a =
      ((RHTower.mobiusCommonDivisorKernel a.val Q.value : ℤ) : ℂ) := by
  rw [RHTower.mobiusCommonDivisorKernel_eq_coprimeIndicator]
  have hu : IsUnit a ↔ a.val.Coprime Q.value := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.isUnit_iff_coprime a.val Q.value)
  unfold RHTower.cglUnitResidueIndicator
  by_cases hcop : a.val.Coprime Q.value <;> simp [hcop, hu]

private theorem mem_gcd_divisors_iff
    {N d : ℕ} (hN : N ≠ 0) (a : ZMod N) :
    d ∈ (a.val.gcd N).divisors ↔ d ∣ a.val ∧ d ∣ N := by
  simp [Nat.mem_divisors, Nat.dvd_gcd_iff, Nat.gcd_ne_zero_right hN]

theorem cglRamanujanAdditiveSum_eq_mobiusDivisorFilter_sieve
    (Q : RHTower.CGLPositiveModulus) (m : ZMod Q.value) :
    RHTower.cglRamanujanAdditiveSum Q m =
      ∑ e ∈ Q.value.divisors,
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (if Q.value / e ∣ m.val then ((Q.value / e : ℕ) : ℂ) else 0) := by
  classical
  rw [RHTower.cglRamanujanAdditiveSum_eq_indicator]
  unfold RHTower.cglRamanujanAdditiveSumIndicator
  simp_rw [cglUnitResidueIndicator_eq_mobiusCommonDivisorKernel_sieve]
  unfold RHTower.mobiusCommonDivisorKernel
  have hdivset (a : ZMod Q.value) :
      (a.val.gcd Q.value).divisors =
        Q.value.divisors.filter (fun e => e ∣ a.val) := by
    ext e
    rw [mem_gcd_divisors_iff Q.positive.ne' a]
    simp [Nat.mem_divisors, Q.positive.ne', and_comm]
  simp_rw [hdivset, Int.cast_sum, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hfactor :
      (∑ a : ZMod Q.value,
          if e ∣ a.val then
            ZMod.stdAddChar (a * m) * ((ArithmeticFunction.moebius e : ℤ) : ℂ)
          else 0) =
        (∑ a : ZMod Q.value,
          if e ∣ a.val then ZMod.stdAddChar (a * m) else 0) *
            ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hea : e ∣ a.val <;> simp [hea]
  rw [hfactor, sum_stdAddChar_divisible Q.positive he m]
  by_cases hem : Q.value / e ∣ m.val <;> simp [hem]
  ring

theorem cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve
    (Q : RHTower.CGLPositiveModulus) (m : ZMod Q.value) :
    RHTower.cglRamanujanAdditiveSum Q m =
      ∑ d ∈ (m.val.gcd Q.value).divisors,
        ((d : ℕ) : ℂ) *
          ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ) := by
  classical
  rw [cglRamanujanAdditiveSum_eq_mobiusDivisorFilter_sieve]
  have hdivset :
      (m.val.gcd Q.value).divisors =
        Q.value.divisors.filter (fun d => d ∣ m.val) := by
    ext d
    rw [mem_gcd_divisors_iff Q.positive.ne' m]
    simp [Nat.mem_divisors, Q.positive.ne', and_comm]
  calc
    (∑ e ∈ Q.value.divisors,
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (if Q.value / e ∣ m.val then ((Q.value / e : ℕ) : ℂ) else 0)) =
        ∑ d ∈ Q.value.divisors,
          if d ∣ m.val then
            ((d : ℕ) : ℂ) *
              ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ)
          else 0 := by
      rw [← Nat.sum_div_divisors Q.value (fun e =>
        ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          (if Q.value / e ∣ m.val then ((Q.value / e : ℕ) : ℂ) else 0))]
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd : d ∣ Q.value := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hquotpos : 0 < Q.value / d :=
        Nat.div_pos (Nat.le_of_dvd Q.positive hdvd) hdpos
      have hquotquot : Q.value / (Q.value / d) = d :=
        Nat.div_eq_of_eq_mul_left hquotpos (Nat.mul_div_cancel' hdvd).symm
      rw [hquotquot]
      by_cases hdm : d ∣ m.val <;> simp [hdm]
      ring
    _ = ∑ d ∈ (m.val.gcd Q.value).divisors,
        ((d : ℕ) : ℂ) *
          ((ArithmeticFunction.moebius (Q.value / d) : ℤ) : ℂ) := by
      rw [hdivset, Finset.sum_filter]

end
end RHTower.Sieve
