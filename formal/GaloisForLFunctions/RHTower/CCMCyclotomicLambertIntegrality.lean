import GaloisForLFunctions.RHTower.CCMLambertCoefficientIntegrality
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Cyclotomic containment for the literal CCM Lambert radicals

The target is the exact arithmetic assertion used in Connes--Consani--Moscovici,
equation (55): a square root of every nonnegative integral radicand belongs to
the concrete complex cyclotomic integer ring.  `CCMCyclotomicInteger` presents
that ring as finite integral linear combinations of complex roots of unity.

The key step is a quadratic Gauss sum.  For a prime `p`, Mathlib proves that
the quadratic Gauss sum has square `±p`; multiplying by `I` in the negative
case yields a cyclotomic square root of `p`.  Strong induction over a prime
divisor then supplies every natural radicand.  No analytic continuation or RH
assumption occurs in this module.
-/

open scoped BigOperators
open PowerSeries

namespace RHTower

noncomputable section

/-- A complex root of unity, recorded by a positive annihilating exponent. -/
def CCMRootOfUnity (z : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ z ^ n = 1

/-- The concrete complex realization of `ℤ^cyc`: finite integral linear
combinations of roots of unity. -/
def CCMCyclotomicInteger (z : ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℤ) (ζ : ι → ℂ),
    (∀ i, CCMRootOfUnity (ζ i)) ∧ z = ∑ i, (c i : ℂ) * ζ i

theorem CCMRootOfUnity.one : CCMRootOfUnity (1 : ℂ) := ⟨1, by norm_num, by simp⟩

theorem CCMRootOfUnity.mul {x y : ℂ} (hx : CCMRootOfUnity x) (hy : CCMRootOfUnity y) :
    CCMRootOfUnity (x * y) := by
  rcases hx with ⟨m, hm, hxm⟩
  rcases hy with ⟨n, hn, hyn⟩
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  calc
    (x * y) ^ (m * n) = x ^ (m * n) * y ^ (m * n) := mul_pow _ _ _
    _ = (x ^ m) ^ n * (y ^ n) ^ m := by rw [pow_mul, Nat.mul_comm m n, pow_mul]
    _ = 1 := by rw [hxm, hyn]; simp

theorem CCMRootOfUnity.neg {x : ℂ} (hx : CCMRootOfUnity x) : CCMRootOfUnity (-x) := by
  rcases hx with ⟨n, hn, hxn⟩
  refine ⟨2 * n, Nat.mul_pos (by norm_num) hn, ?_⟩
  rw [neg_pow, Even.neg_one_pow (by exact ⟨n, by ring⟩), one_mul]
  calc
    x ^ (2 * n) = (x ^ n) ^ (2 : ℕ) := by rw [Nat.mul_comm, pow_mul]
    _ = 1 := by rw [hxn]; simp

theorem CCMCyclotomicInteger.one : CCMCyclotomicInteger (1 : ℂ) := by
  refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => 1, fun _ => CCMRootOfUnity.one, ?_⟩
  simp

theorem CCMCyclotomicInteger.zero : CCMCyclotomicInteger (0 : ℂ) := by
  refine ⟨PUnit, inferInstance, fun _ => 0, fun _ => 1, fun _ => CCMRootOfUnity.one, ?_⟩
  simp

theorem CCMCyclotomicInteger.intCast (z : ℤ) : CCMCyclotomicInteger (z : ℂ) := by
  refine ⟨PUnit, inferInstance, fun _ => z, fun _ => 1, fun _ => CCMRootOfUnity.one, ?_⟩
  simp

theorem CCMCyclotomicInteger.natCast (n : ℕ) : CCMCyclotomicInteger (n : ℂ) := by
  exact CCMCyclotomicInteger.intCast n

theorem CCMCyclotomicInteger.root {z : ℂ} (hz : CCMRootOfUnity z) :
    CCMCyclotomicInteger z := by
  refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => z, fun _ => hz, ?_⟩
  simp

theorem CCMCyclotomicInteger.neg {z : ℂ} (hz : CCMCyclotomicInteger z) :
    CCMCyclotomicInteger (-z) := by
  rcases hz with ⟨ι, hι, c, ζ, hζ, hz⟩
  refine ⟨ι, hι, fun i => -c i, ζ, hζ, ?_⟩
  rw [hz]
  simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

theorem CCMCyclotomicInteger.add {x y : ℂ}
    (hx : CCMCyclotomicInteger x) (hy : CCMCyclotomicInteger y) :
    CCMCyclotomicInteger (x + y) := by
  rcases hx with ⟨ι, hι, c, ζ, hζ, hx⟩
  rcases hy with ⟨κ, hκ, d, η, hη, hy⟩
  refine ⟨Sum ι κ, inferInstance,
    Sum.elim c d, Sum.elim ζ η, ?_, ?_⟩
  · rintro (_ | _) <;> simp [hζ, hη]
  · rw [Fintype.sum_sum_type, hx, hy]
    simp

theorem CCMCyclotomicInteger.mul {x y : ℂ}
    (hx : CCMCyclotomicInteger x) (hy : CCMCyclotomicInteger y) :
    CCMCyclotomicInteger (x * y) := by
  rcases hx with ⟨ι, hι, c, ζ, hζ, hx⟩
  rcases hy with ⟨κ, hκ, d, η, hη, hy⟩
  refine ⟨ι × κ, inferInstance,
    fun ij => c ij.1 * d ij.2, fun ij => ζ ij.1 * η ij.2, ?_, ?_⟩
  · intro ij
    exact (hζ ij.1).mul (hη ij.2)
  · rw [Fintype.sum_prod_type, hx, hy]
    calc
      (∑ i, (c i : ℂ) * ζ i) * ∑ j, (d j : ℂ) * η j =
          ∑ i, ∑ j, ((c i : ℂ) * ζ i) * ((d j : ℂ) * η j) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, (↑(c i * d j) : ℂ) * (ζ i * η j) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [Int.cast_mul]
            ring

def ccmZeta8 : ℂ := Complex.exp (((Real.pi : ℂ) / 4) * Complex.I)

theorem ccmZeta8_root : CCMRootOfUnity ccmZeta8 := by
  refine ⟨8, by norm_num, ?_⟩
  rw [ccmZeta8]
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (8 : ℂ))) 8 :=
    Complex.isPrimitiveRoot_exp 8 (by norm_num)
  rw [show ((Real.pi : ℂ) / 4) * Complex.I =
    2 * Real.pi * Complex.I / (8 : ℂ) by ring]
  exact hprim.pow_eq_one

theorem ccmZeta8_add_inv_eq_sqrtTwo :
    ccmZeta8 + ccmZeta8⁻¹ = (Real.sqrt 2 : ℂ) := by
  rw [ccmZeta8, ← Complex.exp_neg]
  rw [Complex.exp_mul_I]
  have hneg : -((Real.pi : ℂ) / 4 * Complex.I) = (-(Real.pi : ℂ) / 4) * Complex.I := by
    ring
  rw [hneg, Complex.exp_mul_I]
  have hcastneg : (-(Real.pi : ℂ) / 4) = ((-(Real.pi / 4) : ℝ) : ℂ) := by
    push_cast
    ring
  have hcastpos : ((Real.pi : ℂ) / 4) = ((Real.pi / 4 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcospos : Complex.cos ((Real.pi : ℂ) / 4) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [hcastpos, ← Complex.ofReal_cos, Real.cos_pi_div_four]
  have hsinpos : Complex.sin ((Real.pi : ℂ) / 4) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [hcastpos, ← Complex.ofReal_sin, Real.sin_pi_div_four]
  have hcosneg : Complex.cos (-(Real.pi : ℂ) / 4) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [hcastneg, ← Complex.ofReal_cos, Real.cos_neg, Real.cos_pi_div_four]
  have hsinneg : Complex.sin (-(Real.pi : ℂ) / 4) = ((-(Real.sqrt 2 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [hcastneg, ← Complex.ofReal_sin, Real.sin_neg, Real.sin_pi_div_four]
  rw [hcospos, hsinpos, hcosneg, hsinneg]
  push_cast
  ring

theorem ccmSqrtTwo_cyclotomicInteger : CCMCyclotomicInteger (Real.sqrt 2 : ℂ) := by
  rw [← ccmZeta8_add_inv_eq_sqrtTwo]
  exact (CCMCyclotomicInteger.root ccmZeta8_root).add
    (CCMCyclotomicInteger.root (by
      rcases ccmZeta8_root with ⟨n, hn, hpow⟩
      refine ⟨n, hn, ?_⟩
      rw [inv_pow, hpow, inv_one]))

theorem ccmStdAddChar_rootOfUnity (p : ℕ) [NeZero p] (a : ZMod p) :
    CCMRootOfUnity (ZMod.stdAddChar a) := by
  refine ⟨p, NeZero.pos p, ?_⟩
  rw [← (ZMod.stdAddChar (N := p)).map_nsmul_eq_pow]
  simp

theorem ccmQuadraticGaussSum_cyclotomicInteger (p : ℕ) [Fact p.Prime] :
    CCMCyclotomicInteger
      (gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
        (ZMod.stdAddChar (N := p))) := by
  let χ : MulChar (ZMod p) ℂ :=
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  refine ⟨ZMod p, inferInstance, quadraticChar (ZMod p),
    ZMod.stdAddChar (N := p), ?_, ?_⟩
  · intro a
    exact ccmStdAddChar_rootOfUnity p a
  · rfl

theorem ccmPrimeSquareRoot_cyclotomicInteger {p : ℕ} [Fact p.Prime] {z : ℂ}
    (hz : z ^ (2 : ℕ) = (p : ℂ)) : CCMCyclotomicInteger z := by
  by_cases hp2 : p = 2
  · subst p
    have hsq : (Real.sqrt 2 : ℂ) ^ (2 : ℕ) = (2 : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hfactor : (z - (Real.sqrt 2 : ℂ)) * (z + (Real.sqrt 2 : ℂ)) = 0 := by
      calc
        (z - (Real.sqrt 2 : ℂ)) * (z + (Real.sqrt 2 : ℂ)) =
            z ^ (2 : ℕ) - (Real.sqrt 2 : ℂ) ^ (2 : ℕ) := by ring
        _ = 0 := by rw [hz, hsq]; ring
    rcases mul_eq_zero.mp hfactor with h | h
    · rw [sub_eq_zero.mp h]
      exact ccmSqrtTwo_cyclotomicInteger
    · rw [eq_neg_of_add_eq_zero_left h]
      exact ccmSqrtTwo_cyclotomicInteger.neg
  · let χ : MulChar (ZMod p) ℂ :=
      (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
    let g : ℂ := gaussSum χ (ZMod.stdAddChar (N := p))
    have hpchar : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hp2
    have hχne : χ ≠ 1 :=
      (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
        (quadraticChar_ne_one hpchar)
    have hχquad : χ.IsQuadratic :=
      (quadraticChar_isQuadratic (ZMod p)).comp _
    have hgsq : g ^ (2 : ℕ) = χ (-1) * (p : ℂ) := by
      simpa [g, ZMod.card] using
        (gaussSum_sq hχne hχquad (ZMod.isPrimitive_stdAddChar p))
    have hgcyc : CCMCyclotomicInteger g := by
      exact ccmQuadraticGaussSum_cyclotomicInteger p
    rcases quadraticChar_dichotomy (F := ZMod p) (neg_ne_zero.mpr one_ne_zero) with hpos | hneg
    · have hχpos : χ (-1) = 1 := by
        simpa [χ] using congrArg (fun x : ℤ => (x : ℂ)) hpos
      have hg2 : g ^ (2 : ℕ) = (p : ℂ) := by rw [hgsq, hχpos, one_mul]
      have hfactor : (z - g) * (z + g) = 0 := by
        calc
          (z - g) * (z + g) = z ^ (2 : ℕ) - g ^ (2 : ℕ) := by ring
          _ = 0 := by rw [hz, hg2]; ring
      rcases mul_eq_zero.mp hfactor with h | h
      · rw [sub_eq_zero.mp h]
        exact hgcyc
      · rw [eq_neg_of_add_eq_zero_left h]
        exact hgcyc.neg
    · have hχneg : χ (-1) = -1 := by
        simpa [χ] using congrArg (fun x : ℤ => (x : ℂ)) hneg
      have hIg2 : (Complex.I * g) ^ (2 : ℕ) = (p : ℂ) := by
        rw [mul_pow, Complex.I_sq, hgsq, hχneg]
        ring
      have hIgcyc : CCMCyclotomicInteger (Complex.I * g) := by
        apply CCMCyclotomicInteger.mul
        · exact CCMCyclotomicInteger.root ⟨4, by norm_num, by norm_num [Complex.I_sq]⟩
        · exact hgcyc
      have hfactor : (z - Complex.I * g) * (z + Complex.I * g) = 0 := by
        calc
          (z - Complex.I * g) * (z + Complex.I * g) = z ^ (2 : ℕ) - (Complex.I * g) ^ (2 : ℕ) := by ring
          _ = 0 := by rw [hz, hIg2]; ring
      rcases mul_eq_zero.mp hfactor with h | h
      · rw [sub_eq_zero.mp h]
        exact hIgcyc
      · rw [eq_neg_of_add_eq_zero_left h]
        exact hIgcyc.neg

private theorem ccmRealSqrtNat_sq (n : ℕ) :
    ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ^ (2 : ℕ) = (n : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  norm_num

theorem ccmNatSquareRoot_cyclotomicInteger {n : ℕ} {z : ℂ}
    (hz : z ^ (2 : ℕ) = (n : ℂ)) : CCMCyclotomicInteger z := by
  induction n using Nat.strong_induction_on generalizing z with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hz0 : z * z = 0 := by
          calc
            z * z = z ^ (2 : ℕ) := by ring
            _ = 0 := by simpa using hz
        rw [mul_self_eq_zero.mp hz0]
        exact CCMCyclotomicInteger.zero
      by_cases hn1 : n = 1
      · subst n
        have hfactor : (z - 1) * (z + 1) = 0 := by
          calc
            (z - 1) * (z + 1) = z ^ (2 : ℕ) - 1 := by ring
            _ = 0 := by rw [hz]; norm_num
        rcases mul_eq_zero.mp hfactor with h | h
        · rw [sub_eq_zero.mp h]
          exact CCMCyclotomicInteger.one
        · rw [eq_neg_of_add_eq_zero_left h]
          exact CCMCyclotomicInteger.one.neg
      obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
      letI : Fact p.Prime := ⟨hpprime⟩
      let m := n / p
      have hpm : p * m = n := by
        dsimp [m]
        exact Nat.mul_div_cancel' hpdvd
      have hmpos : 0 < m := by
        dsimp [m]
        exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd) hpprime.pos
      have hmlt : m < n := by
        dsimp [m]
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hn0) hpprime.one_lt
      let a : ℂ := ((Real.sqrt (p : ℝ) : ℝ) : ℂ)
      let b : ℂ := ((Real.sqrt (m : ℝ) : ℝ) : ℂ)
      have ha2 : a ^ (2 : ℕ) = (p : ℂ) := by
        exact ccmRealSqrtNat_sq p
      have hb2 : b ^ (2 : ℕ) = (m : ℂ) := by
        exact ccmRealSqrtNat_sq m
      have hacyc : CCMCyclotomicInteger a :=
        ccmPrimeSquareRoot_cyclotomicInteger ha2
      have hbcyc : CCMCyclotomicInteger b := ih m hmlt hb2
      have hab2 : (a * b) ^ (2 : ℕ) = (n : ℂ) := by
        rw [mul_pow, ha2, hb2, ← Nat.cast_mul, hpm]
      have hfactor : (z - a * b) * (z + a * b) = 0 := by
        calc
          (z - a * b) * (z + a * b) = z ^ (2 : ℕ) - (a * b) ^ (2 : ℕ) := by ring
          _ = 0 := by rw [hz, hab2]; ring
      rcases mul_eq_zero.mp hfactor with h | h
      · rw [sub_eq_zero.mp h]
        exact hacyc.mul hbcyc
      · rw [eq_neg_of_add_eq_zero_left h]
        exact (hacyc.mul hbcyc).neg

/-- Every finite harmonic source summand is nonnegative. -/
theorem ccmFiniteSemilocalHarmonicTerm_nonneg (ell m k : ℕ) :
    0 ≤ ccmFiniteSemilocalHarmonicTerm ell m k := by
  unfold ccmFiniteSemilocalHarmonicTerm
  positivity

/-- The finite CCM harmonic coefficient is nonnegative. -/
theorem ccmFiniteSemilocalHarmonic_nonneg (ell m : ℕ) :
    0 ≤ ccmFiniteSemilocalHarmonic ell m := by
  unfold ccmFiniteSemilocalHarmonic
  exact Finset.sum_nonneg fun _ _ => ccmFiniteSemilocalHarmonicTerm_nonneg ell m _

/-- The integral source coefficient in CCM equation (51) is nonnegative. -/
theorem ccmFiniteSemilocalSigma_nonneg (ell m : ℕ) :
    0 ≤ ccmFiniteSemilocalSigma ell m := by
  unfold ccmFiniteSemilocalSigma
  positivity

/-- The CCM equation-(53) radicand is not merely integral: it is a natural
number, represented here inside `ℚ`. -/
theorem ccmLambertRadicand_eq_natCast (ell i j : ℕ) :
    ∃ n : ℕ, ccmLambertRadicand ell i j = (n : ℚ) := by
  obtain ⟨a, ha⟩ := ccmFiniteSemilocalSigma_integral ell i
  obtain ⟨b, hb⟩ := ccmFiniteSemilocalSigma_integral ell j
  have hab0 : 0 ≤ a * b := by
    have hnonneg : 0 ≤ ccmLambertRadicand ell i j := by
      unfold ccmLambertRadicand
      exact mul_nonneg (ccmFiniteSemilocalSigma_nonneg ell i)
        (ccmFiniteSemilocalSigma_nonneg ell j)
    rw [ccmLambertRadicand, ha, hb] at hnonneg
    exact_mod_cast hnonneg
  refine ⟨(a * b).toNat, ?_⟩
  calc
    ccmLambertRadicand ell i j = (a : ℚ) * (b : ℚ) := by
      rw [ccmLambertRadicand, ha, hb]
    _ = ((a * b : ℤ) : ℚ) := by norm_num
    _ = (((a * b).toNat : ℕ) : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg hab0).symm

/-- Exact CCM equation-(55) radical gate: every complex square root occurring
in a literal equation-(53) coefficient lies in `ℤ^cyc`. -/
theorem ccmLambertRadical_cyclotomicInteger (ell i j : ℕ) (z : ℂ)
    (hz : z ^ (2 : ℕ) = (ccmLambertRadicand ell i j : ℂ)) :
    CCMCyclotomicInteger z := by
  obtain ⟨n, hn⟩ := ccmLambertRadicand_eq_natCast ell i j
  have hzn : z ^ (2 : ℕ) = (n : ℂ) := by
    rw [hz, hn]
    norm_num
  exact ccmNatSquareRoot_cyclotomicInteger hzn

/-- A complex number is dyadically cyclotomic-integral when multiplication by
some power of `2` lands in the concrete ring `ℤ^cyc`. -/
def CCMDyadicCyclotomicInteger (z : ℂ) : Prop :=
  ∃ d : ℕ, CCMCyclotomicInteger ((2 : ℂ) ^ d * z)

theorem CCMCyclotomicInteger.two : CCMCyclotomicInteger (2 : ℂ) := by
  rw [show (2 : ℂ) = 1 + 1 by norm_num]
  exact CCMCyclotomicInteger.one.add CCMCyclotomicInteger.one

theorem CCMCyclotomicInteger.pow {z : ℂ} (hz : CCMCyclotomicInteger z) (n : ℕ) :
    CCMCyclotomicInteger (z ^ n) := by
  induction n with
  | zero => simpa using CCMCyclotomicInteger.one
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hz

theorem CCMDyadicCyclotomicInteger.add {x y : ℂ}
    (hx : CCMDyadicCyclotomicInteger x) (hy : CCMDyadicCyclotomicInteger y) :
    CCMDyadicCyclotomicInteger (x + y) := by
  obtain ⟨d, hd⟩ := hx
  obtain ⟨e, he⟩ := hy
  refine ⟨d + e, ?_⟩
  have hleft : CCMCyclotomicInteger ((2 : ℂ) ^ e * ((2 : ℂ) ^ d * x)) :=
    (CCMCyclotomicInteger.two.pow e).mul hd
  have hright : CCMCyclotomicInteger ((2 : ℂ) ^ d * ((2 : ℂ) ^ e * y)) :=
    (CCMCyclotomicInteger.two.pow d).mul he
  rw [pow_add, mul_add]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hleft.add hright

theorem ccmDyadicCyclotomicInteger_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ a ∈ s, CCMDyadicCyclotomicInteger (f a)) :
    CCMDyadicCyclotomicInteger (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using CCMCyclotomicInteger.zero⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem ccmLambertEntrySummand_dyadicCyclotomic (ell i j : ℕ) (z : ℂ)
    (hz : CCMCyclotomicInteger z) :
    CCMDyadicCyclotomicInteger (ccmLambertEntrySummand ell i j z) := by
  refine ⟨2 * ell + i + j, ?_⟩
  rw [ccmLambertEntrySummand, mul_div_cancel₀]
  · exact (((CCMCyclotomicInteger.root CCMRootOfUnity.one).neg.pow _).mul
      (CCMCyclotomicInteger.two.mul ccmSqrtTwo_cyclotomicInteger)).mul hz
  · exact pow_ne_zero _ (by norm_num)

/-- Every literal finite divisor coefficient in CCM equation (53) belongs to
`ℤ^cyc[1/2]`, provided the displayed radical choices are cyclotomic. -/
theorem ccmLambertEntryCoefficient_dyadicCyclotomic (i j n : ℕ) (rad : ℕ → ℂ)
    (hrad : ∀ ell, CCMCyclotomicInteger (rad ell)) :
    CCMDyadicCyclotomicInteger (ccmLambertEntryCoefficient i j n rad) := by
  unfold ccmLambertEntryCoefficient
  split_ifs with hn
  · exact ⟨0, by simpa using CCMCyclotomicInteger.zero⟩
  · apply ccmDyadicCyclotomicInteger_sum
    intro ell _
    split_ifs with hdiv
    · exact ccmLambertEntrySummand_dyadicCyclotomic ell i j (rad ell) (hrad ell)
    · exact ⟨0, by simpa using CCMCyclotomicInteger.zero⟩

/-- The unconditional form of CCM equation (55): no choice of a complex
square-root branch can escape the cyclotomic ring. -/
theorem ccmLambertEntryCoefficient_literal_dyadicCyclotomic (i j n : ℕ) (rad : ℕ → ℂ)
    (hrad : ∀ ell, (rad ell) ^ (2 : ℕ) = (ccmLambertRadicand ell i j : ℂ)) :
    CCMDyadicCyclotomicInteger (ccmLambertEntryCoefficient i j n rad) := by
  apply ccmLambertEntryCoefficient_dyadicCyclotomic
  intro ell
  exact ccmLambertRadical_cyclotomicInteger ell i j (rad ell) (hrad ell)

/-- The formal coefficient system of the literal CCM equation-(53) Lambert
series.  This is a formal power series; no convergence assertion is smuggled
into the arithmetic containment theorem. -/
def ccmLambertEntrySeries (i j : ℕ) (rad : ℕ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => ccmLambertEntryCoefficient i j n rad

theorem ccmLambertEntrySeries_coeff (i j n : ℕ) (rad : ℕ → ℂ) :
    (ccmLambertEntrySeries i j rad).coeff n = ccmLambertEntryCoefficient i j n rad :=
  by rw [ccmLambertEntrySeries, coeff_mk]

theorem ccmLambertEntrySeries_coeff_zero (i j : ℕ) (rad : ℕ → ℂ) :
    (ccmLambertEntrySeries i j rad).coeff 0 = 0 := by
  rw [ccmLambertEntrySeries_coeff]
  exact ccmLambertEntryCoefficient_zero i j rad

/-- The full formal Lambert system has coefficientwise containment in
`ℤ^cyc[1/2]` under its literal square-root equations. -/
theorem ccmLambertEntrySeries_coeff_literal_dyadicCyclotomic (i j n : ℕ) (rad : ℕ → ℂ)
    (hrad : ∀ ell, (rad ell) ^ (2 : ℕ) = (ccmLambertRadicand ell i j : ℂ)) :
    CCMDyadicCyclotomicInteger ((ccmLambertEntrySeries i j rad).coeff n) := by
  rw [ccmLambertEntrySeries_coeff]
  exact ccmLambertEntryCoefficient_literal_dyadicCyclotomic i j n rad hrad

end

end RHTower
