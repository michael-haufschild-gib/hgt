import GaloisForLFunctions.ExceptionalLayerTheory.TheFactorialWeightAtTheOrdinaryPrimeGrowthBoundary
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernelMass
import GaloisForLFunctions.RHTower.PowerGrowthUnderArithmeticConvolution
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# The Möbius error exponent of the factorial parity sum

The local quotient between the factorial-weighted parity function and
Möbius has zero linear term at every prime. The inverse quotient has the
same property. Both absolute Euler products converge to the right of one half.
-/

noncomputable section

open ArithmeticFunction Finset Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Bounded higher prime-power corrections are absolutely summable at every
exponent above one half. Removing the degree-one term is what changes the threshold. -/
theorem summable_higher_prime_power_correction {g : ArithmeticFunction ℝ} (hm : g.IsMultiplicative)
    (h₁ : ∀ p : ℕ, p.Prime → g p=0) {B : ℝ} (hB : 0≤B)
    (hbound : ∀ p k : ℕ, p.Prime → 2≤k → |g (p^k)|≤B) {b : ℝ} (hb : 1/2<b) :
    Summable (fun n : ℕ => |g n|*(n:ℝ)^(-b)) := by
  let f : ArithmeticFunction ℝ := ⟨fun n => |g n|*(n:ℝ)^(-b),by simp⟩
  have hmul : f.IsMultiplicative := by
    constructor
    · change |g 1|*(1:ℕ)^(-b:ℝ)=1
      simp [hm.map_one]
    · intro m n hc
      change |g (m*n)|*((m*n:ℕ):ℝ)^(-b)=_
      rw [hm.map_mul_of_coprime hc,abs_mul,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      change _=(|g m|*(m:ℝ)^(-b))*(|g n|*(n:ℝ)^(-b))
      ring
  have hpos (n : ℕ) : 0≤f n := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hb0 : 0<b := by linarith only [hb]
  let r := (2:ℝ)^(-b)
  have hr : r<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hb0)
  let C := B/(1-r)
  have hC : 0≤C := div_nonneg hB (sub_pos.mpr hr).le
  have hlocal (p : ℕ) (hp : p.Prime) : Summable (fun k : ℕ => f (p^k)) ∧
      (∑' k : ℕ, f (p^k))≤ Real.exp (C*(p:ℝ)^(-2*b)) := by
    let u := (p:ℝ)^(-b)
    have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
    have hu : 0≤u := Real.rpow_nonneg hpR.le _
    have hur : u≤r := Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (neg_nonpos.mpr hb0.le)
    have hd (k : ℕ) : f (p^(k+2)) ≤ (B*u^2)*u^k := by
      change |g (p^(k+2))|*((p^(k+2):ℕ):ℝ)^(-b)≤_
      rw [Nat.cast_pow,← Real.rpow_natCast_mul hpR.le,mul_comm ((k+2:ℕ):ℝ) (-b),Real.rpow_mul_natCast hpR.le]
      exact (mul_le_mul_of_nonneg_right (hbound p _ hp (by omega)) (pow_nonneg hu _)).trans_eq (by
        dsimp only [u]; rw [pow_add]; ring)
    have hg := (hasSum_geometric_of_lt_one hu (hur.trans_lt hr)).mul_left (B*u^2)
    have ht : Summable (fun k : ℕ => f (p^(k+2))) :=
      Summable.of_nonneg_of_le (fun k => hpos _) hd hg.summable
    have hs : Summable (fun k : ℕ => f (p^k)) := (summable_nat_add_iff 2).mp ht
    have htail := ht.tsum_le_tsum hd hg.summable
    rw [hg.tsum_eq] at htail
    have hlo : B*u^2*(1-u)⁻¹≤C*(p:ℝ)^(-2*b) := by
      have hdiv := div_le_div_of_nonneg_left (mul_nonneg hB (sq_nonneg u)) (sub_pos.mpr hr)
        (sub_le_sub_left hur 1)
      calc
        _ = B*u^2/(1-u) := by ring
        _ ≤ B*u^2/(1-r) := hdiv
        _ = _ := by
          rw [show -2*b=(-b)*((2:ℕ):ℝ) by push_cast; ring,Real.rpow_mul_natCast hpR.le]
          dsimp only [C,u]; ring
    have hz : f p=0 := by change |g p|*(p:ℝ)^(-b)=0; rw [h₁ p hp,abs_zero,zero_mul]
    have he := hs.sum_add_tsum_nat_add 2
    simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,hmul.map_one,hz,add_zero] at he
    refine ⟨hs,?_⟩
    rw [← he]
    exact (add_le_add_left (htail.trans hlo) 1).trans (by simpa only [add_comm] using Real.add_one_le_exp (C*(p:ℝ)^(-2*b)))
  exact _root_.RHTower.pm_summable_of_multiplicative_local_bound f hmul hpos (fun hp => (hlocal _ hp).1)
    (fun n => C*(n:ℝ)^(-2*b)) (fun n => mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    ((Real.summable_nat_rpow.mpr (by linarith only [hb] : -2*b < -1)).mul_left C) (fun hp => (hlocal _ hp).2)

#print axioms summable_higher_prime_power_correction

end GaloisForLFunctions.ExceptionalLayerTheory
