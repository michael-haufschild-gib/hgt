import GaloisForLFunctions.goldbach.ProductResidueProfile
import GaloisForLFunctions.RHTower.EstermannRamanujanMainTerm
import GaloisForLFunctions.RHTower.Sieve.KloostermanRamanujanDivisorSum

/-!
# Ramanujan expansion of the actual product-residue profile

Grouping the exact gcd Fourier spectrum by reduced modulus gives the finite
Ramanujan correction, including its nonunit fibres and zero residue.
-/

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- Integer representative and reduced-residue character definitions agree exactly. -/
theorem estermannRamanujanSum_eq_cgl (q : ℕ+) (b : ℤ) :
    _root_.RHTower.estermannRamanujanSum (q : ℕ) b =
      _root_.RHTower.cglRamanujanAdditiveSum ⟨(q : ℕ), q.pos⟩ (b : ZMod (q : ℕ)) := by
  classical
  rw [_root_.RHTower.cglRamanujanAdditiveSum, sum_filter,
    _root_.RHTower.sum_zmod_eq_sum_range]
  rw [_root_.RHTower.estermannRamanujanSum, sum_filter]
  apply sum_congr rfl
  intro a _
  by_cases hc : a.Coprime (q : ℕ)
  · have hu : IsUnit (a : ZMod (q : ℕ)) := (ZMod.isUnit_iff_coprime _ _).mpr hc
    rw [if_pos hc, if_pos hu]
    have hcast : (a : ZMod (q : ℕ)) * (b : ZMod (q : ℕ)) =
        (((a : ℤ) * b : ℤ) : ZMod (q : ℕ)) := by
      simp only [Int.cast_mul, Int.cast_natCast]
    rw [hcast, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  · have hu : ¬ IsUnit (a : ZMod (q : ℕ)) :=
      fun hu => hc ((ZMod.isUnit_iff_coprime _ _).mp hu)
    rw [if_neg hc, if_neg hu]

/-- The Fourier multiplicity is the quotient by the actual reduced modulus. -/
theorem productFrequencyGcd_eq_quotient (q : ℕ+) (a : ZMod (q : ℕ)) :
    (Nat.gcd (q : ℕ) a.val : ℂ) =
      ((q : ℕ) : ℂ) / (_root_.RHTower.reducedModulus (q : ℕ) a : ℂ) := by
  have hd : (_root_.RHTower.reducedModulus (q : ℕ) a : ℂ) ≠ 0 := by
    exact_mod_cast (_root_.RHTower.reducedModulus_pos (q : ℕ) a).ne'
  apply (eq_div_iff hd).mpr
  have h : Nat.gcd (q : ℕ) a.val * _root_.RHTower.reducedModulus (q : ℕ) a =
      (q : ℕ) := by
    rw [Nat.gcd_comm (q : ℕ) a.val, _root_.RHTower.reducedModulus]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a.val (q : ℕ))
  exact_mod_cast h

/-- Every divisor conductor contributes to the exact multiplication-fibre density. -/
theorem productResidueCount_eq_ramanujanDivisorSum (q : ℕ+) (r : ZMod (q : ℕ)) :
    (productResidueCount q r : ℂ) / ((q : ℕ) : ℂ) =
      ∑ d ∈ (q : ℕ).divisors,
        _root_.RHTower.estermannRamanujanSum d (r.val : ℤ) / (d : ℂ) := by
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.pos.ne'
  have hs : (productResidueCount q r : ℂ) =
      ((q : ℕ) : ℂ) * ∑ d ∈ (q : ℕ).divisors,
        _root_.RHTower.estermannRamanujanSum d (r.val : ℤ) / (d : ℂ) := by
    calc
      _ = ∑ a : ZMod (q : ℕ), (Nat.gcd (q : ℕ) a.val : ℂ) *
          ZMod.stdAddChar (-(a * r)) := productResidueCount_eq_gcdFourier q r
      _ = ∑ a : ZMod (q : ℕ), ZMod.stdAddChar (-(a * r)) *
          (((q : ℕ) : ℂ) / (_root_.RHTower.reducedModulus (q : ℕ) a : ℂ)) := by
        apply sum_congr rfl
        intro a _
        rw [productFrequencyGcd_eq_quotient, mul_comm]
      _ = ∑ d ∈ (q : ℕ).divisors,
          _root_.RHTower.estermannRamanujanSum d (-(r.val : ℤ)) *
            (((q : ℕ) : ℂ) / (d : ℂ)) :=
        _root_.RHTower.sum_stdAddChar_mul_reducedModulus (q : ℕ) r
          (fun d => ((q : ℕ) : ℂ) / (d : ℂ))
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        rw [_root_.RHTower.estermannRamanujanSum_neg]
        ring
  apply (div_eq_iff hq).mpr
  exact hs.trans (mul_comm _ _)

/-- The finite correction in the same character convention as the Kloosterman sums. -/
theorem productResidueCount_eq_cglRamanujanDivisorSum (q : ℕ+) (r : ZMod (q : ℕ)) :
    (productResidueCount q r : ℂ) / ((q : ℕ) : ℂ) =
      ∑ d : {d : ℕ // d ∈ (q : ℕ).divisors},
        _root_.RHTower.cglRamanujanAdditiveSum
          ⟨d.val, Nat.pos_of_mem_divisors d.property⟩ (r.val : ZMod d.val) / (d.val : ℂ) := by
  rw [productResidueCount_eq_ramanujanDivisorSum, ← sum_attach]
  simp only [attach_eq_univ]
  apply sum_congr rfl
  intro d _
  have h := estermannRamanujanSum_eq_cgl
    (⟨d.val, Nat.pos_of_mem_divisors d.property⟩ : ℕ+) (r.val : ℤ)
  change _root_.RHTower.estermannRamanujanSum d.val (r.val : ℤ) =
    _root_.RHTower.cglRamanujanAdditiveSum
      ⟨d.val, Nat.pos_of_mem_divisors d.property⟩ ((r.val : ℤ) : ZMod d.val) at h
  simpa only [Int.cast_natCast] using congrArg (fun z : ℂ => z / (d.val : ℂ)) h

/-- Pairing any finite observation with products retains the complete conductor correction. -/
theorem productResidue_ramanujan_pairing (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) :
    (∑ a : ZMod (q : ℕ), ∑ b : ZMod (q : ℕ), f (a * b)) / ((q : ℕ) : ℂ) =
      ∑ d ∈ (q : ℕ).divisors, (1 / (d : ℂ)) *
        ∑ r : ZMod (q : ℕ), _root_.RHTower.estermannRamanujanSum d (r.val : ℤ) * f r := by
  rw [← productResidueCount_pairing, sum_div]
  have hpoint (r : ZMod (q : ℕ)) :
      (productResidueCount q r : ℂ) * f r / ((q : ℕ) : ℂ) =
        (∑ d ∈ (q : ℕ).divisors,
          _root_.RHTower.estermannRamanujanSum d (r.val : ℤ) / (d : ℂ)) * f r := by
    rw [← productResidueCount_eq_ramanujanDivisorSum]
    ring
  simp_rw [hpoint, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  ring

end
end GaloisForLFunctions.Goldbach
