import GaloisForLFunctions.BiarithmeticGeometry.Affine.SubgroupPrimeHeight
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SubgroupOrders
import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# A finite prime height controls rational quotient orders

A proper rational subgroup containing one is bounded for at least one p-adic norm.
The reciprocal order of a rational class is bounded by the subgroup norm bound
divided by that rational's p-adic norm.
-/

namespace GaloisForLFunctions.BiarithmeticGeometry

private theorem padicNorm_nat_eq_inv_pow {p n : ℕ} (hn : n ≠ 0) :
    padicNorm p (n : ℚ) = ((p : ℚ) ^ padicValNat p n)⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (Nat.cast_ne_zero.mpr hn),
    padicValRat.of_nat, zpow_neg, zpow_natCast]

/-- The p-part of a positive integer divides it, so its p-adic norm is at least its reciprocal. -/
theorem reciprocal_le_padicNorm_nat {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (n : ℚ)⁻¹ ≤ padicNorm p (n : ℚ) := by
  rw [padicNorm_nat_eq_inv_pow hn.ne']
  apply (inv_le_inv₀ (Nat.cast_pos.mpr hn) (pow_pos (Nat.cast_pos.mpr hp.pos) _)).mpr
  exact_mod_cast Nat.le_of_dvd hn (pow_padicValNat_dvd (p := p) (n := n))

/-- A bound on the prime exponent of the reduced denominator bounds the p-adic norm. -/
theorem padicNorm_le_of_den_prime_height {p h : ℕ} (hp : p.Prime) (q : ℚ)
    (hden : ¬p ^ (h + 1) ∣ q.den) : padicNorm p q ≤ (p : ℚ) ^ h := by
  by_cases hq : q = 0
  · rw [hq, padicNorm.zero]
    exact pow_nonneg (Nat.cast_nonneg p) h
  have hv : padicValNat p q.den ≤ h := by
    have hnot : ¬h + 1 ≤ padicValNat p q.den :=
      fun he => hden ((Nat.pow_dvd_iff_le_padicValNat hp.ne_one q.den_nz).mpr he)
    omega
  rw [padicNorm.eq_zpow_of_nonzero hq, padicValRat_def]
  calc
    (p : ℚ) ^ (-((padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ))) ≤
        (p : ℚ) ^ (h : ℤ) := by
      apply zpow_le_zpow_right₀ (by exact_mod_cast hp.one_le)
      have hvZ : (padicValNat p q.den : ℤ) ≤ (h : ℤ) := by exact_mod_cast hv
      omega
    _ = (p : ℚ) ^ h := zpow_natCast _ _

/-- Every proper rational subgroup containing one is bounded at some finite place. -/
theorem exists_padicNorm_bound_on_rational_subgroup (H : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ H) (hproper : H ≠ ⊤) :
    ∃ p h : ℕ, p.Prime ∧ ∀ q : ℚ, q ∈ H → padicNorm p q ≤ (p : ℚ) ^ h := by
  obtain ⟨p, h, hp, _, _, hden⟩ := exists_finite_prime_height H h1 hproper
  exact ⟨p, h, hp, fun q hq => padicNorm_le_of_den_prime_height hp q (hden q hq)⟩

/-- A bounded p-adic successor forces long quotient orbits at large p-adic norm. -/
theorem reciprocal_subgroupOrder_le_padicNorm_ratio (H : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ H) {p : ℕ} (hp : p.Prime) {C : ℚ}
    (hbound : ∀ q : ℚ, q ∈ H → padicNorm p q ≤ C) {q : ℚ} (hq : q ≠ 0) :
    (rationalSubgroupOrder H q : ℚ)⁻¹ ≤ C / padicNorm p q := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnorm : 0 < padicNorm p q :=
    lt_of_le_of_ne (padicNorm.nonneg q) (Ne.symm (padicNorm.nonzero hq))
  apply (le_div_iff₀ hnorm).mpr
  calc
    (rationalSubgroupOrder H q : ℚ)⁻¹ * padicNorm p q ≤
        padicNorm p (rationalSubgroupOrder H q : ℚ) * padicNorm p q :=
      mul_le_mul_of_nonneg_right
        (reciprocal_le_padicNorm_nat hp (rationalSubgroupOrder_pos H h1 q)) hnorm.le
    _ = padicNorm p ((rationalSubgroupOrder H q : ℚ) * q) := (padicNorm.mul _ _).symm
    _ ≤ C := hbound _ (rationalSubgroupOrder_mul_mem H q)

/-- Large p-adic norm gives a geometric reciprocal-order bound. -/
theorem reciprocal_subgroupOrder_le_prime_power (H : AddSubgroup ℚ)
    (h1 : (1 : ℚ) ∈ H) {p h e : ℕ} (hp : p.Prime)
    (hbound : ∀ q : ℚ, q ∈ H → padicNorm p q ≤ (p : ℚ) ^ h)
    {q : ℚ} (hq : q ≠ 0) (hlarge : (p : ℚ) ^ e ≤ padicNorm p q) :
    (rationalSubgroupOrder H q : ℚ)⁻¹ ≤ (p : ℚ) ^ h * ((p : ℚ) ^ e)⁻¹ := by
  have hpow : (0 : ℚ) < (p : ℚ) ^ e := pow_pos (Nat.cast_pos.mpr hp.pos) e
  have hinv := (inv_le_inv₀ (hpow.trans_le hlarge) hpow).mpr hlarge
  have horder := reciprocal_subgroupOrder_le_padicNorm_ratio H h1 hp hbound hq
  rw [div_eq_mul_inv] at horder
  exact horder.trans (mul_le_mul_of_nonneg_left hinv (pow_nonneg (Nat.cast_nonneg p) h))

#print axioms exists_padicNorm_bound_on_rational_subgroup
#print axioms reciprocal_subgroupOrder_le_padicNorm_ratio
end GaloisForLFunctions.BiarithmeticGeometry
