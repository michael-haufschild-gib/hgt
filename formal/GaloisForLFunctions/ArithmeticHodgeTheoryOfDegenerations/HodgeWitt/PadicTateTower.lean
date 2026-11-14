import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.CompatibleTowers
import GaloisForLFunctions.HTGeometry.BirchTateWTwop

/-!
# Compatible division points in the p-adic Tate quotient

The existing quotient `ℚ_p/ℤ_p` is primary torsion. Its compatible division
points instead have no primary torsion. Every p-adic integer supplies the
tower `z/pⁿ mod ℤ_p`, and distinct integers give distinct towers. Thus the
torsion-free tower is nonzero; torsion does not commute with this inverse limit.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

open GaloisForLFunctions.HTGeometry

variable (p : ℕ) [Fact p.Prime]

private theorem padic_prime_pow_ne_zero (n : ℕ) : (p : ℤ_[p]) ^ n ≠ 0 :=
  pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- The class `z/pⁿ` in the existing p-adic Tate quotient. -/
def padicDivisionPoint (n : ℕ) : ℤ_[p] →+ PadicTateQuotient p :=
  (Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) ((p : ℤ_[p]) ^ n)).subtype.toAddMonoidHom.comp
    (padicTateTorsionParam p ((p : ℤ_[p]) ^ n) (padic_prime_pow_ne_zero p n))

theorem padicDivisionPoint_apply (n : ℕ) (z : ℤ_[p]) :
    padicDivisionPoint p n z =
      z • (Submodule.Quotient.mk (((p : ℚ_[p]) ^ n)⁻¹) : PadicTateQuotient p) := by
  change z • (Submodule.Quotient.mk (((((p : ℤ_[p]) ^ n) : ℤ_[p]) : ℚ_[p])⁻¹) :
    PadicTateQuotient p) = _
  congr 2

theorem padicDivisionPoint_pow_smul (n : ℕ) (z : ℤ_[p]) :
    p ^ n • padicDivisionPoint p n z = 0 := by
  have h := (padicTateTorsionParam p ((p : ℤ_[p]) ^ n)
    (padic_prime_pow_ne_zero p n) z).2
  rw [Submodule.mem_torsionBy_iff] at h
  change p ^ n • (padicTateTorsionParam p ((p : ℤ_[p]) ^ n)
    (padic_prime_pow_ne_zero p n) z).1 = 0
  simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using h

theorem padicDivisionPoint_transition (n : ℕ) (z : ℤ_[p]) :
    p • padicDivisionPoint p (n + 1) z = padicDivisionPoint p n z := by
  rw [padicDivisionPoint_apply, padicDivisionPoint_apply]
  rw [smul_comm]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul (R := ℤ_[p])]
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  change (p : ℚ_[p]) * ((p : ℚ_[p]) ^ (n + 1))⁻¹ = ((p : ℚ_[p]) ^ n)⁻¹
  rw [pow_succ, mul_inv_rev]
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul]

/-- A division point vanishes precisely when its numerator is divisible by the denominator. -/
theorem padicDivisionPoint_eq_zero_iff (n : ℕ) (z : ℤ_[p]) :
    padicDivisionPoint p n z = 0 ↔ (p : ℤ_[p]) ^ n ∣ z := by
  have he : padicDivisionPoint p n z = 0 ↔
      padicTateTorsionParam p ((p : ℤ_[p]) ^ n) (padic_prime_pow_ne_zero p n) z = 0 :=
    ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [he, ← AddMonoidHom.mem_ker, ker_padicTateTorsionParam]
  exact Ideal.mem_span_singleton

/-- All compatible division points of a p-adic integer, as an additive tower. -/
def padicTateTowerEmbedding : ℤ_[p] →+ tateTower p (PadicTateQuotient p) where
  toFun z := ⟨fun n => padicDivisionPoint p n z,
    (fun n => padicDivisionPoint_transition p n z),
    (fun n => padicDivisionPoint_pow_smul p n z)⟩
  map_zero' := Subtype.ext (funext fun n => map_zero (padicDivisionPoint p n))
  map_add' z w := Subtype.ext (funext fun n => map_add (padicDivisionPoint p n) z w)

/-- The tower retains its entire p-adic numerator. -/
theorem padicTateTowerEmbedding_injective : Function.Injective (padicTateTowerEmbedding p) := by
  have hzero (z : ℤ_[p]) (hz : padicTateTowerEmbedding p z = 0) : z = 0 := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [map_zero]
    have hn := congrArg (fun x : tateTower p (PadicTateQuotient p) => x.1 n) hz
    have hd := (padicDivisionPoint_eq_zero_iff p n z).mp hn
    change z ∈ RingHom.ker (PadicInt.toZModPow n)
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hd
  intro z w h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, h, sub_self]

/-- This torsion-free inverse limit is nontrivial. -/
theorem padicTateTower_one_ne_zero : padicTateTowerEmbedding p 1 ≠ 0 := by
  intro h
  exact one_ne_zero (padicTateTowerEmbedding_injective p (h.trans (map_zero _).symm))

/-- The p-adic quotient's compatible division points have no primary torsion. -/
theorem padicTateTower_pow_smul_eq_zero_iff
    (x : tateTower p (PadicTateQuotient p)) (r : ℕ) : p ^ r • x = 0 ↔ x = 0 :=
  tateTower_pow_smul_eq_zero_iff p x r

#print axioms padicTateTowerEmbedding_injective
#print axioms padicTateTower_one_ne_zero
#print axioms padicTateTower_pow_smul_eq_zero_iff

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
