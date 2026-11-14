import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.InertiaUnitCharacters
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Constant residues and decomposition characters

If the constants contain all `N`-th roots of unity and `d ∣ N`,
every root of `X^d-β^d` for a nonzero constant `β` is constant. A valuation unit with constant
residue has trivial constant character under its decomposition group.
These two facts turn split residue equations into bounds on local
Galois groups.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial

/-- Equal powers differ by a constant root of unity when the exponent divides a split roots-of-unity order. -/
theorem exists_constant_of_power_eq {K E : Type*} [Field K] [Field E]
    (f : K →+* E) {N d : ℕ} (hN : 0 < N) (hd : d ∣ N)
    (hprim : (primitiveRoots N K).Nonempty) {u : E} {β : K}
    (hβ : β ≠ 0) (hu : u ^ d = f β ^ d) : ∃ a : K, f a = u := by
  have hfβ : f β ≠ 0 := fun h => hβ (f.injective (h.trans (map_zero f).symm))
  obtain ⟨ζ, hζ⟩ := hprim
  have hs := Polynomial.X_pow_sub_one_splits ((mem_primitiveRoots hN).mp hζ)
  have hpow : (u / f β) ^ N = 1 := by
    obtain ⟨t, rfl⟩ := hd
    rw [pow_mul, div_pow, hu, div_self (pow_ne_zero _ hfβ), one_pow]
  have hroot : ((X ^ N - C (1 : K)).map f).IsRoot (u / f β) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, map_one]
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, hpow, sub_self]
  obtain ⟨a, ha⟩ := hs.mem_range_of_isRoot
    (monic_X_pow_sub_C 1 (Nat.ne_of_gt hN)).ne_zero hroot
  refine ⟨a * β, ?_⟩
  rw [map_mul, ha, div_mul_cancel₀ _ hfβ]

variable {K F L : Type*} [Field K] [Field F] [Field L] [Algebra F L]

/-- A unit with constant residue has trivial constant character under decomposition. -/
theorem decomposition_unit_character_eq_one
    (v : Valuation L (WithZero (Multiplicative ℤ)))
    (f : K →+* v.valuationSubring)
    (hc : ∀ a : K, a ≠ 0 → v (f a : L) = 1)
    (g : v.valuationSubring.decompositionSubgroup F)
    {x : v.valuationSubring} {a b : K}
    (hx : v (x : L) = 1)
    (hres : IsLocalRing.residue _ x = IsLocalRing.residue _ (f b))
    (hfix : g • f b = f b)
    (heig : (g • x : v.valuationSubring) = f a * x) : a = 1 := by
  have hres' : IsLocalRing.residue _ (g • x - x) = 0 := by
    rw [map_sub, sub_eq_zero,
      IsLocalRing.ResidueField.residue_smul, hres,
      ← IsLocalRing.ResidueField.residue_smul, hfix]
  have hmem := (IsLocalRing.residue_eq_zero_iff _).mp hres'
  have hlt := v.mem_maximalIdeal_iff.mp hmem
  exact valuation_unit_eigenvalue_eq_one v (v.valuationSubring.subtype.comp f)
    hc hx hlt (congrArg Subtype.val heig)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
