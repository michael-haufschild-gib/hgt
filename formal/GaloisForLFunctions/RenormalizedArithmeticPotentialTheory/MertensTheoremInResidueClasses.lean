import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremForCharacters
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonDivergenceLivesOnTheTorsionOrbits
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Mertens' theorem in residue classes

For `r` a unit mod `q`, the prime powers `t ≡ r (mod q)` carry `1/φ(q)` of Mertens' sum:
`A(y; r) = Σ_{t ≤ y, t ≡ r} Λ(t)/t = log y/φ(q) + O(1)` (`exists_abs_classMertensSum_sub_le`).

* **Orthogonality** (`totient_mul_classMertensSum_eq`): `φ(q) A(y; r) = Σ_χ χ(r^{−1}) A_χ(y)`.
* **The principal character** (`abs_principalMertensSum_sub_log_le`): `A_{χ₀}(y)` is Mertens' sum
  without the powers of the primes dividing `q`, so
  `|A_{χ₀}(y) − log y| ≤ log 4 + 4 + Σ_{p ∣ q} log p/(p − 1)`.
* **The other characters** contribute `O(1)` each (`exists_norm_charMertensSum_le`).

This is the input for the horizon on residue classes: every class coprime to `q` carries the same
logarithmic divergence `log y/φ(q)`, so the classes are not separated by the prime place.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ} [NeZero q]

/-- Mertens' sum over the residue class `r` mod `q`: `A(y; r) = Σ_{t ≤ y, t ≡ r} Λ(t)/t`. -/
def classMertensSum (q : ℕ) (r : ZMod q) (y : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 y, (if (t : ZMod q) = r then Λ t / t else 0)

/-- Mertens' sum over the units mod `q`: `A_{χ₀}(y) = Σ_{t ≤ y, (t, q) = 1} Λ(t)/t`. -/
def principalMertensSum (q y : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 y, (if t.Coprime q then Λ t / t else 0)

omit [NeZero q] in
/-- The principal character gives `A_{χ₀}`. -/
theorem charMertensSum_one (y : ℕ) :
    charMertensSum (1 : DirichletCharacter ℂ q) y = (principalMertensSum q y : ℂ) := by
  rw [charMertensSum, principalMertensSum, Complex.ofReal_sum]
  refine sum_congr rfl fun t _ => ?_
  by_cases h : t.Coprime q
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime t q).mpr h), one_mul, if_pos h]
  · rw [MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime t q).mp hu)), zero_mul,
      if_neg h, Complex.ofReal_zero]

/-- **Orthogonality**: `φ(q) A(y; r) = Σ_χ χ(r^{−1}) A_χ(y)`. -/
theorem totient_mul_classMertensSum_eq {r : ZMod q} (hr : IsUnit r) (y : ℕ) :
    (q.totient : ℂ) * (classMertensSum q r y : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ r⁻¹ * charMertensSum χ y := by
  simp only [charMertensSum, mul_sum, classMertensSum, Complex.ofReal_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hr (t : ZMod q)
  have h2 : ∑ χ : DirichletCharacter ℂ q, χ r⁻¹ * (χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ)) =
      (∑ χ : DirichletCharacter ℂ q, χ r⁻¹ * χ (t : ZMod q)) * ((Λ t / t : ℝ) : ℂ) := by
    rw [sum_mul]
    exact sum_congr rfl fun χ _ => by ring
  rw [h2, h]
  by_cases ht : (t : ZMod q) = r
  · rw [if_pos ht, if_pos ht.symm]
  · rw [if_neg ht, if_neg (Ne.symm ht)]
    simp

/-- **The principal character**: `|A_{χ₀}(y) − log y| ≤ log 4 + 4 + Σ_{p ∣ q} log p/(p − 1)`. -/
theorem abs_principalMertensSum_sub_log_le {y : ℕ} (hy : 1 ≤ y) :
    |principalMertensSum q y - Real.log y| ≤
      Real.log 4 + 4 + ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1) := by
  have hmert := RHTower.Mertens.mertens_first y hy
  -- the removed terms are prime powers of the primes dividing `q`
  have hdiff : ∑ t ∈ Icc 1 y, Λ t / t - principalMertensSum q y =
      ∑ t ∈ Icc 1 y, (if t.Coprime q then 0 else Λ t / t) := by
    rw [principalMertensSum, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => by split_ifs <;> ring
  have hterm : ∀ t ∈ Icc 1 y, (if t.Coprime q then 0 else Λ t / t) ≤
      ∑ p ∈ q.primeFactors, (if p ∣ t then Λ t / t else 0) := by
    intro t _
    have hnn : ∀ p ∈ q.primeFactors, 0 ≤ (if p ∣ t then Λ t / t else 0) := fun p _ => by
      split_ifs
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
      · exact le_rfl
    split_ifs with hcop
    · exact sum_nonneg hnn
    · -- a prime `p ∣ gcd(t, q)`
      obtain ⟨p, hp, hpt, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hpmem : p ∈ q.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩
      calc Λ t / t = (if p ∣ t then Λ t / t else 0) := by rw [if_pos hpt]
        _ ≤ ∑ p ∈ q.primeFactors, (if p ∣ t then Λ t / t else 0) :=
            single_le_sum hnn hpmem
  have hsum : ∑ t ∈ Icc 1 y, (if t.Coprime q then 0 else Λ t / t) ≤
      ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1) := by
    calc _ ≤ ∑ t ∈ Icc 1 y, ∑ p ∈ q.primeFactors, (if p ∣ t then Λ t / t else 0) :=
          sum_le_sum hterm
      _ = ∑ p ∈ q.primeFactors, ∑ t ∈ Icc 1 y, (if p ∣ t then Λ t / t else 0) := sum_comm
      _ ≤ _ := sum_le_sum fun p hp =>
          sum_dvd_vonMangoldt_div_le (Nat.prime_of_mem_primeFactors hp) (Icc 1 y)
  have hpos : 0 ≤ ∑ t ∈ Icc 1 y, (if t.Coprime q then 0 else Λ t / t) :=
    sum_nonneg fun t _ => by
      split_ifs
      · exact le_rfl
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
  rw [abs_le] at hmert ⊢
  constructor <;> linarith [hmert.1, hmert.2]

/-- **Mertens' theorem in residue classes**: for `r` a unit mod `q`,
`|A(y; r) − log y/φ(q)| ≤ C` for all `y ≥ 1`. -/
theorem exists_abs_classMertensSum_sub_le {r : ZMod q} (hr : IsUnit r) :
    ∃ C : ℝ, ∀ y : ℕ, 1 ≤ y → |classMertensSum q r y - Real.log y / q.totient| ≤ C := by
  -- a bound for every non-principal character
  have hex : ∀ χ : DirichletCharacter ℂ q, ∃ C : ℝ, χ ≠ 1 → ∀ y, ‖charMertensSum χ y‖ ≤ C := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨0, fun h => absurd hχ h⟩
    · obtain ⟨C, hC⟩ := exists_norm_charMertensSum_le χ hχ
      exact ⟨C, fun _ => hC⟩
  choose C hC using hex
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  set B := Real.log 4 + 4 + ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1)
  set D := ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), C χ
  refine ⟨(B + D) / q.totient, fun y hy => ?_⟩
  have hrinv : IsUnit r⁻¹ :=
    IsUnit.of_mul_eq_one r (ZMod.inv_mul_of_unit r hr)
  -- `φ(q) A(y; r) − log y = (A_{χ₀}(y) − log y) + Σ_{χ ≠ 1} χ(r⁻¹) A_χ(y)`
  have hsplit : (((q.totient : ℝ) * classMertensSum q r y - Real.log y : ℝ) : ℂ) =
      ((principalMertensSum q y - Real.log y : ℝ) : ℂ) +
        ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensSum χ y := by
    rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
      totient_mul_classMertensSum_eq hr y,
      ← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q)),
      MulChar.one_apply hrinv, one_mul, charMertensSum_one, Complex.ofReal_sub]
    ring
  have hE : ‖∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensSum χ y‖ ≤ D := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun χ hχ => ?_)
    rw [norm_mul]
    calc ‖χ r⁻¹‖ * ‖charMertensSum χ y‖ ≤ 1 * C χ :=
          mul_le_mul (DirichletCharacter.norm_le_one χ _) (hC χ (ne_of_mem_erase hχ) y)
            (norm_nonneg _) zero_le_one
      _ = C χ := one_mul _
  have hP := abs_principalMertensSum_sub_log_le (q := q) hy
  have hmain : |(q.totient : ℝ) * classMertensSum q r y - Real.log y| ≤ B + D := by
    have h := congrArg norm hsplit
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    rw [h]
    calc _ ≤ ‖(((principalMertensSum q y - Real.log y : ℝ)) : ℂ)‖ +
          ‖∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensSum χ y‖ :=
          norm_add_le _ _
      _ ≤ B + D := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add hP hE
  rw [show classMertensSum q r y - Real.log y / q.totient =
      ((q.totient : ℝ) * classMertensSum q r y - Real.log y) / q.totient by field_simp,
    abs_div, abs_of_pos hφ]
  exact div_le_div_of_nonneg_right hmain hφ.le

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
