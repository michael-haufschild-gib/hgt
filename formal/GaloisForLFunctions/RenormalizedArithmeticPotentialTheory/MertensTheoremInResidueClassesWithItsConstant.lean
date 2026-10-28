import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCharacterMertensLimitIsTheLogarithmicDerivative
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremInResidueClasses

/-!
# Mertens' theorem in residue classes with its constant

Mertens' theorem in residue classes bounds `A(y; r) − log y/φ(q)`
(`exists_abs_classMertensSum_sub_le`). With the character limits `A_χ(y) → −L′/L(1, χ)`
(`charMertensLimit_eq_neg_logDeriv`) the difference converges, and its limit is explicit.

* **The non-coprime prime powers** (`tendsto_nonCoprimeMertens`): `Q_q(y) = Σ_{t ≤ y, (t, q) > 1}
  Λ(t)/t` increases to a limit `Q_q ≤ Σ_{p ∣ q} log p/(p − 1)`.
* **The principal character** (`tendsto_principalMertensSum_sub_log`): `A_{χ₀}(y) = A(y) − Q_q(y)`,
  so `A_{χ₀}(y) − log y → −γ − Q_q`.
* **The class constant** (`tendsto_classMertensSum_sub`, `classMertensConstant_eq`): for `r` a unit
  mod `q`, `A(y; r) − log y/φ(q) → c_r` with
  `φ(q) c_r = −γ − Q_q + Re Σ_{χ ≠ 1} χ(r⁻¹)(−L′/L(1, χ))`.

By orthogonality the class constants and the character values determine each other: the
constant of the class `r` is the character transform of the values of `−L′/L` at `1`, with the
principal character contributing `−γ − Q_q`. These are the finite parts of the residue-class
Mertens sums, the input of the horizon finite part on residue profiles.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

local notation "γ" => Real.eulerMascheroniConstant

variable {q : ℕ}

/-- The **non-coprime prime powers** `Q_q(y) = Σ_{t ≤ y, (t, q) > 1} Λ(t)/t`. -/
def nonCoprimeMertens (q y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, (if t.Coprime q then 0 else Λ t / t)

theorem nonCoprimeMertens_term_nonneg (q t : ℕ) :
    0 ≤ (if t.Coprime q then 0 else Λ t / t) := by
  split_ifs
  · exact le_rfl
  · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)

/-- `Q_q(y) ≤ Σ_{p ∣ q} log p/(p − 1)`: a prime power not coprime to `q` is a power of some
`p ∣ q`. -/
theorem nonCoprimeMertens_le [NeZero q] (y : ℕ) :
    nonCoprimeMertens q y ≤ ∑ p ∈ q.primeFactors, Real.log p / ((p : ℝ) - 1) := by
  have hnn : ∀ t : ℕ, ∀ p ∈ q.primeFactors, 0 ≤ (if p ∣ t then Λ t / t else 0) := fun t p _ => by
    split_ifs
    · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
    · exact le_rfl
  have hterm : ∀ t ∈ Icc 1 y, (if t.Coprime q then 0 else Λ t / t) ≤
      ∑ p ∈ q.primeFactors, (if p ∣ t then Λ t / t else 0) := by
    intro t _
    split_ifs with hcop
    · exact sum_nonneg (hnn t)
    · obtain ⟨p, hp, hpt, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, NeZero.ne q⟩
      calc Λ t / t = (if p ∣ t then Λ t / t else 0) := by rw [if_pos hpt]
        _ ≤ ∑ p ∈ q.primeFactors, (if p ∣ t then Λ t / t else 0) := single_le_sum (hnn t) hpmem
  calc nonCoprimeMertens q y
      ≤ ∑ t ∈ Icc 1 y, ∑ p ∈ q.primeFactors, (if p ∣ t then Λ t / t else 0) := sum_le_sum hterm
    _ = ∑ p ∈ q.primeFactors, ∑ t ∈ Icc 1 y, (if p ∣ t then Λ t / t else 0) := sum_comm
    _ ≤ _ := sum_le_sum fun p hp =>
        sum_dvd_vonMangoldt_div_le (Nat.prime_of_mem_primeFactors hp) (Icc 1 y)

/-- The **non-coprime limit** `Q_q = lim_y Q_q(y)`. -/
def nonCoprimeLimit (q : ℕ) : ℝ := ⨆ y, nonCoprimeMertens q y

theorem tendsto_nonCoprimeMertens [NeZero q] :
    Tendsto (nonCoprimeMertens q) atTop (𝓝 (nonCoprimeLimit q)) := by
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun y => ?_)
    ⟨_, by rintro _ ⟨y, rfl⟩; exact nonCoprimeMertens_le y⟩
  rw [nonCoprimeMertens, nonCoprimeMertens, sum_Icc_succ_top (by omega)]
  linarith [nonCoprimeMertens_term_nonneg q (y + 1)]

/-- **The principal character**: `A_{χ₀}(y) − log y → −γ − Q_q`. -/
theorem tendsto_principalMertensSum_sub_log [NeZero q] :
    Tendsto (fun y : ℕ => principalMertensSum q y - Real.log y) atTop
      (𝓝 (-γ - nonCoprimeLimit q)) := by
  refine (tendsto_mertensSum_sub_log.sub tendsto_nonCoprimeMertens).congr fun y => ?_
  have h : principalMertensSum q y = mertensSum y - nonCoprimeMertens q y := by
    rw [principalMertensSum, mertensSum, nonCoprimeMertens, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => by split_ifs <;> ring
  rw [h]
  ring

/-- The **class Mertens constant**:
`c_r = (−γ − Q_q + Re Σ_{χ ≠ 1} χ(r⁻¹) α_χ)/φ(q)`, `α_χ = lim A_χ`. -/
def classMertensConstant (q : ℕ) [NeZero q] (r : ZMod q) : ℝ :=
  (-γ - nonCoprimeLimit q +
    (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensLimit χ).re) / q.totient

/-- **Mertens' theorem in residue classes with its constant**: for `r` a unit mod `q`,
`A(y; r) − log y/φ(q) → c_r`. -/
theorem tendsto_classMertensSum_sub [NeZero q] {r : ZMod q} (hr : IsUnit r) :
    Tendsto (fun y : ℕ => classMertensSum q r y - Real.log y / q.totient) atTop
      (𝓝 (classMertensConstant q r)) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hrinv : IsUnit r⁻¹ := IsUnit.of_mul_eq_one r (ZMod.inv_mul_of_unit r hr)
  -- `φ(q) A(y; r) − log y = (A_{χ₀}(y) − log y) + Re Σ_{χ ≠ 1} χ(r⁻¹) A_χ(y)`
  have hsplit : ∀ y : ℕ, (q.totient : ℝ) * classMertensSum q r y - Real.log y =
      (principalMertensSum q y - Real.log y) +
        (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensSum χ y).re := by
    intro y
    have h : (((q.totient : ℝ) * classMertensSum q r y - Real.log y : ℝ) : ℂ) =
        ((principalMertensSum q y - Real.log y : ℝ) : ℂ) +
          ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensSum χ y := by
      rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
        totient_mul_classMertensSum_eq hr y,
        ← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q)),
        MulChar.one_apply hrinv, one_mul, charMertensSum_one, Complex.ofReal_sub]
      ring
    have h' := congrArg Complex.re h
    rwa [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at h'
  -- the non-principal characters converge
  have hchar : Tendsto (fun y : ℕ =>
      (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensSum χ y).re) atTop
      (𝓝 (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensLimit χ).re) :=
    (Complex.continuous_re.tendsto _).comp (tendsto_finsetSum _ fun χ hχ =>
      (tendsto_charMertensSum χ (ne_of_mem_erase hχ)).const_mul _)
  have hmain := (tendsto_principalMertensSum_sub_log (q := q)).add hchar
  have hdiv := hmain.div_const (q.totient : ℝ)
  refine hdiv.congr fun y => ?_
  rw [← hsplit y]
  field_simp

/-- **The class constant through `L′/L`**: `φ(q) c_r = −γ − Q_q + Re Σ_{χ ≠ 1} χ(r⁻¹)(−L′/L(1, χ))`. -/
theorem classMertensConstant_eq [NeZero q] (r : ZMod q) :
    classMertensConstant q r =
      (-γ - nonCoprimeLimit q +
        (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ *
          (-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)).re) /
        q.totient := by
  rw [classMertensConstant]
  congr 3
  exact sum_congr rfl fun χ hχ => by rw [charMertensLimit_eq_neg_logDeriv χ (ne_of_mem_erase hχ)]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
