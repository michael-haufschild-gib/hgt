import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOnResidueClasses
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonSeesOnlyTheMeanOfAClassFunction

/-!
# The residue finite part is diagonalized by characters

On the unit residue classes mod `q` the finite part of the horizon form is the convolution by the
class Mertens constants: the pair of classes `(a, b)` carries `F_{ab} = c_{a⁻¹b} + c_{b⁻¹a}`
(`exists_abs_residueGram_finitePart_le`). This file diagonalizes `F`.

* **Spectral values** (`residueSpectralValue`): `β_χ = −L′/L(1, χ)` for `χ ≠ 1` (the character
  Mertens limit, `charMertensLimit_eq_neg_logDeriv`) and `β_1 = −γ − Q_q`.
* **Conjugate characters** (`charMertensLimit_inv`): `α_{χ⁻¹} = conj α_χ`, since `χ⁻¹ = conj χ`.
* **The class constants are a character transform** (`classMertensConstant_eq_sum`):
  `φ(q) c_r = Σ_χ χ(r⁻¹) β_χ`; the sum is real because `χ ↦ χ⁻¹` conjugates its terms.
* **Fourier inversion** (`sum_classMertensConstant_mul_char`): `Σ_{u ∈ (ℤ/q)ˣ} c_u χ(u) = β_χ`.
* **Diagonalization** (`sum_residueFinitePart_mul_char`): every character is an eigenvector of `F`,
  `Σ_b F_{ab} χ(b) = 2 Re β_χ · χ(a)`.

So the finite part of the horizon on the residue classes mod `q` has the eigenvalues
`2 Re(−L′/L(1, χ))`, one for each non-trivial character, and `2(−γ − Q_q)` on the trivial
character, which carries the rank-one divergence. The residue classes are invisible to the
divergence (RP24) and fully visible to the finite part, which reads the logarithmic derivatives of
all Dirichlet `L`-functions mod `q` at `s = 1`.
-/

noncomputable section

open Finset Filter Topology ComplexConjugate

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {q : ℕ} [NeZero q]

/-- The **spectral value** of a character: `β_χ = α_χ = −L′/L(1, χ)` for `χ ≠ 1`, `β_1 = −γ − Q_q`. -/
def residueSpectralValue (χ : DirichletCharacter ℂ q) : ℂ :=
  if χ = 1 then ((-γ - nonCoprimeLimit q : ℝ) : ℂ) else charMertensLimit χ

omit [NeZero q] in
/-- The inverse character is the conjugate: `χ⁻¹(a) = conj χ(a)`. -/
theorem char_inv_apply_eq_conj (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ⁻¹ a = conj (χ a) :=
  (MulChar.star_apply' χ a).symm

omit [NeZero q] in
theorem charMertensSum_inv (χ : DirichletCharacter ℂ q) (y : ℕ) :
    charMertensSum χ⁻¹ y = conj (charMertensSum χ y) := by
  rw [charMertensSum, charMertensSum, map_sum]
  exact sum_congr rfl fun t _ => by rw [map_mul, Complex.conj_ofReal, char_inv_apply_eq_conj]

/-- **Conjugate characters have conjugate limits**: `α_{χ⁻¹} = conj α_χ`. -/
theorem charMertensLimit_inv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    charMertensLimit χ⁻¹ = conj (charMertensLimit χ) := by
  have h1 := tendsto_charMertensSum χ⁻¹ (inv_ne_one.mpr hχ)
  have h2 := ((Complex.continuous_conj.tendsto _).comp (tendsto_charMertensSum χ hχ))
  exact tendsto_nhds_unique h1 (h2.congr fun y => (charMertensSum_inv χ y).symm)

theorem residueSpectralValue_inv (χ : DirichletCharacter ℂ q) :
    residueSpectralValue χ⁻¹ = conj (residueSpectralValue χ) := by
  by_cases hχ : χ = 1
  · subst hχ
    rw [inv_one, residueSpectralValue, if_pos rfl, Complex.conj_ofReal]
  · rw [residueSpectralValue, if_neg (inv_ne_one.mpr hχ), residueSpectralValue, if_neg hχ,
      charMertensLimit_inv χ hχ]

/-- **The class constants are a character transform**: for `r` a unit,
`φ(q) c_r = Σ_χ χ(r⁻¹) β_χ`. -/
theorem classMertensConstant_eq_sum {r : ZMod q} (hr : IsUnit r) :
    ((classMertensConstant q r : ℝ) : ℂ) =
      (∑ χ : DirichletCharacter ℂ q, χ r⁻¹ * residueSpectralValue χ) / q.totient := by
  have hrinv : IsUnit r⁻¹ := IsUnit.of_mul_eq_one r (ZMod.inv_mul_of_unit r hr)
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  set S := ∑ χ : DirichletCharacter ℂ q, χ r⁻¹ * residueSpectralValue χ with hSdef
  -- `χ ↦ χ⁻¹` conjugates every term, so `S` is real
  have hreal : conj S = S := by
    rw [hSdef, map_sum]
    calc ∑ χ : DirichletCharacter ℂ q, conj (χ r⁻¹ * residueSpectralValue χ)
        = ∑ χ : DirichletCharacter ℂ q, χ⁻¹ r⁻¹ * residueSpectralValue χ⁻¹ :=
          sum_congr rfl fun χ _ => by
            rw [map_mul, char_inv_apply_eq_conj, residueSpectralValue_inv]
      _ = ∑ χ : DirichletCharacter ℂ q, χ r⁻¹ * residueSpectralValue χ :=
          Equiv.sum_comp (Equiv.inv (DirichletCharacter ℂ q))
            (fun ψ : DirichletCharacter ℂ q => ψ r⁻¹ * residueSpectralValue ψ)
  -- `S = β_1 + Σ_{χ ≠ 1} χ(r⁻¹) α_χ`
  have hsplit : S = ((-γ - nonCoprimeLimit q : ℝ) : ℂ) +
      ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ r⁻¹ * charMertensLimit χ := by
    rw [hSdef, ← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q)),
      MulChar.one_apply hrinv, one_mul, residueSpectralValue, if_pos rfl]
    congr 1
    exact sum_congr rfl fun χ hχ => by
      rw [residueSpectralValue, if_neg (ne_of_mem_erase hχ)]
  have hre : S.re = (q.totient : ℝ) * classMertensConstant q r := by
    rw [hsplit, Complex.add_re, Complex.ofReal_re, classMertensConstant]
    have : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    field_simp
  rw [eq_div_iff hφ, ← Complex.conj_eq_iff_re.mp hreal, hre]
  push_cast
  ring

/-- Summing a character over the units: `Σ_u θ(u) = φ(q)` if `θ = 1` and `0` otherwise. -/
theorem sum_units_char (θ : DirichletCharacter ℂ q) :
    ∑ u : (ZMod q)ˣ, θ u = if θ = 1 then (q.totient : ℂ) else 0 := by
  split_ifs with hθ
  · subst hθ
    rw [sum_congr rfl fun u _ => MulChar.one_apply u.isUnit, sum_const, card_univ,
      ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one]
  · exact sum_units_char_eq_zero θ hθ

/-- **Fourier inversion**: `Σ_{u ∈ (ℤ/q)ˣ} c_u χ(u) = β_χ`. -/
theorem sum_classMertensConstant_mul_char (χ : DirichletCharacter ℂ q) :
    ∑ u : (ZMod q)ˣ, ((classMertensConstant q u : ℝ) : ℂ) * χ u = residueSpectralValue χ := by
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  -- `ψ(u⁻¹) χ(u) = (ψ⁻¹ χ)(u)`
  have hterm : ∀ (ψ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ),
      ψ ((u : ZMod q)⁻¹) * χ u = (ψ⁻¹ * χ) u := by
    intro ψ u
    rw [MulChar.coeToFun_mul, Pi.mul_apply, MulChar.inv_apply, Ring.inverse_unit,
      ZMod.inv_coe_unit]
  calc ∑ u : (ZMod q)ˣ, ((classMertensConstant q u : ℝ) : ℂ) * χ u
      = ∑ u : (ZMod q)ˣ, (∑ ψ : DirichletCharacter ℂ q,
          ψ ((u : ZMod q)⁻¹) * residueSpectralValue ψ) / q.totient * χ u :=
        sum_congr rfl fun u _ => by rw [classMertensConstant_eq_sum u.isUnit]
    _ = (∑ ψ : DirichletCharacter ℂ q, residueSpectralValue ψ *
          ∑ u : (ZMod q)ˣ, (ψ⁻¹ * χ) u) / q.totient := by
        simp_rw [div_mul_eq_mul_div, ← sum_div, sum_mul, mul_sum]
        rw [sum_comm]
        congr 1
        exact sum_congr rfl fun ψ _ => sum_congr rfl fun u _ => by rw [← hterm]; ring
    _ = residueSpectralValue χ := by
        simp_rw [sum_units_char, inv_mul_eq_one, mul_ite, mul_zero]
        rw [sum_ite_eq']
        simp only [mem_univ, if_true]
        field_simp

omit [NeZero q] in
/-- On units, `χ(s⁻¹) = conj χ(s)`. -/
theorem char_unit_inv (χ : DirichletCharacter ℂ q) (s : (ZMod q)ˣ) :
    χ ↑(s⁻¹) = conj (χ s) := by
  rw [← char_inv_apply_eq_conj, MulChar.inv_apply, Ring.inverse_unit]

/-- **Diagonalization of the residue finite part**: every character is an eigenvector,
`Σ_b (c_{a⁻¹b} + c_{b⁻¹a}) χ(b) = 2 Re β_χ · χ(a)` for every unit `a`. -/
theorem sum_residueFinitePart_mul_char (χ : DirichletCharacter ℂ q) (a : (ZMod q)ˣ) :
    ∑ b : (ZMod q)ˣ, ((classMertensConstant q ↑(a⁻¹ * b) +
        classMertensConstant q ↑(b⁻¹ * a) : ℝ) : ℂ) * χ b =
      ((2 * (residueSpectralValue χ).re : ℝ) : ℂ) * χ a := by
  have hA := sum_classMertensConstant_mul_char χ
  -- `b = a r`: the first sum is `χ(a) β_χ`
  have h1 : ∑ b : (ZMod q)ˣ, ((classMertensConstant q ↑(a⁻¹ * b) : ℝ) : ℂ) * χ b =
      χ a * residueSpectralValue χ := by
    rw [← hA, mul_sum]
    calc ∑ b : (ZMod q)ˣ, ((classMertensConstant q ↑(a⁻¹ * b) : ℝ) : ℂ) * χ b
        = ∑ r : (ZMod q)ˣ, ((classMertensConstant q ↑(a⁻¹ * (a * r)) : ℝ) : ℂ) * χ ↑(a * r) :=
          (Equiv.sum_comp (Equiv.mulLeft a)
            (fun b : (ZMod q)ˣ => ((classMertensConstant q ↑(a⁻¹ * b) : ℝ) : ℂ) * χ b)).symm
      _ = _ := sum_congr rfl fun r _ => by
          rw [inv_mul_cancel_left, Units.val_mul, map_mul]
          ring
  -- `b = a s⁻¹`: the second sum is `χ(a) conj β_χ`
  have h2 : ∑ b : (ZMod q)ˣ, ((classMertensConstant q ↑(b⁻¹ * a) : ℝ) : ℂ) * χ b =
      χ a * conj (residueSpectralValue χ) := by
    rw [← hA, map_sum, mul_sum]
    calc ∑ b : (ZMod q)ˣ, ((classMertensConstant q ↑(b⁻¹ * a) : ℝ) : ℂ) * χ b
        = ∑ s : (ZMod q)ˣ, ((classMertensConstant q ↑((a * s⁻¹)⁻¹ * a) : ℝ) : ℂ) *
            χ ↑(a * s⁻¹) :=
          (Equiv.sum_comp ((Equiv.inv (ZMod q)ˣ).trans (Equiv.mulLeft a))
            (fun b : (ZMod q)ˣ => ((classMertensConstant q ↑(b⁻¹ * a) : ℝ) : ℂ) * χ b)).symm
      _ = _ := sum_congr rfl fun s _ => by
          have hs : (a * s⁻¹)⁻¹ * a = s := by group
          rw [hs, Units.val_mul, map_mul, char_unit_inv, map_mul, Complex.conj_ofReal]
          ring
  simp_rw [Complex.ofReal_add, add_mul]
  rw [sum_add_distrib, h1, h2, ← mul_add, Complex.add_conj]
  push_cast
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
