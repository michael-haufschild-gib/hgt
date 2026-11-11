import GaloisForLFunctions.FamilyContinuationTheory.TheSexticSymbolsAreReciprocalUpToTheQuadraticPhase
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The quadratic phase is a bicharacter modulo four

`Γ(c) = |c|⁻¹ Σ_{x mod c} ψ_c(x²)` is `(1 + i^{−b} + i^a + i^{b−a})/2` for `c = a + bω`
(`normalizedQuadraticTraceGauss_formula`), so `2Γ(c)` is the Gaussian integer
`T(a, b) = 1 + i^{−b} + i^a + i^{b−a}` with `a, b` read modulo four (`twoGamma`,
`two_mul_gamma_eq`). On the odd classes (`c ∉ (2)`) the following finite identities hold, each
checked over the coordinates modulo four:

* `gamma_ne_zero`: `Γ(c) ≠ 0`, and `Γ(c)⁴ = 1` (`gamma_pow_four`);
* `gamma_mul_sq`: `Γ(cd²) = Γ(c)`;
* `gamma_cocycle`: `Γ(cde) Γ(c) Γ(d) Γ(e) = Γ(cd) Γ(ce) Γ(de)`;
* `gamma_mul_sq_eq`: `Γ(cd)² = Γ(c)² Γ(d)²`.

Hence `r(c, d) = Γ(cd)/(Γ(c)Γ(d))` is a symmetric `±1`-valued bicharacter of the odd residues
modulo four (`quadraticPhase_mul_left`, `quadraticPhase_sq`): by sextic reciprocity it is the
cross phase `χ_q(p)/χ_p(q)` of two good primes, and its bimultiplicativity makes the product of the
pair phases of two indices a function of their residue classes.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.Eisenstein.Coordinates

/-! ### The model over `ZMod 4` -/

/-- `i^k` for `k` modulo four, in `ℤ[i]`. -/
def ipow (k : ZMod 4) : GaussianInt := (⟨0, 1⟩ : GaussianInt) ^ k.val

/-- `2Γ` at the coordinates `(a, b)` modulo four. -/
def twoGamma (a b : ZMod 4) : GaussianInt := 1 + ipow (-b) + ipow a + ipow (b - a)

/-- The coordinates of a product, `(a + bω)(c + dω)`. -/
def mulFst (a b c d : ZMod 4) : ZMod 4 := a * c - b * d

def mulSnd (a b c d : ZMod 4) : ZMod 4 := a * d + b * c - b * d

/-- Odd coordinates: not both even. -/
abbrev oddCoord (a b : ZMod 4) : Prop := ¬ (2 ∣ a.val ∧ 2 ∣ b.val)

theorem twoGamma_ne_zero : ∀ a b : ZMod 4, oddCoord a b → twoGamma a b ≠ 0 := by decide

theorem twoGamma_pow_four : ∀ a b : ZMod 4, oddCoord a b → twoGamma a b ^ 4 = 16 := by
  decide

theorem twoGamma_mul_sq : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    twoGamma (mulFst a b (mulFst c d c d) (mulSnd c d c d))
      (mulSnd a b (mulFst c d c d) (mulSnd c d c d)) = twoGamma a b := by
  decide

theorem twoGamma_sq_mul : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    4 * twoGamma (mulFst a b c d) (mulSnd a b c d) ^ 2 = twoGamma a b ^ 2 * twoGamma c d ^ 2 := by
  decide

theorem twoGamma_cocycle : ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ZMod 4, oddCoord a₁ b₁ →
    oddCoord a₂ b₂ → oddCoord a₃ b₃ →
    twoGamma (mulFst (mulFst a₁ b₁ a₂ b₂) (mulSnd a₁ b₁ a₂ b₂) a₃ b₃)
        (mulSnd (mulFst a₁ b₁ a₂ b₂) (mulSnd a₁ b₁ a₂ b₂) a₃ b₃) *
      twoGamma a₁ b₁ * twoGamma a₂ b₂ * twoGamma a₃ b₃ =
    2 * twoGamma (mulFst a₁ b₁ a₂ b₂) (mulSnd a₁ b₁ a₂ b₂) *
      twoGamma (mulFst a₁ b₁ a₃ b₃) (mulSnd a₁ b₁ a₃ b₃) *
        twoGamma (mulFst a₂ b₂ a₃ b₃) (mulSnd a₂ b₂ a₃ b₃) := by
  decide

/-! ### The bridge to `Γ` -/

/-- `i^k = i^{k mod 4}`. -/
theorem I_zpow_eq_ipow (k : ℤ) : Complex.I ^ k = GaussianInt.toComplex (ipow k) := by
  rw [ipow, map_pow, show GaussianInt.toComplex ⟨0, 1⟩ = Complex.I by
    simp [GaussianInt.toComplex_def], ← zpow_natCast, ZMod.val_intCast]
  have hk : k = 4 * (k / 4) + k % ((4 : ℕ) : ℤ) := by omega
  conv_lhs => rw [hk]
  rw [zpow_add₀ Complex.I_ne_zero, zpow_mul, show Complex.I ^ (4 : ℤ) = 1 by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, Complex.I_pow_four],
    one_zpow, one_mul]

/-- `2Γ(a + bω)` is the Gaussian integer `T(a mod 4, b mod 4)`. -/
theorem two_mul_gamma_eq (a b : ℤ) (hc : eval a b ≠ 0) :
    2 * normalizedQuadraticTraceGauss (eval a b) hc =
      GaussianInt.toComplex (twoGamma (a : ZMod 4) (b : ZMod 4)) := by
  rw [normalizedQuadraticTraceGauss_formula, twoGamma, map_add, map_add, map_add, map_one,
    I_zpow_eq_ipow, I_zpow_eq_ipow, I_zpow_eq_ipow]
  push_cast
  ring

/-- Oddness of `a + bω` in coordinates. -/
theorem oddCoord_of_not_mem (a b : ℤ) (h2 : eval a b ∉ Ideal.span {(2 : O)}) :
    oddCoord (a : ZMod 4) (b : ZMod 4) := by
  rintro ⟨ha, hb⟩
  obtain ⟨a', rfl⟩ : (2 : ℤ) ∣ a := by have := ZMod.val_intCast (n := 4) a; omega
  obtain ⟨b', rfl⟩ : (2 : ℤ) ∣ b := by have := ZMod.val_intCast (n := 4) b; omega
  apply h2
  rw [Ideal.mem_span_singleton]
  refine ⟨eval a' b', ?_⟩
  simp only [eval]
  push_cast
  ring

end GaloisForLFunctions.FamilyContinuationTheory
