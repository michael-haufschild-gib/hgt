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

theorem mulFst_cast (a b c d : ℤ) :
    mulFst (a : ZMod 4) (b : ZMod 4) (c : ZMod 4) (d : ZMod 4) = ((a * c - b * d : ℤ) : ZMod 4) := by
  simp only [mulFst]; push_cast; ring

theorem mulSnd_cast (a b c d : ℤ) :
    mulSnd (a : ZMod 4) (b : ZMod 4) (c : ZMod 4) (d : ZMod 4) =
      ((a * d + b * c - b * d : ℤ) : ZMod 4) := by
  simp only [mulSnd]; push_cast; ring

/-- `Γ(a + bω) = T(a mod 4, b mod 4)/2`, written with the dual average (no proof argument). -/
theorem fixedDualAverage_eval (a b : ℤ) :
    fixedDualAverage (eval a b) = GaussianInt.toComplex (twoGamma (a : ZMod 4) (b : ZMod 4)) / 2 := by
  rw [fixedDualAverage_formula, twoGamma, map_add, map_add, map_add, map_one, I_zpow_eq_ipow,
    I_zpow_eq_ipow, I_zpow_eq_ipow]
  push_cast
  ring

/-- Every element has integer coordinates. -/
theorem exists_eval (c : O) : ∃ a b : ℤ, c = eval a b := ⟨_, _, (eval_coords c).symm⟩

/-- **The cocycle.** For odd `c, d, e`: `Γ(cde) Γ(c) Γ(d) Γ(e) = Γ(cd) Γ(ce) Γ(de)`. -/
theorem gamma_cocycle {c d e : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)})
    (he : e ∉ Ideal.span {(2 : O)}) :
    fixedDualAverage (c * d * e) * fixedDualAverage c * fixedDualAverage d * fixedDualAverage e =
      fixedDualAverage (c * d) * fixedDualAverage (c * e) * fixedDualAverage (d * e) := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  obtain ⟨a₃, b₃, rfl⟩ := exists_eval e
  have h := congrArg GaussianInt.toComplex (twoGamma_cocycle (a₁ : ZMod 4) b₁ a₂ b₂ a₃ b₃
    (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd) (oddCoord_of_not_mem _ _ he))
  simp only [mulFst_cast, mulSnd_cast, map_mul, map_ofNat] at h
  simp only [eval_mul, fixedDualAverage_eval]
  linear_combination h / 16

/-- **The sign.** For odd `c, d`: `Γ(cd)² = Γ(c)² Γ(d)²`. -/
theorem gamma_mul_sq_eq {c d : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)}) :
    fixedDualAverage (c * d) ^ 2 = fixedDualAverage c ^ 2 * fixedDualAverage d ^ 2 := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  have h := congrArg GaussianInt.toComplex (twoGamma_sq_mul (a₁ : ZMod 4) b₁ a₂ b₂
    (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd))
  simp only [mulFst_cast, mulSnd_cast, map_mul, map_pow, map_ofNat] at h
  simp only [eval_mul, fixedDualAverage_eval]
  linear_combination h / 16

/-- **Nonvanishing** on the odd classes. -/
theorem gamma_ne_zero {c : O} (hc : c ∉ Ideal.span {(2 : O)}) : fixedDualAverage c ≠ 0 := by
  obtain ⟨a, b, rfl⟩ := exists_eval c
  rw [fixedDualAverage_eval, div_ne_zero_iff]
  refine ⟨fun h => twoGamma_ne_zero _ _ (oddCoord_of_not_mem _ _ hc) ?_, two_ne_zero⟩
  exact GaussianInt.toComplex_injective (by rw [h, map_zero])

/-- `Γ(c)⁴ = 1` on the odd classes. -/
theorem gamma_pow_four {c : O} (hc : c ∉ Ideal.span {(2 : O)}) : fixedDualAverage c ^ 4 = 1 := by
  obtain ⟨a, b, rfl⟩ := exists_eval c
  have h := congrArg GaussianInt.toComplex (twoGamma_pow_four (a : ZMod 4) b
    (oddCoord_of_not_mem _ _ hc))
  simp only [map_pow, map_ofNat] at h
  rw [fixedDualAverage_eval, div_pow, h]
  norm_num

/-- **Square classes.** For odd `c, d`: `Γ(cd²) = Γ(c)`. -/
theorem gamma_mul_sq {c d : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)}) :
    fixedDualAverage (c * d ^ 2) = fixedDualAverage c := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  have h := congrArg GaussianInt.toComplex (twoGamma_mul_sq (a₁ : ZMod 4) b₁ a₂ b₂
    (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd))
  simp only [mulFst_cast, mulSnd_cast] at h
  rw [sq, eval_mul, eval_mul, fixedDualAverage_eval, fixedDualAverage_eval, h]

/-! ### The bicharacter -/

/-- The quadratic reciprocity phase `r(c, d) = Γ(cd)/(Γ(c)Γ(d))`. -/
def quadraticPhase (c d : O) : ℂ :=
  fixedDualAverage (c * d) / (fixedDualAverage c * fixedDualAverage d)

theorem quadraticPhase_comm (c d : O) : quadraticPhase c d = quadraticPhase d c := by
  rw [quadraticPhase, quadraticPhase, mul_comm c d, mul_comm (fixedDualAverage c)]

theorem oddCoord_mul : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    oddCoord (mulFst a b c d) (mulSnd a b c d) := by
  decide

/-- Odd coordinates give an element outside `(2)`. -/
theorem not_mem_of_oddCoord (a b : ℤ) (h : oddCoord (a : ZMod 4) (b : ZMod 4)) :
    eval a b ∉ Ideal.span {(2 : O)} := by
  intro hmem
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hmem
  obtain ⟨a', b', rfl⟩ := exists_eval z
  have h2 : eval (2 * a') (2 * b') = eval a b := by
    rw [← hz]
    simp only [eval]
    push_cast
    ring
  obtain ⟨ha, hb⟩ := unique_coordinates h2
  apply h
  constructor
  · have := ZMod.val_intCast (n := 4) a
    omega
  · have := ZMod.val_intCast (n := 4) b
    omega

/-- A product of odd elements is odd. -/
theorem odd_mul {c d : O} (hc : c ∉ Ideal.span {(2 : O)}) (hd : d ∉ Ideal.span {(2 : O)}) :
    c * d ∉ Ideal.span {(2 : O)} := by
  obtain ⟨a₁, b₁, rfl⟩ := exists_eval c
  obtain ⟨a₂, b₂, rfl⟩ := exists_eval d
  rw [eval_mul]
  apply not_mem_of_oddCoord
  have h := oddCoord_mul _ _ _ _ (oddCoord_of_not_mem _ _ hc) (oddCoord_of_not_mem _ _ hd)
  rwa [mulFst_cast, mulSnd_cast] at h

/-- `r` is multiplicative in its first argument on the odd classes. -/
theorem quadraticPhase_mul_left {c d e : O} (hc : c ∉ Ideal.span {(2 : O)})
    (hd : d ∉ Ideal.span {(2 : O)}) (he : e ∉ Ideal.span {(2 : O)}) :
    quadraticPhase (c * d) e = quadraticPhase c e * quadraticPhase d e := by
  have h := gamma_cocycle hc hd he
  have h1 := gamma_ne_zero hc
  have h2 := gamma_ne_zero hd
  have h3 := gamma_ne_zero he
  have h12 := gamma_ne_zero (odd_mul hc hd)
  unfold quadraticPhase
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h12 h3)
    (mul_ne_zero (mul_ne_zero h1 h3) (mul_ne_zero h2 h3))]
  linear_combination fixedDualAverage e * h

/-- `r` is a sign on the odd classes. -/
theorem quadraticPhase_sq {c d : O} (hc : c ∉ Ideal.span {(2 : O)})
    (hd : d ∉ Ideal.span {(2 : O)}) : quadraticPhase c d ^ 2 = 1 := by
  have h1 := gamma_ne_zero hc
  have h2 := gamma_ne_zero hd
  rw [quadraticPhase, div_pow, gamma_mul_sq_eq hc hd, mul_pow, div_self
    (mul_ne_zero (pow_ne_zero 2 h1) (pow_ne_zero 2 h2))]

end GaloisForLFunctions.FamilyContinuationTheory
