import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.GaussSum

/-!
# Torsion characteristics: where `+` and `×` meet

The characteristic circle `ℝ/ℤ` of the theta surface has torsion points `j/N`. Over them the
fibres of the surface — the completed even Hurwitz functions at `j/N` — combine into the
completed L-functions of functions on `ℤ/Nℤ`, and Serre duality of the fibres becomes the finite
Fourier transform of `ℤ/Nℤ` (Mathlib: `ZMod.completedLFunction_def_even`,
`ZMod.completedLFunction_one_sub_even`). The additive characters `e(jk/N)` and the multiplicative
characters `χ` are exchanged by this transform, and the exchange coefficient is the Gauss sum.

* **Square-root cancellation from counting** (`normSq_gaussSum_eq_card`). For a nontrivial
  multiplicative character and a primitive additive character of a finite field `F`,
  `|τ(χ, ψ)|² = |F|`: a sum of `|F|` unit numbers has modulus exactly `√|F|`. The proof is
  orthogonality, i.e. counting the solutions of `x = y`; no estimate enters.
* **The sign of the functional equation is a count** (`norm_rootNumber_eq_one`). For a nontrivial
  Dirichlet character modulo a prime `p`, the root number `τ(χ) / (i^ε √p)` of
  `Λ(1 − s, χ) = p^{s − 1/2} W(χ) Λ(s, χ̄)` (Mathlib: `IsPrimitive.completedLFunction_one_sub`) has
  modulus one.

At each finite level the coupling of `+` and `×` is exact and square-root sized, and it is proved
by counting. What the walls ask for is the same coupling for the arithmetic point itself — the
signed sums `Σ μ(n)`, `Σ Λ(n) − x` — uniformly over all levels, where no finite group computes it.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- **Square-root cancellation from counting**: `|τ(χ, ψ)|² = |F|`. -/
theorem normSq_gaussSum_eq_card {F : Type*} [Field F] [Fintype F] {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) : Complex.normSq (gaussSum χ ψ) = Fintype.card F := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have h' : (Complex.normSq (gaussSum χ ψ) : ℂ) = Fintype.card F := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    exact h
  exact_mod_cast h'

/-- The Gauss sum of a nontrivial character has modulus `√|F|`. -/
theorem norm_gaussSum_eq_sqrt_card {F : Type*} [Field F] [Fintype F] {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) : ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  rw [← normSq_gaussSum_eq_card hχ hψ, Complex.norm_def]

/-- **The root number of a nontrivial Dirichlet character modulo a prime is a unit.** -/
theorem norm_rootNumber_eq_one {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    ‖DirichletCharacter.rootNumber χ‖ = 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hτ : ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ = Real.sqrt p := by
    rw [norm_gaussSum_eq_sqrt_card hχ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  have hroot : ‖((p : ℂ) ^ (1 / 2 : ℂ))‖ = Real.sqrt p := by
    rw [Complex.norm_natCast_cpow_of_pos (Fact.out : p.Prime).pos]
    simp [Real.sqrt_eq_rpow]
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, hτ, norm_pow, Complex.norm_I, one_pow,
    div_one, hroot,
    div_self (Real.sqrt_pos.mpr hp).ne']

end GaloisForLFunctions.ArithmeticEffectivityTheory
