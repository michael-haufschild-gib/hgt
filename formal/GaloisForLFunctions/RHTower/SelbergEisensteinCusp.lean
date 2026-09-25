import GaloisForLFunctions.RHTower.SelbergPoincareBounded
import GaloisForLFunctions.RHTower.SelbergPoincareFourier

open UpperHalfPlane Complex
open scoped MatrixGroups

/-!
# The `Γ(N)` Eisenstein series at an arbitrary cusp `σ∞`

`E_∞(σz, s) = Σ_{γ ∈ Γ∞\Γ(N)} Im(γσz)^s` is the lattice sum of `(y/|cz+d|²)^s` over the bottom rows of `γσ`
(`poincare_smul_eq`); these rows are injective in the coset (`botσ_injective`) and are exactly the admissible rows of
`Γ(N)` multiplied by `σ` (`range_botσ`), i.e. the primitive rows `≡ (σ₁₀, σ₁₁) (mod N)`. This is the starting point
for the constant terms `φ_{∞a}(s)` at every cusp, needed in the Maass–Selberg relation for `Γ(N)`.
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCusp
open GaloisForLFunctions.RHTower.SelbergPoincare GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergPoincareBounded CongruenceSubgroup

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- Bottom rows of the coset representatives translated by `σ`. -/
noncomputable def botσ (q : Cosets N) : ℤ × ℤ :=
  ((((Quotient.out q : Gamma N) : SL(2, ℤ)) * σ) 1 0, (((Quotient.out q : Gamma N) : SL(2, ℤ)) * σ) 1 1)

omit [NeZero N] in
theorem botσ_injective : Function.Injective (botσ N σ) := by
  intro q q' h
  simp only [botσ, Prod.mk.injEq] at h
  obtain ⟨e0, e1⟩ := row_eq_of_mul h.1 h.2
  apply bottom_injective N
  ext i; fin_cases i <;> simp [bottom, e0, e1]

/-- The Eisenstein summand `(y/|cz+d|²)^s` as a function of the bottom row. -/
noncomputable def esum (s : ℂ) (z : ℍ) (p : ℤ × ℤ) : ℂ :=
  ((z.im / Complex.normSq ((p.1 : ℂ) * (z : ℂ) + p.2) : ℝ) : ℂ) ^ s

theorem termQ_smul (s : ℂ) (z : ℍ) (q : Cosets N) :
    termQ N 0 s (σ • z) q = esum s z (botσ N σ q) := by
  have hq : termQ N 0 s (σ • z) q = term N 0 s (σ • z) (Quotient.out q) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [hq]
  unfold term esum botσ
  rw [← mul_smul]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, mul_one]
  congr 2
  rw [ModularGroup.im_smul_eq_div_normSq]
  rfl

/-- **The Eisenstein series at the cusp `σ∞`** as a lattice sum over the `σ`-translated admissible rows. -/
theorem poincare_smul_eq (s : ℂ) (z : ℍ) :
    poincare N 0 s (σ • z) = ∑' p : ℤ × ℤ, (Set.range (botσ N σ)).indicator (esum s z) p := by
  unfold poincare
  simp_rw [termQ_smul N σ s z]
  rw [← tsum_range (esum s z) (botσ_injective N σ), tsum_subtype]

/-- Right multiplication of a row vector by `σ`. -/
def rowMul (p : ℤ × ℤ) : ℤ × ℤ := (p.1 * σ 0 0 + p.2 * σ 1 0, p.1 * σ 0 1 + p.2 * σ 1 1)

theorem botσ_eq (q : Cosets N) : botσ N σ q = rowMul σ (bot N q) := by
  simp [botσ, rowMul, bot, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The rows at the cusp `σ∞`** are the admissible rows of `Γ(N)` multiplied by `σ`. -/
theorem range_botσ : Set.range (botσ N σ) = rowMul σ '' adm N := by
  rw [← range_bot N, ← Set.range_comp]
  congr 1; funext q; exact botσ_eq N σ q

end GaloisForLFunctions.RHTower.SelbergEisensteinCusp
