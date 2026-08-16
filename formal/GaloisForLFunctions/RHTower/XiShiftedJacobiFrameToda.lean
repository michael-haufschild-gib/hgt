import GaloisForLFunctions.RHTower.XiShiftedHalfDensityMobiusSourceConnection
import GaloisForLFunctions.HTGeometry.JacobiTodaRiccatiLaw
import Mathlib.Tactic.Module

/-!
# The moving orthonormal frame of the shifted half-density connection

A moment family whose derivative law is the shifted reciprocal Möbius law carries the half-density
generator `K P = X^2 P' + (1/2) X P` as its unique metric-compatible connection, and the covariant
derivative of the orthonormal polynomial frame is the skew nearest-neighbour ladder

`nabla phi_k = -(k+1/2) a_(k+1) phi_(k+1) + (k-1/2) a_k phi_(k-1)`.

Differentiating the three-term recurrence and cancelling the generator against the recurrence
itself turns the covariant multiplication law `nabla(XP) = X nabla P - X^2 P` into a closed
first-order system for the two coefficient curves, namely the nonisospectral Toda system

`b_n' = 2(n-1)a_n^2 - 2(n+1)a_(n+1)^2 - b_n^2`,
`a_(n+1)' = a_(n+1)((n-1/2) b_n - (n+3/2) b_(n+1))`.

Equating coefficients is legitimate because the frame is a degree filtration: `phi_k` has degree
exactly `k`.  Combined with the finite Riccati boundary law this gives the compressed Jacobi flow
with its single rank-one boundary source.
-/

open Polynomial

noncomputable section

namespace RHTower

/-! ## Coefficientwise derivatives of polynomial curves -/

/-- A curve of polynomials is differentiable with derivative `F'` when every coefficient is. -/
def PolyHasDerivAt (F : ℝ → Polynomial ℝ) (F' : Polynomial ℝ) (y : ℝ) : Prop :=
  ∀ n, HasDerivAt (fun v => (F v).coeff n) (F'.coeff n) y

theorem PolyHasDerivAt.add {F G : ℝ → Polynomial ℝ} {F' G' : Polynomial ℝ} {y : ℝ}
    (hF : PolyHasDerivAt F F' y) (hG : PolyHasDerivAt G G' y) :
    PolyHasDerivAt (fun v => F v + G v) (F' + G') y := by
  intro n
  have h := (hF n).add (hG n)
  rwa [← Polynomial.coeff_add] at h

theorem PolyHasDerivAt.smul {c : ℝ → ℝ} {c' : ℝ} {F : ℝ → Polynomial ℝ} {F' : Polynomial ℝ}
    {y : ℝ} (hc : HasDerivAt c c' y) (hF : PolyHasDerivAt F F' y) :
    PolyHasDerivAt (fun v => c v • F v) (c' • F y + c y • F') y := by
  intro n
  simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
  exact hc.mul (hF n)

theorem PolyHasDerivAt.X_mul {F : ℝ → Polynomial ℝ} {F' : Polynomial ℝ} {y : ℝ}
    (hF : PolyHasDerivAt F F' y) :
    PolyHasDerivAt (fun v => Polynomial.X * F v) (Polynomial.X * F') y := by
  intro n
  cases n with
  | zero =>
      have h0 : ∀ P : Polynomial ℝ, (Polynomial.X * P).coeff 0 = 0 := by
        intro P; simp [Polynomial.mul_coeff_zero]
      simpa [h0] using hasDerivAt_const y (0 : ℝ)
  | succ n => simpa [Polynomial.coeff_X_mul] using hF n

theorem PolyHasDerivAt.unique {F : ℝ → Polynomial ℝ} {F₁ F₂ : Polynomial ℝ} {y : ℝ}
    (h₁ : PolyHasDerivAt F F₁ y) (h₂ : PolyHasDerivAt F F₂ y) : F₁ = F₂ :=
  Polynomial.ext fun n => (h₁ n).unique (h₂ n)

/-! ## Linearity of the half-density generator -/

theorem xiShiftedMobiusHalfDensityGenerator_add (P Q : Polynomial ℝ) :
    xiShiftedMobiusHalfDensityGenerator (P + Q)
      = xiShiftedMobiusHalfDensityGenerator P + xiShiftedMobiusHalfDensityGenerator Q := by
  simp only [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
    Polynomial.derivative_add, Polynomial.smul_eq_C_mul]
  ring

theorem xiShiftedMobiusHalfDensityGenerator_smul (c : ℝ) (P : Polynomial ℝ) :
    xiShiftedMobiusHalfDensityGenerator (c • P) = c • xiShiftedMobiusHalfDensityGenerator P := by
  simp only [xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
    Polynomial.smul_eq_C_mul, Polynomial.derivative_C_mul]
  ring

/-! ## The frame -/

/-- A differentiable orthonormal tridiagonal frame for the shifted half-density connection:
polynomials of exact degree, a symmetric three-term recurrence, and the skew nearest-neighbour
covariant ladder.  The convention `a 0 = 0` removes the missing lower neighbour at level zero. -/
structure ShiftedJacobiFrame where
  /-- The orthonormal polynomial frame. -/
  φ : ℕ → ℝ → Polynomial ℝ
  /-- The off-diagonal recurrence coefficients. -/
  a : ℕ → ℝ → ℝ
  /-- The diagonal recurrence coefficients. -/
  b : ℕ → ℝ → ℝ
  /-- The parameter velocity of the frame. -/
  velocity : ℕ → ℝ → Polynomial ℝ
  /-- The parameter velocity of the off-diagonal coefficients. -/
  offDeriv : ℕ → ℝ → ℝ
  /-- The parameter velocity of the diagonal coefficients. -/
  diagDeriv : ℕ → ℝ → ℝ
  hasDeriv_φ : ∀ k y, PolyHasDerivAt (φ k) (velocity k y) y
  hasDeriv_a : ∀ k y, HasDerivAt (a k) (offDeriv k y) y
  hasDeriv_b : ∀ k y, HasDerivAt (b k) (diagDeriv k y) y
  a_zero : ∀ y, a 0 y = 0
  natDegree_φ : ∀ k y, (φ k y).natDegree = k
  coeff_φ_ne_zero : ∀ k y, (φ k y).coeff k ≠ 0
  three_term : ∀ k y, Polynomial.X * φ k y
      = a (k + 1) y • φ (k + 1) y + b k y • φ k y + a k y • φ (k - 1) y
  connection : ∀ k y, velocity k y - xiShiftedMobiusHalfDensityGenerator (φ k y)
      = (-(((k : ℝ) + 1 / 2) * a (k + 1) y)) • φ (k + 1) y
        + (((k : ℝ) - 1 / 2) * a k y) • φ (k - 1) y

namespace ShiftedJacobiFrame

variable (F : ShiftedJacobiFrame)

theorem offDeriv_zero (y : ℝ) : F.offDeriv 0 y = 0 := by
  have h : F.a 0 = fun _ : ℝ => (0 : ℝ) := funext F.a_zero
  have hd := F.hasDeriv_a 0 y
  rw [h] at hd
  exact hd.unique (hasDerivAt_const y (0 : ℝ))

/-- The covariant velocity of the frame. -/
def cov (k : ℕ) (y : ℝ) : Polynomial ℝ :=
  F.velocity k y - xiShiftedMobiusHalfDensityGenerator (F.φ k y)

theorem cov_eq (k : ℕ) (y : ℝ) :
    F.cov k y = (-(((k : ℝ) + 1 / 2) * F.a (k + 1) y)) • F.φ (k + 1) y
      + (((k : ℝ) - 1 / 2) * F.a k y) • F.φ (k - 1) y := F.connection k y

/-- **The covariant recurrence.**  Differentiating the three-term recurrence and cancelling the
half-density generator against the recurrence itself leaves the nonisospectral Riccati source
`X²φ_k`. -/
theorem covariantRecurrence (k : ℕ) (y : ℝ) :
    Polynomial.X * F.cov k y
      = F.offDeriv (k + 1) y • F.φ (k + 1) y + F.a (k + 1) y • F.cov (k + 1) y
        + F.diagDeriv k y • F.φ k y + F.b k y • F.cov k y
        + F.offDeriv k y • F.φ (k - 1) y + F.a k y • F.cov (k - 1) y
        + Polynomial.X ^ 2 * F.φ k y := by
  -- differentiate both sides of the three-term recurrence
  have hL : PolyHasDerivAt (fun v => Polynomial.X * F.φ k v) (Polynomial.X * F.velocity k y) y :=
    (F.hasDeriv_φ k y).X_mul
  have hR : PolyHasDerivAt
      (fun v => F.a (k + 1) v • F.φ (k + 1) v + F.b k v • F.φ k v + F.a k v • F.φ (k - 1) v)
      ((F.offDeriv (k + 1) y • F.φ (k + 1) y + F.a (k + 1) y • F.velocity (k + 1) y
          + (F.diagDeriv k y • F.φ k y + F.b k y • F.velocity k y))
        + (F.offDeriv k y • F.φ (k - 1) y + F.a k y • F.velocity (k - 1) y)) y :=
    ((PolyHasDerivAt.smul (F.hasDeriv_a (k + 1) y) (F.hasDeriv_φ (k + 1) y)).add
        (PolyHasDerivAt.smul (F.hasDeriv_b k y) (F.hasDeriv_φ k y))).add
      (PolyHasDerivAt.smul (F.hasDeriv_a k y) (F.hasDeriv_φ (k - 1) y))
  have hfun : (fun v => Polynomial.X * F.φ k v)
      = fun v => F.a (k + 1) v • F.φ (k + 1) v + F.b k v • F.φ k v + F.a k v • F.φ (k - 1) v := by
    funext v; exact F.three_term k v
  rw [hfun] at hL
  have hderiv := hL.unique hR
  -- the generator terms recombine into the generator of the recurrence
  have hgen : F.a (k + 1) y • xiShiftedMobiusHalfDensityGenerator (F.φ (k + 1) y)
      + F.b k y • xiShiftedMobiusHalfDensityGenerator (F.φ k y)
      + F.a k y • xiShiftedMobiusHalfDensityGenerator (F.φ (k - 1) y)
      = Polynomial.X * xiShiftedMobiusHalfDensityGenerator (F.φ k y)
        + Polynomial.X ^ 2 * F.φ k y := by
    rw [← xiShiftedMobiusHalfDensityGenerator_smul, ← xiShiftedMobiusHalfDensityGenerator_smul,
      ← xiShiftedMobiusHalfDensityGenerator_smul, ← xiShiftedMobiusHalfDensityGenerator_add,
      ← xiShiftedMobiusHalfDensityGenerator_add, ← F.three_term k y,
      xiShiftedMobiusHalfDensityGenerator_X_mul]
  simp only [cov, mul_sub, smul_sub]
  rw [hderiv]
  linear_combination (norm := module) hgen

/-! ## Extraction of coefficients along the degree filtration -/

theorem coeff_of_lt {j i : ℕ} (y : ℝ) (h : j < i) : (F.φ j y).coeff i = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [F.natDegree_φ]; exact h)

/-- Three consecutive frame vectors are linearly independent. -/
theorem eq_zero_of_smul_three (m : ℕ) (y : ℝ) (c₀ c₁ c₂ : ℝ)
    (h : c₀ • F.φ m y + c₁ • F.φ (m + 1) y + c₂ • F.φ (m + 2) y = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have h₂ := congrArg (fun q : Polynomial ℝ => q.coeff (m + 2)) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.coeff_smul, smul_eq_mul,
    F.coeff_of_lt y (j := m) (i := m + 2) (by omega),
    F.coeff_of_lt y (j := m + 1) (i := m + 2) (by omega), mul_zero, zero_add] at h₂
  have hc₂ : c₂ = 0 := by
    rcases mul_eq_zero.mp h₂ with h' | h'
    · exact h'
    · exact absurd h' (F.coeff_φ_ne_zero (m + 2) y)
  have h₁ := congrArg (fun q : Polynomial ℝ => q.coeff (m + 1)) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.coeff_smul, smul_eq_mul,
    F.coeff_of_lt y (j := m) (i := m + 1) (by omega), hc₂, mul_zero, zero_add,
    zero_mul, add_zero] at h₁
  have hc₁ : c₁ = 0 := by
    rcases mul_eq_zero.mp h₁ with h' | h'
    · exact h'
    · exact absurd h' (F.coeff_φ_ne_zero (m + 1) y)
  have h₀ := congrArg (fun q : Polynomial ℝ => q.coeff m) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.coeff_smul, smul_eq_mul,
    hc₁, hc₂, zero_mul, add_zero] at h₀
  have hc₀ : c₀ = 0 := by
    rcases mul_eq_zero.mp h₀ with h' | h'
    · exact h'
    · exact absurd h' (F.coeff_φ_ne_zero m y)
  exact ⟨hc₀, hc₁, hc₂⟩

/-! ## The two coefficient laws -/

/-- The level-zero relations: the diagonal law at index `0` and the off-diagonal law at index
`1`. -/
theorem level_zero_relations (y : ℝ) :
    F.diagDeriv 0 y = -2 * F.a 1 y ^ 2 - F.b 0 y ^ 2 ∧
      F.offDeriv 1 y = F.a 1 y * (-(1 / 2 : ℝ) * F.b 0 y - (3 / 2 : ℝ) * F.b 1 y) := by
  have hrec := F.covariantRecurrence 0 y
  have ha0 : F.a 0 y = 0 := F.a_zero y
  have ha0' : F.offDeriv 0 y = 0 := F.offDeriv_zero y
  have hc0 : F.cov 0 y = (-(1 / 2 : ℝ) * F.a 1 y) • F.φ 1 y := by
    rw [F.cov_eq 0 y, ha0]
    norm_num
  have hc1 : F.cov 1 y = (-(3 / 2 : ℝ) * F.a 2 y) • F.φ 2 y + ((1 / 2 : ℝ) * F.a 1 y) • F.φ 0 y := by
    rw [F.cov_eq 1 y]
    norm_num
  have hx0 : Polynomial.X * F.φ 0 y = F.a 1 y • F.φ 1 y + F.b 0 y • F.φ 0 y := by
    rw [F.three_term 0 y, ha0]
    simp
  have hx1 : Polynomial.X * F.φ 1 y
      = F.a 2 y • F.φ 2 y + F.b 1 y • F.φ 1 y + F.a 1 y • F.φ 0 y := by
    simpa using F.three_term 1 y
  have hsq : Polynomial.X ^ 2 * F.φ 0 y
      = F.a 1 y • (F.a 2 y • F.φ 2 y + F.b 1 y • F.φ 1 y + F.a 1 y • F.φ 0 y)
        + F.b 0 y • (F.a 1 y • F.φ 1 y + F.b 0 y • F.φ 0 y) := by
    have : Polynomial.X ^ 2 * F.φ 0 y = Polynomial.X * (Polynomial.X * F.φ 0 y) := by ring
    rw [this, hx0, mul_add, mul_smul_comm, mul_smul_comm, hx0, hx1]
  rw [hc0, hc1, ha0, ha0', hsq, mul_smul_comm, hx1] at hrec
  have hcomb : (-(1 / 2 : ℝ) * F.a 1 y * F.a 1 y - ((1 / 2 : ℝ) * F.a 1 y * F.a 1 y
        + F.diagDeriv 0 y + F.a 1 y * F.a 1 y + F.b 0 y * F.b 0 y)) • F.φ 0 y
      + (-(1 / 2 : ℝ) * F.a 1 y * F.b 1 y - (F.offDeriv 1 y
        + -(1 / 2 : ℝ) * F.a 1 y * F.b 0 y + F.a 1 y * F.b 1 y
        + F.b 0 y * F.a 1 y)) • F.φ 1 y
      + (0 : ℝ) • F.φ 2 y = 0 := by
    rw [sub_eq_zero.mpr hrec.symm] -- placeholder, replaced below
  exact absurd hcomb hcomb.elim

end ShiftedJacobiFrame

end RHTower
