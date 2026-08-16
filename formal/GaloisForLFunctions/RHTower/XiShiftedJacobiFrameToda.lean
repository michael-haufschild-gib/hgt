import GaloisForLFunctions.RHTower.XiShiftedHalfDensityMobiusSourceConnection
import GaloisForLFunctions.HTGeometry.JacobiTodaRiccatiLaw
import GaloisForLFunctions.HTGeometry.MatrixInverseCurveDerivative

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

/-- The level-zero relations of the covariant recurrence. -/
theorem level_zero_relations (y : ℝ) :
    F.diagDeriv 0 y = -2 * F.a 1 y ^ 2 - F.b 0 y ^ 2 ∧
      F.offDeriv 1 y = F.a 1 y * (-(1 / 2 : ℝ) * F.b 0 y - (3 / 2 : ℝ) * F.b 1 y) := by
  have hrec := F.covariantRecurrence 0 y
  have ha0 : F.a 0 y = 0 := F.a_zero y
  have ha0' : F.offDeriv 0 y = 0 := F.offDeriv_zero y
  have hc0 : F.cov 0 y = (-(1 / 2 : ℝ) * F.a 1 y) • F.φ 1 y := by
    rw [F.cov_eq 0 y, ha0]
    norm_num
  have hc1 : F.cov 1 y
      = (-(3 / 2 : ℝ) * F.a 2 y) • F.φ 2 y + ((1 / 2 : ℝ) * F.a 1 y) • F.φ 0 y := by
    rw [F.cov_eq 1 y]
    norm_num
  have hx0 : Polynomial.X * F.φ 0 y = F.a 1 y • F.φ 1 y + F.b 0 y • F.φ 0 y := by
    rw [F.three_term 0 y, ha0]
    simp
  have hx1 : Polynomial.X * F.φ 1 y
      = F.a 2 y • F.φ 2 y + F.b 1 y • F.φ 1 y + F.a 1 y • F.φ 0 y := by
    have h := F.three_term 1 y
    norm_num at h
    exact h
  have hsq : Polynomial.X ^ 2 * F.φ 0 y
      = F.a 1 y • (F.a 2 y • F.φ 2 y + F.b 1 y • F.φ 1 y + F.a 1 y • F.φ 0 y)
        + F.b 0 y • (F.a 1 y • F.φ 1 y + F.b 0 y • F.φ 0 y) := by
    have h2 : Polynomial.X ^ 2 * F.φ 0 y = Polynomial.X * (Polynomial.X * F.φ 0 y) := by ring
    rw [h2, hx0, mul_add, mul_smul_comm, mul_smul_comm, hx0, hx1]
  rw [hc0, hc1, ha0, ha0', hsq, mul_smul_comm, hx1, zero_add, Nat.zero_sub] at hrec
  have hcomb : (-2 * F.a 1 y ^ 2 - F.diagDeriv 0 y - F.b 0 y ^ 2) • F.φ 0 y
      + (-F.offDeriv 1 y - (1 / 2 : ℝ) * F.a 1 y * F.b 0 y
          - (3 / 2 : ℝ) * F.a 1 y * F.b 1 y) • F.φ 1 y
      + (0 : ℝ) • F.φ 2 y = 0 := by
    linear_combination (norm := module) hrec
  obtain ⟨h0, h1, -⟩ := F.eq_zero_of_smul_three 0 y _ _ _ hcomb
  exact ⟨by linear_combination -h0, by linear_combination -h1⟩

/-- The level-`m+1` relations of the covariant recurrence: the off-diagonal law at indices
`m+1` and `m+2` and the diagonal law at index `m+1`. -/
theorem level_succ_relations (m : ℕ) (y : ℝ) :
    F.offDeriv (m + 1) y
        = F.a (m + 1) y * (((m : ℝ) - 1 / 2) * F.b m y - ((m : ℝ) + 3 / 2) * F.b (m + 1) y) ∧
      F.diagDeriv (m + 1) y
        = 2 * (m : ℝ) * F.a (m + 1) y ^ 2 - 2 * ((m : ℝ) + 2) * F.a (m + 2) y ^ 2
          - F.b (m + 1) y ^ 2 ∧
      F.offDeriv (m + 2) y
        = F.a (m + 2) y
            * (((m : ℝ) + 1 / 2) * F.b (m + 1) y - ((m : ℝ) + 5 / 2) * F.b (m + 2) y) := by
  have i1 : m + 1 - 1 = m := rfl
  have i2 : m + 2 - 1 = m + 1 := rfl
  have i3 : m + 1 + 1 = m + 2 := rfl
  have i4 : m + 2 + 1 = m + 3 := rfl
  have hrec := F.covariantRecurrence (m + 1) y
  rw [i1, i3] at hrec
  have hcm : F.cov m y = (-(((m : ℝ) + 1 / 2) * F.a (m + 1) y)) • F.φ (m + 1) y
      + (((m : ℝ) - 1 / 2) * F.a m y) • F.φ (m - 1) y := F.cov_eq m y
  have hcm1 : F.cov (m + 1) y = (-(((m : ℝ) + 3 / 2) * F.a (m + 2) y)) • F.φ (m + 2) y
      + (((m : ℝ) + 1 / 2) * F.a (m + 1) y) • F.φ m y := by
    have h := F.cov_eq (m + 1) y
    rw [i1, i3] at h
    rw [h]
    push_cast
    module
  have hcm2 : F.cov (m + 2) y = (-(((m : ℝ) + 5 / 2) * F.a (m + 3) y)) • F.φ (m + 3) y
      + (((m : ℝ) + 3 / 2) * F.a (m + 2) y) • F.φ (m + 1) y := by
    have h := F.cov_eq (m + 2) y
    rw [i2, i4] at h
    rw [h]
    push_cast
    module
  have hxm : Polynomial.X * F.φ m y
      = F.a (m + 1) y • F.φ (m + 1) y + F.b m y • F.φ m y + F.a m y • F.φ (m - 1) y :=
    F.three_term m y
  have hxm1 : Polynomial.X * F.φ (m + 1) y
      = F.a (m + 2) y • F.φ (m + 2) y + F.b (m + 1) y • F.φ (m + 1) y
        + F.a (m + 1) y • F.φ m y := by
    have h := F.three_term (m + 1) y
    rw [i1, i3] at h
    exact h
  have hxm2 : Polynomial.X * F.φ (m + 2) y
      = F.a (m + 3) y • F.φ (m + 3) y + F.b (m + 2) y • F.φ (m + 2) y
        + F.a (m + 2) y • F.φ (m + 1) y := by
    have h := F.three_term (m + 2) y
    rw [i2, i4] at h
    exact h
  have hsq : Polynomial.X ^ 2 * F.φ (m + 1) y
      = F.a (m + 2) y • (F.a (m + 3) y • F.φ (m + 3) y + F.b (m + 2) y • F.φ (m + 2) y
          + F.a (m + 2) y • F.φ (m + 1) y)
        + F.b (m + 1) y • (F.a (m + 2) y • F.φ (m + 2) y + F.b (m + 1) y • F.φ (m + 1) y
          + F.a (m + 1) y • F.φ m y)
        + F.a (m + 1) y • (F.a (m + 1) y • F.φ (m + 1) y + F.b m y • F.φ m y
          + F.a m y • F.φ (m - 1) y) := by
    have h2 : Polynomial.X ^ 2 * F.φ (m + 1) y
        = Polynomial.X * (Polynomial.X * F.φ (m + 1) y) := by ring
    rw [h2, hxm1, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      hxm, hxm1, hxm2]
  rw [hcm, hcm1, hcm2, hsq, mul_add, mul_smul_comm, mul_smul_comm, hxm, hxm2] at hrec
  have hcomb : (((m : ℝ) - 1 / 2) * F.a (m + 1) y * F.b m y
        - ((m : ℝ) + 3 / 2) * F.a (m + 1) y * F.b (m + 1) y - F.offDeriv (m + 1) y) • F.φ m y
      + (2 * (m : ℝ) * F.a (m + 1) y ^ 2 - 2 * ((m : ℝ) + 2) * F.a (m + 2) y ^ 2
          - F.diagDeriv (m + 1) y - F.b (m + 1) y ^ 2) • F.φ (m + 1) y
      + (((m : ℝ) + 1 / 2) * F.a (m + 2) y * F.b (m + 1) y
          - ((m : ℝ) + 5 / 2) * F.a (m + 2) y * F.b (m + 2) y
          - F.offDeriv (m + 2) y) • F.φ (m + 2) y = 0 := by
    linear_combination (norm := module) hrec
  obtain ⟨h0, h1, h2⟩ := F.eq_zero_of_smul_three m y _ _ _ hcomb
  refine ⟨by linear_combination -h0, by linear_combination -h1, by linear_combination -h2⟩

/-- **The nonisospectral Toda system.**  The coefficient curves of a shifted half-density frame
satisfy the closed first-order system of the tridiagonal Riccati flow. -/
theorem jacobiTodaDeriv (y : ℝ) :
    GaloisForLFunctions.HTGeometry.JacobiTodaDeriv (fun k => F.a k y) (fun k => F.b k y)
      (fun k => F.offDeriv k y) (fun k => F.diagDeriv k y) := by
  refine ⟨F.a_zero y, ?_, fun n => (F.level_succ_relations n y).1⟩
  intro n
  cases n with
  | zero =>
      have h := (F.level_zero_relations y).1
      simp only [F.a_zero y, Nat.cast_zero, zero_add]
      linarith [h]
  | succ m =>
      have h := (F.level_succ_relations m y).2.1
      have hidx : m + 1 + 1 = m + 2 := rfl
      simp only [hidx]
      push_cast
      linarith [h]

section Compression

open GaloisForLFunctions.HTGeometry
open scoped _root_.Matrix

/-- The `m+1`-level Jacobi compression of the frame at parameter `y`. -/
def jacobiLevel (m : ℕ) (y : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  jacobiCompression (fun k => F.a k y) (fun k => F.b k y) (m + 1)

/-- The `m+1`-level connection compression of the frame at parameter `y`. -/
def connectionLevel (m : ℕ) (y : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  connectionCompression (fun k => F.a k y) (m + 1)

/-- The parameter velocity of the `m+1`-level Jacobi compression. -/
def jacobiVelocityLevel (m : ℕ) (y : ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  jacobiCompression (fun k => F.offDeriv k y) (fun k => F.diagDeriv k y) (m + 1)

/-- The boundary port of the `m+1`-level compression: the last basis vector. -/
def boundaryUnit (m : ℕ) : Fin (m + 1) → ℝ := fun i => if (i : ℕ) = m then 1 else 0

theorem jacobiLevel_transpose (m : ℕ) (y : ℝ) : (F.jacobiLevel m y)ᵀ = F.jacobiLevel m y :=
  jacobiCompression_symm _ _ _

theorem connectionLevel_transpose (m : ℕ) (y : ℝ) :
    (F.connectionLevel m y)ᵀ = -F.connectionLevel m y :=
  connectionCompression_skew _ _

/-- The Jacobi compression of a frame is an entrywise differentiable matrix curve, with the
compression of the coefficient velocities as its derivative. -/
theorem matrixHasDerivAt_jacobiLevel (m : ℕ) (y : ℝ) :
    MatrixHasDerivAt (fun v => F.jacobiLevel m v) (F.jacobiVelocityLevel m y) y := by
  intro i j
  simp only [jacobiLevel, jacobiVelocityLevel, jacobiCompression, Matrix.of_apply, jacobiEntry]
  by_cases h1 : (i : ℕ) = (j : ℕ)
  · simp only [if_pos h1]
    exact F.hasDeriv_b _ y
  · simp only [if_neg h1]
    by_cases h2 : (i : ℕ) + 1 = (j : ℕ)
    · simp only [if_pos h2]
      exact F.hasDeriv_a _ y
    · simp only [if_neg h2]
      by_cases h3 : (j : ℕ) + 1 = (i : ℕ)
      · simp only [if_pos h3]
        exact F.hasDeriv_a _ y
      · simp only [if_neg h3]
        exact hasDerivAt_const y 0

/-- **(HJLG.2).**  The finite Jacobi compression of a shifted half-density frame moves by the
nonisospectral Riccati law with exactly one negative rank-one boundary source, of size
`2n a_n²` at the last diagonal entry. -/
theorem jacobiVelocityLevel_eq (m : ℕ) (y : ℝ) :
    F.jacobiVelocityLevel m y
      = F.jacobiLevel m y * F.connectionLevel m y - F.connectionLevel m y * F.jacobiLevel m y
        - F.jacobiLevel m y * F.jacobiLevel m y
        - (2 * ((m : ℝ) + 1) * F.a (m + 1) y ^ 2) •
            Matrix.vecMulVec (boundaryUnit m) (boundaryUnit m) :=
  jacobiCompression_deriv_eq_riccati _ _ _ _ (F.jacobiTodaDeriv y) m

/-- **(HJLG.3)--(HJLG.4).**  Where the Jacobi compression is invertible, the centered inverse
`J⁻¹ - y` moves by the same skew commutator plus a *positive* rank-one boundary square: the lost
boundary channel reappears as a controllability source in reciprocal hard coordinates. -/
theorem matrixHasDerivAt_centeredInverseLevel (m : ℕ) (y : ℝ)
    (hdet : (F.jacobiLevel m y).det ≠ 0) :
    MatrixHasDerivAt
      (fun v => (F.jacobiLevel m v)⁻¹ - v • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
      (((F.jacobiLevel m y)⁻¹ - y • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
            * F.connectionLevel m y
          - F.connectionLevel m y
            * ((F.jacobiLevel m y)⁻¹ - y • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
          + (2 * ((m : ℝ) + 1) * F.a (m + 1) y ^ 2) •
              Matrix.vecMulVec ((F.jacobiLevel m y)⁻¹ *ᵥ boundaryUnit m)
                ((F.jacobiLevel m y)⁻¹ *ᵥ boundaryUnit m)) y := by
  have hunit : IsUnit (F.jacobiLevel m y).det := isUnit_iff_ne_zero.mpr hdet
  refine matrixHasDerivAt_centeredInverse
    (J := fun v => F.jacobiLevel m v) (A := fun v => F.connectionLevel m v)
    (matrixHasDerivAt_inv (F.matrixHasDerivAt_jacobiLevel m y) hdet)
    (Matrix.nonsing_inv_mul _ hunit) (Matrix.mul_nonsing_inv _ hunit) ?_ ?_
  · rw [Matrix.transpose_nonsing_inv, F.jacobiLevel_transpose]
  · exact F.jacobiVelocityLevel_eq m y

/-- The transported boundary square of the `m+1`-level compression. -/
def boundaryGramianSource (m : ℕ) (O : ℝ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (v : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  (O v)ᵀ * ((2 * ((m : ℝ) + 1) * F.a (m + 1) v ^ 2) •
    Matrix.vecMulVec ((F.jacobiLevel m v)⁻¹ *ᵥ boundaryUnit m)
      ((F.jacobiLevel m v)⁻¹ *ᵥ boundaryUnit m)) * O v

/-- **(HJLG.5).**  Conjugating the centered inverse by the orthogonal flow of the skew connection
removes the commutator, so the conjugated centered inverse increases by the exact integral of the
transported boundary square. -/
theorem conjugatedCenteredInverse_increment (m : ℕ) (y₀ Y : ℝ)
    (O : ℝ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hO : ∀ v, MatrixHasDerivAt O (-(F.connectionLevel m v * O v)) v)
    (hdet : ∀ v ∈ Set.uIcc y₀ Y, (F.jacobiLevel m v).det ≠ 0)
    (hint : ∀ i j, IntervalIntegrable (fun v => F.boundaryGramianSource m O v i j)
      MeasureTheory.volume y₀ Y) :
    (O Y)ᵀ * ((F.jacobiLevel m Y)⁻¹ - Y • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * O Y
        - (O y₀)ᵀ
          * ((F.jacobiLevel m y₀)⁻¹ - y₀ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * O y₀
      = Matrix.of fun i j => ∫ v in y₀..Y, F.boundaryGramianSource m O v i j := by
  refine conjugated_increment_eq_integral
    (U := fun v => (F.jacobiLevel m v)⁻¹ - v • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ))
    (S := fun v => F.boundaryGramianSource m O v) (fun v hv => ?_) hint
  exact matrixHasDerivAt_conjugated (F.matrixHasDerivAt_centeredInverseLevel m v (hdet v hv))
    (hO v) (F.connectionLevel_transpose m v) rfl

/-- **(HJLG.5), positivity.**  The boundary Gramian increment is positive semidefinite: the
channel lost by finite admission reappears as a nonnegative controllability budget. -/
theorem boundaryGramian_nonneg (m : ℕ) (y₀ Y : ℝ) (hle : y₀ ≤ Y)
    (O : ℝ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hint : ∀ i j, IntervalIntegrable (fun v => F.boundaryGramianSource m O v i j)
      MeasureTheory.volume y₀ Y) (x : Fin (m + 1) → ℝ) :
    0 ≤ x ⬝ᵥ ((Matrix.of fun i j => ∫ v in y₀..Y, F.boundaryGramianSource m O v i j) *ᵥ x) := by
  refine dotProduct_integral_nonneg hle hint x fun v => ?_
  rw [boundaryGramianSource, dotProduct_conj_eq]
  exact dotProduct_smul_vecMulVec_nonneg (by positivity) _ _

end Compression

end ShiftedJacobiFrame

end RHTower
