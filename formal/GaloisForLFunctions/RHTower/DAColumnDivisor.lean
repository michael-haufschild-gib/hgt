/-
Zeros of column-factored Dirichlet data are vertically periodic.

A member of Ostrowski column form `F(s) = ∏_{i ∈ t} Ψᵢ(pᵢ^{−s})` is a finite product of
prime columns, each depending on `s` only through the single exponential `pᵢ^{−s}`. That
exponential is invariant under the vertical shift `s ↦ s + (2π/log pᵢ)·i`: its period is
`2π/log pᵢ`. Hence a vanishing column factor is invariant under its own period, and the
divisor of any finite column product is a union of vertical arithmetic progressions — a zero
of `F` propagates along the imaginary-direction progression of the column responsible for it.

By Ostrowski's structure theorem, a differentially algebraic ordinary Dirichlet series is a
power series in finitely many prime exponentials, and multiplicative streams factor through
their columns; so the column form is exactly the differentially algebraic regime for
multiplicative Dirichlet data. The contrapositive is therefore a discriminator: a member with
a zero that is vertically aperiodic in every admissible period `2π/log p` cannot be of column
form, and so lies outside the differentially algebraic column regime — divisor aperiodicity as
a hypertranscendence signature within multiplicative Dirichlet data.

No power-series or primality input is used: the periodicity argument needs only `2 ≤ pᵢ` so
that the base is a real number exceeding one (nonzero base, nonzero logarithm), so the columns
are indexed by the natural number `i` itself and the hypothesis `2 ≤ i` is carried in the
theorems rather than in the definition of the column form.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RHTower

open Complex Finset

/-- The exponential `b^{−s}` has vertical period `2π/log b`: for `2 ≤ b` it is invariant under
`s ↦ s + k·(2π/log b)·i` for every integer `k`. This is the single computational fact behind
column-zero periodicity — the exponent shift `−k·(2π/log b)·log b·i = −2πk·i` is killed by
`exp(−2πik) = 1` after the `log b` cancellation (`log b ≠ 0` since `b > 1`). -/
theorem exp_shift_invariant {b : ℕ} (hb : 2 ≤ b) (s : ℂ) (k : ℤ) :
    (b : ℂ) ^ (-(s + (k * (2 * Real.pi / Real.log b)) * Complex.I)) = (b : ℂ) ^ (-s) := by
  have hb0 : (b : ℂ) ≠ 0 := by
    have : 0 < b := by omega
    exact_mod_cast this.ne'
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hLpos : 0 < Real.log b := Real.log_pos hbR
  have hL0 : (Real.log b : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
  have hlogb : Complex.log (b : ℂ) = (Real.log b : ℂ) := by
    rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (b : ℝ)), Complex.ofReal_natCast]
  have hsplit : -(s + (↑k * (2 * Real.pi / Real.log b)) * Complex.I)
      = (-s) + (-(↑k * (2 * (Real.pi : ℂ) / (Real.log b : ℂ))) * Complex.I) := by
    push_cast; ring
  rw [hsplit, Complex.cpow_add _ _ hb0]
  have hfac : (b : ℂ) ^ (-(↑k * (2 * (Real.pi : ℂ) / (Real.log b : ℂ))) * Complex.I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hb0, hlogb]
    have hexp : (Real.log b : ℂ) * (-(↑k * (2 * (Real.pi : ℂ) / (Real.log b : ℂ))) * Complex.I)
        = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp
      push_cast
      ring
    rw [hexp]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [hfac, mul_one]

/-- Ostrowski column form: `F` is a finite product of prime columns, each a function of the
single exponential `i^{−s}`. Indexing is by the natural number `i` itself; primality is not
needed for the periodicity argument, only `2 ≤ i`, which is why that hypothesis is kept in the
theorems rather than baked into this definition. -/
def ColumnForm (t : Finset ℕ) (Ψ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) : Prop :=
  ∀ s, F s = ∏ i ∈ t, Ψ i ((i : ℂ) ^ (-s))

/-- Periodicity transfer. If `F` is of column form and `F s₀ = 0`, then some column `i` is
responsible for the zero, and because that column depends on `s` only through the exponential
`i^{−s}` — invariant under the shift by `2π/log i` — `F` vanishes on the whole vertical
arithmetic progression `{s₀ + k·(2π/log i)·i : k ∈ ℤ}`. The divisor of a finite column product
is thus a union of vertical progressions. -/
theorem columnForm_zero_periodic {t : Finset ℕ} {Ψ : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hF : ColumnForm t Ψ F) (ht : ∀ i ∈ t, 2 ≤ i) {s₀ : ℂ} (h0 : F s₀ = 0) :
    ∃ i ∈ t, ∀ k : ℤ, F (s₀ + (k * (2 * Real.pi / Real.log i)) * Complex.I) = 0 := by
  rw [hF s₀] at h0
  obtain ⟨i, hi, hΨi⟩ := (Finset.prod_eq_zero_iff).mp h0
  refine ⟨i, hi, fun k => ?_⟩
  rw [hF]
  refine Finset.prod_eq_zero hi ?_
  have hshift : (i : ℂ) ^ (-(s₀ + (↑k * (2 * Real.pi / Real.log i)) * Complex.I))
      = (i : ℂ) ^ (-s₀) := exp_shift_invariant (ht i hi) s₀ k
  rw [hshift, hΨi]

/-- Aperiodicity marker (contrapositive of the transfer). A zero of `F` that is vertically
aperiodic in every admissible period `2π/log b` (for every base `b ≥ 2` there is an integer
shift at which `F` does not vanish) certifies that `F` is of no column form: it lies outside
the differentially algebraic column regime — divisor aperiodicity as a hypertranscendence
signature within multiplicative Dirichlet data. -/
theorem not_columnForm_of_aperiodic_zero {F : ℂ → ℂ} {s₀ : ℂ} (h0 : F s₀ = 0)
    (haper : ∀ b : ℕ, 2 ≤ b →
      ∃ k : ℤ, F (s₀ + (k * (2 * Real.pi / Real.log b)) * Complex.I) ≠ 0) :
    ∀ (t : Finset ℕ) (Ψ : ℕ → ℂ → ℂ), (∀ i ∈ t, 2 ≤ i) → ¬ ColumnForm t Ψ F := by
  intro t Ψ ht hF
  obtain ⟨i, hi, hall⟩ := columnForm_zero_periodic hF ht h0
  obtain ⟨k, hk⟩ := haper i (ht i hi)
  exact hk (hall k)

/-- A witness that the column form is inhabited by a genuine two-factor member: the degree-zero
family `(1 − 2u)(1 − 4u)` in the single exponential `u = 8^{−s}` is of column form over the
one-element index `{8}`. The base `8` is not prime — that is fine, since the periodicity
argument only requires `2 ≤ b`, which is exactly why `ColumnForm` was kept primality-free. -/
theorem columnForm_example :
    ColumnForm {8} (fun _ u => (1 - 2 * u) * (1 - 4 * u))
      (fun s => (1 - 2 * (8 : ℂ) ^ (-s)) * (1 - 4 * (8 : ℂ) ^ (-s))) := by
  intro s
  simp [Finset.prod_singleton]

end RHTower
