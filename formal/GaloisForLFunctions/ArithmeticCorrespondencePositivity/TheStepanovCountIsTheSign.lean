import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.SparseAnnihilatorsAndTheStepanovMechanism

/-!
# The Stepanov count is the sign

Over `𝔽_q`, Stepanov's method builds an auxiliary polynomial vanishing to high order at every
rational point and reads off a **one-sided** count `N_m ≤ q^m + 1 + C q^{m/2}`; Bombieri's remark
that the one-sided count already forces purity completes the proof of Weil's bound. The report asks
for the `ℤ`-analogue (B3.30). Its count is the prime-power count `ψ(x) = Σ_{n ≤ x} Λ(n)`, with main
term `x` from the pole and error from the zeros.

* **The one-sided count is RH** (`riemannHypothesis_iff_one_sided_count`): RH holds iff
  `ψ(x) − x ≤ C √x log²x` for large `x` and some `C`. The one-sided bound already forces every zero
  onto the line (RHTower, `riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq`), and RH gives the
  two-sided bound (von Koch). This is Bombieri's one-sided principle over `ℤ`.
* **Hecke auxiliaries cannot produce it** (`hecke_auxiliary_kills_only_critical`). An auxiliary
  `1 − T_p^N` built from one Hecke operator kills the symbol of `ρ` only if `Re ρ = ½`; a polynomial
  auxiliary with `K` monomials vanishes to order `< K` at every nonzero symbol (P14). Such
  auxiliaries see only the critical lattice and cannot force vanishing at an off-line zero.

So an arithmetic Stepanov method is exactly as strong as the sign: its natural output, a one-sided
square-root count, is equivalent to RH, and its auxiliary sections must come from outside the
Hecke algebra of a single prime.
-/

open Filter Topology Asymptotics

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- **Bombieri's one-sided principle over `ℤ`**: RH iff the prime-power count exceeds its main
term by at most `C √x log²x`. -/
theorem riemannHypothesis_iff_one_sided_count :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in atTop, Chebyshev.psi x - x ≤ C * Real.sqrt x * Real.log x ^ 2 := by
  constructor
  · intro hRH
    obtain ⟨C, hC⟩ := (RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO.mp hRH).bound
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg (Real.log x)))] at hx
    have hpos : 0 ≤ Real.sqrt x * Real.log x ^ 2 :=
      mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _)
    calc Chebyshev.psi x - x ≤ |Chebyshev.psi x - x| := le_abs_self _
      _ ≤ C * (Real.sqrt x * Real.log x ^ 2) := hx
      _ ≤ max C 0 * (Real.sqrt x * Real.log x ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ = max C 0 * Real.sqrt x * Real.log x ^ 2 := by ring
  · rintro ⟨C, hC, h⟩
    exact RHTower.riemannHypothesis_of_chebyshevPsi_sub_le_sqrt_log_sq hC h

/-- **Hecke auxiliaries kill only critical symbols**: if `1 − T_p^N` kills the symbol of `ρ`, then
`Re ρ = ½` and `N Im ρ log p ∈ 2πℤ`. -/
theorem hecke_auxiliary_kills_only_critical {p : ℝ} (hp : 1 < p) {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ}
    (h : 1 - heckeSymbol p ρ ^ N = 0) :
    ρ.re = 1 / 2 ∧ ∃ k : ℤ, (N : ℝ) * ρ.im * Real.log p = 2 * Real.pi * k :=
  (heckeSymbol_pow_eq_one_iff hp hN ρ).mp (sub_eq_zero.mp h).symm

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
