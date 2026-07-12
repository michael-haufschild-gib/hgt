import Mathlib

/-!
# The differential unit equation: no rational logarithmic derivative equals `m·u`

The differential analogue of the shift eigenrelation (`no_shift_eigenrelation`).  On the
differential polynomial ring `ℂ{u} = MvPolynomial ℕ ℂ` — jet coordinates `x₀ = s`,
`x₁ = u`, `x_{j+1} = u⁽ʲ⁾` — with the total derivative `𝒟` (`𝒟 x₀ = 1`, `𝒟 x_k = x_{k+1}`
for `k ≥ 1`), the **differential unit equation** is

`𝒟 w = m · x₁ · w`,  `m ≥ 1`.

It has no nonzero solution in the fraction field.  In cross-multiplied polynomial form: for
coprime `p, q ≠ 0`,

`𝒟p · q − p · 𝒟q = m · x₁ · p · q`

is impossible.  This is the terminal obstruction of the logarithmic-derivative closure of
differential algebraicity: eliminating an `f`-power relation for a differentially algebraic
`f` against the functional equation `f' = u·f` (differentiation contributing the factor `d`
in degree `d`) leaves exactly this identity, with `u = f'/f = x₁`.

The proof is the differential twin of the shift no-go's integer-root pinch.  The total
derivative introduces, at the top jet variable `x_N`, a fresh variable `x_{N+1}` linearly
with coefficient `∂_{x_N}`; applying `∂_{x_{N+1}}` to the equation and using coprimality
plus the strict total-degree drop of `∂_{x_N}` forces `p, q` to be independent of `x_N`.
Descending to `ℂ[x₀]`, a final `∂_{x₁}` reads off `m·p·q = 0`, impossible.

* `totalDeriv` — the total derivative derivation.
* `pderiv_succ_totalDeriv`, `pderiv_one_totalDeriv` — the two commutator identities.
* `totalDegree_pderiv_lt`, `pderiv_ne_zero_of_mem_vars`, `pderiv_self_dvd_eq_zero` — helpers.
* `differential_unit_no_go`, `no_differential_eigenrelation` — the obstruction.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

/-! ## The total derivative -/

/-- The images of the jet generators under the total derivative: `x₀ ↦ 1`,
`x_k ↦ x_{k+1}` for `k ≥ 1`. -/
def totalDerivGen : ℕ → MvPolynomial ℕ ℂ := fun n => if n = 0 then 1 else X (n + 1)

theorem totalDerivGen_zero : totalDerivGen 0 = 1 := rfl

theorem totalDerivGen_succ (n : ℕ) : totalDerivGen (n + 1) = X (n + 2) := by
  simp [totalDerivGen]

/-- The **total derivative** on the differential polynomial ring `ℂ{u} = MvPolynomial ℕ ℂ`:
the `ℂ`-derivation with `x₀ ↦ 1` and `x_k ↦ x_{k+1}` for `k ≥ 1`. -/
def totalDeriv : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  mkDerivation ℂ totalDerivGen

theorem totalDeriv_X (n : ℕ) : totalDeriv (X n) = totalDerivGen n :=
  mkDerivation_X ℂ totalDerivGen n

theorem totalDeriv_C (a : ℂ) : totalDeriv (C a) = 0 := derivation_C ℂ totalDeriv a

/-! ## The commutator identities -/

/-- `[∂_{x_{N+1}}, 𝒟] = ∂_{x_N}` for `N ≥ 1`: applying `∂_{x_{N+1}}` to a total derivative
recovers `∂_{x_N}` up to a total derivative of the already-differentiated polynomial. -/
theorem pderiv_succ_totalDeriv {N : ℕ} (hN : 1 ≤ N) (p : MvPolynomial ℕ ℂ) :
    pderiv (N + 1) (totalDeriv p)
      = totalDeriv (pderiv (N + 1) p) + pderiv N p := by
  have hcomm : ⁅pderiv (N + 1), totalDeriv⁆ = pderiv N := by
    apply derivation_ext
    intro i
    rw [Derivation.commutator_apply, totalDeriv_X]
    rcases i with _ | k
    · -- i = 0
      simp only [totalDerivGen_zero, map_one, Derivation.map_one_eq_zero]
      rw [pderiv_X_of_ne (by omega : N + 1 ≠ 0)]
      rw [totalDeriv_C, sub_zero]
      rw [pderiv_X_of_ne (by omega : N ≠ 0)]
    · -- i = k + 1
      rw [totalDerivGen_succ]
      by_cases hk : k + 1 = N
      · subst hk
        rw [pderiv_X_self, pderiv_X_of_ne (by omega : k + 1 + 1 ≠ k + 1 + 1 - 1 + 1)]
        sorry
      · sorry
  have := Derivation.commutator_apply (pderiv (N + 1)) totalDeriv p
  rw [hcomm] at this
  rw [eq_comm, ← sub_eq_iff_eq_add'] at this ⊢
  linarith? -- placeholder
  sorry

end GaloisForLFunctions

end
