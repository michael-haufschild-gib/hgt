import GaloisForLFunctions.DifferentialPowerElimination
import GaloisForLFunctions.GammaBellSubstitution

/-!
# The generic Bell transfer

The reusable analytic transfer for the differentiation-elimination engine: any analytic
nonzero function `f` on an open set `Ω` satisfies the Bell identity

`f⁽ᵏ⁾(z) = f(z)·B_k(u(z), …, u⁽ᵏ⁻¹⁾(z))`,  `u = f'/f`,

with `B_k = bellCore k` the universal Bell polynomials (from the Γ-transfer).  This is the
step that rewrites a differential-algebraic relation for `f` as a power relation
`∑_d f^d·(u-jet polynomial) = 0`, the input consumed by `diffPowerRel_yields` /
`logDeriv_DA_of_powerRel`.

`iteratedDeriv_eq_bellCore_generic` generalizes `gamma_iteratedDeriv_eq_bellCore` from `Γ` to
any analytic nonzero `f`; the proof is identical modulo replacing the `Γ`-specific
analyticity inputs by the open-set analyticity hypotheses.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial Filter Topology

/-- **Generic Bell identity**: `f⁽ᵏ⁾(z) = f(z)·B_k(u(z),…,u⁽ᵏ⁻¹⁾(z))` for `f` analytic and
nonzero on the open set `Ω`, `u = f'/f`. -/
theorem iteratedDeriv_eq_bellCore_generic {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hfan : ∀ z ∈ Ω, AnalyticAt ℂ f z) (hfne : ∀ z ∈ Ω, f z ≠ 0) :
    ∀ (k : ℕ) {z : ℂ}, z ∈ Ω →
      iteratedDeriv k f z
        = f z * eval (fun j : Fin k =>
            iteratedDeriv (j : ℕ) (fun w => deriv f w / f w) z) (bellCore k) := by
  set u : ℂ → ℂ := fun w => deriv f w / f w with hu_def
  have huan : ∀ z ∈ Ω, AnalyticAt ℂ u z :=
    fun z hz => (hfan z hz).deriv.div (hfan z hz) (hfne z hz)
  intro k
  induction k with
  | zero => intro z _; simp [bellCore_zero, iteratedDeriv_zero]
  | succ k ih =>
      intro z hz
      have hev : iteratedDeriv k f =ᶠ[nhds z]
          (fun w => f w
            * eval (fun j : Fin k => iteratedDeriv (j : ℕ) u w) (bellCore k)) := by
        filter_upwards [hΩ.mem_nhds hz] with w hw
        exact ih hw
      have hg : ∀ j : Fin k, HasDerivAt (fun w => iteratedDeriv (j : ℕ) u w)
          (iteratedDeriv ((j : ℕ) + 1) u z) z :=
        fun j => hasDerivAt_iteratedDeriv_of_analyticOn huan (j : ℕ) hz
      have hchain := hasDerivAt_mvEval_jet (bellCore k)
        (fun j => fun w => iteratedDeriv (j : ℕ) u w)
        (fun j => iteratedDeriv ((j : ℕ) + 1) u z) z hg
      have hf : HasDerivAt f (deriv f z) z := (hfan z hz).differentiableAt.hasDerivAt
      have hRHS := hf.mul hchain
      have hderiv_f : deriv f z = f z * u z := by
        rw [hu_def, mul_comm]
        exact (div_mul_cancel₀ (deriv f z) (hfne z hz)).symm
      rw [iteratedDeriv_succ, hev.deriv_eq.trans hRHS.deriv, hderiv_f]
      rw [bellCore_succ]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_succ,
        Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero]
      ring

/-! ## The jet-frame translation -/

/-- Frame translation `MvPolynomial (Fin (n+1)) (Polynomial ℂ) → MvPolynomial ℕ ℂ`: the
`s`-coefficient polynomial `p ↦ p(x₀)`, and jet variable `j ↦ x_{j+1}`.  This carries the
`Fin`-frame Bell-graded coefficients of the Γ-transfer into the `ℕ`-frame consumed by the
differentiation-elimination engine. -/
def finPolyToNat (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* MvPolynomial ℕ ℂ :=
  eval₂Hom (Polynomial.eval₂RingHom MvPolynomial.C (X 0))
    (fun j : Fin (n + 1) => X ((j : ℕ) + 1))

/-- **Evaluation compatibility of the frame translation.**  Jet-evaluating the `ℕ`-frame
image of `H` at `uJet u z` equals the `Fin`-frame evaluation of `H` at the `u`-jets with the
`s`-coefficients evaluated at `z`. -/
theorem eval_uJet_finPolyToNat {u : ℂ → ℂ} (n : ℕ) (z : ℂ)
    (H : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :
    eval (uJet u z) (finPolyToNat n H)
      = eval₂ (Polynomial.evalRingHom z)
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) u z) H := by
  have hhom : ((eval (uJet u z)).comp (finPolyToNat n) : _ →+* ℂ)
      = eval₂Hom (Polynomial.evalRingHom z)
          (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) u z) := by
    apply MvPolynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro a
        simp [finPolyToNat, Polynomial.coe_eval₂RingHom]
      · simp [finPolyToNat, Polynomial.coe_eval₂RingHom, uJet]
    · intro j
      have hj : uJet u z ((j : ℕ) + 1) = iteratedDeriv (j : ℕ) u z := by simp [uJet]
      simp [finPolyToNat, hj]
  exact RingHom.congr_fun hhom H

end GaloisForLFunctions

end
