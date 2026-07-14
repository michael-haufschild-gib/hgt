import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance

/-!
# The digamma carrier plus a polynomial stays hypertranscendental

For `M ≠ 0` and any polynomial `p`, the carrier `M·ψ(t) + p(t)` is hypertranscendental.  This is the
polynomial-perturbation case of the neutral/nonzero-charge direction of the signed-archimedean
orbit-charge law: a hypothetical algebraic differential relation for the carrier is transported, by an
invertible affine jet substitution `Y_j ↦ M·Y_j + p⁽ʲ⁾(point)`, into an off-pole jet annihilator of the
pure digamma jets, which must vanish by the off-pole digamma Hölder theorem
`digamma_jet_annihilator_eq_zero`.  The substitution is invertible because `M ≠ 0`, so the transported
relation is nonzero — a contradiction.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- Iterated derivative of a polynomial evaluation is the evaluation of its iterated formal
derivative. -/
theorem iteratedDeriv_polynomial_eval (p : Polynomial ℂ) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun x => p.eval x) z = ((⇑Polynomial.derivative)^[j] p).eval z := by
  induction j generalizing z with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ,
      show iteratedDeriv j (fun x => p.eval x)
        = fun x => ((⇑Polynomial.derivative)^[j] p).eval x from funext ih,
      Polynomial.deriv, Function.iterate_succ_apply']

/-- Evaluating `q(X₀)` at a jet vector recovers `q` at the point slot. -/
theorem eval_aeval_X0 {N : ℕ} (q : Polynomial ℂ) (v : Fin (N + 1) → ℂ) :
    MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X 0) q) = q.eval (v 0) := by
  induction q using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp

/-- **The digamma carrier plus a polynomial is hypertranscendental.**  `M·ψ(t) + p(t)` satisfies no
algebraic differential equation when `M ≠ 0`. -/
theorem hypertranscendental_smul_digamma_add_polynomial {M : ℂ} (hM : M ≠ 0) (p : Polynomial ℂ) :
    Hypertranscendental (fun t => M * Complex.digamma t + p.eval t) := by
  rintro ⟨n, Q, hQ0, hQz⟩
  classical
  set σ : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
    Fin.cases (MvPolynomial.X 0)
      (fun j => MvPolynomial.C M * MvPolynomial.X j.succ
        + Polynomial.aeval (MvPolynomial.X 0) ((⇑Polynomial.derivative)^[(j : ℕ)] p)) with hσ
  set τ : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
    Fin.cases (MvPolynomial.X 0)
      (fun j => MvPolynomial.C M⁻¹ * MvPolynomial.X j.succ
        - MvPolynomial.C M⁻¹ * Polynomial.aeval (MvPolynomial.X 0)
            ((⇑Polynomial.derivative)^[(j : ℕ)] p)) with hτ
  set P : MvPolynomial (Fin (n + 2)) ℂ := bind₁ σ Q with hP
  -- the affine substitution is invertible, so `P ≠ 0`
  have hσinv : (fun i => bind₁ τ (σ i))
      = (MvPolynomial.X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
    funext i
    induction i using Fin.cases with
    | zero => simp only [hσ, Fin.cases_zero, bind₁_X_right, hτ]
    | succ j =>
      simp only [hσ, Fin.cases_succ, map_add, map_mul, bind₁_C_right, bind₁_X_right]
      rw [← Polynomial.aeval_algHom_apply (bind₁ τ) (MvPolynomial.X 0)
          ((⇑Polynomial.derivative)^[(j : ℕ)] p), bind₁_X_right]
      simp only [hτ, Fin.cases_succ, Fin.cases_zero]
      have hMM : MvPolynomial.C M * MvPolynomial.C M⁻¹
          = (1 : MvPolynomial (Fin (n + 2)) ℂ) := by
        rw [← map_mul, mul_inv_cancel₀ hM, map_one]
      linear_combination (MvPolynomial.X (Fin.succ j)
        - Polynomial.aeval (MvPolynomial.X 0) ((⇑Polynomial.derivative)^[(j : ℕ)] p)) * hMM
  have hP0 : P ≠ 0 := by
    intro h0
    apply hQ0
    have hback : bind₁ τ P = Q := by
      rw [hP, bind₁_bind₁, hσinv]; simp
    rw [← hback, h0, map_zero]
  -- the additive jet split off the poles
  have hsplit : ∀ (j : ℕ) (z : ℂ), (∀ w : ℕ, z ≠ -(w : ℂ)) →
      iteratedDeriv j (fun t => M * Complex.digamma t + p.eval t) z
        = M * iteratedDeriv j Complex.digamma z + ((⇑Polynomial.derivative)^[j] p).eval z := by
    intro j z hz
    have hψ : ContDiffAt ℂ j Complex.digamma z := contDiffAt_digamma_n z hz j
    have hp : ContDiffAt ℂ j (fun x => p.eval x) z := by
      have h := (Polynomial.contDiff_aeval p (j : WithTop ℕ∞)).contDiffAt (x := z)
      have hfe : (fun x : ℂ => p.aeval x) = fun x : ℂ => p.eval x :=
        funext fun x => congrFun (Polynomial.coe_aeval_eq_eval x) p
      rwa [hfe] at h
    rw [show (fun t => M * Complex.digamma t + p.eval t)
          = (fun x => M * Complex.digamma x) + (fun x => p.eval x) from rfl,
      iteratedDeriv_add (contDiffAt_const.mul hψ) hp, iteratedDeriv_const_mul M hψ,
      iteratedDeriv_polynomial_eval]
  -- `P` annihilates the digamma jets off the poles
  have hann : P = 0 := by
    apply digamma_jet_annihilator_eq_zero n P
    intro z hz
    rw [hP, eval_bind₁]
    have hvec : (fun i => MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) Complex.digamma z) (σ i))
        = Fin.cons z (fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) (fun t => M * Complex.digamma t + p.eval t) z) := by
      funext i
      induction i using Fin.cases with
      | zero => simp only [hσ, Fin.cases_zero, MvPolynomial.eval_X, Fin.cons_zero]
      | succ j =>
        simp only [hσ, Fin.cases_succ, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          Fin.cons_succ]
        rw [eval_aeval_X0, Fin.cons_zero, hsplit (j : ℕ) z hz]
    rw [hvec]
    exact hQz z
  exact hP0 hann

end GaloisForLFunctions

end
