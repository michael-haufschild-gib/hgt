import GaloisForLFunctions.Hurwitz.LadderIndependence
import GaloisForLFunctions.Hurwitz.LadderDeformation
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Hypertranscendence of Hurwitz zeta in its shift variable

The all-order identity

`∂_a^k ζ(s,a) = (-1)^k (s)_k ζ(s+k,a)`

is an invertible diagonal change of coordinates when `Re s > 1`.  Transporting the full algebraic
independence of the shifted Hurwitz ladder across this value relation proves that
`a ↦ ζ(s,a)` is hypertranscendental for every irrational `s` in the convergence half-plane.
-/

open Complex HurwitzZetaShift Polynomial

namespace HurwitzLadder

/-- Diagonal scaling of jet variables over the polynomial coefficient ring `ℂ[a]`. -/
noncomputable def hzetaJetDiagonalScale {σ : Type*} (c : σ → ℂ) :
    MvPolynomial σ (Polynomial ℂ) →ₐ[Polynomial ℂ] MvPolynomial σ (Polynomial ℂ) :=
  MvPolynomial.bind₁
    (fun i => MvPolynomial.C (Polynomial.C (c i)) * MvPolynomial.X i)

/-- Coordinatewise reciprocal scaling inverts `hzetaJetDiagonalScale`. -/
theorem hzetaJetDiagonalScale_inv_apply
    {σ : Type*} (c : σ → ℂ) (hc : ∀ i, c i ≠ 0)
    (P : MvPolynomial σ (Polynomial ℂ)) :
    hzetaJetDiagonalScale (fun i => (c i)⁻¹) (hzetaJetDiagonalScale c P) = P := by
  rw [hzetaJetDiagonalScale, hzetaJetDiagonalScale, MvPolynomial.bind₁_bind₁]
  have hg : (fun i => MvPolynomial.bind₁
      (fun j => MvPolynomial.C (Polynomial.C ((c j)⁻¹)) * MvPolynomial.X j)
      (MvPolynomial.C (Polynomial.C (c i)) * MvPolynomial.X i)) = MvPolynomial.X := by
    funext i
    simp only [map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
    rw [← mul_assoc, ← MvPolynomial.C_mul, ← Polynomial.C_mul]
    simp [hc i]
  rw [hg, MvPolynomial.bind₁_X_left]
  rfl

/-- Evaluation after diagonal scaling is evaluation at the coordinatewise scaled values. -/
theorem eval₂_hzetaJetDiagonalScale
    {σ : Type*} (c x : σ → ℂ) (a : ℂ)
    (P : MvPolynomial σ (Polynomial ℂ)) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom a) x (hzetaJetDiagonalScale c P) =
      MvPolynomial.eval₂ (Polynomial.evalRingHom a) (fun i => c i * x i) P := by
  rw [hzetaJetDiagonalScale]
  change MvPolynomial.eval₂Hom (Polynomial.evalRingHom a) x
      (MvPolynomial.bind₁
        (fun i => MvPolynomial.C (Polynomial.C (c i)) * MvPolynomial.X i) P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  simp

/-- **Hurwitz zeta is hypertranscendental in its shift variable.**

Fix an irrational exponent `s` with `Re s > 1`.  If a polynomial over `ℂ[a]` in any finite
differential jet of `a ↦ ζ(s,a)` vanishes throughout the upper half-plane, then the polynomial is
zero.  Equivalently, `a ↦ ζ(s,a)` satisfies no algebraic ordinary differential equation over
`ℂ(a)` on that domain. -/
theorem hzeta_hypertranscendental_in_shift
    {s : ℂ} (hs1 : 1 < s.re) (hsQ : ∀ r : ℚ, (r : ℂ) ≠ s) (N : ℕ)
    (P : MvPolynomial (Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun k : Fin (N + 1) => iteratedDeriv (k : ℕ) (hzeta s) a) P = 0) :
    P = 0 := by
  let c : Fin (N + 1) → ℂ := fun k =>
    (-1 : ℂ) ^ (k : ℕ) * (ascPochhammer ℂ (k : ℕ)).eval s
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ascPochhammer_eval_ne_zero_of_one_lt_re (k : ℕ) hs1)
  let P' := hzetaJetDiagonalScale c P
  have hrel' : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun k : Fin (N + 1) => hzeta (s + ((k : ℕ) : ℂ)) a) P' = 0 := by
    intro a ha
    change MvPolynomial.eval₂ (Polynomial.evalRingHom a)
      (fun k : Fin (N + 1) => hzeta (s + ((k : ℕ) : ℂ)) a)
      (hzetaJetDiagonalScale c P) = 0
    rw [eval₂_hzetaJetDiagonalScale]
    have hjet : (fun k : Fin (N + 1) =>
        c k * hzeta (s + ((k : ℕ) : ℂ)) a) =
        fun k : Fin (N + 1) => iteratedDeriv (k : ℕ) (hzeta s) a := by
      funext k
      exact (hzeta_iteratedDeriv (k : ℕ) hs1 (a := a) ha).symm
    rw [hjet]
    exact hrel a ha
  have hP' : P' = 0 := hurwitz_ladder_independence hs1 hsQ N P' hrel'
  change hzetaJetDiagonalScale c P = 0 at hP'
  have hinv := congrArg (hzetaJetDiagonalScale (fun i => (c i)⁻¹)) hP'
  rw [hzetaJetDiagonalScale_inv_apply c hc P] at hinv
  simpa using hinv

end HurwitzLadder
