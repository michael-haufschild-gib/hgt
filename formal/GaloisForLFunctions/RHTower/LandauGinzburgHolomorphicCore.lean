import GaloisForLFunctions.RHTower.LandauGinzburgNodeGerm

/-!
# The holomorphic Lagrange-multiplier constraint: critical locus, value, Hessian, fibres

For a holomorphic `F` the multiplier potential `W_F(s,u) = u F(s)` has critical equations `F(s) = 0`
and `u F'(s) = 0`, so at a simple zero the critical point is `(ρ, 0)`; every critical point has
critical value zero; the Hessian, assembled from actual iterated partial derivatives, has
determinant `-(F'(s))²`; and the part of the total space lying over the nonzero values of `W_F` is
a product of the complement of the zero set with the punctured plane, so the family over the nonzero
values carries no variation.

* `lgGradient`, `lgGradient_eq` — the gradient, computed from `deriv`.
* `lgGradient_eq_zero_iff_of_deriv_ne`, `lgPotential_eq_zero_of_lgGradient_eq_zero`.
* `lgHessian`, `lgHessian_eq`, `det_lgHessian`, `det_lgHessian_ne_zero_of_simple`.
* `lgNonzeroLocusEquiv` — the product structure of the nonzero part of the total space.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

noncomputable section

/-! ### Partial derivatives -/

theorem hasDerivAt_lgPotential_snd (F : ℂ → ℂ) (s u : ℂ) :
    HasDerivAt (fun u' => lgPotential F (s, u')) (F s) u := by
  simpa [lgPotential] using (hasDerivAt_id u).mul_const (F s)

theorem deriv_lgPotential_snd (F : ℂ → ℂ) (s u : ℂ) :
    deriv (fun u' => lgPotential F (s, u')) u = F s :=
  (hasDerivAt_lgPotential_snd F s u).deriv

theorem hasDerivAt_lgPotential_fst {F : ℂ → ℂ} {s : ℂ} (hF : DifferentiableAt ℂ F s) (u : ℂ) :
    HasDerivAt (fun s' => lgPotential F (s', u)) (u * deriv F s) s := by
  simpa [lgPotential] using hF.hasDerivAt.const_mul u

theorem deriv_lgPotential_fst {F : ℂ → ℂ} {s : ℂ} (hF : DifferentiableAt ℂ F s) (u : ℂ) :
    deriv (fun s' => lgPotential F (s', u)) s = u * deriv F s :=
  (hasDerivAt_lgPotential_fst hF u).deriv

/-- The gradient of the multiplier potential, assembled from its two partial derivatives. -/
def lgGradient (F : ℂ → ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (deriv (fun s => lgPotential F (s, p.2)) p.1, deriv (fun u => lgPotential F (p.1, u)) p.2)

theorem lgGradient_eq {F : ℂ → ℂ} {p : ℂ × ℂ} (hF : DifferentiableAt ℂ F p.1) :
    lgGradient F p = (p.2 * deriv F p.1, F p.1) := by
  rw [lgGradient, deriv_lgPotential_fst hF, deriv_lgPotential_snd]

/-- The critical equations are the multiplier equation and the original zero equation. -/
theorem lgGradient_eq_zero_iff {F : ℂ → ℂ} {p : ℂ × ℂ} (hF : DifferentiableAt ℂ F p.1) :
    lgGradient F p = 0 ↔ p.2 * deriv F p.1 = 0 ∧ F p.1 = 0 := by
  rw [lgGradient_eq hF, Prod.ext_iff]
  simp

/-- Where `F` has nonvanishing derivative, the critical locus is exactly the zero set of `F` at
multiplier zero. -/
theorem lgGradient_eq_zero_iff_of_deriv_ne {F : ℂ → ℂ} {p : ℂ × ℂ}
    (hF : DifferentiableAt ℂ F p.1) (hsimple : deriv F p.1 ≠ 0) :
    lgGradient F p = 0 ↔ F p.1 = 0 ∧ p.2 = 0 := by
  rw [lgGradient_eq_zero_iff hF]
  simp [hsimple, and_comm]

/-- Every critical point of the multiplier potential has critical value zero. -/
theorem lgPotential_eq_zero_of_lgGradient_eq_zero {F : ℂ → ℂ} {p : ℂ × ℂ}
    (hF : DifferentiableAt ℂ F p.1) (hcrit : lgGradient F p = 0) : lgPotential F p = 0 := by
  have hroot := ((lgGradient_eq_zero_iff hF).mp hcrit).2
  simp [lgPotential, hroot]

/-- All critical points of the multiplier potential share the same critical value. -/
theorem lgPotential_eq_of_lgGradient_eq_zero {F : ℂ → ℂ} {p q : ℂ × ℂ}
    (hFp : DifferentiableAt ℂ F p.1) (hFq : DifferentiableAt ℂ F q.1)
    (hp : lgGradient F p = 0) (hq : lgGradient F q = 0) :
    lgPotential F p = lgPotential F q := by
  rw [lgPotential_eq_zero_of_lgGradient_eq_zero hFp hp,
    lgPotential_eq_zero_of_lgGradient_eq_zero hFq hq]

/-! ### The Hessian -/

/-- The Hessian of the multiplier potential in the coordinates `(s,u)`, assembled from actual
iterated partial derivatives. -/
def lgHessian (F : ℂ → ℂ) (p : ℂ × ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![deriv (fun s => deriv (fun s' => lgPotential F (s', p.2)) s) p.1,
     deriv (fun u => deriv (fun s' => lgPotential F (s', u)) p.1) p.2;
     deriv (fun s => deriv (fun u' => lgPotential F (s, u')) p.2) p.1,
     deriv (fun u => deriv (fun u' => lgPotential F (p.1, u')) u) p.2]

theorem lgHessian_eq {F : ℂ → ℂ} {p : ℂ × ℂ} (hF : AnalyticAt ℂ F p.1) :
    lgHessian F p =
      !![p.2 * deriv (deriv F) p.1, deriv F p.1; deriv F p.1, 0] := by
  have hnear : (fun s => deriv (fun s' => lgPotential F (s', p.2)) s)
      =ᶠ[𝓝 p.1] fun s => p.2 * deriv F s := by
    filter_upwards [hF.eventually_analyticAt] with s hs
    exact deriv_lgPotential_fst hs.differentiableAt p.2
  have h00 : deriv (fun s => deriv (fun s' => lgPotential F (s', p.2)) s) p.1
      = p.2 * deriv (deriv F) p.1 := by
    rw [hnear.deriv_eq]
    exact deriv_const_mul _ (hF.deriv.differentiableAt)
  have h01 : deriv (fun u => deriv (fun s' => lgPotential F (s', u)) p.1) p.2
      = deriv F p.1 := by
    have hfun : (fun u => deriv (fun s' => lgPotential F (s', u)) p.1)
        = fun u => u * deriv F p.1 := by
      funext u
      exact deriv_lgPotential_fst hF.differentiableAt u
    rw [hfun]
    simp
  have h10 : deriv (fun s => deriv (fun u' => lgPotential F (s, u')) p.2) p.1 = deriv F p.1 := by
    have hfun : (fun s => deriv (fun u' => lgPotential F (s, u')) p.2) = F := by
      funext s
      exact deriv_lgPotential_snd F s p.2
    rw [hfun]
  have h11 : deriv (fun u => deriv (fun u' => lgPotential F (p.1, u')) u) p.2 = 0 := by
    have hfun : (fun u => deriv (fun u' => lgPotential F (p.1, u')) u) = fun _ => F p.1 := by
      funext u
      exact deriv_lgPotential_snd F p.1 u
    rw [hfun, deriv_const]
  simp only [lgHessian, h00, h01, h10, h11]

/-- **The Hessian determinant is the negative square of the derivative of `F`.** -/
theorem det_lgHessian {F : ℂ → ℂ} {p : ℂ × ℂ} (hF : AnalyticAt ℂ F p.1) :
    (lgHessian F p).det = -(deriv F p.1) ^ (2 : ℕ) := by
  rw [lgHessian_eq hF, Matrix.det_fin_two_of]
  ring

/-- **A simple zero gives a nondegenerate critical point.** -/
theorem det_lgHessian_ne_zero_of_simple {F : ℂ → ℂ} {p : ℂ × ℂ} (hF : AnalyticAt ℂ F p.1)
    (hsimple : deriv F p.1 ≠ 0) : (lgHessian F p).det ≠ 0 := by
  rw [det_lgHessian hF]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hsimple)

/-! ### The nonzero part of the total space is a product -/

/-- **The family over the nonzero values of the multiplier potential is a product.**  The part of
the total space lying over `ℂ \ {0}` is canonically the complement of the zero set of `F` times the
punctured plane, with the potential itself as the second coordinate.  In particular no nonzero
fibre carries variation, and every two nonzero fibres are canonically identified. -/
def lgNonzeroLocusEquiv (F : ℂ → ℂ) (U : Set ℂ) :
    {p : ℂ × ℂ // p.1 ∈ U ∧ lgPotential F p ≠ 0}
      ≃ ({s : ℂ // s ∈ U ∧ F s ≠ 0} × {t : ℂ // t ≠ 0}) where
  toFun p :=
    (⟨p.1.1, p.2.1, fun h => p.2.2 (by simp [lgPotential, h])⟩, ⟨lgPotential F p.1, p.2.2⟩)
  invFun q :=
    ⟨(q.1.1, q.2.1 / F q.1.1), q.1.2.1, by
      have hF : F q.1.1 ≠ 0 := q.1.2.2
      simp only [lgPotential]
      rw [div_mul_cancel₀ _ hF]
      exact q.2.2⟩
  left_inv p := by
    refine Subtype.ext (Prod.ext rfl ?_)
    have hF : F p.1.1 ≠ 0 := fun h => p.2.2 (by simp [lgPotential, h])
    show lgPotential F p.1 / F p.1.1 = p.1.2
    simp only [lgPotential]
    exact mul_div_cancel_right₀ _ hF
  right_inv q := by
    refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
    have hF : F q.1.1 ≠ 0 := q.1.2.2
    show lgPotential F (q.1.1, q.2.1 / F q.1.1) = q.2.1
    simp only [lgPotential]
    exact div_mul_cancel₀ _ hF

end

end GaloisForLFunctions.RHTower
