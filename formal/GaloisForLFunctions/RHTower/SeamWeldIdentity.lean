import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# The seam-log derivative weld identity

For an even function presented as `Ξ w = Φ (w²)` with `Φ` entire, the chain rule gives
`Ξ' w = 2 w Φ' (w²)`, hence

`Ξ' w / (w · Ξ w) = 2 · logDeriv Φ (w²)`

wherever `w ≠ 0` and `Φ (w²) ≠ 0`.  The right-hand side involves no square-root branch, so the
identity is branch independent, and it is the holomorphic extension of the left-hand side across
the seam `w = 0`.  Dividing an odd tower expansion of `Ξ'/Ξ` by the seam coordinate turns it into
the even tower with the same coefficients.
-/

noncomputable section

namespace RHTower

open Complex

/-- **The weld identity.**  For an even function presented as `Ξ w = Φ (w²)`, the completed
log-derivative divided by the seam coordinate is twice the log-derivative of `Φ` at `w²`. -/
theorem seam_weld_identity {Φ Ξ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hΞ : ∀ w : ℂ, Ξ w = Φ (w ^ (2 : ℕ))) {w : ℂ} (hw : w ≠ 0) (hΦw : Φ (w ^ (2 : ℕ)) ≠ 0) :
    deriv Ξ w / (w * Ξ w) = 2 * logDeriv Φ (w ^ (2 : ℕ)) := by
  have hfun : Ξ = fun z : ℂ => Φ (z ^ (2 : ℕ)) := funext hΞ
  have h1 : HasDerivAt (fun z : ℂ => z ^ (2 : ℕ)) (2 * w) w := by
    simpa using (hasDerivAt_pow 2 w)
  have h2 : HasDerivAt Φ (deriv Φ (w ^ (2 : ℕ))) (w ^ (2 : ℕ)) := (hΦ (w ^ (2 : ℕ))).hasDerivAt
  have h3 : HasDerivAt (fun z : ℂ => Φ (z ^ (2 : ℕ))) (deriv Φ (w ^ (2 : ℕ)) * (2 * w)) w :=
    HasDerivAt.comp w h2 h1
  have hderiv : deriv Ξ w = deriv Φ (w ^ (2 : ℕ)) * (2 * w) := by
    rw [hfun]
    exact h3.deriv
  rw [hderiv, hΞ, logDeriv_apply]
  field_simp

/-- The weld quotient extends holomorphically across the seam: it is the entire-quotient
expression `2 · logDeriv Φ (w²)`, which is differentiable wherever `Φ (w²) ≠ 0`. -/
theorem seam_weld_differentiableAt {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {w : ℂ}
    (hΦw : Φ (w ^ (2 : ℕ)) ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => 2 * logDeriv Φ (z ^ (2 : ℕ))) w := by
  have hana : AnalyticOnNhd ℂ Φ Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hΦ
  have hderiv : Differentiable ℂ (deriv Φ) :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp (hana.deriv)
  have hsq : DifferentiableAt ℂ (fun z : ℂ => z ^ (2 : ℕ)) w := (differentiable_pow 2) w
  have hnum : DifferentiableAt ℂ (fun z : ℂ => deriv Φ (z ^ (2 : ℕ))) w := by fun_prop
  have hden : DifferentiableAt ℂ (fun z : ℂ => Φ (z ^ (2 : ℕ))) w := by fun_prop
  have hquot : DifferentiableAt ℂ (fun z : ℂ => deriv Φ (z ^ (2 : ℕ)) / Φ (z ^ (2 : ℕ))) w :=
    hnum.div hden hΦw
  simpa [logDeriv] using hquot.const_mul (2 : ℂ)

/-- **Dividing the seam tower by the seam coordinate.**  If the completed log-derivative has the
odd tower expansion, then the weld quotient has the same coefficients as an even tower. -/
theorem seam_weld_series {Φ Ξ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hΞ : ∀ w : ℂ, Ξ w = Φ (w ^ (2 : ℕ))) {T : ℕ → ℂ} {w : ℂ} (hw : w ≠ 0) (hΦw : Φ (w ^ (2 : ℕ)) ≠ 0)
    (hsum : deriv Ξ w / Ξ w = ∑' n : ℕ, (-1 : ℂ) ^ n * T (n + 1) * w ^ (2 * n + 1)) :
    2 * logDeriv Φ (w ^ (2 : ℕ)) = ∑' n : ℕ, (-1 : ℂ) ^ n * T (n + 1) * w ^ (2 * n) := by
  rw [← seam_weld_identity hΦ hΞ hw hΦw, div_mul_eq_div_div_swap, hsum, ← tsum_div_const]
  refine tsum_congr (fun n => ?_)
  rw [pow_succ]
  field_simp

end RHTower
