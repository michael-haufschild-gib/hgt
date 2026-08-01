import GaloisForLFunctions.HTGeometry.DigammaFieldValuation

/-!
# Rational coefficients on a vertical line

A complex polynomial divided by the power of its own degree tends to its leading coefficient along
any filter on which the argument escapes to infinity; on a vertical line the modulus escapes, so a
quotient of polynomials, normalized by the matching powers of the argument, tends to the quotient of
the leading coefficients.

Multiplying by the digamma-field valuation gives eq. (19) for a general element `R(s)·P(ψ, ψ′, …)` of
`ℂ(s)⟨ψ⟩`: the normalization is `s^{deg p − deg q}` times the `D`-th power of the leading logarithm,
and the limit is the product of the leading coefficient of `R` with the coefficient of the pure
monomial `ψ^D`.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- **A complex polynomial is its leading monomial along any filter where the argument escapes.** -/
theorem tendsto_eval_div_pow_natDegree_of_norm_atTop {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun a => ‖z a‖) l atTop) (p : Polynomial ℂ) :
    Tendsto (fun a => p.eval (z a) / (z a) ^ p.natDegree) l (nhds p.leadingCoeff) := by
  have hinv : Tendsto (fun a => (z a)⁻¹) l (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hz.inv_tendsto_atTop.congr fun a => ?_
    simp [norm_inv]
  have hrev : Tendsto (fun a => p.reverse.eval ((z a)⁻¹)) l (nhds p.leadingCoeff) := by
    have hcont := p.reverse.continuous.continuousAt.tendsto.comp hinv
    have hval : p.reverse.eval 0 = p.leadingCoeff := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
    rw [hval] at hcont
    exact hcont
  refine hrev.congr' ?_
  filter_upwards [hz.eventually_gt_atTop 0] with a ha
  have hne : z a ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  letI : Invertible (z a) := invertibleOfNonzero hne
  have hreverse := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (z a) p
  have hinvcast : ⅟(z a) = (z a)⁻¹ := by
    apply invOf_eq_right_inv
    exact mul_inv_cancel₀ hne
  rw [hinvcast] at hreverse
  simp only [Polynomial.eval₂_id] at hreverse
  rw [← hreverse]
  field_simp

/-- The modulus on a vertical line grows. -/
theorem tendsto_norm_vertical (σ : ℝ) :
    Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  calc t = |((σ : ℂ) + (t : ℂ) * Complex.I).im| := by rw [him, abs_of_nonneg ht]
    _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _

/-- **A polynomial on a vertical line is its leading monomial.** -/
theorem tendsto_eval_div_pow_natDegree_vertical (σ : ℝ) (p : Polynomial ℂ) :
    Tendsto (fun t : ℝ =>
      p.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree)
      atTop (nhds p.leadingCoeff) :=
  tendsto_eval_div_pow_natDegree_of_norm_atTop (tendsto_norm_vertical σ) p

/-- On a vertical line the argument is eventually nonzero. -/
theorem eventually_vertical_ne_zero (σ : ℝ) :
    ∀ᶠ t : ℝ in atTop, ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  filter_upwards [(tendsto_norm_vertical σ).eventually_gt_atTop 0] with t ht
  intro h
  rw [h] at ht
  simp at ht

/-- Negative powers of the argument vanish on a vertical line. -/
theorem tendsto_one_div_vertical_pow (σ : ℝ) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun t : ℝ => 1 / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k) atTop (nhds 0) := by
  have hnorm : Tendsto (fun t : ℝ => ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ k) atTop atTop :=
    (tendsto_pow_atTop hk.ne').comp (tendsto_norm_vertical σ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hnorm.inv_tendsto_atTop.congr fun t => ?_
  simp [norm_pow]

/-- **The ratio of two rational coefficients on a vertical line.**  Normalized by the matching powers
of the argument, a quotient of polynomials tends to the quotient of the leading coefficients. -/
theorem tendsto_ratio_eval_vertical (σ : ℝ) (p q : Polynomial ℂ) (hq : q ≠ 0) :
    Tendsto (fun t : ℝ =>
      (p.eval ((σ : ℂ) + (t : ℂ) * Complex.I) * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q.natDegree)
        / (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree))
      atTop (nhds (p.leadingCoeff / q.leadingCoeff)) := by
  have hp := tendsto_eval_div_pow_natDegree_vertical σ p
  have hqq := tendsto_eval_div_pow_natDegree_vertical σ q
  have hqlead : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hdiv := hp.div hqq hqlead
  refine hdiv.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ, hqq.eventually_ne hqlead] with t ht hqt
  have hqz : q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    exact hqt (by rw [h, zero_div])
  simp only [Pi.div_apply]
  field_simp

/-- **Eq. (19) for the digamma field with rational coefficients.**  An element
`R(s)·P(ψ, ψ′, …)` of `ℂ(s)⟨ψ⟩`, normalized by `s^{a}` and by the `D`-th power of the leading
logarithm, converges to the product of the leading coefficient of `R` and the coefficient of the pure
monomial `ψ^D`. -/
theorem tendsto_ratCoeff_jetPoly_vertical {σ : ℝ} (hσ : 0 < σ) {n N : ℕ}
    (p q : Polynomial ℂ) (hq : q ≠ 0) (d : Fin N → ℂ) (e : Fin N → Fin (n + 1) → ℕ)
    (D : ℕ) (β : Fin N) (hβpure : ∀ j : Fin n, e β j.succ = 0) (hβdeg : e β 0 = D)
    (hle : ∀ α, e α 0 ≤ D)
    (hother : ∀ α, α ≠ β → e α 0 < D ∨ ∃ j : Fin n, e α j.succ ≠ 0) :
    Tendsto (fun t : ℝ =>
      (p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q.natDegree
          * jetPoly d e (fun j : Fin (n + 1) => digammaJetLine σ (j : ℕ) t))
        / (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p.natDegree * (vertLog t) ^ D))
      atTop (nhds (p.leadingCoeff / q.leadingCoeff * d β)) := by
  have hrat := tendsto_ratio_eval_vertical σ p q hq
  have hjet := tendsto_jetPoly_digamma_div hσ d e D β hβpure hβdeg hle hother
  have hmul := hrat.mul hjet
  refine hmul.congr' ?_
  have hqlead : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hqq := tendsto_eval_div_pow_natDegree_vertical σ q
  filter_upwards [eventually_vertical_ne_zero σ, hqq.eventually_ne hqlead,
    eventually_vertLog_ne_zero] with t ht hqt hL
  have hqz : q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    exact hqt (by rw [h, zero_div])
  field_simp

end GaloisForLFunctions
