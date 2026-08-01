import GaloisForLFunctions.HTGeometry.GammaFieldProjectiveBoundary
import GaloisForLFunctions.HTGeometry.RecurrenceCollapseAlmostPeriodic

/-!
# The recurrence collapse over the Gamma field

The projective boundary of `ℂ(s)⟨Γ⟩` supplies the coefficient limits, the monomials return along the
Bohr return times of the solution, and a Gamma-field monomial is eventually nonvanishing on the line.
So a finite differential relation whose coefficients are Gamma-field monomials collapses to a
nontrivial constant-coefficient relation — eq. (27) → (29) with the coefficients no longer restricted
to the rational subfield `ℂ(Γ)`.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The projective limit datum of a family of Gamma-field monomials normalized at `β`. -/
noncomputable def gammaFieldLimit {n : ℕ} (j : Fin n → ℕ) (p q : Fin n → Polynomial ℂ)
    (D : Fin n → ℕ) (β : Fin n) : Fin n → ℂ := fun α =>
  if j α = j β ∧ (p α * q β).natDegree = (q α * p β).natDegree ∧ D α = D β
    then (p α * q β).leadingCoeff / (q α * p β).leadingCoeff else 0

theorem eventually_gammaFieldElt_ne_zero (m j : ℕ) {p q : Polynomial ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (D : ℕ) : ∀ᶠ t : ℝ in atTop, gammaFieldElt m j p q D t ≠ 0 := by
  have hσ : (0 : ℝ) ≤ 1 / 2 + m := by positivity
  have hψ : ∀ᶠ t : ℝ in atTop,
      Complex.digamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [(tendsto_norm_digamma_vertical hσ).eventually_gt_atTop 0] with t ht
    intro h
    rw [h] at ht
    simp at ht
  filter_upwards [eventually_gamma_ne_zero m, eventually_eval_ne_zero (1 / 2 + m : ℝ) hp,
    eventually_eval_ne_zero (1 / 2 + m : ℝ) hq, hψ] with t hΓ hpt hqt hψt
  simp only [gammaFieldElt, gammaVerticalPoint]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hΓ) (div_ne_zero hpt hqt)) (pow_ne_zero _ hψt)

/-- **Eq. (27) → (29) for coefficients in the Gamma field.**  A finite differential relation whose
coefficients are monomials `Γ^j·(p/q)·ψ^D`, normalized by a lexicographically minimal member,
collapses along the Bohr return times to a nontrivial constant-coefficient relation. -/
theorem recurrence_collapse_gammaField {n m : ℕ} (F M : Fin n → ℂ → ℂ)
    (j : Fin n → ℕ) (p q : Fin n → Polynomial ℂ) (D : Fin n → ℕ) (β : Fin n)
    (hp : ∀ α, p α ≠ 0) (hq : ∀ α, q α ≠ 0)
    (hF : ∀ (α : Fin n) (t : ℝ),
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = gammaFieldElt m (j α) (p α) (q α) (D α) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * M α s = 0)
    (hMcont : ∀ α, Continuous fun t : ℝ =>
      M α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I))
    (hMap : ∀ α, IsBohrAlmostPeriodic fun t : ℝ =>
      M α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I))
    (hlex : ∀ α, j β < j α ∨ (j α = j β ∧
      ((p α * q β).natDegree < (q α * p β).natDegree ∨
        ((p α * q β).natDegree = (q α * p β).natDegree ∧ D α ≤ D β)))) :
    (∑ α, gammaFieldLimit j p q D β α * M α (((1 / 2 + m : ℝ) : ℂ)) = 0) ∧
      gammaFieldLimit j p q D β β = 1 := by
  classical
  have hcoeff : ∀ α : Fin n, Tendsto (fun t : ℝ =>
      F α (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        / F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhds (gammaFieldLimit j p q D β α)) := by
    intro α
    have hbase := tendsto_ratio_gammaFieldElt_lex m (p α) (q α) (p β) (q β)
      (hq α) (hq β) (hp β) (ja := j α) (jb := j β) (Da := D α) (Db := D β) (hlex α)
    refine hbase.congr fun t => ?_
    rw [hF α t, hF β t]
  have hFβ : ∀ᶠ t : ℝ in atTop,
      F β (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [eventually_gammaFieldElt_ne_zero m (j β) (hp β) (hq β) (D β)] with t ht
    rw [hF β t]
    exact ht
  exact recurrence_collapse_of_bohr_return F M β (((1 / 2 + m : ℝ) : ℂ))
    (gammaFieldLimit j p q D β) hrel hMcont hMap hFβ hcoeff

end GaloisForLFunctions
