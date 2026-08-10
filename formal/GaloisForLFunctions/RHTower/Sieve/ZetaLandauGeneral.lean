import GaloisForLFunctions.RHTower.Sieve.LandauRealPart
import GaloisForLFunctions.RHTower.Sieve.ZetaDerivBound

/-!
# Landau's lemma for `ζ` against an arbitrary growth bound

`zeta_landau_at` fixes the radius at `1/4` and feeds in the crude bound `‖ζ‖ ≤ 7 + 2|γ|`, whose
logarithm is `≍ log|γ|`.  That choice is what limits the resulting zero-free region to width
`≍ 1/log|γ|`: the remainder of Landau's estimate is `16 log M / R`, and shrinking `R` without
improving `M` only makes it worse.

Stating the step against the *pair* `(R, Φ)` decouples the two.  A growth bound `Φ` valid on a disc
of radius `R₀` gives a remainder `16 log(Φ/‖ζ(c)‖)/R`, and any later improvement of either input
substitutes with no downstream work.
-/

namespace RHTower.Sieve

open Metric Complex

/-- **Landau's lemma for `ζ` with a general radius and a general growth bound.** -/
theorem zeta_landau_of_bound {c : ℂ} {R R₀ Φ : ℝ}
    (hR : 0 < R) (hRR₀ : R < R₀)
    (hne : ∀ w ∈ ball c R₀, w ≠ 1)
    (hgrow : ∀ w ∈ ball c R₀, ‖riemannZeta w‖ ≤ Φ)
    (hcre : 1 ≤ c.re) (hcΦ : ‖riemannZeta c‖ < Φ) :
    ∃ (Z₁ : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z₁, ‖ρ - c‖ ≤ R / 2) ∧ (∀ ρ ∈ Z₁, riemannZeta ρ = 0) ∧
      (∀ w : ℂ, ‖w - c‖ ≤ R / 2 → riemannZeta w = 0 → w ∈ Z₁) ∧
      (∀ ρ ∈ Z₁, 1 ≤ m ρ) ∧
      ∀ S ⊆ Z₁,
        -(logDeriv riemannZeta c).re
          ≤ 16 * Real.log (Φ / ‖riemannZeta c‖) / R
            - ∑ ρ ∈ S, (m ρ : ℝ) * ((c - ρ)⁻¹).re := by
  have hf : AnalyticOnNhd ℂ riemannZeta (ball c R₀) :=
    (differentiableOn_riemannZeta_of_ne_one hne).analyticOnNhd isOpen_ball
  have hfc : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re hcre
  have hfcpos : (0 : ℝ) < ‖riemannZeta c‖ := norm_pos_iff.mpr hfc
  set M : ℝ := Φ / ‖riemannZeta c‖ with hMdef
  have hM1 : 1 < M := by
    rw [hMdef, lt_div_iff₀ hfcpos, one_mul]
    exact hcΦ
  have hbound : ∀ w ∈ ball c R₀, ‖riemannZeta w‖ ≤ M * ‖riemannZeta c‖ := by
    intro w hw
    rw [hMdef, div_mul_cancel₀ _ (ne_of_gt hfcpos)]
    exact hgrow w hw
  obtain ⟨Z₁, m, hZ₁, hzero, hmem, hmult, hkey⟩ :=
    neg_re_logDeriv_le hR hRR₀ hM1 hf hfc hbound
  refine ⟨Z₁, m, hZ₁, hzero, hmem, hmult, ?_⟩
  intro S hS
  have hre : ∀ ρ ∈ Z₁, ρ.re ≤ c.re := by
    intro ρ hρ
    by_contra hcon
    have hgt : c.re < ρ.re := lt_of_not_ge hcon
    exact riemannZeta_ne_zero_of_one_le_re (by linarith) (hzero ρ hρ)
  have h := hkey c (by rw [sub_self, norm_zero]; positivity) hfc hre S hS
  simpa [hMdef] using h

/-- **The logarithmic derivative is bounded by the Landau remainder alone.**  Every retained zero
lies to the left of the centre, so its term has nonnegative real part and may be discarded. -/
theorem neg_re_logDeriv_le_of_bound {c : ℂ} {R R₀ Φ : ℝ}
    (hR : 0 < R) (hRR₀ : R < R₀)
    (hne : ∀ w ∈ ball c R₀, w ≠ 1)
    (hgrow : ∀ w ∈ ball c R₀, ‖riemannZeta w‖ ≤ Φ)
    (hcre : 1 ≤ c.re) (hcΦ : ‖riemannZeta c‖ < Φ) :
    -(logDeriv riemannZeta c).re ≤ 16 * Real.log (Φ / ‖riemannZeta c‖) / R := by
  obtain ⟨Z₁, m, _, _, _, _, hkey⟩ :=
    zeta_landau_of_bound hR hRR₀ hne hgrow hcre hcΦ
  have h := hkey ∅ (Finset.empty_subset _)
  rwa [Finset.sum_empty, sub_zero] at h

end RHTower.Sieve
