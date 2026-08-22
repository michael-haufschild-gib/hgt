import GaloisForLFunctions.RHTower.ConnesLocalDivision

/-!
# Appendix I (27)(28), localized

Appendix I (27)(28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesLocalDivision` discharges the division hypothesis on a window; the corpus's point-support
structure theorem then says that, after cutting off to that window, a functional annihilated by
every multiple of `φ` is a finite combination of derivatives of the Dirac mass at the zero.  This
is Connes' statement that the solutions of `φ·α = 0` are spanned by the `δ^{(k)}` at the zeros of
`φ`, of order below the multiplicity — localized at one zero, which is how the paper uses it.
-/

open Set
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Appendix I (27)(28), localized at one zero.** -/
theorem connes_division_structure_local {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (u : SchwartzMap ℝ ℂ →L[ℂ] X) (φ : ℝ → ℂ) {R : ℝ}
    (hφsmooth : ContDiff ℝ ∞ φ)
    (hφne : ∀ x : ℝ, x ∈ Ioo (-R) R → x ≠ 0 → φ x ≠ 0)
    (hmul : ∀ ψ χ : SchwartzMap ℝ ℂ,
      ((ψ : ℝ → ℂ) = fun x => φ x * (χ : ℝ → ℂ) x) → u ψ = 0)
    (η : SchwartzMap ℝ ℂ) (hηsupp : tsupport ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ Ioo (-R) R) :
    ∃ (N : ℕ) (c : ℕ → X), ∀ ψ : SchwartzMap ℝ ℂ,
      u (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ψ)
        = ∑ j ∈ Finset.range (N + 1), (iteratedDeriv j (ψ : ℝ → ℂ) 0) • c j := by
  have hηtg : Function.HasTemperateGrowth ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    η.hasTemperateGrowth
  set M : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) with hM
  have hMsupp : ∀ ψ : SchwartzMap ℝ ℂ,
      tsupport ((M ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ Ioo (-R) R := by
    intro ψ
    refine subset_trans (closure_mono ?_) hηsupp
    intro x hx
    have hx' : ((M ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x ≠ 0 := hx
    rw [hM, SchwartzMap.smulLeftCLM_apply_apply hηtg] at hx'
    intro hcon
    rw [hcon, zero_smul] at hx'
    exact hx' rfl
  have hkill : ∀ ψ : SchwartzMap ℝ ℂ,
      (∃ δ > 0, ∀ x : ℝ, |x| ≤ δ → (ψ : ℝ → ℂ) x = 0) → (u.comp M) ψ = 0 := by
    intro ψ hψ
    obtain ⟨δ, hδ, hv⟩ := hψ
    rw [ContinuousLinearMap.comp_apply]
    refine connes_division_kills_local u φ hφsmooth hφne hmul (M ψ) (hMsupp ψ) ⟨δ, hδ, ?_⟩
    intro x hx
    rw [hM, SchwartzMap.smulLeftCLM_apply_apply hηtg, hv x hx, smul_zero]
  obtain ⟨N, c, hc⟩ := exists_delta_representation (u.comp M) hkill
  refine ⟨N, c, fun ψ => ?_⟩
  have hcψ := hc ψ
  rwa [ContinuousLinearMap.comp_apply] at hcψ

end

end GaloisForLFunctions.RHTower
