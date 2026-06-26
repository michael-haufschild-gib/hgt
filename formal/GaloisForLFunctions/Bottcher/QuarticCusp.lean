/-
# The quartic defect vanishes at the cusp `i∞`

`F = θ₃⁴ − θ₂⁴ − θ₄⁴ → 1 − 0 − 1 = 0` as `im τ → ∞`, from the nullwert cusp limits
(`tendsto_thetaThree/Four_atImInfty → 1`, `tendsto_thetaTwo_atImInfty → 0`).

With the weight-2 transformation laws `quarticDefect_add_one`/`_S` (`QuarticDefect.lean`) transporting
this vanishing to the cusps `0` and `1`, `F` is a holomorphic weight-2 `Γ(2)` **cusp form**. The
Jacobi quartic identity `F ≡ 0` (⟹ `λ` omits `1`, hence `λ : ℍ → ℂ∖{0,1}`) is now reduced to the
single absent input `dim S₂(Γ(2)) = 0` (genus-0 compactified modular curve `X(Γ(2))` / the `Γ(2)`
valence formula — mathlib has only the level-one version).

Consumes `QuarticDefect` + `CuspLimits`. Mathlib only otherwise.
-/
import GaloisForLFunctions.Bottcher.QuarticDefect
import GaloisForLFunctions.Bottcher.CuspLimits
open Complex Filter Topology
open scoped Real
namespace Bottcher

theorem tendsto_quarticDefect_atImInfty :
    Tendsto quarticDefect (comap Complex.im atTop) (𝓝 0) := by
  have h := ((tendsto_thetaThree_atImInfty.pow 4).sub
    (tendsto_thetaTwo_atImInfty.pow 4)).sub (tendsto_thetaFour_atImInfty.pow 4)
  simpa [quarticDefect] using h

end Bottcher


namespace Bottcher

theorem thetaFour_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : thetaFour τ ≠ 0 := by
  have h := thetaProduct_ne_zero_of_im_pos hτ
  exact fun h0 => h (by rw [h0]; ring)

theorem modularLambda_ne_one_of_quartic {τ : ℂ} (hτ : 0 < τ.im) (hF : quarticDefect τ = 0) :
    modularLambda τ ≠ 1 := by
  intro hlam
  have h3 : thetaThree τ ≠ 0 := thetaThree_ne_zero_of_im_pos hτ
  have h4 : thetaFour τ ≠ 0 := thetaFour_ne_zero_of_im_pos hτ
  have heq : thetaTwo τ ^ 4 = thetaThree τ ^ 4 := by
    rw [modularLambda, div_pow] at hlam
    field_simp at hlam
    linear_combination hlam
  have hz : thetaFour τ ^ 4 = 0 := by
    rw [quarticDefect] at hF
    linear_combination -hF - heq
  exact h4 ((pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hz)

theorem modularLambda_omits_zero_one_of_quartic {τ : ℂ} (hτ : 0 < τ.im)
    (hF : quarticDefect τ = 0) : modularLambda τ ≠ 0 ∧ modularLambda τ ≠ 1 :=
  ⟨modularLambda_ne_zero_of_im_pos hτ, modularLambda_ne_one_of_quartic hτ hF⟩

end Bottcher


namespace Bottcher

/-- **Packaged interface: the Jacobi quartic identity ⟹ `λ` omits `{0,1}` on all of `ℍ`.**
The single hypothesis `hquartic : ∀ σ ∈ ℍ, F(σ) = 0` (the Jacobi quartic identity `θ₃⁴ = θ₂⁴ + θ₄⁴`,
equivalently `dim S₂(Γ(2)) = 0` applied to the weight-2 cusp form `F`) yields the range condition
`λ : ℍ → ℂ ∖ {0,1}`. Everything else feeding this is already unconditional and axiom-clean. -/
theorem modularLambda_omits_zero_one
    (hquartic : ∀ σ : ℂ, 0 < σ.im → quarticDefect σ = 0) {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda τ ≠ 0 ∧ modularLambda τ ≠ 1 :=
  modularLambda_omits_zero_one_of_quartic hτ (hquartic τ hτ)

/-- The range condition as a single membership: under the quartic identity, `λ τ ∈ ℂ ∖ {0,1}`. -/
theorem modularLambda_mem_compl_zero_one
    (hquartic : ∀ σ : ℂ, 0 < σ.im → quarticDefect σ = 0) {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda τ ∈ ({0, 1} : Set ℂ)ᶜ := by
  obtain ⟨h0, h1⟩ := modularLambda_omits_zero_one hquartic hτ
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h0, h1⟩

end Bottcher
