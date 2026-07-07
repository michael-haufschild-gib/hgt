/-
Homotopy invariance of the winding number.

A continuously parametrised family of nonvanishing loops `H : ℝ → ℝ → ℂ` (each `H σ` a loop, i.e.
`H σ a = H σ b`) has a *constant* winding number in the parameter `σ`
(`windingNumber_homotopy_invariant`): the joint map `ℝ × ℝ → ℂ∖{0}` lifts through `exp` to a
continuous logarithm `G` on the contractible (hence simply connected) plane `ℝ × ℝ`, so
`G(σ,b) − G(σ,a) = 2πi·windingNumber(H σ)`; the left side is continuous in `σ` and the right forces the
integer `windingNumber(H σ)` to be continuous, hence locally constant, hence constant on the connected
line.

In particular two loops joined by such a homotopy through nonvanishing loops have equal winding number
(`windingNumber_of_homotopic`) — the deformation invariance that lets a general boundary be replaced by
a circle.
-/
import GaloisForLFunctions.RHTower.WindingNumber

open Complex Set

namespace RHTower

/-- **Homotopy invariance.**  A continuous family of nonvanishing loops has winding number constant in
the parameter: `windingNumber (H σ₀) a b = windingNumber (H σ₁) a b`. -/
theorem windingNumber_homotopy_invariant {H : ℝ → ℝ → ℂ} {a b : ℝ}
    (hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2))
    (hH0 : ∀ σ t, H σ t ≠ 0) (hHloop : ∀ σ, H σ a = H σ b) (σ₀ σ₁ : ℝ) :
    windingNumber (H σ₀) a b = windingNumber (H σ₁) a b := by
  have hsc : IsSimplyConnected (Set.univ : Set (ℝ × ℝ)) := by
    haveI : ContractibleSpace ↥(Set.univ : Set (ℝ × ℝ)) :=
      (Homeomorph.Set.univ (ℝ × ℝ)).contractibleSpace_iff.mpr inferInstance
    apply SimplyConnectedSpace.ofContractible
  obtain ⟨G, hGc0, hGe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_univ
    hHc.continuousOn (by rintro ⟨w, -, hw⟩; exact hH0 w.1 w.2 hw)
  rw [continuousOn_univ] at hGc0
  have hGexp : ∀ σ t, exp (G (σ, t)) = H σ t := fun σ t => by
    simpa [Function.comp] using hGe (Set.mem_univ (σ, t))
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hincr : ∀ σ, G (σ, b) - G (σ, a)
      = (windingNumber (H σ) a b : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    intro σ
    have hHσc : Continuous (H σ) := hHc.comp (continuous_const.prodMk continuous_id)
    have hLσc : Continuous (fun t => G (σ, t)) := hGc0.comp (continuous_const.prodMk continuous_id)
    have hLσ : IsLoop (H σ) a b := ⟨hHσc, fun t => hH0 σ t, hHloop σ⟩
    exact contLog_increment hLσ hLσc (fun t => hGexp σ t)
  set W : ℝ → ℤ := fun σ => windingNumber (H σ) a b with hW
  have hWcont : Continuous W := by
    rw [Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff]
    have hcomp : (Int.cast ∘ W : ℝ → ℂ)
        = fun σ => (G (σ, b) - G (σ, a)) / (2 * (Real.pi : ℂ) * I) := by
      funext σ; simp only [Function.comp_apply, hW]; rw [hincr σ]; field_simp
    rw [hcomp]
    exact (((hGc0.comp (continuous_id.prodMk continuous_const)).sub
      (hGc0.comp (continuous_id.prodMk continuous_const))).div_const _)
  have hlc : IsLocallyConstant W := (IsLocallyConstant.iff_continuous W).mpr hWcont
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ σ₀) (Set.mem_univ σ₁)

/-- **Deformation invariance.**  Two loops joined by a homotopy through nonvanishing loops have equal
winding number. -/
theorem windingNumber_of_homotopic {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} (H : ℝ → ℝ → ℂ)
    (hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2))
    (hH0 : ∀ σ t, H σ t ≠ 0) (hHloop : ∀ σ, H σ a = H σ b)
    (h0 : ∀ t, H 0 t = γ₀ t) (h1 : ∀ t, H 1 t = γ₁ t) :
    windingNumber γ₀ a b = windingNumber γ₁ a b := by
  have hkey := windingNumber_homotopy_invariant hHc hH0 hHloop 0 1
  rwa [show H 0 = γ₀ from funext h0, show H 1 = γ₁ from funext h1] at hkey

end RHTower
