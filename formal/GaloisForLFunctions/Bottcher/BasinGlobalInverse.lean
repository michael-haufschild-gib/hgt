/-
# The global analytic inverse `ψ = β⁻¹` of the connected Böttcher branch

Gap 2 produced the unconditional branch `β` on the basin `(filledJulia c)ᶜ`, a bijective covering
onto the exterior `{1 < ‖w‖}` with nonvanishing derivative. This file inverts it: `ψ` is analytic on
the exterior, maps into the basin, and satisfies `β ∘ ψ = id`, `ψ ∘ β = id`. The homeomorphism comes
from `Equiv.toHomeomorphOfContinuousOpen` (covering maps are open), and analyticity of the inverse
from `HasDerivAt.of_local_left_inverse` with `deriv β ≠ 0`.

`ψ` is the bridge to the full-unit-disk model `h(t) = t·ψ(1/t)` — the object whose natural boundary
(`natural_boundary_of_even_fe`) powers the connected-case transcendence.
-/
import GaloisForLFunctions.Bottcher.ConnectedBranchMandelbrot

open Set Metric Filter Topology

namespace Bottcher

noncomputable section

/-- **The connected branch together with its global analytic inverse.** For `c ∈ mandelbrot` there
are `β, ψ` with `β` the Gap-2 branch (analytic on the basin, extending the Böttcher coordinate, with
modulus `exp G_c`, exterior values, functional equation) and `ψ` analytic on `{1 < ‖w‖}`, valued in
the basin, inverting `β` on both sides. -/
theorem exists_global_branch_with_inverse_of_mem_mandelbrot (c : ℂ) (hcM : c ∈ mandelbrot) :
    ∃ β ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      (∀ z ∈ (filledJulia c)ᶜ, 1 < ‖β z‖) ∧
      (∀ z ∈ (filledJulia c)ᶜ, β (quadratic c z) = (β z) ^ 2) ∧
      AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖} ∧
      (∀ w : ℂ, 1 < ‖w‖ → ψ w ∈ (filledJulia c)ᶜ) ∧
      (∀ w : ℂ, 1 < ‖w‖ → β (ψ w) = w) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z) := by
  classical
  obtain ⟨β, hβan, hβesc, hβne, hβmod, hβgt, hβfe, hβiter, hβderiv, hβcov, hβbij⟩ :=
    exists_global_branch_covering_bijective_of_mem_mandelbrot c hcM
  set F : {z : ℂ // z ∈ (filledJulia c)ᶜ} → {w : ℂ // 1 < ‖w‖} :=
    fun z => ⟨β (z : ℂ), hβgt (z : ℂ) z.2⟩ with hF
  set Feq : {z : ℂ // z ∈ (filledJulia c)ᶜ} ≃ {w : ℂ // 1 < ‖w‖} :=
    Equiv.ofBijective F hβbij with hFeq
  have hFcont : Continuous F := hβcov.continuous
  have hFopen : IsOpenMap F := hβcov.isOpenMap
  set Fh := Feq.toHomeomorphOfContinuousOpen hFcont hFopen with hFh
  set ψ : ℂ → ℂ := fun w => if hw : 1 < ‖w‖ then (Fh.symm ⟨w, hw⟩ : ℂ) else 0 with hψdef
  have hψval : ∀ (w : ℂ) (hw : 1 < ‖w‖), ψ w = (Fh.symm ⟨w, hw⟩ : ℂ) := by
    intro w hw; rw [hψdef]; exact dif_pos hw
  have hψmem : ∀ w : ℂ, 1 < ‖w‖ → ψ w ∈ (filledJulia c)ᶜ := by
    intro w hw; rw [hψval w hw]; exact (Fh.symm ⟨w, hw⟩).2
  have hβψ : ∀ w : ℂ, 1 < ‖w‖ → β (ψ w) = w := by
    intro w hw
    rw [hψval w hw]
    have := Fh.apply_symm_apply ⟨w, hw⟩
    exact congrArg Subtype.val this
  have hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z := by
    intro z hz
    have h1 : 1 < ‖β z‖ := hβgt z hz
    rw [hψval (β z) h1]
    have hFz : F ⟨z, hz⟩ = ⟨β z, h1⟩ := rfl
    have := Fh.symm_apply_apply ⟨z, hz⟩
    rw [show Fh ⟨z, hz⟩ = F ⟨z, hz⟩ from rfl, hFz] at this
    exact congrArg Subtype.val this
  have hEopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hψcontOn : ContinuousOn ψ {w : ℂ | 1 < ‖w‖} := by
    rw [continuousOn_iff_continuous_restrict]
    have : Continuous (fun w : {w : ℂ // 1 < ‖w‖} => (Fh.symm w : ℂ)) :=
      continuous_subtype_val.comp Fh.symm.continuous
    apply this.congr
    intro w
    rw [Set.restrict_apply, hψval w.val w.2]
  have hψdiff : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖} := by
    intro w₀ hw₀
    have hw₀' : 1 < ‖w₀‖ := hw₀
    have hz₀ : ψ w₀ ∈ (filledJulia c)ᶜ := hψmem w₀ hw₀'
    have hg : ContinuousAt ψ w₀ := hψcontOn.continuousAt (hEopen.mem_nhds hw₀)
    have hf : HasDerivAt β (deriv β (ψ w₀)) (ψ w₀) :=
      ((hβan (ψ w₀) hz₀).differentiableAt).hasDerivAt
    have hf' : deriv β (ψ w₀) ≠ 0 := hβderiv (ψ w₀) hz₀
    have hfg : ∀ᶠ w in 𝓝 w₀, β (ψ w) = w := by
      filter_upwards [hEopen.mem_nhds hw₀] with w hw
      exact hβψ w hw
    exact (HasDerivAt.of_local_left_inverse hg hf hf' hfg).differentiableAt.differentiableWithinAt
  exact ⟨β, ψ, hβan, hβesc, hβmod, hβgt, hβfe,
    (hψdiff.analyticOnNhd hEopen), hψmem, hβψ, hψβ⟩

end

end Bottcher
