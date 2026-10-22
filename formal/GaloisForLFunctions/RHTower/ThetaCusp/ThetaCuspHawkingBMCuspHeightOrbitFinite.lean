import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspOrbitIndex
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompactModularPeriodization

/-! The original high-cusp window has finite orbit support even without an upper height cutoff. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
noncomputable section

/-- A literal height profile with the original compact translation window. -/
def cuspHeightSeed (h : ℝ → ℂ) (z : UpperHalfPlane) : ℂ := (cuspWindow z.re : ℂ)*h z.im

/-- The actual height bound makes every windowed high-cusp orbit sum finitely supported. -/
theorem cuspHeightSeed_orbit_finite (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (z : UpperHalfPlane) : Function.HasFiniteSupport (fun γ : PSL2Z => cuspHeightSeed h (γ • z)) := by
  let M := max z.im (1/z.im)
  let K : Set ℂ := {w | w.re ∈ Icc (-1) 1 ∧ w.im ∈ Icc 2 M}
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKr : K ⊆ Set.range UpperHalfPlane.coe := by
    intro w hw
    rw [UpperHalfPlane.range_coe]
    change 0 < w.im
    linarith [hw.2.1]
  have hc : IsCompact (UpperHalfPlane.coe ⁻¹' K) :=
    UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage' hK hKr
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z)
    (isCompact_singleton (x := z)) hc
  apply hf.subset
  intro γ hγ
  have hw : cuspWindow (γ • z).re ≠ 0 := by
    intro hw
    exact hγ (by simp [cuspHeightSeed,hw])
  have hy : h (γ • z).im ≠ 0 := by
    intro hy
    exact hγ (by simp [cuspHeightSeed,hy])
  have hlo : -1 < (γ • z).re := lt_of_not_ge (fun he => hw (cuspWindow_zero_left he))
  have hhi : (γ • z).re < 1 := lt_of_not_ge (fun he => hw (cuspWindow_zero_right he))
  have htwo : 2 < (γ • z).im := lt_of_not_ge (fun he => hy (hh _ he))
  refine ⟨γ • z,⟨z,mem_singleton z,rfl⟩,?_⟩
  exact ⟨⟨hlo.le,hhi.le⟩,⟨htwo.le,modular_orbit_height_le γ z⟩⟩

/-- The complete high-cusp projective orbit sum is admitted at every original point. -/
theorem cuspHeightSeed_orbit_summable (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (z : UpperHalfPlane) : Summable (fun γ : PSL2Z => cuspHeightSeed h (γ • z)) :=
  summable_of_hasFiniteSupport (cuspHeightSeed_orbit_finite h hh z)

/-- The same finite support admits the full sum of orbit norms, before any regrouping. -/
theorem cuspHeightSeed_orbit_norm_summable (h : ℝ → ℂ) (hh : ∀ y ≤ 2, h y = 0)
    (z : UpperHalfPlane) : Summable (fun γ : PSL2Z => ‖cuspHeightSeed h (γ • z)‖) := by
  apply summable_of_hasFiniteSupport
  apply (cuspHeightSeed_orbit_finite h hh z).subset
  intro γ hγ hz
  apply hγ
  dsimp only at hz ⊢
  rw [hz,norm_zero]

end
end RHTower.D4BMModularCore
