import GaloisForLFunctions.RHTower.RectanglePoleWeightedLogDeriv
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling

/-!
# The residue unit against a weight with an interior pole

For `G(s) = (s − 1)ζ(s)`, an entire weight `φ`, and a rectangle whose boundary avoids the zeros of
`G`, with an interior point `s₀` where `G(s₀) ≠ 0`,

`∮ φ(z)(z − s₀)⁻¹ G'(z)/G(z) dz = 2πi (Σ_w ord_w(G) φ(w)/(w − s₀) + φ(s₀) G'(s₀)/G(s₀))`,

the sum over the zeros of `G` in the closed rectangle
(`rectIntegral_mul_inv_sub_mul_logDeriv_zetaResidueUnit`). This is the contour identity behind the
explicit formula for `ζ'/ζ` at a point of the critical strip.
-/

open Complex Set

namespace RHTower

noncomputable section

open Sieve

/-- Zeros of the residue unit in a rectangle with zero-free boundary lie strictly inside. -/
theorem zetaResidueUnitClosedRectangleZeros_strict {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₁.re : ℂ) + y * I) ≠ 0) :
    ∀ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
      z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
  intro w hw
  obtain ⟨hwK, hwzero⟩ := mem_zetaResidueUnitClosedRectangleZeros.mp hw
  obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
  have hwreU := hwre
  have hwimU := hwim
  rw [uIcc_of_le hre.le] at hwre
  rw [uIcc_of_le him.le] at hwim
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne hwre.1 fun heq => ?_
    have hedge : (z₁.re : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [heq]
    have hneG := hleft w.im hwimU
    rw [hedge] at hneG
    exact hneG hwzero
  · refine lt_of_le_of_ne hwre.2 fun heq => ?_
    have hedge : (z₂.re : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [heq]
    have hneG := hright w.im hwimU
    rw [hedge] at hneG
    exact hneG hwzero
  · refine lt_of_le_of_ne hwim.1 fun heq => ?_
    have hedge : (w.re : ℂ) + z₁.im * I = w := by apply Complex.ext <;> simp [heq]
    have hneG := hbot w.re hwreU
    rw [hedge] at hneG
    exact hneG hwzero
  · refine lt_of_le_of_ne hwim.2 fun heq => ?_
    have hedge : (w.re : ℂ) + z₂.im * I = w := by apply Complex.ext <;> simp [heq]
    have hneG := htop w.re hwreU
    rw [hedge] at hneG
    exact hneG hwzero

/-- **The residue unit against an entire weight with an interior simple pole.** -/
theorem rectIntegral_mul_inv_sub_mul_logDeriv_zetaResidueUnit
    {φ : ℂ → ℂ} {z₁ z₂ s₀ : ℂ} (hφ : AnalyticOnNhd ℂ φ Set.univ)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hs₀ : z₁.re < s₀.re ∧ s₀.re < z₂.re ∧ z₁.im < s₀.im ∧ s₀.im < z₂.im)
    (hs₀G : zetaResidueUnit s₀ ≠ 0)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re, zetaResidueUnit ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im, zetaResidueUnit ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => φ z * (z - s₀)⁻¹ * logDeriv zetaResidueUnit z) z₁ z₂ =
      2 * Real.pi * I * (∑ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * (φ w * (w - s₀)⁻¹) +
          φ s₀ * logDeriv zetaResidueUnit s₀) := by
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_zetaResidueUnit_closedRectangle_factorization z₁ z₂
  let V : Set ℂ := {z : ℂ | h z ≠ 0}
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hsubV : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ V := fun z hz => hhK z hz
  have hin := zetaResidueUnitClosedRectangleZeros_strict hre him hbot htop hright hleft
  have hne : ∀ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂, w ≠ s₀ := by
    intro w hw heq
    have := (mem_zetaResidueUnitClosedRectangleZeros.mp hw).2
    rw [heq] at this
    exact hs₀G this
  have hGfun : zetaResidueUnit =
      fun z => (∏ w ∈ zetaResidueUnitClosedRectangleZeros z₁ z₂, (z - w) ^ m w) * h z :=
    funext hfact
  have hres := rectIntegral_mul_inv_sub_mul_logDeriv_multi_zero
    (zetaResidueUnitClosedRectangleZeros z₁ z₂) (fun w => w) m (φ := φ) (h := h)
    (U := V) (hφ.mono (Set.subset_univ _)) hin hs₀ hne hsubV
    (hhan.mono (Set.subset_univ _)) (fun _ hz => hz)
  rw [hGfun]
  rw [hres]
  congr 2
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [← hGfun, hm w hw]

end

end RHTower
