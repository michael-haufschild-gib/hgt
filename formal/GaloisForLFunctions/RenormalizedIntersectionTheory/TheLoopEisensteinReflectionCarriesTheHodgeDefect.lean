import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRenormalizedHodgeIndex
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1XiCoefficients
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges

/-!
# The loop-Eisenstein reflection carries the Hodge defect

The constant term of the affine `A_1` loop Eisenstein series is a Weyl sum whose coefficients are
Gindikin–Karpelevich products of the rank-one intertwining factor
`c(s) = Λ(s)/Λ(s + 1)` (`HTGeometry.LoopEisenstein.AffineA1.xiRatio`), `Λ` the completed zeta function.
It is a global object: every place enters through `Λ`. Its singular set in the band
`−1/2 < Re s < 0` is where the denominator `Λ(s + 1)` vanishes, i.e. `s + 1` is a zero of `ζ` right of
the critical line.

* **The band poles count the Hodge defect** (`boostPolarIndex_ratCorr_eq_encard_reflectionPoles`):
  the number of denominator zeros of `c` in the band `−1/2 < Re s < 0` is the index of Weil's
  correlation on the pole-orthogonal hyperplane.
* **Hodge index ⇔ no band poles** (`renormalizedHodgeIndex_iff_reflectionPoles_eq_empty`,
  `riemannHypothesis_iff_reflectionPoles_eq_empty`).

So the loop Eisenstein series is a global carrier of the renormalized pairing's sign datum: the
intertwining factor that assembles its constant term has a singularity in the band exactly for each
negative square of the pairing on the pole-orthogonal hyperplane.
-/

open GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The denominator zeros of the loop-Eisenstein intertwining factor `Λ(s)/Λ(s + 1)` in the band
`−1/2 < Re s < 0`. -/
def reflectionPoles : Set ℂ :=
  {s | completedRiemannZeta (s + 1) = 0 ∧ -(1 / 2) < s.re ∧ s.re < 0}

/-- In the right half-plane the completed zeta function vanishes exactly where `ζ` does. -/
theorem completedRiemannZeta_eq_zero_iff {w : ℂ} (hw : 0 < w.re) :
    completedRiemannZeta w = 0 ↔ riemannZeta w = 0 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  rw [riemannZeta_def_of_ne_zero hw0, div_eq_zero_iff,
    or_iff_left (Complex.Gammaℝ_ne_zero_of_re_pos hw)]

/-- A right zero of `ζ` is a zero of `Λ` in the strip right of the critical line. -/
theorem mem_rightZeros_iff {ρ : ℂ} :
    ρ ∈ rightZeros zetaZeroConfig ↔ completedRiemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 := by
  rw [rightZeros, Set.mem_setOf_eq,
    RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip]
  constructor
  · rintro ⟨⟨hxi, h0, h1⟩, hhalf⟩
    have hne : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
    exact ⟨(completedRiemannZeta_eq_zero_iff h0).mpr ((RHTower.xi_eq_zero_iff h0 hne).mp hxi),
      hhalf, h1⟩
  · rintro ⟨hΛ, hhalf, h1⟩
    have h0 : 0 < ρ.re := by linarith
    have hne : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
    exact ⟨⟨(RHTower.xi_eq_zero_iff h0 hne).mpr ((completedRiemannZeta_eq_zero_iff h0).mp hΛ),
      h0, h1⟩, hhalf⟩

/-- The band poles are the right zeros shifted by `−1`. -/
theorem image_reflectionPoles : (fun s : ℂ => s + 1) '' reflectionPoles = rightZeros zetaZeroConfig := by
  ext ρ
  rw [mem_rightZeros_iff]
  constructor
  · rintro ⟨s, ⟨hΛ, h1, h2⟩, rfl⟩
    refine ⟨hΛ, ?_, ?_⟩ <;> simp only [Complex.add_re, Complex.one_re] <;> linarith
  · rintro ⟨hΛ, h1, h2⟩
    refine ⟨ρ - 1, ⟨by simpa using hΛ, ?_, ?_⟩, by ring⟩ <;>
      simp only [Complex.sub_re, Complex.one_re] <;> linarith

/-- **The band poles of the loop-Eisenstein intertwining factor count the Hodge defect.** -/
theorem boostPolarIndex_ratCorr_eq_encard_reflectionPoles :
    boostPolarIndex ratCorr = reflectionPoles.encard := by
  rw [boostPolarIndex_ratCorr, negIndex_zetaKernel, ← image_reflectionPoles,
    (add_left_injective (1 : ℂ)).injOn.encard_image]

/-- **The renormalized Hodge index holds iff the intertwining factor has no band poles.** -/
theorem renormalizedHodgeIndex_iff_reflectionPoles_eq_empty :
    RenormalizedHodgeIndex ratCorr ↔ reflectionPoles = ∅ := by
  rw [RenormalizedHodgeIndex, boostPolarIndex_ratCorr_eq_encard_reflectionPoles,
    Set.encard_eq_zero]

/-- **RH is the absence of band poles of the loop-Eisenstein intertwining factor.** -/
theorem riemannHypothesis_iff_reflectionPoles_eq_empty :
    RiemannHypothesis ↔ reflectionPoles = ∅ := by
  rw [riemannHypothesis_iff_renormalizedHodgeIndex,
    renormalizedHodgeIndex_iff_reflectionPoles_eq_empty]

/-- The band poles are exactly where the rank-one coefficient `xiRatio` of the loop Eisenstein
series has a vanishing denominator. -/
theorem mem_reflectionPoles_iff (s : ℂ) :
    s ∈ reflectionPoles ↔
      completedRiemannZeta (s + 1) = 0 ∧ -(1 / 2) < s.re ∧ s.re < 0 ∧
        LoopEisenstein.AffineA1.xiRatio s =
          completedRiemannZeta s / completedRiemannZeta (s + 1) :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2, rfl⟩, fun h => ⟨h.1, h.2.1, h.2.2.1⟩⟩

end GaloisForLFunctions.RenormalizedIntersectionTheory
