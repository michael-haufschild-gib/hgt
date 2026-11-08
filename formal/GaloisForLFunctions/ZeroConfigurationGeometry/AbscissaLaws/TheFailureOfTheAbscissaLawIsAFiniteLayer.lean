import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration

/-!
# The failure of the abscissa law is a finite layer

For a zero configuration (`not_abscissaLaw_iff_finite_layer`): AAL fails iff for some depth `h ≥ 0`
the zeros right of `½ + h` form a finite nonempty set, the **top layer**. Then
(`finite_layer_structure`):

* the reflection `ρ ↦ 1 − ρ̄` maps the top layer onto the **bottom layer** of zeros left of `½ − h`,
  which is finite and sits at the same heights;
* above the heights of both layers every zero lies in the narrower strip `|Re z − ½| ≤ h`.

So a world without AAL is a finite pair of layers at bounded height over a configuration confined to
a narrower strip: the rigid world of the contradiction search, here at the level of zero sets.
-/

open Complex Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

open ArithmeticCastelnuovoSeveri

variable (Z : ZeroConfig)

/-- The zeros left of `½ − h`. -/
def leftOf (h : ℝ) : Set ℂ := {ρ ∈ Z.carrier | ρ.re < 1 / 2 - h}

/-- **AAL fails exactly at a finite nonempty top layer.** -/
theorem not_abscissaLaw_iff_finite_layer :
    ¬ AbscissaLaw Z ↔ ∃ h : ℝ, 0 ≤ h ∧ (rightOf Z h).Finite ∧ (rightOf Z h).Nonempty := by
  constructor
  · intro hA
    simp only [AbscissaLaw, AbscissaLawAt, not_forall, not_le] at hA
    obtain ⟨h, hh, hfin, ρ, hρ, hre⟩ := hA
    exact ⟨h, hh, hfin, ρ, hρ, hre⟩
  · rintro ⟨h, hh, hfin, ρ, hρ, hre⟩ hA
    have := hA h hh hfin ρ hρ
    linarith

/-- The reflection maps the top layer onto the bottom layer. -/
theorem leftOf_eq_reflect_image (h : ℝ) : leftOf Z h = reflect '' rightOf Z h := by
  ext ρ
  constructor
  · rintro ⟨hρ, hre⟩
    refine ⟨reflect ρ, ⟨Z.reflect_mem ρ hρ, ?_⟩, by simp [reflect]⟩
    rw [ArithmeticCastelnuovoSeveri.re_reflect]; linarith
  · rintro ⟨z, ⟨hz, hre⟩, rfl⟩
    exact ⟨Z.reflect_mem z hz, by rw [ArithmeticCastelnuovoSeveri.re_reflect]; linarith⟩

/-- **The structure of a finite top layer.** The bottom layer is finite with the same heights, and
above the heights of the top layer every zero lies in `|Re z − ½| ≤ h`. -/
theorem finite_layer_structure {h : ℝ} (hfin : (rightOf Z h).Finite) :
    (leftOf Z h).Finite ∧
      Complex.im '' leftOf Z h = Complex.im '' rightOf Z h ∧
      ∃ T : ℝ, ∀ z ∈ Z.carrier, T < |z.im| → |z.re - 1 / 2| ≤ h := by
  have him : ∀ z : ℂ, (reflect z).im = z.im := fun z => by simp [reflect]
  refine ⟨by rw [leftOf_eq_reflect_image]; exact hfin.image _, ?_, ?_⟩
  · rw [leftOf_eq_reflect_image, ← Set.image_comp]
    exact Set.image_congr fun z _ => him z
  · obtain ⟨T, hT⟩ := (hfin.image fun z => |z.im|).bddAbove
    refine ⟨T, fun z hz hzT => ?_⟩
    have hright : z.re ≤ 1 / 2 + h := by
      by_contra hlt
      push Not at hlt
      have := hT ⟨z, ⟨hz, hlt⟩, rfl⟩
      linarith
    have hleft : 1 / 2 - h ≤ z.re := by
      by_contra hlt
      push Not at hlt
      have hmem : reflect z ∈ rightOf Z h :=
        ⟨Z.reflect_mem z hz, by rw [ArithmeticCastelnuovoSeveri.re_reflect]; linarith⟩
      have := hT ⟨reflect z, hmem, rfl⟩
      simp only [him] at this
      linarith
    rw [abs_le]
    constructor <;> linarith

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
