import GaloisForLFunctions.HTGeometry.BohrHullDual
import GaloisForLFunctions.HTGeometry.CompactAbelianPeterWeyl

/-!
# Hull characters separate points

Peter–Weyl produces, for any nonzero point of a compact abelian group, a continuous character not
trivial there; on the Bohr hull every continuous character is the character of a hull frequency.
Together: two points of the hull with the same value under every frequency character coincide.

This makes the evaluation map of the hull into the product of circles indexed by the frequency group
injective, hence — the hull being compact — a homeomorphism onto its image.
-/

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

variable {f : ℝ →ᵇ ℂ}

/-- **Frequency characters separate the points of the hull.** -/
theorem bohrHullChar_separates (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {x y : BohrHull f}
    (h : ∀ lam : ℝ, IsBohrHullFrequency f lam →
      bohrHullChar f lam x = bohrHullChar f lam y) : x = y := by
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  by_contra hne
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨χ, hcont, hmul, hnorm, hne1⟩ := CompactAbelian.exists_character_ne_one hxy
  obtain ⟨lam, hlam, hχ⟩ := exists_frequency_of_hull_character hf htb hcont hmul hnorm
  have hy0 : χ y ≠ 0 := by
    intro hzero
    have hn := hnorm y
    rw [hzero, norm_zero] at hn
    norm_num at hn
  have hxeqχ : χ x = χ y := by
    rw [hχ]
    exact h lam hlam
  have hval : χ (x - y) = 1 := by
    have h1 : χ (x - y) * χ y = χ x := by
      rw [← hmul]
      congr 1
      abel
    rw [hxeqχ] at h1
    field_simp at h1
    exact h1
  exact hne1 hval

end GaloisForLFunctions
