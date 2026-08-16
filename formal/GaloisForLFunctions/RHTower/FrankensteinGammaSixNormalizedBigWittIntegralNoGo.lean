import GaloisForLFunctions.RHTower.FrankensteinXiBidirectionalIntegralCartierSource
import GaloisForLFunctions.RHTower.DeningerGammaSixBigWittStokesSource
import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusRingEndomorphism

/-!
# The normalized Gamma-six Big-Witt source has no integral lift

The existing Gamma-six Stokes source is the rational Teichmüller cross-effect of `1/2` and `1/3`.
Its second ghost is `-1/3`, so it cannot be the scalar extension of an integral Big-Witt class.
This proves that the bidirectional integral Cartier source is not a relabelling or integral lift of
the `1/6`-normalized construction: the latter has an unavoidable denominator already in ghost
degree two.
-/

namespace RHTower

noncomputable section

/-- Exact denominator obstruction in the normalized Gamma-six source. -/
theorem deningerGammaSixBigWittStokesSource_ghost_two :
    deningerBigWittGhostComponent 2 (by omega)
      deningerGammaSixBigWittStokesSource = (-1 / 3 : ℚ) := by
  rw [deningerGammaSixBigWittStokesSource,
    deningerBigWittTeichmullerCrossEffect]
  simp
  norm_num

/-- No integral Big-Witt source scalar-extends to the normalized Gamma-six cross-effect. -/
theorem not_exists_integral_gammaSixBigWittStokesSource_lift :
    ¬ ∃ w : DeningerBigWittRing ℤ,
      deningerBigWittRingMap (Int.castRingHom ℚ) w =
        deningerGammaSixBigWittStokesSource := by
  rintro ⟨w, hw⟩
  have hg := congrArg (deningerBigWittGhostComponent 2 (by omega)) hw
  rw [← deningerBigWittGhostComponent_natural,
    deningerGammaSixBigWittStokesSource_ghost_two] at hg
  have hden := congrArg (fun q : ℚ => 3 * q) hg
  norm_num at hden
  have hint : 3 * deningerBigWittGhostComponent 2 (by omega) w = -1 := by
    exact_mod_cast hden
  omega

end

end RHTower
