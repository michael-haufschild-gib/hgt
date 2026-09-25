import GaloisForLFunctions.RHTower.AngularEnergyQuantization
import GaloisForLFunctions.RHTower.OrbitQuadraticDiscriminant

/-!
# The two energies coincide at an on-line zero

This lane carries two energies built independently: the angular energy of a zero,
`Σ_{ρ'} (Re ρ − Re ρ')²/|ρ − ρ'|²`, summed over the divisor from a zero; and the critical-line
potential `U(t) = Σ_ρ δ_ρ²/(δ_ρ² + (t − Im ρ)²)`, summed over the divisor from a point of the line.
They are not the same functional: the first weights by the squared *difference* of displacements, the
second by the squared displacement itself.

At a zero of the critical line the two weights agree, because the base displacement is zero. The
identity is exact and holds termwise, including on the diagonal, where both sides vanish — the
angular term by its guard and the bump because the base zero is on the line. So

  `angularEnergy ρ₀ = U(Im ρ₀)`  whenever `Re ρ₀ = 1/2`.

The consequence is that the two thresholds recorded separately for these objects are one threshold.
In particular an on-line zero that shares its ordinate with an off-line zero carries angular energy at
least two, the off-line pair contributing a full unit each at that ordinate.
-/

open Complex

namespace RHTower

noncomputable section

/-- Termwise identity: at an on-line base zero the angular term is the bump at its ordinate. -/
theorem angularEnergyTerm_eq_poissonBumpTerm {ρ₀ : XiDivisorSupport} (h : (ρ₀ : ℂ).re = 1 / 2)
    (ρ : XiDivisorSupport) :
    angularEnergyTerm ρ₀ ρ = poissonBumpTerm ((ρ₀ : ℂ).im) ρ := by
  rw [angularEnergyTerm, poissonBumpTerm]
  by_cases hρ : ρ = ρ₀
  · subst hρ
    rw [if_pos rfl, h]
    norm_num
  · rw [if_neg hρ, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, h]
    congr 1
    · ring
    · ring

/-- **The two energies coincide at an on-line zero.** -/
theorem angularEnergy_eq_poissonPotential {ρ₀ : XiDivisorSupport} (h : (ρ₀ : ℂ).re = 1 / 2) :
    angularEnergy ρ₀ = poissonPotential ((ρ₀ : ℂ).im) :=
  tsum_congr (angularEnergyTerm_eq_poissonBumpTerm h)

/-- An on-line zero sharing its ordinate with an off-line zero carries angular energy at least two. -/
theorem two_le_angularEnergy_of_offLine_same_ordinate {ρ₀ ρ : XiDivisorSupport}
    (h₀ : (ρ₀ : ℂ).re = 1 / 2) (hoff : (ρ : ℂ).re ≠ 1 / 2)
    (hord : (ρ : ℂ).im = (ρ₀ : ℂ).im) : 2 ≤ angularEnergy ρ₀ := by
  rw [angularEnergy_eq_poissonPotential h₀, ← hord]
  exact two_le_poissonPotential hoff

end

end RHTower
