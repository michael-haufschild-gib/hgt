import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.OneHeckeEigenformIsBlindToHalvingPairs
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheTwoModeEnergiesRingDownAtTheZeroFreeRate
import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyZeroCascade
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# Halving descent leaves only the Shimura obstruction

If RH fails, a right-hand zero has nonzero zeta value at its half: otherwise
reflection after halving produces zeros converging to the nonzero value at
`2/3`. A sharp single-form energy rate must therefore vanish through the
Shimura factor at such a zero. This does not assert absence of other halving pairs.
-/

open Complex
open scoped UpperHalfPlane
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.RHTower.Gamma0MaassHecke (heckeH)

noncomputable section
namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HalvingPairs

/-- Failure of RH has a right-hand witness outside the halving pairs. -/
theorem exists_right_zero_not_halved (hnot : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 ∧
      riemannZeta (ρ / 2) ≠ 0 := by
  by_contra h
  push Not at h
  apply hnot
  rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  intro s hs
  by_cases hs1 : s.re < 1
  · exact _root_.RHTower.SquarefreeDiscrepancy.riemannZeta_ne_zero_of_halving
      (α := 1 / 4) (by norm_num)
      (fun ρ hρ hright hstrip => h ρ hρ (by linarith only [hright]) hstrip)
      (by linarith only [hs]) (by linarith only [hs1])
  · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hs1)

/-- Any halving pair forces the global zero abscissa to reach at least `2/3`. -/
theorem two_thirds_le_abscissa_of_halving_pair {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hpos : 0 < ρ.re) (hhalf : riemannZeta (ρ / 2) = 0) :
    (2 / 3 : ℝ) ≤ _root_.RHTower.zetaZeroAbscissa := by
  have hlt : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hρ
  have hre : (ρ / 2).re = ρ.re / 2 := by simp
  have href : riemannZeta (1 - ρ / 2) = 0 :=
    (_root_.RHTower.riemannZeta_one_sub_eq_zero_iff
      (by rw [hre]; linarith only [hpos]) (by rw [hre]; linarith only [hlt])).mpr hhalf
  have h₁ := _root_.RHTower.re_le_zetaZeroAbscissa hρ
  have h₂ := _root_.RHTower.re_le_zetaZeroAbscissa href
  rw [Complex.sub_re, Complex.one_re, hre] at h₂
  linarith only [h₁, h₂]

/-- The sharp energy rate of a cusp form. -/
def SharpEnergyRate (g : ℍ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (a : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
    ‖response (fun z => g z * starRingEnd ℂ (g z)) y - a‖ ≤ C * y ^ (3 / 4 - ε)

/-- RH gives the sharp rate for every cusp-form energy. -/
theorem sharpEnergyRate_of_riemannHypothesis {lam : ℝ} {g : ℍ → ℂ}
    (hg : g ∈ HeckeCusp.cuspSpace lam) (hRH : RiemannHypothesis) : SharpEnergyRate g := by
  intro ε hε
  have heps : 0 < min ε (1 / 4 : ℝ) := by
    rcases le_total ε (1 / 4 : ℝ) with h | h
    · rwa [min_eq_left h]
    · rw [min_eq_right h]
      norm_num
  obtain ⟨a, C, hC, hbound⟩ := pair_rate_of_zeroFree hg hg (Θ := 1 / 2)
    le_rfl (by norm_num)
    (_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH)
    heps (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  refine ⟨a, C, fun y hy hy1 => (hbound y hy hy1).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_ge hy hy1
  linarith only [min_le_left ε (1 / 4 : ℝ)]

/-- The remaining diagonal obstruction at a right zero outside the halving pairs. -/
def HasNonhalvingShimuraZero (g : ℍ → ℂ) : Prop :=
  ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 ∧
    riemannZeta (ρ / 2) ≠ 0 ∧
    GaloisForLFunctions.RHTower.HalfWeight.rsFold 1 (Shimura.kernel g) (ρ / 4 + 1 / 4) = 0

/-- A sharp energy rate forces its diagonal to vanish at every right-hand resonance. -/
theorem pairing_half_eq_zero_of_sharp_rate {lam : ℝ} {g : ℍ → ℂ}
    (hg : g ∈ HeckeCusp.cuspSpace lam) (hrate : SharpEnergyRate g)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρright : 1 / 2 < ρ.re) :
    pairing (ρ / 2) g g = 0 := by
  obtain ⟨a, C, hC⟩ := hrate ((ρ.re - 1 / 2) / 4) (by linarith only [hρright])
  exact seedTransform_half_eq_zero_of_rate (isSeed_pair hg hg) hC hρ
    (by linarith only [hρright]) (by linarith only [hρright])

section Hecke

variable {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) {c : ℕ → ℂ}
  (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) {r : ℤ → ℂ} (hr0 : r 0 = 0)
  (hr : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff g n y = r n * (Real.sqrt y : ℂ) *
    HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam))

include hg hc hr0 hr

/-- If a sharp Hecke energy rate coexists with failure of RH, its Shimura integral
vanishes at a nonhalving right zero, at a point with real part between `3/8` and `1/2`. -/
theorem sharp_rate_forces_shimura_zero (hg0 : g ≠ 0) (hr1 : r 1 ≠ 0)
    (hrate : SharpEnergyRate g) (hnot : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 ∧
      riemannZeta (ρ / 2) ≠ 0 ∧
      GaloisForLFunctions.RHTower.HalfWeight.rsFold 1 (Shimura.kernel g) (ρ / 4 + 1 / 4) = 0 ∧
      3 / 8 < (ρ / 4 + 1 / 4).re ∧ (ρ / 4 + 1 / 4).re < 1 / 2 := by
  obtain ⟨ρ, hρ, hright, hlt, hhalf⟩ := exists_right_zero_not_halved hnot
  have hs : 0 < (ρ / 2).re := by simp; linarith only [hright]
  have hslt : (ρ / 2).re < 1 / 2 := by simp; linarith only [hlt]
  have h12 : ρ / 2 ≠ 1 / 2 := by
    intro h
    rw [h] at hslt
    norm_num at hslt
  have h1 : ρ / 2 ≠ 1 := by
    intro h
    rw [h] at hslt
    norm_num at hslt
  have hzero := pairing_half_eq_zero_of_sharp_rate hg hrate hρ hright
  have hfold : GaloisForLFunctions.RHTower.HalfWeight.rsFold 1 (Shimura.kernel g)
      (wOf (ρ / 2)) = 0 := by
    by_contra hf
    exact ((pairing_self_ne_zero_iff_of_rho hg hc hr0 hr hg0 hr1 hs h12 h1).mpr
      ⟨hhalf, hf⟩) hzero
  have hw : wOf (ρ / 2) = ρ / 4 + 1 / 4 := by unfold wOf; ring
  rw [hw] at hfold
  refine ⟨ρ, hρ, hright, hlt, hhalf, hfold, ?_, ?_⟩ <;>
    simp <;> linarith only [hright, hlt]

/-- Halving descent removes the halving-pair condition. The exact remaining
condition is absence of a simultaneous nonhalving Shimura zero. -/
theorem riemannHypothesis_iff_sharp_rate_and_no_shimura_obstruction
    (hg0 : g ≠ 0) (hr1 : r 1 ≠ 0) :
    RiemannHypothesis ↔ SharpEnergyRate g ∧ ¬ HasNonhalvingShimuraZero g := by
  constructor
  · intro hRH
    refine ⟨sharpEnergyRate_of_riemannHypothesis hg hRH, ?_⟩
    rintro ⟨ρ, hρ, hright, _⟩
    exact (_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp
      hRH ρ hright) hρ
  · rintro ⟨hrate, hnone⟩
    by_contra hnot
    obtain ⟨ρ, hρ, hright, hlt, hhalf, hfold, _⟩ :=
      sharp_rate_forces_shimura_zero hg hc hr0 hr hg0 hr1 hrate hnot
    exact hnone ⟨ρ, hρ, hright, hlt, hhalf, hfold⟩

end Hecke

#print axioms exists_right_zero_not_halved
#print axioms two_thirds_le_abscissa_of_halving_pair
#print axioms sharpEnergyRate_of_riemannHypothesis
#print axioms pairing_half_eq_zero_of_sharp_rate
#print axioms sharp_rate_forces_shimura_zero
#print axioms riemannHypothesis_iff_sharp_rate_and_no_shimura_obstruction

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HalvingPairs
