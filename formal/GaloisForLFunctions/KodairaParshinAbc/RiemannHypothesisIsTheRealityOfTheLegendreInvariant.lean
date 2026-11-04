import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfTheArakelovCoordinate
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# The Riemann hypothesis is the reality of the Legendre invariant

Every zero of `ζ` in the critical strip has ordinate `|Im ρ| ≥ 4`
(`RHTower.four_le_abs_im_of_zeta_zero`).  At such points the Legendre invariant
`J(ρ) = 256 (ρ² - ρ + 1)³ / (ρ²(ρ - 1)²)` is real exactly on the critical line
(`legendreInvariant_real_iff_critical`), so

  `RH ⟺ J(ρ) ∈ ℝ for every zero ρ of ζ in the critical strip`,

equivalently: the elliptic curve `E_ρ : y² = x(x - 1)(x - ρ)` has a real `j`-invariant for every
nontrivial zero `ρ`; equivalently, the level-one modular function `J(λ(τ))` is real at the corpus
modular lift `λ(τ) = w_ρ` of every nontrivial zero.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.KodairaParshinAbc

/-- **RH is the reality of the Legendre invariant at the nontrivial zeros.** -/
theorem riemannHypothesis_iff_legendreInvariant_real :
    RiemannHypothesis ↔ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
      (legendreInvariant ρ).im = 0 := by
  constructor
  · intro hRH ρ h0 h1 hz
    have him := RHTower.four_le_abs_im_of_zeta_zero h0 h1 hz
    refine (legendreInvariant_real_iff_critical h0 h1 (by linarith)).mpr ?_
    refine hRH ρ hz ?_ ?_
    · rintro ⟨n, hn⟩
      have : ρ.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro h
      rw [h, one_re] at h1
      exact lt_irrefl 1 h1
  · intro h
    rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_re_lt_half]
    intro s hs0 hs1 hz
    have h1 : s.re < 1 := by linarith
    have him := RHTower.four_le_abs_im_of_zeta_zero hs0 h1 hz
    have hcrit := (legendreInvariant_real_iff_critical hs0 h1 (by linarith)).mp (h s hs0 h1 hz)
    linarith

/-- **RH is the reality of the `j`-invariants of the Legendre curves of the zeros**: for every zero
`ρ` of `ζ` in the strip, `E_ρ : y² = x(x - 1)(x - ρ)` is elliptic, and RH holds iff all these
`j`-invariants are real. -/
theorem riemannHypothesis_iff_legendreCurve_j_real :
    RiemannHypothesis ↔ ∀ ρ : ℂ, (hρ : 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0) →
      haveI : WeierstrassCurve.IsElliptic (HTGeometry.LegendreDoubling.curve ρ) :=
        (legendre_isElliptic_iff ρ).mpr
          ⟨fun h => by rw [h, zero_re] at hρ; exact lt_irrefl 0 hρ.1,
            fun h => by rw [h, one_re] at hρ; exact lt_irrefl 1 hρ.2.1⟩
      (WeierstrassCurve.j (HTGeometry.LegendreDoubling.curve ρ)).im = 0 := by
  rw [riemannHypothesis_iff_legendreInvariant_real]
  refine forall_congr' fun ρ => ⟨fun h hρ => ?_, fun h h0 h1 hz => ?_⟩
  · rw [legendre_j]
    exact h hρ.1 hρ.2.1 hρ.2.2
  · have := h ⟨h0, h1, hz⟩
    rwa [legendre_j] at this

end GaloisForLFunctions.KodairaParshinAbc
