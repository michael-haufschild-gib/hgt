import GaloisForLFunctions.CollectiveDiophantineGeometry.TwoSidedGapIteration
import GaloisForLFunctions.RHTower.EvenLandauPairTest
import GaloisForLFunctions.SignFreePurityMechanisms.SeparationForcesRationality

/-!
# The height separates the zeros exactly when the prime traces are bounded

The reflection `ρ ↦ 1 − conj ρ` preserves the nontrivial zeros of `ζ` and their height `Im ρ`.
By the separation principle a zero alone at its height lies on the critical line
(`re_eq_half_of_injOn_im`). Quantitatively, the horizontal spread of the fibres of the height map
is twice the zero width (`fibre_spread_le_iff_zetaZeroWidth_le`), and the zero width is the growth
exponent of the absolute cubic-spline trace at the primes. Hence:

* every two zeros at one height have real parts within `2σ` of each other exactly when
  `|c(log p)| ≤ K p ^ σ` at every prime (`fibre_spread_le_iff_twoSided_primes`);
* the height is injective on the zeros exactly when the traces at the primes are bounded, exactly
  when the Riemann hypothesis holds (`injOn_im_iff_twoSided_primes`,
  `injOn_im_iff_riemannHypothesis`).

The prime-side quantity carries no sign.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.SignFreePurityMechanisms

open Zeta23 SquareRootThreshold CollectiveDiophantineGeometry

/-- The reflection preserves the height. -/
theorem reflect_im (ρ : ℂ) : (Zeta23.reflect ρ).im = ρ.im := by
  simp [Zeta23.reflect]

/-- The reflection mirrors the real part in `½`. -/
theorem reflect_re (ρ : ℂ) : (Zeta23.reflect ρ).re = 1 - ρ.re := by
  simp [Zeta23.reflect]

/-- **Separation for `ζ`.** If the height is injective on the nontrivial zeros, every zero is
fixed by the reflection, hence on the critical line. -/
theorem re_eq_half_of_injOn_im (hinj : Set.InjOn Complex.im zetaZeroConfig.carrier) {ρ : ℂ}
    (hρ : ρ ∈ zetaZeroConfig.carrier) : ρ.re = 1 / 2 := by
  have hfix : Zeta23.reflect ρ = ρ :=
    fixed_of_injOn (fun z hz => zetaZeroConfig.reflect_mem z hz) (fun z _ => reflect_im z) hinj hρ
  have hre := congrArg Complex.re hfix
  rw [reflect_re] at hre
  linarith only [hre]

/-- The horizontal spread of the fibres of the height map is twice the zero width. -/
theorem fibre_spread_le_iff_zetaZeroWidth_le {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ.im = ρ'.im →
      |ρ.re - ρ'.re| ≤ 2 * σ) ↔ zetaZeroWidth ≤ σ := by
  constructor
  · intro h
    refine Real.sSup_le ?_ hσ
    rintro _ ⟨ρ, hρ, rfl⟩
    have hspread := h ρ hρ _ (zetaZeroConfig.reflect_mem ρ hρ) (reflect_im ρ).symm
    have hform : ρ.re - (Zeta23.reflect ρ).re = 2 * (ρ.re - 1 / 2) := by
      rw [reflect_re]
      ring
    rw [hform, abs_mul, abs_two] at hspread
    linarith only [hspread]
  · intro h ρ hρ ρ' hρ' _
    have h1 := (abs_re_sub_half_le_zetaZeroWidth hρ).trans h
    have h2 := (abs_re_sub_half_le_zetaZeroWidth hρ').trans h
    have hform : ρ.re - ρ'.re = (ρ.re - 1 / 2) - (ρ'.re - 1 / 2) := by ring
    rw [hform]
    exact (abs_sub _ _).trans (by linarith only [h1, h2])

/-- **The spread of the fibres is the growth exponent of the absolute prime traces.** -/
theorem fibre_spread_le_iff_twoSided_primes {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ.im = ρ'.im →
      |ρ.re - ρ'.re| ≤ 2 * σ) ↔
      ∃ K : ℝ, ∀ p : ℕ, p.Prime → |splineTrace (Real.log p)| ≤ K * (p : ℝ) ^ σ :=
  (fibre_spread_le_iff_zetaZeroWidth_le hσ).trans (zeroWidth_iff_twoSided_primes hσ)

/-- Injectivity of the height is zero spread. -/
theorem injOn_im_iff_spread_zero :
    Set.InjOn Complex.im zetaZeroConfig.carrier ↔
      ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ.im = ρ'.im →
        |ρ.re - ρ'.re| ≤ 2 * 0 := by
  constructor
  · intro h ρ hρ ρ' hρ' him
    rw [h hρ hρ' him]
    simp
  · intro h ρ hρ ρ' hρ' him
    have hre := h ρ hρ ρ' hρ' him
    rw [mul_zero] at hre
    exact Complex.ext (sub_eq_zero.mp (abs_nonpos_iff.mp hre)) him

/-- **The height separates the zeros exactly when the absolute prime traces are bounded.** -/
theorem injOn_im_iff_twoSided_primes :
    Set.InjOn Complex.im zetaZeroConfig.carrier ↔
      ∃ K : ℝ, ∀ p : ℕ, p.Prime → |splineTrace (Real.log p)| ≤ K := by
  rw [injOn_im_iff_spread_zero, fibre_spread_le_iff_twoSided_primes le_rfl]
  simp only [Real.rpow_zero, mul_one]

/-- The height separates the zeros exactly when the Riemann hypothesis holds. -/
theorem injOn_im_iff_riemannHypothesis :
    Set.InjOn Complex.im zetaZeroConfig.carrier ↔ RiemannHypothesis :=
  injOn_im_iff_twoSided_primes.trans riemannHypothesis_iff_twoSided_primes.symm

#print axioms re_eq_half_of_injOn_im
#print axioms fibre_spread_le_iff_twoSided_primes
#print axioms injOn_im_iff_twoSided_primes
#print axioms injOn_im_iff_riemannHypothesis

end GaloisForLFunctions.SignFreePurityMechanisms
