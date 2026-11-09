import GaloisForLFunctions.SurfaceOfSpecZ.ThePlaneCountsAtTheIntegerDegrees
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovCountAtThePrimeDegrees

/-!
# The effective classes of the prime planes

The count door of `ThePlaneCountsAtTheIntegerDegrees` asks for a binary `ℕ`-count with Tate limit
`δ_n(x, y) = c_B(0)x² + 2c_B(log n)xy + c_B(0)y²` on every plane `⟨Γ_1, Γ_n⟩`. Since one side at the
primes decides RH (`TheStepanovCountAtThePrimeDegrees`), much less is needed:

* `riemannHypothesis_iff_primePlanes_copositive`: RH holds iff every prime defect form `δ_p` is
  nonnegative on the effective classes `xΓ_1 + yΓ_p`, `x, y ≥ 0`;
* `riemannHypothesis_iff_effectivePrimeCounts`: RH holds iff for every prime `p` the single effective
  class `Γ_1 + Γ_p` carries an `ℕ`-count along its ray with Tate limit `δ_p(1, 1) = 2c_B(0) + 2c_B(log p)`.

On `C × C` the effective classes `xΔ + yΓ_F` meet with `Δ · Γ_F = N_1 ≥ 0`; the bound needed here is
the Stepanov bound, an upper bound on the smoothed point count `−c_B(log p) ≤ c_B(0)`, at the prime
degrees only.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri CountingHolography

theorem planeDefect_one_one (n : ℕ) :
    planeDefect n (1, 1) = 2 * zetaScalingDatum.orbitCorr splineCycle 0 +
      2 * zetaScalingDatum.orbitCorr splineCycle (Real.log n) := by
  simp only [planeDefect]; push_cast; ring

/-- **RH is copositivity of the prime planes.** -/
theorem riemannHypothesis_iff_primePlanes_copositive :
    RiemannHypothesis ↔ ∀ p : ℕ, p.Prime → ∀ x y : ℕ, 0 ≤ planeDefect p (x, y) := by
  constructor
  · intro hRH p hp x y
    have h := (riemannHypothesis_iff_hasseWeil_integerDegrees.mp hRH) p hp.pos
    rw [ScalingDatum.HasseWeilAt] at h
    have h1 := (abs_nonneg _).trans h
    have h2 := (abs_le.mp h).1
    simp only [planeDefect]
    push_cast
    have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
    nlinarith [sq_nonneg ((x : ℝ) - y), mul_nonneg hx hy,
      mul_le_mul_of_nonneg_right h2 (mul_nonneg hx hy)]
  · intro h
    rw [riemannHypothesis_iff_bddBelow_primeDegrees']
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun p hp => ?_⟩
    have := h p hp 1 1
    rw [show ((1 : ℕ) : ℤ) = 1 from rfl, planeDefect_one_one] at this
    linarith

/-- **The count door at the effective prime classes.** -/
theorem riemannHypothesis_iff_effectivePrimeCounts :
    RiemannHypothesis ↔ ∀ p : ℕ, p.Prime → ∃ K : ℕ → ℕ,
      Tendsto (fun m : ℕ => (K m : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (planeDefect p (1, 1))) := by
  constructor
  · intro hRH p hp
    have h := riemannHypothesis_iff_primePlanes_copositive.mp hRH p hp 1 1
    exact ⟨fun m => ⌊(m : ℝ) ^ 2 * planeDefect p (1, 1)⌋₊, tendsto_floor_div_sq h⟩
  · intro h
    rw [riemannHypothesis_iff_bddBelow_primeDegrees']
    refine ⟨zetaScalingDatum.orbitCorr splineCycle 0, fun p hp => ?_⟩
    obtain ⟨K, hK⟩ := h p hp
    have hnn : 0 ≤ planeDefect p (1, 1) :=
      ge_of_tendsto' hK fun m => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [planeDefect_one_one] at hnn
    linarith

end GaloisForLFunctions.SurfaceOfSpecZ
