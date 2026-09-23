import GaloisForLFunctions.RHTower.XiMassPrimeApertureGap

/-!
# Canonical semigroup aperture high-pass for the Xi prime source

Choose fixed mass `1` and Euler depth `3/4`.  The co-moving mass `|u|+2` is exactly an additional
mass deformation of this fixed carrier, with second mass `sqrt ((|u|+2)^(2 : ℕ)-1)`.  Legal-depth
independence moves the bounded co-moving source onto the same Euler line.  The transverse aperture
gap is then one factored von-Mangoldt integral whose kernel is the difference of the two analytic
mass tests.

Boundedness of this canonical semigroup high-pass is equivalent to RH.  No boundedness is asserted
here; the theorem exposes the exact arithmetic kernel where the open cancellation must occur.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- Additional mass taking the mass-one carrier to the co-moving carrier. -/
def xiComovingAdditionalMass (u : ℝ) : ℝ :=
  Real.sqrt (xiComovingMass u ^ (2 : ℕ) - 1)

theorem xiComovingAdditionalMass_half (u : ℝ) :
    1 / 2 ≤ xiComovingAdditionalMass u := by
  have hA := xiComovingMass_ge_two u
  have harg : 0 ≤ xiComovingMass u ^ (2 : ℕ) - 1 := by nlinarith
  have hsquare : xiComovingAdditionalMass u ^ (2 : ℕ) = xiComovingMass u ^ (2 : ℕ) - 1 := by
    rw [xiComovingAdditionalMass, Real.sq_sqrt harg]
  have hnonneg := Real.sqrt_nonneg (xiComovingMass u ^ (2 : ℕ) - 1)
  rw [← xiComovingAdditionalMass] at hnonneg
  nlinarith

theorem xiComovingMass_sq_eq_one_add_additional_sq (u : ℝ) :
    xiComovingMass u ^ (2 : ℕ) = 1 ^ (2 : ℕ) + xiComovingAdditionalMass u ^ (2 : ℕ) := by
  have hA := xiComovingMass_ge_two u
  have harg : 0 ≤ xiComovingMass u ^ (2 : ℕ) - 1 := by nlinarith
  rw [xiComovingAdditionalMass, Real.sq_sqrt harg]
  ring

/-- **Exact mass-semigroup factorization.**  The co-moving Xi carrier is the additional-mass
deformation of the fixed mass-one carrier. -/
theorem xiComovingMassFamily_eq_mass_one_then_additional_pt (u : ℝ) (q : XiZeroCopy) :
    (xiMassFamily (show 1 / 2 ≤ xiComovingMass u by
      linarith [xiComovingMass_ge_two u])).pt q =
      ((xiPoissonAbstract.mass (show 1 / 2 ≤ (1 : ℝ) by norm_num)).mass
        (xiComovingAdditionalMass_half u)).pt q := by
  rw [xiMassFamily_pt_eq_mass_pt]
  symm
  exact xiPoissonAbstract.mass_mass_pt_eq_mass_pt
    (show 1 / 2 ≤ (1 : ℝ) by norm_num)
    (xiComovingAdditionalMass_half u)
    (show 1 / 2 ≤ xiComovingMass u by linarith [xiComovingMass_ge_two u])
    (xiComovingMass_sq_eq_one_add_additional_sq u) q

/-- The co-moving prime bound transported to the common depth `3/4`. -/
theorem norm_xiMassBottomPrimeIntegral_comoving_threeQuarter_le
    {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    ‖xiMassBottomPrimeIntegral (xiComovingMass u) (3 / 4)
        ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiPoissonTraceReal (σ - 1 / 2) +
        xiMassBottomArchUniformBound 2 σ := by
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simp [Complex.mul_re]
    linarith
  rw [xiMassBottomPrimeIntegral_depth_independent
    (show 1 / 2 < (3 / 4 : ℝ) by norm_num)
    (show (3 / 4 : ℝ) < xiComovingMass u by
      linarith [xiComovingMass_ge_two u])
    (show 1 / 2 < (1 : ℝ) by norm_num)
    (show (1 : ℝ) < xiComovingMass u by
      linarith [xiComovingMass_ge_two u]) hτ]
  exact norm_xiMassBottomPrimeIntegral_comoving_le hσ u

/-- Literal factored high-pass integrand on the common Euler line `5/4 + i x`. -/
def xiMassPrimeSemigroupHighPassIntegrand (σ u x : ℝ) : ℂ :=
  (xiMassBottomTest 1 (3 / 4) ((σ : ℂ) + u * I) x -
      xiMassBottomTest (xiComovingMass u) (3 / 4) ((σ : ℂ) + u * I) x) *
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (xiMassBottomEulerPoint (3 / 4) x)

/-- Complete canonical semigroup aperture high-pass. -/
def xiMassPrimeSemigroupHighPass (σ u : ℝ) : ℂ :=
  ∫ x : ℝ, xiMassPrimeSemigroupHighPassIntegrand σ u x

/-- The factored single integral is exactly the previously classified aperture gap. -/
theorem xiMassPrimeSemigroupHighPass_eq_apertureGap
    {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    xiMassPrimeSemigroupHighPass σ u =
      xiMassBottomPrimeApertureGap 1 (3 / 4) σ u := by
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using hσ
  have hfixed := integrable_xiMassBottomPrimeIntegrand
    (show 1 / 2 < (3 / 4 : ℝ) by norm_num)
    (show (3 / 4 : ℝ) < 1 by norm_num) hτ
  have hmoving := integrable_xiMassBottomPrimeIntegrand
    (show 1 / 2 < (3 / 4 : ℝ) by norm_num)
    (show (3 / 4 : ℝ) < xiComovingMass u by
      linarith [xiComovingMass_ge_two u]) hτ
  rw [xiMassPrimeSemigroupHighPass, xiMassBottomPrimeApertureGap,
    ← xiMassBottomPrimeIntegral_depth_independent
      (show 1 / 2 < (3 / 4 : ℝ) by norm_num)
      (show (3 / 4 : ℝ) < xiComovingMass u by
        linarith [xiComovingMass_ge_two u])
      (show 1 / 2 < (1 : ℝ) by norm_num)
      (show (1 : ℝ) < xiComovingMass u by
        linarith [xiComovingMass_ge_two u]) hτ]
  change (∫ x : ℝ, xiMassPrimeSemigroupHighPassIntegrand σ u x) =
    (∫ x : ℝ, xiMassBottomPrimeIntegrand 1 (3 / 4) ((σ : ℂ) + u * I) x) -
      ∫ x : ℝ, xiMassBottomPrimeIntegrand (xiComovingMass u) (3 / 4)
        ((σ : ℂ) + u * I) x
  rw [← MeasureTheory.integral_sub hfixed hmoving]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  unfold xiMassPrimeSemigroupHighPassIntegrand xiMassBottomPrimeIntegrand
  ring

/-- Uniform line boundedness of the canonical semigroup high-pass. -/
def XiMassPrimeSemigroupHighPassLineBound (σ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, ‖xiMassPrimeSemigroupHighPass σ u‖ ≤ C

/-- **Canonical semigroup-high-pass RH criterion.**  RH-strength growth is exactly boundedness of
one factored prime-source mass difference on the common Euler line `5/4+i x`. -/
theorem riemannHypothesis_iff_xiMassPrimeSemigroupHighPassLineBound
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    RiemannHypothesis ↔ XiMassPrimeSemigroupHighPassLineBound σ := by
  have hgap := riemannHypothesis_iff_xiMassBottomPrimeApertureGapLineBound
    (a := (1 : ℝ)) (c := (3 / 4 : ℝ))
    (show 1 / 2 < (3 / 4 : ℝ) by norm_num)
    (show (3 / 4 : ℝ) < 1 by norm_num) hσ
  rw [hgap]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u => by
      rw [xiMassPrimeSemigroupHighPass_eq_apertureGap (by linarith) u]
      exact hC u⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun u => by
      rw [← xiMassPrimeSemigroupHighPass_eq_apertureGap (by linarith) u]
      exact hC u⟩

end

end RHTower
