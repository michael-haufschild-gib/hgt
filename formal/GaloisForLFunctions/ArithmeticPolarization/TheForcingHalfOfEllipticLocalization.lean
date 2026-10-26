import GaloisForLFunctions.ArithmeticPolarization.ThePriceOfEllipticLocalization

/-!
# The forcing half of elliptic localization

The elliptic localizer `σ_γ` splits tests into an even sector, on which every pair at ordinate
`γ` is positive, and an odd sector, on which it is negative (`TwistedSectorsCollideQuartets`). Only
the odd sector can exclude a zero. This module identifies its first theorem.

* **The single-height detector is an odd-sector test** (`sigmaTest_twist_sinhTest`): the corpus
  detector `sinh(δu)(a² − u²)₊^{5/2}`, twisted to the ordinate `γ₀` of a candidate zero, is
  `σ_{γ₀}`-antisymmetric; its summand at the candidate is `−m |tr|²` (`Wsummand_twist_sinhTest`).
* **Odd-sector positivity forbids isolated off-line zeros**
  (`odd_sector_nonneg_forces_offLine_companion`): if Weil's form is nonnegative on that one
  odd-sector test, an off-line zero `½ + δ + iγ₀` has an off-line companion within ordinate distance
  `R`, once the depth signal `sinh(δ(a − 2w))⁴` beats the local zero-count background
  (`arithmetic-positivity-theory`'s `exists_offLine_companion_of_single_height_nonneg`). The
  localizing aperture grows like `(1/2δ) log log γ₀`: the hyperbolic growth of an off-line pair is
  what lets the forcing half localize below the zero spacing scale `log γ₀`.
* **The even sector cannot force** (`even_sector_summand_nonneg`): on `σ_γ`-symmetric tests every
  point at ordinate `γ` contributes `m |tr|² ≥ 0`.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-- The complex form of the corpus detector `sinh(δu)(a² − u²)₊^{5/2}`. -/
def sinhDetector (a δ : ℝ) : ℝ → ℂ := fun u => ((RHTower.sinhTest a δ u : ℝ) : ℂ)

theorem sinhDetector_odd (a δ u : ℝ) : sinhDetector a δ (-u) = -sinhDetector a δ u := by
  simp [sinhDetector, RHTower.sinhTest_odd]

/-- **The detector twisted to ordinate `γ` lies in the odd sector of `σ_γ`.** -/
theorem sigmaTest_twist_sinhTest (a δ γ : ℝ) :
    sigmaTest γ (twist γ (sinhDetector a δ)) = fun u => -twist γ (sinhDetector a δ) u :=
  sigmaTest_twist_odd (sinhDetector_odd a δ)

/-- At every point of ordinate `γ` the twisted detector contributes `−m |tr|²`. -/
theorem Wsummand_twist_sinhTest (Z : Zeta23.ZeroConfig) (a δ : ℝ) {ρ : ℂ} :
    Z.Wsummand (twist ρ.im (sinhDetector a δ)) (twist ρ.im (sinhDetector a δ)) ρ =
      -((Z.mult ρ : ℂ) * (Complex.normSq (tr (twist ρ.im (sinhDetector a δ)) ρ) : ℂ)) :=
  Wsummand_of_sigma_antisymmetric Z (sigmaTest_twist_sinhTest a δ ρ.im) rfl

/-- **The even sector cannot force.** On a `σ_γ`-symmetric test every point at ordinate `γ`
contributes a nonnegative summand. -/
theorem even_sector_summand_nonneg (Z : Zeta23.ZeroConfig) {γ : ℝ} {f : ℝ → ℂ}
    (hf : sigmaTest γ f = f) {ρ : ℂ} (hγ : ρ.im = γ) :
    0 ≤ (Z.Wsummand f f ρ).re := by
  rw [Wsummand_of_sigma_symmetric Z hf hγ, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- **Odd-sector positivity forbids isolated off-line zeros.** If Weil's form of a configuration
with local counts `≤ A₀ log(|t| + 3)` is nonnegative on the odd-sector test at the ordinate of an
off-line point `ρ₀ = ½ + δ + iγ₀`, and the depth signal beats the background, then `ρ₀` has an
off-line companion within ordinate distance `R`. -/
theorem odd_sector_nonneg_forces_offLine_companion (Z : Zeta23.ZeroConfig) {A₀ : ℝ}
    (hA₀ : 1 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ a R w : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hodd : 0 ≤ (Z.W (twist ρ₀.im (sinhDetector a δ)) (twist ρ₀.im (sinhDetector a δ))).re)
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + R)) <
      2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2) :
    ∃ ρ ∈ Z.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧ ρ.re ≠ 1 / 2 := by
  have hsh : twist ρ₀.im (sinhDetector a δ) =
      SquareRootThreshold.heightShift (-ρ₀.im / (2 * Real.pi))
        (fun u => ((RHTower.sinhTest a δ u : ℝ) : ℂ)) := twist_eq_heightShift _ _
  rw [hsh] at hodd
  exact ArithmeticPositivityTheory.exists_offLine_companion_of_single_height_nonneg Z hA₀ hloc hρ₀
    hδ hre hR hw hwa hodd hbig

end GaloisForLFunctions.ArithmeticPolarization
