import GaloisForLFunctions.RHTower.RoutePCompletedXiConormalBaseResidue

/-!
# Cubic raw-conormal modular doublet

The completed Xi logarithmic conormal has a source-defined raw residue.  Its right-half-line
radial column alone obscures functional-equation reflection: the reflected column grows on the
positive half-line.  Place that mate on the negative half-line and pull it back by reflection.
The result is exactly the conjugate right column.  Their bilinear modular pairing is therefore
the positive base Cauchy-cube self-charge `1 / (4 a^3)`.

This also separates two multiplicity questions.  Exact divisor trace uses linear multiplicity and
would require an inverse-square-root half-density.  Excluding the first strict-right zero does
not: the raw logarithmic residue carries multiplicity squared, hence costs at least the same
two-unit quantum.  No additive scalar residue transform can manufacture the square-root law for
all multiplicities.  Thus the minimal Cubic Ward/Hellinger producer may retain raw conormal
residues; what remains is a source-side bound for their modularly reflected trace.
-/

open Complex Set MeasureTheory

namespace RHTower

noncomputable section

/-- Negative-half-line conormal at the critical-line reflected point, pulled back to `r > 0`.
The outer minus compensates the orientation reversal. -/
def xiWardCubicReflectedConormalMateFeature (rho : ℂ) (r : ℝ) : ℂ :=
  -routePXiBaseConormalResidueFeature (1 - star rho) (-r)

/-- Functional-equation reflection converts the bilateral mate into the Hermitian conjugate
without any depth-dependent scalar normalization. -/
theorem xiWardCubicReflectedConormalMateFeature_eq_star
    (rho : ℂ) (r : ℝ) :
    xiWardCubicReflectedConormalMateFeature rho r =
      star (routePXiBaseConormalResidueFeature rho r) := by
  rw [xiWardCubicReflectedConormalMateFeature,
    routePXiBaseConormalResidueFeature,
    routePXiBaseConormalResidueFeature]
  have harg :
      -((1 - star rho - 1 / 2) * (((-r : ℝ) : ℂ))) =
        star (-((rho - 1 / 2) * (r : ℂ))) := by
    simp
    ring
  rw [harg]
  change -(((-r : ℝ) : ℂ) * Complex.exp
      ((starRingEnd ℂ) (-((rho - 1 / 2) * (r : ℂ))))) =
    (starRingEnd ℂ) ((r : ℂ) * Complex.exp (-((rho - 1 / 2) * (r : ℂ))))
  rw [Complex.exp_conj]
  simp

/-- Exact positive cubic self-charge from the bilateral FE-reflected conormal incidence. -/
theorem integral_routePXiBaseConormalResidueFeature_mul_reflectedMate
    {rho : ℂ} (hrho : 1 / 2 < rho.re) :
    (∫ r : ℝ in Ioi 0,
      routePXiBaseConormalResidueFeature rho r *
        xiWardCubicReflectedConormalMateFeature rho r) =
      (((1 : ℝ) / (4 * (rho.re - 1 / 2) ^ 3) : ℝ) : ℂ) := by
  rw [show (fun r : ℝ =>
      routePXiBaseConormalResidueFeature rho r *
        xiWardCubicReflectedConormalMateFeature rho r) =
      fun r : ℝ =>
        star (routePXiBaseConormalResidueFeature rho r) *
          routePXiBaseConormalResidueFeature rho r by
    funext r
    rw [xiWardCubicReflectedConormalMateFeature_eq_star]
    ring]
  rw [integral_star_routePXiBaseConormalResidueFeature_mul hrho hrho]
  rw [sub_self]
  rw [routePBaseCauchyCubicKernel_diagonal (R := 1)
    (a := (rho - 1 / 2).re) (by norm_num) (by simp; linarith)]
  simp

/-- Raw completed-logarithmic-residue charge at one actual strict-right zero support. -/
def xiWardCubicRawConormalCharge (q : XiRightZeroCopy) : ℝ :=
  ((xiSupportMultiplicity (q.1.1) : ℕ) : ℝ) ^ 2 *
    (1 / (4 * (xiRightCenteredZero q).re ^ 3))

/-- Raw multiplicity-squared residue already costs at least one full two-unit base quantum.
Therefore exact inverse-square-root multiplicity normalization is unnecessary for RH exclusion. -/
theorem xiWardCubicRawConormalCharge_ge_two (q : XiRightZeroCopy) :
    2 ≤ xiWardCubicRawConormalCharge q := by
  have hm : (1 : ℝ) ≤ ((xiSupportMultiplicity (q.1.1) : ℕ) : ℝ) := by
    exact_mod_cast xiSupportMultiplicity_pos q.1.1
  have hm2 : (1 : ℝ) ≤ ((xiSupportMultiplicity (q.1.1) : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hc := routePStrictRightZeroBaseCauchyCubicCharge_ge_two q
  rw [xiWardCubicRawConormalCharge]
  nlinarith [mul_le_mul_of_nonneg_right hm2 (by positivity :
    0 ≤ 1 / (4 * (xiRightCenteredZero q).re ^ 3))]

/-- Square-root multiplicity amplitudes cannot be residues of an additive scalar logarithmic
current.  Already multiplicities one and two contradict additivity. -/
theorem no_additive_scalar_multiplicity_halfDensity :
    ¬ ∃ A : ℕ → ℝ,
      (∀ m n, A (m + n) = A m + A n) ∧
      (∀ m, A m ^ 2 = m) := by
  rintro ⟨A, hadd, hsq⟩
  have h1 := hsq 1
  have h2 := hsq 2
  have ha := hadd 1 1
  norm_num at h1 h2 ha
  rcases h1 with h1 | h1 <;> nlinarith

end

end RHTower
