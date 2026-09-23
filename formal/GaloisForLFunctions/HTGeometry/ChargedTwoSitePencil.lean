import GaloisForLFunctions.HTGeometry.QNMQuadraticPencil
import GaloisForLFunctions.HTGeometry.ChargedStringThermalOccupation

/-!
# An actual two-site charged wave pencil

Apply the charged cavity equation behind arXiv:2608.21406v1, equations (64)--(71),
to a finite positive graph Hamiltonian. The existing QNM pencil and companion
operator are reused. This is an exact finite model, not a continuum cavity solution.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Positive nearest-neighbor coupling plus a nonnegative mass term. -/
def chargedTwoSiteBase (k m : ℝ) : ℝ := Real.exp k + m ^ (2 : ℕ)

/-- The uncoupled diagonal energy is strictly positive for every parameter choice. -/
theorem chargedTwoSiteBase_pos (k m : ℝ) : 0 < chargedTwoSiteBase k m := by
  unfold chargedTwoSiteBase
  nlinarith [Real.exp_pos k, sq_nonneg m]

/-- Multiplication by two complex site values on the actual two-site state space. -/
def chargedTwoSiteDiagonal (a b : ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (a • LinearMap.fst ℂ ℂ ℂ).prod (b • LinearMap.snd ℂ ℂ ℂ)

/-- The finite graph Hamiltonian has a positive edge coupling and squared mass. -/
def chargedTwoSiteHamiltonian (k m : ℝ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  (((chargedTwoSiteBase k m : ℝ) : ℂ) • LinearMap.fst ℂ ℂ ℂ -
    (Real.exp k : ℂ) • LinearMap.snd ℂ ℂ ℂ).prod
  (((chargedTwoSiteBase k m : ℝ) : ℂ) • LinearMap.snd ℂ ℂ ℂ -
    (Real.exp k : ℂ) • LinearMap.fst ℂ ℂ ℂ)

/-- Constant coefficient of the charged frequency pencil. -/
def chargedTwoSiteStiffness (k m c d : ℝ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  chargedTwoSiteHamiltonian k m - chargedTwoSiteDiagonal (((c + d : ℝ) : ℂ) ^ (2 : ℕ)) (((c - d : ℝ) : ℂ) ^ (2 : ℕ))

/-- Linear frequency coefficient induced by the two electrostatic site values. -/
def chargedTwoSiteDrift (c d : ℝ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  chargedTwoSiteDiagonal (2 * ((c + d : ℝ) : ℂ)) (2 * ((c - d : ℝ) : ℂ))

/-- An instance of the corpus quadratic wave pencil with identity mass operator. -/
def chargedTwoSitePencil (k m c d : ℝ) (ω : ℂ) : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) :=
  qnmQuadraticPencil (chargedTwoSiteStiffness k m c d) (chargedTwoSiteDrift c d) LinearMap.id ω

/-- The reused pencil is exactly the charged two-site wave residual. -/
theorem chargedTwoSitePencil_apply (k m c d : ℝ) (ω : ℂ) (v : ℂ × ℂ) :
    chargedTwoSitePencil k m c d ω v =
      ((((chargedTwoSiteBase k m : ℝ) : ℂ) - (ω - ((c + d : ℝ) : ℂ)) ^ (2 : ℕ)) * v.1 - (Real.exp k : ℂ) * v.2,
        (((chargedTwoSiteBase k m : ℝ) : ℂ) - (ω - ((c - d : ℝ) : ℂ)) ^ (2 : ℕ)) * v.2 - (Real.exp k : ℂ) * v.1) := by
  ext <;> simp [chargedTwoSitePencil, qnmQuadraticPencil, chargedTwoSiteStiffness,
    chargedTwoSiteDrift, chargedTwoSiteDiagonal, chargedTwoSiteHamiltonian] <;> ring

/-- A common real shift of electrostatic potential and frequency leaves the actual operator unchanged. -/
theorem chargedTwoSitePencil_gauge (k m c d C : ℝ) (ω : ℂ) :
    chargedTwoSitePencil k m (c + C) d (ω + (C : ℂ)) = chargedTwoSitePencil k m c d ω := by
  apply LinearMap.ext
  intro v
  rw [chargedTwoSitePencil_apply, chargedTwoSitePencil_apply]
  apply Prod.ext <;> dsimp <;> push_cast <;> ring

/-- The finite wave equation is equivalent to its actual four-component companion eigenproblem. -/
theorem chargedTwoSiteCompanion_eigen_iff (k m c d : ℝ) (ω : ℂ) (p : (ℂ × ℂ) × (ℂ × ℂ)) :
    qnmCompanionLeft (chargedTwoSiteStiffness k m c d) (chargedTwoSiteDrift c d) p = ω • p ↔
      p.2 = ω • p.1 ∧ chargedTwoSitePencil k m c d ω p.1 = 0 := by
  simpa [qnmCompanionMass, chargedTwoSitePencil] using
    qnmCompanion_eigen_iff (chargedTwoSiteStiffness k m c d) (chargedTwoSiteDrift c d)
      (LinearMap.id : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ)) ω p

/-- The exact Hamiltonian quadratic form is a sum of nonnegative edge and mass energies. -/
theorem chargedTwoSiteHamiltonian_energy (k m : ℝ) (v : ℂ × ℂ) :
    (((starRingEnd ℂ) v.1 * (chargedTwoSiteHamiltonian k m v).1 +
      (starRingEnd ℂ) v.2 * (chargedTwoSiteHamiltonian k m v).2).re) =
        Real.exp k * Complex.normSq (v.1 - v.2) +
          m ^ (2 : ℕ) * (Complex.normSq v.1 + Complex.normSq v.2) := by
  change (((starRingEnd ℂ) v.1 *
    (((chargedTwoSiteBase k m : ℝ) : ℂ) * v.1 - (Real.exp k : ℂ) * v.2) +
    (starRingEnd ℂ) v.2 *
    (((chargedTwoSiteBase k m : ℝ) : ℂ) * v.2 - (Real.exp k : ℂ) * v.1)).re) = _
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, Complex.sub_im, zero_mul, sub_zero, add_zero]
  unfold chargedTwoSiteBase
  ring

/-- Positivity of the actual Hamiltonian requires no operator or boundary premise. -/
theorem chargedTwoSiteHamiltonian_energy_nonneg (k m : ℝ) (v : ℂ × ℂ) :
    0 ≤ (((starRingEnd ℂ) v.1 * (chargedTwoSiteHamiltonian k m v).1 +
      (starRingEnd ℂ) v.2 * (chargedTwoSiteHamiltonian k m v).2).re) := by
  rw [chargedTwoSiteHamiltonian_energy]
  exact add_nonneg (mul_nonneg (Real.exp_pos k).le (Complex.normSq_nonneg _))
    (mul_nonneg (sq_nonneg m) (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)))

end
end GaloisForLFunctions.HTGeometry
