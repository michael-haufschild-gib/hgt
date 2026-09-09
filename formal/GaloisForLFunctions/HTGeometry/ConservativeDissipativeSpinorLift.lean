import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinEnergy
import GaloisForLFunctions.HTGeometry.AbelianHiggsMechanism
import GaloisForLFunctions.HTGeometry.PureConjugationChannel

/-!
# Higgs-spinor lift of conservative–dissipative spin evolution

Applications of Schaffer–Exl's spin mechanism (arXiv:2609.04530) to the existing
Higgs-spinor Lorentz-null Gram map and quantum pure-projector construction.
The normalized stereographic lift lies on the Higgs vacuum manifold; its outer
square is positive, trace one, idempotent, and exactly the Lorentz matrix of
half the physical unit spin. This is a kinematic lift of the proved spin ODE,
not a claim to solve the Higgs field equations.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Positive normalization of the finite stereographic chart. -/
def spinChartScale (z : ℂ) : ℝ := (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹

/-- The chart normalization never vanishes. -/
theorem spinChartScale_pos (z : ℂ) : 0 < spinChartScale z := by
  unfold spinChartScale
  positivity

/-- Exact squared chart normalization, with no nonzero-coordinate premise. -/
theorem spinChartScale_sq (z : ℂ) : spinChartScale z ^ 2 = (1 + ‖z‖ ^ 2)⁻¹ := by
  rw [spinChartScale, inv_pow, Real.sq_sqrt (by positivity)]

/-- A canonical normalized complex doublet over every finite spin chart coordinate. -/
def spinChartSpinor (z : ℂ) : Fin 2 → ℂ := (spinChartScale z : ℂ) • ![z, 1]

/-- The chart lift lies exactly on the existing unit Higgs-spinor vacuum manifold. -/
theorem spinChartSpinor_normSq (z : ℂ) : abelianHiggsSpinorNormSq (spinChartSpinor z) = 1 := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := by positivity
  simp only [abelianHiggsSpinorNormSq, spinChartSpinor, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, Complex.normSq_eq_norm_sq,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [show spinChartScale z ^ 2 * ‖z‖ ^ 2 + spinChartScale z ^ 2 =
    spinChartScale z ^ 2 * (1 + ‖z‖ ^ 2) by ring, spinChartScale_sq, inv_mul_cancel₀ hd]

/-- The spin lift has zero Mexican-hat energy at every chart coordinate. -/
theorem spinChartSpinor_higgs_potential (z : ℂ) :
    abelianHiggsSpinorPotential (spinChartSpinor z) = 0 := by
  rw [abelianHiggsSpinorPotential, spinChartSpinor_normSq, sub_self, zero_pow two_ne_zero]

/-- Existing Lorentz-null time coordinate is fixed to one half. -/
theorem spinChartSpinor_time (z : ℂ) : higgsSpinorTime (spinChartSpinor z) = 1 / 2 := by
  change abelianHiggsSpinorNormSq (spinChartSpinor z) / 2 = 1 / 2
  rw [spinChartSpinor_normSq]

/-- The normalized Higgs-spinor outer square is the literal pure density matrix. -/
def spinChartDensity (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  higgsSpinorEventMatrix (spinChartSpinor z)

/-- The Higgs outer square agrees with the corpus's quantum pure-projector construction. -/
theorem spinChartDensity_eq_pureProjector (z : ℂ) :
    spinChartDensity z = pureProjectorMatrix (spinChartSpinor z) := by
  rfl

/-- The spin density is positive semidefinite by its existing Higgs Gram construction. -/
theorem spinChartDensity_posSemidef (z : ℂ) : (spinChartDensity z).PosSemidef :=
  higgsSpinorEventMatrix_posSemidef _

/-- The spin density is Hermitian. -/
theorem spinChartDensity_isHermitian (z : ℂ) : (spinChartDensity z).IsHermitian :=
  (spinChartDensity_posSemidef z).isHermitian

/-- The density matrix has the exact rational stereographic entries. -/
theorem spinChartDensity_entries (z : ℂ) :
    spinChartDensity z =
      (((1 + ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) • !![((‖z‖ ^ 2 : ℝ) : ℂ), z; conj z, 1] := by
  have hfactor : spinChartDensity z =
      ((spinChartScale z ^ 2 : ℝ) : ℂ) • higgsSpinorEventMatrix ![z, 1] := by
    ext i j
    simp only [spinChartDensity, higgsSpinorEventMatrix, spinChartSpinor,
      Matrix.vecMulVec_apply, Pi.star_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      RCLike.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_pow]
    ring
  rw [hfactor, spinChartScale_sq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higgsSpinorEventMatrix, Matrix.vecMulVec_apply, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]

/-- The spin density has unit trace. -/
theorem spinChartDensity_trace (z : ℂ) : Matrix.trace (spinChartDensity z) = 1 := by
  have hd : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show (1 + ‖z‖ ^ 2 : ℝ) ≠ 0 by positivity)
  rw [spinChartDensity_entries]
  simp [Matrix.trace, Fin.sum_univ_two]
  field_simp
  ring

/-- Every spin density is a rank-one idempotent, hence stays pure. -/
theorem spinChartDensity_sq (z : ℂ) : spinChartDensity z * spinChartDensity z = spinChartDensity z := by
  have hsum : (star (spinChartSpinor z)) ⬝ᵥ spinChartSpinor z = (1 : ℂ) := by
    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, RCLike.star_def,
      ← Complex.normSq_eq_conj_mul_self]
    have h := spinChartSpinor_normSq z
    unfold abelianHiggsSpinorNormSq at h
    exact_mod_cast h
  change Matrix.vecMulVec _ _ * Matrix.vecMulVec _ _ = _
  rw [Matrix.vecMulVec_mul_vecMulVec, hsum, one_smul]
  rfl

/-- The density remains on the corpus's Lorentz null cone. -/
theorem spinChartDensity_det (z : ℂ) : (spinChartDensity z).det = 0 :=
  higgsSpinorEventMatrix_det _

/-- The normalized spinor density is the existing Lorentz matrix of half the unit spin. -/
theorem spinChartDensity_lorentz (z : ℂ) :
    spinChartDensity z = (1 / 2 : ℂ) •
      lorentzHermitianMatrix 1 (_root_.Bottcher.stereo z 0)
        (_root_.Bottcher.stereo z 1) (_root_.Bottcher.stereo z 2) := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := by positivity
  rw [spinChartDensity_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [Matrix.smul_apply, lorentzHermitianMatrix, _root_.Bottcher.stereo,
      Complex.mul_re, Complex.mul_im, -Complex.ofReal_inv, -Complex.ofReal_pow,
      -Complex.ofReal_add, -Complex.ofReal_mul, -Complex.ofReal_div, -Complex.ofReal_sub]
  all_goals field_simp <;> ring

/-- The spin's actual global trajectory has a canonical lift through the existing Higgs spinor. -/
def spinSpinorFlow (a : ℝ) (z : ℂ) (t : ℝ) : Fin 2 → ℂ :=
  spinChartSpinor (spinPlaneFlow a z t)

/-- The entire conservative–dissipative spin trajectory stays on the Higgs vacuum manifold. -/
theorem spinSpinorFlow_higgs_vacuum (a : ℝ) (z : ℂ) (t : ℝ) :
    abelianHiggsSpinorNormSq (spinSpinorFlow a z t) = 1 ∧
      abelianHiggsSpinorPotential (spinSpinorFlow a z t) = 0 :=
  ⟨spinChartSpinor_normSq _, spinChartSpinor_higgs_potential _⟩

/-- Exact Lorentz/Hopf record of the evolving spinor, using the actual spin ODE trajectory. -/
theorem spinSpinorFlow_event (a : ℝ) (z : ℂ) (t : ℝ) :
    higgsSpinorEventMatrix (spinSpinorFlow a z t) = (1 / 2 : ℂ) •
      lorentzHermitianMatrix 1 (spinSphereFlow a z t 0)
        (spinSphereFlow a z t 1) (spinSphereFlow a z t 2) :=
  spinChartDensity_lorentz _

end
end GaloisForLFunctions.HTGeometry.SchafferExl
