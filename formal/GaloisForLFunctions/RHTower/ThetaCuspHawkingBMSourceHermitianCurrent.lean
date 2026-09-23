import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularCutoffCalculus
import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential

/-!
# Hermitian currents of the literal theta source and physical QNM reader

The actual reader has a nonzero Hermitian spectral defect at every Xi occurrence,
including critical-line occurrences. Its angular current therefore cannot be replaced
by a divergence-free positive current.

The original theta source has the different spectral center `Re rho = 1/2`.
For its complete half-square `Q`, the exact positive defect density retains the
complex gradient contact `conj Q * E - Q * conj E`. These local identities do not
assert extinction of the corrected Einstein action or cancellation of its boundaries.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet

namespace RHTower.D4BMSourceHermitianCurrent
open D4BMJointSource D4BMGlobalAngularResponse D4BMAngularSeries
open D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The original positive-height angular chart. -/
abbrev Point := {z : Fin 2 → ℝ // 0 < z 1}

/-- The literal full angular reader at the physical QNM parameter. -/
def reader (q : XiZeroCopy) : (Fin 2 → ℝ) → ℂ :=
  scalar (physicalAngularParameter q)

/-- Hermitian Green current formed from actual coordinate derivatives. -/
def fieldCurrent (f : (Fin 2 → ℝ) → ℂ) (j : Fin 2) (z : Fin 2 → ℝ) : ℂ :=
  conj (f z) * coordDeriv j f z - f z * coordDeriv j (fun w => conj (f w)) z

/-- Divergence in the original hyperbolic volume density. -/
def fieldDivergence (f : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℝ) : ℂ :=
  (z 1 : ℂ)^(2 : ℕ) * (coordDeriv 0 (fieldCurrent f 0) z + coordDeriv 1 (fieldCurrent f 1) z)

/-- The physical reader current, retaining every Fourier mode. -/
abbrev current (q : XiZeroCopy) := fieldCurrent (reader q)

/-- The actual hyperbolic divergence of the physical reader current. -/
abbrev divergence (q : XiZeroCopy) := fieldDivergence (reader q)

private theorem reader_smooth (q : XiZeroCopy) (z : Point) :
    ContDiffAt ℝ 2 (reader q) z.val :=
  cuspLeg_contDiffAt .scalar (physicalAngularParameter q) 2 z.val z.property

private theorem current_partial (f : (Fin 2 → ℝ) → ℂ) (z : Point)
    (hf : ContDiffAt ℝ 2 f z.val) (j : Fin 2) :
    coordDeriv j (fieldCurrent f j) z.val =
      conj (f z.val) * coordDeriv j (coordDeriv j f) z.val -
        f z.val * coordDeriv j (coordDeriv j (fun w => conj (f w))) z.val := by
  have hg : ContDiffAt ℝ 2 (fun w => conj (f w)) z.val :=
    Complex.conjCLE.contDiff.contDiffAt.comp z.val hf
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfj := (ScalarTwoJet.coordDeriv_contDiffAt (m := 1) hf (by norm_num) j).differentiableAt (by norm_num)
  have hgj := (ScalarTwoJet.coordDeriv_contDiffAt (m := 1) hg (by norm_num) j).differentiableAt (by norm_num)
  unfold fieldCurrent
  erw [ScalarTwoJet.coordDeriv_sub (hgd.mul hfj) (hfd.mul hgj),
    ScalarTwoJet.coordDeriv_mul hgd hfj, ScalarTwoJet.coordDeriv_mul hfd hgj]
  ring

private theorem fieldDivergence_eq (f : (Fin 2 → ℝ) → ℂ) (z : Point)
    (hf : ContDiffAt ℝ 2 f z.val) :
    fieldDivergence f z.val = conj (f z.val) * hyperbolicLaplacian f z.val -
      f z.val * conj (hyperbolicLaplacian f z.val) := by
  unfold fieldDivergence
  rw [current_partial f z hf 0, current_partial f z hf 1,
    ← hyperbolicLaplacian_conj]
  unfold hyperbolicLaplacian
  ring

/-- The reader current has an exact nonzero spectral coefficient centered at real part one. -/
theorem divergence_eq_spectral_density (q : XiZeroCopy) (z : Point) :
    divergence q z.val =
      I * (((q.1 : ℂ).re - 1) * (q.1 : ℂ).im : ℝ) *
        (normSq (reader q z.val) : ℂ) := by
  have hL : hyperbolicLaplacian (reader q) z.val =
      (physicalAngularParameter q^(2 : ℕ)-1/4) * reader q z.val :=
    scalarCusp_hyperbolicLaplacian (physicalAngularParameter q) z.val z.property
  have hc : physicalAngularParameter q^(2 : ℕ)-1/4 - conj (physicalAngularParameter q^(2 : ℕ)-1/4) =
      I * (((q.1 : ℂ).re - 1) * (q.1 : ℂ).im : ℝ) := by
    apply Complex.ext <;>
      simp only [Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im] <;>
      norm_num [physicalAngularParameter_eq,Complex.mul_re,Complex.mul_im,pow_two]
    all_goals ring
  change fieldDivergence (reader q) z.val = _
  rw [fieldDivergence_eq (reader q) z (reader_smooth q z), hL, map_mul]
  calc
    _ = (physicalAngularParameter q^(2 : ℕ)-1/4-conj (physicalAngularParameter q^(2 : ℕ)-1/4)) *
        (reader q z.val * conj (reader q z.val)) := by ring
    _ = _ := by rw [hc, Complex.mul_conj]

/-- The reader current retains a positive density with the original spectral orientation. -/
theorem oriented_divergence_eq_positive_density (q : XiZeroCopy) (z : Point) :
    -(q.1 : ℂ).im * (divergence q z.val).im =
      (1-(q.1 : ℂ).re) * (q.1 : ℂ).im^(2 : ℕ) * normSq (reader q z.val) := by
  rw [divergence_eq_spectral_density]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add]
  ring

/-- The oriented reader divergence is nonnegative at every original angular point. -/
theorem oriented_divergence_nonnegative (q : XiZeroCopy) (z : Point) :
    0 ≤ -(q.1 : ℂ).im * (divergence q z.val).im := by
  rw [oriented_divergence_eq_positive_density]
  exact mul_nonneg (mul_nonneg (by linarith [(xi_divisor_support_re_mem_open_unit q.1).2])
    (sq_nonneg _)) (normSq_nonneg _)

/-- The actual reader divergence vanishes precisely at nodes of the reader. -/
theorem divergence_eq_zero_iff_reader_eq_zero (q : XiZeroCopy) (z : Point) :
    divergence q z.val = 0 ↔ reader q z.val = 0 := by
  have ht := xi_divisor_support_im_ne_zero q.1
  have hx : (q.1 : ℂ).re - 1 ≠ 0 := by
    linarith [(xi_divisor_support_re_mem_open_unit q.1).2]
  have hc : I * (((q.1 : ℂ).re - 1) * (q.1 : ℂ).im : ℝ) ≠ 0 :=
    mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr (mul_ne_zero hx ht))
  rw [divergence_eq_spectral_density, mul_eq_zero, or_iff_right hc,
    Complex.ofReal_eq_zero, Complex.normSq_eq_zero]

/-- The nonzero original Weyl mean forces a nonzero value of the full physical reader. -/
theorem exists_reader_ne_zero (q : XiZeroCopy) :
    ∃ z : Point, reader q z.val ≠ 0 := by
  have hC : reflectedCompletedLambda ((q.1 : ℂ)-1) ≠ 0 := by
    have he := (physicalScalar_cutoff_calibration q).1
    have hn := (physicalScalar_cutoff_calibration q).2.1
    rw [he] at hn
    exact (mul_ne_zero_iff.mp hn).2
  by_contra! hz
  have hmean := mean_scalar (physicalAngularParameter q) (show (0 : ℝ) < 1 by norm_num)
  have hzero : (fun x : ℝ => scalar (physicalAngularParameter q) ![x,1]) = fun _ => 0 := by
    funext x
    exact hz ⟨![x,1], by simp⟩
  rw [hzero, physicalScalar_principal] at hmean
  simp [D4BMCuspProjection.mean] at hmean
  exact hC hmean.symm

/-- Every Xi occurrence has a point of strictly positive oriented reader divergence. -/
theorem exists_oriented_divergence_pos (q : XiZeroCopy) :
    ∃ z : Point, 0 < -(q.1 : ℂ).im * (divergence q z.val).im := by
  obtain ⟨z,hz⟩ := exists_reader_ne_zero q
  refine ⟨z, ?_⟩
  rw [oriented_divergence_eq_positive_density]
  exact mul_pos (mul_pos (by linarith [(xi_divisor_support_re_mem_open_unit q.1).2])
    (sq_pos_of_ne_zero (xi_divisor_support_im_ne_zero q.1))) (normSq_pos.mpr hz)

/-- No physical Xi reader has an everywhere divergence-free Hermitian current. -/
theorem not_divergence_free (q : XiZeroCopy) :
    ¬ ∀ z : Point, divergence q z.val = 0 := by
  obtain ⟨z,hz⟩ := exists_reader_ne_zero q
  intro h
  exact hz ((divergence_eq_zero_iff_reader_eq_zero q z).mp (h z))

/-- The literal source current has the critical-line spectral coefficient. -/
theorem source_divergence (q : XiZeroCopy) (z : Point) :
    fieldDivergence (scalar (center q)) z.val =
      4 * I * (((q.1 : ℂ).re - 1/2) * (q.1 : ℂ).im : ℝ) *
        (normSq (scalar (center q) z.val) : ℂ) := by
  have hf : ContDiffAt ℝ 2 (scalar (center q)) z.val :=
    cuspLeg_contDiffAt .scalar (center q) 2 z.val z.property
  have hL : hyperbolicLaplacian (scalar (center q)) z.val =
      (center q^(2 : ℕ)-1/4)*scalar (center q) z.val :=
    scalarCusp_hyperbolicLaplacian (center q) z.val z.property
  rw [fieldDivergence_eq (scalar (center q)) z hf, hL, map_mul]
  have hc : center q^(2 : ℕ)-1/4-conj (center q^(2 : ℕ)-1/4) =
      4 * I * (((q.1 : ℂ).re - 1/2) * (q.1 : ℂ).im : ℝ) := by
    apply Complex.ext <;>
      simp only [Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im] <;>
      norm_num [D4BMGlobalAngularResponse.center,Complex.mul_re,Complex.mul_im,pow_two]
    all_goals ring
  calc
    _ = (center q^(2 : ℕ)-1/4-conj (center q^(2 : ℕ)-1/4)) *
        (scalar (center q) z.val * conj (scalar (center q) z.val)) := by ring
    _ = _ := by rw [hc, Complex.mul_conj]

/-- The complete complex gradient work of the original theta half-square. -/
def squareGradientContact (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  conj (fullSquarePotential q z) * fullGradientEnergy q z -
    fullSquarePotential q z * conj (fullGradientEnergy q z)

/-- The nonlinear half-square current retains its gradient work and exact clock-centered density. -/
theorem square_divergence_sub_gradient_contact (q : XiZeroCopy) (z : Point) :
    fieldDivergence (fullSquarePotential q) z.val - squareGradientContact q z.val =
      8 * I * (((q.1 : ℂ).re - 1/2) * (q.1 : ℂ).im : ℝ) *
        (normSq (fullSquarePotential q z.val) : ℂ) := by
  have hL := fullSquarePotential_laplacian q true z.val z.property
  rw [D4BMHorizon.scalarLaplacian_eq _ z.val z.property] at hL
  change hyperbolicLaplacian (fullSquarePotential q) z.val = _ at hL
  have hc : 2*(D4BMModularCore.physicalRate q true+1)*(D4BMModularCore.physicalRate q true+2) -
      conj (2*(D4BMModularCore.physicalRate q true+1)*(D4BMModularCore.physicalRate q true+2)) =
      8 * I * (((q.1 : ℂ).re - 1/2) * (q.1 : ℂ).im : ℝ) := by
    apply Complex.ext <;>
      simp only [Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im] <;>
      norm_num [D4BMModularCore.physicalRate,Complex.mul_re,Complex.mul_im]
    all_goals ring
  rw [fieldDivergence_eq _ z (fullSquarePotential_smooth q z.val z.property 2),
    hL, map_add, map_mul]
  unfold squareGradientContact
  calc
    _ = (2*(D4BMModularCore.physicalRate q true+1)*(D4BMModularCore.physicalRate q true+2) -
        conj (2*(D4BMModularCore.physicalRate q true+1)*(D4BMModularCore.physicalRate q true+2))) *
        (fullSquarePotential q z.val * conj (fullSquarePotential q z.val)) := by ring
    _ = _ := by rw [hc,Complex.mul_conj]

/-- The source-oriented flux-minus-gradient-work density is an exact nonnegative defect square. -/
theorem square_oriented_contact_balance (q : XiZeroCopy) (z : Point) :
    (((q.1 : ℂ).re-1/2)*(q.1 : ℂ).im) *
        (fieldDivergence (fullSquarePotential q) z.val - squareGradientContact q z.val).im =
      8*((q.1 : ℂ).re-1/2)^(2 : ℕ)*(q.1 : ℂ).im^(2 : ℕ)*normSq (fullSquarePotential q z.val) := by
  rw [square_divergence_sub_gradient_contact]
  norm_num [Complex.mul_im,Complex.mul_re]
  ring

end
end RHTower.D4BMSourceHermitianCurrent
