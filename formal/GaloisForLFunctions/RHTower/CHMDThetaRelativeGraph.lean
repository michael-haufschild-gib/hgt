import GaloisForLFunctions.RHTower.CHMDFullJumpCoreDensity
import GaloisForLFunctions.RHTower.ThetaZeroDivisionLipschitz
import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary

/-!
# Theta-relative sources in the complete CHMD graph

Every globally Lipschitz source bounded by the full theta kernel has a bounded
inverse-Doob profile in the literal jump graph. A weighted cross-difference identity
cancels the small denominators before integration. It requires only the first
archimedean displacement moment and the mass of the complete prime measure.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph

theorem integrableOn_mul_archLevyDensity :
    IntegrableOn (fun t : ℝ => t * archLevyDensity t) (Ioi 0) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 * t))) (Ioi 0) :=
    by simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (show -(1 / 2 : ℝ) < 0 by norm_num) 0)
  refine (integrableOn_mul_exp_neg_half.add (he.div_const 2)).mono'
    ((measurable_id.mul measurable_archLevyDensity).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (mul_nonneg ht.le (archLevyDensity_pos ht).le)]
  change t * archLevyDensity t ≤ t * Real.exp (-(1 / 2 * t)) + Real.exp (-(1 / 2 * t)) / 2
  have h := sq_mul_archLevyDensity_le ht
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith

theorem continuous_phiDoobInv {f : ℝ → ℝ} (hf : Continuous f) : Continuous (phiDoobInv f) :=
  hf.div continuous_riemannKernelReal (fun x => (riemannKernelReal_pos x).ne')

theorem abs_phiDoobInv_le {f : ℝ → ℝ} {M : ℝ}
    (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) (x : ℝ) : |phiDoobInv f x| ≤ M := by
  rw [phiDoobInv, abs_div, abs_of_pos (riemannKernelReal_pos x),
    div_le_iff₀ (riemannKernelReal_pos x)]
  exact hb x

/-- Multiplying by both theta factors cancels the quotient singularity. -/
theorem weighted_relative_difference_le {f : ℝ → ℝ} {A B : NNReal}
    (hf : LipschitzWith A f) (hθ : LipschitzWith B riemannKernelReal)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) (x y : ℝ) :
    riemannKernelReal x * riemannKernelReal y * (phiDoobInv f x - phiDoobInv f y) ^ 2 ≤
      2 * M * ((A : ℝ) + M * B) * (riemannKernelReal y * |x - y|) := by
  let d := phiDoobInv f x - phiDoobInv f y
  have hx := riemannKernelReal_pos x
  have hy := riemannKernelReal_pos y
  have hd : |d| ≤ 2 * M := by
    exact (abs_sub _ _).trans (by linarith [abs_phiDoobInv_le hb x, abs_phiDoobInv_le hb y])
  have heq : riemannKernelReal x * riemannKernelReal y * d =
      riemannKernelReal y * f x - riemannKernelReal x * f y := by
    dsimp [d, phiDoobInv]
    field_simp [hx.ne', hy.ne']
  have hcross : |riemannKernelReal y * f x - riemannKernelReal x * f y| ≤
      riemannKernelReal y * ((A : ℝ) + M * B) * |x - y| := by
    calc
      _ = |riemannKernelReal y * (f x - f y) + f y * (riemannKernelReal y - riemannKernelReal x)| := by ring_nf
      _ ≤ |riemannKernelReal y * (f x - f y)| +
          |f y * (riemannKernelReal y - riemannKernelReal x)| := abs_add_le _ _
      _ = riemannKernelReal y * |f x - f y| + |f y| * |riemannKernelReal x - riemannKernelReal y| := by
        rw [abs_mul, abs_mul, abs_of_pos hy, abs_sub_comm (riemannKernelReal y)]
      _ ≤ riemannKernelReal y * ((A : ℝ) * |x - y|) +
          (M * riemannKernelReal y) * ((B : ℝ) * |x - y|) := by
        gcongr
        · simpa only [Real.norm_eq_abs] using hf.norm_sub_le x y
        · exact hb y
        · simpa only [Real.norm_eq_abs] using hθ.norm_sub_le x y
      _ = _ := by ring
  calc
    _ = |d| * |riemannKernelReal y * f x - riemannKernelReal x * f y| := by
      rw [← heq, abs_mul, abs_of_pos (mul_pos hx hy)]
      dsimp only [d]
      rw [← sq_abs (phiDoobInv f x - phiDoobInv f y)]
      ring
    _ ≤ (2 * M) * (riemannKernelReal y * ((A : ℝ) + M * B) * |x - y|) :=
      mul_le_mul hd hcross (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem relative_memLp_mass {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) :
    MemLp (phiDoobInv f) 2 massMeasure := by
  apply (memLp_const M).mono (continuous_phiDoobInv hf).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hM] using abs_phiDoobInv_le hb x

theorem relative_memLp_difference {f : ℝ → ℝ} {A : NNReal} (hf : LipschitzWith A f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) :
    MemLp (difference (phiDoobInv f)) 2 edgeMeasure := by
  obtain ⟨B, hB⟩ := exists_lipschitz_thetaCuspFullSource
  rw [show thetaCuspFullSource = riemannKernelReal from
    funext thetaCuspFullSource_eq_riemannKernelReal] at hB
  have hcont := continuous_difference (continuous_phiDoobInv hf.continuous)
  have ha : Integrable (fun e => difference (phiDoobInv f) e ^ 2) archMeasure := by
    rw [archMeasure, integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
    have hi := integrableOn_mul_archLevyDensity.mul_prod integrable_riemannKernelReal
    have hs := (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).integrable_comp_of_integrable hi
    have hs' : Integrable (fun e : ℝ × ℝ =>
        (e.1 * archLevyDensity e.1) * riemannKernelReal (e.2 + e.1)) archBase := by
      simpa only [Function.comp_def, add_comm, archBase] using hs
    refine (hs'.const_mul (2 * M * ((A : ℝ) + M * B))).mono'
      (measurable_archWeight.mul (hcont.measurable.pow_const 2)).aestronglyMeasurable ?_
    have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [ht, archWeight_nonneg_ae] with e he hw
    rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
    have h := mul_le_mul_of_nonneg_left
      (weighted_relative_difference_le hf hB hM hb e.2 (e.2 + e.1)) (archLevyDensity_pos he).le
    have habs : |e.2 - (e.2 + e.1)| = e.1 := by
      rw [show e.2 - (e.2 + e.1) = -e.1 by ring, abs_neg, abs_of_pos he]
    rw [habs] at h
    dsimp only [archWeight, difference, left, right]
    nlinarith
  have hp : MemLp (difference (phiDoobInv f)) 2 (Measure.sum primeMeasure) := by
    apply (memLp_const (2 * M)).mono hcont.aestronglyMeasurable
    exact Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * M)]
      exact (abs_sub _ _).trans (by
        linarith [abs_phiDoobInv_le hb (left e), abs_phiDoobInv_le hb (right e)])
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  exact ha.add_measure hp.integrable_sq

/-- Actual inverse-Doob realization in the full source graph. -/
def relativeLift (f : ℝ → ℝ) {A : NNReal} (hf : LipschitzWith A f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) : SourceGraph :=
  CHMDClosedJump.ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right
    (phiDoobInv f) (relative_memLp_mass hf.continuous hM hb) (relative_memLp_difference hf hM hb)

theorem relativeLift_source_ae (f : ℝ → ℝ) {A : NNReal} (hf : LipschitzWith A f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) :
    (relativeLift f hf hM hb).val.fst =ᵐ[massMeasure] phiDoobInv f :=
  (relative_memLp_mass hf.continuous hM hb).coeFn_toLp

/-- The realization retains the entire jump term and the negative cosh mass. -/
theorem relativeLift_energy (f : ℝ → ℝ) {A : NNReal} (hf : LipschitzWith A f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) :
    sourceEnergy (relativeLift f hf hM hb) =
      (∫ e, difference (phiDoobInv f) e ^ 2 ∂edgeMeasure) -
        ∫ x, phiDoobInv f x ^ 2 ∂massMeasure :=
  CHMDClosedJump.energy_ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right
    (phiDoobInv f) (relative_memLp_mass hf.continuous hM hb) (relative_memLp_difference hf hM hb)

theorem relativeLift_compact_approx (f : ℝ → ℝ) {A : NNReal} (hf : LipschitzWith A f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M * riemannKernelReal x) :
    relativeLift f hf hM hb ∈ closure (compactTests : Set SourceGraph) :=
  dense_compactTests _

end RHTower.CHMDDoobGraph
