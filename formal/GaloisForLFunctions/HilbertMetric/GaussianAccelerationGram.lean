import GaloisForLFunctions.HilbertMetric.GaussianMetricRankOneFracture
import GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel
import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAcceleration

/-!
# Inverse-square-root Gram matrices from Gaussian acceleration

Accelerating the bandwidth of a finite Euclidean Gaussian Gram gives the inverse multiquadric
kernel. Positive integration preserves positivity, and every positive bandwidth separates
distinct feature vectors. Thus acceleration preserves the exact collision criterion for strict
positivity and the rank equal to the number of distinct features.
-/

open MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

open HTGeometry

noncomputable section

/-- The inverse multiquadric Gram matrix at a positive acceleration time. -/
def gaussianAccelerationGram {ι : Type*} {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  fun i j => (Real.sqrt (1 + 4 * Real.exp s * ∑ k, (y i k - y j k) ^ 2))⁻¹

/-- Entrywise acceleration evaluates exactly, without exchanging an infinite sum and integral. -/
theorem gaussianAccelerationGram_entry {ι : Type*} {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) (i j : ι) :
    gaussianAccelerationGram y s i j =
      gaussianAcceleration (fun x => finiteGaussianDistanceGram y (x ^ 2) i j)
        (Real.exp s) := by
  have he : (fun x => finiteGaussianDistanceGram y (x ^ 2) i j) =
      (fun x => Real.exp (-(∑ k, (y i k - y j k) ^ 2) * x ^ 2)) := by
    funext x
    unfold finiteGaussianDistanceGram
    congr 1
    ring
  rw [he, gaussianAcceleration_quadratic]
  simp only [gaussianAccelerationGram, mul_neg, sub_neg_eq_add]

theorem integrable_gaussianAccelerationGram_entry {ι : Type*} {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) (i j : ι) :
    IntegrableOn (fun x => gaussianAccelerationKernel (Real.exp s) x *
      finiteGaussianDistanceGram y (x ^ 2) i j) (Ioi 0) := by
  have he : (fun x => finiteGaussianDistanceGram y (x ^ 2) i j) =
      (fun x => Real.exp (-(∑ k, (y i k - y j k) ^ 2) * x ^ 2)) := by
    funext x
    unfold finiteGaussianDistanceGram
    congr 1
    ring
  have h := (integrable_gaussianAcceleration_quadratic_iff s
    (-(∑ k, (y i k - y j k) ^ 2))).mpr
    (lt_of_le_of_lt (neg_nonpos.mpr (Finset.sum_nonneg fun k _ => sq_nonneg _))
      (by positivity))
  convert h using 1
  funext x
  rw [congrFun he x]

private def accelerationMatrixDensity {ι : Type*} {d : ℕ}
    (y : ι → Fin d → ℝ) (s x : ℝ) : Matrix ι ι ℝ :=
  if 0 < x then gaussianAccelerationKernel (Real.exp s) x •
    finiteGaussianDistanceGram y (x ^ 2) else 0

private theorem accelerationMatrixDensity_integrable {ι : Type*} {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) (i j : ι) :
    Integrable (fun x => accelerationMatrixDensity y s x i j)
      (volume.restrict (Ioi 0)) := by
  apply (integrable_gaussianAccelerationGram_entry y s i j).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  simp only [accelerationMatrixDensity, if_pos hx0, Matrix.smul_apply, smul_eq_mul]

private theorem accelerationMatrixDensity_integral {ι : Type*} {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) :
    _root_.HTGeometry.integralMatrixKernel (volume.restrict (Ioi 0))
      (accelerationMatrixDensity y s) = gaussianAccelerationGram y s := by
  ext i j
  rw [gaussianAccelerationGram_entry]
  unfold _root_.HTGeometry.integralMatrixKernel gaussianAcceleration
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  simp only [accelerationMatrixDensity, if_pos hx0, Matrix.smul_apply, smul_eq_mul]

private theorem accelerationMatrixDensity_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (y : ι → Fin d → ℝ) (s x : ℝ) :
    (accelerationMatrixDensity y s x).PosSemidef := by
  classical
  unfold accelerationMatrixDensity
  split_ifs with hx
  · letI : Fintype (Set.range y) := Fintype.ofFinite _
    let z : Set.range y → Fin d → ℝ := Subtype.val
    have hz := (finiteGaussianDistanceGram_posDef_iff_injective_of_pos_fintype
      z (sq_pos_of_pos hx)).mpr Subtype.val_injective
    let label : ι → Set.range y := fun i => ⟨y i, mem_range_self i⟩
    have hp : (finiteGaussianDistanceGram y (x ^ 2)).PosSemidef :=
      hz.posSemidef.submatrix label
    exact hp.smul (gaussianAccelerationKernel_nonneg _ _)
  · exact Matrix.PosSemidef.zero

/-- Gaussian acceleration preserves positive semidefiniteness for every finite feature family. -/
theorem gaussianAccelerationGram_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) :
    (gaussianAccelerationGram y s).PosSemidef := by
  rw [← accelerationMatrixDensity_integral]
  exact _root_.HTGeometry.integralMatrixKernel_posSemidef _ _
    (accelerationMatrixDensity_integrable y s) (accelerationMatrixDensity_posSemidef y s)

/-- The accelerated Gram is strictly positive exactly when feature vectors are distinct. -/
theorem gaussianAccelerationGram_posDef_iff_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) :
    (gaussianAccelerationGram y s).PosDef ↔ Function.Injective y := by
  constructor
  · intro hgram i j hij
    by_contra hne
    have hrows : gaussianAccelerationGram y s i = gaussianAccelerationGram y s j := by
      funext k
      simp only [gaussianAccelerationGram, hij]
    exact hgram.det_pos.ne' (Matrix.det_zero_of_row_eq hne hrows)
  · intro hy
    rw [← accelerationMatrixDensity_integral]
    apply _root_.HTGeometry.integralMatrixKernel_posDef_of_support _ _
      (accelerationMatrixDensity_integrable y s) (accelerationMatrixDensity_posSemidef y s)
    intro v hv
    have hsupport : Ioi (0 : ℝ) ⊆ Function.support
        (_root_.HTGeometry.integralMatrixKernelQuadratic (accelerationMatrixDensity y s) v) := by
      intro x hx
      have hx0 : 0 < x := hx
      have hg := (finiteGaussianDistanceGram_posDef_iff_injective_of_pos_fintype
        y (sq_pos_of_pos hx0)).mpr hy
      have hp : (accelerationMatrixDensity y s x).PosDef := by
        rw [accelerationMatrixDensity, if_pos hx0]
        exact hg.smul (gaussianAccelerationKernel_exp_pos s x)
      exact (hp.dotProduct_mulVec_pos hv).ne'
    exact lt_of_lt_of_le (by simp : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi 0))
      (measure_mono hsupport)

/-- Acceleration preserves the exact rank: repeated feature vectors account for every defect. -/
theorem gaussianAccelerationGram_rank_eq_image_card
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (y : ι → Fin d → ℝ) (s : ℝ) :
    (gaussianAccelerationGram y s).rank = (Finset.univ.image y).card := by
  classical
  let S : Finset (Fin d → ℝ) := Finset.univ.image y
  let witness (a : S) : ∃ i ∈ (Finset.univ : Finset ι), y i = a :=
    Finset.mem_image.mp a.2
  let rep : S → ι := fun a => (witness a).choose
  have hrep (a : S) : y (rep a) = a := (witness a).choose_spec.2
  let label : ι → S := fun i => ⟨y i, by simp [S]⟩
  have hrep_label (i : ι) : y (rep (label i)) = y i := by
    simpa [label] using hrep (label i)
  have hrep_injective : Function.Injective rep := by
    intro a b hab
    apply Subtype.ext
    rw [← hrep a, ← hrep b, hab]
  let yr : S → Fin d → ℝ := fun a => y (rep a)
  have hyr : Function.Injective yr := by
    intro a b hab
    apply Subtype.ext
    rw [← hrep a, ← hrep b]
    exact hab
  let M : Matrix ι ι ℝ := gaussianAccelerationGram y s
  have hsub : M.submatrix rep rep = gaussianAccelerationGram yr s := by
    rfl
  have hpos : (gaussianAccelerationGram yr s).PosDef :=
    (gaussianAccelerationGram_posDef_iff_injective yr s).2 hyr
  have hsubrank : (M.submatrix rep rep).rank = Fintype.card S := by
    rw [hsub]
    exact Matrix.rank_of_isUnit _ hpos.isUnit
  have hlower : S.card ≤ M.rank := by
    calc
      S.card = Fintype.card S := by simp
      _ = (M.submatrix rep rep).rank := hsubrank.symm
      _ ≤ M.rank := Matrix.rank_submatrix_le M rep rep
  have hrow (i : ι) : M.row i = M.row (rep (label i)) := by
    funext j
    change gaussianAccelerationGram y s i j =
      gaussianAccelerationGram y s (rep (label i)) j
    simp only [gaussianAccelerationGram]
    rw [hrep_label]
  have hrange : Set.range M.row =
      Set.range (fun a : S => M.row (rep a)) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨label i, (hrow i).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨rep a, rfl⟩
  have hupper : M.rank ≤ S.card := by
    rw [M.rank_eq_finrank_span_row, hrange]
    simpa only [Set.finrank, Fintype.card_coe] using
      (finrank_range_le_card (R := ℝ) (fun a : S => M.row (rep a)))
  change M.rank = S.card
  exact le_antisymm hupper hlower

end

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.gaussianAccelerationGram_entry
#print axioms GaloisForLFunctions.HilbertMetric.integrable_gaussianAccelerationGram_entry
#print axioms GaloisForLFunctions.HilbertMetric.gaussianAccelerationGram_posSemidef
#print axioms GaloisForLFunctions.HilbertMetric.gaussianAccelerationGram_posDef_iff_injective
#print axioms GaloisForLFunctions.HilbertMetric.gaussianAccelerationGram_rank_eq_image_card
