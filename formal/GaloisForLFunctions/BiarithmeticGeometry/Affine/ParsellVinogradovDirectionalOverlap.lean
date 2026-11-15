import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovDirectionalFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineAxisExponent

/-!
# Sharp distinguished-component decay for arbitrary affine directions

Two triangular filtrations reduce the selected determinant to the same
balanced binary minors: first total degree, then remaining binary degree.
Thus all transverse shear coefficients and vertical translations are free
parameters in the sharp overlap bound for the distinguished coefficient.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The complete selected determinant is independent of every transverse coefficient and shift. -/
theorem exists_directionalAffine_determinant_certificate (r k : ℕ) :
    ∃ s : AffineAxisIndex r k → AffineAxisIndex r k ⊕ AffineAxisIndex r k,
      ∃ c : ℝ, c ≠ 0 ∧ ∀ (θ : ℝ) (η : Fin r → ℝ) (t : ℝ),
        (selectedMatrix (directionalAffineMatrix r k θ η t) s).det = c * θ ^ axisExponent r k := by
  classical
  have hs (d : Fin k) (a : HomogeneousChain r (d.val + 1)) :=
    exists_shear_determinant_certificate (chainDegree a + 1)
  choose s c hc hd using hs
  refine ⟨blockSelector (fun d => blockSelector (s d)), ∏ d, ∏ a, c d a, ?_, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro d _
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => hc d a)
  · intro θ η t
    rw [det_selectedMatrix_of_lower _ (directionalAffine_lower r k θ η t)]
    simp only [directionalAffine_diagonalBlock]
    have hblock (d : Fin k) :
        (selectedMatrix (homogeneousDirectionalMatrix r (d.val + 1) θ η) (blockSelector (s d))).det =
          ∏ a, c d a * θ ^ ((chainDegree a + 1) ^ 2 / 4) := by
      rw [det_selectedMatrix_of_rankLower _ (homogeneousDirectional_rankLower r (d.val + 1) θ η)]
      simp only [homogeneousDirectional_diagonalBlock, hd]
    simp only [hblock, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    change (∑ d : Fin k, homogeneousAxisExponent r (d.val + 1)) = axisExponent r k
    exact Fin.sum_univ_eq_sum_range (fun d : ℕ => homogeneousAxisExponent r (d + 1)) k

/-- Independently centered cube overlap under an arbitrary affine moment shear. -/
def directionalAffineOverlap (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ) (t : ℝ)
    (a b : AffineAxisSpace r k) : Set (AffineAxisSpace r k) :=
  matrixUnitOverlap (directionalAffineMatrix r k θ η t) a b

theorem exists_regularized_directionalAffine_volume_upper (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + |θ|) ^ axisExponent r k * (volume (directionalAffineOverlap r k θ η t a b)).toReal ≤ C := by
  obtain ⟨s, c, hc, hd⟩ := exists_directionalAffine_determinant_certificate r k
  obtain ⟨C, hC, h⟩ := exists_regularized_matrixUnitOverlap_bound
    (fun θ (u : (Fin r → ℝ) × ℝ) => directionalAffineMatrix r k θ u.1 u.2)
    (axisExponent r k) s c hc (fun θ u => hd θ u.1 u.2)
  exact ⟨C, hC, fun θ η t a b => h θ (η, t) a b⟩

/-- Sharp power decay is uniform over all other shear components, shifts, and cube centers. -/
theorem exists_uniform_directionalAffine_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      volume (directionalAffineOverlap r k θ η t a b) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ axisExponent r k) := by
  obtain ⟨s, c, hc, hd⟩ := exists_directionalAffine_determinant_certificate r k
  obtain ⟨C, hC, h⟩ := exists_matrixUnitOverlap_decay
    (fun θ (u : (Fin r → ℝ) × ℝ) => directionalAffineMatrix r k θ u.1 u.2)
    (axisExponent r k) s c hc (fun θ u => hd θ u.1 u.2)
  exact ⟨C, hC, fun θ η t a b => h θ (η, t) a b⟩

theorem volume_cube_inter_directionalAffine_image (r k : ℕ) (θ : ℝ) (η : Fin r → ℝ)
    (t : ℝ) (a b : AffineAxisSpace r k) :
    volume (centeredCube a 1 ∩ (Matrix.toLin' (directionalAffineMatrix r k θ η t)) '' centeredCube b 1) =
      volume (directionalAffineOverlap r k θ η t b a) := by
  simpa only [directionalAffineOverlap, det_directionalAffineMatrix, abs_one,
    ENNReal.ofReal_one, one_mul] using volume_cube_inter_matrix_image (directionalAffineMatrix r k θ η t) a b

/-- The full binomial exponent holds for actual affine images, with unrestricted transverse parameters. -/
theorem exists_uniform_directionalAffine_image_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      volume (centeredCube a 1 ∩ (Matrix.toLin' (directionalAffineMatrix r k θ η t)) '' centeredCube b 1) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ axisExponent r k) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_directionalAffine_overlap_decay r k
  refine ⟨C, hC, fun θ η t a b => ?_⟩
  rw [volume_cube_inter_directionalAffine_image]
  exact h θ η t b a

/-- Allowing arbitrary transverse coefficients retains exactly the same optimal distinguished power. -/
theorem bounded_directionalAffine_overlap_uniform_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + |θ|) ^ p * (volume (directionalAffineOverlap r k θ η t a b)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  constructor
  · rintro ⟨C, h⟩
    apply (bounded_affineAxis_overlap_uniform_iff r k p).mp
    refine ⟨C, fun θ t a b => ?_⟩
    simpa only [directionalAffineOverlap, directionalAffine_zero_tail, affineAxisOverlap] using h θ 0 t a b
  · intro hp
    have hp' : p ≤ (axisExponent r k : ℝ) := by
      simpa only [axisExponent_eq_binomial_sum] using hp
    obtain ⟨C, _, h⟩ := exists_regularized_directionalAffine_volume_upper r k
    refine ⟨C, fun θ η t a b => ?_⟩
    have hb : 1 ≤ 1 + |θ| := by linarith only [abs_nonneg θ]
    have hpow : (1 + |θ|) ^ p ≤ (1 + |θ|) ^ axisExponent r k := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hb hp'
    exact (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg).trans (h θ η t a b)

/-- Intersections with actual affine cube images have the same exact distinguished-component threshold. -/
theorem bounded_directionalAffine_image_overlap_uniform_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ : ℝ) (η : Fin r → ℝ) (t : ℝ) (a b : AffineAxisSpace r k),
      (1 + |θ|) ^ p * (volume (centeredCube a 1 ∩
        (Matrix.toLin' (directionalAffineMatrix r k θ η t)) '' centeredCube b 1)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  rw [← bounded_directionalAffine_overlap_uniform_iff]
  simp only [volume_cube_inter_directionalAffine_image]
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, fun θ η t a b => h θ η t b a⟩
  · rintro ⟨C, h⟩
    exact ⟨C, fun θ η t a b => h θ η t b a⟩

#print axioms exists_directionalAffine_determinant_certificate
#print axioms exists_regularized_directionalAffine_volume_upper
#print axioms exists_uniform_directionalAffine_overlap_decay
#print axioms volume_cube_inter_directionalAffine_image
#print axioms exists_uniform_directionalAffine_image_overlap_decay
#print axioms bounded_directionalAffine_overlap_uniform_iff
#print axioms bounded_directionalAffine_image_overlap_uniform_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
