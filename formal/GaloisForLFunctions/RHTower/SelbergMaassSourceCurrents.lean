import GaloisForLFunctions.RHTower.SelbergMaassTraceDirection
import GaloisForLFunctions.RHTower.SelbergMaassAugmentedDirection

/-!
# Original Maass pair currents and the regulator's spectral forcing

The actual congruence components share one planar eigen-potential. Their
antisymmetric value-derivative currents therefore have zero planar divergence,
including at common source zeros. The literal added regulator coordinate is
constant and instead gives the exact spectral forcing term.

The finite real Gram defect is half the sum of squared pair brackets, without
any nonvanishing or normalization premise. This supplies an algebraic mechanism
for the next source energy comparison. No phase-current reconstruction, quotient
period vanishing, or spectral quarter lower bound is asserted here.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassSourceCurrents
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassCuspTransport
noncomputable section

/-- A literal complex Maass component in the original planar chart. -/
def field (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (q : Deck N) : ℂ → ℂ := (quotientForm N f q).1.1 ∘ ofComplex

/-- Every actual congruence component retains the original C² regularity. -/
theorem field_smooth (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (q : Deck N) (z : ℍ) : ContDiffAt ℝ 2 (field N f q) (z : ℂ) :=
  (quotientForm N f q).2.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- Every actual component has the same original planar potential, with its full height factor. -/
theorem field_laplacian (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (q : Deck N) (z : ℍ) :
    dir 1 (dir 1 (field N f q)) (z : ℂ) + dir Complex.I (dir Complex.I (field N f q)) (z : ℂ) =
      ((-(lam / z.im ^ 2) : ℝ) : ℂ) * field N f q (z : ℂ) := by
  have hz : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have he := (quotientForm N f q).2.2.1.2 z
  change -(z.im : ℂ) ^ 2 * (dir 1 (dir 1 (field N f q)) (z : ℂ) +
    dir Complex.I (dir Complex.I (field N f q)) (z : ℂ)) = (lam : ℂ) * (quotientForm N f q).1.1 z at he
  have hv : field N f q (z : ℂ) = (quotientForm N f q).1.1 z := by
    simp only [field, Function.comp_apply, ofComplex_apply]
  rw [hv]
  apply mul_left_cancel₀ (pow_ne_zero 2 hz)
  push_cast
  field_simp
  linear_combination -he

/-- The original antisymmetric value-derivative current has no divisions by source amplitude. -/
def bracket (F G : ℂ → ℂ) (v z : ℂ) : ℂ := F z * dir v G z - G z * dir v F z

/-- Actual differentiation cancels both mixed first-derivative products in the bracket. -/
theorem bracket_dir {F G : ℂ → ℂ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z) (v : ℂ) :
    dir v (bracket F G v) z = F z * dir v (dir v G) z - G z * dir v (dir v F) z := by
  have hf := (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hg := (hG.differentiableAt (by norm_num)).hasFDerivAt
  have hdf := ((dir_contDiffAt hF v).differentiableAt (by norm_num)).hasFDerivAt
  have hdg := ((dir_contDiffAt hG v).differentiableAt (by norm_num)).hasFDerivAt
  have h := congrArg (fun L => L v) ((hf.mul hdg).sub (hg.mul hdf)).fderiv
  change dir v (bracket F G v) z =
    (F z * dir v (dir v G) z + dir v G z * dir v F z) -
      (G z * dir v (dir v F) z + dir v F z * dir v G z) at h
  rw [h]
  ring

/-- The full planar bracket divergence is exactly the antisymmetric Laplacian pairing. -/
theorem bracket_divergence {F G : ℂ → ℂ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z) :
    dir 1 (bracket F G 1) z + dir Complex.I (bracket F G Complex.I) z =
      F z * (dir 1 (dir 1 G) z + dir Complex.I (dir Complex.I G) z) -
        G z * (dir 1 (dir 1 F) z + dir Complex.I (dir Complex.I F) z) := by
  rw [bracket_dir hF hG, bracket_dir hF hG]
  ring

/-- The original shared Maass equation makes each actual complex pair current divergence-free, including at source zeros. -/
theorem source_current_conservation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (q r : Deck N) (z : ℍ) :
    dir 1 (bracket (field N f q) (field N f r) 1) (z : ℂ) +
      dir Complex.I (bracket (field N f q) (field N f r) Complex.I) (z : ℂ) = 0 := by
  rw [bracket_divergence (field_smooth N f q z) (field_smooth N f r z),
    field_laplacian, field_laplacian]
  ring

/-- The full finite real Gram defect is exactly half the sum of squared antisymmetric pair currents. -/
theorem finite_wedge_identity {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i, a i ^ 2) * (∑ i, b i ^ 2) - (∑ i, a i * b i) ^ 2 =
      (1 / 2 : ℝ) * ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 := by
  have hp (i j : ι) : (a i * b j - a j * b i) ^ 2 =
      a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * (a i * b i) * (a j * b j) := by ring
  have h1 : (∑ i, ∑ j, a i ^ 2 * b j ^ 2) = (∑ i, a i ^ 2) * (∑ j, b j ^ 2) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have h2 : (∑ i, ∑ j, a j ^ 2 * b i ^ 2) = (∑ i, a i ^ 2) * (∑ j, b j ^ 2) := by
    simp_rw [← Finset.sum_mul]
    rw [← Finset.mul_sum]
  have h3 : (∑ i, ∑ j, 2 * (a i * b i) * (a j * b j)) = 2 * (∑ i, a i * b i) ^ 2 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h1, h2, h3]
  ring

/-- The literal regulator coordinate has its original spectral forcing, rather than the common-eigenvalue conservation law. -/
theorem regulator_current_forcing (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (e : Ioi (0 : ℝ)) (q : Deck N) (z : ℍ) :
    dir 1 (bracket (SelbergMaassAugmentedDirection.source N f e none)
        (SelbergMaassAugmentedDirection.source N f e (some q)) 1) (z : ℂ) +
      dir Complex.I (bracket (SelbergMaassAugmentedDirection.source N f e none)
        (SelbergMaassAugmentedDirection.source N f e (some q)) Complex.I) (z : ℂ) =
      ((-(lam / z.im ^ 2) : ℝ) : ℂ) * (e : ℝ) * field N f q (z : ℂ) := by
  change dir 1 (bracket (fun _ : ℂ => ((e : ℝ) : ℂ)) (field N f q) 1) (z : ℂ) +
    dir Complex.I (bracket (fun _ : ℂ => ((e : ℝ) : ℂ)) (field N f q) Complex.I) (z : ℂ) = _
  rw [bracket_divergence contDiffAt_const (field_smooth N f q z), field_laplacian]
  have hc (v : ℂ) : dir v (dir v (fun _ : ℂ => ((e : ℝ) : ℂ))) (z : ℂ) = 0 := by
    change fderiv ℝ (fun w : ℂ => fderiv ℝ (fun _ : ℂ => ((e : ℝ) : ℂ)) w v) (z : ℂ) v = 0
    simp
  rw [hc, hc, add_zero, mul_zero, sub_zero]
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassSourceCurrents
