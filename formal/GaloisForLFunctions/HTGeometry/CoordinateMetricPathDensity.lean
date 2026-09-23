import GaloisForLFunctions.HTGeometry.CoordinateEinsteinCubicPath
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.MetricPathDensity
open Filter Topology
noncomputable section
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

/-- Cubic metric path with every correction retained. -/
def path (G H K L : Mat) (t : ℂ) : Mat :=
  G + t • H + t^(2 : ℕ) • K + t^(3 : ℕ) • L

/-- Determinant variation with every column replacement retained. -/
def determinantSlope (G H : Mat) : ℂ :=
  ∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℂ) *
    ∑ i : Fin d, (∏ j ∈ Finset.univ.erase i, G (σ j) j) * H (σ i) i

private theorem path_entry_smooth (G H K L : Mat) (i j : Fin d) :
    ContDiff ℂ 3 (fun t => path G H K L t i j) := by
  dsimp [path]
  fun_prop

private theorem path_entry_hasDerivAt (G H K L : Mat) (i j : Fin d) :
    HasDerivAt (fun t : ℂ => path G H K L t i j) (H i j) 0 := by
  have hd := ((((hasDerivAt_id (0 : ℂ)).mul_const (H i j)).const_add (G i j)).add
    ((hasDerivAt_pow 2 (0 : ℂ)).mul_const (K i j))).add
    ((hasDerivAt_pow 3 (0 : ℂ)).mul_const (L i j))
  convert! hd using 1
  simp

private theorem det_smooth {F : ℂ → Mat}
    (hF : ∀ i j, ContDiff ℂ 3 (fun t => F t i j)) :
    ContDiff ℂ 3 (fun t => (F t).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => hF (σ i) i)

private theorem inverse_smooth (G H K L : Mat) (hG : G.det ≠ 0) (i j : Fin d) :
    ContDiffAt ℂ 3 (fun t => (path G H K L t)⁻¹ i j) 0 := by
  have hd := det_smooth (path_entry_smooth G H K L)
  have ha : ContDiff ℂ 3 (fun t => (path G H K L t).adjugate i j) := by
    simp only [Matrix.adjugate_apply]
    apply det_smooth
    intro a b
    by_cases ha : a = j
    · simp only [Matrix.updateRow_apply, ha, if_true]
      exact contDiff_const
    · simpa [Matrix.updateRow_apply, ha] using path_entry_smooth G H K L a b
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hd.contDiffAt.inv (by simpa [path] using hG)).mul ha.contDiffAt

/-- The determinant slope is the actual derivative of the corrected metric path. -/
theorem determinant_hasDerivAt (G H K L : Mat) :
    HasDerivAt (fun t => (path G H K L t).det) (determinantSlope G H) 0 := by
  have he := path_entry_hasDerivAt G H K L
  have hp := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => he (σ i) i)).const_mul
      (Equiv.Perm.sign σ : ℂ))
  simpa [Matrix.det_apply', determinantSlope, path] using hp

/-- Local complex volume ratio, with the logarithm branch fixed at the original metric. -/
def volumeRatio (G H K L : Mat) (t : ℂ) : ℂ :=
  Complex.exp (Complex.log ((path G H K L t).det / G.det) / 2)

@[simp] theorem volumeRatio_zero (G H K L : Mat) (hG : G.det ≠ 0) :
    volumeRatio G H K L 0 = 1 := by simp [volumeRatio, path, hG]

/-- The chosen density is an actual square root of the determinant ratio wherever the path is nondegenerate. -/
theorem volumeRatio_sq (G H K L : Mat) (hG : G.det ≠ 0) (t : ℂ)
    (ht : (path G H K L t).det ≠ 0) :
    volumeRatio G H K L t ^ (2 : ℕ) = (path G H K L t).det / G.det := by
  unfold volumeRatio
  rw [pow_two, ← Complex.exp_add]
  convert! Complex.exp_log (div_ne_zero ht hG) using 1
  congr 1
  ring

/-- The volume ratio is regular at the original nondegenerate metric. -/
theorem volumeRatio_contDiffAt (G H K L : Mat) (hG : G.det ≠ 0) :
    ContDiffAt ℂ 3 (volumeRatio G H K L) 0 := by
  have hd : ContDiffAt ℂ 3 (fun t => (path G H K L t).det / G.det) 0 :=
    (det_smooth (path_entry_smooth G H K L)).contDiffAt.div_const G.det
  have hz : (path G H K L (0 : ℂ)).det / G.det = 1 := by simp [path, hG]
  have hl := (Complex.contDiffAt_log (hz ▸ Complex.one_mem_slitPlane)).comp 0 hd
  exact (hl.div_const 2).cexp

/-- Both the determinant variation and the fixed square-root normalization are retained. -/
theorem volumeRatio_hasDerivAt (G H K L : Mat) (hG : G.det ≠ 0) :
    HasDerivAt (volumeRatio G H K L) (determinantSlope G H / (2 * G.det)) 0 := by
  have hd := (determinant_hasDerivAt G H K L).div_const G.det
  have hz : (path G H K L (0 : ℂ)).det / G.det = 1 := by simp [path, hG]
  have hl := (Complex.hasDerivAt_log (hz ▸ Complex.one_mem_slitPlane)).comp 0 hd
  have hv := (hl.div_const 2).cexp
  convert! hv using 1
  simp only [Function.comp_apply, hz, Complex.log_one, zero_div, Complex.exp_zero, inv_one, one_mul]
  ring

/-- The covariant test tensor with both indices raised by the varying metric and its volume. -/
def testWeight (G H K L M : Mat) (t : ℂ) (i j : Fin d) : ℂ :=
  volumeRatio G H K L t * ((path G H K L t)⁻¹ * M * ((path G H K L t)⁻¹).transpose) i j

/-- Exact first variation of the volume-weighted raised test tensor. -/
def testWeightSlope (G H M : Mat) : Mat :=
  (determinantSlope G H / (2 * G.det)) • (G⁻¹ * M * (G⁻¹).transpose) -
    ((G⁻¹ * H * G⁻¹) * M * (G⁻¹).transpose + G⁻¹ * M * (G⁻¹ * H * G⁻¹).transpose)

@[simp] theorem testWeight_zero (G H K L M : Mat) (hG : G.det ≠ 0) (i j : Fin d) :
    testWeight G H K L M 0 i j = (G⁻¹ * M * (G⁻¹).transpose) i j := by
  simp [testWeight, volumeRatio_zero G H K L hG, path]

/-- All scalar weights in the original finite contraction have three actual derivatives. -/
theorem testWeight_contDiffAt (G H K L M : Mat) (hG : G.det ≠ 0) (i j : Fin d) :
    ContDiffAt ℂ 3 (fun t => testWeight G H K L M t i j) 0 := by
  unfold testWeight
  apply (volumeRatio_contDiffAt G H K L hG).mul
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.mul _ (inverse_smooth G H K L hG j a)
  apply ContDiffAt.sum
  intro b _
  exact (inverse_smooth G H K L hG i b).mul contDiffAt_const

/-- Actual differentiation gives both inverse-metric terms, including their order. -/
theorem testWeight_hasDerivAt (G H K L M : Mat) (hG : G.det ≠ 0) (i j : Fin d) :
    HasDerivAt (fun t => testWeight G H K L M t i j) (testWeightSlope G H M i j) 0 := by
  have he := path_entry_hasDerivAt G H K L
  have hi (a b : Fin d) := CoordinateMetricTwoJet.Linearization.matrix_inverse_hasDerivAt
    he (by simpa [path] using hG) a b
  have hc := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hi i b).mul_const (M b a))).mul (hi j a))
  have hv := (volumeRatio_hasDerivAt G H K L hG).mul hc
  convert! hv using 1
  simp only [testWeightSlope, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.transpose_apply, Matrix.mul_apply, Pi.mul_apply, path,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_pow (by decide : (3 : ℕ) ≠ 0),
    zero_smul, add_zero, volumeRatio_zero G H K L hG,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_mul, neg_mul, mul_neg, one_mul]
  ring

end
end GaloisForLFunctions.HTGeometry.MetricPathDensity
