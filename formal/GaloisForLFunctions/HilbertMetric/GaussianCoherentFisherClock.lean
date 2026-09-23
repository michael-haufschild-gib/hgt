import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-!
# Fisher clock of the Gaussian coherent-state Gram model

The Fubini--Study normalization of arXiv:2605.03958, equation (14),
applied to the existing Gaussian value/cross/jet blocks. Projecting out the
normalization direction leaves exactly the Euclidean quadratic form, despite
the exponentially growing unnormalized state mass.
-/
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HilbertMetric

/-- Squared coherent-state norm at one Euclidean label. -/
def coherentClockMass {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  gaussianCoherentGram (fun _ : Fin 1 => x) 0 0

/-- Directional state--tangent overlap from the corpus cross-jet block. -/
def coherentClockOverlap {d : ℕ} (x v : Fin d → ℝ) : ℝ :=
  ∑ i, v i * gaussianCoherentCrossJet (fun _ : Fin 1 => x) 0 (i, 0)

/-- Squared directional tangent norm from the corpus jet Gram block. -/
def coherentClockTangentSq {d : ℕ} (x v : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * v j * gaussianCoherentJetBlock (fun _ : Fin 1 => x) (i, 0) (j, 0)

def coherentClockInformation {d : ℕ} (x v : Fin d → ℝ) : ℝ :=
  _root_.HTGeometry.pureStateQuantumFisherValue (coherentClockMass x)
    (coherentClockOverlap x v) (coherentClockTangentSq x v)

theorem coherentClockMass_pos {d : ℕ} (x : Fin d → ℝ) : 0 < coherentClockMass x :=
  Real.exp_pos _

theorem coherentClockOverlap_formula {d : ℕ} (x v : Fin d → ℝ) :
    coherentClockOverlap x v = (∑ i, x i * v i) * coherentClockMass x := by
  unfold coherentClockOverlap gaussianCoherentCrossJet coherentClockMass gaussianCoherentGram
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem coherentClockTangentSq_formula {d : ℕ} (x v : Fin d → ℝ) :
    coherentClockTangentSq x v =
      ((∑ i, v i ^ (2 : ℕ)) + (∑ i, x i * v i) ^ (2 : ℕ)) * coherentClockMass x := by
  unfold coherentClockTangentSq gaussianCoherentJetBlock
  have hterm : ∀ i j : Fin d,
      v i * v j * (((if i = j then 1 else 0) + x j * x i) *
        Real.exp (coordinateDot (fun _ : Fin 1 => x) 0 0)) =
      ((if i = j then v i ^ (2 : ℕ) else 0) + (x i * v i) * (x j * v j)) *
        coherentClockMass x := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [ite_true, coherentClockMass, gaussianCoherentGram]
      ring
    · simp only [hij, ite_false, zero_add, coherentClockMass, gaussianCoherentGram]
      ring
  have hdiag (i : Fin d) : (∑ j : Fin d, if i = j then v i ^ (2 : ℕ) else 0) = v i ^ (2 : ℕ) := by
    simp
  have hcross : (∑ i, ∑ j, (x i * v i) * (x j * v j)) = (∑ i, x i * v i) ^ (2 : ℕ) := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hterm]
  calc
    _ = ((∑ i, ∑ j, if i = j then v i ^ (2 : ℕ) else 0) +
        (∑ i, ∑ j, (x i * v i) * (x j * v j))) * coherentClockMass x := by
      simp only [Finset.sum_mul, Finset.sum_add_distrib, add_mul]
    _ = _ := by simp_rw [hdiag, hcross]

/-- The projective correction cancels the exponentially large coherent-state mass exactly. -/
theorem coherentClockInformation_formula {d : ℕ} (x v : Fin d → ℝ) :
    coherentClockInformation x v = 4 * ∑ i, v i ^ (2 : ℕ) := by
  rw [coherentClockInformation, coherentClockOverlap_formula, coherentClockTangentSq_formula]
  unfold _root_.HTGeometry.pureStateQuantumFisherValue _root_.HTGeometry.projectiveQuantumTangentValue
  field_simp [(coherentClockMass_pos x).ne']
  ring

/-- Every affine coherent trajectory has constant Fisher speed, independent of position. -/
theorem coherentClock_speed {d : ℕ} (x v : Fin d → ℝ) :
    Real.sqrt (coherentClockInformation x v) = 2 * Real.sqrt (∑ i, v i ^ (2 : ℕ)) := by
  rw [coherentClockInformation_formula, Real.sqrt_mul (by norm_num)]
  norm_num

theorem coherentClock_integral {d : ℕ} (x v : Fin d → ℝ) (a b : ℝ) :
    (∫ t : ℝ in a..b, Real.sqrt (coherentClockInformation (fun i => x i + t * v i) v)) =
      2 * Real.sqrt (∑ i, v i ^ (2 : ℕ)) * (b - a) := by
  simp only [coherentClock_speed, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Zero distinguishability speed is exactly a stationary Euclidean label. -/
theorem coherentClockInformation_zero_iff {d : ℕ} (x v : Fin d → ℝ) :
    coherentClockInformation x v = 0 ↔ v = 0 := by
  rw [coherentClockInformation_formula, mul_eq_zero]
  rw [or_iff_right (by norm_num : (4 : ℝ) ≠ 0)]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, funext_iff, Pi.zero_apply]

/-- Normalized squared overlap obtained from the same coherent Gram kernel. -/
def coherentClockFidelity {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  gaussianCoherentGram ![x, y] 0 1 ^ (2 : ℕ) /
    (gaussianCoherentGram ![x, y] 0 0 * gaussianCoherentGram ![x, y] 1 1)

/-- Endpoint distinguishability depends only on Euclidean separation, not absolute label size. -/
theorem coherentClockFidelity_formula {d : ℕ} (x y : Fin d → ℝ) :
    coherentClockFidelity x y = Real.exp (-(∑ i, (x i - y i) ^ (2 : ℕ))) := by
  unfold coherentClockFidelity gaussianCoherentGram coordinateDot
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end GaloisForLFunctions.HilbertMetric
