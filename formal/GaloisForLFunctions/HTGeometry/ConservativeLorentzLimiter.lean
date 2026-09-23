import GaloisForLFunctions.HTGeometry.ConservativeWeightedScaling
import GaloisForLFunctions.HTGeometry.LorentzConeAdmissibility

/-!
# An explicitly conservative, strictly admissible Lorentz limiter

The scaling mechanism of Fu--Liu, arXiv:2608.29229v1, Theorem 4.4, admits a
closed construction on every finite probability law. Arbitrary fluctuations
are centered, then a single positive scaling factor enforces a quantitative
Lorentz reserve at every node. The mean is constructed inside the strict cone,
rather than leaving mean admissibility as an unproved premise. Substituting
`conservativeGeometryLaw p g` gives the geometry-weighted version.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fluctuation with its probability mean removed. -/
def probabilityCentered (p : FiniteProbabilityLaw ι) (u : ι → E) (i : ι) : E :=
  u i - ∑ j, p.prob j • u j

/-- Centering removes exactly the mean in any real normed vector space. -/
theorem probabilityCentered_mean (p : FiniteProbabilityLaw ι) (u : ι → E) :
    (∑ i, p.prob i • probabilityCentered p u i) = 0 := by
  simp only [probabilityCentered, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, p.sum_prob, one_smul, sub_self]

/-- A finite bound on every centered energy-plus-momentum perturbation. -/
def lorentzLimiterBudget (p : FiniteProbabilityLaw ι) (a : ι → ℝ) (u : ι → E) : ℝ :=
  ∑ i, (|probabilityCentered p a i| + ‖probabilityCentered p u i‖)

theorem lorentzLimiterBudget_nonneg (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) : 0 ≤ lorentzLimiterBudget p a u :=
  Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg (probabilityCentered p a i))
    (norm_nonneg (probabilityCentered p u i))

theorem lorentzLimiterBudget_node (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) (i : ι) :
    |probabilityCentered p a i| + ‖probabilityCentered p u i‖ ≤ lorentzLimiterBudget p a u := by
  classical
  exact Finset.single_le_sum
    (fun j _ => add_nonneg (abs_nonneg (probabilityCentered p a j))
      (norm_nonneg (probabilityCentered p u j))) (Finset.mem_univ i)

/-- A common factor requiring no positivity premise on the supplied fluctuations. -/
def lorentzLimiterFactor (p : FiniteProbabilityLaw ι) (a : ι → ℝ)
    (u : ι → E) (r : ℝ) : ℝ :=
  Real.exp r / (Real.exp r + lorentzLimiterBudget p a u)

theorem lorentzLimiterFactor_pos (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) (r : ℝ) : 0 < lorentzLimiterFactor p a u r :=
  div_pos (Real.exp_pos r) (add_pos_of_pos_of_nonneg (Real.exp_pos r)
    (lorentzLimiterBudget_nonneg p a u))

theorem lorentzLimiterFactor_le_one (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) (r : ℝ) : lorentzLimiterFactor p a u r ≤ 1 := by
  apply (div_le_one (add_pos_of_pos_of_nonneg (Real.exp_pos r)
    (lorentzLimiterBudget_nonneg p a u))).mpr
  linarith [lorentzLimiterBudget_nonneg p a u]

/-- The actual limited energy and momentum at every node. -/
def conservativeLorentzLimit (p : FiniteProbabilityLaw ι) (a : ι → ℝ)
    (u : ι → E) (m : E) (r : ℝ) (i : ι) : ℝ × E :=
  (‖m‖ + Real.exp r + lorentzLimiterFactor p a u r * probabilityCentered p a i,
    m + lorentzLimiterFactor p a u r • probabilityCentered p u i)

/-- Energy conservation at the prescribed strictly admissible mean. -/
theorem conservativeLorentzLimit_energy_mean (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) (m : E) (r : ℝ) :
    (∑ i, p.prob i * (conservativeLorentzLimit p a u m r i).1) = ‖m‖ + Real.exp r := by
  have h := probabilityCentered_mean p a
  change (∑ i, p.prob i * probabilityCentered p a i) = 0 at h
  simp only [conservativeLorentzLimit, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, p.sum_prob, one_mul]
  have he : (∑ i, p.prob i * (lorentzLimiterFactor p a u r * probabilityCentered p a i)) = 0 := by
    calc
      _ = lorentzLimiterFactor p a u r * ∑ i, p.prob i * probabilityCentered p a i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [h, mul_zero]
  rw [he, add_zero]

/-- Momentum conservation uses the same factor as energy. -/
theorem conservativeLorentzLimit_momentum_mean (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) (m : E) (r : ℝ) :
    (∑ i, p.prob i • (conservativeLorentzLimit p a u m r i).2) = m := by
  simp only [conservativeLorentzLimit, smul_add, Finset.sum_add_distrib,
    ← Finset.sum_smul, p.sum_prob, one_smul]
  have he : (∑ i, p.prob i • (lorentzLimiterFactor p a u r • probabilityCentered p u i)) = 0 := by
    simp_rw [smul_comm (p.prob _) (lorentzLimiterFactor p a u r),
      ← Finset.smul_sum, probabilityCentered_mean, smul_zero]
  rw [he, add_zero]

/-- A quantitative reserve survives at every node, including zero-weight nodes. -/
theorem conservativeLorentzLimit_margin (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) (m : E) (r : ℝ) (i : ι) :
    Real.exp r ^ (2 : ℕ) / (Real.exp r + lorentzLimiterBudget p a u) ≤
      lorentzAdmissibilityMargin (conservativeLorentzLimit p a u m r i).1
        (conservativeLorentzLimit p a u m r i).2 := by
  let θ := lorentzLimiterFactor p a u r
  have hθ : 0 ≤ θ := (lorentzLimiterFactor_pos p a u r).le
  have hn : ‖m + θ • probabilityCentered p u i‖ ≤
      ‖m‖ + θ * ‖probabilityCentered p u i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ] using
      norm_add_le m (θ • probabilityCentered p u i)
  have he := neg_abs_le (probabilityCentered p a i)
  have hprod := mul_le_mul_of_nonneg_left he hθ
  have hb := mul_le_mul_of_nonneg_left (lorentzLimiterBudget_node p a u i) hθ
  have hden : Real.exp r + lorentzLimiterBudget p a u ≠ 0 :=
    (add_pos_of_pos_of_nonneg (Real.exp_pos r) (lorentzLimiterBudget_nonneg p a u)).ne'
  have hid : Real.exp r - θ * lorentzLimiterBudget p a u =
      Real.exp r ^ (2 : ℕ) / (Real.exp r + lorentzLimiterBudget p a u) := by
    dsimp [θ, lorentzLimiterFactor]
    field_simp [hden]
    ring
  change _ ≤ ‖m‖ + Real.exp r + θ * probabilityCentered p a i -
    ‖m + θ • probabilityCentered p u i‖
  rw [← hid]
  nlinarith [hn, hprod, hb]

/-- The construction is strictly admissible without any premise on its input arrays. -/
theorem conservativeLorentzLimit_mem_strict (p : FiniteProbabilityLaw ι)
    (a : ι → ℝ) (u : ι → E) (m : E) (r : ℝ) (i : ι) :
    conservativeLorentzLimit p a u m r i ∈ strictLorentzAdmissibility := by
  have hp : 0 < Real.exp r ^ (2 : ℕ) / (Real.exp r + lorentzLimiterBudget p a u) :=
    div_pos (sq_pos_of_pos (Real.exp_pos r))
      (add_pos_of_pos_of_nonneg (Real.exp_pos r) (lorentzLimiterBudget_nonneg p a u))
  have h := conservativeLorentzLimit_margin p a u m r i
  change ‖(conservativeLorentzLimit p a u m r i).2‖ <
    (conservativeLorentzLimit p a u m r i).1
  unfold lorentzAdmissibilityMargin at h
  linarith

end
end GaloisForLFunctions.HTGeometry
