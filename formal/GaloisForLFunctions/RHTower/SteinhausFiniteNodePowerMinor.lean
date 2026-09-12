import GaloisForLFunctions.Hurwitz.ExpIndependence
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.ExpandedEvaluationSetSampling
import GaloisForLFunctions.RHTower.SteinhausFiniteNodeCovariance

/-!
# Real terminal power minors for finite-node Steinhaus covariance

After writing a terminal integer as `n = N x`, the node-dependent part of the reflected AFE
coefficient is the generalized power `x ^ (s_j - 1)`.  In the logarithmic coordinate `z = log x`
this is `exp ((s_j - 1) z)`.  Distinct nodes therefore give a linearly independent family of
entire exponentials.

The arithmetic terminal samples have real `z` in `(log (1 / 2), 0)`, not arbitrary complex
coordinates.  This file proves that restriction to any nonempty real interval preserves the
independence and hence contains a square nonsingular evaluation packet.  This is the qualitative
rank certificate needed before thickening the packet and summing the resulting minors.
-/

open Filter Matrix Set Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Complex points on the embedded real interval `(a, b)`. -/
def realComplexInterval (a b : ℝ) : Set ℂ :=
  {z | z.im = 0 ∧ a < z.re ∧ z.re < b}

/-- The embedded real line approaches each of its points inside the punctured complex plane. -/
private theorem tendsto_ofReal_nhdsNE (a : ℝ) :
    Tendsto (fun t : ℝ => ((t : ℂ))) (𝓝[≠] a) (𝓝[≠] ((a : ℂ))) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact Tendsto.mono_left (Complex.continuous_ofReal.tendsto a) nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, mem_singleton_iff] at ht ⊢
    exact fun h => ht (Complex.ofReal_inj.mp h)

/-- Every nonempty embedded real interval accumulates at its midpoint in the complex plane. -/
theorem frequently_mem_realComplexInterval {a b : ℝ} (hab : a < b) :
    ∃ᶠ z in 𝓝[≠] ((((a + b) / 2 : ℝ) : ℂ)), z ∈ realComplexInterval a b := by
  have hmid : (a + b) / 2 ∈ Ioo a b := by
    constructor <;> linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] ((a + b) / 2),
      ((t : ℂ)) ∈ realComplexInterval a b := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hmid)] with t ht
    exact ⟨by simp, by simpa using ht.1, by simpa using ht.2⟩
  exact (tendsto_ofReal_nhdsNE ((a + b) / 2)).frequently hev.frequently

/-- Evaluation matrix of the normalized terminal power rows in logarithmic coordinates. -/
def finiteNodePowerEvaluationMatrix {J : ℕ}
    (β : Fin J → ℂ) (points : Fin J → ℂ) : Matrix (Fin J) (Fin J) ℂ :=
  fun row j => Complex.exp (β j * points row)

/-- The normalized power evaluation determinant varies continuously with all sample points. -/
theorem continuous_finiteNodePowerEvaluationMatrix_det {J : ℕ} (β : Fin J → ℂ) :
    Continuous (fun points : Fin J → ℂ =>
      (finiteNodePowerEvaluationMatrix β points).det) := by
  refine Continuous.matrix_det (continuous_pi fun row => continuous_pi fun _j => ?_)
  exact Complex.continuous_exp.comp (continuous_const.mul (continuous_apply row))

/-- A nonzero normalized power minor has a uniform positive norm floor when each of its sample
points is moved inside one sufficiently small neighborhood. -/
theorem exists_powerEvaluation_det_norm_lower_neighborhood {J : ℕ}
    (β : Fin J → ℂ) (points : Fin J → ℂ)
    (hdet : IsUnit (finiteNodePowerEvaluationMatrix β points).det) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ q : Fin J → ℂ, (∀ row, dist (q row) (points row) < ε) →
        c ≤ ‖(finiteNodePowerEvaluationMatrix β q).det‖ := by
  let D : (Fin J → ℂ) → ℂ := fun q => (finiteNodePowerEvaluationMatrix β q).det
  have hD : Continuous D := continuous_finiteNodePowerEvaluationMatrix_det β
  have hDne : D points ≠ 0 := hdet.ne_zero
  have hDpos : 0 < ‖D points‖ := norm_pos_iff.mpr hDne
  obtain ⟨ε, hε, hclose⟩ :=
    (Metric.continuousAt_iff.mp hD.continuousAt) (‖D points‖ / 2) (half_pos hDpos)
  refine ⟨ε, ‖D points‖ / 2, hε, half_pos hDpos, ?_⟩
  intro q hq
  have hq' : dist q points < ε := (dist_pi_lt_iff hε).2 hq
  have hdist : dist (D q) (D points) < ‖D points‖ / 2 := hclose hq'
  have hrev : ‖D points - D q‖ < ‖D points‖ / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have htri : ‖D points‖ - ‖D q‖ ≤ ‖D points - D q‖ :=
    norm_sub_norm_le _ _
  linarith

/-- **Real-interval power minor.** Distinct complex exponents admit pairwise distinct real sample
points in every nonempty interval such that their exponential evaluation determinant is a unit.

For the reflected AFE application take `β j = s_j - 1` and
`(a, b) = (log (1 / 2), 0)`. -/
theorem exists_realComplexInterval_powerEvaluation_det_isUnit
    {J : ℕ} {β : Fin J → ℂ} (hβ : Function.Injective β) {a b : ℝ} (hab : a < b) :
    ∃ points : Fin J → ℂ,
      Function.Injective points ∧
      (∀ row, points row ∈ realComplexInterval a b) ∧
      IsUnit (finiteNodePowerEvaluationMatrix β points).det := by
  let g : Fin J → ℂ → ℂ := fun j z => Complex.exp (β j * z)
  have hg : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ := by
    intro j
    have hdiff : Differentiable ℂ (g j) := by
      exact Complex.differentiable_exp.comp
        ((differentiable_const _).mul differentiable_id)
    exact hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hind : LinearIndependent ℂ g := by
    simpa [g] using HurwitzExp.expLin_linearIndependent hβ
  have hrestrict : LinearIndependent ℂ
      (fun j => Set.restrict (realComplexInterval a b) (g j)) :=
    GaloisForLFunctions.HTGeometry.linearIndependent_restrict_of_entire g hg hind
      (frequently_mem_realComplexInterval hab)
  obtain ⟨e, P, he, hPdet, hP⟩ :=
    GaloisForLFunctions.HTGeometry.exists_injective_evaluation_minor_of_linearIndependent
      (fun j => Set.restrict (realComplexInterval a b) (g j)) hrestrict
  let points : Fin J → ℂ := fun row => e row
  have hpoints : ∀ row, points row ∈ realComplexInterval a b := fun row => (e row).2
  have hpoints_inj : Function.Injective points := by
    intro row₁ row₂ hrow
    exact he (Subtype.ext hrow)
  have hmatrix : finiteNodePowerEvaluationMatrix β points = P := by
    ext row j
    simpa [finiteNodePowerEvaluationMatrix, points, g, Set.restrict] using (hP row j).symm
  exact ⟨points, hpoints_inj, hpoints, by rwa [hmatrix]⟩

end

end GaloisForLFunctions.RHTower
