import GaloisForLFunctions.HTGeometry.EinastoSubquadraticCurvature
import GaloisForLFunctions.HTGeometry.EinastoSuperGaussianRegularGeometry

/-!
# Complete central-curvature classification of the actual Einasto correction

Close the shape audit of equation (15) in arXiv:2608.23600. The single actual
integral construction has finite central Kretschmann curvature exactly when
the coupling vanishes or q=exp(-a)≥2. Every nonzero coupling with q<2 gives
positive infinite curvature, for either algebraic sign. On the regular side,
the limit is explicit, including the exceptional Gaussian derivative term.
The bridges identify actual metrics and their derivatives, not just source
formulas or formal series. All parameter choices are unrestricted real data.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem einastoShape_subquadratic_parameterization (a : ℝ) :
    (∃ k : ℝ, a = einastoSubquadraticShape k) ↔ exp (-a) < 2 := by
  constructor
  · rintro ⟨k, rfl⟩
    exact einastoSubquadraticShape_exponent_lt_two k
  · intro hq
    have hd : 1 < 2 / exp (-a) := (lt_div_iff₀ (exp_pos (-a))).mpr (by simpa only [one_mul] using hq)
    have hp : 0 < 2 / exp (-a) - 1 := sub_pos.mpr hd
    refine ⟨log (2 / exp (-a) - 1), ?_⟩
    unfold einastoSubquadraticShape
    rw [exp_log hp]
    have he : (2 : ℝ) / (1 + (2 / exp (-a) - 1)) = exp (-a) := by field_simp; ring
    rw [he, log_exp, neg_neg]

theorem einastoShape_superGaussian_parameterization (a : ℝ) :
    (∃ k : ℝ, a = einastoSuperGaussianShape k) ↔ 2 < exp (-a) := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [einastoSuperGaussianShape_exponent]
    linarith [exp_pos k]
  · intro hq
    refine ⟨log (exp (-a) - 2), ?_⟩
    unfold einastoSuperGaussianShape
    rw [exp_log (sub_pos.mpr hq), show (2 : ℝ) + (exp (-a) - 2) = exp (-a) by ring,
      log_exp, neg_neg]

/-- The unified integral metric agrees locally with the fully audited Gaussian construction. -/
theorem einastoShapeMetric_gaussian_local (d l σ β t : ℝ) :
    einastoShapePerturbedMetric d l einastoGaussianShape σ β =ᶠ[𝓝 (exp t)] einastoGaussianPerturbedMetric d l σ β := by
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have hp := einastoShapeCorrection_actual_integral d l einastoGaussianShape σ (log r)
  have hg := einastoGaussianCorrection_actual_integral d l σ (log r)
  rw [exp_log hr] at hp hg
  have hc := hp.trans hg.symm
  unfold einastoShapePerturbedMetric einastoGaussianPerturbedMetric
  rw [hc]

/-- Local metric equality transfers both actual curvature expressions through two derivatives. -/
theorem einastoShapeMetric_gaussian_curvatures (d l σ β t : ℝ) :
    radialKretschmannScalar (einastoShapePerturbedMetric d l einastoGaussianShape σ β) (exp t) =
      radialKretschmannScalar (einastoGaussianPerturbedMetric d l σ β) (exp t) ∧
    radialRicciScalar (einastoShapePerturbedMetric d l einastoGaussianShape σ β) (exp t) =
      radialRicciScalar (einastoGaussianPerturbedMetric d l σ β) (exp t) := by
  have h := einastoShapeMetric_gaussian_local d l σ β t
  constructor
  · unfold radialKretschmannScalar
    rw [h.self_of_nhds, h.deriv_eq, h.deriv.deriv_eq]
  · unfold radialRicciScalar
    rw [h.self_of_nhds, h.deriv_eq, h.deriv.deriv_eq]

theorem einastoShapeMetric_superGaussian_local (d l k σ β t : ℝ) :
    einastoShapePerturbedMetric d l (einastoSuperGaussianShape k) σ β =ᶠ[𝓝 (exp t)]
      einastoSuperGaussianPerturbedMetric d l k σ β := by
  filter_upwards [eventually_gt_nhds (exp_pos t)] with r hr
  have hp := einastoShapeCorrection_actual_integral d l (einastoSuperGaussianShape k) σ (log r)
  have hg := einastoSuperGaussianCorrection_actual_integral d l k σ (log r)
  rw [exp_log hr] at hp hg
  have hc := hp.trans hg.symm
  unfold einastoShapePerturbedMetric einastoSuperGaussianPerturbedMetric
  rw [hc]

theorem einastoShapeMetric_superGaussian_curvatures (d l k σ β t : ℝ) :
    radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSuperGaussianShape k) σ β) (exp t) =
      radialKretschmannScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t) ∧
    radialRicciScalar (einastoShapePerturbedMetric d l (einastoSuperGaussianShape k) σ β) (exp t) =
      radialRicciScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t) := by
  have h := einastoShapeMetric_superGaussian_local d l k σ β t
  constructor
  · unfold radialKretschmannScalar
    rw [h.self_of_nhds, h.deriv_eq, h.deriv.deriv_eq]
  · unfold radialRicciScalar
    rw [h.self_of_nhds, h.deriv_eq, h.deriv.deriv_eq]

/-- The Gaussian boundary contributes a derivative term absent on the strictly regular side. -/
def einastoShapeCoreMultiplier (d l a σ β : ℝ) : ℝ :=
  1 + (if exp (-a) = 2 then 72 * β / exp l ^ 2 else 0) + 64 * Real.pi * β * (1 - σ) * exp d

theorem einastoShapeCoreMultiplier_zero_coupling (d l a σ : ℝ) : einastoShapeCoreMultiplier d l a σ 0 = 1 := by
  simp [einastoShapeCoreMultiplier]

theorem einastoShapeCoreMultiplier_gaussian (d l σ β : ℝ) :
    einastoShapeCoreMultiplier d l einastoGaussianShape σ β = einastoGaussianCoreMultiplier d l σ β := by
  unfold einastoShapeCoreMultiplier
  rw [einastoGaussianShape_exponent, if_pos rfl]
  rfl

theorem einastoShapeCoreMultiplier_superGaussian (d l k σ β : ℝ) :
    einastoShapeCoreMultiplier d l (einastoSuperGaussianShape k) σ β = einastoSuperGaussianCoreMultiplier d σ β := by
  have hn : exp (-einastoSuperGaussianShape k) ≠ 2 := by
    rw [einastoSuperGaussianShape_exponent]
    linarith [exp_pos k]
  unfold einastoShapeCoreMultiplier
  rw [if_neg hn, add_zero]
  rfl

/-- Complete actual curvature limit: finite exactly on the regular branch, infinite otherwise. -/
theorem einastoShapeMetric_Kretschmann_complete_limit (d l a σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) atBot
      (if β ≠ 0 ∧ exp (-a) < 2 then atTop else
        𝓝 ((512 * Real.pi ^ 2 * exp d ^ 2 / 3) * einastoShapeCoreMultiplier d l a σ β ^ 2)) := by
  by_cases hb : β = 0
  · subst β
    have he : einastoShapePerturbedMetric d l a σ 0 = einastoMetric d l a := by
      funext r
      exact einastoShapePerturbedMetric_zero_coupling d l a σ r
    simp only [ne_eq, not_true_eq_false, false_and, if_false, einastoShapeCoreMultiplier_zero_coupling,
      one_pow, mul_one, he]
    exact einastoRadialKretschmann_core_limit d l a
  · by_cases hq : exp (-a) < 2
    · rw [if_pos ⟨hb, hq⟩]
      obtain ⟨k, ha⟩ := (einastoShape_subquadratic_parameterization a).mpr hq
      rw [ha]
      exact (einastoSubquadraticMetric_Kretschmann_diverges_iff d l k σ β).mpr hb
    · rw [if_neg (by rintro ⟨_, h⟩; exact hq h)]
      by_cases htwo : exp (-a) = 2
      · have ha : a = einastoGaussianShape := by
          have h := congrArg log htwo
          rw [log_exp] at h
          unfold einastoGaussianShape
          linarith
        rw [ha, einastoShapeCoreMultiplier_gaussian]
        have he : (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l einastoGaussianShape σ β) (exp t)) =
            (fun t => radialKretschmannScalar (einastoGaussianPerturbedMetric d l σ β) (exp t)) := by
          funext t
          exact (einastoShapeMetric_gaussian_curvatures d l σ β t).1
        rw [he]
        exact einastoGaussianPerturbedMetric_Kretschmann_explicit d l σ β
      · have hgt : 2 < exp (-a) := lt_of_le_of_ne (not_lt.mp hq) (Ne.symm htwo)
        obtain ⟨k, ha⟩ := (einastoShape_superGaussian_parameterization a).mpr hgt
        rw [ha, einastoShapeCoreMultiplier_superGaussian]
        have he : (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSuperGaussianShape k) σ β) (exp t)) =
            (fun t => radialKretschmannScalar (einastoSuperGaussianPerturbedMetric d l k σ β) (exp t)) := by
          funext t
          exact (einastoShapeMetric_superGaussian_curvatures d l k σ β t).1
        rw [he]
        exact einastoSuperGaussianPerturbedMetric_Kretschmann_explicit d l k σ β

/-- An exact iff, including zero coupling and the Gaussian endpoint. -/
theorem einastoShapeMetric_Kretschmann_finite_limit_iff (d l a σ β K : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) atBot (𝓝 K) ↔
      (β = 0 ∨ 2 ≤ exp (-a)) ∧
        K = (512 * Real.pi ^ 2 * exp d ^ 2 / 3) * einastoShapeCoreMultiplier d l a σ β ^ 2 := by
  have h := einastoShapeMetric_Kretschmann_complete_limit d l a σ β
  by_cases hs : β ≠ 0 ∧ exp (-a) < 2
  · rw [if_pos hs] at h
    constructor
    · intro hk
      exact (not_tendsto_nhds_of_tendsto_atTop h K hk).elim
    · rintro ⟨hr, _⟩
      rcases hr with hz | hq
      · exact (hs.1 hz).elim
      · exact (not_le.mpr hs.2 hq).elim
  · rw [if_neg hs] at h
    have hr : β = 0 ∨ 2 ≤ exp (-a) := by
      by_cases hb : β = 0
      · exact Or.inl hb
      · right
        by_contra hq
        exact hs ⟨hb, lt_of_not_ge hq⟩
    constructor
    · intro hk
      exact ⟨hr, tendsto_nhds_unique hk h⟩
    · rintro ⟨_, rfl⟩
      exact h

/-- Full regularity threshold for the actual first-order metric, independent of the sign discrepancy. -/
theorem einastoShapeMetric_regular_iff (d l a σ β : ℝ) :
    (∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) atBot (𝓝 K)) ↔
      β = 0 ∨ 2 ≤ exp (-a) := by
  simp only [einastoShapeMetric_Kretschmann_finite_limit_iff, exists_eq_right]

theorem einastoShapeMetric_Kretschmann_diverges_iff (d l a σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) atBot atTop ↔
      β ≠ 0 ∧ exp (-a) < 2 := by
  have h := einastoShapeMetric_Kretschmann_complete_limit d l a σ β
  by_cases hs : β ≠ 0 ∧ exp (-a) < 2
  · rw [if_pos hs] at h
    exact iff_of_true h hs
  · rw [if_neg hs] at h
    constructor
    · intro hi
      exact (not_tendsto_nhds_of_tendsto_atTop hi _ h).elim
    · intro hc
      exact (hs hc).elim

/-- In the paper's physical Einasto parameter α=exp(a), the exact nonzero-coupling threshold is α≤1/2. -/
theorem einastoShapeMetric_physical_shape_regular_iff (d l a σ β : ℝ) :
    (∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) atBot (𝓝 K)) ↔
      β = 0 ∨ exp a ≤ (1 / 2 : ℝ) := by
  rw [einastoShapeMetric_regular_iff]
  have he : exp a * exp (-a) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hq : 2 ≤ exp (-a) ↔ exp a ≤ (1 / 2 : ℝ) := by
    constructor
    · intro h
      have hm := mul_le_mul_of_nonneg_left h (exp_pos a).le
      rw [he] at hm
      linarith
    · intro h
      have hm := mul_le_mul_of_nonneg_right h (exp_pos (-a)).le
      rw [he] at hm
      linarith
  exact or_congr Iff.rfl hq

end GaloisForLFunctions.HTGeometry
