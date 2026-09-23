import GaloisForLFunctions.HTGeometry.EinastoSubquadraticMetricJets

/-!
# Actual curvature divergence for every Einasto exponent below two

The normalized actual metric jets determine the exact leading Kretschmann
coefficient. It is positive precisely at nonzero coupling, independently of
the algebraic sign. Thus every nonzero first-order correction is singular for
0<q<2, although the metric itself remains continuous and positive near zero.
The normalized Ricci scalar is controlled as well, including its sign.
-/
noncomputable section
open Filter Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def einastoSubquadraticKretschmannCoefficient (d k β : ℝ) : ℝ :=
  let q := exp (-einastoSubquadraticShape k)
  β ^ (2 : ℕ) * einastoPowerCorrectionCoefficient d (einastoSubquadraticShape k) ^ (2 : ℕ) *
    ((q * (q - 1)) ^ (2 : ℕ) + 4 * q ^ (2 : ℕ) + 4)

def einastoSubquadraticRicciCoefficient (d k β : ℝ) : ℝ :=
  let q := exp (-einastoSubquadraticShape k)
  β * einastoPowerCorrectionCoefficient d (einastoSubquadraticShape k) * (q + 1) * (q + 2)

/-- The sum of all three squared curvature contributions has no nonzero-coupling cancellation. -/
theorem einastoSubquadraticKretschmannCoefficient_pos_iff (d k β : ℝ) :
    0 < einastoSubquadraticKretschmannCoefficient d k β ↔ β ≠ 0 := by
  by_cases hb : β = 0
  · subst β
    simp [einastoSubquadraticKretschmannCoefficient]
  · have hF : einastoPowerCorrectionCoefficient d (einastoSubquadraticShape k) ≠ 0 :=
      ne_of_lt (einastoPowerCorrectionCoefficient_neg d (einastoSubquadraticShape k))
    have hpoly : 0 < (exp (-einastoSubquadraticShape k) * (exp (-einastoSubquadraticShape k) - 1)) ^ (2 : ℕ) +
        4 * exp (-einastoSubquadraticShape k) ^ (2 : ℕ) + 4 := by positivity
    exact iff_of_true (mul_pos (mul_pos (sq_pos_of_ne_zero hb) (sq_pos_of_ne_zero hF)) hpoly) hb

/-- Exact leading coefficient of the actual Kretschmann scalar for all couplings and signs. -/
theorem einastoSubquadraticMetric_scaled_Kretschmann_limit (d l k σ β : ℝ) :
    Tendsto (fun t => (exp t ^ (4 : ℕ) / einastoProfilePower l (einastoSubquadraticShape k) (exp t) ^ (2 : ℕ)) *
      radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) atBot
      (𝓝 (einastoSubquadraticKretschmannCoefficient d k β)) := by
  let a := einastoSubquadraticShape k
  have he : (fun t => (exp t ^ (4 : ℕ) / einastoProfilePower l a (exp t) ^ (2 : ℕ)) *
      radialKretschmannScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) =
      (fun t => (exp t ^ (2 : ℕ) * deriv (deriv (einastoShapePerturbedMetric d l a σ β)) (exp t) / einastoProfilePower l a (exp t)) ^ (2 : ℕ) +
        4 * (exp t * deriv (einastoShapePerturbedMetric d l a σ β) (exp t) / einastoProfilePower l a (exp t)) ^ (2 : ℕ) +
        4 * ((1 - einastoShapePerturbedMetric d l a σ β (exp t)) / einastoProfilePower l a (exp t)) ^ (2 : ℕ)) := by
    funext t
    unfold radialKretschmannScalar
    field_simp [(einastoProfilePower_pos l a t).ne']
  change Tendsto (fun t => (exp t ^ (4 : ℕ) / einastoProfilePower l a (exp t) ^ (2 : ℕ)) *
    radialKretschmannScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) atBot _
  rw [he]
  have h := (((einastoSubquadraticMetric_scaled_second_derivative_limit d l k σ β).pow 2).add
    (((einastoSubquadraticMetric_scaled_derivative_limit d l k σ β).pow 2).const_mul 4)).add
    (((einastoSubquadraticMetric_normalized_limit d l k σ β).pow 2).const_mul 4)
  have hc : (β * (exp (-a) * (exp (-a) - 1) * einastoPowerCorrectionCoefficient d a)) ^ (2 : ℕ) +
      4 * (β * (exp (-a) * einastoPowerCorrectionCoefficient d a)) ^ (2 : ℕ) +
      4 * (-β * einastoPowerCorrectionCoefficient d a) ^ (2 : ℕ) = einastoSubquadraticKretschmannCoefficient d k β := by
    unfold einastoSubquadraticKretschmannCoefficient a
    ring
  rwa [hc] at h

/-- Every nonzero coupling produces positive infinite curvature, even for the literal appendix sign. -/
theorem einastoSubquadraticMetric_Kretschmann_diverges_iff (d l k σ β : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) atBot atTop ↔
      β ≠ 0 := by
  by_cases hb : β = 0
  · subst β
    have he : einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ 0 =
        einastoMetric d l (einastoSubquadraticShape k) := by
      funext r
      exact einastoShapePerturbedMetric_zero_coupling d l (einastoSubquadraticShape k) σ r
    rw [he]
    have h := einastoRadialKretschmann_core_limit d l (einastoSubquadraticShape k)
    constructor
    · intro hi
      exact (not_tendsto_nhds_of_tendsto_atTop hi _ h).elim
    · intro hz
      exact (hz rfl).elim
  · have hL := einastoSubquadraticMetric_scaled_Kretschmann_limit d l k σ β
    have hW := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp (einastoSubquadraticWeight_tendsto_atTop l k)
    have h := hL.pos_mul_atTop ((einastoSubquadraticKretschmannCoefficient_pos_iff d k β).mpr hb) hW
    have he : (fun t => ((exp t ^ (4 : ℕ) / einastoProfilePower l (einastoSubquadraticShape k) (exp t) ^ (2 : ℕ)) *
        radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) *
        (einastoProfilePower l (einastoSubquadraticShape k) (exp t) / exp t ^ (2 : ℕ)) ^ (2 : ℕ)) =
        (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) := by
      funext t
      field_simp [(einastoProfilePower_pos l (einastoSubquadraticShape k) t).ne']
    simp only [Function.comp_def] at h
    rw [he] at h
    exact iff_of_true h hb

/-- Complete finite-limit classification on the singular side of the shape threshold. -/
theorem einastoSubquadraticMetric_Kretschmann_finite_limit_iff (d l k σ β K : ℝ) :
    Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) atBot (𝓝 K) ↔
      β = 0 ∧ K = 512 * Real.pi ^ (2 : ℕ) * exp d ^ (2 : ℕ) / 3 := by
  by_cases hb : β = 0
  · subst β
    have he : einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ 0 = einastoMetric d l (einastoSubquadraticShape k) := by
      funext r
      exact einastoShapePerturbedMetric_zero_coupling d l (einastoSubquadraticShape k) σ r
    rw [he]
    have h := einastoRadialKretschmann_core_limit d l (einastoSubquadraticShape k)
    constructor
    · intro hk
      exact ⟨rfl, tendsto_nhds_unique hk h⟩
    · rintro ⟨_, rfl⟩
      exact h
  · have hi := (einastoSubquadraticMetric_Kretschmann_diverges_iff d l k σ β).mpr hb
    constructor
    · intro hk
      exact (not_tendsto_nhds_of_tendsto_atTop hi K hk).elim
    · rintro ⟨hz, _⟩
      exact (hb hz).elim

theorem einastoSubquadraticMetric_regular_iff (d l k σ β : ℝ) :
    (∃ K : ℝ, Tendsto (fun t => radialKretschmannScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) atBot (𝓝 K)) ↔
      β = 0 := by
  simp only [einastoSubquadraticMetric_Kretschmann_finite_limit_iff, exists_eq_right]

/-- The Ricci scalar has its own exact nonzero leading coefficient. -/
theorem einastoSubquadraticMetric_scaled_Ricci_limit (d l k σ β : ℝ) :
    Tendsto (fun t => (exp t ^ (2 : ℕ) / einastoProfilePower l (einastoSubquadraticShape k) (exp t)) *
      radialRicciScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) atBot
      (𝓝 (einastoSubquadraticRicciCoefficient d k β)) := by
  let a := einastoSubquadraticShape k
  have he : (fun t => (exp t ^ (2 : ℕ) / einastoProfilePower l a (exp t)) * radialRicciScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) =
      (fun t => exp t ^ (2 : ℕ) * deriv (deriv (einastoShapePerturbedMetric d l a σ β)) (exp t) / einastoProfilePower l a (exp t) +
        4 * (exp t * deriv (einastoShapePerturbedMetric d l a σ β) (exp t) / einastoProfilePower l a (exp t)) -
        2 * ((1 - einastoShapePerturbedMetric d l a σ β (exp t)) / einastoProfilePower l a (exp t))) := by
    funext t
    unfold radialRicciScalar
    field_simp [(einastoProfilePower_pos l a t).ne']
    ring
  change Tendsto (fun t => (exp t ^ (2 : ℕ) / einastoProfilePower l a (exp t)) * radialRicciScalar (einastoShapePerturbedMetric d l a σ β) (exp t)) atBot _
  rw [he]
  have h := ((einastoSubquadraticMetric_scaled_second_derivative_limit d l k σ β).add
    ((einastoSubquadraticMetric_scaled_derivative_limit d l k σ β).const_mul 4)).sub
    ((einastoSubquadraticMetric_normalized_limit d l k σ β).const_mul 2)
  have hc : β * (exp (-a) * (exp (-a) - 1) * einastoPowerCorrectionCoefficient d a) +
      4 * (β * (exp (-a) * einastoPowerCorrectionCoefficient d a)) -
      2 * (-β * einastoPowerCorrectionCoefficient d a) = einastoSubquadraticRicciCoefficient d k β := by
    unfold einastoSubquadraticRicciCoefficient a
    ring
  rwa [hc] at h

/-- Ricci tends to negative infinity at positive coupling and positive infinity at negative coupling. -/
theorem einastoSubquadraticMetric_Ricci_complete_limit (d l k σ β : ℝ) :
    Tendsto (fun t => radialRicciScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) atBot
      (if 0 < β then atBot else if β < 0 then atTop else 𝓝 (-32 * Real.pi * exp d)) := by
  have hL := einastoSubquadraticMetric_scaled_Ricci_limit d l k σ β
  have hW := einastoSubquadraticWeight_tendsto_atTop l k
  have he : (fun t => ((exp t ^ (2 : ℕ) / einastoProfilePower l (einastoSubquadraticShape k) (exp t)) *
      radialRicciScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) *
      (einastoProfilePower l (einastoSubquadraticShape k) (exp t) / exp t ^ (2 : ℕ))) =
      (fun t => radialRicciScalar (einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ β) (exp t)) := by
    funext t
    field_simp [(einastoProfilePower_pos l (einastoSubquadraticShape k) t).ne']
  have hF := einastoPowerCorrectionCoefficient_neg d (einastoSubquadraticShape k)
  by_cases hp : 0 < β
  · rw [if_pos hp]
    have hc : einastoSubquadraticRicciCoefficient d k β < 0 := by
      unfold einastoSubquadraticRicciCoefficient
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp hF) (by positivity)) (by positivity)
    have h := hL.neg_mul_atTop hc hW
    rwa [he] at h
  · rw [if_neg hp]
    by_cases hn : β < 0
    · rw [if_pos hn]
      have hc : 0 < einastoSubquadraticRicciCoefficient d k β := by
        unfold einastoSubquadraticRicciCoefficient
        exact mul_pos (mul_pos (mul_pos_of_neg_of_neg hn hF) (by positivity)) (by positivity)
      have h := hL.pos_mul_atTop hc hW
      rwa [he] at h
    · rw [if_neg hn]
      have hz : β = 0 := by linarith
      subst β
      have hm : einastoShapePerturbedMetric d l (einastoSubquadraticShape k) σ 0 = einastoMetric d l (einastoSubquadraticShape k) := by
        funext r
        exact einastoShapePerturbedMetric_zero_coupling d l (einastoSubquadraticShape k) σ r
      rw [hm]
      simpa only [radialRicciScalar_einasto] using einastoRadialRicci_core_limit d l (einastoSubquadraticShape k)

end GaloisForLFunctions.HTGeometry
