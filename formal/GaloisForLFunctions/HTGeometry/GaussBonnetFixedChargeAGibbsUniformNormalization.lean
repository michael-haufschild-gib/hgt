import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddUniformEnergy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsNormalizedOddProfile

/-!
# Uniform normalization by the actual moving barrier

The true quartic barrier scale stays positive and tends to its positive
critical amplitude. Its first correction vanishes. A compact polynomial
reference family and the uniform energy error therefore give uniform
convergence of the barrier-normalized first profile correction.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsBarrierScale (w φ τ l : ℝ) : ℝ :=
  egbFixedChargeAGibbsBarrier w φ τ l / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ)

def egbFixedChargeAGibbsNormalizationState (w φ τ l : ℝ) : ℝ × ℝ :=
  (1 / egbFixedChargeAGibbsBarrierScale w φ τ l,
   ((egbFixedChargeAGibbsBarrierScale w φ τ l - egbFixedChargeAGibbsBarrierCoefficient w φ) /
    egbCoexistenceASymmetricRatio τ) / egbFixedChargeAGibbsBarrierScale w φ τ l)

def egbFixedChargeAGibbsNormalizationReference (w φ τ l ψ : ℝ) : ℝ :=
  (egbFixedChargeAGibbsNormalizationState w φ τ l).1 *
    (egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ (4 : ℕ)) -
  (egbFixedChargeAGibbsNormalizationState w φ τ l).2 * cos ψ ^ (4 : ℕ)

theorem egbFixedChargeAGibbsBarrierScale_pos (w φ τ l : ℝ) :
    0 < egbFixedChargeAGibbsBarrierScale w φ τ l := by
  have hb := egbFixedChargeAGibbsBarrier_pos w φ τ l
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAGibbsBarrierScale
  positivity

theorem egbFixedChargeAGibbsNormalizationState_critical_limit (w φ l : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsNormalizationState w φ τ l) atBot
      (𝓝 ((1 / egbFixedChargeAGibbsBarrierCoefficient w φ), (0 : ℝ))) := by
  have hq := egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l
  have hb := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  have hi := (tendsto_const_nhds (x := (1 : ℝ))).div hq hb.ne'
  have he := (egbFixedChargeAGibbsBarrier_first_correction_limit w φ l).div hq hb.ne'
  simp only [zero_div] at he
  exact hi.prodMk_nhds he

theorem egbFixedChargeAGibbsNormalizationReference_uniform_limit (w φ l : ℝ) :
    TendstoUniformly (fun τ ψ => egbFixedChargeAGibbsNormalizationReference w φ τ l ψ)
      (fun ψ => 4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ (4 : ℕ)) atBot := by
  let model : (ℝ × ℝ) → Icc (-1 : ℝ) 1 → ℝ := fun s t =>
    s.1 * (egbFixedChargeAGibbsOddCoefficient w φ * (t : ℝ) * (1 - (t : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)) -
      s.2 * (1 - (t : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ)
  have hc : Continuous ↿model := by dsimp [model]; fun_prop
  have hu := Continuous.tendstoUniformly model hc ((1 / egbFixedChargeAGibbsBarrierCoefficient w φ), (0 : ℝ))
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := (Metric.tendstoUniformly_iff.mp hu) ε hε
  filter_upwards [(egbFixedChargeAGibbsNormalizationState_critical_limit w φ l).eventually he] with τ hτ
  intro ψ
  let t : Icc (-1 : ℝ) 1 := ⟨sin ψ, neg_one_le_sin ψ, sin_le_one ψ⟩
  have hs : (1 - sin ψ ^ (2 : ℕ)) ^ (2 : ℕ) = cos ψ ^ (4 : ℕ) := by
    have h : 1 - sin ψ ^ (2 : ℕ) = cos ψ ^ (2 : ℕ) := by linarith [sin_sq_add_cos_sq ψ]
    rw [h]
    ring
  have hcrit : model ((1 / egbFixedChargeAGibbsBarrierCoefficient w φ), (0 : ℝ)) t =
      4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ (4 : ℕ) := by
    dsimp [model, t]
    rw [hs, ← egbFixedChargeAGibbsOddCoefficient_barrier_ratio w φ]
    ring
  have hactual : model (egbFixedChargeAGibbsNormalizationState w φ τ l) t =
      egbFixedChargeAGibbsNormalizationReference w φ τ l ψ := by
    dsimp [model, t, egbFixedChargeAGibbsNormalizationReference]
    rw [hs]
  have h := hτ t
  rwa [hcrit, hactual] at h

theorem egbFixedChargeAInteriorGibbsGap_normalization_error (w φ τ l₁ l₂ ψ : ℝ) :
    (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos ψ ^ (4 : ℕ)) /
        egbCoexistenceASymmetricRatio τ - egbFixedChargeAGibbsNormalizationReference w φ τ l₂ ψ =
    (((egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbCoexistenceASymmetricRatio τ ^ (4 : ℕ) -
       egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ) -
       egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ (4 : ℕ)) / egbFixedChargeAGibbsBarrierScale w φ τ l₂ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hb := egbFixedChargeAGibbsBarrier_pos w φ τ l₂
  unfold egbFixedChargeAGibbsNormalizationReference egbFixedChargeAGibbsNormalizationState egbFixedChargeAGibbsBarrierScale
  dsimp only
  field_simp <;> ring

theorem egbFixedChargeAInteriorGibbsGap_uniform_normalized_first_limit (w φ l₁ l₂ : ℝ) :
    TendstoUniformly (fun τ ψ => (egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ -
      cos ψ ^ (4 : ℕ)) / egbCoexistenceASymmetricRatio τ)
      (fun ψ => 4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ (4 : ℕ)) atBot := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hB := egbFixedChargeAGibbsBarrierCoefficient_pos w φ
  have href := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAGibbsNormalizationReference_uniform_limit w φ l₂))
    (ε / 2) (by positivity)
  have henergy := (Metric.tendstoUniformly_iff.mp (egbFixedChargeAInteriorGibbsGap_uniform_first_correction_limit w φ l₁))
    (ε * egbFixedChargeAGibbsBarrierCoefficient w φ / 8) (by positivity)
  have hscale := (egbFixedChargeAGibbsBarrier_quartic_critical_limit w φ l₂).eventually_const_lt
    (show egbFixedChargeAGibbsBarrierCoefficient w φ / 2 < egbFixedChargeAGibbsBarrierCoefficient w φ by linarith)
  filter_upwards [href, henergy, hscale] with τ hr he hq
  intro ψ
  have hpos := egbFixedChargeAGibbsBarrierScale_pos w φ τ l₂
  change egbFixedChargeAGibbsBarrierCoefficient w φ / 2 < egbFixedChargeAGibbsBarrierScale w φ τ l₂ at hq
  have herror : dist (egbFixedChargeAGibbsNormalizationReference w φ τ l₂ ψ)
      ((egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos ψ ^ (4 : ℕ)) /
        egbCoexistenceASymmetricRatio τ) ≤ ε / 4 := by
    rw [dist_comm, Real.dist_eq, egbFixedChargeAInteriorGibbsGap_normalization_error, abs_div, abs_of_pos hpos]
    apply (div_le_iff₀ hpos).mpr
    have heψ := he ψ
    rw [Real.dist_eq, abs_sub_comm] at heψ
    nlinarith
  calc
    _ ≤ dist (4 * egbFixedChargeAMiddleMeanCorrection φ * sin ψ * cos ψ ^ (4 : ℕ))
          (egbFixedChargeAGibbsNormalizationReference w φ τ l₂ ψ) +
        dist (egbFixedChargeAGibbsNormalizationReference w φ τ l₂ ψ)
          ((egbFixedChargeAInteriorGibbsGap w φ τ l₁ ψ / egbFixedChargeAGibbsBarrier w φ τ l₂ - cos ψ ^ (4 : ℕ)) /
            egbCoexistenceASymmetricRatio τ) := dist_triangle _ _ _
    _ < ε := by linarith [hr ψ]

end GaloisForLFunctions.HTGeometry
