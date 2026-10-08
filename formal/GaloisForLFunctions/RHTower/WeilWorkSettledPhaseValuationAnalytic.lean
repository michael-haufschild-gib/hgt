import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationResidueSum
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseGeometricSeries

/-!
# The analytic local residue function of the actual source

All valuation endpoints assemble into one holomorphic function on the disk of
radius `sqrt p`. The actual ratio series converge uniformly on every smaller
closed disk. No coefficient sign or arithmetic exhaustion premise is added.
-/

open Complex Filter Topology Metric Set
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

def valuationResidueSeries (u : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, (u k : ℂ) * z ^ k

def valuationRatioSeries (lam : ℕ → ℝ) (p : ℕ) (s : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, (LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
    LSeries (sourceCoeff lam) (s : ℂ)) * z ^ k

private theorem inverse_sqrt_mul_lt_one {p : ℕ} (hp : p.Prime) {R : ℝ}
    (hR : R < Real.sqrt (p : ℝ)) : (Real.sqrt (p : ℝ))⁻¹ * R < 1 := by
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  rw [mul_comm, ← div_eq_mul_inv, div_lt_one hs]
  exact hR

theorem valuation_powerSeries_differentiableOn {p : ℕ} (hp : p.Prime)
    {a : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ k, ‖a k‖ ≤ C * (Real.sqrt (p : ℝ))⁻¹ ^ k) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' k, a k * z ^ k)
      (ball 0 (Real.sqrt (p : ℝ))) := by
  intro z hz
  have hz' : ‖z‖ < Real.sqrt (p : ℝ) := by
    simpa only [mem_ball, dist_zero_right] using hz
  obtain ⟨R, hzR, hRp⟩ := exists_between hz'
  have hR : 0 ≤ R := (norm_nonneg z).trans hzR.le
  have hd := geometric_series_differentiableOn hC (by positivity) hR ha
    (inverse_sqrt_mul_lt_one hp hRp)
  have hmem : z ∈ ball (0 : ℂ) R := by simpa only [mem_ball, dist_zero_right] using hzR
  exact (hd.differentiableAt (isOpen_ball.mem_nhds hmem)).differentiableWithinAt

/-- Actual endpoint normalization and holomorphy, with the uniform radial
limit on every compact centered disk. Nonvanishing is a separate obligation. -/
theorem exists_forward_valuation_analytic {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) :
    ∃ u : ℕ → ℝ, 0 < u 0 ∧ HasSum u 1 ∧
      (∀ k : ℕ, Tendsto (fun s : ℝ =>
        LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (u k : ℂ))) ∧
      valuationResidueSeries u 0 = (u 0 : ℂ) ∧ valuationResidueSeries u 1 = 1 ∧
      DifferentiableOn ℂ (valuationResidueSeries u) (ball 0 (Real.sqrt (p : ℝ))) ∧
      (∀ z : ℂ, ‖z‖ < Real.sqrt (p : ℝ) →
        Summable (fun k => ‖(u k : ℂ) * z ^ k‖)) ∧
      ∀ R : ℝ, 0 ≤ R → R < Real.sqrt (p : ℝ) →
        TendstoUniformlyOn (valuationRatioSeries lam p) (valuationResidueSeries u)
          (𝓝[>] 1) (closedBall 0 R) := by
  obtain ⟨u, C, hu0, hC, hu, hb, _, hsum⟩ := exists_forward_valuation_normalized_series hW hp
  have hrho : 0 ≤ (Real.sqrt (p : ℝ))⁻¹ := by positivity
  have hub (k : ℕ) : ‖(u k : ℂ)‖ ≤ C * (Real.sqrt (p : ℝ))⁻¹ ^ k := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb k
  refine ⟨u, hu0, hsum, hu, ?_, ?_, ?_, ?_, ?_⟩
  · unfold valuationResidueSeries
    rw [tsum_eq_single 0]
    · simp
    · intro k hk
      simp [zero_pow hk]
  · simp only [valuationResidueSeries, one_pow, mul_one, ← Complex.ofReal_tsum,
      hsum.tsum_eq, Complex.ofReal_one]
  · exact valuation_powerSeries_differentiableOn hp hC hub
  · intro z hz
    exact geometric_series_norm_summable hrho hub (inverse_sqrt_mul_lt_one hp hz)
  · intro R hR hRp
    obtain ⟨D, _, hDb⟩ := exists_forward_valuation_ratio_geometric hW hp
    exact geometric_series_tendstoUniformlyOn hrho hR
      (inverse_sqrt_mul_lt_one hp hRp) hu hDb

end RHTower.WeilSingularArithmetic
