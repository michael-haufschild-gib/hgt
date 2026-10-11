import GaloisForLFunctions.RHTower.PaperHurwitzCompactCharacter
import GaloisForLFunctions.HTGeometry.PaperDiagonalStrongConvergence

/-!
# A native strong-limit jump at the Hurwitz reflection wall

The complete resolvents vary strongly continuously along convergent source sequences. An explicit
Euler-safe rational-Hurwitz source sequence approaches the critical line through compact resolvents,
yet each resolvent remains exactly one unit from the limiting identity in operator norm. The paper
compact-ideal cost jumps from zero to infinity at this strong limit.
-/

namespace RHTower

noncomputable section
open Filter Classical GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Topology ENNReal

/-- Pointwise source continuity passes to every complete square-summable history. -/
theorem paperHurwitzResolvent_strong_tendsto {z : ℕ → ℂ} {rho : ℂ}
    (hz : Tendsto z atTop (𝓝 rho)) (f : PaperHurwitzHistory) :
    Tendsto (fun n => paperHurwitzResolvent (z n) f) atTop (𝓝 (paperHurwitzResolvent rho f)) := by
  have h := paperLpDiagonal_strong_tendsto
    (fun n k => (paperHurwitzRegularizer (z n) k : ℂ))
    (fun k => (paperHurwitzRegularizer rho k : ℂ)) 1 zero_le_one
    (fun n => norm_paperHurwitzRegularizer_complex_le (z n))
    (norm_paperHurwitzRegularizer_complex_le rho)
    (fun k => ((Complex.continuous_ofReal.comp (continuous_paperHurwitzRegularizer k)).tendsto rho).comp hz) f
  simpa only [← paperHurwitzResolvent_eq_diagonal] using h

private theorem regularizer_sub_one_bound (rho : ℂ) (k : ℕ) :
    ‖(paperHurwitzRegularizer rho k : ℂ) - 1‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [paperHurwitzRegularizer_pos rho k],
    by linarith [paperHurwitzRegularizer_le_one rho k]⟩

/-- Every off-wall source retains the full unit operator-norm gap from the wall identity. -/
theorem norm_paperHurwitzResolvent_sub_one (rho : ℂ) :
    ‖paperHurwitzResolvent rho - 1‖ = if rho.re = 1 / 2 then 0 else 1 := by
  by_cases hr : rho.re = 1 / 2
  · simp [paperHurwitzResolvent_of_wall hr, hr]
  · rw [if_neg hr]
    apply le_antisymm
    · have heq : paperHurwitzResolvent rho - 1 = lpDiagonalCLM
          (fun k => (paperHurwitzRegularizer rho k : ℂ) - 1) zero_le_one
          (regularizer_sub_one_bound rho) := by
        ext f k
        simp [paperHurwitzResolvent_apply, lpDiagonalCLM_apply, sub_mul]
      rw [heq]
      exact norm_lpDiagonalCLM_le _ _ _
    · have hc := paperHurwitzResolvent_compactIdealDistance_sub rho (1 / 2 : ℂ)
      have hw : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      rw [paperHurwitzResolvent_of_wall hw] at hc
      simp only [hr, hw, iff_true, if_false] at hc
      have h := compactIdealDistance_le (paperHurwitzResolvent rho - 1) 0 isCompactOperator_zero
      simpa only [sub_zero, hc] using h

/-- A prescribed critical-line point at each height. -/
def paperHurwitzWallPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

/-- A prescribed sequence of genuine open-strip source points, independent of the Xi divisor. -/
def paperHurwitzApproachPoint (t : ℝ) (n : ℕ) : ℂ :=
  (((1 / 2 : ℝ) + ((n : ℝ) + 3)⁻¹ : ℝ) : ℂ) + (t : ℂ) * Complex.I

theorem paperHurwitzWallPoint_re (t : ℝ) : (paperHurwitzWallPoint t).re = 1 / 2 := by
  simp [paperHurwitzWallPoint]

theorem paperHurwitzApproachPoint_re (t : ℝ) (n : ℕ) :
    (paperHurwitzApproachPoint t n).re = 1 / 2 + ((n : ℝ) + 3)⁻¹ := by
  simp only [paperHurwitzApproachPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- The whole sequence lies in the source strip where finite Hurwitz packets are faithful. -/
theorem paperHurwitzApproachPoint_strip (t : ℝ) (n : ℕ) :
    0 < (paperHurwitzApproachPoint t n).re ∧ (paperHurwitzApproachPoint t n).re < 1 := by
  rw [paperHurwitzApproachPoint_re]
  have hn : 0 < (n : ℝ) + 3 := by positivity
  have hp := inv_pos.mpr hn
  have hm := mul_inv_cancel₀ hn.ne'
  have hc := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hp.le
  constructor <;> nlinarith

theorem paperHurwitzApproachPoint_off_wall (t : ℝ) (n : ℕ) :
    (paperHurwitzApproachPoint t n).re ≠ 1 / 2 := by
  rw [paperHurwitzApproachPoint_re]
  have h : 0 < ((n : ℝ) + 3)⁻¹ := inv_pos.mpr (by positivity)
  linarith

/-- Literal source-packet provenance holds at every depth and every point of the approaching ray. -/
theorem paperHurwitzApproachPoint_source_energy (t : ℝ) (n k : ℕ) :
    paperHurwitzPowerEnergy (paperHurwitzApproachPoint t n) k =
      normalizedRationalHurwitzReflectionEnergy (2 ^ k) (paperHurwitzApproachPoint t n) :=
  (normalizedRationalHurwitzReflectionEnergy_eq_scale (paperHurwitzApproachPoint_strip t n) _).symm

theorem tendsto_paperHurwitzApproachPoint (t : ℝ) :
    Tendsto (paperHurwitzApproachPoint t) atTop (𝓝 (paperHurwitzWallPoint t)) := by
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
    (tendsto_const_nhds (x := (3 : ℝ)))
  have hi := tendsto_inv_atTop_zero.comp hn
  have hr := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add hi
  have hc := (Complex.continuous_ofReal.tendsto _).comp hr
  have h := hc.add (tendsto_const_nhds (x := (t : ℂ) * Complex.I))
  change Tendsto (fun n : ℕ => (((1 / 2 : ℝ) + ((n : ℝ) + 3)⁻¹ : ℝ) : ℂ) +
    (t : ℂ) * Complex.I) atTop (𝓝 (paperHurwitzWallPoint t))
  simpa only [paperHurwitzWallPoint, Function.comp_def, add_zero,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h

/-- Every approaching native source operator is compact. -/
theorem paperHurwitzApproachPoint_compact (t : ℝ) (n : ℕ) :
    IsCompactOperator (paperHurwitzResolvent (paperHurwitzApproachPoint t n)) :=
  (paperHurwitzResolvent_compact_iff _).mpr (paperHurwitzApproachPoint_off_wall t n)

/-- Nevertheless, their complete-history strong limit is the identity. -/
theorem tendsto_paperHurwitzApproachPoint_strong (t : ℝ) (f : PaperHurwitzHistory) :
    Tendsto (fun n => paperHurwitzResolvent (paperHurwitzApproachPoint t n) f) atTop (𝓝 f) := by
  have h := paperHurwitzResolvent_strong_tendsto (tendsto_paperHurwitzApproachPoint t) f
  rw [paperHurwitzResolvent_of_wall (paperHurwitzWallPoint_re t)] at h
  exact h

/-- The norm gap never decreases along this source sequence. -/
theorem paperHurwitzApproachPoint_norm_gap (t : ℝ) (n : ℕ) :
    ‖paperHurwitzResolvent (paperHurwitzApproachPoint t n) - 1‖ = 1 := by
  rw [norm_paperHurwitzResolvent_sub_one, if_neg (paperHurwitzApproachPoint_off_wall t n)]

/-- The proven paper cost vanishes along the entire off-wall source sequence. -/
theorem paperHurwitzApproachPoint_traceCost (t : ℝ) (n : ℕ) :
    compactOperatorTraceCost PaperHurwitzHistory
      (paperHurwitzResolvent (paperHurwitzApproachPoint t n)) = 0 := by
  rw [paperHurwitzResolvent_traceCost, if_neg (paperHurwitzApproachPoint_off_wall t n)]

/-- At its strong limit, that same ideal trace is infinite. -/
theorem paperHurwitzWallPoint_traceCost (t : ℝ) :
    compactOperatorTraceCost PaperHurwitzHistory
      (paperHurwitzResolvent (paperHurwitzWallPoint t)) = ∞ := by
  rw [paperHurwitzResolvent_traceCost, if_pos (paperHurwitzWallPoint_re t)]

end
end RHTower
