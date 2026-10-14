import GaloisForLFunctions.RHTower.PaperHurwitzFredholmFiniteLimits
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Complete finite determinant spectrum at the native norm-zero limit

Every real target at least one is realized by explicit shrinking couplings on
the same quadratic Hurwitz source approach. The full finite limit spectrum of
this family is exactly that half-line, despite a common operator-norm limit zero.
-/

namespace RHTower
noncomputable section
open Filter GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt
open scoped Topology

theorem paperHurwitzFiniteFredholmLimit_ge_one (c : ℝ) :
    1 ≤ paperHurwitzFiniteFredholmLimit c := by
  rw [paperHurwitzFiniteFredholmLimit, ← Real.exp_zero, Real.exp_le_exp]
  exact mul_nonneg (sq_nonneg _) (Real.log_pos (by norm_num)).le

def paperHurwitzTargetDensity (D : Set.Ici (1 : ℝ)) : ℝ :=
  Real.sqrt (Real.log (D : ℝ) / Real.log 2)

theorem paperHurwitzTargetDensity_realizes (D : Set.Ici (1 : ℝ)) :
    paperHurwitzFiniteFredholmLimit (paperHurwitzTargetDensity D) = (D : ℝ) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [paperHurwitzFiniteFredholmLimit, paperHurwitzTargetDensity,
    Real.sq_sqrt (div_nonneg (Real.log_nonneg D.property) hl.le),
    div_mul_cancel₀ _ hl.ne', Real.exp_log (lt_of_lt_of_le zero_lt_one D.property)]

theorem paperHurwitzFiniteFredholmLimit_range :
    Set.range paperHurwitzFiniteFredholmLimit = Set.Ici (1 : ℝ) := by
  ext D
  constructor
  · rintro ⟨c, rfl⟩
    exact paperHurwitzFiniteFredholmLimit_ge_one c
  · intro hD
    exact ⟨paperHurwitzTargetDensity ⟨D, hD⟩, paperHurwitzTargetDensity_realizes ⟨D, hD⟩⟩

theorem paperHurwitzFiniteFredholmLimit_eq_iff (c d : ℝ) :
    paperHurwitzFiniteFredholmLimit c = paperHurwitzFiniteFredholmLimit d ↔ |c| = |d| := by
  constructor
  · intro h
    have he := Real.exp_injective h
    have hs : c ^ 2 = d ^ 2 := mul_right_cancel₀ (Real.log_pos (by norm_num)).ne' he
    exact (sq_eq_sq_iff_abs_eq_abs c d).mp hs
  · intro h
    have hs : c ^ 2 = d ^ 2 := (sq_eq_sq_iff_abs_eq_abs c d).mpr h
    simp only [paperHurwitzFiniteFredholmLimit, hs]

theorem paperHurwitz_target_norm_zero_realization (t : ℝ) (D : Set.Ici (1 : ℝ)) :
    (∀ N, MemSchattenClass 1 (paperHurwitzFinitePerturbation t (paperHurwitzTargetDensity D) N)) ∧
    Tendsto (paperHurwitzFinitePerturbation t (paperHurwitzTargetDensity D)) atTop (𝓝 0) ∧
    Tendsto (paperHurwitzFiniteFredholmValue t (paperHurwitzTargetDensity D)) atTop
      (𝓝 ((D : ℝ) : ℂ)) := by
  refine ⟨paperHurwitzFinitePerturbation_traceClass t _,
    paperHurwitzFinitePerturbation_tendsto_zero t _, ?_⟩
  simpa only [paperHurwitzTargetDensity_realizes] using
    paperHurwitzFiniteFredholmValue_tendsto t (paperHurwitzTargetDensity D)

theorem paperHurwitz_target_zero_cost_realization (t : ℝ) (D : Set.Ici (1 : ℝ)) :
    (∀ N, MemSchattenClass 1 (paperHurwitzFinitePerturbation t (paperHurwitzTargetDensity D) N) ∧
      compactOperatorTraceCost PaperHurwitzHistory
        (paperHurwitzFinitePerturbation t (paperHurwitzTargetDensity D) N) = 0) ∧
    Tendsto (paperHurwitzFinitePerturbation t (paperHurwitzTargetDensity D)) atTop (𝓝 0) ∧
    Tendsto (paperHurwitzFiniteFredholmValue t (paperHurwitzTargetDensity D)) atTop
      (𝓝 ((D : ℝ) : ℂ)) := by
  obtain ⟨htrace, hnorm, hdet⟩ := paperHurwitz_target_norm_zero_realization t D
  exact ⟨fun N => ⟨htrace N, paperHurwitzFinitePerturbation_traceCost_zero t _ N⟩, hnorm, hdet⟩

def paperHurwitzNormZeroDeterminantLimits (t : ℝ) : Set ℝ :=
  {D | ∃ c : ℝ,
    (∀ N, MemSchattenClass 1 (paperHurwitzFinitePerturbation t c N) ∧
      compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzFinitePerturbation t c N) = 0) ∧
    Tendsto (paperHurwitzFinitePerturbation t c) atTop (𝓝 0) ∧
    Tendsto (paperHurwitzFiniteFredholmValue t c) atTop (𝓝 (D : ℂ))}

theorem paperHurwitzNormZeroDeterminantLimits_eq (t : ℝ) :
    paperHurwitzNormZeroDeterminantLimits t = Set.Ici (1 : ℝ) := by
  ext D
  constructor
  · rintro ⟨c, _, _, hD⟩
    have h := tendsto_nhds_unique (paperHurwitzFiniteFredholmValue_tendsto t c) hD
    have hr : paperHurwitzFiniteFredholmLimit c = D := Complex.ofReal_injective h
    rw [← hr]
    exact paperHurwitzFiniteFredholmLimit_ge_one c
  · intro hD
    exact ⟨paperHurwitzTargetDensity ⟨D, hD⟩, paperHurwitz_target_zero_cost_realization t ⟨D, hD⟩⟩

theorem paperHurwitzFiniteFredholmValue_one_tendsto (t : ℝ) :
    Tendsto (paperHurwitzFiniteFredholmValue t 1) atTop (𝓝 (2 : ℂ)) := by
  simpa only [paperHurwitzFiniteFredholmLimit, one_pow, one_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), Complex.ofReal_ofNat] using
      paperHurwitzFiniteFredholmValue_tendsto t 1

end
end RHTower
