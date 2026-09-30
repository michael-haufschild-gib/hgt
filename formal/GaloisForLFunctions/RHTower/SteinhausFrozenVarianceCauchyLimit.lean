import GaloisForLFunctions.RHTower.SteinhausSmoothRoughPairSeries
import GaloisForLFunctions.RHTower.SteinhausSmoothPairError
import GaloisForLFunctions.RHTower.SteinhausEulerCauchySeries

open MeasureTheory Filter Complex
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- The original summatory polynomial's frozen-prefix variance, divided by its arithmetic cutoff. -/
def steinhausNormalizedFrozenSummatoryVariance (y N : ℕ) (ω : Omega) : ℝ :=
  (∫ η, ‖∑ n ∈ Finset.Icc 1 N,
    X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ) ∂steinhausMeasure) / N

theorem steinhausNormalizedFrozenSummatoryVariance_nonneg (y N : ℕ) (ω : Omega) :
    0 ≤ steinhausNormalizedFrozenSummatoryVariance y N ω :=
  div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (Nat.cast_nonneg _)

/-- The literal Cauchy mass is finite for every finite prefix and every phase sample. -/
theorem steinhausEulerCauchyMass_ne_top (y : ℕ) (ω : Omega) :
    steinhausEulerCauchyMass y ω ≠ ⊤ := by
  rw [steinhausEulerCauchyMass_eq_smoothPair]
  exact ENNReal.ofReal_ne_top

/-- Real-valued form of the original Cauchy mass, with nonnegativity justified by its integral. -/
theorem steinhausEulerCauchyMass_toReal_eq_smoothPair (y : ℕ) (ω : Omega) :
    (steinhausEulerCauchyMass y ω).toReal =
      (steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹ *
        (∑' ac : Nat.smoothNumbers y × Nat.smoothNumbers y,
          X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω) /
            (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)).re := by
  have hM := steinhausEulerPartition_pos (Nat.primesBelow y)
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) (by norm_num : (0 : ℝ) < 1 / 2)
  have hsum : 0 ≤ (∑' ac : Nat.smoothNumbers y × Nat.smoothNumbers y,
      X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω) /
        (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)).re := by
    rw [← integral_steinhausEulerCauchy_normSq_eq_smoothPair, Complex.ofReal_re]
    exact integral_nonneg (fun _ => sq_nonneg _)
  rw [steinhausEulerCauchyMass_eq_smoothPair]
  exact ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hM.le) hsum)

/-- A deterministic summable coefficient error controls the literal variance for every prefix sample. -/
theorem abs_steinhausNormalizedFrozenSummatoryVariance_sub_cauchyMass_le
    (y N : ℕ) (ω : Omega) :
    |steinhausNormalizedFrozenSummatoryVariance y N ω -
      (steinhausEulerCauchyMass y ω).toReal| ≤ steinhausSmoothPairCountError y N := by
  let α : ℝ := (steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹
  let f (ac : Nat.smoothNumbers y × Nat.smoothNumbers y) : ℂ :=
    (((roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℝ) /
      N : ℝ) : ℂ) * (X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω))
  let g (ac : Nat.smoothNumbers y × Nat.smoothNumbers y) : ℂ :=
    (α : ℂ) * (X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω) /
      (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ))
  let e (ac : Nat.smoothNumbers y × Nat.smoothNumbers y) : ℝ :=
    |(roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℝ) /
      N - α / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)|
  have hf : HasSum f (steinhausNormalizedFrozenSummatoryVariance y N ω : ℂ) :=
    hasSum_steinhausSummatory_frozenPrefix_normalizedPairCount y N ω
  have he : Summable e := summable_steinhausSmoothPair_countError y N
  have hnorm (ac : Nat.smoothNumbers y × Nat.smoothNumbers y) : ‖f ac - g ac‖ ≤ e ac := by
    have hpoint : f ac - g ac =
        (((roughCount (Nat.primesBelow y) ((N : ℝ) / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) : ℝ) /
          N - α / (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ) : ℝ) : ℂ) *
          (X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω)) := by
      dsimp [f, g]
      simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast]
      ring
    rw [hpoint]
    simp only [norm_mul, norm_X, Complex.norm_conj, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_rfl
  have hg : Summable g := by
    have hpoint : (fun ac => f ac - (f ac - g ac)) = g := by
      funext ac
      ring
    rw [← hpoint]
    exact hf.summable.sub (he.of_norm_bounded hnorm)
  have hb := tsum_of_norm_bounded he.hasSum hnorm
  rw [hf.summable.tsum_sub hg, hf.tsum_eq] at hb
  have hgsum : (∑' ac, g ac) = (α : ℂ) *
      (∑' ac : Nat.smoothNumbers y × Nat.smoothNumbers y,
        X ac.1 ω * (starRingEnd ℂ) (X ac.2 ω) /
          (max (ac.1 : ℕ) (ac.2 : ℕ) : ℕ)) := tsum_mul_left
  rw [hgsum] at hb
  have hr := (Complex.abs_re_le_norm _).trans hb
  rw [steinhausEulerCauchyMass_toReal_eq_smoothPair]
  simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, α, e, steinhausSmoothPairCountError] using hr

/-- At each fixed prime prefix the literal normalized variance tends to the actual Cauchy Euler mass. -/
theorem tendsto_steinhausNormalizedFrozenSummatoryVariance (y : ℕ) (ω : Omega) :
    Tendsto (fun N => steinhausNormalizedFrozenSummatoryVariance y N ω) atTop
      (𝓝 (steinhausEulerCauchyMass y ω).toReal) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_steinhausSmoothPairCountError y).eventually (gt_mem_nhds hε))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact (abs_steinhausNormalizedFrozenSummatoryVariance_sub_cauchyMass_le y n ω).trans_lt
    (hN n hn)

end RHTower
