import GaloisForLFunctions.RHTower.LevinsonFiniteCoefficientEnergyLimit
import GaloisForLFunctions.RHTower.Sieve.DirichletMVTNegativeWindow
import GaloisForLFunctions.HTGeometry.FarBandPowerTail

/-!
# Mean square of the finite critical Levinson detector

At the integer-power schedule `L = N^(100 : ℕ)`, `M = N^(49 : ℕ)`, the product polynomial has length
`N^(149 : ℕ)`, strictly below the averaging height `N^(200 : ℕ)`.  The arbitrary-window Dirichlet mean-value
theorem therefore transfers the exact coefficient-energy limit to the normalized polynomial mean
square.  No infinite AFE or displacement estimate is used here.
-/

open Filter Topology MeasureTheory intervalIntegral Finset

namespace RHTower

noncomputable section

/-- Finite unsmoothed critical detector times the literal linear Levinson mollifier. -/
def levinsonFiniteCriticalMollifiedPolynomial (N : ℕ) (t : ℝ) : ℂ :=
  Sieve.dirPoly (N ^ 100 * N ^ 49)
    (levinsonCriticalDetectorMollifiedFinCoeff
      ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49)) (-t)

private theorem tendsto_levinsonFiniteMeanValueErrorScale_zero :
    Tendsto (fun N : ℕ =>
      8 * ((N ^ 100 * N ^ 49 : ℕ) : ℝ) *
          (1 + Real.log (N ^ 100 * N ^ 49 : ℕ)) /
      ((N ^ 200 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hbase := GaloisForLFunctions.tendsto_one_add_log_div_rpow_atTop_zero
    (t := (51 : ℝ)) (by norm_num)
  have hlogReal : Tendsto (fun x : ℝ => Real.log x / x ^ (51 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 51)).tendsto_div_nhds_zero
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ) ^ (51 : ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using hlogReal.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ (51 : ℝ)) atTop (𝓝 0) := by
    have hsub := hbase.sub hlog
    convert hsub using 1 <;> simp
    funext N
    ring
  have hscaled := (hone.const_mul 8).add (hlog.const_mul 1192)
  norm_num at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpow : N ^ 100 * N ^ 49 = N ^ 149 := by ring
  rw [hpow, Nat.cast_pow, Real.log_pow]
  push_cast
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  field_simp [hNne]
  ring

/-- The normalized mean square of the full finite critical detector convolution has the exact
limit `19751/14700` at the `49/100` schedule. -/
theorem tendsto_levinsonFiniteCriticalMollifiedPolynomial_meanSquare :
    Tendsto (fun N : ℕ =>
      (∫ t in (0 : ℝ)..(N ^ 200 : ℕ),
          ‖levinsonFiniteCriticalMollifiedPolynomial N t‖ ^ 2) /
        (N ^ 200 : ℕ)) atTop (𝓝 (19751 / 14700 : ℝ)) := by
  let E : ℕ → ℝ := fun N =>
    ∑ r : Fin (N ^ 100 * N ^ 49),
      levinsonCriticalDetectorFiniteEnergyTerm
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) r
  let A : ℕ → ℝ := fun N =>
    8 * ((N ^ 100 * N ^ 49 : ℕ) : ℝ) *
        (1 + Real.log (N ^ 100 * N ^ 49 : ℕ)) /
      ((N ^ 200 : ℕ) : ℝ)
  let I : ℕ → ℝ := fun N =>
    (∫ t in (0 : ℝ)..(N ^ 200 : ℕ),
        ‖levinsonFiniteCriticalMollifiedPolynomial N t‖ ^ 2) /
      (N ^ 200 : ℕ)
  have hE : Tendsto E atTop (𝓝 (19751 / 14700 : ℝ)) :=
    tendsto_levinsonCriticalDetectorFiniteEnergy_fortyNine_reciprocal
  have hA : Tendsto A atTop (𝓝 0) :=
    tendsto_levinsonFiniteMeanValueErrorScale_zero
  have hAE : Tendsto (fun N => A N * E N) atTop (𝓝 0) := by
    convert hA.mul hE using 1
    all_goals simp
  have hdiff : Tendsto (fun N => I N - E N) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hAEabs : Tendsto (fun N => |A N * E N|) atTop (𝓝 0) := by
      simpa using hAE.abs
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.1 hAEabs) ε hε
    refine ⟨max N₀ 2, ?_⟩
    intro N hN
    have hN0 : N₀ ≤ N := (Nat.le_max_left N₀ 2).trans hN
    have hN2 : 2 ≤ N := (Nat.le_max_right N₀ 2).trans hN
    have hTpos : (0 : ℝ) < (N ^ 200 : ℕ) := by positivity
    have hmean := Sieve.dirichlet_meanValue_window_neg
      (N ^ 100 * N ^ 49)
      (levinsonCriticalDetectorMollifiedFinCoeff
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49))
      0 (N ^ 200 : ℕ)
    have hsum :
        (∑ r : Fin (N ^ 100 * N ^ 49),
          ‖levinsonCriticalDetectorMollifiedFinCoeff
            ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) r‖ ^ 2) =
          E N := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (Complex.normSq_eq_norm_sq _).symm
    rw [hsum] at hmean
    have hEnonneg : 0 ≤ E N := by
      dsimp only [E]
      exact Finset.sum_nonneg fun r hr =>
        Complex.normSq_nonneg
          (levinsonCriticalDetectorMollifiedFinCoeff
            ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ 100) (N ^ 49) r)
    have hmean' :
        |(∫ t in (0 : ℝ)..(N ^ 200 : ℕ),
              ‖levinsonFiniteCriticalMollifiedPolynomial N t‖ ^ 2) -
            ((N ^ 200 : ℕ) : ℝ) * E N| ≤
          8 * ((N ^ 100 * N ^ 49 : ℕ) : ℝ) *
            (1 + Real.log (N ^ 100 * N ^ 49 : ℕ)) * E N := by
      simpa only [levinsonFiniteCriticalMollifiedPolynomial, sub_zero] using hmean
    have hbound : |I N - E N| ≤ |A N * E N| := by
      have hdiv :
          |I N - E N| =
            |(∫ t in (0 : ℝ)..(N ^ 200 : ℕ),
                ‖levinsonFiniteCriticalMollifiedPolynomial N t‖ ^ 2) -
                ((N ^ 200 : ℕ) : ℝ) * E N| /
              ((N ^ 200 : ℕ) : ℝ) := by
        dsimp only [I]
        have halg :
            (∫ t in (0 : ℝ)..(N ^ 200 : ℕ),
                ‖levinsonFiniteCriticalMollifiedPolynomial N t‖ ^ 2) /
                  ((N ^ 200 : ℕ) : ℝ) - E N =
              ((∫ t in (0 : ℝ)..(N ^ 200 : ℕ),
                  ‖levinsonFiniteCriticalMollifiedPolynomial N t‖ ^ 2) -
                ((N ^ 200 : ℕ) : ℝ) * E N) /
                  ((N ^ 200 : ℕ) : ℝ) := by
          field_simp
        rw [halg, abs_div, abs_of_pos hTpos]
      rw [hdiv]
      refine (div_le_div_of_nonneg_right hmean' hTpos.le).trans_eq ?_
      dsimp only [A]
      rw [abs_mul]
      have hAnonneg : 0 ≤ 8 * ((N ^ 100 * N ^ 49 : ℕ) : ℝ) *
          (1 + Real.log (N ^ 100 * N ^ 49 : ℕ)) /
            ((N ^ 200 : ℕ) : ℝ) := by
        positivity
      rw [abs_of_nonneg hAnonneg]
      rw [abs_of_nonneg hEnonneg]
      ring
    have hsmall : |A N * E N| < ε := by
      simpa [Real.dist_eq] using hN₀ N hN0
    simpa [Real.dist_eq] using lt_of_le_of_lt hbound hsmall
  have hI := hdiff.add hE
  have hI' : Tendsto I atTop (𝓝 (19751 / 14700 : ℝ)) := by
    convert hI using 1 <;> simp [I, E]
  exact hI'

end

end RHTower
