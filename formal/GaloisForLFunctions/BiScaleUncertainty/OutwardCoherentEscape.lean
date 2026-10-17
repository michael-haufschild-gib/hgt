import GaloisForLFunctions.BiScaleUncertainty.PlasticCoherentLineMinimizer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Actual outward sources with exactly fixed coherent data

Translate the annular representative's sinh multiplier through integer cells,
invert away from zero, and take the odd part. The full fold stays exact while
the original source energy obeys an explicit inverse-square bound.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported Topology

namespace GaloisForLFunctions.BiScaleUncertainty.OutwardCoherentEscape
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
open FoldedHyperbolicCellDefect AnnularCoherentRetraction PlasticCoherentLineMinimizer
noncomputable section

private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)
private abbrev shift (n : ℕ) : ℝ := ((n : ℝ) + 4) * d
private abbrev profile (f : C_c(ℝ, ℝ)) := sinhCompact (1 / 2) (representative f)

private theorem profile_support (f : C_c(ℝ, ℝ)) (n : ℕ) (u : ℝ)
    (hu : profile f (u - shift n) ≠ 0) :
    ((n : ℝ) + 1) * d < u ∧ u < ((n : ℝ) + 7) * d := by
  have hr : representative f (u - shift n) ≠ 0 := by
    intro hz
    exact hu (by change Real.sinh _ * representative f _ = 0; rw [hz, mul_zero])
  have hb := representative_support f hr
  change d < |u - shift n| ∧ |u - shift n| < 3 * d at hb
  have ha := abs_lt.mp hb.2
  dsimp [shift] at ha
  constructor <;> linarith only [ha.1, ha.2]

private theorem profile_zero_near (f : C_c(ℝ, ℝ)) (n : ℕ) (u : ℝ) (hu : u ≤ d) :
    profile f (u - shift n) = 0 := by
  by_contra hn
  have hb := (profile_support f n u hn).1
  have hd := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) d_pos.le
  nlinarith only [hu, hb, hd]

private theorem right_continuous (f : C_c(ℝ, ℝ)) (n : ℕ) :
    Continuous (fun u => profile f (u - shift n) / Real.sinh (u / 2)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u = 0
  · subst u
    have hz : (fun u => profile f (u - shift n) / Real.sinh (u / 2)) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds (by linarith [d_pos] : -d < (0 : ℝ)) d_pos] with v hv
      rw [profile_zero_near f n v hv.2.le, zero_div]
    exact hz.continuousAt
  · exact ((profile f).continuous.comp (continuous_id.sub continuous_const)).continuousAt.div
      (Real.continuous_sinh.comp (continuous_id.div_const 2)).continuousAt
      (Real.sinh_ne_zero.mpr (div_ne_zero hu (by norm_num)))

private def rightSource (f : C_c(ℝ, ℝ)) (n : ℕ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => profile f (u - shift n) / Real.sinh (u / 2), right_continuous f n⟩, by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Icc (((n : ℝ) + 1) * d) (((n : ℝ) + 7) * d)) isCompact_Icc
    intro u hu
    have hn : profile f (u - shift n) ≠ 0 := by
      intro hz
      exact hu (by simp only [hz, zero_div])
    exact ⟨(profile_support f n u hn).1.le, (profile_support f n u hn).2.le⟩⟩

private theorem right_support (f : C_c(ℝ, ℝ)) (n : ℕ) (u : ℝ)
    (hu : rightSource f n u ≠ 0) :
    ((n : ℝ) + 1) * d < u ∧ u < ((n : ℝ) + 7) * d := by
  apply profile_support f n u
  intro hz
  exact hu (by change profile f _ / _ = 0; rw [hz, zero_div])

private theorem right_sinh (f : C_c(ℝ, ℝ)) (n : ℕ) (u : ℝ) :
    sinhCompact (1 / 2) (rightSource f n) u = profile f (u - shift n) := by
  change Real.sinh ((1 / 2 : ℝ) * u) * (profile f (u - shift n) / Real.sinh (u / 2)) = _
  rw [show (1 / 2 : ℝ) * u = u / 2 by ring]
  by_cases hu : u = 0
  · subst u
    rw [profile_zero_near f n 0 d_pos.le]
    simp
  · field_simp [Real.sinh_ne_zero.mpr (div_ne_zero hu (by norm_num : (2 : ℝ) ≠ 0))]

private theorem right_fold (f : C_c(ℝ, ℝ)) (n : ℕ) :
    cellFold (rightSource f n) = cellFold (oddCompactSource f) := by
  rw [← cellFold_representative f]
  ext x
  rw [cellFold_apply, cellFold_apply]
  simp_rw [right_sinh]
  have he (k : ℤ) : d * (x + k) - shift n = d * (x + (k + -((n : ℤ) + 4))) := by
    dsimp [shift]
    push_cast
    ring
  simp_rw [he]
  have hh := (Equiv.addRight (-((n : ℤ) + 4))).tsum_eq (fun k : ℤ => profile f (d * (x + k)))
  change (∑' k : ℤ, profile f (d * (x + ((k + -((n : ℤ) + 4) : ℤ) : ℝ)))) = _ at hh
  push_cast at hh
  exact hh

private def reflected (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => f (-u), f.continuous.comp continuous_neg⟩,
    f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)⟩

private theorem fold_reflected (f : C_c(ℝ, ℝ)) (x : ℝ) :
    cellFold (reflected f) x = -cellFold f (-x) := by
  rw [cellFold_apply, cellFold_apply]
  have he (k : ℤ) : sinhCompact (1 / 2) (reflected f) (d * (x + k)) =
      -sinhCompact (1 / 2) f (d * (-x + (-k : ℤ))) := by
    change Real.sinh ((1 / 2 : ℝ) * (d * (x + k))) * f (-(d * (x + k))) =
      -(Real.sinh ((1 / 2 : ℝ) * (d * (-x + (-k : ℤ)))) * f (d * (-x + (-k : ℤ))))
    rw [show d * (-x + (-k : ℤ)) = -(d * (x + k)) by push_cast; ring,
      mul_neg, Real.sinh_neg]
    ring
  simp_rw [he]
  rw [tsum_neg]
  congr 1
  exact tsum_comp_neg (fun k : ℤ => sinhCompact (1 / 2) f (d * (-x + k)))

private theorem fold_zero : cellFold (0 : C_c(ℝ, ℝ)) = 0 := by
  ext x
  simp [cellFold_apply, sinhCompact, sinhMultiplier]

private theorem fold_smul (f : C_c(ℝ, ℝ)) (t : ℝ) : cellFold (t • f) = t • cellFold f := by
  simpa only [zero_add, fold_zero] using cellFold_add_smul (0 : C_c(ℝ, ℝ)) f t

private theorem fold_odd (f : C_c(ℝ, ℝ)) (x : ℝ) :
    cellFold (oddCompactSource f) x = (cellFold f x + cellFold f (-x)) / 2 := by
  have he : oddCompactSource f = (1 / 2 : ℝ) • (f + (-1 : ℝ) • reflected f) := by
    ext u
    change (f u - f (-u)) / 2 = (1 / 2 : ℝ) * (f u + -1 * f (-u))
    ring
  rw [he, fold_smul, cellFold_add_smul]
  simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul, fold_reflected]
  ring

/-- Explicit odd compact sources escaping outward while preserving their entire coherent fold. -/
def escapingSource (f : C_c(ℝ, ℝ)) (n : ℕ) : C_c(ℝ, ℝ) := oddCompactSource (rightSource f n)

theorem escapingSource_apply (f : C_c(ℝ, ℝ)) (n : ℕ) (u : ℝ) :
    escapingSource f n u =
      (sinhCompact (1 / 2) (representative f) (u - ((n : ℝ) + 4) * Real.log 2) /
        Real.sinh (u / 2) -
       sinhCompact (1 / 2) (representative f) (-u - ((n : ℝ) + 4) * Real.log 2) /
        Real.sinh (-u / 2)) / 2 := rfl

theorem escapingSource_odd (f : C_c(ℝ, ℝ)) (n : ℕ) (u : ℝ) :
    escapingSource f n (-u) = -escapingSource f n u := oddCompactSource_odd _ u

theorem oddCompactSource_escapingSource (f : C_c(ℝ, ℝ)) (n : ℕ) :
    oddCompactSource (escapingSource f n) = escapingSource f n := by
  ext u
  change (escapingSource f n u - escapingSource f n (-u)) / 2 = _
  rw [escapingSource_odd]
  ring

theorem escapingSource_support (f : C_c(ℝ, ℝ)) (n : ℕ) :
    Function.support (escapingSource f n : ℝ → ℝ) ⊆
      {u : ℝ | ((n : ℝ) + 1) * Real.log 2 < |u| ∧ |u| < ((n : ℝ) + 7) * Real.log 2} := by
  intro u hu
  have ha : 0 < ((n : ℝ) + 1) * d := mul_pos (by positivity) d_pos
  by_cases hr : rightSource f n u = 0
  · have hl : rightSource f n (-u) ≠ 0 := by
      intro hz
      exact hu (by change (rightSource f n u - rightSource f n (-u)) / 2 = 0; rw [hr, hz]; ring)
    have hb := right_support f n (-u) hl
    change _ < |u| ∧ |u| < _
    rw [abs_of_neg (by linarith only [ha, hb.1] : u < 0)]
    exact hb
  · have hb := right_support f n u hr
    change _ < |u| ∧ |u| < _
    rw [abs_of_pos (ha.trans hb.1)]
    exact hb

/-- The fold reconstruction error is identically zero on all of the real line. -/
theorem cellFold_escapingSource (f : C_c(ℝ, ℝ)) (n : ℕ) :
    cellFold (escapingSource f n) = cellFold (oddCompactSource f) := by
  ext x
  rw [escapingSource, fold_odd, right_fold, cellFold_oddSource_even]
  ring

theorem moment_escapingSource (f : C_c(ℝ, ℝ)) (n : ℕ) :
    (∫ u, escapingSource f n u * Real.sinh (u / 2)) =
      ∫ u, oddCompactSource f u * Real.sinh (u / 2) := by
  have he : cellMean (escapingSource f n) = cellMean (oddCompactSource f) := by
    rw [← integral_cellFold, ← integral_cellFold, cellFold_escapingSource]
  unfold cellMean at he
  field_simp [d_pos.ne'] at he
  exact he

theorem exactBudget_escapingSource (f : C_c(ℝ, ℝ)) (n : ℕ) :
    localBudget (escapingSource f n) - schurResidualGain (escapingSource f n) =
      localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f) := by
  have he := integral_cellFold_sq (escapingSource f n)
  rw [oddCompactSource_escapingSource, cellFold_escapingSource] at he
  have hh := he.symm.trans (integral_cellFold_sq f)
  field_simp [d_pos.ne'] at hh
  exact hh

/-- Source-defined coefficient for the unconditional energy decay estimate. -/
def escapeEnergy (f : C_c(ℝ, ℝ)) : ℝ := autocorr (sinhCompact (1 / 2) (representative f)) 0

theorem escapeEnergy_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ escapeEnergy f := autocorr_zero_nonneg _

private theorem right_sq_bound (f : C_c(ℝ, ℝ)) (n : ℕ) (u : ℝ) :
    rightSource f n u ^ 2 ≤ (4 / (((n : ℝ) + 1) * d) ^ 2) * profile f (u - shift n) ^ 2 := by
  change (profile f (u - shift n) / Real.sinh (u / 2)) ^ 2 ≤ _
  by_cases hu : profile f (u - shift n) = 0
  · simp only [hu, zero_div, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  have ha : 0 < ((n : ℝ) + 1) * d := mul_pos (by positivity) d_pos
  have hb := (profile_support f n u hu).1
  have hs : u / 2 ≤ Real.sinh (u / 2) := Real.self_le_sinh_iff.mpr (by linarith only [ha, hb])
  have hp : 0 < Real.sinh (u / 2) := by linarith only [ha, hb, hs]
  have hs2 : (((n : ℝ) + 1) * d) ^ 2 ≤ 4 * Real.sinh (u / 2) ^ 2 := by
    nlinarith only [ha, hb, hs, sq_nonneg (2 * Real.sinh (u / 2) - ((n : ℝ) + 1) * d)]
  rw [div_pow, show 4 / (((n : ℝ) + 1) * d) ^ 2 * profile f (u - shift n) ^ 2 =
    (4 * profile f (u - shift n) ^ 2) / (((n : ℝ) + 1) * d) ^ 2 by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos ha)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hs2 (sq_nonneg (profile f (u - shift n)))]

private theorem right_energy_bound (f : C_c(ℝ, ℝ)) (n : ℕ) :
    autocorr (rightSource f n) 0 ≤ 4 * escapeEnergy f / (((n : ℝ) + 1) * d) ^ 2 := by
  have hi := integrable_sq (rightSource f n).continuous (rightSource f n).hasCompactSupport
  have hs : Integrable (fun u : ℝ => profile f (u - shift n) ^ 2) :=
    (integrable_sq (profile f).continuous (profile f).hasCompactSupport).comp_sub_right (shift n)
  have hb := integral_mono hi (hs.const_mul (4 / (((n : ℝ) + 1) * d) ^ 2)) (right_sq_bound f n)
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun u : ℝ => profile f u ^ 2) (shift n) (μ := volume)] at hb
  rw [integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero] at hb
  change autocorr (rightSource f n) 0 ≤ 4 * autocorr (profile f) 0 / _
  calc
    autocorr (rightSource f n) 0 ≤ 4 / (((n : ℝ) + 1) * d) ^ 2 * autocorr (profile f) 0 := hb
    _ = 4 * autocorr (profile f) 0 / (((n : ℝ) + 1) * d) ^ 2 := by ring

private theorem odd_energy_half (f : C_c(ℝ, ℝ)) (n : ℕ) :
    autocorr (escapingSource f n) 0 = autocorr (rightSource f n) 0 / 2 := by
  have hd (u : ℝ) : rightSource f n u * rightSource f n (-u) = 0 := by
    by_cases hu : rightSource f n u = 0
    · rw [hu, zero_mul]
    by_cases hv : rightSource f n (-u) = 0
    · rw [hv, mul_zero]
    have ha : 0 < ((n : ℝ) + 1) * d := mul_pos (by positivity) d_pos
    have hp := (right_support f n u hu).1
    have hm := (right_support f n (-u) hv).1
    linarith only [ha, hp, hm]
  have he (u : ℝ) : escapingSource f n u ^ 2 =
      (1 / 4 : ℝ) * (rightSource f n u ^ 2 + rightSource f n (-u) ^ 2) := by
    change ((rightSource f n u - rightSource f n (-u)) / 2) ^ 2 = _
    nlinarith only [hd u]
  have hi : Integrable (fun u : ℝ => rightSource f n u ^ 2) :=
    integrable_sq (rightSource f n).continuous (rightSource f n).hasCompactSupport
  have hj : Integrable (fun u : ℝ => rightSource f n (-u) ^ 2) :=
    integrable_sq (reflected (rightSource f n)).continuous (reflected (rightSource f n)).hasCompactSupport
  have hh : (∫ u, escapingSource f n u ^ 2) = (∫ u, rightSource f n u ^ 2) / 2 := by
    simp_rw [he]
    rw [integral_const_mul, integral_add hi hj,
      integral_neg_eq_self (fun u : ℝ => rightSource f n u ^ 2) volume]
    ring
  simpa only [integral_sq_eq_autocorr_zero] using hh

/-- Explicit inverse-square decay of the original energy, with the complete fold held fixed. -/
theorem escapingSource_energy_bound (f : C_c(ℝ, ℝ)) (n : ℕ) :
    autocorr (escapingSource f n) 0 ≤
      2 * escapeEnergy f / (((n : ℝ) + 1) * Real.log 2) ^ 2 := by
  rw [odd_energy_half]
  calc
    autocorr (rightSource f n) 0 / 2 ≤
        (4 * escapeEnergy f / (((n : ℝ) + 1) * Real.log 2) ^ 2) / 2 := by
      gcongr
      exact right_energy_bound f n
    _ = 2 * escapeEnergy f / (((n : ℝ) + 1) * Real.log 2) ^ 2 := by ring

end
end GaloisForLFunctions.BiScaleUncertainty.OutwardCoherentEscape
