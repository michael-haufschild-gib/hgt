import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.CommonOccupation
import GaloisForLFunctions.HTGeometry.ScheffeCounting

/-! # Total variation stability of the common divisor at critical damping -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology

theorem commonScaleReal_hasSum {x : ℝ} (hx : 1/4 < x) :
    HasSum (fun k => (commonScaleWeight x k).re) 1 :=
  Complex.reCLM.hasSum (commonScaleWeight_hasSum hx)

/-- Critical damping preserves the entire common-divisor law in total variation. -/
theorem common_scale_total_variation :
    Tendsto (fun x : ℝ => ∑' k, |(commonScaleWeight x k).re - (commonScaleWeight (1/2) k).re|)
      (𝓝 (1/2)) (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  let y := fun n => max (3/8:ℝ) (u n)
  have hy (n : ℕ) : 1/4 < y n := lt_of_lt_of_le (by norm_num : (1/4:ℝ) < 3/8) (le_max_left _ _)
  have he : y =ᶠ[atTop] u := by
    filter_upwards [hu.eventually (lt_mem_nhds (by norm_num : (3/8:ℝ) < 1/2))] with n hn
    exact max_eq_right hn.le
  have hyt := hu.congr' he.symm
  have hpos (n : ℕ) (k : ℕ+) : 0 ≤ (commonScaleWeight (y n) k).re := by
    obtain ⟨r,hr,heq⟩ := commonScaleWeight_positive (hy n) k
    rw [← heq,Complex.ofReal_re]
    exact hr.le
  have hpt (k : ℕ+) : Tendsto (fun n => (commonScaleWeight (y n) k).re) atTop (𝓝 (commonScaleWeight (1/2) k).re) := by
    have h := commonScaleWeight_tendsto_critical k
    rw [← commonScaleWeight_critical k] at h
    exact (Complex.continuous_re.tendsto _).comp (h.comp hyt)
  have hl := HTGeometry.tendsto_tsum_abs_sub_of_tendsto hpos (fun n => commonScaleReal_hasSum (hy n))
    (commonScaleReal_hasSum (by norm_num : (1/4:ℝ) < 1/2)) hpt
  apply hl.congr'
  filter_upwards [he] with n hn
  simp only [hn,Function.comp_apply]

#print axioms commonScaleReal_hasSum
#print axioms common_scale_total_variation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
