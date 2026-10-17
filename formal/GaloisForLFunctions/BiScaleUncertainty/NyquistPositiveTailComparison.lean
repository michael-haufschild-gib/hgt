import GaloisForLFunctions.BiScaleUncertainty.NyquistPowerTails

/-! # Transfer of a pointwise ratio limit to positive summable tails -/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem tendsto_nyquist_positive_tail_ratio {a b : ℕ → ℝ} (ha : Summable a)
    (hb : Summable b) (hbpos : ∀ n, 0 < b n) {c : ℝ}
    (hlim : Tendsto (fun n => a n / b n) atTop (𝓝 c)) :
    Tendsto (fun N => (∑' k : ℕ, a (N + k)) / (∑' k : ℕ, b (N + k)))
      atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := hlim (ε / 2) (by linarith)
  refine ⟨M, ?_⟩
  intro N hN
  have haN : Summable (fun k : ℕ => a (N + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).mpr ha
  have hbN : Summable (fun k : ℕ => b (N + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).mpr hb
  have hS : 0 < ∑' k : ℕ, b (N + k) :=
    hbN.tsum_pos (fun k => (hbpos (N + k)).le) 0 (hbpos (N + 0))
  have hlo (k : ℕ) : (c - ε / 2) * b (N + k) ≤ a (N + k) := by
    have hd := hM (N + k) (by omega)
    rw [Real.dist_eq] at hd
    apply (le_div_iff₀ (hbpos (N + k))).mp
    linarith [(abs_lt.mp hd).1]
  have hhi (k : ℕ) : a (N + k) ≤ (c + ε / 2) * b (N + k) := by
    have hd := hM (N + k) (by omega)
    rw [Real.dist_eq] at hd
    apply (div_le_iff₀ (hbpos (N + k))).mp
    linarith [(abs_lt.mp hd).2]
  have hsumlo := Summable.tsum_le_tsum hlo (hbN.mul_left (c - ε / 2)) haN
  have hsumhi := Summable.tsum_le_tsum hhi haN (hbN.mul_left (c + ε / 2))
  rw [Summable.tsum_mul_left (c - ε / 2) hbN] at hsumlo
  rw [Summable.tsum_mul_left (c + ε / 2) hbN] at hsumhi
  have hl := (le_div_iff₀ hS).mpr hsumlo
  have hu := (div_le_iff₀ hS).mpr hsumhi
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

end
end GaloisForLFunctions.BiScaleUncertainty
