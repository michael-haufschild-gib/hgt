import GaloisForLFunctions.InfiniteRankWeilTheory.OscillatorySublevelMeasure
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin

/-!+# Finite measure of exponentially small oscillatory values

A uniform local power-law sublevel bound makes exponentially small values occupy finite total
measure on the positive half-line. For a nonzero finite sum of distinct real frequencies, the
finite-jet estimate supplies this bound with no Diophantine assumption on the frequencies.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- A uniform local sublevel estimate turns exponential thresholds into a summable measure
bound over fixed-length cells. -/
theorem volume_exp_small_lt_top_of_uniform_sublevels {f : ℝ → ℂ} {r K p : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hp : 0 < p)
    (hsub : ∀ x ε : ℝ, 0 < ε →
      volume {t ∈ Ioo (x - r) (x + r) | ‖f t‖ < ε} ≤ ENNReal.ofReal (K * ε ^ p))
    {δ : ℝ} (hδ : 0 < δ) :
    volume {t : ℝ | 0 ≤ t ∧ ‖f t‖ ≤ Real.exp (-δ * t)} < ⊤ := by
  let S : ℕ → Set ℝ := fun n =>
    {t ∈ Ioo (((n : ℝ) + 1 / 2) * r - r) (((n : ℝ) + 1 / 2) * r + r) |
      ‖f t‖ < 2 * Real.exp (-δ * ((n : ℝ) * r))}
  have hcover : {t : ℝ | 0 ≤ t ∧ ‖f t‖ ≤ Real.exp (-δ * t)} ⊆ ⋃ n, S n := by
    intro t ht
    let n : ℕ := ⌊t / r⌋₊
    have hleft : (n : ℝ) * r ≤ t :=
      (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg ht.1 hr.le))
    have hright : t < ((n : ℝ) + 1) * r :=
      (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (t / r))
    refine mem_iUnion.mpr ⟨n, ⟨?_, ?_⟩, ?_⟩
    · nlinarith only [hleft, hr]
    · nlinarith only [hright, hr]
    · have he : Real.exp (-δ * t) ≤ Real.exp (-δ * ((n : ℝ) * r)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hleft (neg_nonpos.mpr hδ.le))
      exact ht.2.trans_lt (he.trans_lt (by linarith [Real.exp_pos (-δ * ((n : ℝ) * r))]))
  let u : ℕ → ℝ := fun n => K * (2 * Real.exp (-δ * ((n : ℝ) * r))) ^ p
  have hu (n : ℕ) : 0 ≤ u n := by dsimp [u]; positivity
  have hsum : Summable u := by
    have he := (HTGeometry.summable_exp_neg_nat_mul (mul_pos (mul_pos hδ hr) hp)).mul_left
      (K * (2 : ℝ) ^ p)
    refine he.congr fun n => ?_
    dsimp [u]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le, ← Real.exp_mul,
      show (-δ * ((n : ℝ) * r)) * p = -((n : ℝ) * (δ * r * p)) by ring]
    ring
  have hfinite : ∑' n, ENNReal.ofReal (u n) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hu hsum]
    exact ENNReal.ofReal_lt_top
  refine lt_of_le_of_lt ((measure_mono hcover).trans (measure_iUnion_le S)) ?_
  exact lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => hsub _ _ (by positivity)) hfinite

/-- A nonzero finite oscillatory sum is exponentially small on a set of finite measure. -/
theorem volume_oscillatory_exp_small_lt_top {k : ℕ} (γ : Fin k → ℝ)
    (hγ : Function.Injective γ) (c : Fin k → ℂ) (hc : c ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    volume {t : ℝ | 0 ≤ t ∧ ‖oscillatoryJet γ c 0 t‖ ≤ Real.exp (-δ * t)} < ⊤ := by
  obtain ⟨r, K, hr, hK, hsub⟩ := exists_uniform_oscillatory_sublevel_bound γ hγ c hc
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    exact hc (funext fun i => Fin.elim0 i)
  exact volume_exp_small_lt_top_of_uniform_sublevels hr hK
    (inv_pos.mpr (by exact_mod_cast hk)) hsub hδ

#print axioms volume_oscillatory_exp_small_lt_top

end GaloisForLFunctions.InfiniteRankWeilTheory
