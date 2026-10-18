import GaloisForLFunctions.HTGeometry.BohrBochnerEquivalence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Positive lower density of returns of a continuous almost-periodic function

Relative density supplies one almost-period in every interval of fixed length.
Uniform continuity thickens each such return into an interval of fixed positive
length. Disjoint time blocks then give a linear lower bound for return measure.
-/

open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions

open HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- Returns to the initial value of a continuous Bohr almost-periodic function
have positive lower Lebesgue density. -/
theorem exists_pos_return_density_of_isBohrAlmostPeriodic {f : ℝ → E}
    (hf : Continuous f) (hap : IsBohrAlmostPeriodic f) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (κ * T) ≤
        volume ({t : ℝ | ‖f t - f 0‖ < ε} ∩ Icc 0 T) := by
  classical
  obtain ⟨L, hL, hperiod⟩ := hap (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
    (uniformContinuous_of_isBohrAlmostPeriodic hf hap) (ε / 3) (by positivity)
  let W : ℝ := L + 2 * δ
  have hW : 0 < W := by dsimp [W]; positivity
  choose τ hτ hτperiod using fun k : ℕ => hperiod ((k : ℝ) * W + δ)
  let J : ℕ → Set ℝ := fun k => Ioo (τ k - δ) (τ k + δ)
  have hblock (k : ℕ) : J k ⊆ Ioo ((k : ℝ) * W) (((k : ℝ) + 1) * W) := by
    intro t ht
    have hl := (hτ k).1
    have hu := (hτ k).2
    change τ k - δ < t ∧ t < τ k + δ at ht
    change (k : ℝ) * W < t ∧ t < ((k : ℝ) + 1) * W
    constructor <;> dsimp [W] at * <;> nlinarith [ht.1, ht.2]
  have hgood (k : ℕ) : J k ⊆ {t : ℝ | ‖f t - f 0‖ < ε} := by
    intro t ht
    have hdist : dist t (τ k) < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 := hclose hdist
    have h2 := hτperiod k 0
    simp only [zero_add] at h2
    rw [dist_eq_norm] at h1
    calc
      ‖f t - f 0‖ = ‖(f t - f (τ k)) + (f (τ k) - f 0)‖ := by congr 1; abel
      _ ≤ ‖f t - f (τ k)‖ + ‖f (τ k) - f 0‖ := norm_add_le _ _
      _ < ε := by linarith
  refine ⟨δ / W, div_pos hδ hW, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * W)] with T hT
  have hT0 : 0 ≤ T := by linarith
  let q : ℕ := ⌊T / W⌋₊
  have hqT : (q : ℝ) * W ≤ T :=
    (le_div_iff₀ hW).mp (Nat.floor_le (div_nonneg hT0 hW.le))
  have hTq : T ≤ 2 * (q : ℝ) * W := by
    have hfloor : T < ((q : ℝ) + 1) * W :=
      (div_lt_iff₀ hW).mp (Nat.lt_floor_add_one (T / W))
    nlinarith
  have hd : Set.PairwiseDisjoint (↑(Finset.range q)) J := by
    intro i _hi j _hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hbi := hblock i hti
    have hbj := hblock j htj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hstep : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hij)
      have hsep := mul_le_mul_of_nonneg_right hstep hW.le
      linarith [hbi.2, hbj.1]
    · have hstep : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt hji)
      have hsep := mul_le_mul_of_nonneg_right hstep hW.le
      linarith [hbj.2, hbi.1]
  have hcover : (⋃ k ∈ Finset.range q, J k) ⊆
      {t : ℝ | ‖f t - f 0‖ < ε} ∩ Icc 0 T := by
    intro t ht
    obtain ⟨k, hk, ht⟩ := mem_iUnion₂.mp ht
    have hbk := hblock k ht
    have hkq : (k : ℝ) + 1 ≤ q := by
      exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    have hupper := mul_le_mul_of_nonneg_right hkq hW.le
    exact ⟨hgood k ht, ⟨(mul_nonneg (Nat.cast_nonneg k) hW.le).trans hbk.1.le,
      hbk.2.le.trans (hupper.trans hqT)⟩⟩
  have hmass : volume (⋃ k ∈ Finset.range q, J k) =
      ENNReal.ofReal ((q : ℝ) * (2 * δ)) := by
    rw [measure_biUnion_finset hd (fun _ _ => measurableSet_Ioo)]
    have hJ (k : ℕ) : volume (J k) = ENNReal.ofReal (2 * δ) := by
      change volume (Ioo (τ k - δ) (τ k + δ)) = _
      rw [Real.volume_Ioo]
      congr 1
      ring
    simp_rw [hJ]
    simp [ENNReal.ofReal_mul (Nat.cast_nonneg q)]
  calc
    ENNReal.ofReal (δ / W * T) ≤ ENNReal.ofReal ((q : ℝ) * (2 * δ)) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_mul_eq_mul_div, div_le_iff₀ hW]
      nlinarith [mul_le_mul_of_nonneg_left hTq hδ.le]
    _ = volume (⋃ k ∈ Finset.range q, J k) := hmass.symm
    _ ≤ _ := measure_mono hcover

end GaloisForLFunctions
