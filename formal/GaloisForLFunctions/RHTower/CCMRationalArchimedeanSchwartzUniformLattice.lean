import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzLattice

/-!
# Uniform summable envelopes for archimedean Schwartz lattices

A single Schwartz function, restricted to any real lattice whose spacing is bounded away from
zero, admits one common summable pointwise majorant.  This is the local-uniform strengthening of
fixed-lattice summability required for trace-norm continuity over the positive-real idele-class
coordinate.
-/

noncomputable section

open scoped SchwartzMap

namespace GaloisForLFunctions
namespace RHTower

/-- **Uniform Schwartz lattice envelope.**  All lattice restrictions with spacing at least `a₀`
in absolute value are dominated by one summable sequence. -/
theorem ccmRationalArchimedeanSchwartz_exists_uniformLatticeMajorant
    (f : CCMRationalArchimedeanSchwartz) {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ u : ℤ → ℝ, Summable u ∧
      ∀ (a : ℝ), a₀ ≤ |a| → ∀ n : ℤ,
        ‖f (a * (n : ℝ))‖ ≤ u n := by
  let S : ℝ := SchwartzMap.seminorm ℂ 2 0 f
  let C : ℝ := S / a₀ ^ (2 : ℕ)
  let u : ℤ → ℝ := fun n =>
    if n = 0 then ‖f 0‖ else C * (1 / (n : ℝ) ^ (2 : ℕ))
  have hbase : Summable (fun n : ℤ => C * (1 / (n : ℝ) ^ (2 : ℕ))) :=
    ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)).mul_left C
  have hu : Summable u := by
    apply hbase.congr_cofinite
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
    simp [u, hn]
  refine ⟨u, hu, fun a ha n => ?_⟩
  by_cases hn : n = 0
  · subst n
    simp [u]
  · rw [show u n = C * (1 / (n : ℝ) ^ (2 : ℕ)) by simp [u, hn]]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hnabs : 0 < |(n : ℝ)| := abs_pos.mpr hnR
    have haabs : 0 < |a| := ha₀.trans_le ha
    have han : a * (n : ℝ) ≠ 0 :=
      mul_ne_zero (abs_ne_zero.mp haabs.ne') hnR
    have hx : 0 < ‖a * (n : ℝ)‖ ^ (2 : ℕ) :=
      pow_pos (norm_pos_iff.mpr han) _
    have hminor :
        (a₀ * |(n : ℝ)|) ^ (2 : ℕ) ≤
          ‖a * (n : ℝ)‖ ^ (2 : ℕ) := by
      rw [Real.norm_eq_abs, abs_mul]
      have hmul : a₀ * |(n : ℝ)| ≤ |a| * |(n : ℝ)| :=
        mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      nlinarith [mul_nonneg ha₀.le (abs_nonneg (n : ℝ))]
    have hminorPos : 0 < (a₀ * |(n : ℝ)|) ^ (2 : ℕ) :=
      pow_pos (mul_pos ha₀ hnabs) _
    have hsem := SchwartzMap.norm_pow_mul_le_seminorm
      ℂ f 2 (a * (n : ℝ))
    calc
      ‖f (a * (n : ℝ))‖ ≤
          S / ‖a * (n : ℝ)‖ ^ (2 : ℕ) := by
        apply (le_div_iff₀ hx).2
        simpa [S, mul_comm] using hsem
      _ ≤ S / (a₀ * |(n : ℝ)|) ^ (2 : ℕ) :=
        div_le_div_of_nonneg_left (by positivity) hminorPos hminor
      _ = C * (1 / (n : ℝ) ^ (2 : ℕ)) := by
        dsimp [C]
        have ha₀ne : a₀ ≠ 0 := ha₀.ne'
        field_simp
        rw [sq_abs]

end RHTower
end GaloisForLFunctions
