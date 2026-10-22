import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzReal
import Mathlib.Analysis.PSeries

/-!
# Absolute summability of rational archimedean Schwartz lattice restrictions

Every complex-valued Schwartz function on `ℝ`, restricted to a nonzero real multiple of `ℤ`,
is absolutely summable. This is the archimedean estimate needed to show that rational CCM orbit
coefficients are in `ℓ¹` after finite-adele compact support confines their denominators.

No finite-adele denominator confinement, strong-Schwartz base-parameter estimate, positivity,
zero spectrum, numerical computation, or Riemann-hypothesis premise occurs.
-/

noncomputable section

open scoped SchwartzMap

namespace GaloisForLFunctions
namespace RHTower

/--
The restriction of an archimedean Schwartz function to any nonzero real lattice is absolutely
summable.
-/
theorem ccmRationalArchimedeanSchwartz_lattice_summable
    (f : CCMRationalArchimedeanSchwartz) {a : ℝ} (ha : a ≠ 0) :
    Summable (fun n : ℤ => ‖f (a * (n : ℝ))‖) := by
  let S : ℝ := SchwartzMap.seminorm ℂ 2 0 f
  let C : ℝ := S / |a| ^ (2 : ℕ)
  let b : ℤ → ℝ := fun n =>
    if n = 0 then ‖f 0‖ else C * (1 / (n : ℝ) ^ (2 : ℕ))
  have hbase : Summable (fun n : ℤ => C * (1 / (n : ℝ) ^ (2 : ℕ))) :=
    ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)).mul_left C
  have hb : Summable b := by
    apply hbase.congr_cofinite
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
    simp [b, hn]
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hb
  by_cases hn : n = 0
  · subst n
    simp [b]
  · rw [show b n = C * (1 / (n : ℝ) ^ (2 : ℕ)) by simp [b, hn]]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have han : a * (n : ℝ) ≠ 0 := mul_ne_zero ha hnR
    have hx : 0 < ‖a * (n : ℝ)‖ ^ (2 : ℕ) :=
      pow_pos (norm_pos_iff.mpr han) _
    have hsem :=
      SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 (a * (n : ℝ))
    calc
      ‖f (a * (n : ℝ))‖ ≤
          S / ‖a * (n : ℝ)‖ ^ (2 : ℕ) := by
        apply (le_div_iff₀ hx).2
        simpa [S, mul_comm] using hsem
      _ = C * (1 / (n : ℝ) ^ (2 : ℕ)) := by
        dsimp [C]
        rw [abs_mul]
        have haabs : |a| ≠ 0 := abs_ne_zero.mpr ha
        have hnabs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnR
        field_simp
        rw [sq_abs]

end RHTower
end GaloisForLFunctions
