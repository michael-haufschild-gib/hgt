/-
# The order-`p` regularized determinant of a power-trace sequence

The regularized determinant depends on its operator only through the sequence of power traces from
exponent `p` upwards.  Naming that sequence as the datum removes every reference to a spectrum: the
same series, the same domain of convergence and the same continuity statement hold for an arbitrary
complex sequence with a geometric bound.  The spectral determinant and the operator determinant are
then two instances of one object, and the operator instance needs no self-adjointness.

Main results:
* `tracePowerDetExp`, `tracePowerDet` — **the order-`p` regularized determinant of a sequence**.
* `norm_tracePowerDetTerm_le`, `summable_tracePowerDetExp` — the geometric majorant.
* `tracePowerDet_congr` — **it forgets every trace below `p`**.
* `tendsto_tracePowerDet_of_tendsto` — **it is continuous in the power traces**.
-/
import Mathlib

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The order-`p` regularized exponent of a power-trace sequence. -/
def tracePowerDetExp (p : ℕ) (τ : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, z ^ (k + p) / ((k + p : ℕ) : ℂ) * τ (k + p)

/-- **The order-`p` regularized determinant of a power-trace sequence.** -/
def tracePowerDet (p : ℕ) (τ : ℕ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (- tracePowerDetExp p τ z)

theorem natCast_add_pos_ne_zero {p : ℕ} (hp : 0 < p) (k : ℕ) : ((k + p : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by omega)

theorem one_le_norm_natCast_add {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (1 : ℝ) ≤ ‖((k + p : ℕ) : ℂ)‖ := by
  rw [Complex.norm_natCast]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)

/-- The geometric majorant of the regularized exponent's terms. -/
theorem norm_tracePowerDetTerm_le {p : ℕ} (hp : 0 < p) {τ : ℕ → ℂ} {B S : ℝ}
    (hbound : ∀ k : ℕ, ‖τ (k + p)‖ ≤ S * B ^ k) (z : ℂ) (k : ℕ) :
    ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * τ (k + p)‖ ≤ (S * ‖z‖ ^ p) * (‖z‖ * B) ^ k := by
  have hden := one_le_norm_natCast_add hp k
  have hnum : ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * τ (k + p)‖ ≤ ‖z‖ ^ (k + p) * (S * B ^ k) := by
    rw [norm_mul, norm_div, norm_pow]
    refine mul_le_mul ?_ (hbound k) (norm_nonneg _) ?_
    · rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖((k + p : ℕ) : ℂ)‖)]
      nlinarith [pow_nonneg (norm_nonneg z) (k + p)]
    · positivity
  refine le_trans hnum (le_of_eq ?_)
  rw [pow_add, mul_pow]
  ring

/-- The regularized exponent converges inside the reciprocal geometric rate. -/
theorem summable_tracePowerDetExp {p : ℕ} (hp : 0 < p) {τ : ℕ → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B) (hbound : ∀ k : ℕ, ‖τ (k + p)‖ ≤ S * B ^ k)
    {z : ℂ} (hz : ‖z‖ * B < 1) :
    Summable fun k : ℕ => z ^ (k + p) / ((k + p : ℕ) : ℂ) * τ (k + p) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hzB0 : 0 ≤ ‖z‖ * B := mul_nonneg (norm_nonneg z) hB0
  refine Summable.of_norm_bounded (g := fun k : ℕ => (S * ‖z‖ ^ p) * (‖z‖ * B) ^ k)
    ((summable_geometric_of_lt_one hzB0 hz).mul_left _) ?_
  intro k
  exact norm_tracePowerDetTerm_le hp hbound z k

/-- **The determinant forgets every trace below the order.** -/
theorem tracePowerDet_congr {p : ℕ} {τ σ : ℕ → ℂ}
    (h : ∀ n, p ≤ n → τ n = σ n) (z : ℂ) :
    tracePowerDet p τ z = tracePowerDet p σ z := by
  have hexp : tracePowerDetExp p τ z = tracePowerDetExp p σ z := by
    refine tsum_congr fun k => ?_
    rw [h (k + p) (Nat.le_add_left p k)]
  rw [tracePowerDet, tracePowerDet, hexp]

/-- **Continuity of the order-`p` determinant in the power traces.** -/
theorem tendsto_tracePowerDet_of_tendsto {p : ℕ} (hp : 0 < p)
    {L : Type*} {l : Filter L} {τ : L → ℕ → ℂ} {σ : ℕ → ℂ} {B S : ℝ}
    (hB1 : 1 ≤ B)
    (hbound : ∀ (a : L) (k : ℕ), ‖τ a (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Filter.Tendsto (fun a => τ a (k + p)) l (nhds (σ (k + p))))
    {z : ℂ} (hz : ‖z‖ * B < 1) :
    Filter.Tendsto (fun a => tracePowerDet p (τ a) z) l (nhds (tracePowerDet p σ z)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hzB0 : 0 ≤ ‖z‖ * B := mul_nonneg (norm_nonneg z) hB0
  have hdom : Summable fun k : ℕ => (S * ‖z‖ ^ p) * (‖z‖ * B) ^ k :=
    (summable_geometric_of_lt_one hzB0 hz).mul_left _
  have hexp : Filter.Tendsto (fun a => tracePowerDetExp p (τ a) z) l
      (nhds (tracePowerDetExp p σ z)) := by
    simp only [tracePowerDetExp]
    exact tendsto_tsum_of_dominated_convergence hdom (fun k => (hconv k).const_mul _)
      (Filter.Eventually.of_forall fun a k => norm_tracePowerDetTerm_le hp (hbound a) z k)
  exact (Complex.continuous_exp.continuousAt).tendsto.comp hexp.neg

end

end GaloisForLFunctions.HTGeometry
