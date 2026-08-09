import GaloisForLFunctions.HTGeometry.SectionLogTail

/-!
# The counterterm jet series

After the counterterms are subtracted and the nome product is divided out, what remains of a finite
section's free energy is a power series in the nome product whose coefficients are the finite Euler
products.  Its terms are dominated by a geometric series in `|Q_S| |y|`, so the whole series differs
from its leading term by `O(|Q_S|)`.

Since the nome product collapses and the finite Euler products converge to the infinite one, the
series converges to the leading coefficient of the jet.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- The jet series: the divided remainder of a finite section's free energy. -/
noncomputable def jetSeries {ι : Type*} (p : ι → ℂ) (S : Finset ι) (y : ℂ) (N : ℕ) : ℂ :=
  ∑' k : ℕ, (∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ) *
    ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹

/-- Each term of the jet series is dominated by a geometric term in `|Q_S| |y|`. -/
theorem norm_jetSeries_term_le {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) (y : ℂ) {N : ℕ} (hN : g + 1 ≤ N) (k : ℕ) :
    ‖(∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ) *
        ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹‖
      ≤ ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N) *
          (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hcast : ((k + N : ℕ) : ℝ) = (k : ℝ) + (N : ℝ) := by push_cast; ring
  have hge : (N : ℝ) ≤ ((k + N : ℕ) : ℝ) := by
    rw [hcast]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpos : (0 : ℝ) < ((k + N : ℕ) : ℝ) := lt_of_lt_of_le hNr hge
  have heuler := norm_finiteEulerProduct_le g p hp_lt hsum S (k := k + N) (by omega)
  have hB : (0 : ℝ) ≤ ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹ := le_trans (norm_nonneg _) heuler
  have hnormval : ‖(∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ)‖
      = ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N) / ((k + N : ℕ) : ℝ) := by
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  rw [norm_mul, hnormval]
  have hfirst : ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N) / ((k + N : ℕ) : ℝ)
      ≤ (‖y‖ ^ N / (N : ℝ)) * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by
    have hsplit : ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N)
        = ‖y‖ ^ N * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by
      rw [pow_add, mul_pow]
      ring
    rw [hsplit]
    rw [div_le_iff₀ hpos]
    have hnn : (0 : ℝ) ≤ ‖y‖ ^ N * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k := by positivity
    have hfac : (1 : ℝ) ≤ ((k + N : ℕ) : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNr]
      linarith
    have hrhs : ‖y‖ ^ N / (N : ℝ) * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k * ((k + N : ℕ) : ℝ)
        = (‖y‖ ^ N * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k) * (((k + N : ℕ) : ℝ) / (N : ℝ)) := by
      field_simp
    rw [hrhs]
    exact le_mul_of_one_le_right hnn hfac
  have hstep : ‖∏ a ∈ S, p a‖ ^ k * ‖y‖ ^ (k + N) / ((k + N : ℕ) : ℝ) *
        ‖∏ a ∈ S, (1 - p a ^ (k + N))⁻¹‖
      ≤ ((‖y‖ ^ N / (N : ℝ)) * (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k) *
          ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
    refine mul_le_mul hfirst heuler (norm_nonneg _) ?_
    positivity
  refine hstep.trans (le_of_eq ?_)
  ring

/-- The jet series converges whenever the nome product times the coordinate is a contraction. -/
theorem summable_jetSeries {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) {y : ℂ} {N : ℕ} (hN : g + 1 ≤ N)
    (hcontr : ‖∏ a ∈ S, p a‖ * ‖y‖ < 1) :
    Summable (fun k : ℕ => (∏ a ∈ S, p a) ^ k * y ^ (k + N) / ((k + N : ℕ) : ℂ) *
      ∏ a ∈ S, (1 - p a ^ (k + N))⁻¹) := by
  have hgeom : Summable (fun k : ℕ =>
      ((∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹) / (N : ℝ) * ‖y‖ ^ N) *
        (‖∏ a ∈ S, p a‖ * ‖y‖) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hcontr).mul_left _
  exact Summable.of_norm_bounded hgeom (norm_jetSeries_term_le g p hp_lt hsum S y hN)

end HTGeometry
