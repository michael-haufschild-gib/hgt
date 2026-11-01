import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive-axis control of centered Weil products

Pairing conjugate unitary eigenvalues turns a centered characteristic polynomial
into a positive scalar times a product of `cosh(h z) - cos θ`. Each factor has
nonnegative even Taylor coefficients, so its modulus on a disk is bounded by its
value at the positive real endpoint. The bound survives products without any
dependence on their degrees.

Consequently pointwise convergence on a real half-line already implies local
boundedness throughout the complex plane. For such products the normal-family
step needs no separate estimate of zero counts. This supplies no sequence of
curves and makes no assertion that their products converge to the Riemann xi function.
-/

open Filter Topology

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-- Removing the constant term from the cosh series preserves its radial majorant. -/
theorem norm_cosh_sub_one_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖Complex.cosh z - 1‖ ≤ Real.cosh R - 1 := by
  have hs := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_cosh z)
  have ht := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cosh R)
  simp only [Finset.sum_range_one, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at hs ht
  refine hs.norm_le_of_bounded ht fun n => ?_
  simp only [norm_div, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg z) hz _) (Nat.cast_nonneg _)

/-- A real shift at most one leaves every coefficient of the cosh series nonnegative. -/
theorem norm_cosh_sub_real_le {z : ℂ} {R c : ℝ} (hz : ‖z‖ ≤ R) (hc : c ≤ 1) :
    ‖Complex.cosh z - (c : ℂ)‖ ≤ Real.cosh R - c := by
  have ht := norm_cosh_sub_one_le hz
  have hnorm : ‖(1 : ℂ) - (c : ℂ)‖ = 1 - c := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc)]
  calc
    ‖Complex.cosh z - (c : ℂ)‖ =
        ‖(Complex.cosh z - 1) + (1 - (c : ℂ))‖ := by congr 1; ring
    _ ≤ ‖Complex.cosh z - 1‖ + ‖(1 : ℂ) - (c : ℂ)‖ := norm_add_le _ _
    _ ≤ Real.cosh R - c := by rw [hnorm]; linarith only [ht]

/-- Product associated with conjugate pairs of unitary eigenvalues after exponential centering. -/
noncomputable def centeredWeilProduct {g : ℕ} (A h : ℝ) (θ : Fin g → ℝ) (z : ℂ) : ℂ :=
  (A : ℂ) * ∏ j, (Complex.cosh ((h : ℂ) * z) - (Real.cos (θ j) : ℂ))

/-- Real-axis value of the centered product. -/
noncomputable def centeredWeilProductReal {g : ℕ} (A h : ℝ) (θ : Fin g → ℝ) (R : ℝ) : ℝ :=
  A * ∏ j, (Real.cosh (h * R) - Real.cos (θ j))

/-- Positive real values bound the product on the whole disk, independently of its degree. -/
theorem norm_centeredWeilProduct_le {g : ℕ} {A h R : ℝ} (θ : Fin g → ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ h) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖centeredWeilProduct A h θ z‖ ≤ centeredWeilProductReal A h θ R := by
  have hhz : ‖(h : ℂ) * z‖ ≤ h * R := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hz hh
  unfold centeredWeilProduct centeredWeilProductReal
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA, norm_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_) hA
  intro j _
  exact norm_cosh_sub_real_le hhz (Real.cos_le_one _)

/-- The complex product restricts to its real formula. -/
theorem centeredWeilProduct_ofReal {g : ℕ} (A h : ℝ) (θ : Fin g → ℝ) (R : ℝ) :
    centeredWeilProduct A h θ (R : ℂ) = (centeredWeilProductReal A h θ R : ℂ) := by
  simp only [centeredWeilProduct, centeredWeilProductReal, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_cosh]

/-- Convergence at every point of a real half-line bounds the sequence on every disk. -/
theorem centeredWeilProduct_bounded_disks_of_real_convergence
    {g : ℕ → ℕ} {A h : ℕ → ℝ} (θ : ∀ n, Fin (g n) → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hh : ∀ n, 0 ≤ h n) {r₀ : ℝ} {L : ℝ → ℝ}
    (hconv : ∀ R, r₀ < R → Tendsto
      (fun n => centeredWeilProductReal (A n) (h n) (θ n) R) atTop (𝓝 (L R)))
    (R : ℝ) :
    ∃ B : ℝ, ∀ n z, ‖z‖ ≤ R → ‖centeredWeilProduct (A n) (h n) (θ n) z‖ ≤ B := by
  let T := max R (r₀ + 1)
  have hRT : R ≤ T := le_max_left _ _
  have hrT : r₀ < T := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  obtain ⟨B, hB⟩ := (hconv T hrT).bddAbove_range
  refine ⟨B, fun n z hz => ?_⟩
  exact (norm_centeredWeilProduct_le (θ n) (hA n) (hh n) (hz.trans hRT)).trans
    (hB (Set.mem_range_self n))

/-- Real-half-line convergence supplies the local boundedness required by Vitali's theorem. -/
theorem centeredWeilProduct_locally_bounded_of_real_convergence
    {g : ℕ → ℕ} {A h : ℕ → ℝ} (θ : ∀ n, Fin (g n) → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hh : ∀ n, 0 ≤ h n) {r₀ : ℝ} {L : ℝ → ℝ}
    (hconv : ∀ R, r₀ < R → Tendsto
      (fun n => centeredWeilProductReal (A n) (h n) (θ n) R) atTop (𝓝 (L R))) :
    ∀ z : ℂ, ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ,
      ∀ n w, w ∈ Metric.ball z ε → ‖centeredWeilProduct (A n) (h n) (θ n) w‖ ≤ B := by
  intro z
  obtain ⟨B, hB⟩ := centeredWeilProduct_bounded_disks_of_real_convergence θ hA hh hconv (‖z‖ + 1)
  refine ⟨1, zero_lt_one, B, fun n w hw => hB n w ?_⟩
  have hw' : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have htri := norm_add_le (w - z) z
  rw [sub_add_cancel] at htri
  linarith only [hw', htri]

end GaloisForLFunctions.ArithmeticResonanceTheory
