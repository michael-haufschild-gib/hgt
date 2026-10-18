import GaloisForLFunctions.RHTower.JointAncestryDampedShellCriterion
import GaloisForLFunctions.HTGeometry.WeightedPowerWindowCompression

/-!
# The mass budget of damped prime-shell Mellin amplitudes

The literal shell `(m²,2m²]` has half-mass at most `m`. On the open critical strip,
quadratic damping bounds its Mellin amplitude by `m / ‖s(1-s)‖`. Consequently every
summable spectral family has a quantitative bound on its number of loud modes.
The reciprocal weights lie in a fixed acute cone above absolute height one.
-/

open Complex RHTower

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- Counting the integer interval suffices for the square-shell half-mass bound. -/
theorem jasShellHalfMass_square_le {m : ℕ} (hm : 1 ≤ m) :
    jasShellHalfMass (m ^ 2) ≤ m := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hterm : ∀ p ∈ jasPrimeWindow (m ^ 2) (2 * m ^ 2),
      Real.exp (-(1 / 2) * Real.log p) ≤ 1 / (m : ℝ) := by
    intro p hp
    have hmp : (m : ℝ) ^ 2 ≤ (p : ℝ) := by
      exact_mod_cast ((mem_jasPrimeWindow.mp hp).1).le
    have hlog := Real.log_le_log (pow_pos hm0 2) hmp
    rw [Real.log_pow] at hlog
    calc
      Real.exp (-(1 / 2) * Real.log p) ≤ Real.exp (-Real.log (m : ℝ)) := by
        apply Real.exp_le_exp.mpr
        norm_num at hlog
        linarith
      _ = 1 / (m : ℝ) := by rw [Real.exp_neg, Real.exp_log hm0, one_div]
  have hcard : (jasPrimeWindow (m ^ 2) (2 * m ^ 2)).card ≤ m ^ 2 := by
    have hi : (jasPrimeWindow (m ^ 2) (2 * m ^ 2)).card ≤
        (Finset.Ioc (m ^ 2) (2 * m ^ 2)).card := by
      refine Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ))
        (fun p hp => ?_) Subtype.val_injective.injOn
      exact Finset.mem_Ioc.mpr (mem_jasPrimeWindow.mp hp)
    rw [Nat.card_Ioc] at hi
    omega
  calc
    jasShellHalfMass (m ^ 2) ≤
        ∑ _p ∈ jasPrimeWindow (m ^ 2) (2 * m ^ 2), 1 / (m : ℝ) :=
      Finset.sum_le_sum hterm
    _ = ((jasPrimeWindow (m ^ 2) (2 * m ^ 2)).card : ℝ) * (1 / (m : ℝ)) := by simp
    _ ≤ (m : ℝ) ^ 2 * (1 / (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = (m : ℝ) := by field_simp

/-- The quadratic damping is matched to the exact reciprocal Weil weight. -/
theorem norm_jasShellDampedSum_le_halfMass_mul_weight (N : ℕ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖jasShellDampedSum N s‖ ≤ jasShellHalfMass N * ‖1 / (s * (1 - s))‖ := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  have hs1 : 1 - s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hn0 : 0 < ‖s * (1 - s)‖ := norm_pos_iff.mpr (mul_ne_zero hs0 hs1)
  have hnorm : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hplus : ‖s + 1‖ ^ 2 = (s.re + 1) ^ 2 + s.im ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsub : ‖1 - s‖ ^ 2 = (1 - s.re) ^ 2 + s.im ^ 2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnormle : ‖s‖ ≤ ‖s + 1‖ := by
    nlinarith [norm_nonneg s, norm_nonneg (s + 1)]
  have hsuble : ‖1 - s‖ ≤ ‖s + 1‖ := by
    nlinarith [norm_nonneg (1 - s), norm_nonneg (s + 1)]
  have hprod : ‖s * (1 - s)‖ ≤ ‖s + 1‖ ^ 2 := by
    rw [norm_mul, pow_two]
    exact mul_le_mul hnormle hsuble (norm_nonneg _) (norm_nonneg _)
  have hU : ‖jasShellUniformSum N s‖ ≤ jasShellHalfMass N :=
    (norm_jasShellUniformSum_le N s).trans
      (Finset.sum_le_sum fun p _ => exp_neg_mul_log_prime_anti (by linarith) p)
  rw [jasShellDampedSum, norm_div, norm_pow]
  calc
    ‖jasShellUniformSum N s‖ / ‖s + 1‖ ^ 2 ≤ jasShellHalfMass N / ‖s + 1‖ ^ 2 :=
      div_le_div_of_nonneg_right hU (by positivity)
    _ ≤ jasShellHalfMass N / ‖s * (1 - s)‖ :=
      div_le_div_of_nonneg_left (jasShellHalfMass_nonneg N) hn0 hprod
    _ = jasShellHalfMass N * ‖1 / (s * (1 - s))‖ := by
      rw [norm_div, norm_one]; ring

/-- A square prime shell pays for each mode using its own reciprocal Weil weight. -/
theorem norm_jasShellDampedSum_square_le_weight {m : ℕ} (hm : 1 ≤ m) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖jasShellDampedSum (m ^ 2) s‖ ≤ (m : ℝ) * ‖1 / (s * (1 - s))‖ :=
  (norm_jasShellDampedSum_le_halfMass_mul_weight (m ^ 2) h0 h1).trans
    (mul_le_mul_of_nonneg_right (jasShellHalfMass_square_le hm) (norm_nonneg _))

/-- No separation or density hypothesis is needed to count loud spectral modes. -/
theorem primeShell_loud_card_budget {ι : Type*} (s : ι → ℂ)
    (hs : ∀ i, 0 < (s i).re ∧ (s i).re < 1)
    (hw : Summable fun i => ‖1 / (s i * (1 - s i))‖)
    {m : ℕ} (hm : 1 ≤ m) (G : Finset ι) (L : ℝ)
    (hG : ∀ i ∈ G, L ≤ ‖jasShellDampedSum (m ^ 2) (s i)‖) :
    (G.card : ℝ) * L ≤ (m : ℝ) * ∑' i, ‖1 / (s i * (1 - s i))‖ :=
  HTGeometry.loud_card_mul_le_weight_mass _ _ hw (Nat.cast_nonneg m)
    (fun i => norm_jasShellDampedSum_square_le_weight hm (hs i).1 (hs i).2) G hG

/-- Above absolute height one the strip's reciprocal Weil weights have a uniform cone. -/
theorem half_norm_weight_le_re_of_height {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hheight : 1 ≤ |s.im|) :
    ‖1 / (s * (1 - s))‖ / 2 ≤ (1 / (s * (1 - s))).re := by
  let v := s * (1 - s)
  have hvre : v.re = s.re * (1 - s.re) + s.im ^ 2 := by dsimp [v]; simp; ring
  have hvim : v.im = s.im * (1 - 2 * s.re) := by dsimp [v]; simp; ring
  have hcross : 0 < s.re * (1 - s.re) := mul_pos h0 (by linarith)
  have hA : 0 < v.re := by rw [hvre]; nlinarith [sq_nonneg s.im]
  have hphase : |1 - 2 * s.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hgamma : |s.im| ≤ s.im ^ 2 := by nlinarith [sq_abs s.im]
  have him : |v.im| ≤ v.re := by
    rw [hvim, abs_mul]
    have hb := mul_le_mul_of_nonneg_left hphase (abs_nonneg s.im)
    rw [hvre]
    nlinarith
  have hnorm : ‖v‖ ≤ 2 * v.re := by
    have hb := Complex.norm_le_abs_re_add_abs_im v
    rw [abs_of_pos hA] at hb
    linarith
  have hv0 : v ≠ 0 := fun h => by simp [h] at hA
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  change ‖1 / v‖ / 2 ≤ (1 / v).re
  rw [one_div, norm_inv, Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hident : ‖v‖⁻¹ / 2 = (‖v‖ / 2) / ‖v‖ ^ 2 := by field_simp
  rw [hident]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

end

end GaloisForLFunctions.BiScaleUncertainty
