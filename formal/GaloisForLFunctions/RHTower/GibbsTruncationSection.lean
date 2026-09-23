import Mathlib
import GaloisForLFunctions.RHTower.GibbsWeakCouplingConfinement

/-!
# Truncation of the gas to a binomial section

If every configuration of at most `J` elements is light (`x·e(T) ≤ ε`) and every larger one
is heavy (`x·e(T) ≥ R`), the gas is uniformly close to the truncated binomial

  `∑_{j ≤ J} C(k,j) z^j`,

with error `(ε + e^{-R})·(1+‖z‖)^k`.  Rescaling `z ↦ w/k` turns the truncated binomial into
the `J`-th Taylor section of the exponential, so the gas inherits the zero geometry of those
sections.  The sixth section is recorded here: it has no zero on the imaginary axis, and its
third Hurwitz determinant is negative — the two facts that place a zero of the gas strictly
inside the right half-plane.
-/

namespace RHTower.GibbsGas

open Real

/-- The subset-sum of a constant is a binomial power. -/
theorem sum_powerset_pow_card (S : Finset ℕ) (t : ℝ) :
    ∑ T ∈ S.powerset, t ^ T.card = (1 + t) ^ S.card := by
  have h := Finset.prod_add (fun _ : ℕ => t) (fun _ : ℕ => (1 : ℝ)) S
  simp only [Finset.prod_const, one_pow, mul_one] at h
  rw [← h, add_comm]

/-- The light part of the gas is the truncated binomial. -/
theorem sum_powerset_card_le_eq_binomial (S : Finset ℕ) (J : ℕ) (z : ℂ) :
    ∑ T ∈ S.powerset.filter (fun T => T.card ≤ J), z ^ T.card
      = ∑ j ∈ Finset.range (J + 1), (Nat.choose S.card j : ℂ) * z ^ j := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun T : Finset ℕ => T.card) (t := Finset.range (J + 1))
    (fun T hT => by
      rw [Finset.mem_filter] at hT
      exact Finset.mem_range.mpr (by omega)) (fun T : Finset ℕ => z ^ T.card)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hfil : (S.powerset.filter (fun T => T.card ≤ J)).filter (fun T => T.card = j)
      = S.powersetCard j := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, _⟩, hcard⟩
      exact ⟨hsub, hcard⟩
    · rintro ⟨hsub, hcard⟩
      exact ⟨⟨hsub, by omega⟩, hcard⟩
  rw [hfil]
  have hcongr : ∀ T ∈ S.powersetCard j, z ^ T.card = z ^ j := by
    intro T hT
    rw [(Finset.mem_powersetCard.mp hT).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_powersetCard,
    nsmul_eq_mul]

/-- **The truncation lemma.**  A light/heavy dichotomy at level `J` makes the gas uniformly
close to the truncated binomial of degree `J`. -/
theorem gibbsDiagC_sub_truncated_le (S : Finset ℕ) (x : ℝ) (hx : 0 ≤ x)
    (J : ℕ) (ε R : ℝ) (hε : 0 ≤ ε)
    (hlight : ∀ T ∈ S.powerset, T.card ≤ J → x * ∏ p ∈ T, (p : ℝ) ≤ ε)
    (hheavy : ∀ T ∈ S.powerset, J < T.card → R ≤ x * ∏ p ∈ T, (p : ℝ))
    (z : ℂ) :
    ‖gibbsDiagC S x z
        - ∑ j ∈ Finset.range (J + 1), (Nat.choose S.card j : ℂ) * z ^ j‖
      ≤ (ε + Real.exp (-R)) * (1 + ‖z‖) ^ S.card := by
  classical
  rw [← sum_powerset_card_le_eq_binomial]
  have hsplit : gibbsDiagC S x z
        - ∑ T ∈ S.powerset.filter (fun T => T.card ≤ J), z ^ T.card
      = (∑ T ∈ S.powerset.filter (fun T => T.card ≤ J),
            z ^ T.card * ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 : ℝ) : ℂ))
        + ∑ T ∈ S.powerset.filter (fun T => ¬ T.card ≤ J),
            z ^ T.card * ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) : ℝ) : ℂ) := by
    rw [gibbsDiagC, ← Finset.sum_filter_add_sum_filter_not S.powerset
      (fun T => T.card ≤ J), add_sub_right_comm]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    push_cast
    ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  -- the light block
  have hlightbd : ‖∑ T ∈ S.powerset.filter (fun T => T.card ≤ J),
      z ^ T.card * ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1 : ℝ) : ℂ)‖
      ≤ ε * ∑ T ∈ S.powerset.filter (fun T => T.card ≤ J), ‖z‖ ^ T.card := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    rw [Finset.mem_filter] at hT
    have hT0 : (0 : ℝ) ≤ ∏ p ∈ T, (p : ℝ) :=
      Finset.prod_nonneg fun p _ => Nat.cast_nonneg p
    have hy : 0 ≤ x * ∏ p ∈ T, (p : ℝ) := mul_nonneg hx hT0
    have hexp : |Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1| ≤ ε := by
      have h1 : Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      have h2 : 1 - (x * ∏ p ∈ T, (p : ℝ))
          ≤ Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) := by
        have h3 := Real.add_one_le_exp (-(x * ∏ p ∈ T, (p : ℝ)))
        linarith
      have hle := hlight T hT.1 hT.2
      rw [abs_le]
      constructor <;> linarith
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hzc : (0 : ℝ) ≤ ‖z‖ ^ T.card := by positivity
    calc ‖z‖ ^ T.card * |Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) - 1|
        ≤ ‖z‖ ^ T.card * ε := mul_le_mul_of_nonneg_left hexp hzc
      _ = ε * ‖z‖ ^ T.card := by ring
  -- the heavy block
  have hheavybd : ‖∑ T ∈ S.powerset.filter (fun T => ¬ T.card ≤ J),
      z ^ T.card * ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) : ℝ) : ℂ)‖
      ≤ Real.exp (-R)
        * ∑ T ∈ S.powerset.filter (fun T => ¬ T.card ≤ J), ‖z‖ ^ T.card := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    rw [Finset.mem_filter, not_le] at hT
    have hR := hheavy T hT.1 hT.2
    have hexp : Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) ≤ Real.exp (-R) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    have hzc : (0 : ℝ) ≤ ‖z‖ ^ T.card := by positivity
    calc ‖z‖ ^ T.card * Real.exp (-(x * ∏ p ∈ T, (p : ℝ)))
        ≤ ‖z‖ ^ T.card * Real.exp (-R) := mul_le_mul_of_nonneg_left hexp hzc
      _ = Real.exp (-R) * ‖z‖ ^ T.card := by ring
  refine le_trans (add_le_add hlightbd hheavybd) ?_
  have hR0 : (0 : ℝ) ≤ Real.exp (-R) := (Real.exp_pos _).le
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hsum1 : ∑ T ∈ S.powerset.filter (fun T => T.card ≤ J), ‖z‖ ^ T.card
      ≤ (1 + ‖z‖) ^ S.card := by
    rw [← sum_powerset_pow_card S ‖z‖]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun T _ _ => by positivity)
  have hsum2 : ∑ T ∈ S.powerset.filter (fun T => ¬ T.card ≤ J), ‖z‖ ^ T.card
      ≤ (1 + ‖z‖) ^ S.card := by
    rw [← sum_powerset_pow_card S ‖z‖]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun T _ _ => by positivity)
  have hb1 := mul_le_mul_of_nonneg_left hsum1 hε
  have hb2 := mul_le_mul_of_nonneg_left hsum2 hR0
  nlinarith [hb1, hb2]

/-! ## The sixth Taylor section of the exponential -/

/-- `6!` times the sixth Taylor section of the exponential. -/
noncomputable def expSection6 (w : ℂ) : ℂ :=
  w ^ (6 : ℕ) + 6 * w ^ (5 : ℕ) + 30 * w ^ (4 : ℕ) + 120 * w ^ (3 : ℕ) + 360 * w ^ (2 : ℕ) + 720 * w + 720

theorem expSection6_axis (y : ℝ) :
    expSection6 ((y : ℂ) * Complex.I)
      = (((-(y ^ (6 : ℕ)) + 30 * y ^ (4 : ℕ) - 360 * y ^ (2 : ℕ) + 720 : ℝ)) : ℂ)
        + (((6 * y ^ (5 : ℕ) - 120 * y ^ (3 : ℕ) + 720 * y : ℝ)) : ℂ) * Complex.I := by
  have h2 : ((y : ℂ) * Complex.I) ^ (2 : ℕ) = -((y : ℂ) ^ (2 : ℕ)) := by
    rw [mul_pow, Complex.I_sq]; ring
  have h3 : ((y : ℂ) * Complex.I) ^ (3 : ℕ) = -((y : ℂ) ^ (3 : ℕ)) * Complex.I := by
    rw [pow_succ, h2]; ring
  have h4 : ((y : ℂ) * Complex.I) ^ (4 : ℕ) = (y : ℂ) ^ (4 : ℕ) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]; ring
  have h5 : ((y : ℂ) * Complex.I) ^ (5 : ℕ) = (y : ℂ) ^ (5 : ℕ) * Complex.I := by
    rw [pow_succ, h4]; ring
  have h6 : ((y : ℂ) * Complex.I) ^ (6 : ℕ) = -((y : ℂ) ^ (6 : ℕ)) := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, h2]; ring
  rw [expSection6, h2, h3, h4, h5, h6]
  push_cast
  ring

/-- **The sixth section has no zero on the imaginary axis**: its imaginary part there is
`6y((y²−10)² + 20)`, which vanishes only at `y = 0`, where the value is `720`. -/
theorem expSection6_ne_zero_on_axis (y : ℝ) :
    expSection6 ((y : ℂ) * Complex.I) ≠ 0 := by
  intro h
  rw [expSection6_axis] at h
  have him : 6 * y ^ (5 : ℕ) - 120 * y ^ (3 : ℕ) + 720 * y = 0 := by
    have hh := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero,
      Complex.zero_im] at hh
    linarith
  have hre : -(y ^ (6 : ℕ)) + 30 * y ^ (4 : ℕ) - 360 * y ^ (2 : ℕ) + 720 = 0 := by
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, sub_zero, add_zero,
      Complex.zero_re] at hh
    linarith
  have hfac : 6 * y ^ (5 : ℕ) - 120 * y ^ (3 : ℕ) + 720 * y
      = 6 * y * ((y ^ (2 : ℕ) - 10) ^ (2 : ℕ) + 20) := by ring
  have hpos : (0 : ℝ) < (y ^ (2 : ℕ) - 10) ^ (2 : ℕ) + 20 := by positivity
  have hy : y = 0 := by
    rw [hfac] at him
    rcases mul_eq_zero.mp him with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · norm_num at h3
      · exact h4
    · exact absurd h2 (ne_of_gt hpos)
  rw [hy] at hre
  norm_num at hre

/-- **The third Hurwitz determinant of the sixth section is negative.**  The minor is the
leading `3 × 3` block of the Hurwitz matrix of `w⁶+6w⁵+30w⁴+120w³+360w²+720w+720`. -/
theorem expSection6_hurwitzDelta3 :
    (6 : ℝ) * (30 * 120 - 360 * 6) - 120 * (1 * 120 - 360 * 0)
      + 720 * (1 * 6 - 30 * 0) = -1440 := by
  norm_num

end RHTower.GibbsGas
