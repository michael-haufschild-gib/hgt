import GaloisForLFunctions.RHTower.EulerDeletionRemainderRefinementObstruction

/-!
# Arithmetic minimum classes of the retained deletion remainder

Möbius inversion and Bernoulli-tail normalization give a strictly negative real
arithmetic balance at every zeta zero in the open strip. Two literal arithmetic
profiles have unique minimum labels, with a separate nonattainment class and a
least-index rule retaining all ties. Their decay forces finite labels in opposite
halves of the strip. Every positive label is squarefree.

The exact mean bounds any attained minimum. Even at a critical-line zero, a
finite profile value must undershoot the explicit reciprocal-square boundary.
These statements do not exclude the finite minimum classes and do not prove RH.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The Bernoulli-tail normalization before taking the signed arithmetic real part. -/
def minimumNormalization (s : ℂ) : ℂ := star s * (star s + 1)

/-- The actual normalized arithmetic summand; no zero-location test enters its definition. -/
def minimumBalanceTerm (s : ℂ) (p : ℕ) : ℂ :=
  (μ p : ℂ) * (infiniteRemainder s p / (p : ℂ)) / minimumNormalization s

/-- A real arithmetic profile with freely chosen dilation exponent. -/
def minimumProfile (s : ℂ) (a : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (a + 1) * (minimumBalanceTerm s p).re

/-- First arithmetic profile, defined before choosing a zero. -/
def rightMinimumProfile (s : ℂ) : ℕ → ℝ := minimumProfile s 1

/-- Second arithmetic profile, defined without a branch on zero location. -/
def leftMinimumProfile (s : ℂ) : ℕ → ℝ := minimumProfile s (4 * s.re - 1)

theorem summable_minimumBalanceTerm {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Summable (fun p : ℕ+ => minimumBalanceTerm s p) := by
  have h : Summable (fun p : ℕ+ => (μ (p : ℕ) : ℂ) *
      (infiniteRemainder s p / (p : ℂ))) := by
    apply Summable.of_norm
    simpa only [Nat.one_mul] using
      summable_norm_moebius_infiniteRemainder hs hs1 (m := 1) (by omega)
  exact h.div_const _

theorem minimumProfile_div_weight (s : ℂ) (a : ℝ) {p : ℕ} (hp : 0 < p) :
    minimumProfile s a p / (p : ℝ) ^ (a + 1) = (minimumBalanceTerm s p).re := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rw [minimumProfile]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hp' _)]

theorem summable_minimumProfile_div_weight {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (a : ℝ) : Summable (fun p : ℕ+ => minimumProfile s a p / (p : ℝ) ^ (a + 1)) := by
  have h := (Complex.hasSum_re (summable_minimumBalanceTerm hs hs1).hasSum).summable
  exact h.congr (fun p => (minimumProfile_div_weight s a p.pos).symm)

private theorem minimumNormalization_ne_zero {s : ℂ} (hs : 0 < s.re) :
    minimumNormalization s ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have he := congrArg Complex.re h
    simp at he
    linarith
  · intro h
    have he := congrArg Complex.re h
    simp at he
    linarith

/-- Exact negative balance; all weighted profile sums retain the same arithmetic boundary. -/
theorem tsum_minimumProfile_div_weight_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0) (a : ℝ) :
    (∑' p : ℕ+, minimumProfile s a p / (p : ℝ) ^ (a + 1)) =
      -((star s * (1 - star s))⁻¹).re / 2 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  have hu0 : star s ≠ 0 := (mul_ne_zero_iff.1 (minimumNormalization_ne_zero hs)).1
  have hup : star s + 1 ≠ 0 := (mul_ne_zero_iff.1 (minimumNormalization_ne_zero hs)).2
  have hum : 1 - star s ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp at he
    linarith
  calc
    _ = (∑' p : ℕ+, minimumBalanceTerm s p).re := by
      rw [Complex.re_tsum (summable_minimumBalanceTerm hs hs1)]
      exact tsum_congr fun p => minimumProfile_div_weight s a p.pos
    _ = (((1 / 2 : ℂ) - 1 / (1 - star s)) / minimumNormalization s).re := by
      simp only [minimumBalanceTerm, tsum_div_const]
      rw [moebius_infiniteRemainder_at_zero hs hs1 hz]
    _ = _ := by
      have he : ((1 / 2 : ℂ) - 1 / (1 - star s)) / minimumNormalization s =
          -(star s * (1 - star s))⁻¹ / 2 := by
        rw [minimumNormalization]
        field_simp
        ring
      rw [he]
      simp

/-- The normalized arithmetic boundary is strictly negative throughout the open strip. -/
theorem minimum_boundary_neg {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    -((star s * (1 - star s))⁻¹).re / 2 < 0 := by
  have he : (star s * (1 - star s)).re = s.re * (1 - s.re) + s.im ^ 2 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hp : 0 < (star s * (1 - star s)).re := by
    rw [he]
    exact add_pos_of_pos_of_nonneg (mul_pos hs (sub_pos.2 hs')) (sq_nonneg _)
  have hn : 0 < Complex.normSq (star s * (1 - star s)) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (star s * (1 - star s)).im]
  rw [Complex.inv_re]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hp hn)) (by norm_num)

/-- Every zero forces a negative entry in every power-normalized arithmetic profile. -/
theorem exists_minimumProfile_neg_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0) (a : ℝ) :
    ∃ p : ℕ, 0 < p ∧ minimumProfile s a p < 0 := by
  by_contra h
  push Not at h
  have hn := minimum_boundary_neg hs hs'
  rw [← tsum_minimumProfile_div_weight_at_zero hs hs' hz a] at hn
  have hnn : 0 ≤ ∑' p : ℕ+, minimumProfile s a p / (p : ℝ) ^ (a + 1) := by
    apply tsum_nonneg
    intro p
    exact div_nonneg (h p p.pos) (Real.rpow_nonneg (by positivity) _)
  linarith

/-- An attained negative global minimum on the positive integers. -/
def HasNegativeMinimum (f : ℕ → ℝ) (p : ℕ) : Prop :=
  0 < p ∧ f p < 0 ∧ ∀ q : ℕ, 0 < q → f p ≤ f q

/-- Zero labels no attained negative minimum; a positive label selects the least minimizer. -/
def NegativeMinimumClass (f : ℕ → ℝ) (p : ℕ) : Prop :=
  if p = 0 then ¬ ∃ q, HasNegativeMinimum f q
  else HasNegativeMinimum f p ∧ ∀ q, q < p → ¬ HasNegativeMinimum f q

/-- Every real sequence has one and only one minimum label, including the nonattainment case. -/
theorem existsUnique_negativeMinimumClass (f : ℕ → ℝ) :
    ∃! p : ℕ, NegativeMinimumClass f p := by
  classical
  by_cases h : ∃ p, HasNegativeMinimum f p
  · let p := Nat.find h
    have hp := Nat.find_spec h
    have hp0 : p ≠ 0 := by have := hp.1; dsimp [p]; omega
    refine ⟨p, ?_, ?_⟩
    · change NegativeMinimumClass f p
      simp only [NegativeMinimumClass, hp0, if_false]
      exact ⟨hp, fun q hq => Nat.find_min h hq⟩
    · intro q hq
      by_cases hq0 : q = 0
      · subst q
        simp [NegativeMinimumClass] at hq
        exact False.elim (h.elim hq)
      · rw [NegativeMinimumClass, if_neg hq0] at hq
        apply Nat.le_antisymm
        · by_contra hn
          exact hq.2 p (by omega) hp
        · exact Nat.find_min' h hq.1
  · refine ⟨0, ?_, ?_⟩
    · simpa [NegativeMinimumClass] using h
    · intro q hq
      by_cases hq0 : q = 0
      · exact hq0
      · rw [NegativeMinimumClass, if_neg hq0] at hq
        exact False.elim (h ⟨q, hq.1⟩)

/-- A negative entry together with decay forces attainment of a negative minimum. -/
theorem exists_negativeMinimum_of_tendsto_zero {f : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hn : ∃ p : ℕ, 0 < p ∧ f p < 0) :
    ∃ p, HasNegativeMinimum f p := by
  obtain ⟨p, hp, hfp⟩ := hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hf).1 (f p) hfp)
  let K := max N p
  have hmem : p ∈ Finset.Icc 1 K := by simp only [Finset.mem_Icc]; dsimp [K]; omega
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 K) f ⟨p, hmem⟩
  refine ⟨q, (Finset.mem_Icc.1 hq).1, lt_of_le_of_lt (hmin p hmem) hfp, ?_⟩
  intro r hr
  by_cases hrK : r ≤ K
  · exact hmin r (Finset.mem_Icc.2 ⟨hr, hrK⟩)
  · have hrN : N ≤ r := by dsimp [K] at hrK; omega
    exact (hmin p hmem).trans (hN r hrN).le

private theorem norm_minimumNormalization (s : ℂ) :
    ‖minimumNormalization s‖ = ‖s * (s + 1)‖ := by
  have he : minimumNormalization s = star (s * (s + 1)) := by
    simp [minimumNormalization]
  rw [he, norm_star]

/-- Quantitative profile envelope, with the complex derivative factor cancelled exactly. -/
theorem abs_minimumProfile_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (a : ℝ) {p : ℕ} (hp : 0 < p) :
    |minimumProfile s a p| ≤
      ((∑' n : ℕ+, (n : ℝ) ^ (-2 * s.re - 1)) / (s.re + 1)) *
        (p : ℝ) ^ (a - 2 * s.re) := by
  let S : ℝ := ∑' n : ℕ+, (n : ℝ) ^ (-2 * s.re - 1)
  let D : ℝ := ‖minimumNormalization s‖
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hD : 0 < D := norm_pos_iff.2 (minimumNormalization_ne_zero hs)
  have hmu : ‖(μ p : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := p))
  have hb : ‖minimumBalanceTerm s p‖ ≤
      (((D / (s.re + 1)) * S) * (p : ℝ) ^ (-2 * s.re)) / (p : ℝ) / D := by
    rw [minimumBalanceTerm, norm_div, norm_mul, norm_div, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right ?_ hD.le
    refine (mul_le_of_le_one_left (by positivity) hmu).trans ?_
    apply div_le_div_of_nonneg_right ?_ hp'.le
    simpa only [← norm_minimumNormalization] using norm_infiniteRemainder_le hs hs1 hp
  rw [minimumProfile, abs_mul, abs_of_nonneg (Real.rpow_nonneg hp'.le _)]
  refine (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hb)
    (Real.rpow_nonneg hp'.le _)).trans_eq ?_
  have he : (p : ℝ) ^ (a + 1) * (p : ℝ) ^ (-2 * s.re) / p =
      (p : ℝ) ^ (a - 2 * s.re) := by
    apply (div_eq_iff hp'.ne').2
    rw [← Real.rpow_add hp']
    calc
      _ = (p : ℝ) ^ ((a - 2 * s.re) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hp', Real.rpow_one]
  calc
    _ = (S / (s.re + 1)) * ((p : ℝ) ^ (a + 1) * (p : ℝ) ^ (-2 * s.re) / p) := by
      field_simp
    _ = _ := by rw [he]

/-- The actual profile decays whenever its chosen exponent is smaller than twice the real part. -/
theorem tendsto_minimumProfile {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {a : ℝ} (ha : a < 2 * s.re) :
    Tendsto (minimumProfile s a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 ha)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : -(2 * s.re - a) = a - 2 * s.re := by ring
  have hlim := h.const_mul ((∑' n : ℕ+, (n : ℝ) ^ (-2 * s.re - 1)) / (s.re + 1))
  simp only [Function.comp_apply, he, mul_zero] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with p hp
  exact abs_minimumProfile_le hs hs1 a (by omega)

/-- The complete pair of minimum classes, retaining exceptional nonattainment cases. -/
def ArithmeticMinimumClass (s : ℂ) (ij : ℕ × ℕ) : Prop :=
  NegativeMinimumClass (rightMinimumProfile s) ij.1 ∧
    NegativeMinimumClass (leftMinimumProfile s) ij.2

/-- Every exponent has a unique arithmetic class; no zero or location is assumed for coverage. -/
theorem existsUnique_arithmeticMinimumClass (s : ℂ) :
    ∃! ij : ℕ × ℕ, ArithmeticMinimumClass s ij := by
  obtain ⟨i, hi, hiu⟩ := existsUnique_negativeMinimumClass (rightMinimumProfile s)
  obtain ⟨j, hj, hju⟩ := existsUnique_negativeMinimumClass (leftMinimumProfile s)
  refine ⟨(i,j), ⟨hi,hj⟩, ?_⟩
  rintro ⟨i',j'⟩ ⟨hi',hj'⟩
  exact Prod.ext (hiu i' hi') (hju j' hj')

/-- Every strict-right zero has a finite negative minimum in the first arithmetic profile. -/
theorem rightMinimum_attained_at_strict_right_zero {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0) :
    ∃ p, HasNegativeMinimum (rightMinimumProfile s) p := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  exact exists_negativeMinimum_of_tendsto_zero
    (tendsto_minimumProfile hs0 hs1 (by linarith))
    (exists_minimumProfile_neg_at_zero hs0 hs' hz 1)

/-- Every strict-left zero has a finite negative minimum in the second arithmetic profile. -/
theorem leftMinimum_attained_at_strict_left_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < (1 / 2 : ℝ)) (hz : riemannZeta s = 0) :
    ∃ p, HasNegativeMinimum (leftMinimumProfile s) p := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  exact exists_negativeMinimum_of_tendsto_zero
    (tendsto_minimumProfile hs hs1 (by linarith))
    (exists_minimumProfile_neg_at_zero hs (by linarith) hz (4*s.re-1))

/-- The class with no attained negative minimum in either profile is confined to the line. -/
theorem re_eq_half_of_arithmeticMinimumClass_zero_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0)
    (hc : ArithmeticMinimumClass s (0,0)) : s.re = 1 / 2 := by
  obtain ⟨hx,hy⟩ := hc
  simp [NegativeMinimumClass] at hx hy
  apply le_antisymm
  · by_contra h
    exact (rightMinimum_attained_at_strict_right_zero (by linarith) hs' hz).elim hx
  · by_contra h
    exact (leftMinimum_attained_at_strict_left_zero hs (by linarith) hz).elim hy

/-- An arithmetic minimum cannot be carried by a nonsquarefree modulus. -/
theorem squarefree_of_minimumProfile_neg {s : ℂ} {a : ℝ} {p : ℕ}
    (hp : minimumProfile s a p < 0) : Squarefree p := by
  by_contra h
  have hmu := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
  simp [minimumProfile, minimumBalanceTerm, hmu] at hp

/-- Every positive class label identifies a squarefree arithmetic modulus. -/
theorem squarefree_of_negativeMinimumClass {s : ℂ} {a : ℝ} {p : ℕ}
    (hp : 0 < p) (hc : NegativeMinimumClass (minimumProfile s a) p) : Squarefree p := by
  rw [NegativeMinimumClass, if_neg (by omega)] at hc
  exact squarefree_of_minimumProfile_neg hc.1.2.1

/-- The total positive reciprocal-square weight of the arithmetic mean. -/
def reciprocalSquareMass : ℝ := ∑' p : ℕ+, (1 : ℝ) / (p : ℝ) ^ 2

theorem summable_reciprocalSquareWeight :
    Summable (fun p : ℕ+ => (1 : ℝ) / (p : ℝ) ^ 2) :=
  (Real.summable_one_div_nat_pow.2 (by omega : 1 < 2)).subtype _

/-- A telescoping comparison bounds the entire positive arithmetic averaging mass. -/
theorem reciprocalSquareMass_le_two : reciprocalSquareMass ≤ 2 := by
  have hfin : ∀ N : ℕ, (∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) ≤
      2 - 2 / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ N ih =>
      have hn : (0 : ℝ) < N + 1 := by positivity
      have hn2 : (0 : ℝ) < N + 2 := by positivity
      have he : (2 : ℝ) / (N + 1) - 2 / (N + 2) =
          2 / (((N : ℝ) + 1) * (N + 2)) := by field_simp; ring
      have hstep : (1 : ℝ) / ((N : ℝ) + 1)^(2 : ℕ) ≤ 2 / (N + 1) - 2 / (N + 2) := by
        rw [he]
        apply (div_le_div_iff₀ (sq_pos_of_pos hn) (mul_pos hn hn2)).2
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (N : ℝ) + 1 + 1 = N + 2 by ring]
      linarith
  rw [reciprocalSquareMass, tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)^(2 : ℕ))]
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro N
  have h := hfin N
  simp only [Nat.cast_add, Nat.cast_one]
  exact h.trans (sub_le_self _ (by positivity))

/-- Every lower bound on the first profile is constrained by its exact negative arithmetic mean. -/
theorem lowerBound_rightMinimumProfile_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0)
    {b : ℝ} (hb : ∀ p : ℕ, 0 < p → b ≤ rightMinimumProfile s p) :
    b * reciprocalSquareMass ≤ -((star s * (1 - star s))⁻¹).re / 2 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  have hh : Summable (fun p : ℕ+ => rightMinimumProfile s p / (p : ℝ)^(2 : ℕ)) := by
    simpa only [rightMinimumProfile, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using
      summable_minimumProfile_div_weight hs hs1 1
  have hb' : Summable (fun p : ℕ+ => b / (p : ℝ)^(2 : ℕ)) := by
    simpa only [mul_one_div] using summable_reciprocalSquareWeight.mul_left b
  have h := hb'.tsum_le_tsum (fun (p : ℕ+) => div_le_div_of_nonneg_right (hb p p.pos) (by positivity)) hh
  have he : (∑' p : ℕ+, rightMinimumProfile s p / (p : ℝ)^(2 : ℕ)) =
      -((star s * (1 - star s))⁻¹).re / 2 := by
    simpa only [rightMinimumProfile, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using
      tsum_minimumProfile_div_weight_at_zero hs hs' hz 1
  rw [he] at h
  simpa only [reciprocalSquareMass, div_eq_mul_inv, tsum_mul_left, one_mul] using h

/-- An attained minimum in a zero's first arithmetic class obeys the full negative mean constraint. -/
theorem attained_rightMinimum_mean_bound {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s = 0)
    {p : ℕ} (hp : HasNegativeMinimum (rightMinimumProfile s) p) :
    rightMinimumProfile s p * reciprocalSquareMass ≤
      -((star s * (1 - star s))⁻¹).re / 2 :=
  lowerBound_rightMinimumProfile_at_zero hs hs' hz hp.2.2

/-- Critical-line zeros force a finite undershoot of the predicted arithmetic tail boundary. -/
theorem exists_rightMinimumProfile_below_critical_boundary {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ)) (hz : riemannZeta s = 0) :
    ∃ p : ℕ, 0 < p ∧ rightMinimumProfile s p <
      -reciprocalSquareMass / (8 * (s.im ^ 2 + 9 / 4)) := by
  by_contra h
  push Not at h
  have hm := lowerBound_rightMinimumProfile_at_zero (by linarith : 0 < s.re)
    (by linarith : s.re < 1) hz h
  have he : star s * (1 - star s) = ((s.im ^ 2 + 1 / 4 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, hs]
      ring
    · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_im, hs]
      ring
  have he' : ((star s * (1 - star s))⁻¹).re = (1 : ℝ) / (s.im ^ 2 + 1 / 4) := by
    rw [he, ← one_div, Complex.div_ofReal_re, Complex.one_re]
  rw [he'] at hm
  have hS0 : 0 ≤ reciprocalSquareMass := tsum_nonneg (fun _ => by positivity)
  have hS := reciprocalSquareMass_le_two
  have hSS : reciprocalSquareMass ^ 2 ≤ 4 := by nlinarith
  have hx : 0 < s.im ^ 2 + (1 / 4 : ℝ) := by positivity
  have hy : 0 < s.im ^ 2 + (9 / 4 : ℝ) := by positivity
  have hcmp : (1 : ℝ) / (2 * (s.im ^ 2 + 1 / 4)) ≤
      reciprocalSquareMass ^ 2 / (8 * (s.im ^ 2 + 9 / 4)) := by
    have heL : -reciprocalSquareMass / (8 * (s.im ^ 2 + 9 / 4)) * reciprocalSquareMass =
        -(reciprocalSquareMass ^ 2 / (8 * (s.im ^ 2 + 9 / 4))) := by ring
    have heR : -((1 : ℝ) / (s.im ^ 2 + 1 / 4)) / 2 =
        -((1 : ℝ) / (2 * (s.im ^ 2 + 1 / 4))) := by field_simp
    rw [heL, heR] at hm
    exact neg_le_neg_iff.1 hm
  have hcross := (div_le_div_iff₀ (mul_pos (by norm_num) hx)
    (mul_pos (by norm_num) hy)).1 hcmp
  nlinarith [sq_nonneg s.im]

/-- The first profile is the literal signed, modulus-scaled Bernoulli-normalized remainder. -/
theorem rightMinimumProfile_eq (s : ℂ) {p : ℕ} (hp : 0 < p) :
    rightMinimumProfile s p = (p : ℝ) *
      (((μ p : ℂ) * infiniteRemainder s p) / minimumNormalization s).re := by
  have he : minimumBalanceTerm s p =
      (((μ p : ℂ) * infiniteRemainder s p) / minimumNormalization s) / (p : ℂ) := by
    dsimp [minimumBalanceTerm]
    ring
  rw [rightMinimumProfile, minimumProfile, he, Complex.div_natCast_re,
    show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- The two independently defined profiles coincide on the critical line. -/
theorem leftMinimumProfile_eq_right_on_line {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) :
    leftMinimumProfile s = rightMinimumProfile s := by
  have he : 4 * s.re - 1 = 1 := by linarith
  simp only [leftMinimumProfile, rightMinimumProfile, he]

/-- A critical-line exponent has equal arithmetic minimum labels, including nonattainment. -/
theorem arithmeticMinimumClass_labels_eq_on_line {s : ℂ}
    (hs : s.re = (1 / 2 : ℝ)) {ij : ℕ × ℕ} (hc : ArithmeticMinimumClass s ij) :
    ij.1 = ij.2 := by
  obtain ⟨k,hk,hu⟩ := existsUnique_negativeMinimumClass (rightMinimumProfile s)
  have hj := hc.2
  rw [leftMinimumProfile_eq_right_on_line hs] at hj
  exact (hu ij.1 hc.1).trans (hu ij.2 hj).symm

/-- The second profile uses the fourth power of the literal Dirichlet weight's norm. -/
theorem leftMinimumProfile_eq (s : ℂ) {p : ℕ} (hp : 0 < p) :
    leftMinimumProfile s p =
      (((μ p : ℂ) * infiniteRemainder s p) / minimumNormalization s).re /
        ((p : ℝ) * ‖kernel s p‖ ^ 4) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have he : minimumBalanceTerm s p =
      (((μ p : ℂ) * infiniteRemainder s p) / minimumNormalization s) / (p : ℂ) := by
    dsimp [minimumBalanceTerm]
    ring
  have hpow : ‖kernel s p‖ ^ 4 = ((p : ℝ) ^ (4 * s.re))⁻¹ := by
    rw [kernel, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
    have h := Real.rpow_mul hp'.le (-s.re) (4 : ℝ)
    norm_num only [Real.rpow_ofNat] at h
    rw [← h, show -s.re * 4 = -(4 * s.re) by ring, Real.rpow_neg hp'.le]
  rw [leftMinimumProfile, minimumProfile, he, Complex.div_natCast_re, hpow,
    show 4 * s.re - 1 + 1 = 4 * s.re by ring]
  have hpn : (p : ℝ) ^ (4 * s.re) ≠ 0 := (Real.rpow_pos_of_pos hp' _).ne'
  field_simp

end RHTower.DeletionMixedRefinement
