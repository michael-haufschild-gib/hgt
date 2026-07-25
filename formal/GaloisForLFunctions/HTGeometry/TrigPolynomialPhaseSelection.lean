import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Phase selection in a finite trigonometric polynomial

A finite sum `sum_i c i * exp (-i t lam i)` can be driven, at arbitrarily large `t`, to a value whose
real part is at most `-‖c i₀‖` plus the total modulus of the other coefficients: choose `t` so that
the `i₀` term points along the negative real axis, and bound the rest trivially.

Only one frequency is aligned, so no Kronecker theorem or almost-periodicity is used -- a single
exponential is periodic, and periodicity supplies arbitrarily large `t`.
-/

open Complex
open scoped BigOperators

namespace HTGeometry

theorem exists_int_le_affine {a b T : ℝ} (hb : b ≠ 0) : ∃ k : ℤ, T ≤ a + b * k := by
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · obtain ⟨k, hk⟩ := exists_int_lt ((T - a) / b)
    exact ⟨k, by nlinarith [(lt_div_iff_of_neg hneg).mp hk]⟩
  · obtain ⟨k, hk⟩ := exists_int_gt ((T - a) / b)
    exact ⟨k, by nlinarith [(div_lt_iff₀ hpos).mp hk]⟩

theorem norm_finset_exp_sum_le {ι : Type*} (s : Finset ι) (lam : ι → ℝ) (c : ι → ℂ) (t : ℝ) :
    ‖∑ i ∈ s, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)‖ ≤ ∑ i ∈ s, ‖c i‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The aligning time: a designated nonzero coefficient can be pointed along the negative real axis
at arbitrarily large times. -/
theorem exists_ge_align {c₀ : ℂ} (hc : c₀ ≠ 0) {l : ℝ} (hl : l ≠ 0) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ c₀ * Complex.exp (((-(t * l) : ℝ) : ℂ) * I) = -(‖c₀‖ : ℂ) := by
  set w : ℂ := -(‖c₀‖ : ℂ) / c₀ with hw
  have hcnorm : (0 : ℝ) < ‖c₀‖ := norm_pos_iff.mpr hc
  have hwnorm : ‖w‖ = 1 := by
    rw [hw, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcnorm, div_self (ne_of_gt hcnorm)]
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff w).mp hwnorm
  obtain ⟨k, hk⟩ := exists_int_le_affine (a := -(θ / l)) (b := -(2 * Real.pi / l)) (T := T)
    (by
      have hne : (2 * Real.pi / l) ≠ 0 := div_ne_zero (by positivity) hl
      simpa using hne)
  refine ⟨-(θ / l) + -(2 * Real.pi / l) * k, hk, ?_⟩
  set t : ℝ := -(θ / l) + -(2 * Real.pi / l) * k with ht
  have hval : -(t * l) = θ + 2 * Real.pi * k := by
    rw [ht]; field_simp; ring
  have hphase : Complex.exp (((-(t * l) : ℝ) : ℂ) * I) = w := by
    rw [hval, ← hθ]
    push_cast
    rw [add_mul, Complex.exp_add]
    have hone : Complex.exp ((2 * (Real.pi : ℂ) * (k : ℂ)) * I) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * (k : ℂ)) * I = (k : ℂ) * (2 * (Real.pi : ℂ) * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [hone, mul_one]
  rw [hphase, hw, mul_div_cancel₀ _ hc]

/-- **Phase selection for a conjugate pair.**  When two indices carry opposite frequencies and
conjugate coefficients, aligning one aligns the other, so the pair contributes `-2 ‖c i₀‖`. -/
theorem exists_ge_re_finset_exp_le_pair {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam : ι → ℝ) (c : ι → ℂ) {i₀ i₁ : ι} (hi₀ : i₀ ∈ s) (hi₁ : i₁ ∈ s.erase i₀)
    (hc : c i₀ ≠ 0) (hlam : lam i₀ ≠ 0) (hpair : lam i₁ = -lam i₀)
    (hconj : c i₁ = (starRingEnd ℂ) (c i₀)) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      (∑ i ∈ s, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)).re ≤
        -2 * ‖c i₀‖ + ∑ i ∈ (s.erase i₀).erase i₁, ‖c i‖ := by
  classical
  obtain ⟨t, hT, halign⟩ := exists_ge_align hc hlam T
  refine ⟨t, hT, ?_⟩
  have hconjexp : Complex.exp (((-(t * lam i₁) : ℝ) : ℂ) * I)
      = (starRingEnd ℂ) (Complex.exp (((-(t * lam i₀) : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [hpair]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hterm₁ : c i₁ * Complex.exp (((-(t * lam i₁) : ℝ) : ℂ) * I) = -(‖c i₀‖ : ℂ) := by
    rw [hconj, hconjexp, ← map_mul, halign]
    simp
  have hsplit₀ : (∑ i ∈ s, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)) =
      c i₀ * Complex.exp (((-(t * lam i₀) : ℝ) : ℂ) * I) +
        ∑ i ∈ s.erase i₀, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I) :=
    (Finset.add_sum_erase s _ hi₀).symm
  have hsplit₁ : (∑ i ∈ s.erase i₀, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)) =
      c i₁ * Complex.exp (((-(t * lam i₁) : ℝ) : ℂ) * I) +
        ∑ i ∈ (s.erase i₀).erase i₁, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I) :=
    (Finset.add_sum_erase (s.erase i₀) _ hi₁).symm
  rw [hsplit₀, hsplit₁, halign, hterm₁, Complex.add_re, Complex.add_re]
  have h1 : (-(‖c i₀‖ : ℂ)).re = -‖c i₀‖ := by simp
  have h2 : (∑ i ∈ (s.erase i₀).erase i₁,
      c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)).re ≤
      ∑ i ∈ (s.erase i₀).erase i₁, ‖c i‖ :=
    le_trans (Complex.re_le_norm _) (norm_finset_exp_sum_le _ lam c t)
  rw [h1]
  linarith

/-- **Phase selection.**  At arbitrarily large times the designated term can be made to point along
the negative real axis. -/
theorem exists_ge_re_finset_exp_le {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (lam : ι → ℝ) (c : ι → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ s) (hlam : lam i₀ ≠ 0) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      (∑ i ∈ s, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)).re ≤
        -‖c i₀‖ + ∑ i ∈ s.erase i₀, ‖c i‖ := by
  classical
  by_cases hc : c i₀ = 0
  · refine ⟨T, le_refl _, ?_⟩
    have hsplit : ∑ i ∈ s, ‖c i‖ = ‖c i₀‖ + ∑ i ∈ s.erase i₀, ‖c i‖ :=
      (Finset.add_sum_erase s (fun i => ‖c i‖) hi₀).symm
    have h1 := Complex.re_le_norm (∑ i ∈ s, c i * Complex.exp (((-(T * lam i) : ℝ) : ℂ) * I))
    have h2 := norm_finset_exp_sum_le s lam c T
    have hz : ‖c i₀‖ = 0 := by rw [hc, norm_zero]
    rw [hsplit, hz] at h2
    linarith
  · -- align the `i₀` term with the negative real axis
    set w : ℂ := -(‖c i₀‖ : ℂ) / c i₀ with hw
    have hcnorm : (0 : ℝ) < ‖c i₀‖ := norm_pos_iff.mpr hc
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hcnorm, div_self (ne_of_gt hcnorm)]
    obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff w).mp hwnorm
    obtain ⟨k, hk⟩ := exists_int_le_affine (a := -(θ / lam i₀))
      (b := -(2 * Real.pi / lam i₀)) (T := T)
      (by
        have hne : (2 * Real.pi / lam i₀) ≠ 0 :=
          div_ne_zero (by positivity) hlam
        simpa using hne)
    refine ⟨-(θ / lam i₀) + -(2 * Real.pi / lam i₀) * k, hk, ?_⟩
    set t : ℝ := -(θ / lam i₀) + -(2 * Real.pi / lam i₀) * k with ht
    have hphase : Complex.exp (((-(t * lam i₀) : ℝ) : ℂ) * I) = w := by
      have hval : -(t * lam i₀) = θ + 2 * Real.pi * k := by
        rw [ht]
        field_simp
        ring
      rw [hval, ← hθ]
      push_cast
      rw [add_mul, Complex.exp_add]
      have : Complex.exp ((2 * (Real.pi : ℂ) * (k : ℂ)) * I) = 1 := by
        rw [show (2 * (Real.pi : ℂ) * (k : ℂ)) * I = (k : ℂ) * (2 * (Real.pi : ℂ) * I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I k
      rw [this, mul_one]
    have hterm : c i₀ * Complex.exp (((-(t * lam i₀) : ℝ) : ℂ) * I) = -(‖c i₀‖ : ℂ) := by
      rw [hphase, hw, mul_div_cancel₀ _ hc]
    have hsplit : (∑ i ∈ s, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)) =
        c i₀ * Complex.exp (((-(t * lam i₀) : ℝ) : ℂ) * I) +
          ∑ i ∈ s.erase i₀, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I) :=
      (Finset.add_sum_erase s _ hi₀).symm
    rw [hsplit, hterm, Complex.add_re]
    have h1 : (-(‖c i₀‖ : ℂ)).re = -‖c i₀‖ := by simp
    have h2 : (∑ i ∈ s.erase i₀, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)).re ≤
        ∑ i ∈ s.erase i₀, ‖c i‖ :=
      le_trans (Complex.re_le_norm _) (norm_finset_exp_sum_le _ lam c t)
    rw [h1]
    linarith

/-- **Phase selection for a conjugate pair of frequency classes.**  If the index set splits into a
class at frequency `l`, its mirror class at `-l` whose coefficient sum is the conjugate, and a
remainder, then at arbitrarily large times the two classes together contribute `-2 ‖A‖`, where `A` is
the class coefficient sum. -/
theorem exists_ge_re_sum_exp_le_of_split {ι : Type*} (s sPlus sMinus sr : Finset ι)
    (lam : ι → ℝ) (c : ι → ℂ) {l : ℝ} (hl : l ≠ 0)
    (hsplit : ∀ f : ι → ℂ,
      ∑ i ∈ s, f i = (∑ i ∈ sPlus, f i) + (∑ i ∈ sMinus, f i) + ∑ i ∈ sr, f i)
    (hp : ∀ i ∈ sPlus, lam i = l) (hm : ∀ i ∈ sMinus, lam i = -l)
    (hA : (∑ i ∈ sPlus, c i) ≠ 0)
    (hconj : (∑ i ∈ sMinus, c i) = (starRingEnd ℂ) (∑ i ∈ sPlus, c i)) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      (∑ i ∈ s, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)).re ≤
        -2 * ‖∑ i ∈ sPlus, c i‖ + ∑ i ∈ sr, ‖c i‖ := by
  obtain ⟨t, hT, halign⟩ := exists_ge_align hA hl T
  refine ⟨t, hT, ?_⟩
  set w : ℂ := Complex.exp (((-(t * l) : ℝ) : ℂ) * I) with hwdef
  have hplus : (∑ i ∈ sPlus, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I))
      = (∑ i ∈ sPlus, c i) * w := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [hp i hi]
  have hwconj : Complex.exp (((-(t * (-l)) : ℝ) : ℂ) * I) = (starRingEnd ℂ) w := by
    rw [hwdef, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hminus : (∑ i ∈ sMinus, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I))
      = (starRingEnd ℂ) ((∑ i ∈ sPlus, c i) * w) := by
    have hcong : ∀ i ∈ sMinus, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)
        = c i * Complex.exp (((-(t * (-l)) : ℝ) : ℂ) * I) := by
      intro i hi
      rw [hm i hi]
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, hwconj, hconj, ← map_mul]
  rw [hsplit (fun i => c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)), hplus, hminus, halign,
    map_neg, Complex.conj_ofReal, Complex.add_re, Complex.add_re]
  have h1 : (-((‖∑ i ∈ sPlus, c i‖ : ℝ) : ℂ)).re = -‖∑ i ∈ sPlus, c i‖ := by simp
  have h2 : (∑ i ∈ sr, c i * Complex.exp (((-(t * lam i) : ℝ) : ℂ) * I)).re ≤
      ∑ i ∈ sr, ‖c i‖ :=
    le_trans (Complex.re_le_norm _) (norm_finset_exp_sum_le _ lam c t)
  rw [h1]
  linarith

end HTGeometry
