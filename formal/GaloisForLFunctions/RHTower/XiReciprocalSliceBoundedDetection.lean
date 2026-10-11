import GaloisForLFunctions.RHTower.XiSliceBoundedDetectionOrder
import GaloisForLFunctions.HTGeometry.TaylorFiniteOrderPositiveAxisBound
import GaloisForLFunctions.RHTower.XiReciprocalSliceOffLineDominance

/-!
# Bounded detection order on the reciprocal slice

At the ordinate `γ` of a zero `ρ` of `ξ` off the critical line, with displacement
`δ = |Re ρ − ½| > 0` and `Ξ(γ) ≠ 0`, the pair product `h_γ(σ) = Ξ(γ+σ)Ξ(γ−σ)` contains the own
factor `(1 + σ²/δ²)^m`, from the copies at `γ ∓ iδ`.  This factor is smaller on the imaginary
axis than on the real axis: `3/4` at `σ = iδ/2` against `5/4` at `σ = δ/2`.  The other zeros, at
distance `≥ 2δ` with inverse-square mass `S`, perturb each value by at most `e^{O(δ²S)}`.

Nonnegative reciprocal coefficients of order `< N` would force `|1/h(iδ/2)| ≤ 1/h(δ/2) + 2·tail`
(`HTGeometry.norm_le_re_add_two_mul_tail_of_taylor_nonneg_lt`).

**Theorem** (`exists_not_nonneg_iteratedDeriv_inv_xiHorizontalPair_of_offLine`).  If

  `(4/5) e^{δ²S/2} + 6 (16/7)^m e^{9δ²S/8} (2/3)^N < (4/3) e^{−δ²S/4}`,

then some Taylor coefficient of `1/h_γ` of order `< N` is not a nonnegative real.

With `δ²S` small and `m = 2` this gives detection below order `11`, uniformly in height.  The
direct-slice detection (`exists_re_xiSliceCoeff_neg_of_offLine_mass`) works for every `δ²S`.  The
reciprocal version needs the own pair to dominate (`δ²S < 4 log(5/3)/3 · m`), matching the
nearest-zero law: reciprocal positivity is lost exactly when an off-line zero is the nearest one.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Bounded detection order on the reciprocal slice.** -/
theorem exists_not_nonneg_iteratedDeriv_inv_xiHorizontalPair_of_offLine {ρ : ℂ} (hρ : xi ρ = 0)
    (hne : ρ.re ≠ 1 / 2) (hΞ : XiC ρ.im ≠ 0) {m : ℕ}
    (hown : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) → F.card ≤ m)
    (hfar : ∀ q : XiZeroCopy, ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I) →
        2 * |ρ.re - 1 / 2| ≤ ‖xiSpectralPoint q - ρ.im‖)
    {S : ℝ} (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F,
        ¬ (xiSpectralPoint q = (ρ.im : ℂ) + (|ρ.re - 1 / 2| : ℝ) * I ∨
          xiSpectralPoint q = (ρ.im : ℂ) - (|ρ.re - 1 / 2| : ℝ) * I)) →
      ∑ q ∈ F, 1 / ‖xiSpectralPoint q - ρ.im‖ ^ 2 ≤ S)
    {N : ℕ} (hN : 4 / 5 * Real.exp (|ρ.re - 1 / 2| ^ 2 * S / 2) +
        6 * (16 / 7) ^ m * Real.exp (9 * |ρ.re - 1 / 2| ^ 2 * S / 8) * (2 / 3) ^ N <
      4 / 3 * Real.exp (-(|ρ.re - 1 / 2| ^ 2 * S / 4))) :
    ∃ n < N, ¬ 0 ≤ iteratedDeriv n (fun σ => (xiHorizontalPair ρ.im σ)⁻¹) 0 := by
  classical
  set t : ℝ := ρ.im with htdef
  set δ : ℝ := |ρ.re - 1 / 2| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hne)
  set own : XiZeroCopy → Prop := fun q =>
    xiSpectralPoint q = (t : ℂ) + (δ : ℂ) * I ∨ xiSpectralPoint q = (t : ℂ) - (δ : ℂ) * I
    with hown_def
  set h : ℂ → ℂ := xiHorizontalPair t with hh
  -- `h(0) = Ξ(t)²` is a positive real
  have hreal : (XiC (t : ℂ)).im = 0 := by
    have hc := XiC_conj (t : ℂ)
    rw [Complex.conj_ofReal] at hc
    have := congrArg Complex.im hc
    simp only [Complex.conj_im] at this
    linarith
  have hre0 : (XiC (t : ℂ)).re ≠ 0 := by
    intro h0; apply hΞ; exact Complex.ext (by simp [h0]) (by simp [hreal])
  set c0 : ℝ := (XiC (t : ℂ)).re ^ 2 with hc0
  have hc0pos : 0 < c0 := by positivity
  have hh0 : h 0 = (c0 : ℂ) := xiHorizontalPair_zero_eq_ofReal
  -- an own copy
  obtain ⟨q₀, hq₀⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy ((ρ - 1 / 2) * (-I))).mp (by
    unfold XiC
    have e : (1 / 2 : ℂ) + (ρ - 1 / 2) * -I * I = ρ := by
      have hI : I * I = -1 := I_mul_I
      linear_combination (-(ρ - 1 / 2)) * hI
    rw [e, hρ])
  have hown₀ : own q₀ := by
    have e : (ρ - 1 / 2) * (-I) = (t : ℂ) - ((ρ.re - 1 / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [htdef]
    simp only [hown_def]
    rw [hq₀, e]
    rcases le_or_gt 0 (ρ.re - 1 / 2) with hs | hs
    · right; rw [hδdef, abs_of_nonneg hs]
    · left; rw [hδdef, abs_of_neg hs]; push_cast; ring
  -- the factors
  have hsq_own : ∀ q, own q → (xiSpectralPoint q - t) ^ 2 = -((δ : ℂ) ^ 2) := by
    intro q hq
    rcases hq with e | e <;> rw [e] <;> ring_nf <;> rw [I_sq] <;> ring
  have hc_pos : ∀ q, 0 < ‖xiSpectralPoint q - t‖ := fun q =>
    norm_pos_iff.mpr (sub_ne_zero.mpr (xiSpectralPoint_ne_ofReal hΞ q))
  have hsmall : ∀ q, ¬ own q → ∀ σ : ℂ, ‖σ‖ ≤ 3 * δ / 4 →
      ‖σ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤ ‖σ‖ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) ∧
        ‖σ‖ ^ 2 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) ≤ 1 / 2 := by
    intro q hq σ hσ
    refine ⟨by rw [norm_div, norm_pow, norm_pow]; exact le_of_eq (by ring), ?_⟩
    have h1 := hfar q hq
    have h2 : (2 * δ) ^ 2 ≤ ‖xiSpectralPoint q - t‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : ‖σ‖ ^ 2 ≤ (3 * δ / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hσ 2
    rw [mul_one_div, div_le_iff₀ (by have := hc_pos q; positivity)]
    nlinarith
  -- the finite products and their limits
  have hlim : ∀ σ : ℂ, Tendsto (fun F : Finset XiZeroCopy =>
      ∏ q ∈ F, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2)) atTop (𝓝 (h σ / h 0)) :=
    fun σ => tendsto_prod_one_sub_sq_div hΞ σ
  have hsplit : ∀ (σ : ℂ) (F : Finset XiZeroCopy),
      ‖∏ q ∈ F, (1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2)‖ =
        (∏ q ∈ F with own q, ‖1 + σ ^ 2 / (δ : ℂ) ^ 2‖) *
          ∏ q ∈ F with ¬ own q, ‖1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := by
    intro σ F
    rw [← Finset.prod_filter_mul_prod_filter_not F own, norm_mul, norm_prod, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [hsq_own q (Finset.mem_filter.mp hq).2]
    congr 1
    field_simp
    ring
  have hmass : ∀ F : Finset XiZeroCopy,
      ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2 ≤ S :=
    fun F => hS _ fun q hq => (Finset.mem_filter.mp hq).2
  have hmass_nn : ∀ F : Finset XiZeroCopy,
      0 ≤ ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2 :=
    fun F => Finset.sum_nonneg fun q _ => by positivity
  -- (A) the imaginary point `iδ/2`
  set σ₁ : ℂ := I * ((δ / 2 : ℝ) : ℂ) with hσ₁
  have hσ₁n : ‖σ₁‖ = δ / 2 := by
    rw [hσ₁, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hA : ‖h σ₁ / h 0‖ ≤ 3 / 4 * Real.exp (δ ^ 2 * S / 4) := by
    refine le_of_tendsto (hlim σ₁).norm ?_
    filter_upwards [eventually_ge_atTop {q₀}] with F hF
    have hq₀F : q₀ ∈ F := hF (Finset.mem_singleton_self q₀)
    rw [hsplit]
    have hown_val : ‖1 + σ₁ ^ 2 / (δ : ℂ) ^ 2‖ = 3 / 4 := by
      rw [hσ₁, mul_pow, I_sq]
      have : (1 : ℂ) + -1 * ((δ / 2 : ℝ) : ℂ) ^ 2 / (δ : ℂ) ^ 2 = ((3 / 4 : ℝ) : ℂ) := by
        push_cast; field_simp; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have h1 : ∏ q ∈ F with own q, ‖1 + σ₁ ^ 2 / (δ : ℂ) ^ 2‖ ≤ 3 / 4 := by
      simp only [hown_val, Finset.prod_const]
      have hpos : 1 ≤ (F.filter own).card :=
        Finset.card_pos.mpr ⟨q₀, Finset.mem_filter.mpr ⟨hq₀F, hown₀⟩⟩
      calc (3 / 4 : ℝ) ^ (F.filter own).card ≤ (3 / 4) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hpos
        _ = 3 / 4 := pow_one _
    have h2 : ∏ q ∈ F with ¬ own q, ‖1 - σ₁ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ ≤
        Real.exp (δ ^ 2 * S / 4) := by
      calc ∏ q ∈ F with ¬ own q, ‖1 - σ₁ ^ 2 / (xiSpectralPoint q - t) ^ 2‖
          ≤ ∏ q ∈ F with ¬ own q,
              Real.exp (δ ^ 2 / 4 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)) := by
            refine Finset.prod_le_prod (fun q _ => norm_nonneg _) fun q hq => ?_
            obtain ⟨hb, -⟩ := hsmall q (Finset.mem_filter.mp hq).2 σ₁ (by rw [hσ₁n]; linarith)
            rw [hσ₁n] at hb
            calc ‖1 - σ₁ ^ 2 / (xiSpectralPoint q - t) ^ 2‖
                ≤ ‖(1 : ℂ)‖ + ‖σ₁ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := norm_sub_le _ _
              _ ≤ δ ^ 2 / 4 * (1 / ‖xiSpectralPoint q - t‖ ^ 2) + 1 := by
                  rw [norm_one]; nlinarith
              _ ≤ _ := Real.add_one_le_exp _
        _ = Real.exp (δ ^ 2 / 4 * ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2) := by
            rw [Finset.mul_sum, Real.exp_sum]
        _ ≤ Real.exp (δ ^ 2 * S / 4) := by
            apply Real.exp_le_exp.mpr
            have := mul_le_mul_of_nonneg_left (hmass F) (show 0 ≤ δ ^ 2 / 4 by positivity)
            linarith
    exact mul_le_mul h1 h2 (Finset.prod_nonneg fun q _ => norm_nonneg _) (by norm_num)
  -- (B) the real point `δ/2`
  set σ₂ : ℂ := ((δ / 2 : ℝ) : ℂ) with hσ₂
  have hσ₂n : ‖σ₂‖ = δ / 2 := by
    rw [hσ₂, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hB : 5 / 4 * Real.exp (-(δ ^ 2 * S / 2)) ≤ ‖h σ₂ / h 0‖ := by
    refine ge_of_tendsto (hlim σ₂).norm ?_
    filter_upwards [eventually_ge_atTop {q₀}] with F hF
    have hq₀F : q₀ ∈ F := hF (Finset.mem_singleton_self q₀)
    rw [hsplit]
    have hown_val : ‖1 + σ₂ ^ 2 / (δ : ℂ) ^ 2‖ = 5 / 4 := by
      have : (1 : ℂ) + σ₂ ^ 2 / (δ : ℂ) ^ 2 = ((5 / 4 : ℝ) : ℂ) := by
        rw [hσ₂]; push_cast; field_simp; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have h1 : 5 / 4 ≤ ∏ q ∈ F with own q, ‖1 + σ₂ ^ 2 / (δ : ℂ) ^ 2‖ := by
      simp only [hown_val, Finset.prod_const]
      have hpos : 1 ≤ (F.filter own).card :=
        Finset.card_pos.mpr ⟨q₀, Finset.mem_filter.mpr ⟨hq₀F, hown₀⟩⟩
      calc (5 / 4 : ℝ) = (5 / 4) ^ 1 := (pow_one _).symm
        _ ≤ (5 / 4) ^ (F.filter own).card := pow_le_pow_right₀ (by norm_num) hpos
    have h2 : Real.exp (-(δ ^ 2 * S / 2)) ≤
        ∏ q ∈ F with ¬ own q, ‖1 - σ₂ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := by
      calc Real.exp (-(δ ^ 2 * S / 2))
          ≤ Real.exp (-(2 * (δ ^ 2 / 4 *
              ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2))) := by
            apply Real.exp_le_exp.mpr
            have := mul_le_mul_of_nonneg_left (hmass F) (show 0 ≤ δ ^ 2 / 4 by positivity)
            linarith
        _ = ∏ q ∈ F with ¬ own q,
              Real.exp (-(2 * (δ ^ 2 / 4 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)))) := by
            rw [← Real.exp_sum]; congr 1
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        _ ≤ ∏ q ∈ F with ¬ own q, ‖1 - σ₂ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := by
            refine Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le) fun q hq => ?_
            obtain ⟨hb, hhalf⟩ := hsmall q (Finset.mem_filter.mp hq).2 σ₂
              (by rw [hσ₂n]; linarith)
            rw [hσ₂n] at hb hhalf
            have e : (δ / 2) ^ 2 = δ ^ 2 / 4 := by ring
            rw [e] at hb hhalf
            have hy := exp_neg_two_mul_le_one_sub (by positivity) hhalf
            have h3 := norm_sub_norm_le (1 : ℂ) (σ₂ ^ 2 / (xiSpectralPoint q - t) ^ 2)
            rw [norm_one] at h3
            linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (le_trans (by norm_num) h1)
  -- (C) the circle `‖σ‖ = 3δ/4`
  have hC : ∀ σ ∈ sphere (0 : ℂ) (3 * δ / 4),
      (7 / 16) ^ m * Real.exp (-(9 * δ ^ 2 * S / 8)) ≤ ‖h σ / h 0‖ := by
    intro σ hσ
    have hσn : ‖σ‖ = 3 * δ / 4 := mem_sphere_zero_iff_norm.mp hσ
    refine ge_of_tendsto (hlim σ).norm (Eventually.of_forall fun F => ?_)
    rw [hsplit]
    have h1 : (7 / 16) ^ m ≤ ∏ q ∈ F with own q, ‖1 + σ ^ 2 / (δ : ℂ) ^ 2‖ := by
      have hval : (7 / 16 : ℝ) ≤ ‖1 + σ ^ 2 / (δ : ℂ) ^ 2‖ := by
        have h3 := norm_sub_norm_le (1 : ℂ) (-(σ ^ 2 / (δ : ℂ) ^ 2))
        rw [sub_neg_eq_add, norm_one, norm_neg, norm_div, norm_pow, norm_pow, hσn,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at h3
        have : (3 * δ / 4) ^ 2 / δ ^ 2 = 9 / 16 := by field_simp; ring
        linarith
      calc (7 / 16 : ℝ) ^ m ≤ (7 / 16) ^ (F.filter own).card :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num)
              (hown _ fun q hq => (Finset.mem_filter.mp hq).2)
        _ = ∏ q ∈ F with own q, (7 / 16 : ℝ) := by rw [Finset.prod_const]
        _ ≤ _ := Finset.prod_le_prod (fun q _ => by norm_num) fun q _ => hval
    have h2 : Real.exp (-(9 * δ ^ 2 * S / 8)) ≤
        ∏ q ∈ F with ¬ own q, ‖1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := by
      calc Real.exp (-(9 * δ ^ 2 * S / 8))
          ≤ Real.exp (-(2 * (9 * δ ^ 2 / 16 *
              ∑ q ∈ F with ¬ own q, 1 / ‖xiSpectralPoint q - t‖ ^ 2))) := by
            apply Real.exp_le_exp.mpr
            have := mul_le_mul_of_nonneg_left (hmass F)
              (show 0 ≤ 9 * δ ^ 2 / 16 by positivity)
            linarith
        _ = ∏ q ∈ F with ¬ own q,
              Real.exp (-(2 * (9 * δ ^ 2 / 16 * (1 / ‖xiSpectralPoint q - t‖ ^ 2)))) := by
            rw [← Real.exp_sum]; congr 1
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        _ ≤ ∏ q ∈ F with ¬ own q, ‖1 - σ ^ 2 / (xiSpectralPoint q - t) ^ 2‖ := by
            refine Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le) fun q hq => ?_
            obtain ⟨hb, hhalf⟩ := hsmall q (Finset.mem_filter.mp hq).2 σ hσn.le
            rw [hσn] at hb hhalf
            have e : (3 * δ / 4) ^ 2 = 9 * δ ^ 2 / 16 := by ring
            rw [e] at hb hhalf
            have hy := exp_neg_two_mul_le_one_sub (by positivity) hhalf
            have h3 := norm_sub_norm_le (1 : ℂ) (σ ^ 2 / (xiSpectralPoint q - t) ^ 2)
            rw [norm_one] at h3
            linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (Finset.prod_nonneg fun q _ => norm_nonneg _)
  -- the reciprocal is holomorphic on `‖σ‖ < δ`
  have hne : ∀ σ : ℂ, ‖σ‖ < δ → h σ ≠ 0 := by
    intro σ hσ h0
    rw [hh, xiHorizontalPair, mul_eq_zero] at h0
    have hfar' : ∀ z : ℂ, XiC z = 0 → δ ≤ ‖z - t‖ := by
      intro z hz
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
      rw [← hq]
      by_cases ho : own q
      · rcases ho with e | e <;> rw [e]
        · rw [show (t : ℂ) + (δ : ℂ) * I - t = (δ : ℂ) * I by ring, norm_mul, Complex.norm_I,
            mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
        · rw [show (t : ℂ) - (δ : ℂ) * I - t = -((δ : ℂ) * I) by ring, norm_neg, norm_mul,
            Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      · have := hfar q ho
        linarith
    rcases h0 with h0 | h0
    · have := hfar' _ h0
      rw [show (t : ℂ) + σ - t = σ by ring] at this
      linarith
    · have := hfar' _ h0
      rw [show (t : ℂ) - σ - t = -σ by ring, norm_neg] at this
      linarith
  have hg : DifferentiableOn ℂ (fun σ => (h σ)⁻¹) (ball 0 δ) :=
    (differentiable_xiHorizontalPair t).differentiableOn.inv fun σ hσ =>
      hne σ (by simpa using hσ)
  have hnorm_div : ∀ σ, ‖h σ / h 0‖ = ‖h σ‖ / c0 := by
    intro σ
    rw [norm_div, hh0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0pos]
  -- conclude
  by_contra hall
  push Not at hall
  set M : ℝ := (16 / 7) ^ m * Real.exp (9 * δ ^ 2 * S / 8) / c0 with hM
  have hMb : ∀ σ ∈ sphere (0 : ℂ) (3 * δ / 4), ‖(h σ)⁻¹‖ ≤ M := by
    intro σ hσ
    have h1 := hC σ hσ
    rw [hnorm_div, le_div_iff₀ hc0pos] at h1
    have hpos : 0 < (7 / 16 : ℝ) ^ m * Real.exp (-(9 * δ ^ 2 * S / 8)) * c0 := by positivity
    rw [norm_inv, hM]
    calc ‖h σ‖⁻¹ ≤ ((7 / 16 : ℝ) ^ m * Real.exp (-(9 * δ ^ 2 * S / 8)) * c0)⁻¹ :=
          inv_anti₀ hpos h1
      _ = (16 / 7) ^ m * Real.exp (9 * δ ^ 2 * S / 8) / c0 := by
          rw [Real.exp_neg]; field_simp; rw [← mul_pow]; norm_num
  have hkey := GaloisForLFunctions.HTGeometry.norm_le_re_add_two_mul_tail_of_taylor_nonneg_lt hg
    (ρ := 3 * δ / 4) (by positivity) (by linarith) hMb (r := δ / 2) (by positivity) (by linarith)
    (N := N) hall (z := σ₁) (le_of_eq hσ₁n)
  have hratio : δ / 2 / (3 * δ / 4) = 2 / 3 := by field_simp; ring
  rw [hratio] at hkey
  -- the three values
  have hv1 : 4 / 3 * Real.exp (-(δ ^ 2 * S / 4)) / c0 ≤ ‖(h σ₁)⁻¹‖ := by
    rw [hnorm_div, div_le_iff₀ hc0pos] at hA
    have hpos : 0 < ‖h σ₁‖ := norm_pos_iff.mpr (hne σ₁ (by rw [hσ₁n]; linarith))
    rw [norm_inv, le_inv_comm₀ (by positivity) hpos]
    calc ‖h σ₁‖ ≤ 3 / 4 * Real.exp (δ ^ 2 * S / 4) * c0 := hA
      _ = (4 / 3 * Real.exp (-(δ ^ 2 * S / 4)) / c0)⁻¹ := by
          rw [Real.exp_neg]; field_simp
  have hv2 : ((h σ₂)⁻¹).re ≤ 4 / 5 * Real.exp (δ ^ 2 * S / 2) / c0 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [hnorm_div, le_div_iff₀ hc0pos] at hB
    have hpos : 0 < 5 / 4 * Real.exp (-(δ ^ 2 * S / 2)) * c0 := by positivity
    rw [norm_inv]
    calc ‖h σ₂‖⁻¹ ≤ (5 / 4 * Real.exp (-(δ ^ 2 * S / 2)) * c0)⁻¹ := inv_anti₀ hpos hB
      _ = 4 / 5 * Real.exp (δ ^ 2 * S / 2) / c0 := by rw [Real.exp_neg]; field_simp
  have hcomb : 4 / 3 * Real.exp (-(δ ^ 2 * S / 4)) / c0 ≤
      4 / 5 * Real.exp (δ ^ 2 * S / 2) / c0 +
        2 * (M * (2 / 3) ^ N / (1 - 2 / 3)) := by
    have := hv1.trans hkey
    have e : σ₂ = ((δ / 2 : ℝ) : ℂ) := rfl
    rw [← e] at this
    linarith
  rw [hM] at hcomb
  have e2 : 2 * ((16 / 7) ^ m * Real.exp (9 * δ ^ 2 * S / 8) / c0 * (2 / 3) ^ N / (1 - 2 / 3)) =
      6 * (16 / 7) ^ m * Real.exp (9 * δ ^ 2 * S / 8) * (2 / 3) ^ N / c0 := by
    field_simp; ring
  rw [e2, ← add_div, div_le_div_iff_of_pos_right hc0pos] at hcomb
  linarith

end

end RHTower
