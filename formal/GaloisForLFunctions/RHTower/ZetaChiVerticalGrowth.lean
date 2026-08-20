import GaloisForLFunctions.RHTower.TitchmarshZetaInputs

/-!
# Polynomial growth of the functional-equation factor along a whole vertical line

The corpus bounds `χ` on the strips `-1 ≤ σ ≤ -1/2` and `-1/2 ≤ σ ≤ 1/2`, in both cases only above
ordinate `2`.  Below it the segment is compact and `χ` is continuous there — the archimedean factors
`Γ_ℝ(s)` and `Γ_ℝ(1-s)` miss their pole ladders on the whole strip once `σ ≠ 0` — so the two bounds
combine into a single majorant valid for every ordinate.

This is the form an integral over a full vertical contour edge needs.
-/

open Complex

noncomputable section

namespace RHTower

theorem vertical_ne_neg_two_mul {σ t : ℝ} (hσ0 : σ ≠ 0) (hσlow : -1 ≤ σ) (n : ℕ) :
    ((σ : ℂ) + (t : ℂ) * I) ≠ -(2 * n) := by
  intro hn
  have hre := congrArg Complex.re hn
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.re_ofNat,
    Complex.im_ofNat, Complex.natCast_re, Complex.natCast_im] at hre
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    simp at hre
    exact hσ0 hre
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
    linarith

theorem one_sub_vertical_ne_neg_two_mul {σ t : ℝ} (hσ : σ ≤ 1 / 2) (n : ℕ) :
    (1 - ((σ : ℂ) + (t : ℂ) * I)) ≠ -(2 * n) := by
  intro hn
  have hre := congrArg Complex.re hn
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.natCast_re, Complex.natCast_im] at hre
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem Gammaℝ_vertical_ne_zero {σ t : ℝ} (hσ0 : σ ≠ 0) (hσlow : -1 ≤ σ) :
    Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  rw [Ne, Complex.Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  exact vertical_ne_neg_two_mul hσ0 hσlow n hn

theorem Gammaℝ_one_sub_vertical_ne_zero {σ t : ℝ} (hσ : σ ≤ 1 / 2) :
    Complex.Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I)) ≠ 0 := by
  refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linarith

theorem continuousAt_Gammaℝ_of_ne_poles {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    ContinuousAt Complex.Gammaℝ s := by
  have hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    refine hs m ?_
    have hs2 : s = 2 * (s / 2) := by ring
    calc s = 2 * (s / 2) := hs2
      _ = 2 * (-(m : ℂ)) := by rw [hm]
      _ = -(2 * (m : ℂ)) := by ring
  have hgam : ContinuousAt Complex.Gamma (s / 2) :=
    (Complex.differentiableAt_Gamma (s / 2) hhalf).continuousAt
  have hcomp : ContinuousAt (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have hdiv : ContinuousAt (fun z : ℂ => z / 2) s := by fun_prop
    have hc : ContinuousAt (Complex.Gamma ∘ fun z : ℂ => z / 2) s :=
      ContinuousAt.comp hgam hdiv
    simpa [Function.comp_def] using hc
  have hpow : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    refine ContinuousAt.cpow continuousAt_const (by fun_prop) ?_
    left
    simpa using Real.pi_pos
  have heq : Complex.Gammaℝ
      = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := by
    funext z
    exact Complex.Gammaℝ_def z
  rw [heq]
  exact hpow.mul hcomp

theorem continuousAt_zetaChi_vertical {σ : ℝ} (hσ0 : σ ≠ 0) (hσlow : -1 ≤ σ)
    (hσhigh : σ ≤ 1 / 2) (t : ℝ) :
    ContinuousAt (fun u : ℝ => zetaChi ((σ : ℂ) + (u : ℂ) * I)) t := by
  have hpath : ContinuousAt (fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) t := by fun_prop
  have hpath' : ContinuousAt (fun u : ℝ => 1 - ((σ : ℂ) + (u : ℂ) * I)) t := by fun_prop
  have hnum : ContinuousAt (fun u : ℝ => Complex.Gammaℝ (1 - ((σ : ℂ) + (u : ℂ) * I))) t := by
    have hg : ContinuousAt Complex.Gammaℝ (1 - ((σ : ℂ) + (t : ℂ) * I)) :=
      continuousAt_Gammaℝ_of_ne_poles (fun n => one_sub_vertical_ne_neg_two_mul hσhigh n)
    have hc : ContinuousAt
        (Complex.Gammaℝ ∘ fun u : ℝ => 1 - ((σ : ℂ) + (u : ℂ) * I)) t :=
      ContinuousAt.comp hg hpath'
    simpa [Function.comp_def] using hc
  have hden : ContinuousAt (fun u : ℝ => Complex.Gammaℝ ((σ : ℂ) + (u : ℂ) * I)) t := by
    have hg : ContinuousAt Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * I) :=
      continuousAt_Gammaℝ_of_ne_poles (fun n => vertical_ne_neg_two_mul hσ0 hσlow n)
    have hc : ContinuousAt (Complex.Gammaℝ ∘ fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) t :=
      ContinuousAt.comp hg hpath
    simpa [Function.comp_def] using hc
  have hdiv : ContinuousAt (fun u : ℝ => Complex.Gammaℝ (1 - ((σ : ℂ) + (u : ℂ) * I))
      / Complex.Gammaℝ ((σ : ℂ) + (u : ℂ) * I)) t :=
    hnum.div hden (Gammaℝ_vertical_ne_zero hσ0 hσlow)
  exact hdiv

/-- **Polynomial growth of `χ` along a whole vertical line in `[-1, 1/2]`.** -/
theorem exists_bound_norm_zetaChi_vertical {σ : ℝ} (hσ0 : σ ≠ 0) (hσlow : -1 ≤ σ)
    (hσhigh : σ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ 2 := by
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (fun t _ => (continuousAt_zetaChi_vertical hσ0 hσlow hσhigh t).continuousWithinAt)
  refine ⟨Real.exp 4 + Real.exp 2 + max C₂ 0, by positivity, fun t => ?_⟩
  have hbase : (1 : ℝ) ≤ 1 + |t| := by
    have := abs_nonneg t
    linarith
  have hsq : (1 : ℝ) ≤ (1 + |t|) ^ 2 := one_le_pow₀ hbase
  have hsq0 : (0 : ℝ) ≤ (1 + |t|) ^ 2 := by positivity
  have he4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos _).le
  have he2 : (0 : ℝ) ≤ Real.exp 2 := (Real.exp_pos _).le
  have hmax0 : (0 : ℝ) ≤ max C₂ 0 := le_max_right _ _
  have hlin : (1 : ℝ) + |t| ≤ (1 + |t|) ^ 2 := by nlinarith [hbase]
  rcases le_total 2 |t| with hbig | hsmall
  · rcases le_total σ (-1 / 2) with hleft | hright
    · have h := norm_zetaChi_le_negative_one_strip hσlow hleft hbig
      have hcoef : Real.exp 4 * (1 + |t|) ^ 2
          ≤ (Real.exp 4 + Real.exp 2 + max C₂ 0) * (1 + |t|) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hsq0
      linarith [h, hcoef]
    · have h := norm_zetaChi_le_half_strip (by linarith) hσhigh hbig
      have hstep : Real.exp 2 * (1 + |t|) ≤ Real.exp 2 * (1 + |t|) ^ 2 :=
        mul_le_mul_of_nonneg_left hlin he2
      have hcoef : Real.exp 2 * (1 + |t|) ^ 2
          ≤ (Real.exp 4 + Real.exp 2 + max C₂ 0) * (1 + |t|) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hsq0
      linarith [h, hstep, hcoef]
  · have hmem : t ∈ Set.Icc (-2 : ℝ) 2 := by
      rw [Set.mem_Icc, ← abs_le]
      exact hsmall
    have h := hC₂ t hmem
    have h' : ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max C₂ 0 := le_trans h (le_max_left _ _)
    have hcoef : max C₂ 0 * 1 ≤ (Real.exp 4 + Real.exp 2 + max C₂ 0) * (1 + |t|) ^ 2 := by
      have h1 : max C₂ 0 ≤ Real.exp 4 + Real.exp 2 + max C₂ 0 := by linarith
      calc max C₂ 0 * 1 ≤ max C₂ 0 * (1 + |t|) ^ 2 := mul_le_mul_of_nonneg_left hsq hmax0
        _ ≤ (Real.exp 4 + Real.exp 2 + max C₂ 0) * (1 + |t|) ^ 2 :=
            mul_le_mul_of_nonneg_right h1 hsq0
    linarith [h', hcoef]

end RHTower

end
