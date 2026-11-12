import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.IntegerNormFakeObstructions

/-!
# Integer-norm fakes below exponent one have positive density

**Theorem** (`pos_density_of_integerNormFakeAt_lt_one`).  Every integer-norm fake `B` with count
remainder `|N_B(x) - A x| ≤ C x^β` at an exponent `β < 1` has density `A > 0`.

This extends `pos_density_of_integerNormFakeAt_le_half` from `β ≤ 1/2` to every `β < 1`.

**Proof.**  Suppose `A ≤ 0`.  Then `N_B(x) ≤ C' x^θ`, `θ = max β 0 < 1`, so the Dirichlet series
`Σ a_n n^{-s}` of the norm multiplicities converges absolutely at `σ₁ = (θ + 1)/2 < 1`, and
`(s - 1) ζ_B(s)` vanishes at `s = 1`.  The continuation `G` of `(s - 1) ζ_B(s)` then gives the
holomorphic function `dslope G 1` on `Re s > 1/2`, equal to the Dirichlet series on `Re s > σ₁`.
Landau's theorem (nonnegative coefficients) transfers absolute convergence to every `σ > 1/2`,
where the Euler product makes `ζ_B` zero-free: the fake zero `ρ₀` cannot exist.
-/

open Complex Filter Topology Set
open RHTower RHTower.Sieve RHTower.BeurlingDeletion GaloisForLFunctions.RHTower

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-- Identity theorem on `{Re s > c}`: functions holomorphic there and equal on `{Re s > 1}` are
equal (`c < 1`). -/
theorem eqOn_re_gt_of_eq_on_re_gt_one {c : ℝ} (hc : c < 1) {F₁ F₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ F₁ {s : ℂ | c < s.re})
    (h₂ : DifferentiableOn ℂ F₂ {s : ℂ | c < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → F₁ s = F₂ s) :
    Set.EqOn F₁ F₂ {s : ℂ | c < s.re} := by
  have hU : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {s : ℂ | c < s.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at *
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; linarith
    · have h1 : a * c < a * x.re := mul_lt_mul_of_pos_left hx ha'
      have h2 : b * c ≤ b * y.re := mul_le_mul_of_nonneg_left hy.le hb
      nlinarith
  have hmem : (2 : ℂ) ∈ {s : ℂ | c < s.re} := by simp; linarith
  have hev : F₁ =ᶠ[𝓝 (2 : ℂ)] F₂ := by
    have hU1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact eventuallyEq_of_mem (hU1.mem_nhds (by simp)) fun s hs => heq s hs
  exact (h₁.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (h₂.analyticOnNhd hU)
    hconv.isPreconnected hmem hev

/-- **Positive density of integer-norm fakes.**  An integer-norm fake with count remainder
`O(x^β)`, `β < 1`, has density `A > 0`. -/
theorem pos_density_of_integerNormFakeAt_lt_one {B : BeurlingSystem} {β A C : ℝ}
    (hf : IsIntegerNormFakeAt B β) (hβ : β < 1)
    (hC : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    0 < A := by
  obtain ⟨hInt, hDisc, _, _, G, hGd, hGeq, ρ₀, hρre, hρ1, hG0, _⟩ := hf
  by_contra hAnp
  push Not at hAnp
  set θ : ℝ := max β 0 with hθ
  have hθ0 : 0 ≤ θ := le_max_right _ _
  have hθ1 : θ < 1 := max_lt hβ one_pos
  -- the count is `O(x^θ)`
  have hcnt : ∀ X : ℝ, 1 ≤ X → (B.countBall X : ℝ) ≤ max C 1 * X ^ θ := by
    intro X hX
    have h1 := (le_abs_self _).trans (hC X hX)
    have hAx : A * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAnp (by linarith)
    calc (B.countBall X : ℝ) ≤ (B.countBall X : ℝ) - A * X := by linarith
      _ ≤ C * X ^ β := h1
      _ ≤ max C 1 * X ^ β :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ max C 1 * X ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _))
            (le_trans zero_le_one (le_max_right _ _))
  set a : ℕ → ℂ := fun n => (intCount B hInt n : ℂ) with ha
  set σ₁ : ℝ := (θ + 1) / 2 with hσ₁
  have hσθ : θ < σ₁ := by rw [hσ₁]; linarith
  have hσ1 : σ₁ < 1 := by rw [hσ₁]; linarith
  have hσh : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hsumAt : ∀ σ : ℝ, θ < σ →
      LSeriesSummable a (σ : ℂ) ∧ B.zetaSeriesC (σ : ℂ) = LSeries a (σ : ℂ) := fun σ hσ =>
    zetaSeriesC_eq_LSeries_of_summable hInt hDisc
      (by simpa using summable_intNorm_rpow_of_countBall_le hDisc hθ0 hcnt hσ)
  have hsum1 : LSeriesSummable a (σ₁ : ℂ) := (hsumAt σ₁ hσθ).1
  have habs : LSeries.abscissaOfAbsConv a ≤ (σ₁ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsum1.of_re_le_re (by simp only [Complex.ofReal_re]; exact_mod_cast hy.le)
  have hLd : DifferentiableOn ℂ (LSeries a) {s : ℂ | σ₁ < s.re} :=
    (LSeries_differentiableOn a).mono fun s hs =>
      lt_of_le_of_lt habs (by exact_mod_cast hs)
  have hZL : ∀ s : ℂ, 1 < s.re → B.zetaSeriesC s = LSeries a s := fun s hs =>
    (zetaSeriesC_eq_LSeries_of_summable hInt hDisc
      (summable_intNorm_rpow_of_countBall_le hDisc hθ0 hcnt (by linarith))).2
  have hGd' : DifferentiableOn ℂ G {s : ℂ | σ₁ < s.re} :=
    hGd.mono fun s hs => lt_of_le_of_lt hσh hs
  -- `G = (s - 1) L` on `Re s > σ₁`, so `G(1) = 0`
  have hGL : Set.EqOn G (fun s => (s - 1) * LSeries a s) {s : ℂ | σ₁ < s.re} :=
    eqOn_re_gt_of_eq_on_re_gt_one hσ1 hGd'
      ((differentiableOn_id.sub (differentiableOn_const 1)).mul hLd)
      fun s hs => by rw [hGeq s hs, hZL s hs]
  have hG1 : G 1 = 0 := by
    have h := hGL (show (1 : ℂ) ∈ {s : ℂ | σ₁ < s.re} by simpa using hσ1)
    simpa using h
  -- the removable singularity `F = G/(s - 1)`
  set F : ℂ → ℂ := dslope G 1 with hF
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} :=
    (Complex.differentiableOn_dslope (hU.mem_nhds (by simp; norm_num))).mpr hGd
  have hFval : ∀ s : ℂ, s ≠ 1 → F s = G s / (s - 1) := by
    intro s hs
    rw [hF, dslope_of_ne _ hs, slope_def_field, hG1, sub_zero]
  have hFL : Set.EqOn F (LSeries a) {s : ℂ | σ₁ < s.re} :=
    eqOn_re_gt_of_eq_on_re_gt_one hσ1 (hFd.mono fun s hs => lt_of_le_of_lt hσh hs) hLd
      fun s hs => by
        have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
        rw [hFval s hs1, hGeq s hs, hZL s hs, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)]
  -- Landau: absolute convergence on `Re s > 1/2`
  have hsum : ∀ σ : ℝ, 1 / 2 < σ → LSeriesSummable a (σ : ℂ) := by
    intro σ hσ
    rcases lt_or_ge σ₁ σ with h | h
    · exact hsum1.of_re_le_re (by simp only [Complex.ofReal_re]; exact h.le)
    · have hR0 : 0 ≤ σ₁ + 1 - (σ + 1 / 2) / 2 := by linarith
      set R : NNReal := ⟨σ₁ + 1 - (σ + 1 / 2) / 2, hR0⟩ with hR
      have hRval : (R : ℝ) = σ₁ + 1 - (σ + 1 / 2) / 2 := rfl
      have hcoef : ∀ n, (0 : ℝ) ≤ (intCount B hInt n : ℝ) := fun n => Nat.cast_nonneg _
      have hsum1' : LSeriesSummable (fun n => ((intCount B hInt n : ℝ) : ℂ)) (σ₁ : ℂ) := by
        simpa [ha] using hsum1
      have hball : Metric.closedBall ((σ₁ + 1 : ℝ) : ℂ) (R : ℝ) ⊆ {s : ℂ | 1 / 2 < s.re} := by
        intro z hz
        have hd := Metric.mem_closedBall.mp hz
        have hre : |z.re - (σ₁ + 1)| ≤ dist z ((σ₁ + 1 : ℝ) : ℂ) := by
          rw [Complex.dist_eq]
          have := Complex.abs_re_le_norm (z - ((σ₁ + 1 : ℝ) : ℂ))
          simpa using this
        have := (abs_le.mp (hre.trans hd)).1
        simp only [Set.mem_setOf_eq]
        rw [hRval] at this
        linarith
      have h := landau_summability_transfer (a := fun n => (intCount B hInt n : ℝ)) hcoef hsum1'
        (R := R) (G := F) (hFd.mono hball)
        (fun s hs => by simpa [ha] using hFL hs) (σ := σ) (by rw [hRval]; linarith)
      simpa [ha] using h
  obtain ⟨hZd, hZne⟩ := differentiableOn_and_ne_zero_zetaSeriesC_of_half hInt hDisc hsum
  have hmul : DifferentiableOn ℂ (fun s => (s - 1) * B.zetaSeriesC s) {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_id.sub (differentiableOn_const 1)).mul hZd
  have hid := eqOn_halfPlane_of_eq_on_one hGd hmul hGeq hρre
  rw [hG0] at hid
  exact mul_ne_zero (sub_ne_zero.mpr hρ1) (hZne ρ₀ hρre) hid.symm

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
