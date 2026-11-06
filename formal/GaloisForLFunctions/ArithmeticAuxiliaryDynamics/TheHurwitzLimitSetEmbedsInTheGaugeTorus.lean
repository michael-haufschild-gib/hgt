import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.ReturnsAreReturnsOfThePrimes

/-!
# The Hurwitz limit set embeds in the gauge torus

Let vertical translates of `ζ` converge pointwise on the upper quadrant to a function `G`. Reading
Dirichlet coefficients at large `Re s`, every phase converges: `n^{-iτ_j} → ω(n)`. The limit `ω` is a
point of the gauge torus (unitary, completely multiplicative), and on `Re s > 1`
`G(s) = Σ ω(n) n^{-s}`.

So the Hurwitz limit set of `ζ` on the quadrant maps into the gauge torus, and `ω` determines `G` on
`Re s > 1`. Prescribing a limit is the same as prescribing a point of the torus: a limit function
cannot be arbitrary. A return is the fibre over the identity.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The phase of the integer `n` at the shift `t`. -/
def phaseAt (t : ℝ) (n : ℕ) : ℂ := ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))

theorem norm_phaseAt {n : ℕ} (hn : 0 < n) (t : ℝ) : ‖phaseAt t n‖ = 1 := by
  rw [phaseAt, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  simp

/-- The phase is completely multiplicative. -/
theorem phaseAt_mul (t : ℝ) (a b : ℕ) : phaseAt t (a * b) = phaseAt t a * phaseAt t b := by
  rw [phaseAt, phaseAt, phaseAt]
  push_cast
  have h := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
    (Nat.cast_nonneg b : (0 : ℝ) ≤ b) (-((t : ℂ) * I))
  simpa using h

/-- The Dirichlet term against a bounded coefficient. -/
private lemma hasSum_shift_diff {t u : ℝ} {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => zetaTerm s n * (phaseAt t (n + 1) - phaseAt u (n + 1)))
      (riemannZeta (s + (t : ℂ) * I) - riemannZeta (s + (u : ℂ) * I)) := by
  have hre1 : 1 < (s + (t : ℂ) * I).re := by simpa using hs
  have hre2 : 1 < (s + (u : ℂ) * I).re := by simpa using hs
  have h := (hasSum_zetaTerm hre1).sub (hasSum_zetaTerm hre2)
  have hfun : (fun n => zetaTerm s n * (phaseAt t (n + 1) - phaseAt u (n + 1))) =
      fun n => zetaTerm (s + (t : ℂ) * I) n - zetaTerm (s + (u : ℂ) * I) n := by
    funext n
    rw [zetaTerm_add, zetaTerm_add, phaseAt, phaseAt]
    push_cast
    ring
  rw [hfun]
  exact h

/-- **Isolating a coefficient.** For coefficients bounded by `2`, a Dirichlet series with value `X` at
`s`, `Re s ≥ 2`, has its `N`-th term bounded by `X`, the earlier coefficients, and a small tail. -/
theorem norm_coeff_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 2) {s : ℂ} (hs : 2 ≤ s.re) {X : ℂ}
    (hX : HasSum (fun n => zetaTerm s n * a n) X) (N : ℕ) :
    ((N : ℝ) + 1) ^ (-s.re) * ‖a N‖ ≤
      ‖X‖ + ∑ n ∈ Finset.range N, ‖a n‖ + 2 * ((N : ℝ) + 2) ^ (2 - s.re) := by
  have hsummable := hX.summable
  have hsplit := hsummable.sum_add_tsum_nat_add (N + 1)
  rw [hX.tsum_eq, Finset.sum_range_succ] at hsplit
  set Tl := ∑' n, zetaTerm s (n + (N + 1)) * a (n + (N + 1)) with hTl
  have htail : ‖Tl‖ ≤ 2 * ((N : ℝ) + 2) ^ (2 - s.re) := by
    have hbound : ∀ n, ‖zetaTerm s (n + (N + 1)) * a (n + (N + 1))‖ ≤
        2 * ((N : ℝ) + 2) ^ (2 - s.re) * realStep 1 (n + N) := by
      intro n
      have hm : ((n + (N + 1) : ℕ) : ℝ) + 1 = (n : ℝ) + N + 2 := by push_cast; ring
      rw [norm_mul, norm_zetaTerm, hm]
      have hx : (0 : ℝ) < (n : ℝ) + N + 2 := by positivity
      have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      have hle : (N : ℝ) + 2 ≤ (n : ℝ) + N + 2 := by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hsplit' : ((n : ℝ) + N + 2) ^ (-s.re) =
          ((n : ℝ) + N + 2) ^ (2 - s.re) * ((n : ℝ) + N + 2) ^ (-2 : ℝ) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
      have h1 : ((n : ℝ) + N + 2) ^ (2 - s.re) ≤ ((N : ℝ) + 2) ^ (2 - s.re) :=
        Real.rpow_le_rpow_of_nonpos hN2 hle (by linarith)
      have h2 : ((n : ℝ) + N + 2) ^ (-2 : ℝ) ≤ realStep 1 (n + N) := by
        rw [IsProducer.realStep_one, Real.rpow_neg hx.le, Real.rpow_two, ← one_div]
        have hcast : ((n + N : ℕ) : ℝ) = (n : ℝ) + N := by push_cast; ring
        rw [hcast]
        refine one_div_le_one_div_of_le (by positivity) ?_
        nlinarith
      have hR := realStep_nonneg zero_le_one (n + N)
      rw [hsplit']
      calc _ ≤ (((N : ℝ) + 2) ^ (2 - s.re) * realStep 1 (n + N)) * 2 :=
            mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) (ha _) (norm_nonneg _)
              (by positivity)
        _ = _ := by ring
    have hsum : HasSum (fun n => 2 * ((N : ℝ) + 2) ^ (2 - s.re) * realStep 1 (n + N))
        (2 * ((N : ℝ) + 2) ^ (2 - s.re) * ((N : ℝ) + 1) ^ (-(1 : ℝ))) :=
      (hasSum_realStep_shift zero_lt_one N).mul_left _
    have hle := tsum_of_norm_bounded hsum hbound
    have hone : ((N : ℝ) + 1) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith) (by norm_num)
    have hpos : 0 ≤ 2 * ((N : ℝ) + 2) ^ (2 - s.re) := by positivity
    calc ‖Tl‖ ≤ _ := hle
      _ ≤ 2 * ((N : ℝ) + 2) ^ (2 - s.re) * 1 := mul_le_mul_of_nonneg_left hone hpos
      _ = _ := mul_one _
  have hfirst : ‖∑ n ∈ Finset.range N, zetaTerm s n * a n‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_zetaTerm]
    have h1 : ((n : ℝ) + 1) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith) (by linarith)
    calc _ ≤ 1 * ‖a n‖ := by gcongr
      _ = _ := one_mul _
  have hkey : zetaTerm s N * a N = X - ∑ n ∈ Finset.range N, zetaTerm s n * a n - Tl := by
    rw [← hsplit]
    ring
  have hnorm : ‖zetaTerm s N * a N‖ = ((N : ℝ) + 1) ^ (-s.re) * ‖a N‖ := by
    rw [norm_mul, norm_zetaTerm]
  rw [← hnorm, hkey]
  calc _ ≤ ‖X - ∑ n ∈ Finset.range N, zetaTerm s n * a n‖ + ‖Tl‖ := norm_sub_le _ _
    _ ≤ ‖X‖ + ‖∑ n ∈ Finset.range N, zetaTerm s n * a n‖ + ‖Tl‖ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ _ := by linarith

/-- **Limits of translates fix every phase.** If `ζ(s + iτ_j)` converges at every point of the upper
quadrant with `Re s > 1`, every phase `(n + 1)^{-iτ_j}` converges. -/
theorem exists_tendsto_phase {τ : ℕ → ℝ} {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → 0 < s.im →
      Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop (𝓝 (G s))) (N : ℕ) :
    ∃ w : ℂ, Tendsto (fun j => phaseAt (τ j) (N + 1)) atTop (𝓝 w) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    choose! ω hω using ih
    refine cauchySeq_tendsto_of_complete ?_
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hA : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hB : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hratio1 : ((N : ℝ) + 1) / ((N : ℝ) + 2) < 1 := by
      rw [div_lt_one hB]
      linarith
    have hratio0 : 0 ≤ ((N : ℝ) + 1) / ((N : ℝ) + 2) := by positivity
    have hpow := tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hratio1
    have hsmall : ∀ᶠ σ : ℝ in atTop,
        2 * ((N : ℝ) + 2) ^ 2 * (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ σ < ε / 2 := by
      have hlim := hpow.const_mul (2 * ((N : ℝ) + 2) ^ 2)
      rw [mul_zero] at hlim
      exact hlim.eventually (gt_mem_nhds (by positivity))
    obtain ⟨σ, hσ2, hσε⟩ := ((eventually_ge_atTop 2).and hsmall).exists
    set s : ℂ := (σ : ℂ) + I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = 1 := by simp [hs]
    have hF := hG s (by rw [hsre]; linarith) (by rw [hsim]; norm_num)
    have hApow : 0 < ((N : ℝ) + 1) ^ σ := Real.rpow_pos_of_pos hA _
    -- The combined error of one index tends to zero.
    set B : ℕ → ℝ := fun j => ‖riemannZeta (s + (τ j : ℂ) * I) - G s‖ +
      ∑ n ∈ Finset.range N, ‖phaseAt (τ j) (n + 1) - ω n‖ with hBdef
    have hB0 : Tendsto B atTop (𝓝 0) := by
      have h1 : Tendsto (fun j => ‖riemannZeta (s + (τ j : ℂ) * I) - G s‖) atTop (𝓝 0) := by
        have := (hF.sub_const (G s)).norm
        simpa using this
      have h2 : Tendsto (fun j => ∑ n ∈ Finset.range N, ‖phaseAt (τ j) (n + 1) - ω n‖)
          atTop (𝓝 0) := by
        have := tendsto_finset_sum (Finset.range N) fun n hn =>
          ((hω n (Finset.mem_range.mp hn)).sub_const (ω n)).norm
        simpa using this
      have := h1.add h2
      simpa using this
    have hB1 : Tendsto (fun j => ((N : ℝ) + 1) ^ σ * B j) atTop (𝓝 0) := by
      have := hB0.const_mul (((N : ℝ) + 1) ^ σ)
      simpa using this
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (hB1.eventually (gt_mem_nhds (by positivity : 0 < ε / 4)))
    refine ⟨J, fun j hj i hi => ?_⟩
    rw [Complex.dist_eq]
    have hbd : ∀ n, ‖phaseAt (τ j) (n + 1) - phaseAt (τ i) (n + 1)‖ ≤ 2 := by
      intro n
      have h1 := norm_sub_le (phaseAt (τ j) (n + 1)) (phaseAt (τ i) (n + 1))
      rw [norm_phaseAt (Nat.succ_pos n), norm_phaseAt (Nat.succ_pos n)] at h1
      linarith
    have hdec := norm_coeff_le hbd (s := s) (by rw [hsre]; exact hσ2)
      (hasSum_shift_diff (t := τ j) (u := τ i) (by rw [hsre]; linarith)) N
    rw [hsre] at hdec
    have hmul : ((N : ℝ) + 1) ^ σ * (((N : ℝ) + 1) ^ (-σ) *
        ‖phaseAt (τ j) (N + 1) - phaseAt (τ i) (N + 1)‖) =
        ‖phaseAt (τ j) (N + 1) - phaseAt (τ i) (N + 1)‖ := by
      rw [← mul_assoc, ← Real.rpow_add hA, add_neg_cancel, Real.rpow_zero, one_mul]
    have hmain := mul_le_mul_of_nonneg_left hdec hApow.le
    rw [hmul] at hmain
    -- Two-sided comparison through the limits.
    have hF2 : ‖riemannZeta (s + (τ j : ℂ) * I) - riemannZeta (s + (τ i : ℂ) * I)‖ ≤
        ‖riemannZeta (s + (τ j : ℂ) * I) - G s‖ + ‖riemannZeta (s + (τ i : ℂ) * I) - G s‖ := by
      have := norm_sub_le (riemannZeta (s + (τ j : ℂ) * I) - G s)
        (riemannZeta (s + (τ i : ℂ) * I) - G s)
      simpa using this
    have hS2 : ∑ n ∈ Finset.range N, ‖phaseAt (τ j) (n + 1) - phaseAt (τ i) (n + 1)‖ ≤
        ∑ n ∈ Finset.range N, ‖phaseAt (τ j) (n + 1) - ω n‖ +
          ∑ n ∈ Finset.range N, ‖phaseAt (τ i) (n + 1) - ω n‖ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n _ => ?_
      have := norm_sub_le (phaseAt (τ j) (n + 1) - ω n) (phaseAt (τ i) (n + 1) - ω n)
      simpa using this
    have hsumB : ‖riemannZeta (s + (τ j : ℂ) * I) - riemannZeta (s + (τ i : ℂ) * I)‖ +
        ∑ n ∈ Finset.range N, ‖phaseAt (τ j) (n + 1) - phaseAt (τ i) (n + 1)‖ ≤ B j + B i := by
      simp only [hBdef]
      linarith
    have htailid : ((N : ℝ) + 1) ^ σ * (2 * ((N : ℝ) + 2) ^ (2 - σ)) =
        2 * ((N : ℝ) + 2) ^ 2 * (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ σ := by
      rw [Real.div_rpow hA.le hB.le, sub_eq_add_neg, Real.rpow_add hB, Real.rpow_neg hB.le,
        Real.rpow_two]
      ring
    have hj1 := hJ j hj
    have hi1 := hJ i hi
    have hscaled := mul_le_mul_of_nonneg_left hsumB hApow.le
    have hsplitB : ((N : ℝ) + 1) ^ σ * (B j + B i) =
        ((N : ℝ) + 1) ^ σ * B j + ((N : ℝ) + 1) ^ σ * B i := mul_add _ _ _
    rw [mul_add, htailid] at hmain
    linarith

/-- **A Dirichlet series with vanishing values has vanishing coefficients.** -/
theorem coeff_eq_zero_of_hasSum_zero {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 2)
    (h0 : ∀ σ : ℝ, 2 ≤ σ → HasSum (fun n => zetaTerm ((σ : ℂ) + I) n * a n) 0) (N : ℕ) : a N = 0 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hA : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hB : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    have hratio1 : ((N : ℝ) + 1) / ((N : ℝ) + 2) < 1 := by
      rw [div_lt_one hB]
      linarith
    have hratio0 : 0 ≤ ((N : ℝ) + 1) / ((N : ℝ) + 2) := by positivity
    have hpow := tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hratio1
    have hlim : Tendsto (fun σ : ℝ => 2 * ((N : ℝ) + 2) ^ 2 *
        (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ σ) atTop (𝓝 0) := by
      have := hpow.const_mul (2 * ((N : ℝ) + 2) ^ 2)
      simpa using this
    have hbound : ∀ᶠ σ : ℝ in atTop, ‖a N‖ ≤ 2 * ((N : ℝ) + 2) ^ 2 *
        (((N : ℝ) + 1) / ((N : ℝ) + 2)) ^ σ := by
      filter_upwards [eventually_ge_atTop 2] with σ hσ
      have hre : ((σ : ℂ) + I).re = σ := by simp
      have hdec := norm_coeff_le ha (s := (σ : ℂ) + I) (by rw [hre]; exact hσ) (h0 σ hσ) N
      rw [hre, norm_zero, zero_add] at hdec
      have hS : ∑ n ∈ Finset.range N, ‖a n‖ = 0 :=
        Finset.sum_eq_zero fun n hn => by rw [ih n (Finset.mem_range.mp hn), norm_zero]
      rw [hS, zero_add] at hdec
      have hApow : 0 < ((N : ℝ) + 1) ^ σ := Real.rpow_pos_of_pos hA _
      have hmain := mul_le_mul_of_nonneg_left hdec hApow.le
      have hmul : ((N : ℝ) + 1) ^ σ * (((N : ℝ) + 1) ^ (-σ) * ‖a N‖) = ‖a N‖ := by
        rw [← mul_assoc, ← Real.rpow_add hA, add_neg_cancel, Real.rpow_zero, one_mul]
      rw [hmul] at hmain
      refine hmain.trans (le_of_eq ?_)
      rw [Real.div_rpow hA.le hB.le, sub_eq_add_neg, Real.rpow_add hB, Real.rpow_neg hB.le,
        Real.rpow_two]
      ring
    have hle := ge_of_tendsto hlim hbound
    exact norm_le_zero_iff.mp hle

/-- **The Hurwitz limit set embeds in the gauge torus.** If `ζ(s + iτ_j) → G(s)` on the upper quadrant,
then every phase converges, the limit is unitary and completely multiplicative, and
`G(s) = Σ ω(n) n^{-s}` on `Re s > 1`. -/
theorem exists_gauge_point {τ : ℕ → ℝ} {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → 0 < s.im →
      Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop (𝓝 (G s))) :
    ∃ ω : ℕ → ℂ, (∀ n, 0 < n → Tendsto (fun j => phaseAt (τ j) n) atTop (𝓝 (ω n))) ∧
      (∀ n, 0 < n → ‖ω n‖ = 1) ∧ (∀ a b, 0 < a → 0 < b → ω (a * b) = ω a * ω b) ∧
      ∀ s : ℂ, 1 < s.re → 0 < s.im → HasSum (fun n => zetaTerm s n * ω (n + 1)) (G s) := by
  choose w hw using exists_tendsto_phase hG
  refine ⟨fun n => w (n - 1), fun n hn => ?_, fun n hn => ?_, fun a b ha hb => ?_, fun s hs him => ?_⟩
  · have := hw (n - 1)
    rwa [Nat.sub_add_cancel hn] at this
  · have h1 := hw (n - 1)
    rw [Nat.sub_add_cancel hn] at h1
    have h2 := h1.norm
    simp only [norm_phaseAt hn] at h2
    exact (tendsto_nhds_unique h2 tendsto_const_nhds)
  · have hab : 0 < a * b := Nat.mul_pos ha hb
    have h1 := hw (a * b - 1)
    rw [Nat.sub_add_cancel hab] at h1
    have h2 := hw (a - 1)
    rw [Nat.sub_add_cancel ha] at h2
    have h3 := hw (b - 1)
    rw [Nat.sub_add_cancel hb] at h3
    have h4 := h2.mul h3
    simp only [← phaseAt_mul] at h4
    exact tendsto_nhds_unique h1 h4
  · -- Dominated convergence in the phases.
    have hnorm : ∀ n, ‖w n‖ = 1 := by
      intro n
      have h2 := (hw n).norm
      simp only [norm_phaseAt (Nat.succ_pos n)] at h2
      exact tendsto_nhds_unique h2 tendsto_const_nhds
    have hsummable : Summable fun n => zetaTerm s n * w n :=
      Summable.of_norm_bounded (summable_norm_zetaTerm hs) fun n => by
        rw [norm_mul, hnorm, mul_one]
    have hdom := summable_norm_zetaTerm hs
    have hlim : Tendsto (fun j => ∑' n, zetaTerm s n * phaseAt (τ j) (n + 1)) atTop
        (𝓝 (∑' n, zetaTerm s n * w n)) := by
      refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖zetaTerm s n‖) hdom
        (fun n => (hw n).const_mul _) (Eventually.of_forall fun j n => ?_)
      rw [norm_mul, norm_phaseAt (Nat.succ_pos n), mul_one]
    have hval : ∀ j, ∑' n, zetaTerm s n * phaseAt (τ j) (n + 1) =
        riemannZeta (s + (τ j : ℂ) * I) := by
      intro j
      have hre : 1 < (s + (τ j : ℂ) * I).re := by simpa using hs
      rw [← (hasSum_zetaTerm hre).tsum_eq]
      refine tsum_congr fun n => ?_
      rw [zetaTerm_add, phaseAt]
      push_cast
      rfl
    simp only [hval] at hlim
    have heq := tendsto_nhds_unique (hG s hs him) hlim
    have hfun : (fun n => zetaTerm s n * w (n + 1 - 1)) = fun n => zetaTerm s n * w n := by
      funext n
      rw [Nat.add_sub_cancel]
    simp only [hfun]
    rw [heq]
    exact hsummable.hasSum

/-- **The fibre over the identity.** If the translates converge to `ζ` on the quadrant `Re s > 1`, then
all phases return. -/
theorem tendsto_phase_one_of_limit_zeta {τ : ℕ → ℝ}
    (hG : ∀ s : ℂ, 1 < s.re → 0 < s.im →
      Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop (𝓝 (riemannZeta s))) {n : ℕ}
    (hn : 0 < n) : Tendsto (fun j => phaseAt (τ j) n) atTop (𝓝 1) := by
  obtain ⟨ω, hlim, hnorm, _, hsum⟩ := exists_gauge_point hG
  have hω : ∀ N, ω (N + 1) - 1 = 0 := by
    refine coeff_eq_zero_of_hasSum_zero (a := fun N => ω (N + 1) - 1) (fun N => ?_) (fun σ hσ => ?_)
    · have h1 := norm_sub_le (ω (N + 1)) 1
      rw [hnorm _ (Nat.succ_pos N), norm_one] at h1
      linarith
    · have hre : 1 < ((σ : ℂ) + I).re := by simp; linarith
      have him : 0 < ((σ : ℂ) + I).im := by simp
      have h1 := (hsum _ hre him).sub (hasSum_zetaTerm hre)
      rw [sub_self] at h1
      have hfun : (fun n => zetaTerm ((σ : ℂ) + I) n * (ω (n + 1) - 1)) = fun n =>
          zetaTerm ((σ : ℂ) + I) n * ω (n + 1) - zetaTerm ((σ : ℂ) + I) n := by
        funext n
        ring
      rw [hfun]
      exact h1
  have hval : ω n = 1 := by
    have h1 := hω (n - 1)
    rw [Nat.sub_add_cancel hn] at h1
    exact sub_eq_zero.mp h1
  rw [← hval]
  exact hlim n hn

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
