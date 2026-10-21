import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionDiagonal
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62PrincipalGuthMaynardForm
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumMajorant
import GaloisForLFunctions.RHTower.Sieve.LogPolyDyadicSplit
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# Guth–Maynard §6: the pair bounds behind (6.1)

The inputs of the step from `Σ_{t₁,t₂∈W} |A(t₁−t₂)|²` to (6.1), `A(τ) = Σ_{m≠0} ĥ_τ(mN)`:

* the Dirichlet head of Lemma 6.2 is a Heath-Brown polynomial with a phase-twisted coefficient,
  `‖Σ_{m≤M} m^{−i(τ+u)}‖ = ‖Σ_{m≤M} m^{iu} m^{iτ}‖`, so by the majorant principle
  `hbPairSum_le_of_norm_le` the common shift `u` costs nothing:
  `Σ_{t₁,t₂} ‖Σ_{m≤M} m^{−i(t₁−t₂+u)}‖² ≤ Σ_{t₁,t₂} ‖Σ_{m≤M} m^{i(t₁−t₂)}‖²`;
* the dyadic split of `[1, M]` costs the factor `⌊log₂ M⌋ + 1` (corpus `LogPolyDyadicSplit`);
* Lemma 4.3 gives `|A(τ)| ≤ 2(1+Z) A_j (1+|τ|)^j / N^j` (frequencies `|m| ≥ 1` all decay);
* squaring Lemma 6.2 with Cauchy–Schwarz in `u`:
  `|A|² ≤ 2C² |τ|^{−1} (2U) ∫_{−U}^{U} |D(τ+u)|² du + 2C² T^{−200}`.
-/

set_option autoImplicit false

open Complex Finset
open scoped FourierTransform ComplexConjugate

noncomputable section

namespace RHTower.GuthMaynard

open Sieve

/-- `Σ_{m≤M} m^{−iτ}` is the Heath-Brown polynomial with unit coefficients at `−τ`. -/
theorem cglGMHeadPoly_eq_hbPoly (M : ℕ) (τ : ℝ) :
    cglGMHeadPoly M τ = hbPoly (Finset.Icc 1 M) (fun _ => 1) (-τ) := by
  rw [cglGMHeadPoly, dirPoly_eq_hbPoly]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n - 1 < M := by
    have := Finset.mem_Icc.mp hn
    omega
  dsimp only
  rw [dif_pos hn']

/-- `n^{−is} = conj n^{is}`. -/
theorem hbPhase_neg (n : ℕ) (s : ℝ) : hbPhase n (-s) = conj (hbPhase n s) := by
  rw [hbPhase, hbPhase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- `‖Σ_{m≤M} m^{−i(τ+u)}‖ = ‖Σ_{m≤M} m^{iu} m^{iτ}‖`. -/
theorem norm_cglGMHeadPoly_add (M : ℕ) (τ u : ℝ) :
    ‖cglGMHeadPoly M (τ + u)‖ =
      ‖hbPoly (Finset.Icc 1 M) (fun m => hbPhase m u) τ‖ := by
  rw [cglGMHeadPoly_eq_hbPoly]
  have hconj : hbPoly (Finset.Icc 1 M) (fun _ => 1) (-(τ + u)) =
      conj (hbPoly (Finset.Icc 1 M) (fun m => hbPhase m u) τ) := by
    rw [hbPoly, hbPoly, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [one_mul, hbPhase_neg, map_mul, hbPhase_add, map_mul, mul_comm]
  rw [hconj, RCLike.norm_conj]

/-- **The shift `u` costs nothing.**
`Σ_{t₁,t₂∈W} ‖Σ_{m≤M} m^{−i(t₁−t₂+u)}‖² ≤ Σ_{t₁,t₂∈W} ‖Σ_{m≤M} m^{i(t₁−t₂)}‖²`. -/
theorem sum_normSq_head_le_hbPairSum (M : ℕ) (W : Finset ℝ) (u : ℝ) :
    ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly M (x - y + u)‖ ^ 2 ≤
      hbPairSum W (Finset.Icc 1 M) (fun _ => ((1 : ℝ) : ℂ)) := by
  have hrw : ∑ x ∈ W, ∑ y ∈ W, ‖cglGMHeadPoly M (x - y + u)‖ ^ 2 =
      hbPairSum W (Finset.Icc 1 M) (fun m => hbPhase m u) := by
    unfold hbPairSum
    simp_rw [norm_cglGMHeadPoly_add]
  rw [hrw]
  exact hbPairSum_le_of_norm_le W (b := fun _ => 1) fun n _ => (norm_hbPhase n u).le

/-- The Heath-Brown polynomial is the corpus `logPoly` at frequency `t/2π`. -/
theorem hbPoly_eq_logPoly (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    hbPoly S a t = logPoly a S (t / (2 * Real.pi)) := by
  unfold hbPoly logPoly hbPhase
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 3
  field_simp

/-- **The dyadic split of `[1, M]`.**
`Σ_{t₁,t₂} ‖Σ_{m≤M} m^{iτ}‖² ≤ (⌊log₂ M⌋+1) Σ_j Σ_{t₁,t₂} ‖Σ_{m ∈ block j} m^{iτ}‖²`. -/
theorem hbPairSum_Icc_le_dyadicBlocks (W : Finset ℝ) (M : ℕ) (a : ℕ → ℂ) :
    hbPairSum W (Finset.Icc 1 M) a ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (Nat.log 2 M + 1), hbPairSum W (dyadicSegmentBlock M j) a := by
  unfold hbPairSum
  have hpt : ∀ x ∈ W, ∀ y ∈ W, ‖hbPoly (Finset.Icc 1 M) a (x - y)‖ ^ 2 ≤
      ((Nat.log 2 M + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (Nat.log 2 M + 1),
        ‖hbPoly (dyadicSegmentBlock M j) a (x - y)‖ ^ 2 := by
    intro x _ y _
    simp_rw [hbPoly_eq_logPoly]
    exact_mod_cast normSq_logPoly_Icc_le_card_mul_sum_blocks a M ((x - y) / (2 * Real.pi))
  calc ∑ x ∈ W, ∑ y ∈ W, ‖hbPoly (Finset.Icc 1 M) a (x - y)‖ ^ 2
      ≤ ∑ x ∈ W, ∑ y ∈ W, ((Nat.log 2 M + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (Nat.log 2 M + 1),
          ‖hbPoly (dyadicSegmentBlock M j) a (x - y)‖ ^ 2 :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = _ := by
        simp_rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
        exact Finset.sum_comm

/-- **Lemma 4.3 for `A`.** For `N ≥ 1`, `j ≥ 2`:
`|Σ_{m≠0} ĥ_τ(mN)| ≤ 2(1+Z) A_j (1+|τ|)^j / N^j`. -/
theorem norm_gmNonzero_le_decay (w : CGLRealSmoothBump) {N : ℝ} (hN : 1 ≤ N) {j : ℕ}
    (hj : 2 ≤ j) (τ : ℝ) :
    ‖gmNonzero w N τ‖ ≤ 2 * (1 + cglGMInverseSquareMass) *
      (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump j / (2 * Real.pi) ^ j *
        (1 + |τ|) ^ j / N ^ j) := by
  have hN0 : 0 < N := by linarith
  set X : ℝ := cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump j / (2 * Real.pi) ^ j *
    (1 + |τ|) ^ j / N ^ j with hX
  set f : ℤ → ℂ := fun m => 𝓕 (cglSmoothBumpHt w.toCGLSmoothBump τ : ℝ → ℂ) ((m : ℝ) * N)
    with hf
  have hsplit := tsum_puncturedFrequency_eq_sum_add_tail f
    (summable_fourier_cglSmoothBumpHt_int w.toCGLSmoothBump τ N hN0) 1
  have htail := norm_frequencyTail_le w.toCGLSmoothBump τ N hN0 le_rfl hj
  simp only [Int.cast_neg, neg_mul] at htail
  have hpm : ∀ s : ℝ, |s| = 1 → ‖𝓕 (cglSmoothBumpHt w.toCGLSmoothBump τ : ℝ → ℂ) (s * N)‖ ≤ X := by
    intro s hs
    have hsN : |s * N| = N := by rw [abs_mul, hs, one_mul, abs_of_pos hN0]
    have h := norm_fourier_cglSmoothBumpHt_le_div w.toCGLSmoothBump j τ (ξ := s * N)
      (by rw [← abs_pos, hsN]; exact hN0)
    rwa [hsN] at h
  have htailX : cglGMFrequencyTailWeight w.toCGLSmoothBump j τ N 1 = 2 * X *
      cglGMInverseSquareMass := by
    simp [cglGMFrequencyTailWeight, hX]
  unfold gmNonzero cglGMNonzeroModeSum
  change ‖∑' m : CGLProposition51PuncturedFrequency, f m‖ ≤ _
  rw [hsplit, Finset.Icc_self, Finset.sum_singleton]
  have h1 := hpm 1 (by simp)
  have h2 := hpm (-1) (by simp)
  simp only [one_mul, neg_mul] at h1 h2
  calc _ ≤ ‖f ((1 : ℕ) : ℤ)‖ + ‖f (-((1 : ℕ) : ℤ))‖ +
        ‖∑' k : ℕ, (f ((k + 1 + 1 : ℕ) : ℤ) + f (-((k + 1 + 1 : ℕ) : ℤ)))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ X + X + 2 * X * cglGMInverseSquareMass := by
        simp only [hf, Nat.cast_one, Int.cast_one, one_mul, Int.cast_neg, neg_mul]
        rw [← htailX]
        exact add_le_add (add_le_add h1 h2) htail
    _ = _ := by ring

/-- **Squared Lemma 6.2 with Cauchy–Schwarz in `u`.**  If `a ≤ C r I + C e` with
`I = ∫_{−U}^{U} ‖D‖`, then `a² ≤ 2C² r² (2U) ∫_{−U}^{U} ‖D‖² + 2C² e²`. -/
theorem sq_le_of_lemma62 {D : ℝ → ℂ} (hD : Continuous D) {a C r e U : ℝ} (ha : 0 ≤ a)
    (hU : 0 ≤ U)
    (h : a ≤ C * r * (∫ u in (-U)..U, ‖D u‖) + C * e) :
    a ^ 2 ≤ 2 * C ^ 2 * r ^ 2 * (2 * U * ∫ u in (-U)..U, ‖D u‖ ^ 2) + 2 * C ^ 2 * e ^ 2 := by
  set I : ℝ := ∫ u in (-U)..U, ‖D u‖ with hI
  set J : ℝ := ∫ u in (-U)..U, ‖D u‖ ^ 2 with hJ
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
  have hcs := GaloisForLFunctions.HTGeometry.integral_norm_le_sqrt_length_mul_sqrt_meanSquare hD
    (a := -U) (b := U)
    (by linarith)
  rw [← hI, ← hJ, show U - -U = 2 * U by ring] at hcs
  have hIsq : I ^ 2 ≤ 2 * U * J := by
    have h2 : (Real.sqrt (2 * U) * Real.sqrt J) ^ 2 = 2 * U * J := by
      rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hJ0]
    calc I ^ 2 ≤ (Real.sqrt (2 * U) * Real.sqrt J) ^ 2 := pow_le_pow_left₀ hI0 hcs 2
      _ = 2 * U * J := h2
  have hsq : a ^ 2 ≤ (C * r * I + C * e) ^ 2 := pow_le_pow_left₀ ha h 2
  have hamgm : (C * r * I + C * e) ^ 2 ≤ 2 * (C * r * I) ^ 2 + 2 * (C * e) ^ 2 := by
    nlinarith [sq_nonneg (C * r * I - C * e)]
  have hmain : (C * r * I) ^ 2 ≤ C ^ 2 * r ^ 2 * (2 * U * J) := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left hIsq (by positivity)
  nlinarith [hmain]

end RHTower.GuthMaynard
