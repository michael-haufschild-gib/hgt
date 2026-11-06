import GaloisForLFunctions.VerifiedHeightRungs.JensenEntries
import GaloisForLFunctions.VerifiedHeightRungs.SeparatedNodesControlTheTransform
import GaloisForLFunctions.VerifiedHeightRungs.TheNormalizedSmoothingKeepsThePoles
import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary

/-!
# Window positivity from verified zeros

**Theorem** (`windowPositiveAt_of_rhVerifiedThrough`). For every `a` there is an explicit height `windowHeight a` such
that RH through it makes the Weil form of `ζ` nonnegative on every test supported in `[−a, a]`.

Write `W(f, f) = κ⁻¹ W(f, g) + ∫ |h_f|² (1 − q²/κ)(μ + P_X)`, `g = f ⋆ w_b ⋆ w_b`, with the normalization `κ = q(i/2)²` that
preserves the pole terms. Three facts close it.

* **Symbol side.** `1 − q²/κ ≥ ϖ ≍ b²`, and the symbol is at least `1` above `T₁ = 4e^{E+2π}`. So the integral is at least
  `2π ϖ ∫|f|²`, minus `D ≍ b²` times the mass of `h_f` on `|τ| ≤ T₁`.
* **Zero side.** The summand of `W(f, g)` at an on-line zero is `m |h_f(γ)|² q(γ)² ≥ 0`, and the zeros above the verified
  height carry `q² ≲ b⁻⁶ |γ|⁻⁴`: a tail as small as we like.
* **Sampling.** Verified zeros have no gap of length `σ = 48⁻⁴/(9a)` at large height, so there are nodes at which
  Lagrange interpolation controls `h_f` on `|τ| ≤ T₁`, up to `48^{−2n}`. The node terms of the zero side pay `D ·` mass.

Choosing `n` from `T₁` and then `b` from `n`, the mass pays itself; the height comes last.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-- On-line zeros from a verified height, in the carrier of `ζ`. -/
theorem re_eq_half_of_mem_carrier {T : ℝ} (hRH : RHVerifiedThrough T) {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier)
    (hT : |ρ.im| ≤ T) : ρ.re = 1 / 2 := by
  have hxi : xi ρ = 0 := (xi_eq_zero_iff hρ.2.1 (by
    intro he
    have hh := hρ.2.2
    rw [he] at hh
    norm_num at hh)).mpr hρ.1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have h := im_xiSpectralPoint_eq_zero hRH q (by rw [re_xiSpectralPoint, hq]; exact hT)
  rw [im_xiSpectralPoint, hq] at h
  linarith only [h]

/-- **The zero side.** Above the verified height the summands are a tail; below they are nonnegative and at least half of
`|h_f(γ)|²` on a chosen finite set of zeros. -/
theorem re_W_smoothed_ge_of_verified {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Set.Icc (-a) a) (hT : 0 ≤ T) (hRH : RHVerifiedThrough T)
    (S : Finset zetaZeroConfig.carrier)
    (hS : ∀ ρ ∈ S, |(ρ : ℂ).im| ≤ T ∧ 2 * (b * (ρ : ℂ).im) ^ 2 ≤ 1) :
    1 / 2 * ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 -
        Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) * (24 * 240 * Real.log 3 / (1 + T)) ≤
      (zetaZeroConfig.W f (smoothedTest b f)).re := by
  classical
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hfs' : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))
  obtain ⟨K, hK⟩ : ∃ K, K = Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) := ⟨_, rfl⟩
  rw [← hK]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  let u : zetaZeroConfig.carrier → ℝ := fun ρ =>
    if ρ ∈ S then 1 / 2 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 else 0
  have hterm (ρ : zetaZeroConfig.carrier) : u ρ - K * highTailErr zetaZeroConfig T ρ ≤
      (zetaZeroConfig.Wsummand f (smoothedTest b f) ρ).re := by
    by_cases hρT : |(ρ : ℂ).im| ≤ T
    · have hre := re_eq_half_of_mem_carrier hRH ρ.2 hρT
      have hgam : gammaOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [WeilEF.gammaOf_re]
        · simp [WeilEF.gammaOf_im, hre]
      obtain ⟨r, hr, hr0, hr1⟩ := kernelQ_real hb hb1 (ρ : ℂ).im
      rw [highTailErr, if_pos hρT, mul_zero, sub_zero, Wsummand_smoothedTest zetaZeroConfig hb.le hf.continuous hfc,
        hgam, Complex.conj_ofReal, hr]
      have hval : ((zetaZeroConfig.mult ρ : ℕ) : ℂ) * (paperFT f ((ρ : ℂ).im : ℝ) *
          conj (paperFT f ((ρ : ℂ).im : ℝ)) * (r : ℂ) ^ 2) =
          (((zetaZeroConfig.mult ρ : ℕ) * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 * r ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj']
        push_cast
        ring
      rw [hval, Complex.ofReal_re]
      have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult ρ := by
        exact_mod_cast zetaZeroConfig.one_le_mult ρ ρ.2
      have hN := sq_nonneg ‖paperFT f ((ρ : ℂ).im : ℝ)‖
      by_cases hρS : ρ ∈ S
      · have hu : u ρ = 1 / 2 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 := if_pos hρS
        rw [hu]
        have h2 := (hS ρ hρS).2
        have hr2 : 1 / 2 ≤ r ^ 2 := by linarith only [hr1, h2]
        calc
          1 / 2 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 ≤ 1 * ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 * r ^ 2 := by
            nlinarith only [mul_le_mul_of_nonneg_left hr2 hN]
          _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg r)
            exact mul_le_mul_of_nonneg_right hm1 hN
      · have hu : u ρ = 0 := if_neg hρS
        rw [hu]
        positivity
    · have hρS : ρ ∉ S := fun h => hρT (hS ρ h).1
      have hu : u ρ = 0 := if_neg hρS
      rw [hu, zero_sub, highTailErr, if_neg hρT]
      have h := re_Wsummand_smoothedTest_ge_high zetaZeroConfig ha hb hb1 hf.continuous hfs' ρ.2
      refine le_trans (le_of_eq ?_) h
      rw [hK]
      have hD : (0 : ℝ) < 1 + |(ρ : ℂ).im| := by positivity
      field_simp
  obtain ⟨hs4, t4⟩ := highTailErr_summable_le zetaZeroConfig (A₀ := 240) (by norm_num) zeta_unit_count_le_240 hT
  have hA : HasCompactSupport (smoothedTest b f) := hasCompactSupport_smoothedTest hb.le hfc
  have hAs : tsupport (smoothedTest b f) ⊆ Set.Icc (-(a + 2)) (a + 2) :=
    (tsupport_smoothedTest_subset hb.le hfs).trans
      (Set.Icc_subset_Icc (by linarith only [hb1]) (by linarith only [hb1]))
  have hfA : tsupport f ⊆ Set.Icc (-(a + 2)) (a + 2) :=
    hfs.trans (Set.Icc_subset_Icc (by linarith only) (by linarith only))
  have hW := (W_eq_pole_add_integral_bilinear hf (smoothedTest_contDiff hb.le hf hfc) hfA hAs).1
  have hre := (Complex.hasSum_re hW.hasSum).summable
  have hsumu : Summable u := summable_of_finite_support (S.finite_toSet.subset fun ρ hρ => by
    by_contra hc
    exact hρ (if_neg hc))
  have hle := Summable.tsum_le_tsum hterm (hsumu.sub (hs4.mul_left K)) hre
  rw [hsumu.tsum_sub (hs4.mul_left K), tsum_mul_left] at hle
  have hut : ∑' ρ, u ρ = 1 / 2 * ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 := by
    rw [tsum_eq_sum (s := S) (fun ρ hρ => if_neg hρ), Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ hρ => if_pos hρ
  rw [hut] at hle
  rw [ZeroConfig.W, Complex.re_tsum hW]
  have ht := mul_le_mul_of_nonneg_left t4 hK0
  linarith only [hle, ht]

/-- The final balance, in real variables. -/
theorem window_numeric {κi ϖ b D₀ T₁ K Sn F Tail Wg Wf M R D a q : ℝ} (hκ1 : 1 / 2 ≤ κi) (hκ2 : κi ≤ 1)
    (hϖ : b ^ 2 / 2560 ≤ ϖ) (hzero : 1 / 2 * Sn - Tail ≤ Wg)
    (hself : κi * Wg + ϖ * (2 * π * F) - D * M * (2 * T₁) ≤ Wf) (hD0 : 0 ≤ D) (hD : D ≤ b ^ 2 * D₀) (hD₀ : 0 ≤ D₀)
    (hM : M = K * Sn + R) (hR0 : 0 ≤ R) (hR : R ≤ 4 * a * F * q) (h1 : 8 * T₁ * D₀ * K * b ^ 2 ≤ 1)
    (h2 : 8 * a * T₁ * D₀ * q ≤ π / 2560) (hTail0 : 0 ≤ Tail) (hTail : Tail ≤ π * b ^ 2 / 2560 * F) (hSn : 0 ≤ Sn)
    (hF : 0 ≤ F) (hT₁ : 0 ≤ T₁) (hK : 0 ≤ K) : 0 ≤ Wf := by
  have hπ := Real.pi_pos
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  -- The cost of the low band.
  have hcost : D * M * (2 * T₁) ≤ 1 / 4 * Sn + π * b ^ 2 / 2560 * F := by
    have h3 : D * M * (2 * T₁) ≤ b ^ 2 * D₀ * M * (2 * T₁) := by
      have := mul_le_mul_of_nonneg_right hD hM0
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h4 : M ≤ K * Sn + 4 * a * F * q := by rw [hM]; linarith only [hR]
    have h5 : b ^ 2 * D₀ * M * (2 * T₁) ≤ b ^ 2 * D₀ * (K * Sn + 4 * a * F * q) * (2 * T₁) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have e : b ^ 2 * D₀ * (K * Sn + 4 * a * F * q) * (2 * T₁) =
        (8 * T₁ * D₀ * K * b ^ 2) * (Sn / 4) + (8 * a * T₁ * D₀ * q) * (b ^ 2 * F) := by ring
    have h6 : (8 * T₁ * D₀ * K * b ^ 2) * (Sn / 4) ≤ 1 * (Sn / 4) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h7 : (8 * a * T₁ * D₀ * q) * (b ^ 2 * F) ≤ π / 2560 * (b ^ 2 * F) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    rw [e] at h5
    linarith only [h3, h5, h6, h7]
  -- The node terms of the zero side.
  have hzeroκ : 1 / 4 * Sn - Tail ≤ κi * Wg := by
    have h3 := mul_le_mul_of_nonneg_left hzero (by linarith only [hκ1] : 0 ≤ κi)
    have h4 : κi * Tail ≤ 1 * Tail := mul_le_mul_of_nonneg_right hκ2 hTail0
    have h5 : 1 / 2 * (1 / 2 * Sn) ≤ κi * (1 / 2 * Sn) :=
      mul_le_mul_of_nonneg_right hκ1 (by positivity)
    nlinarith only [h3, h4, h5]
  have hmass : π * b ^ 2 / 1280 * F ≤ ϖ * (2 * π * F) := by
    have := mul_le_mul_of_nonneg_right hϖ (by positivity : 0 ≤ 2 * π * F)
    refine le_trans (le_of_eq ?_) this
    ring
  have e2 : π * b ^ 2 / 1280 * F = 2 * (π * b ^ 2 / 2560 * F) := by ring
  linarith only [hself, hcost, hzeroκ, hmass, hTail, e2]

/-! ## The height -/

/-- The archimedean exponent at aperture `a + 2`. -/
def winE (a : ℝ) : ℝ := horizonExponent (Real.exp (2 * (a + 2)))

/-- The height `T₁` above which the symbol is at least one. -/
def winT₁ (a : ℝ) : ℝ := 4 * Real.exp (winE a + 2 * π)

/-- The constant `D₀ = 1 + (1 + T₁²) E/2π`. -/
def winD₀ (a : ℝ) : ℝ := 1 + (1 + winT₁ a ^ 2) * (winE a / (2 * π))

/-- The number of nodes, minus one. -/
def winN (a : ℝ) : ℕ :=
  ⌈max (max (winT₁ a) (gapHeight (nodeStep a / 2)) / nodeStep a) (8 * a * winT₁ a * winD₀ a * 1000)⌉₊

/-- The Lagrange constant `2 (n+1) 48^{2n}`. -/
def winK (a : ℝ) : ℝ := 2 * ((winN a : ℝ) + 1) * ((48 : ℝ) ^ winN a) ^ 2

/-- The smoothing width. -/
def winB (a : ℝ) : ℝ := 1 / (8 * winT₁ a * winD₀ a * winK a + 6 * ((winN a : ℝ) + 1) * nodeStep a + 1)

/-- The constant of the tail. -/
def winC (a : ℝ) : ℝ :=
  2 * a * Real.exp a * (Real.exp 1 * 400 ^ 2) * (24 * 240 * Real.log 3) * 1000

/-- **The verified height for aperture `a ≥ 1`.** -/
def windowHeightOfOne (a : ℝ) : ℝ :=
  max (3 * ((winN a : ℝ) + 1) * nodeStep a + Real.exp (gapScale (nodeStep a / 2)) + 1) (winC a / winB a ^ 8)

/-- **The verified height.** -/
def windowHeight (a : ℝ) : ℝ := windowHeightOfOne (max a 1)

/-- **Window positivity from verified zeros, for `a ≥ 1`.** -/
theorem re_W_nonneg_of_rhVerifiedThrough {a T : ℝ} (ha : 1 ≤ a) (hT : windowHeightOfOne a ≤ T)
    (hRH : RHVerifiedThrough T) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Set.Icc (-a) a) :
    0 ≤ (zetaZeroConfig.W f f).re := by
  classical
  have ha0 : 0 < a := by linarith only [ha]
  have hπ := Real.pi_pos
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = nodeStep a := ⟨_, rfl⟩
  have hσ : 0 < σ := by rw [hσdef]; exact nodeStep_pos ha0
  have hσ1 : σ ≤ 1 := by
    rw [hσdef, nodeStep, div_le_one (by positivity)]
    nlinarith only [ha]
  obtain ⟨n, hndef⟩ : ∃ n, n = winN a := ⟨_, rfl⟩
  have hE0 : 0 < winE a := horizonExponent_pos _
  have hT₁0 : 0 < winT₁ a := by unfold winT₁; positivity
  have hD₀0 : 0 < winD₀ a := by unfold winD₀; positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- The size of `n`.
  have hn1 : max (winT₁ a) (gapHeight (σ / 2)) ≤ ((n : ℝ) + 1) * σ := by
    have h1 : max (winT₁ a) (gapHeight (nodeStep a / 2)) / nodeStep a ≤ (n : ℝ) := by
      rw [hndef]
      exact (le_max_left _ _).trans (Nat.le_ceil _)
    rw [hσdef]
    rw [div_le_iff₀ (nodeStep_pos ha0)] at h1
    nlinarith only [h1, nodeStep_pos ha0]
  have hn2 : 8 * a * winT₁ a * winD₀ a * 1000 ≤ (n : ℝ) := by
    rw [hndef]
    exact (le_max_right _ _).trans (Nat.le_ceil _)
  -- The width.
  obtain ⟨b, hbdef⟩ : ∃ b, b = winB a := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = winK a := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; unfold winK; positivity
  have hdenpos : 0 < 8 * winT₁ a * winD₀ a * K + 6 * ((n : ℝ) + 1) * σ + 1 := by positivity
  have hbval : b = 1 / (8 * winT₁ a * winD₀ a * K + 6 * ((n : ℝ) + 1) * σ + 1) := by
    rw [hbdef, winB, ← hKdef, ← hndef, ← hσdef]
  have hb : 0 < b := by rw [hbval]; positivity
  have hb1 : b ≤ 1 := by
    rw [hbval, div_le_one hdenpos]
    have : 0 ≤ 8 * winT₁ a * winD₀ a * K + 6 * ((n : ℝ) + 1) * σ := by positivity
    linarith only [this]
  have hbK : b * (8 * winT₁ a * winD₀ a * K) ≤ 1 := by
    rw [hbval, one_div, inv_mul_le_iff₀ hdenpos]
    have : 0 ≤ 6 * ((n : ℝ) + 1) * σ := by positivity
    linarith only [this]
  have hbσ : b * (6 * ((n : ℝ) + 1) * σ) ≤ 1 := by
    rw [hbval, one_div, inv_mul_le_iff₀ hdenpos]
    have : 0 ≤ 8 * winT₁ a * winD₀ a * K := by positivity
    linarith only [this]
  -- The height.
  have hT1 : 3 * ((n : ℝ) + 1) * σ + Real.exp (gapScale (σ / 2)) + 1 ≤ T := by
    refine le_trans ?_ hT
    rw [windowHeightOfOne, ← hndef, ← hσdef]
    exact le_max_left _ _
  have hT2 : winC a / b ^ 8 ≤ T := by
    refine le_trans ?_ hT
    rw [windowHeightOfOne, hbdef]
    exact le_max_right _ _
  have hE1 := Real.exp_pos (gapScale (σ / 2))
  have hT0 : 0 ≤ T := by
    have : 0 ≤ 3 * ((n : ℝ) + 1) * σ := by positivity
    linarith only [hT1, this, hE1]
  -- The nodes.
  have hnode : ∀ j : ℕ, j ∈ Finset.range (n + 1) → ∃ ρ : zetaZeroConfig.carrier,
      ((n : ℝ) + 1 + 2 * j) * σ ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ ((n : ℝ) + 1 + 2 * j + 1) * σ := by
    intro j hj
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    obtain ⟨c, hc⟩ : ∃ c, c = ((n : ℝ) + 1 + 2 * j) * σ + σ / 2 := ⟨_, rfl⟩
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hcup : c ≤ 3 * ((n : ℝ) + 1) * σ := by
      rw [hc]
      nlinarith only [hσ, hjn]
    have hclow : ((n : ℝ) + 1) * σ ≤ c := by
      rw [hc]
      nlinarith only [hσ, hj0]
    have hgap : gapHeight (σ / 2) ≤ |c| := by
      rw [abs_of_nonneg hc0]
      exact (le_max_right _ _).trans (hn1.trans hclow)
    have hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - c| ≤ Real.exp (gapScale (σ / 2)) → ρ.re = 1 / 2 := by
      intro ρ hρ hρc
      refine re_eq_half_of_mem_carrier hRH hρ ?_
      have h1 : |ρ.im| ≤ |ρ.im - c| + |c| := by
        have := abs_sub_abs_le_abs_sub ρ.im c
        linarith only [this]
      rw [abs_of_nonneg hc0] at h1
      linarith only [h1, hρc, hcup, hT1]
    obtain ⟨ρ, hρ, hρc⟩ := exists_zero_near_of_onLine (σ := σ / 2) (by positivity) (by linarith only [hσ1, hσ]) hgap hon
    obtain ⟨h1, h2⟩ := abs_lt.1 hρc
    refine ⟨⟨ρ, hρ⟩, ?_, ?_⟩
    · change _ ≤ ρ.im
      rw [hc] at h1
      linarith only [h1]
    · change ρ.im ≤ _
      rw [hc] at h2
      nlinarith only [h2]
  -- Choose the nodes as a function on `ℕ`.
  have hne : Nonempty zetaZeroConfig.carrier := by
    obtain ⟨ρ, -⟩ := hnode 0 (Finset.mem_range.2 (Nat.succ_pos n))
    exact ⟨ρ⟩
  have hnode' : ∀ j : ℕ, ∃ ρ : zetaZeroConfig.carrier, j ∈ Finset.range (n + 1) →
      ((n : ℝ) + 1 + 2 * j) * σ ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ ((n : ℝ) + 1 + 2 * j + 1) * σ := by
    intro j
    by_cases hj : j ∈ Finset.range (n + 1)
    · obtain ⟨ρ, hρ⟩ := hnode j hj
      exact ⟨ρ, fun _ => hρ⟩
    · exact ⟨hne.some, fun h => absurd h hj⟩
  choose node hnodeP using hnode'
  let v : ℕ → ℝ := fun j => ((node j : ℂ)).im
  have hvP : ∀ j ∈ Finset.range (n + 1), ((n : ℝ) + 1 + 2 * j) * nodeStep a ≤ v j ∧
      v j ≤ ((n : ℝ) + 1 + 2 * j + 1) * nodeStep a := fun j hj => by
    rw [← hσdef]
    exact hnodeP j hj
  have hinj : Set.InjOn node (Finset.range (n + 1) : Finset ℕ) := by
    intro i hi j hj hij
    by_contra hne
    have hvij : v i = v j := by simp only [v, hij]
    have h1 := hvP i hi
    have h2 := hvP j hj
    rw [← hσdef] at h1 h2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h3 : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      nlinarith only [h1.2, h2.1, hvij, h3, hσ]
    · have h3 : (j : ℝ) + 1 ≤ i := by exact_mod_cast hgt
      nlinarith only [h1.1, h2.2, hvij, h3, hσ]
  let S : Finset zetaZeroConfig.carrier := (Finset.range (n + 1)).image node
  have hvnn : ∀ j ∈ Finset.range (n + 1), 0 ≤ v j := fun j hj => by
    have h1 := (hvP j hj).1
    rw [← hσdef] at h1
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact le_trans (by positivity) h1
  have hvup : ∀ j ∈ Finset.range (n + 1), v j ≤ 3 * ((n : ℝ) + 1) * σ := fun j hj => by
    have h1 := (hvP j hj).2
    rw [← hσdef] at h1
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine h1.trans ?_
    nlinarith only [hσ, hjn]
  have hS : ∀ ρ ∈ S, |(ρ : ℂ).im| ≤ T ∧ 2 * (b * (ρ : ℂ).im) ^ 2 ≤ 1 := by
    intro ρ hρ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hρ
    have h0 := hvnn j hj
    have h1 := hvup j hj
    have hvj : ((node j : ℂ)).im = v j := rfl
    rw [hvj, abs_of_nonneg h0]
    constructor
    · have : 0 < Real.exp (gapScale (σ / 2)) := hE1
      linarith only [h1, hT1, this]
    · have h2 : b * v j ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_left h1 hb.le
        nlinarith only [this, hbσ]
      have h3 : 0 ≤ b * v j := mul_nonneg hb.le h0
      nlinarith only [h2, h3]
  -- The pieces.
  have hfc : HasCompactSupport f := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hfs' : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))
  obtain ⟨Sn, hSn⟩ : ∃ Sn, Sn = ∑ j ∈ Finset.range (n + 1), ‖paperFT f (v j)‖ ^ 2 := ⟨_, rfl⟩
  have hSn0 : 0 ≤ Sn := by
    rw [hSn]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSsum : ∑ ρ ∈ S, ‖paperFT f ((ρ : ℂ).im : ℝ)‖ ^ 2 = Sn := by
    rw [hSn, Finset.sum_image hinj]
  obtain ⟨F, hF⟩ : ∃ F, F = ∫ u, ‖f u‖ ^ 2 := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact integral_nonneg fun _ => sq_nonneg _
  have hN : (∫ u, ‖f u‖) ^ 2 ≤ 2 * a * F := by
    rw [hF]
    exact sq_integral_norm_le_of_abs_support hf.continuous ha0.le fun x hx => by
      by_contra h
      exact absurd (hfs' x h) (not_le.mpr hx)
  obtain ⟨r₀, hr1, hr2, hrlow, hrup⟩ := kernelQ_half hb hb1
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hb2' : 0 < b ^ 2 := by positivity
  have hr01 : 1 ≤ r₀ := by linarith only [hrlow, hb2']
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = r₀ ^ 2 := ⟨_, rfl⟩
  have hκ1 : 1 + b ^ 2 / 1280 ≤ κ := by rw [hκ]; nlinarith only [hrlow, hb2']
  have hκ2 : κ ≤ 1 + b ^ 2 := by
    rw [hκ]
    nlinarith only [hrup, hb2, hb2', hr01]
  have hκ0 : 0 < κ := by linarith only [hκ1, hb2']
  have hκle2 : κ ≤ 2 := by linarith only [hκ2, hb2]
  have hκi1 : 1 / 2 ≤ κ⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hκ0 hκle2
  have hκi2 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hκ1, hb2'])
  obtain ⟨ϖ, hϖdef⟩ : ∃ ϖ, ϖ = 1 - κ⁻¹ := ⟨_, rfl⟩
  have hϖeq : ϖ = (κ - 1) * κ⁻¹ := by
    rw [hϖdef]
    field_simp
  have hϖlow : b ^ 2 / 2560 ≤ ϖ := by
    rw [hϖeq]
    have h1 : b ^ 2 / 1280 ≤ κ - 1 := by linarith only [hκ1]
    have := mul_le_mul h1 hκi1 (by norm_num) (by linarith only [h1, hb2'])
    refine le_trans (le_of_eq ?_) this
    ring
  have hϖup : ϖ ≤ b ^ 2 := by
    rw [hϖeq]
    have h1 : κ - 1 ≤ b ^ 2 := by linarith only [hκ2]
    have h0 : 0 ≤ κ - 1 := by linarith only [hκ1, hb2']
    calc
      (κ - 1) * κ⁻¹ ≤ (κ - 1) * 1 := mul_le_mul_of_nonneg_left hκi2 h0
      _ ≤ _ := by linarith only [h1]
  have hϖ0 : 0 ≤ ϖ := by linarith only [hϖlow, hb2']
  -- The low band.
  obtain ⟨R, hRdef⟩ : ∃ R, R = 2 * ((∫ u, ‖f u‖) * ((48 : ℝ) ^ (2 * n))⁻¹) ^ 2 := ⟨_, rfl⟩
  have hKeq : K = 2 * ((n : ℝ) + 1) * ((48 : ℝ) ^ n) ^ 2 := by rw [hKdef, winK, ← hndef]
  have hMb : ∀ τ : ℝ, |τ| ≤ winT₁ a → ‖paperFT f τ‖ ^ 2 ≤ K * Sn + R := by
    intro τ hτ
    have h := norm_sq_paperFT_le_of_nodes ha0 hf.continuous hfc hfs' v hvP (x := τ) (by
      rw [← hσdef]
      exact hτ.trans ((le_max_left _ _).trans hn1))
    rw [hKeq, hSn, hRdef]
    exact h
  have hself := re_W_self_ge ha0.le hb hb1 hf hfs hr1 hr2 hr01 (T₁ := winT₁ a) (M := K * Sn + R) le_rfl hMb
  rw [← hκ, ← hϖdef, ← hF] at hself
  have hzero := re_W_smoothed_ge_of_verified ha0.le hb hb1 hf hfs hT0 hRH S hS
  rw [hSsum] at hzero
  -- The bounds of `window_numeric`.
  have hEdef : horizonExponent (Real.exp (2 * (a + 2))) = winE a := rfl
  rw [hEdef] at hself
  obtain ⟨E', hE'⟩ : ∃ E', E' = winE a / (2 * π) := ⟨_, rfl⟩
  have hE'0 : 0 ≤ E' := by rw [hE']; positivity
  rw [← hE'] at hself
  have hD₀eq : winD₀ a = 1 + (1 + winT₁ a ^ 2) * E' := by rw [winD₀, hE']
  have hD0 : 0 ≤ ϖ + (ϖ + (b * winT₁ a) ^ 2) * E' := by positivity
  have hDle : ϖ + (ϖ + (b * winT₁ a) ^ 2) * E' ≤ b ^ 2 * winD₀ a := by
    rw [hD₀eq]
    have h1 : (ϖ + (b * winT₁ a) ^ 2) * E' ≤ (b ^ 2 + b ^ 2 * winT₁ a ^ 2) * E' :=
      mul_le_mul_of_nonneg_right (by rw [mul_pow]; linarith only [hϖup]) hE'0
    nlinarith only [h1, hϖup]
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = (((48 : ℝ) ^ (2 * n))⁻¹) ^ 2 := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hRle : R ≤ 4 * a * F * q := by
    rw [hRdef, mul_pow, ← hq]
    have := mul_le_mul_of_nonneg_right hN hq0
    nlinarith only [this]
  have h1 : 8 * winT₁ a * winD₀ a * K * b ^ 2 ≤ 1 := by
    have h0 : 0 ≤ 8 * winT₁ a * winD₀ a * K := by positivity
    have : b ^ 2 ≤ b := by nlinarith only [hb, hb1]
    calc
      8 * winT₁ a * winD₀ a * K * b ^ 2 ≤ 8 * winT₁ a * winD₀ a * K * b := mul_le_mul_of_nonneg_left this h0
      _ = b * (8 * winT₁ a * winD₀ a * K) := by ring
      _ ≤ 1 := hbK
  have h2 : 8 * a * winT₁ a * winD₀ a * q ≤ π / 2560 := by
    -- `48^{4n} ≥ n`.
    have hq1 : q * (n : ℝ) ≤ 1 := by
      have hpow : (n : ℝ) ≤ (48 : ℝ) ^ (2 * n) := by
        have h3 := one_add_mul_le_pow (a := (47 : ℝ)) (by norm_num) (2 * n)
        push_cast at h3
        norm_num at h3
        nlinarith only [h3, hn0]
      have hpos : (0 : ℝ) < 48 ^ (2 * n) := by positivity
      have hge1 : (1 : ℝ) ≤ 48 ^ (2 * n) := one_le_pow₀ (by norm_num)
      rw [hq, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
      nlinarith only [hpow, hge1]
    have hpq : (8 * a * winT₁ a * winD₀ a * 1000) * q ≤ (n : ℝ) * q :=
      mul_le_mul_of_nonneg_right hn2 hq0
    have hval : 8 * a * winT₁ a * winD₀ a * q ≤ 1 / 1000 := by
      nlinarith only [hpq, hq1]
    have := Real.pi_gt_three
    linarith only [hval, this]
  -- The tail.
  obtain ⟨Tail, hTaildef⟩ : ∃ Tail, Tail = Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) *
      (24 * 240 * Real.log 3 / (1 + T)) := ⟨_, rfl⟩
  rw [← hTaildef] at hzero
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hTail0 : 0 ≤ Tail := by
    rw [hTaildef]
    positivity
  have hTail : Tail ≤ π * b ^ 2 / 2560 * F := by
    have hT3 : winC a / b ^ 8 ≤ 1 + T := by linarith only [hT2]
    have hb8 : 0 < b ^ 8 := by positivity
    have hC0 : 0 ≤ winC a := by unfold winC; positivity
    rw [div_le_iff₀ hb8] at hT3
    have hTp : 0 < 1 + T := by linarith only [hT0]
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = Real.exp a * (Real.exp 1 * 400 ^ 2) * (24 * 240 * Real.log 3) := ⟨_, rfl⟩
    have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
    have hC : winC a = 2 * a * Z * 1000 := by rw [winC, hZ]; ring
    have e : Tail = (∫ u, ‖f u‖) ^ 2 * Z / (b ^ 6 * (1 + T)) := by
      rw [hTaildef, hZ]
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    have h3 : (∫ u, ‖f u‖) ^ 2 * Z ≤ 2 * a * F * Z := mul_le_mul_of_nonneg_right hN hZ0
    have h4 : π / 2560 ≥ 1 / 1000 := by
      have := Real.pi_gt_three
      linarith only [this]
    have h5 : 2 * a * Z * 1000 * F ≤ (1 + T) * b ^ 8 * F := by
      rw [hC] at hT3
      exact mul_le_mul_of_nonneg_right hT3 hF0
    have h6 : 0 ≤ (1 + T) * b ^ 8 * F := by positivity
    have e2 : π * b ^ 2 / 2560 * F * (b ^ 6 * (1 + T)) = π / 2560 * ((1 + T) * b ^ 8 * F) := by ring
    rw [e2]
    have h7 : 1 / 1000 * ((1 + T) * b ^ 8 * F) ≤ π / 2560 * ((1 + T) * b ^ 8 * F) :=
      mul_le_mul_of_nonneg_right h4 h6
    nlinarith only [h3, h5, h7]
  exact window_numeric (κi := κ⁻¹) (ϖ := ϖ) (b := b) (D₀ := winD₀ a) (T₁ := winT₁ a) (K := K) (Sn := Sn) (F := F)
    (Tail := Tail) (Wg := (zetaZeroConfig.W f (smoothedTest b f)).re) (Wf := (zetaZeroConfig.W f f).re)
    (M := K * Sn + R) (R := R) (D := ϖ + (ϖ + (b * winT₁ a) ^ 2) * E') (a := a) (q := q)
    hκi1 hκi2 hϖlow hzero hself hD0 hDle hD₀0.le rfl hR0 hRle h1 h2 hTail0 hTail hSn0 hF0 hT₁0.le hK0

/-- **Window positivity from verified zeros.** RH through `windowHeight a` makes the Weil form of `ζ` nonnegative on
`[−a, a]`. -/
theorem windowPositiveAt_of_rhVerifiedThrough {a : ℝ} (hRH : RHVerifiedThrough (windowHeight a)) :
    WindowVisibilityLaw.WindowPositiveAt zetaZeroConfig a := fun f hf hfs =>
  re_W_nonneg_of_rhVerifiedThrough (le_max_right a 1) le_rfl hRH hf
    (hfs.trans (Set.Icc_subset_Icc (neg_le_neg (le_max_left a 1)) (le_max_left a 1)))

end

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.windowPositiveAt_of_rhVerifiedThrough
