import GaloisForLFunctions.RHTower.LindelofOffLineSparse
import GaloisForLFunctions.RHTower.GammaDampedLaurentAtOne
import GaloisForLFunctions.RHTower.XiCosineShiftLaguerrePolya

/-!
# The Lindelöf hypothesis on the critical line implies its half-plane form

**Theorem** (`lindelofHalfPlane_of_criticalLine`). If for every `ε > 0` there is `C` with
`‖ζ(½ + it)‖ ≤ C|t|^ε` for `|t| ≥ 1`, then for every `ε > 0` there is `C' ≥ 1` with
`‖ζ(s)‖ ≤ C'|Im s|^ε` for `Re s ≥ ½`, `|Im s| ≥ 1`.

**Corollaries.** Under the Lindelöf hypothesis in its standard form, off-line zeros are sparse
(`offLineSparse_of_lindelofCriticalLine`). If moreover `(ξ(s+h) + ξ(s−h))/2` has only real zeros,
then `β ≥ ½ − h − ε` for all zeros of large height (`eventually_strip_of_lindelofCriticalLine`).

**Proof.** Phragmén–Lindelöf on the strip `½ ≤ Re s ≤ 2` for
`F(s) = (s − 1)ζ(s)(s + 2)^{−(1+ε)}`, where `(s − 1)ζ(s)` is continued across `s = 1`. On
`Re s = ½`, `‖F‖ ≤ (3/2)C` for `|t| ≥ 1` and is bounded on the compact segment `|t| ≤ 1`. On
`Re s = 2`, `‖F‖ ≤ 2` since `‖ζ‖ ≤ 2` and `‖s − 1‖ ≤ ‖s + 2‖`. Inside, the crude bound
`‖ζ(σ+it)‖ ≤ 2 + 4|t|` gives polynomial growth. So `‖F‖ ≤ C₁` on the strip, and
`‖ζ(s)‖ ≤ C₁‖s + 2‖^{1+ε}/‖s − 1‖ ≤ 5^{1+ε}C₁|t|^ε`. For `Re s ≥ 2`, `‖ζ‖ ≤ 2`.
-/

open Complex Filter Topology Set

namespace RHTower.LindelofSparse

open RHTower.DeBruijn RHTower.CosineDefectBudget RHTower.CosineSparseCluster

noncomputable section

/-- The Lindelöf hypothesis on the critical line. -/
def LindelofCriticalLine : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| →
    ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ ε

/-- `(s − 1)ζ(s)`, continued across the pole. -/
def zetaTimesSubOne (s : ℂ) : ℂ := (s - 1) * zetaPoleFree s + (Complex.Gammaℝ s)⁻¹

theorem differentiable_zetaTimesSubOne : Differentiable ℂ zetaTimesSubOne := fun s =>
  (((differentiableAt_id).sub_const 1).mul (differentiable_zetaPoleFree s)).add
    (Complex.differentiable_Gammaℝ_inv s)

theorem zetaTimesSubOne_eq {s : ℂ} (hs : s ≠ 1) : zetaTimesSubOne s = (s - 1) * riemannZeta s := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hx : (s - 1) * (1 / (s - 1) / Complex.Gammaℝ s) = (Complex.Gammaℝ s)⁻¹ := by
    rcases eq_or_ne (Complex.Gammaℝ s) 0 with hg | hg
    · simp [hg]
    · field_simp
  rw [zetaTimesSubOne, zetaPoleFree, mul_sub, hx]
  ring

/-- The Phragmén–Lindelöf test function `(s − 1)ζ(s)(s + 2)^{−p}`. -/
def lindelofTest (p : ℝ) (s : ℂ) : ℂ := zetaTimesSubOne s * (s + 2) ^ ((-p : ℝ) : ℂ)

theorem norm_lindelofTest (p : ℝ) (s : ℂ) :
    ‖lindelofTest p s‖ = ‖zetaTimesSubOne s‖ * ‖s + 2‖ ^ (-p) := by
  rw [lindelofTest, norm_mul, Complex.norm_cpow_real]

theorem norm_add_two_ge {s : ℂ} (hs : 0 ≤ s.re) : 2 ≤ ‖s + 2‖ ∧ |s.im| ≤ ‖s + 2‖ ∧
    ‖s + 2‖ ≤ s.re + 2 + |s.im| := by
  have h1 := Complex.abs_re_le_norm (s + 2)
  have h2 := Complex.abs_im_le_norm (s + 2)
  have h3 := Complex.norm_le_abs_re_add_abs_im (s + 2)
  simp only [add_re, re_ofNat, add_im, im_ofNat, add_zero] at h1 h2 h3
  rw [abs_of_nonneg (by linarith)] at h1 h3
  exact ⟨by linarith, h2, h3⟩

theorem differentiableOn_lindelofTest (p : ℝ) :
    DifferentiableOn ℂ (lindelofTest p) {s : ℂ | 0 ≤ s.re} := by
  intro s hs
  refine ((differentiable_zetaTimesSubOne s).mul ?_).differentiableWithinAt
  refine ((differentiableAt_id).add_const 2).cpow_const ?_
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [id, add_re, re_ofNat]
  have : 0 ≤ s.re := hs
  linarith

/-- On `Re s ≥ ½`, `|Im s| ≥ 2`: `‖ζ(s)‖ ≤ 2 + 4|Im s|` for `Re s ≤ 2`. -/
theorem norm_riemannZeta_le_linear {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 2 + 4 * |s.im| := by
  have hs : s = ((s.re : ℝ) : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  have h := norm_riemannZeta_le_strip (σ := s.re) (t := s.im) ⟨by linarith, h2⟩ ht
  rw [← hs] at h
  have hd : 2 ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    simp only [sub_im, one_im, zero_sub, abs_neg] at this
    linarith
  have hinv : 1 / ‖1 - s‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hq : 2 * |s.im| / s.re ≤ 4 * |s.im| := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg s.im]
  linarith

/-- **Convexity.** The critical-line Lindelöf hypothesis implies its half-plane form. -/
theorem lindelofHalfPlane_of_criticalLine (hLH : LindelofCriticalLine) : LindelofHalfPlane := by
  intro ε hε
  obtain ⟨C₀, hC₀⟩ := hLH ε hε
  set p := 1 + ε with hp
  have hp1 : 1 ≤ p := by linarith
  set F := lindelofTest p with hF
  -- the compact part of the critical line
  have hcont : Continuous fun t : ℝ => F ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    have hd : DifferentiableOn ℂ F {s : ℂ | 0 ≤ s.re} := differentiableOn_lindelofTest p
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hmem : (1 / 2 : ℂ) + (t : ℂ) * I ∈ {s : ℂ | 0 < s.re} := by
      simp only [mem_setOf_eq, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_zero]; norm_num
    have hF' : DifferentiableAt ℂ F ((1 / 2 : ℂ) + (t : ℂ) * I) :=
      (hd.mono fun s (hs : 0 < s.re) => hs.le).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)
    have hc : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) t := by fun_prop
    exact ContinuousAt.comp (g := F) hF'.continuousAt hc
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  set Cb := max (max (3 / 2 * |C₀|) K₁) 2 with hCb
  -- boundary bounds
  have hle_a : ∀ z : ℂ, z.re = 1 / 2 → ‖F z‖ ≤ Cb := by
    intro z hz
    have hzeq : z = (1 / 2 : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hz]
    rcases le_or_gt 1 |z.im| with ht | ht
    · have hz1 : z ≠ 1 := fun h => by rw [h] at ht; simp at ht; linarith
      rw [hF, norm_lindelofTest, zetaTimesSubOne_eq hz1, norm_mul]
      obtain ⟨h2, him, -⟩ := norm_add_two_ge (s := z) (by rw [hz]; norm_num)
      have hz' := hC₀ z.im ht
      rw [← hzeq] at hz'
      have hsub : ‖z - 1‖ ≤ |z.im| + 1 / 2 := by
        have := Complex.norm_le_abs_re_add_abs_im (z - 1)
        simp only [sub_re, one_re, sub_im, one_im, sub_zero, hz] at this
        norm_num at this ⊢; linarith
      have hpow : ‖z + 2‖ ^ (-p) ≤ |z.im| ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) him (by linarith)
      have hC0 : 0 ≤ C₀ * |z.im| ^ ε := (norm_nonneg _).trans hz'
      have key : ‖z - 1‖ * ‖riemannZeta z‖ * ‖z + 2‖ ^ (-p) ≤
          (|z.im| + 1 / 2) * (C₀ * |z.im| ^ ε) * |z.im| ^ (-p) := by
        gcongr
      have hsimp : (|z.im| + 1 / 2) * (C₀ * |z.im| ^ ε) * |z.im| ^ (-p) =
          C₀ * ((|z.im| + 1 / 2) / |z.im|) := by
        have ht0 : 0 < |z.im| := by linarith
        rw [hp, show -(1 + ε) = -1 + -ε by ring, Real.rpow_add ht0, Real.rpow_neg ht0.le,
          Real.rpow_neg ht0.le, Real.rpow_one]
        have : |z.im| ^ ε ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
        field_simp
      rw [hsimp] at key
      have hratio : (|z.im| + 1 / 2) / |z.im| ≤ 3 / 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hC0' : 0 ≤ C₀ := by
        by_contra hneg
        have : C₀ * |z.im| ^ ε < 0 :=
          mul_neg_of_neg_of_pos (not_le.mp hneg) (Real.rpow_pos_of_pos (by linarith) _)
        linarith
      have : C₀ * ((|z.im| + 1 / 2) / |z.im|) ≤ 3 / 2 * |C₀| := by
        rw [abs_of_nonneg hC0']; nlinarith
      calc _ ≤ C₀ * ((|z.im| + 1 / 2) / |z.im|) := key
        _ ≤ 3 / 2 * |C₀| := this
        _ ≤ Cb := (le_max_left _ _).trans (le_max_left _ _)
    · have hmem : z.im ∈ Icc (-1 : ℝ) 1 := by
        rw [abs_lt] at ht; exact ⟨ht.1.le, ht.2.le⟩
      have := hK₁ z.im hmem
      rw [← hzeq] at this
      exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  have hle_b : ∀ z : ℂ, z.re = 2 → ‖F z‖ ≤ Cb := by
    intro z hz
    have hz1 : z ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
    rw [hF, norm_lindelofTest, zetaTimesSubOne_eq hz1, norm_mul]
    obtain ⟨h2, -, -⟩ := norm_add_two_ge (s := z) (by rw [hz]; norm_num)
    have hζ : ‖riemannZeta z‖ ≤ 2 := norm_riemannZeta_le_two (by rw [hz])
    have hsub : ‖z - 1‖ ≤ ‖z + 2‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (z - 1)), ← Real.sqrt_sq (norm_nonneg (z + 2))]
      apply Real.sqrt_le_sqrt
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [sub_re, one_re, sub_im, one_im, sub_zero, add_re, re_ofNat, add_im, im_ofNat,
        add_zero, hz]
      nlinarith
    have hpow : ‖z + 2‖ ^ (-p) ≤ ‖z + 2‖ ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h20 : 0 < ‖z + 2‖ := by linarith
    have hinv : ‖z + 2‖ ^ (-1 : ℝ) = ‖z + 2‖⁻¹ := by rw [Real.rpow_neg_one]
    calc ‖z - 1‖ * ‖riemannZeta z‖ * ‖z + 2‖ ^ (-p)
        ≤ ‖z + 2‖ * 2 * ‖z + 2‖⁻¹ := by
          rw [← hinv]; gcongr
      _ = 2 := by field_simp
      _ ≤ Cb := le_max_right _ _
  -- growth in the strip
  have hgrowth : ∃ c < Real.pi / (2 - 1 / 2), ∃ B,
      F =O[Filter.comap (abs ∘ im) Filter.atTop ⊓ Filter.principal (re ⁻¹' Ioo (1 / 2) 2)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, by
      have := Real.pi_gt_three
      rw [lt_div_iff₀ (by norm_num)]; linarith, 1, ?_⟩
    refine Asymptotics.IsBigO.of_bound 6 ?_
    rw [Filter.eventually_inf_principal]
    have hev : ∀ᶠ z in Filter.comap (abs ∘ im) Filter.atTop, 2 ≤ |z.im| := by
      rw [Filter.eventually_comap]
      filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx z hz
      simp only [Function.comp_apply] at hz
      rw [hz]; exact hx
    filter_upwards [hev] with z hz hzs
    obtain ⟨hzs1, hzs2⟩ := hzs
    have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz; linarith
    rw [hF, norm_lindelofTest, zetaTimesSubOne_eq hz1, norm_mul]
    obtain ⟨h2, -, h3⟩ := norm_add_two_ge (s := z) (by linarith)
    have hζ := norm_riemannZeta_le_linear hzs1.le hzs2.le hz
    have hsub : ‖z - 1‖ ≤ 1 + |z.im| := by
      have := Complex.norm_le_abs_re_add_abs_im (z - 1)
      simp only [sub_re, one_re, sub_im, one_im, sub_zero] at this
      have : |z.re - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have hpow : ‖z + 2‖ ^ (-p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    set x := |z.im| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    have hexp : (1 + x) * (2 + 4 * x) ≤ 6 * Real.exp (Real.exp x) := by
      have e2 := Real.quadratic_le_exp_of_nonneg hx0
      have e4 : Real.exp (1 + x) ≤ Real.exp (Real.exp x) :=
        Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp x])
      have e5 : Real.exp (1 + x) = Real.exp 1 * Real.exp x := Real.exp_add 1 x
      have e6 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have e7 : 2 * Real.exp x ≤ Real.exp 1 * Real.exp x :=
        mul_le_mul_of_nonneg_right e6 (Real.exp_pos x).le
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, one_mul]
    calc ‖z - 1‖ * ‖riemannZeta z‖ * ‖z + 2‖ ^ (-p)
        ≤ (1 + x) * (2 + 4 * x) * 1 := by gcongr
      _ ≤ 6 * Real.exp (Real.exp x) := by linarith
  -- Phragmén–Lindelöf
  have hPL : ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → ‖F z‖ ≤ Cb := fun z ha hb =>
    PhragmenLindelof.vertical_strip
      ((differentiableOn_lindelofTest p).mono fun s hs => by
        rw [Complex.closure_preimage_re, closure_Ioo (by norm_num)] at hs
        exact (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hs.1).diffContOnCl
      hgrowth hle_a hle_b ha hb
  -- back to ζ
  refine ⟨max 2 (5 ^ p * Cb), le_trans (by norm_num) (le_max_left _ _), fun s hs ht => ?_⟩
  have hpowt : 1 ≤ |s.im| ^ ε := Real.one_le_rpow ht hε.le
  rcases le_or_gt s.re 2 with hs2 | hs2
  · have hs1 : s ≠ 1 := fun h => by rw [h] at ht; simp at ht; linarith
    have hFs := hPL s hs hs2
    rw [hF, norm_lindelofTest, zetaTimesSubOne_eq hs1, norm_mul] at hFs
    obtain ⟨h2, him, h3⟩ := norm_add_two_ge (s := s) (by linarith)
    have hsub : |s.im| ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simpa using this
    have hd0 : 0 < ‖s - 1‖ := by linarith
    have hpos : 0 < ‖s + 2‖ ^ (-p) := Real.rpow_pos_of_pos (by linarith) _
    have hζ : ‖riemannZeta s‖ ≤ Cb * ‖s + 2‖ ^ p / ‖s - 1‖ := by
      rw [le_div_iff₀ hd0]
      have e : ‖s + 2‖ ^ p = (‖s + 2‖ ^ (-p))⁻¹ := by
        rw [Real.rpow_neg (by linarith), inv_inv]
      rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos]
      linarith
    have hCb0 : 0 ≤ Cb := (le_max_right _ _).trans' (by norm_num)
    have h5 : ‖s + 2‖ ≤ 5 * |s.im| := by linarith
    have hstep : Cb * ‖s + 2‖ ^ p / ‖s - 1‖ ≤ 5 ^ p * Cb * |s.im| ^ ε := by
      rw [div_le_iff₀ hd0]
      have ht0 : 0 < |s.im| := by linarith
      have hp' : ‖s + 2‖ ^ p ≤ (5 * |s.im|) ^ p := Real.rpow_le_rpow (by linarith) h5 (by linarith)
      rw [Real.mul_rpow (by norm_num) ht0.le, hp, Real.rpow_add ht0, Real.rpow_one] at hp'
      have : 5 ^ (1 + ε) * Cb * |s.im| ^ ε * |s.im| ≤ 5 ^ (1 + ε) * Cb * |s.im| ^ ε * ‖s - 1‖ :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
      calc Cb * ‖s + 2‖ ^ (1 + ε) ≤ Cb * (5 ^ (1 + ε) * (|s.im| * |s.im| ^ ε)) :=
            mul_le_mul_of_nonneg_left hp' hCb0
        _ = 5 ^ (1 + ε) * Cb * |s.im| ^ ε * |s.im| := by ring
        _ ≤ _ := this
    calc ‖riemannZeta s‖ ≤ 5 ^ p * Cb * |s.im| ^ ε := hζ.trans hstep
      _ ≤ max 2 (5 ^ p * Cb) * |s.im| ^ ε :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have hζ : ‖riemannZeta s‖ ≤ 2 := norm_riemannZeta_le_two hs2.le
    calc ‖riemannZeta s‖ ≤ 2 * 1 := by linarith
      _ ≤ max 2 (5 ^ p * Cb) * |s.im| ^ ε :=
          mul_le_mul (le_max_left _ _) hpowt (by norm_num) (by positivity)

/-- **Backlund's direction**, from the Lindelöf hypothesis in its standard form. -/
theorem offLineSparse_of_lindelofCriticalLine (hLH : LindelofCriticalLine) : OffLineSparse :=
  offLineSparse_of_lindelof (lindelofHalfPlane_of_criticalLine hLH)

/-- **Under the Lindelöf hypothesis a real-rooted differenced `ξ` is an eventual strip.** -/
theorem eventually_strip_of_lindelofCriticalLine (hLH : LindelofCriticalLine) {h : ℝ}
    (hh : 0 < h) (hreal : ∀ z, cosShiftXi h z = 0 → z.im = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ q : XiZeroCopy, T ≤ (xiSpectralPoint q).re → (xiSpectralPoint q).im ≤ h + ε :=
  eventually_strip_of_lindelof_of_cosShiftXi_real (lindelofHalfPlane_of_criticalLine hLH) hh hreal hε

/-- **Suzuki's shifted-Xi threshold is the strip width under the Lindelöf hypothesis.** For
`h > 0`: if every zero satisfies `|β − ½| < h`, then `A^h = cos(hD)Ξ = (Ξ(z+ih) + Ξ(z−ih))/2` has
only real zeros (de Bruijn, unconditional). Conversely, under LH, real-rootedness of `A^h` forces
`β ≥ ½ − h − ε` for all zeros of large height, for every `ε > 0`. So under LH any passage of the
Suzuki family below `h = ½` is a zero-free-strip statement. -/
theorem suzuki_threshold_strip_of_lindelof (hLH : LindelofCriticalLine) {h : ℝ} (hh : 0 < h) :
    ((∀ q : XiZeroCopy, |(xiSpectralPoint q).im| < h) → ∀ z, cosShiftXi h z = 0 → z.im = 0) ∧
    ((∀ z, cosShiftXi h z = 0 → z.im = 0) → ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ q : XiZeroCopy,
      T ≤ (xiSpectralPoint q).re → (xiSpectralPoint q).im ≤ h + ε) := by
  refine ⟨fun hstrip z hz => ?_, fun hreal ε hε => eventually_strip_of_lindelofCriticalLine hLH hh
    hreal hε⟩
  have hLP := laguerrePolya_cosineShiftXi_of_im_gt (h := h) fun q => (abs_lt.mp (hstrip q)).1
  exact GaloisForLFunctions.HTGeometry.im_eq_zero_of_laguerrePolya hLP (cosShiftXi_zero_ne h) hz

end

end RHTower.LindelofSparse
