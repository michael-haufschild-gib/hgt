import GaloisForLFunctions.RHTower.BacklundLindelofConverse
import GaloisForLFunctions.RHTower.ZetaChiLineSharp

/-!
# Backlund's theorem with the Lindelöf hypothesis in its standard form

**Theorem** (`lindelofCriticalLine_of_lindelofOpen`). If `μ(σ) = 0` for every `σ > ½`, then
`‖ζ(½ + it)‖ ≤ C_ε|t|^ε` for `|t| ≥ 1`.

**Corollary** (`offLineSparse_iff_lindelofCriticalLine`). Off-line zeros are sparse in Backlund's
sense (for every `η, L, c > 0`, eventually every window of length `2L` at height `t` carries at most
`c log t` zeros with `|β − ½| > η`) if and only if the Lindelöf hypothesis holds.

**Proof.** Fix `ε₀ > 0`, put `δ = min(ε₀/2, ¼)`, `ε = ε₀/2`, `p = 1 + δ + ε`. On `Re s = ½ + δ`,
`‖ζ‖ ≤ |t|^ε` for large `|t|`. On `Re s = ½ − δ`, the functional equation `ζ(s) = χ(s)ζ(1 − s)`
with `‖χ(½ − δ + it)‖ ≤ C|t|^δ` gives `‖ζ‖ ≤ C|t|^{δ+ε}`. So `F(s) = (s − 1)ζ(s)(s + 2)^{−p}` is
bounded on both edges of the strip `½ − δ ≤ Re s ≤ ½ + δ`, with compactness for bounded `|t|`.
Inside, `‖ζ(σ + it)‖ ≤ 2 + 8|t|`, so Phragmén–Lindelöf bounds `F` on the strip, and on the
critical line `‖ζ(½ + it)‖ ≤ C'|t|^{p−1} ≤ C'|t|^{ε₀}`.
-/

open Complex Filter Topology Set

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster

noncomputable section

theorem gammaR_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have := congrArg Complex.im hn
  simp at this
  exact hs this

/-- **Left edge.** Under `μ(σ) = 0` for `σ > ½`, `‖ζ(½ − δ + it)‖ ≤ C|t|^{δ+ε}` for large `|t|`. -/
theorem exists_norm_riemannZeta_leftLine_le (hLO : LindelofOpen) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) :
    ∃ C T : ℝ, 0 < C ∧ 2 ≤ T ∧ ∀ z : ℂ, z.re = 1 / 2 - δ → T ≤ |z.im| →
      ‖riemannZeta z‖ ≤ C * |z.im| ^ (δ + ε) := by
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_norm_zetaChi_line_le (σ := 1 / 2 - δ) (by linarith)
  obtain ⟨T, hT⟩ := hLO (1 / 2 + δ) ε (by linarith) hε
  refine ⟨Cχ, max T 2, hCχ, le_max_right _ _, fun z hz ht => ?_⟩
  have ht2 : 2 ≤ |z.im| := le_trans (le_max_right _ _) ht
  have hx0 : 0 < |z.im| := by linarith
  have him : z.im ≠ 0 := fun h => by rw [h, abs_zero] at ht2; linarith
  have h0 : z ≠ 0 := fun h => him (by rw [h]; simp)
  have h1 : z ≠ 1 := fun h => him (by rw [h]; simp)
  have hG : Gammaℝ (1 - z) ≠ 0 := gammaR_ne_zero_of_im_ne_zero (by simpa using him)
  have hzeq : z = ((1 / 2 - δ : ℝ) : ℂ) + (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [hz]
  have hχz := hχ z.im ht2
  rw [← hzeq, show (1 : ℝ) / 2 - (1 / 2 - δ) = δ by ring] at hχz
  have hζ := hT (1 - z) (by simp [hz]; linarith)
    (by simp only [sub_im, one_im, zero_sub, abs_neg]; exact le_trans (le_max_left _ _) ht)
  simp only [sub_im, one_im, zero_sub, abs_neg] at hζ
  rw [zeta_eq_zetaChi_mul h0 h1 hG, norm_mul, Real.rpow_add hx0, ← mul_assoc]
  exact mul_le_mul hχz hζ (norm_nonneg _) (by positivity)

/-- `‖ζ(s)‖ ≤ 2 + 8|Im s|` on `¼ ≤ Re s ≤ 2`, `|Im s| ≥ 2`. -/
theorem norm_riemannZeta_le_linear_quarter {s : ℂ} (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 2)
    (ht : 2 ≤ |s.im|) : ‖riemannZeta s‖ ≤ 2 + 8 * |s.im| := by
  have hs : s = ((s.re : ℝ) : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  have h := norm_riemannZeta_le_strip (σ := s.re) (t := s.im) ⟨by linarith, h2⟩ ht
  rw [← hs] at h
  have hd : 2 ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    simp only [sub_im, one_im, zero_sub, abs_neg] at this
    linarith
  have hinv : 1 / ‖1 - s‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hq : 2 * |s.im| / s.re ≤ 8 * |s.im| := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg s.im]
  linarith

/-- A power bound `‖ζ(z)‖ ≤ K|Im z|^{p−1}` gives `‖(z − 1)ζ(z)(z + 2)^{−p}‖ ≤ 2K`. -/
theorem norm_lindelofTest_le_of_bound {p K : ℝ} {z : ℂ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (hre0 : 0 ≤ z.re) (hre2 : z.re ≤ 2) (ht : 1 ≤ |z.im|)
    (hζ : ‖riemannZeta z‖ ≤ K * |z.im| ^ (p - 1)) : ‖lindelofTest p z‖ ≤ 2 * K := by
  have hz1 : z ≠ 1 := fun h => by rw [h] at ht; simp at ht; linarith
  rw [norm_lindelofTest, zetaTimesSubOne_eq hz1, norm_mul]
  obtain ⟨-, him, -⟩ := norm_add_two_ge hre0
  set x := |z.im| with hx
  have hx0 : 0 < x := by linarith
  have hsub : ‖z - 1‖ ≤ x + 1 := by
    have := Complex.norm_le_abs_re_add_abs_im (z - 1)
    simp only [sub_re, one_re, sub_im, one_im, sub_zero] at this
    have : |z.re - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hpow : ‖z + 2‖ ^ (-p) ≤ x ^ (-p) := Real.rpow_le_rpow_of_nonpos hx0 him (by linarith)
  have hxx : x ^ (p - 1) * x ^ (-p) = x⁻¹ := by
    rw [← Real.rpow_add hx0, show p - 1 + -p = (-1 : ℝ) by ring, Real.rpow_neg_one]
  have hratio : (x + 1) * x⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hx0]; linarith
  calc ‖z - 1‖ * ‖riemannZeta z‖ * ‖z + 2‖ ^ (-p)
      ≤ (x + 1) * (K * x ^ (p - 1)) * x ^ (-p) := by gcongr
    _ = K * ((x + 1) * x⁻¹) := by
        rw [show (x + 1) * (K * x ^ (p - 1)) * x ^ (-p) = K * (x + 1) * (x ^ (p - 1) * x ^ (-p))
          by ring, hxx]; ring
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left hratio hK
    _ = 2 * K := by ring

theorem continuous_lindelofTest_line (p : ℝ) {a : ℝ} (ha : 0 < a) :
    Continuous fun t : ℝ => lindelofTest p ((a : ℂ) + (t : ℂ) * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : (a : ℂ) + (t : ℂ) * I ∈ {s : ℂ | 0 < s.re} := by simp [ha]
  have hF : DifferentiableAt ℂ (lindelofTest p) ((a : ℂ) + (t : ℂ) * I) :=
    ((differentiableOn_lindelofTest p).mono fun s (hs : 0 < s.re) => hs.le).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)
  have hc : ContinuousAt (fun t : ℝ => (a : ℂ) + (t : ℂ) * I) t := by fun_prop
  exact ContinuousAt.comp (g := lindelofTest p) hF.continuousAt hc

/-- A bound far up a vertical line extends to the whole line by compactness. -/
theorem exists_lindelofTest_line_bound {p a T K : ℝ} (ha : 0 < a)
    (hfar : ∀ z : ℂ, z.re = a → T ≤ |z.im| → ‖lindelofTest p z‖ ≤ K) :
    ∃ C : ℝ, ∀ z : ℂ, z.re = a → ‖lindelofTest p z‖ ≤ C := by
  obtain ⟨K₁, hK₁⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (continuous_lindelofTest_line p ha).continuousOn
  refine ⟨max K K₁, fun z hz => ?_⟩
  rcases le_or_gt T |z.im| with ht | ht
  · exact (hfar z hz ht).trans (le_max_left _ _)
  · have hzeq : z = (a : ℂ) + (z.im : ℂ) * I := by apply Complex.ext <;> simp [hz]
    have hmem : z.im ∈ Icc (-T) T := by rw [abs_lt] at ht; exact ⟨ht.1.le, ht.2.le⟩
    have := hK₁ z.im hmem
    rw [← hzeq] at this
    exact this.trans (le_max_right _ _)

/-- **Phragmén–Lindelöf for the test function** on a strip `a ≤ Re s ≤ b` inside `[¼, 2]` of
width less than `π`. -/
theorem norm_lindelofTest_le_strip {p a b Cb : ℝ} (hp : 1 ≤ p) (ha : 1 / 4 ≤ a) (hab : a < b)
    (hb : b ≤ 2) (hπ : b - a < Real.pi)
    (hle_a : ∀ z : ℂ, z.re = a → ‖lindelofTest p z‖ ≤ Cb)
    (hle_b : ∀ z : ℂ, z.re = b → ‖lindelofTest p z‖ ≤ Cb) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖lindelofTest p z‖ ≤ Cb := by
  have hgrowth : ∃ c < Real.pi / (b - a), ∃ B,
      lindelofTest p =O[Filter.comap (abs ∘ im) Filter.atTop ⊓ Filter.principal (re ⁻¹' Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, by rw [lt_div_iff₀ (by linarith)]; linarith, 1, ?_⟩
    refine Asymptotics.IsBigO.of_bound 16 ?_
    rw [Filter.eventually_inf_principal]
    have hev : ∀ᶠ z in Filter.comap (abs ∘ im) Filter.atTop, 2 ≤ |z.im| := by
      rw [Filter.eventually_comap]
      filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with x hx z hz
      simp only [Function.comp_apply] at hz
      rw [hz]; exact hx
    filter_upwards [hev] with z hz hzs
    obtain ⟨hzs1, hzs2⟩ := hzs
    have hz1 : z ≠ 1 := fun h => by rw [h] at hz; simp at hz; linarith
    rw [norm_lindelofTest, zetaTimesSubOne_eq hz1, norm_mul]
    obtain ⟨h2, -, -⟩ := norm_add_two_ge (s := z) (by linarith)
    have hζ := norm_riemannZeta_le_linear_quarter (by linarith) (by linarith) hz
    have hsub : ‖z - 1‖ ≤ 1 + |z.im| := by
      have := Complex.norm_le_abs_re_add_abs_im (z - 1)
      simp only [sub_re, one_re, sub_im, one_im, sub_zero] at this
      have : |z.re - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have hpow : ‖z + 2‖ ^ (-p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    set x := |z.im| with hx
    have hx0 : 0 ≤ x := abs_nonneg _
    have hexp : (1 + x) * (2 + 8 * x) ≤ 16 * Real.exp (Real.exp x) := by
      have e2 := Real.quadratic_le_exp_of_nonneg hx0
      have e3 : Real.exp x ≤ Real.exp (Real.exp x) :=
        Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp x])
      nlinarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, one_mul]
    calc ‖z - 1‖ * ‖riemannZeta z‖ * ‖z + 2‖ ^ (-p)
        ≤ (1 + x) * (2 + 8 * x) * 1 := by gcongr
      _ ≤ 16 * Real.exp (Real.exp x) := by linarith
  intro z hza hzb
  exact PhragmenLindelof.vertical_strip
    ((differentiableOn_lindelofTest p).mono fun s hs => by
      rw [Complex.closure_preimage_re, closure_Ioo hab.ne] at hs
      exact (by linarith : (0 : ℝ) ≤ a).trans hs.1).diffContOnCl
    hgrowth hle_a hle_b hza hzb

/-- Back from the test function to `ζ` on the critical line. -/
theorem norm_riemannZeta_criticalLine_le_of_test {p Cb : ℝ} {z : ℂ} (hp : 1 ≤ p) (hCb : 0 ≤ Cb)
    (hz : z.re = 1 / 2) (ht : 1 ≤ |z.im|) (hF : ‖lindelofTest p z‖ ≤ Cb) :
    ‖riemannZeta z‖ ≤ Cb * (7 / 2) ^ p * |z.im| ^ (p - 1) := by
  have hz1 : z ≠ 1 := fun h => by rw [h] at ht; simp at ht; linarith
  rw [norm_lindelofTest, zetaTimesSubOne_eq hz1, norm_mul] at hF
  obtain ⟨h2, -, h3⟩ := norm_add_two_ge (s := z) (by rw [hz]; norm_num)
  set x := |z.im| with hx
  have hx0 : 0 < x := by linarith
  have hsub : x ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simpa using this
  have hd0 : 0 < ‖z - 1‖ := by linarith
  have hpos : 0 < ‖z + 2‖ ^ (-p) := Real.rpow_pos_of_pos (by linarith) _
  have hζ : ‖riemannZeta z‖ ≤ Cb * ‖z + 2‖ ^ p / ‖z - 1‖ := by
    rw [le_div_iff₀ hd0]
    have e : ‖z + 2‖ ^ p = (‖z + 2‖ ^ (-p))⁻¹ := by
      rw [Real.rpow_neg (by linarith), inv_inv]
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  have h7 : ‖z + 2‖ ≤ 7 / 2 * x := by rw [hz] at h3; linarith
  have hp' : ‖z + 2‖ ^ p ≤ (7 / 2) ^ p * x ^ p := by
    rw [← Real.mul_rpow (by norm_num) hx0.le]
    exact Real.rpow_le_rpow (by linarith) h7 (by linarith)
  have hxp : x ^ p = x ^ (p - 1) * x := by
    rw [← Real.rpow_add_one hx0.ne', sub_add_cancel]
  refine hζ.trans ?_
  rw [div_le_iff₀ hd0]
  calc Cb * ‖z + 2‖ ^ p ≤ Cb * ((7 / 2) ^ p * x ^ p) := mul_le_mul_of_nonneg_left hp' hCb
    _ = Cb * (7 / 2) ^ p * x ^ (p - 1) * x := by rw [hxp]; ring
    _ ≤ Cb * (7 / 2) ^ p * x ^ (p - 1) * ‖z - 1‖ :=
        mul_le_mul_of_nonneg_left hsub (by positivity)

/-- **`μ(σ) = 0` for all `σ > ½` gives the Lindelöf hypothesis on the critical line.** -/
theorem lindelofCriticalLine_of_lindelofOpen (hLO : LindelofOpen) : LindelofCriticalLine := by
  intro ε₀ hε₀
  set δ := min (ε₀ / 2) (1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδε : δ ≤ ε₀ / 2 := min_le_left _ _
  set ε := ε₀ / 2 with hε
  have hε0 : 0 < ε := by linarith
  set p := 1 + δ + ε with hp
  have hp1 : 1 ≤ p := by linarith
  have hp1' : p - 1 = δ + ε := by rw [hp]; ring
  obtain ⟨Cl, Tl, hCl, hTl, hleft⟩ := exists_norm_riemannZeta_leftLine_le hLO hδ0 hε0
  obtain ⟨Tr, hright⟩ := hLO (1 / 2 + δ) ε (by linarith) hε0
  obtain ⟨Ca, hCa⟩ := exists_lindelofTest_line_bound (p := p) (a := 1 / 2 - δ) (T := Tl)
    (K := 2 * Cl) (by linarith) fun z hz ht =>
      norm_lindelofTest_le_of_bound hp1 hCl.le (by rw [hz]; linarith) (by rw [hz]; linarith)
        (by linarith) (by rw [hp1']; exact hleft z hz ht)
  obtain ⟨Cr, hCr⟩ := exists_lindelofTest_line_bound (p := p) (a := 1 / 2 + δ) (T := max Tr 1)
    (K := 2 * 1) (by linarith) fun z hz ht => by
      have ht1 : 1 ≤ |z.im| := le_trans (le_max_right _ _) ht
      refine norm_lindelofTest_le_of_bound hp1 zero_le_one (by rw [hz]; linarith)
        (by rw [hz]; linarith) ht1 ?_
      refine (hright z (le_of_eq hz.symm) (le_trans (le_max_left _ _) ht)).trans ?_
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  set Cb := max (max Ca Cr) 0 with hCb
  have hstrip := norm_lindelofTest_le_strip (p := p) (a := 1 / 2 - δ) (b := 1 / 2 + δ) (Cb := Cb)
    hp1 (by linarith) (by linarith) (by linarith) (by linarith [Real.pi_gt_three])
    (fun z hz => (hCa z hz).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun z hz => (hCr z hz).trans ((le_max_right _ _).trans (le_max_left _ _)))
  refine ⟨Cb * (7 / 2) ^ p, fun t ht => ?_⟩
  set z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I with hzdef
  have hzre : z.re = 1 / 2 := by simp [hzdef]
  have hzim : z.im = t := by simp [hzdef]
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have h := norm_riemannZeta_criticalLine_le_of_test hp1 hCb0 hzre (by rw [hzim]; exact ht)
    (hstrip z (by rw [hzre]; linarith) (by rw [hzre]; linarith))
  rw [hzim, hp1'] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)

/-- **Backlund's theorem.** Off-line zeros are sparse if and only if the Lindelöf hypothesis holds:
for every `ε > 0`, `‖ζ(½ + it)‖ ≤ C_ε|t|^ε` for `|t| ≥ 1`. -/
theorem offLineSparse_iff_lindelofCriticalLine : OffLineSparse ↔ LindelofCriticalLine :=
  ⟨fun h => lindelofCriticalLine_of_lindelofOpen (lindelofOpen_of_offLineSparse h),
    offLineSparse_of_lindelofCriticalLine⟩

/-- The three forms of the Lindelöf hypothesis used here are equivalent. -/
theorem lindelofCriticalLine_iff_lindelofOpen : LindelofCriticalLine ↔ LindelofOpen :=
  ⟨fun h => lindelofOpen_of_offLineSparse (offLineSparse_of_lindelofCriticalLine h),
    lindelofCriticalLine_of_lindelofOpen⟩

end

end RHTower.BacklundConverse
