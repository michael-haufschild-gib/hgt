import GaloisForLFunctions.RHTower.OddWeilSpectralMeasure
import GaloisForLFunctions.RHTower.EvenTestLaplacePositivity

/-!
# The real cut of an odd Weil-positive weight is its even mean-zero deficit

For an odd Weil-positive weight the squared-variable Weil function `aΨ(½+a)`, `z = a²`, is the
Nevanlinna transform of a finite circle measure `ν` with a constant `c`.  The odd spectral
representation expresses the Weil functional on odd tests through `ν`.  Here the representation is
extended to every `C²` compactly supported test `f`:

`Re W_lam(f ⋆ f̃) = ∫ Θ_f(e^{iθ}) dν(θ) − c |f̂(0)|²`,

with the same spectral weight `Θ_f`.  On the critical ordinates
`Θ_f = [(1+γ²)(|f̂(√γ)|² + |f̂(−√γ)|²)/2 − |f̂(0)|²]/γ`; on the cut (`−¼ ≤ γ < 0`)
`Θ_f = [|f̂(0)|² − (1+γ²) Re(f̂(−i√(−γ)) conj f̂(i√(−γ)))]/(−γ)`.

For a mean-zero test (`f̂(0) = 0`) the weight is nonnegative on the critical ordinates, at the
centre and at `ζ = 1`; for an even mean-zero test it is `−(1+γ²)|f̂(i√(−γ))|²/(−γ) ≤ 0` on the
cut.  Odd tests see the cut with the opposite sign.

**Cut removal** (`cut_measure_eq_zero_of_even_mean_zero_nonneg`).  If the Weil functional is
nonnegative on every even test with `f̂(0) = 0`, the cut measure vanishes.  The two-bump test
`f_L = b(· − L) − 2b + b(· + L)` has transform `(2cos(Lv) − 2) b̂(v)` on the real line, whose
contribution to the critical integral is `O(L²)`, but `(2cosh(Lr) − 2) b̂(ir)` on the cut, whose
contribution is `≤ −L⁴ r⁴ (∫b)² ν(cut_r)`.  Letting `L → ∞` forces `ν(cut_r) = 0`.

**Converse** (`weilFullFunctional_nonneg_of_cut_eq_zero`).  Without cut mass the functional is
nonnegative on every mean-zero test of either parity.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open Zeta23 Zeta23.WeilEF GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.OddResolvent
open WeilHerglotz RHTower.AtomDomination RHTower.WeilLineIntegral RHTower.WeilAtomic RHTower.EvenSector

/-! ## The central value of the autocorrelation transform -/

/-- `H(½) = |f̂(0)|²` for every test. -/
theorem Hfn_weilTest_half {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Hfn (EF.weilTest f f) (1 / 2) = ((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ) := by
  have h := Hfn_weilTest_critical hf.continuous hfc 0
  rw [Complex.ofReal_zero, zero_mul, add_zero] at h
  rw [← h]
  congr 1
  push_cast
  ring

/-- `H(½ + r) = f̂(−ir) · conj f̂(ir)` for every test and real `r`. -/
theorem Hfn_weilTest_half_add_ofReal_general {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (r : ℝ) :
    Hfn (EF.weilTest f f) ((1 / 2 : ℂ) + r) = paperFT f (-(I * r)) * conj (paperFT f (I * r)) := by
  unfold Hfn
  have e : ((1 / 2 : ℂ) + r - 1 / 2) / I = -(I * r) := by
    rw [add_sub_cancel_left, div_eq_mul_inv, Complex.inv_I]; ring
  rw [e, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, map_neg, map_mul, Complex.conj_I,
    Complex.conj_ofReal, neg_mul, neg_neg]

/-- For an even test `H(½ + r) = |f̂(ir)|²`. -/
theorem Hfn_weilTest_half_add_ofReal_of_even {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (heven : ∀ x, f (-x) = f x) (r : ℝ) :
    Hfn (EF.weilTest f f) ((1 / 2 : ℂ) + r) = ((‖paperFT f (I * r)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Hfn_weilTest_half_add_ofReal_general hf hfc, paperFT_neg_of_even heven, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-! ## The spectral representation on every test -/

/-- **The spectral representation of the full Weil functional on an arbitrary test.**
`Re W_lam(f ⋆ f̃) = ∫ Θ_f(e^{iθ}) dν(θ) − c |f̂(0)|²`. -/
theorem re_weilFullFunctional_eq_integral_spectralWeight_sub {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (weilFullFunctional lam (EF.weilTest f f)).re =
      (∫ θ, oddSpectralWeight f (circleMap 0 1 θ) ∂ν) - c * ‖paperFT f 0‖ ^ 2 := by
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨D, hD0, hD⟩ := exists_norm_lineTransform_le hf hfc
  have hFc : Continuous (lineTransform f) := continuous_lineTransform hf hfc
  have hFi : Integrable (lineTransform f) := integrable_lineTransform hf hfc
  have hae : ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 ∨ -(1 / 4) ≤ circleOrd (circleMap 0 1 θ) :=
    ae_support_of_measure_eq_zero hsupp
  set g : ℝ × ℝ → ℂ := fun p => lineTransform f p.1 * oddLineKernel (circleMap 0 1 p.2) (linePt p.1)
    with hg
  have hgm : Measurable g := (hFc.measurable.comp measurable_fst).mul measurable_oddLineKernel_prod
  set M : ℝ := ν.real univ with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ t : ℝ, t ≠ 0 →
      ∀ᵐ θ ∂ν, ‖g (t, θ)‖ ≤ ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) := by
    intro t ht
    filter_upwards [hae] with θ hθ
    simp only [hg, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_oddLineKernel_le ht (norm_circleMap_one θ) hθ)
      (norm_nonneg _)
  have hint : ∀ t : ℝ, t ≠ 0 → Integrable (fun θ => g (t, θ)) ν := fun t ht =>
    Integrable.mono' (integrable_const (‖lineTransform f t‖ * (44 * (1 + t ^ 2))))
      (hgm.comp measurable_prodMk_left).aestronglyMeasurable (hpt t ht)
  have hgi : Integrable g (volume.prod ν) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    constructor
    · filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      exact hint t ht
    · refine (integrable_inv_one_add_sq.const_mul (2 * D * 44 * M)).mono'
        hgm.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
      calc ∫ θ, ‖g (t, θ)‖ ∂ν ≤ ∫ _θ, ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) ∂ν :=
            integral_mono_ae (hint t ht).norm (integrable_const _) (hpt t ht)
        _ = ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) * M := by
            rw [integral_const, smul_eq_mul, hM]; ring
        _ ≤ 2 * D / (1 + t ^ 2) ^ 2 * (44 * (1 + t ^ 2)) * M := by gcongr; exact hD t
        _ = 2 * D * 44 * M * (1 + t ^ 2)⁻¹ := by field_simp
  rw [weilFullFunctional_eq_line_integral hsl hkd hkc (c := 5 / 4) (by norm_num) (by norm_num)]
  have hline : ∀ t : ℝ, (Hfn k (((5 / 4 : ℝ) : ℂ) + t * I) + Hfn k (1 - ((5 / 4 : ℝ) : ℂ) - t * I)) *
      weilFunction lam (((5 / 4 : ℝ) : ℂ) + t * I) = lineTransform f t * Ψ (linePt t) := by
    intro t
    rw [linePt_eq, ← hΨe _ (by simp; norm_num)]
    rfl
  simp_rw [hline]
  have hsub : ∀ᵐ t ∂volume, lineTransform f t * Ψ (linePt t) =
      (∫ θ, g (t, θ) ∂ν) - c * (lineTransform f t / lineA t) := by
    filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
    rw [slit_eq_integral_oddLineKernel hΨd hΨe hrep ht, mul_sub, ← integral_const_mul]
    simp only [hg]
    ring
  have hci : Integrable fun t => c * (lineTransform f t / lineA t) := by
    refine (hFi.norm.const_mul (|c| * (4 / 3))).mono'
      ((hFc.div continuous_lineA fun t => lineA_ne_zero t).const_mul (c : ℂ)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have h34 := norm_lineA_ge t
    have : ‖lineTransform f t‖ / ‖lineA t‖ ≤ ‖lineTransform f t‖ * (4 / 3) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (lineTransform f t)]
    calc |c| * (‖lineTransform f t‖ / ‖lineA t‖) ≤ |c| * (‖lineTransform f t‖ * (4 / 3)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg c)
      _ = |c| * (4 / 3) * ‖lineTransform f t‖ := by ring
  have hswap : (∫ t, ∫ θ, g (t, θ) ∂ν) = ∫ θ, (∫ t, g (t, θ)) ∂ν :=
    integral_integral_swap (f := fun t θ => g (t, θ)) hgi
  rw [integral_congr_ae hsub, integral_sub hgi.integral_prod_left hci, hswap, integral_const_mul]
  -- the `c`-term: `(1/2π) ∫ F/(w − ½) = H(½) = |f̂(0)|²`
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hkd hkc
  have hH := differentiable_Hfn hkd hkc
  have hpair := two_line_pair hH (c := 5 / 4) (C := C)
    (fun σ t h1 h2 => hC σ t (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith))
    (z₀ := 1 / 2) (by norm_num) (by norm_num)
  have hH0 : Hfn k (1 / 2) = ((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ) := Hfn_weilTest_half hf hfc
  have hgp : ∀ t : ℝ, lineTransform f t / lineA t =
      (lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I)) / 2 := by
    intro t
    unfold gPair
    rw [← linePt_eq, linePt_sub_half, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, linePt_sub_half]
    have := lineA_ne_zero t
    field_simp
    ring
  have hcterm : (1 / (2 * Real.pi) : ℂ) * ∫ t, lineTransform f t / lineA t =
      ((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hgp]
    rw [integral_div, ← mul_div_assoc]
    have e : (1 / (2 * Real.pi) : ℂ) *
        ∫ t, lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I) =
        Hfn k (1 / 2) + Hfn k (1 - 1 / 2) := by
      rw [← hpair]
      rfl
    rw [e, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hH0]
    ring
  rw [mul_sub, mul_left_comm, hcterm]
  have hJi : Integrable (fun θ => ∫ t, g (t, θ)) ν := hgi.integral_prod_right
  have hre : (∫ θ, (∫ t, g (t, θ)) ∂ν).re = ∫ θ, (∫ t, g (t, θ)).re ∂ν := by
    have h := integral_re hJi
    simp only [RCLike.re_to_complex] at h
    exact h.symm
  rw [Complex.sub_re, show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by
    push_cast; ring, Complex.re_ofReal_mul, hre, ← integral_const_mul]
  have hc : ((c : ℂ) * ((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ)).re = c * ‖paperFT f 0‖ ^ 2 := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hc]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [oddSpectralWeight]
  rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-! ## Evaluation of the spectral weight on an arbitrary test -/

/-- Partial-fraction evaluation off `ζ = ±1` for an arbitrary test:
`Θ_f(ζ) = Re[−|f̂(0)|²/γ + ((1 + γ²)/(2γ)) (H(½ + ρ) + H(½ − ρ))]`, `ρ² = −γ`. -/
theorem spectralWeight_eq_of_ne {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : circleOrd ζ ≠ 0) {ρ : ℂ} (hρ : ρ ^ 2 = -(circleOrd ζ : ℂ))
    (hρ1 : 1 - 5 / 4 < (1 / 2 + ρ).re) (hρ2 : (1 / 2 + ρ).re < 5 / 4) :
    oddSpectralWeight f ζ =
      (-(((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ) / circleOrd ζ) +
        ((1 + (circleOrd ζ : ℂ) ^ 2) / (2 * circleOrd ζ)) *
        (Hfn (EF.weilTest f f) (1 / 2 + ρ) + Hfn (EF.weilTest f f) (1 - (1 / 2 + ρ)))).re := by
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨C, -, hC⟩ := norm_Hfn_le hkd hkc
  have hH := differentiable_Hfn hkd hkc
  have hCs : ∀ σ t : ℝ, 1 - 5 / 4 ≤ σ → σ ≤ 5 / 4 → ‖Hfn k (σ + t * I)‖ ≤ C / (1 + t ^ 2) :=
    fun σ t h1 h2 => hC σ t (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  have hpair₀ := two_line_pair hH (c := 5 / 4) hCs (z₀ := 1 / 2) (by norm_num) (by norm_num)
  have hpairρ := two_line_pair hH (c := 5 / 4) hCs (z₀ := 1 / 2 + ρ) hρ1 hρ2
  have hH0 : Hfn k (1 / 2) = ((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ) := Hfn_weilTest_half hf hfc
  have hi₀ := integrable_lineTransform_mul_gPair hf hfc (z₀ := 1 / 2) (by norm_num) (by norm_num)
  have hiρ := integrable_lineTransform_mul_gPair hf hfc hρ1 hρ2
  set A : ℂ := -(1 / (circleOrd ζ : ℂ)) / 2 with hA
  set B : ℂ := (1 + (circleOrd ζ : ℂ) ^ 2) / (2 * circleOrd ζ) with hB
  have hsplit : ∀ᵐ t ∂volume, lineTransform f t * oddLineKernel ζ (linePt t) =
      A * (lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I)) +
        B * (lineTransform f t * gPair (1 / 2 + ρ) (((5 / 4 : ℝ) : ℂ) + t * I)) := by
    filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
    rw [oddLineKernel_eq_gPair ht hζ h1 hγ hρ, ← linePt_eq, hA, hB]
    ring
  unfold oddSpectralWeight
  rw [integral_congr_ae hsplit, integral_add (hi₀.const_mul A) (hiρ.const_mul B),
    integral_const_mul, integral_const_mul, mul_add, mul_left_comm, mul_left_comm (1 / (2 * Real.pi : ℂ))]
  have e₀ : (1 / (2 * Real.pi) : ℂ) *
      ∫ t, lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I) =
      Hfn k (1 / 2) + Hfn k (1 - 1 / 2) := by rw [← hpair₀]; rfl
  have eρ : (1 / (2 * Real.pi) : ℂ) *
      ∫ t, lineTransform f t * gPair (1 / 2 + ρ) (((5 / 4 : ℝ) : ℂ) + t * I) =
      Hfn k (1 / 2 + ρ) + Hfn k (1 - (1 / 2 + ρ)) := by rw [← hpairρ]; rfl
  rw [e₀, eρ, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hH0]
  congr 1
  rw [hA]
  ring

/-- **On the critical ordinates** (`γ > 0`), for an arbitrary test:
`Θ_f(ζ) = [(1 + γ²)(|f̂(√γ)|² + |f̂(−√γ)|²)/2 − |f̂(0)|²]/γ`. -/
theorem spectralWeight_eq_of_pos {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) (hγ : 0 < circleOrd ζ) :
    oddSpectralWeight f ζ =
      ((1 + circleOrd ζ ^ 2) * ((‖paperFT f (Real.sqrt (circleOrd ζ))‖ ^ 2 +
        ‖paperFT f (-Real.sqrt (circleOrd ζ))‖ ^ 2) / 2) - ‖paperFT f 0‖ ^ 2) / circleOrd ζ := by
  have hr2 : Real.sqrt (circleOrd ζ) ^ 2 = circleOrd ζ := Real.sq_sqrt hγ.le
  have hρ : ((Real.sqrt (circleOrd ζ) : ℂ) * I) ^ 2 = -(circleOrd ζ : ℂ) := by
    rw [mul_pow, I_sq, ← Complex.ofReal_pow, hr2]; ring
  rw [spectralWeight_eq_of_ne hf hfc hζ h1 hγ.ne' hρ (by simp; norm_num) (by simp; norm_num)]
  have ha : (1 / 2 : ℂ) + (Real.sqrt (circleOrd ζ) : ℂ) * I =
      ((1 / 2 : ℝ) : ℂ) + Real.sqrt (circleOrd ζ) * I := by push_cast; ring
  have hb : (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + (Real.sqrt (circleOrd ζ) : ℂ) * I) =
      ((1 / 2 : ℝ) : ℂ) - Real.sqrt (circleOrd ζ) * I := by push_cast; ring
  rw [ha, hb, Hfn_weilTest_critical hf.continuous hfc, Hfn_weilTest_critical_neg hf.continuous hfc]
  have hγ0 : (circleOrd ζ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have e : -(((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ) / circleOrd ζ) +
      ((1 + (circleOrd ζ : ℂ) ^ 2) / (2 * circleOrd ζ)) *
      (((‖paperFT f (Real.sqrt (circleOrd ζ))‖ ^ 2 : ℝ) : ℂ) +
        ((‖paperFT f (-Real.sqrt (circleOrd ζ))‖ ^ 2 : ℝ) : ℂ)) =
      ((((1 + circleOrd ζ ^ 2) * ((‖paperFT f (Real.sqrt (circleOrd ζ))‖ ^ 2 +
        ‖paperFT f (-Real.sqrt (circleOrd ζ))‖ ^ 2) / 2) - ‖paperFT f 0‖ ^ 2) /
        circleOrd ζ : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [e, Complex.ofReal_re]

/-- **On the cut** (`−¼ ≤ γ < 0`), for an even test:
`Θ_f(ζ) = [|f̂(0)|² − (1 + γ²)|f̂(i√(−γ))|²]/(−γ)`. -/
theorem spectralWeight_eq_of_neg_of_even {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (heven : ∀ x, f (-x) = f x) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : -(1 / 4) ≤ circleOrd ζ) (hγ' : circleOrd ζ < 0) :
    oddSpectralWeight f ζ =
      (‖paperFT f 0‖ ^ 2 -
        (1 + circleOrd ζ ^ 2) * ‖paperFT f (I * Real.sqrt (-circleOrd ζ))‖ ^ 2) /
        (-circleOrd ζ) := by
  have hr2 : Real.sqrt (-circleOrd ζ) ^ 2 = -circleOrd ζ := Real.sq_sqrt (by linarith)
  have hρ : ((Real.sqrt (-circleOrd ζ) : ℂ)) ^ 2 = -(circleOrd ζ : ℂ) := by
    rw [← Complex.ofReal_pow, hr2]; push_cast; ring
  have hr12 : Real.sqrt (-circleOrd ζ) ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hr0 : 0 ≤ Real.sqrt (-circleOrd ζ) := Real.sqrt_nonneg _
  rw [spectralWeight_eq_of_ne hf hfc hζ h1 hγ'.ne hρ (by simp; linarith) (by simp; linarith)]
  have hb : (1 : ℂ) - (1 / 2 + (Real.sqrt (-circleOrd ζ) : ℂ)) =
      (1 / 2 : ℂ) + ((-Real.sqrt (-circleOrd ζ) : ℝ) : ℂ) := by push_cast; ring
  rw [hb, Hfn_weilTest_half_add_ofReal_of_even hf hfc heven,
    Hfn_weilTest_half_add_ofReal_of_even hf hfc heven]
  have hneg : paperFT f (I * ((-Real.sqrt (-circleOrd ζ) : ℝ) : ℂ)) =
      paperFT f (I * Real.sqrt (-circleOrd ζ)) := by
    rw [← paperFT_neg_of_even heven]; congr 1; push_cast; ring
  rw [hneg]
  have hγ0 : (circleOrd ζ : ℂ) ≠ 0 := by exact_mod_cast hγ'.ne
  have e : -(((‖paperFT f 0‖ ^ 2 : ℝ) : ℂ) / circleOrd ζ) +
      ((1 + (circleOrd ζ : ℂ) ^ 2) / (2 * circleOrd ζ)) *
      (((‖paperFT f (I * Real.sqrt (-circleOrd ζ))‖ ^ 2 : ℝ) : ℂ) +
        ((‖paperFT f (I * Real.sqrt (-circleOrd ζ))‖ ^ 2 : ℝ) : ℂ)) =
      (((‖paperFT f 0‖ ^ 2 -
        (1 + circleOrd ζ ^ 2) * ‖paperFT f (I * Real.sqrt (-circleOrd ζ))‖ ^ 2) /
        (-circleOrd ζ) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [e, Complex.ofReal_re]

/-! ## The centre by continuity -/

/-- The spectral weight at the centre is the limit of its values along `bdryPt(1/(n+1))`. -/
theorem tendsto_spectralWeight_bdryPt {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun n : ℕ => oddSpectralWeight f (bdryPt (1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (oddSpectralWeight f (-1))) := by
  set ζn : ℕ → ℂ := fun n => bdryPt (1 / ((n : ℝ) + 1)) with hζn
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hseq : Tendsto ζn atTop (𝓝 (-1)) := by
    rw [← bdryPt_zero]
    exact continuous_bdryPt.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨D, hD0, hD⟩ := exists_norm_lineTransform_le hf hfc
  have hFc := continuous_lineTransform hf hfc
  unfold oddSpectralWeight
  refine (Complex.continuous_re.tendsto _).comp (Tendsto.const_mul _ ?_)
  refine tendsto_integral_of_dominated_convergence
    (fun t => 2 * D / (1 + t ^ 2) ^ 2 * (44 * (1 + t ^ 2))) ?_ ?_ ?_ ?_
  · intro n
    exact (hFc.measurable.mul (measurable_oddLineKernel_linePt _)).aestronglyMeasurable
  · have : Integrable fun t : ℝ => 2 * D * 44 * (1 + t ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul _
    refine this.congr (Eventually.of_forall fun t => ?_)
    field_simp
  · intro n
    filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
    rw [norm_mul]
    exact mul_le_mul (hD t) (norm_oddLineKernel_le ht (norm_bdryPt _)
      (Or.inr (by rw [circleOrd_bdryPt]; linarith [hpos n]))) (norm_nonneg _) (by positivity)
  · filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
    exact Tendsto.const_mul _ ((continuousAt_oddLineKernel_neg_one ht).tendsto.comp hseq)

/-- For a mean-zero test the weight is nonnegative on the critical ordinates. -/
theorem spectralWeight_nonneg_of_pos_of_meanZero {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (h0 : paperFT f 0 = 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : 0 < circleOrd ζ) : 0 ≤ oddSpectralWeight f ζ := by
  rw [spectralWeight_eq_of_pos hf hfc hζ h1 hγ, h0, norm_zero, zero_pow two_ne_zero, sub_zero]
  positivity

/-- For a mean-zero test the weight is nonnegative at the centre. -/
theorem spectralWeight_neg_one_nonneg_of_meanZero {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (h0 : paperFT f 0 = 0) : 0 ≤ oddSpectralWeight f (-1) :=
  ge_of_tendsto' (tendsto_spectralWeight_bdryPt hf hfc) fun n =>
    spectralWeight_nonneg_of_pos_of_meanZero hf hfc h0 (norm_bdryPt _) (bdryPt_ne_one _)
      (by rw [circleOrd_bdryPt]; positivity)

/-- A uniform bound on the critical ordinates bounds the central value. -/
theorem spectralWeight_neg_one_le_of_forall_pos {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {M : ℝ}
    (hM : ∀ ζ : ℂ, ‖ζ‖ = 1 → ζ ≠ 1 → 0 < circleOrd ζ → oddSpectralWeight f ζ ≤ M) :
    oddSpectralWeight f (-1) ≤ M :=
  le_of_tendsto' (tendsto_spectralWeight_bdryPt hf hfc) fun n =>
    hM _ (norm_bdryPt _) (bdryPt_ne_one _) (by rw [circleOrd_bdryPt]; positivity)

/-- For a mean-zero test the weight is nonnegative off the cut. -/
theorem spectralWeight_nonneg_of_meanZero_of_not_cut {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (h0 : paperFT f 0 = 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hs : ζ = 1 ∨ 0 ≤ circleOrd ζ) : 0 ≤ oddSpectralWeight f ζ := by
  by_cases h1 : ζ = 1
  · rw [h1, oddSpectralWeight_one hf hfc]
  · have hγ : 0 ≤ circleOrd ζ := hs.resolve_left h1
    rcases hγ.lt_or_eq with hpos | hzero
    · exact spectralWeight_nonneg_of_pos_of_meanZero hf hfc h0 hζ h1 hpos
    · have : ζ = -1 := by rw [eq_bdryPt_circleOrd hζ h1, ← hzero, bdryPt_zero]
      rw [this]
      exact spectralWeight_neg_one_nonneg_of_meanZero hf hfc h0

/-! ## Integrability of the spectral weight -/

/-- The spectral weight is `ν`-integrable along the circle. -/
theorem integrable_spectralWeight_circleMap {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun θ => oddSpectralWeight f (circleMap 0 1 θ)) ν := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_lineTransform_le hf hfc
  have hFc : Continuous (lineTransform f) := continuous_lineTransform hf hfc
  have hae : ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 ∨ -(1 / 4) ≤ circleOrd (circleMap 0 1 θ) :=
    ae_support_of_measure_eq_zero hsupp
  set g : ℝ × ℝ → ℂ := fun p => lineTransform f p.1 * oddLineKernel (circleMap 0 1 p.2) (linePt p.1)
    with hg
  have hgm : Measurable g := (hFc.measurable.comp measurable_fst).mul measurable_oddLineKernel_prod
  set M : ℝ := ν.real univ with hM
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ t : ℝ, t ≠ 0 →
      ∀ᵐ θ ∂ν, ‖g (t, θ)‖ ≤ ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) := by
    intro t ht
    filter_upwards [hae] with θ hθ
    simp only [hg, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_oddLineKernel_le ht (norm_circleMap_one θ) hθ)
      (norm_nonneg _)
  have hint : ∀ t : ℝ, t ≠ 0 → Integrable (fun θ => g (t, θ)) ν := fun t ht =>
    Integrable.mono' (integrable_const (‖lineTransform f t‖ * (44 * (1 + t ^ 2))))
      (hgm.comp measurable_prodMk_left).aestronglyMeasurable (hpt t ht)
  have hgi : Integrable g (volume.prod ν) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    constructor
    · filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      exact hint t ht
    · refine (integrable_inv_one_add_sq.const_mul (2 * D * 44 * M)).mono'
        hgm.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
      calc ∫ θ, ‖g (t, θ)‖ ∂ν ≤ ∫ _θ, ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) ∂ν :=
            integral_mono_ae (hint t ht).norm (integrable_const _) (hpt t ht)
        _ = ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) * M := by
            rw [integral_const, smul_eq_mul, hM]; ring
        _ ≤ 2 * D / (1 + t ^ 2) ^ 2 * (44 * (1 + t ^ 2)) * M := by gcongr; exact hD t
        _ = 2 * D * 44 * M * (1 + t ^ 2)⁻¹ := by field_simp
  have hJi : Integrable (fun θ => ∫ t, g (t, θ)) ν := hgi.integral_prod_right
  have e : (fun θ => oddSpectralWeight f (circleMap 0 1 θ)) =
      fun θ => ((1 / (2 * Real.pi) : ℂ) * ∫ t, g (t, θ)).re := by
    funext θ
    simp only [oddSpectralWeight, hg]
  rw [e]
  exact (hJi.const_mul _).re

/-! ## The two-bump even mean-zero test -/

/-- `f_L = b(· − L) − 2 b + b(· + L)` for a real profile `b`. -/
def twoBumpTest (b : ℝ → ℝ) (L : ℝ) (x : ℝ) : ℂ :=
  (b (x - L) : ℂ) - 2 * (b x : ℂ) + (b (x + L) : ℂ)

theorem twoBumpTest_neg {b : ℝ → ℝ} (hb : ∀ x, b (-x) = b x) (L x : ℝ) :
    twoBumpTest b L (-x) = twoBumpTest b L x := by
  unfold twoBumpTest
  rw [show -x - L = -(x + L) by ring, show -x + L = -(x - L) by ring, hb, hb, hb]
  ring

theorem contDiff_twoBumpTest {b : ℝ → ℝ} (hb : ContDiff ℝ 2 b) (L : ℝ) :
    ContDiff ℝ 2 (twoBumpTest b L) := by
  unfold twoBumpTest
  have h1 : ContDiff ℝ 2 fun x : ℝ => (b (x - L) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hb.comp (contDiff_id.sub contDiff_const))
  have h2 : ContDiff ℝ 2 fun x : ℝ => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp hb
  have h3 : ContDiff ℝ 2 fun x : ℝ => (b (x + L) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hb.comp (contDiff_id.add contDiff_const))
  exact (h1.sub (contDiff_const.mul h2)).add h3

theorem hasCompactSupport_twoBumpTest {b : ℝ → ℝ} (hbc : HasCompactSupport b) (L : ℝ) :
    HasCompactSupport (twoBumpTest b L) := by
  have h1 : HasCompactSupport fun x : ℝ => (b (x - L) : ℂ) :=
    (hbc.comp_homeomorph (Homeomorph.subRight L)).comp_left Complex.ofReal_zero
  have h2 : HasCompactSupport fun x : ℝ => (b x : ℂ) := hbc.comp_left Complex.ofReal_zero
  have h3 : HasCompactSupport fun x : ℝ => (b (x + L) : ℂ) :=
    (hbc.comp_homeomorph (Homeomorph.addRight L)).comp_left Complex.ofReal_zero
  exact (h1.sub (h2.mul_left)).add h3

/-- Translation multiplies the transform by `e^{izx}`. -/
theorem paperFT_comp_sub_const (h : ℝ → ℂ) (x : ℝ) (z : ℂ) :
    paperFT (fun u => h (u - x)) z = Complex.exp (I * z * x) * paperFT h z := by
  unfold paperFT
  have := integral_sub_right_eq_self (μ := volume)
    (fun v : ℝ => h v * Complex.exp (I * z * ((v + x : ℝ) : ℂ))) x
  simp only [sub_add_cancel] at this
  rw [this, ← integral_const_mul]
  congr 1; funext v
  push_cast
  rw [mul_add, Complex.exp_add]; ring

/-- The transform of the two-bump test: `(e^{izL} + e^{−izL} − 2) b̂(z)`. -/
theorem paperFT_twoBumpTest {b : ℝ → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (L : ℝ) (z : ℂ) :
    paperFT (twoBumpTest b L) z =
      (Complex.exp (I * z * L) + Complex.exp (-(I * z * L)) - 2) *
        paperFT (fun x => (b x : ℂ)) z := by
  set g : ℝ → ℂ := fun x => (b x : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp hb
  have hgs : HasCompactSupport g := hbc.comp_left Complex.ofReal_zero
  have hi : ∀ (k : ℝ → ℂ), Continuous k → HasCompactSupport k →
      Integrable fun u : ℝ => k u * Complex.exp (I * z * u) := fun k hk hkc =>
    (hk.mul (by fun_prop)).integrable_of_hasCompactSupport hkc.mul_right
  have h1 : paperFT (fun u : ℝ => g (u - L)) z = Complex.exp (I * z * L) * paperFT g z :=
    paperFT_comp_sub_const g L z
  have h3 : paperFT (fun u : ℝ => g (u + L)) z = Complex.exp (-(I * z * L)) * paperFT g z := by
    have := paperFT_comp_sub_const g (-L) z
    simp only [sub_neg_eq_add, Complex.ofReal_neg] at this
    rw [this]
    congr 2
    ring
  have hsplit : twoBumpTest b L = fun u => (fun u => g (u - L)) u - 2 * g u + (fun u => g (u + L)) u := by
    funext u; simp only [twoBumpTest, hg]
  rw [hsplit]
  have e : ∀ u : ℝ, ((fun u => g (u - L)) u - 2 * g u + (fun u => g (u + L)) u) *
      Complex.exp (I * z * u) =
      g (u - L) * Complex.exp (I * z * u) - 2 * (g u * Complex.exp (I * z * u)) +
        g (u + L) * Complex.exp (I * z * u) := by intro u; ring
  unfold paperFT
  simp_rw [e]
  rw [integral_add, integral_sub, integral_const_mul]
  · change paperFT (fun u => g (u - L)) z - 2 * paperFT g z + paperFT (fun u => g (u + L)) z =
      (Complex.exp (I * z * L) + Complex.exp (-(I * z * L)) - 2) * paperFT g z
    rw [h1, h3]
    ring
  · exact hi _ (hgc.comp (continuous_id.sub continuous_const))
      ((hgs.comp_homeomorph (Homeomorph.subRight L)))
  · exact (hi g hgc hgs).const_mul 2
  · exact (hi _ (hgc.comp (continuous_id.sub continuous_const))
      ((hgs.comp_homeomorph (Homeomorph.subRight L)))).sub ((hi g hgc hgs).const_mul 2)
  · exact hi _ (hgc.comp (continuous_id.add continuous_const))
      ((hgs.comp_homeomorph (Homeomorph.addRight L)))

theorem paperFT_twoBumpTest_zero {b : ℝ → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (L : ℝ) : paperFT (twoBumpTest b L) 0 = 0 := by
  rw [paperFT_twoBumpTest hb hbc]
  simp only [mul_zero, zero_mul, neg_zero, Complex.exp_zero]
  norm_num

/-- On the real line: `|f̂_L(v)| = 2(1 − cos(vL)) |b̂(v)|`. -/
theorem norm_paperFT_twoBumpTest_ofReal {b : ℝ → ℝ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (L v : ℝ) :
    ‖paperFT (twoBumpTest b L) v‖ = 2 * (1 - Real.cos (v * L)) * ‖paperFT (fun x => (b x : ℂ)) v‖ := by
  rw [paperFT_twoBumpTest hb hbc, norm_mul]
  congr 1
  have e : Complex.exp (I * v * L) + Complex.exp (-(I * v * L)) - 2 =
      ((2 * (Real.cos (v * L) - 1) : ℝ) : ℂ) := by
    have h := Complex.two_cos ((v * L : ℝ) : ℂ)
    push_cast at h ⊢
    rw [show I * v * L = (v * L) * I by ring, show -((v : ℂ) * L * I) = -(v * L) * I by ring,
      ← h]
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith [Real.cos_le_one (v * L)])]
  ring

/-- The exponential moment `∫ b(u) e^{−ru} du`. -/
def expMoment (b : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u, b u * Real.exp (-(r * u))

theorem paperFT_ofReal_I_mul (b : ℝ → ℝ) (r : ℝ) :
    paperFT (fun x => (b x : ℂ)) (I * r) = ((expMoment b r : ℝ) : ℂ) := by
  unfold paperFT expMoment
  rw [← integral_complex_ofReal]
  congr 1; funext u
  simp only
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- For an even nonnegative profile the exponential moment dominates the mass. -/
theorem integral_le_expMoment {b : ℝ → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (hbn : ∀ x, 0 ≤ b x) (hbe : ∀ x, b (-x) = b x) (r : ℝ) :
    ∫ u, b u ≤ expMoment b r := by
  have hi : ∀ s : ℝ, Integrable fun u : ℝ => b u * Real.exp (-(s * u)) := fun s =>
    (hb.mul (by fun_prop)).integrable_of_hasCompactSupport hbc.mul_right
  have hrefl : expMoment b r = ∫ u, b u * Real.exp (r * u) := by
    unfold expMoment
    rw [← integral_neg_eq_self]
    congr 1; funext u
    rw [hbe]; congr 2; ring
  have h2 : 2 * expMoment b r = ∫ u, b u * (Real.exp (-(r * u)) + Real.exp (r * u)) := by
    have := integral_add (hi r) (by simpa using hi (-r))
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    unfold expMoment
    rw [← integral_add (hi r) (by simpa using hi (-r))]
    congr 1; funext u; ring
  have h3 : ∫ u, 2 * b u ≤ ∫ u, b u * (Real.exp (-(r * u)) + Real.exp (r * u)) := by
    refine integral_mono ((hb.integrable_of_hasCompactSupport hbc).const_mul 2) ?_ fun u => ?_
    · have := (hi r).add (by simpa using hi (-r))
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [Pi.add_apply]
      ring
    · have hc : 2 ≤ Real.exp (-(r * u)) + Real.exp (r * u) := by
        have := Real.one_le_cosh (r * u)
        rw [Real.cosh_eq] at this
        linarith
      nlinarith [hbn u]
  rw [integral_const_mul] at h3
  linarith

/-- On the imaginary axis: `f̂_L(ir) = (2 cosh(rL) − 2) · expMoment b r`. -/
theorem paperFT_twoBumpTest_I_mul {b : ℝ → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (L r : ℝ) :
    paperFT (twoBumpTest b L) (I * r) = (((2 * Real.cosh (r * L) - 2) * expMoment b r : ℝ) : ℂ) := by
  rw [paperFT_twoBumpTest hb hbc, paperFT_ofReal_I_mul]
  have e : Complex.exp (I * (I * r) * L) + Complex.exp (-(I * (I * r) * L)) - 2 =
      ((2 * Real.cosh (r * L) - 2 : ℝ) : ℂ) := by
    rw [show I * (I * r) * L = ((-(r * L) : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring,
      show -(((-(r * L) : ℝ) : ℂ)) = ((r * L : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.cosh_eq]
    push_cast
    ring
  rw [e, ← Complex.ofReal_mul]

end RHTower.OddResolvent
