import GaloisForLFunctions.ArithmeticPolarization.TheCollidedFormIsCoerciveAtEveryAperture
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AnnihilatingTestsForSparseSpectra
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity

/-!
# The collided form is the logarithmic Sobolev norm

**Theorem** (`collidedForm_equiv_logSobolev`). For every aperture `A > 0` there are `0 < c ≤ C`
with

  `c ∫ |f̂(σ)|² log(|σ| + 4) dσ ≤ D(f) ≤ C ∫ |f̂(σ)|² log(|σ| + 4) dσ`

for every `C²` test supported in `[−A, A]`: on each aperture the collided polarization is the
logarithmic Sobolev norm, the norm of `L²` with the density of the zeros as weight.

* **Upper bound** (`collidedForm_le_log`). At a zero `ρ = ½ + a + iγ` the value `f̂(ρ)` is a
  convolution of the line values of `f̂` with the transform `K_a(r) = χ̂(r − ia)` of a fixed cutoff
  `χ ≡ 1` on `[−A, A]` (`tr_eq_integral_conv`, Fourier inversion of `χ e^{a·}`), and
  `|K_a(r)| ≤ B/(1 + r²)` uniformly in `|a| ≤ ½`. By Cauchy–Schwarz
  `|f̂(ρ)|² ≤ B′ ∫ |f̂(σ)|²/(1 + (γ − σ)²)` (`normSq_tr_le_local`), and the Lorentzian zero mass
  `Σ_ρ 1/(1 + (σ − γ)²)` is `O(log(|σ| + 4))`.
* **Lower bound** (`log_le_collidedForm`). The explicit-formula density exceeds
  `(1/4π) log(|σ| + 4)` above a height `T₁`, so `Re W ≥ (1/4π) ∫ |f̂|² log − K · lowMass`, and the
  low-frequency mass is controlled by `D` through coercivity.
-/

open Complex MeasureTheory Set Filter Topology Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23

/-! ### The smoothing kernel at a zero -/

/-- A `C²` cutoff equal to `1` on `[−A, A]` and supported in `[−A − 1, A + 1]`. -/
theorem exists_cutoff {A : ℝ} (hA : 0 < A) :
    ∃ χ : ℝ → ℂ, ContDiff ℝ 2 χ ∧ (∀ u, |u| ≤ A → χ u = 1) ∧ (∀ u, χ u ≠ 0 → |u| ≤ A + 1) := by
  let b : ContDiffBump (0 : ℝ) := ⟨A, A + 1, hA, by linarith⟩
  refine ⟨fun u => ((b u : ℝ) : ℂ), Complex.ofRealCLM.contDiff.comp (b.contDiff (n := 2)),
    fun u hu => ?_, fun u hu => ?_⟩
  · have : u ∈ Metric.closedBall (0 : ℝ) b.rIn := by
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hu
    simp [b.one_of_mem_closedBall this]
  · have h : b u ≠ 0 := fun h0 => hu (by simp [h0])
    have hs : u ∈ Function.support b := h
    rw [b.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    exact hs.le

/-- **Weighted Cauchy–Schwarz.** `(∫ w g)² ≤ (∫ w)(∫ w g²)` for `w ≥ 0`. -/
theorem sq_integral_mul_le {w g : ℝ → ℝ} (hw : ∀ r, 0 ≤ w r) (hwi : Integrable w)
    (hwgi : Integrable fun r => w r * g r) (hwg2 : Integrable fun r => w r * g r ^ 2) :
    (∫ r, w r * g r) ^ 2 ≤ (∫ r, w r) * ∫ r, w r * g r ^ 2 := by
  have hW : 0 ≤ ∫ r, w r := integral_nonneg hw
  rcases hW.eq_or_lt with h0 | hpos
  · -- `w = 0` a.e.
    have hz : w =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hw hwi).mp h0.symm
    have : ∫ r, w r * g r = 0 := by
      rw [integral_congr_ae (hz.mono fun r hr => by
        simp only [Pi.zero_apply] at hr ⊢; rw [hr, zero_mul])]
      simp
    rw [this, ← h0]; simp
  · set t := (∫ r, w r * g r) / ∫ r, w r
    have hint : Integrable fun r => w r * (g r - t) ^ 2 := by
      have : (fun r => w r * (g r - t) ^ 2) =
          fun r => w r * g r ^ 2 - 2 * t * (w r * g r) + t ^ 2 * w r := by funext r; ring
      rw [this]; exact (hwg2.sub (hwgi.const_mul _)).add (hwi.const_mul _)
    have hnn : 0 ≤ ∫ r, w r * (g r - t) ^ 2 :=
      integral_nonneg fun r => mul_nonneg (hw r) (sq_nonneg _)
    have i3 : Integrable fun r => 2 * t * (w r * g r) := hwgi.const_mul _
    have i1 : Integrable fun r => w r * g r ^ 2 - 2 * t * (w r * g r) := hwg2.sub i3
    have i2 : Integrable fun r => t ^ 2 * w r := hwi.const_mul _
    have hexp : ∫ r, w r * (g r - t) ^ 2 =
        (∫ r, w r * g r ^ 2) - 2 * t * (∫ r, w r * g r) + t ^ 2 * ∫ r, w r := by
      have : (fun r => w r * (g r - t) ^ 2) =
          fun r => w r * g r ^ 2 - 2 * t * (w r * g r) + t ^ 2 * w r := by funext r; ring
      rw [this, integral_add i1 i2, integral_sub hwg2 i3, integral_const_mul, integral_const_mul]
    rw [hexp] at hnn
    have ht : t * ∫ r, w r = ∫ r, w r * g r := div_mul_cancel₀ _ hpos.ne'
    nlinarith

/-- The transform of `χ e^{a·}` is `χ̂` shifted into the strip. -/
theorem paperFT_mul_exp (χ : ℝ → ℂ) (a r : ℝ) :
    paperFT (fun u => χ u * Complex.exp ((a : ℂ) * u)) r = paperFT χ ((r : ℂ) - I * a) := by
  rw [paperFT, paperFT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Uniform decay of the kernel in the strip.** `|χ̂(r − ia)| ≤ B/(1 + r²)` for `|a| ≤ ½`, with
`B` depending only on `χ` and its support. -/
theorem norm_paperFT_cutoff_le {χ : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A) (hχ : ContDiff ℝ 2 χ)
    (hχs : ∀ u, χ u ≠ 0 → |u| ≤ A + 1) {a : ℝ} (ha : |a| ≤ 1 / 2) (r : ℝ) :
    ‖paperFT χ ((r : ℂ) - I * a)‖ ≤
      Real.exp ((A + 1) / 2) * (4 * ((∫ u, ‖χ u‖) + ∫ u, ‖deriv (deriv χ) u‖)) *
        (1 + r ^ 2)⁻¹ := by
  have h := RHTower.norm_paperFT_le_decay hχ hχs ((r : ℂ) - I * a)
  have him : |((r : ℂ) - I * a).im| = |a| := by simp
  have hre : |((r : ℂ) - I * a).re| = |r| := by simp
  rw [him, hre] at h
  have hB : 0 ≤ 4 * ((∫ u, ‖χ u‖) + ∫ u, ‖deriv (deriv χ) u‖) := by
    have h1 : 0 ≤ ∫ u, ‖χ u‖ := integral_nonneg (f := fun u => ‖χ u‖) fun u => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv χ) u‖ :=
      integral_nonneg (f := fun u => ‖deriv (deriv χ) u‖) fun u => norm_nonneg _
    positivity
  have hA1 : 0 ≤ A + 1 := by linarith
  refine h.trans ?_
  have hexp : Real.exp (|a| * (A + 1)) ≤ Real.exp ((A + 1) / 2) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right ha hA1
    linarith
  have hsq : (1 + r ^ 2)⁻¹ ≥ ((1 + |r|) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith [abs_nonneg r, sq_abs r]
  calc Real.exp (|a| * (A + 1)) * (4 * ((∫ u, ‖χ u‖) + ∫ u, ‖deriv (deriv χ) u‖)) /
        (1 + |r|) ^ 2
      = Real.exp (|a| * (A + 1)) * (4 * ((∫ u, ‖χ u‖) + ∫ u, ‖deriv (deriv χ) u‖)) *
          ((1 + |r|) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ Real.exp ((A + 1) / 2) * (4 * ((∫ u, ‖χ u‖) + ∫ u, ‖deriv (deriv χ) u‖)) *
          (1 + r ^ 2)⁻¹ := by
        gcongr

/-- **The convolution representation at a point of the strip.** For `f` supported in `[−A, A]`
and a cutoff `χ ≡ 1` there, `f̂(s) = (1/2π) ∫ χ̂(r − ia) f̂(γ − r) dr`, `s = ½ + a + iγ`. -/
theorem tr_eq_integral_conv {A : ℝ} {χ : ℝ → ℂ} (hA : 0 ≤ A) (hχ : ContDiff ℝ 2 χ)
    (hχ1 : ∀ u, |u| ≤ A → χ u = 1) (hχs : ∀ u, χ u ≠ 0 → |u| ≤ A + 1) {f : ℝ → ℂ}
    (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-A) A) {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    tr f s = 1 / (2 * (π : ℂ)) *
      ∫ r : ℝ, paperFT χ ((r : ℂ) - I * ((s.re - 1 / 2 : ℝ) : ℂ)) * paperFT f ((s.im : ℂ) - r) := by
  set a : ℝ := s.re - 1 / 2 with hadef
  set γ : ℝ := s.im with hγdef
  set k : ℝ → ℂ := fun u => χ u * Complex.exp ((a : ℂ) * u) with hkdef
  set K : ℝ → ℂ := fun r => paperFT χ ((r : ℂ) - I * a) with hKdef
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have hkc : Continuous k := hχ.continuous.mul (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))
  have hkcs : HasCompactSupport k := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(A + 1)) (b := A + 1)) fun u hu => ?_
    have : χ u = 0 := by
      by_contra h
      exact hu (abs_le.mp (hχs u h))
    simp [hkdef, this]
  have hki : Integrable k := hkc.integrable_of_hasCompactSupport hkcs
  have hFk : ∀ r : ℝ, paperFT k r = K r := fun r => paperFT_mul_exp χ a r
  set B := Real.exp ((A + 1) / 2) * (4 * ((∫ u, ‖χ u‖) + ∫ u, ‖deriv (deriv χ) u‖)) with hBdef
  have hKb : ∀ r, ‖K r‖ ≤ B * (1 + r ^ 2)⁻¹ := fun r =>
    norm_paperFT_cutoff_le hA hχ hχs hs r
  have hKm : AEStronglyMeasurable K := by
    have : K = fun r : ℝ => paperFT k r := funext fun r => (hFk r).symm
    rw [this]
    exact (RHTower.KernelStrip.continuous_paperFT_of_integrable hki).aestronglyMeasurable
  have hKi : Integrable K :=
    Integrable.mono' (integrable_inv_one_add_sq.const_mul B) hKm
      (Filter.Eventually.of_forall hKb)
  -- inversion of `k`
  have hinv : ∀ u, k u = 1 / (2 * (π : ℂ)) * ∫ r : ℝ, K r * Complex.exp (-I * r * u) := by
    intro u
    have h := ArithmeticCastelnuovoSeveri.eq_invFT_paperFT hkc hki
      (by simpa only [hFk] using hKi) u
    rw [h, ArithmeticCastelnuovoSeveri.invFT]
    simp only [hFk]
  -- `f e^{(s − ½)u} = f k e^{iγu}`
  have hpt : ∀ u, f u * Complex.exp ((s - 1 / 2) * u) = f u * Complex.exp (I * γ * u) * k u := by
    intro u
    by_cases hu : f u = 0
    · rw [hu]; ring
    · have hχu : χ u = 1 := hχ1 u (abs_le.mpr (hfs (subset_tsupport f hu)))
      simp only [hkdef, hχu, one_mul]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      have hs' : s = ((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I := by
        apply Complex.ext <;> simp [hadef, hγdef]
      rw [hs']; push_cast; ring
  -- Fubini
  set F : ℝ → ℝ → ℂ := fun u r => f u * Complex.exp (I * γ * u) * (K r * Complex.exp (-I * r * u))
    with hFdef
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine Integrable.mono'
      ((hf.norm.integrable_of_hasCompactSupport hfc.norm).mul_prod hKi.norm) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact ((hf.aestronglyMeasurable.comp_fst).mul
        ((Complex.continuous_exp.comp (continuous_const.mul
          Complex.continuous_ofReal)).aestronglyMeasurable.comp_fst)).mul
        ((hKm.comp_snd).mul (Continuous.aestronglyMeasurable (by fun_prop)))
    · simp only [Function.uncurry, hFdef, norm_mul]
      rw [show ‖Complex.exp (I * γ * p.1)‖ = 1 by
          rw [Complex.norm_exp]; simp,
        show ‖Complex.exp (-I * p.2 * p.1)‖ = 1 by rw [Complex.norm_exp]; simp]
      ring_nf; rfl
  have hswap := integral_integral_swap hFint
  have hleft : tr f s = 1 / (2 * (π : ℂ)) * ∫ u, ∫ r, F u r := by
    rw [tr_eq, integral_congr_ae (Filter.Eventually.of_forall hpt), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show f u * Complex.exp (I * γ * u) * k u = 1 / (2 * (π : ℂ)) * ∫ r, F u r
    rw [hinv u, show (∫ r, F u r) = f u * Complex.exp (I * γ * u) *
      ∫ r, K r * Complex.exp (-I * r * u) from integral_const_mul _ _]
    ring
  rw [hleft, hswap]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  show ∫ u, F u r = K r * paperFT f ((γ : ℂ) - r)
  rw [paperFT, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hFdef]
  rw [show Complex.exp (I * ((γ : ℂ) - r) * u) =
      Complex.exp (I * γ * u) * Complex.exp (-I * r * u) by rw [← Complex.exp_add]; congr 1; ring]
  ring

/-! ### The local estimate at a point of the strip -/

/-- **The local estimate.** `|f̂(s)|² ≤ B ∫ |f̂(σ)|² / (1 + (Im s − σ)²)` uniformly in the strip. -/
theorem normSq_tr_le_local {A : ℝ} (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
      ∀ s : ℂ, |s.re - 1 / 2| ≤ 1 / 2 →
        Complex.normSq (tr f s) ≤ B * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + (s.im - σ) ^ 2)⁻¹ := by
  obtain ⟨χ, hχ, hχ1, hχs⟩ := exists_cutoff hA
  set B₁ := Real.exp ((A + 1) / 2) * (4 * ((∫ u, ‖χ u‖) + ∫ u, ‖deriv (deriv χ) u‖)) with hB₁
  have hB₁0 : 0 ≤ B₁ := by
    have h1 : 0 ≤ ∫ u, ‖χ u‖ := integral_nonneg (f := fun u => ‖χ u‖) fun u => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv χ) u‖ :=
      integral_nonneg (f := fun u => ‖deriv (deriv χ) u‖) fun u => norm_nonneg _
    positivity
  refine ⟨B₁ ^ 2 / (4 * π), by positivity, fun f hf hfs s hs => ?_⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  set γ := s.im
  set K : ℝ → ℂ := fun r => paperFT χ ((r : ℂ) - I * ((s.re - 1 / 2 : ℝ) : ℂ)) with hKdef
  have hKb : ∀ r, ‖K r‖ ≤ B₁ * (1 + r ^ 2)⁻¹ := fun r => norm_paperFT_cutoff_le hA.le hχ hχs hs r
  set g : ℝ → ℝ := fun r => ‖paperFT f ((γ : ℂ) - r)‖ with hgdef
  set w : ℝ → ℝ := fun r => ‖K r‖ with hwdef
  -- measurability and integrability
  have hFc : Continuous fun σ : ℝ => paperFT f σ :=
    RHTower.KernelStrip.continuous_paperFT_of_integrable
      (hf.continuous.integrable_of_hasCompactSupport hfc)
  have hgc : Continuous g := by
    have : g = fun r => ‖(fun σ : ℝ => paperFT f σ) (γ - r)‖ := by
      funext r; simp only [hgdef]; push_cast; rfl
    rw [this]; exact (hFc.comp (continuous_const.sub continuous_id)).norm
  have hKc : Continuous K := by
    have hk : Continuous fun u => χ u * Complex.exp (((s.re - 1 / 2 : ℝ) : ℂ) * u) :=
      hχ.continuous.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have hkcs : HasCompactSupport fun u => χ u * Complex.exp (((s.re - 1 / 2 : ℝ) : ℂ) * u) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -(A + 1)) (b := A + 1)) fun u hu => ?_
      have : χ u = 0 := by by_contra h; exact hu (abs_le.mp (hχs u h))
      simp [this]
    have := RHTower.KernelStrip.continuous_paperFT_of_integrable
      (hk.integrable_of_hasCompactSupport hkcs)
    have hfun : K = fun r : ℝ =>
        paperFT (fun u => χ u * Complex.exp (((s.re - 1 / 2 : ℝ) : ℂ) * u)) r :=
      funext fun r => (paperFT_mul_exp χ _ r).symm
    rw [hfun]; exact this
  have hwi : Integrable w :=
    Integrable.mono' (integrable_inv_one_add_sq.const_mul B₁) hKc.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
                                               exact hKb r)
  have hg_le : ∀ r, g r ≤ ∫ u, ‖f u‖ := fun r => by
    simp only [hgdef, paperFT]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [norm_mul, Complex.norm_exp]
    have : (I * ((γ : ℂ) - r) * u).re = 0 := by simp
    rw [this, Real.exp_zero, mul_one]
  have hwgi : Integrable fun r => w r * g r :=
    Integrable.mono' (hwi.mul_const (∫ u, ‖f u‖)) (hKc.norm.mul hgc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hg_le r) (norm_nonneg _))
  have hF2 := integrable_norm_sq_paperFT_of_tests hf hfc
  have hg2 : Integrable fun r => g r ^ 2 := by
    have : (fun r => g r ^ 2) = fun r => (fun σ : ℝ => ‖paperFT f σ‖ ^ 2) (γ - r) := by
      funext r; simp only [hgdef]; push_cast; rfl
    rw [this]; exact hF2.comp_sub_left γ
  have hwg2 : Integrable fun r => w r * g r ^ 2 :=
    Integrable.mono' (hg2.const_mul B₁) (hKc.norm.mul (hgc.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
        have h1 : (1 + r ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg r])
        calc w r * g r ^ 2 ≤ B₁ * (1 + r ^ 2)⁻¹ * g r ^ 2 :=
              mul_le_mul_of_nonneg_right (hKb r) (sq_nonneg _)
          _ ≤ B₁ * 1 * g r ^ 2 := by gcongr
          _ = B₁ * g r ^ 2 := by ring)
  -- the representation and Cauchy–Schwarz
  have hrep := tr_eq_integral_conv hA.le hχ hχ1 hχs hf.continuous hfs hs
  have hnorm : ‖tr f s‖ ≤ 1 / (2 * π) * ∫ r, w r * g r := by
    rw [hrep, norm_mul]
    have h2π : ‖1 / (2 * (π : ℂ))‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [h2π]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
      (by positivity)
    exact integral_congr_ae (Filter.Eventually.of_forall fun r => norm_mul _ _)
  have hcs := sq_integral_mul_le (fun r => norm_nonneg _) hwi hwgi hwg2
  have hw : ∫ r, w r ≤ B₁ * π := by
    calc ∫ r, w r ≤ ∫ r, B₁ * (1 + r ^ 2)⁻¹ :=
          integral_mono hwi (integrable_inv_one_add_sq.const_mul B₁) hKb
      _ = B₁ * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hwg : ∫ r, w r * g r ^ 2 ≤ B₁ * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + (γ - σ) ^ 2)⁻¹ := by
    have hint : Integrable fun r : ℝ => B₁ * ((1 + r ^ 2)⁻¹ * g r ^ 2) := by
      have hcinv : Continuous fun r : ℝ => (1 + r ^ 2)⁻¹ :=
        (continuous_const.add (continuous_id.pow 2)).inv₀ fun r =>
          (by positivity : (0 : ℝ) < 1 + r ^ 2).ne'
      refine (Integrable.mono' hg2 (hcinv.aestronglyMeasurable.mul (hgc.pow 2).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun r => ?_)).const_mul B₁
      have hpos : 0 ≤ (1 + r ^ 2)⁻¹ := by positivity
      show ‖(1 + r ^ 2)⁻¹ * g r ^ 2‖ ≤ g r ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos (sq_nonneg _))]
      have h1 : (1 + r ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg r])
      calc (1 + r ^ 2)⁻¹ * g r ^ 2 ≤ 1 * g r ^ 2 := by gcongr
        _ = g r ^ 2 := one_mul _
    calc ∫ r, w r * g r ^ 2 ≤ ∫ r : ℝ, B₁ * ((1 + r ^ 2)⁻¹ * g r ^ 2) :=
          integral_mono hwg2 hint fun r => by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hKb r) (sq_nonneg _)
      _ = B₁ * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + (γ - σ) ^ 2)⁻¹ := by
          rw [integral_const_mul]
          congr 1
          have : (fun r : ℝ => (1 + r ^ 2)⁻¹ * g r ^ 2) =
              fun r => (fun σ : ℝ => ‖paperFT f σ‖ ^ 2 * (1 + (γ - σ) ^ 2)⁻¹) (γ - r) := by
            funext r; simp only [hgdef]; push_cast; ring_nf
          rw [this]
          exact integral_sub_left_eq_self
            (fun σ : ℝ => ‖paperFT f σ‖ ^ 2 * (1 + (γ - σ) ^ 2)⁻¹) volume γ
  rw [Complex.normSq_eq_norm_sq]
  have hI : 0 ≤ ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + (γ - σ) ^ 2)⁻¹ :=
    integral_nonneg fun σ => mul_nonneg (sq_nonneg _) (by positivity)
  calc ‖tr f s‖ ^ 2 ≤ (1 / (2 * π) * ∫ r, w r * g r) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (1 / (2 * π)) ^ 2 * (∫ r, w r * g r) ^ 2 := by ring
    _ ≤ (1 / (2 * π)) ^ 2 * ((∫ r, w r) * ∫ r, w r * g r ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ (1 / (2 * π)) ^ 2 *
          ((B₁ * π) * (B₁ * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + (γ - σ) ^ 2)⁻¹)) := by
        gcongr
    _ = B₁ ^ 2 / (4 * π) * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + (γ - σ) ^ 2)⁻¹ := by
        field_simp; ring

/-! ### Summation over the zeros -/

theorem abs_re_sub_half_le (ρ : zetaZeroConfig.carrier) : |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 := by
  have h0 : 0 < (ρ : ℂ).re := ρ.2.2.1
  have h1 : (ρ : ℂ).re < 1 := ρ.2.2.2
  rw [abs_le]; constructor <;> linarith

/-- The logarithmic Sobolev weight is integrable against `|f̂|²` for every test. -/
theorem integrable_norm_sq_paperFT_mul_log {A : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-A) A) :
    Integrable fun σ : ℝ => ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4) := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ A := fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))
  set D₀ := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hD₀
  have hF2 := integrable_norm_sq_paperFT_of_tests hf hfc
  have hlogc : Continuous fun σ : ℝ => Real.log (|σ| + 4) :=
    (continuous_abs.add continuous_const).log fun σ => (by positivity : (0 : ℝ) < |σ| + 4).ne'
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (3 * D₀ ^ 2))
    (hF2.aestronglyMeasurable.mul hlogc.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun σ => ?_)
  -- `|f̂(σ)| ≤ D₀/(1 + |σ|)²` and `log(|σ| + 4) ≤ 3(1 + |σ|)`
  have hdec := RHTower.norm_paperFT_le_decay hf hsupp (σ : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
    Complex.ofReal_re] at hdec
  have ha : 0 ≤ ‖paperFT f σ‖ := norm_nonneg _
  have hlog0 : 0 ≤ Real.log (|σ| + 4) := Real.log_nonneg (by linarith [abs_nonneg σ])
  have hlog : Real.log (|σ| + 4) ≤ 3 * (1 + |σ|) := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < |σ| + 4)
    linarith [abs_nonneg σ]
  have had : ‖paperFT f σ‖ * (1 + |σ|) ^ 2 ≤ D₀ := by
    rwa [le_div_iff₀ (by positivity)] at hdec
  have h1 : (1 : ℝ) ≤ 1 + |σ| := by linarith [abs_nonneg σ]
  have hσ : 1 + σ ^ 2 ≤ (1 + |σ|) ^ 2 := by nlinarith [sq_abs σ, abs_nonneg σ]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hlog0), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4) * (1 + σ ^ 2)
      ≤ ‖paperFT f σ‖ ^ 2 * (3 * (1 + |σ|)) * (1 + |σ|) ^ 2 := by gcongr
    _ = 3 * (‖paperFT f σ‖ * (1 + |σ|) ^ 2) * (‖paperFT f σ‖ * (1 + |σ|)) := by ring
    _ ≤ 3 * (‖paperFT f σ‖ * (1 + |σ|) ^ 2) * (‖paperFT f σ‖ * (1 + |σ|) ^ 2) := by
        gcongr; exact le_self_pow₀ h1 (by norm_num)
    _ ≤ 3 * D₀ * D₀ := by gcongr
    _ = 3 * D₀ ^ 2 := by ring

/-- The zero mass of a finite set of zeros against the Lorentzian is at most the full
Lorentzian zero mass. -/
theorem sum_mult_lorentz_le (σ : ℝ) (S : Finset zetaZeroConfig.carrier) :
    ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ ≤
      RHTower.lorentzMass σ := by
  set g : ℂ → ℝ := fun z => 1 / (1 + (σ - z.im) ^ 2) with hgdef
  have hg0 : ∀ z, 0 ≤ g z := fun z => by positivity
  have hgs : Summable fun q : RHTower.XiZeroCopy => g (q.1 : ℂ) :=
    RHTower.summable_lorentzMassTerm σ
  have hL : RHTower.lorentzMass σ =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * g ρ :=
    ArithmeticCastelnuovoSeveri.tsum_xiZeroCopy_eq_zetaCarrier hgs
  rw [hL]
  have hpt : ∀ ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
      (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ = (zetaZeroConfig.mult ρ : ℝ) * g ρ := fun ρ => by
    simp only [hgdef, one_div]; congr 2; ring
  rw [Finset.sum_congr rfl fun ρ _ => hpt ρ]
  exact (ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy hg0 hgs).sum_le_tsum S
    fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (hg0 _)

/-- **Upper bound.** `D(f) ≤ C ∫ |f̂(σ)|² log(|σ| + 4)` on every aperture. -/
theorem collidedForm_le_log {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
      collidedForm zetaZeroConfig f ≤ C * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4) := by
  obtain ⟨B, hB0, hB⟩ := normSq_tr_le_local hA
  set c₀ := RHTower.xiLineTwoLogDerivConstant with hc₀
  have hc₀0 : 0 ≤ c₀ := RHTower.xiLineTwoLogDerivConstant_nonneg
  refine ⟨B * (8 * (c₀ + 1)), by positivity, fun f hf hfs => ?_⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  have hF2 := integrable_norm_sq_paperFT_of_tests hf hfc
  have hlogint := integrable_norm_sq_paperFT_mul_log hf hfs
  -- the Lorentzian zero mass is at most `8(c₀ + 1) log(|σ| + 4)`
  have hmass : ∀ σ : ℝ, RHTower.lorentzMass σ ≤ 8 * (c₀ + 1) * Real.log (|σ| + 4) := by
    intro σ
    have hl1 : 1 ≤ Real.log (|σ| + 4) := by
      rw [← Real.log_exp 1]
      refine Real.log_le_log (Real.exp_pos 1) ?_
      linarith [Real.exp_one_lt_d9, abs_nonneg σ]
    have := RHTower.lorentzMass_le_log σ
    nlinarith
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      Integrable fun σ : ℝ => ‖paperFT f σ‖ ^ 2 * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ := fun ρ => by
    have hc : Continuous fun σ : ℝ => (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ :=
      (continuous_const.add ((continuous_const.sub continuous_id).pow 2)).inv₀ fun σ =>
        (by positivity : (0 : ℝ) < 1 + ((ρ : ℂ).im - σ) ^ 2).ne'
    refine Integrable.mono' hF2 (hF2.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun σ => ?_)
    have hpos : 0 ≤ (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ := by positivity
    have hle : (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ((ρ : ℂ).im - σ)])
    show ‖‖paperFT f σ‖ ^ 2 * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹‖ ≤ ‖paperFT f σ‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpos)]
    exact mul_le_of_le_one_right (sq_nonneg _) hle
  refine (zeta_summable_collided hf hfc).tsum_le_of_sum_le fun S => ?_
  set m : zetaZeroConfig.carrier → ℝ := fun ρ => (zetaZeroConfig.mult ρ : ℝ) with hm
  have hfun : (fun σ : ℝ => ‖paperFT f σ‖ ^ 2 *
      ∑ ρ ∈ S, m ρ * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹) =
      fun σ : ℝ => ∑ ρ ∈ S, m ρ * (‖paperFT f σ‖ ^ 2 * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹) := by
    funext σ; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ρ _ => by ring
  have hsumint : Integrable fun σ : ℝ => ‖paperFT f σ‖ ^ 2 *
      ∑ ρ ∈ S, m ρ * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ := by
    rw [hfun]; exact integrable_finsetSum S fun ρ _ => (hterm ρ).const_mul _
  have hexch : ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * ∑ ρ ∈ S, m ρ * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ =
      ∑ ρ ∈ S, m ρ * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ := by
    rw [hfun, integral_finsetSum S fun ρ _ => (hterm ρ).const_mul _]
    exact Finset.sum_congr rfl fun ρ _ => integral_const_mul _ _
  calc ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr f ρ)
      ≤ ∑ ρ ∈ S, m ρ * (B * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹) :=
        Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left
          (hB f hf hfs ρ (abs_re_sub_half_le ρ)) (Nat.cast_nonneg _)
    _ = B * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * ∑ ρ ∈ S, m ρ * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹ := by
        rw [hexch, Finset.mul_sum]
        exact Finset.sum_congr rfl fun ρ _ => by ring
    _ ≤ B * ∫ σ : ℝ, (8 * (c₀ + 1)) * (‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4)) := by
        refine mul_le_mul_of_nonneg_left (integral_mono hsumint (hlogint.const_mul _)
          fun σ => ?_) hB0
        have h := (sum_mult_lorentz_le σ S).trans (hmass σ)
        calc ‖paperFT f σ‖ ^ 2 * ∑ ρ ∈ S, m ρ * (1 + ((ρ : ℂ).im - σ) ^ 2)⁻¹
            ≤ ‖paperFT f σ‖ ^ 2 * (8 * (c₀ + 1) * Real.log (|σ| + 4)) :=
              mul_le_mul_of_nonneg_left h (sq_nonneg _)
          _ = 8 * (c₀ + 1) * (‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4)) := by ring
    _ = B * (8 * (c₀ + 1)) * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4) := by
        rw [integral_const_mul]; ring

/-! ### The lower bound -/

/-- **The explicit-formula density dominates the logarithmic weight** off a compact window:
`ν_X(τ) ≥ (1/4π) log(|τ| + 4) − K₁ 1_{[−T₁, T₁]}(τ)` (Stirling for `μ`, `|ν_X − μ| ≤ 3X²`). -/
theorem exists_log_le_nuX {X : ℝ} (hX : 1 ≤ X) :
    ∃ T₁ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ τ : ℝ, 1 / (4 * π) * Real.log (|τ| + 4) -
      K₁ * (Icc (-T₁) T₁).indicator (fun _ => (1 : ℝ)) τ ≤ nuX X τ := by
  obtain ⟨C, hC0, hC⟩ := RHTower.Littlewood.exists_stirling
  have hπ := Real.pi_pos
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 1 / (4 * π) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; positivity
  have h2k : 1 / (2 * π) = 2 * k := by rw [hk]; field_simp; ring
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = 2 * k * (Real.log 2 + Real.log (2 * π)) + C := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (c₁ + 3 * X ^ 2) / k := ⟨_, rfl⟩
  obtain ⟨T₁, hT₁⟩ : ∃ T : ℝ, T = max 4 (Real.exp M) := ⟨_, rfl⟩
  have hT₁4 : 4 ≤ T₁ := hT₁ ▸ le_max_left _ _
  have hlogT : 0 ≤ Real.log (T₁ + 4) := Real.log_nonneg (by linarith)
  refine ⟨T₁, 1 + 3 * X ^ 2 + k * Real.log (T₁ + 4), by positivity, fun τ => ?_⟩
  rw [← hk]
  have hν := (abs_le.mp (RHTower.Littlewood.abs_nuX_sub_mu_le hX τ)).1
  by_cases hτ : τ ∈ Icc (-T₁) T₁
  · -- inside the window: `μ > −1`
    rw [Set.indicator_of_mem hτ, mul_one]
    have hτa : |τ| ≤ T₁ := abs_le.mpr hτ
    have hlog : Real.log (|τ| + 4) ≤ Real.log (T₁ + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hmu := RHTower.Littlewood.neg_one_lt_mu τ
    have := mul_le_mul_of_nonneg_left hlog hk0.le
    linarith
  · -- outside: Stirling
    rw [Set.indicator_of_notMem hτ, mul_zero, sub_zero]
    have hτa : T₁ < |τ| := by
      by_contra h; push Not at h; exact hτ (abs_le.mp h)
    have hτpos : 0 < |τ| := by linarith
    have hS := (abs_le.mp (hC τ (by linarith))).1
    have hCτ : C / τ ^ 2 ≤ C := div_le_self hC0 (by nlinarith [sq_abs τ])
    rw [h2k, Real.log_div hτpos.ne' (by positivity)] at hS
    -- `log(|τ| + 4) ≤ log 2 + log |τ|`
    have hW : Real.log (|τ| + 4) ≤ Real.log 2 + Real.log |τ| := by
      rw [← Real.log_mul (by norm_num) hτpos.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    -- `log(|τ| + 4) ≥ M`, so `k log(|τ| + 4) ≥ c₁ + 3X²`
    have hMl : M ≤ Real.log (|τ| + 4) := by
      have h1 : M ≤ Real.log T₁ := by
        rw [← Real.log_exp M]
        exact Real.log_le_log (Real.exp_pos M) (hT₁ ▸ le_max_right _ _)
      have h2 : Real.log T₁ ≤ Real.log (|τ| + 4) := Real.log_le_log (by linarith) (by linarith)
      linarith
    have hkM : c₁ + 3 * X ^ 2 ≤ k * Real.log (|τ| + 4) := by
      have h := mul_le_mul_of_nonneg_left hMl hk0.le
      rwa [show k * M = c₁ + 3 * X ^ 2 by rw [hM]; field_simp] at h
    have hkW := mul_le_mul_of_nonneg_left hW (by positivity : (0 : ℝ) ≤ 2 * k)
    rw [hc₁] at hkM
    nlinarith

/-- **Lower bound.** `c ∫ |f̂(σ)|² log(|σ| + 4) ≤ D(f)` on every aperture. -/
theorem log_le_collidedForm {A : ℝ} (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
      c * (∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4)) ≤ collidedForm zetaZeroConfig f := by
  obtain ⟨c₀, hc₀, hcoer⟩ := exists_collidedForm_coercive hA
  have hX : 1 ≤ Real.exp (2 * A) := Real.one_le_exp (by positivity)
  obtain ⟨T₁, K₁, hK₁, hν⟩ := exists_log_le_nuX hX
  have hπ := Real.pi_pos
  have hden : 0 < 1 + 2 * π * K₁ / c₀ := by
    have : 0 ≤ 2 * π * K₁ / c₀ := div_nonneg (mul_nonneg (by positivity) hK₁) hc₀.le
    linarith
  refine ⟨1 / (4 * π) / (1 + 2 * π * K₁ / c₀), div_pos (by positivity) hden, fun f hf hfs => ?_⟩
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  obtain ⟨hint, hre⟩ := re_W_eq_integral_nuX hA hf hfs
  have hF := integrable_norm_sq_paperFT_of_tests hf hfc
  have hlogint := integrable_norm_sq_paperFT_mul_log hf hfs
  set ind : ℝ → ℝ := (Icc (-T₁) T₁).indicator fun _ => (1 : ℝ) with hind
  have hind_eq : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ind τ) =
      (Icc (-T₁) T₁).indicator fun τ => ‖paperFT f τ‖ ^ 2 := by
    funext τ; rw [hind]
    by_cases hτ : τ ∈ Icc (-T₁) T₁
    · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ, mul_one]
    · rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem hτ, mul_zero]
  have hindInt : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * ind τ := by
    rw [hind_eq]; exact hF.indicator measurableSet_Icc
  have hlow : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * ind τ = lowMass T₁ f := by
    rw [hind_eq, integral_indicator measurableSet_Icc, lowMass]
  -- `Re W ≥ (1/4π) ∫ |f̂|² log − K₁ · lowMass`
  have hWlow : 1 / (4 * π) * (∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4)) -
      K₁ * lowMass T₁ f ≤ (zetaZeroConfig.W f f).re := by
    have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (1 / (4 * π) * Real.log (|τ| + 4) - K₁ * ind τ) =
        1 / (4 * π) * (∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4)) - K₁ * lowMass T₁ f := by
      have : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * (1 / (4 * π) * Real.log (|τ| + 4) - K₁ * ind τ)) =
          fun τ : ℝ => 1 / (4 * π) * (‖paperFT f τ‖ ^ 2 * Real.log (|τ| + 4)) -
            K₁ * (‖paperFT f τ‖ ^ 2 * ind τ) := by
        funext τ; ring
      rw [this, integral_sub (hlogint.const_mul _) (hindInt.const_mul _), integral_const_mul,
        integral_const_mul, hlow]
    rw [hre, ← hsplit]
    refine integral_mono ?_ hint fun τ => mul_le_mul_of_nonneg_left (hν τ) (sq_nonneg _)
    exact ((hlogint.const_mul (1 / (4 * π))).sub (hindInt.const_mul K₁)).congr
      (Filter.Eventually.of_forall fun τ => by simp only [Pi.sub_apply]; ring)
  have hWD : (zetaZeroConfig.W f f).re ≤ collidedForm zetaZeroConfig f :=
    re_W_le_collided (zeta_summable_collided hf hfc)
  -- the low-frequency mass is controlled by `D` through coercivity
  have hlowD : lowMass T₁ f ≤ 2 * π / c₀ * collidedForm zetaZeroConfig f := by
    have h1 : lowMass T₁ f ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 :=
      setIntegral_le_integral hF (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    have hplan := RHTower.integral_norm_sq_paperFT_eq hf hfs
    have h2 := hcoer f hf hfs
    have h3 : 2 * π * (∫ u, ‖f u‖ ^ 2) ≤ 2 * π / c₀ * collidedForm zetaZeroConfig f := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
      nlinarith
    linarith
  have hD0 : 0 ≤ collidedForm zetaZeroConfig f := collidedForm_nonneg (Z := zetaZeroConfig) f
  have key : 1 / (4 * π) * (∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4)) ≤
      (1 + 2 * π * K₁ / c₀) * collidedForm zetaZeroConfig f := by
    have := mul_le_mul_of_nonneg_left hlowD hK₁
    have e : (1 + 2 * π * K₁ / c₀) * collidedForm zetaZeroConfig f =
        collidedForm zetaZeroConfig f + K₁ * (2 * π / c₀ * collidedForm zetaZeroConfig f) := by
      field_simp
    rw [e]; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  linarith

/-- **The collided form is the logarithmic Sobolev norm** on every aperture. -/
theorem collidedForm_equiv_logSobolev {A : ℝ} (hA : 0 < A) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
      c * (∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4)) ≤ collidedForm zetaZeroConfig f ∧
      collidedForm zetaZeroConfig f ≤ C * ∫ σ : ℝ, ‖paperFT f σ‖ ^ 2 * Real.log (|σ| + 4) := by
  obtain ⟨c, hc, hlo⟩ := log_le_collidedForm hA
  obtain ⟨C, hC, hup⟩ := collidedForm_le_log hA
  exact ⟨c, max c C, hc, le_max_left _ _, fun f hf hfs => ⟨hlo f hf hfs,
    (hup f hf hfs).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (integral_nonneg fun σ => mul_nonneg (sq_nonneg _)
        (Real.log_nonneg (by linarith [abs_nonneg σ]))))⟩⟩

end GaloisForLFunctions.ArithmeticPolarization
