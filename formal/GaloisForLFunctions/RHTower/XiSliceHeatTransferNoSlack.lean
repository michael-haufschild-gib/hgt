import GaloisForLFunctions.RHTower.XiSliceHeatTransferPositivity
import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative

/-!
# No slack in the heat transfer of slice positivity

`T_n(λ, 0, t)` (`xiSliceHeatTransfer`) is the `n`-th Taylor coefficient at `0` of the slice of `Ξ`
at height `t` heated in the slice variable, `e^{(λ/2)∂_x²} S_0(t, ·)`.  For `λ ≥ 1/8` it is
nonnegative at every height (`xiSliceHeatTransfer_nonneg`), and RH is its nonnegativity for every
`λ > 0` (`riemannHypothesis_iff_forall_xiSliceHeatTransfer_nonneg`).

**Theorem** (`exists_not_xiSliceHeatTransfer_nonneg_of_neg`).  For every `λ < 0` some `T_n(λ, 0, t)`
is not nonnegative.  So the threshold `λ_WD = inf{λ : T(λ, 0, ·) ≥ 0 at every height}` satisfies
`0 ≤ λ_WD ≤ Λ ≤ 1/8` (`wdHeatThreshold_nonneg`, `wdHeatThreshold_le_newmanConstant`), with `Λ` the
de Bruijn–Newman constant, and RH is `λ_WD = 0` (`riemannHypothesis_iff_wdHeatThreshold_eq_zero`):
the slices of `Ξ` sit exactly on the boundary of heat positivity, with no slack in the backward
direction.  Admissible heats are closed upward (`xiSliceHeatTransfer_nonneg_of_le`), since
`T_n(λ′) = Σ_k ((λ′−λ)/2)^k/k! · (n+2k)!/n! · T_{n+2k}(λ)` (`hasSum_xiSliceHeatTransfer_shift`).

Proof.  Suppose `T(λ, 0, t) ≥ 0` at every height for some `λ < 0`, and let `μ > 0`.  The
exponents satisfy `λ(u² + v²) − μ(u+v)²/2 = λ(u−v)²/2 − (μ − λ)(u+v)²/2`, so the double integral
`∫∫ Φ(u)e^{λu²} Φ(v)e^{λv²} (u−v)ⁿ/n! e^{it(u+v) − μ(u+v)²/2}` is the Gaussian height average, of
variance `μ − λ > 0`, of `T_n(λ, 0, ·)` (`integral_heightGaussian_mul_integral_weight`), hence
nonnegative.  As `μ → 0⁺` it tends to the `n`-th slice moment of `H_λ`.  So every slice of `H_λ`
has nonnegative Taylor coefficients, `|H_λ(t + iy)|` is nondecreasing in `y ≥ 0` at every `t`, and
`H_λ` has no non-real zero.  This contradicts the Newman–Rodgers–Tao theorem
(`riemannHeat_neg_nonreal_zeros_infinite`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-- Multiplying a super-exponential kernel by `e^{tx²}`, `t ≤ 0`, keeps it super-exponential. -/
theorem SuperExpKernel.mul_exp_sq_of_nonpos {g : ℝ → ℝ} (hg : SuperExpKernel g) {t : ℝ}
    (ht : t ≤ 0) : SuperExpKernel (fun x => g x * Real.exp (t * x ^ 2)) where
  continuous := hg.continuous.mul (by fun_prop)
  even x := by simp only [even_two.neg_pow, hg.even]
  nonneg x := mul_nonneg (hg.nonneg x) (Real.exp_pos _).le
  pos_zero := by simpa using hg.pos_zero
  decay := by
    obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := hg.decay
    refine ⟨A, B, b, c, hA, hB, hb, hc, fun x => ?_⟩
    have h1 : Real.exp (t * x ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    calc g x * Real.exp (t * x ^ 2) ≤ g x * 1 :=
          mul_le_mul_of_nonneg_left h1 (hg.nonneg x)
      _ = g x := mul_one _
      _ ≤ _ := hdec x

/-- **Gaussian height average of a Fourier double integral.**  For an integrable continuous
weight `W`,
`∫ G_σ(t − t′) ∫∫ W e^{it′(u+v)} dt′ = ∫∫ W e^{it(u+v) − (u+v)²/(4σ²)}`. -/
theorem integral_heightGaussian_mul_integral_weight {W : ℝ × ℝ → ℝ} (hW : Integrable W)
    (hWc : Continuous W) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ∫ t' : ℝ, (heightGaussian σ t t' : ℂ) * ∫ p : ℝ × ℝ, (W p : ℂ) * cexp (I * t' * (p.1 + p.2)) =
      ∫ p : ℝ × ℝ, (W p : ℂ) *
        cexp (I * t * (p.1 + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * σ ^ 2)) := by
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap]
  · refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    have e : ∀ t' : ℝ, (heightGaussian σ t t' : ℂ) * ((W p : ℂ) * cexp (I * t' * (p.1 + p.2))) =
        (W p : ℂ) * (((σ / Real.sqrt Real.pi * Real.exp (-(σ ^ 2 * (t - t') ^ 2)) : ℝ) : ℂ) *
          cexp (-(I * t' * ((-(p.1 + p.2) : ℝ) : ℂ)))) := by
      intro t'
      have harg : -(I * (t' : ℂ) * ((-(p.1 + p.2) : ℝ) : ℂ)) = I * t' * (p.1 + p.2) := by
        push_cast; ring
      rw [harg]
      simp only [heightGaussian]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_heightGaussian_mul_cexp hσ]
    congr 2
    push_cast
    ring
  · have hG := integrable_heightGaussian hσ t
    refine (hG.mul_prod hW.norm).mono' ?_ (Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      unfold heightGaussian
      fun_prop
    · simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_cexp_I_mul_ofReal_add, mul_one]
      have hGz : 0 ≤ heightGaussian σ t z.1 := by unfold heightGaussian; positivity
      rw [abs_of_nonneg hGz]

/-- A Gaussian height average of nonnegative values is nonnegative. -/
theorem integral_heightGaussian_mul_nonneg {M : ℝ → ℂ} (hM : ∀ t', 0 ≤ M t') {σ : ℝ}
    (hσ : 0 ≤ σ) (t : ℝ) : 0 ≤ ∫ t' : ℝ, (heightGaussian σ t t' : ℂ) * M t' := by
  have hMr : ∀ t', M t' = (((M t').re : ℝ) : ℂ) := fun t' =>
    Complex.ext (by simp) (by simp [((Complex.nonneg_iff.mp (hM t')).2).symm])
  have e : (fun t' : ℝ => (heightGaussian σ t t' : ℂ) * M t') =
      fun t' => ((heightGaussian σ t t' * (M t').re : ℝ) : ℂ) := by
    funext t'
    rw [hMr t']
    push_cast
    simp
  rw [e, integral_complex_ofReal]
  refine Complex.zero_le_real.mpr (integral_nonneg fun t' => ?_)
  have hG : 0 ≤ heightGaussian σ t t' := by unfold heightGaussian; positivity
  exact mul_nonneg hG (Complex.nonneg_iff.mp (hM t')).1

/-- Nonnegative Taylor coefficients of every slice of a super-exponential transform rule out
non-real zeros. -/
theorem cosTransform_zero_im_eq_zero_of_slice_nonneg {g : ℝ → ℝ} (hg : SuperExpKernel g)
    (h : ∀ t : ℝ, NonnegTaylorAtZero
      (fun x => cosTransform g ((t : ℂ) - I * x) * cosTransform g ((t : ℂ) + I * x)))
    {ζ : ℂ} (hζ : cosTransform g ζ = 0) : ζ.im = 0 := by
  by_contra him
  -- move the zero to the upper half-plane
  obtain ⟨w, hw, hwim⟩ : ∃ w : ℂ, cosTransform g w = 0 ∧ 0 < w.im := by
    rcases lt_or_gt_of_ne him with hlt | hgt
    · refine ⟨(starRingEnd ℂ) ζ, ?_, by simpa using hlt⟩
      rw [hg.cosTransform_conj, hζ, map_zero]
    · exact ⟨ζ, hζ, hgt⟩
  set t := w.re
  have hsq : ∀ y : ℝ, (cosTransform g ((t : ℂ) - I * y) * cosTransform g ((t : ℂ) + I * y)).re =
      ‖cosTransform g ((t : ℂ) + I * y)‖ ^ 2 := by
    intro y
    have hc : (t : ℂ) - I * y = (starRingEnd ℂ) ((t : ℂ) + I * y) := by
      apply Complex.ext <;> simp
    rw [hc, hg.cosTransform_conj, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hw' : (t : ℂ) + I * (w.im : ℂ) = w := by apply Complex.ext <;> simp [t]
  have hseg : ∀ y : ℝ, 0 ≤ y → y ≤ w.im → cosTransform g ((t : ℂ) + I * y) = 0 := by
    intro y hy0 hyw
    have hle := re_le_re_of_nonnegTaylorAtZero (h t) hy0 hyw
    rw [hsq, hsq, hw', hw, norm_zero] at hle
    have h0 : ‖cosTransform g ((t : ℂ) + I * y)‖ ^ 2 ≤ 0 := by simpa using hle
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm h0 (sq_nonneg _)))
  set G : ℂ → ℂ := fun v => cosTransform g ((t : ℂ) + I * v) with hG
  have hGd : Differentiable ℂ G := by
    have := hg.differentiable
    simp only [hG]
    fun_prop
  have hGzero := GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval hGd
    (t₀ := w.im / 2) (r := w.im / 2) (by linarith) (fun y hy => by
      rw [abs_lt] at hy
      exact hseg y (by linarith) (by linarith))
  have h0 : cosTransform g 0 = 0 := by
    have := hGzero (-(t : ℂ) / I)
    simp only [hG] at this
    rwa [show (t : ℂ) + I * (-(t : ℂ) / I) = 0 by field_simp; ring] at this
  exact hg.cosTransform_zero_ne h0

/-- **No slack.**  For every `λ < 0` some heated slice coefficient `T_n(λ, 0, t)` is not
nonnegative. -/
theorem exists_not_xiSliceHeatTransfer_nonneg_of_neg {lam : ℝ} (hlam : lam < 0) :
    ∃ t : ℝ, ∃ n : ℕ, ¬ 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  by_contra hcon
  push Not at hcon
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set g : ℝ → ℝ := fun u => Φ u * Real.exp (lam * u ^ 2) with hgdef
  have hg : SuperExpKernel g := riemannKernel_superExp.mul_exp_sq_of_nonpos hlam.le
  -- every slice moment of `H_λ` is nonnegative
  have hmom : ∀ t : ℝ, ∀ n : ℕ, 0 ≤ kernelSliceMoment g 0 t n := by
    intro t n
    set W₁ : ℝ × ℝ → ℝ := fun p => g p.1 * g p.2 * Real.exp (0 * (p.1 - p.2)) *
      ((p.1 - p.2) ^ n / n.factorial) with hW₁
    set W₂ : ℝ × ℝ → ℝ := fun p => Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      Real.exp (0 * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) with hW₂
    have hW₁c : Continuous W₁ := by
      have := hg.continuous; simp only [hW₁]; fun_prop
    have hW₂c : Continuous W₂ := by
      have := continuous_riemannKernelReal; simp only [hW₂, hΦ]; fun_prop
    have hW₂i : Integrable W₂ := by
      refine (integrable_prod_majorant riemannKernel_superExp (|0| + 1)).mono'
        hW₂c.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      have h1 := abs_sub_pow_div_mul_exp_le 0 p.1 p.2 n
      have he : Real.exp (lam * (p.1 - p.2) ^ 2 / 2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (p.1 - p.2)])
      have hΦΦ : 0 ≤ Φ p.1 * Φ p.2 := mul_nonneg (hΦ0 _) (hΦ0 _)
      simp only [hW₂, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 _), abs_of_pos (Real.exp_pos _),
        abs_div, abs_pow, Nat.abs_cast]
      calc Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (0 * (p.1 - p.2)) *
            (|p.1 - p.2| ^ n / n.factorial)
          = Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
              (|p.1 - p.2| ^ n / n.factorial * Real.exp (0 * (p.1 - p.2))) := by ring
        _ ≤ Φ p.1 * Φ p.2 * 1 *
              (Real.exp ((|0| + 1) * |p.1|) * Real.exp ((|0| + 1) * |p.2|)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left he hΦΦ) h1 (by positivity)
              (by positivity)
        _ = _ := by ring
    -- the Gaussian-damped moments are averages of `T(λ, 0, ·)`
    set I₁ : ℝ → ℂ := fun μ => ∫ p : ℝ × ℝ, (W₁ p : ℂ) *
      cexp (I * t * (p.1 + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 * (μ / 2)) with hI₁
    have hI₁nonneg : ∀ μ : ℝ, 0 < μ → 0 ≤ I₁ μ := by
      intro μ hμ
      set σ := Real.sqrt (1 / (2 * (μ - lam))) with hσdef
      have hμl : 0 < μ - lam := by linarith
      have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
      have hσ2 : σ ^ 2 = 1 / (2 * (μ - lam)) := Real.sq_sqrt (by positivity)
      have hav := integral_heightGaussian_mul_integral_weight hW₂i hW₂c hσ t
      have hT : ∀ t' : ℝ, ∫ p : ℝ × ℝ, (W₂ p : ℂ) * cexp (I * t' * (p.1 + p.2)) =
          xiSliceHeatTransfer lam 0 t' n := by
        intro t'; simp only [hW₂, xiSliceHeatTransfer, hΦ]
      simp_rw [hT] at hav
      have heq : I₁ μ = ∫ p : ℝ × ℝ, (W₂ p : ℂ) *
          cexp (I * t * (p.1 + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * σ ^ 2)) := by
        simp only [hI₁]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        beta_reduce
        have hσc : (σ : ℂ) ^ 2 = ((1 / (2 * (μ - lam)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_pow, hσ2]
        have hμlc : ((μ - lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμl.ne'
        have hargs : I * t * ((p.1 : ℂ) + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 * (μ / 2) =
            I * t * ((p.1 : ℂ) + p.2) + ((-(μ * (p.1 + p.2) ^ 2 / 2)) : ℝ) := by
          push_cast; ring
        have hargs2 : I * t * ((p.1 : ℂ) + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 / (4 * (σ : ℂ) ^ 2) =
            I * t * ((p.1 : ℂ) + p.2) + ((-((μ - lam) * (p.1 + p.2) ^ 2 / 2)) : ℝ) := by
          rw [hσc]
          push_cast
          field_simp
          ring
        rw [hargs, hargs2, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp,
          ← Complex.ofReal_exp]
        have hreal : W₁ p * Real.exp (-(μ * (p.1 + p.2) ^ 2 / 2)) =
            W₂ p * Real.exp (-((μ - lam) * (p.1 + p.2) ^ 2 / 2)) := by
          simp only [hW₁, hW₂, hgdef]
          have : Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) *
              Real.exp (-(μ * (p.1 + p.2) ^ 2 / 2)) =
              Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
                Real.exp (-((μ - lam) * (p.1 + p.2) ^ 2 / 2)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          calc Φ p.1 * Real.exp (lam * p.1 ^ 2) * (Φ p.2 * Real.exp (lam * p.2 ^ 2)) *
                Real.exp (0 * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) *
                  Real.exp (-(μ * (p.1 + p.2) ^ 2 / 2))
              = Φ p.1 * Φ p.2 * (Real.exp (lam * p.1 ^ 2) * Real.exp (lam * p.2 ^ 2) *
                  Real.exp (-(μ * (p.1 + p.2) ^ 2 / 2))) *
                    Real.exp (0 * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) := by ring
            _ = _ := by rw [this]; ring
        calc (W₁ p : ℂ) * (cexp (I * t * ((p.1 : ℂ) + p.2)) *
              ((Real.exp (-(μ * (p.1 + p.2) ^ 2 / 2)) : ℝ) : ℂ))
            = ((W₁ p * Real.exp (-(μ * (p.1 + p.2) ^ 2 / 2)) : ℝ) : ℂ) *
                cexp (I * t * ((p.1 : ℂ) + p.2)) := by push_cast; ring
          _ = ((W₂ p * Real.exp (-((μ - lam) * (p.1 + p.2) ^ 2 / 2)) : ℝ) : ℂ) *
                cexp (I * t * ((p.1 : ℂ) + p.2)) := by rw [hreal]
          _ = _ := by push_cast; ring
      rw [heq, ← hav]
      exact integral_heightGaussian_mul_nonneg (fun t' => hcon t' n) hσ.le t
    -- and tend to the slice moment of `H_λ`
    have hlim : Tendsto I₁ (𝓝[>] 0) (𝓝 (kernelSliceMoment g 0 t n)) := by
      have hW₁i : Integrable W₁ := by
        refine (integrable_prod_majorant hg (|0| + 1)).mono' hW₁c.aestronglyMeasurable
          (Eventually.of_forall fun p => ?_)
        have h1 := abs_sub_pow_div_mul_exp_le 0 p.1 p.2 n
        have hg1 := hg.nonneg p.1
        have hg2 := hg.nonneg p.2
        simp only [hW₁, Real.norm_eq_abs, abs_mul, abs_of_nonneg hg1, abs_of_nonneg hg2,
          abs_of_pos (Real.exp_pos _), abs_div, abs_pow, Nat.abs_cast]
        calc g p.1 * g p.2 * Real.exp (0 * (p.1 - p.2)) * (|p.1 - p.2| ^ n / n.factorial)
            = g p.1 * g p.2 * (|p.1 - p.2| ^ n / n.factorial * Real.exp (0 * (p.1 - p.2))) := by
              ring
          _ ≤ g p.1 * g p.2 * (Real.exp ((|0| + 1) * |p.1|) * Real.exp ((|0| + 1) * |p.2|)) :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg hg1 hg2)
          _ = _ := by ring
      have h := tendsto_integral_filter_of_dominated_convergence (fun p => ‖W₁ p‖)
        (l := 𝓝[>] (0 : ℝ))
        (F := fun (μ : ℝ) p => (W₁ p : ℂ) *
          cexp (I * t * ((p.1 : ℂ) + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 * (μ / 2)))
        (f := fun p => (W₁ p : ℂ) * cexp (I * t * ((p.1 : ℂ) + p.2)))
        (Eventually.of_forall fun μ => by
          refine Continuous.aestronglyMeasurable ?_
          fun_prop)
        (by
          filter_upwards [self_mem_nhdsWithin] with μ hμ
          refine Eventually.of_forall fun p => ?_
          rw [norm_mul, Complex.norm_real]
          have hc : ((p.1 + p.2 : ℝ) : ℂ) ^ 2 * ((μ : ℂ) / 2) =
              (((p.1 + p.2) ^ 2 * (μ / 2) : ℝ) : ℂ) := by push_cast; ring
          have hre : (I * t * ((p.1 : ℂ) + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 * ((μ : ℂ) / 2)).re =
              -((p.1 + p.2) ^ 2 * (μ / 2)) := by
            rw [hc, Complex.sub_re, Complex.ofReal_re]
            simp
          rw [Complex.norm_exp, hre]
          have : Real.exp (-((p.1 + p.2) ^ 2 * (μ / 2))) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by
              have := Set.mem_Ioi.mp hμ
              nlinarith [sq_nonneg (p.1 + p.2)])
          calc ‖W₁ p‖ * Real.exp (-((p.1 + p.2) ^ 2 * (μ / 2))) ≤ ‖W₁ p‖ * 1 :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
            _ = ‖W₁ p‖ := mul_one _)
        hW₁i.norm
        (Eventually.of_forall fun p => by
          have hc : Continuous (fun μ : ℝ => (W₁ p : ℂ) *
              cexp (I * t * ((p.1 : ℂ) + p.2) - ((p.1 + p.2 : ℝ) : ℂ) ^ 2 * (μ / 2))) := by
            fun_prop
          have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
          simpa using this)
      have e0 : (∫ p : ℝ × ℝ, (W₁ p : ℂ) * cexp (I * t * ((p.1 : ℂ) + p.2))) =
          kernelSliceMoment g 0 t n := by
        simp only [hW₁, kernelSliceMoment]
      rw [e0] at h
      exact h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun μ hμ => hI₁nonneg μ hμ)
  -- so every slice of `H_λ` has nonnegative Taylor coefficients
  have hslice : ∀ t : ℝ, NonnegTaylorAtZero
      (fun x => cosTransform g ((t : ℂ) - I * x) * cosTransform g ((t : ℂ) + I * x)) := by
    intro t
    refine ⟨?_, fun n => ?_⟩
    · have := hg.differentiable
      fun_prop
    · have h := hmom t n
      rw [kernelSliceMoment_eq_iteratedDeriv hg, Complex.ofReal_zero] at h
      have hfac : (0 : ℂ) < (n.factorial : ℂ) := by exact_mod_cast Nat.factorial_pos n
      have := mul_nonneg h hfac.le
      rwa [div_mul_cancel₀ _ hfac.ne'] at this
  -- contradiction with Newman–Rodgers–Tao
  obtain ⟨ζ, hζ, him⟩ := (riemannHeat_neg_nonreal_zeros_infinite (τ := -lam) (by linarith)).nonempty
  rw [neg_neg] at hζ
  exact him (cosTransform_zero_im_eq_zero_of_slice_nonneg hg hslice hζ)

/-- **The heat threshold is nonnegative.**  If `T(λ, 0, ·)` is nonnegative at every height and
order, then `λ ≥ 0`. -/
theorem nonneg_of_forall_xiSliceHeatTransfer_nonneg {lam : ℝ}
    (h : ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n) : 0 ≤ lam := by
  by_contra hneg
  obtain ⟨t, n, hn⟩ := exists_not_xiSliceHeatTransfer_nonneg_of_neg (lt_of_not_ge hneg)
  exact hn (h t n)


/-! ## The WD heat threshold -/

/-- **Heat shift of the transfer.**  For `λ ≤ λ′`,
`T_n(λ′, x₀, t) = Σ_k ((λ′−λ)/2)^k/k! · (n+2k)!/n! · T_{n+2k}(λ, x₀, t)`. -/
theorem hasSum_xiSliceHeatTransfer_shift {lam lam' : ℝ} (hll : lam ≤ lam') (x₀ t : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ => ((((lam' - lam) / 2) ^ k / k.factorial *
        ((n + 2 * k).factorial / n.factorial) : ℝ) : ℂ) *
      xiSliceHeatTransfer lam x₀ t (n + 2 * k)) (xiSliceHeatTransfer lam' x₀ t n) := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set d : ℝ := lam' - lam with hd
  have hd0 : 0 ≤ d := by rw [hd]; linarith
  set F : ℕ → ℝ × ℝ → ℂ := fun k p =>
    ((Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      ((d * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) * Real.exp (x₀ * (p.1 - p.2)) *
        ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2)) with hF
  set D : ℝ × ℝ → ℝ := fun p =>
    Φ p.1 * Real.exp (|lam'| * p.1 ^ 2) * Real.exp ((|x₀| + 1) * |p.1|) *
      (Φ p.2 * Real.exp (|lam'| * p.2 ^ 2) * Real.exp ((|x₀| + 1) * |p.2|)) with hD
  have hDi : Integrable D :=
    integrable_prod_majorant (riemannKernel_superExp.mul_exp_sq (abs_nonneg lam')) (|x₀| + 1)
  have hnormF : ∀ k p, ‖F k p‖ = Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      ((d * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) *
        (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) := by
    intro k p
    have hq : 0 ≤ d * (p.1 - p.2) ^ 2 / 2 := by positivity
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I_mul_ofReal_add,
      mul_one, abs_div, abs_pow, Nat.abs_cast, abs_of_nonneg (hΦ0 _), abs_of_nonneg hq,
      abs_of_pos (Real.exp_pos _)]
    ring
  have hexpsq : ∀ p : ℝ × ℝ, Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      Real.exp (d * (p.1 - p.2) ^ 2 / 2) ≤
        Real.exp (|lam'| * p.1 ^ 2) * Real.exp (|lam'| * p.2 ^ 2) := by
    intro p
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : lam * (p.1 - p.2) ^ 2 / 2 + d * (p.1 - p.2) ^ 2 / 2 = lam' * (p.1 - p.2) ^ 2 / 2 := by
      rw [hd]; ring
    rw [h1]
    have h2 : lam' ≤ |lam'| := le_abs_self _
    have h3 : 0 ≤ (p.1 - p.2) ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (p.1 + p.2), abs_nonneg lam']
  have hbound : ∀ N : ℕ, ∀ p : ℝ × ℝ, ∑ k ∈ Finset.range N, ‖F k p‖ ≤ D p := by
    intro N p
    simp only [hnormF]
    have hq : 0 ≤ d * (p.1 - p.2) ^ 2 / 2 := by positivity
    have e : ∑ k ∈ Finset.range N, Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
        ((d * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) =
        Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) *
          ∑ k ∈ Finset.range N, (d * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e]
    have h1 := Real.sum_le_exp_of_nonneg hq N
    have h2 := abs_sub_pow_div_mul_exp_le x₀ p.1 p.2 n
    have hΦΦ : 0 ≤ Φ p.1 * Φ p.2 := mul_nonneg (hΦ0 _) (hΦ0 _)
    calc Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
          (|p.1 - p.2| ^ n / n.factorial * Real.exp (x₀ * (p.1 - p.2))) *
          ∑ k ∈ Finset.range N, (d * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial
        ≤ Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
          (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) *
            Real.exp (d * (p.1 - p.2) ^ 2 / 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) h1
            (Finset.sum_nonneg fun k _ => by positivity) (by positivity)
      _ = Φ p.1 * Φ p.2 * (Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
            Real.exp (d * (p.1 - p.2) ^ 2 / 2)) *
          (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) := by ring
      _ ≤ Φ p.1 * Φ p.2 * (Real.exp (|lam'| * p.1 ^ 2) * Real.exp (|lam'| * p.2 ^ 2)) *
          (Real.exp ((|x₀| + 1) * |p.1|) * Real.exp ((|x₀| + 1) * |p.2|)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexpsq p) hΦΦ)
            (by positivity)
      _ = D p := by simp only [hD]; ring
  have hmeas : ∀ k, AEStronglyMeasurable (F k) := by
    intro k
    refine Continuous.aestronglyMeasurable ?_
    have := continuous_riemannKernelReal
    simp only [hF, hΦ]
    fun_prop
  have hint : ∀ k, Integrable (F k) := by
    intro k
    refine hDi.mono' (hmeas k) (Eventually.of_forall fun p => ?_)
    have := hbound (k + 1) p
    rw [Finset.sum_range_succ] at this
    have hnn : 0 ≤ ∑ i ∈ Finset.range k, ‖F i p‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hsum : Summable (fun k => ∫ p, ‖F k p‖) := by
    refine summable_of_sum_range_le (c := ∫ p, D p)
      (fun k => integral_nonneg fun p => norm_nonneg _) fun N => ?_
    rw [← integral_finsetSum _ (fun k _ => (hint k).norm)]
    exact integral_mono (integrable_finsetSum _ fun k _ => (hint k).norm) hDi (hbound N)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ p : ℝ × ℝ, ∑' k, F k p =
      ((Φ p.1 * Φ p.2 * Real.exp (lam' * (p.1 - p.2) ^ 2 / 2) * Real.exp (x₀ * (p.1 - p.2)) *
        ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2)) := by
    intro p
    have hexp := NormedSpace.expSeries_div_hasSum_exp (d * (p.1 - p.2) ^ 2 / 2)
    rw [← Real.exp_eq_exp_ℝ] at hexp
    have hR := (hexp.mul_left (Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2))).mul_right
      (Real.exp (x₀ * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial))
    have hC := (Complex.hasSum_ofReal.mpr hR).mul_right (cexp (I * t * (p.1 + p.2)))
    have hlam' : Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (d * (p.1 - p.2) ^ 2 / 2) =
        Real.exp (lam' * (p.1 - p.2) ^ 2 / 2) := by
      rw [← Real.exp_add]; congr 1; rw [hd]; ring
    refine (hC.congr_fun fun k => ?_).tsum_eq.trans ?_
    · simp only [hF]
      push_cast
      ring
    · rw [← hlam']
      push_cast
      ring
  simp_rw [htsum] at h
  refine h.congr_fun fun k => ?_
  simp only [hF, xiSliceHeatTransfer]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hfac : ((n.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfac2 : (((n + 2 * k).factorial : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hkfac : ((k.factorial : ℝ)) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hreal : Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) *
      ((d * (p.1 - p.2) ^ 2 / 2) ^ k / k.factorial) * Real.exp (x₀ * (p.1 - p.2)) *
        ((p.1 - p.2) ^ n / n.factorial) =
      (d / 2) ^ k / k.factorial * ((n + 2 * k).factorial / n.factorial) *
        (Φ p.1 * Φ p.2 * Real.exp (lam * (p.1 - p.2) ^ 2 / 2) * Real.exp (x₀ * (p.1 - p.2)) *
          ((p.1 - p.2) ^ (n + 2 * k) / (n + 2 * k).factorial)) := by
    simp only [pow_add, pow_mul, div_pow, mul_pow]
    field_simp
  beta_reduce
  rw [hreal]
  push_cast
  ring

/-- **Admissible heats are closed upward.** -/
theorem xiSliceHeatTransfer_nonneg_of_le {lam lam' : ℝ} (hll : lam ≤ lam')
    (h : ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n) (t : ℝ) (n : ℕ) :
    0 ≤ xiSliceHeatTransfer lam' 0 t n := by
  refine (hasSum_xiSliceHeatTransfer_shift hll 0 t n).nonneg fun k => ?_
  have hc : (0 : ℝ) ≤ ((lam' - lam) / 2) ^ k / k.factorial * ((n + 2 * k).factorial / n.factorial) :=
    mul_nonneg (div_nonneg (pow_nonneg (by linarith) _) (by positivity)) (by positivity)
  exact mul_nonneg (Complex.zero_le_real.mpr hc) (h t (n + 2 * k))

/-- The heats at which every heated slice coefficient is nonnegative at every height. -/
def wdHeatAdmissible : Set ℝ := {lam | ∀ t : ℝ, ∀ n : ℕ, 0 ≤ xiSliceHeatTransfer lam 0 t n}

/-- **The WD heat threshold** `λ_WD = inf{λ : e^{(λ/2)∂_x²} S_0(t, ·) ≥ 0 at every height}`. -/
def wdHeatThreshold : ℝ := sInf wdHeatAdmissible

theorem eighth_mem_wdHeatAdmissible : (1 / 8 : ℝ) ∈ wdHeatAdmissible :=
  fun t n => (xiSliceHeatTransfer_nonneg le_rfl t n).2

theorem wdHeatAdmissible_bddBelow : BddBelow wdHeatAdmissible :=
  ⟨0, fun _ h => nonneg_of_forall_xiSliceHeatTransfer_nonneg h⟩

/-- `λ_WD ≥ 0`. -/
theorem wdHeatThreshold_nonneg : 0 ≤ wdHeatThreshold :=
  le_csInf ⟨_, eighth_mem_wdHeatAdmissible⟩ fun _ h => nonneg_of_forall_xiSliceHeatTransfer_nonneg h

/-- Every heat above the threshold is admissible. -/
theorem mem_wdHeatAdmissible_of_lt {lam : ℝ} (h : wdHeatThreshold < lam) :
    lam ∈ wdHeatAdmissible := by
  obtain ⟨s, hs, hslt⟩ := (csInf_lt_iff wdHeatAdmissible_bddBelow
    ⟨_, eighth_mem_wdHeatAdmissible⟩).mp h
  exact fun t n => xiSliceHeatTransfer_nonneg_of_le hslt.le hs t n

/-- **`λ_WD ≤ Λ`**: the WD heat threshold is at most the de Bruijn–Newman constant. -/
theorem wdHeatThreshold_le_newmanConstant : wdHeatThreshold ≤ newmanConstant := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hpos : 0 < newmanConstant + ε := by linarith [newmanConstant_nonneg]
  have hmem := (mem_realRootedTimes_iff hpos.le).mpr (by linarith)
  refine csInf_le wdHeatAdmissible_bddBelow fun t n => ?_
  exact xiSliceHeatTransfer_nonneg_of_strip hpos le_rfl (fun ζ hζ => by rw [hmem.2 ζ hζ]) t n

/-- **The Riemann hypothesis as `λ_WD = 0`.** -/
theorem riemannHypothesis_iff_wdHeatThreshold_eq_zero :
    RiemannHypothesis ↔ wdHeatThreshold = 0 := by
  constructor
  · intro hRH
    rw [riemannHypothesis_iff_newmanConstant_eq_zero] at hRH
    exact le_antisymm (hRH ▸ wdHeatThreshold_le_newmanConstant) wdHeatThreshold_nonneg
  · intro h0
    refine riemannHypothesis_iff_forall_xiSliceHeatTransfer_nonneg.mpr fun lam hlam t n => ?_
    exact mem_wdHeatAdmissible_of_lt (by rw [h0]; exact hlam) t n

end

end RHTower.DeBruijn
