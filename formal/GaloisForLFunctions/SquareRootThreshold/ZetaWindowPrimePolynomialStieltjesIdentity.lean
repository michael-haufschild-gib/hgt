import GaloisForLFunctions.RHTower.BumpAutocorrelationWindowKernel
import GaloisForLFunctions.SquareRootThreshold.ZetaLocalizedFormWindowedVarianceLaw
import GaloisForLFunctions.RHTower.ZeroCountRemainderNotIntegrable

/-!
# The window prime polynomial and the Stieltjes identity for the zero count

Fix an aperture `ℓ > 0`, the scaled bump `Φ_ℓ` (`cb ℓ 0`) and its autocorrelation `K_ℓ`, with
`ψ_ℓ = K̂_ℓ = |Φ̂_ℓ|²` on the real line.  At height `T` the bump is modulated to `S_ξ Φ_ℓ` with
`ξ = −T/2π` (`heightWindowShift`).  Its localized Weil form is `A(T) − Π(T)`, where `Π(T)` is the
prime polynomial over the prime powers `n ≤ e^{2ℓ}` (`windowPrime` is its real part).

* **Zero side** (`windowPrime_eq`).  Unconditionally,
  `Re Π(T) = pole(T) + ∫ ψ_ℓ(τ − T) μ(τ) dτ − Σ_ρ m_ρ Re K̂_ℓ(γ_ρ − T)`, `γ_ρ = (ρ − ½)/i`.
* **Abel summation** (`sum_zeroWindowFinset_mul_eq`).  For a `C¹` weight `f` on `[a, b]`,
  `Σ_{a<Im ρ≤b} m_ρ f(Im ρ) = N(a, b) f(b) − ∫_a^b N(a, t) f'(t) dt`.
* **Stieltjes identity** (`sum_zeroWindow_psi_sub_integral_eq`).  With `N` the zero count, `M` the
  smooth Riemann–von Mangoldt term and `S = N − M`,
  `Σ_{1<Im ρ≤2T} m_ρ ψ_ℓ(Im ρ − T) − ∫_1^{2T} ψ_ℓ(t − T) M'(t) dt
    = ψ_ℓ(T) S(2T) − ψ_ℓ(1 − T) S(1) − ∫_1^{2T} S(t) ψ_ℓ'(t − T) dt`.
  It is integration by parts against `dS = dN − M' dt`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.Littlewood

/-- The height shift `ξ = −T/2π` placing the window at height `T`. -/
def heightWindowShift (T : ℝ) : ℝ := -T / (2 * π)

theorem two_pi_mul_windowShift (T : ℝ) : 2 * π * heightWindowShift T = -T := by
  unfold heightWindowShift; field_simp

/-- The real part of the prime polynomial of the bump window of aperture `ℓ` at height `T`. -/
def windowPrime (ℓ T : ℝ) : ℝ :=
  (primePolynomial (cb ℓ 0) ⌊Real.exp (2 * ℓ)⌋₊ (heightWindowShift T)).re

/-- The pole terms of the bump window at height `T`. -/
def windowPole (ℓ T : ℝ) : ℝ :=
  (paperFT (bumpAutocorrelation ℓ) (I / 2 - T) + paperFT (bumpAutocorrelation ℓ) (-I / 2 - T)).re

/-- The localized kernel is the height shift of `K_ℓ`. -/
theorem weilTest_heightShift_cb (ξ : ℝ) :
    EF.weilTest (heightShift ξ (cb ℓ 0)) (heightShift ξ (cb ℓ 0)) = heightShift ξ (bumpAutocorrelation ℓ) := by
  funext v
  rw [weilTest_heightShift, heightShift, bumpAutocorrelation]

section Window

variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

theorem tsupport_cb_subset_Icc : tsupport (cb ℓ 0) ⊆ Icc (-ℓ) ℓ := by
  have h := tsupport_cb_subset hℓ
  rwa [show 2 * ℓ / 2 = ℓ by ring] at h

omit hℓ in
theorem paperFT_localizedKernel (z : ℂ) (T : ℝ) :
    paperFT (EF.weilTest (heightShift (heightWindowShift T) (cb ℓ 0))
      (heightShift (heightWindowShift T) (cb ℓ 0))) z = paperFT (bumpAutocorrelation ℓ) (z - T) := by
  rw [weilTest_heightShift_cb, paperFT_heightShift]
  congr 1
  have h := two_pi_mul_windowShift T
  rw [show (2 : ℂ) * π * (heightWindowShift T : ℂ) = ((2 * π * heightWindowShift T : ℝ) : ℂ) by push_cast; ring,
    h]
  push_cast; ring

/-- **The zero side of the window.**  `Re Π(T) = pole(T) + ∫ ψ_ℓ(τ − T) μ(τ) dτ −
Σ_ρ m_ρ Re K̂_ℓ(γ_ρ − T)`. -/
theorem windowPrime_eq (T : ℝ) :
    Summable (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * (paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re) ∧
      windowPrime ℓ T = windowPole ℓ T + (∫ τ, psi ℓ 0 (τ - T) * mu τ) -
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * (paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re := by
  set ξ := heightWindowShift T with hξ
  set g := heightShift ξ (cb ℓ 0) with hg
  have hf : ContDiff ℝ 2 (cb ℓ 0) := contDiff_cb ℓ 0
  have hfs := tsupport_cb_subset_Icc hℓ
  have hgd : ContDiff ℝ 2 g := heightShift_contDiff hf ξ
  have hgs : tsupport g ⊆ Icc (-(2 * ℓ / 2)) (2 * ℓ / 2) := by
    rw [show 2 * ℓ / 2 = ℓ by ring]; exact (tsupport_heightShift_subset ξ _).trans hfs
  have hgc : HasCompactSupport g := hasCompactSupport_of_tsupport_subset_Icc hgs
  -- the zero sum
  obtain ⟨hsum, -, -⟩ := paperInputs_zeta.EF (2 * ℓ) (by positivity) g g hgd hgd hgs hgs
  have hterm : ∀ ρ : zetaZeroConfig.carrier, zetaZeroConfig.Wsummand g g ρ =
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T) := by
    intro ρ
    rw [ZeroConfig.Wsummand, mul_assoc, ← EF.paperFT_weilTest hgd.continuous hgd.continuous hgc hgc,
      paperFT_localizedKernel]
  have hsum' : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re := by
    refine (Complex.reCLM.summable hsum).congr fun ρ => ?_
    simp [Complex.reCLM_apply, hterm, Complex.mul_re]
  have hWre : (zetaZeroConfig.W g g).re = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (paperFT (bumpAutocorrelation ℓ) (gammaOf ρ - T)).re := by
    rw [ZeroConfig.W, Complex.re_tsum hsum]
    congr 1 with ρ
    simp [hterm, Complex.mul_re]
  -- the archimedean part
  have hval : ∀ τ : ℝ, paperFT (EF.weilTest g g) τ = (psi ℓ 0 (τ - T) : ℂ) := by
    intro τ
    rw [paperFT_localizedKernel, show ((τ : ℂ) - T) = ((τ - T : ℝ) : ℂ) by push_cast; ring,
      paperFT_bumpKernel_ofReal hℓ]
  have harch : (archPart (cb ℓ 0) ξ).re = windowPole ℓ T + ∫ τ, psi ℓ 0 (τ - T) * mu τ := by
    rw [archPart, Complex.add_re, windowPole, paperFT_localizedKernel, paperFT_localizedKernel]
    congr 1
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest g g) τ * (mu τ : ℂ)) =
        fun τ : ℝ => ((psi ℓ 0 (τ - T) * mu τ : ℝ) : ℂ) := by
      funext τ; rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  refine ⟨hsum', ?_⟩
  have hW : zetaZeroConfig.W g g = archPart (cb ℓ 0) ξ -
      primePolynomial (cb ℓ 0) ⌊Real.exp (2 * ℓ)⌋₊ ξ :=
    zetaZeroConfig_W_heightShift_eq_sub hf hfs ξ
  have hPi : primePolynomial (cb ℓ 0) ⌊Real.exp (2 * ℓ)⌋₊ ξ = archPart (cb ℓ 0) ξ -
      zetaZeroConfig.W g g := by rw [hW]; ring
  rw [windowPrime, ← hξ, hPi, Complex.sub_re, harch, hWre]

end Window

/-! ### Abel summation over the zeros -/

/-- The zeros with ordinate in `(a, b]`. -/
def zeroWindowFinset (a b : ℝ) : Finset zetaZeroConfig.carrier :=
  ((zetaZeroConfig.finite_window a b).preimage Subtype.val_injective.injOn).toFinset

theorem mem_zeroWindowFinset {a b : ℝ} {ρ : zetaZeroConfig.carrier} :
    ρ ∈ zeroWindowFinset a b ↔ a < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ b := by
  simp only [zeroWindowFinset, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨ρ.2, h⟩⟩

theorem sum_zeroWindowFinset_mult (a b : ℝ) :
    ∑ ρ ∈ zeroWindowFinset a b, (zetaZeroConfig.mult ρ : ℝ) = zetaZeroConfig.N a b := by
  rw [← tsum_window_mult a b, tsum_eq_sum (s := zeroWindowFinset a b)]
  · exact Finset.sum_congr rfl fun ρ hρ => (if_pos (mem_zeroWindowFinset.mp hρ)).symm
  · intro ρ hρ; exact if_neg fun h => hρ (mem_zeroWindowFinset.mpr h)

/-- **Abel summation over the zeros.**  For `a ≤ b` and a `C¹` weight `f` on `[a, b]`,
`Σ_{a<γ≤b} m_ρ f(γ) = N(a, b) f(b) − ∫_a^b N(a, t) f'(t) dt`. -/
theorem sum_zeroWindowFinset_mul_eq {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Icc a b)) :
    ∑ ρ ∈ zeroWindowFinset a b, (zetaZeroConfig.mult ρ : ℝ) * f (ρ : ℂ).im =
      (zetaZeroConfig.N a b : ℝ) * f b - ∫ t in a..b, (zetaZeroConfig.N a t : ℝ) * f' t := by
  classical
  set S := zeroWindowFinset a b with hS
  have hγ : ∀ ρ ∈ S, a < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ b := fun ρ hρ => mem_zeroWindowFinset.mp hρ
  have hint : IntegrableOn f' (Ioc a b) volume := by
    have := (hf'.mono (by rw [uIcc_of_le hab])).intervalIntegrable (μ := volume)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 this
  have hftc : ∀ ρ ∈ S, f (ρ : ℂ).im = f b - ∫ t in ((ρ : ℂ).im)..b, f' t := by
    intro ρ hρ
    have hsub : uIcc ((ρ : ℂ).im) b ⊆ Icc a b := by
      rw [uIcc_of_le (hγ ρ hρ).2]; exact Icc_subset_Icc (hγ ρ hρ).1.le le_rfl
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hf t (hsub ht))
      ((hf'.mono hsub).intervalIntegrable)]
    ring
  have hind : ∀ ρ ∈ S, ∫ t in ((ρ : ℂ).im)..b, f' t =
      ∫ t in a..b, (Ici (ρ : ℂ).im).indicator f' t := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hγ ρ hρ
    rw [intervalIntegral.integral_of_le h2, intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      show Ici (ρ : ℂ).im ∩ Ioc a b = Icc (ρ : ℂ).im b by
        ext t; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
        constructor
        · rintro ⟨ha, -, hb⟩; exact ⟨ha, hb⟩
        · rintro ⟨ha, hb⟩; exact ⟨ha, h1.trans_le ha, hb⟩,
      integral_Icc_eq_integral_Ioc]
  have hsumN : ∀ t ∈ uIcc a b, ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) *
      (Ici (ρ : ℂ).im).indicator f' t = (zetaZeroConfig.N a t : ℝ) * f' t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hfilt : zeroWindowFinset a t =
        S.filter (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im ≤ t) := by
      ext ρ
      simp only [Finset.mem_filter, mem_zeroWindowFinset, hS]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans ht.2⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    rw [← sum_zeroWindowFinset_mult, Finset.sum_mul, hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases hρt : (ρ : ℂ).im ≤ t
    · rw [indicator_of_mem (show t ∈ Ici (ρ : ℂ).im from hρt), if_pos hρt]
    · rw [indicator_of_notMem (show t ∉ Ici (ρ : ℂ).im from hρt), if_neg hρt, mul_zero]
  have hintρ : ∀ ρ ∈ S, IntervalIntegrable (fun t => (zetaZeroConfig.mult ρ : ℝ) *
      (Ici (ρ : ℂ).im).indicator f' t) volume a b := fun ρ _ =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (hint.indicator measurableSet_Ici)).const_mul _
  calc ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * f (ρ : ℂ).im
      = ∑ ρ ∈ S, ((zetaZeroConfig.mult ρ : ℝ) * f b -
          ∫ t in a..b, (zetaZeroConfig.mult ρ : ℝ) * (Ici (ρ : ℂ).im).indicator f' t) := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [hftc ρ hρ, hind ρ hρ, intervalIntegral.integral_const_mul]; ring
    _ = (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ)) * f b -
          ∫ t in a..b, ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) * (Ici (ρ : ℂ).im).indicator f' t := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul, intervalIntegral.integral_finsetSum hintρ]
    _ = (zetaZeroConfig.N a b : ℝ) * f b - ∫ t in a..b, (zetaZeroConfig.N a t : ℝ) * f' t := by
        rw [intervalIntegral.integral_congr hsumN, hS, sum_zeroWindowFinset_mult]

/-- The density `M'(t) = log(t/2π)/2π` of the smooth Riemann–von Mangoldt term. -/
def smoothCountDensity (t : ℝ) : ℝ := (Real.log (t / routeKRVMBase) + 1) / (2 * π)

theorem continuousOn_smoothCountDensity : ContinuousOn smoothCountDensity (Ioi 0) := by
  intro t ht
  have ht0 : t ≠ 0 := (mem_Ioi.mp ht).ne'
  have hb : t / routeKRVMBase ≠ 0 := div_ne_zero ht0 routeKRVMBase_pos.ne'
  exact ((((continuousAt_id.div_const _).log hb).add continuousAt_const).div_const _
    ).continuousWithinAt

theorem zeroWindow_count_eq {t : ℝ} (ht : 1 ≤ t) :
    (zetaZeroConfig.N 1 t : ℝ) = zeroCountReal t - zeroCountReal 1 := by
  have h := xiZeroCount_sub_eq zero_le_one ht
  unfold zeroCountReal
  have h' : ((xiZeroCount t - xiZeroCount 1 : ℤ) : ℝ) = ((zetaZeroConfig.N 1 t : ℤ) : ℝ) := by
    rw [h]
  push_cast at h'
  linarith

section Stieltjes

variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

theorem continuous_psiDeriv : Continuous (psiDeriv ℓ) := by
  have hK := bumpMomentKernel_contDiff' hℓ (n := 0)
  have hc : HasCompactSupport (bumpMomentKernel ℓ) :=
    hasCompactSupport_of_support_subset_abs (bumpMomentKernel_support hℓ)
  exact Complex.continuous_re.comp
    ((WeilEF.differentiable_paperFT hK.continuous hc).continuous.comp Complex.continuous_ofReal)

theorem continuous_psi_zero : Continuous (psi ℓ 0) :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_psi_zero hℓ y).continuousAt

/-- **The Stieltjes identity on `[1, 2T]`.**  With `S = N − M`,
`Σ_{1<γ≤2T} m ψ(γ − T) − ∫_1^{2T} ψ(t − T) M'(t) dt =
  ψ(T) S(2T) − ψ(1 − T) S(1) − ∫_1^{2T} S(t) ψ'(t − T) dt`. -/
theorem sum_zeroWindow_psi_sub_integral_eq {T : ℝ} (hT : 1 ≤ T) :
    ∑ ρ ∈ zeroWindowFinset 1 (2 * T), (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) -
        ∫ t in (1 : ℝ)..(2 * T), psi ℓ 0 (t - T) * smoothCountDensity t =
      psi ℓ 0 T * rvmRemainder (2 * T) - psi ℓ 0 (1 - T) * rvmRemainder 1 -
        ∫ t in (1 : ℝ)..(2 * T), rvmRemainder t * psiDeriv ℓ (t - T) := by
  have h12 : (1 : ℝ) ≤ 2 * T := by linarith
  have hu : ∀ t, HasDerivAt (fun t => psi ℓ 0 (t - T)) (psiDeriv ℓ (t - T)) t := fun t =>
    (hasDerivAt_psi_zero hℓ (t - T)).comp_sub_const t T
  have hcu : Continuous fun t => psiDeriv ℓ (t - T) :=
    (continuous_psiDeriv hℓ).comp (continuous_id.sub continuous_const)
  have hpos : ∀ t ∈ uIcc (1 : ℝ) (2 * T), 0 < t := fun t ht => by
    rw [uIcc_of_le h12] at ht; linarith [ht.1]
  -- Abel summation for the zeros
  have hA := sum_zeroWindowFinset_mul_eq h12 (f := fun t => psi ℓ 0 (t - T))
    (f' := fun t => psiDeriv ℓ (t - T)) (fun t _ => hu t) hcu.continuousOn
  simp only [show 2 * T - T = T by ring] at hA
  -- integration by parts for the smooth term
  have hM : ∀ t ∈ uIcc (1 : ℝ) (2 * T), HasDerivAt routeKSmoothRVMCount (smoothCountDensity t) t :=
    fun t ht => hasDerivAt_routeKSmoothRVMCount (hpos t ht)
  have hMc : ContinuousOn smoothCountDensity (uIcc (1 : ℝ) (2 * T)) :=
    continuousOn_smoothCountDensity.mono fun t ht => hpos t ht
  have hP := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hu t) hM
    (hcu.intervalIntegrable _ _) hMc.intervalIntegrable
  simp only [show 2 * T - T = T by ring] at hP
  -- the integrals of `N`, `M` and `S` against `ψ'`
  have hNmono : MonotoneOn zeroCountReal (uIcc (1 : ℝ) (2 * T)) :=
    fun x _ y _ h => zeroCountReal_mono h
  have hiN : IntervalIntegrable (fun t => zeroCountReal t * psiDeriv ℓ (t - T)) volume 1 (2 * T) :=
    hNmono.intervalIntegrable.mul_continuousOn hcu.continuousOn
  have hiM : IntervalIntegrable (fun t => routeKSmoothRVMCount t * psiDeriv ℓ (t - T)) volume 1
      (2 * T) :=
    ((continuousOn_routeKSmoothRVMCount.mono fun t ht => hpos t ht).mul
      hcu.continuousOn).intervalIntegrable
  have hi1 : IntervalIntegrable (fun t => zeroCountReal 1 * psiDeriv ℓ (t - T)) volume 1 (2 * T) :=
    (continuous_const.mul hcu).intervalIntegrable _ _
  have hN1 : ∫ t in (1 : ℝ)..(2 * T), (zetaZeroConfig.N 1 t : ℝ) * psiDeriv ℓ (t - T) =
      (∫ t in (1 : ℝ)..(2 * T), zeroCountReal t * psiDeriv ℓ (t - T)) -
        zeroCountReal 1 * ∫ t in (1 : ℝ)..(2 * T), psiDeriv ℓ (t - T) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hiN hi1]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le h12] at ht
    simp only [zeroWindow_count_eq ht.1]
    ring
  have hS : ∫ t in (1 : ℝ)..(2 * T), rvmRemainder t * psiDeriv ℓ (t - T) =
      (∫ t in (1 : ℝ)..(2 * T), zeroCountReal t * psiDeriv ℓ (t - T)) -
        ∫ t in (1 : ℝ)..(2 * T), routeKSmoothRVMCount t * psiDeriv ℓ (t - T) := by
    rw [← intervalIntegral.integral_sub hiN hiM]
    exact intervalIntegral.integral_congr fun t _ => by simp only [rvmRemainder]; ring
  have hFTC : ∫ t in (1 : ℝ)..(2 * T), psiDeriv ℓ (t - T) = psi ℓ 0 T - psi ℓ 0 (1 - T) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hu t) (hcu.intervalIntegrable _ _)]
    simp only [show 2 * T - T = T by ring]
  have hN2 := zeroWindow_count_eq h12
  have hcomm : ∫ t in (1 : ℝ)..(2 * T), psiDeriv ℓ (t - T) * routeKSmoothRVMCount t =
      ∫ t in (1 : ℝ)..(2 * T), routeKSmoothRVMCount t * psiDeriv ℓ (t - T) :=
    intervalIntegral.integral_congr fun t _ => mul_comm _ _
  rw [hA, hP, hN1, hS, hcomm, hFTC, hN2]
  simp only [rvmRemainder]
  ring

end Stieltjes

end GaloisForLFunctions.SquareRootThreshold
