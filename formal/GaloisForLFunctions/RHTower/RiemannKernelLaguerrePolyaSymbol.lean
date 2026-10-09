import GaloisForLFunctions.RHTower.RiemannKernelSineSymbolLaguerrePolya
import GaloisForLFunctions.RHTower.LaguerrePolyaDivideRealZero
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness

/-!
# Laguerre–Pólya symbols preserve the Laguerre–Pólya class on Riemann-kernel transforms

**Theorem** (`laguerrePolya_paperFT_mul_symbol`). Let `φ` be Laguerre–Pólya with `φ(0) ≠ 0`, and
`g` of exponential growth. If `z ↦ ∫ Φ(u)g(u)e^{izu}du` is Laguerre–Pólya, so is
`z ↦ ∫ Φ(u)g(u)φ(iu)e^{izu}du`, i.e. `φ(D)` preserves the class on these transforms.

**Corollary** (`not_laguerrePolya_paperFT_div_symbol`). For every Laguerre–Pólya `φ` with
`φ(0) ≠ 0` and a real zero `a ≠ 0`, the transform `∫ Φ(u)φ(iu)^{−1}e^{izu}du` is not
Laguerre–Pólya. Write `φ = (1 − z/a)φ₂` with `φ₂ = −a·dslope φ a` Laguerre–Pólya
(`laguerrePolya_dslope`); applying `φ₂(D)` yields the first-order damped transform
`∫ Φ(u)(1 − iu/a)^{−1}e^{izu}du`, which is not Laguerre–Pólya
(`not_laguerrePolya_dampedKernelTransform`). This is CANNOT-497 for transcendental symbols.

**Proof of the theorem.** Real-rooted approximants `p_m → φ` act as products of linear factors
(`laguerrePolya_paperFT_mul_poly`). On the imaginary axis they obey the uniform Gaussian bound
`|p_m(iu)| ≤ K e^{cu²}`: indeed `|p(iu)|² ≤ p(0)² exp(u²Λ(p)/p(0)²)`
(`norm_sq_polyEvalC_I_mul_le`), and `p_m(0)`, `Λ(p_m)` converge with the Taylor coefficients of
`φ`. Riemann's kernel decays like `exp(−3e^{2|u|})` and so beats every Gaussian
(`exists_norm_riemannPhiKernel_le_gauss`). Dominated convergence and closure under locally
uniform limits finish.
-/

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open Zeta23
open GaloisForLFunctions.HTGeometry

namespace RHTower.KernelStrip

noncomputable section

/-! ## Riemann's kernel beats every Gaussian -/

theorem exists_norm_riemannPhiKernel_le_gauss (c R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      ‖riemannPhiKernel u‖ ≤ C * Real.exp (-(c * u ^ 2 + R * |u|)) := by
  obtain ⟨C₀, hC₀⟩ := RHTower.riemannPhiKernel_decay_below_theta (c := 3) (by norm_num)
    (by linarith [Real.pi_gt_three])
  set K : ℝ := c ^ 2 / 4 + R ^ 2 / 4 + 1 / 4 with hK
  refine ⟨max C₀ 0 * Real.exp K, by positivity, fun u => ?_⟩
  set t := |u| with ht
  have ht0 : 0 ≤ t := abs_nonneg u
  have hu2 : u ^ 2 = t ^ 2 := (sq_abs u).symm
  have h4 : 2 * t ^ 4 ≤ 3 * Real.exp (2 * |u|) := by
    have := Real.pow_div_factorial_le_exp (2 * t) (by positivity) 4
    norm_num [Nat.factorial] at this
    nlinarith
  have hpoly : c * t ^ 2 + R * t ≤ 2 * t ^ 4 + K := by
    nlinarith [sq_nonneg (t ^ 2 - c / 2), sq_nonneg (t - R / 2), sq_nonneg (t ^ 2 - 1 / 2)]
  calc ‖riemannPhiKernel u‖ ≤ C₀ * Real.exp (-(3 * Real.exp (2 * |u|))) := hC₀ u
    _ ≤ max C₀ 0 * Real.exp (-(3 * Real.exp (2 * |u|))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C₀ 0 * Real.exp (K - (c * u ^ 2 + R * |u|)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (le_max_right _ _)
        rw [hu2]; linarith
    _ = max C₀ 0 * Real.exp K * Real.exp (-(c * u ^ 2 + R * |u|)) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring

/-! ## Polynomial symbols -/

theorem polyEvalC_multiset_prod (s : Multiset ℝ) (z : ℂ) :
    polyEvalC ((s.map fun r => X - C r).prod) z = (s.map fun r : ℝ => z - (r : ℂ)).prod := by
  induction s using Multiset.induction with
  | empty => simp [polyEvalC]
  | cons r t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, polyEvalC_mul, polyEvalC_X_sub_C, ih,
      Multiset.map_cons, Multiset.prod_cons]

/-- Products of linear factors `iu − r`, `r ≠ 0`, preserve the class. -/
theorem laguerrePolya_paperFT_mul_rootProd {g : ℝ → ℂ} (hg : ExpGrowth g) (s : Multiset ℝ)
    (hs : ∀ r ∈ s, r ≠ 0)
    (hLP : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * g u) z) :
    ExpGrowth (fun u : ℝ => g u * (s.map fun r : ℝ => I * (u : ℂ) - (r : ℂ)).prod) ∧
      GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
        paperFT (fun u => riemannPhiKernel u *
          (g u * (s.map fun r : ℝ => I * (u : ℂ) - (r : ℂ)).prod)) z := by
  induction s using Multiset.induction with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one]
    exact ⟨hg, hLP⟩
  | cons r t ih =>
    obtain ⟨hgt, hLPt⟩ := ih fun r' hr' => hs r' (Multiset.mem_cons_of_mem hr')
    have hr : -r ≠ 0 := neg_ne_zero.mpr (hs r (Multiset.mem_cons_self r t))
    have hstep := laguerrePolya_paperFT_mul_linear hgt hr 1 hLPt
    have e : ∀ u : ℝ, g u * (t.map fun r : ℝ => I * (u : ℂ) - (r : ℂ)).prod *
        (((-r : ℝ) : ℂ) + I * ((1 : ℝ) : ℂ) * u) =
        g u * ((r ::ₘ t).map fun r : ℝ => I * (u : ℂ) - (r : ℂ)).prod := by
      intro u
      rw [Multiset.map_cons, Multiset.prod_cons]
      push_cast; ring
    refine ⟨?_, laguerrePolya_paperFT_congr e hstep⟩
    have := hgt.mul (expGrowth_linear (-r) 1)
    obtain ⟨hc, A, κ, hA⟩ := this
    exact ⟨hc.congr fun u => e u, A, κ, fun u => by simpa only [e u] using hA u⟩

/-- **Real-rooted polynomial symbols preserve the class.** -/
theorem laguerrePolya_paperFT_mul_poly {g : ℝ → ℂ} (hg : ExpGrowth g) {p : ℝ[X]}
    (hp : p.Splits) (hp0 : p.eval 0 ≠ 0)
    (hLP : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * g u) z) :
    ExpGrowth (fun u : ℝ => g u * polyEvalC p (I * u)) ∧
      GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
        paperFT (fun u => riemannPhiKernel u * (g u * polyEvalC p (I * u))) z := by
  have hroots : ∀ r ∈ p.roots, r ≠ 0 := by
    intro r hr h
    rw [h] at hr
    exact hp0 ((mem_roots (by rintro rfl; simp at hp0)).mp hr)
  obtain ⟨hE, hL⟩ := laguerrePolya_paperFT_mul_rootProd hg p.roots hroots hLP
  have e : ∀ u : ℝ, g u * (p.roots.map fun r : ℝ => I * (u : ℂ) - (r : ℂ)).prod *
      ((p.leadingCoeff : ℂ) + I * ((0 : ℝ) : ℂ) * u) = g u * polyEvalC p (I * u) := by
    intro u
    conv_rhs => rw [hp.eq_prod_roots]
    rw [polyEvalC_mul, polyEvalC_C, polyEvalC_multiset_prod]
    push_cast; ring
  by_cases hlc : p.leadingCoeff = 0
  · exfalso; rw [leadingCoeff_eq_zero] at hlc; rw [hlc] at hp0; simp at hp0
  have hstep := laguerrePolya_paperFT_mul_linear hE hlc 0 hL
  refine ⟨?_, laguerrePolya_paperFT_congr e hstep⟩
  have := hE.mul (expGrowth_linear p.leadingCoeff 0)
  obtain ⟨hc, A, κ, hA⟩ := this
  exact ⟨hc.congr fun u => e u, A, κ, fun u => by simpa only [e u] using hA u⟩

/-! ## Dominated convergence under a Gaussian bound -/

theorem norm_kernel_mul_le_gauss {g : ℝ → ℂ} (hg : ExpGrowth g) (K c R : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℝ → ℂ), (∀ u, ‖k u‖ ≤ K * Real.exp (c * u ^ 2)) →
      ∀ u : ℝ, ‖riemannPhiKernel u‖ * ‖g u‖ * ‖k u‖ * Real.exp (|R| * |u|) ≤
        C * Real.exp (-(1 * |u|)) := by
  obtain ⟨-, A, κ, hA⟩ := hg
  have hA0 : 0 ≤ A := by have := (norm_nonneg _).trans (hA 0); simpa using this
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_gauss c (κ + |R| + 1)
  refine ⟨C * A * K, by positivity, fun k hk u => ?_⟩
  calc ‖riemannPhiKernel u‖ * ‖g u‖ * ‖k u‖ * Real.exp (|R| * |u|)
      ≤ (C * Real.exp (-(c * u ^ 2 + (κ + |R| + 1) * |u|))) * (A * Real.exp (κ * |u|)) *
          (K * Real.exp (c * u ^ 2)) * Real.exp (|R| * |u|) := by
        gcongr
        · exact hC u
        · exact hA u
        · exact hk u
    _ = C * A * K * Real.exp (-(1 * |u|)) := by
        rw [show C * Real.exp (-(c * u ^ 2 + (κ + |R| + 1) * |u|)) * (A * Real.exp (κ * |u|)) *
            (K * Real.exp (c * u ^ 2)) * Real.exp (|R| * |u|) =
            C * A * K * (Real.exp (-(c * u ^ 2 + (κ + |R| + 1) * |u|)) * Real.exp (κ * |u|) *
              Real.exp (c * u ^ 2) * Real.exp (|R| * |u|)) by ring,
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- **Locally uniform convergence of transforms under a uniform Gaussian bound.** -/
theorem tendstoLocallyUniformly_paperFT_of_gaussBound {g : ℝ → ℂ} (hg : ExpGrowth g)
    {k : ℕ → ℝ → ℂ} {kLim : ℝ → ℂ} (hk : ∀ m, Continuous (k m)) (hkLim : Continuous kLim)
    {K c : ℝ} (hK : 0 ≤ K) (hb : ∀ m u, ‖k m u‖ ≤ K * Real.exp (c * u ^ 2))
    (hbLim : ∀ u, ‖kLim u‖ ≤ K * Real.exp (c * u ^ 2))
    (hlim : ∀ u, Tendsto (fun m => k m u) atTop (𝓝 (kLim u))) :
    TendstoLocallyUniformly (fun (m : ℕ) (z : ℂ) => paperFT (fun u => riemannPhiKernel u *
        (g u * k m u)) z) (fun z : ℂ => paperFT (fun u => riemannPhiKernel u * (g u * kLim u)) z)
      atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K' hK'
  obtain ⟨R, hR⟩ := hK'.isBounded.subset_closedBall (0 : ℂ)
  have gc := hg.1
  obtain ⟨C, hC0, hC⟩ := norm_kernel_mul_le_gauss hg (2 * K) c R (by positivity)
  have hdiff : ∀ m u, ‖kLim u - k m u‖ ≤ 2 * K * Real.exp (c * u ^ 2) := fun m u => by
    refine (norm_sub_le _ _).trans ?_
    have := hb m u; have := hbLim u; linarith
  set D : ℕ → ℝ → ℝ := fun m u => ‖riemannPhiKernel u‖ * ‖g u‖ * ‖kLim u - k m u‖ *
    Real.exp (|R| * |u|) with hD
  have hDbound : ∀ m u, D m u ≤ C * Real.exp (-(1 * |u|)) := fun m u =>
    hC (fun u => kLim u - k m u) (hdiff m) u
  have hDcont : ∀ m, Continuous (D m) := fun m => by
    simp only [hD]
    exact ((continuous_norm.comp continuous_riemannPhiKernel).mul (continuous_norm.comp gc)).mul
      (continuous_norm.comp (hkLim.sub (hk m))) |>.mul (by fun_prop)
  have hint : Integrable fun u : ℝ => C * Real.exp (-(1 * |u|)) :=
    (RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul _
  have hDint : ∀ m, Integrable (D m) := fun m =>
    hint.mono' (hDcont m).aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hD]; positivity)]
      exact hDbound m u)
  have hDlim : Tendsto (fun m => ∫ u, D m u) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun u => C * Real.exp (-(1 * |u|)))
      (fun m => (hDcont m).aestronglyMeasurable) hint
      (fun m => Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hD]; positivity)]
        exact hDbound m u)
      (Eventually.of_forall fun u => by
        have h1 : Tendsto (fun m => ‖kLim u - k m u‖) atTop (𝓝 0) := by
          have := (hlim u).const_sub (kLim u)
          rw [sub_self] at this
          have h2 := (continuous_norm.tendsto _).comp this
          rw [norm_zero] at h2
          exact h2
        have := (h1.const_mul (‖riemannPhiKernel u‖ * ‖g u‖)).mul_const (Real.exp (|R| * |u|))
        simpa [hD, mul_assoc] using this)
    simpa using h
  -- integrability of each transform integrand
  obtain ⟨C₁, hC₁0, hC₁⟩ := norm_kernel_mul_le_gauss hg K c R hK
  have hI : ∀ (k' : ℝ → ℂ), Continuous k' → (∀ u, ‖k' u‖ ≤ K * Real.exp (c * u ^ 2)) →
      ∀ z : ℂ, ‖z‖ ≤ R → Integrable fun u : ℝ =>
        riemannPhiKernel u * (g u * k' u) * cexp (I * z * u) := by
    intro k' hk' hbk z hz
    refine ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C₁).mono'
      ((continuous_riemannPhiKernel.mul (gc.mul hk')).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_mul, norm_mul, ← mul_assoc]
    calc ‖riemannPhiKernel u‖ * ‖g u‖ * ‖k' u‖ * ‖cexp (I * z * u)‖
        ≤ ‖riemannPhiKernel u‖ * ‖g u‖ * ‖k' u‖ * Real.exp (|R| * |u|) :=
          mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_of_norm_le hz u) (by positivity)
      _ ≤ C₁ * Real.exp (-(1 * |u|)) := hC₁ k' hbk u
  have hG : ∀ (m : ℕ) (z : ℂ), ‖z‖ ≤ R →
      dist (paperFT (fun u => riemannPhiKernel u * (g u * kLim u)) z)
        (paperFT (fun u => riemannPhiKernel u * (g u * k m u)) z) ≤ ∫ u, D m u := by
    intro m z hz
    have i1 := hI kLim hkLim hbLim z hz
    have i2 := hI (k m) (hk m) (hb m) z hz
    rw [dist_eq_norm]
    unfold paperFT
    rw [← integral_sub i1 i2]
    refine norm_integral_le_of_norm_le (hDint m) (Eventually.of_forall fun u => ?_)
    have e : riemannPhiKernel u * (g u * kLim u) * cexp (I * z * u) -
        riemannPhiKernel u * (g u * k m u) * cexp (I * z * u) =
        riemannPhiKernel u * g u * (kLim u - k m u) * cexp (I * z * u) := by ring
    rw [e, norm_mul, norm_mul, norm_mul]
    simp only [hD]
    exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_of_norm_le hz u) (by positivity)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hDlim.eventually (gt_mem_nhds hε)] with m hm z hz
  have hzR : ‖z‖ ≤ R := by simpa using hR hz
  exact (hG m z hzR).trans_lt hm

/-! ## Laguerre–Pólya symbols -/

theorem eval_zero_derivative (q : ℝ[X]) : (derivative q).eval 0 = q.coeff 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]; norm_num

theorem eval_zero_derivative_derivative (q : ℝ[X]) :
    (derivative (derivative q)).eval 0 = 2 * q.coeff 2 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative]; norm_num; ring

/-- **Laguerre–Pólya symbols preserve the class.** -/
theorem laguerrePolya_paperFT_mul_symbol {g : ℝ → ℂ} (hg : ExpGrowth g) {φ : ℂ → ℂ}
    (hφ : GaloisForLFunctions.HTGeometry.LaguerrePolya φ) (hφ0 : φ 0 ≠ 0)
    (hLP : GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * g u) z) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * (g u * φ (I * u))) z := by
  have hφd := hφ.differentiable
  obtain ⟨p, hsplit, hconv⟩ := hφ
  -- the real Taylor coefficients
  set L : ℕ → ℝ := fun j => (deriv^[j] φ 0 / (j.factorial : ℂ)).re with hL
  have hcoef : ∀ j, Tendsto (fun m => (p m).coeff j) atTop (𝓝 (L j)) := fun j => by
    have h := tendsto_coeff_of_tendstoLocallyUniformly hconv j
    have h2 := (Complex.continuous_re.tendsto _).comp h
    simp only [Function.comp_def, Complex.ofReal_re] at h2
    exact h2
  have hφ0' : φ 0 = ((L 0 : ℝ) : ℂ) := by
    have h := tendsto_coeff_of_tendstoLocallyUniformly hconv 0
    simp only [Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one, div_one] at h
    have him := (Complex.continuous_im.tendsto _).comp h
    simp only [Function.comp_def, Complex.ofReal_im] at him
    have him0 : (φ 0).im = 0 := tendsto_nhds_unique him tendsto_const_nhds
    apply Complex.ext
    · simp [hL]
    · simp [him0]
  have hL0 : L 0 ≠ 0 := by
    intro h; apply hφ0; rw [hφ0', h, Complex.ofReal_zero]
  -- convergence of `p_m(0)` and of `Λ(p_m)/p_m(0)²`
  have he0 : Tendsto (fun m => (p m).eval 0) atTop (𝓝 (L 0)) := by
    simpa only [coeff_zero_eq_eval_zero] using hcoef 0
  set Qlim : ℝ := (L 1 ^ 2 - L 0 * (2 * L 2)) / L 0 ^ 2 with hQlim
  have hQ : Tendsto (fun m => lagAtZero (p m) / (p m).eval 0 ^ 2) atTop (𝓝 Qlim) := by
    have e : ∀ m, lagAtZero (p m) / (p m).eval 0 ^ 2 =
        ((p m).coeff 1 ^ 2 - (p m).coeff 0 * (2 * (p m).coeff 2)) / (p m).coeff 0 ^ 2 := by
      intro m
      rw [lagAtZero, eval_zero_derivative, eval_zero_derivative_derivative,
        coeff_zero_eq_eval_zero]
    simp_rw [e]
    exact (((hcoef 1).pow 2).sub ((hcoef 0).mul ((hcoef 2).const_mul 2))).div
      ((hcoef 0).pow 2) (pow_ne_zero 2 hL0)
  set K : ℝ := |L 0| + 1 with hK
  set cG : ℝ := max (Qlim + 1) 0 / 2 with hcG
  have hK0 : 0 ≤ K := by positivity
  have hev : ∀ᶠ m in atTop, (p m).eval 0 ≠ 0 ∧ |(p m).eval 0| ≤ K ∧
      lagAtZero (p m) / (p m).eval 0 ^ 2 ≤ Qlim + 1 := by
    have h1 := he0.eventually_ne hL0
    have h2 : ∀ᶠ m in atTop, |(p m).eval 0| ≤ K := by
      have := ((continuous_abs.tendsto _).comp he0).eventually (gt_mem_nhds
        (show |L 0| < K by rw [hK]; linarith))
      exact this.mono fun m hm => hm.le
    have h3 := hQ.eventually (gt_mem_nhds (show Qlim < Qlim + 1 by linarith))
    filter_upwards [h1, h2, h3] with m hm1 hm2 hm3 using ⟨hm1, hm2, hm3.le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- the uniform Gaussian bound
  have hbound : ∀ (m : ℕ) (u : ℝ), ‖polyEvalC (p (m + N)) (I * u)‖ ≤ K * Real.exp (cG * u ^ 2) := by
    intro m u
    obtain ⟨h0, hK', hQm⟩ := hN (m + N) (by omega)
    have hsq := norm_sq_polyEvalC_I_mul_le (hsplit (m + N)) h0 u
    have hexp : u ^ 2 * lagAtZero (p (m + N)) / (p (m + N)).eval 0 ^ 2 ≤ (2 * cG) * u ^ 2 := by
      rw [mul_div_assoc]
      have : lagAtZero (p (m + N)) / (p (m + N)).eval 0 ^ 2 ≤ 2 * cG := by
        rw [hcG]; linarith [le_max_left (Qlim + 1) 0]
      nlinarith [sq_nonneg u]
    have hsq' : ‖polyEvalC (p (m + N)) (I * u)‖ ^ 2 ≤ (K * Real.exp (cG * u ^ 2)) ^ 2 := by
      calc _ ≤ (p (m + N)).eval 0 ^ 2 *
            Real.exp (u ^ 2 * lagAtZero (p (m + N)) / (p (m + N)).eval 0 ^ 2) := hsq
        _ ≤ K ^ 2 * Real.exp ((2 * cG) * u ^ 2) := by
            refine mul_le_mul ?_ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (sq_nonneg _)
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hK' 2
        _ = (K * Real.exp (cG * u ^ 2)) ^ 2 := by
            rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq'
  have hlim : ∀ u : ℝ, Tendsto (fun m => polyEvalC (p (m + N)) (I * u)) atTop (𝓝 (φ (I * u))) := by
    intro u
    have h := TendstoLocallyUniformlyOn.tendsto_at (tendstoLocallyUniformlyOn_univ.2 hconv)
      (Set.mem_univ (I * (u : ℂ)))
    exact h.comp (tendsto_add_atTop_nat N)
  have hboundLim : ∀ u : ℝ, ‖φ (I * u)‖ ≤ K * Real.exp (cG * u ^ 2) := fun u =>
    le_of_tendsto' ((continuous_norm.tendsto _).comp (hlim u)) fun m => hbound m u
  have hconvT := tendstoLocallyUniformly_paperFT_of_gaussBound hg
    (k := fun m u => polyEvalC (p (m + N)) (I * u)) (kLim := fun u => φ (I * u))
    (fun m => (differentiable_polyEvalC _).continuous.comp (by fun_prop))
    (hφd.continuous.comp (by fun_prop)) hK0 hbound hboundLim hlim
  refine GaloisForLFunctions.HTGeometry.LaguerrePolya.of_tendstoLocallyUniformly
    (fun m => ?_) hconvT
  exact (laguerrePolya_paperFT_mul_poly hg (hsplit (m + N)) (hN (m + N) (by omega)).1 hLP).2

/-! ## CANNOT-497 for transcendental symbols -/

/-- **Damping by a Laguerre–Pólya symbol with a real zero leaves the class.** For every
Laguerre–Pólya `φ` with `φ(0) ≠ 0` and a real zero `a ≠ 0`, the transform
`z ↦ ∫ Φ(u) φ(iu)^{−1} e^{izu} du` is not Laguerre–Pólya. -/
theorem not_laguerrePolya_paperFT_div_symbol {φ : ℂ → ℂ}
    (hφ : GaloisForLFunctions.HTGeometry.LaguerrePolya φ) (hφ0 : φ 0 ≠ 0) {a : ℝ}
    (ha0 : a ≠ 0) (ha : φ a = 0) :
    ¬ GaloisForLFunctions.HTGeometry.LaguerrePolya fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * (φ (I * u))⁻¹) z := by
  intro hLP
  have hne : ∀ u : ℝ, φ (I * u) ≠ 0 := fun u h => by
    have := hφ.norm_I_mul_ge u
    rw [h, norm_zero] at this
    exact hφ0 (norm_le_zero_iff.mp this)
  have hφ0n : 0 < ‖φ 0‖ := norm_pos_iff.mpr hφ0
  have hg : ExpGrowth fun u : ℝ => (φ (I * u))⁻¹ :=
    ⟨(hφ.differentiable.continuous.comp (by fun_prop)).inv₀ hne, ‖φ 0‖⁻¹, 0, fun u => by
      rw [norm_inv, zero_mul, Real.exp_zero, mul_one]
      exact inv_anti₀ hφ0n (hφ.norm_I_mul_ge u)⟩
  set φ₂ : ℂ → ℂ := fun z => ((-a : ℝ) : ℂ) * dslope φ (a : ℂ) z with hφ₂def
  have hφ₂ : GaloisForLFunctions.HTGeometry.LaguerrePolya φ₂ :=
    (RHTower.laguerrePolya_dslope hφ hφ0 ha).const_mul (-a)
  have ha0' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  have hφ₂0 : φ₂ 0 ≠ 0 := by
    simp only [hφ₂def]
    rw [dslope_of_ne _ (Ne.symm ha0'), slope_def_field, ha]
    convert hφ0 using 1
    push_cast
    field_simp
    ring
  have hIu : ∀ u : ℝ, I * (u : ℂ) - a ≠ 0 := fun u h => by
    have := congrArg Complex.re h
    simp at this
    exact ha0 this
  have hmul : ∀ u : ℝ, (φ (I * u))⁻¹ * φ₂ (I * u) = (chainSymbol [1 / a] u)⁻¹ := by
    intro u
    simp only [hφ₂def, chainSymbol]
    rw [dslope_of_ne _ (sub_ne_zero.mp (hIu u)), slope_def_field, ha]
    have h1 := hne u
    have h2 := hIu u
    have h3 : (1 : ℂ) - I * ((1 / a : ℝ) : ℂ) * u ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
    have h2' : (a : ℂ) - I * u ≠ 0 := by
      intro h; apply h2; linear_combination -h
    have e1 : (1 : ℂ) - I * ((1 / a : ℝ) : ℂ) * u = ((a : ℂ) - I * u) / a := by
      push_cast; field_simp
    rw [mul_one, e1, inv_div]
    push_cast
    field_simp
    ring
  have hfinal := laguerrePolya_paperFT_mul_symbol hg hφ₂ hφ₂0 hLP
  refine not_laguerrePolya_dampedKernelTransform (cs := [1 / a])
    ⟨1 / a, List.mem_singleton_self _, one_div_ne_zero ha0⟩ ?_
  have e : dampedKernelTransform [1 / a] = fun z : ℂ =>
      paperFT (fun u => riemannPhiKernel u * ((φ (I * u))⁻¹ * φ₂ (I * u))) z := by
    funext z
    unfold dampedKernelTransform
    congr 1
    funext u
    rw [hmul u]
  rw [e]
  exact hfinal

end

end RHTower.KernelStrip
