import GaloisForLFunctions.RHTower.ThetaDivisorBernsteinGauge

/-!
# Translation mixtures of the theta source by finite measures: flux, sieve and seed

For a finite measure `ν` on `ℝ` with `∫ e^{|s|/2} dν < ∞`, the translation mixture
`g_ν = ∫ k(· + s) dν(s)` of the completed theta source satisfies:

* `∫ e^{wx} g_ν = M_ν(w) XiC(iw)` with `M_ν(w) = ∫ e^{-ws} dν` on `|Re w| ≤ 1/2`, and the flux
  law `b_{∫ f(·+s) dν}(t) = ∫ e^{5s/2} b_f(e^{2s} t) dν(s)`;
* prime deletion commutes with mixing, and every deleted flux of a positive mixture is completely
  monotone (positive mixtures of completely monotone profiles);
* along any exhaustion of the primes the deleted fluxes converge to the seed flux
  `b_{seed,ν}(t) = 2π ∫ e^{5s/2} e^{-π e^{2s} t} dν(s)`;
* complete monotonicity of a signed seed flux forces positivity of the signed translation measure
  (Bernstein–Widder, Laplace uniqueness and the injective rate map `s ↦ π e^{2s}`).

**All-sieve theorem.**  Every finite-prime-deleted flux of `∫ k(·+s) d(ν₁ - ν₂)(s)` is completely
monotone iff `ν₂ ≤ ν₁`.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-! ## Complete monotonicity under integrals and pointwise limits -/

theorem fwdDiff_iter_eq_sum_mul (δ : ℝ) (f : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    (fwdDiff δ)^[k] f t = ∑ i ∈ Finset.range (k + 1),
      (((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) : ℤ) : ℝ) * f (t + i * δ) := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul]

/-- A positive mixture of completely monotone profiles is completely monotone. -/
theorem completelyMonotoneOn_integral {ν : Measure ℝ} {G : ℝ → ℝ → ℝ}
    (hG : ∀ s, CompletelyMonotoneOn (G s)) (hint : ∀ t, 0 < t → Integrable (fun s => G s t) ν)
    (hcont : ContinuousOn (fun t => ∫ s, G s t ∂ν) (Ioi 0)) :
    CompletelyMonotoneOn (fun t => ∫ s, G s t ∂ν) := by
  refine ⟨fun k δ hδ t ht => ?_, hcont⟩
  have hpos : ∀ i : ℕ, 0 < t + i * δ := fun i => by positivity
  rw [fwdDiff_iter_eq_sum_mul]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (hint _ (hpos i)).const_mul _, ← integral_const_mul]
  refine integral_nonneg fun s => ?_
  have := (hG s).1 k δ hδ t ht
  rwa [fwdDiff_iter_eq_sum_mul] at this

/-- Complete monotonicity passes to pointwise limits with a continuous limit profile. -/
theorem completelyMonotoneOn_of_tendsto {F : ℕ → ℝ → ℝ} {H : ℝ → ℝ}
    (hF : ∀ j, CompletelyMonotoneOn (F j))
    (hlim : ∀ t, 0 < t → Tendsto (fun j => F j t) atTop (𝓝 (H t)))
    (hcont : ContinuousOn H (Ioi 0)) : CompletelyMonotoneOn H := by
  refine ⟨fun k δ hδ t ht => ?_, hcont⟩
  have hpos : ∀ i : ℕ, 0 < t + i * δ := fun i => by positivity
  have hsum : Tendsto (fun j => (-1 : ℝ) ^ k * (fwdDiff δ)^[k] (F j) t) atTop
      (𝓝 ((-1) ^ k * (fwdDiff δ)^[k] H t)) := by
    simp only [fwdDiff_iter_eq_sum_mul]
    exact (tendsto_finsetSum _ fun i _ => (hlim _ (hpos i)).const_mul _).const_mul _
  exact ge_of_tendsto' hsum fun j => (hF j).1 k δ hδ t ht

theorem integrable_exp_neg_mul_of_Ici {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ : ρ (Ici 0)ᶜ = 0)
    {u : ℝ} (hu : 0 ≤ u) : Integrable (fun r => Real.exp (-u * r)) ρ := by
  have hae : ∀ᵐ r ∂ρ, r ∈ Ici (0 : ℝ) := ae_iff.mpr hρ
  refine Integrable.mono' (integrable_const 1) (by fun_prop : Continuous fun r : ℝ =>
    Real.exp (-u * r)).aestronglyMeasurable ?_
  filter_upwards [hae] with r hr
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [mem_Ici.mp hr])

/-- **Signed Laplace positivity.**  If the difference of the Laplace transforms of two finite
measures on `[0,∞)` is completely monotone, the difference is a positive measure. -/
theorem le_of_completelyMonotoneOn_laplace_sub {τ₁ τ₂ : Measure ℝ} [IsFiniteMeasure τ₁]
    [IsFiniteMeasure τ₂] (h₁ : τ₁ (Ici 0)ᶜ = 0) (h₂ : τ₂ (Ici 0)ᶜ = 0)
    (hCM : CompletelyMonotoneOn fun u =>
      (∫ r, Real.exp (-u * r) ∂τ₁) - ∫ r, Real.exp (-u * r) ∂τ₂) :
    τ₂ ≤ τ₁ := by
  have hlim := (tendsto_laplaceIntegral_nhdsGT_zero τ₁ h₁).sub
    (tendsto_laplaceIntegral_nhdsGT_zero τ₂ h₂)
  obtain ⟨τ, hτfin, hτ, hrep⟩ := exists_finiteLaplaceMeasure_of_completelyMonotoneOn hCM hlim
  haveI := hτfin
  have heq : τ + τ₂ = τ₁ := by
    refine measure_eq_of_laplace_eq (by rw [Measure.add_apply, hτ, h₂, add_zero]) h₁
      fun u hu => ?_
    rw [integral_add_measure (integrable_exp_neg_mul_of_Ici hτ hu.le)
      (integrable_exp_neg_mul_of_Ici h₂ hu.le), ← hrep u hu]
    ring
  rw [← heq]
  exact Measure.le_add_left le_rfl

/-! ## Translation mixtures by finite measures -/

/-- The translation mixture `∫ f(x + s) dν(s)`. -/
noncomputable def thetaMeasureGauge (ν : Measure ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s, f (x + s) ∂ν

theorem integrable_comp_add_of_bounded {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (x : ℝ) :
    Integrable (fun s => f (x + s)) ν :=
  Integrable.mono' (integrable_const C) (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hC _)

theorem continuous_thetaMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Continuous (thetaMeasureGauge ν f) := by
  refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_)
    (integrable_const C) (ae_of_all _ fun s => ?_)
  · exact (hf.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hC _
  · exact hf.comp (continuous_id.add continuous_const)

theorem abs_thetaPrimeDeletion_le {f : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) (S : Finset ℕ)
    (x : ℝ) : |thetaPrimeDeletion S f x| ≤ (2 : ℝ) ^ S.card * C := by
  unfold thetaPrimeDeletion
  calc |∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * (((∏ p ∈ T, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        f (x + Real.log (∏ p ∈ T, p : ℕ)))|
      ≤ ∑ T ∈ S.powerset, |(-1 : ℝ) ^ T.card * (((∏ p ∈ T, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        f (x + Real.log (∏ p ∈ T, p : ℕ)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ S.powerset, C := by
        refine Finset.sum_le_sum fun T _ => ?_
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        have h0 : 0 ≤ ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
        have h1 : ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
          rcases Nat.eq_zero_or_pos (∏ p ∈ T, p) with h | h
          · rw [h, Nat.cast_zero, Real.zero_rpow (by norm_num)]; norm_num
          · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h) (by norm_num)
        rw [abs_of_nonneg h0]
        have := hC (x + Real.log (∏ p ∈ T, p : ℕ))
        have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
        nlinarith [abs_nonneg (f (x + Real.log (∏ p ∈ T, p : ℕ)))]
    _ = (2 : ℝ) ^ S.card * C := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        push_cast
        ring

/-- Prime deletion commutes with translation mixtures. -/
theorem thetaPrimeDeletion_thetaMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (S : Finset ℕ) :
    thetaPrimeDeletion S (thetaMeasureGauge ν f) =
      thetaMeasureGauge ν (thetaPrimeDeletion S f) := by
  funext x
  unfold thetaPrimeDeletion thetaMeasureGauge
  have hre : ∀ (T : Finset ℕ) (s : ℝ), x + s + Real.log (∏ p ∈ T, p : ℕ) =
      x + Real.log (∏ p ∈ T, p : ℕ) + s := fun T s => by ring
  simp_rw [hre]
  rw [integral_finsetSum _ fun T _ => ((integrable_comp_add_of_bounded hf hC _).const_mul
    _).const_mul _]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [integral_const_mul, integral_const_mul]

theorem integral_norm_exp_half_comp_add (f : ℝ → ℝ) (s : ℝ) :
    (∫ x, ‖Real.exp (x / 2) * f (x + s)‖) =
      Real.exp (-(s / 2)) * ∫ y, ‖Real.exp (y / 2) * f y‖ := by
  rw [← integral_const_mul]
  have h := integral_add_right_eq_self (μ := volume)
    (fun y => Real.exp (-(s / 2)) * ‖Real.exp (y / 2) * f y‖) s
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- **Flux of a translation mixture.**  `b_{∫ f(·+s) dν}(t) = ∫ e^{5s/2} b_f(e^{2s} t) dν(s)`. -/
theorem thetaNormalizedFlux_thetaMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (-(s / 2))) ν) {f : ℝ → ℝ} (hf : Continuous f)
    (hfi : Integrable (fun y => Real.exp (y / 2) * f y)) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaMeasureGauge ν f) t =
      ∫ s, Real.exp (5 * s / 2) * thetaNormalizedFlux f (Real.exp (2 * s) * t) ∂ν := by
  simp_rw [← thetaNormalizedFlux_comp_add f _ ht]
  have key : ∀ s, thetaNormalizedFlux (fun x => f (x + s)) t = t ^ (-(3 / 2 : ℝ)) *
      ∫ x in Ici (Real.log t / 2), Real.exp (x / 2) * f (x + s) := fun s => rfl
  simp_rw [key]
  rw [integral_const_mul]
  unfold thetaNormalizedFlux thetaMeasureGauge
  congr 1
  simp_rw [← integral_const_mul]
  set μ := volume.restrict (Ici (Real.log t / 2))
  set F : ℝ × ℝ → ℝ := fun q => Real.exp (q.1 / 2) * f (q.1 + q.2)
  have hFc : Continuous F := by
    simp only [F]
    fun_prop
  have hFi : ∀ s, Integrable (fun x => F (x, s)) := fun s => by
    have h := (hfi.comp_add_right s).const_mul (Real.exp (-(s / 2)))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [F]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  have hint : Integrable F (μ.prod ν) := by
    rw [integrable_prod_iff' hFc.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun s => (hFi s).integrableOn, ?_⟩
    have hmeas : AEStronglyMeasurable (fun s => ∫ x, ‖F (x, s)‖ ∂μ) ν := by
      exact ((hFc.comp continuous_swap).norm.aestronglyMeasurable
        (μ := ν.prod μ)).integral_prod_right'
    refine Integrable.mono' (hν.mul_const (∫ y, ‖Real.exp (y / 2) * f y‖)) hmeas
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    calc (∫ x, ‖F (x, s)‖ ∂μ) ≤ ∫ x, ‖F (x, s)‖ :=
          setIntegral_le_integral (hFi s).norm (ae_of_all _ fun x => norm_nonneg _)
      _ = Real.exp (-(s / 2)) * ∫ y, ‖Real.exp (y / 2) * f y‖ :=
          integral_norm_exp_half_comp_add f s
  exact integral_integral_swap (f := fun x s => F (x, s)) hint

/-- **Real Laplace law of a translation mixture of `k`.** -/
theorem integral_exp_mul_thetaMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν] {w : ℝ}
    (hν : Integrable (fun s => Real.exp (-(w * s))) ν) :
    Integrable (fun x => Real.exp (w * x) * thetaMeasureGauge ν thetaCuspFullSource x) ∧
    (∫ x, Real.exp (w * x) * thetaMeasureGauge ν thetaCuspFullSource x) =
      (∫ s, Real.exp (-(w * s)) ∂ν) * ∫ y, Real.exp (w * y) * thetaCuspFullSource y := by
  set K := ∫ y, Real.exp (w * y) * thetaCuspFullSource y
  set F : ℝ × ℝ → ℝ := fun q => Real.exp (w * q.1) * thetaCuspFullSource (q.1 + q.2)
  have hFc : Continuous F := by
    have := continuous_thetaCuspFullSource
    simp only [F]
    fun_prop
  have hFi : ∀ s, Integrable (fun x => F (x, s)) := fun s =>
    integrable_exp_mul_comp_add_thetaCuspFullSource w s
  have hnorm : ∀ s, (∫ x, ‖F (x, s)‖) = Real.exp (-(w * s)) * K := by
    intro s
    rw [← integral_exp_mul_comp_add_thetaCuspFullSource]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [F, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos_all _).le)
  have hint : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFc.aestronglyMeasurable]
    exact ⟨ae_of_all _ hFi, (hν.mul_const K).congr (ae_of_all _ fun s => (hnorm s).symm)⟩
  have hswap := integral_integral_swap (f := fun x s => F (x, s)) hint
  have hfib : Integrable (fun x => ∫ s, F (x, s) ∂ν) := hint.integral_prod_left
  have heq : (fun x => Real.exp (w * x) * thetaMeasureGauge ν thetaCuspFullSource x) =
      fun x => ∫ s, F (x, s) ∂ν := by
    funext x
    simp only [F, thetaMeasureGauge]
    rw [integral_const_mul]
  refine ⟨heq ▸ hfib, ?_⟩
  rw [heq, hswap]
  simp only [F]
  simp_rw [integral_exp_mul_comp_add_thetaCuspFullSource]
  rw [integral_mul_const]

/-- **Complex Laplace law of a translation mixture of `k`** on the closed critical strip:
`∫ e^{wx} g_ν = M_ν(w) XiC(iw)` with `M_ν(w) = ∫ e^{-ws} dν(s)`. -/
theorem integral_cexp_mul_thetaMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaMeasureGauge ν thetaCuspFullSource x : ℂ)) =
      (∫ s, Complex.exp (-(w * s)) ∂ν) * XiC (I * w) := by
  set K := ∫ y, Real.exp (w.re * y) * thetaCuspFullSource y
  set F : ℝ × ℝ → ℂ := fun q => Complex.exp (w * q.1) * (thetaCuspFullSource (q.1 + q.2) : ℂ)
  have hFc : Continuous F := by
    have := continuous_thetaCuspFullSource
    simp only [F]
    fun_prop
  have hFi : ∀ s, Integrable (fun x => F (x, s)) := fun s =>
    integrable_cexp_mul_comp_add s (integrable_cexp_mul_thetaCuspFullSource w)
  have hnorm : ∀ s, (∫ x, ‖F (x, s)‖) = Real.exp (-(w.re * s)) * K := by
    intro s
    rw [← integral_exp_mul_comp_add_thetaCuspFullSource]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [F, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (thetaCuspFullSource_pos_all _), Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have hdom : Integrable (fun s => Real.exp (-(w.re * s))) ν := by
    refine Integrable.mono' hν (by fun_prop : Continuous fun s : ℝ =>
      Real.exp (-(w.re * s))).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc -(w.re * s) ≤ |w.re * s| := neg_le_abs _
      _ = |w.re| * |s| := abs_mul _ _
      _ ≤ 1 / 2 * |s| := by gcongr
      _ = |s| / 2 := by ring
  have hint : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hFc.aestronglyMeasurable]
    exact ⟨ae_of_all _ hFi, (hdom.mul_const K).congr (ae_of_all _ fun s => (hnorm s).symm)⟩
  have hswap := integral_integral_swap (f := fun x s => F (x, s)) hint
  have heq : (fun x : ℝ => Complex.exp (w * x) *
      (thetaMeasureGauge ν thetaCuspFullSource x : ℂ)) = fun x => ∫ s, F (x, s) ∂ν := by
    funext x
    simp only [F, thetaMeasureGauge]
    rw [← integral_complex_ofReal, integral_const_mul]
  rw [heq, hswap]
  simp only [F]
  have hin : ∀ s : ℝ, (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspFullSource (x + s) : ℂ)) =
      Complex.exp (-(w * s)) * XiC (I * w) := fun s => by
    rw [integral_cexp_mul_comp_add w s (fun y => (thetaCuspFullSource y : ℂ)),
      integral_cexp_mul_thetaCuspFullSource]
  simp_rw [hin]
  rw [integral_mul_const]

/-! ## Deleted fluxes of the theta source -/

theorem thetaNormalizedFlux_thetaPrimeDeletion_eq {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {u : ℝ}
    (hu : 0 < u) :
    thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) u =
      ∑' n : ℕ, (thetaCoprimeLabels S).indicator
        (fun m => 2 * Real.pi * (m : ℝ) ^ 2 * Real.exp (-Real.pi * (m : ℝ) ^ 2 * u)) n := by
  rw [thetaPrimeDeletion_thetaCuspFullSource_eq_atomSum S hS, thetaNormalizedFlux_thetaAtomSum _ hu]

theorem summable_thetaGaussFlux_atoms {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ => 2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (-Real.pi * (n : ℝ) ^ 2 * u) := by
  have h := (summable_pow_mul_exp_neg_nat_sq 2 (sigma := Real.pi * u) (by positivity)).mul_left
    (2 * Real.pi)
  refine h.congr fun n => ?_
  rw [show -Real.pi * (n : ℝ) ^ 2 * u = -(Real.pi * u) * (n : ℝ) ^ 2 by ring]
  ring

theorem thetaNormalizedFlux_thetaPrimeDeletion_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {u : ℝ} (hu : 0 < u) : 0 ≤ thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) u := by
  rw [thetaNormalizedFlux_thetaPrimeDeletion_eq hS hu]
  exact tsum_nonneg fun n => Set.indicator_nonneg (fun m _ => by positivity) n

theorem thetaNormalizedFlux_thetaPrimeDeletion_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {u : ℝ} (hu : 0 < u) :
    thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) u ≤ u ^ (-(3 / 2 : ℝ)) / 2 := by
  refine le_trans ?_ (thetaNormalizedFlux_thetaCuspFullSource_le hu)
  rw [thetaNormalizedFlux_thetaPrimeDeletion_eq hS hu, thetaNormalizedFlux_thetaCuspFullSource hu]
  exact (summable_thetaGaussFlux_atoms hu).indicator _ |>.tsum_le_tsum
    (fun n => Set.indicator_le_self' (fun m _ => by positivity) n) (summable_thetaGaussFlux_atoms hu)

/-- Each translated deleted flux profile `t ↦ e^{5s/2} b_{D_S k}(e^{2s} t)` is completely
monotone. -/
theorem completelyMonotoneOn_shifted_deletedFlux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (s : ℝ) :
    CompletelyMonotoneOn fun t => Real.exp (5 * s / 2) *
      thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t) := by
  classical
  have hCM := completelyMonotoneOn_tsum_exp
    (fun n : ℕ => Real.exp (5 * s / 2) * (thetaCoprimeLabels S).indicator
      (fun m => 2 * Real.pi * (m : ℝ) ^ 2) n)
    (fun n : ℕ => Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * s))
    (fun n => mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun m _ => by positivity) n))
    (fun n => by positivity) (fun t ht => by
      have hu : 0 < Real.exp (2 * s) * t := mul_pos (Real.exp_pos _) ht
      refine (((summable_thetaGaussFlux_atoms hu).indicator (thetaCoprimeLabels S)).mul_left
        (Real.exp (5 * s / 2))).congr fun n => ?_
      simp only [Set.indicator_apply]
      split_ifs
      · rw [show -Real.pi * (n : ℝ) ^ 2 * (Real.exp (2 * s) * t) =
          -(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * s)) * t by ring]
        ring
      · simp)
  refine hCM.congr_Ioi fun t ht => ?_
  have hu : 0 < Real.exp (2 * s) * t := mul_pos (Real.exp_pos _) ht
  simp only
  rw [thetaNormalizedFlux_thetaPrimeDeletion_eq hS hu, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [Set.indicator_apply]
  split_ifs
  · rw [show -Real.pi * (n : ℝ) ^ 2 * (Real.exp (2 * s) * t) =
      -(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * s)) * t by ring]
    ring
  · simp

theorem shifted_deletedFlux_le {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (s : ℝ) {t : ℝ}
    (ht : 0 < t) :
    |Real.exp (5 * s / 2) * thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource)
      (Real.exp (2 * s) * t)| ≤ Real.exp (-(s / 2)) * (t ^ (-(3 / 2 : ℝ)) / 2) := by
  have hu : 0 < Real.exp (2 * s) * t := mul_pos (Real.exp_pos _) ht
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (thetaNormalizedFlux_thetaPrimeDeletion_nonneg hS hu))]
  have hb := thetaNormalizedFlux_thetaPrimeDeletion_le hS hu
  rw [Real.mul_rpow (Real.exp_pos _).le ht.le, ← Real.exp_mul] at hb
  calc Real.exp (5 * s / 2) * thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource)
        (Real.exp (2 * s) * t)
      ≤ Real.exp (5 * s / 2) * (Real.exp (2 * s * (-(3 / 2 : ℝ))) * t ^ (-(3 / 2 : ℝ)) / 2) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Real.exp (-(s / 2)) * (t ^ (-(3 / 2 : ℝ)) / 2) := by
        rw [show Real.exp (5 * s / 2) * (Real.exp (2 * s * (-(3 / 2 : ℝ))) *
          t ^ (-(3 / 2 : ℝ)) / 2) = Real.exp (5 * s / 2) * Real.exp (2 * s * (-(3 / 2 : ℝ))) *
          (t ^ (-(3 / 2 : ℝ)) / 2) by ring, ← Real.exp_add]
        ring_nf

theorem continuousOn_deletedFlux {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ContinuousOn (thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource)) (Ioi 0) :=
  (completelyMonotoneOn_shifted_deletedFlux hS 0).2.congr fun t _ => by simp

theorem continuous_shifted_deletedFlux_in_shift {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {t : ℝ}
    (ht : 0 < t) : Continuous fun s => Real.exp (5 * s / 2) *
      thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t) :=
  (Real.continuous_exp.comp (by fun_prop)).mul ((continuousOn_deletedFlux hS).comp_continuous
    (by fun_prop) fun s => mul_pos (Real.exp_pos _) ht)

theorem continuousOn_integral_shifted_deletedFlux {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (-(s / 2))) ν) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ContinuousOn (fun t => ∫ s, Real.exp (5 * s / 2) *
      thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t) ∂ν)
      (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ / 2 := by have := mem_Ioi.mp ht₀; linarith
  have hloc : ContinuousOn (fun t => ∫ s, Real.exp (5 * s / 2) *
      thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t) ∂ν)
      (Ioi (t₀ / 2)) := by
    refine continuousOn_of_dominated
      (bound := fun s => Real.exp (-(s / 2)) * ((t₀ / 2) ^ (-(3 / 2 : ℝ)) / 2))
      (fun t ht => ?_) (fun t ht => ae_of_all _ fun s => ?_) (hν.mul_const _)
      (ae_of_all _ fun s => ?_)
    · have ht0 : 0 < t := lt_trans ht₀' ht
      exact (continuous_shifted_deletedFlux_in_shift hS ht0).aestronglyMeasurable
    · have ht0 : 0 < t := lt_trans ht₀' ht
      rw [Real.norm_eq_abs]
      refine (shifted_deletedFlux_le hS s ht0).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_nonpos ht₀' (le_of_lt ht)
        (by norm_num)) (by norm_num)
    · exact (completelyMonotoneOn_shifted_deletedFlux hS s).2.mono
        (fun t ht => lt_trans ht₀' ht)
  exact (hloc.continuousAt (Ioi_mem_nhds (by have := mem_Ioi.mp ht₀; linarith))).continuousWithinAt

theorem integrable_exp_neg_half_of_abs {ν : Measure ℝ}
    (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) :
    Integrable (fun s => Real.exp (-(s / 2))) ν :=
  Integrable.mono' hν (by fun_prop : Continuous fun s : ℝ => Real.exp (-(s / 2))).aestronglyMeasurable
    (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by have := neg_abs_le s; linarith))

/-- The deleted flux of a translation mixture is the mixture of translated deleted fluxes. -/
theorem thetaNormalizedFlux_thetaPrimeDeletion_thetaMeasureGauge {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaPrimeDeletion S (thetaMeasureGauge ν thetaCuspFullSource)) t =
      ∫ s, Real.exp (5 * s / 2) *
        thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t) ∂ν := by
  obtain ⟨C, hC⟩ := exists_abs_thetaCuspFullSource_le_const
  rw [thetaPrimeDeletion_thetaMeasureGauge continuous_thetaCuspFullSource hC,
    thetaNormalizedFlux_thetaMeasureGauge (integrable_exp_neg_half_of_abs hν)
      (continuous_thetaPrimeDeletion S continuous_thetaCuspFullSource) _ ht]
  exact (integrable_exp_mul_thetaPrimeDeletion S (fun p hp => (hS p hp).pos) (1 / 2)).congr
    (ae_of_all _ fun x => by simp only; ring_nf)

theorem integrable_shifted_deletedFlux {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun s => Real.exp (5 * s / 2) *
      thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t)) ν :=
  Integrable.mono' ((integrable_exp_neg_half_of_abs hν).mul_const _)
    (continuous_shifted_deletedFlux_in_shift hS ht).aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact shifted_deletedFlux_le hS s ht)

/-- **Positive mixtures pass every finite sieve.**  For a positive finite translation measure,
every finite-prime-deleted flux is completely monotone. -/
theorem completelyMonotoneOn_thetaPrimeDeletion_thetaMeasureGauge {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    CompletelyMonotoneOn (thetaNormalizedFlux
      (thetaPrimeDeletion S (thetaMeasureGauge ν thetaCuspFullSource))) := by
  have h := completelyMonotoneOn_integral (ν := ν)
    (G := fun s t => Real.exp (5 * s / 2) *
      thetaNormalizedFlux (thetaPrimeDeletion S thetaCuspFullSource) (Real.exp (2 * s) * t))
    (fun s => completelyMonotoneOn_shifted_deletedFlux hS s)
    (fun t ht => integrable_shifted_deletedFlux hν hS ht)
    (continuousOn_integral_shifted_deletedFlux (integrable_exp_neg_half_of_abs hν) hS)
  exact h.congr_Ioi fun t ht =>
    (thetaNormalizedFlux_thetaPrimeDeletion_thetaMeasureGauge hν hS ht).symm

/-! ## Cofinal deletion reads the seed flux -/

/-- The seed flux `2π ∫ e^{5s/2} e^{-π e^{2s} t} dν(s)`. -/
noncomputable def thetaSeedFlux (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ s, Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * (Real.exp (2 * s) * t))) ∂ν

theorem PrimeExhaustion.tendsto_deletedFlux {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) {u : ℝ}
    (hu : 0 < u) :
    Tendsto (fun j => thetaNormalizedFlux (thetaPrimeDeletion (S j) thetaCuspFullSource) u) atTop
      (𝓝 (2 * Real.pi * Real.exp (-Real.pi * u))) := by
  classical
  set w : ℕ → ℝ := fun m => 2 * Real.pi * (m : ℝ) ^ 2 * Real.exp (-Real.pi * (m : ℝ) ^ 2 * u)
  have hlim : (2 * Real.pi * Real.exp (-Real.pi * u)) =
      ∑' n : ℕ, if n = 1 then w n else 0 := by
    rw [tsum_eq_single 1 (fun n hn => if_neg hn), if_pos rfl]
    simp [w]
  rw [hlim]
  have heq : ∀ j, thetaNormalizedFlux (thetaPrimeDeletion (S j) thetaCuspFullSource) u =
      ∑' n, (thetaCoprimeLabels (S j)).indicator w n :=
    fun j => thetaNormalizedFlux_thetaPrimeDeletion_eq (hS.prime j) hu
  simp_rw [heq]
  refine tendsto_tsum_of_dominated_convergence (bound := w) (summable_thetaGaussFlux_atoms hu)
    (fun n => ?_) (Eventually.of_forall fun j n => ?_)
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · have h0 : ∀ j, (thetaCoprimeLabels (S j)).indicator w 0 = 0 := fun j => by
          rw [Set.indicator_apply]; split_ifs <;> simp [w]
        simp only [h0, show (0 : ℕ) ≠ 1 by norm_num, if_false]
        exact tendsto_const_nhds
      · have h1 : ∀ j, (1 : ℕ) ∈ thetaCoprimeLabels (S j) := fun j p hp hdiv =>
          (hS.prime j p hp).one_lt.ne' (Nat.dvd_one.mp hdiv)
        simp only [Set.indicator_of_mem (h1 _)]
        exact tendsto_const_nhds
    · rw [if_neg (by omega)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hS.eventually_not_coprime hn] with j hj
      rw [Set.indicator_of_notMem (show n ∉ thetaCoprimeLabels (S j) from hj)]
  · rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun m _ => by positivity) n)]
    exact Set.indicator_le_self' (fun m _ => by positivity) n

/-- **Cofinal seed limit.**  Along every exhaustion of the primes, the deleted fluxes of a
translation mixture converge to its seed flux. -/
theorem PrimeExhaustion.tendsto_flux_thetaMeasureGauge {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) {t : ℝ}
    (ht : 0 < t) :
    Tendsto (fun j => thetaNormalizedFlux
      (thetaPrimeDeletion (S j) (thetaMeasureGauge ν thetaCuspFullSource)) t) atTop
      (𝓝 (thetaSeedFlux ν t)) := by
  simp_rw [fun j => thetaNormalizedFlux_thetaPrimeDeletion_thetaMeasureGauge hν (hS.prime j) ht]
  refine tendsto_integral_of_dominated_convergence
    (fun s => Real.exp (-(s / 2)) * (t ^ (-(3 / 2 : ℝ)) / 2))
    (fun j => (continuous_shifted_deletedFlux_in_shift (hS.prime j) ht).aestronglyMeasurable)
    ((integrable_exp_neg_half_of_abs hν).mul_const _)
    (fun j => ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]; exact shifted_deletedFlux_le (hS.prime j) s ht)
    (ae_of_all _ fun s => ?_)
  exact (hS.tendsto_deletedFlux (mul_pos (Real.exp_pos _) ht)).const_mul _

/-! ## The signed seed measure is read by complete monotonicity -/

theorem integrable_prod_exp_half_comp_add {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (-(s / 2))) ν) {f : ℝ → ℝ} (hf : Continuous f)
    (hfi : Integrable (fun y => Real.exp (y / 2) * f y)) :
    Integrable (fun q : ℝ × ℝ => Real.exp (q.1 / 2) * f (q.1 + q.2)) (volume.prod ν) := by
  have hFc : Continuous fun q : ℝ × ℝ => Real.exp (q.1 / 2) * f (q.1 + q.2) := by fun_prop
  rw [integrable_prod_iff' hFc.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun s => ?_, ?_⟩
  · have h := (hfi.comp_add_right s).const_mul (Real.exp (-(s / 2)))
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  · exact (hν.mul_const (∫ y, ‖Real.exp (y / 2) * f y‖)).congr
      (ae_of_all _ fun s => (integral_norm_exp_half_comp_add f s).symm)

theorem thetaFluxSource_thetaMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (-(s / 2))) ν) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) (hfi : Integrable (fun y => Real.exp (y / 2) * f y)) :
    ThetaFluxSource (thetaMeasureGauge ν f) := by
  refine ⟨continuous_thetaMeasureGauge hf hC, fun X => ?_⟩
  have h := (integrable_prod_exp_half_comp_add hν hf hfi).integral_prod_left
  refine (h.congr (ae_of_all _ fun x => ?_)).integrableOn
  simp only [thetaMeasureGauge]
  rw [integral_const_mul]

theorem thetaPrimeDeletion_sub (S : Finset ℕ) (f g : ℝ → ℝ) :
    thetaPrimeDeletion S (fun x => f x - g x) =
      fun x => thetaPrimeDeletion S f x - thetaPrimeDeletion S g x := by
  funext x
  unfold thetaPrimeDeletion
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun T _ => by ring

theorem thetaNormalizedFlux_sub {f g : ℝ → ℝ} (hf : ThetaFluxSource f) (hg : ThetaFluxSource g)
    (t : ℝ) :
    thetaNormalizedFlux (fun x => f x - g x) t = thetaNormalizedFlux f t - thetaNormalizedFlux g t := by
  have h := thetaNormalizedFlux_add hf (hg.const_mul (-1)) t
  rw [thetaNormalizedFlux_const_mul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  rw [h]

theorem thetaFluxSource_deletedMeasureGauge {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (|s| / 2)) ν) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ThetaFluxSource (thetaPrimeDeletion S (thetaMeasureGauge ν thetaCuspFullSource)) := by
  obtain ⟨C, hC⟩ := exists_abs_thetaCuspFullSource_le_const
  rw [thetaPrimeDeletion_thetaMeasureGauge continuous_thetaCuspFullSource hC]
  exact thetaFluxSource_thetaMeasureGauge (integrable_exp_neg_half_of_abs hν)
    (continuous_thetaPrimeDeletion S continuous_thetaCuspFullSource)
    (abs_thetaPrimeDeletion_le hC S)
    ((integrable_exp_mul_thetaPrimeDeletion S (fun p hp => (hS p hp).pos) (1 / 2)).congr
      (ae_of_all _ fun x => by simp only; ring_nf))

theorem two_pi_exp_neg_le_flux {u : ℝ} (hu : 0 < u) :
    2 * Real.pi * Real.exp (-Real.pi * u) ≤ thetaNormalizedFlux thetaCuspFullSource u := by
  rw [thetaNormalizedFlux_thetaCuspFullSource hu]
  have h := le_hasSum (summable_thetaGaussFlux_atoms hu).hasSum 1 (fun n _ => by positivity)
  simpa using h

theorem seed_integrand_le (s : ℝ) {t : ℝ} (ht : 0 < t) :
    |Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * (Real.exp (2 * s) * t)))| ≤
      Real.exp (-(s / 2)) * (t ^ (-(3 / 2 : ℝ)) / 2) := by
  have hu : 0 < Real.exp (2 * s) * t := mul_pos (Real.exp_pos _) ht
  rw [abs_of_nonneg (by positivity)]
  refine le_trans ?_ (shifted_deletedFlux_le (S := ∅) (fun p hp => absurd hp (by simp)) s ht)
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
    (thetaNormalizedFlux_thetaPrimeDeletion_nonneg (S := ∅) (fun p hp => absurd hp (by simp)) hu))]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [thetaPrimeDeletion_empty]
  exact two_pi_exp_neg_le_flux hu

theorem continuousOn_thetaSeedFlux {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (-(s / 2))) ν) : ContinuousOn (thetaSeedFlux ν) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ / 2 := by have := mem_Ioi.mp ht₀; linarith
  have hloc : ContinuousOn (thetaSeedFlux ν) (Ioi (t₀ / 2)) := by
    refine continuousOn_of_dominated
      (bound := fun s => Real.exp (-(s / 2)) * ((t₀ / 2) ^ (-(3 / 2 : ℝ)) / 2))
      (fun t _ => by fun_prop) (fun t ht => ae_of_all _ fun s => ?_) (hν.mul_const _)
      (ae_of_all _ fun s => by fun_prop)
    rw [Real.norm_eq_abs]
    refine le_trans ?_ (seed_integrand_le s ht₀')
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (by positivity)) (Real.exp_pos _).le
    have : t₀ / 2 ≤ t := le_of_lt ht
    have h2 : 0 < Real.exp (2 * s) := Real.exp_pos _
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le h2.le) (sub_nonneg.mpr this)]
  exact (hloc.continuousAt (Ioi_mem_nhds (by have := mem_Ioi.mp ht₀; linarith))).continuousWithinAt

/-- The seed rate map `s ↦ π e^{2s}`. -/
noncomputable def thetaSeedRate (s : ℝ) : ℝ := Real.pi * Real.exp (2 * s)

theorem measurableEmbedding_thetaSeedRate : MeasurableEmbedding thetaSeedRate := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun r => Real.log (r / Real.pi) / 2)
    (by unfold thetaSeedRate; fun_prop) ?_ (by fun_prop) ?_
  · have hr : Set.range thetaSeedRate = Ioi 0 := by
      ext r
      constructor
      · rintro ⟨s, rfl⟩
        exact mem_Ioi.mpr (by unfold thetaSeedRate; positivity)
      · intro hr
        refine ⟨Real.log (r / Real.pi) / 2, ?_⟩
        unfold thetaSeedRate
        rw [show 2 * (Real.log (r / Real.pi) / 2) = Real.log (r / Real.pi) by ring,
          Real.exp_log (div_pos hr Real.pi_pos)]
        field_simp
    rw [hr]
    exact measurableSet_Ioi
  · intro s
    simp only [thetaSeedRate]
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
    ring

/-- The seed density `2π e^{5s/2} e^{-π e^{2s}}`. -/
noncomputable def thetaSeedDensity (s : ℝ) : ℝ :=
  2 * Real.pi * Real.exp (5 * s / 2) * Real.exp (-Real.pi * Real.exp (2 * s))

theorem thetaSeedDensity_pos (s : ℝ) : 0 < thetaSeedDensity s := by
  unfold thetaSeedDensity
  positivity

theorem thetaSeedDensity_le (s : ℝ) : thetaSeedDensity s ≤ Real.exp (-(s / 2)) / 2 := by
  have h := seed_integrand_le s one_pos
  rw [abs_of_nonneg (by positivity), Real.one_rpow, mul_one] at h
  unfold thetaSeedDensity
  linarith [show Real.exp (5 * s / 2) * (2 * Real.pi * Real.exp (-Real.pi * Real.exp (2 * s))) =
    2 * Real.pi * Real.exp (5 * s / 2) * Real.exp (-Real.pi * Real.exp (2 * s)) by ring,
    show Real.exp (-(s / 2)) * (1 / 2) = Real.exp (-(s / 2)) / 2 by ring]

theorem continuous_thetaSeedDensity : Continuous thetaSeedDensity := by
  unfold thetaSeedDensity
  fun_prop

/-- The seed rate measure: the push-forward of `thetaSeedDensity · ν` under `s ↦ π e^{2s}`. -/
noncomputable def thetaSeedRateMeasure (ν : Measure ℝ) : Measure ℝ :=
  (ν.withDensity fun s => ENNReal.ofReal (thetaSeedDensity s)).map thetaSeedRate

theorem isFiniteMeasure_thetaSeedRateMeasure {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : Integrable (fun s => Real.exp (-(s / 2))) ν) :
    IsFiniteMeasure (thetaSeedRateMeasure ν) := by
  have hfin : HasFiniteIntegral thetaSeedDensity ν :=
    (Integrable.mono' (hν.div_const 2) continuous_thetaSeedDensity.aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_of_pos (thetaSeedDensity_pos s)]
        exact thetaSeedDensity_le s)).hasFiniteIntegral
  haveI := isFiniteMeasure_withDensity_ofReal hfin
  unfold thetaSeedRateMeasure
  infer_instance

theorem thetaSeedRateMeasure_compl_Ici (ν : Measure ℝ) : thetaSeedRateMeasure ν (Ici 0)ᶜ = 0 := by
  unfold thetaSeedRateMeasure
  rw [measurableEmbedding_thetaSeedRate.map_apply]
  have : thetaSeedRate ⁻¹' (Ici 0)ᶜ = ∅ := by
    ext s
    simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le, mem_empty_iff_false, iff_false,
      not_lt]
    unfold thetaSeedRate
    positivity
  rw [this, measure_empty]

theorem integral_exp_neg_mul_thetaSeedRateMeasure {ν : Measure ℝ} {u : ℝ} :
    (∫ r, Real.exp (-u * r) ∂thetaSeedRateMeasure ν) = thetaSeedFlux ν (1 + u) := by
  unfold thetaSeedRateMeasure thetaSeedFlux
  rw [integral_map measurableEmbedding_thetaSeedRate.measurable.aemeasurable
    (by fun_prop : Continuous fun r : ℝ => Real.exp (-u * r)).aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable fun s => ENNReal.ofReal (thetaSeedDensity s) from
        ENNReal.measurable_ofReal.comp continuous_thetaSeedDensity.measurable)
      (ae_of_all _ fun s => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [smul_eq_mul, ENNReal.toReal_ofReal (thetaSeedDensity_pos s).le]
  unfold thetaSeedDensity thetaSeedRate
  have he : Real.exp (-Real.pi * Real.exp (2 * s)) * Real.exp (-u * (Real.pi * Real.exp (2 * s))) =
      Real.exp (-Real.pi * (Real.exp (2 * s) * (1 + u))) := by
    rw [← Real.exp_add]; ring_nf
  rw [mul_assoc (2 * Real.pi * Real.exp (5 * s / 2)), he]
  ring

/-- Pulling back an inequality of seed rate measures to the translation measures. -/
theorem le_of_thetaSeedRateMeasure_le {ν₁ ν₂ : Measure ℝ}
    (h : thetaSeedRateMeasure ν₂ ≤ thetaSeedRateMeasure ν₁) : ν₂ ≤ ν₁ := by
  set D : ℝ → ENNReal := fun s => ENNReal.ofReal (thetaSeedDensity s)
  have hD : Measurable D := ENNReal.measurable_ofReal.comp continuous_thetaSeedDensity.measurable
  have hwd : ν₂.withDensity D ≤ ν₁.withDensity D := by
    rw [Measure.le_iff]
    intro A hA
    have e := measurableEmbedding_thetaSeedRate
    have h1 := (Measure.le_iff.mp h) _ (e.measurableSet_image' hA)
    rw [thetaSeedRateMeasure, thetaSeedRateMeasure, e.map_apply, e.map_apply,
      e.injective.preimage_image] at h1
    exact h1
  have hrec : ∀ ν : Measure ℝ, (ν.withDensity D).withDensity (fun s => (D s)⁻¹) = ν := by
    intro ν
    rw [← withDensity_mul ν hD (show Measurable fun s => (D s)⁻¹ from hD.inv),
      show (D * fun s => (D s)⁻¹) = 1 from funext fun s =>
      ENNReal.mul_inv_cancel (by simp [D, thetaSeedDensity_pos s]) ENNReal.ofReal_ne_top,
      withDensity_one]
  rw [Measure.le_iff]
  intro A hA
  rw [← hrec ν₁, ← hrec ν₂, withDensity_apply _ hA, withDensity_apply _ hA]
  exact lintegral_mono' (Measure.restrict_mono subset_rfl hwd) le_rfl

/-- **Seed positivity.**  If the signed seed flux `b_{seed,ν₁} - b_{seed,ν₂}` is completely
monotone, then `ν₂ ≤ ν₁`. -/
theorem le_of_completelyMonotoneOn_thetaSeedFlux_sub {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (h₁ : Integrable (fun s => Real.exp (-(s / 2))) ν₁)
    (h₂ : Integrable (fun s => Real.exp (-(s / 2))) ν₂)
    (hCM : CompletelyMonotoneOn fun t => thetaSeedFlux ν₁ t - thetaSeedFlux ν₂ t) : ν₂ ≤ ν₁ := by
  haveI := isFiniteMeasure_thetaSeedRateMeasure h₁
  haveI := isFiniteMeasure_thetaSeedRateMeasure h₂
  apply le_of_thetaSeedRateMeasure_le
  refine le_of_completelyMonotoneOn_laplace_sub (thetaSeedRateMeasure_compl_Ici ν₁)
    (thetaSeedRateMeasure_compl_Ici ν₂) ?_
  refine (completelyMonotoneOn_comp_add_left hCM zero_le_one).congr_Ioi fun u _ => ?_
  simp only
  rw [integral_exp_neg_mul_thetaSeedRateMeasure, integral_exp_neg_mul_thetaSeedRateMeasure]

/-! ## The all-sieve classification -/

/-- The primes up to `j`. -/
def thetaPrimesUpTo (j : ℕ) : Finset ℕ := (Finset.range (j + 1)).filter Nat.Prime

theorem primeExhaustion_thetaPrimesUpTo : PrimeExhaustion thetaPrimesUpTo :=
  ⟨fun j p hp => (Finset.mem_filter.mp hp).2, fun p hp => Filter.eventually_atTop.mpr
    ⟨p, fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩⟩⟩

/-- The signed translation gauge `∫ k(x+s) d(ν₁ - ν₂)(s)`. -/
noncomputable def thetaSignedMeasureGauge (ν₁ ν₂ : Measure ℝ) (x : ℝ) : ℝ :=
  thetaMeasureGauge ν₁ thetaCuspFullSource x - thetaMeasureGauge ν₂ thetaCuspFullSource x

theorem thetaMeasureGauge_add_measure {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) (x : ℝ) :
    thetaMeasureGauge (ν₁ + ν₂) f x = thetaMeasureGauge ν₁ f x + thetaMeasureGauge ν₂ f x :=
  integral_add_measure (integrable_comp_add_of_bounded hf hC x)
    (integrable_comp_add_of_bounded hf hC x)

theorem thetaSignedMeasureGauge_of_le {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (h : ν₂ ≤ ν₁) :
    haveI : IsFiniteMeasure (ν₁ - ν₂) := isFiniteMeasure_of_le ν₁ Measure.sub_le
    thetaSignedMeasureGauge ν₁ ν₂ = thetaMeasureGauge (ν₁ - ν₂) thetaCuspFullSource := by
  haveI : IsFiniteMeasure (ν₁ - ν₂) := isFiniteMeasure_of_le ν₁ Measure.sub_le
  obtain ⟨C, hC⟩ := exists_abs_thetaCuspFullSource_le_const
  funext x
  unfold thetaSignedMeasureGauge
  conv_lhs => rw [← Measure.sub_add_cancel_of_le h]
  rw [thetaMeasureGauge_add_measure continuous_thetaCuspFullSource hC]
  ring

/-- **All-sieve theorem.**  For finite translation measures with `∫ e^{|s|/2} < ∞`, every
finite-prime-deleted flux of the signed gauge `∫ k(·+s) d(ν₁ - ν₂)(s)` is completely monotone
iff the signed translation measure `ν₁ - ν₂` is positive. -/
theorem allSieve_completelyMonotone_iff {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁]
    [IsFiniteMeasure ν₂] (h₁ : Integrable (fun s => Real.exp (|s| / 2)) ν₁)
    (h₂ : Integrable (fun s => Real.exp (|s| / 2)) ν₂) :
    (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      CompletelyMonotoneOn (thetaNormalizedFlux
        (thetaPrimeDeletion S (thetaSignedMeasureGauge ν₁ ν₂)))) ↔ ν₂ ≤ ν₁ := by
  constructor
  · intro hall
    have hS := primeExhaustion_thetaPrimesUpTo
    have hflux : ∀ j, ∀ t, 0 < t → thetaNormalizedFlux
        (thetaPrimeDeletion (thetaPrimesUpTo j) (thetaSignedMeasureGauge ν₁ ν₂)) t =
        thetaNormalizedFlux (thetaPrimeDeletion (thetaPrimesUpTo j)
          (thetaMeasureGauge ν₁ thetaCuspFullSource)) t -
        thetaNormalizedFlux (thetaPrimeDeletion (thetaPrimesUpTo j)
          (thetaMeasureGauge ν₂ thetaCuspFullSource)) t := by
      intro j t _
      unfold thetaSignedMeasureGauge
      rw [thetaPrimeDeletion_sub, thetaNormalizedFlux_sub
        (thetaFluxSource_deletedMeasureGauge h₁ (hS.prime j))
        (thetaFluxSource_deletedMeasureGauge h₂ (hS.prime j))]
    have hCM : CompletelyMonotoneOn fun t => thetaSeedFlux ν₁ t - thetaSeedFlux ν₂ t :=
      completelyMonotoneOn_of_tendsto (fun j => hall _ (hS.prime j))
        (fun t ht => by
          simp_rw [hflux _ t ht]
          exact (hS.tendsto_flux_thetaMeasureGauge h₁ ht).sub
            (hS.tendsto_flux_thetaMeasureGauge h₂ ht))
        ((continuousOn_thetaSeedFlux (integrable_exp_neg_half_of_abs h₁)).sub
          (continuousOn_thetaSeedFlux (integrable_exp_neg_half_of_abs h₂)))
    exact le_of_completelyMonotoneOn_thetaSeedFlux_sub (integrable_exp_neg_half_of_abs h₁)
      (integrable_exp_neg_half_of_abs h₂) hCM
  · intro h S hS
    haveI : IsFiniteMeasure (ν₁ - ν₂) := isFiniteMeasure_of_le ν₁ Measure.sub_le
    rw [thetaSignedMeasureGauge_of_le h]
    exact completelyMonotoneOn_thetaPrimeDeletion_thetaMeasureGauge
      (h₁.mono_measure Measure.sub_le) hS

end RHTower
