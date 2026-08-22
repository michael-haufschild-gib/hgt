import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.Basic
import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.Energy
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralHeatCauchySchwarz

/-!
# The heat equation for a spectral kernel, and Lemma 2.1 in kernel form

The spectral kernel `K(t,x,y) = Σₙ e^{−tλₙ} φₙ(x)\overline{φₙ(y)}` solves the heat equation: for
`t > 0`,

```text
∂ₜ K(t,x,y) = −(ΔK)(t,x,y) ,     (ΔK)(t,x,y) := Σₙ λₙ e^{−tλₙ} φₙ(x)\overline{φₙ(y)} ,
```

differentiation under the sum being legitimate because `λ e^{−t₀λ/2} ≤ 2/(e t₀)`.

The same object `ΔK` is what Lemma 2.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small
eigenvalues of the Laplacian* (arXiv:2509.06151v2), estimates; that estimate is recorded here in
kernel form, `|ΔK(t,x,y)| ≤ (4/e) t^{−1} K(t/2,x,x)^{1/2} K(t,y,y)^{1/2}`.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*}

/-- The Laplacian of the spectral heat kernel in the time variable. -/
noncomputable def spectralHeatKernelLaplacian (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) (t : ℝ) (x y : X) : ℂ :=
  ∑' n, ((lam n * Real.exp (-(t * lam n)) : ℝ) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y))

/-- **Lemma 2.1 of Dai–Yoshikawa, kernel form.**

`|ΔK(t,x,y)| ≤ (4/e) t^{−1} K(t/2,x,x)^{1/2} K(t,y,y)^{1/2}`. -/
theorem norm_spectralHeatKernelLaplacian_le (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) {t : ℝ} {x y : X}
    (ht : 0 < t) (hlam : ∀ n, 0 ≤ lam n)
    (hprod : Summable fun n => lam n * Real.exp (-(t * lam n)) * (‖φ n x‖ * ‖φ n y‖))
    (hx : Summable fun n => Real.exp (-(t / 2 * lam n)) * ‖φ n x‖ ^ 2)
    (hy : Summable fun n => Real.exp (-(t * lam n)) * ‖φ n y‖ ^ 2) :
    ‖spectralHeatKernelLaplacian lam φ t x y‖
      ≤ (4 * Real.exp (-1)) / t
          * (Real.sqrt (spectralHeatDiag lam φ (t / 2) x)
              * Real.sqrt (spectralHeatDiag lam φ t y)) := by
  have hterm : ∀ n, ‖((lam n * Real.exp (-(t * lam n)) : ℝ) : ℂ)
      * (φ n x * (starRingEnd ℂ) (φ n y))‖
      = lam n * Real.exp (-(t * lam n)) * (‖φ n x‖ * ‖φ n y‖) := by
    intro n
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hlam n), abs_of_nonneg (Real.exp_nonneg (-(t * lam n)))]
  have hsummableNorm : Summable fun n =>
      ‖((lam n * Real.exp (-(t * lam n)) : ℝ) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y))‖ :=
    hprod.congr fun n => (hterm n).symm
  refine le_trans (norm_tsum_le_tsum_norm hsummableNorm) ?_
  rw [tsum_congr hterm]
  exact DaiYoshikawa.tsum_eigenvalue_heat_mul_le ht hlam hx hy

/-- **The heat equation.**

For `t > t₀ > 0` the spectral heat kernel is differentiable in time with derivative `−ΔK`. -/
theorem hasDerivAt_spectralHeatKernel (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) {t₀ t : ℝ} {x y : X}
    (ht₀ : 0 < t₀) (ht : t₀ < t) (hlam : ∀ n, 0 ≤ lam n)
    (hdom : Summable fun n => Real.exp (-(t₀ / 2 * lam n)) * (‖φ n x‖ * ‖φ n y‖)) :
    HasDerivAt (fun s => spectralHeatKernel lam φ s x y)
      (-(spectralHeatKernelLaplacian lam φ t x y)) t := by
  set u : ℕ → ℝ := fun n =>
    2 / (Real.exp 1 * t₀) * (Real.exp (-(t₀ / 2 * lam n)) * (‖φ n x‖ * ‖φ n y‖)) with hu
  have hsu : Summable u := hdom.mul_left _
  have hg : ∀ (n : ℕ) (s : ℝ), s ∈ Ioi t₀ →
      HasDerivAt (fun z => (Real.exp (-(z * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y)))
        (-(((lam n * Real.exp (-(s * lam n)) : ℝ) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y)))) s := by
    intro n s _
    have h1 : HasDerivAt (fun z : ℝ => (-(lam n)) * z) (-(lam n)) s := by
      simpa using (hasDerivAt_id s).const_mul (-(lam n))
    have h2 : HasDerivAt (fun z : ℝ => Real.exp ((-(lam n)) * z))
        (Real.exp ((-(lam n)) * s) * (-(lam n))) s := h1.exp
    have h3 : HasDerivAt (fun z : ℝ => ((Real.exp ((-(lam n)) * z) : ℝ) : ℂ))
        (((Real.exp ((-(lam n)) * s) * (-(lam n)) : ℝ) : ℂ)) s :=
      h2.ofReal_comp
    have h4 := h3.mul_const (φ n x * (starRingEnd ℂ) (φ n y))
    have hfun : (fun z : ℝ => (Real.exp (-(z * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y)))
        = fun z : ℝ => ((Real.exp ((-(lam n)) * z) : ℝ) : ℂ)
            * (φ n x * (starRingEnd ℂ) (φ n y)) := by
      funext z
      congr 3
      ring
    rw [hfun]
    have hval : ((Real.exp ((-(lam n)) * s) * (-(lam n)) : ℝ) : ℂ)
          * (φ n x * (starRingEnd ℂ) (φ n y))
        = -(((lam n * Real.exp (-(s * lam n)) : ℝ) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y))) := by
      have hexp : Real.exp ((-(lam n)) * s) = Real.exp (-(s * lam n)) := by
        congr 1
        ring
      rw [hexp]
      push_cast
      ring
    rwa [hval] at h4
  have hg' : ∀ (n : ℕ) (s : ℝ), s ∈ Ioi t₀ →
      ‖-(((lam n * Real.exp (-(s * lam n)) : ℝ) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y)))‖
        ≤ u n := by
    intro n s hs
    have hs' : t₀ < s := hs
    have hnorm : ‖-(((lam n * Real.exp (-(s * lam n)) : ℝ) : ℂ)
        * (φ n x * (starRingEnd ℂ) (φ n y)))‖
        = lam n * Real.exp (-(s * lam n)) * (‖φ n x‖ * ‖φ n y‖) := by
      rw [norm_neg]
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hlam n), abs_of_nonneg (Real.exp_nonneg (-(s * lam n)))]
    rw [hnorm, hu]
    have hmono : Real.exp (-(s * lam n)) ≤ Real.exp (-(t₀ * lam n)) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hlam n, ht₀, hs']
    have hsplit : Real.exp (-(t₀ * lam n))
        = Real.exp (-(t₀ / 2 * lam n)) * Real.exp (-(t₀ / 2 * lam n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hkey : lam n * Real.exp (-(t₀ / 2 * lam n)) ≤ 2 / (Real.exp 1 * t₀) := by
      have h := mul_exp_neg_le_inv (t₀ := t₀ / 2) (by linarith) (hlam n)
      refine h.trans (le_of_eq ?_)
      field_simp
    have hstep : lam n * Real.exp (-(s * lam n)) ≤ 2 / (Real.exp 1 * t₀)
        * Real.exp (-(t₀ / 2 * lam n)) := by
      calc lam n * Real.exp (-(s * lam n))
          ≤ lam n * Real.exp (-(t₀ * lam n)) := mul_le_mul_of_nonneg_left hmono (hlam n)
        _ = (lam n * Real.exp (-(t₀ / 2 * lam n))) * Real.exp (-(t₀ / 2 * lam n)) := by
            rw [hsplit]; ring
        _ ≤ (2 / (Real.exp 1 * t₀)) * Real.exp (-(t₀ / 2 * lam n)) :=
            mul_le_mul_of_nonneg_right hkey (Real.exp_nonneg _)
    have hnn : (0 : ℝ) ≤ ‖φ n x‖ * ‖φ n y‖ := by positivity
    calc lam n * Real.exp (-(s * lam n)) * (‖φ n x‖ * ‖φ n y‖)
        ≤ (2 / (Real.exp 1 * t₀) * Real.exp (-(t₀ / 2 * lam n))) * (‖φ n x‖ * ‖φ n y‖) :=
          mul_le_mul_of_nonneg_right hstep hnn
      _ = 2 / (Real.exp 1 * t₀) * (Real.exp (-(t₀ / 2 * lam n)) * (‖φ n x‖ * ‖φ n y‖)) := by
          ring
  have hy₀ : (t₀ + (t - t₀) / 2) ∈ Ioi t₀ := by
    simp only [Set.mem_Ioi]
    linarith
  have hg0 : Summable fun n =>
      (Real.exp (-((t₀ + (t - t₀) / 2) * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n y)) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hdom
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hlam n, ht₀, ht]
  have hmain := hasDerivAt_tsum_of_isPreconnected hsu isOpen_Ioi isPreconnected_Ioi hg hg'
    hy₀ hg0 (Set.mem_Ioi.mpr ht)
  have hneg : (∑' n, -(((lam n * Real.exp (-(t * lam n)) : ℝ) : ℂ)
      * (φ n x * (starRingEnd ℂ) (φ n y))))
      = -(spectralHeatKernelLaplacian lam φ t x y) := by
    rw [spectralHeatKernelLaplacian, ← tsum_neg]
  rwa [hneg] at hmain

end GaloisForLFunctions.HTGeometry
