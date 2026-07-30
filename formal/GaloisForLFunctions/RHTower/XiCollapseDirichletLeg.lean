import GaloisForLFunctions.RHTower.XiHypertranscendenceChain

/-!
# The Dirichlet leg of the ξ jet decomposition: von Mangoldt jets

On the half-plane of absolute convergence every jet of `ζ'/ζ` is a von Mangoldt Dirichlet
series: `(d/ds)^j (ζ'/ζ)(s) = (−1)^{j+1}·Σ_n Λ(n)·(log n)^j·n^{−s}`.  This identifies the
`z`-leg of the weld split `ξ'/ξ = (rational) + ½ψ(s/2) + ζ'/ζ` as the prime-supported
frequency side of the Dirichlet frequency collapse: the frequencies are `log n` with von
Mangoldt weights, the polynomial-in-`log` coefficients are the `logMul` iterates — the
exact data the minimal-frequency estimate and the prime-power Vandermonde extraction
consume.

* `abscissaOfAbsConv_vonMangoldt_le` — the abscissa of `Λ` is at most `1`.
* `zetaLogDeriv_eventuallyEq_neg_LSeries` — `ζ'/ζ = −L(Λ)` locally on the half-plane.
* `iteratedDeriv_zetaLogDeriv_eq_LSeries` — **the von Mangoldt jet identity**.
-/

noncomputable section

namespace RHTower

open Complex Filter LSeries ArithmeticFunction
open scoped LSeries.notation

theorem abscissaOfAbsConv_vonMangoldt_le :
    abscissaOfAbsConv ↗Λ ≤ 1 := by
  apply abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact LSeriesSummable_vonMangoldt (by simpa using hy)

/-- The logarithmic derivative of `ζ` is the negated von Mangoldt L-series, locally on the
half-plane of absolute convergence. -/
theorem zetaLogDeriv_eventuallyEq_neg_LSeries {s : ℂ} (hs : 1 < s.re) :
    zetaLogDeriv =ᶠ[nhds s] fun w => -(LSeries ↗Λ w) := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  have h := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw
  rw [zetaLogDeriv]
  rw [h]
  ring

/-- **The von Mangoldt jet identity**: on the half-plane of absolute convergence,
`(d/ds)^j (ζ'/ζ)(s) = (−1)^{j+1}·L((log·)^{[j]} Λ)(s)` — every jet of the Dirichlet leg is
an absolutely convergent prime-supported Dirichlet series with polynomial-in-`log`
weights. -/
theorem iteratedDeriv_zetaLogDeriv_eq_LSeries (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv j zetaLogDeriv s
      = (-1) ^ (j + 1) * LSeries (LSeries.logMul^[j] ↗Λ) s := by
  have habs : abscissaOfAbsConv ↗Λ < s.re :=
    lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  rw [(zetaLogDeriv_eventuallyEq_neg_LSeries hs).iteratedDeriv_eq j]
  have hneg : iteratedDeriv j (fun w => -(LSeries ↗Λ w)) s
      = -(iteratedDeriv j (LSeries ↗Λ) s) := by
    rw [show (fun w => -(LSeries ↗Λ w)) = fun w => (-1 : ℂ) * LSeries ↗Λ w from by
      funext w
      ring]
    rw [iteratedDeriv_const_mul_field]
    ring
  rw [hneg, LSeries_iteratedDeriv j habs]
  ring

/-! ## The half-argument digamma leg -/

/-- Chain rule for the half-argument digamma jets:
`(d/ds)^j ψ(s/2) = (1/2)^j·ψ⁽ʲ⁾(s/2)` off the poles. -/
theorem iteratedDeriv_half_digamma (j : ℕ) :
    ∀ s : ℂ, (∀ p : ℕ, s / 2 ≠ -(p : ℂ)) →
      iteratedDeriv j (fun w => Complex.digamma (w / 2)) s
        = (1 / 2 : ℂ) ^ j * iteratedDeriv j Complex.digamma (s / 2) := by
  have hψ : (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma := by
    funext w
    rw [Complex.digamma_def, logDeriv_apply]
  have hΩ : IsOpen {z : ℂ | ∀ p : ℕ, z / 2 ≠ -(p : ℂ)} := by
    have hpre : {z : ℂ | ∀ p : ℕ, z / 2 ≠ -(p : ℂ)}
        = (fun z : ℂ => z / 2) ⁻¹' {w : ℂ | ∀ p : ℕ, w ≠ -(p : ℂ)} := rfl
    rw [hpre]
    exact (GaloisForLFunctions.offPoles_isOpen).preimage (continuous_id.div_const 2)
  induction j with
  | zero =>
      intro s _
      simp
  | succ j ih =>
      intro s hs
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun w => Complex.digamma (w / 2))
          =ᶠ[nhds s] fun w => (1 / 2 : ℂ) ^ j
            * iteratedDeriv j Complex.digamma (w / 2) := by
        filter_upwards [hΩ.mem_nhds hs] with w hw
        exact ih w hw
      rw [hev.deriv_eq]
      have h1 : AnalyticAt ℂ (iteratedDeriv j Complex.digamma) (s / 2) := by
        rw [← hψ]
        exact GaloisForLFunctions.analyticAt_iteratedDeriv_logDeriv j _ hs
      have hjet : HasDerivAt (fun w : ℂ => iteratedDeriv j Complex.digamma (w / 2))
          (deriv (iteratedDeriv j Complex.digamma) (s / 2) * (1 / 2)) s := by
        have hg : HasDerivAt (iteratedDeriv j Complex.digamma)
            (deriv (iteratedDeriv j Complex.digamma) (s / 2)) (s / 2) :=
          h1.differentiableAt.hasDerivAt
        have hf : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := by
          simpa using (hasDerivAt_id s).div_const 2
        simpa using! hg.comp s hf
      have hmul : HasDerivAt (fun w : ℂ => (1 / 2 : ℂ) ^ j
            * iteratedDeriv j Complex.digamma (w / 2))
          ((1 / 2 : ℂ) ^ j * (deriv (iteratedDeriv j Complex.digamma) (s / 2) * (1 / 2)))
          s := hjet.const_mul _
      rw [hmul.deriv, ← iteratedDeriv_succ]
      ring

/-! ## The full jet decomposition -/

/-- **The jet decomposition of `ξ'/ξ`** on the half-plane of absolute convergence: every
jet splits into the rational leg, the half-argument digamma leg with the chain-rule factor
`(1/2)^{j+1}`, and the von Mangoldt Dirichlet leg — the exact input of the Dirichlet
frequency collapse. -/
theorem iteratedDeriv_xiLogDeriv_split (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv j xiLogDeriv s
      = iteratedDeriv j
          (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) s
        + (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma (s / 2)
        + (-1) ^ (j + 1) * LSeries (LSeries.logMul^[j] ↗Λ) s := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have h1 : s ≠ 1 := fun h => by simp [h] at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpoles : ∀ p : ℕ, s / 2 ≠ -(p : ℂ) := by
    intro p hEq
    have hre := congrArg Complex.re hEq
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  -- analyticity of the three legs
  have hr_an : AnalyticAt ℂ
      (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2) s := by
    refine AnalyticAt.sub ?_ analyticAt_const
    exact (analyticAt_const.div analyticAt_id h0).add
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs1)
  have ha_an : AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) * Complex.digamma (w / 2)) s := by
    have hψ : (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma := by
      funext w
      rw [Complex.digamma_def, logDeriv_apply]
    have hdg : AnalyticAt ℂ Complex.digamma (s / 2) := by
      have := GaloisForLFunctions.analyticAt_iteratedDeriv_logDeriv 0 _ hpoles
      rw [hψ] at this
      simpa [iteratedDeriv_zero] using this
    have hhalf : AnalyticAt ℂ (fun w : ℂ => w / 2) s :=
      analyticAt_id.div analyticAt_const (by norm_num)
    have hcomp := AnalyticAt.comp (f := fun w : ℂ => w / 2) (x := s) hdg hhalf
    exact analyticAt_const.mul (by simpa [Function.comp] using! hcomp)
  have hζan : AnalyticAt ℂ riemannZeta s := by
    have hopen : IsOpen {w : ℂ | w ≠ 1} := isOpen_ne
    have hdiff : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun w hw =>
      (differentiableAt_riemannZeta hw).differentiableWithinAt
    exact (hdiff.analyticOnNhd hopen) s h1
  have hz_an : AnalyticAt ℂ zetaLogDeriv s := by
    have hdiv := (hζan.deriv).div hζan hζ
    exact hdiv
  -- split along the weld and separate the jets
  rw [(xiLogDeriv_eventuallyEq_split hs).iteratedDeriv_eq j]
  have hgroup : (fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2
        + (1 / 2) * Complex.digamma (w / 2) + zetaLogDeriv w)
      = (((fun w : ℂ => 1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2)
          + fun w : ℂ => (1 / 2 : ℂ) * Complex.digamma (w / 2))
        + fun w => zetaLogDeriv w) := rfl
  rw [hgroup]
  rw [iteratedDeriv_add (hr_an.add ha_an).contDiffAt hz_an.contDiffAt,
    iteratedDeriv_add hr_an.contDiffAt ha_an.contDiffAt]
  have haleg : iteratedDeriv j (fun w : ℂ => (1 / 2 : ℂ) * Complex.digamma (w / 2)) s
      = (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma (s / 2) := by
    rw [show (fun w : ℂ => (1 / 2 : ℂ) * Complex.digamma (w / 2))
        = fun w : ℂ => (1 / 2 : ℂ) * (fun v : ℂ => Complex.digamma (v / 2)) w from rfl]
    rw [GaloisForLFunctions.iteratedDeriv_const_mul_field]
    show (1 / 2 : ℂ) * iteratedDeriv j (fun v : ℂ => Complex.digamma (v / 2)) s
      = (1 / 2 : ℂ) ^ (j + 1) * iteratedDeriv j Complex.digamma (s / 2)
    rw [iteratedDeriv_half_digamma j s hpoles]
    ring
  have hzleg : iteratedDeriv j (fun w => zetaLogDeriv w) s
      = (-1) ^ (j + 1) * LSeries (LSeries.logMul^[j] ↗Λ) s :=
    iteratedDeriv_zetaLogDeriv_eq_LSeries j hs
  rw [haleg, hzleg]

end RHTower

end
