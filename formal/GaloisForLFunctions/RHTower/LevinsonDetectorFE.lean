import GaloisForLFunctions.RHTower.ReflectionCocycleArchimedean

/-!
# The functional equation of Levinson's detector

Levinson's method replaces Hardy's `Z` by the deformed detector `G = ζ + λζ'`.  What makes it a
detector is an exact functional equation: in the open critical strip

```text
Y(s)·Λ(s) = Γ_ℝ(s)·G(s) + Γ_ℝ(1−s)·G(1−s),
Y(s) = 2 − λ·(Γ_ℝ'/Γ_ℝ)(s) − λ·(Γ_ℝ'/Γ_ℝ)(1−s),
```

where `Λ = Γ_ℝ·ζ` is the completed zeta.  The proof is the product rule for `Λ = Γ_ℝ·ζ` at `s` and at
`1−s`, together with the oddness of `Λ'` under `s ↦ 1−s`.  At `λ = 0` this degenerates to
`2Λ(s) = Γ_ℝ(s)ζ(s) + Γ_ℝ(1−s)ζ(1−s)`, the identity behind Hardy's `Z`; `λ ≠ 0` is Levinson's
deformation, and `Y(½+it) = 2 + 1/r + o(1)` for `λ = −1/(r log T)` is what keeps the detector
faithful.
-/

open Complex


noncomputable section

namespace RHTower

/-- Levinson's detector: the linear combination `ζ + λ ζ'`. -/
def levinsonG (lam : ℂ) (s : ℂ) : ℂ := riemannZeta s + lam * deriv riemannZeta s

/-- The archimedean weight of the detector's functional equation. -/
def levinsonY (lam : ℂ) (s : ℂ) : ℂ :=
  2 - lam * logDeriv Complex.Gammaℝ s - lam * logDeriv Complex.Gammaℝ (1 - s)

theorem completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  rw [riemannZeta_def_of_ne_zero hs0, mul_div_cancel₀]
  exact Complex.Gammaℝ_ne_zero_of_re_pos hs

/-- The completed zeta derivative is odd under the functional equation. -/
theorem deriv_completedRiemannZeta_one_sub (s : ℂ) :
    deriv completedRiemannZeta (1 - s) = -deriv completedRiemannZeta s := by
  have hfun : (fun z : ℂ => completedRiemannZeta (1 - z)) = completedRiemannZeta :=
    funext completedRiemannZeta_one_sub
  have hinner : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := (hasDerivAt_id s).const_sub 1
  by_cases hdiff : DifferentiableAt ℂ completedRiemannZeta (1 - s)
  · have hcomp : HasDerivAt (fun z : ℂ => completedRiemannZeta (1 - z))
        (deriv completedRiemannZeta (1 - s) * (-1)) s :=
      hdiff.hasDerivAt.comp s hinner
    rw [hfun] at hcomp
    have hd := hcomp.deriv
    rw [hd]
    ring
  · have hdiff' : ¬ DifferentiableAt ℂ completedRiemannZeta s := by
      intro hd
      refine hdiff ?_
      have hcomp : DifferentiableAt ℂ (fun z : ℂ => completedRiemannZeta (1 - z)) (1 - s) := by
        have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) (1 - s) :=
          (hasDerivAt_id (1 - s)).const_sub 1
        have h2 : (1 : ℂ) - (1 - s) = s := by ring
        rw [← h2] at hd
        exact (hd.hasDerivAt.comp (1 - s) h1).differentiableAt
      rw [hfun] at hcomp
      exact hcomp
    rw [deriv_zero_of_not_differentiableAt hdiff, deriv_zero_of_not_differentiableAt hdiff']
    ring

theorem hasDerivAt_completedRiemannZeta_of_strip {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    HasDerivAt completedRiemannZeta
      (deriv Complex.Gammaℝ s * riemannZeta s
        + Complex.Gammaℝ s * deriv riemannZeta s) s := by
  have hG := hasDerivAt_Gammaℝ_of_re_pos hs
  have hZ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hprod : HasDerivAt (fun z : ℂ => Complex.Gammaℝ z * riemannZeta z)
      (deriv Complex.Gammaℝ s * riemannZeta s
        + Complex.Gammaℝ s * deriv riemannZeta s) s := by
    have h := hG.mul hZ
    have hgd : deriv Complex.Gammaℝ s
        = Complex.Gammaℝ s * ((s / 2).digamma / 2 - (Real.log Real.pi : ℂ) / 2) := hG.deriv
    rw [hgd]
    exact h
  refine hprod.congr_of_eventuallyEq ?_
  have hopen : {z : ℂ | 0 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hopen] with z hz
  exact completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE hz

/-- **The functional equation of Levinson's detector.**  In the open critical strip

```text
Y(s)·Λ(s) = Γ_ℝ(s)·G(s) + Γ_ℝ(1−s)·G(1−s),
```

where `G = ζ + λζ'` and `Y(s) = 2 − λ·(Γ_ℝ'/Γ_ℝ)(s) − λ·(Γ_ℝ'/Γ_ℝ)(1−s)`.  The proof is the product
rule applied to `Λ = Γ_ℝ·ζ` at `s` and at `1−s`, together with the oddness of `Λ'` under the
functional equation. -/
theorem levinsonY_mul_completedRiemannZeta (lam : ℂ) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    levinsonY lam s * completedRiemannZeta s
      = Complex.Gammaℝ s * levinsonG lam s
        + Complex.Gammaℝ (1 - s) * levinsonG lam (1 - s) := by
  have h0' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hs1' : (1 - s) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re] at hre
    have hzero : s.re = 0 := by linarith
    rw [hzero] at h0
    exact lt_irrefl 0 h0
  have hGs : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hGs' : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0'
  have hΛs : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s :=
    completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE h0
  have hΛs' : completedRiemannZeta (1 - s) = Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) :=
    completedRiemannZeta_eq_Gammaℝ_mul_levinsonDetectorFE h0'
  have hFE : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  have hd : deriv completedRiemannZeta s
      = deriv Complex.Gammaℝ s * riemannZeta s + Complex.Gammaℝ s * deriv riemannZeta s :=
    (hasDerivAt_completedRiemannZeta_of_strip h0 hs1).deriv
  have hd' : deriv completedRiemannZeta (1 - s)
      = deriv Complex.Gammaℝ (1 - s) * riemannZeta (1 - s)
        + Complex.Gammaℝ (1 - s) * deriv riemannZeta (1 - s) :=
    (hasDerivAt_completedRiemannZeta_of_strip h0' hs1').deriv
  have hodd : deriv completedRiemannZeta (1 - s) = -deriv completedRiemannZeta s :=
    deriv_completedRiemannZeta_one_sub s
  have hLDs : deriv Complex.Gammaℝ s = logDeriv Complex.Gammaℝ s * Complex.Gammaℝ s := by
    rw [logDeriv_apply, div_mul_cancel₀ _ hGs]
  have hLDs' : deriv Complex.Gammaℝ (1 - s)
      = logDeriv Complex.Gammaℝ (1 - s) * Complex.Gammaℝ (1 - s) := by
    rw [logDeriv_apply, div_mul_cancel₀ _ hGs']
  have e1 : Complex.Gammaℝ s * deriv riemannZeta s
      = deriv completedRiemannZeta s
        - logDeriv Complex.Gammaℝ s * completedRiemannZeta s := by
    rw [hd, hLDs, hΛs]; ring
  have e2 : Complex.Gammaℝ (1 - s) * deriv riemannZeta (1 - s)
      = deriv completedRiemannZeta (1 - s)
        - logDeriv Complex.Gammaℝ (1 - s) * completedRiemannZeta (1 - s) := by
    rw [hd', hLDs', hΛs']; ring
  have key : Complex.Gammaℝ s * levinsonG lam s
      + Complex.Gammaℝ (1 - s) * levinsonG lam (1 - s)
      = 2 * completedRiemannZeta s
        - lam * (logDeriv Complex.Gammaℝ s + logDeriv Complex.Gammaℝ (1 - s))
          * completedRiemannZeta s := by
    rw [levinsonG, levinsonG]
    have expand : Complex.Gammaℝ s * (riemannZeta s + lam * deriv riemannZeta s)
        + Complex.Gammaℝ (1 - s) * (riemannZeta (1 - s) + lam * deriv riemannZeta (1 - s))
        = (Complex.Gammaℝ s * riemannZeta s)
          + lam * (Complex.Gammaℝ s * deriv riemannZeta s)
          + (Complex.Gammaℝ (1 - s) * riemannZeta (1 - s))
          + lam * (Complex.Gammaℝ (1 - s) * deriv riemannZeta (1 - s)) := by ring
    rw [expand, e1, e2, ← hΛs, ← hΛs', hFE, hodd]
    ring
  rw [key, levinsonY]
  ring

end RHTower

end
