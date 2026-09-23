import GaloisForLFunctions.RHTower.LevinsonDetectorPolar
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding

/-!
# The entire form of Levinson's detector

`ζ` has a simple pole and `ζ'` a double pole at `s = 1`, so `G = ζ + λζ'` becomes entire after
multiplication by `(s-1)^(2 : ℕ)`.  The resulting entire function

```text
G♯(s) = (s-1)·zetaEntire(s) + λ·((s-1)·zetaEntire'(s) - zetaEntire(s))
```

agrees with `(s-1)^(2 : ℕ)·G(s)` away from the pole, has the same zeros there, and its logarithmic
derivative differs from that of `G` by the explicit rational term `2/(s-1)`.  This is the form the
rectangle argument principle consumes.
-/

open Complex Set

noncomputable section

namespace RHTower

/-- The entire function agreeing with `(s-1)^(2 : ℕ)·(ζ + λζ')` away from the pole. -/
def levinsonGEntire (lam : ℂ) (s : ℂ) : ℂ :=
  (s - 1) * zetaEntire s + lam * ((s - 1) * deriv zetaEntire s - zetaEntire s)

theorem differentiable_deriv_zetaEntire : Differentiable ℂ (deriv zetaEntire) := by
  have h : AnalyticOnNhd ℂ zetaEntire Set.univ :=
    differentiable_zetaEntire.differentiableOn.analyticOnNhd isOpen_univ
  intro s
  exact (h.deriv s (Set.mem_univ s)).differentiableAt

theorem differentiable_levinsonGEntire (lam : ℂ) :
    Differentiable ℂ (levinsonGEntire lam) := by
  intro s
  refine DifferentiableAt.add ?_ ?_
  · exact ((differentiableAt_id).sub_const 1).mul (differentiable_zetaEntire s)
  · refine DifferentiableAt.mul (differentiableAt_const _)
      (DifferentiableAt.sub ?_ (differentiable_zetaEntire s))
    exact ((differentiableAt_id).sub_const 1).mul (differentiable_deriv_zetaEntire s)

theorem analyticOnNhd_levinsonGEntire (lam : ℂ) :
    AnalyticOnNhd ℂ (levinsonGEntire lam) Set.univ :=
  (differentiable_levinsonGEntire lam).differentiableOn.analyticOnNhd isOpen_univ

/-- Away from the pole the derivative of the entire multiple splits by the product rule. -/
theorem deriv_zetaEntire_eq {s : ℂ} (hs : s ≠ 1) :
    deriv zetaEntire s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have hev : zetaEntire =ᶠ[nhds s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz using zetaEntire_eq hz
  have hzd : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul hzd
  rw [hev.deriv_eq, hd.deriv, one_mul]

theorem levinsonGEntire_eq (lam : ℂ) {s : ℂ} (hs : s ≠ 1) :
    levinsonGEntire lam s = (s - 1) ^ (2 : ℕ) * levinsonG lam s := by
  rw [levinsonGEntire, deriv_zetaEntire_eq hs, zetaEntire_eq hs, levinsonG]
  ring

theorem levinsonGEntire_eq_zero_iff (lam : ℂ) {s : ℂ} (hs : s ≠ 1) :
    levinsonGEntire lam s = 0 ↔ levinsonG lam s = 0 := by
  rw [levinsonGEntire_eq lam hs, mul_eq_zero]
  have h : (s - 1) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hs)
  simp [h]

/-- The value at the pole is `-λ`; in particular the entire detector is not identically zero. -/
theorem levinsonGEntire_one (lam : ℂ) : levinsonGEntire lam 1 = -lam := by
  have hz : zetaEntire 1 = 1 := by
    rw [zetaEntire]
    simp [Complex.Gammaℝ_one]
  rw [levinsonGEntire, hz]
  ring

theorem exists_levinsonGEntire_ne_zero {lam : ℂ} (hlam : lam ≠ 0) :
    ∃ z : ℂ, levinsonGEntire lam z ≠ 0 :=
  ⟨1, by rw [levinsonGEntire_one]; simpa using hlam⟩

/-- The logarithmic derivative of the entire detector differs from that of `G` by `2/(s-1)`. -/
theorem logDeriv_levinsonGEntire (lam : ℂ) {s : ℂ} (hs : s ≠ 1)
    (hG : levinsonG lam s ≠ 0) :
    logDeriv (levinsonGEntire lam) s = 2 / (s - 1) + logDeriv (levinsonG lam) s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hev : levinsonGEntire lam =ᶠ[nhds s] fun z => (z - 1) ^ (2 : ℕ) * levinsonG lam z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz using levinsonGEntire_eq lam hz
  have hcong : logDeriv (levinsonGEntire lam) s
      = logDeriv (fun z => (z - 1) ^ (2 : ℕ) * levinsonG lam z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hpow : ((s : ℂ) - 1) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hs1
  have hdpow : DifferentiableAt ℂ (fun z : ℂ => (z - 1) ^ (2 : ℕ)) s :=
    (((differentiableAt_id).sub_const 1).pow 2)
  have hdG : DifferentiableAt ℂ (levinsonG lam) s :=
    (analyticAt_levinsonG lam hs).differentiableAt
  have hlogpow : logDeriv (fun z : ℂ => (z - 1) ^ (2 : ℕ)) s = 2 / (s - 1) := by
    have hd : HasDerivAt (fun z : ℂ => (z - 1) ^ (2 : ℕ)) (2 * (s - 1)) s := by
      have h : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
      refine (h.pow 2).congr_deriv ?_
      push_cast
      ring
    rw [logDeriv_apply, hd.deriv]
    field_simp
    try ring
  rw [hcong, logDeriv_mul s hpow hG hdpow hdG, hlogpow]

end RHTower

end
