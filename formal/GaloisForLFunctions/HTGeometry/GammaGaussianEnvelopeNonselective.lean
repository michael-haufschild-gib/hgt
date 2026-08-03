import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeDecay
import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeDivisor

/-!
# The envelope is nonselective: off-critical quartets survive it

The reflection quartet of an off-critical point,

```text
Q_ρ(s) = (s - ρ)(s - (1-ρ))(s - ρ̄)(s - (1 - ρ̄)),
```

is a reflection-symmetric datum of polynomial vertical growth: `Q_ρ(1-s) = Q_ρ(s)`.  Enveloping it
keeps it moderate, makes it cosine-Fourier self-dual in the exact sense

```text
χ(s) · (A Q_ρ)(1-s) = (A Q_ρ)(s),
```

and preserves its divisor: the enveloped datum has a simple zero at `ρ` and vanishes in the right
half-plane exactly on the quartet.

So the whole package — moderate datum, self-dual completion, faithful divisor — is realized by data
whose zeros lie arbitrarily far off the critical line.  Existence of such a completion therefore
cannot select the critical line; whatever does must be a positivity, not a completion.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- The reflection quartet of a point: its zeros are `ρ`, `1-ρ`, `ρ̄`, `1-ρ̄`. -/
def reflectionQuartet (ρ : ℂ) (s : ℂ) : ℂ :=
  (s - ρ) * (s - (1 - ρ)) * (s - (starRingEnd ℂ) ρ) * (s - (1 - (starRingEnd ℂ) ρ))

/-- The quartet is invariant under the Riemann reflection. -/
theorem reflectionQuartet_one_sub (ρ s : ℂ) :
    reflectionQuartet ρ (1 - s) = reflectionQuartet ρ s := by
  rw [reflectionQuartet, reflectionQuartet]
  ring

/-- The quartet vanishes exactly on its four points. -/
theorem reflectionQuartet_eq_zero_iff (ρ s : ℂ) :
    reflectionQuartet ρ s = 0 ↔
      s = ρ ∨ s = 1 - ρ ∨ s = (starRingEnd ℂ) ρ ∨ s = 1 - (starRingEnd ℂ) ρ := by
  rw [reflectionQuartet, mul_eq_zero, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero,
    sub_eq_zero, sub_eq_zero]
  tauto

/-- The quartet is analytic. -/
theorem analyticAt_reflectionQuartet (ρ s : ℂ) : AnalyticAt ℂ (reflectionQuartet ρ) s := by
  unfold reflectionQuartet
  fun_prop

/-- The quartet has polynomial vertical growth. -/
theorem hasStripPolyGrowth_reflectionQuartet (ρ : ℂ) :
    HasStripPolyGrowth (reflectionQuartet ρ) := by
  have h := ((((hasStripPolyGrowth_sub_const ρ).mul
    (hasStripPolyGrowth_sub_const (1 - ρ))).mul
    (hasStripPolyGrowth_sub_const ((starRingEnd ℂ) ρ))).mul
    (hasStripPolyGrowth_sub_const (1 - (starRingEnd ℂ) ρ)))
  exact h

/-! ## The divisor at the off-critical point -/

/-- Away from the critical line and the real axis the four points are distinct, so the quartet has a
simple zero at `ρ`. -/
theorem meromorphicOrderAt_reflectionQuartet {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    meromorphicOrderAt (reflectionQuartet ρ) ρ = 1 := by
  set g : ℂ → ℂ := fun s =>
    (s - (1 - ρ)) * (s - (starRingEnd ℂ) ρ) * (s - (1 - (starRingEnd ℂ) ρ)) with hg
  have hfact : reflectionQuartet ρ = (fun s => (s - ρ)) * g := by
    funext s
    rw [reflectionQuartet, hg]
    simp only [Pi.mul_apply]
    ring
  have hne1 : ρ - (1 - ρ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    apply hre
    linarith
  have hne2 : ρ - (starRingEnd ℂ) ρ ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
    apply him
    linarith
  have hne3 : ρ - (1 - (starRingEnd ℂ) ρ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at hr
    apply hre
    linarith
  have hgne : g ρ ≠ 0 := by
    rw [hg]
    exact mul_ne_zero (mul_ne_zero hne1 hne2) hne3
  have hganalytic : AnalyticAt ℂ g ρ := by
    rw [hg]
    fun_prop
  have hgorder : meromorphicOrderAt g ρ = 0 := by
    rw [hganalytic.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hgne)]
    simp
  rw [hfact, meromorphicOrderAt_mul (by fun_prop : MeromorphicAt (fun s : ℂ => s - ρ) ρ)
    hganalytic.meromorphicAt, hgorder, add_zero]
  exact meromorphicOrderAt_id_sub_const

/-- **The envelope keeps the simple off-critical zero.** -/
theorem meromorphicOrderAt_envelope_reflectionQuartet {ρ : ℂ} (h0 : 0 < ρ.re)
    (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    meromorphicOrderAt (fun s => gammaGaussianEnvelope s * reflectionQuartet ρ s) ρ = 1 := by
  rw [meromorphicOrderAt_envelope_mul (analyticAt_reflectionQuartet ρ ρ).meromorphicAt h0]
  exact meromorphicOrderAt_reflectionQuartet hre him

/-- In the right half-plane the enveloped quartet vanishes exactly on the quartet: the envelope
neither creates nor destroys a zero there. -/
theorem envelope_reflectionQuartet_eq_zero_iff {ρ s : ℂ} (hs : 0 < s.re) :
    gammaGaussianEnvelope s * reflectionQuartet ρ s = 0 ↔
      s = ρ ∨ s = 1 - ρ ∨ s = (starRingEnd ℂ) ρ ∨ s = 1 - (starRingEnd ℂ) ρ := by
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact absurd h (gammaGaussianEnvelope_ne_zero_of_re_pos hs)
    · exact (reflectionQuartet_eq_zero_iff ρ s).1 h
  · intro h
    exact Or.inr ((reflectionQuartet_eq_zero_iff ρ s).2 h)

/-! ## Self-duality of the enveloped quartet -/

/-- A reflection-symmetric datum has a cosine-Fourier self-dual envelope. -/
theorem evenChiFactor_mul_envelope_mul_of_symm {F : ℂ → ℂ} (hF : ∀ s : ℂ, F (1 - s) = F s)
    {s : ℂ} (hs : s.re < 1) :
    evenChiFactor s * (gammaGaussianEnvelope (1 - s) * F (1 - s))
      = gammaGaussianEnvelope s * F s := by
  rw [evenChiFactor_mul_envelope_mul_one_sub hs, hF s]

/-- **The enveloped quartet is self-dual.** -/
theorem envelope_reflectionQuartet_selfDual {ρ s : ℂ} (hs : s.re < 1) :
    evenChiFactor s * (gammaGaussianEnvelope (1 - s) * reflectionQuartet ρ (1 - s))
      = gammaGaussianEnvelope s * reflectionQuartet ρ s :=
  evenChiFactor_mul_envelope_mul_of_symm (reflectionQuartet_one_sub ρ) hs

/-! ## The nonselection theorem -/

/-- **The universal envelope cannot select the critical line.**  For every point strictly inside the
critical strip which is neither on the critical line nor on the real axis there is a
reflection-symmetric datum of polynomial vertical growth whose envelope is moderate, cosine-Fourier
self-dual, and has a simple zero at that point.  Existence of a faithful self-dual completion is
therefore compatible with arbitrary off-critical reflection quartets. -/
theorem exists_selfDual_moderate_with_offCritical_zero {ρ : ℂ} (h0 : 0 < ρ.re)
    (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    ∃ F : ℂ → ℂ,
      HasStripPolyGrowth F ∧
      (∀ s : ℂ, F (1 - s) = F s) ∧
      HasStripPolyGrowth (fun s => gammaGaussianEnvelope s * F s) ∧
      (∀ s : ℂ, s.re < 1 →
        evenChiFactor s * (gammaGaussianEnvelope (1 - s) * F (1 - s))
          = gammaGaussianEnvelope s * F s) ∧
      meromorphicOrderAt (fun s => gammaGaussianEnvelope s * F s) ρ = 1 := by
  refine ⟨reflectionQuartet ρ, hasStripPolyGrowth_reflectionQuartet ρ,
    reflectionQuartet_one_sub ρ,
    hasStripPolyGrowth_envelope_mul (hasStripPolyGrowth_reflectionQuartet ρ),
    fun s hs => envelope_reflectionQuartet_selfDual hs,
    meromorphicOrderAt_envelope_reflectionQuartet h0 hre him⟩

end

end GaloisForLFunctions
