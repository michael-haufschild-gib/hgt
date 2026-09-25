import GaloisForLFunctions.RHTower.OrbitQuadraticDiscriminant
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The functional-equation matching is conjugation, and the potential is a Blaschke defect

The previous module reduced the critical-line potential to the orbit quadratics and named the
missing datum the *matching* `ρ ↦ 1 − ρ̄`. That reading was wrong, and this module corrects it.

In the spectral coordinate `z_ρ = (ρ − 1/2)·(−i)` the functional-equation partner is simply the
complex conjugate: `z_{σρ} = z̄_ρ`. The matching therefore requires no choice at all. It is the
pairing of the non-real zeros of a real entire function with their conjugates, and the orbit
quadratic is the corresponding real quadratic factor. There is no half-divisor to construct, and
the obstruction identified earlier is not the obstruction.

What the matching buys is a clean form for the potential. Set

  `B_ρ(t) = (t − z̄_ρ)/(t − z_ρ)`,

the Blaschke factor of the zero at the real point `t`. It is unimodular on the real axis, it equals
`1` exactly when `ρ` lies on the critical line, and the partner's factor is its conjugate. The bump
is its defect from one:

  `bump_ρ(t) = ‖1 − B_ρ(t)‖² / 4 = (1 − Re B_ρ(t))/2`,

and summing over the divisor, where each off-line orbit contributes twice,

  `Σ_ρ (1 − B_ρ(t)) = 2 U(t)`.

So the potential is *linear* in the family of Blaschke defects, not quadratic. Moreover

  `1 − B_ρ(t) = 2i (Re ρ − 1/2)/(t − z_ρ)`,

which displays the whole difficulty in one line: the defect is the resolvent `1/(t − z_ρ)` weighted
by the displacement. The holomorphic data of `Ξ` supply the unweighted power sums
`Σ_ρ (t − z_ρ)^{-k}`, through the Taylor coefficients of its logarithmic derivative at `t`, and
supply no weighting by the displacement. That, and not the matching, is what is missing.
-/

open Complex

namespace RHTower

noncomputable section

@[simp] theorem xiSpectralPointSupport_re (ρ : XiDivisorSupport) :
    (xiSpectralPointSupport ρ).re = (ρ : ℂ).im := by
  simp [xiSpectralPointSupport]

@[simp] theorem xiSpectralPointSupport_im (ρ : XiDivisorSupport) :
    (xiSpectralPointSupport ρ).im = -((ρ : ℂ).re - 1 / 2) := by
  simp [xiSpectralPointSupport]

/-- **The matching is conjugation.** In the spectral coordinate the functional-equation partner of a
zero is its complex conjugate, so the pairing is canonical and requires no choice. -/
theorem xiSpectralPointSupport_supportPartner (ρ : XiDivisorSupport) :
    xiSpectralPointSupport (supportPartner ρ)
      = (starRingEnd ℂ) (xiSpectralPointSupport ρ) := by
  refine Complex.ext ?_ ?_ <;>
    simp [supportPartner_re, supportPartner_im] <;> ring

/-- A spectral point is real exactly when its zero lies on the critical line. -/
theorem xiSpectralPointSupport_im_eq_zero_iff (ρ : XiDivisorSupport) :
    (xiSpectralPointSupport ρ).im = 0 ↔ (ρ : ℂ).re = 1 / 2 := by
  rw [xiSpectralPointSupport_im, neg_eq_zero, sub_eq_zero]

/-- **The hypothesis is the reality of the spectral divisor.** -/
theorem riemannHypothesis_iff_forall_xiSpectralPointSupport_im_eq_zero :
    RiemannHypothesis ↔ ∀ ρ : XiDivisorSupport, (xiSpectralPointSupport ρ).im = 0 := by
  constructor
  · intro h ρ
    exact (xiSpectralPointSupport_im_eq_zero_iff ρ).mpr
      ((supportPartner_eq_self_iff ρ).mp (riemannHypothesis_iff_supportPartner_eq_id.mp h ρ))
  · intro h
    exact riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ =>
      (xiSpectralPointSupport_im_eq_zero_iff ρ).mp (h ρ)

theorem normSq_sub_xiSpectralPointSupport (t : ℝ) (ρ : XiDivisorSupport) :
    Complex.normSq ((t : ℂ) - xiSpectralPointSupport ρ)
      = ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) + (t - (ρ : ℂ).im) ^ (2 : ℕ) := by
  simp [Complex.normSq_apply]
  ring

theorem conj_sub_xiSpectralPointSupport (ρ : XiDivisorSupport) :
    (starRingEnd ℂ) (xiSpectralPointSupport ρ) - xiSpectralPointSupport ρ
      = 2 * Complex.I * (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) := by
  refine Complex.ext ?_ ?_ <;> simp <;> ring

/-- The Blaschke factor of a zero, at a real point. -/
def xiBlaschke (ρ : XiDivisorSupport) (t : ℝ) : ℂ :=
  ((t : ℂ) - (starRingEnd ℂ) (xiSpectralPointSupport ρ)) / ((t : ℂ) - xiSpectralPointSupport ρ)

/-- The partner's Blaschke factor is the conjugate. -/
theorem xiBlaschke_supportPartner (ρ : XiDivisorSupport) (t : ℝ) :
    xiBlaschke (supportPartner ρ) t = (starRingEnd ℂ) (xiBlaschke ρ t) := by
  rw [xiBlaschke, xiBlaschke, xiSpectralPointSupport_supportPartner, map_div₀,
    map_sub, map_sub, Complex.conj_ofReal, starRingEnd_self_apply]

/-- **The Blaschke defect.** The resolvent weighted by the displacement. -/
theorem one_sub_xiBlaschke (ρ : XiDivisorSupport) (t : ℝ)
    (hne : (t : ℂ) ≠ xiSpectralPointSupport ρ) :
    1 - xiBlaschke ρ t
      = 2 * Complex.I * (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) / ((t : ℂ) - xiSpectralPointSupport ρ) := by
  have hd : (t : ℂ) - xiSpectralPointSupport ρ ≠ 0 := sub_ne_zero.mpr hne
  rw [xiBlaschke, eq_div_iff hd, sub_mul, one_mul, div_mul_cancel₀ _ hd,
    ← conj_sub_xiSpectralPointSupport]
  ring

/-- The Blaschke factor is unimodular on the real axis. -/
theorem normSq_xiBlaschke (ρ : XiDivisorSupport) (t : ℝ)
    (hne : (t : ℂ) ≠ xiSpectralPointSupport ρ) : Complex.normSq (xiBlaschke ρ t) = 1 := by
  have hd : (t : ℂ) - xiSpectralPointSupport ρ ≠ 0 := sub_ne_zero.mpr hne
  have hdn : Complex.normSq ((t : ℂ) - xiSpectralPointSupport ρ) ≠ 0 :=
    fun hc => hd (Complex.normSq_eq_zero.mp hc)
  rw [xiBlaschke, Complex.normSq_div]
  have hnum : Complex.normSq ((t : ℂ) - (starRingEnd ℂ) (xiSpectralPointSupport ρ))
      = Complex.normSq ((t : ℂ) - xiSpectralPointSupport ρ) := by
    simp [Complex.normSq_apply]
    ring
  rw [hnum, div_self hdn]

/-- **The bump is the squared Blaschke defect.** -/
theorem poissonBumpTerm_eq_normSq_one_sub_xiBlaschke (ρ : XiDivisorSupport) (t : ℝ)
    (hne : (t : ℂ) ≠ xiSpectralPointSupport ρ) :
    poissonBumpTerm t ρ = Complex.normSq (1 - xiBlaschke ρ t) / 4 := by
  have hd : (t : ℂ) - xiSpectralPointSupport ρ ≠ 0 := sub_ne_zero.mpr hne
  have hdn : Complex.normSq ((t : ℂ) - xiSpectralPointSupport ρ) ≠ 0 :=
    fun hc => hd (Complex.normSq_eq_zero.mp hc)
  have hnum : Complex.normSq (2 * Complex.I * (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ))
      = 4 * ((ρ : ℂ).re - 1 / 2) ^ (2 : ℕ) := by
    simp [Complex.normSq_apply]
    ring
  rw [one_sub_xiBlaschke ρ t hne, Complex.normSq_div, hnum,
    normSq_sub_xiSpectralPointSupport, poissonBumpTerm]
  ring

/-- The real-part form of the same identity. -/
theorem poissonBumpTerm_eq_one_sub_re_xiBlaschke (ρ : XiDivisorSupport) (t : ℝ)
    (hne : (t : ℂ) ≠ xiSpectralPointSupport ρ) :
    poissonBumpTerm t ρ = (1 - (xiBlaschke ρ t).re) / 2 := by
  have hu := normSq_xiBlaschke ρ t hne
  rw [poissonBumpTerm_eq_normSq_one_sub_xiBlaschke ρ t hne]
  have hexp : Complex.normSq (1 - xiBlaschke ρ t)
      = 1 - 2 * (xiBlaschke ρ t).re + Complex.normSq (xiBlaschke ρ t) := by
    simp [Complex.normSq_apply]
    ring
  rw [hexp, hu]
  ring

/-- **The orbit sum.** A zero and its partner together contribute four times one bump, so the
potential is the total Blaschke defect halved. -/
theorem one_sub_xiBlaschke_add_partner (ρ : XiDivisorSupport) (t : ℝ)
    (hne : (t : ℂ) ≠ xiSpectralPointSupport ρ) :
    (1 - xiBlaschke ρ t) + (1 - xiBlaschke (supportPartner ρ) t)
      = ((4 * poissonBumpTerm t ρ : ℝ) : ℂ) := by
  rw [xiBlaschke_supportPartner, poissonBumpTerm_eq_one_sub_re_xiBlaschke ρ t hne]
  refine Complex.ext ?_ ?_ <;> simp <;> ring

/-- The Blaschke factor is one exactly on the critical line. -/
theorem xiBlaschke_eq_one_iff (ρ : XiDivisorSupport) (t : ℝ)
    (hne : (t : ℂ) ≠ xiSpectralPointSupport ρ) :
    xiBlaschke ρ t = 1 ↔ (ρ : ℂ).re = 1 / 2 := by
  have hd : (t : ℂ) - xiSpectralPointSupport ρ ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · intro h
    have h0 : (1 : ℂ) - xiBlaschke ρ t = 0 := by rw [h]; ring
    rw [one_sub_xiBlaschke ρ t hne, div_eq_zero_iff] at h0
    rcases h0 with h1 | h2
    · have : (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) = 0 := by
        rcases mul_eq_zero.mp h1 with h3 | h4
        · exact absurd h3 (by simp [Complex.I_ne_zero])
        · exact h4
      have := Complex.ofReal_eq_zero.mp this
      linarith
    · exact absurd h2 hd
  · intro h
    have hz : (((ρ : ℂ).re - 1 / 2 : ℝ) : ℂ) = 0 := by
      rw [h]; norm_num
    have h0 : (1 : ℂ) - xiBlaschke ρ t = 0 := by
      rw [one_sub_xiBlaschke ρ t hne, hz]
      simp
    linear_combination -h0

end

end RHTower
