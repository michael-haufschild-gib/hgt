import GaloisForLFunctions.RHTower.SpectralBlaschkeMatching

/-!
# What computes the signature: a sign, not a magnitude

The trace-form reading turned the target into a signature. Signatures of the kind that arise here —
"a real entire function has only real zeros" — are computed classically by the **Hermite–Biehler /
Nevanlinna** criterion: such a function has only real zeros exactly when its logarithmic derivative
maps the upper half-plane into the lower, that is, when an explicit imaginary part never changes
sign.

Termwise this is transparent. The logarithmic derivative is a sum of resolvents, and the resolvent of
a zero contributes

  `−Im (z − z_ρ)^{-1} = (Im z − Im z_ρ) / |z − z_ρ|²`.

A zero on the critical line has real spectral point, so its contribution is positive throughout the
open upper half-plane. A zero off the line has an orbit member with **positive** spectral imaginary
part, and directly beneath it — at half its height — that contribution is negative, with exact value
`−2/Im z_ρ`. So the hypothesis is equivalent to the positivity of every term at every point of the
open upper half-plane.

The reason to record this separately is the *kind* of statement it is. Everything earlier in this
lane was a magnitude: a potential below two, a count below one, an estimate uniform in the height.
Those run into the obstruction that the required constant is absolute while every available estimate
grows. **This criterion is a sign.** The detector's magnitude `−2/Im z_ρ` diverges as a zero
approaches the line — degree minus one, useless as a bound — while its *sign* is constant, degree
zero, and is exactly what decides. A sign condition has no threshold to cross and no constant to
lose, so the absolute-constant obstruction does not apply to it.

That is what changes: positivity of an imaginary part is a statement about a **harmonic function on a
half-plane** vanishing on the boundary, and the technology for such statements — maximum principles,
Herglotz representation, Harnack — is disjoint from the averaging machinery every no-go in this lane
excludes.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Nevanlinna term of a zero at a point: minus the imaginary part of its resolvent. -/
def nevanlinnaTerm (z : ℂ) (ρ : XiDivisorSupport) : ℝ :=
  (z.im - (xiSpectralPointSupport ρ).im) / Complex.normSq (z - xiSpectralPointSupport ρ)

theorem nevanlinnaTerm_eq_neg_im_inv (z : ℂ) (ρ : XiDivisorSupport) :
    nevanlinnaTerm z ρ = -((z - xiSpectralPointSupport ρ)⁻¹).im := by
  rw [nevanlinnaTerm, Complex.inv_im, Complex.sub_im]
  ring

/-- **A zero on the critical line is positive throughout the upper half-plane.** -/
theorem nevanlinnaTerm_pos_of_im_eq_zero {z : ℂ} (hz : 0 < z.im) {ρ : XiDivisorSupport}
    (h : (xiSpectralPointSupport ρ).im = 0) : 0 < nevanlinnaTerm z ρ := by
  have hne : z - xiSpectralPointSupport ρ ≠ 0 := by
    intro hc
    rw [sub_eq_zero] at hc
    rw [hc, h] at hz
    exact lt_irrefl 0 hz
  rw [nevanlinnaTerm, h, sub_zero]
  exact div_pos hz (Complex.normSq_pos.mpr hne)

/-- **The witness value.** Directly beneath a zero of positive spectral height, at half that height,
the term is exactly `−2` over the height: the magnitude diverges as the zero approaches the line,
the sign does not move. -/
theorem nevanlinnaTerm_witness_value {ρ : XiDivisorSupport}
    (h : 0 < (xiSpectralPointSupport ρ).im) :
    nevanlinnaTerm
        (⟨(xiSpectralPointSupport ρ).re, (xiSpectralPointSupport ρ).im / 2⟩ : ℂ) ρ
      = -2 / (xiSpectralPointSupport ρ).im := by
  have hne : (xiSpectralPointSupport ρ).im ≠ 0 := ne_of_gt h
  rw [nevanlinnaTerm]
  simp only [Complex.sub_re, Complex.sub_im, Complex.normSq_apply, sub_self]
  field_simp
  ring

/-- A zero of positive spectral height breaks the sign. -/
theorem exists_nevanlinnaTerm_neg {ρ : XiDivisorSupport}
    (h : 0 < (xiSpectralPointSupport ρ).im) :
    ∃ z : ℂ, 0 < z.im ∧ nevanlinnaTerm z ρ < 0 := by
  refine ⟨(⟨(xiSpectralPointSupport ρ).re, (xiSpectralPointSupport ρ).im / 2⟩ : ℂ),
    (by show (0 : ℝ) < (xiSpectralPointSupport ρ).im / 2; linarith), ?_⟩
  rw [nevanlinnaTerm_witness_value h]
  exact div_neg_of_neg_of_pos (by norm_num) h

/-- **The sign criterion.** The hypothesis is the positivity of every Nevanlinna term at every point
of the open upper half-plane — a condition on a sign, with no threshold and no constant. -/
theorem riemannHypothesis_iff_forall_nevanlinnaTerm_pos :
    RiemannHypothesis ↔ ∀ z : ℂ, 0 < z.im → ∀ ρ : XiDivisorSupport, 0 < nevanlinnaTerm z ρ := by
  constructor
  · intro h z hz ρ
    exact nevanlinnaTerm_pos_of_im_eq_zero hz
      (riemannHypothesis_iff_forall_xiSpectralPointSupport_im_eq_zero.mp h ρ)
  · intro h
    refine riemannHypothesis_iff_forall_xiSpectralPointSupport_im_eq_zero.mpr fun ρ => ?_
    by_contra hc
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · have hp : 0 < (xiSpectralPointSupport (supportPartner ρ)).im := by
        rw [xiSpectralPointSupport_supportPartner, Complex.conj_im]
        linarith
      obtain ⟨z, hz, hneg⟩ := exists_nevanlinnaTerm_neg hp
      exact absurd (h z hz (supportPartner ρ)) (not_lt.mpr (le_of_lt hneg))
    · obtain ⟨z, hz, hneg⟩ := exists_nevanlinnaTerm_neg hgt
      exact absurd (h z hz ρ) (not_lt.mpr (le_of_lt hneg))

end

end RHTower
