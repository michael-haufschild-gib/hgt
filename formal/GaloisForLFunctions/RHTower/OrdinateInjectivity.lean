import GaloisForLFunctions.RHTower.ReflectionTateParity

/-!
# The hypothesis is the injectivity of the ordinate map

The Hermitian reflection `ρ ↦ 1 − conj ρ` **preserves the imaginary part**, so the `ℤ/2`-action
whose triviality is the hypothesis (`ReflectionTateParity`) is *fibred over the height*: every orbit
lies inside a single horizontal slice, and each slice is an independent finite `ℤ/2`-problem.

A free orbit therefore consists of two **distinct** zeros at **exactly the same ordinate**.  Hence:

  `RiemannHypothesis ↔ distinct zeros of ξ have distinct imaginary parts`.

This replaces the positivity form of the hypothesis by a **separation** form.  The quantity to be
excluded is an exact ordinate collision — distance zero — rather than a real part resolved at scale
`1/log t`, which is where every pair-correlation and mollifier method stalls.  In particular any
height carrying only one divisor point is automatically critical, with no hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The Hermitian reflection preserves the ordinate.**  The `ℤ/2`-action is fibred over the
height. -/
theorem lagPartner_im (q : XiZeroCopy) : ((lagPartner q).1 : ℂ).im = (q.1 : ℂ).im := by
  rw [lagPartner_coe]
  simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
  ring

/-- Every reflection orbit lies inside a single horizontal slice. -/
theorem lagPartner_im_eq_of_im_eq {t : ℝ} {q : XiZeroCopy} (h : (q.1 : ℂ).im = t) :
    ((lagPartner q).1 : ℂ).im = t := by rw [lagPartner_im]; exact h

/-- **A height carrying a single divisor point is automatically critical**, unconditionally. -/
theorem re_eq_half_of_slice_subsingleton {q : XiZeroCopy}
    (h : ∀ r : XiZeroCopy, ((r.1 : ℂ)).im = (q.1 : ℂ).im → ((r.1 : ℂ)) = (q.1 : ℂ)) :
    (q.1 : ℂ).re = 1 / 2 :=
  (lagPartner_fst_eq_iff q).mp (h (lagPartner q) (lagPartner_im q))

/-- Injectivity of the ordinate map implies the hypothesis. -/
theorem riemannHypothesis_of_ordinate_injective
    (h : ∀ q r : XiZeroCopy, (q.1 : ℂ).im = (r.1 : ℂ).im → (q.1 : ℂ) = (r.1 : ℂ)) :
    RiemannHypothesis :=
  riemannHypothesis_iff_lagPartner_fst_eq.mpr fun q =>
    h (lagPartner q) q (lagPartner_im q)

/-- Under the hypothesis the ordinate map is injective. -/
theorem ordinate_injective_of_riemannHypothesis (hRH : RiemannHypothesis)
    (q r : XiZeroCopy) (h : (q.1 : ℂ).im = (r.1 : ℂ).im) : (q.1 : ℂ) = (r.1 : ℂ) := by
  apply Complex.ext
  · rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q,
      xiZeroCopy_re_eq_half_of_riemannHypothesis hRH r]
  · exact h

/-- **The hypothesis is the injectivity of the ordinate map on the divisor.** -/
theorem riemannHypothesis_iff_ordinate_injective :
    RiemannHypothesis ↔
      ∀ q r : XiZeroCopy, (q.1 : ℂ).im = (r.1 : ℂ).im → (q.1 : ℂ) = (r.1 : ℂ) :=
  ⟨ordinate_injective_of_riemannHypothesis, riemannHypothesis_of_ordinate_injective⟩

/-- Failure of the hypothesis produces two **distinct** divisor points at **exactly the same**
ordinate: the obstruction is an exact collision, not a small separation. -/
theorem exists_ordinate_collision_of_not_riemannHypothesis (h : ¬ RiemannHypothesis) :
    ∃ q r : XiZeroCopy, (q.1 : ℂ).im = (r.1 : ℂ).im ∧ (q.1 : ℂ) ≠ (r.1 : ℂ) := by
  by_contra hc
  push Not at hc
  exact h (riemannHypothesis_of_ordinate_injective fun q r hqr => hc q r hqr)

end

end RHTower
