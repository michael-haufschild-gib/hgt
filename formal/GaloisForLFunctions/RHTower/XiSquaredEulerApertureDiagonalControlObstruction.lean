import GaloisForLFunctions.RHTower.XiSquaredEulerApertureHilbertCorrelation
import GaloisForLFunctions.RHTower.ScaleCovariantXiBernsteinAbelCorollary

/-!
# Diagonal-control obstruction for the squared-Euler aperture

The all-degree squared-Euler identity splits each Xi reciprocal-square atom into a positive
Hilbert response and a transverse charge.  This file shows that no atomwise bounded comparison
can control the latter at an off-critical atom.

Indeed, real affine polynomial evaluation at a nonreal atom is onto the complex plane.  Choosing
the value on the kernel line of the sheared Hilbert functional makes the positive response vanish
while leaving a strictly positive transverse charge.  Thus any successful all-degree charge
control must mix distinct Xi atoms globally.  More sharply, existence of an arbitrary finite
termwise comparison constant at every atom is already equivalent to RH.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- **Atomic kernel-charge separation.**  At every off-critical Xi atom, one real affine
polynomial lies in the kernel of the positive sheared response while retaining strictly positive
transverse charge. -/
theorem exists_xiSquaredEulerAperture_atom_charge_without_hilbert
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ p : Polynomial ℝ,
      p.natDegree ≤ 1 ∧
      xiSquaredEulerApertureHilbertTerm p q = 0 ∧
        0 < xiSquaredEulerApertureTransverseTerm p q := by
  let lam : ℂ := xiZeroCopyReciprocalSquare q
  have him : lam.im ≠ 0 := by
    intro him
    apply hoff
    apply (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp
    simpa only [lam, xiZeroCopyReciprocalSquare_eq] using him
  have hre : 0 < lam.re := by
    simpa only [lam] using xiZeroCopyReciprocalSquare_re_pos q
  let w : ℂ := ((lam.im / lam.re : ℝ) : ℂ) + I
  let p : Polynomial ℝ := realLinearInterpolator lam w
  have heval : evalRealPolynomial p lam = w := by
    exact evalRealLinearInterpolator him
  refine ⟨p, ?_, ?_, ?_⟩
  · dsimp only [p]
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hN0 : N ≠ 0 := by omega
    have hN1 : N ≠ 1 := by omega
    simp [realLinearInterpolator, Polynomial.coeff_C, Polynomial.coeff_X,
      hN0, Ne.symm hN1]
  · unfold xiSquaredEulerApertureHilbertTerm
      xiSquaredEulerApertureShearedEvaluation
    change lam.re *
      ((evalRealPolynomial p lam).re -
        lam.im / lam.re * (evalRealPolynomial p lam).im) ^ 2 = 0
    rw [heval]
    simp [w]
  · unfold xiSquaredEulerApertureTransverseTerm
    change 0 < Complex.normSq lam / lam.re *
      (evalRealPolynomial p lam).im ^ 2
    rw [heval]
    have hnorm : 0 < Complex.normSq lam := by
      exact Complex.normSq_pos.mpr (fun hzero => him (by rw [hzero]; rfl))
    simpa [w] using div_pos hnorm hre

/-- No finite atomwise comparison constant can dominate transverse charge by Hilbert response at
an off-critical atom.  The obstruction is a kernel inclusion failure, not a poor constant. -/
theorem not_exists_xiSquaredEulerAperture_termwise_bound_of_ne_half
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ ∃ K : ℝ, ∀ p : Polynomial ℝ,
      xiSquaredEulerApertureTransverseTerm p q ≤
        K * xiSquaredEulerApertureHilbertTerm p q := by
  rintro ⟨K, hK⟩
  obtain ⟨p, _hpDegree, hpHilbert, hpTransverse⟩ :=
    exists_xiSquaredEulerAperture_atom_charge_without_hilbert q hoff
  have hp := hK p
  rw [hpHilbert, mul_zero] at hp
  linarith

/-- Orbitwise bounded charge control permits a separate arbitrary finite constant at every Xi
atom.  It asks for no uniformity across atoms. -/
def XiSquaredEulerApertureOrbitwiseBoundedCharge : Prop :=
  ∀ q : XiZeroCopy, ∃ K : ℝ, ∀ p : Polynomial ℝ,
    xiSquaredEulerApertureTransverseTerm p q ≤
      K * xiSquaredEulerApertureHilbertTerm p q

/-- **Sharp diagonal-control boundary.**  Even completely nonuniform atomwise bounded control is
equivalent to RH.  Under RH every transverse term vanishes.  Conversely, the atomic
kernel-charge separator rules out every off-critical atom.  Therefore a noncircular proof of the
global all-degree charge inequality must use genuinely off-diagonal coupling between atoms. -/
theorem xiSquaredEulerApertureOrbitwiseBoundedCharge_iff_riemannHypothesis :
    XiSquaredEulerApertureOrbitwiseBoundedCharge ↔ RiemannHypothesis := by
  constructor
  · intro hbound
    apply riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.mpr
    intro q
    have hline : (q.1 : ℂ).re = 1 / 2 := by
      by_contra hoff
      exact not_exists_xiSquaredEulerAperture_termwise_bound_of_ne_half q hoff
        (hbound q)
    have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_eq]
      exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).mpr hline
    exact Complex.nonneg_iff.mpr
      ⟨(xiZeroCopyReciprocalSquare_re_pos q).le, him.symm⟩
  · intro hRH q
    refine ⟨0, fun p => ?_⟩
    obtain ⟨x, _hx, hcoord⟩ :=
      xiCentralReciprocalSquare_pos_real_of_rh hRH q.1
    have hlam : xiZeroCopyReciprocalSquare q = (x : ℂ) := by
      rw [xiZeroCopyReciprocalSquare_eq]
      exact hcoord
    rw [xiSquaredEulerApertureTransverseTerm, hlam,
      evalRealPolynomial_ofReal]
    simp

end

end RHTower
