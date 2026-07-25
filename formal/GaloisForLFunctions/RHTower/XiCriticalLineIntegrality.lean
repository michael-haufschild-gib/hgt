import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric

/-!
# The critical line as an integrality condition

The Hurwitz monodromy character identifies two exponents exactly when they differ by an integer, so
the differential-algebraic characterisation of the critical line reduces to the arithmetic of the
single real number `1 - 2 Re rho`: the functional-equation partner `1 - rho` and the Schwarz partner
`conj rho` carry the same character precisely when that number is an integer, and inside the open
strip the only available integer is zero.

Stated directly on the divisor this says the Riemann Hypothesis is an *integrality* assertion rather
than an estimate: every Xi zero must place `1 - 2 Re rho` in `Z`.  The strip supplies the width, the
integrality supplies the location.
-/

open Complex

namespace RHTower

noncomputable section

/-- **RH as integrality.**  The Riemann Hypothesis holds if and only if `1 - 2 Re rho` is an integer
at every point of the Xi divisor.  The open strip confines that number to `(-1, 1)`, so integrality
alone pins it to `0`, which is the critical line. -/
theorem riemannHypothesis_iff_forall_exists_int_one_sub_two_re :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, ∃ m : ℤ, 1 - 2 * (rho : ℂ).re = (m : ℝ) := by
  constructor
  · intro hRH rho
    refine ⟨0, ?_⟩
    rw [xi_divisor_support_re_eq_half_of_rh hRH rho]
    norm_num
  · intro h
    refine riemannHypothesis_of_xiSpectralPoint_real fun q => ⟨(xiSpectralPoint q).re, ?_⟩
    obtain ⟨m, hm⟩ := h q.1
    have hmem := xi_divisor_support_re_mem_open_unit q.1
    have hlo : (-1 : ℝ) < (m : ℝ) := by rw [← hm]; linarith [hmem.2]
    have hhi : (m : ℝ) < 1 := by rw [← hm]; linarith [hmem.1]
    have hm0 : m = 0 := by
      have h1 : (-1 : ℤ) < m := by exact_mod_cast hlo
      have h2 : m < 1 := by exact_mod_cast hhi
      omega
    have hre : ((q.1 : ℂ)).re = 1 / 2 := by
      rw [hm0] at hm
      push_cast at hm
      linarith
    have him : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint]
      have hhalf : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
      have hhalfim : ((1 : ℂ) / 2).im = 0 := by norm_num
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
        Complex.sub_re, Complex.sub_im, hhalf, hhalfim]
      rw [hre]
      ring
    conv_lhs => rw [← Complex.re_add_im (xiSpectralPoint q)]
    rw [him]
    simp

end

end RHTower

namespace RHTower

noncomputable section

/-- **RH as a fixed-point property.**  The anti-holomorphic involution `sigma rho = 1 - conj rho`
preserves the Xi divisor -- it is the functional equation composed with Schwarz reflection -- and its
fixed locus is exactly the critical line.  So the Riemann Hypothesis says precisely that `sigma` acts
on the divisor with no free orbits. -/
theorem riemannHypothesis_iff_forall_add_conj_eq_one :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ) + (starRingEnd ℂ) (rho : ℂ) = 1 := by
  rw [riemannHypothesis_iff_forall_exists_int_one_sub_two_re]
  constructor
  · intro h rho
    obtain ⟨m, hm⟩ := h rho
    have hmem := xi_divisor_support_re_mem_open_unit rho
    have hlo : (-1 : ℝ) < (m : ℝ) := by rw [← hm]; linarith [hmem.2]
    have hhi : (m : ℝ) < 1 := by rw [← hm]; linarith [hmem.1]
    have hm0 : m = 0 := by
      have h1 : (-1 : ℤ) < m := by exact_mod_cast hlo
      have h2 : m < 1 := by exact_mod_cast hhi
      omega
    rw [hm0] at hm
    push_cast at hm
    have hre : ((rho : ℂ)).re = 1 / 2 := by linarith
    refine Complex.ext ?_ ?_
    · simp [Complex.add_re, hre]; ring
    · simp [Complex.add_im]
  · intro h rho
    refine ⟨0, ?_⟩
    have hre := congrArg Complex.re (h rho)
    simp only [Complex.add_re, Complex.conj_re, Complex.one_re] at hre
    push_cast
    linarith
end

end RHTower

namespace RHTower

noncomputable section

/-- The critical-line reflection `sigma rho = 1 - conj rho` on the Xi divisor support: the functional
equation composed with Schwarz reflection.  It is an involution and the divisor is invariant under
it, so the divisor splits into `sigma`-fixed points -- the zeros on the critical line -- and free
orbits of size two. -/
def xiZeroLineConjEquiv : XiDivisorSupport ≃ XiDivisorSupport :=
  xiZeroConjEquiv.trans xiZeroReflectEquiv

@[simp]
theorem xiZeroLineConjEquiv_apply (rho : XiDivisorSupport) :
    ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ) = 1 - (starRingEnd ℂ) (rho : ℂ) := rfl

theorem xiZeroLineConjEquiv_involutive :
    Function.Involutive (xiZeroLineConjEquiv) := by
  intro rho
  apply Subtype.ext
  rw [xiZeroLineConjEquiv_apply, xiZeroLineConjEquiv_apply]
  simp

/-- **RH as the absence of free orbits.**  The Riemann Hypothesis holds exactly when the
critical-line reflection fixes every point of the Xi divisor -- that is, when the involution
`sigma rho = 1 - conj rho` acts with no free orbit. -/
theorem riemannHypothesis_iff_xiZeroLineConj_fixed :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport, xiZeroLineConjEquiv rho = rho := by
  rw [riemannHypothesis_iff_forall_add_conj_eq_one]
  constructor
  · intro h rho
    apply Subtype.ext
    rw [xiZeroLineConjEquiv_apply]
    have := h rho
    linear_combination -this
  · intro h rho
    have := congrArg (fun x : XiDivisorSupport => (x : ℂ)) (h rho)
    simp only [xiZeroLineConjEquiv_apply] at this
    linear_combination -this

end

end RHTower
