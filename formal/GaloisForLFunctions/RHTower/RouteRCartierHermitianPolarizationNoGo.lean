import GaloisForLFunctions.RHTower.BurnolCartierZeroTransferHeadPolarization

/-!
# Route R fixed Hermitian Cartier-polarization classification

The actual forward and cosine aperture heads form a two-dimensional physical
fibre.  Cartier zero-transfer acts diagonally by the literal gains

`g rho = conj rho / (1 - rho)` and `gDual rho = (1 - conj rho) / rho`.

This module closes the whole fixed same-fibre Hermitian escape, not only the
unweighted norm used by the earlier endpoint.  The mixed Hermitian coefficient
is conserved exactly because `conj (g rho) * gDual rho = 1`; the two diagonal
coefficients acquire reciprocal positive weights.  Consequently:

* every orientation-symmetric positive diagonal reading strictly increases at
  a hypothetical right-half Xi divisor, independently of its mixed term;
* a fixed Hermitian reading conserved on the whole physical fibre has zero
  diagonal coefficients, hence belongs to the split indefinite family;
* the reflection/Cartier loop is already projectively scalar for every grade,
  so projective Stokes flatness cannot imply neutral grade.

No source annihilation, critical-line placement, or RH is assumed.
-/

open Complex Real
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- Literal two-head physical fibre: forward Gamma orientation followed by its
cosine/reciprocal mate. -/
abbrev RouteRCartierHeadPlane := ℂ × ℂ

/-- Literal Cartier action on the two aperture heads. -/
def routeRCartierHeadTransport (rho : ℂ) (z : RouteRCartierHeadPlane) :
    RouteRCartierHeadPlane :=
  (burnolCartierForwardHeadGain rho * z.1,
    burnolCartierCosineHeadGain rho * z.2)

/-- Exchange of the two Gamma orientations. -/
def routeRCartierHeadSwap (z : RouteRCartierHeadPlane) :
    RouteRCartierHeadPlane :=
  (z.2, z.1)

/-- Fixed Hermitian quadratic reading with real diagonal coefficients.  The
last term is the complete mixed coefficient; no orientation symmetry or
positivity is built into the definition. -/
def routeRFixedHermitianHeadReading
    (A B : ℝ) (C : ℂ) (z : RouteRCartierHeadPlane) : ℝ :=
  A * Complex.normSq z.1 + B * Complex.normSq z.2 +
    2 * (conj z.1 * C * z.2).re

/-- Fixed source head vector, up to its common irrelevant sign. -/
def routeRFixedGammaHeadVector : RouteRCartierHeadPlane :=
  (1, (Real.log 2 : ℂ))

private theorem routeR_one_sub_conj_ne_zero {rho : ℂ} (hrho : rho ≠ 1) :
    (1 : ℂ) - conj rho ≠ 0 := by
  intro h
  have hc : conj rho = 1 := (sub_eq_zero.mp h).symm
  have hr : rho = 1 := by
    simpa using congrArg conj hc
  exact hrho hr

/-- The two literal Cartier gains preserve the mixed Hermitian coefficient. -/
theorem conj_burnolCartierForwardHeadGain_mul_cosineHeadGain
    {rho : ℂ} (hzero : rho ≠ 0) (hone : rho ≠ 1) :
    conj (burnolCartierForwardHeadGain rho) *
        burnolCartierCosineHeadGain rho = 1 := by
  have hc : (1 : ℂ) - conj rho ≠ 0 := routeR_one_sub_conj_ne_zero hone
  rw [burnolCartierForwardHeadGain, burnolCartierCosineHeadGain,
    map_div₀, map_sub, map_one, conj_conj]
  field_simp [hzero, hc]

/-- Exact pullback formula for an arbitrary fixed Hermitian reading.  Cartier
transport changes only the diagonal terms; the entire mixed coefficient is
conserved. -/
theorem routeRFixedHermitianHeadReading_transport
    {rho : ℂ} (hzero : rho ≠ 0) (hone : rho ≠ 1)
    (A B : ℝ) (C : ℂ) (z : RouteRCartierHeadPlane) :
    routeRFixedHermitianHeadReading A B C
        (routeRCartierHeadTransport rho z) -
      routeRFixedHermitianHeadReading A B C z =
    A * (Complex.normSq (burnolCartierForwardHeadGain rho) - 1) *
        Complex.normSq z.1 +
      B * (Complex.normSq (burnolCartierCosineHeadGain rho) - 1) *
        Complex.normSq z.2 := by
  have hcross :=
    conj_burnolCartierForwardHeadGain_mul_cosineHeadGain hzero hone
  rw [routeRFixedHermitianHeadReading, routeRFixedHermitianHeadReading,
    routeRCartierHeadTransport, Complex.normSq_mul, Complex.normSq_mul]
  simp only [map_mul]
  have hmix :
      (conj (burnolCartierForwardHeadGain rho) * conj z.1 * C *
          (burnolCartierCosineHeadGain rho * z.2)).re =
        (conj z.1 * C * z.2).re := by
    congr 1
    calc
      conj (burnolCartierForwardHeadGain rho) * conj z.1 * C *
          (burnolCartierCosineHeadGain rho * z.2) =
          (conj (burnolCartierForwardHeadGain rho) *
            burnolCartierCosineHeadGain rho) * (conj z.1 * C * z.2) := by ring
      _ = conj z.1 * C * z.2 := by rw [hcross]; simp
  rw [hmix]
  ring

/-- C18: on the actual fixed vector and an orientation-symmetric reading, the
defect is independent of the mixed coefficient. -/
theorem routeRFixedOrientationSymmetricHermitianHeadReading_defect
    {rho : ℂ} (hzero : rho ≠ 0) (hone : rho ≠ 1)
    (A : ℝ) (C : ℂ) :
    routeRFixedHermitianHeadReading A A C
        (routeRCartierHeadTransport rho routeRFixedGammaHeadVector) -
      routeRFixedHermitianHeadReading A A C routeRFixedGammaHeadVector =
    A * ((Complex.normSq (burnolCartierForwardHeadGain rho) - 1) +
      (Real.log 2) ^ 2 *
        (Complex.normSq (burnolCartierCosineHeadGain rho) - 1)) := by
  rw [routeRFixedHermitianHeadReading_transport hzero hone]
  simp only [routeRFixedGammaHeadVector, Complex.normSq_one,
    Complex.normSq_ofReal]
  ring

/-- C18, strict form: every fixed orientation-symmetric Hermitian reading with
positive diagonal strictly amplifies on the literal physical heads of a
hypothetical right-half Xi divisor.  Its mixed coefficient is arbitrary. -/
theorem xiDivisor_routeRFixedOrientationSymmetricHermitianHeadReading_strictly_amplifies
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {A : ℝ} (hA : 0 < A) (C : ℂ) :
    routeRFixedHermitianHeadReading A A C routeRFixedGammaHeadVector <
      routeRFixedHermitianHeadReading A A C
        (routeRCartierHeadTransport (rho : ℂ) routeRFixedGammaHeadVector) := by
  have hzero : (rho : ℂ) ≠ 0 := by
    intro h
    rw [h] at hright
    norm_num at hright
  have hone : (rho : ℂ) ≠ 1 := by
    intro h
    have hlt := xiDivisor_re_lt_one_of_half_lt rho hright
    rw [h] at hlt
    norm_num at hlt
  rw [sub_pos.symm,
    routeRFixedOrientationSymmetricHermitianHeadReading_defect hzero hone]
  have hbase :=
    xiDivisor_burnolCartierZeroTransfer_strictly_amplifies_gammaHeadEnergy rho hright
  rw [burnolSoninGammaHeadEnergy_fixedSubWindowSourceAtom,
    xiDivisor_burnolSoninGammaHeadEnergy_cartierZeroTransfer rho hright] at hbase
  have hcore :
      0 < (Complex.normSq (burnolCartierForwardHeadGain (rho : ℂ)) - 1) +
        (Real.log 2) ^ 2 *
          (Complex.normSq (burnolCartierCosineHeadGain (rho : ℂ)) - 1) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    linarith
  exact mul_pos hA hcore

/-- Right-half literal Cartier transport cannot conserve a nonzero forward
diagonal coefficient on the whole fixed fibre. -/
theorem xiDivisor_routeRFixedHermitianHeadReading_conserved_forall_forces_forward_zero
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {A B : ℝ} {C : ℂ}
    (hconserved : ∀ z : RouteRCartierHeadPlane,
      routeRFixedHermitianHeadReading A B C
          (routeRCartierHeadTransport (rho : ℂ) z) =
        routeRFixedHermitianHeadReading A B C z) :
    A = 0 := by
  have h := hconserved (1, 0)
  rw [routeRFixedHermitianHeadReading, routeRFixedHermitianHeadReading,
    routeRCartierHeadTransport] at h
  simp only [mul_one, mul_zero, Complex.normSq_zero, Complex.normSq_one,
    map_zero, zero_mul, add_zero] at h
  have hgain : 1 < Complex.normSq (burnolCartierForwardHeadGain (rho : ℂ)) := by
    rw [← Complex.sq_norm]
    have := one_lt_norm_burnolCartierForwardHeadGain hright
      (xiDivisor_re_lt_one_of_half_lt rho hright)
    nlinarith [norm_nonneg (burnolCartierForwardHeadGain (rho : ℂ))]
  nlinarith

/-- Right-half literal Cartier transport cannot conserve a nonzero reciprocal
diagonal coefficient on the whole fixed fibre. -/
theorem xiDivisor_routeRFixedHermitianHeadReading_conserved_forall_forces_cosine_zero
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    {A B : ℝ} {C : ℂ}
    (hconserved : ∀ z : RouteRCartierHeadPlane,
      routeRFixedHermitianHeadReading A B C
          (routeRCartierHeadTransport (rho : ℂ) z) =
        routeRFixedHermitianHeadReading A B C z) :
    B = 0 := by
  have h := hconserved (0, 1)
  rw [routeRFixedHermitianHeadReading, routeRFixedHermitianHeadReading,
    routeRCartierHeadTransport] at h
  simp only [mul_one, mul_zero, Complex.normSq_zero, Complex.normSq_one,
    map_zero, zero_mul, add_zero] at h
  have hgain : Complex.normSq (burnolCartierCosineHeadGain (rho : ℂ)) < 1 := by
    rw [← Complex.sq_norm]
    have := norm_burnolCartierCosineHeadGain_lt_one hright
      (xiDivisor_re_lt_one_of_half_lt rho hright)
    nlinarith [norm_nonneg (burnolCartierCosineHeadGain (rho : ℂ))]
  nlinarith

/-- C20: complete classification on the actual right-half Xi fibre.  A fixed
Hermitian reading is Cartier-conserved for every vector exactly when both
diagonal coefficients vanish.  The surviving family is the split,
sign-indefinite off-diagonal source form. -/
theorem xiDivisor_routeRFixedHermitianHeadReading_conserved_forall_iff
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re)
    (A B : ℝ) (C : ℂ) :
    (∀ z : RouteRCartierHeadPlane,
      routeRFixedHermitianHeadReading A B C
          (routeRCartierHeadTransport (rho : ℂ) z) =
        routeRFixedHermitianHeadReading A B C z) ↔
      A = 0 ∧ B = 0 := by
  constructor
  · intro h
    exact
      ⟨xiDivisor_routeRFixedHermitianHeadReading_conserved_forall_forces_forward_zero
          rho hright h,
        xiDivisor_routeRFixedHermitianHeadReading_conserved_forall_forces_cosine_zero
          rho hright h⟩
  · rintro ⟨rfl, rfl⟩ z
    have hzero : (rho : ℂ) ≠ 0 := by
      intro h
      rw [h] at hright
      norm_num at hright
    have hone : (rho : ℂ) ≠ 1 := by
      intro h
      have hlt := xiDivisor_re_lt_one_of_half_lt rho hright
      rw [h] at hlt
      norm_num at hlt
    have hdef := routeRFixedHermitianHeadReading_transport hzero hone
      0 0 C z
    simp only [zero_mul, zero_add] at hdef
    linarith

/-- C21: the closed Cartier/orientation-reversal loop is projectively scalar
for every complex parameter.  Thus projective flatness carries no horizontal
annihilation information. -/
theorem routeRCartierHeadTransport_swap_loop_projectively_flat
    (rho : ℂ) (z : RouteRCartierHeadPlane) :
    routeRCartierHeadTransport rho
        (routeRCartierHeadSwap
          (routeRCartierHeadTransport rho (routeRCartierHeadSwap z))) =
      (burnolCartierForwardHeadGain rho *
        burnolCartierCosineHeadGain rho) • z := by
  apply Prod.ext <;>
    simp only [routeRCartierHeadTransport, routeRCartierHeadSwap,
      Prod.fst, Prod.snd, Prod.smul_fst, Prod.smul_snd]
  · ring
  · ring

/-- Nontrivial projectively-flat boost witness.  Projective loop flatness does
not force the literal Cartier transport to be the identity. -/
theorem exists_routeRCartier_projectivelyFlat_nontrivial :
    ∃ rho : ℂ,
      (∀ z : RouteRCartierHeadPlane,
        routeRCartierHeadTransport rho
            (routeRCartierHeadSwap
              (routeRCartierHeadTransport rho (routeRCartierHeadSwap z))) =
          (burnolCartierForwardHeadGain rho *
            burnolCartierCosineHeadGain rho) • z) ∧
      routeRCartierHeadTransport rho (1, 0) ≠ (1, 0) := by
  refine ⟨(3 / 4 : ℂ), routeRCartierHeadTransport_swap_loop_projectively_flat _, ?_⟩
  have hgain : burnolCartierForwardHeadGain (3 / 4 : ℂ) = 3 := by
    apply Complex.ext <;>
      norm_num [burnolCartierForwardHeadGain, Complex.div_re, Complex.div_im]
  intro h
  have hf := congrArg Prod.fst h
  simp only [routeRCartierHeadTransport, hgain, mul_one] at hf
  norm_num at hf

end RHTower
