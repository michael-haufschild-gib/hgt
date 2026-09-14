import GaloisForLFunctions.Hurwitz.PolygammaHurwitzValue
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse

/-!
# Xi prime seams from finite rational Hurwitz fibres

The Hurwitz distribution relation can be shifted one unit into the half-plane of absolute
convergence and divided by its nonzero base value.  The resulting finite rational-fibre response
recovers `n^s` exactly for every exponent with positive real part.

Applying this response to the Schwarz and functional-equation reflections of an open-strip point
rewrites every canonical prime seam as a difference of two finite Hurwitz value packets.  In
particular, the common first-prime charge is carried by the two-point fibre `{1/2, 1}` at exponents
`conj rho + 1` and `2 - rho`; all four Hurwitz values lie in their defining convergence half-plane.

This is a source-value bridge, not a proof that the reflected packets agree.  Its positive content
is that no continuation at a zero, divisor enumeration, or asymptotic coefficient extraction is
needed to state the remaining equality.
-/

open Complex
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The normalized finite rational Hurwitz fibre at exponent `s + 1`.

For `n > 0` and `0 < Re s`, every Hurwitz value and the Riemann-zeta denominator are represented
by absolutely convergent Dirichlet series. -/
def rationalHurwitzFiberResponse (n : ℕ) (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.range n,
      HurwitzZetaShift.hzeta (s + 1)
        (((1 : ℂ) + (k : ℕ)) / (n : ℕ))) /
    ((n : ℂ) * riemannZeta (s + 1))

/-- At modulus two the response is the explicit normalized packet at the rational points
`1 / 2` and `1`. -/
theorem rationalHurwitzFiberResponse_two (s : ℂ) :
    rationalHurwitzFiberResponse 2 s =
      (HurwitzZetaShift.hzeta (s + 1) (1 / 2 : ℂ) +
        HurwitzZetaShift.hzeta (s + 1) 1) /
        (2 * riemannZeta (s + 1)) := by
  simp [rationalHurwitzFiberResponse, Finset.sum_range_succ]

/-- **Finite rational-fibre response law.**  The normalized fibre recovers `n^s` exactly. -/
theorem rationalHurwitzFiberResponse_eq_cpow
    {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 0 < s.re) :
    rationalHurwitzFiberResponse n s = (n : ℂ) ^ s := by
  have hs1 : 1 < (s + 1).re := lt_add_of_pos_left 1 hs
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hz : riemannZeta (s + 1) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs1
  rw [rationalHurwitzFiberResponse,
    hzeta_distribution hs1 hn (1 : ℂ),
    hzeta_one_eq_riemannZeta hs1]
  rw [Complex.cpow_add _ _ hnC, Complex.cpow_one, mul_assoc,
    mul_div_cancel_right₀ _ (mul_ne_zero hnC hz)]

/-- The FE--Schwarz seam written only with finite rational Hurwitz fibre responses. -/
def rationalHurwitzFiberReflectionSeam (n : ℕ) (rho : ℂ) : ℂ :=
  (Real.log n : ℂ) *
    ((rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho))⁻¹ -
      (rationalHurwitzFiberResponse n (1 - rho))⁻¹)

/-- **Finite-value realization of every scale seam.**  On the open strip, the rational-Hurwitz
fibre defect is exactly the previously isolated FE--Schwarz seam charge. -/
theorem rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge
    {n : ℕ} (hn : 0 < n) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    rationalHurwitzFiberReflectionSeam n rho =
      orbitwiseNatPrimeSeamCharge n rho := by
  have hconj : 0 < ((starRingEnd ℂ) rho).re := hstrip.1
  have href : 0 < (1 - rho).re := sub_pos.mpr hstrip.2
  rw [rationalHurwitzFiberReflectionSeam,
    rationalHurwitzFiberResponse_eq_cpow hn hconj,
    rationalHurwitzFiberResponse_eq_cpow hn href,
    ← Complex.cpow_neg, ← Complex.cpow_neg]
  rfl

/-- A single nontrivial rational fibre is reflection-fixed exactly on the critical line.  The
forward direction uses only equality of norms and strict monotonicity of real powers. -/
theorem rationalHurwitzFiberResponse_reflection_fixed_iff
    {n : ℕ} (hn : 1 < n) {rho : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1) :
    rationalHurwitzFiberResponse n ((starRingEnd ℂ) rho) =
        rationalHurwitzFiberResponse n (1 - rho) ↔
      rho.re = 1 / 2 := by
  have hn0 : 0 < n := Nat.zero_lt_one.trans hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hconj : 0 < ((starRingEnd ℂ) rho).re := hstrip.1
  have href : 0 < (1 - rho).re := sub_pos.mpr hstrip.2
  rw [rationalHurwitzFiberResponse_eq_cpow hn0 hconj,
    rationalHurwitzFiberResponse_eq_cpow hn0 href]
  constructor
  · intro h
    have hnorm := congrArg norm h
    have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn0
    change ‖((n : ℝ) : ℂ) ^ (starRingEnd ℂ) rho‖ =
      ‖((n : ℝ) : ℂ) ^ (1 - rho)‖ at hnorm
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnR0,
      Complex.norm_cpow_eq_rpow_re_of_pos hnR0] at hnorm
    have hre : ((starRingEnd ℂ) rho).re = (1 - rho).re :=
      (Real.strictMono_rpow_of_base_gt_one hnR).injective hnorm
    simp only [Complex.conj_re, Complex.sub_re, Complex.one_re] at hre
    linarith only [hre]
  · intro hre
    have hfixed : (starRingEnd ℂ) rho = 1 - rho := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.sub_re, Complex.one_re]
        linarith only [hre]
      · simp only [Complex.conj_im, Complex.sub_im, Complex.one_im, zero_sub]
    rw [hfixed]

/-- The common first-prime seam is exactly the finite two-point Hurwitz fibre defect. -/
theorem rationalHurwitzFiberTwoReflectionSeam_eq_firstPrimeSeamCharge
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    rationalHurwitzFiberReflectionSeam 2 rho =
      orbitwiseFirstPrimeSeamCharge rho := by
  rw [rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge (by norm_num) hstrip,
    orbitwiseNatPrimeSeamCharge_two_eq_firstPrime]

/-- Vanishing of the common first-prime charge is exactly equality of the two convergent
two-point Hurwitz fibre responses. -/
theorem rationalHurwitzFiberTwo_reflection_fixed_iff_firstPrimeSeamCharge_eq_zero
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    rationalHurwitzFiberResponse 2 ((starRingEnd ℂ) rho) =
        rationalHurwitzFiberResponse 2 (1 - rho) ↔
      orbitwiseFirstPrimeSeamCharge rho = 0 := by
  rw [rationalHurwitzFiberResponse_reflection_fixed_iff (by norm_num) hstrip,
    orbitwiseFirstPrimeSeamCharge_eq_zero_iff]

/-- Every Xi-divisor fibre has reflection-equal finite Hurwitz responses on `{1/2, 1}`. -/
def XiRationalHurwitzFiberTwoReflectionFixed : Prop :=
  ∀ rho : XiDivisorSupport,
    rationalHurwitzFiberResponse 2 ((starRingEnd ℂ) (rho : ℂ)) =
      rationalHurwitzFiberResponse 2 (1 - (rho : ℂ))

/-- The finite rational-Hurwitz value relation is exactly the already isolated common-charge
assertion over the complete Xi divisor. -/
theorem xiRationalHurwitzFiberTwoReflectionFixed_iff_firstPrimeSeamChargesVanish :
    XiRationalHurwitzFiberTwoReflectionFixed ↔ XiFirstPrimeSeamChargesVanish := by
  constructor
  · intro h rho
    exact
      (rationalHurwitzFiberTwo_reflection_fixed_iff_firstPrimeSeamCharge_eq_zero
        (xi_divisor_support_re_mem_open_unit rho)).mp (h rho)
  · intro h rho
    exact
      (rationalHurwitzFiberTwo_reflection_fixed_iff_firstPrimeSeamCharge_eq_zero
        (xi_divisor_support_re_mem_open_unit rho)).mpr (h rho)

/-- **Finite-value chain to RH.**  Equality of the two absolutely convergent rational-Hurwitz
packets at every Xi divisor point implies the Riemann hypothesis. -/
theorem riemannHypothesis_of_xiRationalHurwitzFiberTwoReflectionFixed
    (h : XiRationalHurwitzFiberTwoReflectionFixed) : RiemannHypothesis := by
  apply riemannHypothesis_of_xiPrimeSeamChargesCoherent
  apply xiPrimeSeamChargesCoherent_iff_firstPrimeSeamChargesVanish.mpr
  exact xiRationalHurwitzFiberTwoReflectionFixed_iff_firstPrimeSeamChargesVanish.mp h

/-- RH supplies the finite reflected-value identity, so the new source interface is exact. -/
theorem xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis :
    XiRationalHurwitzFiberTwoReflectionFixed ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiRationalHurwitzFiberTwoReflectionFixed
  · intro hRH rho
    apply (rationalHurwitzFiberResponse_reflection_fixed_iff (n := 2)
      (by norm_num) (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

end

end RHTower
