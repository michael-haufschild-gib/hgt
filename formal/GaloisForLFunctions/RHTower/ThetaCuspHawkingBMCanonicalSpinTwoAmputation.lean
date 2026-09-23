import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompletedBalancedSpinTwoFirstLiveJet

/-!
# Canonical analytic amputation of the completed spin-two source

At the actual repeated Eisenstein parameter `s=2`, the completed balanced vertex in the
spectral coordinate `z` is exactly `XiC(z)^(2 : ℕ) * U(z)`, where

`U(z) = ((4z^(2 : ℕ)+1)(4z^(2 : ℕ)+25)/32) XiC(z-3i) XiC(-z-3i)`.

This is the unique entire quotient, defined without a zero copy, multiplicity, or prescribed
response. In the strip `-5/2 < Im z < 5/2` its only zeros are the two geometric points
`z=±i/2`. Consequently it is an analytic unit on the physical Xi strip, and is strictly
positive on the real axis. Both geometric zeros are simple, so the inverse source has exact
pole order `-1` there. Every first-live vertex jet divided by the corresponding
external-square jet recovers this same source.

The removed external factor is retained in the exact factorization: the unamputated vertex
has the same zero locus as XiC, with doubled order, in the physical strip. Analytic amputation
therefore constructs a source normalization and does not remove or restrict the Xi divisor.
It supplies no causal radial operator, left-QNM incidence, or extinction law.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The entire external-leg quotient at the actual repeated Eisenstein parameter. No Xi
copy, zero multiplicity, or target response enters its definition. -/
def d4BMCanonicalSpinTwoAmputatedSource (z : ℂ) : ℂ :=
  d4BMCompletedBalancedSpinTwoProjectingSideFactor
    d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * z)

/-- Explicit polynomial and two shifted-Xi factors of the canonical amputated source. -/
theorem d4BMCanonicalSpinTwoAmputatedSource_eq (z : ℂ) :
    d4BMCanonicalSpinTwoAmputatedSource z =
      ((4 * z ^ (2 : ℕ) + 1) * (4 * z ^ (2 : ℕ) + 25) / 32) *
        XiC (z - 3 * Complex.I) * XiC (-z - 3 * Complex.I) := by
  unfold d4BMCanonicalSpinTwoAmputatedSource d4BMCompletedBalancedSpinTwoProjectingSideFactor
  rw [thetaCuspHawkingBalancedSpinTwoBochnerCoefficient_actualRepeated_projecting_factorization]
  unfold thetaCuspHawkingCompletedEisensteinXiFactor
    d4BMActualRepeatedEisensteinCenteredParameter
  have hplus : -Complex.I * (2 * (3 / 2 : ℂ) + Complex.I * z) =
      z - 3 * Complex.I := by
    calc
      _ = -3 * Complex.I - (Complex.I * Complex.I) * z := by ring
      _ = z - 3 * Complex.I := by rw [Complex.I_mul_I]; ring
  have hminus : -Complex.I * (2 * (3 / 2 : ℂ) - Complex.I * z) =
      -z - 3 * Complex.I := by
    calc
      _ = -3 * Complex.I + (Complex.I * Complex.I) * z := by ring
      _ = -z - 3 * Complex.I := by rw [Complex.I_mul_I]; ring
  rw [hplus, hminus]

/-- The canonical amputation is entire, including every projecting Xi zero. -/
theorem analyticAt_d4BMCanonicalSpinTwoAmputatedSource (z : ℂ) :
    AnalyticAt ℂ d4BMCanonicalSpinTwoAmputatedSource z := by
  exact (analyticAt_d4BMCompletedBalancedSpinTwoProjectingSideFactor
    d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * z)).comp (by fun_prop)

/-- Exact source factorization before any divisor specialization. -/
theorem d4BMCompletedSpinTwoVertex_eq_XiC_sq_mul_canonicalSource (z : ℂ) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
        d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * z) =
      XiC z ^ (2 : ℕ) * d4BMCanonicalSpinTwoAmputatedSource z := by
  rw [thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_eq_externalSquare_mul_side]
  have hx : thetaCuspHawkingCompletedEisensteinXiFactor (Complex.I * z) = XiC z := by
    unfold thetaCuspHawkingCompletedEisensteinXiFactor
    congr 1
    calc
      -Complex.I * (Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
      _ = z := by rw [Complex.I_mul_I]; ring
  simp only [d4BMCompletedEisensteinProjectingExternalSquare, hx,
    d4BMCanonicalSpinTwoAmputatedSource, pow_two]

/-- Off the external zero set, ordinary division agrees with the entire amputation. -/
theorem d4BMCompletedSpinTwoVertex_div_XiC_sq
    (z : ℂ) (hz : XiC z ≠ 0) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
        d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * z) / XiC z ^ (2 : ℕ) =
      d4BMCanonicalSpinTwoAmputatedSource z := by
  rw [d4BMCompletedSpinTwoVertex_eq_XiC_sq_mul_canonicalSource]
  field_simp

/-- Uniqueness is global analytic uniqueness, rather than pointwise division at zeros. -/
theorem d4BMCanonicalSpinTwoAmputation_existsUnique :
    ∃! source : ℂ → ℂ, AnalyticOnNhd ℂ source Set.univ ∧
      ∀ z : ℂ, thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
          d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * z) =
        XiC z ^ (2 : ℕ) * source z := by
  refine ⟨d4BMCanonicalSpinTwoAmputatedSource,
    ⟨fun z _ => analyticAt_d4BMCanonicalSpinTwoAmputatedSource z,
      d4BMCompletedSpinTwoVertex_eq_XiC_sq_mul_canonicalSource⟩, ?_⟩
  rintro source ⟨hsource, hfactor⟩
  apply hsource.eq_of_eventuallyEq
    (fun z _ => analyticAt_d4BMCanonicalSpinTwoAmputatedSource z)
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), XiC z ≠ 0 :=
    XiC_differentiable.continuous.continuousAt.eventually_ne XiC_zero_ne
  filter_upwards [hnear] with z hz
  exact mul_left_cancel₀ (pow_ne_zero 2 hz)
    ((hfactor z).symm.trans (d4BMCompletedSpinTwoVertex_eq_XiC_sq_mul_canonicalSource z))

private theorem spinTwo_quadratic_roots (z c : ℂ) :
    4 * z ^ (2 : ℕ) + c ^ (2 : ℕ) = 0 ↔
      z = c * Complex.I / 2 ∨ z = -c * Complex.I / 2 := by
  have hfactor : 4 * z ^ (2 : ℕ) + c ^ (2 : ℕ) =
      (2 * z - c * Complex.I) * (2 * z + c * Complex.I) := by
    calc
      _ = 4 * z ^ (2 : ℕ) - c ^ (2 : ℕ) * (Complex.I * Complex.I) := by
        rw [Complex.I_mul_I]; ring
      _ = _ := by ring
  rw [hfactor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linear_combination (1 / 2 : ℂ) * h
    · right; linear_combination (1 / 2 : ℂ) * h
  · rintro (rfl | rfl)
    · left; ring
    · right; ring

/-- Both shifted Xi factors are nonzero on a larger strip, independently of the projecting
Xi value. -/
theorem d4BMCanonicalSpinTwoAmputation_shiftedFactors_ne_zero
    (z : ℂ) (hz : -(5 / 2 : ℝ) < z.im ∧ z.im < 5 / 2) :
    XiC (z - 3 * Complex.I) ≠ 0 ∧ XiC (-z - 3 * Complex.I) ≠ 0 := by
  constructor
  · apply XiC_ne_zero_of_im_lt_neg_half
    norm_num [Complex.sub_im, Complex.mul_im]
    linarith [hz.2]
  · apply XiC_ne_zero_of_im_lt_neg_half
    norm_num [Complex.sub_im, Complex.neg_im, Complex.mul_im]
    linarith [hz.1]

/-- Exact zero set of the amputated source in the larger strip. The two surviving zeros are
geometric boundary points of the physical Xi strip. -/
theorem d4BMCanonicalSpinTwoAmputatedSource_eq_zero_iff
    (z : ℂ) (hz : -(5 / 2 : ℝ) < z.im ∧ z.im < 5 / 2) :
    d4BMCanonicalSpinTwoAmputatedSource z = 0 ↔
      z = Complex.I / 2 ∨ z = -Complex.I / 2 := by
  obtain ⟨hplus, hminus⟩ := d4BMCanonicalSpinTwoAmputation_shiftedFactors_ne_zero z hz
  rw [d4BMCanonicalSpinTwoAmputatedSource_eq, mul_eq_zero, mul_eq_zero]
  simp only [hplus, hminus, or_false]
  have hden : (32 : ℂ) ≠ 0 := by norm_num
  rw [div_eq_zero_iff, or_iff_left hden, mul_eq_zero]
  have hfirst := spinTwo_quadratic_roots z 1
  have hsecond := spinTwo_quadratic_roots z 5
  norm_num only [one_pow, one_mul, neg_mul, OfNat.ofNat, show (5 : ℂ) ^ (2 : ℕ) = 25 by norm_num]
    at hfirst hsecond
  rw [hfirst, hsecond]
  constructor
  · rintro (h | h | h)
    · exact h
    · subst z; norm_num at hz
    · subst z; norm_num at hz
  · intro h
    exact Or.inl h

/-- Canonical source is a unit at every point of the physical strip, not only at Xi copies. -/
theorem d4BMCanonicalSpinTwoAmputatedSource_ne_zero
    (z : ℂ) (hz : -(1 / 2 : ℝ) < z.im ∧ z.im < 1 / 2) :
    d4BMCanonicalSpinTwoAmputatedSource z ≠ 0 := by
  intro hzero
  have hwide : -(5 / 2 : ℝ) < z.im ∧ z.im < 5 / 2 := by
    constructor <;> linarith [hz.1, hz.2]
  rcases (d4BMCanonicalSpinTwoAmputatedSource_eq_zero_iff z hwide).1 hzero with h | h
  · subst z; norm_num at hz
  · subst z; norm_num at hz

/-- The source-normalizing inverse is analytic on the entire physical Xi strip. -/
theorem analyticAt_inv_d4BMCanonicalSpinTwoAmputatedSource
    (z : ℂ) (hz : -(1 / 2 : ℝ) < z.im ∧ z.im < 1 / 2) :
    AnalyticAt ℂ (fun w => (d4BMCanonicalSpinTwoAmputatedSource w)⁻¹) z := by
  exact (analyticAt_d4BMCanonicalSpinTwoAmputatedSource z).inv
    (d4BMCanonicalSpinTwoAmputatedSource_ne_zero z hz)

/-- The two shifted factors pair as an exact positive square on the real axis. -/
theorem d4BMCanonicalSpinTwoAmputatedSource_ofReal (x : ℝ) :
    d4BMCanonicalSpinTwoAmputatedSource (x : ℂ) =
      ((((4 * x ^ (2 : ℕ) + 1) * (4 * x ^ (2 : ℕ) + 25) / 32) *
        Complex.normSq (XiC ((x : ℂ) - 3 * Complex.I)) : ℝ) : ℂ) := by
  have hpair : XiC (-(x : ℂ) - 3 * Complex.I) =
      (starRingEnd ℂ) (XiC ((x : ℂ) - 3 * Complex.I)) := by
    rw [show -(x : ℂ) - 3 * Complex.I = -((x : ℂ) + 3 * Complex.I) by ring,
      XiC_even, ← XiC_conj]
    congr 1
    norm_num
    exact (map_ofNat (starRingEnd ℂ) 3).symm
  rw [d4BMCanonicalSpinTwoAmputatedSource_eq, hpair, mul_assoc, Complex.mul_conj]
  push_cast
  rfl

/-- Strict positivity is unconditional at every real spectral parameter. -/
theorem d4BMCanonicalSpinTwoAmputatedSource_re_pos (x : ℝ) :
    0 < (d4BMCanonicalSpinTwoAmputatedSource (x : ℂ)).re := by
  rw [d4BMCanonicalSpinTwoAmputatedSource_ofReal, Complex.ofReal_re]
  have hshift := (d4BMCanonicalSpinTwoAmputation_shiftedFactors_ne_zero
    (x : ℂ) (by norm_num)).1
  have hnorm := Complex.normSq_pos.mpr hshift
  positivity

/-- Normalizing the first-live jet removes exactly the external-square leading coefficient
and recovers the same predeclared entire source for every multiplicity. -/
theorem d4BMFirstLiveSpinTwoJet_div_externalJet_eq_canonicalSource (q : XiZeroCopy) :
    d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet q /
      iteratedDeriv (2 * d4BMXiProjectingLegMultiplicity q)
        d4BMCompletedEisensteinProjectingExternalSquare
        (d4BMXiProjectingEisensteinCenteredParameter q) =
      d4BMCanonicalSpinTwoAmputatedSource (xiSpectralPoint q) := by
  unfold d4BMActualMultiplicityMatchedCompletedBalancedSpinTwoAngularJet
  rw [iteratedDeriv_thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex_at_twiceMultiplicity]
  have hne := iteratedDeriv_d4BMCompletedEisensteinProjectingExternalSquare_ne_zero q
  unfold d4BMCanonicalSpinTwoAmputatedSource d4BMXiProjectingEisensteinCenteredParameter at *
  field_simp

/-- Amputation retains the unresolved Xi divisor explicitly: in the physical strip, the
unamputated vertex vanishes exactly where XiC vanishes. -/
theorem d4BMCompletedSpinTwoVertex_eq_zero_iff_XiC
    (z : ℂ) (hz : -(1 / 2 : ℝ) < z.im ∧ z.im < 1 / 2) :
    thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
        d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * z) = 0 ↔
      XiC z = 0 := by
  rw [d4BMCompletedSpinTwoVertex_eq_XiC_sq_mul_canonicalSource, mul_eq_zero,
    or_iff_left (d4BMCanonicalSpinTwoAmputatedSource_ne_zero z hz), pow_eq_zero_iff (by omega)]

/-- Exact preservation of multiplicity: every vertex order in the physical strip is twice
its Xi order. The analytic normalization contributes zero order. -/
theorem analyticOrderAt_d4BMCompletedSpinTwoVertex
    (z : ℂ) (hz : -(1 / 2 : ℝ) < z.im ∧ z.im < 1 / 2) :
    analyticOrderAt (fun w => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
      d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * w)) z =
      2 • analyticOrderAt XiC z := by
  have hfun : (fun w => thetaCuspHawkingCompletedBalancedSpinTwoEisensteinVertex
      d4BMActualRepeatedEisensteinCenteredParameter (Complex.I * w)) =
        XiC ^ (2 : ℕ) * d4BMCanonicalSpinTwoAmputatedSource := by
    funext w
    exact d4BMCompletedSpinTwoVertex_eq_XiC_sq_mul_canonicalSource w
  rw [hfun, analyticOrderAt_mul ((XiC_analytic z (Set.mem_univ z)).pow 2)
    (analyticAt_d4BMCanonicalSpinTwoAmputatedSource z),
    analyticOrderAt_pow (XiC_analytic z (Set.mem_univ z)),
    (analyticAt_d4BMCanonicalSpinTwoAmputatedSource z).analyticOrderAt_eq_zero.2
      (d4BMCanonicalSpinTwoAmputatedSource_ne_zero z hz), add_zero]

/-- At either geometric boundary root, the derivative is the explicit nonzero polynomial
slope times the two shifted source factors. -/
theorem hasDerivAt_d4BMCanonicalSpinTwoAmputatedSource_geometricBoundary
    (z : ℂ) (hz : 4 * z ^ (2 : ℕ) + 1 = 0) :
    HasDerivAt d4BMCanonicalSpinTwoAmputatedSource
      (6 * z * XiC (z - 3 * Complex.I) * XiC (-z - 3 * Complex.I)) z := by
  let P : ℂ → ℂ := fun w => (4 * w ^ (2 : ℕ) + 1) * (4 * w ^ (2 : ℕ) + 25) / 32
  have hp : HasDerivAt P (6 * z) z := by
    have hraw : HasDerivAt P
        (((4 * (2 * z)) * (4 * z ^ (2 : ℕ) + 25) + (4 * z ^ (2 : ℕ) + 1) * (4 * (2 * z))) / 32) z := by
      simpa [P] using
        (((((hasDerivAt_id z).pow 2).const_mul 4).add_const 1).mul
          ((((hasDerivAt_id z).pow 2).const_mul 4).add_const 25)).div_const 32
    have heq : ((4 * (2 * z)) * (4 * z ^ (2 : ℕ) + 25) + (4 * z ^ (2 : ℕ) + 1) * (4 * (2 * z))) / 32 =
        6 * z := by
      linear_combination (z / 2) * hz
    rw [heq] at hraw
    exact hraw
  have hpzero : P z = 0 := by simp [P, hz]
  have hplus : AnalyticAt ℂ (fun w => XiC (w - 3 * Complex.I)) z :=
    (XiC_analytic _ (Set.mem_univ _)).comp (by fun_prop)
  have hminus : AnalyticAt ℂ (fun w => XiC (-w - 3 * Complex.I)) z :=
    (XiC_analytic _ (Set.mem_univ _)).comp (by fun_prop)
  have hprod := (hp.mul hplus.differentiableAt.hasDerivAt).mul
    hminus.differentiableAt.hasDerivAt
  have hfun : d4BMCanonicalSpinTwoAmputatedSource =
      (P * (fun w => XiC (w - 3 * Complex.I))) *
        (fun w => XiC (-w - 3 * Complex.I)) := by
    funext w
    exact d4BMCanonicalSpinTwoAmputatedSource_eq w
  rw [hfun]
  simpa only [Pi.mul_apply, hpzero, zero_mul, add_zero] using hprod

/-- The geometric boundary zeros are simple. This is independent of all Xi-copy data. -/
theorem analyticOrderAt_d4BMCanonicalSpinTwoAmputatedSource_geometricBoundary
    (z : ℂ) (hz : 4 * z ^ (2 : ℕ) + 1 = 0) :
    analyticOrderAt d4BMCanonicalSpinTwoAmputatedSource z = 1 := by
  have hzroot : z = Complex.I / 2 ∨ z = -Complex.I / 2 := by
    simpa using (spinTwo_quadratic_roots z 1).1 (by simpa using hz)
  have hwide : -(5 / 2 : ℝ) < z.im ∧ z.im < 5 / 2 := by
    rcases hzroot with rfl | rfl <;> norm_num
  have hzne : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  obtain ⟨hplus, hminus⟩ := d4BMCanonicalSpinTwoAmputation_shiftedFactors_ne_zero z hwide
  apply (analyticAt_d4BMCanonicalSpinTwoAmputatedSource z).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · exact (d4BMCanonicalSpinTwoAmputatedSource_eq_zero_iff z hwide).2 hzroot
  · rw [(hasDerivAt_d4BMCanonicalSpinTwoAmputatedSource_geometricBoundary z hz).deriv]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hzne) hplus) hminus

/-- The inverse source normalization has exact simple poles at both fixed geometric
boundary points. Its singularity is source-defined before divisor selection. -/
theorem meromorphicOrderAt_inv_d4BMCanonicalSpinTwoAmputatedSource_geometricBoundary
    (z : ℂ) (hz : 4 * z ^ (2 : ℕ) + 1 = 0) :
    meromorphicOrderAt (fun w => (d4BMCanonicalSpinTwoAmputatedSource w)⁻¹) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt d4BMCanonicalSpinTwoAmputatedSource⁻¹ z = _
  rw [meromorphicOrderAt_inv,
    (analyticAt_d4BMCanonicalSpinTwoAmputatedSource z).meromorphicOrderAt_eq,
    analyticOrderAt_d4BMCanonicalSpinTwoAmputatedSource_geometricBoundary z hz]
  norm_num

end

end RHTower
