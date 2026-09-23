import GaloisForLFunctions.RHTower.CoshQuartetEnvelope
import GaloisForLFunctions.RHTower.CoshPolynomialPeriodClassification
import GaloisForLFunctions.RHTower.CoshPolynomialExactOrderOne
import GaloisForLFunctions.RHTower.SimultaneousFiniteJetFlatness
import GaloisForLFunctions.HTGeometry.ResidueFilledFluxGerm

/-!
# A real-even order-one realization with a delayed completed-flux defect

For every jet depth `N` this file constructs one entire function

```text
F_N(w) = cosh (w - π/2) · cosh (w + π/2) · (1 + (w⁴ + π⁴/4)^{2N+1}),
```

together with its functional-equation normalization `X_N(s) = F_N(-2πi(s - 1/2))`.  The four points
`α = π(1+i)/2`, `-α`, `conj α`, `-conj α` are simple zeros of `F_N`, and under the normalization
they become the quartet

```text
1/4 ± i/4 ,   3/4 ± i/4 ,
```

which lies strictly inside the critical strip, off the critical line and off the real axis.

`X_N` is real-even (`X_N(1-s) = X_N(s)` and `X_N(conj s) = conj X_N(s)`), has no real zeros, has
exact entire order one, and has no nonzero period.  At the two partner centres `-α` and `-conj α`,
whose difference `πi` is exactly one period of the envelope, the residue-filled completed-flux
germs have identical Taylor coefficients through order `N` and differ at the later odd order
`2N+1`.  Consequently no fixed finite completed-flux jet can be a critical-axis selector inside
this envelope.
-/

namespace RHTower

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The construction -/

/-- The displacement of the envelope. -/
def quartetShift : ℝ := Real.pi / 2

theorem quartetShift_ne_zero : quartetShift ≠ 0 := by
  simp only [quartetShift]
  positivity

/-- The entire envelope. -/
def gradedEnvelope (w : ℂ) : ℂ := coshQuartetEnvelope quartetShift w

/-- The selected quartet centre `α = π(1+i)/2`. -/
private def quartetPoint : ℂ := (Real.pi / 2 : ℝ) + (Real.pi / 2 : ℝ) * I

/-- The real even quartet polynomial `w⁴ + π⁴/4`, whose four roots are the quartet. -/
private def quartetPoly (w : ℂ) : ℂ := w ^ (4 : ℕ) + (Real.pi : ℂ) ^ (4 : ℕ) / 4

/-- The Hermite-flat multiplier of depth `N`. -/
def flatMultiplier (N : ℕ) (w : ℂ) : ℂ := 1 + quartetPoly w ^ (2 * N + 1)

/-- The realizing entire function. -/
def gradedRealityFn (N : ℕ) (w : ℂ) : ℂ := gradedEnvelope w * flatMultiplier N w

/-- Its functional-equation normalization. -/
def gradedRealityXi (N : ℕ) (s : ℂ) : ℂ :=
  gradedRealityFn N (-(2 * (Real.pi : ℂ) * I) * (s - 1 / 2))

/-! ## Symmetries -/

theorem quartetPoly_neg (w : ℂ) : quartetPoly (-w) = quartetPoly w := by
  simp only [quartetPoly]
  ring

theorem quartetPoly_conj (w : ℂ) :
    quartetPoly ((starRingEnd ℂ) w) = (starRingEnd ℂ) (quartetPoly w) := by
  simp only [quartetPoly, map_add, map_div₀, map_pow, Complex.conj_ofReal, map_ofNat]

theorem flatMultiplier_neg (N : ℕ) (w : ℂ) :
    flatMultiplier N (-w) = flatMultiplier N w := by
  simp [flatMultiplier, quartetPoly_neg]

theorem flatMultiplier_conj (N : ℕ) (w : ℂ) :
    flatMultiplier N ((starRingEnd ℂ) w) = (starRingEnd ℂ) (flatMultiplier N w) := by
  simp [flatMultiplier, quartetPoly_conj, map_add, map_pow]

theorem gradedRealityFn_neg (N : ℕ) (w : ℂ) :
    gradedRealityFn N (-w) = gradedRealityFn N w := by
  simp [gradedRealityFn, gradedEnvelope, coshQuartetEnvelope_neg, flatMultiplier_neg]

theorem gradedRealityFn_conj (N : ℕ) (w : ℂ) :
    gradedRealityFn N ((starRingEnd ℂ) w) = (starRingEnd ℂ) (gradedRealityFn N w) := by
  simp [gradedRealityFn, gradedEnvelope, coshQuartetEnvelope_conj, flatMultiplier_conj]

/-- **Functional equation.**  The normalization is symmetric about the critical line. -/
theorem gradedRealityXi_functional_equation (N : ℕ) (s : ℂ) :
    gradedRealityXi N (1 - s) = gradedRealityXi N s := by
  rw [gradedRealityXi, gradedRealityXi,
    show -(2 * (Real.pi : ℂ) * I) * ((1 - s) - 1 / 2)
      = -(-(2 * (Real.pi : ℂ) * I) * (s - 1 / 2)) by ring,
    gradedRealityFn_neg]

/-- **Schwarz reality.** -/
theorem gradedRealityXi_conj (N : ℕ) (s : ℂ) :
    gradedRealityXi N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (gradedRealityXi N s) := by
  have hw : -(2 * (Real.pi : ℂ) * I) * ((starRingEnd ℂ) s - 1 / 2)
      = -((starRingEnd ℂ) (-(2 * (Real.pi : ℂ) * I) * (s - 1 / 2))) := by
    simp only [map_neg, map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  rw [gradedRealityXi, hw, gradedRealityFn_neg, gradedRealityFn_conj, gradedRealityXi]

/-! ## The quartet and its simplicity -/

theorem quartetPoint_sq : quartetPoint ^ (2 : ℕ) = (Real.pi : ℂ) ^ (2 : ℕ) / 2 * I := by
  simp only [quartetPoint]
  push_cast
  rw [show ((Real.pi : ℂ) / 2 + (Real.pi : ℂ) / 2 * I) ^ (2 : ℕ)
      = (Real.pi : ℂ) ^ (2 : ℕ) / 4 * (1 + I ^ (2 : ℕ) + 2 * I) by ring, Complex.I_sq]
  ring

theorem quartetPoly_quartetPoint : quartetPoly quartetPoint = 0 := by
  have h : quartetPoint ^ (4 : ℕ) = (quartetPoint ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
  rw [quartetPoly, h, quartetPoint_sq,
    show ((Real.pi : ℂ) ^ (2 : ℕ) / 2 * I) ^ (2 : ℕ) = (Real.pi : ℂ) ^ (4 : ℕ) / 4 * I ^ (2 : ℕ) by ring,
    Complex.I_sq]
  ring

theorem quartetPoly_neg_quartetPoint : quartetPoly (-quartetPoint) = 0 := by
  rw [quartetPoly_neg, quartetPoly_quartetPoint]

theorem quartetPoly_conj_quartetPoint :
    quartetPoly ((starRingEnd ℂ) quartetPoint) = 0 := by
  rw [quartetPoly_conj, quartetPoly_quartetPoint, map_zero]

theorem quartetPoly_neg_conj_quartetPoint :
    quartetPoly (-((starRingEnd ℂ) quartetPoint)) = 0 := by
  rw [quartetPoly_neg, quartetPoly_conj_quartetPoint]

/-- The functional-equation partner centre `c = -α`. -/
def fePartnerCentre : ℂ := -quartetPoint

/-- The Schwarz partner centre `d = -conj α`; it differs from `c` by exactly one envelope
period. -/
def schwarzPartnerCentre : ℂ := -((starRingEnd ℂ) quartetPoint)

theorem quartetPoly_fePartnerCentre : quartetPoly fePartnerCentre = 0 :=
  quartetPoly_neg_quartetPoint

theorem quartetPoly_schwarzPartnerCentre : quartetPoly schwarzPartnerCentre = 0 :=
  quartetPoly_neg_conj_quartetPoint

theorem schwarzPartnerCentre_eq :
    schwarzPartnerCentre = fePartnerCentre + (Real.pi : ℂ) * I := by
  simp only [schwarzPartnerCentre, fePartnerCentre, quartetPoint]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem fePartnerCentre_add_shift : fePartnerCentre + (quartetShift : ℂ) = -((Real.pi : ℂ) / 2) * I := by
  simp only [fePartnerCentre, quartetPoint, quartetShift]
  push_cast
  ring

theorem schwarzPartnerCentre_add_shift :
    schwarzPartnerCentre + (quartetShift : ℂ) = ((Real.pi : ℂ) / 2) * I := by
  simp only [schwarzPartnerCentre, quartetPoint, quartetShift]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem fePartnerCentre_sub_shift_re :
    (fePartnerCentre - (quartetShift : ℂ)).re = -Real.pi := by
  simp only [fePartnerCentre, quartetPoint, quartetShift]
  push_cast
  simp
  ring

theorem schwarzPartnerCentre_sub_shift_re :
    (schwarzPartnerCentre - (quartetShift : ℂ)).re = -Real.pi := by
  simp only [schwarzPartnerCentre, quartetPoint, quartetShift]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  simp
  ring

/-! ## Simple zeros at the partner centres -/

theorem cosh_neg_pi_div_two_mul_I : Complex.cosh (-((Real.pi : ℂ) / 2) * I) = 0 := by
  rw [Complex.cosh_mul_I]; simp

theorem sinh_neg_pi_div_two_mul_I : Complex.sinh (-((Real.pi : ℂ) / 2) * I) = -I := by
  rw [Complex.sinh_mul_I]; simp

theorem cosh_pi_div_two_mul_I : Complex.cosh (((Real.pi : ℂ) / 2) * I) = 0 := by
  rw [Complex.cosh_mul_I]; simp

theorem sinh_pi_div_two_mul_I : Complex.sinh (((Real.pi : ℂ) / 2) * I) = I := by
  rw [Complex.sinh_mul_I]; simp

theorem analyticAt_coshSub (a : ℝ) (c : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => Complex.cosh (z - (a : ℂ))) c :=
  Complex.analyticAt_cosh.comp (analyticAt_id.sub analyticAt_const)

theorem analyticAt_coshAdd (a : ℝ) (c : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => Complex.cosh (z + (a : ℂ))) c :=
  Complex.analyticAt_cosh.comp (analyticAt_id.add analyticAt_const)

theorem deriv_coshAdd (a : ℝ) (c : ℂ) :
    deriv (fun z : ℂ => Complex.cosh (z + (a : ℂ))) c = Complex.sinh (c + (a : ℂ)) := by
  have h : HasDerivAt (fun z : ℂ => Complex.cosh (z + (a : ℂ))) (Complex.sinh (c + (a : ℂ))) c := by
    simpa using ((hasDerivAt_id c).add_const ((a : ℂ))).ccosh
  exact h.deriv

theorem gradedEnvelope_eq_mul :
    gradedEnvelope = (fun z : ℂ => Complex.cosh (z - (quartetShift : ℂ))) *
      (fun z : ℂ => Complex.cosh (z + (quartetShift : ℂ))) := rfl

/-- The `π i`-period of the envelope. -/
theorem gradedEnvelope_add_pi_mul_I (w : ℂ) :
    gradedEnvelope (w + (Real.pi : ℂ) * I) = gradedEnvelope w :=
  coshQuartetEnvelope_add_pi_mul_I quartetShift w

private theorem analyticOrderAt_envelope_of_partner {c : ℂ}
    (hre : (c - (quartetShift : ℂ)).re = -Real.pi)
    (hadd : Complex.cosh (c + (quartetShift : ℂ)) = 0)
    (hderiv : Complex.sinh (c + (quartetShift : ℂ)) ≠ 0) :
    analyticOrderAt gradedEnvelope c = 1 := by
  have hone : analyticOrderAt (fun z : ℂ => Complex.cosh (z - (quartetShift : ℂ))) c = 0 := by
    refine (analyticAt_coshSub quartetShift c).analyticOrderAt_eq_zero.mpr ?_
    refine cosh_ne_zero_of_re_ne_zero ?_
    rw [hre]
    simp [Real.pi_ne_zero]
  have htwo : analyticOrderAt (fun z : ℂ => Complex.cosh (z + (quartetShift : ℂ))) c = 1 := by
    refine (analyticAt_coshAdd quartetShift c).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hadd ?_
    rw [deriv_coshAdd]
    exact hderiv
  rw [gradedEnvelope_eq_mul,
    analyticOrderAt_mul (analyticAt_coshSub quartetShift c) (analyticAt_coshAdd quartetShift c),
    hone, htwo, zero_add]

theorem analyticOrderAt_gradedEnvelope_fePartner :
    analyticOrderAt gradedEnvelope fePartnerCentre = 1 := by
  refine analyticOrderAt_envelope_of_partner fePartnerCentre_sub_shift_re ?_ ?_
  · rw [fePartnerCentre_add_shift]; exact cosh_neg_pi_div_two_mul_I
  · rw [fePartnerCentre_add_shift, sinh_neg_pi_div_two_mul_I]
    simp [Complex.I_ne_zero]

theorem analyticOrderAt_gradedEnvelope_schwarzPartner :
    analyticOrderAt gradedEnvelope schwarzPartnerCentre = 1 := by
  refine analyticOrderAt_envelope_of_partner schwarzPartnerCentre_sub_shift_re ?_ ?_
  · rw [schwarzPartnerCentre_add_shift]; exact cosh_pi_div_two_mul_I
  · rw [schwarzPartnerCentre_add_shift, sinh_pi_div_two_mul_I]
    exact Complex.I_ne_zero

theorem analyticAt_quartetPoly (w : ℂ) : AnalyticAt ℂ quartetPoly w := by
  unfold quartetPoly
  fun_prop

theorem analyticAt_flatMultiplier (N : ℕ) (w : ℂ) : AnalyticAt ℂ (flatMultiplier N) w := by
  unfold flatMultiplier
  exact analyticAt_const.add ((analyticAt_quartetPoly w).pow _)

theorem analyticAt_gradedEnvelope (w : ℂ) : AnalyticAt ℂ gradedEnvelope w :=
  coshQuartetEnvelope_analyticAt quartetShift w

theorem analyticAt_gradedRealityFn (N : ℕ) (w : ℂ) : AnalyticAt ℂ (gradedRealityFn N) w :=
  (analyticAt_gradedEnvelope w).mul (analyticAt_flatMultiplier N w)

theorem flatMultiplier_eq_one_of_root {N : ℕ} {w : ℂ} (hw : quartetPoly w = 0) :
    flatMultiplier N w = 1 := by
  rw [flatMultiplier, hw, zero_pow (by omega), add_zero]

theorem analyticOrderAt_flatMultiplier_of_root {N : ℕ} {w : ℂ} (hw : quartetPoly w = 0) :
    analyticOrderAt (flatMultiplier N) w = 0 :=
  (analyticAt_flatMultiplier N w).analyticOrderAt_eq_zero.mpr (by
    rw [flatMultiplier_eq_one_of_root hw]; exact one_ne_zero)

/-- **The functional-equation partner centre is a simple zero.** -/
theorem analyticOrderAt_gradedRealityFn_fePartner (N : ℕ) :
    analyticOrderAt (gradedRealityFn N) fePartnerCentre = 1 := by
  have hroot : quartetPoly fePartnerCentre = 0 := quartetPoly_neg_quartetPoint
  rw [show gradedRealityFn N = gradedEnvelope * flatMultiplier N from rfl,
    analyticOrderAt_mul (analyticAt_gradedEnvelope _) (analyticAt_flatMultiplier N _),
    analyticOrderAt_gradedEnvelope_fePartner, analyticOrderAt_flatMultiplier_of_root hroot,
    add_zero]

/-- **The Schwarz partner centre is a simple zero.** -/
theorem analyticOrderAt_gradedRealityFn_schwarzPartner (N : ℕ) :
    analyticOrderAt (gradedRealityFn N) schwarzPartnerCentre = 1 := by
  have hroot : quartetPoly schwarzPartnerCentre = 0 := quartetPoly_neg_conj_quartetPoint
  rw [show gradedRealityFn N = gradedEnvelope * flatMultiplier N from rfl,
    analyticOrderAt_mul (analyticAt_gradedEnvelope _) (analyticAt_flatMultiplier N _),
    analyticOrderAt_gradedEnvelope_schwarzPartner, analyticOrderAt_flatMultiplier_of_root hroot,
    add_zero]

/-! ## The quartet in the normalized coordinate -/

theorem quartetPoint_sub_shift : quartetPoint - (quartetShift : ℂ) = ((Real.pi : ℂ) / 2) * I := by
  simp only [quartetPoint, quartetShift]
  push_cast
  ring

theorem conj_quartetPoint_sub_shift :
    (starRingEnd ℂ) quartetPoint - (quartetShift : ℂ) = -((Real.pi : ℂ) / 2) * I := by
  simp only [quartetPoint, quartetShift]
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem gradedEnvelope_quartetPoint : gradedEnvelope quartetPoint = 0 := by
  rw [gradedEnvelope, coshQuartetEnvelope, quartetPoint_sub_shift, cosh_pi_div_two_mul_I,
    zero_mul]

theorem gradedEnvelope_conj_quartetPoint :
    gradedEnvelope ((starRingEnd ℂ) quartetPoint) = 0 := by
  rw [gradedEnvelope, coshQuartetEnvelope, conj_quartetPoint_sub_shift,
    cosh_neg_pi_div_two_mul_I, zero_mul]

theorem gradedEnvelope_neg (w : ℂ) : gradedEnvelope (-w) = gradedEnvelope w :=
  coshQuartetEnvelope_neg quartetShift w

theorem gradedEnvelope_fePartnerCentre : gradedEnvelope fePartnerCentre = 0 := by
  rw [fePartnerCentre, gradedEnvelope_neg, gradedEnvelope_quartetPoint]

theorem gradedEnvelope_schwarzPartnerCentre : gradedEnvelope schwarzPartnerCentre = 0 := by
  rw [schwarzPartnerCentre, gradedEnvelope_neg, gradedEnvelope_conj_quartetPoint]

theorem gradedRealityFn_eq_zero_of_envelope {N : ℕ} {w : ℂ} (hw : gradedEnvelope w = 0) :
    gradedRealityFn N w = 0 := by
  rw [gradedRealityFn, hw, zero_mul]

/-- The normalization sends the four quartet points to the strip. -/
theorem gradedRealityXi_coordinate (N : ℕ) (s : ℂ) :
    gradedRealityXi N s = gradedRealityFn N (-(2 * (Real.pi : ℂ) * I) * (s - 1 / 2)) := rfl

theorem gradedRealityXi_quartet_one (N : ℕ) :
    gradedRealityXi N (1 / 4 + I / 4) = 0 := by
  have hcoord : -(2 * (Real.pi : ℂ) * I) * ((1 / 4 + I / 4) - 1 / 2) = quartetPoint := by
    simp only [quartetPoint]
    push_cast
    linear_combination (-(Real.pi : ℂ) / 2) * Complex.I_sq
  rw [gradedRealityXi_coordinate, hcoord]
  exact gradedRealityFn_eq_zero_of_envelope gradedEnvelope_quartetPoint

theorem gradedRealityXi_quartet_two (N : ℕ) :
    gradedRealityXi N (3 / 4 - I / 4) = 0 := by
  have hcoord : -(2 * (Real.pi : ℂ) * I) * ((3 / 4 - I / 4) - 1 / 2) = fePartnerCentre := by
    simp only [fePartnerCentre, quartetPoint]
    push_cast
    linear_combination ((Real.pi : ℂ) / 2) * Complex.I_sq
  rw [gradedRealityXi_coordinate, hcoord]
  exact gradedRealityFn_eq_zero_of_envelope gradedEnvelope_fePartnerCentre

theorem gradedRealityXi_quartet_three (N : ℕ) :
    gradedRealityXi N (3 / 4 + I / 4) = 0 := by
  have hcoord : -(2 * (Real.pi : ℂ) * I) * ((3 / 4 + I / 4) - 1 / 2)
      = (starRingEnd ℂ) quartetPoint := by
    simp only [quartetPoint, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    linear_combination (-(Real.pi : ℂ) / 2) * Complex.I_sq
  rw [gradedRealityXi_coordinate, hcoord]
  exact gradedRealityFn_eq_zero_of_envelope gradedEnvelope_conj_quartetPoint

theorem gradedRealityXi_quartet_four (N : ℕ) :
    gradedRealityXi N (1 / 4 - I / 4) = 0 := by
  have hcoord : -(2 * (Real.pi : ℂ) * I) * ((1 / 4 - I / 4) - 1 / 2) = schwarzPartnerCentre := by
    simp only [schwarzPartnerCentre, quartetPoint, map_add, map_mul, Complex.conj_I,
      Complex.conj_ofReal]
    push_cast
    linear_combination ((Real.pi : ℂ) / 2) * Complex.I_sq
  rw [gradedRealityXi_coordinate, hcoord]
  exact gradedRealityFn_eq_zero_of_envelope gradedEnvelope_schwarzPartnerCentre

theorem deriv_gradedEnvelope_add_pi_mul_I (w : ℂ) :
    deriv gradedEnvelope (w + (Real.pi : ℂ) * I) = deriv gradedEnvelope w := by
  have hfun : (fun z : ℂ => gradedEnvelope (z + (Real.pi : ℂ) * I)) = gradedEnvelope :=
    funext gradedEnvelope_add_pi_mul_I
  have hbase : HasDerivAt gradedEnvelope (deriv gradedEnvelope (w + (Real.pi : ℂ) * I))
      (w + (Real.pi : ℂ) * I) :=
    (analyticAt_gradedEnvelope _).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => gradedEnvelope (z + (Real.pi : ℂ) * I))
      (deriv gradedEnvelope (w + (Real.pi : ℂ) * I)) w := by
    simpa [Function.comp_def] using hbase.comp w ((hasDerivAt_id w).add_const ((Real.pi : ℂ) * I))
  rw [hfun] at hd
  exact hd.deriv.symm

/-! ## The zero-free real axis -/

theorem quartetPoly_mul_I (y : ℝ) :
    quartetPoly ((y : ℂ) * I) = ((y ^ (4 : ℕ) + Real.pi ^ (4 : ℕ) / 4 : ℝ) : ℂ) := by
  simp only [quartetPoly]
  push_cast
  linear_combination ((y : ℂ) ^ (4 : ℕ) * ((I : ℂ) ^ (2 : ℕ) - 1)) * Complex.I_sq

theorem flatMultiplier_mul_I (N : ℕ) (y : ℝ) :
    flatMultiplier N ((y : ℂ) * I)
      = ((1 + (y ^ (4 : ℕ) + Real.pi ^ (4 : ℕ) / 4) ^ (2 * N + 1) : ℝ) : ℂ) := by
  rw [flatMultiplier, quartetPoly_mul_I]
  push_cast
  ring

theorem flatMultiplier_mul_I_ne_zero (N : ℕ) (y : ℝ) : flatMultiplier N ((y : ℂ) * I) ≠ 0 := by
  rw [flatMultiplier_mul_I]
  have hpos : (0 : ℝ) < 1 + (y ^ (4 : ℕ) + Real.pi ^ (4 : ℕ) / 4) ^ (2 * N + 1) := by
    have hbase : (0 : ℝ) < y ^ (4 : ℕ) + Real.pi ^ (4 : ℕ) / 4 := by positivity
    positivity
  rw [Ne, Complex.ofReal_eq_zero]
  exact hpos.ne'

theorem gradedRealityFn_mul_I_ne_zero (N : ℕ) (y : ℝ) : gradedRealityFn N ((y : ℂ) * I) ≠ 0 := by
  obtain ⟨r, hr, hval⟩ := coshQuartetEnvelope_mul_I_pos_real (a := quartetShift) (y := y)
    quartetShift_ne_zero
  refine mul_ne_zero ?_ (flatMultiplier_mul_I_ne_zero N y)
  rw [gradedEnvelope, hval]
  simpa using hr.ne'

/-- **The real axis carries no zero.** -/
theorem gradedRealityXi_ne_zero_of_real (N : ℕ) (t : ℝ) : gradedRealityXi N (t : ℂ) ≠ 0 := by
  have hcoord : -(2 * (Real.pi : ℂ) * I) * ((t : ℂ) - 1 / 2)
      = ((-(2 * Real.pi * (t - 1 / 2)) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [gradedRealityXi_coordinate, hcoord]
  exact gradedRealityFn_mul_I_ne_zero N _

/-! ## Exact order one and aperiodicity -/

/-- The multiplier as a genuine polynomial. -/
def flatPolynomial (N : ℕ) : Polynomial ℂ :=
  1 + (Polynomial.X ^ (4 : ℕ) + Polynomial.C ((Real.pi : ℂ) ^ (4 : ℕ) / 4)) ^ (2 * N + 1)

theorem flatPolynomial_eval (N : ℕ) (w : ℂ) :
    (flatPolynomial N).eval w = flatMultiplier N w := by
  simp [flatPolynomial, flatMultiplier, quartetPoly]

theorem flatPolynomial_coeff (N : ℕ) :
    (flatPolynomial N).coeff (4 * (2 * N + 1)) = 1 := by
  have hmonic : (Polynomial.X ^ (4 : ℕ) + Polynomial.C ((Real.pi : ℂ) ^ (4 : ℕ) / 4)).Monic :=
    Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hnd : (Polynomial.X ^ (4 : ℕ) + Polynomial.C ((Real.pi : ℂ) ^ (4 : ℕ) / 4)).natDegree = 4 :=
    Polynomial.natDegree_X_pow_add_C
  have hpm : ((Polynomial.X ^ (4 : ℕ) + Polynomial.C ((Real.pi : ℂ) ^ (4 : ℕ) / 4)) ^ (2 * N + 1)).Monic :=
    hmonic.pow _
  have hpnd : ((Polynomial.X ^ (4 : ℕ) + Polynomial.C ((Real.pi : ℂ) ^ (4 : ℕ) / 4)) ^
      (2 * N + 1)).natDegree = 4 * (2 * N + 1) := by
    rw [Polynomial.natDegree_pow, hnd]
    ring
  rw [flatPolynomial, Polynomial.coeff_add, Polynomial.coeff_one, if_neg (by omega), zero_add,
    ← hpnd, hpm.coeff_natDegree]

theorem flatPolynomial_degree_pos (N : ℕ) : 0 < (flatPolynomial N).degree := by
  have hle : ((4 * (2 * N + 1) : ℕ) : WithBot ℕ) ≤ (flatPolynomial N).degree :=
    Polynomial.le_degree_of_ne_zero (by rw [flatPolynomial_coeff]; exact one_ne_zero)
  refine lt_of_lt_of_le ?_ hle
  exact_mod_cast Nat.pos_of_ne_zero (by omega)

theorem flatPolynomial_ne_zero (N : ℕ) : flatPolynomial N ≠ 0 := by
  intro h
  have hpos := flatPolynomial_degree_pos N
  rw [h, Polynomial.degree_zero] at hpos
  exact absurd hpos (by simp)

theorem gradedRealityFn_eq_envelope_mul_polynomial (N : ℕ) (w : ℂ) :
    gradedRealityFn N w = coshQuartetEnvelope quartetShift w * (flatPolynomial N).eval w := by
  rw [flatPolynomial_eval]
  rfl

/-- **No nonzero period.** -/
theorem gradedRealityFn_periodic_iff (N : ℕ) (h : ℂ) :
    Function.Periodic (gradedRealityFn N) h ↔ h = 0 := by
  have hfun : gradedRealityFn N
      = fun w => coshQuartetEnvelope quartetShift w * (flatPolynomial N).eval w :=
    funext (gradedRealityFn_eq_envelope_mul_polynomial N)
  rw [hfun]
  exact coshQuartetEnvelope_mul_polynomial_periodic_iff quartetShift quartetShift_ne_zero
    (flatPolynomial N) (flatPolynomial_degree_pos N) h

/-- **Exact order one.**  Globally the realizer is bounded by a polynomial multiple of `exp 2‖w‖`,
and on a real ray it is bounded below by a positive multiple of `exp 2x`. -/
theorem gradedRealityFn_exact_order_one_bounds (N : ℕ) :
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ w : ℂ, ‖gradedRealityFn N w‖
        ≤ Kupper * (1 + ‖w‖) ^ (flatPolynomial N).natDegree * Real.exp (2 * ‖w‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤ ‖gradedRealityFn N (x : ℂ)‖ := by
  obtain ⟨Ku, Kl, R, hKu, hKl, hupper, hlower⟩ :=
    coshQuartetEnvelope_mul_polynomial_exact_order_one_bounds quartetShift
      (flatPolynomial_ne_zero N)
  refine ⟨Ku, Kl, R, hKu, hKl, fun w => ?_, fun x hx => ?_⟩
  · rw [gradedRealityFn_eq_envelope_mul_polynomial]
    exact hupper w
  · rw [gradedRealityFn_eq_envelope_mul_polynomial]
    exact hlower x hx

/-! ## The delayed completed-flux defect -/

/-- The shifted quartet polynomial: `quartetPoly (w + x) = x · quartetShiftPoly w x` at a root. -/
def quartetShiftPoly (w x : ℂ) : ℂ := 4 * w ^ (3 : ℕ) + 6 * w ^ (2 : ℕ) * x + 4 * w * x ^ (2 : ℕ) + x ^ (3 : ℕ)

theorem quartetPoly_add (w x : ℂ) :
    quartetPoly (w + x) = x * quartetShiftPoly w x + quartetPoly w := by
  simp only [quartetPoly, quartetShiftPoly]
  ring

theorem quartetPoly_add_of_root {w : ℂ} (hw : quartetPoly w = 0) (x : ℂ) :
    quartetPoly (w + x) = x * quartetShiftPoly w x := by
  rw [quartetPoly_add, hw, add_zero]

/-- The analytic unit of the Hermite-flat factorization at a quartet root. -/
def multUnit (N : ℕ) (w x : ℂ) : ℂ := quartetShiftPoly w x ^ (2 * N + 1)

@[simp] theorem multUnit_zero (N : ℕ) (w : ℂ) :
    multUnit N w 0 = (4 * w ^ (3 : ℕ)) ^ (2 * N + 1) := by
  simp [multUnit, quartetShiftPoly]

theorem analyticAt_multUnit (N : ℕ) (w : ℂ) : AnalyticAt ℂ (multUnit N w) 0 := by
  unfold multUnit quartetShiftPoly
  fun_prop

theorem hermiteFlatFactor_multUnit {N : ℕ} {w : ℂ} (hw : quartetPoly w = 0) :
    hermiteFlatFactor (2 * N + 1) (multUnit N w) = fun x => flatMultiplier N (w + x) := by
  funext x
  rw [hermiteFlatFactor, multUnit, flatMultiplier, quartetPoly_add_of_root hw, mul_pow]

/-- The multiplier's completed-flux correction at a quartet root. -/
def multFlux (N : ℕ) (w : ℂ) : ℂ → ℂ :=
  hermiteFlatFluxCorrection (2 * N + 1) (multUnit N w)

theorem deriv_flatMultiplier_shift (N : ℕ) (w x : ℂ) :
    deriv (fun y : ℂ => flatMultiplier N (w + y)) x = deriv (flatMultiplier N) (w + x) := by
  have hbase : HasDerivAt (flatMultiplier N) (deriv (flatMultiplier N) (w + x)) (w + x) :=
    (analyticAt_flatMultiplier N (w + x)).differentiableAt.hasDerivAt
  have h := hbase.comp x ((hasDerivAt_id x).const_add w)
  simpa [Function.comp_def] using h.deriv

/-- The multiplier germ is the residue-filled flux germ of the multiplier. -/
theorem fluxGerm_flatMultiplier_eq {N : ℕ} {w : ℂ} (hw : quartetPoly w = 0) :
    fluxGerm (flatMultiplier N) w
      = fun x => -x * deriv (flatMultiplier N) (w + x) / flatMultiplier N (w + x) := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [fluxGerm_zero, analyticOrderAt_flatMultiplier_of_root hw]
    simp
  · exact fluxGerm_of_ne_zero _ _ hx

theorem multFlux_eventuallyEq {N : ℕ} {w : ℂ} (hw : quartetPoly w = 0) :
    multFlux N w =ᶠ[𝓝 0] fluxGerm (flatMultiplier N) w := by
  have h := hermiteFlatFluxCorrection_eventuallyEq_neg_mul_logDeriv
    (M := 2 * N + 1) (by omega) (analyticAt_multUnit N w)
  rw [fluxGerm_flatMultiplier_eq hw]
  refine h.trans (Filter.Eventually.of_forall fun x => ?_)
  rw [hermiteFlatFactor_multUnit hw]
  show -x * deriv (fun y : ℂ => flatMultiplier N (w + y)) x / flatMultiplier N (w + x)
      = -x * deriv (flatMultiplier N) (w + x) / flatMultiplier N (w + x)
  rw [deriv_flatMultiplier_shift]

/-- The two partner base germs are literally equal: the centres differ by one envelope period. -/
theorem fluxGerm_gradedEnvelope_partners_eq :
    fluxGerm gradedEnvelope schwarzPartnerCentre = fluxGerm gradedEnvelope fePartnerCentre := by
  funext x
  by_cases hx : x = 0
  · subst x
    rw [fluxGerm_zero, fluxGerm_zero, analyticOrderAt_gradedEnvelope_schwarzPartner,
      analyticOrderAt_gradedEnvelope_fePartner]
  · rw [fluxGerm_of_ne_zero _ _ hx, fluxGerm_of_ne_zero _ _ hx, schwarzPartnerCentre_eq,
      show fePartnerCentre + (Real.pi : ℂ) * I + x = (fePartnerCentre + x) + (Real.pi : ℂ) * I by
        ring,
      gradedEnvelope_add_pi_mul_I, deriv_gradedEnvelope_add_pi_mul_I]

theorem four_mul_fePartnerCentre_cube :
    4 * fePartnerCentre ^ (3 : ℕ) = (Real.pi : ℂ) ^ (3 : ℕ) * (1 - I) := by
  simp only [fePartnerCentre, quartetPoint]
  push_cast
  linear_combination (-((Real.pi : ℂ) ^ (3 : ℕ) / 2) * (I + 3)) * Complex.I_sq

theorem four_mul_schwarzPartnerCentre_cube :
    4 * schwarzPartnerCentre ^ (3 : ℕ) = (Real.pi : ℂ) ^ (3 : ℕ) * (1 + I) := by
  simp only [schwarzPartnerCentre, quartetPoint, map_add, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  push_cast
  linear_combination (((Real.pi : ℂ) ^ (3 : ℕ) / 2) * (I - 3)) * Complex.I_sq

/-- **The two partner leading coefficients differ.**  This is the exact odd-order separation. -/
theorem multUnit_zero_ne (N : ℕ) :
    multUnit N fePartnerCentre 0 ≠ multUnit N schwarzPartnerCentre 0 := by
  rw [multUnit_zero, multUnit_zero, four_mul_fePartnerCentre_cube,
    four_mul_schwarzPartnerCentre_cube]
  intro h
  have hfac : (Real.pi : ℂ) ^ (3 : ℕ) * (1 - I) = (-I) * ((Real.pi : ℂ) ^ (3 : ℕ) * (1 + I)) := by
    linear_combination ((Real.pi : ℂ) ^ (3 : ℕ)) * Complex.I_sq
  rw [hfac, mul_pow] at h
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hone : (1 + I : ℂ) ≠ 0 := by
    simp [Complex.ext_iff]
  have hne : ((Real.pi : ℂ) ^ (3 : ℕ) * (1 + I)) ^ (2 * N + 1) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hpi) hone)
  have h1 : (-I : ℂ) ^ (2 * N + 1) * ((Real.pi : ℂ) ^ (3 : ℕ) * (1 + I)) ^ (2 * N + 1)
      = 1 * ((Real.pi : ℂ) ^ (3 : ℕ) * (1 + I)) ^ (2 * N + 1) := by
    rw [one_mul]; exact h
  have hunit := mul_right_cancel₀ hne h1
  have hsq : (-I : ℂ) ^ (2 : ℕ) = -1 := by linear_combination Complex.I_sq
  have hval : (-I : ℂ) ^ (2 * N + 1) = (-1 : ℂ) ^ N * (-I) := by
    rw [pow_add, pow_one, pow_mul, hsq]
  rw [hval] at hunit
  rcases Nat.even_or_odd N with hN | hN
  · rw [hN.neg_one_pow, one_mul] at hunit
    simp [Complex.ext_iff] at hunit
  · rw [hN.neg_one_pow, show (-1 : ℂ) * (-I) = I by ring] at hunit
    simp [Complex.ext_iff] at hunit

theorem multFlux_sub_eq (N : ℕ) :
    multFlux N fePartnerCentre - multFlux N schwarzPartnerCentre
      = (id : ℂ → ℂ) ^ (2 * N + 1) *
        (hermiteFlatFluxUnit (2 * N + 1) (multUnit N fePartnerCentre)
          - hermiteFlatFluxUnit (2 * N + 1) (multUnit N schwarzPartnerCentre)) := by
  funext x
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq, multFlux,
    hermiteFlatFluxCorrection]
  ring

theorem analyticOrderAt_multFlux_sub (N : ℕ) :
    analyticOrderAt (multFlux N fePartnerCentre - multFlux N schwarzPartnerCentre) 0
      = ((2 * N + 1 : ℕ) : ℕ∞) := by
  have hMpos : 0 < 2 * N + 1 := by omega
  have hunitc := hermiteFlatFluxUnit_analyticAt_zero hMpos (analyticAt_multUnit N fePartnerCentre)
  have hunitd :=
    hermiteFlatFluxUnit_analyticAt_zero hMpos (analyticAt_multUnit N schwarzPartnerCentre)
  have hval : (hermiteFlatFluxUnit (2 * N + 1) (multUnit N fePartnerCentre)
      - hermiteFlatFluxUnit (2 * N + 1) (multUnit N schwarzPartnerCentre)) 0 ≠ 0 := by
    rw [Pi.sub_apply, hermiteFlatFluxUnit_zero hMpos, hermiteFlatFluxUnit_zero hMpos]
    intro hc
    have hMne : ((2 * N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hdiff : multUnit N fePartnerCentre 0 - multUnit N schwarzPartnerCentre 0 = 0 := by
      have hz : -((2 * N + 1 : ℕ) : ℂ) * (multUnit N fePartnerCentre 0
          - multUnit N schwarzPartnerCentre 0) = 0 := by
        rw [mul_sub]; linear_combination hc
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd (neg_eq_zero.mp h) hMne
      · exact h
    exact multUnit_zero_ne N (sub_eq_zero.mp hdiff)
  rw [multFlux_sub_eq,
    analyticOrderAt_mul (analyticAt_id.pow _) (hunitc.sub hunitd),
    analyticOrderAt_pow analyticAt_id, analyticOrderAt_id,
    (hunitc.sub hunitd).analyticOrderAt_eq_zero.mpr hval]
  simp

theorem gradedRealityFn_eq_mul (N : ℕ) :
    gradedRealityFn N = gradedEnvelope * flatMultiplier N := rfl

/-- The residue-filled completed-flux germ at the functional-equation partner centre. -/
def feGerm (N : ℕ) : ℂ → ℂ := fluxGerm (gradedRealityFn N) fePartnerCentre

/-- The residue-filled completed-flux germ at the Schwarz partner centre. -/
def schwarzGerm (N : ℕ) : ℂ → ℂ := fluxGerm (gradedRealityFn N) schwarzPartnerCentre

theorem analyticAt_feGerm (N : ℕ) : AnalyticAt ℂ (feGerm N) 0 :=
  fluxGerm_analyticAt_zero (m := 1) (analyticAt_gradedRealityFn N _)
    (by simpa using analyticOrderAt_gradedRealityFn_fePartner N)

theorem analyticAt_schwarzGerm (N : ℕ) : AnalyticAt ℂ (schwarzGerm N) 0 :=
  fluxGerm_analyticAt_zero (m := 1) (analyticAt_gradedRealityFn N _)
    (by simpa using analyticOrderAt_gradedRealityFn_schwarzPartner N)

theorem germDiff_eventuallyEq (N : ℕ) :
    feGerm N - schwarzGerm N =ᶠ[𝓝 0]
      multFlux N fePartnerCentre - multFlux N schwarzPartnerCentre := by
  have hEc : analyticOrderAt gradedEnvelope fePartnerCentre = ((1 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_gradedEnvelope_fePartner
  have hEd : analyticOrderAt gradedEnvelope schwarzPartnerCentre = ((1 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_gradedEnvelope_schwarzPartner
  have hPc : analyticOrderAt (flatMultiplier N) fePartnerCentre = ((0 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_flatMultiplier_of_root (N := N) quartetPoly_fePartnerCentre
  have hPd : analyticOrderAt (flatMultiplier N) schwarzPartnerCentre = ((0 : ℕ) : ℕ∞) := by
    simpa using analyticOrderAt_flatMultiplier_of_root (N := N) quartetPoly_schwarzPartnerCentre
  have hc : fluxGerm (gradedRealityFn N) fePartnerCentre =ᶠ[𝓝 0]
      fluxGerm gradedEnvelope fePartnerCentre + fluxGerm (flatMultiplier N) fePartnerCentre := by
    rw [gradedRealityFn_eq_mul]
    exact fluxGerm_mul (analyticAt_gradedEnvelope _) (analyticAt_flatMultiplier N _) hEc hPc
  have hd : fluxGerm (gradedRealityFn N) schwarzPartnerCentre =ᶠ[𝓝 0]
      fluxGerm gradedEnvelope schwarzPartnerCentre
        + fluxGerm (flatMultiplier N) schwarzPartnerCentre := by
    rw [gradedRealityFn_eq_mul]
    exact fluxGerm_mul (analyticAt_gradedEnvelope _) (analyticAt_flatMultiplier N _) hEd hPd
  have hmc := multFlux_eventuallyEq (N := N) quartetPoly_fePartnerCentre
  have hmd := multFlux_eventuallyEq (N := N) quartetPoly_schwarzPartnerCentre
  have hbase := congrFun fluxGerm_gradedEnvelope_partners_eq
  filter_upwards [hc, hd, hmc, hmd] with x hcx hdx hmcx hmdx
  simp only [Pi.sub_apply, Pi.add_apply] at hcx hdx ⊢
  rw [feGerm, schwarzGerm, hcx, hdx, hmcx, hmdx, hbase x]
  ring

theorem iteratedDeriv_germDiff (N n : ℕ) :
    iteratedDeriv n (feGerm N) 0 - iteratedDeriv n (schwarzGerm N) 0
      = iteratedDeriv n (multFlux N fePartnerCentre - multFlux N schwarzPartnerCentre) 0 := by
  rw [← iteratedDeriv_sub (analyticAt_feGerm N).contDiffAt (analyticAt_schwarzGerm N).contDiffAt]
  exact (germDiff_eventuallyEq N).iteratedDeriv_eq n

private theorem multFlux_sub_jet (N : ℕ) :
    (∀ n < 2 * N + 1,
        iteratedDeriv n (multFlux N fePartnerCentre - multFlux N schwarzPartnerCentre) 0 = 0) ∧
      iteratedDeriv (2 * N + 1)
        (multFlux N fePartnerCentre - multFlux N schwarzPartnerCentre) 0 ≠ 0 := by
  have hMpos : 0 < 2 * N + 1 := by omega
  have han : AnalyticAt ℂ (multFlux N fePartnerCentre - multFlux N schwarzPartnerCentre) 0 :=
    (hermiteFlatFluxCorrection_analyticAt_zero hMpos (analyticAt_multUnit N fePartnerCentre)).sub
      (hermiteFlatFluxCorrection_analyticAt_zero hMpos
        (analyticAt_multUnit N schwarzPartnerCentre))
  have h := GaloisForLFunctions.RHTower.GelfondSchneiderProof.analyticOrderAt_eq_nat_imp_iteratedDeriv_eq_zero han
    (2 * N + 1) (analyticOrderAt_multFlux_sub N)
  exact ⟨fun n hn => by simpa only [iteratedDeriv_eq_iterate] using h.1 n hn,
    by simpa only [iteratedDeriv_eq_iterate] using h.2⟩

/-- **The two partner germs share every Taylor coefficient through the prescribed depth.** -/
theorem feGerm_iteratedDeriv_eq_schwarz_of_le (N : ℕ) {n : ℕ} (hn : n ≤ N) :
    iteratedDeriv n (feGerm N) 0 = iteratedDeriv n (schwarzGerm N) 0 := by
  have hzero := (multFlux_sub_jet N).1 n (by omega)
  have h := iteratedDeriv_germDiff N n
  rw [hzero] at h
  linear_combination h

/-- **The two partner germs differ at the later odd order `2N+1`.** -/
theorem feGerm_iteratedDeriv_ne_schwarz_at_escape (N : ℕ) :
    iteratedDeriv (2 * N + 1) (feGerm N) 0 ≠ iteratedDeriv (2 * N + 1) (schwarzGerm N) 0 := by
  intro hc
  refine (multFlux_sub_jet N).2 ?_
  rw [← iteratedDeriv_germDiff N (2 * N + 1), hc, sub_self]

/-! ## The capstone -/

theorem quartet_strictly_inside_strip :
    ((1 / 4 + I / 4 : ℂ).re = 1 / 4 ∧ (1 / 4 + I / 4 : ℂ).im = 1 / 4) ∧
      ((3 / 4 - I / 4 : ℂ).re = 3 / 4 ∧ (3 / 4 - I / 4 : ℂ).im = -(1 / 4)) ∧
      ((3 / 4 + I / 4 : ℂ).re = 3 / 4 ∧ (3 / 4 + I / 4 : ℂ).im = 1 / 4) ∧
      ((1 / 4 - I / 4 : ℂ).re = 1 / 4 ∧ (1 / 4 - I / 4 : ℂ).im = -(1 / 4)) := by
  norm_num

/-- **No fixed finite completed-flux jet selects the symmetry axis.**

For every depth `N` the entire function `gradedRealityFn N` and its normalization
`gradedRealityXi N` realize simultaneously:

* the functional equation `X(1-s) = X(s)` and Schwarz reality `X(conj s) = conj X(s)`;
* no zero on the real axis;
* a genuine off-critical zero quartet `1/4 ± i/4`, `3/4 ± i/4`, strictly inside the critical strip,
  each of which is a *simple* zero;
* exact entire order one, and no nonzero period;
* identical residue-filled completed-flux Taylor coefficients at the two partner centres through
  order `N`, with an explicit failure at the later odd order `2N+1`.

Hence functional-equation symmetry, Schwarz reality, critical-strip location, absence of real
zeros, order-one growth and aperiodicity cannot turn any fixed finite completed-flux jet into a
critical-axis selector. -/
theorem finite_jet_graded_reality_nonselection (N : ℕ) :
    (∀ w : ℂ, AnalyticAt ℂ (gradedRealityFn N) w) ∧
      (∀ s : ℂ, gradedRealityXi N (1 - s) = gradedRealityXi N s) ∧
      (∀ s : ℂ, gradedRealityXi N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (gradedRealityXi N s)) ∧
      (∀ t : ℝ, gradedRealityXi N (t : ℂ) ≠ 0) ∧
      (gradedRealityXi N (1 / 4 + I / 4) = 0 ∧ gradedRealityXi N (3 / 4 - I / 4) = 0 ∧
        gradedRealityXi N (3 / 4 + I / 4) = 0 ∧ gradedRealityXi N (1 / 4 - I / 4) = 0) ∧
      (analyticOrderAt (gradedRealityFn N) fePartnerCentre = 1 ∧
        analyticOrderAt (gradedRealityFn N) schwarzPartnerCentre = 1) ∧
      (∀ h : ℂ, Function.Periodic (gradedRealityFn N) h ↔ h = 0) ∧
      (∀ n ≤ N, iteratedDeriv n (feGerm N) 0 = iteratedDeriv n (schwarzGerm N) 0) ∧
      iteratedDeriv (2 * N + 1) (feGerm N) 0 ≠ iteratedDeriv (2 * N + 1) (schwarzGerm N) 0 :=
  ⟨analyticAt_gradedRealityFn N,
    gradedRealityXi_functional_equation N,
    gradedRealityXi_conj N,
    gradedRealityXi_ne_zero_of_real N,
    ⟨gradedRealityXi_quartet_one N, gradedRealityXi_quartet_two N,
      gradedRealityXi_quartet_three N, gradedRealityXi_quartet_four N⟩,
    ⟨analyticOrderAt_gradedRealityFn_fePartner N,
      analyticOrderAt_gradedRealityFn_schwarzPartner N⟩,
    gradedRealityFn_periodic_iff N,
    fun _ hn => feGerm_iteratedDeriv_eq_schwarz_of_le N hn,
    feGerm_iteratedDeriv_ne_schwarz_at_escape N⟩

end

end RHTower
