import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinSqrtWhittakerTail

/-!
# Literal two-step Maass words on completed Eisenstein Whittaker modes

For a positive Fourier frequency, the standard Maass operators act radially as

`R_k = Y d/dY - cY + k/2`,  `L_k = Y d/dY + cY - k/2`.

Using the corpus-led real-argument Bessel derivative, this module differentiates the literal
square-root-normalized mode `sqrt(Y) K_nu(cY)`, composes `R_2 R_0` and
`L_(-2) L_0`, and proves exact finite shift words.  Both words contain only height/index degrees
at most two and Bessel orders `nu, nu±1, nu±2`.

Substituting `c=2*pi*n` gives finite combinations of the already-admitted completed Eisenstein
tails.  Lean proves both full infinite nonconstant weight `+4` and weight `-4` tails tend to zero
at the cusp.  This closes the literal nonconstant part of the two balanced-spin Stokes currents.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [LITERAL MAASS WHITTAKER WORD]`
-/


open Complex Real Filter Topology

namespace RHTower

noncomputable section

abbrev D4BMPositiveReal := {x : ℝ // 0 < x}

def d4BMWhittakerP0 (c : D4BMPositiveReal) (nu : ℂ) (Y : ℝ) : ℂ :=
  (Real.sqrt Y : ℂ) *
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder ((c : ℝ) * Y) nu

def d4BMWhittakerP1 (c : D4BMPositiveReal) (nu : ℂ) (Y : ℝ) : ℂ :=
  d4BMWhittakerP0 c nu Y * (((c : ℝ) * Y : ℝ) : ℂ)

def d4BMWhittakerP2 (c : D4BMPositiveReal) (nu : ℂ) (Y : ℝ) : ℂ :=
  d4BMWhittakerP1 c nu Y * (((c : ℝ) * Y : ℝ) : ℂ)

def d4BMWhittakerP0Deriv (c : D4BMPositiveReal) (nu : ℂ)
    (Y : D4BMPositiveReal) : ℂ :=
  ((1 / (2 * Real.sqrt (Y : ℝ)) : ℝ) : ℂ) *
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder ((c : ℝ) * (Y : ℝ)) nu +
    (Real.sqrt (Y : ℝ) : ℂ) * (c : ℂ) * (-(1 / 2 : ℂ)) *
      (GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * (Y : ℝ)) (nu + 1) +
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          ((c : ℝ) * (Y : ℝ)) (nu - 1))

def d4BMWhittakerP1Deriv (c : D4BMPositiveReal) (nu : ℂ)
    (Y : D4BMPositiveReal) : ℂ :=
  d4BMWhittakerP0Deriv c nu Y * (((c : ℝ) * (Y : ℝ) : ℝ) : ℂ) +
    d4BMWhittakerP0 c nu (Y : ℝ) * (c : ℂ)

theorem d4BM_hasDerivAt_whittakerP0
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    HasDerivAt (d4BMWhittakerP0 c nu) (d4BMWhittakerP0Deriv c nu Y) (Y : ℝ) := by
  have harg : 0 < (c : ℝ) * (Y : ℝ) := mul_pos c.2 Y.2
  have hK0 := d4BM_hasDerivAt_modifiedBesselKOrder_argument harg nu
  have hinner : HasDerivAt (fun q : ℝ => (c : ℝ) * q) (c : ℝ) (Y : ℝ) := by
    simpa using (hasDerivAt_id (Y : ℝ)).const_mul (c : ℝ)
  have hK := hK0.scomp (Y : ℝ) hinner
  have hsqrt : HasDerivAt (fun q : ℝ => (Real.sqrt q : ℂ))
      ((1 / (2 * Real.sqrt (Y : ℝ)) : ℝ) : ℂ) (Y : ℝ) := by
    simpa using (Real.hasDerivAt_sqrt Y.2.ne').ofReal_comp
  have hmul := hsqrt.mul hK
  have hfun : d4BMWhittakerP0 c nu =ᶠ[𝓝 (Y : ℝ)]
      ((fun q : ℝ => (Real.sqrt q : ℂ)) *
        ((fun q : ℝ => GaloisForLFunctions.HTGeometry.modifiedBesselKOrder q nu) ∘
          fun q : ℝ => (c : ℝ) * q)) :=
    Filter.Eventually.of_forall fun q => by rfl
  refine (hmul.congr_of_eventuallyEq hfun).congr_deriv ?_
  simp [d4BMWhittakerP0Deriv, Function.comp_apply]
  ring

theorem d4BM_hasDerivAt_whittakerP1
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    HasDerivAt (d4BMWhittakerP1 c nu) (d4BMWhittakerP1Deriv c nu Y) (Y : ℝ) := by
  have h0 := d4BM_hasDerivAt_whittakerP0 c nu Y
  have hr : HasDerivAt (fun q : ℝ => ((((c : ℝ) * q : ℝ) : ℂ)))
      (c : ℂ) (Y : ℝ) := by
    have h := (hasDerivAt_id (Y : ℝ)).const_mul (c : ℝ)
    simpa using h.ofReal_comp
  have hmul := h0.mul hr
  have hfun : d4BMWhittakerP1 c nu =ᶠ[𝓝 (Y : ℝ)]
      (d4BMWhittakerP0 c nu * fun q : ℝ => ((((c : ℝ) * q : ℝ) : ℂ))) :=
    Filter.Eventually.of_forall fun q => by rfl
  refine (hmul.congr_of_eventuallyEq hfun).congr_deriv ?_
  rfl

def d4BMPositiveFrequencyMaassRaiseAt
    (k : ℤ) (c : D4BMPositiveReal) (Y : D4BMPositiveReal)
    (value deriv : ℂ) : ℂ :=
  (Y : ℂ) * deriv - ((c : ℂ) * (Y : ℂ)) * value + (k : ℂ) / 2 * value

def d4BMPositiveFrequencyMaassLowerAt
    (k : ℤ) (c : D4BMPositiveReal) (Y : D4BMPositiveReal)
    (value deriv : ℂ) : ℂ :=
  (Y : ℂ) * deriv + ((c : ℂ) * (Y : ℂ)) * value - (k : ℂ) / 2 * value

def d4BMPositiveFrequencyRaiseZeroMode
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) : ℂ :=
  d4BMPositiveFrequencyMaassRaiseAt 0 c Y
    (d4BMWhittakerP0 c nu (Y : ℝ)) (d4BMWhittakerP0Deriv c nu Y)

def d4BMPositiveFrequencyLowerZeroMode
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) : ℂ :=
  d4BMPositiveFrequencyMaassLowerAt 0 c Y
    (d4BMWhittakerP0 c nu (Y : ℝ)) (d4BMWhittakerP0Deriv c nu Y)

theorem d4BM_positiveFrequencyRaiseZeroMode_eq
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    d4BMPositiveFrequencyRaiseZeroMode c nu Y =
      (1 / 2 : ℂ) * d4BMWhittakerP0 c nu Y -
      d4BMWhittakerP1 c nu Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) Y := by
  simp [d4BMPositiveFrequencyRaiseZeroMode, d4BMPositiveFrequencyMaassRaiseAt,
    d4BMWhittakerP0Deriv, d4BMWhittakerP0, d4BMWhittakerP1]
  have hsqrt : Real.sqrt (Y : ℝ) ≠ 0 := (Real.sqrt_pos.2 Y.2).ne'
  have hYsqrt : (Y : ℂ) = (Real.sqrt (Y : ℝ) : ℂ) ^ (2 : ℕ) := by
    exact_mod_cast (Real.sq_sqrt Y.2.le).symm
  rw [hYsqrt]
  field_simp [hsqrt]
  ring

theorem d4BM_positiveFrequencyLowerZeroMode_eq
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    d4BMPositiveFrequencyLowerZeroMode c nu Y =
      (1 / 2 : ℂ) * d4BMWhittakerP0 c nu Y +
      d4BMWhittakerP1 c nu Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) Y := by
  simp [d4BMPositiveFrequencyLowerZeroMode, d4BMPositiveFrequencyMaassLowerAt,
    d4BMWhittakerP0Deriv, d4BMWhittakerP0, d4BMWhittakerP1]
  have hsqrt : Real.sqrt (Y : ℝ) ≠ 0 := (Real.sqrt_pos.2 Y.2).ne'
  have hYsqrt : (Y : ℂ) = (Real.sqrt (Y : ℝ) : ℂ) ^ (2 : ℕ) := by
    exact_mod_cast (Real.sq_sqrt Y.2.le).symm
  rw [hYsqrt]
  field_simp [hsqrt]
  ring

def d4BMPositiveFrequencyRaiseZeroModeDeriv
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) : ℂ :=
  (1 / 2 : ℂ) * d4BMWhittakerP0Deriv c nu Y -
    d4BMWhittakerP1Deriv c nu Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1Deriv c (nu + 1) Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1Deriv c (nu - 1) Y

def d4BMPositiveFrequencyLowerZeroModeDeriv
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) : ℂ :=
  (1 / 2 : ℂ) * d4BMWhittakerP0Deriv c nu Y +
    d4BMWhittakerP1Deriv c nu Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1Deriv c (nu + 1) Y -
    (1 / 2 : ℂ) * d4BMWhittakerP1Deriv c (nu - 1) Y

theorem d4BM_hasDerivAt_positiveFrequencyRaiseZeroMode
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    HasDerivAt (fun q : ℝ =>
      (1 / 2 : ℂ) * d4BMWhittakerP0 c nu q -
      d4BMWhittakerP1 c nu q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) q)
      (d4BMPositiveFrequencyRaiseZeroModeDeriv c nu Y) (Y : ℝ) := by
  have h := (((d4BM_hasDerivAt_whittakerP0 c nu Y).const_mul (1 / 2 : ℂ)).sub
      (d4BM_hasDerivAt_whittakerP1 c nu Y) |>.sub
      ((d4BM_hasDerivAt_whittakerP1 c (nu + 1) Y).const_mul (1 / 2 : ℂ)) |>.sub
      ((d4BM_hasDerivAt_whittakerP1 c (nu - 1) Y).const_mul (1 / 2 : ℂ)))
  have hfun : (fun q : ℝ =>
      (1 / 2 : ℂ) * d4BMWhittakerP0 c nu q -
      d4BMWhittakerP1 c nu q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) q) =ᶠ[𝓝 (Y : ℝ)]
      (((fun y => (1 / 2 : ℂ) * d4BMWhittakerP0 c nu y) - d4BMWhittakerP1 c nu -
        fun y => (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) y) -
        fun y => (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) y) :=
    Filter.Eventually.of_forall fun q => by rfl
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  rfl

theorem d4BM_hasDerivAt_positiveFrequencyLowerZeroMode
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    HasDerivAt (fun q : ℝ =>
      (1 / 2 : ℂ) * d4BMWhittakerP0 c nu q +
      d4BMWhittakerP1 c nu q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) q)
      (d4BMPositiveFrequencyLowerZeroModeDeriv c nu Y) (Y : ℝ) := by
  have h := (((d4BM_hasDerivAt_whittakerP0 c nu Y).const_mul (1 / 2 : ℂ)).add
      (d4BM_hasDerivAt_whittakerP1 c nu Y) |>.sub
      ((d4BM_hasDerivAt_whittakerP1 c (nu + 1) Y).const_mul (1 / 2 : ℂ)) |>.sub
      ((d4BM_hasDerivAt_whittakerP1 c (nu - 1) Y).const_mul (1 / 2 : ℂ)))
  have hfun : (fun q : ℝ =>
      (1 / 2 : ℂ) * d4BMWhittakerP0 c nu q +
      d4BMWhittakerP1 c nu q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) q -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) q) =ᶠ[𝓝 (Y : ℝ)]
      (((fun y => (1 / 2 : ℂ) * d4BMWhittakerP0 c nu y) + d4BMWhittakerP1 c nu -
        fun y => (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) y) -
        fun y => (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) y) :=
    Filter.Eventually.of_forall fun q => by rfl
  refine (h.congr_of_eventuallyEq hfun).congr_deriv ?_
  rfl

def d4BMPositiveFrequencyRaiseTwoRaiseZeroMode
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) : ℂ :=
  d4BMPositiveFrequencyMaassRaiseAt 2 c Y
    ((1 / 2 : ℂ) * d4BMWhittakerP0 c nu Y -
      d4BMWhittakerP1 c nu Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) Y)
    (d4BMPositiveFrequencyRaiseZeroModeDeriv c nu Y)

def d4BMPositiveFrequencyLowerNegTwoLowerZeroMode
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) : ℂ :=
  d4BMPositiveFrequencyMaassLowerAt (-2) c Y
    ((1 / 2 : ℂ) * d4BMWhittakerP0 c nu Y +
      d4BMWhittakerP1 c nu Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu + 1) Y -
      (1 / 2 : ℂ) * d4BMWhittakerP1 c (nu - 1) Y)
    (d4BMPositiveFrequencyLowerZeroModeDeriv c nu Y)

theorem d4BM_positiveFrequencyRaiseTwoRaiseZeroMode_eq_shiftWord
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    d4BMPositiveFrequencyRaiseTwoRaiseZeroMode c nu Y =
      (3 / 4 : ℂ) * d4BMWhittakerP0 c nu Y -
      3 * d4BMWhittakerP1 c nu Y -
      (3 / 2 : ℂ) * (d4BMWhittakerP1 c (nu + 1) Y + d4BMWhittakerP1 c (nu - 1) Y) +
      (3 / 2 : ℂ) * d4BMWhittakerP2 c nu Y +
      (d4BMWhittakerP2 c (nu + 1) Y + d4BMWhittakerP2 c (nu - 1) Y) +
      (1 / 4 : ℂ) * (d4BMWhittakerP2 c (nu + 2) Y + d4BMWhittakerP2 c (nu - 2) Y) := by
  simp [d4BMPositiveFrequencyRaiseTwoRaiseZeroMode,
    d4BMPositiveFrequencyRaiseZeroModeDeriv, d4BMPositiveFrequencyMaassRaiseAt,
    d4BMWhittakerP0Deriv, d4BMWhittakerP1Deriv,
    d4BMWhittakerP0, d4BMWhittakerP1, d4BMWhittakerP2]
  have hsqrt : Real.sqrt (Y : ℝ) ≠ 0 := (Real.sqrt_pos.2 Y.2).ne'
  have hYsqrt : (Y : ℂ) = (Real.sqrt (Y : ℝ) : ℂ) ^ (2 : ℕ) := by
    exact_mod_cast (Real.sq_sqrt Y.2.le).symm
  rw [hYsqrt]
  field_simp [hsqrt]
  ring

theorem d4BM_positiveFrequencyLowerNegTwoLowerZeroMode_eq_shiftWord
    (c : D4BMPositiveReal) (nu : ℂ) (Y : D4BMPositiveReal) :
    d4BMPositiveFrequencyLowerNegTwoLowerZeroMode c nu Y =
      (3 / 4 : ℂ) * d4BMWhittakerP0 c nu Y +
      3 * d4BMWhittakerP1 c nu Y -
      (3 / 2 : ℂ) * (d4BMWhittakerP1 c (nu + 1) Y + d4BMWhittakerP1 c (nu - 1) Y) +
      (3 / 2 : ℂ) * d4BMWhittakerP2 c nu Y -
      (d4BMWhittakerP2 c (nu + 1) Y + d4BMWhittakerP2 c (nu - 1) Y) +
      (1 / 4 : ℂ) * (d4BMWhittakerP2 c (nu + 2) Y + d4BMWhittakerP2 c (nu - 2) Y) := by
  simp [d4BMPositiveFrequencyLowerNegTwoLowerZeroMode,
    d4BMPositiveFrequencyLowerZeroModeDeriv, d4BMPositiveFrequencyMaassLowerAt,
    d4BMWhittakerP0Deriv, d4BMWhittakerP1Deriv,
    d4BMWhittakerP0, d4BMWhittakerP1, d4BMWhittakerP2]
  have hsqrt : Real.sqrt (Y : ℝ) ≠ 0 := (Real.sqrt_pos.2 Y.2).ne'
  have hYsqrt : (Y : ℂ) = (Real.sqrt (Y : ℝ) : ℂ) ^ (2 : ℕ) := by
    exact_mod_cast (Real.sq_sqrt Y.2.le).symm
  rw [hYsqrt]
  field_simp [hsqrt]
  ring

def d4BMPositiveFrequencyRaiseTwoRaiseZeroWhittakerTail
    (u nu : ℂ) (Y : ℝ) : ℂ :=
  (3 / 4 : ℂ) *
      d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u nu 0 0 Y -
    (3 * (2 * Real.pi : ℂ)) *
      d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u nu 1 1 Y -
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)) *
      (d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu + 1) 1 1 Y +
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu - 1) 1 1 Y) +
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)) *
      d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u nu 2 2 Y +
    (2 * Real.pi : ℂ) ^ (2 : ℕ) *
      (d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu + 1) 2 2 Y +
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu - 1) 2 2 Y) +
    ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)) *
      (d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu + 2) 2 2 Y +
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu - 2) 2 2 Y)

def d4BMPositiveFrequencyLowerNegTwoLowerZeroWhittakerTail
    (u nu : ℂ) (Y : ℝ) : ℂ :=
  (3 / 4 : ℂ) *
      d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u nu 0 0 Y +
    (3 * (2 * Real.pi : ℂ)) *
      d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u nu 1 1 Y -
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)) *
      (d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu + 1) 1 1 Y +
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu - 1) 1 1 Y) +
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)) *
      d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u nu 2 2 Y -
    (2 * Real.pi : ℂ) ^ (2 : ℕ) *
      (d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu + 1) 2 2 Y +
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu - 1) 2 2 Y) +
    ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)) *
      (d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu + 2) 2 2 Y +
        d4BMCompletedEisensteinSqrtPolynomialBesselJetTail u (nu - 2) 2 2 Y)

theorem tendsto_d4BMPositiveFrequencyRaiseTwoRaiseZeroWhittakerTail_atTop_zero
    (u nu : ℂ) :
    Tendsto (d4BMPositiveFrequencyRaiseTwoRaiseZeroWhittakerTail u nu) atTop (𝓝 0) := by
  unfold d4BMPositiveFrequencyRaiseTwoRaiseZeroWhittakerTail
  have h00 := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u nu 0 0
  have h10 := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u nu 1 1
  have h1p := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu + 1) 1 1
  have h1m := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu - 1) 1 1
  have h20 := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u nu 2 2
  have h2p := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu + 1) 2 2
  have h2m := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu - 1) 2 2
  have h2pp := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu + 2) 2 2
  have h2mm := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu - 2) 2 2
  simpa only [mul_zero, sub_zero, add_zero] using
    (((((h00.const_mul (3 / 4 : ℂ)).sub
      (h10.const_mul (3 * (2 * Real.pi : ℂ)))).sub
      ((h1p.add h1m).const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)))).add
      (h20.const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)))).add
      ((h2p.add h2m).const_mul ((2 * Real.pi : ℂ) ^ (2 : ℕ)))).add
      ((h2pp.add h2mm).const_mul ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)))

theorem tendsto_d4BMPositiveFrequencyLowerNegTwoLowerZeroWhittakerTail_atTop_zero
    (u nu : ℂ) :
    Tendsto (d4BMPositiveFrequencyLowerNegTwoLowerZeroWhittakerTail u nu) atTop (𝓝 0) := by
  unfold d4BMPositiveFrequencyLowerNegTwoLowerZeroWhittakerTail
  have h00 := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u nu 0 0
  have h10 := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u nu 1 1
  have h1p := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu + 1) 1 1
  have h1m := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu - 1) 1 1
  have h20 := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u nu 2 2
  have h2p := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu + 1) 2 2
  have h2m := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu - 1) 2 2
  have h2pp := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu + 2) 2 2
  have h2mm := tendsto_d4BMCompletedEisensteinSqrtPolynomialBesselJetTail_atTop_zero u (nu - 2) 2 2
  simpa only [mul_zero, sub_zero, add_zero] using
    (((((h00.const_mul (3 / 4 : ℂ)).add
      (h10.const_mul (3 * (2 * Real.pi : ℂ)))).sub
      ((h1p.add h1m).const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)))).add
      (h20.const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)))).sub
      ((h2p.add h2m).const_mul ((2 * Real.pi : ℂ) ^ (2 : ℕ)))).add
      ((h2pp.add h2mm).const_mul ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ (2 : ℕ)))

end

end RHTower

