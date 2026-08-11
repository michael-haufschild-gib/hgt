import GaloisForLFunctions.RHTower.XiResolventMassRigidity

/-!
# The collapse principle and the exact arithmetic target behind the quartic gap

The escape law reads: RH holds iff `(X+1)^4 M X → 0`.  This file settles what kind of bound can
ever realize that decay and isolates the precise arithmetic quantity that remains open.

**The collapse principle.**  If any function `g` eventually dominates the deviation mass and
beats the quartic rate, `(X+1)^4 g X → 0`, then RH follows.  By the quartic rigidity of `M`, such
a bound is therefore never an asymptotic improvement: producing it is *the same problem* as
proving RH, and once produced the mass is identically zero.  This turns the strategic slogan
"beat the exponent four" into a theorem about the solution space of the assignment.

**The arithmetic target.**  Termwise, `‖u‖^2 = Re (u^2) + 2 (Im u)^2`, so the ℓ²-mass of the
resolvent coordinates splits as

`sum_q ‖u_q‖^2 = Re (R_1 X) + 2 M X`,

where `R_1 X = xiResolventMoment 1 X` is the arithmetic second moment — the negative shift
derivative of the Euler-ray response `R_0`, whose value at `X = x^2` is
`logDeriv xi (1/2 + x) / x`.  Hence, at every shift:

* the geometric side always dominates: `Re (R_1 X) ≤ sum_q ‖u_q‖^2`;
* RH holds iff the two agree: `RH ↔ sum_q ‖u_q‖^2 = Re (R_1 X)`;
* and the full assignment reduces to a one-sided estimate: any eventual arithmetic majorant
  `sum_q ‖u_q‖^2 ≤ Re (R_1 X) + g X` with `(X+1)^4 g X → 0` proves RH.

The open core is exactly this last inequality.  The ℓ²-mass is a conjugation-diagonal sum: it
pairs each divisor copy with its own line conjugate.  Every bilinear arithmetic observable —
products of moments, vertical-line second moments of the resolvent trace — is blind to that
diagonal, because reindexing by the conjugation involution converts the twisted double sum into
the plain one.  Extracting the diagonal needs zero-separating technology (Landau-type
exponential sums over ordinates), whose unconditional error terms are far above the required
`o(X^{-4})`.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-! ## §1 The ℓ²-mass decomposition -/

/-- Termwise Pythagoras for the resolvent coordinate:
`‖u‖^2 = Re (u^2) + 2 (Im u)^2`. -/
theorem norm_sq_xiResolventPoint_decomposition (X : ℝ) (q : XiZeroCopy) :
    ‖xiResolventPoint X q‖ ^ 2 =
      ((xiResolventPoint X q) ^ 2).re + 2 * (xiResolventPoint X q).im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, sq, Complex.mul_re]
  ring

theorem summable_norm_sq_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy => ‖xiResolventPoint X q‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    (summable_norm_xiResolventPoint hX)
  have h1 := norm_xiResolventPoint_le_one hX q
  nlinarith [norm_nonneg (xiResolventPoint X q)]

/-- **The ℓ²-mass decomposition**: the square-summed resolvent coordinates are the arithmetic
second moment plus twice the deviation mass. -/
theorem tsum_norm_sq_xiResolventPoint_eq {X : ℝ} (hX : 0 ≤ X) :
    ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ^ 2 =
      (xiResolventMoment 1 X).re + 2 * xiResolventImSqMass X := by
  have hpow := summable_xiResolventPoint_pow hX 1
  have hre : Summable (fun q : XiZeroCopy => ((xiResolventPoint X q) ^ 2).re) := by
    have h := (Complex.hasSum_re hpow.hasSum).summable
    simpa using h
  have him : Summable (fun q : XiZeroCopy => 2 * (xiResolventPoint X q).im ^ 2) :=
    (summable_im_sq_xiResolventPoint hX).mul_left 2
  calc ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ^ 2
      = ∑' q : XiZeroCopy,
          (((xiResolventPoint X q) ^ 2).re + 2 * (xiResolventPoint X q).im ^ 2) :=
        tsum_congr fun q => norm_sq_xiResolventPoint_decomposition X q
    _ = (∑' q : XiZeroCopy, ((xiResolventPoint X q) ^ 2).re) +
          ∑' q : XiZeroCopy, 2 * (xiResolventPoint X q).im ^ 2 :=
        hre.tsum_add him
    _ = (xiResolventMoment 1 X).re + 2 * xiResolventImSqMass X := by
        rw [tsum_mul_left, xiResolventImSqMass, xiResolventMoment]
        congr 1
        rw [Complex.re_tsum hpow]

/-- The geometric side always dominates the arithmetic side. -/
theorem moment_one_re_le_tsum_norm_sq {X : ℝ} (hX : 0 ≤ X) :
    (xiResolventMoment 1 X).re ≤ ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ^ 2 := by
  rw [tsum_norm_sq_xiResolventPoint_eq hX]
  have h : 0 ≤ xiResolventImSqMass X :=
    tsum_nonneg fun q => sq_nonneg (xiResolventPoint X q).im
  linarith

/-- **RH is the equality of geometry and arithmetic**: the ℓ²-mass of the resolvent coordinates
equals the arithmetic second moment exactly on the Riemann hypothesis. -/
theorem riemannHypothesis_iff_tsum_norm_sq_eq_moment_one_re {X : ℝ} (hX : 0 ≤ X) :
    RiemannHypothesis ↔
      ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ^ 2 = (xiResolventMoment 1 X).re := by
  rw [riemannHypothesis_iff_xiResolventImSqMass_eq_zero hX,
    tsum_norm_sq_xiResolventPoint_eq hX]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have hnn : 0 ≤ xiResolventImSqMass X :=
      tsum_nonneg fun q => sq_nonneg (xiResolventPoint X q).im
    linarith

/-! ## §2 The arithmetic identity of the second moment -/

/-- **The second moment is the negative shift derivative of the Euler-ray response**: the
arithmetic side of the target is one derivative of `logDeriv xi` on the real ray. -/
theorem hasDerivAt_xiResolventMoment_zero {X : ℝ} (hX : 0 < X) :
    HasDerivAt (fun v : ℝ => xiResolventMoment 0 v) (-(xiResolventMoment 1 X)) X := by
  have h := hasDerivAt_xiShiftedReciprocalMoment hX 0
  simp only [Nat.cast_zero, zero_add, neg_mul, one_mul] at h
  rw [xiShiftedReciprocalMoment_eq_xiResolventMoment hX.le 1] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hX] with v hv
  exact (xiShiftedReciprocalMoment_eq_xiResolventMoment (le_of_lt hv) 0).symm

/-! ## §3 The collapse principle -/

/-- **The collapse principle**: any eventual majorant of the deviation mass that beats the
quartic rate proves RH.  By quartic rigidity there is no asymptotic route: a successful majorant
certifies that the mass was identically zero. -/
theorem riemannHypothesis_of_mass_eventually_le (g : ℝ → ℝ)
    (hle : ∀ᶠ X : ℝ in atTop, xiResolventImSqMass X ≤ g X)
    (hdecay : Tendsto (fun X : ℝ => (X + 1) ^ 4 * g X) atTop (nhds 0)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_tendsto_quartic_mass_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    have hnn : 0 ≤ xiResolventImSqMass X :=
      tsum_nonneg fun q => sq_nonneg (xiResolventPoint X q).im
    positivity
  · filter_upwards [hle, eventually_ge_atTop (0 : ℝ)] with X hX hX0
    exact mul_le_mul_of_nonneg_left hX (by positivity)

/-- **The exact open target**: an eventual arithmetic majorant of the ℓ²-mass within `o(X^{-4})`
of the arithmetic second moment proves RH.  The reverse inequality holds unconditionally, so the
entire content of RH is this one-sided estimate. -/
theorem riemannHypothesis_of_tsum_norm_sq_eventually_le (g : ℝ → ℝ)
    (hle : ∀ᶠ X : ℝ in atTop, ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ ^ 2 ≤
      (xiResolventMoment 1 X).re + g X)
    (hdecay : Tendsto (fun X : ℝ => (X + 1) ^ 4 * g X) atTop (nhds 0)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_mass_eventually_le (fun X => g X / 2) ?_ ?_
  · filter_upwards [hle, eventually_ge_atTop (0 : ℝ)] with X hX hX0
    have hid := tsum_norm_sq_xiResolventPoint_eq hX0
    linarith
  · have h := hdecay.const_mul (1 / 2 : ℝ)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards with X
    ring

end

end RHTower
