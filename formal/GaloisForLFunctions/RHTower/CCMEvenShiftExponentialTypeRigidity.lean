import GaloisForLFunctions.RHTower.CCMPublishedSourceEvenShiftSieve
import GaloisForLFunctions.RHTower.CCMRestrictedWeilFloorGrowthSpectrum
import Mathlib.Algebra.Polynomial.Div

/-!
# Even-shift sieves preserve the CCM tail frontier

The physical multiplier `1 - exp (-q h)` removes local singularities at `h = 0`, but tends to
one at the infinite aperture boundary.  This file proves the universal rigidity law: for every
positive shift `q`, multiplication by this coboundary preserves zero exponential type for every
eventually nonnegative carrier.

Consequently the shift-two sieve exactly desingularizes the published Gamma density while leaving
the RH-equivalent tail-growth problem of the completed critical-Mellin error unchanged.  This is
an unconditional no-go for using any fixed positive even shift alone to gain the missing half-unit
of continuation.
-/

open Filter

noncomputable section

namespace RHTower

/-- Upper exponential-rate budget for a continuous aperture carrier. -/
def ApertureExponentialUpperBound (eta : ℝ → ℝ) (epsilon : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ h : ℝ in atTop, eta h ≤ C * Real.exp (epsilon * h)

/-- **Complete exponential-spectrum multiplier law.**  An eventually nonnegative carrier and
its product with an eventually positive bounded invertible scalar weight have exactly the same
upper exponential-rate budgets, rate by rate. -/
theorem apertureExponentialUpperBound_mul_iff_of_eventually_bounded
    {weight eta : ℝ → ℝ} {c C epsilon : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hweight : ∀ᶠ h : ℝ in atTop, c ≤ weight h ∧ weight h ≤ C)
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    ApertureExponentialUpperBound (fun h => weight h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta epsilon := by
  constructor
  · rintro ⟨D, hD, hbound⟩
    refine ⟨D / c, div_nonneg hD hc.le, ?_⟩
    filter_upwards [hbound, hweight, heta] with h hh hw heta0
    have hcle : c * eta h ≤ weight h * eta h :=
      mul_le_mul_of_nonneg_right hw.1 heta0
    have hetaDiv : eta h ≤ (weight h * eta h) / c :=
      (le_div_iff₀ hc).2 (by simpa [mul_comm] using hcle)
    calc
      eta h ≤ (weight h * eta h) / c := hetaDiv
      _ ≤ (D * Real.exp (epsilon * h)) / c :=
        div_le_div_of_nonneg_right hh hc.le
      _ = (D / c) * Real.exp (epsilon * h) := by ring
  · rintro ⟨D, hD, hbound⟩
    refine ⟨C * D, mul_nonneg hC hD, ?_⟩
    filter_upwards [hbound, hweight, heta] with h hh hw heta0
    calc
      weight h * eta h ≤ C * eta h :=
        mul_le_mul_of_nonneg_right hw.2 heta0
      _ ≤ C * (D * Real.exp (epsilon * h)) :=
        mul_le_mul_of_nonneg_left hh hC
      _ = (C * D) * Real.exp (epsilon * h) := by ring

/-- **Asymptotic-multiplier rigidity law.**  Multiplying an eventually nonnegative carrier by
any eventually positive, bounded, and bounded-away-from-zero weight preserves zero exponential
type.  This separates local regularization from the infinite-aperture growth frontier. -/
theorem subexponentialAtApertureInfinity_mul_iff_of_eventually_bounded
    {weight eta : ℝ → ℝ} {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hweight : ∀ᶠ h : ℝ in atTop, c ≤ weight h ∧ weight h ≤ C)
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity (fun h => weight h * eta h) ↔
      SubexponentialAtApertureInfinity eta := by
  constructor <;> intro hsub epsilon hepsilon
  · exact (apertureExponentialUpperBound_mul_iff_of_eventually_bounded
      hc hC hweight heta).1 (hsub epsilon hepsilon)
  · exact (apertureExponentialUpperBound_mul_iff_of_eventually_bounded
      hc hC hweight heta).2 (hsub epsilon hepsilon)

/-- A weight converging to a positive constant is automatically invisible to the zero-type
frontier. -/
theorem subexponentialAtApertureInfinity_mul_iff_of_tendsto_pos
    {weight eta : ℝ → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweight : Tendsto weight atTop (nhds ell))
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity (fun h => weight h * eta h) ↔
      SubexponentialAtApertureInfinity eta := by
  have hlower : ∀ᶠ h : ℝ in atTop, ell / 2 ≤ weight h :=
    ((tendsto_order.1 hweight).1 (ell / 2) (by linarith)).mono
      (fun _ hh => hh.le)
  have hupper : ∀ᶠ h : ℝ in atTop, weight h ≤ 2 * ell :=
    ((tendsto_order.1 hweight).2 (2 * ell) (by linarith)).mono
      (fun _ hh => hh.le)
  apply subexponentialAtApertureInfinity_mul_iff_of_eventually_bounded
    (c := ell / 2) (C := 2 * ell) (by positivity) (by positivity)
  · filter_upwards [hlower, hupper] with h hlo hhi
    exact ⟨hlo, hhi⟩
  · exact heta

/-- Rate-by-rate version for every multiplier converging to a positive constant. -/
theorem apertureExponentialUpperBound_mul_iff_of_tendsto_pos
    {weight eta : ℝ → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweight : Tendsto weight atTop (nhds ell))
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound (fun h => weight h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta epsilon := by
  have hlower : ∀ᶠ h : ℝ in atTop, ell / 2 ≤ weight h :=
    ((tendsto_order.1 hweight).1 (ell / 2) (by linarith)).mono
      (fun _ hh => hh.le)
  have hupper : ∀ᶠ h : ℝ in atTop, weight h ≤ 2 * ell :=
    ((tendsto_order.1 hweight).2 (2 * ell) (by linarith)).mono
      (fun _ hh => hh.le)
  apply apertureExponentialUpperBound_mul_iff_of_eventually_bounded
    (c := ell / 2) (C := 2 * ell) (by positivity) (by positivity)
  · filter_upwards [hlower, hupper] with h hlo hhi
    exact ⟨hlo, hhi⟩
  · exact heta

/-- **Necessary boundary-collapse law.**  If multiplication by a convergent nonnegative-limit
weight genuinely creates an exponential upper bound absent from the original carrier, that
weight must converge to zero.  Thus every scalar transform capable of crossing a tail exponent
is necessarily asymptotically noninvertible. -/
theorem tendsto_weight_eq_zero_of_mul_upperBound_of_not_upperBound
    {weight eta : ℝ → ℝ} {ell epsilon : ℝ} (hell : 0 ≤ ell)
    (hweight : Tendsto weight atTop (nhds ell))
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h)
    (hmul : ApertureExponentialUpperBound
      (fun h => weight h * eta h) epsilon)
    (hetaNo : ¬ ApertureExponentialUpperBound eta epsilon) :
    ell = 0 := by
  by_contra hell0
  have hellPos : 0 < ell := lt_of_le_of_ne hell (Ne.symm hell0)
  exact hetaNo ((apertureExponentialUpperBound_mul_iff_of_tendsto_pos
    hellPos hweight heta epsilon).1 hmul)

/-- Absolute physical multiplier of a finite polynomial in one fixed spectral shift. -/
def finiteShiftPolynomialMultiplier (q : ℝ) (P : Polynomial ℝ) (h : ℝ) : ℝ :=
  |P.eval (Real.exp (-q * h))|

/-- Multiplication by an exact exponential attenuation translates the complete upper-rate
spectrum by its attenuation rate. -/
theorem apertureExponentialUpperBound_exp_neg_mul_iff
    (r epsilon : ℝ) (eta : ℝ → ℝ) :
    ApertureExponentialUpperBound
        (fun h => Real.exp (-r * h) * eta h) epsilon ↔
      ApertureExponentialUpperBound eta (epsilon + r) := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with h hh
    have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_pos (r * h)).le
    calc
      eta h = Real.exp (r * h) * (Real.exp (-r * h) * eta h) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp (r * h) * (C * Real.exp (epsilon * h)) := hmul
      _ = C * Real.exp ((epsilon + r) * h) := by
        rw [show (epsilon + r) * h = r * h + epsilon * h by ring,
          Real.exp_add]
        ring
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with h hh
    have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-r * h)).le
    calc
      Real.exp (-r * h) * eta h ≤
          Real.exp (-r * h) * (C * Real.exp ((epsilon + r) * h)) := hmul
      _ = C * Real.exp (epsilon * h) := by
        rw [show epsilon * h = -r * h + (epsilon + r) * h by ring,
          Real.exp_add]
        ring

/-- A finite shift polynomial factored by `X^m` has exactly the attenuation of that valuation. -/
theorem finiteShiftPolynomialMultiplier_X_pow_mul
    (q : ℝ) (m : ℕ) (Q : Polynomial ℝ) (h : ℝ) :
    finiteShiftPolynomialMultiplier q (Polynomial.X ^ m * Q) h =
      Real.exp (-(q * (m : ℝ)) * h) *
        finiteShiftPolynomialMultiplier q Q h := by
  rw [finiteShiftPolynomialMultiplier, finiteShiftPolynomialMultiplier,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, abs_mul, abs_pow]
  rw [show -(q * (m : ℝ)) * h = (m : ℝ) * (-q * h) by ring,
    Real.exp_nat_mul]
  rw [abs_of_pos (Real.exp_pos (-q * h))]

/-- Every finite fixed-shift polynomial has boundary multiplier equal to the absolute value of
its constant term. -/
theorem tendsto_finiteShiftPolynomialMultiplier
    {q : ℝ} (hq : 0 < q) (P : Polynomial ℝ) :
    Tendsto (finiteShiftPolynomialMultiplier q P) atTop
      (nhds |P.eval 0|) := by
  have hexp : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  exact (P.continuousAt.tendsto.comp hexp).abs

/-- **Finite fixed-shift algebra rigidity.**  If a polynomial in a fixed positive spectral shift
has nonzero constant term, it preserves every exponential upper-rate budget of every eventually
nonnegative carrier. -/
theorem apertureExponentialUpperBound_finiteShiftPolynomial_iff
    {q : ℝ} (hq : 0 < q) {P : Polynomial ℝ} (hP : P.eval 0 ≠ 0)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => finiteShiftPolynomialMultiplier q P h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta epsilon := by
  exact apertureExponentialUpperBound_mul_iff_of_tendsto_pos
    (abs_pos.mpr hP) (tendsto_finiteShiftPolynomialMultiplier hq P) heta epsilon

/-- Zero exponential type is invariant under every finite fixed-shift polynomial with nonzero
constant term. -/
theorem subexponentialAtApertureInfinity_finiteShiftPolynomial_iff
    {q : ℝ} (hq : 0 < q) {P : Polynomial ℝ} (hP : P.eval 0 ≠ 0)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => finiteShiftPolynomialMultiplier q P h * eta h) ↔
      SubexponentialAtApertureInfinity eta := by
  exact subexponentialAtApertureInfinity_mul_iff_of_tendsto_pos
    (abs_pos.mpr hP) (tendsto_finiteShiftPolynomialMultiplier hq P) heta

/-- **Valuation law for the finite fixed-shift algebra.**  If `P=X^m Q` with `Q(0)≠0`, then
the valuation `m` translates every aperture exponent by exactly `q*m`; the unit factor `Q` is
completely rate-inert. -/
theorem apertureExponentialUpperBound_finiteShiftValuation_iff
    {q : ℝ} (hq : 0 < q) (m : ℕ) {Q : Polynomial ℝ} (hQ : Q.eval 0 ≠ 0)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => finiteShiftPolynomialMultiplier q (Polynomial.X ^ m * Q) h * eta h)
        epsilon ↔
      ApertureExponentialUpperBound eta (epsilon + q * (m : ℝ)) := by
  have hrewrite : (fun h =>
      finiteShiftPolynomialMultiplier q (Polynomial.X ^ m * Q) h * eta h) =
      (fun h => Real.exp (-(q * (m : ℝ)) * h) *
        (finiteShiftPolynomialMultiplier q Q h * eta h)) := by
    funext h
    rw [finiteShiftPolynomialMultiplier_X_pow_mul]
    ring
  rw [hrewrite, apertureExponentialUpperBound_exp_neg_mul_iff]
  exact apertureExponentialUpperBound_finiteShiftPolynomial_iff
    hq hQ heta (epsilon + q * (m : ℝ))

/-- **Complete finite fixed-shift spectral law.**  For every nonzero polynomial filter, its root
multiplicity at the augmentation point `0` is exactly the translation of the aperture exponent
spectrum. No other polynomial coefficient affects the rate. -/
theorem apertureExponentialUpperBound_finiteShiftPolynomial_complete_iff
    {q : ℝ} (hq : 0 < q) {P : Polynomial ℝ} (hP : P ≠ 0)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => finiteShiftPolynomialMultiplier q P h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta
        (epsilon + q * (P.rootMultiplicity 0 : ℝ)) := by
  let m : ℕ := P.rootMultiplicity 0
  let Q : Polynomial ℝ := P /ₘ (Polynomial.X - Polynomial.C 0) ^ m
  have hfactor : Polynomial.X ^ m * Q = P := by
    simpa only [m, Q, Polynomial.C_0, sub_zero] using
      Polynomial.pow_mul_divByMonic_rootMultiplicity_eq P 0
  have hQ : Q.eval 0 ≠ 0 := by
    simpa only [Q, m] using
      Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hP
  have hleft : (fun h => finiteShiftPolynomialMultiplier q P h * eta h) =
      (fun h => finiteShiftPolynomialMultiplier q (Polynomial.X ^ m * Q) h * eta h) := by
    rw [hfactor]
  rw [hleft]
  simpa only [m] using
    apertureExponentialUpperBound_finiteShiftValuation_iff
      hq m hQ heta epsilon

/-- **Augmentation-ideal necessity.**  If a finite polynomial in a fixed positive shift creates
an exponential upper bound that the original carrier does not possess, its constant term must
vanish. Thus every exponent-changing finite shift filter lies in the augmentation ideal and is
asymptotically noninvertible. -/
theorem finiteShiftPolynomial_eval_zero_of_mul_upperBound_of_not_upperBound
    {q : ℝ} (hq : 0 < q) {P : Polynomial ℝ} {eta : ℝ → ℝ}
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) {epsilon : ℝ}
    (hmul : ApertureExponentialUpperBound
      (fun h => finiteShiftPolynomialMultiplier q P h * eta h) epsilon)
    (hetaNo : ¬ ApertureExponentialUpperBound eta epsilon) :
    P.eval 0 = 0 := by
  have habs : |P.eval 0| = 0 :=
    tendsto_weight_eq_zero_of_mul_upperBound_of_not_upperBound
      (abs_nonneg (P.eval 0)) (tendsto_finiteShiftPolynomialMultiplier hq P)
      heta hmul hetaNo
  exact abs_eq_zero.mp habs

/-- Physical-space coboundary multiplier for a positive spectral translation. -/
def ccmShiftCoboundaryMultiplier (q h : ℝ) : ℝ :=
  1 - Real.exp (-q * h)

/-- A fixed positive shift coboundary is eventually bounded below by one half. -/
theorem eventually_one_half_le_ccmShiftCoboundaryMultiplier
    {q : ℝ} (hq : 0 < q) :
    ∀ᶠ h : ℝ in atTop, 1 / 2 ≤ ccmShiftCoboundaryMultiplier q h := by
  have ht : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  have hevent : ∀ᶠ h : ℝ in atTop, Real.exp (-q * h) < 1 / 2 :=
    ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hevent] with h hh
  rw [ccmShiftCoboundaryMultiplier]
  linarith

/-- On the nonnegative half-line the fixed-shift coboundary lies between zero and one. -/
theorem ccmShiftCoboundaryMultiplier_mem_unitInterval
    {q h : ℝ} (hq : 0 < q) (hh : 0 ≤ h) :
    0 ≤ ccmShiftCoboundaryMultiplier q h ∧
      ccmShiftCoboundaryMultiplier q h ≤ 1 := by
  rw [ccmShiftCoboundaryMultiplier]
  constructor
  · have : Real.exp (-q * h) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by nlinarith)
    simpa using sub_nonneg.mpr this
  · linarith [Real.exp_pos (-q * h)]

/-- The complete rate spectrum of the fixed positive shift sieve is unchanged. -/
theorem apertureExponentialUpperBound_shiftCoboundary_iff
    {q : ℝ} (hq : 0 < q) {eta : ℝ → ℝ}
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => ccmShiftCoboundaryMultiplier q h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta epsilon := by
  apply apertureExponentialUpperBound_mul_iff_of_eventually_bounded
    (c := (1 / 2 : ℝ)) (C := 1) (by norm_num) (by norm_num)
  · filter_upwards [eventually_one_half_le_ccmShiftCoboundaryMultiplier hq,
      eventually_ge_atTop (0 : ℝ)] with h hlo hh0
    exact ⟨hlo, (ccmShiftCoboundaryMultiplier_mem_unitInterval hq hh0).2⟩
  · exact heta

/-- **Fixed-shift exponential-type rigidity.**  Multiplication by `1-exp(-q h)` preserves zero
exponential type for every eventually nonnegative aperture carrier.  The theorem is uniform in
the carrier and in every positive shift length. -/
theorem subexponentialAtApertureInfinity_shiftCoboundary_iff
    {q : ℝ} (hq : 0 < q) {eta : ℝ → ℝ}
    (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => ccmShiftCoboundaryMultiplier q h * eta h) ↔
      SubexponentialAtApertureInfinity eta := by
  apply subexponentialAtApertureInfinity_mul_iff_of_eventually_bounded
    (c := (1 / 2 : ℝ)) (C := 1) (by norm_num) (by norm_num)
  · filter_upwards [eventually_one_half_le_ccmShiftCoboundaryMultiplier hq,
      eventually_ge_atTop (0 : ℝ)] with h hlo hh0
    exact ⟨hlo, (ccmShiftCoboundaryMultiplier_mem_unitInterval hq hh0).2⟩
  · exact heta

/-- **CCM shift-two tail no-go.**  The exact multiplier that removes the published Gamma
singularity cannot improve the exponential type of the completed critical-Mellin error. -/
theorem criticalMellinCompletedError_shiftTwo_subexponential_iff :
    SubexponentialAtApertureInfinity
        (fun h => (1 - Real.exp (-2 * h)) *
          |criticalMellinCompletedError h|) ↔
      SubexponentialAtApertureInfinity
        (fun h => |criticalMellinCompletedError h|) := by
  simpa only [ccmShiftCoboundaryMultiplier] using
    (subexponentialAtApertureInfinity_shiftCoboundary_iff
      (q := (2 : ℝ)) (by norm_num)
      (eta := fun h => |criticalMellinCompletedError h|)
      (Eventually.of_forall fun h => abs_nonneg (criticalMellinCompletedError h)))

/-- Rate-by-rate form of the CCM no-go: the shift-two desingularization preserves every upper
exponential bound of the completed critical-Mellin error, not only the zero-type endpoint. -/
theorem criticalMellinCompletedError_shiftTwo_upperBound_iff (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => (1 - Real.exp (-2 * h)) *
          |criticalMellinCompletedError h|) epsilon ↔
      ApertureExponentialUpperBound
        (fun h => |criticalMellinCompletedError h|) epsilon := by
  simpa only [ccmShiftCoboundaryMultiplier] using
    (apertureExponentialUpperBound_shiftCoboundary_iff
      (q := (2 : ℝ)) (by norm_num)
      (eta := fun h => |criticalMellinCompletedError h|)
      (Eventually.of_forall fun h => abs_nonneg (criticalMellinCompletedError h)) epsilon)

end RHTower
