import GaloisForLFunctions.RHTower.Suzuki.SuzukiJumpKernelLoewnerGap
import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity
import GaloisForLFunctions.HTGeometry.CompactFourierSineKernel

/-!
# Full-frequency Neumann holonomy in Suzuki affine sewing

The direct Neumann channel `r₀(t) = -|t|/2` cancels from the central residue of Suzuki's
two-shift sewn quotient.  It does not cancel as a spectral function.  For an odd compact source
with characteristic `W` and central jet `d = W'(0)`, its Xi-real normalized reflection-odd
response is

`-d sin(a z) / (2 z W(z))`.

This module proves the exact algebraic consequences:

* affine sewing leaves a projective characteristic holonomy;
* the universal central pole cancels while the centered response survives;
* a finite resolvent update turns the survivor into a centered projective tangent;
* the full jump Pick kernel splits into Euler--Gamma and Neumann-holonomy kernels.

The compact-distribution triangle calculation producing the displayed source response is proved
on paper in the matching pipeline card.  No positivity, RH premise, or numerical computation is
used here.
-/

open Complex Filter Set Topology GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The signed Neumann kernel becomes a smooth affine kernel.  This is the pointwise identity
behind the right-minus-left triangle calculation, including the diagonal value. -/
theorem sign_mul_suzukiNeumannKernel (t : ℝ) :
    (SignType.sign t : ℝ) * (-|t| / 2) = -t / 2 := by
  calc
    (SignType.sign t : ℝ) * (-|t| / 2) =
        -((SignType.sign t : ℝ) * |t|) / 2 := by ring
    _ = -t / 2 := by rw [sign_mul_abs]

/-- Xi-real normalized reflection-odd Neumann response of an odd characteristic.
`centralJet` is the characteristic's first central jet. -/
def suzukiNormalizedNeumannOddResponse
    (a : ℝ) (centralJet : ℂ) (W : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(centralJet * Complex.sin ((a : ℂ) * z)) / (2 * z * W z)

/-- Removing the universal central principal part exposes the projective response. -/
def suzukiCenteredNeumannOddResponse
    (a : ℝ) (centralJet : ℂ) (W : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiNormalizedNeumannOddResponse a centralJet W z + (a : ℂ) / (2 * z)

/-- Exact Neumann survivor under affine sewing to shift zero. -/
def suzukiNeumannHolonomyCorrection
    (a alpha beta : ℝ) (centralJetAlpha centralJetBeta : ℂ)
    (WAlpha WBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((alpha : ℂ) * (beta : ℂ) / ((beta - alpha : ℝ) : ℂ)) *
    (suzukiNormalizedNeumannOddResponse a centralJetBeta WBeta z -
      suzukiNormalizedNeumannOddResponse a centralJetAlpha WAlpha z)

/-- Projective cross numerator of two centrally normalized odd characteristics. -/
def suzukiCenteredProjectiveShiftNumerator
    (centralJetAlpha centralJetBeta : ℂ) (WAlpha WBeta : ℂ → ℂ) (z : ℂ) : ℂ :=
  centralJetAlpha * WBeta z - centralJetBeta * WAlpha z

/-- The universal `-a/(2z)` channel disappears from the difference exactly, before taking any
limit. -/
theorem suzukiNormalizedNeumannOddResponse_sub_eq_centered_sub
    (a : ℝ) (centralJetAlpha centralJetBeta : ℂ)
    (WAlpha WBeta : ℂ → ℂ) (z : ℂ) :
    suzukiNormalizedNeumannOddResponse a centralJetBeta WBeta z -
        suzukiNormalizedNeumannOddResponse a centralJetAlpha WAlpha z =
      suzukiCenteredNeumannOddResponse a centralJetBeta WBeta z -
        suzukiCenteredNeumannOddResponse a centralJetAlpha WAlpha z := by
  simp only [suzukiCenteredNeumannOddResponse]
  ring

/-- The Neumann holonomy is the difference of normalized reciprocal characteristics. -/
theorem suzukiNeumannHolonomyCorrection_eq_normalizedReciprocal
    {a alpha beta : ℝ} (hab : alpha ≠ beta)
    {centralJetAlpha centralJetBeta : ℂ} {WAlpha WBeta : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hWAlpha : WAlpha z ≠ 0) (hWBeta : WBeta z ≠ 0) :
    suzukiNeumannHolonomyCorrection a alpha beta
        centralJetAlpha centralJetBeta WAlpha WBeta z =
      ((alpha : ℂ) * (beta : ℂ) * Complex.sin ((a : ℂ) * z) /
          (2 * z * ((beta - alpha : ℝ) : ℂ))) *
        (centralJetAlpha / WAlpha z - centralJetBeta / WBeta z) := by
  have hden : ((beta - alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab.symm
  simp only [suzukiNeumannHolonomyCorrection, suzukiNormalizedNeumannOddResponse]
  field_simp [hz, hWAlpha, hWBeta, hden]
  ring

/-- Cross-multiplied projective form of the same survivor. -/
theorem suzukiNeumannHolonomyCorrection_eq_projectiveCross
    {a alpha beta : ℝ} (hab : alpha ≠ beta)
    {centralJetAlpha centralJetBeta : ℂ} {WAlpha WBeta : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hWAlpha : WAlpha z ≠ 0) (hWBeta : WBeta z ≠ 0) :
    suzukiNeumannHolonomyCorrection a alpha beta
        centralJetAlpha centralJetBeta WAlpha WBeta z =
      ((alpha : ℂ) * (beta : ℂ) * Complex.sin ((a : ℂ) * z) /
          (2 * z * ((beta - alpha : ℝ) : ℂ))) *
        (suzukiCenteredProjectiveShiftNumerator
          centralJetAlpha centralJetBeta WAlpha WBeta z /
            (WAlpha z * WBeta z)) := by
  rw [suzukiNeumannHolonomyCorrection_eq_normalizedReciprocal hab hz hWAlpha hWBeta]
  simp only [suzukiCenteredProjectiveShiftNumerator]
  field_simp [hWAlpha, hWBeta]

/-- The old central affine cancellation does not extend to functions: affine sewing of the full
shifted responses is the Euler--Gamma sewing plus the explicit holonomy correction. -/
theorem suzukiRealAffineSourceFunction_shiftedNeumann
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    (a : ℝ) (centralJetAlpha centralJetBeta : ℂ)
    (WAlpha WBeta qAlphaEG qBetaEG : ℂ → ℂ) (z : ℂ) :
    suzukiRealAffineSourceFunction alpha beta
        (fun u => qAlphaEG u - (alpha : ℂ) *
          suzukiNormalizedNeumannOddResponse a centralJetAlpha WAlpha u)
        (fun u => qBetaEG u - (beta : ℂ) *
          suzukiNormalizedNeumannOddResponse a centralJetBeta WBeta u) z =
      suzukiRealAffineSourceFunction alpha beta qAlphaEG qBetaEG z +
        suzukiNeumannHolonomyCorrection a alpha beta
          centralJetAlpha centralJetBeta WAlpha WBeta z := by
  have hden : ((beta - alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab.symm
  simp only [suzukiRealAffineSourceFunction, suzukiNeumannHolonomyCorrection]
  field_simp [hden]
  ring

/-- Function-level decomposition of the actual jump candidate into its Euler--Gamma part and
Neumann projective holonomy. -/
theorem suzukiJumpWeylCandidate_shiftedNeumann
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    (a : ℝ) (centralJetAlpha centralJetBeta : ℂ)
    (WAlpha WBeta multiplier qAlphaEG qBetaEG : ℂ → ℂ) (z : ℂ) :
    suzukiJumpWeylCandidate multiplier alpha beta
        (fun u => qAlphaEG u - (alpha : ℂ) *
          suzukiNormalizedNeumannOddResponse a centralJetAlpha WAlpha u)
        (fun u => qBetaEG u - (beta : ℂ) *
          suzukiNormalizedNeumannOddResponse a centralJetBeta WBeta u) z =
      suzukiJumpWeylCandidate multiplier alpha beta qAlphaEG qBetaEG z +
        suzukiNeumannHolonomyCorrection a alpha beta
          centralJetAlpha centralJetBeta WAlpha WBeta z := by
  simp only [suzukiJumpWeylCandidate]
  rw [suzukiRealAffineSourceFunction_shiftedNeumann hab]
  ring

/-- Pick kernels are additive at function level. -/
theorem suzukiScalarPickKernel_add
    (f g : ℂ → ℂ) (z w : ℂ) :
    suzukiScalarPickKernel (fun u => f u + g u) z w =
      suzukiScalarPickKernel f z w + suzukiScalarPickKernel g z w := by
  simp only [suzukiScalarPickKernel, map_add]
  ring

/-- Full Pick-kernel correction: omitting Neumann holonomy drops a genuine kernel, not a scalar
normalization. -/
theorem suzukiScalarPickKernel_jumpWeylCandidate_shiftedNeumann
    {alpha beta : ℝ} (hab : alpha ≠ beta)
    (a : ℝ) (centralJetAlpha centralJetBeta : ℂ)
    (WAlpha WBeta multiplier qAlphaEG qBetaEG : ℂ → ℂ) (z w : ℂ) :
    suzukiScalarPickKernel
        (suzukiJumpWeylCandidate multiplier alpha beta
          (fun u => qAlphaEG u - (alpha : ℂ) *
            suzukiNormalizedNeumannOddResponse a centralJetAlpha WAlpha u)
          (fun u => qBetaEG u - (beta : ℂ) *
            suzukiNormalizedNeumannOddResponse a centralJetBeta WBeta u)) z w =
      suzukiScalarPickKernel
          (suzukiJumpWeylCandidate multiplier alpha beta qAlphaEG qBetaEG) z w +
        suzukiScalarPickKernel
          (suzukiNeumannHolonomyCorrection a alpha beta
            centralJetAlpha centralJetBeta WAlpha WBeta) z w := by
  have hfun :
      suzukiJumpWeylCandidate multiplier alpha beta
          (fun u => qAlphaEG u - (alpha : ℂ) *
            suzukiNormalizedNeumannOddResponse a centralJetAlpha WAlpha u)
          (fun u => qBetaEG u - (beta : ℂ) *
            suzukiNormalizedNeumannOddResponse a centralJetBeta WBeta u) =
        fun u => suzukiJumpWeylCandidate multiplier alpha beta qAlphaEG qBetaEG u +
          suzukiNeumannHolonomyCorrection a alpha beta
            centralJetAlpha centralJetBeta WAlpha WBeta u := by
    funext u
    exact suzukiJumpWeylCandidate_shiftedNeumann hab a centralJetAlpha centralJetBeta
      WAlpha WBeta multiplier qAlphaEG qBetaEG u
  rw [hfun, suzukiScalarPickKernel_add]

/-- Exact finite-update law for the centered projective numerator. -/
theorem suzukiCenteredProjectiveShiftNumerator_finiteUpdate
    (centralJet tangentJet delta : ℂ) (W J : ℂ → ℂ) (z : ℂ) :
    suzukiCenteredProjectiveShiftNumerator centralJet
        (centralJet + delta * tangentJet) W
        (fun u => W u + delta * J u) z =
      delta * (centralJet * J z - tangentJet * W z) := by
  simp only [suzukiCenteredProjectiveShiftNumerator]
  ring

/-- Under the exact second-resolvent update, the shift denominator cancels and the Neumann
survivor is the centered projective tangent divided by the two endpoint characteristics. -/
theorem suzukiNeumannHolonomyCorrection_finiteUpdate
    {a alpha beta : ℝ} (hab : alpha ≠ beta)
    {centralJet tangentJet : ℂ} {W J : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hW : W z ≠ 0)
    (hWnew : W z + (((beta - alpha : ℝ) : ℂ) * J z) ≠ 0) :
    suzukiNeumannHolonomyCorrection a alpha beta centralJet
        (centralJet + (((beta - alpha : ℝ) : ℂ) * tangentJet)) W
        (fun u => W u + (((beta - alpha : ℝ) : ℂ) * J u)) z =
      ((alpha : ℂ) * (beta : ℂ) * Complex.sin ((a : ℂ) * z) / (2 * z)) *
        ((centralJet * J z - tangentJet * W z) /
          (W z * (W z + (((beta - alpha : ℝ) : ℂ) * J z)))) := by
  have hden : ((beta - alpha : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab.symm
  rw [suzukiNeumannHolonomyCorrection_eq_projectiveCross hab hz hW hWnew,
    suzukiCenteredProjectiveShiftNumerator_finiteUpdate]
  field_simp [hz, hW, hWnew, hden]

/-- Dyadic specialization used by the curvature-recurrence-selected pair. -/
theorem suzukiNeumannHolonomyCorrection_dyadic
    {a L : ℝ} (hL : L ≠ 0)
    {centralJetFar centralJetNear : ℂ} {WFar WNear : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hWFar : WFar z ≠ 0) (hWNear : WNear z ≠ 0) :
    suzukiNeumannHolonomyCorrection a (-2 * L) (-L)
        centralJetFar centralJetNear WFar WNear z =
      ((L : ℂ) * Complex.sin ((a : ℂ) * z) / z) *
        (centralJetFar / WFar z - centralJetNear / WNear z) := by
  rw [suzukiNeumannHolonomyCorrection_eq_normalizedReciprocal
    (by
      intro h
      apply hL
      linarith) hz hWFar hWNear]
  push_cast
  field_simp [hL, hz]
  ring

/-- Analytic engine for the far-negative dyadic survivor.  If a normalized characteristic
reciprocal varies differentiably with the resolvent parameter `epsilon`, then the dyadic
difference between parameters `epsilon / 2` and `epsilon`, amplified by `1 / epsilon`, has the
first-order limit with the exact factor `1 / 2`. -/
theorem tendsto_suzukiDyadicReciprocalSecant
    {F : ℂ → ℂ} {d : ℂ} (hF : HasDerivAt F d 0) (hzero : F 0 ≠ 0) :
    Tendsto (fun epsilon : ℂ =>
      ((F (epsilon / 2))⁻¹ - (F epsilon)⁻¹) / epsilon)
      (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (𝓝 (d / (2 * (F 0) ^ (2 : ℕ)))) := by
  have harg : HasDerivAt (fun epsilon : ℂ => epsilon / 2) (1 / 2) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℂ) 0).div_const 2
  have hFzero : HasDerivAt F d ((0 : ℂ) / 2) := by
    simpa using hF
  have hhalf : HasDerivAt (fun epsilon : ℂ => F (epsilon / 2)) (d / 2) 0 := by
    simpa [Function.comp_def, div_eq_mul_inv] using
      HasDerivAt.comp (𝕜 := ℂ) (𝕜' := ℂ) 0 hFzero harg
  have hhalfInv := hhalf.inv (by simpa using hzero)
  have hInv := hF.inv hzero
  have hhalfInv' : HasDerivAt
      (fun epsilon : ℂ => (F (epsilon / 2))⁻¹)
      (-(d / 2) / (F 0) ^ (2 : ℕ)) 0 := by
    have hhalfInv'' := hhalfInv.congr_deriv
      (g' := -(d / 2) / (F 0) ^ (2 : ℕ)) (by norm_num)
    exact hhalfInv''.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  have hdiff : HasDerivAt
      (fun epsilon : ℂ => (F (epsilon / 2))⁻¹ - (F epsilon)⁻¹)
      (d / (2 * (F 0) ^ (2 : ℕ))) 0 := by
    have hraw := hhalfInv'.sub hInv
    have hraw' := hraw.congr_deriv
      (g' := d / (2 * (F 0) ^ (2 : ℕ))) (by
        field_simp [hzero]
        ring)
    exact hraw'.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  simpa [div_eq_inv_mul] using hdiff.tendsto_slope_zero

/-! ## Projective cancellation rigidity -/

/-- **Neumann holonomy projective rigidity.**  Away from the degenerate shift, frequency, and
characteristic divisors, the full-frequency Neumann correction cancels exactly when the two
central jets define the same projective characteristic value. -/
theorem suzukiNeumannHolonomyCorrection_eq_zero_iff_projectiveAlignment
    {a alpha beta : ℝ} (ha : a ≠ 0) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hab : alpha ≠ beta)
    {centralJetAlpha centralJetBeta : ℂ} {WAlpha WBeta : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hsin : Complex.sin ((a : ℂ) * z) ≠ 0)
    (hWAlpha : WAlpha z ≠ 0) (hWBeta : WBeta z ≠ 0) :
    suzukiNeumannHolonomyCorrection a alpha beta
        centralJetAlpha centralJetBeta WAlpha WBeta z = 0 ↔
      centralJetAlpha * WBeta z = centralJetBeta * WAlpha z := by
  rw [suzukiNeumannHolonomyCorrection_eq_projectiveCross hab hz hWAlpha hWBeta]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have halphaC : (alpha : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr halpha
  have hbetaC : (beta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbeta
  have hshiftC : (((beta - alpha : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab.symm
  have hscalar :
      (alpha : ℂ) * (beta : ℂ) * Complex.sin ((a : ℂ) * z) /
          (2 * z * ((beta - alpha : ℝ) : ℂ)) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero halphaC hbetaC) hsin)
      (mul_ne_zero (mul_ne_zero (by norm_num) hz) hshiftC)
  have hWprod : WAlpha z * WBeta z ≠ 0 := mul_ne_zero hWAlpha hWBeta
  simp only [suzukiCenteredProjectiveShiftNumerator]
  constructor
  · intro hzero
    have hquot :
        (centralJetAlpha * WBeta z - centralJetBeta * WAlpha z) /
            (WAlpha z * WBeta z) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hscalar
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp hquot).resolve_right hWprod)
  · intro halign
    rw [sub_eq_zero.mpr halign, zero_div, mul_zero]

/-- The full shifted jump equals its Euler--Gamma truncation exactly on the same projective
alignment locus.  Thus central pole cancellation extends to function-level cancellation only
under this rigidity condition. -/
theorem suzukiJumpWeylCandidate_shiftedNeumann_eq_iff_projectiveAlignment
    {a alpha beta : ℝ} (ha : a ≠ 0) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hab : alpha ≠ beta)
    {centralJetAlpha centralJetBeta : ℂ} {WAlpha WBeta multiplier qAlphaEG qBetaEG : ℂ → ℂ}
    {z : ℂ} (hz : z ≠ 0) (hsin : Complex.sin ((a : ℂ) * z) ≠ 0)
    (hWAlpha : WAlpha z ≠ 0) (hWBeta : WBeta z ≠ 0) :
    suzukiJumpWeylCandidate multiplier alpha beta
        (fun u => qAlphaEG u - (alpha : ℂ) *
          suzukiNormalizedNeumannOddResponse a centralJetAlpha WAlpha u)
        (fun u => qBetaEG u - (beta : ℂ) *
          suzukiNormalizedNeumannOddResponse a centralJetBeta WBeta u) z =
      suzukiJumpWeylCandidate multiplier alpha beta qAlphaEG qBetaEG z ↔
        centralJetAlpha * WBeta z = centralJetBeta * WAlpha z := by
  rw [suzukiJumpWeylCandidate_shiftedNeumann hab]
  simpa using
    (suzukiNeumannHolonomyCorrection_eq_zero_iff_projectiveAlignment
      ha halpha hbeta hab hz hsin hWAlpha hWBeta)

/-- For an exact finite resolvent update, full-frequency cancellation is equivalent to vanishing
of the endpoint/tangent projective determinant. -/
theorem suzukiNeumannHolonomyCorrection_finiteUpdate_eq_zero_iff_projectiveTangent
    {a alpha beta : ℝ} (ha : a ≠ 0) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hab : alpha ≠ beta)
    {centralJet tangentJet : ℂ} {W J : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hsin : Complex.sin ((a : ℂ) * z) ≠ 0)
    (hW : W z ≠ 0)
    (hWnew : W z + (((beta - alpha : ℝ) : ℂ) * J z) ≠ 0) :
    suzukiNeumannHolonomyCorrection a alpha beta centralJet
        (centralJet + (((beta - alpha : ℝ) : ℂ) * tangentJet)) W
        (fun u => W u + (((beta - alpha : ℝ) : ℂ) * J u)) z = 0 ↔
      centralJet * J z = tangentJet * W z := by
  rw [suzukiNeumannHolonomyCorrection_eq_zero_iff_projectiveAlignment
    ha halpha hbeta hab hz hsin hW hWnew]
  have hshiftC : (((beta - alpha : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hab.symm
  constructor
  · intro h
    have hzero : (((beta - alpha : ℝ) : ℂ)) *
        (centralJet * J z - tangentJet * W z) = 0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hshiftC)
  · intro h
    have hzero : centralJet * J z - tangentJet * W z = 0 := sub_eq_zero.mpr h
    linear_combination (((beta - alpha : ℝ) : ℂ)) * hzero

/-! ## `(7)` and `(8)` for a moment source -/

/-- An **odd source**: every even moment vanishes.  This is what oddness of the compactly supported
source gives on its moment sequence. -/
def IsOddSourceMoments (s : ℕ → ℝ) : Prop := ∀ k : ℕ, s (2 * k) = 0

theorem IsOddSourceMoments.zeroth {s : ℕ → ℝ} (h : IsOddSourceMoments s) : s 0 = 0 := by
  simpa using h 0

/-- The moment functional of a constant polynomial is that constant times the zeroth moment. -/
theorem momentFunctional_C (s : ℕ → ℝ) (c : ℝ) :
    HTGeometry.momentFunctional s (Polynomial.C c) = c * s 0 := by
  have hsmul : (Polynomial.C c : Polynomial ℝ) = c • (Polynomial.X : Polynomial ℝ) ^ (0 : ℕ) := by
    rw [pow_zero, Polynomial.smul_eq_C_mul, mul_one]
  rw [hsmul, HTGeometry.momentFunctional_smul, HTGeometry.momentFunctional_X_pow]

/-- **`(7)`.**  For an odd source the right-minus-left Neumann response is the constant `s 1 / 2`:
the smoothed kernel `sgn(t) r₀(t) = -t/2` pairs against the source through its first moment only,
and the `x`-dependent term is killed by the vanishing zeroth moment. -/
theorem momentFunctional_neumannResponseDifference {s : ℕ → ℝ}
    (hs : IsOddSourceMoments s) (x : ℝ) :
    HTGeometry.momentFunctional s
        (Polynomial.C (2⁻¹ : ℝ) * (Polynomial.X - Polynomial.C x)) = s 1 / 2 := by
  have hC : (Polynomial.C (2⁻¹ : ℝ) * Polynomial.C x : Polynomial ℝ)
      = Polynomial.C (x / 2) := by
    rw [← Polynomial.C_mul]
    congr 1
    ring
  have hsplit : (Polynomial.C (2⁻¹ : ℝ) * (Polynomial.X - Polynomial.C x) : Polynomial ℝ)
      = (2⁻¹ : ℝ) • (Polynomial.X : Polynomial ℝ) ^ (1 : ℕ) + Polynomial.C (-(x / 2)) := by
    rw [pow_one, Polynomial.smul_eq_C_mul, mul_sub, hC, Polynomial.C_neg]
    ring
  rw [hsplit, HTGeometry.momentFunctional_add, HTGeometry.momentFunctional_smul,
    HTGeometry.momentFunctional_X_pow, momentFunctional_C, hs.zeroth]
  ring

/-- The response is independent of the evaluation point: this constancy is exactly what makes `(8)`
the Fourier transform of a constant. -/
theorem momentFunctional_neumannResponseDifference_const {s : ℕ → ℝ}
    (hs : IsOddSourceMoments s) (x y : ℝ) :
    HTGeometry.momentFunctional s
        (Polynomial.C (2⁻¹ : ℝ) * (Polynomial.X - Polynomial.C x))
      = HTGeometry.momentFunctional s
        (Polynomial.C (2⁻¹ : ℝ) * (Polynomial.X - Polynomial.C y)) := by
  rw [momentFunctional_neumannResponseDifference hs x,
    momentFunctional_neumannResponseDifference hs y]

/-- **`(8)`.**  Half the compact Fourier transform of the constant response over `[-a, a]` is the
first moment carried by the sine kernel. -/
theorem half_integral_neumannResponseDifference_eq_sineKernel
    (s : ℕ → ℝ) (a : ℝ) {z : ℂ} (hz : z ≠ 0) :
    (2⁻¹ : ℂ) *
        ∫ y in (-a : ℝ)..a, ((s 1 / 2 : ℝ) : ℂ) * Complex.exp (I * z * (y : ℝ))
      = (s 1 : ℂ) * Complex.sin ((a : ℂ) * z) / (2 * z) := by
  rw [GaloisForLFunctions.HTGeometry.integral_const_mul_exp_mul_I_symm a
    ((s 1 / 2 : ℝ) : ℂ) z hz]
  push_cast
  field_simp

end

end RHTower
