import GaloisForLFunctions.RHTower.FZZCigarContinuedScreeningMark
import GaloisForLFunctions.RHTower.TrigammaVertical

/-!
# Strict sign of the original continued diagonal insertion

For `alpha=beta=-2-2x`, `0<x<1/2`, the normalized original first mark obeys
`D/FP > (1/(2x)-1/(1+x))/2 > 0`. Since the original finite part is strictly
negative, its actual diagonal insertion is strictly negative as well.

The real logarithmic Gamma derivative is identified with the real part of
complex digamma. The unit-shift recurrence moves both negative arguments to
the positive axis. Strict monotonicity gives a positive lower increment and
bounds the upper increment by `1/(1+x)`. Thus the sign follows from the
original admitted and evaluated source, without a positivity or stationarity
premise. The positive chart covers distances from the first collision pole.

This is one retained position-sector response. Physical parameter transport
and cancellation with the complete FZZ source remain separate obligations.
-/

open Filter Set
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem no_poles {s : ℝ} (hs : 0 < s ∨ (-1 < s ∧ s < 0)) :
    ∀ n : ℕ, s ≠ -n := by
  intro n hn
  rcases hs with hs|hs
  · have hp : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · cases n with
    | zero => norm_num at hn; linarith [hs.2]
    | succ n =>
      have hp : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast at hn
      linarith [hs.1]

private theorem complex_no_poles {s : ℝ} (hs : ∀ n : ℕ, s ≠ -n) :
    ∀ n : ℕ, (s : ℂ) ≠ -(n : ℂ) := by
  intro n hn
  apply hs n
  exact_mod_cast hn

private theorem psi_eq_re (s : ℝ) (hs : ∀ n : ℕ, s ≠ -n) :
    fzzScreeningPlaneGammaLogSlope s = (Complex.digamma (s : ℂ)).re := by
  have hd := (Complex.differentiableAt_Gamma (s : ℂ) (complex_no_poles hs)).hasDerivAt.real_of_complex
  have hr : deriv Real.Gamma s = (deriv Complex.Gamma (s : ℂ)).re := hd.deriv
  simp only [fzzScreeningPlaneGammaLogSlope, hr, Complex.digamma_def, logDeriv_apply,
    Complex.Gamma_ofReal, Complex.div_ofReal_re]

private theorem psi_shift (s : ℝ) (hs : ∀ n : ℕ, s ≠ -n) (hs1 : ∀ n : ℕ, s+1 ≠ -n) :
    fzzScreeningPlaneGammaLogSlope (s+1) = fzzScreeningPlaneGammaLogSlope s + s⁻¹ := by
  rw [psi_eq_re (s+1) hs1, psi_eq_re s hs]
  have hc := congrArg Complex.re (Complex.digamma_apply_add_one (s : ℂ) (complex_no_poles hs))
  have harg : ((s+1 : ℝ) : ℂ) = (s : ℂ)+1 := by push_cast; rfl
  rw [← harg] at hc
  simpa only [Complex.add_re, ← Complex.ofReal_inv, Complex.ofReal_re] using hc

private theorem psi_strictMono {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s < t) :
    fzzScreeningPlaneGammaLogSlope s < fzzScreeningPlaneGammaLogSlope t := by
  rw [psi_eq_re s (no_poles (Or.inl hs)), psi_eq_re t (no_poles (Or.inl ht))]
  exact _root_.RHTower.strictMonoOn_re_digamma_ofReal hs ht hst

private theorem diagonal_slope_lower (x : ℝ) (hx : 0 < x) (hx2 : x < 1/2) :
    0 < (1/(2*x)-1/(1+x))/2 ∧
      (1/(2*x)-1/(1+x))/2 < fzzScreeningPlaneContinuedGammaSlope (-2-2*x) (-2-2*x) := by
  have hfirst := psi_strictMono (by linarith : 0 < 1-2*x) (by linarith : 0 < 1-x) (by linarith)
  have hupper := psi_strictMono (by linarith : 0 < 1+2*x) (by linarith : 0 < 2+x) (by linarith)
  have hpos := psi_shift (1+x) (no_poles (Or.inl (by linarith)))
    (no_poles (Or.inl (by linarith)))
  rw [show 1+x+1 = 2+x by ring] at hpos
  have hneg1 := psi_shift (-x) (no_poles (Or.inr ⟨by linarith,by linarith⟩))
    (no_poles (Or.inl (by linarith)))
  have hneg2 := psi_shift (-2*x) (no_poles (Or.inr ⟨by linarith,by linarith⟩))
    (no_poles (Or.inl (by linarith)))
  rw [show -x+1 = 1-x by ring, inv_neg] at hneg1
  rw [show -2*x+1 = 1-2*x by ring] at hneg2
  have hni : (-2*x)⁻¹ = -(2*x)⁻¹ := by rw [show -2*x = -(2*x) by ring, inv_neg]
  rw [hni] at hneg2
  have hi : 0 < 1/(2*x)-1/(1+x) := by
    rw [one_div, one_div]
    exact sub_pos.mpr (inv_strictAnti₀ (by positivity : 0 < 2*x) (by linarith : 2*x < 1+x))
  refine ⟨div_pos hi (by norm_num), ?_⟩
  unfold fzzScreeningPlaneContinuedGammaSlope
  rw [show -(-2-2*x)/2-(-2-2*x)/2-1 = 1+2*x by ring,
    show 1+(-2-2*x)/2 = -x by ring, show -(-2-2*x)/2 = 1+x by ring,
    show 2+(-2-2*x)/2+(-2-2*x)/2 = -2*x by ring]
  have hi2 : x⁻¹-(2*x)⁻¹ = 1/(2*x) := by
    field_simp [hx.ne'] <;> ring
  rw [one_div] at hi2
  simp only [one_div] at *
  linarith

/-- Positive distance from the first collision pole along the diagonal chart. -/
def fzzScreeningDiagonalDistance (u : ℝ) : ℝ := (1+Real.exp u)⁻¹/2

private theorem diagonal_distance_range (u : ℝ) :
    0 < fzzScreeningDiagonalDistance u ∧ fzzScreeningDiagonalDistance u < 1/2 := by
  have hd : 0 < 1+Real.exp u := by positivity
  have hi := inv_pos.mpr hd
  have hl : (1+Real.exp u)⁻¹ < 1 := (inv_lt_one₀ hd).mpr (by linarith [Real.exp_pos u])
  unfold fzzScreeningDiagonalDistance
  constructor <;> linarith

/-- A strictly positive lower bound for the normalized original diagonal insertion. -/
theorem fzzScreeningPlaneContinuedMark_diagonal_response_lower (u : ℝ) :
    0 < (1/(2*fzzScreeningDiagonalDistance u)-1/(1+fzzScreeningDiagonalDistance u))/2 ∧
      (1/(2*fzzScreeningDiagonalDistance u)-1/(1+fzzScreeningDiagonalDistance u))/2 <
        fzzScreeningPlaneContinuedMark (fzzScreeningFirstContinuationPower u)
          (fzzScreeningFirstContinuationPower u) /
            fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
              (fzzScreeningFirstContinuationPower u) := by
  have hr := diagonal_distance_range u
  have he : fzzScreeningFirstContinuationPower u = -2-2*fzzScreeningDiagonalDistance u := by
    unfold fzzScreeningFirstContinuationPower fzzScreeningDiagonalDistance
    ring
  rw [fzzScreeningPlaneContinuedMark_logResponse, he]
  exact diagonal_slope_lower _ hr.1 hr.2

/-- The actual first diagonal mark is strictly negative, hence never stationary. -/
theorem fzzScreeningPlaneContinuedMark_diagonal_neg (u : ℝ) :
    fzzScreeningPlaneContinuedMark (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower u) < 0 := by
  have h := fzzScreeningPlaneContinuedMark_diagonal_response_lower u
  have hp := lt_trans h.1 h.2
  have hn := fzzScreeningPlaneFinitePart_neg u u
  have hm := mul_neg_of_pos_of_neg hp hn
  rwa [div_mul_cancel₀ _ hn.ne] at hm

end GaloisForLFunctions.RHTower
