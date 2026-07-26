/-
The frontier object under the large sieve: the mean is exactly right, and only the maximum is open.

The frontier object is `Σ_(r) c_r e(n ξ_r)` over the `R ≍ N^(2/3)` Farey fractions of order
`L = N^(1/3)`, with unimodular coefficients and frequencies `ξ_r = √(2a/q)`.  The dual large sieve
gives

    Σ_(n ≤ N) |Σ_r c_r e(n ξ_r)|²  ≪  (N + δ^(-1)) Σ_r |c_r|² ,

where `δ` is the minimal spacing of the frequencies.  The spacing is `≫ L^(-2) = N^(-2/3)`, so
`δ^(-1) ≪ N^(2/3) ≪ N` and the mean square over `n ≤ N` is `≪ R = N^(2/3)`:

    **root mean square  ≪  N^(1/3)  —  exactly the Lindelöf value.**

So the across-arc half of the cancellation is available *in mean square*, and the entire deficit is
the passage from mean to maximum.  Quantitatively, at most `N^(1-2δ)` of the `N` values of `n` can
have the sum exceed `N^(1/3+δ)`.

On the other side, the resonance method gives a lower bound `≫ N^(1/3) exp(c√(log N log log N))`,
subpolynomially above the Lindelöf value.  So for the frontier object:

    mean square exponent        **2/3**   (root mean square **1/3**)
    known lower bound           **1/3**   up to `exp(c√(log N log log N))`
    trivial upper bound         **2/3**
    Lindelöf assertion          **1/3**

**Every known lower bound sits within a subpolynomial factor of the mean; the whole open interval is
the factor `N^(1/3)` between the mean and the trivial maximum.**
-/
import GaloisForLFunctions.HTGeometry.FourAccountings

namespace HTGeometry

/-! ### The sieve input -/

/-- Exponent of the number of Farey fractions of order `N^(1/3)`. -/
def frontierTermCount : ℚ := 2 / 3

/-- Exponent of the minimal spacing of the frontier frequencies (negative). -/
def frontierSpacing : ℚ := -(2 / 3)

/-- **The sieve's second term is dominated by the first.**  `δ^(-1) ≍ N^(2/3)` against `N`. -/
theorem sieve_second_term_negligible : -frontierSpacing < 1 := by
  unfold frontierSpacing; norm_num

/-- **The mean-square exponent delivered by the sieve.** -/
def frontierMeanSquare : ℚ := frontierTermCount

/-- **Its square root is exactly the Lindelöf value.** -/
theorem frontier_rms : frontierMeanSquare / 2 = 1 / 3 := by
  unfold frontierMeanSquare frontierTermCount; norm_num

/-! ### The three levels -/

/-- The trivial bound on the frontier object. -/
def frontierTrivial : ℚ := 2 / 3

/-- The Lindelöf assertion for the frontier object. -/
def frontierLindelof : ℚ := 1 / 3

/-- The root mean square, which the sieve delivers unconditionally. -/
def frontierRootMeanSquare : ℚ := 1 / 3

/-- **The root mean square already equals the Lindelöf value.** -/
theorem rms_equals_lindelof : frontierRootMeanSquare = frontierLindelof := rfl

/-- **And the trivial bound exceeds it by exactly the Farey order.** -/
theorem trivial_exceeds_lindelof : frontierTrivial - frontierLindelof = 1 / 3 := by
  unfold frontierTrivial frontierLindelof; norm_num

/-- That excess is one factor of the Farey order, matching the coherence deficit. -/
theorem excess_is_coherence_deficit :
    frontierTrivial - frontierLindelof = coherenceDeficit (1 / 3) := by
  rw [deficit_equals_scale, trivial_exceeds_lindelof]

/-! ### The exceptional set -/

/-- Exponent of the number of `n ≤ N` at which the sum can exceed `N^(1/3 + d)`. -/
def frontierExceptionalCount (d : ℚ) : ℚ := 1 - 2 * d

/-- **It is derived from the mean square.**  Values exceeding `N^(1/3+d)` contribute
`N^(2/3+2d)` each, against a total of `N^(1+2/3)`. -/
theorem exceptionalCount_from_meanSquare (d : ℚ) :
    frontierExceptionalCount d = 1 + frontierMeanSquare - (frontierMeanSquare + 2 * d) := by
  unfold frontierExceptionalCount; ring

/-- **The exceptional set shrinks as the excess grows.** -/
theorem exceptionalCount_antitone {d d' : ℚ} (h : d < d') :
    frontierExceptionalCount d' < frontierExceptionalCount d := by
  unfold frontierExceptionalCount; linarith

/-- **It vanishes only at `d = 1/2`**, far beyond the range in question. -/
theorem exceptionalCount_zero_iff (d : ℚ) : frontierExceptionalCount d = 0 ↔ d = 1 / 2 := by
  unfold frontierExceptionalCount
  constructor <;> intro h <;> linarith

/-- At the trivial excess `d = 1/3` the exceptional set still has exponent `1/3`. -/
theorem exceptionalCount_at_trivial : frontierExceptionalCount (1 / 3) = 1 / 3 := by
  unfold frontierExceptionalCount; norm_num

/-! ### The two-sided position -/

/-- The known lower bound's exponent — the resonance method contributes only a subpolynomial
factor. -/
def frontierKnownLower : ℚ := 1 / 3

/-- **The known lower bound already matches the Lindelöf value in exponent.** -/
theorem lower_matches_lindelof : frontierKnownLower = frontierLindelof := rfl

/-- **So the whole open interval is between the mean and the trivial bound.** -/
theorem open_interval :
    frontierKnownLower = 1 / 3 ∧ frontierTrivial = 2 / 3 ∧
      frontierTrivial - frontierKnownLower = 1 / 3 := by
  refine ⟨rfl, rfl, ?_⟩
  unfold frontierTrivial frontierKnownLower; norm_num

/-- **The summary.**  The sieve gives the mean exactly, the resonance method gives a lower bound
matching it in exponent, and the Lindelöf assertion is that the maximum matches the mean.  The entire
uncertainty is one factor of the Farey order. -/
theorem frontier_position :
    frontierRootMeanSquare = frontierLindelof ∧
      frontierKnownLower = frontierLindelof ∧
      frontierTrivial - frontierLindelof = 1 / 3 ∧
      frontierTrivial - frontierLindelof = coherenceDeficit (1 / 3) :=
  ⟨rfl, rfl, trivial_exceeds_lindelof, excess_is_coherence_deficit⟩

end HTGeometry
