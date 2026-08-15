import GaloisForLFunctions.RHTower.SuzukiOnePrimeTerminalPrunedPropagator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Terminal one-prime channels and the degree of the pruned propagator

Below the second-prime aperture threshold the surviving one-prime valuation sites are `0` and `1`.
Which of them a fixed puncture orientation actually sees is decided by the aperture itself:

* `2a < log 2` — only the physical root survives, and the compressed prime block at that single
  site is zero;
* `2a = log 2` — the two sites are the two opposite endpoints, whose inward orientations are
  opposite, so no orientation sees both;
* `log 2 < 2a < log 3` — site `1` is strictly interior and is seen by every orientation, while the
  root endpoint is seen only by the inward one.  Exactly one orientation per root therefore
  carries the two-site involution; the other carries the zero block.

The terminal transport group is consequently of degree zero, so at Gamma height `σ = 3/4` the slow
exponent is `p = 5/4` and both the homogeneous tail `x^{-p}` and the second near-end remainder
`x^{1-N}`, `N = 2`, are square integrable past the frequency origin.
-/

namespace RHTower

noncomputable section

open MeasureTheory Set

open scoped Matrix Matrix.Norms.Operator

/-! ## Sub-threshold aperture: only the root site survives -/

/-- Below the first prime displacement, the closed aperture contains only the root valuation. -/
theorem onePrime_terminal_index_eq_zero (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 2) (hn0 : 0 ≤ n)
    (hn : (n : ℝ) * Real.log 2 ≤ 2 * a) : n = 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnlt : n < 1 := by
    by_contra h
    have h1n : (1 : ℤ) ≤ n := by omega
    have h1nR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1n
    have hmul : (1 : ℝ) * Real.log 2 ≤ (n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h1nR hlog2.le
    linarith
  omega

/-- Right-rooted sub-threshold confinement. -/
theorem onePrimeRightCenter_index_eq_zero (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 2)
    (hx : onePrimeRightCenter a n ∈ Set.Icc (-a) a) : n = 0 := by
  rw [onePrimeRightCenter_mem_Icc_iff] at hx
  exact onePrime_terminal_index_eq_zero a n hA
    (onePrimeDisplacement_nonneg_iff n |>.mp hx.1) hx.2

/-- Left-rooted sub-threshold confinement. -/
theorem onePrimeLeftCenter_index_eq_zero (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 2)
    (hx : onePrimeLeftCenter a n ∈ Set.Icc (-a) a) : n = 0 := by
  rw [onePrimeLeftCenter_mem_Icc_iff] at hx
  exact onePrime_terminal_index_eq_zero a n hA
    (onePrimeDisplacement_nonneg_iff n |>.mp hx.1) hx.2

/-- **The one-site compressed block vanishes.**  A carrier state supported on the root valuation
alone is annihilated by the compression of the symmetric literal weighted shift, because both of
its neighbours are outside the surviving support. -/
theorem onePrimeTerminalCompression_eq_zero_of_rootSupported
    (f : SuzukiOnePrimeFractionalCarrier)
    (hsupp : ∀ n : ℤ, n ≠ 0 → f (onePrimeValuation n) = 0) :
    suzukiOnePrimeFractionalOrbitShiftCLM onePrimeForwardStep f (onePrimeValuation 0) +
        suzukiOnePrimeFractionalOrbitShiftCLM (-onePrimeForwardStep) f
          (onePrimeValuation 0) = 0 := by
  simp only [suzukiOnePrimeFractionalOrbitShiftCLM_apply]
  have hp : onePrimeValuation 0 + onePrimeForwardStep = onePrimeValuation 1 := by
    funext j
    simp [onePrimeValuation, onePrimeForwardStep]
  have hm : onePrimeValuation 0 + -onePrimeForwardStep = onePrimeValuation (-1) := by
    funext j
    simp [onePrimeValuation, onePrimeForwardStep]
  rw [hp, hm, hsupp 1 (by norm_num), hsupp (-1) (by norm_num)]
  ring

/-! ## The two terminal centers -/

/-- The root site is the aperture endpoint itself. -/
theorem onePrimeRightCenter_zero (a : ℝ) : onePrimeRightCenter a 0 = a := by
  simp [onePrimeRightCenter, onePrimeDisplacement]

theorem onePrimeLeftCenter_zero (a : ℝ) : onePrimeLeftCenter a 0 = -a := by
  simp [onePrimeLeftCenter, onePrimeDisplacement]

theorem onePrimeRightCenter_one (a : ℝ) :
    onePrimeRightCenter a 1 = a - Real.log 2 := by
  simp [onePrimeRightCenter, onePrimeDisplacement]

theorem onePrimeLeftCenter_one (a : ℝ) :
    onePrimeLeftCenter a 1 = -a + Real.log 2 := by
  simp [onePrimeLeftCenter, onePrimeDisplacement]

/-! ## Resonant aperture: the two sites are opposite endpoints -/

/-- At the resonant aperture the first prime site is the opposite endpoint. -/
theorem onePrimeRightCenter_one_eq_neg_of_resonant (a : ℝ) (h : 2 * a = Real.log 2) :
    onePrimeRightCenter a 1 = -a := by
  rw [onePrimeRightCenter_one]
  linarith

/-- **Opposite inward orientations.**  At the resonant aperture no puncture orientation activates
both terminal sites: the right endpoint is entered only from below, the left endpoint only from
above.  Every fixed-orientation compressed block is therefore one-site. -/
theorem onePrimeResonant_not_both_active (a o L : ℝ) (h : 2 * a = Real.log 2) :
    ¬ (GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff a
          (onePrimeRightCenter a 0) o L ≠ 0 ∧
        GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff a
          (onePrimeRightCenter a 1) o L ≠ 0) := by
  rintro ⟨h0, h1⟩
  have he : 0 < Real.exp (-L) := Real.exp_pos _
  have hi0 := (GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff_ne_zero_iff a
    (onePrimeRightCenter a 0) o L).mp h0
  have hi1 := (GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff_ne_zero_iff a
    (onePrimeRightCenter a 1) o L).mp h1
  rw [onePrimeRightCenter_zero] at hi0
  rw [onePrimeRightCenter_one_eq_neg_of_resonant a h] at hi1
  have hneg : o * Real.exp (-L) < 0 := by linarith [hi0.2]
  have hpos : 0 < o * Real.exp (-L) := by linarith [hi1.1]
  linarith

/-! ## Interior window: one orientation carries the involution, the other the zero block -/

/-- Above the resonant aperture the first prime site is strictly interior. -/
theorem onePrimeRightCenter_one_mem_Ioo (a : ℝ) (h : Real.log 2 < 2 * a) :
    onePrimeRightCenter a 1 ∈ Set.Ioo (-a) a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [onePrimeRightCenter_one]
  exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩

/-- The outward orientation never sees the root endpoint. -/
theorem onePrimeRightRoot_cutoff_eq_zero_of_outward (a o L : ℝ) (ho : 0 < o) :
    GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff a
      (onePrimeRightCenter a 0) o L = 0 := by
  by_contra hne
  have hi := (GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff_ne_zero_iff a
    (onePrimeRightCenter a 0) o L).mp hne
  rw [onePrimeRightCenter_zero] at hi
  have he : 0 < Real.exp (-L) := Real.exp_pos _
  nlinarith [hi.2]

/-- The inward orientation does see the root endpoint, once the physical scale is finer than the
aperture. -/
theorem onePrimeRightRoot_cutoff_ne_zero_of_inward (a o L : ℝ)
    (ho : o < 0) (ho1 : -1 ≤ o) (hL : Real.exp (-L) < 2 * a) :
    GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff a
      (onePrimeRightCenter a 0) o L ≠ 0 := by
  have he : 0 < Real.exp (-L) := Real.exp_pos _
  rw [GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff_ne_zero_iff,
    onePrimeRightCenter_zero]
  refine ⟨?_, ?_⟩
  · nlinarith
  · nlinarith

/-- The strictly interior first prime site is seen by every orientation once the physical scale is
finer than both of its distances to the walls. -/
theorem onePrimeRightSite_one_cutoff_ne_zero_of_interior (a o L : ℝ) (ho : |o| ≤ 1)
    (hL : Real.exp (-L) < min (2 * a - Real.log 2) (Real.log 2)) :
    GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff a
      (onePrimeRightCenter a 1) o L ≠ 0 := by
  have he : 0 < Real.exp (-L) := Real.exp_pos _
  have hoo := abs_le.mp ho
  have hL1 : Real.exp (-L) < 2 * a - Real.log 2 := lt_of_lt_of_le hL (min_le_left _ _)
  have hL2 : Real.exp (-L) < Real.log 2 := lt_of_lt_of_le hL (min_le_right _ _)
  have hbound : -Real.exp (-L) ≤ o * Real.exp (-L) ∧ o * Real.exp (-L) ≤ Real.exp (-L) := by
    constructor <;> nlinarith [hoo.1, hoo.2]
  rw [GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff_ne_zero_iff,
    onePrimeRightCenter_one]
  exact ⟨by linarith [hbound.1], by linarith [hbound.2]⟩

/-! ## Degree of the terminal transport group -/

/-- **The terminal one-prime propagator has degree zero.**  Its uniform bound holds with the
constant `1 + ‖B‖` and no power of the frequency, for every real literal prime coupling. -/
theorem onePrimeTerminalGroup_degree_zero :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c t : ℝ,
      ‖NormedSpace.exp (((-(t : ℂ) * Complex.I)) •
          (((c : ℝ) : ℂ) • onePrimeTerminalAdjacency))‖ ≤ C * (1 + |t|) ^ (0 : ℝ) := by
  refine ⟨1 + ‖onePrimeTerminalAdjacency‖, by positivity, fun c t => ?_⟩
  rw [Real.rpow_zero, mul_one]
  exact norm_exp_real_smul_onePrimeTerminalAdjacency_le c t

/-! ## Square integrability of the tails at the degree-zero exponent -/

/-- A power tail decaying faster than the square-root threshold is square integrable past the
frequency origin. -/
theorem integrableOn_sq_rpow_neg_of_half_lt {p : ℝ} (hp : 1 / 2 < p) :
    IntegrableOn (fun x : ℝ => (x ^ (-p)) ^ 2) (Ioi 1) volume := by
  have h : IntegrableOn (fun x : ℝ => x ^ (-(2 * p))) (Ioi 1) volume :=
    (integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  show x ^ (-(2 * p)) = (x ^ (-p)) ^ 2
  have hsplit : -(2 * p) = -p + -p := by ring
  rw [hsplit, Real.rpow_add hx0, ← pow_two]

/-- The slow exponent at Gamma height `3/4` is `5/4`. -/
theorem onePrimeSlowExponent : (1 : ℝ) / 2 + 3 / 4 = 5 / 4 := by norm_num

/-- The homogeneous terminal tail at Gamma height `3/4` is square integrable. -/
theorem integrableOn_sq_onePrimeSlowTail :
    IntegrableOn (fun x : ℝ => (x ^ (-(5 / 4 : ℝ))) ^ 2) (Ioi 1) volume :=
  integrableOn_sq_rpow_neg_of_half_lt (by norm_num)

/-- Every near-end remainder from the second order on is square integrable. -/
theorem integrableOn_sq_onePrimeNearEndRemainder (N : ℕ) (hN : 2 ≤ N) :
    IntegrableOn (fun x : ℝ => (x ^ ((1 : ℝ) - (N : ℝ))) ^ 2) (Ioi 1) volume := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hrw : (1 : ℝ) - (N : ℝ) = -((N : ℝ) - 1) := by ring
  rw [hrw]
  exact integrableOn_sq_rpow_neg_of_half_lt (by linarith)

end

end RHTower
