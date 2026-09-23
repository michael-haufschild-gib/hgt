import GaloisForLFunctions.HTGeometry.MaximumTermProfileMoments
import GaloisForLFunctions.HTGeometry.MaximumTermWindowMoments
import GaloisForLFunctions.HTGeometry.ShiftedGeometricTails
import GaloisForLFunctions.HTGeometry.CentralIndexWindowLipschitz

/-!
# The Wiman--Valiron estimate at a window of half-width `N`

All the pieces meet here.  At a maximum-modulus point of the circle where the modulus is critical
along the circle, the three moments of the coefficient profile are controlled by one window of
half-width `N`: Bessel bounds the window's mass by `sqrt(2N+1)` times the value, and the Gaussian
decay bounds the tails.  Feeding those into the profile form of the estimate gives

`|z f'/f - nu| <= (sqrt(2N+1) + 2 G_0) |Lambda - nu|
                  + sqrt(2 (N^(2 : ℕ) sqrt(2N+1) + 2 G_2) (sqrt(2N+1) + 2 G_0))`,

where `G_0` and `G_2` bound the two shifted geometric tails at rate `N/(4L)`.

Every occurrence of the central index has disappeared from the right-hand side: the estimate is
governed by the window half-width and the tail sums alone.  With `N` of order `sqrt(L)` the tails are
negligible and the bound is of order `L^{3/4}`, where `L` is the Lipschitz constant of the central
index on the window.
-/

open MeasureTheory Complex

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ} {r : ℝ}

/-! ## Scaling the moments to the normalised profile -/

/-- The modulus of a normalised coefficient is its term divided by the maximum term. -/
private theorem norm_normalisedCoeff_eq
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) (n : ℕ) :
    ‖normalisedCoeff a r z n‖ = (‖a n‖ * r ^ n) / maxTerm a r := by
  have hCn : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  rw [normalisedCoeff_def, norm_div, hCn, norm_mul, norm_pow, hz]

/-- The total mass of the normalised profile. -/
private theorem tsum_norm_normalisedCoeff_eq
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) :
    ∑' n : ℕ, ‖normalisedCoeff a r z n‖ = coeffSum a r / maxTerm a r := by
  rw [coeffSum, ← tsum_div_const]
  exact tsum_congr fun n => norm_normalisedCoeff_eq ha hr hn₀ hz n

/-- The second moment of the normalised profile. -/
private theorem tsum_sq_norm_normalisedCoeff_eq
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) :
    ∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ)) ^ (2 : ℕ) * ‖normalisedCoeff a r z n‖
      = (∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n)) / maxTerm a r := by
  rw [← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [norm_normalisedCoeff_eq ha hr hn₀ hz n]
  ring

/-! ## The estimate -/

set_option maxHeartbeats 1000000 in
/-- **The Wiman--Valiron estimate at a window of half-width `N`.**  At a maximum-modulus point where
the modulus is critical along the circle, the logarithmic derivative differs from the central index
by at most the mean-minus-mode gap inflated by `sqrt(2N+1)` plus the geometric mean of the second
moment and the total misalignment — both measured against the value, not against the maximum term. -/
theorem norm_mul_logDeriv_sub_centralIndex_le_window
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    {N : ℕ} (hN0 : 0 < N) (hNK : (N : ℝ) ≤ 2 * L * H) (hNv : 2 * L * v₀ ≤ (N : ℝ))
    (hlipA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    (hlipB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {z : ℂ} (hz : ‖z‖ = Real.exp x)
    (hfz : maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖)
    (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 (Real.exp x) θ)‖ ≤ ‖coeffFun a z‖)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a (Real.exp x) z n
      = ((‖∑' n : ℕ, normalisedCoeff a (Real.exp x) z n‖ : ℝ) : ℂ) * u)
    {G₀ G₂ : ℝ}
    (hG₀ : ∑' j : ℕ, Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j) ≤ G₀)
    (hG₂ : ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ (2 : ℕ)
        * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j) ≤ G₂) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
      ≤ (Real.sqrt (2 * (N : ℝ) + 1) + 2 * G₀)
          * |meanIndex a (Real.exp x) - (centralIndex a (Real.exp x) : ℝ)|
        + Real.sqrt (2 * ((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1) + 2 * G₂)
            * (Real.sqrt (2 * (N : ℝ) + 1) + 2 * G₀)) := by
  classical
  set r : ℝ := Real.exp x with hrdef
  have hr : 0 < r := Real.exp_pos x
  set v : ℕ := centralIndex a r with hv
  set μ : ℝ := maxTerm a r with hμdef
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hfz
  have hμne : μ ≠ 0 := by rw [hμdef]; exact ne_of_gt hμpos
  have hfne : ‖coeffFun a z‖ ≠ 0 := ne_of_gt hfpos
  set A : ℝ := ‖coeffFun a z‖ / μ with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ hμpos, one_mul]
    exact hfz
  have hAmul : A * μ = ‖coeffFun a z‖ := by
    rw [hA, div_mul_cancel₀ _ hμne]
  -- the tail sums are nonnegative
  have hG₀nn : (0 : ℝ) ≤ G₀ :=
    le_trans (tsum_nonneg fun j => pow_nonneg (Real.exp_pos _).le _) hG₀
  have hG₂nn : (0 : ℝ) ≤ G₂ := by
    refine le_trans (tsum_nonneg fun j => ?_) hG₂
    exact mul_nonneg (sq_nonneg _) (pow_nonneg (Real.exp_pos _).le _)
  set S : ℝ := Real.sqrt (2 * (N : ℝ) + 1) with hS
  have hSnn : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  -- the window sum
  have hcard : ((Finset.Ico (v - N) (v + N + 1)).card : ℝ) ≤ 2 * (N : ℝ) + 1 := by
    have h := Nat.card_Ico (v - N) (v + N + 1)
    have hle : (Finset.Ico (v - N) (v + N + 1)).card ≤ 2 * N + 1 := by
      rw [h]; omega
    calc ((Finset.Ico (v - N) (v + N + 1)).card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
          exact_mod_cast hle
      _ = 2 * (N : ℝ) + 1 := by push_cast; ring
  have hwin : ∑ n ∈ Finset.Ico (v - N) (v + N + 1), ‖a n‖ * r ^ n ≤ S * ‖coeffFun a z‖ := by
    refine le_trans (sum_window_le_sqrt_card_mul_bound ha hr.le (norm_nonneg _) hmax _) ?_
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard) (norm_nonneg _)
  -- the zeroth moment
  have hzeroth : coeffSum a r ≤ S * ‖coeffFun a z‖ + 2 * μ * G₀ := by
    refine le_trans (coeffSum_le_gaussian ha hn₀ hH hL hN0 hNK hNv hlipA hlipB hwin) ?_
    have := mul_le_mul_of_nonneg_left hG₀ (by positivity : (0 : ℝ) ≤ 2 * μ)
    linarith
  -- the second moment
  have hsecond : ∑' n : ℕ, ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n)
      ≤ (N : ℝ) ^ (2 : ℕ) * (S * ‖coeffFun a z‖) + 2 * μ * G₂ := by
    refine le_trans (tsum_index_sq_le_gaussian ha hn₀ hH hL hN0 hNK hNv hlipA hlipB hwin) ?_
    have := mul_le_mul_of_nonneg_left hG₂ (by positivity : (0 : ℝ) ≤ 2 * μ)
    linarith
  -- normalised versions
  have hmulS : S * A * μ = S * ‖coeffFun a z‖ := by
    rw [mul_assoc, hAmul]
  have hSig0 : ∑' n : ℕ, ‖normalisedCoeff a r z n‖ ≤ S * A + 2 * G₀ := by
    rw [tsum_norm_normalisedCoeff_eq ha hr hn₀ hz, div_le_iff₀ hμpos]
    calc coeffSum a r ≤ S * ‖coeffFun a z‖ + 2 * μ * G₀ := hzeroth
      _ = (S * A + 2 * G₀) * μ := by rw [← hmulS]; ring
  have hSig2 : ∑' n : ℕ, ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * ‖normalisedCoeff a r z n‖
      ≤ (N : ℝ) ^ (2 : ℕ) * (S * A) + 2 * G₂ := by
    rw [tsum_sq_norm_normalisedCoeff_eq ha hr hn₀ hz, div_le_iff₀ hμpos]
    calc ∑' n : ℕ, ((n : ℝ) - (v : ℝ)) ^ (2 : ℕ) * (‖a n‖ * r ^ n)
        ≤ (N : ℝ) ^ (2 : ℕ) * (S * ‖coeffFun a z‖) + 2 * μ * G₂ := hsecond
      _ = ((N : ℝ) ^ (2 : ℕ) * (S * A) + 2 * G₂) * μ := by rw [← hmulS]; ring
  -- the alignment defect
  have hWnorm : ‖∑' n : ℕ, normalisedCoeff a r z n‖ = A := by
    have hCnorm : ‖a v * z ^ v‖ = μ := by
      rw [norm_mul, norm_pow, hz]
      exact term_centralIndex_eq ha hr hn₀
    have hfac : coeffFun a z = (a v * z ^ v) * ∑' n : ℕ, normalisedCoeff a r z n :=
      coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
    rw [hA, hfac, norm_mul, hCnorm]
    exact (mul_div_cancel_left₀ _ hμne).symm
  have hD : ∑' n : ℕ, (‖normalisedCoeff a r z n‖
      - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ S * A + 2 * G₀ - A := by
    rw [tsum_normalised_defect_eq ha hr hn₀ hz hu hWdir, hWnorm,
      tsum_norm_normalisedCoeff_eq ha hr hn₀ hz] at *
    have hSig : coeffSum a r / μ ≤ S * A + 2 * G₀ := by
      rw [div_le_iff₀ hμpos]
      calc coeffSum a r ≤ S * ‖coeffFun a z‖ + 2 * μ * G₀ := hzeroth
        _ = (S * A + 2 * G₀) * μ := by rw [← hmulS]; ring
    linarith
  -- the profile estimate
  have hprofile := norm_mul_logDeriv_sub_centralIndex_le_profile ha hr hn₀ hz hfz hcrit hu hWdir
    hSig2 hD
  refine le_trans hprofile ?_
  -- bound the two pieces
  set S₂ : ℝ := (N : ℝ) ^ (2 : ℕ) * (S * A) + 2 * G₂ with hS₂def
  set Dv : ℝ := S * A + 2 * G₀ - A with hDvdef
  set C : ℝ := Real.sqrt (2 * ((N : ℝ) ^ (2 : ℕ) * S + 2 * G₂) * (S + 2 * G₀)) with hC
  have hCnn : (0 : ℝ) ≤ C := Real.sqrt_nonneg _
  have hS₂A : S₂ ≤ A * ((N : ℝ) ^ (2 : ℕ) * S + 2 * G₂) := by
    rw [hS₂def]
    nlinarith [hA1, hG₂nn, hSnn, sq_nonneg ((N : ℝ))]
  have hDvA : Dv ≤ A * (S + 2 * G₀) := by
    rw [hDvdef]
    nlinarith [hA1, hG₀nn, hSnn]
  have hS₂nn : (0 : ℝ) ≤ S₂ := by
    rw [hS₂def]; positivity
  have hDvnn : (0 : ℝ) ≤ Dv := by
    refine le_trans (tsum_nonneg fun n => alignment_defect_nonneg _ hu) hD
  have hsqrtle : Real.sqrt (2 * S₂ * Dv) ≤ A * C := by
    have hkey : 2 * S₂ * Dv ≤ (A * C) ^ (2 : ℕ) := by
      have hCsq : C ^ (2 : ℕ) = 2 * ((N : ℝ) ^ (2 : ℕ) * S + 2 * G₂) * (S + 2 * G₀) := by
        rw [hC, Real.sq_sqrt (by positivity)]
      have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) * S + 2 * G₂ := by positivity
      have h2 : (0 : ℝ) ≤ S + 2 * G₀ := by positivity
      calc 2 * S₂ * Dv ≤ 2 * (A * ((N : ℝ) ^ (2 : ℕ) * S + 2 * G₂)) * (A * (S + 2 * G₀)) := by
            have hstep : S₂ * Dv ≤ (A * ((N : ℝ) ^ (2 : ℕ) * S + 2 * G₂)) * (A * (S + 2 * G₀)) := by
              have hAD : (0 : ℝ) ≤ A * ((N : ℝ) ^ (2 : ℕ) * S + 2 * G₂) := by positivity
              nlinarith [hS₂A, hDvA, hS₂nn, hDvnn]
            linarith
        _ = A ^ (2 : ℕ) * (2 * ((N : ℝ) ^ (2 : ℕ) * S + 2 * G₂) * (S + 2 * G₀)) := by ring
        _ = (A * C) ^ (2 : ℕ) := by rw [mul_pow, hCsq]
    have hAC : (0 : ℝ) ≤ A * C := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * S₂ * Dv by positivity),
      Real.sqrt_nonneg (2 * S₂ * Dv), hkey, hAC]
  have hcoeff : coeffSum a r / ‖coeffFun a z‖ ≤ S + 2 * G₀ := by
    rw [div_le_iff₀ hfpos]
    nlinarith [hzeroth, hfz, hG₀nn]
  have habs : (0 : ℝ) ≤ |meanIndex a r - (v : ℝ)| := abs_nonneg _
  have hmuf : μ / ‖coeffFun a z‖ = 1 / A := by
    rw [hA, one_div_div]
  calc (coeffSum a r * |meanIndex a r - (v : ℝ)| + Real.sqrt (2 * S₂ * Dv) * μ)
        / ‖coeffFun a z‖
      = (coeffSum a r / ‖coeffFun a z‖) * |meanIndex a r - (v : ℝ)|
        + Real.sqrt (2 * S₂ * Dv) * (μ / ‖coeffFun a z‖) := by
        rw [add_div, ← div_mul_eq_mul_div, mul_div_assoc]
    _ ≤ (S + 2 * G₀) * |meanIndex a r - (v : ℝ)| + (A * C) * (1 / A) := by
        rw [hmuf]
        exact add_le_add (mul_le_mul_of_nonneg_right hcoeff habs)
          (mul_le_mul_of_nonneg_right hsqrtle (by positivity))
    _ = (S + 2 * G₀) * |meanIndex a r - (v : ℝ)| + C := by
        rw [mul_one_div, mul_comm A C, mul_div_assoc, div_self (ne_of_gt hApos), mul_one]

/-- **The Wiman--Valiron estimate with the tails summed.**  The two shifted geometric series have
closed forms, so the window estimate becomes explicit in the window half-width `N` and the Lipschitz
constant `L` alone. -/
theorem norm_mul_logDeriv_sub_centralIndex_le_explicit_window
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    {N : ℕ} (hN0 : 0 < N) (hNK : (N : ℝ) ≤ 2 * L * H) (hNv : 2 * L * v₀ ≤ (N : ℝ))
    (hlipA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    (hlipB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {z : ℂ} (hz : ‖z‖ = Real.exp x)
    (hfz : maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖)
    (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 (Real.exp x) θ)‖ ≤ ‖coeffFun a z‖)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a (Real.exp x) z n
      = ((‖∑' n : ℕ, normalisedCoeff a (Real.exp x) z n‖ : ℝ) : ℂ) * u) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
      ≤ (Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
              / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
          * |meanIndex a (Real.exp x) - (centralIndex a (Real.exp x) : ℝ)|
        + Real.sqrt (2 * ((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1)
              + 2 * (2 * ((N : ℝ) + 1) ^ (2 : ℕ) * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                  / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ (3 : ℕ)))
            * (Real.sqrt (2 * (N : ℝ) + 1)
              + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                  / (1 - Real.exp (-((N : ℝ) / (4 * L))))))) := by
  have hq0 : (0 : ℝ) < Real.exp (-((N : ℝ) / (4 * L))) := Real.exp_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq1 : Real.exp (-((N : ℝ) / (4 * L))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
    linarith
  exact norm_mul_logDeriv_sub_centralIndex_le_window ha hn₀ hH hL hN0 hNK hNv hlipA hlipB hz hfz
    hmax hcrit hu hWdir
    (le_of_eq (tsum_shifted_geom hq0.le hq1 N))
    (tsum_shifted_sq_weight_le hq0 hq1 N)

/-- **The Wiman--Valiron estimate in spread form.**  The regularity input is a single number: the
spread of the central index across the window.  Monotonicity turns it into the Lipschitz constant
`spread / v₀` on scales at least `v₀`, which is all the Gaussian argument uses, so the hypotheses
reduce to `2 * spread <= N <= 2 * spread * H / v₀`. -/
theorem norm_mul_logDeriv_sub_centralIndex_le_spread
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H v₀ L : ℝ} (hH : 0 < H) (hv₀ : 0 < v₀)
    (hspread : 0 < centralIndexSpread a x H)
    (hLdef : L = centralIndexSpread a x H / v₀)
    {N : ℕ} (hN0 : 0 < N)
    (hlow : 2 * centralIndexSpread a x H ≤ (N : ℝ))
    (hhigh : (N : ℝ) ≤ 2 * centralIndexSpread a x H * H / v₀)
    {z : ℂ} (hz : ‖z‖ = Real.exp x)
    (hfz : maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖)
    (hmax : ∀ θ : ℝ, ‖coeffFun a (circleMap 0 (Real.exp x) θ)‖ ≤ ‖coeffFun a z‖)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a (Real.exp x) z n
      = ((‖∑' n : ℕ, normalisedCoeff a (Real.exp x) z n‖ : ℝ) : ℂ) * u) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
      ≤ (Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
              / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
          * |meanIndex a (Real.exp x) - (centralIndex a (Real.exp x) : ℝ)|
        + Real.sqrt (2 * ((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1)
              + 2 * (2 * ((N : ℝ) + 1) ^ (2 : ℕ) * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                  / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ (3 : ℕ)))
            * (Real.sqrt (2 * (N : ℝ) + 1)
              + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
                  / (1 - Real.exp (-((N : ℝ) / (4 * L))))))) := by
  have hv₀ne : v₀ ≠ 0 := ne_of_gt hv₀
  have hL : 0 < L := by rw [hLdef]; positivity
  have hNK : (N : ℝ) ≤ 2 * L * H := by
    rw [hLdef]
    refine le_trans hhigh (le_of_eq ?_)
    field_simp
  have hNv : 2 * L * v₀ ≤ (N : ℝ) := by
    rw [hLdef]
    have heq : 2 * (centralIndexSpread a x H / v₀) * v₀ = 2 * centralIndexSpread a x H := by
      field_simp
    rw [heq]
    exact hlow
  have hlipA := centralIndex_le_add_spread_div_mul (a := a) ha hn₀ (x := x) (H := H) hv₀
  have hlipB := sub_spread_div_mul_le_centralIndex (a := a) ha hn₀ (x := x) (H := H) hv₀
  rw [← hLdef] at hlipA hlipB
  exact norm_mul_logDeriv_sub_centralIndex_le_explicit_window ha hn₀ hH hL hN0 hNK hNv
    hlipA hlipB hz hfz hmax hcrit hu hWdir

end GaloisForLFunctions.HTGeometry
