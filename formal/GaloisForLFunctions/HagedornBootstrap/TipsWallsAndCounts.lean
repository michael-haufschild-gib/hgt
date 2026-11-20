import GaloisForLFunctions.HagedornBootstrap.QuadraticUnits
import GaloisForLFunctions.HagedornBootstrap.BootstrapSlope
import GaloisForLFunctions.HagedornBootstrap.PolyakovLandau
import GaloisForLFunctions.HagedornBootstrap.ZeroLawAndDeficit

/-!
# Tips, walls and counts

* **Hellerman's slope is the edge tip.** The tip-to-slope map `Λ(x) = 1/(1/12 + x²/3)` sends the
  edge `x = 1/2` of the strip to Hellerman's `6`; the bootstrap tip `x* = arsinh(1)/π` lies inside
  the strip, so `Λ_V > 6`. In terms of the fundamental unit `ε = 1 + √2` of the corpus `ℤ[√2]`,
  `Λ_V = 12π²/(π² + 4 log² ε)`.
* **Convexity of the Haar cost.** The Gross–Witten–Wadia potential is convex on `(−∞, 1)`: its
  derivative is nondecreasing across the junction.
* **The far minimum at leading order.** Near `u = 1/2` the walled action with `b = −B` is
  `S(1/2) + g(ε)`, `g(ε) = (m − B/2)ε + (4/3)ε³`. For `m < B/2` it has its minimum on
  `[0, ∞)` at `ε* = ½√(B/2 − m)` with `g(ε*) = −(8/3)ε*³ = O(B^{3/2})`, since
  `g(ε) − g(ε*) = (4/3)(ε − ε*)²(ε + 2ε*)`; for `m ≥ B/2` there is none: the large black hole is
  born at `T_min`.
* **Counting the zeros.** The counting function `N(x) = ½∫_{x*}^x ρ_U` of the zero law obeys
  `(x − x*)²/3 ≤ N(x) ≤ (x² − x*²)/3`.
-/

noncomputable section

open Real Set

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### Tips -/

/-- **Hellerman's slope:** `Λ(1/2) = 6`. -/
theorem slopeOfTip_half : slopeOfTip (1 / 2) = 6 := by norm_num [slopeOfTip]

/-- The bootstrap tip lies inside the strip: `x* < 1/2`. -/
theorem bootstrapTip_lt_half : bootstrapTip < 1 / 2 := by
  unfold bootstrapTip
  rw [div_lt_iff₀ Real.pi_pos]
  have := arsinh_one_lt
  have := Real.pi_gt_three
  linarith

/-- `Λ_V > 6` because the tip is inside the strip. -/
theorem hellerman_lt_viraSlope : 6 < viraSlope := by
  rw [← slopeOfTip_bootstrapTip, ← slopeOfTip_half]
  exact slopeOfTip_strictAntiOn (mem_Ici.mpr bootstrapTip_pos.le) (mem_Ici.mpr (by norm_num))
    bootstrapTip_lt_half

/-- **`Λ_V` through the fundamental unit of `ℤ[√2]`.** -/
theorem viraSlope_eq_fundUnit :
    viraSlope = 12 * π ^ 2 / (π ^ 2 + 4 * Real.log (RHTower.SqrtTwo.emb RHTower.SqrtTwo.fundUnit) ^ 2) := by
  rw [viraSlope, arsinh_one_eq_log_fundUnit]

/-! ### Convexity of the Haar cost -/

theorem gwwDeriv_monotoneOn : MonotoneOn gwwDeriv (Iio 1) := by
  intro a ha b hb hab
  simp only [mem_Iio] at ha hb
  rcases le_or_gt a (1 / 2) with h1 | h1 <;> rcases le_or_gt b (1 / 2) with h2 | h2
  · rw [gwwDeriv_of_le h1, gwwDeriv_of_le h2]; linarith
  · rw [gwwDeriv_of_le h1, gwwDeriv_of_ge h2.le]
    rw [le_div_iff₀ (by linarith)]; nlinarith
  · linarith
  · rw [gwwDeriv_of_ge h1.le, gwwDeriv_of_ge h2.le]
    apply one_div_le_one_div_of_le (by linarith); linarith

/-- **The Gross–Witten–Wadia potential is convex on `(−∞, 1)`.** -/
theorem gwwPotential_convexOn : ConvexOn ℝ (Iio 1) gwwPotential := by
  apply MonotoneOn.convexOn_of_deriv (convex_Iio 1)
  · exact fun u hu => (hasDerivAt_gwwPotential hu).continuousAt.continuousWithinAt
  · rw [interior_Iio]
    exact fun u hu => (hasDerivAt_gwwPotential hu).differentiableAt.differentiableWithinAt
  · rw [interior_Iio]
    exact gwwDeriv_monotoneOn.congr fun u hu => ((hasDerivAt_gwwPotential hu).deriv).symm

/-! ### The far minimum at leading order -/

/-- The leading-order action `g(ε) = (m − B/2)ε + (4/3)ε³` beyond the gap point. -/
def wallModel (m B ε : ℝ) : ℝ := (m - B / 2) * ε + 4 / 3 * ε ^ 3

/-- The far saddle `ε* = ½√(B/2 − m)`. -/
def farSaddle (m B : ℝ) : ℝ := Real.sqrt (B / 2 - m) / 2

theorem farSaddle_sq {m B : ℝ} (h : m < B / 2) : 4 * farSaddle m B ^ 2 = B / 2 - m := by
  unfold farSaddle
  rw [div_pow, Real.sq_sqrt (by linarith)]
  ring

/-- `g(ε) − g(ε*) = (4/3)(ε − ε*)²(ε + 2ε*)`. -/
theorem wallModel_sub {m B : ℝ} (h : m < B / 2) (ε : ℝ) :
    wallModel m B ε - wallModel m B (farSaddle m B) =
      4 / 3 * (ε - farSaddle m B) ^ 2 * (ε + 2 * farSaddle m B) := by
  have hs := farSaddle_sq h
  unfold wallModel
  rw [show m - B / 2 = -(4 * farSaddle m B ^ 2) by linarith]
  ring

/-- **The far minimum:** for `m < B/2`, `ε*` minimizes `g` on `[0, ∞)` with value `−(8/3)ε*³`. -/
theorem wallModel_farMin {m B : ℝ} (h : m < B / 2) :
    wallModel m B (farSaddle m B) = -(8 / 3) * farSaddle m B ^ 3 ∧
      ∀ ε, 0 ≤ ε → wallModel m B (farSaddle m B) ≤ wallModel m B ε := by
  have hs := farSaddle_sq h
  have h0 : 0 ≤ farSaddle m B := by unfold farSaddle; positivity
  constructor
  · unfold wallModel
    rw [show m - B / 2 = -(4 * farSaddle m B ^ 2) by linarith]
    ring
  · intro ε hε
    have := wallModel_sub h ε
    have : 0 ≤ 4 / 3 * (ε - farSaddle m B) ^ 2 * (ε + 2 * farSaddle m B) := by positivity
    linarith

theorem hasDerivAt_wallModel_farSaddle {m B : ℝ} (h : m < B / 2) :
    HasDerivAt (wallModel m B) 0 (farSaddle m B) := by
  have hs := farSaddle_sq h
  unfold wallModel
  refine (((hasDerivAt_id _).const_mul (m - B / 2)).add ((hasDerivAt_pow 3 _).const_mul (4 / 3))).congr_deriv ?_
  simp only [id]
  push_cast
  linarith

/-- **Birth of the large black hole at `T_min`:** for `m ≥ B/2` the gap point itself is the
minimum of `g` on `[0, ∞)`. -/
theorem wallModel_no_farMin {m B : ℝ} (h : B / 2 ≤ m) {ε : ℝ} (hε : 0 ≤ ε) :
    wallModel m B 0 ≤ wallModel m B ε := by
  unfold wallModel
  have : 0 ≤ (m - B / 2) * ε := mul_nonneg (by linarith) hε
  have : 0 ≤ 4 / 3 * ε ^ 3 := by positivity
  simp; linarith

/-! ### Counting the zeros -/

/-- The counting function `N(x) = ½∫_{x*}^x ρ_U` of the zero law. -/
def zeroCount (x : ℝ) : ℝ := (1 / 2) * ∫ s in bootstrapTip..x, zeroLaw s

theorem intervalIntegrable_zeroLaw {x : ℝ} (hx : bootstrapTip ≤ x) :
    IntervalIntegrable zeroLaw MeasureTheory.volume bootstrapTip x :=
  (continuousOn_zeroLaw.mono (Icc_subset_Ici_self)).intervalIntegrable_of_Icc hx

/-- **Lower count:** `N(x) ≥ (x − x*)²/3`. -/
theorem zeroCount_ge {x : ℝ} (hx : bootstrapTip ≤ x) : (x - bootstrapTip) ^ 2 / 3 ≤ zeroCount x := by
  unfold zeroCount
  have h := intervalIntegral.integral_mono_on hx
    ((by fun_prop : Continuous fun s : ℝ => 4 / 3 * (s - bootstrapTip)).intervalIntegrable _ _)
    (intervalIntegrable_zeroLaw hx) (fun s hs => zeroLaw_ge_linear hs.1)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_id
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul] at h
  nlinarith

/-- **Upper count:** `N(x) ≤ (x² − x*²)/3`. -/
theorem zeroCount_le {x : ℝ} (hx : bootstrapTip ≤ x) : zeroCount x ≤ (x ^ 2 - bootstrapTip ^ 2) / 3 := by
  unfold zeroCount
  have h := intervalIntegral.integral_mono_on hx (intervalIntegrable_zeroLaw hx)
    ((by fun_prop : Continuous fun s : ℝ => 4 / 3 * s).intervalIntegrable _ _)
    (fun s hs => by
      have hs0 : 0 ≤ s := bootstrapTip_pos.le.trans hs.1
      have := zeroLaw_le_linear (x := s) (by rw [abs_of_nonneg hs0]; exact hs.1)
      rwa [abs_of_nonneg hs0] at this)
  rw [intervalIntegral.integral_const_mul, integral_id] at h
  nlinarith

end GaloisForLFunctions.HagedornBootstrap
