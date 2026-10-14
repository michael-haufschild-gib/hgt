import GaloisForLFunctions.RHTower.TwistedArcGenerator
import GaloisForLFunctions.HTGeometry.LegendreRunningMeanKernel

/-!
# The twisted point vector is the squared Legendre operator in the arc parameter

For `Q_c(x) = x² − 2cx + 1` and `|c| < 1`, `∂_c Q_c(x)^{−1/2−j} = (2j+1) x Q_c(x)^{−3/2−j}`
(`hasDerivAt_arcQuadTerm_param`).  Iterating it gives the exact identity

`τ_c(x) = 𝔐_c² Q_c(x)^{−1/2}`,   `𝔐_c = ∂_c (1 − c²) ∂_c`,

for the twisted point vector `τ_c = twPointVec c` (`hasDerivAt_legendreArcSecond`): the
intermediate stages are `(1 − c²) ∂_c Q^{−1/2} = (1 − c²) x Q^{−3/2}`,
`𝔐_c Q^{−1/2} = −2cx Q^{−3/2} + 3(1 − c²) x² Q^{−5/2}` (`legendreArcFirst`) and
`∂_c 𝔐_c Q^{−1/2} = −2x Q^{−3/2} − 12cx² Q^{−5/2} + 15(1 − c²) x³ Q^{−7/2}`
(`legendreArcSecond`).

**Theorem** (`integral_twPointPair_mul_legendreKernel`).  For the symmetrized pair
`Ψ_x(c) = Q_c(x)^{−1/2} + Q_c(−x)^{−1/2}` (even in `c`), whose slope is
`arcPairSlope c x = x Q_c(x)^{−3/2} − x Q_c(−x)^{−3/2}`, and every `0 < c ≤ ½`,

`∫₀^{1/2} (τ_u(x) + τ_u(−x)) k_c(u) du = (3/2) arcPairSlope(½, x) − (1 − c²) arcPairSlope(c, x)/c`,

where `k_c = legendreKernel ½ c ≥ 0` is the clamped Legendre kernel.  This is the clamped
running-mean identity of `HTGeometry.LegendreRunningMeanKernel` applied to `f = Ψ_x`.
-/

open MeasureTheory Set intervalIntegral
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem hasDerivAt_arcQuad_param (c x : ℝ) : HasDerivAt (fun c => arcQuad c x) (-2 * x) c := by
  have h := ((hasDerivAt_const c (x ^ 2)).sub (((hasDerivAt_id c).const_mul 2).mul_const x)).add
    (hasDerivAt_const c (1 : ℝ))
  unfold arcQuad
  exact h.congr_deriv (by simp)

/-- `∂_c Q_c(x)^{−1/2−j} = (2j+1) x Q_c(x)^{−3/2−j}`. -/
theorem hasDerivAt_arcQuadTerm_param {c : ℝ} (hc : |c| < 1) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun c => arcQuadTerm c j x) ((2 * j + 1) * x * arcQuadTerm c (j + 1) x) c := by
  have hQ := arcQuad_pos hc x
  have h1 := (hasDerivAt_arcQuad_param c x).rpow_const (p := (-1 / 2 : ℝ)) (Or.inl hQ.ne')
  have h2 := (hasDerivAt_arcQuad_param c x).pow j
  have h3 : HasDerivAt (fun c => arcQuad c x ^ (-1 / 2 : ℝ) / arcQuad c x ^ j) _ c :=
    h1.div h2 (pow_pos hQ j).ne'
  refine h3.congr_deriv ?_
  have e : arcQuad c x ^ ((-1 / 2 : ℝ) - 1) = arcQuad c x ^ (-1 / 2 : ℝ) / arcQuad c x := by
    rw [Real.rpow_sub hQ, Real.rpow_one]
  unfold arcQuadTerm
  rw [e]
  rcases j with _ | j
  · simp
    field_simp
  · push_cast
    rw [pow_succ]
    field_simp
    ring

theorem continuousAt_arcQuadTerm_param {c : ℝ} (hc : |c| < 1) (j : ℕ) (x : ℝ) :
    ContinuousAt (fun c => arcQuadTerm c j x) c :=
  (hasDerivAt_arcQuadTerm_param hc j x).continuousAt

/-- The slope `x Q_c(x)^{−3/2} − x Q_c(−x)^{−3/2}` of the symmetrized arc pair. -/
def arcPairSlope (c x : ℝ) : ℝ := x * arcQuadTerm c 1 x + -x * arcQuadTerm c 1 (-x)

/-- `𝔐_c Q_c(x)^{−1/2} = −2cx Q^{−3/2} + 3(1 − c²) x² Q^{−5/2}`. -/
def legendreArcFirst (c x : ℝ) : ℝ :=
  -2 * c * x * arcQuadTerm c 1 x + 3 * (1 - c ^ 2) * x ^ 2 * arcQuadTerm c 2 x

/-- `∂_c 𝔐_c Q_c(x)^{−1/2} = −2x Q^{−3/2} − 12cx² Q^{−5/2} + 15(1 − c²) x³ Q^{−7/2}`. -/
def legendreArcSecond (c x : ℝ) : ℝ :=
  -2 * x * arcQuadTerm c 1 x - 12 * c * x ^ 2 * arcQuadTerm c 2 x +
    15 * (1 - c ^ 2) * x ^ 3 * arcQuadTerm c 3 x

theorem hasDerivAt_legendreArcZero {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    HasDerivAt (fun c => (1 - c ^ 2) * (x * arcQuadTerm c 1 x)) (legendreArcFirst c x) c := by
  have h1 := hasDerivAt_arcQuadTerm_param hc 1 x
  have hp : HasDerivAt (fun c : ℝ => 1 - c ^ 2) (-(2 * c)) c := by
    simpa using ((hasDerivAt_pow 2 c).const_sub 1)
  refine (hp.mul (h1.const_mul x)).congr_deriv ?_
  unfold legendreArcFirst
  push_cast
  ring

theorem hasDerivAt_legendreArcFirst {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    HasDerivAt (fun c => legendreArcFirst c x) (legendreArcSecond c x) c := by
  have h1 := hasDerivAt_arcQuadTerm_param hc 1 x
  have h2 := hasDerivAt_arcQuadTerm_param hc 2 x
  have hp : HasDerivAt (fun c : ℝ => 1 - c ^ 2) (-(2 * c)) c := by
    simpa using ((hasDerivAt_pow 2 c).const_sub 1)
  have hl : HasDerivAt (fun c : ℝ => -2 * c * x) (-2 * x) c := by
    simpa using ((hasDerivAt_id c).const_mul (-2)).mul_const x
  refine ((hl.mul h1).add (((hp.const_mul 3).mul_const (x ^ 2)).mul h2)).congr_deriv ?_
  unfold legendreArcSecond
  push_cast
  ring

/-- **`τ_c = 𝔐_c² Q_c^{−1/2}`.** -/
theorem hasDerivAt_legendreArcSecond {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    HasDerivAt (fun c => (1 - c ^ 2) * legendreArcSecond c x) (twPointVec c x) c := by
  have h1 := hasDerivAt_arcQuadTerm_param hc 1 x
  have h2 := hasDerivAt_arcQuadTerm_param hc 2 x
  have h3 := hasDerivAt_arcQuadTerm_param hc 3 x
  have hp : HasDerivAt (fun c : ℝ => 1 - c ^ 2) (-(2 * c)) c := by
    simpa using ((hasDerivAt_pow 2 c).const_sub 1)
  have hl : HasDerivAt (fun c : ℝ => 12 * c * x ^ 2) (12 * x ^ 2) c := by
    simpa using ((hasDerivAt_id c).const_mul 12).mul_const (x ^ 2)
  have hs : HasDerivAt (fun c => legendreArcSecond c x)
      (-2 * x * (3 * x * arcQuadTerm c 2 x) - (12 * x ^ 2 * arcQuadTerm c 2 x +
        12 * c * x ^ 2 * (5 * x * arcQuadTerm c 3 x)) +
        (15 * (-(2 * c)) * x ^ 3 * arcQuadTerm c 3 x +
          15 * (1 - c ^ 2) * x ^ 3 * (7 * x * arcQuadTerm c 4 x))) c := by
    have k1 := (h1.const_mul (-2 * x))
    have k2 := hl.mul h2
    have k3 := ((hp.const_mul 15).mul_const (x ^ 3)).mul h3
    refine ((k1.sub k2).add k3).congr_deriv ?_
    push_cast
    ring
  refine (hp.mul hs).congr_deriv ?_
  unfold legendreArcSecond twPointVec
  ring

theorem arcQuadTerm_zero_neg (j : ℕ) (x : ℝ) : arcQuadTerm 0 j (-x) = arcQuadTerm 0 j x := by
  unfold arcQuadTerm arcQuad
  ring_nf

theorem arcPairSlope_zero (x : ℝ) : arcPairSlope 0 x = 0 := by
  unfold arcPairSlope
  rw [arcQuadTerm_zero_neg]
  ring

theorem legendreArcSecond_zero_add_neg (x : ℝ) :
    legendreArcSecond 0 x + legendreArcSecond 0 (-x) = 0 := by
  unfold legendreArcSecond
  rw [arcQuadTerm_zero_neg 1, arcQuadTerm_zero_neg 2, arcQuadTerm_zero_neg 3]
  ring

theorem abs_lt_one_of_mem_uIcc_half {u : ℝ} (hu : u ∈ uIcc (0 : ℝ) (1 / 2)) : |u| < 1 := by
  rw [uIcc_of_le (by norm_num)] at hu
  rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]

/-- **Twisted point pairs through a clamped Legendre kernel.** -/
theorem integral_twPointPair_mul_legendreKernel (x : ℝ) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    ∫ u in (0 : ℝ)..(1 / 2), (twPointVec u x + twPointVec u (-x)) * legendreKernel (1 / 2) c u =
      (1 - (1 / 2 : ℝ) ^ 2) * arcPairSlope (1 / 2) x / (1 / 2) -
        (1 - c ^ 2) * arcPairSlope c x / c := by
  have hG : ∀ s ∈ uIcc (0 : ℝ) (1 / 2), HasDerivAt (fun s => (1 - s ^ 2) * arcPairSlope s x)
      (legendreArcFirst s x + legendreArcFirst s (-x)) s := by
    intro s hs
    have hs1 := abs_lt_one_of_mem_uIcc_half hs
    refine ((hasDerivAt_legendreArcZero hs1 x).add
      (hasDerivAt_legendreArcZero hs1 (-x))).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by
      simp only [Pi.add_apply]; unfold arcPairSlope; ring
  have hq : ∀ s ∈ uIcc (0 : ℝ) (1 / 2), HasDerivAt (fun s => legendreArcFirst s x +
      legendreArcFirst s (-x)) (legendreArcSecond s x + legendreArcSecond s (-x)) s := by
    intro s hs
    have hs1 := abs_lt_one_of_mem_uIcc_half hs
    exact (hasDerivAt_legendreArcFirst hs1 x).add (hasDerivAt_legendreArcFirst hs1 (-x))
  have hH : ∀ s ∈ uIcc (0 : ℝ) (1 / 2), HasDerivAt (fun s => (1 - s ^ 2) *
      (legendreArcSecond s x + legendreArcSecond s (-x)))
      (twPointVec s x + twPointVec s (-x)) s := by
    intro s hs
    have hs1 := abs_lt_one_of_mem_uIcc_half hs
    refine ((hasDerivAt_legendreArcSecond hs1 x).add
      (hasDerivAt_legendreArcSecond hs1 (-x))).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by simp only [Pi.add_apply]; ring
  have hqc : ContinuousOn (fun s => legendreArcFirst s x + legendreArcFirst s (-x))
      (uIcc 0 (1 / 2)) := fun s hs => (hq s hs).continuousAt.continuousWithinAt
  have hq1c : ContinuousOn (fun s => legendreArcSecond s x + legendreArcSecond s (-x))
      (uIcc 0 (1 / 2)) := by
    intro s hs
    have hs1 := abs_lt_one_of_mem_uIcc_half hs
    have h1 : (1 : ℝ) - s ^ 2 ≠ 0 := by
      have := abs_lt.mp hs1; nlinarith
    have hc' := ((hH s hs).continuousAt).div (continuousAt_const.sub (continuousAt_id.pow 2)) h1
    refine (hc'.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [(continuousAt_const.sub (continuousAt_id.pow 2)).eventually_ne h1] with t ht
    simp only [Pi.div_apply, Pi.sub_apply, Pi.pow_apply, id] at ht ⊢
    field_simp
  have hrc : ContinuousOn (fun s => twPointVec s x + twPointVec s (-x)) (uIcc 0 (1 / 2)) := by
    intro s hs
    have hs1 := abs_lt_one_of_mem_uIcc_half hs
    have hcont : ∀ y : ℝ, ContinuousAt (fun s => twPointVec s y) s := by
      intro y
      unfold twPointVec
      have := fun j => continuousAt_arcQuadTerm_param hs1 j y
      fun_prop
    exact ((hcont x).add (hcont (-x))).continuousWithinAt
  have hq10 : legendreArcSecond 0 x + legendreArcSecond 0 (-x) = 0 :=
    legendreArcSecond_zero_add_neg x
  exact integral_mul_legendreKernel hc hc2 (by norm_num) hG hq hH (arcPairSlope_zero x) hq10
    hqc hq1c hrc

end

end RHTower
