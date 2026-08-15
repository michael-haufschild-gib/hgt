import GaloisForLFunctions.HTGeometry.MovingCanonicalProduct
import GaloisForLFunctions.HTGeometry.MovingDivisorData

/-!
# The genus-one canonical product of a moving divisor

The analytic estimates for the clock divisor use only that the locations are trapped between
`(n+1)/2` and `2(n+1)`.  A general moving divisor is trapped between `c(n+1)` and `C(n+1)`, so
rescaling by `2c` brings it into the clock window and transports the growth series, the summability
of the reciprocal squares, and the exponent-one criterion.
-/

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- Rescaling the argument only rescales the order-one weight. -/
theorem orderOneWeight_le_of_norm_mul {t K : ℝ} (ht : 1 ≤ t) (hK : 0 ≤ K) {w z : ℂ}
    (hw : ‖w‖ = t * ‖z‖) :
    orderOneWeight K w ≤ orderOneWeight (K * t * (1 + Real.log t / Real.log 2)) z := by
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hlogz : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogzpos : 0 < Real.log (2 + ‖z‖) := lt_of_lt_of_le hlog2 hlogz
  have hfac : 1 + t * ‖z‖ ≤ t * (1 + ‖z‖) := by nlinarith
  have harg : Real.log (2 + t * ‖z‖) ≤ Real.log t + Real.log (2 + ‖z‖) := by
    have hle : (2 : ℝ) + t * ‖z‖ ≤ t * (2 + ‖z‖) := by nlinarith
    have hpos2 : (0 : ℝ) < 2 + t * ‖z‖ := by positivity
    have h1 : Real.log (2 + t * ‖z‖) ≤ Real.log (t * (2 + ‖z‖)) :=
      Real.log_le_log hpos2 hle
    rwa [Real.log_mul (ne_of_gt htpos) (by linarith)] at h1
  have hlogbound : Real.log (2 + t * ‖z‖)
      ≤ (1 + Real.log t / Real.log 2) * Real.log (2 + ‖z‖) := by
    have hstep : Real.log t ≤ (Real.log t / Real.log 2) * Real.log (2 + ‖z‖) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    have hexp : (1 + Real.log t / Real.log 2) * Real.log (2 + ‖z‖)
        = Real.log (2 + ‖z‖) + (Real.log t / Real.log 2) * Real.log (2 + ‖z‖) := by ring
    rw [hexp]
    linarith
  rw [orderOneWeight, orderOneWeight, hw]
  have hnn1 : 0 ≤ 1 + t * ‖z‖ := by positivity
  have hnn2 : 0 ≤ K * (1 + t * ‖z‖) := by positivity
  calc K * (1 + t * ‖z‖) * Real.log (2 + t * ‖z‖)
      ≤ K * (1 + t * ‖z‖) * ((1 + Real.log t / Real.log 2) * Real.log (2 + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hlogbound hnn2
    _ ≤ K * (t * (1 + ‖z‖)) * ((1 + Real.log t / Real.log 2) * Real.log (2 + ‖z‖)) := by
        have hfac' : K * (1 + t * ‖z‖) ≤ K * (t * (1 + ‖z‖)) :=
          mul_le_mul_of_nonneg_left hfac hK
        have hrhs : 0 ≤ (1 + Real.log t / Real.log 2) * Real.log (2 + ‖z‖) := by
          have : 0 ≤ Real.log t / Real.log 2 := div_nonneg hlogt (le_of_lt hlog2)
          nlinarith
        exact mul_le_mul_of_nonneg_right hfac' hrhs
    _ = K * t * (1 + Real.log t / Real.log 2) * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by ring

namespace MovingDivisor

variable (D : MovingDivisor) (θ : ℕ → ℝ)

/-- A rescaling factor bringing the divisor into the window `(n+1)/2 ≤ · ≤ K (n+1)`. -/
noncomputable def normalizer : ℝ := min (2 * (D.exists_lower_linear θ).choose) 1

theorem normalizer_pos : 0 < D.normalizer θ := by
  have hc := (D.exists_lower_linear θ).choose_spec.1
  exact lt_min (by linarith) zero_lt_one

theorem normalizer_le_one : D.normalizer θ ≤ 1 := min_le_right _ _

/-- The rescaled locations sit in the clock window from below. -/
theorem half_le_normalized (n : ℕ) :
    ((n : ℝ) + 1) / 2 ≤ D.zero θ n / D.normalizer θ := by
  have hc := (D.exists_lower_linear θ).choose_spec
  have hspos : 0 < D.normalizer θ := D.normalizer_pos θ
  have hsle : D.normalizer θ ≤ 2 * (D.exists_lower_linear θ).choose := min_le_left _ _
  rw [le_div_iff₀ hspos]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  nlinarith [hc.2 n, hc.1]

theorem normalized_pos (n : ℕ) : 0 < D.zero θ n / D.normalizer θ :=
  div_pos (D.zero_pos θ n) (D.normalizer_pos θ)

theorem norm_zero_eq (n : ℕ) :
    ‖(D.zero θ n : ℂ)‖ = D.normalizer θ * ‖((D.zero θ n / D.normalizer θ : ℝ) : ℂ)‖ := by
  have hspos : 0 < D.normalizer θ := D.normalizer_pos θ
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (D.zero_pos θ n), abs_of_pos (D.normalized_pos θ n)]
  field_simp

/-- **The reciprocal squares of a moving divisor are summable.** -/
theorem summable_inv_norm_sq :
    Summable (fun n => 1 / ‖(D.zero θ n : ℂ)‖ ^ 2) := by
  have hspos : 0 < D.normalizer θ := D.normalizer_pos θ
  have hbase := halfLinear_summable_inv_sq (a := fun n => D.zero θ n / D.normalizer θ)
    (D.normalized_pos θ) (D.half_le_normalized θ)
  have hscaled := hbase.mul_left ((D.normalizer θ) ^ 2)⁻¹
  refine hscaled.congr fun n => ?_
  rw [D.norm_zero_eq θ n]
  have hne : ‖((D.zero θ n / D.normalizer θ : ℝ) : ℂ)‖ ≠ 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (D.normalized_pos θ n)]
    exact ne_of_gt (D.normalized_pos θ n)
  field_simp

/-- **The growth series of a moving divisor is bounded by an order-one weight.** -/
theorem exists_growthSeries_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ∑' n, min (2 * ‖z‖ / ‖(D.zero θ n : ℂ)‖) (2 * ‖z‖ ^ 2 / ‖(D.zero θ n : ℂ)‖ ^ 2)
        ≤ orderOneWeight C z := by
  have hspos : 0 < D.normalizer θ := D.normalizer_pos θ
  have hsle : D.normalizer θ ≤ 1 := D.normalizer_le_one θ
  set t : ℝ := (D.normalizer θ)⁻¹ with ht
  have htge : 1 ≤ t := by
    rw [ht, le_inv_comm₀ zero_lt_one hspos]
    simpa using hsle
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg htge
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨32 * t * (1 + Real.log t / Real.log 2), by positivity, fun z => ?_⟩
  have hnorm : ‖(t : ℂ) * z‖ = t * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one htge)]
  have hbase := halfLinear_growthSeries_le_orderOneWeight
    (a := fun n => D.zero θ n / D.normalizer θ)
    (D.normalized_pos θ) (D.half_le_normalized θ) ((t : ℂ) * z)
  have hterm : ∀ n : ℕ,
      min (2 * ‖z‖ / ‖(D.zero θ n : ℂ)‖) (2 * ‖z‖ ^ 2 / ‖(D.zero θ n : ℂ)‖ ^ 2)
        = min (2 * ‖(t : ℂ) * z‖ / ‖((D.zero θ n / D.normalizer θ : ℝ) : ℂ)‖)
            (2 * ‖(t : ℂ) * z‖ ^ 2 / ‖((D.zero θ n / D.normalizer θ : ℝ) : ℂ)‖ ^ 2) := by
    intro n
    have hz := D.norm_zero_eq θ n
    have hne : (0 : ℝ) < ‖((D.zero θ n / D.normalizer θ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (D.normalized_pos θ n)]
      exact D.normalized_pos θ n
    rw [hnorm, hz, ht]
    congr 1
    · field_simp
    · field_simp
  have heq : ∑' n, min (2 * ‖z‖ / ‖(D.zero θ n : ℂ)‖) (2 * ‖z‖ ^ 2 / ‖(D.zero θ n : ℂ)‖ ^ 2)
      = ∑' n, min (2 * ‖(t : ℂ) * z‖ / ‖((D.zero θ n / D.normalizer θ : ℝ) : ℂ)‖)
          (2 * ‖(t : ℂ) * z‖ ^ 2 / ‖((D.zero θ n / D.normalizer θ : ℝ) : ℂ)‖ ^ 2) :=
    tsum_congr hterm
  rw [heq]
  exact le_trans hbase (orderOneWeight_le_of_norm_mul htge (by norm_num) hnorm)

end MovingDivisor

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Filter
open scoped Topology

/-- The exponent-one criterion is invariant under a positive rescaling of the divisor. -/
theorem hasExponentOfConvergenceOne_of_scaled {a : ℕ → ℝ} (hpos : ∀ n : ℕ, 0 < a n) {s : ℝ}
    (hs : 0 < s) (h : HasExponentOfConvergenceOne (fun n => ((a n / s : ℝ) : ℂ))) :
    HasExponentOfConvergenceOne (fun n => (a n : ℂ)) := by
  have hnorm : ∀ n : ℕ, ‖(a n : ℂ)‖ = s * ‖((a n / s : ℝ) : ℂ)‖ := by
    intro n
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (hpos n), abs_of_pos (div_pos (hpos n) hs)]
    field_simp
  have hnormpos : ∀ n : ℕ, 0 < ‖((a n / s : ℝ) : ℂ)‖ := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (hpos n) hs)]
    exact div_pos (hpos n) hs
  constructor
  · intro p hp
    have hbase := h.1 p hp
    have hscaled := hbase.mul_left ((s : ℝ) ^ p)⁻¹
    refine hscaled.congr fun n => ?_
    rw [hnorm n, Real.mul_rpow (le_of_lt hs) (le_of_lt (hnormpos n))]
    have h1 : (s : ℝ) ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hs p)
    have h2 : ‖((a n / s : ℝ) : ℂ)‖ ^ p ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (hnormpos n) p)
    field_simp
  · intro hsum
    refine h.2 ?_
    have hscaled := hsum.mul_left s
    refine hscaled.congr fun n => ?_
    rw [hnorm n]
    have h2 : ‖((a n / s : ℝ) : ℂ)‖ ≠ 0 := ne_of_gt (hnormpos n)
    field_simp

namespace MovingDivisor

variable (D : MovingDivisor) (θ : ℕ → ℝ)

/-- **A moving divisor has exponent of convergence one.** -/
theorem hasExponentOfConvergenceOne :
    HasExponentOfConvergenceOne (fun n => (D.zero θ n : ℂ)) := by
  obtain ⟨C, hC, hub⟩ := D.exists_upper_linear θ
  have hspos : 0 < D.normalizer θ := D.normalizer_pos θ
  refine hasExponentOfConvergenceOne_of_scaled (D.zero_pos θ) hspos ?_
  refine halfLinear_hasExponentOfConvergenceOne (D.normalized_pos θ) (D.half_le_normalized θ)
    (K := C / D.normalizer θ) (div_pos hC hspos) fun n => ?_
  rw [div_le_iff₀ hspos]
  have h := hub n
  have : C / D.normalizer θ * ((n : ℝ) + 1) * D.normalizer θ = C * ((n : ℝ) + 1) := by
    field_simp
  rw [this]
  exact h

/-- The genus-one canonical product of a moving divisor. -/
noncomputable def canonicalProduct : ℂ → ℂ :=
  realCanonicalProduct (D.zero θ)

theorem zero_ne_zero (n : ℕ) : ((D.zero θ n : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (D.zero_pos θ n))

theorem canonicalProduct_analytic :
    AnalyticOnNhd ℂ (D.canonicalProduct θ) Set.univ :=
  RHTower.canonicalProductE1Indexed_analytic _ (D.zero_ne_zero θ) (D.summable_inv_norm_sq θ)

/-- **The canonical product of a moving divisor has an order-one growth envelope.** -/
theorem canonicalProduct_orderOneEnvelope :
    OrderOneEnvelope (D.canonicalProduct θ) := by
  obtain ⟨C, hC, hle⟩ := D.exists_growthSeries_le θ
  refine ⟨C, hC, fun z => ?_⟩
  exact (RHTower.canonicalProductE1Indexed_norm_le_exp_min _ (D.zero_ne_zero θ)
    (D.summable_inv_norm_sq θ) z).trans (Real.exp_le_exp.mpr (hle z))

end MovingDivisor

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open Complex Filter
open scoped Topology ComplexConjugate

namespace MovingDivisor

variable (D : MovingDivisor) (θ : ℕ → ℝ)

/-- **Schwarz reality of the canonical product of a moving divisor.** -/
theorem canonicalProduct_conj (z : ℂ) :
    D.canonicalProduct θ (conj z) = conj (D.canonicalProduct θ z) :=
  realCanonicalProduct_conj (D.zero_pos θ) (D.summable_inv_norm_sq θ) z

/-- **The divisor of the canonical product is exactly the moving locations.** -/
theorem canonicalProduct_eq_zero_iff (z : ℂ) :
    D.canonicalProduct θ z = 0 ↔ ∃ n, z = (D.zero θ n : ℂ) :=
  realCanonicalProduct_eq_zero_iff (D.zero_pos θ) (D.summable_inv_norm_sq θ) z

/-- **Every location is a simple zero.** -/
theorem canonicalProduct_zero_analyticOrderAt (n : ℕ) :
    analyticOrderAt (D.canonicalProduct θ) (D.zero θ n : ℂ) = 1 :=
  realCanonicalProduct_zero_analyticOrderAt (D.zero_pos θ) (D.injective θ)
    (D.summable_inv_norm_sq θ) n

/-- The negative logarithmic derivative of the canonical product, as a normally convergent
series. -/
noncomputable def logDerivative : ℂ → ℂ := realLogDerivative (D.zero θ)

theorem summable_logDerivative {z : ℂ} (hz : ∀ n, z ≠ (D.zero θ n : ℂ)) :
    Summable (fun n => ((D.zero θ n : ℂ) - z)⁻¹ - (D.zero θ n : ℂ)⁻¹) :=
  summable_realLogDerivative (D.zero_pos θ) (D.summable_inv_norm_sq θ) hz

/-- **The carrier of a moving divisor is Herglotz on the upper half-plane.** -/
theorem logDerivative_im_nonneg {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (D.logDerivative θ z).im :=
  realLogDerivative_im_nonneg (D.zero_pos θ) (D.summable_inv_norm_sq θ) hz

theorem neg_logDeriv_canonicalProduct_eq {z : ℂ} (hz : ∀ n, z ≠ (D.zero θ n : ℂ)) :
    -logDeriv (D.canonicalProduct θ) z = D.logDerivative θ z :=
  neg_logDeriv_realCanonicalProduct_eq (D.zero_pos θ) (D.summable_inv_norm_sq θ) hz

end MovingDivisor

end GaloisForLFunctions.HTGeometry
