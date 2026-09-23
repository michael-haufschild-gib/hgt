import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaKelvinCrossCurrent

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory Polynomial Set

noncomputable section

namespace RHTower

/-- Forced half-density normalization that removes the Kelvin cocycle. -/
def routeUHardEdgeKelvinNormalizedCrossDensity
    (a : ℝ) (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  (a / x) ^ (2 * routeUHardEdgeKelvinDegree a P) *
    routeUHardEdgeKelvinCrossDensity a P 0 x

/-- The normalized cross state is exactly anti-invariant under physical inversion. -/
theorem routeUHardEdgeKelvinNormalizedCrossDensity_inversion
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (P : Polynomial ℝ) :
    routeUHardEdgeKelvinNormalizedCrossDensity a P (a ^ (2 : ℕ) / x) =
      -routeUHardEdgeKelvinNormalizedCrossDensity a P x := by
  rw [routeUHardEdgeKelvinNormalizedCrossDensity,
    routeUHardEdgeKelvinNormalizedCrossDensity,
    routeUHardEdgeKelvinCrossDensity_inversion ha hx P]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hinv : a / (a ^ (2 : ℕ) / x) = x / a := by
    field_simp [ha0, hx0]
  have hratio : (x / a) * (a ^ (2 : ℕ) / x ^ (2 : ℕ)) = a / x := by
    field_simp [ha0, hx0]
  rw [hinv]
  simp only [mul_one]
  rw [show (x / a) ^ (2 * routeUHardEdgeKelvinDegree a P) *
      (-(a ^ (2 : ℕ) / x ^ (2 : ℕ)) ^ (2 * routeUHardEdgeKelvinDegree a P) *
        routeUHardEdgeKelvinCrossDensity a P 0 x) =
      -(((x / a) * (a ^ (2 : ℕ) / x ^ (2 : ℕ))) ^
        (2 * routeUHardEdgeKelvinDegree a P)) *
          routeUHardEdgeKelvinCrossDensity a P 0 x by
    rw [mul_pow]
    ring]
  rw [hratio]
  ring

/-- Log-radius form of the normalized Kelvin cross state. -/
def routeUHardEdgeMellinOddCrossDensity
    (a : ℝ) (P : Polynomial ℝ) (u : ℝ) : ℝ :=
  routeUHardEdgeKelvinNormalizedCrossDensity a P (a * Real.exp u)

/-- Kelvin anti-invariance becomes ordinary oddness in log-radius. -/
theorem routeUHardEdgeMellinOddCrossDensity_neg
    {a : ℝ} (ha : 0 < a) (P : Polynomial ℝ) (u : ℝ) :
    routeUHardEdgeMellinOddCrossDensity a P (-u) =
      -routeUHardEdgeMellinOddCrossDensity a P u := by
  have hx : 0 < a * Real.exp u := mul_pos ha (Real.exp_pos u)
  have harg : a * Real.exp (-u) = a ^ (2 : ℕ) / (a * Real.exp u) := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt ha, Real.exp_ne_zero]
  rw [routeUHardEdgeMellinOddCrossDensity,
    routeUHardEdgeMellinOddCrossDensity, harg,
    routeUHardEdgeKelvinNormalizedCrossDensity_inversion ha hx P]

theorem routeUHardEdgeMellinOddCrossDensity_zero
    {a : ℝ} (ha : 0 < a) (P : Polynomial ℝ) :
    routeUHardEdgeMellinOddCrossDensity a P 0 = 0 := by
  have h := routeUHardEdgeMellinOddCrossDensity_neg ha P 0
  norm_num at h ⊢
  linarith

/-- Unique heat time at which one positive log-radius orbit has zero pure heat defect. -/
def routeUHardEdgeKelvinCriticalHeatTime
    (a : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  (((2 * d + 1 : ℕ) : ℝ) * u) / (a ^ (2 : ℕ) * Real.sinh (2 * u))

theorem routeUHardEdgeKelvinCriticalHeatTime_pos
    {a u : ℝ} (ha : 0 < a) (hu : 0 < u) (d : ℕ) :
    0 < routeUHardEdgeKelvinCriticalHeatTime a d u := by
  rw [routeUHardEdgeKelvinCriticalHeatTime]
  exact div_pos (mul_pos (by positivity) hu)
    (mul_pos (sq_pos_of_pos ha) (Real.sinh_pos_iff.mpr (by positivity)))

/-- Pure heat part of the Kelvin modular weight defect in inner log-radius. -/
def routeUHardEdgeKelvinHeatDefect
    (a : ℝ) (d : ℕ) (t u : ℝ) : ℝ :=
  1 - Real.exp
    (2 * (((2 * d + 1 : ℕ) : ℝ) * u) -
      2 * t * a ^ (2 : ℕ) * Real.sinh (2 * u))

theorem routeUHardEdgeKelvinHeatDefect_pos_iff
    {a t u : ℝ} (ha : 0 < a) (hu : 0 < u) (d : ℕ) :
    0 < routeUHardEdgeKelvinHeatDefect a d t u ↔
      routeUHardEdgeKelvinCriticalHeatTime a d u < t := by
  have hden : 0 < a ^ (2 : ℕ) * Real.sinh (2 * u) :=
    mul_pos (sq_pos_of_pos ha) (Real.sinh_pos_iff.mpr (by positivity))
  rw [routeUHardEdgeKelvinHeatDefect, sub_pos, Real.exp_lt_one_iff,
    routeUHardEdgeKelvinCriticalHeatTime, div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith

theorem routeUHardEdgeKelvinHeatDefect_neg_iff
    {a t u : ℝ} (ha : 0 < a) (hu : 0 < u) (d : ℕ) :
    routeUHardEdgeKelvinHeatDefect a d t u < 0 ↔
      t < routeUHardEdgeKelvinCriticalHeatTime a d u := by
  have hden : 0 < a ^ (2 : ℕ) * Real.sinh (2 * u) :=
    mul_pos (sq_pos_of_pos ha) (Real.sinh_pos_iff.mpr (by positivity))
  rw [routeUHardEdgeKelvinHeatDefect, sub_neg, Real.one_lt_exp_iff,
    routeUHardEdgeKelvinCriticalHeatTime, lt_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

theorem routeUHardEdgeKelvinHeatDefect_eq_zero_iff
    {a t u : ℝ} (ha : 0 < a) (hu : 0 < u) (d : ℕ) :
    routeUHardEdgeKelvinHeatDefect a d t u = 0 ↔
      t = routeUHardEdgeKelvinCriticalHeatTime a d u := by
  have hden : 0 < a ^ (2 : ℕ) * Real.sinh (2 * u) :=
    mul_pos (sq_pos_of_pos ha) (Real.sinh_pos_iff.mpr (by positivity))
  rw [routeUHardEdgeKelvinHeatDefect, sub_eq_zero, eq_comm,
    Real.exp_eq_one_iff, routeUHardEdgeKelvinCriticalHeatTime,
    eq_div_iff hden.ne']
  constructor <;> intro h <;> nlinarith

/-- The heat orientation genuinely changes on every positive Kelvin orbit. -/
theorem exists_pos_heatTimes_with_opposite_routeUHardEdgeKelvinHeatDefect
    {a u : ℝ} (ha : 0 < a) (hu : 0 < u) (d : ℕ) :
    ∃ tMinus tPlus : ℝ, 0 < tMinus ∧ 0 < tPlus ∧
      routeUHardEdgeKelvinHeatDefect a d tMinus u < 0 ∧
      0 < routeUHardEdgeKelvinHeatDefect a d tPlus u := by
  let τ := routeUHardEdgeKelvinCriticalHeatTime a d u
  have hτ : 0 < τ := routeUHardEdgeKelvinCriticalHeatTime_pos ha hu d
  refine ⟨τ / 2, 2 * τ, by positivity, by positivity, ?_, ?_⟩
  · rw [routeUHardEdgeKelvinHeatDefect_neg_iff ha hu d]
    dsimp only [τ]
    linarith
  · rw [routeUHardEdgeKelvinHeatDefect_pos_iff ha hu d]
    dsimp only [τ]
    linarith

/-- Physical pure heat defect before log-radius substitution. -/
def routeUHardEdgeKelvinPhysicalHeatDefect
    (a : ℝ) (d : ℕ) (t x : ℝ) : ℝ :=
  1 - (a ^ (2 : ℕ) / x ^ (2 : ℕ)) ^ (2 * d + 1) *
    Real.exp (-(t * ((a ^ (2 : ℕ) / x) ^ (2 : ℕ) - x ^ (2 : ℕ))))

/-- Inner log-radius converts the physical defect to its exact critical-phase normal form. -/
theorem routeUHardEdgeKelvinPhysicalHeatDefect_logRadius
    {a u : ℝ} (ha : 0 < a) (d : ℕ) (t : ℝ) :
    routeUHardEdgeKelvinPhysicalHeatDefect a d t (a * Real.exp (-u)) =
      routeUHardEdgeKelvinHeatDefect a d t u := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have he0 : Real.exp u ≠ 0 := Real.exp_ne_zero u
  have hexpSq : Real.exp (2 * u) = Real.exp u ^ (2 : ℕ) := by
    rw [show 2 * u = (2 : ℕ) * u by norm_num]
    exact Real.exp_nat_mul u 2
  have hratio : a ^ (2 : ℕ) / (a * Real.exp (-u)) ^ (2 : ℕ) = Real.exp (2 * u) := by
    rw [Real.exp_neg, hexpSq]
    field_simp [ha0, he0]
  have hgap : (a ^ (2 : ℕ) / (a * Real.exp (-u))) ^ (2 : ℕ) -
      (a * Real.exp (-u)) ^ (2 : ℕ) = 2 * a ^ (2 : ℕ) * Real.sinh (2 * u) := by
    rw [Real.exp_neg, Real.sinh_eq]
    have hexpNegSq : Real.exp (-(2 * u)) = (Real.exp u)⁻¹ ^ (2 : ℕ) := by
      rw [Real.exp_neg, hexpSq, inv_pow]
    rw [hexpSq, hexpNegSq]
    field_simp [ha0, he0]
  rw [routeUHardEdgeKelvinPhysicalHeatDefect, routeUHardEdgeKelvinHeatDefect,
    hratio, hgap, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- Actual paired cross current has exactly the critical heat defect in inner log-radius. -/
theorem routeUHardEdgeKelvinPairedCrossCurrent_one_logRadius
    {a u : ℝ} (ha : 0 < a) (P : Polynomial ℝ) (t : ℝ) :
    routeUHardEdgeKelvinPairedCrossCurrent a P t (fun _ => 1)
        (a * Real.exp (-u)) =
      routeUHardEdgeKelvinCrossDensity a P t (a * Real.exp (-u)) *
        routeUHardEdgeKelvinHeatDefect a (routeUHardEdgeKelvinDegree a P) t u := by
  have hx : 0 < a * Real.exp (-u) := mul_pos ha (Real.exp_pos _)
  rw [routeUHardEdgeKelvinPairedCrossCurrent_eq_weightDefect ha hx P]
  simp only [mul_one]
  change routeUHardEdgeKelvinCrossDensity a P t (a * Real.exp (-u)) *
      routeUHardEdgeKelvinPhysicalHeatDefect a
        (routeUHardEdgeKelvinDegree a P) t (a * Real.exp (-u)) = _
  rw [routeUHardEdgeKelvinPhysicalHeatDefect_logRadius ha]

end RHTower
