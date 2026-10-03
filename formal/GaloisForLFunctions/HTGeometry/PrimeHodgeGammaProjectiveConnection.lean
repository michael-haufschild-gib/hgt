import GaloisForLFunctions.HTGeometry.CubicWallHodgeBetaFlux
import GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder
import GaloisForLFunctions.HTGeometry.GammaWendelInequality
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureSignedProjectiveCurvature

/-!
# The projective connection carried by the prime–Hodge history tails

Let `g_n = Γ(n+1)/((2n+1) Γ(n+1/2)) = a_∞(n)/(2n+1)` be the theta-aperture half-order Gamma gap and
`κ_n = (g_n - 2g_{n+1} + g_{n+2})/g_n` its projective curvature.

* **(PPTI.45)** `κ_n = 3/((2n+3)(2n+5))`;
* **(PPTI.47)–(PPTI.48)** the history tails `m_n = 105/((2n+3)(2n+5)(2n+7))` of the prime–Hodge
  defect determine the curvature and conversely, `m_n = 35 κ_n/(2n+7)`, and through the double
  Hellinger law `κ_n = (2n+7)/35 · h(n+1) h(n+5/2)/(h(1) h(5/2))`;
* **Theorem PPTI-H.**  The discrete connection `∇y(n) = y_{n+2} - 2y_{n+1} + (1-κ_n) y_n` has
  solution space exactly `{c g + d q}`, `q_n = (n+1)(n+2) g_n`; `g_n √n → 1/2` and
  `q_n/n^{3/2} → 1/2`; every bounded (equivalently every null) parallel section is a multiple of
  `g`, and is fixed by its value at one site;
* the curvature and the tails are summable (`n²κ_n → 3/4`, `n³m_n → 105/8`) while the double-log
  sequence `3/(n log n)` is not, so neither can differ from it by a summable perturbation.
-/

open Real Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The aperture gap and its curvature -/

/-- The half-order Gamma gap `g_n = Γ(n+1)/((2n+1)Γ(n+1/2))`. -/
abbrev apertureGap (n : ℕ) : ℝ := thetaCuspGaussianApertureColdHalfOrderGammaGap n

theorem apertureGap_pos (n : ℕ) : 0 < apertureGap n :=
  thetaCuspGaussianApertureColdHalfOrderGammaGap_pos n

/-- **(PPTI.43).**  `g_n = a_∞(n)/(2n+1)` with `a_∞(s) = Γ(s+1)/Γ(s+1/2)`. -/
theorem apertureGap_eq_relativeCreator (n : ℕ) :
    ((apertureGap n : ℝ) : ℂ) = mellinRelativeCreator (n : ℂ) / (2 * (n : ℂ) + 1) := by
  rw [apertureGap, thetaCuspGaussianApertureColdHalfOrderGammaGap, mellinRelativeCreator,
    show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    show ((n : ℂ) + 1 / 2) = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  rw [div_div, mul_comm]

/-- **(PPTI.52).**  `g_{n+1}/g_n = (2n+2)/(2n+3)`. -/
theorem apertureGap_succ (n : ℕ) :
    apertureGap (n + 1) = (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3) * apertureGap n :=
  thetaCuspGaussianApertureColdHalfOrderGammaGap_succ n

/-- **(PPTI.44).**  The projective curvature `κ_n`. -/
def apertureCurvature (n : ℕ) : ℝ :=
  (apertureGap n - 2 * apertureGap (n + 1) + apertureGap (n + 2)) / apertureGap n

/-- **(PPTI.45).**  `κ_n = 3/((2n+3)(2n+5))`. -/
theorem apertureCurvature_eq (n : ℕ) :
    apertureCurvature n = 3 / ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5)) := by
  rw [apertureCurvature, thetaCuspGaussianApertureColdHalfOrderGammaGap_secondDiff]
  have hg := (apertureGap_pos n).ne'
  field_simp

theorem apertureCurvature_pos (n : ℕ) : 0 < apertureCurvature n := by
  rw [apertureCurvature_eq]
  positivity

theorem historyTail_eq (n : ℕ) :
    PrimeHodgeHistory.m n = 105 / ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7)) := by
  rw [PrimeHodgeHistory.m]
  push_cast
  ring

/-- **(PPTI.47).**  `m_n = 35 κ_n/(2n+7)`. -/
theorem historyTail_eq_apertureCurvature (n : ℕ) :
    PrimeHodgeHistory.m n = 35 * apertureCurvature n / (2 * (n : ℝ) + 7) := by
  rw [historyTail_eq, apertureCurvature_eq]
  field_simp
  ring

/-- **(PPTI.47).**  `κ_n = (2n+7) m_n/35`. -/
theorem apertureCurvature_eq_historyTail (n : ℕ) :
    apertureCurvature n = (2 * (n : ℝ) + 7) * PrimeHodgeHistory.m n / 35 := by
  rw [historyTail_eq, apertureCurvature_eq]
  field_simp
  ring

/-- The history tails are the normalized homotopy energies of the cubic wall. -/
theorem historyTail_eq_homotopyEnergy (n : ℕ) : PrimeHodgeHistory.m n = homotopyEnergy n := by
  rw [historyTail_eq, homotopyEnergy_eq]

/-- **(PPTI.48).**  `κ_n = (2n+7)/35 · h(n+1) h(n+5/2)/(h(1) h(5/2))`. -/
theorem apertureCurvature_eq_hodgeBeta (n : ℕ) :
    apertureCurvature n =
      (2 * (n : ℝ) + 7) / 35 *
        (eulerPrimitiveBoundaryHodgeBetaColumn (n + 1) *
            eulerPrimitiveBoundaryHodgeBetaColumn (n + 5 / 2) /
          (eulerPrimitiveBoundaryHodgeBetaColumn 1 *
            eulerPrimitiveBoundaryHodgeBetaColumn (5 / 2))) := by
  rw [apertureCurvature_eq_historyTail, historyTail_eq_homotopyEnergy, homotopyEnergy_eq_hodgeBeta]
  ring

/-! ## The discrete connection and its two rays -/

/-- **(PPTI.49).**  `∇_κ y(n) = y_{n+2} - 2 y_{n+1} + (1 - κ_n) y_n`. -/
def projectiveConnection (y : ℕ → ℝ) (n : ℕ) : ℝ :=
  y (n + 2) - 2 * y (n + 1) + (1 - apertureCurvature n) * y n

/-- The second ray `q_n = (n+1)(n+2) g_n`. -/
def secondRay (n : ℕ) : ℝ := ((n : ℝ) + 1) * ((n : ℝ) + 2) * apertureGap n

theorem secondRay_succ (n : ℕ) :
    secondRay (n + 1) = (2 * (n : ℝ) + 6) / (2 * (n : ℝ) + 3) * secondRay n := by
  rw [secondRay, secondRay, apertureGap_succ]
  push_cast
  field_simp
  ring

theorem projectiveConnection_apertureGap (n : ℕ) : projectiveConnection apertureGap n = 0 := by
  rw [projectiveConnection, apertureCurvature]
  have hg := (apertureGap_pos n).ne'
  field_simp
  ring

theorem projectiveConnection_secondRay (n : ℕ) : projectiveConnection secondRay n = 0 := by
  rw [projectiveConnection, apertureCurvature_eq, show n + 2 = (n + 1) + 1 from rfl,
    secondRay_succ (n + 1), secondRay_succ n]
  push_cast
  field_simp
  ring

theorem projectiveConnection_add_smul (c d : ℝ) (y z : ℕ → ℝ) (n : ℕ) :
    projectiveConnection (fun k => c * y k + d * z k) n =
      c * projectiveConnection y n + d * projectiveConnection z n := by
  simp only [projectiveConnection]
  ring

/-- Two parallel sections with the same first two values coincide. -/
theorem parallel_eq_of_initial {y z : ℕ → ℝ} (hy : ∀ n, projectiveConnection y n = 0)
    (hz : ∀ n, projectiveConnection z n = 0) (h0 : y 0 = z 0) (h1 : y 1 = z 1) : y = z := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | k + 2, ih =>
      have hyk := hy k
      have hzk := hz k
      rw [projectiveConnection] at hyk hzk
      rw [ih k (by omega), ih (k + 1) (by omega)] at hyk
      linarith

theorem secondRay_zero : secondRay 0 = 2 * apertureGap 0 := by
  rw [secondRay]
  push_cast
  ring

theorem secondRay_one : secondRay 1 = 6 * apertureGap 1 := by
  rw [secondRay]
  push_cast
  ring

/-- **Theorem PPTI-H (PPTI.50).**  The parallel sections are exactly `c g + d q`. -/
theorem parallel_iff (y : ℕ → ℝ) :
    (∀ n, projectiveConnection y n = 0) ↔
      ∃ c d : ℝ, ∀ n, y n = c * apertureGap n + d * secondRay n := by
  constructor
  · intro hy
    have hg0 := (apertureGap_pos 0).ne'
    have hg1 := (apertureGap_pos 1).ne'
    set d : ℝ := (y 1 / apertureGap 1 - y 0 / apertureGap 0) / 4 with hd
    set c : ℝ := y 0 / apertureGap 0 - 2 * d with hc
    refine ⟨c, d, fun n => ?_⟩
    have h := parallel_eq_of_initial hy (z := fun k => c * apertureGap k + d * secondRay k)
      (fun n => by
        rw [projectiveConnection_add_smul, projectiveConnection_apertureGap,
          projectiveConnection_secondRay]
        ring) ?_ ?_
    · exact congrFun h n
    · simp only [secondRay_zero, hc]
      field_simp
      ring
    · simp only [secondRay_one, hc, hd]
      field_simp
      ring
  · rintro ⟨c, d, h⟩ n
    have : y = fun k => c * apertureGap k + d * secondRay k := funext h
    rw [this, projectiveConnection_add_smul, projectiveConnection_apertureGap,
      projectiveConnection_secondRay]
    ring

/-- The coordinates `(c, d)` of a parallel section are unique. -/
theorem parallel_coeff_unique {c d c' d' : ℝ}
    (h : ∀ n, c * apertureGap n + d * secondRay n = c' * apertureGap n + d' * secondRay n) :
    c = c' ∧ d = d' := by
  have h0 := h 0
  have h1 := h 1
  rw [secondRay_zero] at h0
  rw [secondRay_one] at h1
  have e0 : ((c - c') + 2 * (d - d')) * apertureGap 0 = 0 := by linear_combination h0
  have e1 : ((c - c') + 6 * (d - d')) * apertureGap 1 = 0 := by linear_combination h1
  have e0' := (mul_eq_zero.1 e0).resolve_right (apertureGap_pos 0).ne'
  have e1' := (mul_eq_zero.1 e1).resolve_right (apertureGap_pos 1).ne'
  constructor <;> linarith

theorem apertureGap_le_zero (n : ℕ) : apertureGap n ≤ apertureGap 0 := by
  induction n with
  | zero => exact le_rfl
  | succ k ih =>
    rw [apertureGap_succ]
    have : (2 * (k : ℝ) + 2) / (2 * (k : ℝ) + 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith [apertureGap_pos k]

/-! ## Asymptotics of the two rays -/

/-- Wendel's bounds at the half step:
`(n+1/2) Γ(n+1/2) ≤ Γ(n+1) √(n+1)` and `Γ(n+1) ≤ Γ(n+1/2) √(n+1/2)`. -/
theorem gammaRatio_bounds (n : ℕ) :
    ((n : ℝ) + 1 / 2) * Real.Gamma ((n : ℝ) + 1 / 2) ≤
        Real.Gamma ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) ∧
      Real.Gamma ((n : ℝ) + 1) ≤ Real.Gamma ((n : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) + 1 / 2) := by
  have hx : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  have hup := Gamma_add_le hx (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hlo := le_Gamma_add hx (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  rw [show (n : ℝ) + 1 / 2 + 1 / 2 = (n : ℝ) + 1 by ring] at hup hlo
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hlo
  rw [← Real.sqrt_eq_rpow] at hup hlo
  exact ⟨by linarith, hup⟩

/-- **(PPTI.51).**  `g_n √n → 1/2`. -/
theorem tendsto_apertureGap_mul_sqrt :
    Tendsto (fun n : ℕ => apertureGap n * Real.sqrt n) atTop (𝓝 (1 / 2)) := by
  have hlo : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) / 2) atTop (𝓝 (1 / 2)) := by
    have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).sqrt
    rw [Real.sqrt_one] at h
    simpa using h.div_const 2
  have hhi : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / ((n : ℝ) + 1 / 2)) / 2) atTop
      (𝓝 (1 / 2)) := by
    have h := (tendsto_natCast_div_add_atTop (1 / 2 : ℝ)).sqrt
    rw [Real.sqrt_one] at h
    simpa using h.div_const 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨hl, -⟩ := gammaRatio_bounds n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hs1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hG := Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ) + 1 / 2 by positivity)
    have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    rw [Real.sqrt_div hn'.le, apertureGap, thetaCuspGaussianApertureColdHalfOrderGammaGap, div_div,
      div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hl hsn]
  · filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨-, hu⟩ := gammaRatio_bounds n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hG := Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ) + 1 / 2 by positivity)
    have hsh : 0 < Real.sqrt ((n : ℝ) + 1 / 2) := Real.sqrt_pos.2 (by positivity)
    have hsq : Real.sqrt ((n : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) + 1 / 2) = (n : ℝ) + 1 / 2 :=
      Real.mul_self_sqrt (by positivity)
    have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    rw [Real.sqrt_div hn'.le, apertureGap, thetaCuspGaussianApertureColdHalfOrderGammaGap, div_div,
      div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hkey : Real.Gamma ((n : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) + 1 / 2) *
        (Real.sqrt n * Real.sqrt ((n : ℝ) + 1 / 2)) =
          Real.Gamma ((n : ℝ) + 1 / 2) * Real.sqrt n * ((n : ℝ) + 1 / 2) := by
      calc Real.Gamma ((n : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) + 1 / 2) *
            (Real.sqrt n * Real.sqrt ((n : ℝ) + 1 / 2))
          = Real.Gamma ((n : ℝ) + 1 / 2) * Real.sqrt n *
              (Real.sqrt ((n : ℝ) + 1 / 2) * Real.sqrt ((n : ℝ) + 1 / 2)) := by ring
        _ = _ := by rw [hsq]
    nlinarith [mul_le_mul_of_nonneg_right hu (mul_nonneg hsn hsh.le)]

theorem tendsto_apertureGap_zero : Tendsto apertureGap atTop (𝓝 0) := by
  have h := tendsto_apertureGap_mul_sqrt.div_atTop
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [Function.comp_apply]
  field_simp

/-- **(PPTI.51).**  `q_n/n^{3/2} → 1/2`. -/
theorem tendsto_secondRay_div :
    Tendsto (fun n : ℕ => secondRay n / ((n : ℝ) * Real.sqrt n)) atTop (𝓝 (1 / 2)) := by
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) / ((n : ℝ) * (n : ℝ)))
      atTop (𝓝 1) := by
    have h1 := tendsto_natCast_div_add_atTop (1 : ℝ)
    have h2 := tendsto_natCast_div_add_atTop (2 : ℝ)
    have h := (h1.inv₀ one_ne_zero).mul (h2.inv₀ one_ne_zero)
    simp only [inv_one, mul_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have h := hratio.mul tendsto_apertureGap_mul_sqrt
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := Real.mul_self_sqrt hn'.le
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  rw [secondRay, eq_div_iff (by positivity)]
  calc ((n : ℝ) + 1) * ((n : ℝ) + 2) / ((n : ℝ) * (n : ℝ)) * (apertureGap n * Real.sqrt n) *
        ((n : ℝ) * Real.sqrt n)
      = ((n : ℝ) + 1) * ((n : ℝ) + 2) * apertureGap n *
          ((Real.sqrt n * Real.sqrt n) / ((n : ℝ) * (n : ℝ)) * (n : ℝ)) := by ring
    _ = ((n : ℝ) + 1) * ((n : ℝ) + 2) * apertureGap n := by
        rw [hs]
        field_simp

theorem tendsto_secondRay_atTop : Tendsto secondRay atTop atTop := by
  have hgrow : Tendsto (fun n : ℕ => (n : ℝ) * Real.sqrt n) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (tendsto_secondRay_div).pos_mul_atTop (by norm_num) hgrow
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  field_simp

/-- **Bounded-ray rigidity.**  A parallel section is bounded iff it is a multiple of `g`. -/
theorem parallel_bounded_iff {y : ℕ → ℝ} (hy : ∀ n, projectiveConnection y n = 0) :
    (∃ C, ∀ n, |y n| ≤ C) ↔ ∃ c, ∀ n, y n = c * apertureGap n := by
  obtain ⟨c, d, hcd⟩ := (parallel_iff y).1 hy
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨c, fun n => ?_⟩
    by_contra hne
    have hd : d ≠ 0 := by
      rintro rfl
      exact hne (by rw [hcd n, zero_mul, add_zero])
    have hbound : ∀ n, |d| * secondRay n ≤ C + |c| * apertureGap 0 := by
      intro n
      have hq : 0 < secondRay n := by
        rw [secondRay]
        exact mul_pos (by positivity) (apertureGap_pos n)
      have h1 : d * secondRay n = y n - c * apertureGap n := by rw [hcd n]; ring
      calc |d| * secondRay n = |d * secondRay n| := by rw [abs_mul, abs_of_pos hq]
        _ = |y n - c * apertureGap n| := by rw [h1]
        _ ≤ |y n| + |c * apertureGap n| := abs_sub _ _
        _ ≤ C + |c| * apertureGap 0 := by
          rw [abs_mul, abs_of_pos (apertureGap_pos n)]
          gcongr
          · exact hC n
          · exact apertureGap_le_zero n
    have htend : Tendsto (fun n => |d| * secondRay n) atTop atTop :=
      tendsto_secondRay_atTop.const_mul_atTop (abs_pos.2 hd)
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop (C + |c| * apertureGap 0)).exists
    exact absurd (hbound n) (not_le.2 hn)
  · rintro ⟨c, hc⟩
    refine ⟨|c| * apertureGap 0, fun n => ?_⟩
    rw [hc n, abs_mul, abs_of_pos (apertureGap_pos n)]
    exact mul_le_mul_of_nonneg_left (apertureGap_le_zero n) (abs_nonneg c)

/-- A parallel section tends to zero iff it is a multiple of `g`. -/
theorem parallel_tendsto_zero_iff {y : ℕ → ℝ} (hy : ∀ n, projectiveConnection y n = 0) :
    Tendsto y atTop (𝓝 0) ↔ ∃ c, ∀ n, y n = c * apertureGap n := by
  constructor
  · intro ht
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto y ht)
    exact (parallel_bounded_iff hy).1
      ⟨C, fun n => by simpa [Real.norm_eq_abs] using hC (y n) ⟨n, rfl⟩⟩
  · rintro ⟨c, hc⟩
    have h := tendsto_apertureGap_zero.const_mul c
    rw [mul_zero] at h
    exact h.congr fun n => (hc n).symm

/-- A bounded parallel section is fixed by its value at one site. -/
theorem parallel_bounded_unique {y z : ℕ → ℝ} (hy : ∀ n, projectiveConnection y n = 0)
    (hz : ∀ n, projectiveConnection z n = 0) (hyb : ∃ C, ∀ n, |y n| ≤ C)
    (hzb : ∃ C, ∀ n, |z n| ≤ C) (n₀ : ℕ) (h : y n₀ = z n₀) : y = z := by
  obtain ⟨c, hc⟩ := (parallel_bounded_iff hy).1 hyb
  obtain ⟨c', hc'⟩ := (parallel_bounded_iff hz).1 hzb
  have hcc : c = c' := by
    have := h
    rw [hc, hc'] at this
    exact mul_right_cancel₀ (apertureGap_pos n₀).ne' this
  funext n
  rw [hc, hc', hcc]

end GaloisForLFunctions.HTGeometry
