import GaloisForLFunctions.RHTower.ModularArcDyadicFullStripFunctionalSymmetry

/-!
# The two-variable critical-strip oscillatory Mellin transform: dihedral `(l, τ) ↦ (±l, ±τ)` symmetry, `cosh(lv) cos(τv)` representation, `R → ∞` Dominated Convergence, and `k`-and-`τ`-independent sub-critical strip bounds

In `ModularArcDyadicInfiniteLineVector` and `ModularArcDyadicFullStripFunctionalSymmetry`, we
studied the real-axis multiplicative Mellin integral
`∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx` (`|l| < 1/2`, `τ = 0`) and the
critical-line oscillatory Mellin integral
`∫_{x > 0} x^{−1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx` (`l = 0`, `τ ∈ ℝ`).

In this module we unify both transforms into the **two-variable critical-strip oscillatory Mellin
transform**
`M_k(l, τ) = ∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx`
across the entire two-dimensional critical strip `(l, τ) ∈ (−1/2, 1/2) × ℝ`
(corresponding to `s = 1/2 + l + iτ` with `0 < Re(s) < 1`):

1. **Exact log-scale change of variables and `cosh(lv) cos(τv)` representation
   (`setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile`,
   `integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh`):**
   For all `l, τ ∈ ℝ`,
   `∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx = ∫_ℝ e^{lv} cos(τv) · arcLineInfiniteDyadicProfile k ν v dv`,
   and for all `|l| < 1/2`, `τ ∈ ℝ`, this equals `∫_ℝ cosh(lv) cos(τv) · arcLineInfiniteDyadicProfile k ν v dv`.
2. **Simultaneous dihedral symmetry `(l, τ) ↦ (±l, ±τ)`
   (`setIntegral_Ioi_rpow_neg_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector`,
   `setIntegral_Ioi_rpow_mul_cos_neg_log_mul_arcLineInfiniteDyadicVector`,
   `setIntegral_Ioi_rpow_abs_sub_half_mul_cos_abs_log_mul_arcLineInfiniteDyadicVector`):**
   `M_k(−l, τ) = M_k(l, −τ) = M_k(|l|, |τ|) = M_k(l, τ)` for all `(l, τ) ∈ ℝ²`, encoding both
   the functional equation reflection `s ↔ 1 − s̄` and Schwarz conjugation `s ↔ s̄`.
3. **Exact specialization welds to the real-axis Laplace transform (`τ = 0`) and critical-line
   cosine transform (`l = 0`)
   (`setIntegral_Ioi_rpow_mul_cos_zero_log_mul_arcLineInfiniteDyadicVector`,
   `setIntegral_Ioi_rpow_zero_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector`):**
   `M_k(l, 0) = arcLineInfiniteDyadicLaplaceTransform k ν |l| > 0` for `|l| < 1/2` and
   `M_k(0, τ) = arcLineInfiniteDyadicCosTransform k ν τ > 0` for `τ ∈ ℝ`.
4. **Unconditional `R → ∞` Dominated Convergence across all `(|l| < 1/2, τ ∈ ℝ)` and
   `k`-and-`τ`-independent `1650 · ν.real univ / (1/4 − |l|)` bound on `|l| < 1/4`
   (`tendsto_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_atTop`,
   `abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_le_quarter`,
   `exists_dyadic_stripOscillatoryMellin_arcWitness`).**
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Exact log-scale bridge and dihedral `(l, τ) ↦ (±l, ±τ)` symmetries -/

/-- Helper: `|exp(l · v)| ≤ exp(|l| · |v|)` for all `l, v ∈ ℝ`. -/
theorem abs_exp_mul_le_exp_abs_mul (l v : ℝ) :
    |Real.exp (l * v)| ≤ Real.exp (|l| * |v|) := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact (le_abs_self (l * v)).trans_eq (abs_mul l v)

/-- **Exact log-scale change of variables for the two-variable oscillatory Mellin integral at
finite dyadic depth `R` (`k ≥ 1`, `l, τ ∈ ℝ`):**
`∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineDyadicTowerVector k R ν x dx = ∫_ℝ e^{lv} cos(τv) · arcLineDyadicTowerProfile k R ν v dv`. -/
theorem setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_eq_profile
    {k : ℕ} (hk : 1 ≤ k) (R : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineDyadicTowerVector k R ν x) =
      ∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineDyadicTowerVector hk R ν v]
  have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
      Real.exp (l * v) * Real.exp (v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.cos (τ * v) *
          arcLineDyadicTowerVector k R ν (Real.exp v))
      = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.cos (τ * v) *
          arcLineDyadicTowerVector k R ν (Real.exp v) := by ring
    _ = (Real.exp (l * v) * Real.exp (v / 2)) * Real.cos (τ * v) *
          arcLineDyadicTowerVector k R ν (Real.exp v) := by rw [hexp]
    _ = Real.exp (l * v) * Real.cos (τ * v) *
          (Real.exp (v / 2) * arcLineDyadicTowerVector k R ν (Real.exp v)) := by ring

/-- **Exact log-scale change of variables for the two-variable oscillatory Mellin integral of
`arcLineInfiniteDyadicVector k ν` (`k ≥ 1`, `l, τ ∈ ℝ`):**
`∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx = ∫_ℝ e^{lv} cos(τv) · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  rw [setIntegral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp,
    ← exp_half_mul_arcLineInfiniteDyadicVector hk ν v]
  have hexp : Real.exp v * Real.exp (v * (l - 1 / 2)) =
      Real.exp (l * v) * Real.exp (v / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc Real.exp v * (Real.exp (v * (l - 1 / 2)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v))
      = (Real.exp v * Real.exp (v * (l - 1 / 2))) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by ring
    _ = (Real.exp (l * v) * Real.exp (v / 2)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicVector k ν (Real.exp v) := by rw [hexp]
    _ = Real.exp (l * v) * Real.cos (τ * v) *
          (Real.exp (v / 2) * arcLineInfiniteDyadicVector k ν (Real.exp v)) := by ring

/-- Reflection symmetry `l ↦ −l` for the two-variable Fourier-Laplace transform of
`arcLineInfiniteDyadicProfile k ν`. -/
theorem integral_exp_neg_mul_cos_mul_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ v : ℝ, Real.exp ((-l) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have h := integral_neg_eq_self
    (fun v : ℝ => Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) volume
  simpa [mul_neg, neg_mul, Real.cos_neg, arcLineInfiniteDyadicProfile_neg] using h

/-- Reflection symmetry `τ ↦ −τ` for the two-variable Fourier-Laplace transform of
`arcLineInfiniteDyadicProfile k ν`. -/
theorem integral_exp_mul_cos_neg_mul_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ v : ℝ, Real.exp (l * v) * Real.cos ((-τ) * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  congr 1
  funext v
  rw [neg_mul, Real.cos_neg]

/-- Combined dihedral reduction `(l, τ) ↦ (|l|, |τ|)` on the logarithmic axis. -/
theorem integral_exp_abs_mul_cos_abs_mul_arcLineInfiniteDyadicProfile
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ v : ℝ, Real.exp (|l| * v) * Real.cos (|τ| * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hτ : (∫ v : ℝ, Real.exp (|l| * v) * Real.cos (|τ| * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (|l| * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    rcases le_total 0 τ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, integral_exp_mul_cos_neg_mul_arcLineInfiniteDyadicProfile]
  rw [hτ]
  rcases le_total 0 l with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, integral_exp_neg_mul_cos_mul_arcLineInfiniteDyadicProfile]

/-- **Functional equation reflection `l ↦ −l` (`s ↔ 1 − s̄`) for the two-variable oscillatory Mellin
integral (`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_rpow_neg_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi 0, x ^ (-l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν (-l) τ,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν l τ,
    integral_exp_neg_mul_cos_mul_arcLineInfiniteDyadicProfile]

/-- **Conjugation reflection `τ ↦ −τ` (`s ↔ s̄`) for the two-variable oscillatory Mellin integral
(`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_rpow_mul_cos_neg_log_mul_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos ((-τ) * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν l (-τ),
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν l τ,
    integral_exp_mul_cos_neg_mul_arcLineInfiniteDyadicProfile]

/-- **Combined dihedral invariance `(l, τ) ↦ (|l|, |τ|)` for the two-variable oscillatory Mellin
integral (`k ≥ 1`, `l, τ ∈ ℝ`).** -/
theorem setIntegral_Ioi_rpow_abs_sub_half_mul_cos_abs_log_mul_arcLineInfiniteDyadicVector
    {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam) (l τ : ℝ) :
    (∫ x in Ioi 0, x ^ (|l| - 1 / 2) * Real.cos (|τ| * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν |l| |τ|,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk ν l τ,
    integral_exp_abs_mul_cos_abs_mul_arcLineInfiniteDyadicProfile]

/-! ### Exact welds at `τ = 0` (real axis) and `l = 0` (critical line) -/

/-- **Exact weld at `τ = 0`:** the two-variable oscillatory Mellin integral reduces to the
multiplicative Mellin integral `∫_{x > 0} x^{l − 1/2} · arcLineInfiniteDyadicVector k ν x dx`. -/
theorem setIntegral_Ioi_rpow_mul_cos_zero_log_mul_arcLineInfiniteDyadicVector
    (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (0 * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
  simp

/-- **Exact weld at `l = 0`:** the two-variable oscillatory Mellin integral reduces to the
critical-line oscillatory Mellin integral
`∫_{x > 0} x^{−1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx`. -/
theorem setIntegral_Ioi_rpow_zero_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector
    (k : ℕ) (ν : Measure ArcParam) (τ : ℝ) :
    (∫ x in Ioi 0, x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x) =
      ∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x := by
  rw [zero_sub]

/-! ### Integrability, `cosh(lv) cos(τv)` representation, and `R → ∞` Dominated Convergence -/

/-- Integrability of `e^{lv} cos(τv) · arcLineDyadicTowerProfile k R ν v` across the full open
critical strip `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`). -/
theorem integrable_exp_mul_cos_mul_arcLineDyadicTowerProfile
    {k : ℕ} (hk : 2 ≤ k) (R : ℕ) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      Real.exp (l * v) * Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v) := by
  set c := (|l| + 1 / 2) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : c < 1 / 2 := by dsimp [c]; linarith
  have hcl : 0 < c - |l| := by dsimp [c]; linarith
  set A := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))
  refine ((integrable_rexp_neg_mul_abs hcl).const_mul A).mono'
    (((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v) * Real.cos (τ * v))).mul
      (continuous_arcLineDyadicTowerProfile k R ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hcos : |Real.exp (l * v)| * |Real.cos (τ * v)| ≤ Real.exp (|l| * |v|) := by
    calc |Real.exp (l * v)| * |Real.cos (τ * v)|
        ≤ Real.exp (|l| * |v|) * 1 :=
          mul_le_mul (abs_exp_mul_le_exp_abs_mul l v) (Real.abs_cos_le_one _)
            (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|l| * |v|) := mul_one _
  calc |Real.exp (l * v)| * |Real.cos (τ * v)| * |arcLineDyadicTowerProfile k R ν v|
      ≤ Real.exp (|l| * |v|) * (A * Real.exp (-(c * |v|))) :=
        mul_le_mul hcos
          (abs_arcLineDyadicTowerProfile_le_exp_subcritical hk R hν hc0 hc v)
          (abs_nonneg _) (Real.exp_pos _).le
    _ = A * Real.exp (-((c - |l|) * |v|)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- Integrability of `e^{lv} cos(τv) · arcLineInfiniteDyadicProfile k ν v` across the full open
critical strip `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`). -/
theorem integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    Integrable (fun v : ℝ =>
      Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
  set c := (|l| + 1 / 2) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : c < 1 / 2 := by dsimp [c]; linarith
  have hcl : 0 < c - |l| := by dsimp [c]; linarith
  set A := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))
  refine ((integrable_rexp_neg_mul_abs hcl).const_mul A).mono'
    (((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v) * Real.cos (τ * v))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hcos : |Real.exp (l * v)| * |Real.cos (τ * v)| ≤ Real.exp (|l| * |v|) := by
    calc |Real.exp (l * v)| * |Real.cos (τ * v)|
        ≤ Real.exp (|l| * |v|) * 1 :=
          mul_le_mul (abs_exp_mul_le_exp_abs_mul l v) (Real.abs_cos_le_one _)
            (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|l| * |v|) := mul_one _
  calc |Real.exp (l * v)| * |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
      ≤ Real.exp (|l| * |v|) * (A * Real.exp (-(c * |v|))) :=
        mul_le_mul hcos
          (abs_arcLineInfiniteDyadicProfile_le_exp_subcritical hk hν hc0 hc v)
          (abs_nonneg _) (Real.exp_pos _).le
    _ = A * Real.exp (-((c - |l|) * |v|)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- **Exact `cosh(lv) cos(τv)` representation across `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`):**
`∫_ℝ e^{lv} cos(τv) · arcLineInfiniteDyadicProfile k ν v dv = ∫_ℝ cosh(lv) cos(τv) · arcLineInfiniteDyadicProfile k ν v dv`. -/
theorem integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
  have hIl : Integrable (fun v : ℝ =>
      Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl τ
  have hIneg : Integrable (fun v : ℝ =>
      Real.exp (-(l * v)) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    have heq : (fun v : ℝ => Real.exp (-(l * v)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => Real.exp ((-l) * v) * Real.cos (τ * v) *
          arcLineInfiniteDyadicProfile k ν v := by
      funext v; rw [neg_mul]
    rw [heq]
    exact integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν (by simpa using hl) τ
  have hneg_eq : (∫ v : ℝ, Real.exp (-(l * v)) * Real.cos (τ * v) *
        arcLineInfiniteDyadicProfile k ν v) =
      ∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v := by
    have heq : (fun v : ℝ => Real.exp (-(l * v)) * Real.cos (τ * v) *
          arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => Real.exp ((-l) * v) * Real.cos (τ * v) *
          arcLineInfiniteDyadicProfile k ν v := by
      funext v; rw [neg_mul]
    rw [heq, integral_exp_neg_mul_cos_mul_arcLineInfiniteDyadicProfile]
  have e : (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) *
        arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => (1 / 2 : ℝ) * (Real.exp (l * v) * Real.cos (τ * v) *
          arcLineInfiniteDyadicProfile k ν v +
        Real.exp (-(l * v)) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    funext v; rw [Real.cosh_eq]; ring
  rw [e, integral_const_mul, integral_add hIl hIneg, hneg_eq]
  ring

/-- **Unconditional `R → ∞` Dominated Convergence for the two-variable Fourier-Laplace integral
across the entire open critical strip `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem tendsto_integral_exp_mul_cos_mul_arcLineDyadicTowerProfile_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    Tendsto (fun R : ℕ =>
      ∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineDyadicTowerProfile k R ν v)
      atTop (𝓝 (∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) *
        arcLineInfiniteDyadicProfile k ν v)) := by
  set c := (|l| + 1 / 2) / 2
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : c < 1 / 2 := by dsimp [c]; linarith
  have hcl : 0 < c - |l| := by dsimp [c]; linarith
  set A := 25 * ν.real univ * (1 + 16 / ((1 - 2 * c) ^ 2 * (Real.log k) ^ 2))
  refine tendsto_integral_of_dominated_convergence
    (fun v => A * Real.exp (-((c - |l|) * |v|)))
    (fun R => (((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v) * Real.cos (τ * v))).mul
      (continuous_arcLineDyadicTowerProfile k R ν)).aestronglyMeasurable)
    ((integrable_rexp_neg_mul_abs hcl).const_mul A)
    (fun R => Eventually.of_forall fun v => ?_)
    (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hcos : |Real.exp (l * v)| * |Real.cos (τ * v)| ≤ Real.exp (|l| * |v|) := by
      calc |Real.exp (l * v)| * |Real.cos (τ * v)|
          ≤ Real.exp (|l| * |v|) * 1 :=
            mul_le_mul (abs_exp_mul_le_exp_abs_mul l v) (Real.abs_cos_le_one _)
              (abs_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (|l| * |v|) := mul_one _
    calc |Real.exp (l * v)| * |Real.cos (τ * v)| * |arcLineDyadicTowerProfile k R ν v|
        ≤ Real.exp (|l| * |v|) * (A * Real.exp (-(c * |v|))) :=
          mul_le_mul hcos
            (abs_arcLineDyadicTowerProfile_le_exp_subcritical hk R hν hc0 hc v)
            (abs_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp (-((c - |l|) * |v|)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  · exact (tendsto_arcLineDyadicTowerProfile_atTop hk ν v).const_mul
      (Real.exp (l * v) * Real.cos (τ * v))

/-- **Unconditional `R → ∞` Dominated Convergence for the two-variable oscillatory Mellin integral
on `(0, ∞)` across the entire open critical strip `|l| < 1/2`, `τ ∈ ℝ` (`k ≥ 2`).** -/
theorem tendsto_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    Tendsto (fun R : ℕ =>
      ∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineDyadicTowerVector k R ν x)
      atTop (𝓝 (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x)) := by
  have hk1 : 1 ≤ k := by omega
  simp_rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_eq_profile hk1 _ ν l τ,
    setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ]
  exact tendsto_integral_exp_mul_cos_mul_arcLineDyadicTowerProfile_atTop hk hν hl τ

/-! ### `k`-and-`τ`-independent strip bound on `|l| < 1/4` -/

/-- **Scale- and height-independent `1650 · ν.real univ / (1/4 − |l|)` bound across the central
sub-strip `|l| < 1/4` and all `τ ∈ ℝ` (`k ≥ 2`):**
For every `k ≥ 2`, `|l| < 1/4`, and `τ ∈ ℝ`,
`|∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx| ≤ 1650 · ν.real univ / (1/4 − |l|)`
(with constant completely independent of both `k ≥ 2` and `τ ∈ ℝ`). -/
theorem abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_le_quarter
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 4) (τ : ℝ) :
    |∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
        arcLineInfiniteDyadicVector k ν x| ≤
      1650 * ν.real univ / (1 / 4 - |l|) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith
  have hcl : 0 < 1 / 4 - |l| := sub_pos.mpr hl
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ]
  have h1 := abs_integral_le_integral_abs
    (μ := volume)
    (f := fun v : ℝ => Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
  have h2 := integral_mono
    (integrable_exp_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ).abs
    ((integrable_rexp_neg_mul_abs hcl).const_mul (825 * ν.real univ))
    (fun v => ?_)
  · rw [integral_const_mul, integral_rexp_neg_mul_abs hcl] at h2
    calc |∫ v : ℝ, Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v|
        ≤ ∫ v : ℝ, |Real.exp (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v| := h1
      _ ≤ 825 * ν.real univ * (2 / (1 / 4 - |l|)) := h2
      _ = 1650 * ν.real univ / (1 / 4 - |l|) := by ring
  · dsimp only
    rw [abs_mul, abs_mul]
    have hcos : |Real.exp (l * v)| * |Real.cos (τ * v)| ≤ Real.exp (|l| * |v|) := by
      calc |Real.exp (l * v)| * |Real.cos (τ * v)|
          ≤ Real.exp (|l| * |v|) * 1 :=
            mul_le_mul (abs_exp_mul_le_exp_abs_mul l v) (Real.abs_cos_le_one _)
              (abs_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (|l| * |v|) := mul_one _
    calc |Real.exp (l * v)| * |Real.cos (τ * v)| * |arcLineInfiniteDyadicProfile k ν v|
        ≤ Real.exp (|l| * |v|) * (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|))) :=
          mul_le_mul hcos
            (abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v)
            (abs_nonneg _) (Real.exp_pos _).le
      _ = 825 * ν.real univ * Real.exp (-((1 / 4 - |l|) * |v|)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-! ### Master unconditional theorem for the two-variable critical-strip oscillatory Mellin transform -/

/-- **Master unconditional theorem for the two-variable critical-strip oscillatory Mellin transform
`M_k(l, τ) = ∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineInfiniteDyadicVector k ν x dx`.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2`, the single line-model vector
`V_k = arcLineInfiniteDyadicVector k ν : ℝ → ℝ` satisfies:
1. Simultaneous dihedral invariance `(l, τ) ↦ (±l, ±τ)` across all `(l, τ) ∈ ℝ²`:
   `M_k(−l, τ) = M_k(l, −τ) = M_k(|l|, |τ|) = M_k(l, τ)`;
2. Exact specialization at `τ = 0` (real axis): for all `|l| < 1/2`, `M_k(l, 0) > 0`, and for every
   `N ∈ ℕ`, `M_k(l, 0) / (1/2 − l)^N → 0` as `l → (1/2)⁻` and `M_k(l, 0) / (1/2 + l)^N → 0` as `l → (−1/2)⁺`;
3. Exact specialization at `l = 0` (critical line): for all `τ ∈ ℝ`, `M_k(0, τ) > 0`;
4. Unconditional `R → ∞` Dominated Convergence across all `|l| < 1/2` and `τ ∈ ℝ`:
   `∫_{x > 0} x^{l − 1/2} cos(τ log x) · arcLineDyadicTowerVector k R ν x dx → M_k(l, τ)`;
5. Scale- and height-independent sub-critical strip bound: for all `|l| < 1/4` and `τ ∈ ℝ`,
   `|M_k(l, τ)| ≤ 1650 · ν.real univ / (1/4 − |l|)` (independently of both `k` and `τ`);
6. As `k → ∞`, simultaneously:
   - `M_k(l, 0) → ∫ e^{lv} arcPoissonProfile ν v > 0` for all `|l| < 1/2`,
   - `M_k(0, τ) → ∫ cos(τv) arcPoissonProfile ν v > 0` for all `τ ∈ ℝ`,
   - `∫_{x > 0} (V_k(x) − arcLineAtomicVector (log k) ν x)² dx → 0` (at rate `O(k⁻¹)`), and
   - `arcLineInfiniteDyadicSineMoment k ν (arcFreq n) → 0` for all `n ∈ ℕ`. -/
theorem exists_dyadic_stripOscillatoryMellin_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      (∀ k : ℕ, 2 ≤ k →
        (∀ l τ : ℝ,
          (∫ x in Ioi 0, x ^ (|l| - 1 / 2) * Real.cos (|τ| * Real.log x) *
              arcLineInfiniteDyadicVector k ν x) =
            ∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
              arcLineInfiniteDyadicVector k ν x) ∧
        (∀ l : ℝ, |l| < 1 / 2 →
          0 < ∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (0 * Real.log x) *
            arcLineInfiniteDyadicVector k ν x) ∧
        (∀ τ : ℝ,
          0 < ∫ x in Ioi 0, x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) *
            arcLineInfiniteDyadicVector k ν x) ∧
        (∀ l : ℝ, |l| < 1 / 2 → ∀ τ : ℝ,
          Tendsto (fun R : ℕ =>
            ∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
              arcLineDyadicTowerVector k R ν x)
            atTop (𝓝 (∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
              arcLineInfiniteDyadicVector k ν x))) ∧
        (∀ l : ℝ, |l| < 1 / 4 → ∀ τ : ℝ,
          |∫ x in Ioi 0, x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
              arcLineInfiniteDyadicVector k ν x| ≤
            1650 * ν.real univ / (1 / 4 - |l|)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 - l) ^ N)
          (𝓝[<] (1 / 2)) (𝓝 0)) ∧
        (∀ N : ℕ, Tendsto (fun l : ℝ =>
          (∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) /
            (1 / 2 + l) ^ N)
          (𝓝[>] (-1 / 2)) (𝓝 0))) ∧
      (∀ l : ℝ, |l| < 1 / 2 →
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi 0, x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x)
          atTop (𝓝 (∫ v, Real.exp (l * v) * arcPoissonProfile ν v))) ∧
      (∀ τ : ℝ,
        Tendsto (fun k : ℕ =>
          ∫ x in Ioi 0, x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) *
            arcLineInfiniteDyadicVector k ν x)
          atTop (𝓝 (∫ v, Real.cos (τ * v) * arcPoissonProfile ν v))) ∧
      Tendsto (fun k : ℕ =>
        ∫ x in Ioi 0,
          (arcLineInfiniteDyadicVector k ν x - arcLineAtomicVector (Real.log k) ν x) ^ 2)
        atTop (𝓝 0) ∧
      (∀ n : ℕ, Tendsto (fun k : ℕ => arcLineInfiniteDyadicSineMoment k ν (arcFreq n))
        atTop (𝓝 0)) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym,
    fun k hk => ?_,
    fun l hl => tendsto_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_atTop_of_abs_lt_half hsym hl,
    fun τ => ?_,
    tendsto_setIntegral_Ioi_sq_arcLineInfiniteDyadicVector_sub_atomic_atTop hsym,
    tendsto_arcLineInfiniteDyadicSineMoment_arcFreq_atTop hblind⟩
  · have hk1 : 1 ≤ k := by omega
    refine ⟨fun l τ =>
        setIntegral_Ioi_rpow_abs_sub_half_mul_cos_abs_log_mul_arcLineInfiniteDyadicVector hk1 ν l τ,
      fun l hl => ?_,
      fun τ => ?_,
      fun l hl τ =>
        tendsto_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineDyadicTowerVector_atTop hk hsym hl τ,
      fun l hl τ =>
        abs_setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_le_quarter
          hk hsym hl τ,
      fun N =>
        tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin hk N hsym,
      fun N =>
        tendsto_div_pow_setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_nhdsWithin_neg_half
          hk N hsym⟩
    · rw [setIntegral_Ioi_rpow_mul_cos_zero_log_mul_arcLineInfiniteDyadicVector]
      exact setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_pos_of_abs_lt_half hk hsym hpd hl
    · rw [setIntegral_Ioi_rpow_zero_sub_half_mul_cos_log_mul_arcLineInfiniteDyadicVector]
      exact setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_pos hk hsym hpd τ
  · refine (tendsto_arcLineInfiniteDyadicCosTransform_atTop ν τ).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with k hk
    exact (setIntegral_Ioi_cos_log_mul_arcLineInfiniteDyadicVector_eq hk hsym τ).symm

end

end RHTower
