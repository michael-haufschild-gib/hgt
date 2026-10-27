import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanCrossKernel
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedPrimeRows
import GaloisForLFunctions.ArithmeticElectrostatics.TheGaugeIsInvisibleAtAtomicResolution

/-!
# The stability law at the spacing scale

The archimedean place pays the prime place on atomic tests up to a fixed fraction of the spacing
`δ_N = log(1 + 1/N)` of the atoms, uniformly in `N`.

Let `f = Σ_{n ≤ N} x_n g(· − log n)` with a real `C²` bump `g` supported in `[0, w]`. Then
`M(f) = 2θ′(0)‖f‖² + levyEnergy f − ‖g‖² P_N(x)`, and the two sides are bounded row by row:

* the Lévy energy (`TheArchimedeanCrossKernel`): `log(1/w) − 8e^{5/2} w m (1 + log(N + 1))` per unit
  mass at the atom `m` — the self-energy with constant one minus the cross-kernel row;
* the prime form (`TheTiltedPrimeRows`): `log N + 2(log 4 + 4) − (m/4N) log m` — the covariant
  counterterm minus the down-tower saving of the tilted weight `1 + n/N`.

At `w ≤ c₁/N`, `c₁ = 1/(32 e^{5/2})` (`spacingRatio`), the cross-kernel row is at most
`(m/4N)(1 + log(N + 1))`, and the tilted saving `(m/4N) log m` pays it up to `3/4`
(`crossRow_le_saving`): **the down tower of the prime form pays the archimedean cross kernel scale
by scale**. What remains is the matched difference of the two divergences.

* **Quantitative law** (`markovEnergy_atomicTest_ge_spacing`): for `0 < w ≤ c₁ δ_N`,
  `M(f) ≥ (2θ′(0) + log(1/(wN)) − C) ‖f‖²`, `C = 2(log 4 + 4) + 1` (`spacingConstant`).
* **The stability law at the spacing scale** (`markovEnergy_atomicTest_nonneg_spacing`): `M(f) ≥ 0`
  for every atomic test of width `w ≤ c₀ δ_N`, `c₀ = c₁ e^{−(C + 2|θ′(0)|)}` (`spacingWidthRatio`),
  for every `N ≥ 1`.
* **Weil's form at the spacing scale** (`re_W_add_sinh_sq_nonneg_spacing`,
  `re_W_atomicTest_nonneg_spacing_of_abs_le`, `re_W_atomicTest_nonneg_spacing_of_nonneg`):
  `Re W(f) + 2S(f)² ≥ 0` — a rank-one correction, the pole — and `Re W(f) ≥ 0` on the cone
  `|S| ≤ |C|`, in particular for nonnegative weights and bumps.
* **Gauge blindness** (`twinMarkov_atomicTest_ge_spacing`, `twinMarkov_atomicTest_nonneg_spacing`):
  every completely multiplicative sign twin satisfies the same law with the same constants.

The width `c₀ δ_N` is a fixed fraction of the spacing: the tests see the zeros up to height `≍ N`.
The constants are not optimized. The matching uses constant one on both sides — the self-energy
`log(1/w)` and the covariant counterterm `log N` — so the finite part is `log(1/(wN)) + O(1)`, the
Nyquist margin.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics Zeta23

variable {g : ℝ → ℝ} {w : ℝ}

/-! ### The constants -/

/-- The cross-kernel ratio `c₁ = 1/(32 e^{5/2})`: below `c₁ δ_N` the tilted prime rows pay the
archimedean cross kernel. -/
def spacingRatio : ℝ := 1 / (32 * Real.exp (5 / 2))

/-- The constant `C = 2(log 4 + 4) + 1` of the spacing-scale law: Mertens and Chebyshev, plus the
unpaid part of the cross kernel. -/
def spacingConstant : ℝ := 2 * (Real.log 4 + 4) + 1

/-- The stability ratio `c₀ = c₁ e^{−(C + 2|θ′(0)|)}`. -/
def spacingWidthRatio : ℝ :=
  spacingRatio * Real.exp (-(spacingConstant + 2 * |gammaHardyPhaseRate 0|))

theorem spacingRatio_pos : 0 < spacingRatio := by unfold spacingRatio; positivity

theorem spacingRatio_lt_half : spacingRatio < 1 / 2 := by
  unfold spacingRatio
  have : 1 ≤ Real.exp (5 / 2) := Real.one_le_exp (by norm_num)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem spacingWidthRatio_pos : 0 < spacingWidthRatio :=
  mul_pos spacingRatio_pos (Real.exp_pos _)

theorem spacingWidthRatio_le : spacingWidthRatio ≤ spacingRatio := by
  unfold spacingWidthRatio
  have h : Real.exp (-(spacingConstant + 2 * |gammaHardyPhaseRate 0|)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    unfold spacingConstant
    have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  nlinarith [spacingRatio_pos]

/-- `δ_N ≤ 1/N`. -/
theorem atomSpacing_le_inv {N : ℕ} (hN : 1 ≤ N) : atomSpacing N ≤ 1 / N := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / N by positivity)
  unfold atomSpacing
  linarith

/-! ### The cross kernel is paid by the tilt -/

/-- **The tilt pays the cross kernel**: at `w ≤ c₁/N`,
`8e^{5/2} w m (1 + log(N+1)) ≤ (m/4N) log m + 3/4` for `1 ≤ m ≤ N`. -/
theorem crossRow_le_saving {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hw : w ≤ spacingRatio / N) :
    8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1)) ≤
      (m : ℝ) / (4 * N) * Real.log m + 3 / 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hlogN1 : 0 ≤ 1 + Real.log (N + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N + 1 by linarith)
    linarith
  -- `8e^{5/2} w ≤ 1/(4N)`
  have hcoef : 8 * Real.exp (5 / 2) * w ≤ 1 / (4 * N) := by
    have he : 0 < Real.exp (5 / 2) := Real.exp_pos _
    have : 8 * Real.exp (5 / 2) * (spacingRatio / N) = 1 / (4 * N) := by
      unfold spacingRatio; field_simp; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hw (by positivity)
  -- `(m/N) log((N+1)/m) ≤ (N + 1 − m)/N ≤ 2`
  have hlogq : Real.log ((N + 1) / m) ≤ (N + 1) / m - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log (N + 1) = Real.log ((N + 1) / m) + Real.log m := by
    rw [Real.log_div (by positivity) hm0.ne']; ring
  have hkey : (m : ℝ) / N * Real.log ((N + 1) / m) ≤ 2 := by
    have h1 : (m : ℝ) / N * Real.log ((N + 1) / m) ≤ (m : ℝ) / N * ((N + 1) / m - 1) :=
      mul_le_mul_of_nonneg_left hlogq (by positivity)
    have h2 : (m : ℝ) / N * ((N + 1) / m - 1) = (N + 1 - m) / N := by field_simp
    have h3 : ((N : ℝ) + 1 - m) / N ≤ 2 := by
      rw [div_le_iff₀ hN0]; nlinarith
    linarith
  have ht : (m : ℝ) / N ≤ 1 := by rw [div_le_one hN0]; exact hmN'
  calc 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))
      = (8 * Real.exp (5 / 2) * w) * (m * (1 + Real.log (N + 1))) := by ring
    _ ≤ 1 / (4 * N) * (m * (1 + Real.log (N + 1))) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (m : ℝ) / (4 * N) * Real.log m +
          ((m : ℝ) / N / 4 + (m : ℝ) / N * Real.log ((N + 1) / m) / 4) := by
        rw [hsplit]; field_simp; ring
    _ ≤ (m : ℝ) / (4 * N) * Real.log m + 3 / 4 := by linarith

/-! ### The quantitative law -/

/-- **The row-by-row estimate**: for `0 < w ≤ c₁ δ_N` and any weights `y` with `y_m² = x_m²`,
`2θ′(0)‖f_x‖² + levyEnergy f_x − ‖g‖² P_N(y) ≥ (2θ′(0) + log(1/w) − log N − C) ‖f_x‖²`. -/
theorem levy_sub_atomicWeilForm_ge (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingRatio * atomSpacing N) (x y : ℕ → ℝ)
    (hxy : ∀ m ∈ Icc 1 N, y m ^ 2 = x m ^ 2) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant) *
        ∫ u, atomicTest N x g u ^ 2 ≤
      2 * gammaHardyPhaseRate 0 * (∫ u, atomicTest N x g u ^ 2) +
        levyEnergy (atomicTest N x g) - (∫ u, g u ^ 2) * atomicWeilForm N y := by
  have hδ := atomSpacing_pos hN
  have hw2 : w ≤ atomSpacing N / 2 := by
    nlinarith [spacingRatio_lt_half, spacingRatio_pos]
  have hwN : w ≤ spacingRatio / N := by
    calc w ≤ spacingRatio * atomSpacing N := hw
      _ ≤ spacingRatio * (1 / N) :=
          mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN) spacingRatio_pos.le
      _ = spacingRatio / N := by ring
  rw [integral_atomicTest_sq hg hgc hgsupp (by linarith) x]
  have hlevy := levyEnergy_atomicTest_ge hg hgc hgsupp hN hw0 hw2 x
  have hprime : atomicWeilForm N y ≤ ∑ m ∈ Icc 1 N, x m ^ 2 *
      (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) :=
    (atomicWeilForm_le_tilted N y).trans (le_of_eq (sum_congr rfl fun m hm => by rw [hxy m hm]))
  set G2 := ∫ u, g u ^ 2
  have hG2 : 0 ≤ G2 := integral_nonneg fun u => sq_nonneg _
  -- row by row
  have hrow : ∀ m ∈ Icc 1 N,
      (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant) ≤
        2 * gammaHardyPhaseRate 0 +
          (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
          (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
    intro m hm
    have := crossRow_le_saving (mem_Icc.mp hm).1 (mem_Icc.mp hm).2 hwN
    unfold spacingConstant
    linarith
  have hsum : (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant) *
      ((∑ m ∈ Icc 1 N, x m ^ 2) * G2) ≤
      G2 * ∑ m ∈ Icc 1 N, x m ^ 2 * (2 * gammaHardyPhaseRate 0 +
          (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
          (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m)) := by
    rw [mul_comm _ G2, ← mul_assoc, mul_comm _ G2, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hG2
    rw [mul_sum]
    exact sum_le_sum fun m hm => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)
  have hexpand : G2 * ∑ m ∈ Icc 1 N, x m ^ 2 * (2 * gammaHardyPhaseRate 0 +
        (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
        (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m)) =
      2 * gammaHardyPhaseRate 0 * ((∑ m ∈ Icc 1 N, x m ^ 2) * G2) +
        G2 * ∑ m ∈ Icc 1 N, x m ^ 2 *
          (Real.log (1 / w) - 8 * Real.exp (5 / 2) * w * m * (1 + Real.log (N + 1))) -
        G2 * ∑ m ∈ Icc 1 N, x m ^ 2 *
          (Real.log N + 2 * (Real.log 4 + 4) - (m : ℝ) / (4 * N) * Real.log m) := by
    simp only [mul_sum, sum_mul, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun m _ => by ring
  have hP := mul_le_mul_of_nonneg_left hprime hG2
  linarith

/-- **The stability law at the spacing scale, quantitative form**: for `0 < w ≤ c₁ δ_N`,
`M(f) ≥ (2θ′(0) + log(1/w) − log N − C) ‖f‖²`. -/
theorem markovEnergy_atomicTest_ge_spacing (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingRatio * atomSpacing N) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant) *
        ∫ u, atomicTest N x g u ^ 2 ≤
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hw' : w < atomSpacing N := by
    nlinarith [spacingRatio_lt_half, spacingRatio_pos, atomSpacing_pos hN]
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hg hgc hgsupp hw' x]
  exact levy_sub_atomicWeilForm_ge hg hgc hgsupp hN hw0 hw x x fun _ _ => rfl

/-! ### The stability law -/

/-- At `w ≤ c₀ δ_N` the coefficient of the quantitative law is nonnegative. -/
theorem spacingGain_nonneg {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingWidthRatio * atomSpacing N) :
    0 ≤ 2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant := by
  have hδ := atomSpacing_pos hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set X := spacingConstant + 2 * |gammaHardyPhaseRate 0|
  -- `1/w ≥ N e^{X}/c₁ ≥ N e^{X}`
  have hc1 : spacingRatio ≤ 1 := by linarith [spacingRatio_lt_half]
  have hwN : w ≤ Real.exp (-X) / N := by
    calc w ≤ spacingWidthRatio * atomSpacing N := hw
      _ ≤ spacingWidthRatio * (1 / N) :=
          mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN) spacingWidthRatio_pos.le
      _ ≤ Real.exp (-X) * (1 / N) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          unfold spacingWidthRatio
          nlinarith [Real.exp_pos (-X), spacingRatio_pos]
      _ = Real.exp (-X) / N := by ring
  have hlog : Real.log N + X ≤ Real.log (1 / w) := by
    have h1 : N * Real.exp X ≤ 1 / w := by
      rw [le_div_iff₀ hw0]
      have := mul_le_mul_of_nonneg_left hwN (by positivity : (0 : ℝ) ≤ N * Real.exp X)
      rw [show (N : ℝ) * Real.exp X * (Real.exp (-X) / N) = 1 by
        rw [Real.exp_neg]; field_simp] at this
      linarith
    calc Real.log N + X = Real.log (N * Real.exp X) := by
          rw [Real.log_mul hN0.ne' (Real.exp_pos X).ne', Real.log_exp]
      _ ≤ Real.log (1 / w) := Real.log_le_log (by positivity) h1
  have := neg_abs_le (gammaHardyPhaseRate 0)
  simp only [X] at hlog
  linarith

/-- **The stability law at the spacing scale**: every atomic test of width at most `c₀ δ_N` at the
points `log n`, `n ≤ N`, has nonnegative Markov form, for every `N ≥ 1`. -/
theorem markovEnergy_atomicTest_nonneg_spacing (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingWidthRatio * atomSpacing N) (x : ℕ → ℝ) :
    0 ≤ markovEnergy (fun u => (atomicTest N x g u : ℂ)) := by
  have hw' : w ≤ spacingRatio * atomSpacing N :=
    hw.trans (mul_le_mul_of_nonneg_right spacingWidthRatio_le (atomSpacing_pos hN).le)
  have h := markovEnergy_atomicTest_ge_spacing hg hgc hgsupp hN hw0 hw' x
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg (spacingGain_nonneg hN hw0 hw) hint) h

/-! ### Weil's form at the spacing scale -/

/-- **Weil's form at the spacing scale, up to the pole**: `Re W(f) + 2S(f)² ≥ 0` on every atomic
test of width at most `c₀ δ_N`. The correction has rank one. -/
theorem re_W_add_sinh_sq_nonneg_spacing (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingWidthRatio * atomSpacing N) (x : ℕ → ℝ) :
    0 ≤ (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ))
        fun u => (atomicTest N x g u : ℂ)).re + 2 * sinhHalfMoment (atomicTest N x g) ^ 2 := by
  rw [re_W_atomicTest_eq hg hgsupp N x]
  have hM := markovEnergy_atomicTest_nonneg_spacing hg hgc hgsupp hN hw0 hw x
  nlinarith [sq_nonneg (coshHalfMoment (atomicTest N x g))]

/-- **Weil positivity at the spacing scale on the cone `|S| ≤ |C|`**. -/
theorem re_W_atomicTest_nonneg_spacing_of_abs_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingWidthRatio * atomSpacing N) (x : ℕ → ℝ)
    (hSC : |sinhHalfMoment (atomicTest N x g)| ≤ |coshHalfMoment (atomicTest N x g)|) :
    0 ≤ (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ))
        fun u => (atomicTest N x g u : ℂ)).re := by
  rw [re_W_atomicTest_eq hg hgsupp N x]
  have hM := markovEnergy_atomicTest_nonneg_spacing hg hgc hgsupp hN hw0 hw x
  have hsq : sinhHalfMoment (atomicTest N x g) ^ 2 ≤ coshHalfMoment (atomicTest N x g) ^ 2 := by
    rw [← sq_abs, ← sq_abs (coshHalfMoment _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hSC 2
  linarith

/-- **Weil positivity at the spacing scale on nonnegative atomic tests**. -/
theorem re_W_atomicTest_nonneg_spacing_of_nonneg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hN : 1 ≤ N)
    (hw0 : 0 < w) (hw : w ≤ spacingWidthRatio * atomSpacing N) {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) :
    0 ≤ (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ))
        fun u => (atomicTest N x g u : ℂ)).re := by
  set f := atomicTest N x g
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hf0 : ∀ u, 0 ≤ f u := fun u => sum_nonneg fun n _ => mul_nonneg (hx n) (hg0 _)
  have hneg : ∀ u, u < 0 → f u = 0 := fun u hu => sum_eq_zero fun n hn => by
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [hgsupp _ fun h => by linarith [h.1], mul_zero]
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → Integrable fun u => f u * φ u := fun φ hφ =>
    (hf.continuous.mul hφ).integrable_of_hasCompactSupport (hfc.mul_right)
  have hS0 : 0 ≤ sinhHalfMoment f := integral_nonneg fun u => by
    show 0 ≤ f u * Real.sinh (u / 2)
    rcases lt_or_ge u 0 with hu | hu
    · rw [hneg u hu, zero_mul]
    · exact mul_nonneg (hf0 u) (Real.sinh_nonneg_iff.mpr (by linarith))
  have hSC : sinhHalfMoment f ≤ coshHalfMoment f :=
    integral_mono (hint _ (Real.continuous_sinh.comp (continuous_id.div_const 2)))
      (hint _ (Real.continuous_cosh.comp (continuous_id.div_const 2))) fun u =>
        mul_le_mul_of_nonneg_left (Real.sinh_lt_cosh _).le (hf0 u)
  refine re_W_atomicTest_nonneg_spacing_of_abs_le hg hgc hgsupp hN hw0 hw x ?_
  rw [abs_of_nonneg hS0, abs_of_nonneg (hS0.trans hSC)]
  exact hSC

/-! ### Gauge blindness -/

variable {ω : ArithmeticFunction ℝ}

/-- **The spacing-scale law is gauge blind, quantitative form**: every completely multiplicative
sign twin satisfies `M_ω(f) ≥ (2θ′(0) + log(1/w) − log N − C) ‖f‖²` at `w ≤ c₁ δ_N`. -/
theorem twinMarkov_atomicTest_ge_spacing (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingRatio * atomSpacing N) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant) *
        ∫ u, atomicTest N x g u ^ 2 ≤
      archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  have hw' : w < atomSpacing N := by
    nlinarith [spacingRatio_lt_half, spacingRatio_pos, atomSpacing_pos hN]
  -- the twin's prime sum is `ζ`'s on the gauged weights `ωx`, which have the same squares
  have hsq : ∀ m ∈ Icc 1 N, (ω m * x m) ^ 2 = x m ^ 2 := fun m hm => by
    rcases hsign m (mem_Icc.mp hm).1 with h | h <;> rw [h] <;> ring
  rw [archForm_eq_levyEnergy (contDiff_atomicTest hg N x) (hasCompactSupport_atomicTest hgsupp N x),
    (twistedPrimeSum_atomicTest hω hsign hg hgc hgsupp hw' x).1,
    primeSum_atomicTest hg hgc hgsupp hw' _]
  exact levy_sub_atomicWeilForm_ge hg hgc hgsupp hN hw0 hw x _ hsq

/-- **The stability law at the spacing scale is gauge blind**: every completely multiplicative sign
twin has nonnegative Markov form on every atomic test of width at most `c₀ δ_N`. -/
theorem twinMarkov_atomicTest_nonneg_spacing (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ spacingWidthRatio * atomSpacing N) (x : ℕ → ℝ) :
    0 ≤ archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  have hw' : w ≤ spacingRatio * atomSpacing N :=
    hw.trans (mul_le_mul_of_nonneg_right spacingWidthRatio_le (atomSpacing_pos hN).le)
  have h := twinMarkov_atomicTest_ge_spacing hω hsign hg hgc hgsupp hN hw0 hw' x
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg (spacingGain_nonneg hN hw0 hw) hint) h

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
