import GaloisForLFunctions.RHTower.CHMDThresholdWeylSequence
import GaloisForLFunctions.RHTower.CHMDPrimeWindowTail
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# Negative Doob energy localizes in a compact window

The complete arithmetic Doob form `E(p) = ‖edge‖² − ‖source‖²_μ` on the theta–cosh mass space
is bounded below by `−ε ‖p‖²_μ − C_ε · (mass of p inside |x| ≤ R_ε)` for every `ε > 0`.

Mechanism: by the harmonic identity the prime jumps from `y` carry the total rate
`cosh(y/2) + O(1)`; the jumps landing outside a window of radius `R` carry only
`O(r^R) cosh(y/2)` (shell bound), so the jumps landing inside the window carry almost the full
polar rate `cosh(y/2)`, which is exactly the mass density divided by `Θ`. The elementary
inequality `(a−b)² ≥ β a² + α b² − δ⁻¹(α a² + β b²) − δ(a² + b²)` for window indicators `α, β`
then shows that the prime jump energy dominates `(1 − O(r^R) − δ)‖p‖²_μ` up to a multiple of the
window mass. The archimedean jump energy is dropped (it is nonnegative). Compact `C²` tests are
dense in the graph norm, and both sides are graph-continuous.

Consequences: every far-field vector (vanishing on the window) has energy `≥ −ε ‖p‖²`; every
unit family on which the arithmetic resolvent is asymptotically a scalar `μ > 1/2` keeps a definite
amount of mass inside a fixed window (no escape to the cusp above the threshold). This is sharp:
the normalized primitive cusp escape is a unit family with resolvent defect tending to zero at the
level `1/2` and with no mass in any fixed window for all large translations.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump ThetaSourceWard

/-! ## Two-sided bound of the prime shift sum -/

/-- The symmetric prime shift sum differs from the polar rate `cosh(y/2)` by a uniformly bounded
archimedean correction. -/
theorem exists_primeKernelSum_two_sided :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, |primeKernelSum y - Real.cosh (y / 2)| ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound
  have hsym : ∀ y, |∫ u in Ioi (0 : ℝ), symArchTerm y u| ≤
      2 * ∫ u in Ioi (0 : ℝ), gammaSourceBound u := by
    intro y
    have hn : ‖∫ u in Ioi (0 : ℝ), symArchTerm y u‖ ≤ ∫ u in Ioi (0 : ℝ), ‖symArchTerm y u‖ :=
      norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ))) _
    rw [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_symArchTerm y).norm
      (gammaSourceBound_integrable.const_mul 2) measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have he : symArchTerm y u = gammaSourceTerm y u + gammaSourceTerm (-y) u := by
      simp only [gammaSourceTerm_eq, symArchTerm, WeilExcess.riemannKernelReal_neg]
      rw [show -y + u = -(y - u) by ring, WeilExcess.riemannKernelReal_neg]
      ring
    rw [Real.norm_eq_abs, he]
    calc |gammaSourceTerm y u + gammaSourceTerm (-y) u|
        ≤ |gammaSourceTerm y u| + |gammaSourceTerm (-y) u| := abs_add_le _ _
      _ ≤ gammaSourceBound u + gammaSourceBound u :=
          add_le_add (abs_gammaSourceTerm_le_bound y hu') (abs_gammaSourceTerm_le_bound (-y) hu')
      _ = 2 * gammaSourceBound u := by ring
  refine ⟨2 * |archConstantReal| * C + 2 * ∫ u in Ioi (0 : ℝ), gammaSourceBound u, ?_, fun y => ?_⟩
  · have h0 : 0 ≤ 2 * ∫ u in Ioi (0 : ℝ), gammaSourceBound u := (abs_nonneg _).trans (hsym 0)
    have h1 : 0 ≤ 2 * |archConstantReal| * C := by positivity
    linarith
  · rw [theta_harmonic_identity]
    have hθ := riemannKernelReal_pos y
    have h1 : |2 * archConstantReal * riemannKernelReal y| ≤ 2 * |archConstantReal| * C := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hθ]
      exact mul_le_mul_of_nonneg_left (hC y) (by positivity)
    have he : Real.cosh (y / 2) - 2 * archConstantReal * riemannKernelReal y +
        (∫ u in Ioi (0 : ℝ), symArchTerm y u) - Real.cosh (y / 2) =
        (∫ u in Ioi (0 : ℝ), symArchTerm y u) + -(2 * archConstantReal * riemannKernelReal y) := by
      ring
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith [hsym y]

/-! ## The window inequality for a single jump -/

/-- For window indicators `α, β ∈ {0,1}` and `δ > 0`:
`(a − b)² ≥ β a² + α b² − δ⁻¹(α a² + β b²) − δ(a² + b²)`. -/
theorem window_jump_lower {a b α β δ : ℝ} (hδ : 0 < δ) (hα : α = 0 ∨ α = 1) (hβ : β = 0 ∨ β = 1) :
    β * a ^ 2 + α * b ^ 2 - δ⁻¹ * (α * a ^ 2 + β * b ^ 2) - δ * (a ^ 2 + b ^ 2) ≤ (a - b) ^ 2 := by
  have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have k1 : 2 * a * b ≤ δ⁻¹ * a ^ 2 + δ * b ^ 2 := by
    have : δ⁻¹ * a ^ 2 + δ * b ^ 2 - 2 * a * b = δ⁻¹ * (a - δ * b) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hδi (sq_nonneg (a - δ * b))]
  have k2 : 2 * a * b ≤ δ * a ^ 2 + δ⁻¹ * b ^ 2 := by
    have : δ * a ^ 2 + δ⁻¹ * b ^ 2 - 2 * a * b = δ⁻¹ * (b - δ * a) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hδi (sq_nonneg (b - δ * a))]
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b), mul_nonneg hδ.le (sq_nonneg a),
      mul_nonneg hδ.le (sq_nonneg b), mul_nonneg hδi (sq_nonneg a), mul_nonneg hδi (sq_nonneg b)]

/-! ## Termwise integration of symmetric prime shift series -/

/-- The symmetric shift pair with bounded coefficients. -/
def shiftPair (c₁ c₂ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  vonMangoldtAtom n * (riemannKernelReal (x + Real.log n) * c₁ (x + Real.log n) +
    riemannKernelReal (x - Real.log n) * c₂ (x - Real.log n))

theorem measurable_shiftPair {c₁ c₂ : ℝ → ℝ} (hc₁ : Measurable c₁) (hc₂ : Measurable c₂) (n : ℕ) :
    Measurable (shiftPair c₁ c₂ n) := by
  have h1 : Measurable fun x : ℝ => x + Real.log n := measurable_id.add_const _
  have h2 : Measurable fun x : ℝ => x - Real.log n := measurable_id.sub_const _
  exact measurable_const.mul
    (((continuous_riemannKernelReal.measurable.comp h1).mul (hc₁.comp h1)).add
      ((continuous_riemannKernelReal.measurable.comp h2).mul (hc₂.comp h2)))

theorem abs_shiftPair_le {c₁ c₂ : ℝ → ℝ} (hb₁ : ∀ x, |c₁ x| ≤ 1) (hb₂ : ∀ x, |c₂ x| ≤ 1) (n : ℕ)
    (x : ℝ) : |shiftPair c₁ c₂ n x| ≤
      vonMangoldtAtom n * (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)) := by
  unfold shiftPair
  rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (vonMangoldtAtom_nonneg n)
  rw [abs_mul, abs_mul, abs_of_pos (riemannKernelReal_pos _), abs_of_pos (riemannKernelReal_pos _)]
  exact add_le_add (mul_le_of_le_one_right (riemannKernelReal_pos _).le (hb₁ _))
    (mul_le_of_le_one_right (riemannKernelReal_pos _).le (hb₂ _))

theorem abs_shiftPair_le_const {c₁ c₂ : ℝ → ℝ} (hb₁ : ∀ x, |c₁ x| ≤ 1) (hb₂ : ∀ x, |c₂ x| ≤ 1)
    {Cθ : ℝ} (hCθ : ∀ x, riemannKernelReal x ≤ Cθ) (n : ℕ) (x : ℝ) :
    |shiftPair c₁ c₂ n x| ≤ vonMangoldtAtom n * (2 * Cθ) := by
  refine (abs_shiftPair_le hb₁ hb₂ n x).trans (mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n))
  linarith [hCθ (x + Real.log n), hCθ (x - Real.log n)]

theorem abs_nearInd_le_one (R x : ℝ) : |nearInd R x| ≤ 1 := by
  rw [abs_of_nonneg (nearInd_nonneg R x)]
  exact nearInd_le_one R x

/-- An integrable function times a bounded measurable function is integrable. -/
theorem integrable_mul_bounded {m h : ℝ → ℝ} (hm : Integrable m) (hh : Measurable h) {c : ℝ}
    (hb : ∀ x, |h x| ≤ c) : Integrable fun x => m x * h x :=
  (hm.bdd_mul hh.aestronglyMeasurable (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hb x)).congr (Eventually.of_forall fun x => mul_comm _ _)

/-- A symmetric prime shift series with bounded measurable coefficients integrates termwise
against an integrable weight of bounded support. -/
theorem tsum_integral_shiftPair {g : ℝ → ℝ} (hg : Integrable g) {R₀ : ℝ}
    (hsupp : ∀ x, g x ≠ 0 → |x| ≤ R₀) {c₁ c₂ : ℝ → ℝ} (hc₁ : Measurable c₁) (hc₂ : Measurable c₂)
    (hb₁ : ∀ x, |c₁ x| ≤ 1) (hb₂ : ∀ x, |c₂ x| ≤ 1) :
    (Summable fun n : ℕ => ∫ x, g x * shiftPair c₁ c₂ n x) ∧
    ∑' n : ℕ, ∫ x, g x * shiftPair c₁ c₂ n x = ∫ x, g x * ∑' n : ℕ, shiftPair c₁ c₂ n x := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_theta_bound
  have hint : ∀ n, Integrable fun x => g x * shiftPair c₁ c₂ n x := fun n =>
    integrable_mul_bounded hg (measurable_shiftPair hc₁ hc₂ n) (abs_shiftPair_le_const hb₁ hb₂ hCθ n)
  have hgabs : Integrable fun x => |g x| := hg.abs
  set K : ℝ := (∫ x, |g x|) * (2 * (C * Real.exp (4 * R₀))) with hK
  have hnorm : ∀ n : ℕ, (∫ x, ‖g x * shiftPair c₁ c₂ n x‖) ≤ K * (vonMangoldtAtom n / (n : ℝ) ^ 2) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [shiftPair, vonMangoldtAtom]
    have hpt' : ∀ x, ‖g x * shiftPair c₁ c₂ n x‖ ≤
        |g x| * (2 * (C * Real.exp (4 * R₀)) * (vonMangoldtAtom n / (n : ℝ) ^ 2)) := by
      intro x
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hx : g x = 0
      · simp [hx]
      · have hxR := hsupp x hx
        have hsh := riemannKernelReal_shift_le hC hC0 hxR hn
        have ha : 0 ≤ vonMangoldtAtom n := vonMangoldtAtom_nonneg n
        refine mul_le_mul_of_nonneg_left ((abs_shiftPair_le hb₁ hb₂ n x).trans ?_) (abs_nonneg _)
        calc vonMangoldtAtom n * (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))
            ≤ vonMangoldtAtom n * (2 * (C * Real.exp (4 * R₀)) * (1 / (n : ℝ) ^ 2)) :=
              mul_le_mul_of_nonneg_left hsh ha
          _ = 2 * (C * Real.exp (4 * R₀)) * (vonMangoldtAtom n / (n : ℝ) ^ 2) := by ring
    calc (∫ x, ‖g x * shiftPair c₁ c₂ n x‖)
        ≤ ∫ x, |g x| * (2 * (C * Real.exp (4 * R₀)) * (vonMangoldtAtom n / (n : ℝ) ^ 2)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
            (hgabs.mul_const _) (Eventually.of_forall hpt')
      _ = K * (vonMangoldtAtom n / (n : ℝ) ^ 2) := by
          rw [integral_mul_const, hK]
          ring
  have hsum : Summable fun n : ℕ => ∫ x, ‖g x * shiftPair c₁ c₂ n x‖ :=
    (summable_atom_div_sq.mul_left K).of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _) hnorm
  refine ⟨?_, ?_⟩
  · exact (hsum.of_norm_bounded fun n => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_integral_abs)
  · rw [integral_tsum_of_summable_integral_norm hint hsum]
    congr 1
    funext x
    exact tsum_mul_left

theorem primeCross_eq_tsum_shiftPair (R x : ℝ) :
    primeCross R x = ∑' n : ℕ, shiftPair (nearInd R) (nearInd R) n x := rfl

theorem primeKernelSum_eq_tsum_shiftPair (x : ℝ) :
    primeKernelSum x = ∑' n : ℕ, shiftPair (fun _ => 1) (fun _ => 1) n x := by
  unfold primeKernelSum shiftPair
  simp only [mul_one]

/-! ## The prime jump energy dominates the window-cross mass -/

theorem integrable_phiDoobPrimeJump' {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    (n : ℕ) : Integrable (phiDoobPrimeJump v n) :=
  ((integrable_phiDoobPrimeDiagonal hv hvc n).sub (integrable_phiDoobPrimeCross hv hvc n)).congr
    (Eventually.of_forall fun x => (phiDoobPrimeJump_eq_diagonal_sub_cross v n x).symm)

/-- The window coefficient `β − δ⁻¹α − δ` is bounded by `1 + δ⁻¹ + δ`. -/
theorem abs_window_coeff_le {R δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |nearInd R y - δ⁻¹ * nearInd R x - δ| ≤ 1 + δ⁻¹ + δ := by
  have h1 := nearInd_nonneg R x
  have h2 := nearInd_le_one R x
  have h3 := nearInd_nonneg R y
  have h4 := nearInd_le_one R y
  have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hδi h1, mul_le_mul_of_nonneg_left h2 hδi]

/-- The theta-weighted square of a compact test. -/
def thetaSq (v : ℝ → ℝ) (x : ℝ) : ℝ := v x ^ 2 * riemannKernelReal x

theorem thetaSq_nonneg (v : ℝ → ℝ) (x : ℝ) : 0 ≤ thetaSq v x :=
  mul_nonneg (sq_nonneg _) (riemannKernelReal_pos x).le

theorem continuous_thetaSq {v : ℝ → ℝ} (hv : Continuous v) : Continuous (thetaSq v) :=
  (hv.pow 2).mul continuous_riemannKernelReal

theorem hasCompactSupport_thetaSq {v : ℝ → ℝ} (hvc : HasCompactSupport v) :
    HasCompactSupport (thetaSq v) := by
  have h := hvc.mul_right (f' := fun x => v x * riemannKernelReal x)
  have he : thetaSq v = v * fun x => v x * riemannKernelReal x := by
    funext x
    simp only [thetaSq, Pi.mul_apply]
    ring
  rw [he]
  exact h

theorem integrable_thetaSq {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (thetaSq v) :=
  (continuous_thetaSq hv).integrable_of_hasCompactSupport (hasCompactSupport_thetaSq hvc)

theorem integrable_thetaSq_mul_cosh {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable fun x => thetaSq v x * Real.cosh (x / 2) :=
  ((continuous_thetaSq hv).mul (Real.continuous_cosh.comp (continuous_id.div_const 2)))
    |>.integrable_of_hasCompactSupport (hasCompactSupport_thetaSq hvc).mul_right

/-- `Θ v²` times a measurable function of at most polar growth is integrable. -/
theorem integrable_thetaSq_mul {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    {h : ℝ → ℝ} (hh : Measurable h) {a b : ℝ} (hb : ∀ x, |h x| ≤ a * Real.cosh (x / 2) + b) :
    Integrable fun x => thetaSq v x * h x := by
  have hg : Integrable fun x => thetaSq v x * (a * Real.cosh (x / 2) + b) :=
    ((continuous_thetaSq hv).mul ((continuous_const.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).add continuous_const))
      |>.integrable_of_hasCompactSupport (hasCompactSupport_thetaSq hvc).mul_right
  refine hg.mono' ((continuous_thetaSq hv).measurable.mul hh).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (thetaSq_nonneg v x)]
  exact mul_le_mul_of_nonneg_left (hb x) (thetaSq_nonneg v x)

theorem thetaSq_support {v : ℝ → ℝ} {R₀ : ℝ} (hsupp : ∀ x, v x ≠ 0 → -R₀ ≤ x ∧ x ≤ R₀) (x : ℝ)
    (hx : thetaSq v x ≠ 0) : |x| ≤ R₀ := by
  refine abs_le.mpr (hsupp x fun h => hx ?_)
  simp [thetaSq, h]

/-- Per prime: the jump energy of `v` along `log n` dominates the window-cross term minus the
window and diffuse penalties. -/
theorem integral_phiDoobPrimeJump_window_lower {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (∫ x, thetaSq v x * shiftPair (nearInd R) (nearInd R) n x) -
      (∫ x, (thetaSq v x * (δ⁻¹ * nearInd R x + δ)) * shiftPair (fun _ => 1) (fun _ => 1) n x) ≤
      ∫ x, phiDoobPrimeJump v n x := by
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_theta_bound
  have hvC := hv.continuous
  have hm : Integrable (thetaSq v) := integrable_thetaSq hvC hvc
  have ha : 0 ≤ vonMangoldtAtom n := vonMangoldtAtom_nonneg n
  have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hsh : Measurable fun x : ℝ => x + Real.log n := measurable_id.add_const _
  have hsh' : Measurable fun x : ℝ => x - Real.log n := measurable_id.sub_const _
  -- the two halves of the pointwise lower bound
  set A : ℝ → ℝ := fun x => thetaSq v x * (vonMangoldtAtom n * riemannKernelReal (x + Real.log n) *
    (nearInd R (x + Real.log n) - δ⁻¹ * nearInd R x - δ)) with hA_def
  set B : ℝ → ℝ := fun x => thetaSq v (x + Real.log n) * (vonMangoldtAtom n * riemannKernelReal x *
    (nearInd R x - δ⁻¹ * nearInd R (x + Real.log n) - δ)) with hB_def
  set B' : ℝ → ℝ := fun x => thetaSq v x * (vonMangoldtAtom n * riemannKernelReal (x - Real.log n) *
    (nearInd R (x - Real.log n) - δ⁻¹ * nearInd R x - δ)) with hB'_def
  have hcoef : ∀ x y, |vonMangoldtAtom n * riemannKernelReal y *
      (nearInd R y - δ⁻¹ * nearInd R x - δ)| ≤ vonMangoldtAtom n * Cθ * (1 + δ⁻¹ + δ) := by
    intro x y
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos (riemannKernelReal_pos _)]
    have h1 := hCθ y
    have h2 := abs_window_coeff_le (R := R) hδ x y
    have h3 := (riemannKernelReal_pos y).le
    have h4 := abs_nonneg (nearInd R y - δ⁻¹ * nearInd R x - δ)
    calc vonMangoldtAtom n * riemannKernelReal y * |nearInd R y - δ⁻¹ * nearInd R x - δ|
        ≤ vonMangoldtAtom n * Cθ * |nearInd R y - δ⁻¹ * nearInd R x - δ| := by gcongr
      _ ≤ vonMangoldtAtom n * Cθ * (1 + δ⁻¹ + δ) := by gcongr
  have hA : Integrable A :=
    integrable_mul_bounded hm ((measurable_const.mul
      (continuous_riemannKernelReal.measurable.comp hsh)).mul
      ((((measurable_nearInd R).comp hsh).sub (measurable_const.mul (measurable_nearInd R))).sub
        measurable_const)) (fun x => hcoef x (x + Real.log n))
  have hB : Integrable B :=
    integrable_mul_bounded (hm.comp_add_right (Real.log n)) ((measurable_const.mul
      continuous_riemannKernelReal.measurable).mul
      (((measurable_nearInd R).sub (measurable_const.mul ((measurable_nearInd R).comp hsh))).sub
        measurable_const)) (fun x => hcoef (x + Real.log n) x)
  have hB' : Integrable B' :=
    integrable_mul_bounded hm ((measurable_const.mul
      (continuous_riemannKernelReal.measurable.comp hsh')).mul
      ((((measurable_nearInd R).comp hsh').sub (measurable_const.mul (measurable_nearInd R))).sub
        measurable_const)) (fun x => hcoef x (x - Real.log n))
  have hT₁ : Integrable fun x => thetaSq v x * shiftPair (nearInd R) (nearInd R) n x :=
    integrable_mul_bounded hm (measurable_shiftPair (measurable_nearInd R) (measurable_nearInd R) n)
      (abs_shiftPair_le_const (abs_nearInd_le_one R) (abs_nearInd_le_one R) hCθ n)
  have hT₂ : Integrable fun x =>
      (thetaSq v x * (δ⁻¹ * nearInd R x + δ)) * shiftPair (fun _ => 1) (fun _ => 1) n x := by
    refine (integrable_mul_bounded hm (h := fun x => (δ⁻¹ * nearInd R x + δ) *
      shiftPair (fun _ => 1) (fun _ => 1) n x) ((measurable_const.mul (measurable_nearInd R) |>.add
        measurable_const).mul (measurable_shiftPair measurable_const measurable_const n))
      (c := (δ⁻¹ + δ) * (vonMangoldtAtom n * (2 * Cθ))) (fun x => ?_)).congr
      (Eventually.of_forall fun x => by ring)
    rw [abs_mul]
    have h1 : |δ⁻¹ * nearInd R x + δ| ≤ δ⁻¹ + δ := by
      rw [abs_of_nonneg (by nlinarith [nearInd_nonneg R x])]
      nlinarith [nearInd_le_one R x]
    have h2 := abs_shiftPair_le_const (c₁ := fun _ : ℝ => (1 : ℝ)) (c₂ := fun _ : ℝ => (1 : ℝ))
      (fun _ => by simp) (fun _ => by simp) hCθ n x
    have h3 := abs_nonneg (shiftPair (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) n x)
    calc |δ⁻¹ * nearInd R x + δ| * |shiftPair (fun _ => 1) (fun _ => 1) n x|
        ≤ (δ⁻¹ + δ) * |shiftPair (fun _ => 1) (fun _ => 1) n x| := by gcongr
      _ ≤ (δ⁻¹ + δ) * (vonMangoldtAtom n * (2 * Cθ)) := by gcongr
  -- pointwise lower bound
  have hpt : ∀ x, A x + B x ≤ phiDoobPrimeJump v n x := by
    intro x
    have hw := window_jump_lower (a := v x) (b := v (x + Real.log n)) hδ
      (nearInd_zero_or_one R x) (nearInd_zero_or_one R (x + Real.log n))
    have hwt : 0 ≤ vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n) :=
      mul_nonneg (mul_nonneg ha (riemannKernelReal_pos _).le) (riemannKernelReal_pos _).le
    calc A x + B x = (vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n)) *
          (nearInd R (x + Real.log n) * v x ^ 2 + nearInd R x * v (x + Real.log n) ^ 2 -
            δ⁻¹ * (nearInd R x * v x ^ 2 + nearInd R (x + Real.log n) * v (x + Real.log n) ^ 2) -
            δ * (v x ^ 2 + v (x + Real.log n) ^ 2)) := by
          simp only [hA_def, hB_def, thetaSq]
          ring
      _ ≤ (vonMangoldtAtom n * riemannKernelReal x * riemannKernelReal (x + Real.log n)) *
          (v x - v (x + Real.log n)) ^ 2 := mul_le_mul_of_nonneg_left hw hwt
      _ = phiDoobPrimeJump v n x := by
          unfold phiDoobPrimeJump
          ring
  have hJ := integrable_phiDoobPrimeJump' hvC hvc n
  have h1 : (∫ x, A x) + ∫ x, B x ≤ ∫ x, phiDoobPrimeJump v n x := by
    rw [← integral_add hA hB]
    exact integral_mono (hA.add hB) hJ hpt
  have h2 : (∫ x, B x) = ∫ x, B' x := by
    rw [← integral_add_right_eq_self B' (Real.log n)]
    congr 1
    funext x
    simp only [hB_def, hB'_def, add_sub_cancel_right]
  have h3 : (∫ x, A x) + ∫ x, B' x =
      (∫ x, thetaSq v x * shiftPair (nearInd R) (nearInd R) n x) -
        ∫ x, (thetaSq v x * (δ⁻¹ * nearInd R x + δ)) * shiftPair (fun _ => 1) (fun _ => 1) n x := by
    rw [← integral_add hA hB', ← integral_sub hT₁ hT₂]
    congr 1
    funext x
    simp only [hA_def, hB'_def, shiftPair]
    ring
  linarith

/-- **Window-cross domination.** On every compact `C²` test the prime jump energy dominates the
`Θ`-weighted square mass against the in-window prime shifts, minus `δ⁻¹` times the window mass and
`δ` times the full mass, both against the total prime shift sum. -/
theorem tsum_phiDoobPrimeJump_window_lower {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x, thetaSq v x * primeCross R x) -
      (∫ x, (thetaSq v x * (δ⁻¹ * nearInd R x + δ)) * primeKernelSum x) ≤
      ∑' n, ∫ x, phiDoobPrimeJump v n x := by
  obtain ⟨R₀, _, hsuppv⟩ := CHMDTranslation.support_interval hvc
  have hvC := hv.continuous
  have hm : Integrable (thetaSq v) := integrable_thetaSq hvC hvc
  have hsupp₁ := thetaSq_support hsuppv
  have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hg₂ : Integrable fun x => thetaSq v x * (δ⁻¹ * nearInd R x + δ) :=
    integrable_mul_bounded hm (measurable_const.mul (measurable_nearInd R) |>.add measurable_const)
      (c := δ⁻¹ + δ) fun x => by
        rw [abs_of_nonneg (by nlinarith [nearInd_nonneg R x])]
        nlinarith [nearInd_le_one R x]
  have hsupp₂ : ∀ x, thetaSq v x * (δ⁻¹ * nearInd R x + δ) ≠ 0 → |x| ≤ R₀ := fun x hx =>
    hsupp₁ x (left_ne_zero_of_mul hx)
  obtain ⟨hs₁, he₁⟩ := tsum_integral_shiftPair hm hsupp₁ (measurable_nearInd R) (measurable_nearInd R)
    (abs_nearInd_le_one R) (abs_nearInd_le_one R)
  obtain ⟨hs₂, he₂⟩ := tsum_integral_shiftPair hg₂ hsupp₂ (c₁ := fun _ => 1) (c₂ := fun _ => 1)
    measurable_const measurable_const (fun _ => by simp) (fun _ => by simp)
  have hJ := summable_integral_phiDoobPrimeJump hvC hvc
  have hle := Summable.tsum_le_tsum (fun n => integral_phiDoobPrimeJump_window_lower hv hvc R hδ n)
    (hs₁.sub hs₂) hJ
  rw [Summable.tsum_sub hs₁ hs₂, he₁, he₂] at hle
  simp_rw [primeCross_eq_tsum_shiftPair, primeKernelSum_eq_tsum_shiftPair]
  exact hle

/-! ## Measurability of the shift sums -/

theorem measurable_primeCross (R : ℝ) : Measurable (primeCross R) := by
  show Measurable fun x => ∑' n : ℕ, shiftPair (nearInd R) (nearInd R) n x
  exact Measurable.tsum fun n => measurable_shiftPair (measurable_nearInd R) (measurable_nearInd R) n

theorem measurable_primeKernelSum : Measurable primeKernelSum := by
  have he : primeKernelSum = fun x => ∑' n : ℕ, shiftPair (fun _ => 1) (fun _ => 1) n x :=
    funext primeKernelSum_eq_tsum_shiftPair
  rw [he]
  exact Measurable.tsum fun n => measurable_shiftPair measurable_const measurable_const n

/-! ## The window mass -/

/-- The mass of a graph vector inside the window `|x| ≤ R`. -/
def nearMass (R : ℝ) (p : SourceGraph) : ℝ :=
  ∫ x, nearInd R x * (p.val.fst x) ^ 2 ∂massMeasure

theorem nearMass_nonneg (R : ℝ) (p : SourceGraph) : 0 ≤ nearMass R p :=
  integral_nonneg fun x => mul_nonneg (nearInd_nonneg R x) (sq_nonneg _)

theorem nearMass_compactLift (R : ℝ) (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    nearMass R (compactLift v hv hvc) = ∫ x, nearInd R x * v x ^ 2 ∂massMeasure := by
  unfold nearMass
  apply integral_congr_ae
  filter_upwards [compactLift_source_ae v hv hvc] with x hx
  rw [hx]

theorem norm_compactLift_source_sq (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ‖(compactLift v hv hvc).val.fst‖ ^ 2 = ∫ x, v x ^ 2 ∂massMeasure := by
  show ‖(compact_memLp_mass hv.continuous hvc).toLp v‖ ^ 2 = _
  rw [norm_toLp_sq]

theorem integral_sq_mass_eq (v : ℝ → ℝ) :
    (∫ x, v x ^ 2 ∂massMeasure) = ∫ x, thetaSq v x * Real.cosh (x / 2) := by
  rw [integral_mass]
  congr 1
  funext x
  simp only [thetaSq, massDensity]
  ring

theorem integral_near_sq_mass_eq (R : ℝ) (v : ℝ → ℝ) :
    (∫ x, nearInd R x * v x ^ 2 ∂massMeasure) =
      ∫ x, (thetaSq v x * Real.cosh (x / 2)) * nearInd R x := by
  rw [integral_mass]
  congr 1
  funext x
  simp only [thetaSq, massDensity]
  ring

theorem sourceEnergy_compactLift_eq (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    sourceEnergy (compactLift v hv hvc) =
      phiDoobArchJumpEnergy v + (∑' n, ∫ x, phiDoobPrimeJump v n x) - ∫ x, v x ^ 2 ∂massMeasure := by
  rw [sourceEnergy, compactLift, energy_ofFunction, ← integral_complete_difference_sq hv hvc]
  rfl

/-! ## The window lower bound on compact tests -/

/-- **Confinement inequality on compact tests.** With `K₁` the relative tail of the prime shifts
outside the window of radius `R` and `B` the archimedean correction constant, for every `δ > 0`
`E(v) ≥ −(K₁ + (1+δ)B/cosh(R/2) + δ)‖v‖²_μ − (B + δ⁻¹(1+B) + δB) · nearMass_R(v)`. -/
theorem sourceEnergy_compactLift_window_lower {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) {R : ℝ} (hR : 0 ≤ R) {K₁ : ℝ}
    (hT : ∀ x, primeTail R x ≤ K₁ * Real.cosh (x / 2)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y, |primeKernelSum y - Real.cosh (y / 2)| ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    -(K₁ + (1 + δ) * B / Real.cosh (R / 2) + δ) * ‖(compactLift v hv hvc).val.fst‖ ^ 2 -
      (B + δ⁻¹ * (1 + B) + δ * B) * nearMass R (compactLift v hv hvc) ≤
      sourceEnergy (compactLift v hv hvc) := by
  have hvC := hv.continuous
  have hm0 : ∀ x, 0 ≤ thetaSq v x := thetaSq_nonneg v
  have hm : Integrable (thetaSq v) := integrable_thetaSq hvC hvc
  have hmcosh : Integrable fun x => thetaSq v x * Real.cosh (x / 2) := integrable_thetaSq_mul_cosh hvC hvc
  have hmnear : Integrable fun x => (thetaSq v x * Real.cosh (x / 2)) * nearInd R x :=
    integrable_mul_bounded hmcosh (measurable_nearInd R) (abs_nearInd_le_one R)
  have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  set c := Real.cosh (R / 2) with hc
  have hc1 : 1 ≤ c := Real.one_le_cosh _
  have hc0 : 0 < c := by linarith
  rw [norm_compactLift_source_sq, nearMass_compactLift, sourceEnergy_compactLift_eq,
    integral_sq_mass_eq, integral_near_sq_mass_eq]
  set V := ∫ x, thetaSq v x * Real.cosh (x / 2) with hV
  set N := ∫ x, (thetaSq v x * Real.cosh (x / 2)) * nearInd R x with hN
  set I := ∫ x, thetaSq v x with hI
  have harch := phiDoobArchJumpEnergy_nonneg v
  have hwin := tsum_phiDoobPrimeJump_window_lower hv hvc R hδ
  -- the cross term from below
  have hcross_int : Integrable fun x => thetaSq v x * primeCross R x :=
    integrable_thetaSq_mul hvC hvc (measurable_primeCross R) (a := 1) (b := B) fun x => by
      rw [abs_of_nonneg (primeCross_nonneg R x)]
      have h1 := hB x
      rw [abs_le] at h1
      have h2 := primeTail_nonneg R x
      have h3 := primeCross_add_primeTail R x
      linarith
  have hlow_int : Integrable fun x => thetaSq v x * ((1 - K₁) * Real.cosh (x / 2) - B) :=
    ((continuous_thetaSq hvC).mul ((continuous_const.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).sub continuous_const))
      |>.integrable_of_hasCompactSupport (hasCompactSupport_thetaSq hvc).mul_right
  have F1 : (∫ x, thetaSq v x * ((1 - K₁) * Real.cosh (x / 2) - B)) ≤
      ∫ x, thetaSq v x * primeCross R x := by
    refine integral_mono hlow_int hcross_int fun x => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hm0 x)
    have h1 := hB x
    rw [abs_le] at h1
    have h2 := hT x
    have h3 := primeCross_add_primeTail R x
    linarith
  have F1val : (∫ x, thetaSq v x * ((1 - K₁) * Real.cosh (x / 2) - B)) = (1 - K₁) * V - B * I := by
    rw [hV, hI, ← integral_const_mul, ← integral_const_mul, ← integral_sub (hmcosh.const_mul _)
      (hm.const_mul _)]
    congr 1
    funext x
    ring
  -- the window term from above
  have hwin_int : Integrable fun x => (thetaSq v x * (δ⁻¹ * nearInd R x + δ)) * primeKernelSum x := by
    refine (integrable_thetaSq_mul hvC hvc (h := fun x => (δ⁻¹ * nearInd R x + δ) * primeKernelSum x)
      ((measurable_const.mul (measurable_nearInd R) |>.add measurable_const).mul measurable_primeKernelSum)
      (a := δ⁻¹ + δ) (b := (δ⁻¹ + δ) * B) fun x => ?_).congr (Eventually.of_forall fun x => by ring)
    rw [abs_mul]
    have h1 : |δ⁻¹ * nearInd R x + δ| ≤ δ⁻¹ + δ := by
      rw [abs_of_nonneg (by nlinarith [nearInd_nonneg R x])]
      nlinarith [nearInd_le_one R x]
    have h2 : |primeKernelSum x| ≤ Real.cosh (x / 2) + B := by
      have := hB x
      rw [abs_le] at this ⊢
      constructor <;> linarith [Real.cosh_pos (x / 2)]
    have h3 := abs_nonneg (primeKernelSum x)
    have h4 : 0 ≤ δ⁻¹ + δ := by linarith
    calc |δ⁻¹ * nearInd R x + δ| * |primeKernelSum x| ≤ (δ⁻¹ + δ) * (Real.cosh (x / 2) + B) :=
          mul_le_mul h1 h2 h3 h4
      _ = (δ⁻¹ + δ) * Real.cosh (x / 2) + (δ⁻¹ + δ) * B := by ring
  have hu1 : Integrable fun x => δ⁻¹ * (1 + B) * ((thetaSq v x * Real.cosh (x / 2)) * nearInd R x) :=
    hmnear.const_mul _
  have hu2 : Integrable fun x => δ * (thetaSq v x * Real.cosh (x / 2)) := hmcosh.const_mul _
  have hu3 : Integrable fun x => δ * B * thetaSq v x := hm.const_mul _
  have hu12 : Integrable fun x => δ⁻¹ * (1 + B) * ((thetaSq v x * Real.cosh (x / 2)) * nearInd R x) +
      δ * (thetaSq v x * Real.cosh (x / 2)) := hu1.add hu2
  have hup_int : Integrable fun x => δ⁻¹ * (1 + B) * ((thetaSq v x * Real.cosh (x / 2)) * nearInd R x) +
      δ * (thetaSq v x * Real.cosh (x / 2)) + δ * B * thetaSq v x := hu12.add hu3
  have F2 : (∫ x, (thetaSq v x * (δ⁻¹ * nearInd R x + δ)) * primeKernelSum x) ≤
      ∫ x, δ⁻¹ * (1 + B) * ((thetaSq v x * Real.cosh (x / 2)) * nearInd R x) +
        δ * (thetaSq v x * Real.cosh (x / 2)) + δ * B * thetaSq v x := by
    refine integral_mono hwin_int hup_int fun x => ?_
    have h1 := hB x
    rw [abs_le] at h1
    have hα0 := nearInd_nonneg R x
    have hw0 : 0 ≤ thetaSq v x * (δ⁻¹ * nearInd R x + δ) :=
      mul_nonneg (hm0 x) (by nlinarith)
    have hk1 := mul_le_mul_of_nonneg_left (show primeKernelSum x ≤ Real.cosh (x / 2) + B by linarith) hw0
    have hk2 : 0 ≤ δ⁻¹ * B * nearInd R x * (thetaSq v x * (Real.cosh (x / 2) - 1)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hδi hB0) hα0)
        (mul_nonneg (hm0 x) (by linarith [Real.one_le_cosh (x / 2)]))
    nlinarith [hk1, hk2]
  have F2val : (∫ x, δ⁻¹ * (1 + B) * ((thetaSq v x * Real.cosh (x / 2)) * nearInd R x) +
      δ * (thetaSq v x * Real.cosh (x / 2)) + δ * B * thetaSq v x) =
      δ⁻¹ * (1 + B) * N + δ * V + δ * B * I := by
    rw [integral_add hu12 hu3, integral_add hu1 hu2, integral_const_mul, integral_const_mul,
      integral_const_mul]
  -- the diffuse mass is controlled by the window mass and the far field
  have F4 : I ≤ N + V / c := by
    have hint : Integrable fun x => (thetaSq v x * Real.cosh (x / 2)) * nearInd R x +
        (thetaSq v x * Real.cosh (x / 2)) / c := hmnear.add (hmcosh.div_const _)
    have hpt : ∀ x, thetaSq v x ≤ (thetaSq v x * Real.cosh (x / 2)) * nearInd R x +
        (thetaSq v x * Real.cosh (x / 2)) / c := by
      intro x
      have hcx := Real.one_le_cosh (x / 2)
      have hq : 0 ≤ (thetaSq v x * Real.cosh (x / 2)) / c :=
        div_nonneg (mul_nonneg (hm0 x) (by linarith)) hc0.le
      rcases nearInd_zero_or_one R x with h0 | h1
      · have hfar : farInd R x = 1 := by
          have := nearInd_add_farInd R x
          linarith
        have hθ := theta_le_mass_div_cosh hR hfar
        have : thetaSq v x ≤ (thetaSq v x * Real.cosh (x / 2)) / c := by
          calc thetaSq v x = v x ^ 2 * riemannKernelReal x := rfl
            _ ≤ v x ^ 2 * (massDensity x / Real.cosh (R / 2)) :=
                mul_le_mul_of_nonneg_left hθ (sq_nonneg _)
            _ = (thetaSq v x * Real.cosh (x / 2)) / c := by
                simp only [thetaSq, massDensity, hc]
                ring
        rw [h0]
        linarith
      · rw [h1, mul_one]
        nlinarith [hm0 x]
    have := integral_mono hm hint hpt
    rw [integral_add hmnear (hmcosh.div_const _), integral_div] at this
    exact this
  -- assemble
  have hBc : 0 ≤ (1 + δ) * B := by positivity
  have hF4 := mul_le_mul_of_nonneg_left F4 hBc
  have hE := calc
    -(K₁ + (1 + δ) * B / c + δ) * V - (B + δ⁻¹ * (1 + B) + δ * B) * N
        = -(K₁ + δ) * V - δ⁻¹ * (1 + B) * N - (1 + δ) * B * (N + V / c) := by ring
    _ ≤ -(K₁ + δ) * V - δ⁻¹ * (1 + B) * N - (1 + δ) * B * I := by linarith
    _ = ((1 - K₁) * V - B * I) - (δ⁻¹ * (1 + B) * N + δ * V + δ * B * I) - V := by ring
  linarith [hE, F1, F1val, F2, F2val, hwin, harch]

/-! ## The window mass as a bounded quadratic form -/

/-- Multiplication by the window indicator on the mass space. -/
def nearMul (R : ℝ) : MassSpace →L[ℝ] MassSpace :=
  lpBoundedMulCLM (measurable_nearInd R) zero_le_one fun x => by
    rw [Real.norm_eq_abs]
    exact abs_nearInd_le_one R x

theorem nearMul_coeFn (R : ℝ) (f : MassSpace) :
    (nearMul R f : ℝ → ℝ) =ᵐ[massMeasure] fun x => nearInd R x * f x :=
  lpBoundedMulCLM_coeFn _ _ _ f

theorem norm_nearMul_le (R : ℝ) (f : MassSpace) : ‖nearMul R f‖ ≤ ‖f‖ :=
  ((nearMul R).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg f) (norm_lpBoundedMulCLM_le _ _ _))

theorem nearMass_eq_norm_sq (R : ℝ) (p : SourceGraph) :
    nearMass R p = ‖nearMul R (sourceMap p)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  unfold nearMass
  apply integral_congr_ae
  filter_upwards [nearMul_coeFn R (sourceMap p)] with x hx
  rw [hx]
  have hsm : (sourceMap p : ℝ → ℝ) x = p.val.fst x := rfl
  rw [hsm]
  rcases nearInd_zero_or_one R x with h | h <;> simp [h, pow_two]

theorem continuous_nearMass (R : ℝ) : Continuous (nearMass R) := by
  have h : nearMass R = fun p => ‖nearMul R (sourceMap p)‖ ^ 2 := funext (nearMass_eq_norm_sq R)
  rw [h]
  exact ((nearMul R).continuous.comp sourceMap.continuous).norm.pow 2

/-! ## The confinement theorem on the completed graph -/

/-- **Negative Doob energy localizes.** For every `ε > 0` there are a window radius `R` and a
constant `C` with `E(p) ≥ −ε ‖p‖²_μ − C · nearMass_R(p)` for every vector `p` of the completed
arithmetic Doob graph. -/
theorem exists_window_energy_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ p : SourceGraph,
      -ε * ‖sourceMap p‖ ^ 2 - C * nearMass R p ≤ sourceEnergy p := by
  obtain ⟨A, hA0, hA⟩ := exists_primeTail_bound
  obtain ⟨B, hB0, hB⟩ := exists_primeKernelSum_two_sided
  set δ : ℝ := min 1 (ε / 3) with hδ_def
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 3 := min_le_right _ _
  have htail : Tendsto (fun R : ℝ => 2 * A * shellRatio ^ ⌊R⌋₊) atTop (𝓝 0) := by
    have h := shellRatio_pow_floor_tendsto.const_mul (2 * A)
    rwa [mul_zero] at h
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp
    (htail.eventually_lt_const (by positivity : (0 : ℝ) < ε / 3))
  set R : ℝ := max R₁ (max 0 (24 * B / ε)) with hR_def
  have hR0 : 0 ≤ R := le_max_of_le_right (le_max_left _ _)
  have hRR₁ : R₁ ≤ R := le_max_left _ _
  have hRB : 24 * B / ε ≤ R := le_max_of_le_right (le_max_right _ _)
  have hK₁ : 2 * A * shellRatio ^ ⌊R⌋₊ ≤ ε / 3 := (hR₁ R hRR₁).le
  have hcosh : 2 * B / Real.cosh (R / 2) ≤ ε / 3 := by
    have hc0 := Real.cosh_pos (R / 2)
    rw [div_le_iff₀ hc0]
    have h1 : (R / 2 + 1) / 2 ≤ Real.cosh (R / 2) := by
      rw [Real.cosh_eq]
      have := Real.add_one_le_exp (R / 2)
      have := Real.exp_pos (-(R / 2))
      linarith
    have h2 : 24 * B ≤ R * ε := (div_le_iff₀ hε).mp hRB
    nlinarith [mul_le_mul_of_nonneg_left h1 hε.le]
  refine ⟨R, B + δ⁻¹ * (1 + B) + δ * B, hR0, by positivity, ?_⟩
  have hT : ∀ x, primeTail R x ≤ (2 * A * shellRatio ^ ⌊R⌋₊) * Real.cosh (x / 2) := fun x =>
    primeTail_le_cosh hA R x
  have hcompact : ∀ p ∈ (compactTests : Set SourceGraph),
      -ε * ‖sourceMap p‖ ^ 2 - (B + δ⁻¹ * (1 + B) + δ * B) * nearMass R p ≤ sourceEnergy p := by
    rintro p ⟨v, hv, hvc, rfl⟩
    have h := sourceEnergy_compactLift_window_lower hv hvc hR0 hT hB0 hB hδ
    have hcoef : 2 * A * shellRatio ^ ⌊R⌋₊ + (1 + δ) * B / Real.cosh (R / 2) + δ ≤ ε := by
      have h' : (1 + δ) * B / Real.cosh (R / 2) ≤ 2 * B / Real.cosh (R / 2) := by
        apply div_le_div_of_nonneg_right _ (Real.cosh_pos _).le
        nlinarith
      linarith
    have hn := nearMass_nonneg R (compactLift v hv hvc)
    have hsm : sourceMap (compactLift v hv hvc) = (compactLift v hv hvc).val.fst := rfl
    rw [hsm]
    have hsq : 0 ≤ ‖(compactLift v hv hvc).val.fst‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hcoef hsq]
  intro p
  refine Dense.induction dense_compactTests (P := fun q => -ε * ‖sourceMap q‖ ^ 2 -
    (B + δ⁻¹ * (1 + B) + δ * B) * nearMass R q ≤ sourceEnergy q) hcompact ?_ p
  exact isClosed_le ((continuous_const.mul (sourceMap.continuous.norm.pow 2)).sub
    (continuous_const.mul (continuous_nearMass R))) continuous_sourceEnergy

/-- **Far-field positivity up to `ε`.** Vectors with no mass inside the window of radius `R_ε`
have Doob energy at least `−ε` times their mass. -/
theorem exists_farField_energy_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p : SourceGraph, nearMass R p = 0 →
      -ε * ‖sourceMap p‖ ^ 2 ≤ sourceEnergy p := by
  obtain ⟨R, C, hR0, _, h⟩ := exists_window_energy_bound hε
  refine ⟨R, hR0, fun p hp => ?_⟩
  have := h p
  rwa [hp, mul_zero, sub_zero] at this

/-! ## No cusp escape above the threshold -/

/-- **Approximate eigenvectors of the resolvent above `1/2` are confined.** For every level
`μ > 1/2` there are a window radius `R`, a mass level `θ > 0` and a tolerance `η > 0` such that
every unit vector `w` with `‖Rw − μw‖ ≤ η` has `‖1_{|x|≤R} · Rw‖² ≥ θ`. -/
theorem exists_window_mass_resolvent {μ : ℝ} (hμ : 1 / 2 < μ) :
    ∃ R θ η : ℝ, 0 ≤ R ∧ 0 < θ ∧ 0 < η ∧ ∀ w : MassSpace, ‖w‖ = 1 →
      ‖resolvent w - μ • w‖ ≤ η → θ ≤ ‖nearMul R (resolvent w)‖ ^ 2 := by
  have hμ0 : 0 < μ := by linarith
  set ε : ℝ := (2 * μ - 1) / (2 * μ) with hε_def
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  obtain ⟨R, C, hR0, hC0, hbound⟩ := exists_window_energy_bound hε
  set γ : ℝ := μ * (2 * μ - 1) / 4 with hγ_def
  have hγ : 0 < γ := div_pos (mul_pos hμ0 (by linarith)) (by norm_num)
  set η : ℝ := min μ (γ / (8 * μ * (μ + 1))) with hη_def
  have hη : 0 < η := lt_min hμ0 (div_pos hγ (by positivity))
  refine ⟨R, γ / (C + 1), η, hR0, div_pos hγ (by linarith), hη, fun w hw hρ => ?_⟩
  set ρ := ‖resolvent w - μ • w‖ with hρ_def
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hρμ : ρ ≤ μ := hρ.trans (min_le_left _ _)
  have hργ : ρ * (8 * μ * (μ + 1)) ≤ γ := by
    have h := hρ.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at h
  have ha_low : μ - ρ ≤ ‖resolvent w‖ := by
    have h := norm_sub_norm_le (μ • w) (resolvent w)
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos hμ0, norm_sub_rev] at h
    linarith
  have hs : ⟪w, resolvent w⟫_ℝ ≤ μ + ρ := by
    have h1 : ⟪w, resolvent w⟫_ℝ - μ = ⟪w, resolvent w - μ • w⟫_ℝ := by
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hw]
      ring
    have h2 : |⟪w, resolvent w - μ • w⟫_ℝ| ≤ ρ := by
      calc |⟪w, resolvent w - μ • w⟫_ℝ| ≤ ‖w‖ * ‖resolvent w - μ • w‖ := abs_real_inner_le_norm _ _
        _ = ρ := by rw [hw, one_mul]
    have h3 := (abs_le.mp h2).2
    linarith
  have hE := sourceEnergy_rieszLift w
  have hb := hbound (rieszLift w)
  have hsm : sourceMap (rieszLift w) = resolvent w := rfl
  have hnm : nearMass R (rieszLift w) = ‖nearMul R (resolvent w)‖ ^ 2 := by
    rw [nearMass_eq_norm_sq, hsm]
  rw [hsm, hnm, hE] at hb
  set a := ‖resolvent w‖ with ha_def
  set m := ‖nearMul R (resolvent w)‖ ^ 2 with hm_def
  set s := ⟪w, resolvent w⟫_ℝ with hs_def
  have hm0 : 0 ≤ m := sq_nonneg _
  have key : γ ≤ C * m := by
    have h1 : (μ - ρ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) ha_low 2
    have h4 : ε * (2 * μ) = 2 * μ - 1 := by
      rw [hε_def]
      field_simp
    have h5 : 2 * μ * ((2 - ε) * a ^ 2 - s) ≤ 2 * μ * (C * m) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    have h6 : 2 * μ * ((2 - ε) * a ^ 2 - s) = (2 * μ + 1) * a ^ 2 - 2 * μ * s := by
      linear_combination (-(a ^ 2)) * h4
    have P1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * μ + 1)
    have P2 := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 2 * μ)
    have P3 : 0 ≤ (2 * μ + 1) * ρ ^ 2 := by positivity
    have P5 : γ * (4 * μ) = μ ^ 2 * (2 * μ - 1) := by
      rw [hγ_def]
      ring
    have P6 : γ * 1 ≤ γ * (4 * μ) := mul_le_mul_of_nonneg_left (by linarith) hγ.le
    have h7 : 2 * μ * γ ≤ 2 * μ * (C * m) := by nlinarith
    exact le_of_mul_le_mul_left h7 (by linarith)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **No cusp escape above the threshold.** Every sequence of unit vectors on which the arithmetic
resolvent is asymptotically the scalar `μ > 1/2` keeps, eventually, a definite amount of mass
inside a fixed window: Weyl sequences at levels above `1/2` cannot escape to the cusp. -/
theorem eventually_window_mass_of_weyl {μ : ℝ} (hμ : 1 / 2 < μ) (e : ℕ → MassSpace)
    (he : ∀ n, ‖e n‖ = 1)
    (hw : Tendsto (fun n => ‖resolvent (e n) - μ • e n‖) atTop (𝓝 0)) :
    ∃ R θ : ℝ, 0 ≤ R ∧ 0 < θ ∧ ∀ᶠ n in atTop, θ ≤ ‖nearMul R (e n)‖ := by
  obtain ⟨R, θ, η, hR0, hθ, hη, h⟩ := exists_window_mass_resolvent hμ
  have hμ0 : 0 < μ := by linarith
  refine ⟨R, Real.sqrt θ / (2 * μ), hR0, by positivity, ?_⟩
  have h1 : ∀ᶠ n in atTop, ‖resolvent (e n) - μ • e n‖ < min η (Real.sqrt θ / 2) :=
    hw.eventually_lt_const (lt_min hη (by positivity))
  filter_upwards [h1] with n hn
  have hρη : ‖resolvent (e n) - μ • e n‖ ≤ η := (hn.trans_le (min_le_left _ _)).le
  have hρθ : ‖resolvent (e n) - μ • e n‖ ≤ Real.sqrt θ / 2 := (hn.trans_le (min_le_right _ _)).le
  have hm := h (e n) (he n) hρη
  have hsq : Real.sqrt θ ≤ ‖nearMul R (resolvent (e n))‖ := by
    calc Real.sqrt θ ≤ Real.sqrt (‖nearMul R (resolvent (e n))‖ ^ 2) := Real.sqrt_le_sqrt hm
      _ = ‖nearMul R (resolvent (e n))‖ := Real.sqrt_sq (norm_nonneg _)
  have htr : ‖nearMul R (resolvent (e n))‖ ≤
      ‖resolvent (e n) - μ • e n‖ + μ * ‖nearMul R (e n)‖ := by
    have hdecomp : nearMul R (resolvent (e n)) =
        nearMul R (resolvent (e n) - μ • e n) + μ • nearMul R (e n) := by
      rw [← map_smul, ← map_add, sub_add_cancel]
    calc ‖nearMul R (resolvent (e n))‖
        = ‖nearMul R (resolvent (e n) - μ • e n) + μ • nearMul R (e n)‖ := by rw [hdecomp]
      _ ≤ ‖nearMul R (resolvent (e n) - μ • e n)‖ + ‖μ • nearMul R (e n)‖ := norm_add_le _ _
      _ ≤ ‖resolvent (e n) - μ • e n‖ + μ * ‖nearMul R (e n)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ0]
          exact add_le_add (norm_nearMul_le R _) le_rfl
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ## Sharpness: the threshold family escapes every window -/

/-- The normalized cusp-escape vector at translation `t` has no mass in the window of radius `R₀`
once `t` exceeds `R₀` plus the support radius of the profile. -/
theorem nearMul_escape_eq_zero {Rp : ℝ}
    (hRp : ∀ x, CHMDTranslation.profile x ≠ 0 → -Rp ≤ x ∧ x ≤ Rp) {R₀ t : ℝ} (ht : R₀ + Rp < t) :
    nearMul R₀ (CHMDEscape.source (CHMDEscape.normalized t)) = 0 := by
  have hsm : CHMDEscape.source (CHMDEscape.normalized t) =
      ‖CHMDEscape.source (CHMDEscape.lift t)‖⁻¹ • CHMDEscape.source (CHMDEscape.lift t) := rfl
  rw [hsm, map_smul]
  suffices h : nearMul R₀ (CHMDEscape.source (CHMDEscape.lift t)) = 0 by rw [h, smul_zero]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hae : (CHMDEscape.source (CHMDEscape.lift t) : ℝ → ℝ) =ᵐ[massMeasure] CHMDEscape.test t :=
    compactLift_source_ae (CHMDEscape.test t) (CHMDEscape.test_contDiff t) (CHMDEscape.test_compact t)
  filter_upwards [nearMul_coeFn R₀ (CHMDEscape.source (CHMDEscape.lift t)), hae] with x hx hx'
  rw [hx, hx']
  simp only [Pi.zero_apply]
  rcases nearInd_zero_or_one R₀ x with h0 | h1
  · rw [h0, zero_mul]
  · have hxR : |x| ≤ R₀ := by
      by_contra hc
      simp [nearInd, hc] at h1
    have hprof : CHMDTranslation.profile (x - t) = 0 := by
      by_contra hc
      have h2 := (hRp _ hc).1
      have h3 := (abs_le.mp hxR).2
      linarith
    rw [h1, one_mul]
    show CHMDTranslation.translate CHMDTranslation.profile t x / riemannKernelReal x = 0
    rw [CHMDTranslation.translate, hprof, zero_div]

/-- **Sharpness of the threshold.** The normalized primitive cusp escape is a unit family on which
the arithmetic resolvent is asymptotically the scalar `1/2`, and it has no mass in any fixed
window for all large translations: at the threshold `1/2`, approximate eigenvectors do escape to
the cusp, while above `1/2` they cannot. -/
theorem threshold_escape_sequence :
    ∃ e : ℕ → MassSpace, (∀ n, ‖e n‖ = 1) ∧
      Tendsto (fun n => ‖resolvent (e n) - (1 / 2 : ℝ) • e n‖) atTop (𝓝 0) ∧
      ∀ R₀ : ℝ, ∀ᶠ n in atTop, nearMul R₀ (e n) = 0 := by
  obtain ⟨Rp, _, hRp⟩ := CHMDTranslation.support_interval CHMDTranslation.profile_compact
  refine ⟨fun n => CHMDEscape.source (CHMDEscape.normalized (n : ℝ)), fun n =>
    CHMDEscape.normalized_source_norm _, ?_, fun R₀ => ?_⟩
  · exact resolvent_defect_tendsto_zero.comp tendsto_natCast_atTop_atTop
  · filter_upwards [eventually_gt_atTop ⌈R₀ + Rp⌉₊] with n hn
    apply nearMul_escape_eq_zero hRp
    have h1 : R₀ + Rp ≤ ⌈R₀ + Rp⌉₊ := Nat.le_ceil _
    have h2 : (⌈R₀ + Rp⌉₊ : ℝ) < n := by exact_mod_cast hn
    linarith

end RHTower.CHMDPolar
