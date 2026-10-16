import GaloisForLFunctions.RHTower.CHMDGeneratorWeilOperator
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
orthonormal Weyl sequence of the arithmetic resolvent at a level `μ > 1/2` keeps a definite
fraction of its mass inside a fixed window (no escape to the cusp above the threshold).
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

theorem integrable_thetaSq {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (thetaSq v) := by
  have hc : Continuous (thetaSq v) := (hv.pow 2).mul continuous_riemannKernelReal
  have hs : HasCompactSupport (thetaSq v) := by
    have h := hvc.mul_right (f' := fun x => v x * riemannKernelReal x)
    have he : thetaSq v = v * fun x => v x * riemannKernelReal x := by
      funext x
      simp only [thetaSq, Pi.mul_apply]
      ring
    rw [he]
    exact h
  exact hc.integrable_of_hasCompactSupport hs

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

end RHTower.CHMDPolar
