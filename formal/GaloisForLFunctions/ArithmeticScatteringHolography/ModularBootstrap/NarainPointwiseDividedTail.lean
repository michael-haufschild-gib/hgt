import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralZero
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPointwiseStripBounds
import GaloisForLFunctions.RHTower.SmoothDyadicZetaReflection

/-!
# Uniform bounds at the removable Narain center

Dividing out the central zero retains an exact mean-plus-tail formula and yields uniform bounds on compact spectral rectangles.
-/

open Complex RHTower Set
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Removing the central zero preserves the explicit Fourier-tail decomposition. -/
theorem dividedFilledEisensteinNumerator_eq_mean_add_tail
    (z : D4BMUpperHalfPlaneCoordinate) (u : ℂ) :
    dividedFilledEisensteinNumerator z u =
      dividedFilledNumeratorMean ⟨z.y, z.y_pos⟩ u +
        2 * (2 * u - 1) * (1 + 2 * u) * eisTail u z.x z.y := by
  let G : ℂ → ℂ := fun v => dividedFilledNumeratorMean ⟨z.y, z.y_pos⟩ v +
    2 * (2 * v - 1) * (1 + 2 * v) * eisTail v z.x z.y
  have hG : Differentiable ℂ G := by
    convert! (differentiable_dividedFilledNumeratorMean ⟨z.y, z.y_pos⟩).add
      ((by fun_prop : Differentiable ℂ (fun v : ℂ => 2 * (2 * v - 1) * (1 + 2 * v))).mul
        (fun v => differentiableAt_eisTail z.x z.y_pos v)) using 1
  have heq (v : ℂ) : v * dividedFilledEisensteinNumerator z v = v * G v := by
    rw [← filledEisensteinNumerator_eq_mul_divided]
    change filledNumeratorMean ⟨z.y, z.y_pos⟩ v +
      (2 * v - 1) * (1 + 2 * v) * (2 * v) * eisTail v z.x z.y = _
    rw [filledNumeratorMean_eq_mul_divided]
    dsimp only [G]
    ring
  change dividedFilledEisensteinNumerator z u = G u
  by_cases hu : u = 0
  · subst u
    have hd := ((hasDerivAt_id (0 : ℂ)).mul
      ((differentiable_dividedFilledEisensteinNumerator z) 0).hasDerivAt).deriv
    have hg := ((hasDerivAt_id (0 : ℂ)).mul (hG 0).hasDerivAt).deriv
    change deriv (fun v : ℂ => v * dividedFilledEisensteinNumerator z v) 0 =
      1 * dividedFilledEisensteinNumerator z 0 +
        0 * deriv (dividedFilledEisensteinNumerator z) 0 at hd
    change deriv (fun v : ℂ => v * G v) 0 = 1 * G 0 + 0 * deriv G 0 at hg
    simp only [one_mul, zero_mul, add_zero] at hd hg
    have h := congrArg (fun f : ℂ → ℂ => deriv f 0) (funext heq)
    rwa [hd, hg] at h
  · exact mul_left_cancel₀ hu (heq u)


/-- The entire divided numerator is bounded on compact spectral rectangles,
uniformly in the horizontal target coordinate. -/
theorem exists_dividedFilledEisensteinNumerator_uniform_rect_bound
    (Y : Height) {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ∀ u : ℂ, |u.re| ≤ B → |u.im| ≤ T →
      ‖dividedFilledEisensteinNumerator ⟨x, Y.val, Y.property⟩ u‖ ≤ C := by
  obtain ⟨M, hM, hm⟩ := exists_norm_le_on_rect
    (f := dividedFilledNumeratorMean Y) (a := -B) (b := B) (c := T)
    (fun σ t _ _ _ => (differentiable_dividedFilledNumeratorMean Y).continuous.continuousAt)
  obtain ⟨C, N, hC, hb⟩ := exists_weightedTail_jets_le_sharp Y.property hB
  refine ⟨M + 16 * (1 + B) ^ 2 * C * (1 + T) ^ (N + 2), by positivity, ?_⟩
  intro x u hu ht
  have hm' : ‖dividedFilledNumeratorMean Y u‖ ≤ M := by
    simpa only [Complex.re_add_im] using hm u.re u.im (abs_le.mp hu).1 (abs_le.mp hu).2 ht
  have hY : Y.val ∈ Icc (Y.val / 2) (2 * Y.val) := by
    have hpos : 0 < Y.val := Y.property
    constructor <;> linarith only [hpos]
  have htail := (eisTail_jets_le (hb u false x Y.val hu hY)
    (hb u true x Y.val hu hY)).1
  have he : Real.exp (-(Real.pi * |u.im| / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hp : (1 + |u.im|) ^ N ≤ (1 + T) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith only [ht]) N
  have htail' : ‖eisTail u x Y.val‖ ≤ 2 * C * (1 + T) ^ N := by
    calc
      _ ≤ 2 * (C * (1 + |u.im|) ^ N * Real.exp (-(Real.pi * |u.im| / 2))) := htail
      _ ≤ 2 * (C * (1 + T) ^ N * 1) := by gcongr
      _ = _ := by ring
  obtain ⟨hplus, _, _, hminus, _⟩ := norm_one_add_two_mul_le hu hB
  have hlinear : 2 * (1 + B) * (1 + |u.im|) ≤ 2 * (1 + B) * (1 + T) := by gcongr
  have hplus' : ‖1 + 2 * u‖ ≤ 2 * (1 + B) * (1 + T) := hplus.trans hlinear
  have hminus' : ‖2 * u - 1‖ ≤ 2 * (1 + B) * (1 + T) := by
    rw [show 2 * u - 1 = -(2 * (1 / 2 - u)) by ring, norm_neg,
      norm_mul, Complex.norm_ofNat]
    have h0 : 2 * ‖(1 / 2 : ℂ) - u‖ ≤ 2 * (1 + B) * (1 + |u.im|) := by
      nlinarith only [hminus]
    exact h0.trans hlinear
  rw [dividedFilledEisensteinNumerator_eq_mean_add_tail]
  calc
    _ ≤ ‖dividedFilledNumeratorMean Y u‖ +
        ‖2 * (2 * u - 1) * (1 + 2 * u) * eisTail u x Y.val‖ := norm_add_le _ _
    _ ≤ M + 2 * (2 * (1 + B) * (1 + T)) *
        (2 * (1 + B) * (1 + T)) * (2 * C * (1 + T) ^ N) := by
      simp only [norm_mul, Complex.norm_ofNat]
      gcongr
    _ = _ := by rw [pow_add]; ring

#print axioms exists_dividedFilledEisensteinNumerator_uniform_rect_bound

#print axioms dividedFilledEisensteinNumerator_eq_mean_add_tail
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
