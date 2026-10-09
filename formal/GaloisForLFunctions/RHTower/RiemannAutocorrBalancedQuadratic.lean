import GaloisForLFunctions.RHTower.RiemannAutocorrWeightedTranslation

/-!
# Quadratic cancellation for balanced Riemann-kernel translations

Actual cusp-series derivatives give a weighted quadratic remainder. Balanced
translation weights cancel its linear term before integration, so no derivative
of an improper integral is assumed.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower

/-- Short translations of every fixed actual kernel derivative retain a
decaying Lipschitz constant. -/
theorem exists_riemannKernelDeriv_translation_envelope (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ x h : ℝ, |h| ≤ 1 →
      ‖riemannKernelDeriv k (x + h) - riemannKernelDeriv k x‖ ≤
        D * Real.exp (-(3 * |x|)) * |h| := by
  obtain ⟨C, hC, hbound⟩ := exists_riemannKernelDeriv_cubic_exp_envelope (k + 1)
  refine ⟨C * Real.exp 3, by positivity, ?_⟩
  intro x h hh
  have hderiv (z : ℝ) (hz : z ∈ Icc (x - 1) (x + 1)) :
      ‖riemannKernelDeriv (k + 1) z‖ ≤ (C * Real.exp 3) * Real.exp (-(3 * |x|)) := by
    have hzx : |z - x| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hdist := abs_sub_abs_le_abs_sub x z
    rw [abs_sub_comm x z] at hdist
    calc
      _ ≤ C * Real.exp (-(3 * |z|)) := hbound z
      _ ≤ C * Real.exp (3 - 3 * |x|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
  have hx : x ∈ Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have hxh : x + h ∈ Icc (x - 1) (x + 1) := by
    have := abs_le.mp hh
    constructor <;> linarith
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Icc (x - 1) (x + 1)) =>
      (hasDerivAt_riemannKernelDeriv k z).hasDerivWithinAt)
    hderiv (convex_Icc (x - 1) (x + 1)) hx hxh
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using hm

/-- Every actual kernel derivative has a quadratic short-translation remainder
with an exponentially decaying center weight. -/
theorem exists_riemannKernelDeriv_quadratic_remainder_envelope (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ x h : ℝ, |h| ≤ 1 →
      ‖riemannKernelDeriv k (x + h) - riemannKernelDeriv k x -
        (h : ℂ) * riemannKernelDeriv (k + 1) x‖ ≤
          D * Real.exp (-(3 * |x|)) * h ^ 2 := by
  obtain ⟨D, hD, hshift⟩ := exists_riemannKernelDeriv_translation_envelope (k + 1)
  refine ⟨D, hD, ?_⟩
  intro x h hh
  let g (z : ℝ) := riemannKernelDeriv k z -
    ((z - x : ℝ) : ℂ) * riemannKernelDeriv (k + 1) x
  have hg (z : ℝ) : HasDerivAt g
      (riemannKernelDeriv (k + 1) z - riemannKernelDeriv (k + 1) x) z := by
    have hlin := (((hasDerivAt_id z).sub_const x).ofReal_comp).mul_const
      (riemannKernelDeriv (k + 1) x)
    have hs := (hasDerivAt_riemannKernelDeriv k z).sub hlin
    simp only [id_eq, Complex.ofReal_one, one_mul] at hs
    have heq : (riemannKernelDeriv k - fun y : ℝ =>
        ((y - x : ℝ) : ℂ) * riemannKernelDeriv (k + 1) x) = g := by
      funext y
      rfl
    erw [heq] at hs
    exact hs
  have hbound (z : ℝ) (hz : z ∈ Icc (x - |h|) (x + |h|)) :
      ‖riemannKernelDeriv (k + 1) z - riemannKernelDeriv (k + 1) x‖ ≤
        D * Real.exp (-(3 * |x|)) * |h| := by
    have hzx : |z - x| ≤ |h| := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hs := hshift x (z - x) (hzx.trans hh)
    rw [show x + (z - x) = z by ring] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hzx (by positivity))
  have hx : x ∈ Icc (x - |h|) (x + |h|) := by
    constructor <;> linarith [abs_nonneg h]
  have hxh : x + h ∈ Icc (x - |h|) (x + |h|) := by
    constructor <;> linarith [neg_abs_le h, le_abs_self h]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Icc (x - |h|) (x + |h|)) => (hg z).hasDerivWithinAt)
    hbound (convex_Icc (x - |h|) (x + |h|)) hx hxh
  have heq : riemannKernelDeriv k (x + h) - riemannKernelDeriv k x -
      (h : ℂ) * riemannKernelDeriv (k + 1) x = g (x + h) - g x := by
    dsimp only [g]
    simp only [add_sub_cancel_left, sub_self, Complex.ofReal_zero, zero_mul, sub_zero]
    ring
  rw [heq]
  calc
    _ ≤ (D * Real.exp (-(3 * |x|)) * |h|) * |h| := by
      simpa only [add_sub_cancel_left, Real.norm_eq_abs] using hm
    _ = (D * Real.exp (-(3 * |x|))) * |h| ^ 2 := by ring
    _ = _ := by rw [sq_abs]

/-- Cancelling the first moment exposes a quadratic remainder of the actual
real kernel, uniformly over every pair of short translation offsets. -/
theorem exists_riemannKernelReal_balanced_quadratic_envelope :
    ∃ D : ℝ, 0 < D ∧ ∀ x u v a b : ℝ,
      |u| ≤ 1 → |v| ≤ 1 → 0 ≤ a → 0 ≤ b → a * u + b * v = 0 →
        |a * (riemannKernelReal (x + u) - riemannKernelReal x) +
          b * (riemannKernelReal (x + v) - riemannKernelReal x)| ≤
            D * Real.exp (-(3 * |x|)) * (a * u ^ 2 + b * v ^ 2) := by
  obtain ⟨D, hD, hrem⟩ := exists_riemannKernelDeriv_quadratic_remainder_envelope 0
  have hr (x h : ℝ) (hh : |h| ≤ 1) :
      |riemannKernelReal (x + h) - riemannKernelReal x - h * (riemannKernelDeriv 1 x).re| ≤
        D * Real.exp (-(3 * |x|)) * h ^ 2 := by
    have hre := Complex.abs_re_le_norm
      (riemannKernelDeriv 0 (x + h) - riemannKernelDeriv 0 x -
        (h : ℂ) * riemannKernelDeriv 1 x)
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal] at hre
    have hrem' := hrem x h hh
    simp only [riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal] at hrem'
    exact hre.trans hrem'
  refine ⟨D, hD, ?_⟩
  intro x u v a b hu hv ha hb hbal
  let d := (riemannKernelDeriv 1 x).re
  have heq : a * (riemannKernelReal (x + u) - riemannKernelReal x) +
      b * (riemannKernelReal (x + v) - riemannKernelReal x) =
      a * (riemannKernelReal (x + u) - riemannKernelReal x - u * d) +
        b * (riemannKernelReal (x + v) - riemannKernelReal x - v * d) := by
    calc
      _ = a * (riemannKernelReal (x + u) - riemannKernelReal x - u * d) +
          b * (riemannKernelReal (x + v) - riemannKernelReal x - v * d) +
          (a * u + b * v) * d := by ring
      _ = _ := by rw [hbal, zero_mul, add_zero]
  rw [heq]
  calc
    _ ≤ |a * (riemannKernelReal (x + u) - riemannKernelReal x - u * d)| +
        |b * (riemannKernelReal (x + v) - riemannKernelReal x - v * d)| := abs_add_le _ _
    _ = a * |riemannKernelReal (x + u) - riemannKernelReal x - u * d| +
        b * |riemannKernelReal (x + v) - riemannKernelReal x - v * d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (D * Real.exp (-(3 * |x|)) * u ^ 2) +
        b * (D * Real.exp (-(3 * |x|)) * v ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (hr x u hu) ha)
        (mul_le_mul_of_nonneg_left (hr x v hv) hb)
    _ = _ := by ring

/-- Balanced short translations of the actual autocorrelation have a quadratic
variance bound with exponential decay at their common center. -/
theorem exists_riemannAutocorr_balanced_quadratic_envelope :
    ∃ E : ℝ, 0 < E ∧ ∀ y u v a b : ℝ,
      |u| ≤ 1 → |v| ≤ 1 → 0 ≤ a → 0 ≤ b → a * u + b * v = 0 →
        |a * (riemannAutocorr (y + u) - riemannAutocorr y) +
          b * (riemannAutocorr (y + v) - riemannAutocorr y)| ≤
            E * Real.exp (-(2 * |y|)) * (a * u ^ 2 + b * v ^ 2) := by
  obtain ⟨C, hC, hzero⟩ := exists_riemannKernelDeriv_cubic_exp_envelope 0
  obtain ⟨D, hD, hbalanced⟩ := exists_riemannKernelReal_balanced_quadratic_envelope
  have hphi (t : ℝ) : |riemannKernelReal t| ≤ C * Real.exp (-(3 * |t|)) := by
    simpa only [riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal,
      Complex.norm_real, Real.norm_eq_abs] using hzero t
  let I : ℝ := ∫ t : ℝ, Real.exp (-|t|)
  have hI : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨C * D * (I + 1), by positivity, ?_⟩
  intro y u v a b hu hv ha hb hbal
  let R := a * u ^ 2 + b * v ^ 2
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have heq : a * (riemannAutocorr (y + u) - riemannAutocorr y) +
      b * (riemannAutocorr (y + v) - riemannAutocorr y) =
      ∫ t : ℝ, riemannKernelReal t *
        (a * (riemannKernelReal (t - (y + u)) - riemannKernelReal (t - y)) +
          b * (riemannKernelReal (t - (y + v)) - riemannKernelReal (t - y))) := by
    have h0 := integrable_riemannKernelReal_mul y
    have h1 := integrable_riemannKernelReal_mul (y + u)
    have h2 := integrable_riemannKernelReal_mul (y + v)
    calc
      _ = ∫ t : ℝ,
          a * (riemannKernelReal t * riemannKernelReal (t - (y + u)) -
            riemannKernelReal t * riemannKernelReal (t - y)) +
          b * (riemannKernelReal t * riemannKernelReal (t - (y + v)) -
            riemannKernelReal t * riemannKernelReal (t - y)) := by
        erw [integral_add ((h1.sub h0).const_mul a) ((h2.sub h0).const_mul b),
          integral_const_mul, integral_const_mul, integral_sub h1 h0, integral_sub h2 h0]
        rfl
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  have hpoint (t : ℝ) :
      |riemannKernelReal t *
        (a * (riemannKernelReal (t - (y + u)) - riemannKernelReal (t - y)) +
          b * (riemannKernelReal (t - (y + v)) - riemannKernelReal (t - y)))| ≤
      (C * D * R * Real.exp (-(2 * |y|))) * Real.exp (-|t|) := by
    have hs := hbalanced (t - y) (-u) (-v) a b
      (by simpa only [abs_neg] using hu) (by simpa only [abs_neg] using hv) ha hb
      (by nlinarith [hbal])
    rw [show t - y + -u = t - (y + u) by ring,
      show t - y + -v = t - (y + v) by ring,
      show (-u) ^ 2 = u ^ 2 by ring, show (-v) ^ 2 = v ^ 2 by ring] at hs
    have htriangle : |y| ≤ |t| + |t - y| := by
      simpa only [sub_sub_cancel] using abs_sub t (t - y)
    rw [abs_mul]
    calc
      _ ≤ (C * Real.exp (-(3 * |t|))) * (D * Real.exp (-(3 * |t - y|)) * R) :=
        mul_le_mul (hphi t) hs (abs_nonneg _) (by positivity)
      _ = (C * D * R) * Real.exp (-(3 * |t|) - 3 * |t - y|) := by
        simp only [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ (C * D * R) * Real.exp (-(2 * |y|) - |t|) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith [abs_nonneg (t - y)])) (by positivity)
      _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring
  calc
    _ ≤ ∫ t : ℝ, |riemannKernelReal t *
        (a * (riemannKernelReal (t - (y + u)) - riemannKernelReal (t - y)) +
          b * (riemannKernelReal (t - (y + v)) - riemannKernelReal (t - y)))| := by
      rw [heq, ← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (C * D * R * Real.exp (-(2 * |y|))) * Real.exp (-|t|) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_exp_neg_abs.const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = (C * D * R * Real.exp (-(2 * |y|))) * I := by rw [integral_const_mul]
    _ ≤ (C * D * R * Real.exp (-(2 * |y|))) * (I + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by dsimp only [R]; ring

end RHTower
