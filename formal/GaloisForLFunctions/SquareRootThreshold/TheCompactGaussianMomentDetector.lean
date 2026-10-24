import GaloisForLFunctions.SquareRootThreshold.TheCenteredHeatTraceRisesAtEveryOffLineZero
import GaloisForLFunctions.RHTower.XiGaussianHeatTestPhysicalSide
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound

/-!
# The compact Gaussian moment detector

The odd Gaussian `h(x) = e^{−icx} ∂ₓ e^{−bx²}` has the entire transform

  `ĥ(z) = −i(z − c) (π/b)^{1/2} e^{−(z−c)²/(4b)}`      (`paperFT_gaussMomentTest`),

so its Weil summand at a spectral point is `(π/b) (z − c)² e^{−(z−c)²/(2b)}`, a positive multiple of
the heat moment at time `1/(2b)`. The detector actually used is the compact cutoff `f = χ_A h`, where
`χ_A = 1` on `[−A, A]` and `0` off `[−A−1, A+1]` is built from the canonical smooth transition. Two
estimates make the cutoff harmless:

* **Gaussian tail.** On the strip `|Im w| ≤ ½`, `|f̂(w) − ĥ(w)| ≤ (4π/b)^{1/2} e^{−bA²/4}` once
  `A ≥ 3/b` (`norm_paperFT_cutoff_sub_le`).
* **Spectral decay of the cutoff.** `|f̂(w)| ≤ e^{(A+1)/2} 16 (A+1) M (1+|c|)² G / (1 + |Re w|)²`,
  with `G = 12 (4/b)³` bounding the first three Gaussian derivatives and `M` an absolute constant of
  the smooth transition (`norm_paperFT_cutoffMomentTest_le`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower Zeta23

/-! ### The Gaussian derivatives -/

theorem gaussDeriv_one (b x : ℝ) :
    gaussDeriv b 1 x = -(2 * (b : ℂ) * x) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
  simp [gaussDeriv, gaussDerivPoly]

theorem gaussDeriv_two (b x : ℝ) :
    gaussDeriv b 2 x =
      (4 * (b : ℂ) ^ 2 * x ^ 2 - 2 * b) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
  simp [gaussDeriv, gaussDerivPoly]
  ring

theorem gaussDeriv_three (b x : ℝ) :
    gaussDeriv b 3 x =
      (12 * (b : ℂ) ^ 2 * x - 8 * b ^ 3 * x ^ 3) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2) := by
  simp [gaussDeriv, gaussDerivPoly]
  ring

theorem norm_cexp_neg_mul_sq (b x : ℝ) :
    ‖Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)‖ = Real.exp (-(b * x ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two]

/-- The first three Gaussian derivatives are at most `(1 + |x|)³ e^{−bx²}` for `b ≤ 1/4`. -/
theorem norm_gaussDeriv_le {b : ℝ} (hb : 0 < b) (hb4 : b ≤ 1 / 4) {m : ℕ} (hm1 : 1 ≤ m)
    (hm3 : m ≤ 3) (x : ℝ) :
    ‖gaussDeriv b m x‖ ≤ (1 + |x|) ^ 3 * Real.exp (-(b * x ^ 2)) := by
  have hx := abs_nonneg x
  have hxs : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hp : 1 ≤ (1 + |x|) ^ 3 := one_le_pow₀ (by linarith)
  have hcube : |x| ^ 3 ≤ (1 + |x|) ^ 3 := pow_le_pow_left₀ hx (by linarith) 3
  have hsq : |x| ^ 2 ≤ (1 + |x|) ^ 3 := by nlinarith [pow_le_pow_left₀ hx (by linarith : |x| ≤ 1 + |x|) 2]
  have hlin : 1 + |x| ≤ (1 + |x|) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  interval_cases m
  · rw [gaussDeriv_one, norm_mul, norm_cexp_neg_mul_sq]
    gcongr
    have e : -(2 * (b : ℂ) * x) = ((-(2 * b * x) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul,
      abs_of_pos hb, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  · rw [gaussDeriv_two, norm_mul, norm_cexp_neg_mul_sq]
    gcongr
    have e : (4 * (b : ℂ) ^ 2 * x ^ 2 - 2 * b) = ((4 * b ^ 2 * x ^ 2 - 2 * b : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg b]
  · rw [gaussDeriv_three, norm_mul, norm_cexp_neg_mul_sq]
    gcongr
    have e : (12 * (b : ℂ) ^ 2 * x - 8 * b ^ 3 * x ^ 3) =
        ((12 * b ^ 2 * x - 8 * b ^ 3 * x ^ 3 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    have e1 : |12 * b ^ 2 * x| = 12 * b ^ 2 * |x| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 12 * b ^ 2)]
    have e2 : |8 * b ^ 3 * x ^ 3| = 8 * b ^ 3 * |x| ^ 3 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * b ^ 3), abs_pow]
    rw [e1, e2]
    have hb2 : 12 * b ^ 2 ≤ 1 := by nlinarith
    have hb3 : 8 * b ^ 3 ≤ 1 := by nlinarith [pow_le_pow_left₀ hb.le hb4 3]
    have k1 := mul_le_mul_of_nonneg_right hb2 hx
    have k2 := mul_le_mul_of_nonneg_right hb3 (pow_nonneg hx 3)
    nlinarith [sq_nonneg |x|]

/-- The uniform bound `G = 12 (4/b)³` on the first three Gaussian derivatives. -/
def gaussSupBound (b : ℝ) : ℝ := 12 * (4 / b) ^ 3

theorem norm_gaussDeriv_le_sup {b : ℝ} (hb : 0 < b) (hb4 : b ≤ 1 / 4) {m : ℕ} (hm1 : 1 ≤ m)
    (hm3 : m ≤ 3) (x : ℝ) : ‖gaussDeriv b m x‖ ≤ gaussSupBound b := by
  refine (norm_gaussDeriv_le hb hb4 hm1 hm3 x).trans ?_
  have h := one_add_abs_pow_le_exp hb 3 x
  have he : Real.exp (b / 2) ≤ 2 := by
    have : b / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    calc Real.exp (b / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr this
      _ = 2 := Real.exp_log (by norm_num)
  have hmul : Real.exp (b / 2 * x ^ 2) * Real.exp (-(b * x ^ 2)) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h4 : 0 ≤ (4 / b) ^ 3 := by positivity
  calc (1 + |x|) ^ 3 * Real.exp (-(b * x ^ 2))
      ≤ 6 * (4 / b) ^ 3 * Real.exp (b / 2) * Real.exp (b / 2 * x ^ 2) *
          Real.exp (-(b * x ^ 2)) := by gcongr
    _ = 6 * (4 / b) ^ 3 * Real.exp (b / 2) *
          (Real.exp (b / 2 * x ^ 2) * Real.exp (-(b * x ^ 2))) := by ring
    _ ≤ 6 * (4 / b) ^ 3 * 2 * 1 := by gcongr
    _ = gaussSupBound b := by unfold gaussSupBound; ring

/-! ### The Gaussian moment test -/

/-- The odd Gaussian moment test `e^{−icx} ∂ₓ e^{−bx²}`. -/
def gaussMomentTest (b c : ℝ) (x : ℝ) : ℂ := Complex.exp (-(I * c * x)) * gaussDeriv b 1 x

theorem paperFT_gaussMomentTest {b : ℝ} (hb : 0 < b) (c : ℝ) (z : ℂ) :
    paperFT (gaussMomentTest b c) z =
      -(I * (z - c)) * ((π / (b : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (-(z - c) ^ 2 / (4 * b))) := by
  have h := paperFT_modulate (gaussDeriv b 1) c z
  have e : gaussMomentTest b c = fun u : ℝ => Complex.exp (-(I * c * u)) * gaussDeriv b 1 u := rfl
  rw [e, h, paperFT_def, integral_gaussDeriv_mul_cexp hb 1 (z - c), pow_one]

theorem integrable_gaussMomentTest_mul_cexp {b : ℝ} (hb : 0 < b) (c : ℝ) (w : ℂ) :
    Integrable fun u : ℝ => gaussMomentTest b c u * Complex.exp (I * w * u) := by
  have e : ∀ u : ℝ, gaussDeriv b 1 u * Complex.exp (I * (w - c) * u) =
      gaussMomentTest b c u * Complex.exp (I * w * u) := fun u => by
    unfold gaussMomentTest
    rw [mul_comm (Complex.exp _) (gaussDeriv b 1 u), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  exact (integrable_gaussDeriv_mul_cexp hb 1 (w - c)).congr (Eventually.of_forall e)

theorem norm_cexp_I_mul_le {w : ℂ} (hw : |w.im| ≤ 1 / 2) (u : ℝ) :
    ‖Complex.exp (I * w * u)‖ ≤ Real.exp (|u| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have e : (I * w * (u : ℂ)).re = -(w.im * u) := by simp [Complex.mul_re]
  rw [e]
  have := abs_mul w.im u
  have h1 := neg_abs_le (w.im * u)
  have h2 : |w.im| * |u| ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hw (abs_nonneg u)
  linarith

/-! ### The smooth transition and its second derivative -/

theorem hasDerivAt_smoothTransition (y : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition y) y :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem contDiff_deriv_smoothTransition : ContDiff ℝ 1 (deriv Real.smoothTransition) := by
  have h := (Real.smoothTransition.contDiff (n := ((1 + 1 : ℕ) : ℕ∞))).iterate_deriv' 1 1
  simpa using h

theorem hasDerivAt_deriv_smoothTransition (y : ℝ) :
    HasDerivAt (deriv Real.smoothTransition) (deriv (deriv Real.smoothTransition) y) y :=
  (contDiff_deriv_smoothTransition.differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem continuous_deriv_deriv_smoothTransition :
    Continuous (deriv (deriv Real.smoothTransition)) :=
  contDiff_deriv_smoothTransition.continuous_deriv le_rfl

theorem deriv_deriv_smoothTransition_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have hopen : IsOpen (Icc (0 : ℝ) 1)ᶜ := isClosed_Icc.isOpen_compl
  have hev : deriv Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact HTGeometry.deriv_smoothTransition_eq_zero_of_notMem hy
  rw [hev.deriv_eq, deriv_const]

theorem exists_bound_deriv_deriv_smoothTransition :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ Λ := by
  have hcont : ContinuousOn (fun x => |deriv (deriv Real.smoothTransition) x|) (Icc (0 : ℝ) 1) :=
    (continuous_abs.comp continuous_deriv_deriv_smoothTransition).continuousOn
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn ⟨0, by norm_num⟩ hcont
  refine ⟨|deriv (deriv Real.smoothTransition) x₀|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact hmax hx
  · rw [deriv_deriv_smoothTransition_eq_zero_of_notMem hx, abs_zero]
    exact abs_nonneg _

/-- The first derivative bound of the smooth transition. -/
def transitionBound₁ : ℝ := Classical.choose HTGeometry.exists_bound_deriv_smoothTransition

/-- The second derivative bound of the smooth transition. -/
def transitionBound₂ : ℝ := Classical.choose exists_bound_deriv_deriv_smoothTransition

theorem transitionBound₁_spec :
    0 ≤ transitionBound₁ ∧ ∀ x, |deriv Real.smoothTransition x| ≤ transitionBound₁ :=
  Classical.choose_spec HTGeometry.exists_bound_deriv_smoothTransition

theorem transitionBound₂_spec :
    0 ≤ transitionBound₂ ∧ ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ transitionBound₂ :=
  Classical.choose_spec exists_bound_deriv_deriv_smoothTransition

/-- The absolute cutoff constant `M = 2Λ₂ + 2Λ₁² + 4Λ₁ + 2`. -/
def cutoffConstant : ℝ :=
  2 * transitionBound₂ + 2 * transitionBound₁ ^ 2 + 4 * transitionBound₁ + 2

theorem one_le_cutoffConstant : 1 ≤ cutoffConstant := by
  have h1 := transitionBound₁_spec.1
  have h2 := transitionBound₂_spec.1
  unfold cutoffConstant
  nlinarith

/-! ### The cutoff -/

local notation "st" => Real.smoothTransition
local notation "st₁" => deriv Real.smoothTransition
local notation "st₂" => deriv (deriv Real.smoothTransition)

/-- The plateau cutoff `χ_A(x) = ϑ(A + 1 − x) ϑ(A + 1 + x)`: one on `[−A, A]`, zero off
`[−A−1, A+1]`. -/
def plateauCutoff (A x : ℝ) : ℝ := st (A + 1 - x) * st (A + 1 + x)

def plateauCutoff₁ (A x : ℝ) : ℝ := -(st₁ (A + 1 - x) * st (A + 1 + x)) + st (A + 1 - x) * st₁ (A + 1 + x)

def plateauCutoff₂ (A x : ℝ) : ℝ :=
  st₂ (A + 1 - x) * st (A + 1 + x) - 2 * (st₁ (A + 1 - x) * st₁ (A + 1 + x)) +
    st (A + 1 - x) * st₂ (A + 1 + x)

theorem hasDerivAt_sub_affine (A x : ℝ) : HasDerivAt (fun y : ℝ => A + 1 - y) (-1) x := by
  simpa using (hasDerivAt_id x).const_sub (A + 1)

theorem hasDerivAt_add_affine (A x : ℝ) : HasDerivAt (fun y : ℝ => A + 1 + y) 1 x := by
  simpa using (hasDerivAt_id x).const_add (A + 1)

theorem hasDerivAt_plateauCutoff (A x : ℝ) :
    HasDerivAt (plateauCutoff A) (plateauCutoff₁ A x) x := by
  have h1 := (hasDerivAt_smoothTransition (A + 1 - x)).comp x (hasDerivAt_sub_affine A x)
  have h2 := (hasDerivAt_smoothTransition (A + 1 + x)).comp x (hasDerivAt_add_affine A x)
  refine (h1.mul h2).congr_deriv ?_
  simp only [Function.comp_apply, plateauCutoff₁]
  ring

theorem hasDerivAt_plateauCutoff₁ (A x : ℝ) :
    HasDerivAt (plateauCutoff₁ A) (plateauCutoff₂ A x) x := by
  have h0m := (hasDerivAt_smoothTransition (A + 1 - x)).comp x (hasDerivAt_sub_affine A x)
  have h0p := (hasDerivAt_smoothTransition (A + 1 + x)).comp x (hasDerivAt_add_affine A x)
  have h1m := (hasDerivAt_deriv_smoothTransition (A + 1 - x)).comp x (hasDerivAt_sub_affine A x)
  have h1p := (hasDerivAt_deriv_smoothTransition (A + 1 + x)).comp x (hasDerivAt_add_affine A x)
  refine (((h1m.mul h0p).neg).add (h0m.mul h1p)).congr_deriv ?_
  simp only [Function.comp_apply, plateauCutoff₂]
  ring

theorem plateauCutoff_nonneg (A x : ℝ) : 0 ≤ plateauCutoff A x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem plateauCutoff_le_one (A x : ℝ) : plateauCutoff A x ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem plateauCutoff_eq_one {A x : ℝ} (hx : |x| ≤ A) : plateauCutoff A x = 1 := by
  have h := abs_le.mp hx
  unfold plateauCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem plateauCutoff_eq_zero {A x : ℝ} (hx : A + 1 < |x|) : plateauCutoff A x = 0 := by
  unfold plateauCutoff
  rcases lt_abs.mp hx with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (x := A + 1 + x) (by linarith), mul_zero]

theorem abs_plateauCutoff₁_le (A x : ℝ) : |plateauCutoff₁ A x| ≤ 2 * transitionBound₁ := by
  obtain ⟨h0, hb⟩ := transitionBound₁_spec
  have a1 := hb (A + 1 - x)
  have a2 := hb (A + 1 + x)
  have s1 := Real.smoothTransition.nonneg (A + 1 - x)
  have s2 := Real.smoothTransition.nonneg (A + 1 + x)
  have t1 := Real.smoothTransition.le_one (A + 1 - x)
  have t2 := Real.smoothTransition.le_one (A + 1 + x)
  unfold plateauCutoff₁
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg s1, abs_of_nonneg s2]
  nlinarith [abs_nonneg (st₁ (A + 1 - x)), abs_nonneg (st₁ (A + 1 + x))]

theorem abs_plateauCutoff₂_le (A x : ℝ) :
    |plateauCutoff₂ A x| ≤ 2 * transitionBound₂ + 2 * transitionBound₁ ^ 2 := by
  obtain ⟨h0, hb⟩ := transitionBound₁_spec
  obtain ⟨h0', hb'⟩ := transitionBound₂_spec
  have a1 := hb (A + 1 - x)
  have a2 := hb (A + 1 + x)
  have b1 := hb' (A + 1 - x)
  have b2 := hb' (A + 1 + x)
  have s1 := Real.smoothTransition.nonneg (A + 1 - x)
  have s2 := Real.smoothTransition.nonneg (A + 1 + x)
  have t1 := Real.smoothTransition.le_one (A + 1 - x)
  have t2 := Real.smoothTransition.le_one (A + 1 + x)
  have p1 : |st₂ (A + 1 - x) * st (A + 1 + x)| ≤ transitionBound₂ := by
    rw [abs_mul, abs_of_nonneg s2]
    exact (mul_le_of_le_one_right (abs_nonneg _) t2).trans b1
  have p2 : |2 * (st₁ (A + 1 - x) * st₁ (A + 1 + x))| ≤ 2 * transitionBound₁ ^ 2 := by
    rw [abs_mul, abs_mul, abs_two, sq]
    have := mul_le_mul a1 a2 (abs_nonneg _) h0
    linarith
  have p3 : |st (A + 1 - x) * st₂ (A + 1 + x)| ≤ transitionBound₂ := by
    rw [abs_mul, abs_of_nonneg s1]
    exact (mul_le_of_le_one_left (abs_nonneg _) t1).trans b2
  have q1 := abs_add_le (st₂ (A + 1 - x) * st (A + 1 + x) - 2 * (st₁ (A + 1 - x) * st₁ (A + 1 + x)))
    (st (A + 1 - x) * st₂ (A + 1 + x))
  have q2 := abs_sub (st₂ (A + 1 - x) * st (A + 1 + x)) (2 * (st₁ (A + 1 - x) * st₁ (A + 1 + x)))
  unfold plateauCutoff₂
  linarith

theorem continuous_plateauCutoff₂ (A : ℝ) : Continuous (plateauCutoff₂ A) := by
  have c0 : Continuous st := Real.smoothTransition.contDiff (n := 0) |>.continuous
  have c1 : Continuous st₁ := HTGeometry.continuous_deriv_smoothTransition
  have c2 : Continuous st₂ := continuous_deriv_deriv_smoothTransition
  unfold plateauCutoff₂
  fun_prop

/-! ### The compact detector -/

/-- The compact Gaussian moment detector `χ_A · h`. -/
def cutoffMomentTest (A b c : ℝ) (x : ℝ) : ℂ := (plateauCutoff A x : ℂ) * gaussMomentTest b c x

/-- The modulation `e^{−icx}`. -/
def modulation (c x : ℝ) : ℂ := Complex.exp (-(I * c * x))

theorem hasDerivAt_modulation (c x : ℝ) :
    HasDerivAt (modulation c) (modulation c x * (-(I * c))) x := by
  have h0 : HasDerivAt (fun y : ℝ => (-(I * c)) * (y : ℂ)) (-(I * c)) x := by
    have := ((hasDerivAt_id x).ofReal_comp).const_mul (-(I * c))
    simp only [id, Complex.ofReal_one, mul_one] at this
    exact this
  have e : ∀ y : ℝ, Complex.exp (-(I * c) * (y : ℂ)) = modulation c y := fun y => by
    unfold modulation; congr 1; ring
  rw [show modulation c = fun y : ℝ => Complex.exp (-(I * c) * (y : ℂ)) from
    funext fun y => (e y).symm, ← e x]
  exact h0.cexp

/-- `h' = e^{−icx}(−ic g₁ + g₂)`. -/
def gaussMomentTest₁ (b c x : ℝ) : ℂ :=
  modulation c x * (-(I * c) * gaussDeriv b 1 x + gaussDeriv b 2 x)

/-- `h'' = e^{−icx}((−ic)² g₁ + 2(−ic) g₂ + g₃)`. -/
def gaussMomentTest₂ (b c x : ℝ) : ℂ :=
  modulation c x * ((-(I * c)) ^ 2 * gaussDeriv b 1 x + 2 * (-(I * c)) * gaussDeriv b 2 x +
    gaussDeriv b 3 x)

theorem hasDerivAt_gaussMomentTest (b c x : ℝ) :
    HasDerivAt (gaussMomentTest b c) (gaussMomentTest₁ b c x) x := by
  refine ((hasDerivAt_modulation c x).mul (hasDerivAt_gaussDeriv b 1 x)).congr_deriv ?_
  unfold gaussMomentTest₁
  ring

theorem hasDerivAt_gaussMomentTest₁ (b c x : ℝ) :
    HasDerivAt (gaussMomentTest₁ b c) (gaussMomentTest₂ b c x) x := by
  refine ((hasDerivAt_modulation c x).mul
    (((hasDerivAt_gaussDeriv b 1 x).const_mul (-(I * c))).add
      (hasDerivAt_gaussDeriv b 2 x))).congr_deriv ?_
  unfold gaussMomentTest₂
  ring

def cutoffMomentTest₁ (A b c x : ℝ) : ℂ :=
  (plateauCutoff₁ A x : ℂ) * gaussMomentTest b c x + (plateauCutoff A x : ℂ) * gaussMomentTest₁ b c x

def cutoffMomentTest₂ (A b c x : ℝ) : ℂ :=
  (plateauCutoff₂ A x : ℂ) * gaussMomentTest b c x +
    2 * ((plateauCutoff₁ A x : ℂ) * gaussMomentTest₁ b c x) +
      (plateauCutoff A x : ℂ) * gaussMomentTest₂ b c x

theorem hasDerivAt_cutoffMomentTest (A b c x : ℝ) :
    HasDerivAt (cutoffMomentTest A b c) (cutoffMomentTest₁ A b c x) x := by
  exact ((hasDerivAt_plateauCutoff A x).ofReal_comp).mul (hasDerivAt_gaussMomentTest b c x)

theorem hasDerivAt_cutoffMomentTest₁ (A b c x : ℝ) :
    HasDerivAt (cutoffMomentTest₁ A b c) (cutoffMomentTest₂ A b c x) x := by
  have h1 := ((hasDerivAt_plateauCutoff₁ A x).ofReal_comp).mul (hasDerivAt_gaussMomentTest b c x)
  have h2 := ((hasDerivAt_plateauCutoff A x).ofReal_comp).mul (hasDerivAt_gaussMomentTest₁ b c x)
  refine (h1.add h2).congr_deriv ?_
  unfold cutoffMomentTest₂
  ring

theorem deriv_cutoffMomentTest (A b c : ℝ) :
    deriv (cutoffMomentTest A b c) = cutoffMomentTest₁ A b c :=
  funext fun x => (hasDerivAt_cutoffMomentTest A b c x).deriv

theorem deriv_deriv_cutoffMomentTest (A b c : ℝ) :
    deriv (deriv (cutoffMomentTest A b c)) = cutoffMomentTest₂ A b c := by
  rw [deriv_cutoffMomentTest]
  exact funext fun x => (hasDerivAt_cutoffMomentTest₁ A b c x).deriv

theorem continuous_gaussDeriv (b : ℝ) (m : ℕ) : Continuous (gaussDeriv b m) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gaussDeriv b m x).continuousAt

theorem continuous_modulation (c : ℝ) : Continuous (modulation c) := by
  unfold modulation; fun_prop

theorem continuous_cutoffMomentTest₂ (A b c : ℝ) : Continuous (cutoffMomentTest₂ A b c) := by
  have c0 : Continuous (plateauCutoff A) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_plateauCutoff A x).continuousAt
  have c1 : Continuous (plateauCutoff₁ A) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_plateauCutoff₁ A x).continuousAt
  have c2 := continuous_plateauCutoff₂ A
  have g1 := continuous_gaussDeriv b 1
  have g2 := continuous_gaussDeriv b 2
  have g3 := continuous_gaussDeriv b 3
  have hm := continuous_modulation c
  have hh : Continuous (gaussMomentTest b c) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gaussMomentTest b c x).continuousAt
  have hh1 : Continuous (gaussMomentTest₁ b c) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gaussMomentTest₁ b c x).continuousAt
  have hh2 : Continuous (gaussMomentTest₂ b c) := by
    unfold gaussMomentTest₂
    exact hm.mul (((continuous_const.mul g1).add (continuous_const.mul g2)).add g3)
  unfold cutoffMomentTest₂
  exact (((Complex.continuous_ofReal.comp c2).mul hh).add
    (continuous_const.mul ((Complex.continuous_ofReal.comp c1).mul hh1))).add
      ((Complex.continuous_ofReal.comp c0).mul hh2)

theorem contDiff_cutoffMomentTest (A b c : ℝ) : ContDiff ℝ 2 (cutoffMomentTest A b c) := by
  have hd : Differentiable ℝ (cutoffMomentTest A b c) := fun x =>
    (hasDerivAt_cutoffMomentTest A b c x).differentiableAt
  have hd1 : Differentiable ℝ (cutoffMomentTest₁ A b c) := fun x =>
    (hasDerivAt_cutoffMomentTest₁ A b c x).differentiableAt
  have h1 : ContDiff ℝ 1 (deriv (cutoffMomentTest A b c)) := by
    rw [deriv_cutoffMomentTest, contDiff_one_iff_deriv]
    refine ⟨hd1, ?_⟩
    rw [show deriv (cutoffMomentTest₁ A b c) = cutoffMomentTest₂ A b c from
      funext fun x => (hasDerivAt_cutoffMomentTest₁ A b c x).deriv]
    exact continuous_cutoffMomentTest₂ A b c
  exact contDiff_succ_iff_deriv.mpr ⟨hd, by simp, h1⟩

theorem cutoffMomentTest_eq_zero {A b c x : ℝ} (hx : A + 1 < |x|) : cutoffMomentTest A b c x = 0 := by
  rw [cutoffMomentTest, plateauCutoff_eq_zero hx]
  simp

theorem cutoffMomentTest_supp {A b c : ℝ} :
    ∀ u, cutoffMomentTest A b c u ≠ 0 → |u| ≤ A + 1 := fun u hu => by
  by_contra h
  exact hu (cutoffMomentTest_eq_zero (not_le.mp h))

/-! ### Sup bounds of the detector -/

theorem norm_modulation (c x : ℝ) : ‖modulation c x‖ = 1 := by
  rw [modulation, Complex.norm_exp]
  simp [Complex.mul_re]

theorem norm_gaussMomentTest_le {b : ℝ} (hb : 0 < b) (hb4 : b ≤ 1 / 4) (c x : ℝ) :
    ‖gaussMomentTest b c x‖ ≤ gaussSupBound b := by
  have e : gaussMomentTest b c x = modulation c x * gaussDeriv b 1 x := rfl
  rw [e, norm_mul, norm_modulation, one_mul]
  exact norm_gaussDeriv_le_sup hb hb4 le_rfl (by norm_num) x

theorem norm_cutoffMomentTest_le {A b : ℝ} (hb : 0 < b) (hb4 : b ≤ 1 / 4) (c x : ℝ) :
    ‖cutoffMomentTest A b c x‖ ≤ gaussSupBound b := by
  rw [cutoffMomentTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (plateauCutoff_nonneg A x)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (plateauCutoff_le_one A x)).trans
    (norm_gaussMomentTest_le hb hb4 c x)

theorem norm_cutoffMomentTest₂_le {A b : ℝ} (hb : 0 < b) (hb4 : b ≤ 1 / 4) (c x : ℝ) :
    ‖cutoffMomentTest₂ A b c x‖ ≤ cutoffConstant * (1 + |c|) ^ 2 * gaussSupBound b := by
  have G1 := norm_gaussDeriv_le_sup hb hb4 (m := 1) le_rfl (by norm_num) x
  have G2 := norm_gaussDeriv_le_sup hb hb4 (m := 2) (by norm_num) (by norm_num) x
  have G3 := norm_gaussDeriv_le_sup hb hb4 (m := 3) (by norm_num) le_rfl x
  set G := gaussSupBound b
  have hG : 0 ≤ G := le_trans (norm_nonneg _) G1
  have hIc : ‖-(I * (c : ℂ))‖ = |c| := by simp
  have hh : ‖gaussMomentTest b c x‖ ≤ G := norm_gaussMomentTest_le hb hb4 c x
  have hh1 : ‖gaussMomentTest₁ b c x‖ ≤ (1 + |c|) * G := by
    rw [gaussMomentTest₁, norm_mul, norm_modulation, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hIc]
    nlinarith [abs_nonneg c]
  have hh2 : ‖gaussMomentTest₂ b c x‖ ≤ (1 + |c|) ^ 2 * G := by
    rw [gaussMomentTest₂, norm_mul, norm_modulation, one_mul]
    have n1 : ‖(-(I * (c : ℂ))) ^ 2 * gaussDeriv b 1 x‖ ≤ |c| ^ 2 * G := by
      rw [norm_mul, norm_pow, hIc]; exact mul_le_mul_of_nonneg_left G1 (sq_nonneg _)
    have n2 : ‖2 * (-(I * (c : ℂ))) * gaussDeriv b 2 x‖ ≤ 2 * |c| * G := by
      rw [norm_mul, norm_mul, hIc, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left G2 (by positivity)
    refine norm_add₃_le.trans ?_
    nlinarith [abs_nonneg c]
  have k0 : |plateauCutoff A x| ≤ 1 := by
    rw [abs_of_nonneg (plateauCutoff_nonneg A x)]; exact plateauCutoff_le_one A x
  have k1 := abs_plateauCutoff₁_le A x
  have k2 := abs_plateauCutoff₂_le A x
  have hB1 := transitionBound₁_spec.1
  have hB2 := transitionBound₂_spec.1
  have hc1 : 1 ≤ 1 + |c| := by linarith [abs_nonneg c]
  rw [cutoffMomentTest₂]
  refine norm_add₃_le.trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_ofNat]
  have t1 : |plateauCutoff₂ A x| * ‖gaussMomentTest b c x‖ ≤
      (2 * transitionBound₂ + 2 * transitionBound₁ ^ 2) * G :=
    mul_le_mul k2 hh (norm_nonneg _) (by positivity)
  have t2 : |plateauCutoff₁ A x| * ‖gaussMomentTest₁ b c x‖ ≤
      (2 * transitionBound₁) * ((1 + |c|) * G) :=
    mul_le_mul k1 hh1 (norm_nonneg _) (by positivity)
  have t3 : |plateauCutoff A x| * ‖gaussMomentTest₂ b c x‖ ≤ 1 * ((1 + |c|) ^ 2 * G) :=
    mul_le_mul k0 hh2 (norm_nonneg _) zero_le_one
  have hsq : 1 + |c| ≤ (1 + |c|) ^ 2 := by nlinarith
  unfold cutoffConstant
  nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hB1 hG),
    mul_le_mul_of_nonneg_right (one_le_pow₀ hc1 : (1 : ℝ) ≤ (1 + |c|) ^ 2)
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * transitionBound₂ + 2 * transitionBound₁ ^ 2) hG)]

/-! ### Transform estimates -/

/-- A function bounded by `K` and supported in `[−a, a]` has `L¹` norm at most `2aK`. -/
theorem integral_norm_le_of_supp {φ : ℝ → ℂ} {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) (hb : ∀ u, ‖φ u‖ ≤ K) :
    ∫ u, ‖φ u‖ ≤ 2 * a * K := by
  have hint : Integrable ((Icc (-a) a).indicator fun _ : ℝ => K) :=
    (continuous_const.integrableOn_Icc (μ := volume)).integrable_indicator measurableSet_Icc
  have hle : ∀ u, ‖φ u‖ ≤ (Icc (-a) a).indicator (fun _ : ℝ => K) u := fun u => by
    by_cases hu : u ∈ Icc (-a) a
    · rw [indicator_of_mem hu]; exact hb u
    · rw [indicator_of_notMem hu]
      have : φ u = 0 := by
        by_contra h
        exact hu (abs_le.mp (hsupp u h))
      rw [this, norm_zero]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
    (Eventually.of_forall hle)).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul]
  ring

/-- **Spectral decay of the detector.** -/
theorem norm_paperFT_cutoffMomentTest_le {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hb4 : b ≤ 1 / 4)
    (c : ℝ) (w : ℂ) :
    ‖paperFT (cutoffMomentTest A b c) w‖ ≤
      Real.exp (|w.im| * (A + 1)) *
        (16 * (A + 1) * cutoffConstant * (1 + |c|) ^ 2 * gaussSupBound b) / (1 + |w.re|) ^ 2 := by
  have h := norm_paperFT_le_decay (contDiff_cutoffMomentTest A b c) cutoffMomentTest_supp w
  rw [deriv_deriv_cutoffMomentTest] at h
  have hG : 0 ≤ gaussSupBound b := by unfold gaussSupBound; positivity
  have hM := one_le_cutoffConstant
  have hc : 1 ≤ (1 + |c|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg c])
  have i0 := integral_norm_le_of_supp (a := A + 1) (K := gaussSupBound b) (by linarith) hG
    cutoffMomentTest_supp (norm_cutoffMomentTest_le hb hb4 c)
  have hsupp₂ : ∀ u, cutoffMomentTest₂ A b c u ≠ 0 → |u| ≤ A + 1 := fun u hu => by
    by_contra hgt
    apply hu
    have h0 : ∀ y, A + 1 < |y| → cutoffMomentTest A b c y = 0 := fun y hy =>
      cutoffMomentTest_eq_zero hy
    have hopen : IsOpen {y : ℝ | A + 1 < |y|} := isOpen_lt continuous_const continuous_abs
    have hev : cutoffMomentTest A b c =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds (not_le.mp hgt)] with y hy
      exact h0 y hy
    have hev' : deriv (cutoffMomentTest A b c) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [hev.eventuallyEq_nhds] with y hy
      rw [hy.deriv_eq, deriv_const]
    rw [← deriv_deriv_cutoffMomentTest, hev'.deriv_eq, deriv_const]
  have i2 := integral_norm_le_of_supp (a := A + 1)
    (K := cutoffConstant * (1 + |c|) ^ 2 * gaussSupBound b) (by linarith) (by positivity) hsupp₂
    (norm_cutoffMomentTest₂_le (A := A) hb hb4 c)
  refine h.trans ?_
  have hE : 0 ≤ Real.exp (|w.im| * (A + 1)) := (Real.exp_pos _).le
  have hden : 0 < (1 + |w.re|) ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right hden]
  refine mul_le_mul_of_nonneg_left ?_ hE
  have hsum : (∫ u, ‖cutoffMomentTest A b c u‖) + ∫ u, ‖cutoffMomentTest₂ A b c u‖ ≤
      4 * (A + 1) * cutoffConstant * (1 + |c|) ^ 2 * gaussSupBound b := by
    have : 2 * (A + 1) * gaussSupBound b ≤
        2 * (A + 1) * (cutoffConstant * (1 + |c|) ^ 2 * gaussSupBound b) := by
      gcongr
      nlinarith [mul_le_mul hM hc zero_le_one (by linarith)]
    nlinarith
  linarith

/-- **The cutoff costs a Gaussian tail.** On the strip `|Im w| ≤ ½`, for `A ≥ 3/b`,
`|f̂(w) − ĥ(w)| ≤ (4π/b)^{1/2} e^{−bA²/4}`. -/
theorem norm_paperFT_cutoff_sub_le {A b : ℝ} (hb : 0 < b) (hA : 3 / b ≤ A) (c : ℝ) {w : ℂ}
    (hw : |w.im| ≤ 1 / 2) :
    ‖paperFT (cutoffMomentTest A b c) w - paperFT (gaussMomentTest b c) w‖ ≤
      Real.sqrt (Real.pi / (b / 4)) * Real.exp (-(b * A ^ 2 / 4)) := by
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hf : Integrable fun u : ℝ => cutoffMomentTest A b c u * Complex.exp (I * w * u) :=
    ((contDiff_cutoffMomentTest A b c).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs cutoffMomentTest_supp).mul_right
  have hh := integrable_gaussMomentTest_mul_cexp hb c w
  rw [paperFT_def, paperFT_def, ← integral_sub hf hh]
  have hb4 : 0 < b / 4 := by positivity
  have hg : Integrable fun u : ℝ =>
      Real.exp (-(b * A ^ 2 / 4)) * Real.exp (-(b / 4) * u ^ 2) :=
    (integrable_exp_neg_mul_sq hb4).const_mul _
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) hg (Eventually.of_forall fun u => ?_)).trans
      (le_of_eq ?_))
  · beta_reduce
    rw [← sub_mul, norm_mul]
    by_cases hu : |u| ≤ A
    · have e : cutoffMomentTest A b c u - gaussMomentTest b c u = 0 := by
        rw [cutoffMomentTest, plateauCutoff_eq_one hu]; simp
      rw [e, norm_zero, zero_mul]
      positivity
    · have hu' : A < |u| := not_le.mp hu
      have hdiff : ‖cutoffMomentTest A b c u - gaussMomentTest b c u‖ ≤
          ‖gaussMomentTest b c u‖ := by
        have e : cutoffMomentTest A b c u - gaussMomentTest b c u =
            ((plateauCutoff A u - 1 : ℝ) : ℂ) * gaussMomentTest b c u := by
          rw [cutoffMomentTest]; push_cast; ring
        rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h0 := plateauCutoff_nonneg A u
        have h1 := plateauCutoff_le_one A u
        rw [abs_of_nonpos (by linarith)]
        exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
      have hgm : ‖gaussMomentTest b c u‖ ≤ 2 * b * |u| * Real.exp (-(b * u ^ 2)) := by
        have e : gaussMomentTest b c u = modulation c u * gaussDeriv b 1 u := rfl
        rw [e, norm_mul, norm_modulation, one_mul, gaussDeriv_one, norm_mul, norm_cexp_neg_mul_sq,
          norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb]
      have hexp := norm_cexp_I_mul_le hw u
      -- `|u| e^{|u|/2} ≤ e^{bu²/2}` for `|u| ≥ 3/b`, and `bA² ≤ bu²`
      have hy : 3 / b ≤ |u| := hA.trans hu'.le
      have hlog : Real.log (2 * b * |u|) + |u| / 2 ≤ b * u ^ 2 / 2 := by
        have h1 : Real.log (2 * b * |u|) ≤ 2 * b * |u| := by
          have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * b * |u|)
          linarith
        have hbu : 3 ≤ b * |u| := by rwa [div_le_iff₀ hb, mul_comm] at hy
        have hb1 : 2 * b * |u| ≤ |u| := by
          have : b ≤ 1 / 2 := by
            by_contra hbig
            have : 3 / b < 6 := by rw [div_lt_iff₀ hb]; linarith
            linarith [abs_nonneg u, hA0]
          nlinarith [abs_nonneg u]
        have hsq : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
        rw [hsq]
        nlinarith [abs_nonneg u]
      have hpos : 0 < 2 * b * |u| := by
        have : 0 < |u| := lt_of_lt_of_le hA0 hu'.le
        positivity
      have hA2 : A ^ 2 ≤ u ^ 2 := by
        rw [← sq_abs u]; exact pow_le_pow_left₀ hA0.le hu'.le 2
      calc ‖cutoffMomentTest A b c u - gaussMomentTest b c u‖ * ‖Complex.exp (I * w * u)‖
          ≤ (2 * b * |u| * Real.exp (-(b * u ^ 2))) * Real.exp (|u| / 2) :=
            mul_le_mul (hdiff.trans hgm) hexp (norm_nonneg _) (by positivity)
        _ = Real.exp (Real.log (2 * b * |u|) + |u| / 2 - b * u ^ 2) := by
            rw [Real.exp_sub, Real.exp_add, Real.exp_log hpos, Real.exp_neg]; ring
        _ ≤ Real.exp (-(b * A ^ 2 / 4) + -(b / 4) * u ^ 2) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_le_mul_of_nonneg_left hA2 hb.le]
        _ = Real.exp (-(b * A ^ 2 / 4)) * Real.exp (-(b / 4) * u ^ 2) := Real.exp_add _ _
  · rw [integral_const_mul, integral_gaussian]
    ring

end GaloisForLFunctions.SquareRootThreshold
