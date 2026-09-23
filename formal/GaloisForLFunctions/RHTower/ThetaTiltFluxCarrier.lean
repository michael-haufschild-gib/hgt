import GaloisForLFunctions.RHTower.XiBezoutianPointedIncidence
import GaloisForLFunctions.RHTower.WeightedLaplaceShift
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# The critical tilt flux of a one-sided theta correlation is the Xi Bezoutian form

Let `k` be an even, superexponentially decaying kernel and let

`X(w) = ∫ k(x) e^{w x} dx`

be its bilateral Laplace transform, an entire function.  For a finite exponential packet
`Φ(x) = ∑_j c_j e^{w_j x}` with `Re w_j > 0` and a real tilt `a`, put

`(W_a Φ)(s) = ∫ e^{a(x+s)} k(x+s) Φ(x) dx`,   `J_Φ(a) = ‖W_a Φ‖²_{L²(0,∞)}`.

The change of variable `y = x + s` gives `(W_a Φ)(s) = ∑_j c_j X(w_j + a) e^{-w_j s}`, hence

`J_Φ(a) = ∑_{j,l} c_j conj(c_l) X(w_j + a) conj(X(w_l + a)) / (w_j + conj w_l)`,

and differentiating the finite sum at `a = 0` produces exactly the Bezoutian form

`J_Φ'(0) = ∑_{j,l} c_j conj(c_l) (X'(w_j) conj(X(w_l)) + X(w_j) conj(X'(w_l))) / (w_j + conj w_l)`.

For the completed Riemann source `X = ξ(1/2 + ·)` this quadratic form is the corpus's centred Xi
Bezoutian, so nonnegativity of the critical tilt flux on every finite Euler packet is exactly the
Riemann hypothesis.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace RHTower

noncomputable section

/-! ## The source kernel -/

/-- An even, positive, continuous kernel decaying faster than every exponential. -/
structure ThetaSource where
  k : ℝ → ℝ
  pos : ∀ x, 0 < k x
  even' : ∀ x, k (-x) = k x
  cont : Continuous k
  decay : ∀ M : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ x, k x ≤ C * Real.exp (-(M * |x|))

variable (S : ThetaSource)

theorem ThetaSource.norm_le {M : ℝ} (S : ThetaSource) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖(S.k x : ℂ)‖ ≤ C * Real.exp (-(M * |x|)) := by
  obtain ⟨C, hC, hbd⟩ := S.decay M
  refine ⟨C, hC, fun x => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.pos x)]
  exact hbd x

/-- A single decaying majorant works uniformly on a unit ball of frequencies. -/
theorem ThetaSource.exists_ball_bound (S : ThetaSource) (w : ℂ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, ‖u - w‖ ≤ 1 → ∀ x : ℝ,
      ‖(x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (u * (x : ℂ))‖
        ≤ C * (|x| ^ m * Real.exp (-1 * |x|)) := by
  obtain ⟨C, hC, hbd⟩ := S.decay (|w.re| + 2)
  refine ⟨C, hC, fun u hu x => ?_⟩
  have hure : |u.re| ≤ |w.re| + 1 := by
    have h1 : |u.re - w.re| ≤ 1 := le_trans (by simpa using Complex.abs_re_le_norm (u - w)) hu
    have h2 : |w.re| - |u.re| ≤ |u.re - w.re| := by
      rw [abs_sub_comm]
      exact abs_sub_abs_le_abs_sub _ _
    have h3 : |u.re| - |w.re| ≤ |u.re - w.re| := abs_sub_abs_le_abs_sub _ _
    linarith
  have hexp : ‖Complex.exp (u * (x : ℂ))‖ = Real.exp (u.re * x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hpow : ‖(x : ℂ) ^ m‖ = |x| ^ m := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hknorm : ‖(S.k x : ℂ)‖ = S.k x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.pos x)]
  have hexple : Real.exp (u.re * x) ≤ Real.exp ((|w.re| + 1) * |x|) := by
    refine Real.exp_le_exp.mpr ?_
    calc u.re * x ≤ |u.re * x| := le_abs_self _
      _ = |u.re| * |x| := abs_mul _ _
      _ ≤ (|w.re| + 1) * |x| := mul_le_mul_of_nonneg_right hure (abs_nonneg x)
  have hcollapse : C * Real.exp (-((|w.re| + 2) * |x|)) * Real.exp ((|w.re| + 1) * |x|)
      = C * Real.exp (-1 * |x|) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [norm_mul, norm_mul, hpow, hexp, hknorm]
  have hstep : |x| ^ m * S.k x * Real.exp (u.re * x)
      ≤ |x| ^ m * (C * Real.exp (-((|w.re| + 2) * |x|))) * Real.exp ((|w.re| + 1) * |x|) := by
    refine mul_le_mul ?_ hexple (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left (hbd x) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  calc |x| ^ m * (C * Real.exp (-((|w.re| + 2) * |x|))) * Real.exp ((|w.re| + 1) * |x|)
      = |x| ^ m * (C * Real.exp (-((|w.re| + 2) * |x|)) * Real.exp ((|w.re| + 1) * |x|)) := by ring
    _ = |x| ^ m * (C * Real.exp (-1 * |x|)) := by rw [hcollapse]
    _ = C * (|x| ^ m * Real.exp (-1 * |x|)) := by ring

theorem ThetaSource.continuous_integrand (S : ThetaSource) (u : ℂ) (m : ℕ) :
    Continuous fun x : ℝ => (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (u * (x : ℂ)) :=
  (((continuous_pow m).comp Complex.continuous_ofReal).mul
    (Complex.continuous_ofReal.comp S.cont)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

theorem ThetaSource.integrable_mul_exp (S : ThetaSource) (w : ℂ) (m : ℕ) :
    Integrable fun x : ℝ => (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (w * (x : ℂ)) := by
  obtain ⟨C, hC, hbd⟩ := S.exists_ball_bound w m
  refine Integrable.mono' (g := fun x : ℝ => C * (|x| ^ m * Real.exp (-1 * |x|)))
    ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs m one_pos).const_mul C)
    (S.continuous_integrand w m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hbd w (by simp) x)

/-- **Equation (1).**  The bilateral Laplace transform of the source. -/
def bilateralLaplace (S : ThetaSource) (w : ℂ) : ℂ :=
  ∫ x : ℝ, (S.k x : ℂ) * Complex.exp (w * (x : ℂ))

/-- Its formal derivative, the first moment transform. -/
def bilateralLaplaceDeriv (S : ThetaSource) (w : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * (S.k x : ℂ) * Complex.exp (w * (x : ℂ))

theorem integrable_bilateralLaplace (S : ThetaSource) (w : ℂ) :
    Integrable fun x : ℝ => (S.k x : ℂ) * Complex.exp (w * (x : ℂ)) := by
  refine (S.integrable_mul_exp w 0).congr (Filter.Eventually.of_forall fun x => ?_)
  simp

theorem bilateralLaplace_conj (S : ThetaSource) (w : ℂ) :
    conj (bilateralLaplace S w) = bilateralLaplace S (conj w) := by
  rw [bilateralLaplace, bilateralLaplace, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

/-! ## Analyticity of the transform -/

theorem ThetaSource.continuous_laplace_integrand (S : ThetaSource) (u : ℂ) :
    Continuous fun x : ℝ => (S.k x : ℂ) * Complex.exp (u * (x : ℂ)) :=
  (Complex.continuous_ofReal.comp S.cont).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

theorem ThetaSource.continuous_moment_integrand (S : ThetaSource) (u : ℂ) :
    Continuous fun x : ℝ => (x : ℂ) * (S.k x : ℂ) * Complex.exp (u * (x : ℂ)) :=
  (Complex.continuous_ofReal.mul (Complex.continuous_ofReal.comp S.cont)).mul
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

theorem hasDerivAt_laplace_integrand (S : ThetaSource) (x : ℝ) (u : ℂ) :
    HasDerivAt (fun u : ℂ => (S.k x : ℂ) * Complex.exp (u * (x : ℂ)))
      ((x : ℂ) * (S.k x : ℂ) * Complex.exp (u * (x : ℂ))) u := by
  have h1 : HasDerivAt (fun u : ℂ => u * (x : ℂ)) ((x : ℂ)) u := by
    simpa using (hasDerivAt_id u).mul_const ((x : ℂ))
  have h2 := (h1.cexp).const_mul ((S.k x : ℂ))
  refine h2.congr_deriv ?_
  ring

/-- **The transform is entire**, with derivative the first moment transform. -/
theorem hasDerivAt_bilateralLaplace (S : ThetaSource) (w : ℂ) :
    HasDerivAt (bilateralLaplace S) (bilateralLaplaceDeriv S w) w := by
  obtain ⟨C, hC, hbd⟩ := S.exists_ball_bound w 1
  have hbd' : ∀ u : ℂ, ‖u - w‖ ≤ 1 → ∀ x : ℝ,
      ‖(x : ℂ) * (S.k x : ℂ) * Complex.exp (u * (x : ℂ))‖
        ≤ C * (|x| ^ (1 : ℕ) * Real.exp (-1 * |x|)) := by
    intro u hu x
    simpa only [pow_one] using hbd u hu x
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (u : ℂ) (x : ℝ) => (S.k x : ℂ) * Complex.exp (u * (x : ℂ)))
    (F' := fun (u : ℂ) (x : ℝ) => (x : ℂ) * (S.k x : ℂ) * Complex.exp (u * (x : ℂ)))
    (x₀ := w) (bound := fun x : ℝ => C * (|x| ^ (1 : ℕ) * Real.exp (-1 * |x|)))
    (μ := volume)
    (Metric.ball_mem_nhds w one_pos)
    (Filter.Eventually.of_forall fun u => (S.continuous_laplace_integrand u).aestronglyMeasurable)
    (integrable_bilateralLaplace S w)
    (S.continuous_moment_integrand w).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x u hu =>
      hbd' u (le_of_lt (by simpa [Complex.dist_eq] using hu)) x)
    ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 one_pos).const_mul C)
    (Filter.Eventually.of_forall fun x u _ => hasDerivAt_laplace_integrand S x u)
  exact hres.2

theorem differentiable_bilateralLaplace (S : ThetaSource) :
    Differentiable ℂ (bilateralLaplace S) :=
  fun w => (hasDerivAt_bilateralLaplace S w).differentiableAt

theorem deriv_bilateralLaplace (S : ThetaSource) (w : ℂ) :
    deriv (bilateralLaplace S) w = bilateralLaplaceDeriv S w :=
  (hasDerivAt_bilateralLaplace S w).deriv

/-! ## The tilted one-sided correlation window -/

/-- **Equation (2).**  A finite exponential packet. -/
def expPacketFn {d : ℕ} (c w : Fin d → ℂ) (x : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (w j * (x : ℂ))

/-- **Equation (3).**  The tilted one-sided correlation window. -/
def tiltWindow (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (a s : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((a : ℂ) * ((x : ℂ) + (s : ℂ))) * (S.k (x + s) : ℂ) * expPacketFn c w x

/-- The translated integrand of a single mode. -/
def tiltModeShift (S : ThetaSource) (w : ℂ) (a s : ℝ) (y : ℝ) : ℂ :=
  Complex.exp ((a : ℂ) * (y : ℂ)) * (S.k y : ℂ) * Complex.exp (w * ((y : ℂ) - (s : ℂ)))

theorem tiltModeShift_apply (S : ThetaSource) (w : ℂ) (a s : ℝ) (x : ℝ) :
    tiltModeShift S w a s (x + s)
      = Complex.exp ((a : ℂ) * ((x : ℂ) + (s : ℂ))) * (S.k (x + s) : ℂ)
        * Complex.exp (w * (x : ℂ)) := by
  rw [tiltModeShift]
  push_cast
  ring_nf

theorem tiltModeShift_eq (S : ThetaSource) (w : ℂ) (a s : ℝ) (y : ℝ) :
    tiltModeShift S w a s y
      = Complex.exp (-w * (s : ℂ))
        * ((S.k y : ℂ) * Complex.exp ((w + (a : ℂ)) * (y : ℂ))) := by
  have h1 : Complex.exp ((a : ℂ) * (y : ℂ)) * Complex.exp (w * (y : ℂ))
      = Complex.exp ((w + (a : ℂ)) * (y : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h2 : Complex.exp (w * ((y : ℂ) - (s : ℂ)))
      = Complex.exp (w * (y : ℂ)) * Complex.exp (-w * (s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [tiltModeShift, h2, ← h1]
  ring

theorem integrable_tiltModeShift (S : ThetaSource) (w : ℂ) (a s : ℝ) :
    Integrable (tiltModeShift S w a s) := by
  refine ((integrable_bilateralLaplace S (w + (a : ℂ))).const_mul
    (Complex.exp (-w * (s : ℂ)))).congr (Filter.Eventually.of_forall fun y => ?_)
  rw [tiltModeShift_eq]

theorem integrable_tilt_single (S : ThetaSource) (w : ℂ) (a s : ℝ) :
    Integrable fun x : ℝ => Complex.exp ((a : ℂ) * ((x : ℂ) + (s : ℂ))) * (S.k (x + s) : ℂ)
      * Complex.exp (w * (x : ℂ)) := by
  refine ((integrable_tiltModeShift S w a s).comp_add_right s).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact tiltModeShift_apply S w a s x

theorem integral_tilt_single (S : ThetaSource) (w : ℂ) (a s : ℝ) :
    (∫ x : ℝ, Complex.exp ((a : ℂ) * ((x : ℂ) + (s : ℂ))) * (S.k (x + s) : ℂ)
        * Complex.exp (w * (x : ℂ)))
      = bilateralLaplace S (w + (a : ℂ)) * Complex.exp (-w * (s : ℂ)) := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (tiltModeShift_apply S w a s x).symm),
    MeasureTheory.integral_add_right_eq_self (tiltModeShift S w a s) s,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (tiltModeShift_eq S w a s)),
    MeasureTheory.integral_const_mul, bilateralLaplace]
  ring

/-- **Equation (5).**  After the change of variable `y = x + s` the window is a finite exponential
sum whose amplitudes are the tilted transform values. -/
theorem tiltWindow_eq (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (a s : ℝ) :
    tiltWindow S c w a s
      = ∑ j, c j * bilateralLaplace S (w j + (a : ℂ)) * Complex.exp (-(w j) * (s : ℂ)) := by
  have hcongr : ∀ x : ℝ,
      Complex.exp ((a : ℂ) * ((x : ℂ) + (s : ℂ))) * (S.k (x + s) : ℂ) * expPacketFn c w x
        = ∑ j, c j * (Complex.exp ((a : ℂ) * ((x : ℂ) + (s : ℂ))) * (S.k (x + s) : ℂ)
            * Complex.exp (w j * (x : ℂ))) := by
    intro x
    rw [expPacketFn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [tiltWindow, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_finsetSum _
      (fun j _ => (integrable_tilt_single S (w j) a s).const_mul (c j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_tilt_single]
  ring

/-! ## The tilt correlation energy -/

/-- **Equation (4).**  The one-sided correlation energy of the tilted window. -/
def tiltCorrelation (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (a : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), ‖tiltWindow S c w a s‖ ^ (2 : ℕ)

/-- **Equation (8).**  The closed form of the correlation energy. -/
def tiltCorrelationForm (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (a : ℝ) : ℂ :=
  ∑ j, ∑ l, c j * conj (c l)
    * (bilateralLaplace S (w j + (a : ℂ)) * conj (bilateralLaplace S (w l + (a : ℂ))))
    / (w j + conj (w l))

theorem tiltWindow_mul_conj (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (a s : ℝ) :
    tiltWindow S c w a s * conj (tiltWindow S c w a s)
      = ∑ j, ∑ l, (c j * conj (c l)
          * (bilateralLaplace S (w j + (a : ℂ)) * conj (bilateralLaplace S (w l + (a : ℂ)))))
          * Complex.exp (-((w j + conj (w l)) * (s : ℂ))) := by
  rw [tiltWindow_eq, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have hconj : conj (c l * bilateralLaplace S (w l + (a : ℂ)) * Complex.exp (-(w l) * (s : ℂ)))
      = conj (c l) * conj (bilateralLaplace S (w l + (a : ℂ)))
        * Complex.exp (-(conj (w l)) * (s : ℂ)) := by
    rw [map_mul, map_mul, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]
  have hexp : Complex.exp (-(w j) * (s : ℂ)) * Complex.exp (-(conj (w l)) * (s : ℂ))
      = Complex.exp (-((w j + conj (w l)) * (s : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hconj, ← hexp]
  ring

theorem re_add_conj_pos {d : ℕ} {w : Fin d → ℂ} (hw : ∀ j, 0 < (w j).re) (j l : Fin d) :
    0 < (w j + conj (w l)).re := by
  rw [re_add_conj]
  have h1 := hw j
  have h2 := hw l
  linarith

theorem integrableOn_tiltPairSum (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) (a : ℝ) :
    IntegrableOn (fun s : ℝ => ∑ j, ∑ l, (c j * conj (c l)
        * (bilateralLaplace S (w j + (a : ℂ)) * conj (bilateralLaplace S (w l + (a : ℂ)))))
        * Complex.exp (-((w j + conj (w l)) * (s : ℂ)))) (Set.Ioi (0 : ℝ)) :=
  MeasureTheory.integrable_finsetSum _ (fun j _ =>
    MeasureTheory.integrable_finsetSum _ (fun l _ =>
      (GaloisForLFunctions.HTGeometry.integrableOn_cexp_neg_mul
        (re_add_conj_pos hw j l)).const_mul _))

theorem integrableOn_tiltWindow_sq (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) (a : ℝ) :
    IntegrableOn (fun s : ℝ => tiltWindow S c w a s * conj (tiltWindow S c w a s))
      (Set.Ioi (0 : ℝ)) :=
  (integrableOn_tiltPairSum S c w hw a).congr
    (Filter.Eventually.of_forall fun s => (tiltWindow_mul_conj S c w a s).symm)

/-- **Equation (8).**  The correlation energy is the finite Cauchy form of the tilted transform
values. -/
theorem tiltCorrelation_eq (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) (a : ℝ) :
    ((tiltCorrelation S c w a : ℝ) : ℂ) = tiltCorrelationForm S c w a := by
  have hS : ∀ j l : Fin d, 0 < (w j + conj (w l)).re := re_add_conj_pos hw
  have hstep : ((tiltCorrelation S c w a : ℝ) : ℂ)
      = ∫ s in Set.Ioi (0 : ℝ), tiltWindow S c w a s * conj (tiltWindow S c w a s) := by
    rw [tiltCorrelation, ← integral_complex_ofReal]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [hstep, MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (tiltWindow_mul_conj S c w a)),
    MeasureTheory.integral_finsetSum _ (fun j _ =>
      MeasureTheory.integrable_finsetSum _ (fun l _ =>
        (GaloisForLFunctions.HTGeometry.integrableOn_cexp_neg_mul
          (re_add_conj_pos hw j l)).const_mul
          (c j * conj (c l)
            * (bilateralLaplace S (w j + (a : ℂ))
              * conj (bilateralLaplace S (w l + (a : ℂ))))))),
    tiltCorrelationForm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun l _ =>
    (GaloisForLFunctions.HTGeometry.integrableOn_cexp_neg_mul
      (re_add_conj_pos hw j l)).const_mul
      (c j * conj (c l)
        * (bilateralLaplace S (w j + (a : ℂ))
          * conj (bilateralLaplace S (w l + (a : ℂ))))))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MeasureTheory.integral_const_mul,
    GaloisForLFunctions.RHTower.integral_cexp_neg_mul_Ioi_zero (hS j l), one_div]
  ring

/-! ## The critical first variation -/

theorem bilateralLaplaceDeriv_conj (S : ThetaSource) (w : ℂ) :
    conj (bilateralLaplaceDeriv S w) = bilateralLaplaceDeriv S (conj w) := by
  rw [bilateralLaplaceDeriv, bilateralLaplaceDeriv, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [map_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]

/-- **Equation (6).**  The source Bezoutian of the transform. -/
def sourceBezoutian (S : ThetaSource) (w v : ℂ) : ℂ :=
  (bilateralLaplaceDeriv S w * conj (bilateralLaplace S v)
    + bilateralLaplace S w * conj (bilateralLaplaceDeriv S v)) / (w + conj v)

theorem add_zero_ofReal (z : ℂ) : z + (((0 : ℝ)) : ℂ) = z := by
  push_cast
  ring

theorem hasDerivAt_shifted_laplace (S : ThetaSource) (z : ℂ) :
    HasDerivAt (fun a : ℝ => bilateralLaplace S (z + (a : ℂ)))
      (bilateralLaplaceDeriv S z) 0 := by
  have hline : HasDerivAt (fun a : ℝ => z + (a : ℂ)) 1 0 :=
    (Complex.ofRealCLM.hasDerivAt).const_add z
  have hcomp := HasDerivAt.scomp (0 : ℝ)
    (h := fun a : ℝ => z + (a : ℂ)) (g₁ := bilateralLaplace S)
    (by rw [add_zero_ofReal]; exact hasDerivAt_bilateralLaplace S z) hline
  rw [one_smul] at hcomp
  exact hcomp

/-- **Equations (7)–(8).**  The tilt derivative of the closed correlation form. -/
theorem hasDerivAt_tiltCorrelationForm (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) :
    HasDerivAt (tiltCorrelationForm S c w)
      (∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)) 0 := by
  have hconj : ∀ (l : Fin d) (a : ℝ), conj (bilateralLaplace S (w l + (a : ℂ)))
      = bilateralLaplace S (conj (w l) + (a : ℂ)) := by
    intro l a
    rw [bilateralLaplace_conj, map_add, Complex.conj_ofReal]
  have hterm : ∀ j l : Fin d, HasDerivAt
      (fun a : ℝ => c j * conj (c l)
        * (bilateralLaplace S (w j + (a : ℂ)) * conj (bilateralLaplace S (w l + (a : ℂ))))
        / (w j + conj (w l)))
      (c j * conj (c l) * sourceBezoutian S (w j) (w l)) 0 := by
    intro j l
    have hmul := (hasDerivAt_shifted_laplace S (w j)).mul
      (hasDerivAt_shifted_laplace S (conj (w l)))
    rw [add_zero_ofReal, add_zero_ofReal] at hmul
    have hscaled := (hmul.const_mul (c j * conj (c l))).div_const (w j + conj (w l))
    have hval : c j * conj (c l) * (bilateralLaplaceDeriv S (w j)
          * bilateralLaplace S (conj (w l))
          + bilateralLaplace S (w j) * bilateralLaplaceDeriv S (conj (w l)))
        / (w j + conj (w l))
        = c j * conj (c l) * sourceBezoutian S (w j) (w l) := by
      rw [sourceBezoutian, ← bilateralLaplace_conj, ← bilateralLaplaceDeriv_conj]
      ring
    rw [hval] at hscaled
    refine hscaled.congr_of_eventuallyEq ?_
    filter_upwards with a
    simp only [Pi.mul_apply]
    rw [hconj l a]
  have hsum : HasDerivAt
      (∑ j : Fin d, fun a : ℝ => ∑ l, c j * conj (c l)
        * (bilateralLaplace S (w j + (a : ℂ)) * conj (bilateralLaplace S (w l + (a : ℂ))))
        / (w j + conj (w l)))
      (∑ j : Fin d, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)) 0 := by
    refine HasDerivAt.sum fun j _ => ?_
    have h := HasDerivAt.sum (u := Finset.univ)
      (A := fun l : Fin d => fun a : ℝ => c j * conj (c l)
        * (bilateralLaplace S (w j + (a : ℂ)) * conj (bilateralLaplace S (w l + (a : ℂ))))
        / (w j + conj (w l)))
      (A' := fun l : Fin d => c j * conj (c l) * sourceBezoutian S (w j) (w l))
      (x := (0 : ℝ)) (fun l _ => hterm j l)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with a
    simp only [Finset.sum_apply]
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards with a
  simp only [Finset.sum_apply]
  rw [tiltCorrelationForm]

/-- **Equation (7).**  The critical tilt flux of a finite exponential packet is the source
Bezoutian quadratic form. -/
theorem hasDerivAt_tiltCorrelation (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) :
    HasDerivAt (tiltCorrelation S c w)
      ((∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)).re) 0 := by
  have hcast : HasDerivAt (fun a : ℝ => ((tiltCorrelation S c w a : ℝ) : ℂ))
      (∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)) 0 :=
    (hasDerivAt_tiltCorrelationForm S c w).congr_of_eventuallyEq
      (by filter_upwards with a; exact tiltCorrelation_eq S c w hw a)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcast
  exact hre

/-! ## Parity of the transform and the reflection law -/

theorem bilateralLaplace_neg (S : ThetaSource) (w : ℂ) :
    bilateralLaplace S (-w) = bilateralLaplace S w := by
  rw [bilateralLaplace, bilateralLaplace, ← MeasureTheory.integral_neg_eq_self
    (fun x : ℝ => (S.k x : ℂ) * Complex.exp (w * (x : ℂ))) volume]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [S.even' x]
  push_cast
  congr 1
  ring

theorem bilateralLaplaceDeriv_neg (S : ThetaSource) (w : ℂ) :
    bilateralLaplaceDeriv S (-w) = -bilateralLaplaceDeriv S w := by
  rw [bilateralLaplaceDeriv, bilateralLaplaceDeriv, ← MeasureTheory.integral_neg,
    ← MeasureTheory.integral_neg_eq_self
      (fun x : ℝ => -((x : ℂ) * (S.k x : ℂ) * Complex.exp (w * (x : ℂ)))) volume]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [S.even' x]
  push_cast
  have hexp : Complex.exp (-w * (x : ℂ)) = Complex.exp (w * -(x : ℂ)) := by
    congr 1
    ring
  rw [hexp]
  ring

/-! ## The untilted window and first-moment operators -/

/-- **Equation (9).**  `W Φ`, the untilted correlation window. -/
def sourceWindow (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (s : ℝ) : ℂ :=
  ∑ j, c j * bilateralLaplace S (w j) * Complex.exp (-(w j) * (s : ℂ))

/-- **Equation (9).**  `M Φ`, the first-moment window. -/
def sourceMoment (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (s : ℝ) : ℂ :=
  ∑ j, c j * bilateralLaplaceDeriv S (w j) * Complex.exp (-(w j) * (s : ℂ))

theorem tiltWindow_zero (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (s : ℝ) :
    tiltWindow S c w 0 s = sourceWindow S c w s := by
  rw [tiltWindow_eq, sourceWindow]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  rw [add_zero]

/-- The translated integrand of a single first-moment mode. -/
def momentModeShift (S : ThetaSource) (w : ℂ) (s : ℝ) (y : ℝ) : ℂ :=
  (y : ℂ) * (S.k y : ℂ) * Complex.exp (w * ((y : ℂ) - (s : ℂ)))

theorem momentModeShift_apply (S : ThetaSource) (w : ℂ) (s x : ℝ) :
    momentModeShift S w s (x + s)
      = ((x : ℂ) + (s : ℂ)) * (S.k (x + s) : ℂ) * Complex.exp (w * (x : ℂ)) := by
  rw [momentModeShift]
  push_cast
  ring_nf

theorem momentModeShift_eq (S : ThetaSource) (w : ℂ) (s y : ℝ) :
    momentModeShift S w s y
      = Complex.exp (-w * (s : ℂ)) * ((y : ℂ) * (S.k y : ℂ) * Complex.exp (w * (y : ℂ))) := by
  have h2 : Complex.exp (w * ((y : ℂ) - (s : ℂ)))
      = Complex.exp (w * (y : ℂ)) * Complex.exp (-w * (s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [momentModeShift, h2]
  ring

theorem integrable_momentModeShift (S : ThetaSource) (w : ℂ) (s : ℝ) :
    Integrable (momentModeShift S w s) := by
  refine ((S.integrable_mul_exp w 1).const_mul (Complex.exp (-w * (s : ℂ)))).congr
    (Filter.Eventually.of_forall fun y => ?_)
  rw [momentModeShift_eq]
  simp [pow_one]

theorem integrable_moment_single (S : ThetaSource) (w : ℂ) (s : ℝ) :
    Integrable fun x : ℝ => ((x : ℂ) + (s : ℂ)) * (S.k (x + s) : ℂ)
      * Complex.exp (w * (x : ℂ)) := by
  refine ((integrable_momentModeShift S w s).comp_add_right s).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact momentModeShift_apply S w s x

theorem integral_moment_single (S : ThetaSource) (w : ℂ) (s : ℝ) :
    (∫ x : ℝ, ((x : ℂ) + (s : ℂ)) * (S.k (x + s) : ℂ) * Complex.exp (w * (x : ℂ)))
      = bilateralLaplaceDeriv S w * Complex.exp (-w * (s : ℂ)) := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x =>
      (momentModeShift_apply S w s x).symm),
    MeasureTheory.integral_add_right_eq_self (momentModeShift S w s) s,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (momentModeShift_eq S w s)),
    MeasureTheory.integral_const_mul, bilateralLaplaceDeriv]
  ring

/-- **Equation (17).**  The first-moment window of a finite packet is the finite exponential sum
with amplitudes `X'(w_j)`. -/
theorem sourceMoment_eq_integral (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (s : ℝ) :
    (∫ x : ℝ, ((x : ℂ) + (s : ℂ)) * (S.k (x + s) : ℂ) * expPacketFn c w x)
      = sourceMoment S c w s := by
  have hcongr : ∀ x : ℝ, ((x : ℂ) + (s : ℂ)) * (S.k (x + s) : ℂ) * expPacketFn c w x
      = ∑ j, c j * (((x : ℂ) + (s : ℂ)) * (S.k (x + s) : ℂ) * Complex.exp (w j * (x : ℂ))) := by
    intro x
    rw [expPacketFn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_finsetSum _
      (fun j _ => (integrable_moment_single S (w j) s).const_mul (c j)),
    sourceMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_moment_single]
  ring

/-- **Equation (18b).**  Evenness of the source reflects the window and antireflects the moment.
`R` acts on a packet by negating every frequency. -/
theorem sourceWindow_neg (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (s : ℝ) :
    sourceWindow S c (fun j => -(w j)) s = sourceWindow S c w (-s) := by
  rw [sourceWindow, sourceWindow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilateralLaplace_neg]
  push_cast
  congr 2
  ring

theorem sourceMoment_neg (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (s : ℝ) :
    sourceMoment S c (fun j => -(w j)) s = -sourceMoment S c w (-s) := by
  rw [sourceMoment, sourceMoment, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilateralLaplaceDeriv_neg]
  push_cast
  have hexp : Complex.exp (-(-(w j)) * (s : ℂ)) = Complex.exp (-(w j) * (-(s : ℂ))) := by
    congr 1
    ring
  rw [hexp]
  ring

/-! ## The Cauchy Gram of finite exponential sums -/

/-- A finite exponential sum on the positive half line. -/
private def expSum {d : ℕ} (a w : Fin d → ℂ) (s : ℝ) : ℂ :=
  ∑ j, a j * Complex.exp (-(w j) * (s : ℂ))

theorem expSum_mul_conj {d : ℕ} (a b w : Fin d → ℂ) (s : ℝ) :
    expSum a w s * conj (expSum b w s)
      = ∑ j, ∑ l, a j * conj (b l) * Complex.exp (-((w j + conj (w l)) * (s : ℂ))) := by
  rw [expSum, expSum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have hconj : conj (b l * Complex.exp (-(w l) * (s : ℂ)))
      = conj (b l) * Complex.exp (-(conj (w l)) * (s : ℂ)) := by
    rw [map_mul, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]
  have hexp : Complex.exp (-(w j) * (s : ℂ)) * Complex.exp (-(conj (w l)) * (s : ℂ))
      = Complex.exp (-((w j + conj (w l)) * (s : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hconj, ← hexp]
  ring

theorem integrableOn_expSum_pairSum {d : ℕ} (a b w : Fin d → ℂ) (hw : ∀ j, 0 < (w j).re) :
    IntegrableOn (fun s : ℝ => ∑ j, ∑ l, a j * conj (b l)
        * Complex.exp (-((w j + conj (w l)) * (s : ℂ)))) (Set.Ioi (0 : ℝ)) :=
  MeasureTheory.integrable_finsetSum _ (fun j _ =>
    MeasureTheory.integrable_finsetSum _ (fun l _ =>
      (GaloisForLFunctions.HTGeometry.integrableOn_cexp_neg_mul
        (re_add_conj_pos hw j l)).const_mul _))

theorem integrableOn_expSum_mul_conj {d : ℕ} (a b w : Fin d → ℂ) (hw : ∀ j, 0 < (w j).re) :
    IntegrableOn (fun s : ℝ => expSum a w s * conj (expSum b w s)) (Set.Ioi (0 : ℝ)) :=
  (integrableOn_expSum_pairSum a b w hw).congr
    (Filter.Eventually.of_forall fun s => (expSum_mul_conj a b w s).symm)

/-- The Cauchy Gram value of two finite exponential sums on the half line. -/
theorem integral_expSum_mul_conj {d : ℕ} (a b w : Fin d → ℂ) (hw : ∀ j, 0 < (w j).re) :
    (∫ s in Set.Ioi (0 : ℝ), expSum a w s * conj (expSum b w s))
      = ∑ j, ∑ l, a j * conj (b l) / (w j + conj (w l)) := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (expSum_mul_conj a b w)),
    MeasureTheory.integral_finsetSum _ (fun j _ =>
      MeasureTheory.integrable_finsetSum _ (fun l _ =>
        (GaloisForLFunctions.HTGeometry.integrableOn_cexp_neg_mul
          (re_add_conj_pos hw j l)).const_mul (a j * conj (b l))))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun l _ =>
    (GaloisForLFunctions.HTGeometry.integrableOn_cexp_neg_mul
      (re_add_conj_pos hw j l)).const_mul (a j * conj (b l)))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [MeasureTheory.integral_const_mul,
    GaloisForLFunctions.RHTower.integral_cexp_neg_mul_Ioi_zero (re_add_conj_pos hw j l), one_div]
  ring

theorem integral_norm_sq_eq_expSum {d : ℕ} (a w : Fin d → ℂ) (hw : ∀ j, 0 < (w j).re) :
    ((∫ s in Set.Ioi (0 : ℝ), ‖expSum a w s‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ j, ∑ l, a j * conj (a l) / (w j + conj (w l)) := by
  rw [← integral_complex_ofReal, ← integral_expSum_mul_conj a a w hw]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp only
  rw [Complex.mul_conj']
  push_cast
  ring

/-! ## The contraction coordinate -/

theorem sourceWindow_eq_expSum (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) :
    sourceWindow S c w = expSum (fun j => c j * bilateralLaplace S (w j)) w := by
  funext s
  rw [sourceWindow, expSum]

theorem sourceMoment_eq_expSum (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) :
    sourceMoment S c w = expSum (fun j => c j * bilateralLaplaceDeriv S (w j)) w := by
  funext s
  rw [sourceMoment, expSum]

/-- **Equation (14).**  `V_{+,t} = M + t W`. -/
def contractionPlus (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (t : ℝ) (s : ℝ) : ℂ :=
  sourceMoment S c w s + (t : ℂ) * sourceWindow S c w s

/-- **Equation (14).**  `V_{-,t} = M - t W`. -/
def contractionMinus (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (t : ℝ) (s : ℝ) : ℂ :=
  sourceMoment S c w s - (t : ℂ) * sourceWindow S c w s

theorem contractionPlus_eq_expSum (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (t : ℝ) :
    contractionPlus S c w t
      = expSum (fun j => c j * (bilateralLaplaceDeriv S (w j)
          + (t : ℂ) * bilateralLaplace S (w j))) w := by
  funext s
  rw [contractionPlus, sourceMoment, sourceWindow, expSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem contractionMinus_eq_expSum (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (t : ℝ) :
    contractionMinus S c w t
      = expSum (fun j => c j * (bilateralLaplaceDeriv S (w j)
          - (t : ℂ) * bilateralLaplace S (w j))) w := by
  funext s
  rw [contractionMinus, sourceMoment, sourceWindow, expSum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The moment/window pairing of a finite packet. -/
def momentWindowPairing (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) : ℂ :=
  ∫ s in Set.Ioi (0 : ℝ), sourceMoment S c w s * conj (sourceWindow S c w s)

theorem momentWindowPairing_eq (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) :
    momentWindowPairing S c w
      = ∑ j, ∑ l, (c j * bilateralLaplaceDeriv S (w j))
          * conj (c l * bilateralLaplace S (w l)) / (w j + conj (w l)) := by
  rw [momentWindowPairing, sourceWindow_eq_expSum, sourceMoment_eq_expSum,
    integral_expSum_mul_conj _ _ w hw]

theorem conj_momentWindowPairing_eq (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) :
    conj (momentWindowPairing S c w)
      = ∑ j, ∑ l, (c j * bilateralLaplace S (w j))
          * conj (c l * bilateralLaplaceDeriv S (w l)) / (w j + conj (w l)) := by
  rw [momentWindowPairing_eq S c w hw, map_sum]
  have hstep : ∀ j : Fin d, conj (∑ l, (c j * bilateralLaplaceDeriv S (w j))
          * conj (c l * bilateralLaplace S (w l)) / (w j + conj (w l)))
      = ∑ l, conj (c j * bilateralLaplaceDeriv S (w j))
          * (c l * bilateralLaplace S (w l)) / (conj (w j) + w l) := by
    intro j
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_div₀, map_mul, Complex.conj_conj, map_add, Complex.conj_conj]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [add_comm (conj (w l)) (w j)]
  ring

/-- **Equation (10).**  The critical flux is twice the real part of the moment/window pairing. -/
theorem sourceBezoutianSum_eq_pairing (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) :
    ∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)
      = momentWindowPairing S c w + conj (momentWindowPairing S c w) := by
  rw [conj_momentWindowPairing_eq S c w hw, momentWindowPairing_eq S c w hw,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sourceBezoutian, map_mul, map_mul]
  ring

/-- The two contraction energies differ by exactly `2 t` times the flux. -/
theorem contraction_energy_difference (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) (t : ℝ) :
    ((∫ s in Set.Ioi (0 : ℝ), ‖contractionPlus S c w t s‖ ^ (2 : ℕ) : ℝ) : ℂ)
        - ((∫ s in Set.Ioi (0 : ℝ), ‖contractionMinus S c w t s‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = 2 * (t : ℂ) * (momentWindowPairing S c w + conj (momentWindowPairing S c w)) := by
  rw [contractionPlus_eq_expSum, contractionMinus_eq_expSum,
    integral_norm_sq_eq_expSum _ w hw, integral_norm_sq_eq_expSum _ w hw,
    conj_momentWindowPairing_eq S c w hw, momentWindowPairing_eq S c w hw,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, map_add, map_sub, Complex.conj_ofReal]
  ring

/-- **Equation (15).**  The critical flux is the exact difference of the two contraction
energies. -/
theorem sourceBezoutianSum_eq_contraction_difference (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ)
    (hw : ∀ j, 0 < (w j).re) {t : ℝ} (ht : 0 < t) :
    ∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)
      = (1 / (2 * (t : ℂ)))
        * (((∫ s in Set.Ioi (0 : ℝ), ‖contractionPlus S c w t s‖ ^ (2 : ℕ) : ℝ) : ℂ)
          - ((∫ s in Set.Ioi (0 : ℝ), ‖contractionMinus S c w t s‖ ^ (2 : ℕ) : ℝ) : ℂ)) := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [contraction_energy_difference S c w hw t, sourceBezoutianSum_eq_pairing S c w hw]
  field_simp

/-! ## The spectral transfer multiplier and the reflection law -/

/-- **Equation (18).**  On a single exponential mode the contraction coordinate acts by the Cayley
multiplier of the logarithmic derivative `L = X'/X`. -/
theorem contraction_multiplier (S : ThetaSource) {w : ℂ} (hX : bilateralLaplace S w ≠ 0) (t : ℝ) :
    (bilateralLaplaceDeriv S w - (t : ℂ) * bilateralLaplace S w)
        * (bilateralLaplaceDeriv S w / bilateralLaplace S w + (t : ℂ))
      = (bilateralLaplaceDeriv S w / bilateralLaplace S w - (t : ℂ))
        * (bilateralLaplaceDeriv S w + (t : ℂ) * bilateralLaplace S w) := by
  field_simp

/-- **Equation (18c).**  The contraction coordinate is a cross-boundary reflection: `V_{-,t} Φ` on
the positive half line is minus the reflected continuation of `V_{+,t} R Φ`. -/
theorem contractionMinus_eq_reflected (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) (t s : ℝ) :
    contractionMinus S c w t s = -(contractionPlus S c (fun j => -(w j)) t (-s)) := by
  have hM := sourceMoment_neg S c w (-s)
  have hW := sourceWindow_neg S c w (-s)
  rw [neg_neg] at hM hW
  rw [contractionMinus, contractionPlus, hM, hW]
  ring

/-! ## The Riemann specialization -/

theorem sourceBezoutian_conj_symm (S : ThetaSource) (w v : ℂ) :
    conj (sourceBezoutian S w v) = sourceBezoutian S v w := by
  rw [sourceBezoutian, sourceBezoutian, map_div₀, map_add, map_mul, map_mul, Complex.conj_conj,
    Complex.conj_conj, map_add, Complex.conj_conj]
  ring

theorem sourceBezoutianSum_conj (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) :
    conj (∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l))
      = ∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l) := by
  rw [map_sum]
  have hstep : ∀ j : Fin d, conj (∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l))
      = ∑ l, conj (c j) * c l * sourceBezoutian S (w l) (w j) := by
    intro j
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_mul, Complex.conj_conj, sourceBezoutian_conj_symm]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sourceBezoutianSum_im (S : ThetaSource) {d : ℕ} (c w : Fin d → ℂ) :
    (∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)).im = 0 := by
  have h := sourceBezoutianSum_conj S c w
  have him := congrArg Complex.im h
  rw [Complex.conj_im] at him
  linarith

/-- **Equation (12).**  For the completed Riemann theta source the source Bezoutian is the corpus's
centred Xi Bezoutian. -/
theorem sourceBezoutian_eq_xiCentBezoutian (S : ThetaSource)
    (hX : ∀ w, bilateralLaplace S w = xiCent w) {w v : ℂ} (hne : w + conj v ≠ 0) :
    sourceBezoutian S w v = xiCentBezoutian w (conj v) := by
  have hfun : bilateralLaplace S = xiCent := funext hX
  have hD : ∀ z, bilateralLaplaceDeriv S z = deriv xiCent z := by
    intro z
    rw [← deriv_bilateralLaplace S z, hfun]
  rw [sourceBezoutian, hX, hX, hD, hD, xiCentBezoutian_eq_div hne, xiCentBezoutianNumerator,
    ← xiCent_conj, ← deriv_xiCent_conj]

theorem dotProduct_mulVec_bezoutian {d : ℕ} (B : ℂ → ℂ → ℂ) (x w : Fin d → ℂ) :
    star x ⬝ᵥ (Matrix.of fun j k : Fin d => B (w j) (w k)).mulVec x
      = ∑ j, ∑ l, conj (x j) * x l * B (w j) (w l) := by
  rw [GaloisForLFunctions.HTGeometry.dotProduct_mulVec_kernelMatrix B x w]
  simp only [GaloisForLFunctions.HTGeometry.kernelEnergy]

/-- **Equation (13).**  For the completed Riemann theta source, nonnegativity of the critical tilt
flux on every finite Euler packet is exactly the Riemann hypothesis. -/
theorem riemannHypothesis_iff_sourceBezoutian_nonneg (S : ThetaSource)
    (hX : ∀ w, bilateralLaplace S w = xiCent w) :
    RiemannHypothesis ↔
      ∀ (d : ℕ) (c w : Fin d → ℂ), (∀ j, 1 / 2 < (w j).re) →
        0 ≤ (∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l)).re := by
  have hbez : ∀ {w v : ℂ}, 1 / 2 < w.re → 1 / 2 < v.re →
      sourceBezoutian S w v = xiCentBezoutian w (conj v) := by
    intro w v hw hv
    refine sourceBezoutian_eq_xiCentBezoutian S hX ?_
    intro h
    have := congrArg Complex.re h
    rw [re_add_conj, Complex.zero_re] at this
    linarith
  rw [riemannHypothesis_iff_posSemidef_xiCentBezoutian]
  constructor
  · intro hPSD d c w hw
    have hmat := hPSD d (fun j => (⟨w j, hw j⟩ : {W : ℂ // 1 / 2 < W.re}))
    have hval := hmat.dotProduct_mulVec_nonneg (fun j => conj (c j))
    rw [dotProduct_mulVec_bezoutian (fun u v => xiCentBezoutian u (conj v))
      (fun j => conj (c j)) w] at hval
    simp only [Complex.conj_conj] at hval
    have hcongr : (∑ j, ∑ l, c j * conj (c l) * xiCentBezoutian (w j) (conj (w l)))
        = ∑ j, ∑ l, c j * conj (c l) * sourceBezoutian S (w j) (w l) :=
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by
        rw [hbez (hw j) (hw l)]
    rw [hcongr] at hval
    exact (Complex.le_def.mp hval).1
  · intro hflux n w
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext j k
      simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
      rw [← hbez (w j).2 (w k).2, ← hbez (w k).2 (w j).2, sourceBezoutian_conj_symm]
    · intro x
      rw [dotProduct_mulVec_bezoutian (fun u v => xiCentBezoutian u (conj v))
        x (fun j => (w j : ℂ))]
      have hcongr : (∑ j, ∑ l, conj (x j) * x l * xiCentBezoutian ((w j : ℂ)) (conj ((w l : ℂ))))
          = ∑ j, ∑ l, (fun j => conj (x j)) j * conj ((fun j => conj (x j)) l)
              * sourceBezoutian S ((w j : ℂ)) ((w l : ℂ)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [hbez (w j).2 (w l).2, Complex.conj_conj]
      rw [hcongr]
      refine Complex.le_def.mpr ⟨?_, ?_⟩
      · exact hflux n (fun j => conj (x j)) (fun j => (w j : ℂ)) (fun j => (w j).2)
      · exact (sourceBezoutianSum_im S (fun j => conj (x j)) (fun j => (w j : ℂ))).symm

/-- **Equation (13)** in flux form: the tilt derivative of the correlation energy. -/
theorem riemannHypothesis_iff_tiltFlux_nonneg (S : ThetaSource)
    (hX : ∀ w, bilateralLaplace S w = xiCent w) :
    RiemannHypothesis ↔
      ∀ (d : ℕ) (c w : Fin d → ℂ), (∀ j, 1 / 2 < (w j).re) → ∀ D : ℝ,
        HasDerivAt (tiltCorrelation S c w) D 0 → 0 ≤ D := by
  rw [riemannHypothesis_iff_sourceBezoutian_nonneg S hX]
  constructor
  · intro h d c w hw D hD
    have hw' : ∀ j, 0 < (w j).re := fun j => lt_trans (by norm_num) (hw j)
    have hval := hasDerivAt_tiltCorrelation S c w hw'
    rw [hD.unique hval]
    exact h d c w hw
  · intro h d c w hw
    have hw' : ∀ j, 0 < (w j).re := fun j => lt_trans (by norm_num) (hw j)
    exact h d c w hw _ (hasDerivAt_tiltCorrelation S c w hw')

end

end RHTower
