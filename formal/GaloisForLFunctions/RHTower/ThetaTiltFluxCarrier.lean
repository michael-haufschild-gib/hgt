import GaloisForLFunctions.RHTower.XiBezoutianPointedIncidence
import GaloisForLFunctions.RHTower.WeightedLaplaceShift
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

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
open scoped ComplexConjugate

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

theorem ThetaSource.integrable_mul_exp (S : ThetaSource) (w : ℂ) (m : ℕ) :
    Integrable fun x : ℝ => (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (w * (x : ℂ)) := by
  obtain ⟨C, hC, hbd⟩ := S.decay (|w.re| + 1)
  have hcont : Continuous fun x : ℝ =>
      (x : ℂ) ^ m * (S.k x : ℂ) * Complex.exp (w * (x : ℂ)) :=
    (((continuous_pow m).comp Complex.continuous_ofReal).mul
      (Complex.continuous_ofReal.comp S.cont)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  refine Integrable.mono' (g := fun x : ℝ => C * (|x| ^ m * Real.exp (-1 * |x|)))
    ((HTGeometry.integrable_abs_pow_mul_exp_neg_abs m one_pos).const_mul C)
    hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hexp : ‖Complex.exp (w * (x : ℂ))‖ = Real.exp (w.re * x) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hpow : ‖(x : ℂ) ^ m‖ = |x| ^ m := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hknorm : ‖(S.k x : ℂ)‖ = S.k x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.pos x)]
  have hexple : Real.exp (w.re * x) ≤ Real.exp (|w.re| * |x|) := by
    refine Real.exp_le_exp.mpr ?_
    calc w.re * x ≤ |w.re * x| := le_abs_self _
      _ = |w.re| * |x| := abs_mul _ _
  have hcollapse : C * Real.exp (-((|w.re| + 1) * |x|)) * Real.exp (|w.re| * |x|)
      = C * Real.exp (-1 * |x|) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [norm_mul, norm_mul, hpow, hexp, hknorm]
  have hstep : |x| ^ m * S.k x * Real.exp (w.re * x)
      ≤ |x| ^ m * (C * Real.exp (-((|w.re| + 1) * |x|))) * Real.exp (|w.re| * |x|) := by
    refine mul_le_mul ?_ hexple (Real.exp_pos _).le (by positivity)
    exact mul_le_mul_of_nonneg_left (hbd x) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  calc |x| ^ m * (C * Real.exp (-((|w.re| + 1) * |x|))) * Real.exp (|w.re| * |x|)
      = |x| ^ m * (C * Real.exp (-((|w.re| + 1) * |x|)) * Real.exp (|w.re| * |x|)) := by ring
    _ = |x| ^ m * (C * Real.exp (-1 * |x|)) := by rw [hcollapse]
    _ = C * (|x| ^ m * Real.exp (-1 * |x|)) := by ring

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

end

end RHTower
