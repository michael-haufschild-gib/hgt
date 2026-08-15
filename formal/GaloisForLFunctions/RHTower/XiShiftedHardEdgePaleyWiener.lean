import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDerivativeBound
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals

/-!
# Paley–Wiener support of a strong limit of rational hard-edge tests

The Cayley lift of a trigonometric profile lies in `L²` because the half-density factor is
`a/√(a²+x²)`, and the whole chain of its spectral derivatives is again of this shape.  Feeding that
chain into the `L²` Fourier multiplier calculus turns the trigonometric derivative bound

`‖g^{(m)}‖₂ ≤ (∏_{i<m} (1/a)(1/2 + 2(N+i)))·‖g‖₂`

into a frequency-tail bound for `ĝ`, and along a family with `N ≤ Ca` and `a → ∞` the constant
tends to `(2C)^m`.  Letting `m` grow kills every frequency with `2π|ξ| > 2C`: the strong limit is a
Paley–Wiener function of exponential type `2C`.
-/

open MeasureTheory Filter FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The Cayley lift as an `L²` function -/

theorem continuous_routeUCayleyLift (a : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (routeUCayleyLift a F) := by
  unfold routeUCayleyLift routeUHardEdgeInverseChart
  fun_prop

theorem memLp_routeUCayleyLift {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ θ : ℝ, |F θ| ≤ M) :
    MemLp (routeUCayleyLift a F) 2 (volume : Measure ℝ) := by
  have hcont := continuous_routeUCayleyLift a hF
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  have hdom : Integrable (fun x : ℝ => M ^ 2 * a ^ 2 * ((a ^ 2 + x ^ 2)⁻¹))
      (volume : Measure ℝ) := (integrable_inv_sq_add_sq ha).const_mul _
  refine Integrable.mono' hdom (hcont.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have hsq : routeUCayleyLift a F x ^ 2
      = (a ^ 2 / (a ^ 2 + x ^ 2)) * F (routeUHardEdgeInverseChart a x) ^ 2 := by
    rw [routeUCayleyLift, mul_pow, cos_half_inverseChart_sq ha]
  have hFb : F (routeUHardEdgeInverseChart a x) ^ 2 ≤ M ^ 2 := by
    have h := hM (routeUHardEdgeInverseChart a x)
    nlinarith [abs_nonneg (F (routeUHardEdgeInverseChart a x)),
      sq_abs (F (routeUHardEdgeInverseChart a x))]
  have hfrac : (0 : ℝ) ≤ a ^ 2 / (a ^ 2 + x ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsq]
  refine le_trans (mul_le_mul_of_nonneg_left hFb hfrac) (le_of_eq ?_)
  field_simp

/-! ## The complexified derivative chain -/

/-- The complexified chain of spectral derivatives of a Cayley lift. -/
def routeUCayleyChain (a : ℝ) (F : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ((routeUCayleyLift a (trigCayleyIter a j F) x : ℝ) : ℂ)

theorem memLp_routeUCayleyChain {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (j : ℕ) :
    MemLp (routeUCayleyChain a F j) 2 (volume : Measure ℝ) := by
  have hiter : RealTrigDeg (D + j) (trigCayleyIter a j F) := realTrigDeg_trigCayleyIter j D hF
  obtain ⟨M, hM⟩ := hiter.exists_bound
  exact memLp_ofReal (memLp_routeUCayleyLift ha hiter.continuous hM)

theorem hasDerivAt_routeUCayleyChain {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (j : ℕ) (x : ℝ) :
    HasDerivAt (routeUCayleyChain a F j) (routeUCayleyChain a F (j + 1) x) x := by
  have hiter : RealTrigDeg (D + j) (trigCayleyIter a j F) := realTrigDeg_trigCayleyIter j D hF
  have hstep := hasDerivAt_routeUCayleyLift_step ha (F := trigCayleyIter a j F)
    (F' := deriv (trigCayleyIter a j F)) (fun θ => hiter.hasDerivAt θ) x
  have hnext : routeUCayleyChain a F (j + 1) x
      = ((routeUCayleyLift a (trigCayleyStep a (trigCayleyIter a j F)
          (deriv (trigCayleyIter a j F))) x : ℝ) : ℂ) := by
    rw [routeUCayleyChain, trigCayleyIter_succ]
  rw [hnext]
  exact hstep.ofReal_comp

theorem norm_toLp_routeUCayleyChain_sq {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (j : ℕ) :
    ‖(memLp_routeUCayleyChain ha hF j).toLp (routeUCayleyChain a F j)‖ ^ 2
      = ∫ x : ℝ, routeUCayleyLift a (trigCayleyIter a j F) x ^ 2 := by
  rw [norm_lpTwo_sq]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_routeUCayleyChain ha hF j).coeFn_toLp] with x hx
  rw [hx, routeUCayleyChain, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## The frequency tail of a single packet -/

/-- The trigonometric derivative bound transported to the `L²` classes of the chain. -/
theorem norm_toLp_routeUCayleyChain_le {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (m : ℕ) :
    ‖(memLp_routeUCayleyChain ha hF m).toLp (routeUCayleyChain a F m)‖
      ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))))
        * ‖(memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)‖ := by
  have hP : (0 : ℝ) ≤ ∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))) := by
    refine Finset.prod_nonneg fun i _ => ?_
    have h1 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h3 : (0 : ℝ) < 1 / a := by positivity
    nlinarith
  have hbase := integral_iteratedDeriv_routeUCayleyLift_sq_le ha m hF
  rw [iteratedDeriv_routeUCayleyLift ha m hF] at hbase
  have hsq : ‖(memLp_routeUCayleyChain ha hF m).toLp (routeUCayleyChain a F m)‖ ^ 2
      ≤ ((∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))))
        * ‖(memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)‖) ^ 2 := by
    rw [mul_pow, norm_toLp_routeUCayleyChain_sq ha hF m, norm_toLp_routeUCayleyChain_sq ha hF 0,
      trigCayleyIter_zero]
    exact hbase
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **The frequency-tail estimate for a single hard-edge packet.** -/
theorem routeUCayley_highFrequency_le {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    r ^ m * ‖restrictLp (highFrequencySet r)
        (𝓕 ((memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)))‖
      ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))))
        * ‖(memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)‖ :=
  le_trans
    (norm_restrictLp_fourier_le (f := routeUCayleyChain a F)
      (fun j => memLp_routeUCayleyChain ha hF j)
      (fun j x => hasDerivAt_routeUCayleyChain ha hF j x) hr m)
    (norm_toLp_routeUCayleyChain_le ha hF m)

end RHTower

end
