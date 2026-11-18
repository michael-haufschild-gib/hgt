import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFloorPrimitiveOfTheIntegerReference
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.TheLogarithmicFloorKernelOnTheCriticalStrip
import GaloisForLFunctions.HTGeometry.CausalFourierBridge

/-!
# Integer quadrature as a fractional-part convolution

An exponential tilt of the primitive is a convolution with the fractional
part of the exponential. Its derivative recovers the tilted quadrature error.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped FourierTransform Convolution
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- An exponentially weighted primitive of the centered integer wave. -/
def weightedIntegerPrimitive (Φ : ℝ → ℝ) (β t : ℝ) : ℝ :=
  Real.exp (-(1/2-β)*t)*(∫ v in Iic t, Real.exp (v/2)*(integerReferenceWave Φ v-
    Real.exp (v/2)*(∫ u, Real.exp (-u/2)*Φ u)))

/-- Absolute convergence of the atom series is locally uniform in time. -/
theorem continuous_integerReferenceWave {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) : Continuous (integerReferenceWave Φ) := by
  apply continuous_iff_continuousAt.2
  intro t
  let T := t+1
  let m := fun n : ℕ => (C*Real.exp (2*T))*(1/(n:ℝ)^2)
  have hs : Summable m := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left _
  have h : ContinuousOn (fun x : ℝ => ∑' n : ℕ, continuousIntegerAtom Φ n x) (Iio T) := by
    apply continuousOn_tsum (fun n => by unfold continuousIntegerAtom; fun_prop) hs
    intro n x hx
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [continuousIntegerAtom,m]
    apply (continuousIntegerAtom_bound hb (by exact_mod_cast hn : (1:ℝ)≤n) x).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (le_of_lt hx) (by norm_num : (0:ℝ)≤2))) hC) (by positivity)
  have ht : t < T := lt_add_one t
  exact (h.congr (fun y _ => (tsum_continuousIntegerAtom hb y).symm)).continuousAt (Iio_mem_nhds ht)

private theorem hasDerivAt_left_primitive {g : ℝ → ℝ} (hc : Continuous g)
    (hi : ∀ t, IntegrableOn g (Iic t)) (t : ℝ) :
    HasDerivAt (fun y => ∫ x in Iic y, g x) (g t) t := by
  let b := t-1
  have h := ((hc.integral_hasStrictDerivAt b t).hasDerivAt).const_add (∫ x in Iic b, g x)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show b<t by dsimp only [b]; linarith)] with y hy
  rw [intervalIntegral.integral_of_le (le_of_lt hy),← setIntegral_union (Iic_disjoint_Ioc le_rfl)
    measurableSet_Ioc (hi b) ((hi y).mono_set (fun _ hx => hx.2)),Iic_union_Ioc_eq_Iic (le_of_lt hy)]

/-- Differentiation recovers the tilted lattice discrepancy without a
derivative of the profile. -/
theorem hasDerivAt_weightedIntegerPrimitive {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (β t : ℝ) :
    HasDerivAt (weightedIntegerPrimitive Φ β)
      (-(1/2-β)*weightedIntegerPrimitive Φ β t + Real.exp (β*t)*(integerReferenceWave Φ t-
        Real.exp (t/2)*(∫ u, Real.exp (-u/2)*Φ u))) t := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let g := fun v : ℝ => Real.exp (v/2)*(integerReferenceWave Φ v-Real.exp (v/2)*A)
  have hN := continuous_integerReferenceWave hc hC hb
  have hcont : Continuous g := by dsimp only [g]; fun_prop
  have hi (y : ℝ) : IntegrableOn g (Iic y) := by
    apply ((integerReference_exp_primitive hc hC hb y).1.sub ((integrableOn_exp_Iic y).mul_const A)).congr_fun _ measurableSet_Iic
    intro v _
    change Real.exp (v/2)*integerReferenceWave Φ v-Real.exp v*A = Real.exp (v/2)*(integerReferenceWave Φ v-Real.exp (v/2)*A)
    rw [mul_sub,← mul_assoc,← Real.exp_add,show v/2+v/2=v by ring]
  have de := (((hasDerivAt_id t).const_mul (-(1/2-β))).exp).mul (hasDerivAt_left_primitive hcont hi t)
  apply de.congr_deriv
  have he : Real.exp (-(1/2-β)*t)*Real.exp (t/2)=Real.exp (β*t) := by
    rw [← Real.exp_add]; congr 1; ring
  dsimp only [weightedIntegerPrimitive,g,id_eq]
  rw [← he]
  dsimp only [A]; ring

/-- The integration that turns the lattice into a floor function also factors
the primitive into a Mellin kernel and the tilted state. -/
theorem weightedIntegerPrimitive_eq_convolution {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (hp : Integrable fun u : ℝ => Real.exp (-u/2)*Φ u)
    (hm : Integrable fun u : ℝ => Real.exp (u/2)*Φ u) (β t : ℝ) :
    weightedIntegerPrimitive Φ β t = ∫ u, weightedFloorDiscrepancy (1/2-β) (t-u)*
      (Real.exp (β*u)*Φ u) := by
  rw [weightedIntegerPrimitive,(integerReference_centered_primitive hc hC hb hp hm t).1,
    mul_neg,← integral_const_mul,← integral_neg]
  apply integral_congr_ae (Eventually.of_forall fun u => ?_)
  have h : Real.exp (-(1/2-β)*t)*Real.exp (u/2) =
      Real.exp (-(1/2-β)*(t-u))*Real.exp (β*u) := by
    rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  unfold weightedFloorDiscrepancy
  linear_combination -(Int.fract (Real.exp (t-u))*Φ u)*h

/-- Absolute and square integrability of the primitive, with its complete
Fourier multiplier on every subcritical positive tilt. -/
theorem weightedIntegerPrimitive_fourier {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (hp : Integrable fun u : ℝ => Real.exp (-u/2)*Φ u)
    (hm : Integrable fun u : ℝ => Real.exp (u/2)*Φ u) {β : ℝ} (hβ : 0 ≤ β) (hβ' : β < 1/2)
    (hψ : Integrable fun u : ℝ => Real.exp (β*u)*Φ u) :
    let B := fun t : ℝ => (weightedIntegerPrimitive Φ β t:ℂ)
    Integrable B ∧ MemLp B 2 ∧ ∀ ξ : ℝ,
      let s : ℂ := ((1/2-β:ℝ):ℂ)+(2*Real.pi*ξ:ℝ)*Complex.I
      𝓕 B ξ = 𝓕 (fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)) ξ*(riemannZeta s/s) := by
  let ψ := fun u : ℝ => ((Real.exp (β*u)*Φ u:ℝ):ℂ)
  let k := fun v : ℝ => (weightedFloorDiscrepancy (1/2-β) v:ℂ)
  have hσ := sub_pos.2 hβ'
  have hσ' : 1/2-β < 1 := by linarith
  have hiψ : Integrable ψ := hψ.ofReal
  have hik : Integrable k := (integrable_weightedFloorDiscrepancy hσ hσ').ofReal
  have he : (fun t : ℝ => (weightedIntegerPrimitive Φ β t:ℂ)) =
      ψ ⋆[ContinuousLinearMap.mul ℂ ℂ] k := by
    funext t
    rw [weightedIntegerPrimitive_eq_convolution hc hC hb hp hm,← integral_complex_ofReal,convolution_def]
    apply integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only [ψ,k,ContinuousLinearMap.mul_apply']
    rw [Complex.ofReal_mul,mul_comm]
  dsimp only
  rw [he]
  have hi : Integrable (ψ ⋆[ContinuousLinearMap.mul ℂ ℂ] k) :=
    (hiψ.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hik).integral_prod_left
  have hk (v : ℝ) : ‖k v‖ ≤ 1 := by
    simpa only [k,Complex.norm_real,Real.norm_eq_abs] using abs_weightedFloorDiscrepancy_le_one hσ.le hσ'.le v
  refine ⟨hi,_root_.RHTower.memLp_two_of_integrable_of_norm_le hi
    (fun t => _root_.RHTower.norm_convolution_le_of_bound hiψ hk t),fun ξ => ?_⟩
  rw [_root_.RHTower.fourier_mul_convolution_eq_of_integrable hiψ hik]
  exact congrArg ((𝓕 ψ ξ)*·) (fourier_weightedFloorDiscrepancy hσ hσ' ξ)

#print axioms weightedIntegerPrimitive_eq_convolution
#print axioms hasDerivAt_weightedIntegerPrimitive
#print axioms weightedIntegerPrimitive_fourier
end GaloisForLFunctions.ExclusionOfTheCriticalState
