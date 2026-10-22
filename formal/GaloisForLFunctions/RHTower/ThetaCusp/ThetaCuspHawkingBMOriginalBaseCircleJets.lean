import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonSourceJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalHorizonRegularity
import GaloisForLFunctions.HTGeometry.ClockParametricDerivative

/-! Actual angular base derivatives of the moving source circle and their
interchange with the complete normalized source integral. -/
open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOriginalBaseCircleJets
open D4BMNativeCircle D4BMSquareCuspJets D4BMAngularSeries
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false
private abbrev P := Fin 2 → ℝ

def U (d theta k : ℝ) : ℂ := (Real.exp k*offset d theta:ℝ)
def Y (d theta k : ℝ) : ℂ := (Real.exp k*height d theta:ℝ)
def weighted (a b : ℕ) (f : P → ℂ) (d theta x k : ℝ) : ℂ :=
  U d theta k^a*Y d theta k^b*f (logCircle d theta x k)

private theorem partial_smooth (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordDeriv i f) domain := by
  intro z hz
  exact (coordDeriv_contDiffAt (hf.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz))
    (by simp) i).contDiffWithinAt

private theorem raw_horizontal (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (d theta x k : ℝ) :
    HasDerivAt (fun t => f (logCircle d theta t k)) (coordDeriv 0 f (logCircle d theta x k)) x := by
  have hc : HasDerivAt (fun t => logCircle d theta t k) (Pi.single 0 1) x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [logCircle,circle] using (hasDerivAt_id x).add_const (Real.exp k*offset d theta)
    · simpa [logCircle,circle] using hasDerivAt_const x (Real.exp k*height d theta)
  have hz : 0 < logCircle d theta x k 1 := mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  exact ((hf.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt x hc

private theorem raw_height (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (d theta x k : ℝ) :
    HasDerivAt (fun t => f (logCircle d theta x t))
      (U d theta k*coordDeriv 0 f (logCircle d theta x k)+Y d theta k*coordDeriv 1 f (logCircle d theta x k)) k := by
  let v : P := ![Real.exp k*offset d theta,Real.exp k*height d theta]
  have hc : HasDerivAt (fun t => logCircle d theta x t) v k := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((Real.hasDerivAt_exp k).mul_const (offset d theta)).const_add x
    · exact (Real.hasDerivAt_exp k).mul_const (height d theta)
  have hz : 0 < logCircle d theta x k 1 := mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have h := ((hf.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt k hc
  apply h.congr_deriv
  rw [pi_eq_sum_univ' v,map_sum]
  simp [Fin.sum_univ_two,v,U,Y,coordDeriv,Complex.real_smul]

private theorem coefficient_derivatives (d theta k : ℝ) :
    HasDerivAt (U d theta) (U d theta k) k ∧ HasDerivAt (Y d theta) (Y d theta k) k := by
  exact ⟨((Real.hasDerivAt_exp k).mul_const (offset d theta)).ofReal_comp,
    ((Real.hasDerivAt_exp k).mul_const (height d theta)).ofReal_comp⟩

private theorem power_derivative {g : ℝ → ℂ} {k : ℝ} (hg : HasDerivAt g (g k) k) (n : ℕ) :
    HasDerivAt (fun t => g t^n) ((n:ℂ)*g k^n) k := by
  apply (hg.pow n).congr_deriv
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel,pow_succ]; push_cast; ring

/-- Horizontal differentiation of the original weighted source circle acts on its source field. -/
theorem weighted_horizontal (a b : ℕ) (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (d theta x k : ℝ) :
    HasDerivAt (fun t => weighted a b f d theta t k)
      (weighted a b (coordDeriv 0 f) d theta x k) x :=
  (raw_horizontal f hf d theta x k).const_mul _

/-- Log-height differentiation retains both moving circle coordinates and their weight. -/
theorem weighted_height (a b : ℕ) (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (d theta x k : ℝ) :
    HasDerivAt (fun t => weighted a b f d theta x t)
      (((a:ℂ)+(b:ℂ))*weighted a b f d theta x k+
        weighted (a+1) b (coordDeriv 0 f) d theta x k+
        weighted a (b+1) (coordDeriv 1 f) d theta x k) k := by
  have hu := power_derivative (coefficient_derivatives d theta k).1 a
  have hy := power_derivative (coefficient_derivatives d theta k).2 b
  have h := (hu.mul hy).mul (raw_height f hf d theta x k)
  apply h.congr_deriv
  dsimp [weighted]
  simp only [pow_succ]
  ring

/-- Both actual horizontal derivatives of the weighted source circle. -/
theorem weighted_horizontal_second (a b : ℕ) (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (d theta x k : ℝ) :
    deriv (deriv (fun t => weighted a b f d theta t k)) x=
      weighted a b (coordDeriv 0 (coordDeriv 0 f)) d theta x k := by
  have h : deriv (fun r => weighted a b f d theta r k)=
      fun t => weighted a b (coordDeriv 0 f) d theta t k := by
    funext t
    exact (weighted_horizontal a b f hf d theta t k).deriv
  rw [h]
  exact (weighted_horizontal a b (coordDeriv 0 f) (partial_smooth f hf 0) d theta x k).deriv

/-- The exact second log-height derivative, including both mixed source orders. -/
theorem weighted_height_second (a b : ℕ) (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (d theta x k : ℝ) :
    deriv (deriv (fun t => weighted a b f d theta x t)) k=
      ((a:ℂ)+(b:ℂ))^(2 : ℕ)*weighted a b f d theta x k+
      (2*((a:ℂ)+(b:ℂ))+1)*(weighted (a+1) b (coordDeriv 0 f) d theta x k+
        weighted a (b+1) (coordDeriv 1 f) d theta x k)+
      weighted (a+2) b (coordDeriv 0 (coordDeriv 0 f)) d theta x k+
      weighted (a+1) (b+1) (coordDeriv 1 (coordDeriv 0 f)) d theta x k+
      weighted (a+1) (b+1) (coordDeriv 0 (coordDeriv 1 f)) d theta x k+
      weighted a (b+2) (coordDeriv 1 (coordDeriv 1 f)) d theta x k := by
  have h : deriv (fun r => weighted a b f d theta x r)=
      fun t => ((a:ℂ)+(b:ℂ))*weighted a b f d theta x t+
        weighted (a+1) b (coordDeriv 0 f) d theta x t+weighted a (b+1) (coordDeriv 1 f) d theta x t := by
    funext t
    exact (weighted_height a b f hf d theta x t).deriv
  rw [h]
  have hh := (((weighted_height a b f hf d theta x k).const_mul ((a:ℂ)+(b:ℂ))).add
    (weighted_height (a+1) b (coordDeriv 0 f) (partial_smooth f hf 0) d theta x k)).add
    (weighted_height a (b+1) (coordDeriv 1 f) (partial_smooth f hf 1) d theta x k)
  change HasDerivAt (fun t => ((a:ℂ)+(b:ℂ))*weighted a b f d theta x t+
    weighted (a+1) b (coordDeriv 0 f) d theta x t+weighted a (b+1) (coordDeriv 1 f) d theta x t) _ k at hh
  rw [hh.deriv]
  simp only [Nat.cast_add,Nat.cast_one,show a+1+1=a+2 by omega,show b+1+1=b+2 by omega]
  ring

/-- Every weighted source-circle expression is smooth in all circle and base coordinates. -/
theorem weighted_smooth (a b : ℕ) (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain) :
    ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => weighted a b f (v 0) (v 1) (v 2) (v 3)) := by
  have hC : ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => logCircle (v 0) (v 1) (v 2) (v 3)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := intro v; exact (denominator_pos _ _).ne')
  have hF : ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => f (logCircle (v 0) (v 1) (v 2) (v 3))) := by
    apply contDiff_iff_contDiffAt.mpr
    intro v
    have hz : 0 < logCircle (v 0) (v 1) (v 2) (v 3) 1 := mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
    exact (hf.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).comp v hC.contDiffAt
  have hU : ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => U (v 0) (v 1) (v 3)) := by
    have h : ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => Real.exp (v 3)*offset (v 0) (v 1)) := by
      unfold offset denominator
      fun_prop (disch := intro v; exact (denominator_pos _ _).ne')
    exact Complex.ofRealCLM.contDiff.comp h
  have hY : ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => Y (v 0) (v 1) (v 3)) := by
    have h : ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => Real.exp (v 3)*height (v 0) (v 1)) := by
      unfold height denominator
      fun_prop (disch := intro v; exact (denominator_pos _ _).ne')
    exact Complex.ofRealCLM.contDiff.comp h
  exact ((hU.pow a).mul (hY.pow b)).mul hF

/-- The actual base operations needed by the angular metric current and derivative interchange. -/
def baseOperator (j : Fin 5) (F : ℝ → ℝ → ℂ) (x k : ℝ) : ℂ :=
  ![F x k,deriv (F x) k,deriv (deriv (fun t => F t k)) x,deriv (deriv (F x)) k,deriv (fun t => F t k) x] j

private theorem deriv_linear (F G : ℝ → ℂ) (c d : ℂ)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) :
    deriv (fun t => c*F t+d*G t)=fun t => c*deriv F t+d*deriv G t := by
  funext t
  exact (((hF t).hasDerivAt.const_mul c).add ((hG t).hasDerivAt.const_mul d)).deriv

private theorem twice_linear (F G : ℝ → ℂ) (c d : ℂ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (x : ℝ) :
    deriv (deriv (fun t => c*F t+d*G t)) x=c*deriv (deriv F) x+d*deriv (deriv G) x := by
  rw [deriv_linear F G c d (hF.differentiable (by simp)) (hG.differentiable (by simp))]
  exact congrFun (deriv_linear (deriv F) (deriv G) c d
    ((contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp))
    ((contDiff_infty_iff_deriv.mp hG).2.differentiable (by simp))) x

/-- All required base operations respect the original source's linear coefficients. -/
theorem baseOperator_linear (j : Fin 5) (F G : ℝ → ℝ → ℂ) (c d : ℂ)
    (hF : ContDiff ℝ ∞ (fun v : ℝ × ℝ => F v.1 v.2))
    (hG : ContDiff ℝ ∞ (fun v : ℝ × ℝ => G v.1 v.2)) (x k : ℝ) :
    baseOperator j (fun x k => c*F x k+d*G x k) x k=
      c*baseOperator j F x k+d*baseOperator j G x k := by
  have hxF : ContDiff ℝ ∞ (fun t => F t k) := hF.comp (show ContDiff ℝ ∞ (fun t : ℝ => (t,k)) by fun_prop)
  have hxG : ContDiff ℝ ∞ (fun t => G t k) := hG.comp (show ContDiff ℝ ∞ (fun t : ℝ => (t,k)) by fun_prop)
  have hkF : ContDiff ℝ ∞ (F x) := hF.comp (show ContDiff ℝ ∞ (fun t : ℝ => (x,t)) by fun_prop)
  have hkG : ContDiff ℝ ∞ (G x) := hG.comp (show ContDiff ℝ ∞ (fun t : ℝ => (x,t)) by fun_prop)
  fin_cases j
  · rfl
  · exact congrFun (deriv_linear (F x) (G x) c d (hkF.differentiable (by simp)) (hkG.differentiable (by simp))) k
  · exact twice_linear _ _ c d hxF hxG x
  · exact twice_linear _ _ c d hkF hkG k
  · exact congrFun (deriv_linear _ _ c d (hxF.differentiable (by simp)) (hxG.differentiable (by simp))) x

theorem weighted_base_smooth (a b : ℕ) (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain) (d theta : ℝ) :
    ContDiff ℝ ∞ (fun v : ℝ × ℝ => weighted a b f d theta v.1 v.2) := by
  have hC : ContDiff ℝ ∞ (fun v : ℝ × ℝ => (![d,theta,v.1,v.2] : Fin 4 → ℝ)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact contDiff_const
    · exact contDiff_fst
    · exact contDiff_snd
  have h := (weighted_smooth a b f hf).comp hC
  exact h

/-- Each actual base derivative is jointly smooth in the circle and base coordinates. -/
theorem weighted_operator_smooth (a b : ℕ) (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain) (j : Fin 5) :
    ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => baseOperator j
      (weighted a b f (v 0) (v 1)) (v 2) (v 3)) := by
  have hx := partial_smooth f hf 0
  have hy := partial_smooth f hf 1
  have h (a b : ℕ) := weighted_smooth a b f hf
  have hX (a b : ℕ) := weighted_smooth a b (coordDeriv 0 f) hx
  have hY (a b : ℕ) := weighted_smooth a b (coordDeriv 1 f) hy
  fin_cases j
  · exact h a b
  · change ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => deriv (fun t => weighted a b f (v 0) (v 1) (v 2) t) (v 3))
    simp_rw [(weighted_height a b f hf _ _ _ _).deriv]
    exact ((contDiff_const.mul (h a b)).add (hX (a+1) b)).add (hY a (b+1))
  · change ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => deriv (deriv (fun t => weighted a b f (v 0) (v 1) t (v 3))) (v 2))
    simp_rw [weighted_horizontal_second a b f hf]
    exact weighted_smooth a b _ (partial_smooth _ hx 0)
  · change ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => deriv (deriv (fun t => weighted a b f (v 0) (v 1) (v 2) t)) (v 3))
    simp_rw [weighted_height_second a b f hf]
    exact (((((contDiff_const.mul (h a b)).add
      (contDiff_const.mul ((hX (a+1) b).add (hY a (b+1))))).add
      (weighted_smooth (a+2) b _ (partial_smooth _ hx 0))).add
      (weighted_smooth (a+1) (b+1) _ (partial_smooth _ hx 1))).add
      (weighted_smooth (a+1) (b+1) _ (partial_smooth _ hy 0))).add
      (weighted_smooth a (b+2) _ (partial_smooth _ hy 1))
  · change ContDiff ℝ ∞ (fun v : Fin 4 → ℝ => deriv (fun t => weighted a b f (v 0) (v 1) t (v 3)) (v 2))
    simp_rw [(weighted_horizontal a b f hf _ _ _ _).deriv]
    exact hX a b

end
end RHTower.D4BMOriginalBaseCircleJets

namespace RHTower.D4BMOriginalBaseCircleJets
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-- Differentiation through the entire original normalized source cube. -/
theorem cube_hasDerivAt (f g : ℝ → ℝ → ℝ → ℝ → ℂ)
    (hf : Continuous (fun v : ℝ × ℝ × ℝ × ℝ => f v.1 v.2.1 v.2.2.1 v.2.2.2))
    (hg : Continuous (fun v : ℝ × ℝ × ℝ × ℝ => g v.1 v.2.1 v.2.2.1 v.2.2.2))
    (hderiv : ∀ z a b t, HasDerivAt (fun w => f w a b t) (g z a b t) z) (z : ℝ) :
    HasDerivAt (fun w => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f w a b t)
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, g z a b t) z := by
  have h0 (f : ℝ → ℝ → ℝ → ℝ → ℂ)
      (hf : Continuous (fun v : ℝ × ℝ × ℝ × ℝ => f v.1 v.2.1 v.2.2.1 v.2.2.2)) :
      Continuous (fun v : (ℝ × ℝ) × ℝ => ∫ t in (0:ℝ)..1, f v.1.1 v.1.2 v.2 t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hf.comp (show Continuous (fun v : ((ℝ × ℝ) × ℝ) × ℝ => (v.1.1.1,v.1.1.2,v.1.2,v.2)) by fun_prop)
  have h1 (f : ℝ → ℝ → ℝ → ℝ → ℂ)
      (hf : Continuous (fun v : ℝ × ℝ × ℝ × ℝ => f v.1 v.2.1 v.2.2.1 v.2.2.2)) :
      Continuous (fun v : ℝ × ℝ => ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f v.1 v.2 b t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (h0 f hf) 0 1
  apply hasDerivAt_parametric_intervalIntegral (h1 f hf) (h1 g hg) _ 0 1 z
  intro z a
  apply hasDerivAt_parametric_intervalIntegral ((h0 f hf).comp (show Continuous (fun v : ℝ × ℝ => ((v.1,a),v.2)) by fun_prop))
    ((h0 g hg).comp (show Continuous (fun v : ℝ × ℝ => ((v.1,a),v.2)) by fun_prop)) _ 0 1 z
  intro z b
  exact hasDerivAt_parametric_intervalIntegral
    (hf.comp (show Continuous (fun v : ℝ × ℝ => (v.1,a,b,v.2)) by fun_prop))
    (hg.comp (show Continuous (fun v : ℝ × ℝ => (v.1,a,b,v.2)) by fun_prop))
    (fun z t => hderiv z a b t) 0 1 z

end
end RHTower.D4BMOriginalBaseCircleJets

namespace RHTower.D4BMOriginalBaseCircleJets
noncomputable section
set_option autoImplicit false

/-- The actual first and second base derivatives commute with the full source cube. -/
theorem cube_baseOperator (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℂ)
    (hS : ∀ a b t, ContDiff ℝ ∞ (fun v : ℝ × ℝ => f v.1 v.2 a b t))
    (hC : ∀ j : Fin 5, Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      baseOperator j (fun x k => f x k v.2.1 v.2.2.1 v.2.2.2) v.1.1 v.1.2))
    (j : Fin 5) (x k : ℝ) :
    baseOperator j (fun x k => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f x k a b t) x k=
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        baseOperator j (fun x k => f x k a b t) x k := by
  let A (x k : ℝ) := ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f x k a b t
  let J (j : Fin 5) (x k : ℝ) := ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
    baseOperator j (fun x k => f x k a b t) x k
  have hX (a b t k : ℝ) : ContDiff ℝ ∞ (fun x => f x k a b t) :=
    (hS a b t).comp (show ContDiff ℝ ∞ (fun x : ℝ => (x,k)) by fun_prop)
  have hK (a b t x : ℝ) : ContDiff ℝ ∞ (fun k => f x k a b t) :=
    (hS a b t).comp (show ContDiff ℝ ∞ (fun k : ℝ => (x,k)) by fun_prop)
  have hcx (j : Fin 5) (k : ℝ) := (hC j).comp
    (show Continuous (fun v : ℝ × ℝ × ℝ × ℝ => ((v.1,k),v.2)) by fun_prop)
  have hck (j : Fin 5) (x : ℝ) := (hC j).comp
    (show Continuous (fun v : ℝ × ℝ × ℝ × ℝ => ((x,v.1),v.2)) by fun_prop)
  have hx (x k : ℝ) : HasDerivAt (fun r => A r k) (J 4 x k) x := by
    apply cube_hasDerivAt _ _ (hcx 0 k) (hcx 4 k) _ x
    intro x a b t
    exact ((hX a b t k).differentiable (by simp) x).hasDerivAt
  have hk (x k : ℝ) : HasDerivAt (A x) (J 1 x k) k := by
    apply cube_hasDerivAt _ _ (hck 0 x) (hck 1 x) _ k
    intro k a b t
    exact ((hK a b t x).differentiable (by simp) k).hasDerivAt
  have hxx (x k : ℝ) : HasDerivAt (fun r => J 4 r k) (J 2 x k) x := by
    apply cube_hasDerivAt _ _ (hcx 4 k) (hcx 2 k) _ x
    intro x a b t
    exact (((contDiff_infty_iff_deriv.mp (hX a b t k)).2).differentiable (by simp) x).hasDerivAt
  have hkk (x k : ℝ) : HasDerivAt (J 1 x) (J 3 x k) k := by
    apply cube_hasDerivAt _ _ (hck 1 x) (hck 3 x) _ k
    intro k a b t
    exact (((contDiff_infty_iff_deriv.mp (hK a b t x)).2).differentiable (by simp) k).hasDerivAt
  fin_cases j
  · rfl
  · exact (hk x k).deriv
  · change deriv (deriv (fun r => A r k)) x=J 2 x k
    have he : deriv (fun r => A r k)=fun r => J 4 r k := funext (fun r => (hx r k).deriv)
    rw [he]
    exact (hxx x k).deriv
  · change deriv (deriv (A x)) k=J 3 x k
    have he : deriv (A x)=J 1 x := funext (fun r => (hk x r).deriv)
    rw [he]
    exact (hkk x k).deriv
  · exact (hx x k).deriv

end
end RHTower.D4BMOriginalBaseCircleJets
