import GaloisForLFunctions.RHTower.ChiRamanujanWeightedRationalTrace
import GaloisForLFunctions.RHTower.ChiRamanujanCubicCriticalBoundary

/-!
# Complete tested rational cubic and its critical boundary

The literal two-axis-excluded rational series equals the connected arithmetic
source at every imaginary frequency. Actual absolute coefficient control
justifies termwise integration for every integrable frequency test. Every
fixed smooth compact test then has the full critical finite-part, product-PV
and intersection-mass boundary. Physical height transfer remains separate.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology ContDiff
namespace RHTower.BAGTrace

theorem rationalCharacter_one (α : ℂ) : rationalCharacter α rationalOne=1 := by
  simp [rationalCharacter,rationalOne]

theorem weightedRationalCubic_axis_left (σ : ℝ) (α β : ℂ) (a : PositiveRational) :
    weightedRationalCubic σ α β (rationalOne,a)=weightedRationalAxis σ β a := by
  simp only [weightedRationalCubic,rationalCubic_axis_left,rationalCharacter_one,mul_one,
    weightedRationalAxis]

theorem weightedRationalCubic_axis_right (σ : ℝ) (α β : ℂ) (a : PositiveRational) :
    weightedRationalCubic σ α β (a,rationalOne)=weightedRationalAxis σ α a := by
  simp only [weightedRationalCubic,rationalCubic_axis_right,rationalCharacter_one,mul_one,
    weightedRationalAxis]

private theorem weightedRationalCubic_origin (σ : ℝ) (α β : ℂ) :
    weightedRationalCubic σ α β (rationalOne,rationalOne)=1 := by
  simp [weightedRationalCubic,rationalCubic,rationalCharacter,rationalOne,rationalRamanujanCoefficient,
    pmPowerDampedRamanujanDenominator]

private theorem complex_remove_two_slices_hasSum {X : Type} [DecidableEq X] (e : X)
    {f : X × X → ℂ} {A B C : ℂ} (h : HasSum f A)
    (hl : HasSum (fun x => f (e,x)) B) (hr : HasSum (fun x => f (x,e)) C) :
    HasSum (fun v => if v.1=e ∨ v.2=e then 0 else f v) (A-B-C+f (e,e)) := by
  have hm {Y Z : Type} {a : Y → ℂ} {b : Z → ℂ} {x y : ℂ}
      (ha : HasSum a x) (hb : HasSum b y) :
      HasSum (fun v : Y × Z => a v.1*b v.2) (x*y) :=
    ha.mul hb (summable_mul_of_summable_norm ha.summable.norm hb.summable.norm)
  have hd := hasSum_ite_eq e (1 : ℂ)
  have h' := ((h.sub (hm hd hl)).sub (hm hr hd)).add ((hm hd hd).mul_left (f (e,e)))
  simp only [one_mul,mul_one] at h'
  refine h'.congr_fun ?_
  rintro ⟨x,y⟩
  by_cases hx : x=e <;> by_cases hy : y=e <;> simp [hx,hy]

def weightedRationalOffAxes (σ : ℝ) (α β : ℂ) (w : PositiveRational × PositiveRational) : ℂ := by
  classical
  exact if w.1.1=1 ∨ w.2.1=1 then 0 else weightedRationalCubic σ α β w

theorem weightedRationalOffAxes_hasSum {σ : ℝ} (hσ : 1 < σ) {α β : ℂ}
    (hα : α.re=0) (hβ : β.re=0) :
    HasSum (weightedRationalOffAxes σ α β)
      (sixZetaCubic σ α β-twoZetaAxis σ β-twoZetaAxis σ α+1) := by
  classical
  have hl := (weightedRationalAxis_hasSum hσ hβ).congr_fun
    (weightedRationalCubic_axis_left σ α β)
  have hr := (weightedRationalAxis_hasSum hσ hα).congr_fun
    (weightedRationalCubic_axis_right σ α β)
  have h := complex_remove_two_slices_hasSum rationalOne (weightedRationalCubic_hasSum hσ hα hβ) hl hr
  rw [weightedRationalCubic_origin] at h
  have he (a : PositiveRational) : a=rationalOne ↔ a.1=1 := Subtype.ext_iff
  exact h.congr_fun (fun v => by simp only [weightedRationalOffAxes,he])

theorem norm_weightedRationalOffAxes (σ : ℝ) {α β : ℂ}
    (hα : α.re=0) (hβ : β.re=0) (v : PositiveRational × PositiveRational) :
    ‖weightedRationalOffAxes σ α β v‖=|rationalOffAxesCubic σ v| := by
  simp only [weightedRationalOffAxes,rationalOffAxesCubic]
  split_ifs <;> simp only [norm_zero,abs_zero,norm_weightedRationalCubic σ hα hβ]

/-- Exact identification of the actual weighted rational source with the full connected kernel. -/
theorem weightedRationalOffAxes_hasSum_connectedKernel (Φ : ℝ × ℝ → ℂ)
    {ε : ℝ} (hε : 0 < ε) (w : ℝ × ℝ) :
    HasSum (fun a => weightedRationalOffAxes (1+ε) ((w.1 : ℂ)*Complex.I)
      ((w.2 : ℂ)*Complex.I) a*Φ w) (cubicConnectedKernel Φ ε w) := by
  have hσ : 1 < (1+ε : ℝ) := by linarith
  have hα : ((w.1 : ℂ)*Complex.I).re=0 := by simp
  have hβ : ((w.2 : ℂ)*Complex.I).re=0 := by simp
  have h := (weightedRationalOffAxes_hasSum hσ hα hβ).mul_right (Φ w)
  have hl := (complete_weighted_offAxes_trace
    (σ := ((1+ε : ℝ) : ℂ)) (by simpa using hσ) hα hβ).mul_const (Φ w)
  have he := tendsto_nhds_unique hl (complete_weighted_offAxes_connectedKernel Φ hε w)
  change (sixZetaCubic _ _ _-twoZetaAxis _ _-twoZetaAxis _ _+1)*Φ w=_ at he
  rwa [he] at h

theorem continuous_rationalCharacter_frequency (a : PositiveRational) :
    Continuous (fun u : ℝ => rationalCharacter ((u : ℂ)*Complex.I) a) := by
  have h0 : (a.1 : ℂ) ≠ 0 := by exact_mod_cast a.2.ne'
  exact ((Complex.continuous_ofReal.mul continuous_const).neg).const_cpow (.inl h0)

theorem continuous_weightedRationalOffAxes_frequency (σ : ℝ) (a : PositiveRational × PositiveRational) :
    Continuous (fun w : ℝ × ℝ => weightedRationalOffAxes σ ((w.1 : ℂ)*Complex.I)
      ((w.2 : ℂ)*Complex.I) a) := by
  classical
  unfold weightedRationalOffAxes
  split_ifs
  · exact continuous_const
  · exact ((continuous_const.mul ((continuous_rationalCharacter_frequency a.1).comp
      continuous_fst)).mul ((continuous_rationalCharacter_frequency a.2).comp continuous_snd))

def rationalCubicTest (Φ : ℝ × ℝ → ℂ) (σ : ℝ) (a : PositiveRational × PositiveRational) : ℂ :=
  ∫ w : ℝ × ℝ, weightedRationalOffAxes σ ((w.1 : ℂ)*Complex.I) ((w.2 : ℂ)*Complex.I) a*Φ w

/-- Termwise integration of the complete unordered rational cubic, with domination proved
from the actual absolute coefficient mass. The test may be any integrable frequency function. -/
theorem rationalCubicTest_hasSum {Φ : ℝ × ℝ → ℂ} (hΦ : Integrable Φ)
    {ε : ℝ} (hε : 0 < ε) :
    HasSum (rationalCubicTest Φ (1+ε)) (∫ w : ℝ × ℝ,cubicConnectedKernel Φ ε w) := by
  have hσ : 1 < (1+ε : ℝ) := by linarith
  have hn : Summable (fun a => |rationalOffAxesCubic (1+ε) a|) := by
    simpa only [Real.norm_eq_abs] using summable_norm_rationalOffAxesCubic hσ
  apply hasSum_integral_of_dominated_convergence
    (fun a w => |rationalOffAxesCubic (1+ε) a| * ‖Φ w‖)
  · intro a
    exact (continuous_weightedRationalOffAxes_frequency (1+ε) a).aestronglyMeasurable.mul
      hΦ.aestronglyMeasurable
  · intro a
    exact Eventually.of_forall fun w => by
      rw [norm_mul,norm_weightedRationalOffAxes _ (by simp) (by simp)]
  · exact Eventually.of_forall (fun w => hn.mul_right ‖Φ w‖)
  · simp_rw [tsum_mul_right]
    exact hΦ.norm.const_mul _
  · exact Eventually.of_forall (weightedRationalOffAxes_hasSum_connectedKernel Φ hε)

/-- Every fixed smooth compact test of the actual rational series has the full critical
finite-part / product-PV / intersection-mass boundary. No physical limit is assumed. -/
theorem exists_rationalCubicTest_criticalBoundary {Φ : ℝ × ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) :
    ∃ R > 0, Function.support Φ ⊆ Icc (-R,-R) (R,R) ∧
      Tendsto (fun ε : ℝ => ∑' a,rationalCubicTest Φ (1+ε) a)
        (𝓝[>] 0) (𝓝 (cubicCriticalBoundaryValue Φ R)) := by
  obtain ⟨R,hR,hsupp,hlim⟩ := exists_cubicCriticalBoundary hΦ hc
  refine ⟨R,hR,hsupp,hlim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (rationalCubicTest_hasSum (hΦ.continuous.integrable_of_hasCompactSupport hc) hε).tsum_eq.symm

end RHTower.BAGTrace
