import GaloisForLFunctions.HTGeometry.PeriodicLatticeBranching

/-!
# Whole-fiber lattice containment for the periodic parameter

The exact cancellation identity forces every distinguished preimage onto its
labeled lattice. The quadratic discriminant proves all such fibers simple.
-/

noncomputable section
open Complex Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.PeriodicLatticeFibers

open PeriodicLatticeSections PeriodicLatticeBranching

def phase (w : ℂ) : ℂ := exp (Real.pi*I*w/12)
def fiberMark (j : ℤ) : ℂ := exp ((2*Real.pi*I/3)*j)
def fiber (j : ℤ) (w : ℂ) : ℂ :=
  numerator (phase w)-fiberMark j*denominator (phase w)
def latticeMap (w : ℂ) : ℂ := rationalMap (phase w)

theorem phase_ne_zero (w : ℂ) : phase w ≠ 0 := exp_ne_zero _

theorem reciprocal_coordinates {t : ℂ} (ht : t ≠ 0) :
    numerator t⁻¹=denominator t/t^2 ∧ denominator t⁻¹=numerator t/t^2 := by
  dsimp [numerator,denominator]
  constructor <;> field_simp

theorem conjugate_coordinates (t : ℂ) :
    numerator (conj t)=conj (numerator t) ∧
      denominator (conj t)=conj (denominator t) := by
  simp [numerator,denominator,a_conj]

theorem phase_neg (w : ℂ) : phase (-w)=(phase w)⁻¹ := by
  rw [phase,phase,← exp_neg]
  congr 1
  ring

theorem phase_neg_conj (w : ℂ) : phase (-conj w)=conj (phase w) := by
  simp [phase,← exp_conj,map_ofNat]

theorem fiberMark_cube (j : ℤ) : fiberMark j^3=1 := by
  rw [fiberMark,← exp_nat_mul]
  rw [← exp_zero]
  exact exp_eq_exp_iff_exists_int.mpr ⟨j,by ring⟩

theorem no_common_zero (t : ℂ) : ¬ (numerator t=0 ∧ denominator t=0) := by
  rintro ⟨hn,hd⟩
  have hab : a*t=1 := (sub_eq_zero.mp hd).symm
  rcases mul_eq_zero.mp hn with ht | ht
  · simp [ht] at hab
  · have ht' : t=a := sub_eq_zero.mp ht
    rw [ht',← pow_two,a_sq] at hab
    norm_num at hab

theorem denominator_ne_zero_of_fiber {t c : ℂ}
    (hf : numerator t=c*denominator t) : denominator t ≠ 0 := by
  intro h
  exact no_common_zero t ⟨by simpa [h] using hf,h⟩

theorem latticeMap_fiber_iff (j : ℤ) (w : ℂ) : latticeMap w=fiberMark j ↔ fiber j w=0 := by
  by_cases hd : denominator (phase w)=0
  · have hn : numerator (phase w) ≠ 0 := fun h => no_common_zero _ ⟨h,hd⟩
    simp [latticeMap,rationalMap,fiber,hd,hn,fiberMark]
    exact (exp_ne_zero _).symm
  · simp [latticeMap,rationalMap,fiber,div_eq_iff hd,sub_eq_zero]

theorem phase_power_of_fiber {t c : ℂ} (ht : t ≠ 0) (hc : c^3=1)
    (hf : numerator t=c*denominator t) : t^8=c := by
  have hd := denominator_ne_zero_of_fiber hf
  have hv : numerator t^3-denominator t^3=0 := by
    rw [hf,mul_pow,hc]
    ring
  have hq := quotient_factor ht
  rw [hv,zero_mul] at hq
  field_simp at hq
  have hh : t^8*denominator t=c*denominator t := by
    rw [← hf]
    linear_combination -hq
  have hh' := congrArg (fun z => z/denominator t) hh
  simpa [hd] using hh'

/-- This implication controls the complete preimage, including any unanticipated points. -/
theorem every_fiber_labeled (j : ℤ) {w : ℂ} (hw : fiber j w=0) :
    ∃ k : ℤ, w=j+3*k := by
  have hf : numerator (phase w)=fiberMark j*denominator (phase w) := sub_eq_zero.mp hw
  have he := phase_power_of_fiber (phase_ne_zero w) (fiberMark_cube j) hf
  simp only [phase,fiberMark,← exp_nat_mul] at he
  obtain ⟨k,hk⟩ := exp_eq_exp_iff_exists_int.mp he
  refine ⟨k,?_⟩
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero hp I_ne_zero))
  linear_combination (3/2 : ℂ)*hk

theorem fiber_derivative_ne_zero {t c : ℂ} (hc : c^3=1)
    (hf : numerator t=c*denominator t) : 2*t+a*(c-1) ≠ 0 := by
  intro hd
  have hg : t^2+a*(c-1)*t-c=0 := by
    dsimp [numerator,denominator] at hf
    linear_combination hf
  have hd2 : (2*t+a*(c-1))^2=0 := by rw [hd]; norm_num
  have hp : c^2+4*c+1=0 := by
    linear_combination (3/2 : ℂ)*hd2-6*hg-(3/2 : ℂ)*(c-1)^2*a_sq
  have he : 15*c+3=0 := by linear_combination hc-(c-4)*hp
  have he' : c= -1/5 := by linear_combination (1/15 : ℂ)*he
  norm_num [he'] at hp

theorem phase_deriv (w : ℂ) :
    HasDerivAt phase (phase w*((Real.pi : ℂ)*I/12)) w := by
  have hs : HasDerivAt (fun w : ℂ => Real.pi*I*w/12) ((Real.pi : ℂ)*I/12) w := by
    convert! ((hasDerivAt_id w).const_mul ((Real.pi : ℂ)*I)).div_const 12 using 1
    simp
  exact (hasDerivAt_exp _).comp w hs

theorem fiber_deriv (j : ℤ) (w : ℂ) :
    HasDerivAt (fiber j)
      ((2*phase w+a*(fiberMark j-1))*(phase w*((Real.pi : ℂ)*I/12))) w := by
  have ht := phase_deriv w
  convert! (ht.mul (ht.sub_const a)).sub
    (((ht.const_mul a).const_sub 1).const_mul (fiberMark j)) using 1
  ring

/-- Every distinguished fiber is simple, without selecting or counting its roots. -/
theorem every_fiber_simple (j : ℤ) {w : ℂ} (hw : fiber j w=0) :
    analyticOrderAt (fiber j) w=1 := by
  have hf : numerator (phase w)=fiberMark j*denominator (phase w) := sub_eq_zero.mp hw
  have ha : AnalyticAt ℂ (fiber j) w := by
    unfold fiber numerator denominator phase
    fun_prop
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hw
  rw [(fiber_deriv j w).deriv]
  exact mul_ne_zero (fiber_derivative_ne_zero (fiberMark_cube j) hf)
    (mul_ne_zero (phase_ne_zero w) (div_ne_zero (mul_ne_zero hp I_ne_zero) (by norm_num)))

theorem every_actual_fiber_simple (j : ℤ) {w : ℂ} (hw : latticeMap w=fiberMark j) :
    analyticOrderAt (fun z => latticeMap z-fiberMark j) w=1 := by
  have hf := (latticeMap_fiber_iff j w).mp hw
  have hd : denominator (phase w) ≠ 0 := denominator_ne_zero_of_fiber (sub_eq_zero.mp hf)
  let u : ℂ → ℂ := fun z => (denominator (phase z))⁻¹
  have ha : AnalyticAt ℂ (fiber j) w := by unfold fiber numerator denominator phase; fun_prop
  have hb : AnalyticAt ℂ u w := by
    apply AnalyticAt.inv
    · unfold denominator phase
      fun_prop
    · exact hd
  have hu : analyticOrderAt u w=0 := hb.analyticOrderAt_eq_zero.mpr (inv_ne_zero hd)
  have hc : ContinuousAt (fun z => denominator (phase z)) w := by unfold denominator phase; fun_prop
  have he : (fun z => latticeMap z-fiberMark j) =ᶠ[𝓝 w] fiber j*u := by
    filter_upwards [hc.eventually_ne hd] with z hz
    simp only [latticeMap,rationalMap,Pi.mul_apply,fiber,u]
    field_simp
  rw [analyticOrderAt_congr he,analyticOrderAt_mul ha hb,every_fiber_simple j hf,hu]
  simp

def affineCoordinate (w : ℂ) : ℂ := 1/2+Real.pi*I*w
def branchPoint (k : ℤ) : ℂ := (point 1 criticalValue k-1/2)/(Real.pi*I)

theorem latticeMap_affine (w : ℂ) : latticeMap w=parameterMap 1 (affineCoordinate w) := by
  dsimp [latticeMap,parameterMap,phase,parameter,affineCoordinate]
  congr 2
  ring

theorem affine_branchPoint (k : ℤ) : affineCoordinate (branchPoint k)=point 1 criticalValue k := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp [affineCoordinate,branchPoint]
  field_simp
  ring

theorem branchPoint_injective : Function.Injective branchPoint := by
  intro j k h
  apply point_injective (by norm_num : (1 : ℝ) ≠ 0) criticalValue
  have hh := congrArg affineCoordinate h
  simpa only [affine_branchPoint] using hh

theorem latticeMap_branch_order (k : ℤ) :
    AnalyticAt ℂ latticeMap (branchPoint k) ∧
      analyticOrderAt (fun w => latticeMap w-latticeMap (branchPoint k)) (branchPoint k)=2 := by
  have ha : AnalyticAt ℂ (parameterMap 1) (affineCoordinate (branchPoint k)) := by
    apply parameterMap_analyticAt
    rw [affine_branchPoint,parameter_point (by norm_num : (1 : ℝ) ≠ 0) criticalValue_ne_zero]
    exact denominator_criticalValue_ne_zero
  have hc : AnalyticAt ℂ affineCoordinate (branchPoint k) := by unfold affineCoordinate; fun_prop
  have he : latticeMap=parameterMap 1 ∘ affineCoordinate := funext latticeMap_affine
  constructor
  · rw [he]
    exact ha.comp hc
  · have hd : HasDerivAt affineCoordinate ((Real.pi : ℂ)*I) (branchPoint k) := by
      convert! ((hasDerivAt_id (branchPoint k)).const_mul ((Real.pi : ℂ)*I)).const_add (1/2) using 1
      simp
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hf : (fun w => latticeMap w-latticeMap (branchPoint k))=
        (fun s => parameterMap 1 s-parameterMap 1 (point 1 criticalValue k)) ∘ affineCoordinate := by
      ext w
      simp [latticeMap_affine,affine_branchPoint]
    rw [hf,analyticOrderAt_comp_of_deriv_ne_zero hc
      (by rw [hd.deriv]; exact mul_ne_zero hp I_ne_zero),affine_branchPoint]
    exact parameterMap_branch_order (by norm_num) k

/-- The same map whose complete distinguished fibers are lattice-labeled has
infinitely many ordinary branch points. -/
theorem labeled_lattice_infinite_branching :
    (∀ (j : ℤ) (w : ℂ), fiber j w=0 →
      (∃ k : ℤ, w=j+3*k) ∧ analyticOrderAt (fiber j) w=1) ∧
    ∃ ρ : ℤ → ℂ, Function.Injective ρ ∧ ∀ k,
      AnalyticAt ℂ latticeMap (ρ k) ∧
      analyticOrderAt (fun w => latticeMap w-latticeMap (ρ k)) (ρ k)=2 := by
  exact ⟨fun j w hw => ⟨every_fiber_labeled j hw,every_fiber_simple j hw⟩,
    branchPoint,branchPoint_injective,latticeMap_branch_order⟩

end GaloisForLFunctions.HTGeometry.PeriodicLatticeFibers
