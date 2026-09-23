import GaloisForLFunctions.HTGeometry.KukolOrbitPotentialExhaustion
import Mathlib

/-!
# Strict convexity of simultaneous future-tube orbit potentials

Application of Kukol, *Extended Future Tube Conjecture for Unipotent Subgroups*,
arXiv:2609.10214, Sections 4–5. These results use the native imaginary orbit
action and its reciprocal-margin exhaustion on the full strict-state domain.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exponential strict-state coordinates cover the whole future cone, not a selected subclass. -/
theorem kukolStrictState_range :
    Set.range (fun p : ℝ × ℝ × E => kukolStrictState p.1 p.2.1 p.2.2)=kukolFuture := by
  ext x
  constructor
  · rintro ⟨⟨r,s,z⟩,rfl⟩
    exact kukolStrictState_mem_future r s z
  · rintro ⟨hm,hq⟩
    refine ⟨(Real.log x.1,Real.log (kukolQuadratic x),x.2.2),?_⟩
    apply Prod.ext
    · exact Real.exp_log hm
    · apply Prod.ext
      · dsimp [kukolStrictState]
        rw [Real.exp_log hm,Real.exp_log hq]
        unfold kukolQuadratic
        field_simp
        ring
      · rfl

/-- Reciprocation is convex on the positive half-line. -/
theorem kukol_convexOn_reciprocal : ConvexOn ℝ (Ioi (0 : ℝ)) (fun t => 1/t) := by
  refine ⟨convex_Ioi _,?_⟩
  intro x hx y hy a b ha hb hab
  change 0 < x at hx
  change 0 < y at hy
  have hmix : 0 < a*x+b*y := by
    simpa only [smul_eq_mul,Set.mem_Ioi] using (convex_Ioi (0 : ℝ) hx hy ha hb hab)
  simp only [smul_eq_mul,mul_one_div]
  rw [div_le_iff₀ hmix]
  have hid : (a/x+b/y)*(a*x+b*y)-1 = a*b*(x-y)^(2 : ℕ)/(x*y) := by
    have hb' : b=1-a := by linarith
    rw [hb']
    field_simp
    ring
  have hnonneg : 0 ≤ a*b*(x-y)^(2 : ℕ)/(x*y) :=
    div_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)) (mul_pos hx hy).le
  linarith

/-- Every strict-state margin is strictly concave on the entire parameter space. -/
theorem strictConcaveOn_kukolTubeMargin (v : KukolLightCone E) (r s : ℝ) (z : E) :
    StrictConcaveOn ℝ Set.univ (kukolTubeMargin v r s z) := by
  refine ⟨convex_univ,?_⟩
  intro u _ w _ huw a b ha hb hab
  have hb' : b=1-a := by linarith
  have hdef := kukolImaginaryAction_convex_defect u w v (kukolStrictState r s z) a
  have hc : 0 < (Real.exp r)^(2 : ℕ)+v.1^(2 : ℕ) :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.exp_pos r)) (sq_nonneg _)
  have hw : 0 < ‖u-w‖^(2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huw))
  have hp : 0 < a*b*((Real.exp r)^(2 : ℕ)+v.1^(2 : ℕ))*‖u-w‖^(2 : ℕ) :=
    mul_pos (mul_pos (mul_pos ha hb) hc) hw
  change a*kukolTubeMargin v r s z u+b*kukolTubeMargin v r s z w <
    kukolTubeMargin v r s z (a • u+b • w)
  change kukolTubeMargin v r s z (a • u+(1-a) • w) =
    a*kukolTubeMargin v r s z u+(1-a)*kukolTubeMargin v r s z w+
      a*(1-a)*((Real.exp r)^(2 : ℕ)+v.1^(2 : ℕ))*‖u-w‖^(2 : ℕ) at hdef
  rw [← hb'] at hdef
  linarith

/-- A single reciprocal margin is strictly convex on its full admissible orbit domain. -/
theorem strictConvexOn_kukolTubeReciprocal (v : KukolLightCone E) (r s : ℝ) (z : E) :
    StrictConvexOn ℝ {u | 0 < kukolTubeMargin v r s z u}
      (fun u => 1/kukolTubeMargin v r s z u) := by
  have hc := strictConcaveOn_kukolTubeMargin v r s z
  refine ⟨by simpa only [Set.mem_univ,true_and] using hc.convex_gt 0,?_⟩
  intro u hu w hw huw a b ha hb hab
  have hmix : 0 < a*kukolTubeMargin v r s z u+b*kukolTubeMargin v r s z w :=
    add_pos (mul_pos ha hu) (mul_pos hb hw)
  have hstrict := hc.2 (Set.mem_univ u) (Set.mem_univ w) huw ha hb hab
  simp only [smul_eq_mul] at hstrict ⊢
  have hrec := one_div_lt_one_div_of_lt hmix hstrict
  exact hrec.trans_le (by simpa only [smul_eq_mul] using
    kukol_convexOn_reciprocal.2 hu hw ha.le hb.le hab)

variable {ι : Type*}

/-- The common admissible domain for an arbitrary strict simultaneous family. -/
def kukolTubeDomain (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) : Set E :=
  {u | ∀ i,0 < kukolTubeMargin (v i) (r i) (s i) (z i) u}

/-- Every strict simultaneous family starts inside its own admissible domain. -/
theorem kukolTubeDomain_zero (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) :
    (0 : E) ∈ kukolTubeDomain v r s z := by
  intro i
  exact (kukolImaginaryAction_zero_future (v i).1 (v i).2.1 (r i) (s i) (v i).2.2 (z i)).2

/-- Arbitrary simultaneous admissible domains are convex. -/
theorem convex_kukolTubeDomain (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) :
    Convex ℝ (kukolTubeDomain v r s z) := by
  intro u hu w hw a b ha hb hab i
  exact (strictConvexOn_kukolTubeReciprocal (v i) (r i) (s i) (z i)).1
    (hu i) (hw i) ha hb hab

variable [Fintype ι]

/-- Finite simultaneous domains are open. -/
theorem isOpen_kukolTubeDomain (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) :
    IsOpen (kukolTubeDomain v r s z) := by
  unfold kukolTubeDomain
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
    (continuous_kukolTubeMargin (v i) (r i) (s i) (z i))

/-- The native reciprocal-margin potential is continuous on its entire admissible domain. -/
theorem continuousOn_kukolTubePotential (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) :
    ContinuousOn (kukolTubePotential v r s z) (kukolTubeDomain v r s z) := by
  unfold kukolTubePotential
  apply continuousOn_finsetSum
  intro i _
  exact continuousOn_const.div (continuous_kukolTubeMargin (v i) (r i) (s i) (z i)).continuousOn
    (fun u hu => (hu i).ne')

/-- The simultaneous potential is strictly positive throughout its domain. -/
theorem kukolTubePotential_mapsTo_pos (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (anchor : ι) : Set.MapsTo (kukolTubePotential v r s z) (kukolTubeDomain v r s z) (Ioi 0) := by
  intro u hu
  exact (one_div_pos.mpr (hu anchor)).trans_le
    (Finset.single_le_sum (fun i _ => (one_div_pos.mpr (hu i)).le) (Finset.mem_univ anchor))

/-- The whole finite-family orbit potential is strictly convex, without a separate convexity assumption. -/
theorem strictConvexOn_kukolTubePotential (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (anchor : ι) : StrictConvexOn ℝ (kukolTubeDomain v r s z) (kukolTubePotential v r s z) := by
  refine ⟨convex_kukolTubeDomain v r s z,?_⟩
  intro u hu w hw huw a b ha hb hab
  simp only [kukolTubePotential,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  have hterm (i : ι) := (strictConvexOn_kukolTubeReciprocal (v i) (r i) (s i) (z i)).2
    (hu i) (hw i) huw ha hb hab
  apply Finset.sum_lt_sum
  · intro i _
    exact (hterm i).le
  · exact ⟨anchor,Finset.mem_univ anchor,hterm anchor⟩

end GaloisForLFunctions.HTGeometry
