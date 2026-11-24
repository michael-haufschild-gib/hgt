import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.TorusSections

/-! # Sharp torus volume loss near a set meeting every coordinate circle -/
open MeasureTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Origins whose whole forward cube on the selected coordinates stays in F. -/
def cubeOrigins (F : Set (UnitAddTorus I)) (g : ℝ) (S : Finset I) : Set (UnitAddTorus I) :=
  {x | ∀ u : I → ℝ, (∀ i, u i∈Icc (0:ℝ) g) → (∀ i, i∉S → u i=0) →
    x+(fun i => (u i:UnitAddCircle))∈F}

omit [Fintype I] [DecidableEq I] in
theorem closed_cubeOrigins {F : Set (UnitAddTorus I)} (hF : IsClosed F) (g : ℝ) (S : Finset I) :
    IsClosed (cubeOrigins F g S) := by
  simp only [cubeOrigins,setOf_forall]
  exact isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    hF.preimage (continuous_id.add continuous_const)

omit [Fintype I] [DecidableEq I] in
private theorem origins_subset (F : Set (UnitAddTorus I)) {g : ℝ} (hg : 0≤g) (S : Finset I) :
    cubeOrigins F g S ⊆ F := by
  intro x hx
  simpa only [AddCircle.coe_zero,show (fun _ : I => (0:UnitAddCircle))=0 from rfl,add_zero] using
    hx (fun _ => 0) (fun _ => ⟨le_rfl,hg⟩) (fun _ _ => rfl)

omit [Fintype I] in
private theorem insert_axis (F : Set (UnitAddTorus I)) (g : ℝ) (S : Finset I) (i : I) (hi : i∉S)
    {x : UnitAddTorus I} (hx : x∈cubeOrigins F g (insert i S)) (t : ℝ) (ht : t∈Icc (0:ℝ) g) :
    x+Pi.single i (t:UnitAddCircle)∈cubeOrigins F g S := by
  intro u hu hs
  let v := Function.update u i t
  have hbox (j : I) : v j ∈ Icc (0:ℝ) g := by
    by_cases hj : j=i
    · simpa only [v,hj,Function.update_self] using ht
    · simpa only [v,Function.update_of_ne hj] using hu j
  have hzero (j : I) (hj : j∉insert i S) : v j=0 := by
    simp only [Finset.mem_insert,not_or] at hj
    exact (Function.update_of_ne hj.1 ..).trans (hs j hj.2)
  have he : x+Pi.single i (t:UnitAddCircle)+(fun j => (u j:UnitAddCircle)) =
      x+(fun j => (v j:UnitAddCircle)) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [Pi.add_apply,Pi.single_eq_same,hs i hi,AddCircle.coe_zero,add_zero,v,Function.update_self]
    · simp only [Pi.add_apply,Pi.single_eq_of_ne hj,add_zero,v,Function.update_of_ne hj]
  rw [he]
  exact hx v hbox hzero

/-- If the complement of a closed target meets every coordinate circle,
the Haar mass of origins of side-g cubes inside it is at most (1-g)^D. -/
theorem cube_volume_bound {F : Set (UnitAddTorus I)} (hF : IsClosed F)
    (hc : ∀ i : I, ∀ x : UnitAddTorus I, ∃ t : UnitAddCircle, x+Pi.single i t∉F)
    {g : ℝ} (hg : 0≤g) (hg' : g<1) (S : Finset I) :
    volume (cubeOrigins F g S) ≤ ENNReal.ofReal (1-g)^S.card*volume F := by
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.card_empty,pow_zero,one_mul] using measure_mono (origins_subset F hg ∅)
  | @insert i S hi ih =>
    have hcut (x : UnitAddTorus I) := (hc i x).imp fun t ht =>
      fun h => ht (origins_subset F hg S h)
    have h := axis_section_bound i (closed_cubeOrigins hF g (insert i S)).measurableSet
      (closed_cubeOrigins hF g S).measurableSet hg hg' hcut (fun _ hx => insert_axis F g S i hi hx)
    rw [Finset.card_insert_of_notMem hi,pow_succ',mul_assoc]
    exact h.trans (mul_le_mul_right ih _)

#print axioms cube_volume_bound
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
