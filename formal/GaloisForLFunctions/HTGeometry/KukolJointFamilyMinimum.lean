import GaloisForLFunctions.HTGeometry.KukolTubePotentialMinimum

/-!
# Compatibility of canonical parameters for joined tube families

Application of Kukol, *Extended Future Tube Conjecture for Unipotent Subgroups*,
arXiv:2609.10214.

Applying the paper's unique-minimum mechanism to a joined native family gives
an exact compatibility criterion and a strictly positive cost for incompatible minima.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℝ E] in
/-- Joining finite families adds their native potentials without changing any summands. -/
theorem kukolTubePotential_sum_family
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (v' : κ → KukolLightCone E) (r' s' : κ → ℝ) (z' : κ → E) (u : E) :
    kukolTubePotential (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z') u =
      kukolTubePotential v r s z u+kukolTubePotential v' r' s' z' u := by
  simp [kukolTubePotential,Fintype.sum_sum_type]

omit [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ] in
/-- The simultaneous subgroup domain is exactly the intersection of the two domains. -/
theorem kukolConstrainedTubeDomain_sum_family (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (v' : κ → KukolLightCone E) (r' s' : κ → ℝ) (z' : κ → E) :
    kukolConstrainedTubeDomain W (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z') =
      kukolConstrainedTubeDomain W v r s z ∩ kukolConstrainedTubeDomain W v' r' s' z' := by
  ext u
  simp only [kukolConstrainedTubeDomain,kukolTubeDomain,Set.mem_inter_iff,Set.mem_setOf_eq,Sum.forall,
    Sum.elim_inl,Sum.elim_inr]
  tauto

/-- No admissible point shares the minimum value unless it is the canonical minimizer. -/
theorem kukolTubeMinimumValue_eq_iff (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι)
    (u : kukolConstrainedTubeDomain W v r s z) :
    kukolTubePotential v r s z u=kukolTubeMinimumValue W v r s z anchor ↔
      u.val=kukolTubeMinimizer W v r s z anchor := by
  constructor
  · intro he
    apply (kukolTubeMinimizer_eq_iff W v r s z anchor u).mpr
    refine ⟨u.property,?_⟩
    intro w hw
    change kukolTubePotential v r s z u ≤ kukolTubePotential v r s z w
    rw [he]
    exact (kukolTubeMinimizer_spec W v r s z anchor).2 hw
  · intro he
    simp only [he,kukolTubeMinimumValue]

/-- Sharing one parameter can only increase the total minimum relative to separate minimization. -/
theorem kukolTubeMinimumValue_joint_ge (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι)
    (v' : κ → KukolLightCone E) (r' s' : κ → ℝ) (z' : κ → E) (anchor' : κ) :
    kukolTubeMinimumValue W v r s z anchor+kukolTubeMinimumValue W v' r' s' z' anchor' ≤
      kukolTubeMinimumValue W (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z')
        (Sum.inl anchor) := by
  have hu := (kukolTubeMinimizer_spec W (Sum.elim v v') (Sum.elim r r')
    (Sum.elim s s') (Sum.elim z z') (Sum.inl anchor)).1
  rw [kukolConstrainedTubeDomain_sum_family] at hu
  have h := (kukolTubeMinimizer_spec W v r s z anchor).2 hu.1
  have h' := (kukolTubeMinimizer_spec W v' r' s' z' anchor').2 hu.2
  simpa only [kukolTubeMinimumValue,kukolTubePotential_sum_family] using add_le_add h h'

/-- The joint minimum equals the sum exactly when the two canonical parameters agree. -/
theorem kukolTubeMinimumValue_joint_eq_iff (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι)
    (v' : κ → KukolLightCone E) (r' s' : κ → ℝ) (z' : κ → E) (anchor' : κ) :
    kukolTubeMinimumValue W (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z')
        (Sum.inl anchor)=
      kukolTubeMinimumValue W v r s z anchor+kukolTubeMinimumValue W v' r' s' z' anchor' ↔
      kukolTubeMinimizer W v r s z anchor=kukolTubeMinimizer W v' r' s' z' anchor' := by
  let joint := kukolTubeMinimizer W (Sum.elim v v') (Sum.elim r r')
    (Sum.elim s s') (Sum.elim z z') (Sum.inl anchor)
  have hj := kukolTubeMinimizer_spec W (Sum.elim v v') (Sum.elim r r')
    (Sum.elim s s') (Sum.elim z z') (Sum.inl anchor)
  have hjD : joint ∈ kukolConstrainedTubeDomain W v r s z ∩ kukolConstrainedTubeDomain W v' r' s' z' := by
    simpa only [kukolConstrainedTubeDomain_sum_family] using hj.1
  have hu := kukolTubeMinimizer_spec W v r s z anchor
  have hw := kukolTubeMinimizer_spec W v' r' s' z' anchor'
  constructor
  · intro he
    have ha := hu.2 hjD.1
    have hb := hw.2 hjD.2
    change kukolTubePotential (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z') joint=_ at he
    rw [kukolTubePotential_sum_family] at he
    have ea : kukolTubePotential v r s z joint=kukolTubeMinimumValue W v r s z anchor := by
      change kukolTubeMinimumValue W v r s z anchor ≤ kukolTubePotential v r s z joint at ha
      change kukolTubeMinimumValue W v' r' s' z' anchor' ≤ kukolTubePotential v' r' s' z' joint at hb
      linarith
    have eb : kukolTubePotential v' r' s' z' joint=kukolTubeMinimumValue W v' r' s' z' anchor' := by linarith
    exact ((kukolTubeMinimumValue_eq_iff W v r s z anchor ⟨joint,hjD.1⟩).mp ea).symm.trans
      ((kukolTubeMinimumValue_eq_iff W v' r' s' z' anchor' ⟨joint,hjD.2⟩).mp eb)
  · intro he
    have hD : kukolTubeMinimizer W v r s z anchor ∈
        kukolConstrainedTubeDomain W (Sum.elim v v') (Sum.elim r r')
          (Sum.elim s s') (Sum.elim z z') := by
      rw [kukolConstrainedTubeDomain_sum_family]
      exact ⟨hu.1,by simpa only [he] using hw.1⟩
    have hle := hj.2 hD
    change kukolTubePotential (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z') joint ≤
      kukolTubePotential (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z')
        (kukolTubeMinimizer W v r s z anchor) at hle
    rw [kukolTubePotential_sum_family,kukolTubePotential_sum_family] at hle
    have hval : kukolTubePotential v' r' s' z' (kukolTubeMinimizer W v r s z anchor)=
        kukolTubeMinimumValue W v' r' s' z' anchor' := by rw [he]; rfl
    rw [hval] at hle
    apply le_antisymm ?_ (kukolTubeMinimumValue_joint_ge W v r s z anchor v' r' s' z' anchor')
    simpa only [kukolTubeMinimumValue,kukolTubePotential_sum_family] using hle

/-- Incompatible canonical parameters force a strictly positive joint compromise cost. -/
theorem kukolTubeMinimumValue_joint_strict_iff (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι)
    (v' : κ → KukolLightCone E) (r' s' : κ → ℝ) (z' : κ → E) (anchor' : κ) :
    kukolTubeMinimumValue W v r s z anchor+kukolTubeMinimumValue W v' r' s' z' anchor' <
      kukolTubeMinimumValue W (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z')
        (Sum.inl anchor) ↔
      kukolTubeMinimizer W v r s z anchor≠kukolTubeMinimizer W v' r' s' z' anchor' := by
  have hle := kukolTubeMinimumValue_joint_ge W v r s z anchor v' r' s' z' anchor'
  have heq := kukolTubeMinimumValue_joint_eq_iff W v r s z anchor v' r' s' z' anchor'
  constructor
  · intro h he
    have hm := heq.mpr he
    linarith
  · intro h
    by_contra hn
    exact h (heq.mp (le_antisymm (le_of_not_gt hn) hle))

end GaloisForLFunctions.HTGeometry
