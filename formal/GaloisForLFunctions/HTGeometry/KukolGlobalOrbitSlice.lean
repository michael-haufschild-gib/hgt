import GaloisForLFunctions.HTGeometry.KukolComplexDiagonalOrbits

/-!
# Global slices and arbitrary complex linear unipotent subgroups

The invariant candidates in Kukol, arXiv:2609.10214, Section 5 yield an
explicit global zero-anchor slice. An equivalence separates each regular
family into a group parameter and its unique canonical representative.
For any complex linear subgroup, adding the quotient-valued gauge gives
complete subgroup orbit invariants.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {κ ι : Type*} [Fintype κ]

/-- Fix the anchor's transverse coordinate at zero by an explicit group translate. -/
def kukolDiagonalNormalize (anchor : ι) (x : ι → KukolRegularPoint κ) (j : ι) :
    KukolRegularPoint κ := kukolRegularAction (-kukolDiagonalGauge anchor x) (x j)

/-- The chosen gauge sends the anchor exactly to the zero transverse slice. -/
theorem kukolDiagonalNormalize_anchor (anchor : ι) (x : ι → KukolRegularPoint κ) :
    (kukolDiagonalNormalize anchor x anchor).transverse=0 := by
  funext k
  dsimp [kukolDiagonalNormalize,kukolRegularAction,kukolDiagonalGauge]
  field_simp
  ring

/-- The normalized transverse coordinates are exactly the paper's pair invariants divided by the anchor. -/
theorem kukolDiagonalNormalize_transverse (anchor j : ι) (x : ι → KukolRegularPoint κ) (k : κ) :
    (kukolDiagonalNormalize anchor x j).transverse k =
      kukolRegularPair (x anchor) (x j) k/((x anchor).minus : ℂ) := by
  dsimp [kukolDiagonalNormalize,kukolRegularAction,kukolDiagonalGauge,kukolRegularPair]
  field_simp
  ring

/-- Canonical representatives are constant along entire complex unipotent orbits. -/
theorem kukolDiagonalNormalize_action (anchor : ι) (u : κ → ℂ)
    (x : ι → KukolRegularPoint κ) :
    kukolDiagonalNormalize anchor (fun j => kukolRegularAction u (x j)) =
      kukolDiagonalNormalize anchor x := by
  funext j
  unfold kukolDiagonalNormalize
  rw [kukolDiagonalGauge_action,← kukolRegularAction_add]
  congr 1
  abel

/-- Canonical representatives have exactly the same information as the complete invariant tuple. -/
theorem kukolDiagonalNormalize_eq_iff (anchor : ι) (x y : ι → KukolRegularPoint κ) :
    kukolDiagonalNormalize anchor x=kukolDiagonalNormalize anchor y ↔
      kukolDiagonalInvariants anchor x=kukolDiagonalInvariants anchor y := by
  constructor
  · intro h
    have he := congrArg (kukolDiagonalInvariants anchor) h
    change kukolDiagonalInvariants anchor (fun j =>
      kukolRegularAction (-kukolDiagonalGauge anchor x) (x j)) =
      kukolDiagonalInvariants anchor (fun j =>
        kukolRegularAction (-kukolDiagonalGauge anchor y) (y j)) at he
    simpa only [kukolDiagonalInvariants_action] using he
  · intro h
    obtain ⟨u,hu⟩ := (kukolDiagonal_orbit_iff anchor x y).mpr h
    rw [← funext hu,kukolDiagonalNormalize_action]

/-- The global zero-anchor slice; every regular orbit meets it once. -/
def KukolDiagonalSlice (anchor : ι) :=
  {x : ι → KukolRegularPoint κ | (x anchor).transverse=0}

/-- An exact trivialization of every simultaneous regular orbit, including arbitrary indexed families. -/
def kukolDiagonalOrbitEquiv (anchor : ι) :
    (ι → KukolRegularPoint κ) ≃ (κ → ℂ) × KukolDiagonalSlice (κ := κ) anchor where
  toFun x := (kukolDiagonalGauge anchor x,
    ⟨kukolDiagonalNormalize anchor x,kukolDiagonalNormalize_anchor anchor x⟩)
  invFun p j := kukolRegularAction p.1 (p.2.val j)
  left_inv x := by
    funext j
    dsimp only [kukolDiagonalNormalize]
    rw [← kukolRegularAction_add,add_neg_cancel,kukolRegularAction_zero]
  right_inv p := by
    have hs : kukolDiagonalGauge anchor p.2.val=0 := by
      funext k
      dsimp [kukolDiagonalGauge]
      rw [p.2.property]
      simp
    apply Prod.ext
    · change kukolDiagonalGauge anchor (fun j => kukolRegularAction p.1 (p.2.val j))=p.1
      rw [kukolDiagonalGauge_action,hs,zero_add]
    · apply Subtype.ext
      funext j
      dsimp only [kukolDiagonalNormalize]
      rw [kukolDiagonalGauge_action,hs,zero_add,← kukolRegularAction_add,
        neg_add_cancel,kukolRegularAction_zero]

/-- Quotient-valued gauge data records exactly the invariants for an arbitrary complex linear subgroup. -/
def kukolSubgroupInvariants (W : Submodule ℂ (κ → ℂ)) (anchor : ι)
    (x : ι → KukolRegularPoint κ) :=
  (kukolDiagonalInvariants anchor x,
    (Submodule.Quotient.mk (kukolDiagonalGauge anchor x) : (κ → ℂ) ⧸ W))

/-- The quotient gauge is invariant under every parameter in the selected subgroup. -/
theorem kukolSubgroupInvariants_action (W : Submodule ℂ (κ → ℂ)) (anchor : ι)
    (u : W) (x : ι → KukolRegularPoint κ) :
    kukolSubgroupInvariants W anchor (fun j => kukolRegularAction u.val (x j)) =
      kukolSubgroupInvariants W anchor x := by
  apply Prod.ext
  · exact kukolDiagonalInvariants_action anchor u.val x
  · change (Submodule.Quotient.mk (kukolDiagonalGauge anchor
        (fun j => kukolRegularAction u.val (x j))) : (κ → ℂ) ⧸ W) =
      Submodule.Quotient.mk (kukolDiagonalGauge anchor x)
    rw [kukolDiagonalGauge_action]
    apply (Submodule.Quotient.eq W).mpr
    simpa only [add_sub_cancel_left] using u.property

/-- Complete orbit classification works for every complex linear subgroup, including proper subgroups. -/
theorem kukolSubgroup_orbit_iff (W : Submodule ℂ (κ → ℂ)) (anchor : ι)
    (x y : ι → KukolRegularPoint κ) :
    (∃ u : W,∀ j,kukolRegularAction u.val (x j)=y j) ↔
      kukolSubgroupInvariants W anchor x=kukolSubgroupInvariants W anchor y := by
  constructor
  · rintro ⟨u,hu⟩
    have h := kukolSubgroupInvariants_action W anchor u x
    simpa only [funext hu] using h.symm
  · intro h
    have hi : kukolDiagonalInvariants anchor x=kukolDiagonalInvariants anchor y := congrArg Prod.fst h
    have hq : (Submodule.Quotient.mk (kukolDiagonalGauge anchor x) : (κ → ℂ) ⧸ W)=
        Submodule.Quotient.mk (kukolDiagonalGauge anchor y) := congrArg Prod.snd h
    obtain ⟨u,hu⟩ := (kukolDiagonal_orbit_iff anchor x y).mpr hi
    have hm : u ∈ W := by
      have he := (Submodule.Quotient.eq' W).mp hq
      rw [← funext hu,kukolDiagonalGauge_action] at he
      convert he using 1
      abel
    exact ⟨⟨u,hm⟩,hu⟩

end GaloisForLFunctions.HTGeometry
