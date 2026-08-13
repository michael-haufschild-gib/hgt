import GaloisForLFunctions.HTGeometry.MeromorphicPlaneDifferential

/-!
# Constants and translations of the meromorphic plane field

The complex constants embed in the field of meromorphic functions on the plane, and every additive
translation of the variable acts on it as a field automorphism commuting with differentiation.
Together these make the meromorphic plane field a differential `ℂ`-algebra with a translation
action, the carrier on which lattice invariance defines the elliptic functions.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Translation of the variable preserves the codiscrete filter. -/
theorem tendsto_add_const_planeCodiscrete (c : ℂ) :
    Tendsto (fun z : ℂ => z + c) planeCodiscrete planeCodiscrete := by
  refine Filter.tendsto_def.mpr fun S hS => ?_
  refine mem_planeCodiscrete.mpr fun x => ?_
  have hshift : Tendsto (fun w : ℂ => w + c) (𝓝[≠] x) (𝓝[≠] (x + c)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((by fun_prop : Continuous fun w : ℂ => w + c).tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcon
      exact hw (by simpa using add_right_cancel hcon)
  exact hshift ((mem_planeCodiscrete.mp hS) (x + c))

/-- Translation of germs along the codiscrete filter. -/
noncomputable def planeGermTranslate (c : ℂ) (x : Germ planeCodiscrete ℂ) :
    Germ planeCodiscrete ℂ :=
  x.compTendsto (fun z : ℂ => z + c) (tendsto_add_const_planeCodiscrete c)

@[simp] theorem planeGermTranslate_coe (c : ℂ) (f : ℂ → ℂ) :
    planeGermTranslate c (f : Germ planeCodiscrete ℂ)
      = ((fun z : ℂ => f (z + c) : ℂ → ℂ) : Germ planeCodiscrete ℂ) := rfl

theorem planeGermTranslate_mem {c : ℂ} {g : Germ planeCodiscrete ℂ}
    (hg : g ∈ meromorphicPlaneSubring) : planeGermTranslate c g ∈ meromorphicPlaneSubring := by
  obtain ⟨f, hf, rfl⟩ := hg
  refine ⟨fun z => f (z + c), fun z => ?_, rfl⟩
  exact MeromorphicAt.comp_analyticAt (f := f) (g := fun w : ℂ => w + c) (hf (z + c)) (by fun_prop)

/-- Translation of the variable, as a map of the meromorphic plane field. -/
noncomputable def planeTranslate (c : ℂ) (x : MeromorphicPlane) : MeromorphicPlane :=
  show MeromorphicPlane from
    ⟨planeGermTranslate c x.germ,
      planeGermTranslate_mem (show (meromorphicPlaneSubring : Type) from x).2⟩

@[simp] theorem germ_planeTranslate (c : ℂ) (x : MeromorphicPlane) :
    (planeTranslate c x).germ = planeGermTranslate c x.germ := rfl

theorem planeTranslate_ofMeromorphic (c : ℂ) (f : ℂ → ℂ) (hf : ∀ z, MeromorphicAt f z) :
    planeTranslate c (ofMeromorphic f hf)
      = ofMeromorphic (fun z => f (z + c)) (fun z =>
          MeromorphicAt.comp_analyticAt (f := f) (g := fun w : ℂ => w + c)
            (hf (z + c)) (by fun_prop)) := by
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_planeTranslate, germ_ofMeromorphic, germ_ofMeromorphic, planeGermTranslate_coe]

theorem planeTranslate_zero (x : MeromorphicPlane) : planeTranslate 0 x = x := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [planeTranslate_ofMeromorphic]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  simp

theorem planeTranslate_add (c d : ℂ) (x : MeromorphicPlane) :
    planeTranslate c (planeTranslate d x) = planeTranslate (d + c) x := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [planeTranslate_ofMeromorphic, planeTranslate_ofMeromorphic, planeTranslate_ofMeromorphic]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  show f (z + c + d) = f (z + (d + c))
  rw [add_assoc, add_comm c d]

theorem planeTranslate_map_add (c : ℂ) (x y : MeromorphicPlane) :
    planeTranslate c (x + y) = planeTranslate c x + planeTranslate c y := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [ofMeromorphic_add, planeTranslate_ofMeromorphic, planeTranslate_ofMeromorphic,
    planeTranslate_ofMeromorphic, ofMeromorphic_add]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => rfl)

theorem planeTranslate_map_mul (c : ℂ) (x y : MeromorphicPlane) :
    planeTranslate c (x * y) = planeTranslate c x * planeTranslate c y := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  obtain ⟨g, hg, rfl⟩ := y.exists_rep
  rw [ofMeromorphic_mul, planeTranslate_ofMeromorphic, planeTranslate_ofMeromorphic,
    planeTranslate_ofMeromorphic, ofMeromorphic_mul]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => rfl)

theorem planeTranslate_one (c : ℂ) : planeTranslate c 1 = 1 := by
  have h1 : (1 : MeromorphicPlane) = ofMeromorphic (1 : ℂ → ℂ) (fun z => MeromorphicAt.const 1 z) :=
    rfl
  rw [h1, planeTranslate_ofMeromorphic]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => rfl)

/-- **Translation of the variable is a field automorphism.** -/
noncomputable def planeTranslateEquiv (c : ℂ) : MeromorphicPlane ≃+* MeromorphicPlane where
  toFun := planeTranslate c
  invFun := planeTranslate (-c)
  left_inv := by
    intro x
    rw [planeTranslate_add, add_neg_cancel, planeTranslate_zero]
  right_inv := by
    intro x
    rw [planeTranslate_add, neg_add_cancel, planeTranslate_zero]
  map_add' := planeTranslate_map_add c
  map_mul' := planeTranslate_map_mul c

@[simp] theorem planeTranslateEquiv_apply (c : ℂ) (x : MeromorphicPlane) :
    planeTranslateEquiv c x = planeTranslate c x := rfl

/-- **Translation commutes with differentiation.** -/
theorem planeTranslate_deriv (c : ℂ) (x : MeromorphicPlane) :
    planeTranslate c (meromorphicPlaneDeriv x) = meromorphicPlaneDeriv (planeTranslate c x) := by
  obtain ⟨f, hf, rfl⟩ := x.exists_rep
  rw [meromorphicPlaneDeriv_ofMeromorphic, planeTranslate_ofMeromorphic,
    planeTranslate_ofMeromorphic, meromorphicPlaneDeriv_ofMeromorphic]
  refine MeromorphicPlane.germ_injective ?_
  rw [germ_ofMeromorphic, germ_ofMeromorphic]
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun z => ?_)
  have hshift : deriv (fun w : ℂ => f (w + c)) z = deriv f (z + c) := by
    simpa using deriv_comp_add_const f c z
  exact hshift.symm

end GaloisForLFunctions.HTGeometry
