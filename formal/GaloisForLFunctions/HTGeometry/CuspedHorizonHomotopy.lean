import GaloisForLFunctions.HTGeometry.CuspedHorizonPoset
import GaloisForLFunctions.HTGeometry.SSetStrongHomotopyEquivalence

/-!
# The all-depth cusped horizon poset retracts onto its depth-one skeleton

The cusped poset carries a monotone map out of its cylinder whose two ends are the identity and the
retraction onto the depth-one vertices.  Passing to nerves turns that map into a simplicial homotopy,
so the nerve of the all-depth poset is homotopy equivalent to the nerve of the building poset it
retracts onto.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial SSet CuspedVertex

universe u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [DecidableEq (Submodule K V)]

/-- The cusp deformation, as a functor out of the cylinder on the cusped poset. -/
def cuspCylinderFunctor (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] :
    CategoryTheory.Functor (CuspedVertex K V × catInterval.{u}) (CuspedVertex K V) :=
  prodPreorderFunctor cuspHomotopyInterval

/-- **At time zero the deformation is the identity.** -/
theorem cuspCylinder_zero :
    (cylinderIncl (CuspedVertex K V) (ULift.up 0)).comp (cuspCylinderFunctor K V)
      = CategoryTheory.Functor.id (CuspedVertex K V) := by
  refine CategoryTheory.Functor.ext (fun v => ?_) (fun v w f => ?_)
  · simp [cuspCylinderFunctor, prodPreorderFunctor, cylinderIncl, cuspHomotopyInterval]
  · apply Subsingleton.elim

/-- **At time one it is the retraction onto the depth-one vertices.** -/
theorem cuspCylinder_one :
    (cylinderIncl (CuspedVertex K V) (ULift.up 1)).comp (cuspCylinderFunctor K V)
      = retractFunctor := by
  refine CategoryTheory.Functor.ext (fun v => ?_) (fun v w f => ?_)
  · simp [cuspCylinderFunctor, prodPreorderFunctor, cylinderIncl, cuspHomotopyInterval,
      retractFunctor]
  · apply Subsingleton.elim

/-- **The nerve of the cusped horizon poset deformation retracts onto the nerve of its depth-one
skeleton.**  The nerve of the identity is simplicially homotopic to the nerve of the retraction. -/
noncomputable def cuspNerveHomotopy (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] :
    SSet.Homotopy (nerveFunctor.map (CategoryTheory.Functor.id (CuspedVertex K V)).toCatHom)
      (nerveFunctor.map (retractFunctor (K := K) (V := V)).toCatHom) := by
  have h := nerveHomotopy (cuspCylinderFunctor K V)
  rwa [cuspCylinder_zero, cuspCylinder_one] at h

/-- **The identity of the nerve is homotopic to the nerve of the retraction**, which is the
statement that the inclusion of the depth-one skeleton is a homotopy equivalence. -/
noncomputable def cuspNerveHomotopyId (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] :
    SSet.Homotopy (𝟙 (nerveFunctor.obj (Cat.of (CuspedVertex K V))))
      (nerveFunctor.map (retractFunctor (K := K) (V := V)).toCatHom) := by
  have h := cuspNerveHomotopy K V
  rwa [show (CategoryTheory.Functor.id (CuspedVertex K V)).toCatHom
      = 𝟙 (Cat.of (CuspedVertex K V)) from rfl, nerveFunctor.map_id] at h

/-! ## The retract is the building, and the retraction is a deformation retraction -/

/-- The inclusion of the depth-one skeleton into the all-depth poset. -/
def depthOneIncl (K V : Type u) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    CategoryTheory.Functor {v : CuspedVertex K V // v.depth = 0} (CuspedVertex K V) :=
  Monotone.functor (f := Subtype.val) (fun _ _ h => h)

/-- The retraction onto the depth-one skeleton, landing in the skeleton itself. -/
def cuspRetractFunctor (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] :
    CategoryTheory.Functor (CuspedVertex K V) {v : CuspedVertex K V // v.depth = 0} :=
  Monotone.functor (f := fun v => ⟨retract v, rfl⟩) (fun _ _ h => retract_monotone h)

/-- **The retraction restricts to the identity on the depth-one skeleton.** -/
theorem depthOneIncl_comp_cuspRetract :
    (depthOneIncl K V).comp (cuspRetractFunctor K V)
      = CategoryTheory.Functor.id {v : CuspedVertex K V // v.depth = 0} :=
  CategoryTheory.Functor.ext (fun v => Subtype.ext (ext' rfl v.2.symm))
    (fun _ _ _ => Subsingleton.elim _ _)

/-- **And composed the other way it is the retraction of the all-depth poset.** -/
theorem cuspRetract_comp_depthOneIncl :
    (cuspRetractFunctor K V).comp (depthOneIncl K V) = retractFunctor := rfl

/-- **The order complex of the all-depth cusped poset deformation retracts onto the order complex of
its depth-one skeleton.**  The inclusion is a section of the retraction on the nose, and the other
composite is simplicially homotopic to the identity: this is the deformation retraction of the
statement, in the simplicial category. -/
noncomputable def cuspDeformationRetract (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] :
    SSetDeformationRetract (nerveFunctor.obj (Cat.of (CuspedVertex K V)))
      (nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.depth = 0})) where
  incl := nerveFunctor.map (depthOneIncl K V).toCatHom
  retr := nerveFunctor.map (cuspRetractFunctor K V).toCatHom
  incl_retr := by
    rw [← CategoryTheory.Functor.map_comp,
      show (depthOneIncl K V).toCatHom ≫ (cuspRetractFunctor K V).toCatHom
        = (CategoryTheory.Functor.id {v : CuspedVertex K V // v.depth = 0}).toCatHom by
        rw [← depthOneIncl_comp_cuspRetract]; rfl]
    exact nerveFunctor.map_id _
  homotopy := by
    have h := cuspNerveHomotopyId K V
    rw [← cuspRetract_comp_depthOneIncl,
      show ((cuspRetractFunctor K V).comp (depthOneIncl K V)).toCatHom
        = (cuspRetractFunctor K V).toCatHom ≫ (depthOneIncl K V).toCatHom from rfl,
      CategoryTheory.Functor.map_comp] at h
    exact h

/-- **The depth-one skeleton's order complex is the order complex of the building.**  The nerve of
the skeleton is isomorphic to the nerve of the poset of nonzero proper subspaces under reverse
inclusion. -/
noncomputable def depthOneNerveIso (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.depth = 0})
      ≅ nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ) :=
  orderIsoNerveIso depthOneOrderIso

/-- **The all-depth order complex deformation retracts onto the building's order complex.**  The
retract of the previous construction, transported along the identification of the depth-one skeleton
with the poset of nonzero proper subspaces. -/
noncomputable def cuspBuildingDeformationRetract (K V : Type u) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [DecidableEq (Submodule K V)] :
    SSetDeformationRetract (nerveFunctor.obj (Cat.of (CuspedVertex K V)))
      (nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)) where
  incl := (depthOneNerveIso K V).inv ≫ (cuspDeformationRetract K V).incl
  retr := (cuspDeformationRetract K V).retr ≫ (depthOneNerveIso K V).hom
  incl_retr := by
    rw [Category.assoc, ← Category.assoc ((cuspDeformationRetract K V).incl),
      (cuspDeformationRetract K V).incl_retr, Category.id_comp, Iso.inv_hom_id]
  homotopy := by
    have h := (cuspDeformationRetract K V).homotopy
    rwa [show (cuspDeformationRetract K V).retr ≫ (cuspDeformationRetract K V).incl
        = ((cuspDeformationRetract K V).retr ≫ (depthOneNerveIso K V).hom)
          ≫ (depthOneNerveIso K V).inv ≫ (cuspDeformationRetract K V).incl by
        rw [Category.assoc, ← Category.assoc ((depthOneNerveIso K V).hom), Iso.hom_inv_id,
          Category.id_comp]] at h

/-- **The all-depth cusped horizon complex and the spherical building have the same simplicial
homotopy type.**  This is the homotopy-type statement carried by the explicit cusp deformation;
it is stronger than, and logically prior to, the induced homology isomorphisms below. -/
noncomputable def cuspBuildingStrongHomotopyEquiv (K V : Type u) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [DecidableEq (Submodule K V)] :
    SSetStrongHomotopyEquiv (nerveFunctor.obj (Cat.of (CuspedVertex K V)))
      (nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)) :=
  (cuspBuildingDeformationRetract K V).toStrongHomotopyEquiv

/-- **The all-depth cusped horizon complex has the homology of the building**, in every degree and
with any coefficients: the cusps add nothing.  With the classical computation of the building's
homology this is the persistence of the Steinberg class of the statement. -/
noncomputable def cuspBuildingHomologyIso (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ) :
    (nerveFunctor.obj (Cat.of (CuspedVertex K V))).homology R n
      ≅ (nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ)).homology R n :=
  (cuspBuildingDeformationRetract K V).homologyIso R n

/-! ## The dimension of the building, and vanishing above it -/

/-- **The order complex of the building has dimension below `N - 1`.**  A nondegenerate simplex is a
strict chain of nonzero proper subspaces, and such a chain has at most `N - 1` members. -/
theorem buildingHasDimensionLT (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    SSet.HasDimensionLT
      (nerveFunctor.obj (Cat.of ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ))
      (Module.finrank K V - 1) := by
  classical
  refine hasDimensionLT_nerve_of_chain_bound _ (fun n f hf => ?_)
  have hinj : Function.Injective
      (fun i : Fin (n + 1) => ((OrderDual.ofDual (f i) : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) :
        Submodule K V)) := fun i j h => hf.injective (Subtype.ext h)
  set T : Finset (Submodule K V) :=
    Finset.image (fun i : Fin (n + 1) =>
      ((OrderDual.ofDual (f i) : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) : Submodule K V))
      Finset.univ with hT
  have hcard : T.card = n + 1 := by
    rw [hT, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hmem : ∀ W ∈ T, ∃ i : Fin (n + 1),
      ((OrderDual.ofDual (f i) : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) : Submodule K V) = W := by
    intro W hW
    rw [hT, Finset.mem_image] at hW
    obtain ⟨i, -, hi⟩ := hW
    exact ⟨i, hi⟩
  have hchain : ∀ W ∈ T, ∀ W' ∈ T, W ≤ W' ∨ W' ≤ W := by
    intro W hW W' hW'
    obtain ⟨i, rfl⟩ := hmem W hW
    obtain ⟨j, rfl⟩ := hmem W' hW'
    rcases le_total i j with h | h
    · exact Or.inr (hf.monotone h)
    · exact Or.inl (hf.monotone h)
  have hbot : ∀ W ∈ T, W ≠ ⊥ := by
    intro W hW
    obtain ⟨i, rfl⟩ := hmem W hW
    exact (OrderDual.ofDual (f i)).2.1
  have htop : ∀ W ∈ T, W ≠ ⊤ := by
    intro W hW
    obtain ⟨i, rfl⟩ := hmem W hW
    exact (OrderDual.ofDual (f i)).2.2
  have := card_le_finrank_sub_one T hchain hbot htop
  omega

/-- **The all-depth cusped horizon complex has no homology above the building's dimension.**  Even
though the complex itself is infinite dimensional — every cusp is an infinite chain — its homology
vanishes in degrees `N - 1` and above, with any coefficients. -/
theorem isZero_cuspHomology (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : Module.finrank K V - 1 ≤ n) :
    Limits.IsZero ((nerveFunctor.obj (Cat.of (CuspedVertex K V))).homology R n) := by
  haveI := buildingHasDimensionLT K V
  exact Limits.IsZero.of_iso
    (isZero_homology_of_hasDimensionLT _ (Module.finrank K V - 1) R n hn)
    (cuspBuildingHomologyIso K V R n)

/-! ## Connectedness of the building, and degree zero -/

/-- A nonzero proper subspace contains a line, and in dimension at least three that line is itself a
vertex of the building. -/
theorem exists_line_le (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hN : 3 ≤ Module.finrank K V) {W : Submodule K V} (hW : W ≠ ⊥) :
    ∃ L : Submodule K V, L ≤ W ∧ Module.finrank K L = 1 ∧ L ≠ ⊥ ∧ L ≠ ⊤ := by
  obtain ⟨x, hxW, hx⟩ := (Submodule.ne_bot_iff W).1 hW
  refine ⟨K ∙ x, (Submodule.span_singleton_le_iff_mem x W).2 hxW, finrank_span_singleton hx, ?_, ?_⟩
  · simpa [Submodule.span_singleton_eq_bot] using hx
  · intro hcon
    have h1 : Module.finrank K (K ∙ x) = 1 := finrank_span_singleton hx
    rw [hcon, finrank_top] at h1
    omega

/-- **The building poset is zigzag connected in dimension at least three.**  Any two nonzero proper
subspaces are joined through a line in each and the plane those two lines span, which is a proper
subspace because the dimension is at least three. -/
theorem buildingZigzag (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hN : 3 ≤ Module.finrank K V)
    (a b : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤}) :
    Relation.ReflTransGen (fun x y : {S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤} => x ≤ y ∨ y ≤ x) a b := by
  obtain ⟨L, hLa, hL1, hLbot, hLtop⟩ := exists_line_le K V hN a.2.1
  obtain ⟨L', hL'b, hL'1, hL'bot, hL'top⟩ := exists_line_le K V hN b.2.1
  have hsup : Module.finrank K ((L ⊔ L' : Submodule K V)) ≤ 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq L L'
    omega
  have hMtop : (L ⊔ L' : Submodule K V) ≠ ⊤ := by
    intro hcon
    rw [hcon, finrank_top] at hsup
    omega
  have hMbot : (L ⊔ L' : Submodule K V) ≠ ⊥ := by
    intro hcon
    exact hLbot (le_bot_iff.1 (hcon ▸ le_sup_left))
  refine Relation.ReflTransGen.head (b := ⟨L, hLbot, hLtop⟩) (Or.inr ?_) ?_
  · exact hLa
  refine Relation.ReflTransGen.head (b := ⟨L ⊔ L', hMbot, hMtop⟩) (Or.inl ?_) ?_
  · show (L : Submodule K V) ≤ L ⊔ L'
    exact le_sup_left
  refine Relation.ReflTransGen.head (b := ⟨L', hL'bot, hL'top⟩) (Or.inr ?_)
    (Relation.ReflTransGen.single (Or.inl ?_))
  · show (L' : Submodule K V) ≤ L ⊔ L'
    exact le_sup_right
  · exact hL'b

/-- **The order complex of the building is connected in dimension at least three.** -/
theorem buildingIsConnected (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hN : 3 ≤ Module.finrank K V) :
    SSet.IsConnected (nerve ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ) := by
  obtain ⟨L, -, -, hLbot, hLtop⟩ :=
    exists_line_le K V hN (W := (⊤ : Submodule K V)) (by
      intro hcon
      have : Module.finrank K V = 0 := by
        rw [← finrank_top K V, hcon, finrank_bot]
      omega)
  haveI : Nonempty ({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ :=
    ⟨OrderDual.toDual ⟨L, hLbot, hLtop⟩⟩
  exact (SSet.isConnected_iff _).2
    ⟨isPreconnected_nerve_of_zigzag (zigzag_orderDual (buildingZigzag K V hN)), inferInstance⟩

/-- **The all-depth cusped horizon complex is connected in dimension at least three**, so its
homology in degree zero is a single copy of the coefficients: the vanishing of reduced `H_0`, which
is the `j = 0` case of the card's homology statement. -/
noncomputable def cuspHomologyZeroIso (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq (Submodule K V)] (hN : 3 ≤ Module.finrank K V)
    {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C]
    (R : C) :
    (nerveFunctor.obj (Cat.of (CuspedVertex K V))).homology R 0 ≅ R := by
  haveI : SSet.IsConnected
      (nerveFunctor.obj (Cat.of (({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ))) :=
    buildingIsConnected K V hN
  exact cuspBuildingHomologyIso K V R 0 ≪≫
    asIso ((nerveFunctor.obj (Cat.of (({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ))).homology₀ε R)

/-! ## The cusps are contractible -/

/-- **A cusp has a greatest element.**  All the vertices carried by one subspace form a chain whose
largest member is the depth-one vertex on that subspace. -/
@[reducible] def cuspOrderTop {S : Submodule K V} (hb : S ≠ ⊥) (ht : S ≠ ⊤) :
    OrderTop {v : CuspedVertex K V // v.space = S} where
  top := ⟨⟨S, 0, hb, ht, fun h => absurd rfl h⟩, rfl⟩
  le_top v := ⟨Nat.zero_le _, fun _ => le_of_eq v.2.symm, fun _ => v.2.symm⟩

/-- **Each cusp is contractible.**  The order complex of the vertices carried by one subspace has no
homology in positive degrees, however deep the cusp runs.

This is the card's sentence that the order complex of a jet-tail chain is an infinite simplex, hence
contractible, in the form the homology of the nerve records. -/
theorem isZero_homology_cusp (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {S : Submodule K V} (hb : S ≠ ⊥) (ht : S ≠ ⊤) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : 1 ≤ n) :
    Limits.IsZero
      ((nerveFunctor.obj (Cat.of {v : CuspedVertex K V // v.space = S})).homology R n) := by
  haveI := cuspOrderTop (K := K) (V := V) hb ht
  exact isZero_homology_of_orderTop R n hn

/-- **The subspaces above a fixed one form a contractible poset**, having a least element. -/
theorem isZero_homology_above (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : Submodule K V) {C : Type*} [Category C]
    [Limits.HasCoproducts.{u} C] [Preadditive C] [CategoryWithHomology C] (R : C) (n : ℕ)
    (hn : 1 ≤ n) :
    Limits.IsZero
      ((nerveFunctor.obj (Cat.of {S : Submodule K V // L ≤ S})).homology R n) := by
  haveI : OrderBot {S : Submodule K V // L ≤ S} :=
    { bot := ⟨L, le_rfl⟩, bot_le := fun S => S.2 }
  exact isZero_homology_of_orderBot R n hn

end GaloisForLFunctions.HTGeometry
