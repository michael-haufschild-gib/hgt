import GaloisForLFunctions.HTGeometry.PSDKernelOperations

open scoped BigOperators InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A norm-one vector, used as a reference direction for an incomplete tensor product. -/
structure HilbertUnitVector (E : Type*) [Norm E] where
  val : E
  norm_eq_one : ‖val‖ = 1

namespace HilbertUnitVector

instance {E : Type*} [Norm E] : Coe (HilbertUnitVector E) E := ⟨HilbertUnitVector.val⟩

end HilbertUnitVector

/-- Elementary tensors differing from the reference family in only finitely many coordinates. -/
structure IncompleteTensorElementary
    {I : Type*} (H : I → Type*) [∀ i, Norm (H i)]
    (Ω : ∀ i, HilbertUnitVector (H i)) where
  value : ∀ i, H i
  support : Finset I
  eq_reference : ∀ i, i ∉ support → value i = Ω i

namespace IncompleteTensorElementary

variable {I : Type*}
  (H : I → Type*) [∀ i, Norm (H i)]
  (Ω : ∀ i, HilbertUnitVector (H i))

/-- The pure reference tensor. -/
def reference : IncompleteTensorElementary H Ω where
  value i := Ω i
  support := ∅
  eq_reference _ _ := rfl

/-- A finite pure tensor, extended by the reference vectors off its finite packet. -/
def ofFinset [DecidableEq I] (S : Finset I) (v : ∀ i : ↑S, H i.1) :
    IncompleteTensorElementary H Ω where
  value i := if hi : i ∈ S then v ⟨i, hi⟩ else Ω i
  support := S
  eq_reference i hi := by simp [hi]

@[simp]
theorem reference_value (i : I) : (reference H Ω).value i = Ω i := rfl

@[simp]
theorem ofFinset_value_mem [DecidableEq I]
    (S : Finset I) (v : ∀ i : ↑S, H i.1)
    (i : I) (hi : i ∈ S) :
    (ofFinset H Ω S v).value i = v ⟨i, hi⟩ := by
  simp [ofFinset, hi]

@[simp]
theorem ofFinset_value_not_mem [DecidableEq I]
    (S : Finset I) (v : ∀ i : ↑S, H i.1)
    (i : I) (hi : i ∉ S) :
    (ofFinset H Ω S v).value i = Ω i := by
  simp [ofFinset, hi]

end IncompleteTensorElementary

variable {I X : Type*} [DecidableEq I]

theorem isPSDKernel_finset_prod
    (S : Finset I) (K : I → X → X → ℂ)
    (hK : ∀ i ∈ S, IsPSDKernel (K i)) :
    IsPSDKernel (fun x y => ∏ i ∈ S, K i x y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (isPSDKernel_one (X := X))
  | @insert a S ha ih =>
      simpa [Finset.prod_insert ha] using
        (hK a (Finset.mem_insert_self a S)).mul
          (ih (fun i hi => hK i (Finset.mem_insert_of_mem hi)))

section Kernel

variable (H : I → Type*) [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace ℂ (H i)]
  (Ω : ∀ i, HilbertUnitVector (H i))

abbrev ElementaryTensor := IncompleteTensorElementary H Ω

/-- Product inner kernel on finite-excitation elementary tensors. -/
def incompleteTensorKernel (x y : ElementaryTensor H Ω) : ℂ :=
  ∏ i ∈ x.support ∪ y.support, inner ℂ (y.value i) (x.value i)

theorem incompleteTensorKernel_eq_prod_of_subset
    (x y : ElementaryTensor H Ω) (S : Finset I)
    (hx : x.support ⊆ S) (hy : y.support ⊆ S) :
    incompleteTensorKernel H Ω x y =
      ∏ i ∈ S, inner ℂ (y.value i) (x.value i) := by
  rw [incompleteTensorKernel]
  apply Finset.prod_subset (Finset.union_subset hx hy)
  intro i hiS hi
  have hix : i ∉ x.support := fun hmem => hi (Finset.mem_union_left _ hmem)
  have hiy : i ∉ y.support := fun hmem => hi (Finset.mem_union_right _ hmem)
  rw [x.eq_reference i hix, y.eq_reference i hiy,
    inner_self_eq_norm_sq_to_K, (Ω i).norm_eq_one]
  norm_num

theorem incompleteTensorKernel_conj_symm (x y : ElementaryTensor H Ω) :
    conj (incompleteTensorKernel H Ω x y) =
      incompleteTensorKernel H Ω y x := by
  classical
  rw [incompleteTensorKernel, map_prod, incompleteTensorKernel, Finset.union_comm]
  apply Finset.prod_congr rfl
  intro i hi
  exact inner_conj_symm _ _

theorem isPSDKernel_incompleteTensorKernel :
    IsPSDKernel (incompleteTensorKernel H Ω) := by
  classical
  apply isPSDKernel_of_forall_posSemidef
  · exact incompleteTensorKernel_conj_symm H Ω
  · intro n w
    let S : Finset I := Finset.univ.biUnion fun j => (w j).support
    have hw (j : Fin n) : (w j).support ⊆ S := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
    have hprod : IsPSDKernel
        (fun x y : ElementaryTensor H Ω =>
          ∏ i ∈ S, inner ℂ (y.value i) (x.value i)) := by
      apply isPSDKernel_finset_prod S
        (fun i (x y : ElementaryTensor H Ω) => inner ℂ (y.value i) (x.value i))
      intro i hi
      exact isPSDKernel_gram (fun x : ElementaryTensor H Ω => x.value i)
    have hmat := hprod.posSemidef w
    convert hmat using 1
    ext j k
    exact incompleteTensorKernel_eq_prod_of_subset H Ω (w j) (w k) S (hw j) (hw k)

noncomputable instance incompleteTensorKernelFact :
    Fact (IsPSDKernel (incompleteTensorKernel H Ω)) :=
  ⟨isPSDKernel_incompleteTensorKernel H Ω⟩

/-- Von Neumann's incomplete tensor product: Hilbert completion of finite-excitation pure tensors
with the product inner kernel. -/
abbrev IncompleteTensorProduct : Type _ :=
  KernelHilbert (incompleteTensorKernel H Ω)

/-- Canonical image of an elementary finite-excitation tensor. -/
def incompleteTensorVector (x : ElementaryTensor H Ω) :
    IncompleteTensorProduct H Ω :=
  KernelHilbert.vector (incompleteTensorKernel H Ω) x

/-- Exact pure-tensor inner-product law in the completed carrier. -/
theorem inner_incompleteTensorVector (x y : ElementaryTensor H Ω) :
    inner ℂ (incompleteTensorVector H Ω y) (incompleteTensorVector H Ω x) =
      incompleteTensorKernel H Ω x y :=
  KernelHilbert.inner_vector x y

/-- Distinguished incomplete-product reference vector. -/
def incompleteTensorReference : IncompleteTensorProduct H Ω :=
  incompleteTensorVector H Ω (IncompleteTensorElementary.reference H Ω)

theorem norm_incompleteTensorReference :
    ‖incompleteTensorReference H Ω‖ = 1 := by
  have hinner : inner ℂ (incompleteTensorReference H Ω)
      (incompleteTensorReference H Ω) = 1 := by
    change inner ℂ (incompleteTensorVector H Ω
        (IncompleteTensorElementary.reference H Ω))
      (incompleteTensorVector H Ω
        (IncompleteTensorElementary.reference H Ω)) = (1 : ℂ)
    rw [inner_incompleteTensorVector, incompleteTensorKernel]
    simp [IncompleteTensorElementary.reference]
  have hsq : ‖incompleteTensorReference H Ω‖ ^ 2 =
      RCLike.re (inner ℂ (incompleteTensorReference H Ω)
        (incompleteTensorReference H Ω)) :=
    norm_sq_eq_re_inner _
  rw [hinner] at hsq
  norm_num at hsq
  rcases hsq with hsq | hsq
  · exact hsq
  · linarith [norm_nonneg (incompleteTensorReference H Ω)]

end Kernel

end


end GaloisForLFunctions.HTGeometry
