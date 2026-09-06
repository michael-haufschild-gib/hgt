import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicFaces
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.FusionHeat

/-!
# Actual faces and Euler heat of the repeated cubic join

Faces are finite sets of block-labeled vertices. Taking fibers gives a bijection
with tuples of cubic faces, and cardinality adds across blocks. Multiplication
of signed face sums proves reduced Euler coefficient -1 for every join power.
Using the logarithms of actual fusion capacities gives the Euler heat trace
and identifies its regularized kernel with the previously proved Bose defect.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Finset


def cubicJoinFace {n : ℕ} (F : Fin n → Finset (Fin 5)) : Finset (Fin n × Fin 5) :=
  Finset.univ.biUnion (fun i => (F i).image (fun q => (i,q)))

def cubicFaceFiber {n : ℕ} (σ : Finset (Fin n × Fin 5)) (i : Fin n) : Finset (Fin 5) :=
  (σ.filter (fun p => p.1=i)).image Prod.snd

theorem cubicJoinFace_mem {n : ℕ} (F : Fin n → Finset (Fin 5)) (p : Fin n × Fin 5) :
    p ∈ cubicJoinFace F ↔ p.2 ∈ F p.1 := by
  rcases p with ⟨i,q⟩
  simp [cubicJoinFace,Finset.mem_biUnion]

theorem cubicFaceFiber_mem {n : ℕ} (σ : Finset (Fin n × Fin 5)) (i : Fin n) (q : Fin 5) :
    q ∈ cubicFaceFiber σ i ↔ (i,q) ∈ σ := by
  simp only [cubicFaceFiber,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨j,r⟩,⟨hp,hj⟩,hr⟩
    dsimp only at hj hr
    subst j
    subst r
    exact hp
  · intro h
    exact ⟨(i,q),⟨h,rfl⟩,rfl⟩

theorem cubicFaceFiber_join {n : ℕ} (F : Fin n → Finset (Fin 5)) (i : Fin n) :
    cubicFaceFiber (cubicJoinFace F) i=F i := by
  ext q
  rw [cubicFaceFiber_mem,cubicJoinFace_mem]

theorem cubicJoinFace_fibers {n : ℕ} (σ : Finset (Fin n × Fin 5)) :
    cubicJoinFace (cubicFaceFiber σ)=σ := by
  ext p
  rw [cubicJoinFace_mem,cubicFaceFiber_mem]

theorem cubicJoinFace_injective (n : ℕ) :
    Function.Injective (@cubicJoinFace n) := by
  intro F G h
  funext i
  have hh := congrArg (fun σ => cubicFaceFiber σ i) h
  simpa only [cubicFaceFiber_join] using hh

def fusedCubicFaces (n : ℕ) : Finset (Finset (Fin n × Fin 5)) :=
  Finset.univ.image (fun F : Fin n → cubicFaces => cubicJoinFace (fun i => (F i).val))

theorem fusedCubicFaces_mem (n : ℕ) (σ : Finset (Fin n × Fin 5)) :
    σ ∈ fusedCubicFaces n ↔ ∀ i, cubicFaceFiber σ i ∈ cubicFaces := by
  constructor
  · rintro h
    obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp h
    intro i
    rw [cubicFaceFiber_join]
    exact (F i).property
  · intro h
    refine Finset.mem_image.mpr ⟨fun i => ⟨cubicFaceFiber σ i,h i⟩,Finset.mem_univ _,?_⟩
    exact cubicJoinFace_fibers σ

theorem cubicJoinFace_card {n : ℕ} (F : Fin n → Finset (Fin 5)) :
    (cubicJoinFace F).card=∑ i, (F i).card := by
  have hd : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i => (F i).image (fun q => (i,q))) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hi hj
    obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hi
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hj
    exact hij (congrArg Prod.fst (hq.trans hr.symm))
  rw [cubicJoinFace,Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_image_of_injOn
  intro q _ r _ h
  exact congrArg Prod.snd h

def fusedCubicReducedEuler (n : ℕ) : ℤ :=
  -(∑ σ ∈ fusedCubicFaces n, (-1 : ℤ)^σ.card)

theorem fusedCubicReducedEuler_eq (n : ℕ) : fusedCubicReducedEuler n = -1 := by
  have hinj : Function.Injective (fun F : Fin n → cubicFaces =>
      cubicJoinFace (fun i => (F i).val)) := by
    intro F G h
    have hh := cubicJoinFace_injective n h
    funext i
    exact Subtype.ext (congrFun hh i)
  have hsum : (∑ σ : cubicFaces, (-1 : ℤ)^σ.val.card)=1 := by
    calc
      _ = ∑ σ ∈ cubicFaces, (-1 : ℤ)^σ.card := Finset.sum_coe_sort cubicFaces _
      _ = 1 := cubicFaces_euler
  have hp := Fintype.sum_pow (fun σ : cubicFaces => (-1 : ℤ)^σ.val.card) n
  rw [hsum,one_pow] at hp
  unfold fusedCubicReducedEuler fusedCubicFaces
  rw [Finset.sum_image (fun F _ G _ h => hinj h)]
  simp_rw [cubicJoinFace_card,← Finset.prod_pow_eq_pow_sum]
  rw [← hp]

def cubicEulerHeat (u : ℝ) : ℝ :=
  ∑' n : ℕ, (fusedCubicReducedEuler (n+1) : ℝ)*
    Real.exp (-fusionEnergy (n+1)*Real.exp u)

theorem cubicEulerHeat_eq (u : ℝ) : cubicEulerHeat u = -fusionHeat u := by
  simp only [cubicEulerHeat,fusedCubicReducedEuler_eq,Int.cast_neg,Int.cast_one,
    neg_one_mul,tsum_neg,fusionHeat]

theorem cubicEulerHeat_hasSum (u : ℝ) :
    HasSum (fun n : ℕ => (fusedCubicReducedEuler (n+1) : ℝ)*
      Real.exp (-fusionEnergy (n+1)*Real.exp u))
      (-(1/(Real.exp (fusionSpacing*Real.exp u)-1))) := by
  simpa only [fusedCubicReducedEuler_eq,Int.cast_neg,Int.cast_one,neg_one_mul]
    using (fusionHeat_hasSum u).neg

theorem cubicEulerHeat_kernel (u : ℝ) :
    fusionRegularizedKernel (Real.exp u)=
      ((1/(fusionSpacing*Real.exp u)+cubicEulerHeat u : ℝ) : ℂ) := by
  rw [fusionRegularizedKernel_discrete,cubicEulerHeat_eq,sub_eq_add_neg]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
