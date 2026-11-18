import GaloisForLFunctions.RepresentationLifting.Lattices.SimplexFacetSumCokernel
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Diagonal points in a projective frame

Intersect the hyperplane opposite a coordinate vertex with the line from
that vertex to the frame point. These intersections give the diagonal
points of a complete quadrangle in dimension two. In every dimension
the full relation module is detected by the simplex facet-sum operator.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset Submodule
open scoped Classical
noncomputable section

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- Homogeneous coordinates of the intersection opposite vertex `i`. -/
def frameDiagonal (w : ι → R) (i j : ι) : R := if j = i then 0 else w j

/-- The span of the diagonal point is the actual intersection of the
coordinate hyperplane with the span of the frame point and its opposite
vertex. The formula works over a general commutative coefficient ring. -/
theorem frameDiagonal_intersection (w : ι → R) (i : ι) :
    (LinearMap.proj i : (ι → R) →ₗ[R] R).ker ⊓ span R ({w,Pi.single i 1} : Set (ι → R)) =
      span R ({frameDiagonal w i} : Set (ι → R)) := by
  apply le_antisymm
  · intro v hv
    have hi : v i = 0 := hv.1
    obtain ⟨a,b,he⟩ := mem_span_pair.mp hv.2
    apply mem_span_singleton.mpr
    refine ⟨a,?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp [frameDiagonal,hi]
    · simpa [frameDiagonal,hji,Pi.single_apply] using congrFun he j
  · apply span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    refine ⟨show frameDiagonal w i i = 0 by simp [frameDiagonal], mem_span_pair.mpr ⟨1,-w i,?_⟩⟩
    funext j
    by_cases hji : j = i <;> simp [frameDiagonal,Pi.single_apply,hji]

variable {n : ℕ}

/-- The weighted sum of frame diagonals is the facet-sum map followed
by diagonal coordinate scaling. -/
theorem sum_frameDiagonals (w a : Fin (n+1) → R) (j : Fin (n+1)) :
    (∑ i, a i • frameDiagonal w i) j = facetSums R n a j * w j := by
  have h : ∑ i, a i * frameDiagonal w i j =
      (∑ i ∈ univ.erase j, a i) * w j := by
    rw [← sum_mul, ← sum_erase_add univ (fun i => a i * frameDiagonal w i j) (mem_univ j)]
    simp only [frameDiagonal,if_pos rfl,mul_zero,add_zero]
    exact sum_congr rfl fun i hi => by rw [if_neg (ne_of_mem_erase hi).symm]
  rw [Finset.sum_apply, h]
  congr 1
  exact eq_sub_of_add_eq (sum_erase_add univ a (mem_univ j))

/-- After independent choices of nonzero frame coordinates, every
relation still has constant coefficients killed by the dimension. -/
theorem frameDiagonal_relations (w : Fin (n+1) → Rˣ) (a : Fin (n+1) → R) :
    (∑ i, a i • frameDiagonal (fun j => (w j : R)) i) = 0 ↔
      ∃ b : R, (n:R)*b = 0 ∧ a = fun _ => b := by
  rw [← mem_ker_facetSums R n a, LinearMap.mem_ker]
  constructor
  · intro h
    funext j
    have he := congrFun h j
    rw [sum_frameDiagonals] at he
    have hh := congrArg (fun x : R => x*(↑(w j)⁻¹ : R)) he
    simpa [mul_assoc] using hh
  · intro h
    funext j
    rw [sum_frameDiagonals,h]
    simp

/-- Recovering coefficients of a specified point reduces to one scalar
equation, even if the residue characteristic divides the dimension. -/
def frameDiagonalFiberEquiv (w : Fin (n+1) → Rˣ) (y : Fin (n+1) → R) :
    {a : Fin (n+1) → R // (∑ i, a i • frameDiagonal (fun j => (w j:R)) i) = y} ≃
      {b : R // (n:R)*b = ∑ i, y i * (↑(w i)⁻¹:R)} := by
  refine (Equiv.subtypeEquivRight (q := fun a => facetSums R n a =
    fun i => y i * (↑(w i)⁻¹:R)) ?_).trans (facetFiberEquiv R n _)
  intro a
  constructor
  · intro h
    funext j
    have he := congrFun h j
    rw [sum_frameDiagonals] at he
    simpa [mul_assoc] using congrArg (fun z : R => z * (↑(w j)⁻¹:R)) he
  · intro h
    funext j
    rw [sum_frameDiagonals,congrFun h j]
    simp [mul_assoc]

private def translateScalarFiber (a b : R) : {z : R // a*z = a*b} ≃ {z : R // a*z = 0} where
  toFun z := ⟨z.val-b, by rw [mul_sub,z.property,sub_self]⟩
  invFun z := ⟨z.val+b, by rw [mul_add,z.property,zero_add]⟩
  left_inv z := Subtype.ext (sub_add_cancel _ _)
  right_inv z := Subtype.ext (add_sub_cancel_right _ _)

/-- Over the composite residue ring `ℤ/qℤ`, every attainable target has
exactly `gcd(q,n)` diagonal-coordinate representations. The weighted total
decides which targets are attainable. -/
theorem frameDiagonal_residue_fiber_card (q : ℕ+) (w : Fin (n+1) → (ZMod (q:ℕ))ˣ)
    (y : Fin (n+1) → ZMod (q:ℕ)) :
    Nat.card {a : Fin (n+1) → ZMod (q:ℕ) //
      (∑ i, a i • frameDiagonal (fun j => (w j:ZMod (q:ℕ))) i) = y} =
      if (n:ZMod (q:ℕ)) ∣ ∑ i, y i*(↑(w i)⁻¹:ZMod (q:ℕ)) then Nat.gcd (q:ℕ) n else 0 := by
  classical
  rw [Nat.card_congr (frameDiagonalFiberEquiv w y)]
  split_ifs with h
  · obtain ⟨b,hb⟩ := h
    rw [hb,Nat.card_congr (translateScalarFiber (n:ZMod (q:ℕ)) b)]
    let f := (nsmulAddMonoidHom n : ZMod (q:ℕ) →+ ZMod (q:ℕ))
    have e : {z : ZMod (q:ℕ) // (n:ZMod (q:ℕ))*z = 0} ≃ f.ker :=
      Equiv.subtypeEquivRight fun z => by simp [f,nsmul_eq_mul]
    rw [Nat.card_congr e]
    simpa [f,Nat.card_eq_fintype_card] using IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod (q:ℕ)) n
  · letI : IsEmpty {b : ZMod (q:ℕ) // (n:ZMod (q:ℕ))*b = ∑ i, y i*(↑(w i)⁻¹:ZMod (q:ℕ))} :=
      ⟨fun b => h ⟨b.val,b.property.symm⟩⟩
    exact Nat.card_of_isEmpty

/-- A relation supported on a proper subset must vanish, even in a
residue characteristic where the full frame becomes dependent. -/
theorem frameDiagonal_relation_missing_vertex (w : Fin (n+1) → Rˣ) (a : Fin (n+1) → R)
    (j : Fin (n+1)) :
    ((∑ i, a i • frameDiagonal (fun k => (w k:R)) i) = 0 ∧ a j = 0) ↔ a = 0 := by
  constructor
  · rintro ⟨h,hj⟩
    obtain ⟨b,_,he⟩ := (frameDiagonal_relations w a).mp h
    rw [he] at hj ⊢
    change b = 0 at hj
    simp [hj]
  · rintro rfl
    simp

/-- The diagonal points are independent precisely outside the residue
characteristics dividing the dimension. For a complete quadrangle this
is the Fano characteristic-two collinearity criterion. -/
theorem frameDiagonals_independent_iff {K : Type*} [Field K] (w : Fin (n+1) → Kˣ) :
    LinearIndependent K (frameDiagonal (fun j => (w j : K))) ↔ (n:K) ≠ 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h hn
    have hz := (frameDiagonal_relations w (fun _ => (1:K))).mpr ⟨1,by simp [hn],rfl⟩
    exact one_ne_zero (h _ hz 0)
  · intro hn a ha j
    obtain ⟨b,hb,rfl⟩ := (frameDiagonal_relations w a).mp ha
    exact (mul_eq_zero.mp hb).resolve_left hn

#print axioms frameDiagonal_intersection
#print axioms frameDiagonal_relations
#print axioms frameDiagonal_residue_fiber_card
#print axioms frameDiagonals_independent_iff

end
end GaloisForLFunctions.RepresentationLifting
