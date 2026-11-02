import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.PNat.Basic

/-! Euclidean division partitions the full positive lattice cone into
Gauss-branch images and exact multiple rays. The multiple rays supply
the zeta forcing term in the unprimitive lattice response. -/

set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerLatticeRenewal

/-- All positive denominator pairs strictly inside the cone `p<q`. -/
def Cone := {p : ℕ × ℕ // 0 < p.1 ∧ p.1 < p.2}

/-- Cone pairs with a nonzero Euclidean remainder. -/
def NonmultipleCone := {p : Cone // p.val.2%p.val.1 ≠ 0}

/-- Positive cone coordinates are the two nonnegative distances from its boundary rays. -/
def rectangleEquiv : ℕ × ℕ ≃ Cone where
  toFun p := ⟨(p.1+1,p.1+p.2+2),by omega⟩
  invFun p := (p.val.1-1,p.val.2-p.val.1-1)
  left_inv p := by apply Prod.ext <;> simp only <;> omega
  right_inv p := by
    have hp := p.property
    apply Subtype.ext
    apply Prod.ext <;> simp only <;> omega

theorem rectangleEquiv_apply (p : ℕ × ℕ) :
    (rectangleEquiv p).val=(p.1+1,p.1+p.2+2) := rfl

/-- A positive inverse branch acts on literal denominator pairs. -/
def branchPair (n : ℕ+) (p : Cone) : NonmultipleCone :=
  ⟨⟨(p.val.2,(n : ℕ)*p.val.2+p.val.1),by
    have hp := p.property
    have hn : 1 ≤ (n : ℕ) := n.property
    have hmul := Nat.mul_le_mul_right p.val.2 hn
    simp only [one_mul] at hmul
    exact ⟨by omega,by omega⟩⟩,by
      change ((n : ℕ)*p.val.2+p.val.1)%p.val.2 ≠ 0
      simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,mul_zero,Nat.zero_mod,zero_add,
        Nat.mod_eq_of_lt p.property.2]
      exact p.property.1.ne'⟩

private theorem quotient_unique {n m p r q : ℕ} (hp : p < q) (hr : r < q)
    (he : n*q+p=m*q+r) : n=m := by
  apply le_antisymm
  · by_contra h
    have hm : m+1 ≤ n := by omega
    have hmul := Nat.mul_le_mul_right q hm
    rw [Nat.succ_mul] at hmul
    omega
  · by_contra h
    have hn : n+1 ≤ m := by omega
    have hmul := Nat.mul_le_mul_right q hn
    rw [Nat.succ_mul] at hmul
    omega

private theorem branchPair_injective :
    Function.Injective (fun x : ℕ+ × Cone => branchPair x.1 x.2) := by
  rintro ⟨n,p⟩ ⟨m,r⟩ he
  have hq : p.val.2=r.val.2 := congrArg (fun x : NonmultipleCone => x.val.val.1) he
  have hsum : (n : ℕ)*p.val.2+p.val.1=(m : ℕ)*r.val.2+r.val.1 :=
    congrArg (fun x : NonmultipleCone => x.val.val.2) he
  rw [← hq] at hsum
  have hnr := quotient_unique p.property.2 (by rw [hq]; exact r.property.2) hsum
  have hnm : n=m := Subtype.ext hnr
  have hpr : p=r := by
    apply Subtype.ext
    apply Prod.ext
    · rw [hnr] at hsum
      exact Nat.add_left_cancel hsum
    · exact hq
  exact Prod.ext hnm hpr

/-- Nonzero remainders are exactly the cone points with a unique branch predecessor. -/
theorem branchPair_surjective :
    Function.Surjective (fun x : ℕ+ × Cone => branchPair x.1 x.2) := by
  intro x
  have hp : 0 < x.val.val.1 := x.val.property.1
  have hq : x.val.val.1 < x.val.val.2 := x.val.property.2
  have hn : 0 < x.val.val.2/x.val.val.1 := Nat.div_pos (by omega) hp
  have hr : x.val.val.2%x.val.val.1 < x.val.val.1 := Nat.mod_lt _ hp
  have hrpos : 0 < x.val.val.2%x.val.val.1 := Nat.pos_of_ne_zero x.property
  refine ⟨(⟨x.val.val.2/x.val.val.1,hn⟩,
    ⟨(x.val.val.2%x.val.val.1,x.val.val.1),hrpos,hr⟩),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (x.val.val.2/x.val.val.1)*x.val.val.1+x.val.val.2%x.val.val.1=x.val.val.2
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div x.val.val.2 x.val.val.1

/-- Exact renewal bijection for the nonmultiple part of the full lattice cone. -/
def renewalEquiv : ℕ+ × Cone ≃ NonmultipleCone :=
  Equiv.ofBijective (fun x => branchPair x.1 x.2) ⟨branchPair_injective,branchPair_surjective⟩

/-- The missing multiple ray, with quotient at least two. -/
def multiplePair (a : ℕ+) (k : ℕ) : Cone :=
  ⟨((a : ℕ),(a : ℕ)*(k+2)),by
    refine ⟨a.property,?_⟩
    have ha : 0 < (a : ℕ) := a.property
    have h : (a : ℕ)*2 ≤ (a : ℕ)*(k+2) := Nat.mul_le_mul_left _ (by omega)
    simp only [Nat.mul_two] at h
    omega⟩

private theorem multiplePair_mod (a : ℕ+) (k : ℕ) :
    (multiplePair a k).val.2%(multiplePair a k).val.1=0 := by
  change ((a : ℕ)*(k+2))%(a : ℕ)=0
  simp only [Nat.mul_mod,Nat.mod_self,zero_mul,Nat.zero_mod]

private def splitPair : (ℕ+ × ℕ) ⊕ NonmultipleCone → Cone
  | .inl (a,k) => multiplePair a k
  | .inr p => p.val

private theorem splitPair_injective : Function.Injective splitPair := by
  intro x y h
  cases x with
  | inl p =>
    obtain ⟨a,k⟩ := p
    cases y with
    | inl q =>
      obtain ⟨b,l⟩ := q
      have ha : a=b := Subtype.ext (congrArg (fun p : Cone => p.val.1) h)
      subst b
      have he := congrArg (fun p : Cone => p.val.2) h
      change (a : ℕ)*(k+2)=(a : ℕ)*(l+2) at he
      have hk : k=l := by
        have hkl := Nat.eq_of_mul_eq_mul_left a.property he
        omega
      subst l
      rfl
    | inr q =>
      have he := congrArg (fun p : Cone => p.val.2%p.val.1) h
      change (multiplePair a k).val.2%(multiplePair a k).val.1=q.val.val.2%q.val.val.1 at he
      rw [multiplePair_mod] at he
      exact False.elim (q.property he.symm)
  | inr p =>
    cases y with
    | inl q =>
      obtain ⟨a,k⟩ := q
      have he := congrArg (fun p : Cone => p.val.2%p.val.1) h
      change p.val.val.2%p.val.val.1=(multiplePair a k).val.2%(multiplePair a k).val.1 at he
      rw [multiplePair_mod] at he
      exact False.elim (p.property he)
    | inr q => exact congrArg Sum.inr (Subtype.ext h)

private theorem splitPair_surjective : Function.Surjective splitPair := by
  intro p
  by_cases hp : p.val.2%p.val.1=0
  · have hpos : 0 < p.val.2/p.val.1 := Nat.div_pos (le_of_lt p.property.2) p.property.1
    have he : p.val.1*(p.val.2/p.val.1)=p.val.2 := by
      simpa only [hp,zero_add] using Nat.mod_add_div p.val.2 p.val.1
    have hn : 2 ≤ p.val.2/p.val.1 := by
      by_contra hn
      have hq : p.val.2/p.val.1=1 := by omega
      rw [hq,mul_one] at he
      have h := p.property.2
      omega
    refine ⟨Sum.inl (⟨p.val.1,p.property.1⟩,p.val.2/p.val.1-2),?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change p.val.1*(p.val.2/p.val.1-2+2)=p.val.2
      rw [Nat.sub_add_cancel hn,he]
  · exact ⟨Sum.inr ⟨p,hp⟩,rfl⟩

/-- Exact partition into multiple rays and branch-renewed cone pairs. -/
def multipleNonmultipleEquiv : (ℕ+ × ℕ) ⊕ NonmultipleCone ≃ Cone :=
  Equiv.ofBijective splitPair ⟨splitPair_injective,splitPair_surjective⟩

theorem renewalEquiv_apply (n : ℕ+) (p : Cone) :
    (renewalEquiv (n,p)).val.val=(p.val.2,(n : ℕ)*p.val.2+p.val.1) := rfl

theorem multipleNonmultipleEquiv_inl (a : ℕ+) (k : ℕ) :
    multipleNonmultipleEquiv (.inl (a,k))=multiplePair a k := rfl

theorem multipleNonmultipleEquiv_inr (p : NonmultipleCone) :
    multipleNonmultipleEquiv (.inr p)=p.val := rfl

#print axioms branchPair_surjective
#print axioms rectangleEquiv
#print axioms renewalEquiv
#print axioms multipleNonmultipleEquiv
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerLatticeRenewal
