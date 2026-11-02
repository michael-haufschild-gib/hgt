import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.PNat.Basic

/-! Euclidean division classifies the primitive positive pairs reached by
one Gauss inverse branch. The first-coordinate-one pairs are exactly the
boundary rows excluded from this bijection. -/

set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeRenewal

/-- Primitive lattice pairs strictly inside the positive cone `p<q`. -/
def Cone := {p : ℕ × ℕ // 0 < p.1 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2}

/-- The interior rows after removing first coordinate one. -/
def DeepCone := {p : Cone // 2 ≤ p.val.1}

/-- The literal denominator-pair action of a positive Gauss branch. -/
def branchPair (n : ℕ+) (p : Cone) : DeepCone :=
  ⟨⟨(p.val.2,(n : ℕ)*p.val.2+p.val.1),by
    have hp := p.property
    have hn : 1 ≤ (n : ℕ) := n.property
    have hmul := Nat.mul_le_mul_right p.val.2 hn
    simp only [one_mul] at hmul
    exact ⟨by omega,by omega,(Nat.coprime_mul_right_add_right p.val.2 p.val.1 n).mpr p.property.2.2.symm⟩⟩,
      by change 2 ≤ p.val.2; have hp := p.property; omega⟩

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

theorem branchPair_injective : Function.Injective (fun x : ℕ+ × Cone => branchPair x.1 x.2) := by
  rintro ⟨n,p⟩ ⟨m,r⟩ he
  have hq : p.val.2=r.val.2 := congrArg (fun x : DeepCone => x.val.val.1) he
  have hsum : (n : ℕ)*p.val.2+p.val.1=(m : ℕ)*r.val.2+r.val.1 :=
    congrArg (fun x : DeepCone => x.val.val.2) he
  rw [← hq] at hsum
  have hnr := quotient_unique p.property.2.1 (by rw [hq]; exact r.property.2.1) hsum
  have hnm : n=m := Subtype.ext hnr
  have hpr : p=r := by
    apply Subtype.ext
    apply Prod.ext
    · rw [hnr] at hsum
      exact Nat.add_left_cancel hsum
    · exact hq
  exact Prod.ext hnm hpr

/-- Coprimality excludes zero remainder, so every deep cone point has one predecessor. -/
theorem branchPair_surjective : Function.Surjective (fun x : ℕ+ × Cone => branchPair x.1 x.2) := by
  intro x
  have hp : 0 < x.val.val.1 := x.val.property.1
  have hq : x.val.val.1 < x.val.val.2 := x.val.property.2.1
  have hn : 0 < x.val.val.2/x.val.val.1 := Nat.div_pos (by omega) hp
  have hr : x.val.val.2%x.val.val.1 < x.val.val.1 := Nat.mod_lt _ hp
  have hc : Nat.Coprime (x.val.val.2%x.val.val.1) x.val.val.1 := by
    change Nat.gcd (x.val.val.2%x.val.val.1) x.val.val.1=1
    rw [← Nat.gcd_rec]
    exact x.val.property.2.2
  have hrpos : 0 < x.val.val.2%x.val.val.1 := by
    by_contra h
    have hz : x.val.val.2%x.val.val.1=0 := by omega
    have hg := hc
    change Nat.gcd (x.val.val.2%x.val.val.1) x.val.val.1=1 at hg
    simp only [hz,Nat.gcd_zero_left] at hg
    have hx := x.property
    omega
  refine ⟨(⟨x.val.val.2/x.val.val.1,hn⟩,
    ⟨(x.val.val.2%x.val.val.1,x.val.val.1),hrpos,hr,hc⟩),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (x.val.val.2/x.val.val.1)*x.val.val.1+x.val.val.2%x.val.val.1=x.val.val.2
    simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div x.val.val.2 x.val.val.1

/-- Exact primitive-lattice renewal under one positive Gauss inverse branch. -/
def renewalEquiv : ℕ+ × Cone ≃ DeepCone :=
  Equiv.ofBijective (fun x => branchPair x.1 x.2) ⟨branchPair_injective,branchPair_surjective⟩

/-- The remaining primitive rows have first coordinate one and second coordinate at least two. -/
def boundaryPair (k : ℕ) : Cone :=
  ⟨(1,k+2),by
    change 0 < (1 : ℕ) ∧ 1 < k+2 ∧ Nat.Coprime 1 (k+2)
    exact ⟨by omega,by omega,Nat.coprime_one_left _⟩⟩

private def splitPair : ℕ ⊕ DeepCone → Cone
  | .inl k => boundaryPair k
  | .inr p => p.val

private theorem splitPair_injective : Function.Injective splitPair := by
  intro x y h
  cases x with
  | inl k =>
    cases y with
    | inl l =>
      have he := congrArg (fun p : Cone => p.val.2) h
      change k+2=l+2 at he
      have hk : k=l := by omega
      exact congrArg Sum.inl hk
    | inr p =>
      have he := congrArg (fun p : Cone => p.val.1) h
      change 1=p.val.val.1 at he
      have hp := p.property
      omega
  | inr p =>
    cases y with
    | inl k =>
      have he := congrArg (fun p : Cone => p.val.1) h
      change p.val.val.1=1 at he
      have hp := p.property
      omega
    | inr q =>
      exact congrArg Sum.inr (Subtype.ext h)

private theorem splitPair_surjective : Function.Surjective splitPair := by
  intro p
  by_cases hp : p.val.1=1
  · refine ⟨Sum.inl (p.val.2-2),?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hp.symm
    · change p.val.2-2+2=p.val.2
      have h := p.property.2.1
      omega
  · have h := p.property.1
    exact ⟨Sum.inr ⟨p,by omega⟩,rfl⟩

/-- Exact partition into boundary rows and the image of the primitive renewal map. -/
def boundaryDeepEquiv : ℕ ⊕ DeepCone ≃ Cone :=
  Equiv.ofBijective splitPair ⟨splitPair_injective,splitPair_surjective⟩

theorem renewalEquiv_apply (n : ℕ+) (p : Cone) :
    (renewalEquiv (n,p)).val.val=(p.val.2,(n : ℕ)*p.val.2+p.val.1) := rfl

#print axioms branchPair_injective
#print axioms branchPair_surjective
#print axioms renewalEquiv
#print axioms boundaryDeepEquiv

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoprimeRenewal
