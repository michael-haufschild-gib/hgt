import GaloisForLFunctions.SignedArithmeticCorrespondences.DivisorIncidenceOnLateCombs

/-!
# The path components of the fourfold Weil comb

For (6k,24k] only ratios two and three occur. A lower endpoint at most 8k
has both contacts. Its triple is shared with a double precisely when that
lower endpoint is even. The resulting nontrivial components have two,
three, or four vertices. The decomposition holds for arbitrary signed
profiles and arbitrary contact weights.
-/

open Finset
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
noncomputable section
open scoped Classical

/-- Lower endpoints of the isolated two-vertex components. -/
def fourfoldPairs (k : ℕ) : Finset ℕ :=
  (Ioc (8*k) (12*k)).filter fun a => a ≤ 9*k ∨ ¬3 ∣ a

/-- Odd lower endpoints with both a double and a triple. -/
def fourfoldTriples (k : ℕ) : Finset ℕ :=
  (Ioc (6*k) (8*k)).filter fun b => b%2=1

/-- A four-vertex component indexed by i has path 4i, 2i, 6i, 3i. -/
def fourfoldQuads (k : ℕ) : Finset ℕ := Ioc (3*k) (4*k)

private theorem small_lowers (k : ℕ) :
    Ioc (6*k) (8*k) = fourfoldTriples k ∪ (fourfoldQuads k).image (fun i => 2*i) := by
  ext n
  simp only [fourfoldTriples,fourfoldQuads,mem_union,mem_filter,mem_Ioc,mem_image]
  constructor
  · intro h
    by_cases hodd : n%2=1
    · exact Or.inl ⟨h,hodd⟩
    · exact Or.inr ⟨n/2,by omega,by omega⟩
  · rintro (h|⟨i,hi,rfl⟩) <;> omega

private theorem large_lowers (k : ℕ) :
    Ioc (8*k) (12*k) = fourfoldPairs k ∪ (fourfoldQuads k).image (fun i => 3*i) := by
  ext n
  simp only [fourfoldPairs,fourfoldQuads,mem_union,mem_filter,mem_Ioc,mem_image]
  constructor
  · intro h
    by_cases ha : n≤9*k ∨ ¬3∣n
    · exact Or.inl ⟨h,ha⟩
    · exact Or.inr ⟨n/3,by omega,by omega⟩
  · rintro (h|⟨i,hi,rfl⟩) <;> omega

private theorem small_disjoint (k : ℕ) :
    Disjoint (fourfoldTriples k) ((fourfoldQuads k).image fun i => 2*i) := by
  apply disjoint_left.mpr
  intro n hn hm
  obtain ⟨i,_,rfl⟩ := mem_image.mp hm
  have := (mem_filter.mp hn).2
  omega

private theorem large_disjoint (k : ℕ) :
    Disjoint (fourfoldPairs k) ((fourfoldQuads k).image fun i => 3*i) := by
  apply disjoint_left.mpr
  intro n hn hm
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
  have := (mem_filter.mp hn).2
  have := (mem_Ioc.mp hi).1
  omega

/-- The anchored comb has 3k pairs, k triples and k four-vertex paths. -/
theorem fourfold_path_counts (k : ℕ) :
    (fourfoldPairs k).card=3*k ∧ (fourfoldTriples k).card=k ∧ (fourfoldQuads k).card=k := by
  have hq : (fourfoldQuads k).card=k := by rw [fourfoldQuads,Nat.card_Ioc]; omega
  have h₁ := congrArg Finset.card (small_lowers k)
  have h₂ := congrArg Finset.card (large_lowers k)
  rw [Nat.card_Ioc,card_union_of_disjoint (small_disjoint k),card_image_of_injective _
    (fun i j (h : 2*i=2*j) => by omega),hq] at h₁
  rw [Nat.card_Ioc,card_union_of_disjoint (large_disjoint k),card_image_of_injective _
    (fun i j (h : 3*i=3*j) => by omega),hq] at h₂
  exact ⟨by omega,by omega,hq⟩

/-- Labels for the three types of nontrivial component. -/
inductive FourfoldPath where
  | pair (a : ℕ)
  | triple (b : ℕ)
  | quad (i : ℕ)
  deriving DecidableEq

def FourfoldPath.admissible (k : ℕ) : FourfoldPath → Prop
  | .pair a => a ∈ fourfoldPairs k
  | .triple b => b ∈ fourfoldTriples k
  | .quad i => i ∈ fourfoldQuads k

def FourfoldPath.sites : FourfoldPath → Finset ℕ
  | .pair a => {a,2*a}
  | .triple b => {b,2*b,3*b}
  | .quad i => {4*i,2*i,6*i,3*i}

/-- Distinct admissible labels never share a coordinate. -/
theorem fourfold_path_sites_disjoint {k : ℕ} {u v : FourfoldPath}
    (hu : u.admissible k) (hv : v.admissible k) (hne : u≠v) : Disjoint u.sites v.sites := by
  apply disjoint_left.mpr
  intro n hn hm
  cases u <;> cases v <;>
    simp only [FourfoldPath.admissible,FourfoldPath.sites,fourfoldPairs,fourfoldTriples,fourfoldQuads,
      mem_insert,mem_singleton,mem_filter,mem_Ioc,FourfoldPath.pair.injEq,FourfoldPath.triple.injEq,
      FourfoldPath.quad.injEq] at * <;> omega

theorem fourfold_path_sites_subset {k : ℕ} {u : FourfoldPath} (hu : u.admissible k) :
    u.sites ⊆ Ioc (6*k) (24*k) := by
  intro n hn
  cases u <;> simp only [FourfoldPath.admissible,FourfoldPath.sites,fourfoldPairs,
    fourfoldTriples,fourfoldQuads,mem_filter,mem_Ioc,mem_insert,mem_singleton] at * <;> omega

/-- Both orientations of the bilinear entry on an edge. -/
def fourfoldEdge (c e : ℕ → ℝ) (n m : ℕ) := c n*e m + c m*e n

/-- Exact block formula. In a four-vertex block the successive weights are
w(2), w(3), w(2). Nothing couples different blocks. -/
theorem fourfold_contact_blocks (k : ℕ) (w c e : ℕ → ℝ) :
    let E := fourfoldEdge c e
    contactTerm w (Ioc (6*k) (24*k)) c e =
      (∑ a ∈ fourfoldPairs k, w 2*E a (2*a)) +
      (∑ b ∈ fourfoldTriples k, (w 2*E b (2*b) + w 3*E b (3*b))) +
      ∑ i ∈ fourfoldQuads k, (w 2*E (2*i) (4*i) + w 3*E (2*i) (6*i) + w 2*E (3*i) (6*i)) := by
  let E := fourfoldEdge c e
  let A := fourfoldPairs k
  let B := fourfoldTriples k
  let Q := fourfoldQuads k
  have h := contactTerm_lateComb_eq w (6*k) 1 c e
  have endpoint : 6*k+3*1*(6*k)=24*k := by omega
  rw [endpoint] at h
  have hrat : Icc 2 (3*1) = ({2,3}:Finset ℕ) := by
    ext x; simp only [mem_Icc,mem_insert,mem_singleton]; omega
  rw [hrat,sum_insert (by simp),sum_singleton] at h
  have h₂ : combSlice (6*k) 1 2 = Ioc (6*k) (8*k) ∪ Ioc (8*k) (12*k) := by
    ext x; simp only [combSlice,mem_Ioc,mem_union,endpoint]; omega
  have h₃ : combSlice (6*k) 1 3 = Ioc (6*k) (8*k) := by
    unfold combSlice; rw [endpoint]; congr 1; omega
  have hdis : Disjoint (Ioc (6*k) (8*k)) (Ioc (8*k) (12*k)) :=
    disjoint_left.mpr fun _ hx hy => (not_lt_of_ge (mem_Ioc.mp hx).2) (mem_Ioc.mp hy).1
  rw [h₂,h₃,sum_union hdis,small_lowers k,large_lowers k] at h
  simp only [sum_union (small_disjoint k),sum_union (large_disjoint k),
    sum_image (fun i _ j _ (h : 2*i=2*j) => by omega),
    sum_image (fun i _ j _ (h : 3*i=3*j) => by omega)] at h
  have mul2 (i : ℕ) : 2*(2*i)=4*i := by omega
  have mul3 (i : ℕ) : 3*(2*i)=6*i := by omega
  have mul23 (i : ℕ) : 2*(3*i)=6*i := by omega
  simp only [mul2,mul3,mul23] at h
  rw [h]
  dsimp only [fourfoldEdge]
  simp only [sum_add_distrib,← mul_sum]
  ring

#print axioms fourfold_path_counts
#print axioms fourfold_path_sites_disjoint
#print axioms fourfold_contact_blocks
end
end GaloisForLFunctions.SignedArithmeticCorrespondences
