import GaloisForLFunctions.RepresentationLifting.Lattices.SimplexFacetSumCokernel
import Mathlib.Data.Finset.Powerset
import GaloisForLFunctions.HTGeometry.UniformGaleContraction

/-!
# Integral incidence of uniform matroid bases

Single-element exchanges generate all coordinate differences. The remaining
obstruction is the total sum modulo the rank, or modulo the gcd of rank and corank
for bases and cobases together.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset Submodule
open scoped Classical
noncomputable section

variable {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]

/-- Indicator of an incidence column over the chosen coefficient ring. -/
def edgeIndicator (S : Finset ι) (i : ι) : R := if i ∈ S then 1 else 0

/-- Span of columns of the vertex/edge incidence matrix of the complete
k-uniform hypergraph. -/
def uniformEdgeSpan (k : ℕ) : Submodule R (ι → R) :=
  span R (edgeIndicator R '' {S : Finset ι | S.card=k})

private theorem edge_mem (k : ℕ) {S : Finset ι} (h : S.card=k) :
    edgeIndicator R S ∈ uniformEdgeSpan (ι:=ι) R k := subset_span ⟨S,h,rfl⟩

private theorem exchange_mem (k : Set.Ioo (0:ℕ) (Fintype.card ι)) (i j : ι) :
    (Pi.single i 1-Pi.single j 1 : ι → R) ∈ uniformEdgeSpan R k.val := by
  by_cases hi : i=j
  · simp [hi]
  let U := ((univ : Finset ι).erase i).erase j
  have hj : j ∈ (univ : Finset ι).erase i := mem_erase.mpr ⟨hi.symm,mem_univ _⟩
  have hsize : k.val-1 ≤ U.card := by
    have hk := k.property.2
    simp only [U,card_erase_of_mem hj,card_erase_of_mem (mem_univ i),card_univ]
    omega
  obtain ⟨T,hT,hcard⟩ := exists_subset_card_eq hsize
  have hn₁ : i ∉ T := fun h => notMem_erase i univ (mem_of_mem_erase (hT h))
  have hn₂ : j ∉ T := fun h => notMem_erase j _ (hT h)
  have hcard' {z : ι} (hz : z ∉ T) : (insert z T).card = k.val := by
    rw [card_insert_of_notMem hz,hcard]; have := k.property.1; omega
  have hv : edgeIndicator R (insert i T)-edgeIndicator R (insert j T) =
      (Pi.single i 1-Pi.single j 1 : ι → R) := by
    funext z
    by_cases hzi : z=i
    · subst z
      simp [edgeIndicator,Pi.single_apply,hi,hi.symm,hn₁]
    · by_cases hzj : z=j
      · subst z
        simp [edgeIndicator,Pi.single_apply,hi,hi.symm,hn₂]
      · simp [edgeIndicator,Pi.single_apply,hzi,hzj,Ne.symm hzi,Ne.symm hzj]
  rw [← hv]
  exact sub_mem _ (edge_mem R _ (hcard' hn₁)) (edge_mem R _ (hcard' hn₂))

private theorem total_edge (S : Finset ι) : ∑ i, edgeIndicator R S i = (S.card:R) := by
  simp [edgeIndicator,sum_boole]

/-- Every zero-sum vector is an integral linear combination of single-vertex exchanges. -/
private theorem augmentation_mem (k : Set.Ioo (0:ℕ) (Fintype.card ι)) (j : ι) (x : ι → R)
    (hx : ∑ i, x i = 0) : x ∈ uniformEdgeSpan R k.val := by
  have he : ∑ i, x i • (Pi.single i 1 - Pi.single j 1 : ι → R) = x := by
    funext t
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,mul_sub,sum_sub_distrib,
      ← sum_mul,hx,zero_mul,sub_zero]
    simp [Pi.single_apply]
  rw [← he]
  exact sum_mem fun i _ => smul_mem _ _ (exchange_mem R k i j)

/-- All k-uniform edge sums are realizable exactly when the total coordinate
sum is a multiple of k. No restriction on the residue characteristic is needed. -/
theorem uniformEdgeSpan_mem (k : Set.Ioo (0:ℕ) (Fintype.card ι)) (x : ι → R) :
    x ∈ uniformEdgeSpan R k.val ↔ (k.val:R) ∣ ∑ i, x i := by
  let T : (ι → R) →ₗ[R] R := ∑ i, LinearMap.proj i
  have hT (y : ι → R) : T y = ∑ i, y i := by simp [T]
  have hle : uniformEdgeSpan (ι:=ι) R k.val ≤ (Ideal.span ({(k.val:R)} : Set R)).comap T := by
    apply span_le.mpr
    rintro _ ⟨S,hS,rfl⟩
    change T (edgeIndicator R S) ∈ Ideal.span _
    rw [hT,total_edge,show S.card=k.val from hS,Ideal.mem_span_singleton]
  constructor
  · intro hx
    have h := hle hx
    simpa only [Submodule.mem_comap,hT,Ideal.mem_span_singleton] using h
  · rintro ⟨a,ha⟩
    obtain ⟨S,_,hc⟩ := exists_subset_card_eq (s:= univ (α:=ι)) (n:=k.val)
      (by simpa only [card_univ] using k.property.2.le)
    obtain ⟨j,_⟩ := card_pos.mp (hc.symm ▸ k.property.1)
    have hz : ∑ i, (x-a • edgeIndicator R S) i = 0 := by
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,sum_sub_distrib,← mul_sum,total_edge,hc,ha]
      ring
    have hh := add_mem (uniformEdgeSpan (ι:=ι) R k.val) (augmentation_mem R k j _ hz)
      (smul_mem _ a (edge_mem R _ hc))
    simpa only [sub_add_cancel] using hh

/-- The complete invariant-factor obstruction, over any commutative base. -/
def uniformEdgeCokernel (k : Set.Ioo (0:ℕ) (Fintype.card ι)) :
    ((ι → R) ⧸ uniformEdgeSpan R k.val) ≃ₗ[R] R ⧸ Ideal.span ({(k.val:R)} : Set R) := by
  let f := (Ideal.span ({(k.val:R)} : Set R)).mkQ.comp (∑ i : ι, LinearMap.proj (R:=R) i)
  have hf (x : ι → R) : f x = Submodule.Quotient.mk (∑ i, x i) := by simp [f]
  have hk : f.ker = uniformEdgeSpan (ι:=ι) R k.val := by
    ext x
    rw [LinearMap.mem_ker,hf,Submodule.Quotient.mk_eq_zero,Ideal.mem_span_singleton,uniformEdgeSpan_mem]
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨a,rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hn := Fintype.card_pos_iff.mp (k.property.1.trans k.property.2)
    obtain ⟨i⟩ := hn
    exact ⟨Pi.single i a,by simp [hf]⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hsurj)

/-- An assignment with zero sum on every edge is constant and annihilated
by k. This classifies the dual kernel over arbitrary coefficient rings. -/
theorem uniformEdge_kernel (k : Set.Ioo (0:ℕ) (Fintype.card ι)) (y : ι → R) :
    (∀ S : Finset ι, S.card=k.val → ∑ i ∈ S, y i = 0) ↔
      ∃ b : R, (k.val:R)*b=0 ∧ y=fun _ => b := by
  let f : (ι → R) →ₗ[R] R :=
    ∑ i, y i • (LinearMap.proj (R:=R) i : (ι → R) →ₗ[R] R)
  have hf (x : ι → R) : f x = ∑ i, y i*x i := by simp [f]
  have hS (S : Finset ι) : f (edgeIndicator R S) = ∑ i ∈ S, y i := by
    simp only [hf,edgeIndicator,mul_ite,mul_one,mul_zero,← sum_filter]
    simp
  constructor
  · intro hy
    have hle : uniformEdgeSpan R k.val ≤ f.ker := by
      apply span_le.mpr
      rintro _ ⟨S,h,rfl⟩
      rw [LinearMap.mem_ker,hS,hy S h]
    have hn := Fintype.card_pos_iff.mp (k.property.1.trans k.property.2)
    obtain ⟨j⟩ := hn
    have hconst (i : ι) : y i = y j := by
      have h := hle (exchange_mem R k i j)
      rw [LinearMap.mem_ker,map_sub,hf,hf] at h
      simpa [Pi.single_apply] using sub_eq_zero.mp h
    refine ⟨y j,?_,funext hconst⟩
    obtain ⟨S,_,hc⟩ := exists_subset_card_eq (s:= univ (α:=ι)) (n:=k.val)
      (by simpa only [card_univ] using k.property.2.le)
    have h := hy S hc
    simpa only [hconst,sum_const,nsmul_eq_mul,hc] using h
  · rintro ⟨b,hb,rfl⟩ S hS'
    simpa [hS',nsmul_eq_mul] using hb

/-- Incidence span of the actual bases of a finite matroid. -/
def baseIncidenceSpan (M : Matroid ι) : Submodule R (ι → R) :=
  span R (edgeIndicator R '' {S : Finset ι | M.IsBase (S : Set ι)})

theorem uniformBaseSpan (k : Set.Ioo (0:ℕ) (Fintype.card ι)) :
    baseIncidenceSpan R (HTGeometry.uniformMatroidOn (Set.univ : Set ι) k.val) = uniformEdgeSpan R k.val := by
  have hk : k.val ≤ (Set.univ : Set ι).ncard := by simpa using k.property.2.le
  unfold baseIncidenceSpan uniformEdgeSpan
  congr 2
  ext S
  simp [HTGeometry.uniformMatroidOn_isBase_iff hk]

private theorem uniform_sup_mem (k l : Set.Ioo (0:ℕ) (Fintype.card ι)) (x : ι → R) :
    x ∈ uniformEdgeSpan R k.val ⊔ uniformEdgeSpan R l.val ↔
      ∃ a b : R, ∑ i, x i = k.val*a+l.val*b := by
  constructor
  · intro h
    obtain ⟨v,hv,w,hw,rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨a,ha⟩ := (uniformEdgeSpan_mem R k _).mp hv
    obtain ⟨b,hb⟩ := (uniformEdgeSpan_mem R l _).mp hw
    exact ⟨a,b,by simp only [Pi.add_apply,sum_add_distrib,ha,hb]⟩
  · rintro ⟨a,b,h⟩
    obtain ⟨j⟩ := Fintype.card_pos_iff.mp (k.property.1.trans k.property.2)
    let w : ι → R := Pi.single j (l.val*b)
    have hw : ∑ i, w i = l.val*b := by simp [w]
    apply Submodule.mem_sup.mpr
    refine ⟨x-w,(uniformEdgeSpan_mem R k _).mpr ⟨a,?_⟩,w,
      (uniformEdgeSpan_mem R l _).mpr ⟨b,hw⟩,sub_add_cancel _ _⟩
    rw [show (∑ i, (x-w) i) = (∑ i, x i)-∑ i,w i from sum_sub_distrib,h,hw,add_sub_cancel_right]

open scoped Matroid in
/-- Joint incidence of uniform matroid bases and dual bases detects the gcd
of rank and corank. The two complete base systems can span integrally even
when neither base system spans integrally on its own. -/
theorem uniform_primal_dual_lattice (k : Set.Ioo (0:ℕ) (Fintype.card ι)) (x : ι → ℤ) :
    let M := HTGeometry.uniformMatroidOn (Set.univ : Set ι) k.val
    x ∈ baseIncidenceSpan ℤ M ⊔ baseIncidenceSpan ℤ M✶ ↔
      (Nat.gcd k.val (Fintype.card ι-k.val):ℤ) ∣ ∑ i, x i := by
  let m := Fintype.card ι-k.val
  have hm : m ∈ Set.Ioo 0 (Fintype.card ι) := ⟨Nat.sub_pos_of_lt k.property.2,
    Nat.sub_lt (k.property.1.trans k.property.2) k.property.1⟩
  dsimp only
  rw [HTGeometry.uniformMatroidOn_dual (by simpa using k.property.2.le),Set.ncard_univ,
    Nat.card_eq_fintype_card,uniformBaseSpan ℤ k,uniformBaseSpan ℤ ⟨m,hm⟩,
    uniform_sup_mem ℤ k ⟨m,hm⟩]
  constructor
  · rintro ⟨a,b,h⟩
    rw [h]
    exact dvd_add ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)).trans (dvd_mul_right _ _))
      ((Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (dvd_mul_right _ _))
  · rintro ⟨c,h⟩
    refine ⟨(Nat.gcdA k.val m)*c,(Nat.gcdB k.val m)*c,?_⟩
    rw [h,Nat.gcd_eq_gcd_ab]
    ring
end
end GaloisForLFunctions.RepresentationLifting
