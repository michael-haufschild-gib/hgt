import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeVertexLocalFlow
import DifferentialGeometry.Topology.Homology.Relative
import Mathlib.NumberTheory.Bertrand

/-!
# Signed singular-homology indices of arithmetic prime vertices

When the conductor cutoff does not exceed the cube of the apex prime, the
actual exit link is a finite discrete space of larger prime neighbours.
The local block is contractible, so its relative singular-homology Euler
characteristic is one minus the number of those neighbours.
-/
noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open EffectiveScalingGeometry HodgeTheoryWithoutVarieties

/-- Larger prime neighbours whose product with the apex remains below the cutoff. -/
def PrimeUpperNeighbour (B N : ℕ) (p : Fin (B+3)) :=
  {q : Fin (B+3) // p<q ∧ q.val.Prime ∧ p.val*q.val≤N}

instance primeUpperNeighbourFintype (B N : ℕ) (p : Fin (B+3)) :
    Fintype (PrimeUpperNeighbour B N p) :=
  inferInstanceAs (Fintype {q : Fin (B+3) // p<q ∧ q.val.Prime ∧ p.val*q.val≤N})

/-- Below the cubic cutoff no upper-link face can contain two distinct vertices. -/
theorem primeUpperLink_pair_eq {B N : ℕ} {p : Fin (B+3)} (hN : N≤p.val^3)
    {S : Finset (Fin (B+3))} (hS : S∈primeUpperLinkFaces B N p)
    {q r : Fin (B+3)} (hq : q∈S) (hr : r∈S) : q=r := by
  by_contra hqr
  have hS' := (mem_filter.mp hS).2
  have hpq := hS'.1 q hq
  have hpr := hS'.1 r hr
  have hface := mem_primeHeightFaces.mp hS'.2
  have hp := hface.1 p (mem_insert_self p S)
  have hsub : ({p,q,r} : Finset (Fin (B+3)))⊆insert p S := by
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨mem_insert_self p S,mem_insert_of_mem hq,mem_insert_of_mem hr⟩
  have hm := prod_le_prod_of_subset_of_one_le' (f := fun a : Fin (B+3) => a.val) hsub
    (fun a ha _ => (hface.1 a ha).one_lt.le)
  have hpnot : p∉({q,r} : Finset (Fin (B+3))) := by
    simp only [mem_insert,mem_singleton,not_or]
    exact ⟨ne_of_lt hpq,ne_of_lt hpr⟩
  rw [prod_insert hpnot,prod_insert (show q∉({r}:Finset (Fin (B+3))) by simpa only [mem_singleton] using hqr),prod_singleton] at hm
  have hqnat : p.val<q.val := hpq
  have hrnat : p.val<r.val := hpr
  have hmul : p.val*p.val<q.val*r.val :=
    (Nat.mul_lt_mul_of_pos_right hqnat hp.pos).trans_le
      (Nat.mul_le_mul_left q.val hrnat.le)
  have hcube : p.val^3<p.val*(q.val*r.val) := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using Nat.mul_lt_mul_of_pos_left hmul hp.pos
  exact (not_lt_of_ge (hm.trans (hface.2.trans hN))) hcube

/-- Every larger arithmetic neighbour is a vertex of the actual upper link. -/
def primeUpperNeighbourVertex {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime)
    (q : PrimeUpperNeighbour B N p) : faceFamilySpace (primeUpperLinkFaces B N p) :=
  ⟨stdSimplex.vertex (S := ℝ) q.val,mem_faceFamilySpace.mpr
    ⟨{q.val},mem_filter.mpr ⟨mem_univ _,by
      intro r hr
      simpa only [mem_singleton.mp hr] using q.property.1,by
      apply mem_primeHeightFaces.mpr
      constructor
      · intro r hr
        rcases mem_insert.mp hr with rfl | hr
        · exact hp
        · rw [mem_singleton] at hr
          simpa only [hr] using q.property.2.1
      · rw [prod_insert (show p∉({q.val}:Finset (Fin (B+3))) by
          simpa only [mem_singleton] using ne_of_lt q.property.1),prod_singleton]
        exact q.property.2.2⟩,vertex_mem_supportFace (mem_singleton_self _)⟩⟩

theorem primeUpperNeighbourVertex_injective {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime) :
    Function.Injective (primeUpperNeighbourVertex (N := N) p hp) := by
  intro q r he
  apply Subtype.ext
  by_contra hqr
  have hc := congrArg (fun x : faceFamilySpace (primeUpperLinkFaces B N p) => x.val.val q.val) he
  change (Pi.single q.val (1:ℝ) : Fin (B+3) → ℝ) q.val=
    (Pi.single r.val (1:ℝ) : Fin (B+3) → ℝ) q.val at hc
  rw [Pi.single_eq_same,Pi.single_eq_of_ne hqr] at hc
  exact one_ne_zero hc

/-- At cubic cutoff the whole upper-link realization consists of arithmetic neighbour vertices. -/
theorem primeUpperNeighbourVertex_surjective {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime)
    (hN : N≤p.val^3) : Function.Surjective (primeUpperNeighbourVertex (N := N) p hp) := by
  intro x
  obtain ⟨S,hS,hxS⟩ := mem_faceFamilySpace.mp x.property
  have hnonzero : ∃q,x.val.val q≠0 := by
    by_contra h
    push Not at h
    have hs := x.val.property.2
    simp only [h,sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨q,hq⟩ := hnonzero
  have hqS : q∈S := by
    by_contra hn
    exact hq (hxS q hn)
  have hsingle : S={q} := by
    apply subset_antisymm
    · intro r hr
      exact mem_singleton.mpr (primeUpperLink_pair_eq hN hS hr hqS)
    · exact singleton_subset_iff.mpr hqS
  have hS' := (mem_filter.mp hS).2
  have hf := mem_primeHeightFaces.mp hS'.2
  have hpq := hS'.1 q hqS
  have hprod : p.val*q.val≤N := by
    have h := hf.2
    rw [hsingle,prod_insert (show p∉({q}:Finset (Fin (B+3))) by
      simpa only [mem_singleton] using ne_of_lt hpq),prod_singleton] at h
    exact h
  let v : PrimeUpperNeighbour B N p := ⟨q,hpq,hf.1 q (mem_insert_of_mem hqS),hprod⟩
  refine ⟨v,?_⟩
  have hz (r : Fin (B+3)) (hr : r≠q) : x.val.val r=0 :=
    hxS r (by simpa only [hsingle,mem_singleton] using hr)
  have hs : ∑r,x.val.val r=x.val.val q := sum_eq_single q
    (fun r _ hr => hz r hr) (fun hn => (hn (mem_univ q)).elim)
  have hq1 : x.val.val q=1 := hs.symm.trans x.val.property.2
  apply Subtype.ext
  apply Subtype.ext
  funext r
  change (Pi.single q (1:ℝ) : Fin (B+3) → ℝ) r=x.val.val r
  by_cases hr : r=q
  · subst r
    rw [Pi.single_eq_same,hq1]
  · rw [Pi.single_eq_of_ne hr,hz r hr]

/-- The local index is defined by actual relative singular homology of the exit pair. -/
def primeVertexRelativeIndex (B N : ℕ) (p : Fin (B+3)) : ℤ :=
  DifferentialGeometry.Homology.relativeEulerChar (TopCat.of (primeVertexBlock B N p))
    (primeVertexExit B N p) ℚ

private theorem relativeEuler_of_contractible_finite_exit (X Y : TopCat.{0}) (A : Set X)
    [ContractibleSpace X] [Finite Y] [TotallyDisconnectedSpace Y] (e : A ≃ₕ Y) :
    DifferentialGeometry.Homology.relativeEulerChar X A ℚ=1-(Nat.card Y:ℤ) := by
  have hY := DifferentialGeometry.Homology.finiteHomologyType_of_finite_totallyDisconnected ℚ (X := Y)
  have hA := (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homotopyEquiv ℚ
    (X := TopCat.of A) (Y := Y) e).mpr hY
  have hX := DifferentialGeometry.Homology.finiteHomologyType_of_contractible ℚ (X := X)
  calc
    DifferentialGeometry.Homology.relativeEulerChar X A ℚ=
        DifferentialGeometry.Homology.eulerChar ℚ X-DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of A) :=
      DifferentialGeometry.Homology.relativeEulerChar_eq_sub X A ℚ hA hX
    _=1-DifferentialGeometry.Homology.eulerChar ℚ Y := by
      rw [DifferentialGeometry.Homology.eulerChar_of_contractible,
        DifferentialGeometry.Homology.eulerChar_eq_of_homotopyEquiv ℚ (X := TopCat.of A) (Y := Y) e]
    _=1-(Nat.card Y:ℤ) := by rw [DifferentialGeometry.Homology.eulerChar_of_finite_totallyDisconnected]

/-- Exact signed local index in the entire discrete-exit range. -/
theorem primeVertexRelativeIndex_cubic {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime)
    (hpN : p.val≤N) (hN : N≤p.val^3) :
    primeVertexRelativeIndex B N p=1-(Nat.card (PrimeUpperNeighbour B N p):ℤ) := by
  letI : ContractibleSpace (primeVertexBlock B N p) := primeVertexBlock_contractible p hp hpN
  letI : Finite (faceFamilySpace (primeUpperLinkFaces B N p)) :=
    Finite.of_surjective (primeUpperNeighbourVertex p hp) (primeUpperNeighbourVertex_surjective p hp hN)
  have he : primeVertexRelativeIndex B N p=
      1-(Nat.card (faceFamilySpace (primeUpperLinkFaces B N p)):ℤ) :=
    relativeEuler_of_contractible_finite_exit (TopCat.of (primeVertexBlock B N p))
      (TopCat.of (faceFamilySpace (primeUpperLinkFaces B N p))) (primeVertexExit B N p)
      (primeExitLinkHomotopyEquiv B N p)
  rw [he]
  have hc := Nat.card_congr (Equiv.ofBijective (primeUpperNeighbourVertex p hp)
    ⟨primeUpperNeighbourVertex_injective p hp,primeUpperNeighbourVertex_surjective p hp hN⟩)
  rw [←hc]

#print axioms primeUpperLink_pair_eq
#print axioms primeUpperNeighbourVertex_surjective
#print axioms primeVertexRelativeIndex_cubic

/-- Every dyadic prime interval above the apex supplies a distinct exit component. -/
theorem primeUpperNeighbour_card_ge {p k : ℕ} (hp : p.Prime) (hk : 2^k≤p) :
    k≤Nat.card (PrimeUpperNeighbour (p^3) (p^3) ⟨p,by
      have hh : p≤p^3 := Nat.le_pow (by omega : 0<3)
      omega⟩) := by
  classical
  let v : Fin (p^3+3) := ⟨p,by
    have hh : p≤p^3 := Nat.le_pow (by omega : 0<3)
    omega⟩
  have hex (i : Fin k) : ∃q,q.Prime ∧ 2^i.val*p<q ∧ q≤2*(2^i.val*p) :=
    Nat.exists_prime_lt_and_le_two_mul (2^i.val*p)
      (mul_ne_zero (pow_ne_zero _ (by omega)) hp.ne_zero)
  let q (i : Fin k) := Classical.choose (hex i)
  have hq (i : Fin k) : (q i).Prime ∧ 2^i.val*p<q i ∧ q i≤2*(2^i.val*p) :=
    Classical.choose_spec (hex i)
  have hbound (i : Fin k) : q i≤p*p := by
    have hi : 2^(i.val+1)≤2^k := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      q i≤2*(2^i.val*p) := (hq i).2.2
      _=2^(i.val+1)*p := by rw [pow_succ]; ring
      _≤2^k*p := Nat.mul_le_mul_right p hi
      _≤p*p := Nat.mul_le_mul_right p hk
  have hpCube : p*p≤p^3 := by
    have hh := Nat.mul_le_mul_left (p*p) hp.one_lt.le
    simpa only [pow_succ,pow_zero,mul_one,one_mul] using hh
  let e : Fin k → PrimeUpperNeighbour (p^3) (p^3) v := fun i =>
    ⟨⟨q i,by have h := (hbound i).trans hpCube; omega⟩,by
      constructor
      · change p<q i
        have hpow : 1≤2^i.val := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
        have hbase : p≤2^i.val*p := by
          simpa only [one_mul] using Nat.mul_le_mul_right p hpow
        exact hbase.trans_lt (hq i).2.1
      exact ⟨(hq i).1,by
        change p*q i≤p^3
        have h := Nat.mul_le_mul_left p (hbound i)
        simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using h⟩⟩
  have hstrict : StrictMono q := by
    intro i j hij
    have hpow : 2^(i.val+1)≤2^j.val := Nat.pow_le_pow_right (by omega) (by exact hij)
    calc
      q i≤2*(2^i.val*p) := (hq i).2.2
      _=2^(i.val+1)*p := by rw [pow_succ]; ring
      _≤2^j.val*p := Nat.mul_le_mul_right p hpow
      _<q j := (hq j).2.1
  have hinj : Function.Injective e := by
    intro i j he
    exact hstrict.injective (congrArg
      (fun z : PrimeUpperNeighbour (p^3) (p^3) v => z.val.val) he)
  have hc := Nat.card_le_card_of_injective e hinj
  simpa only [Nat.card_fin] using hc

/-- Genuine relative singular-homology indices are unbounded below on arithmetic prime complexes. -/
theorem primeVertexRelativeIndex_unbounded_below (k : ℕ) :
    ∃ (N : ℕ) (p : Fin (N+3)),p.val.Prime ∧ p.val≤N ∧ primeVertexRelativeIndex N N p≤-(k:ℤ) := by
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes (2^(k+1))
  have hpCube : p≤p^3 := Nat.le_pow (by omega : 0<3)
  let v : Fin (p^3+3) := ⟨p,by omega⟩
  refine ⟨p^3,v,hp,hpCube,?_⟩
  rw [primeVertexRelativeIndex_cubic v hp hpCube le_rfl]
  have hc := primeUpperNeighbour_card_ge hp hpbound
  have hc' : (k+1:ℕ)≤Nat.card (PrimeUpperNeighbour (p^3) (p^3) v) := hc
  have hz : (k:ℤ)+1≤(Nat.card (PrimeUpperNeighbour (p^3) (p^3) v):ℤ) := by exact_mod_cast hc'
  linarith only [hz]

#print axioms primeVertexRelativeIndex_unbounded_below

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
