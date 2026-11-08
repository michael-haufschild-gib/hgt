import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimeComponentRigidity
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheNerveOfTheStarCover
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# The connected core and its arithmetic Euler correction

Deleting the isolated upper-half prime vertices leaves the path component of
prime two. Its signed augmented face count is the Mertens sum plus the number
of removed primes. The core is realized by the actual small-label faces and
is preserved by every self-map homotopic to the identity.
-/

noncomputable section
open Finset
open DifferentialGeometry.Simplex
open GaloisForLFunctions.EffectiveScalingGeometry
open GaloisForLFunctions.HodgeTheoryWithoutVarieties
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- The literal nerve after removing upper-half prime vertices. -/
def primeCoreNerve (N : ℕ) : Finset (Finset ℕ) :=
  (squarefreeNerve N).filter (fun S => ∀p∈S, 2*p≤N)

/-- The signed augmented face count of the connected core. -/
def primeCoreEulerChar (N : ℕ) : ℤ := ∑ S∈primeCoreNerve N, (-1)^S.card

private theorem nerve_face_of_upperPrime {N p : ℕ} {S : Finset ℕ}
    (hS : S∈squarefreeNerve N) (hpS : p∈S) (hlate : N<2*p) : S={p} := by
  have hs := mem_squarefreeNerve.mp hS
  apply subset_antisymm
  · intro q hq
    apply mem_singleton.mpr
    by_contra hqp
    have hpq : p≠q := Ne.symm hqp
    have hsub : {p,q}⊆S := by simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨hpS,hq⟩
    have hm : p*q≤∏ i∈S,i := by
      have h := prod_le_prod_of_subset_of_one_le' (f := fun i : ℕ => i) hsub
        (fun i hi _ => (hs.1 i hi).one_lt.le)
      rw [prod_insert (show p∉({q}:Finset ℕ) by simpa using hpq),prod_singleton] at h
      exact h
    have htwo := Nat.mul_le_mul_left p (hs.1 q hq).two_le
    omega
  · exact singleton_subset_iff.mpr hpS

/-- Every removed face is precisely one isolated prime vertex. -/
theorem squarefreeNerve_core_partition (N : ℕ) :
    squarefreeNerve N = primeCoreNerve N ∪ (primesInIoc (N/2) N).image (fun p : ℕ => ({p} : Finset ℕ)) := by
  ext S
  constructor
  · intro hS
    by_cases hc : ∀p∈S,2*p≤N
    · exact mem_union_left _ (mem_filter.mpr ⟨hS,hc⟩)
    · simp only [not_forall] at hc
      obtain ⟨p,hpS,hlarge⟩ := hc
      have hlate : N<2*p := Nat.lt_of_not_ge hlarge
      have hs := mem_squarefreeNerve.mp hS
      have hpN : p≤N := (Nat.le_of_dvd (prod_pos (fun q hq => (hs.1 q hq).pos))
        (dvd_prod_of_mem (fun q : ℕ => q) hpS)).trans hs.2
      apply mem_union_right
      exact mem_image.mpr ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,hpN⟩,hs.1 p hpS⟩,
        (nerve_face_of_upperPrime hS hpS hlate).symm⟩
  · intro hS
    rcases mem_union.mp hS with hc|himage
    · exact (mem_filter.mp hc).1
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp himage
      obtain ⟨hprime,_hlo,hhi⟩ := mem_primesInIoc hp
      exact mem_squarefreeNerve.mpr ⟨by simpa using hprime,by simpa using hhi⟩

theorem primeCoreNerve_disjoint_upperPrimes (N : ℕ) :
    Disjoint (primeCoreNerve N) ((primesInIoc (N/2) N).image (fun p : ℕ => ({p} : Finset ℕ))) := by
  apply disjoint_left.mpr
  intro S hcore hlate
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hlate
  have hsmall := (mem_filter.mp hcore).2 p (mem_singleton_self p)
  have hlarge := (mem_primesInIoc hp).2.1
  omega

/-- Removing isolated vertices adds their cardinality to the signed augmented face count. -/
theorem primeCoreEulerChar_eq (N : ℕ) :
    primeCoreEulerChar N=nerveEulerChar N+(primesInIoc (N/2) N).card := by
  have he : nerveEulerChar N=primeCoreEulerChar N-(primesInIoc (N/2) N).card := by
    rw [nerveEulerChar,squarefreeNerve_core_partition,
      sum_union (primeCoreNerve_disjoint_upperPrimes N)]
    change primeCoreEulerChar N +
      (∑ S∈(primesInIoc (N/2) N).image (fun p : ℕ => ({p} : Finset ℕ)),(-1:ℤ)^S.card)=_
    rw [sum_image (s := primesInIoc (N/2) N) (g := fun p : ℕ => ({p} : Finset ℕ))
      (f := fun S : Finset ℕ => (-1:ℤ)^S.card)
      (by intro p _hp q _hq he; exact singleton_injective he)]
    simp only [card_singleton,pow_one,sum_const,nsmul_eq_mul,mul_neg,mul_one]
    ring
  linarith only [he]

/-- The core's reduced Euler characteristic retains the negative of the prime component mass. -/
theorem primeCore_reducedEulerChar (N : ℕ) :
    -primeCoreEulerChar N = -(∑ n∈Icc 1 N,ArithmeticFunction.moebius n)-
      (primesInIoc (N/2) N).card := by
  rw [primeCoreEulerChar_eq,nerveEulerChar_eq_mertens]
  ring

/-- Finite-ambient faces of the actual connected core. -/
def primeCoreFaces (B N : ℕ) : Finset (Finset (Fin (B+3))) :=
  (primeHeightFaces B N).filter (fun S => ∀p∈S,2*p.val≤N)

/-- The core nerve and its barycentric face model have the same arithmetic faces. -/
theorem primeCoreFaces_map_iff {B N : ℕ} (S : Finset (Fin (B+3))) :
    S∈primeCoreFaces B N ↔ S.map Fin.valEmbedding ∈ primeCoreNerve N := by
  simp only [primeCoreFaces,primeCoreNerve,mem_filter,mem_primeHeightFaces,
    mem_squarefreeNerve,forall_mem_map,Fin.valEmbedding_apply,prod_map]

/-- The coordinate core is exactly the realization of the core's prime faces. -/
theorem inPrimeCore_iff_mem_coreFaces {B N : ℕ} (x : PrimeHeightSpace B N) :
    InPrimeCore x ↔ x.val∈faceFamilySpace (primeCoreFaces B N) := by
  constructor
  · intro hc
    obtain ⟨S,hS,hxS⟩ := mem_faceFamilySpace.mp x.property
    refine mem_faceFamilySpace.mpr ⟨S,mem_filter.mpr ⟨hS,?_⟩,hxS⟩
    intro p hpS
    by_contra hlarge
    have hlate : N<2*p.val := Nat.lt_of_not_ge hlarge
    have hsingle := upperPrime_face_singleton hlate hS hpS
    have hz : ∀q, x.val.val q=0 := by
      intro q
      by_cases hqp : q=p
      · subst q
        exact hc p hlate
      · exact hxS q (by rw [hsingle]; simpa only [mem_singleton] using hqp)
    have hsum := x.val.property.2
    simp only [hz,sum_const_zero] at hsum
    exact zero_ne_one hsum
  · intro hc p hlate
    obtain ⟨S,hS,hxS⟩ := mem_faceFamilySpace.mp hc
    apply hxS p
    intro hpS
    have hsmall := (mem_filter.mp hS).2 p hpS
    omega

#print axioms primeCoreEulerChar_eq
#print axioms primeCore_reducedEulerChar
#print axioms inPrimeCore_iff_mem_coreFaces

/-- The vertex two lies in the core at every height at least four. -/
theorem primeTwo_mem_core {B N : ℕ} (hN : 4≤N) :
    InPrimeCore (primeVertex (twoVertex B) Nat.prime_two (by change 2≤N; omega)) := by
  intro p hp
  have hne : p≠twoVertex B := by
    intro he
    subst p
    change N<2*2 at hp
    omega
  change (Pi.single (twoVertex B) (1:ℝ) : Fin (B+3) → ℝ) p=0
  rw [Pi.single_eq_of_ne hne]

/-- The coordinate core is the entire path component of prime two. -/
theorem primeCore_eq_pathComponent {B N : ℕ} (hN : 4≤N) :
    {x : PrimeHeightSpace B N | InPrimeCore x} =
      pathComponent (primeVertex (twoVertex B) Nat.prime_two (by change 2≤N; omega)) := by
  ext x
  change InPrimeCore x ↔ Joined _ x
  rw [primeHeight_joined_iff hN]
  constructor
  · intro hx
    exact Or.inl ⟨primeTwo_mem_core hN,hx⟩
  · rintro (⟨_,hx⟩|hx)
    · exact hx
    · rw [← hx]
      exact primeTwo_mem_core hN

/-- The core is path connected with its own subspace topology. -/
theorem primeCore_isPathConnected {B N : ℕ} (hN : 4≤N) :
    IsPathConnected {x : PrimeHeightSpace B N | InPrimeCore x} := by
  rw [primeCore_eq_pathComponent hN]
  exact isPathConnected_pathComponent

#print axioms primeCore_isPathConnected

/-- A self-map homotopic to the identity preserves the connected core. -/
theorem homotopy_preserves_primeCore {B N : ℕ} (hN : 4≤N)
    (f : ContinuousMap (PrimeHeightSpace B N) (PrimeHeightSpace B N))
    (H : (ContinuousMap.id _).Homotopy f) {x : PrimeHeightSpace B N}
    (hx : InPrimeCore x) : InPrimeCore (f x) := by
  have hj : Joined x (f x) := ⟨H.evalAt x⟩
  rcases (primeHeight_joined_iff hN x (f x)).mp hj with h|h
  · exact h.2
  · rw [← h]
    exact hx

#print axioms homotopy_preserves_primeCore

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
