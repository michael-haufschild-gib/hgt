import GaloisForLFunctions.EffectiveScalingGeometry.PrimeHeightFiltration
import Mathlib.Topology.Connected.Clopen

/-!
# Isolated-prime rigidity and the connected core

Upper-half primes are isolated points of the actual barycentric prime complex.
Every map homotopic to the identity fixes them individually. At heights at least
four, all remaining points form one path component, identified by vanishing upper-half
coordinates. This isolates the degree-zero obstruction to fixed-point localization.
-/

noncomputable section
open Finset ContinuousMap
open DifferentialGeometry.Simplex
open GaloisForLFunctions.HodgeTheoryWithoutVarieties
open GaloisForLFunctions.EffectiveScalingGeometry
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

private theorem singleton_support_eq_vertex {V : Type*} [Fintype V] [DecidableEq V]
    (p : V) (x : stdSimplex ℝ V) (hx : x ∈ supportFace {p}) :
    x = stdSimplex.vertex (S := ℝ) p := by
  have hs : (∑ i, x.val i) = x.val p := by
    apply sum_eq_single p
    · intro i _hi hip
      exact hx i (by simpa using hip)
    · intro hp
      exact (hp (mem_univ p)).elim
  have hp : x.val p = 1 := hs.symm.trans x.property.2
  apply Subtype.ext
  funext i
  by_cases hi : i=p
  · subst i
    simpa [stdSimplex.vertex] using hp
  · change x.val i = (Pi.single p (1:ℝ) : V → ℝ) i
    rw [Pi.single_eq_of_ne hi]
    exact hx i (by simpa only [mem_singleton] using hi)

/-- A prime in the upper half-window belongs to no larger face. -/
theorem upperPrime_face_singleton {B N : ℕ} {p : Fin (B+3)}
    (hlate : N < 2*p.val) {S : Finset (Fin (B+3))}
    (hS : S ∈ primeHeightFaces B N) (hpS : p ∈ S) : S={p} := by
  have hs := mem_primeHeightFaces.mp hS
  apply subset_antisymm
  · intro q hq
    apply mem_singleton.mpr
    by_contra hqp
    have hpq : p≠q := Ne.symm hqp
    have hsub : {p,q} ⊆ S := by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hpS,hq⟩
    have hmul : p.val*q.val ≤ ∏ i ∈ S, i.val := by
      have h := prod_le_prod_of_subset_of_one_le' hsub
        (fun i hi _ => (hs.1 i hi).one_lt.le)
      rw [prod_insert (show p ∉ ({q} : Finset (Fin (B+3))) by simpa using hpq),
        prod_singleton] at h
      exact h
    have htwo := Nat.mul_le_mul_left p.val (hs.1 q hq).two_le
    omega
  · exact singleton_subset_iff.mpr hpS

/-- The point with all barycentric mass at a prime label. -/
def primeVertex {B N : ℕ} (p : Fin (B+3)) (hp : p.val.Prime) (hN : p.val≤N) :
    PrimeHeightSpace B N :=
  ⟨stdSimplex.vertex (S := ℝ) p, mem_faceFamilySpace.mpr
    ⟨{p}, mem_primeHeightFaces.mpr ⟨by simpa using hp, by simpa using hN⟩,
      vertex_mem_supportFace (mem_singleton_self p)⟩⟩

theorem upperPrime_coordinate {B N : ℕ} (p : Fin (B+3)) (hlate : N < 2*p.val)
    (x : PrimeHeightSpace B N) : x.val.val p=0 ∨ x.val=stdSimplex.vertex (S := ℝ) p := by
  obtain ⟨S,hS,hx⟩ := mem_faceFamilySpace.mp x.property
  by_cases hp : p∈S
  · right
    rw [upperPrime_face_singleton hlate hS hp] at hx
    exact singleton_support_eq_vertex p x.val hx
  · exact Or.inl (hx p hp)

/-- An upper-half prime is an open-and-closed singleton in the actual realization. -/
theorem upperPrime_vertex_clopen {B N : ℕ} (p : Fin (B+3))
    (hp : p.val.Prime) (hN : p.val≤N) (hlate : N < 2*p.val) :
    IsClopen ({primeVertex p hp hN} : Set (PrimeHeightSpace B N)) := by
  refine ⟨isClosed_singleton, ?_⟩
  have heq : ({primeVertex p hp hN} : Set (PrimeHeightSpace B N)) =
      {x | (1/2:ℝ) < x.val.val p} := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      norm_num [primeVertex, stdSimplex.vertex]
    · intro hx
      rcases upperPrime_coordinate p hlate x with hz | hv
      · simp only [Set.mem_setOf_eq, hz] at hx
        norm_num at hx
      · exact Subtype.ext hv
  rw [heq]
  exact isOpen_lt continuous_const
    ((continuous_apply p).comp (continuous_subtype_val.comp continuous_subtype_val))

/-- Every path from an isolated prime vertex stays at that vertex. -/
theorem upperPrime_path_target {B N : ℕ} (p : Fin (B+3))
    (hp : p.val.Prime) (hN : p.val≤N) (hlate : N < 2*p.val)
    {x : PrimeHeightSpace B N} (γ : Path (primeVertex p hp hN) x) :
    x=primeVertex p hp hN := by
  have hc := (upperPrime_vertex_clopen p hp hN hlate).preimage γ.continuous
  have h0 : (0:unitInterval) ∈ γ ⁻¹' {primeVertex p hp hN} := by simp
  have hall := hc.eq_univ ⟨0,h0⟩
  have h1 : (1:unitInterval) ∈ γ ⁻¹' {primeVertex p hp hN} := by rw [hall]; trivial
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, Path.target] using h1

/-- A homotopy from the identity fixes every upper-half prime vertex. -/
theorem homotopy_fixes_upperPrime {B N : ℕ} (f : C(PrimeHeightSpace B N, PrimeHeightSpace B N))
    (H : (ContinuousMap.id _).Homotopy f) (p : Fin (B+3))
    (hp : p.val.Prime) (hN : p.val≤N) (hlate : N < 2*p.val) :
    f (primeVertex p hp hN)=primeVertex p hp hN :=
  upperPrime_path_target p hp hN hlate (H.evalAt (primeVertex p hp hN))

#print axioms homotopy_fixes_upperPrime

private theorem primeLabel_le_height {B N : ℕ} {S : Finset (Fin (B+3))}
    (hS : S ∈ primeHeightFaces B N) {p : Fin (B+3)} (hp : p ∈ S) : p.val ≤ N := by
  have hs := mem_primeHeightFaces.mp hS
  exact (Nat.le_of_dvd (prod_pos (fun q hq => (hs.1 q hq).pos))
    (dvd_prod_of_mem (fun q : Fin (B+3) => q.val) hp)).trans hs.2

/-- The straight segment from a point of a prime face to one of its vertices. -/
def primeFacePath {B N : ℕ} {S : Finset (Fin (B+3))}
    (hS : S ∈ primeHeightFaces B N) (p : Fin (B+3)) (hpS : p ∈ S)
    (x : PrimeHeightSpace B N) (hx : x.val ∈ supportFace S) :
    Path x (primeVertex p ((mem_primeHeightFaces.mp hS).1 p hpS)
      (primeLabel_le_height hS hpS)) where
  toFun t := ⟨vertexContraction p (t,x.val), mem_faceFamilySpace.mpr ⟨S,hS,by
    have h := vertexContraction_mem_insert_supportFace (a := p) t hx
    simpa only [insert_eq_of_mem hpS] using h⟩⟩
  continuous_toFun := ((vertexContraction p).continuous.comp
    (continuous_id.prodMk continuous_const)).subtype_mk _
  source' := Subtype.ext (vertexContraction_zero p x.val)
  target' := Subtype.ext (vertexContraction_one p x.val)

/-- The core has zero mass at every upper-half prime vertex. -/
def InPrimeCore {B N : ℕ} (x : PrimeHeightSpace B N) : Prop :=
  ∀ p : Fin (B+3), N < 2*p.val → x.val.val p=0

/-- Every point belongs to the core or is one of the isolated arithmetic vertices. -/
theorem primeCore_or_upperPrime {B N : ℕ} (x : PrimeHeightSpace B N) :
    InPrimeCore x ∨ ∃ (p : Fin (B+3)) (hp : p.val.Prime) (hN : p.val≤N),
      N < 2*p.val ∧ x=primeVertex p hp hN := by
  by_cases hc : InPrimeCore x
  · exact Or.inl hc
  · right
    simp only [InPrimeCore, not_forall] at hc
    obtain ⟨p,hlate,hne⟩ := hc
    have hv := (upperPrime_coordinate p hlate x).resolve_left hne
    obtain ⟨S,hS,hx⟩ := mem_faceFamilySpace.mp x.property
    have hpS : p∈S := by
      by_contra hpS
      exact hne (hx p hpS)
    exact ⟨p, (mem_primeHeightFaces.mp hS).1 p hpS,
      primeLabel_le_height hS hpS, hlate, Subtype.ext hv⟩

private theorem support_nonempty {V : Type*} [Fintype V] {S : Finset V}
    {x : stdSimplex ℝ V} (hx : x∈supportFace S) : S.Nonempty := by
  by_contra h
  have he : S=∅ := not_nonempty_iff_eq_empty.mp h
  have hz : ∀i, x.val i=0 := fun i => hx i (by simp [he])
  have hs := x.property.2
  simp only [hz,sum_const_zero] at hs
  exact zero_ne_one hs

/-- Every point of the core is joined to prime two; the paths need not form a contraction. -/
theorem primeCore_joined_two {B N : ℕ} (hN : 4≤N) (x : PrimeHeightSpace B N)
    (hxcore : InPrimeCore x) :
    Joined x (primeVertex (twoVertex B) Nat.prime_two (by change 2≤N; omega)) := by
  obtain ⟨S,hS,hxS⟩ := mem_faceFamilySpace.mp x.property
  obtain ⟨p,hpS⟩ := support_nonempty hxS
  have hp := (mem_primeHeightFaces.mp hS).1 p hpS
  have hpN := primeLabel_le_height hS hpS
  have hxp : Joined x (primeVertex p hp hpN) := ⟨primeFacePath hS p hpS x hxS⟩
  have hsmall : 2*p.val≤N := by
    by_contra hn
    have hlate : N < 2*p.val := Nat.lt_of_not_ge hn
    have he := upperPrime_face_singleton hlate hS hpS
    rw [he] at hxS
    have hv := singleton_support_eq_vertex p x.val hxS
    have hz := hxcore p hlate
    rw [hv] at hz
    simp at hz
  by_cases hp2 : p=twoVertex B
  · subst p
    exact hxp
  · have hedge : {p,twoVertex B}∈primeHeightFaces B N := by
      apply mem_primeHeightFaces.mpr
      constructor
      · intro q hq
        rcases mem_insert.mp hq with rfl|hq
        · exact hp
        · rw [mem_singleton] at hq
          subst q
          exact Nat.prime_two
      · rw [prod_insert (show p ∉ ({twoVertex B} : Finset (Fin (B+3))) by simpa using hp2),
          prod_singleton]
        change p.val*2≤N
        omega
    exact hxp.trans ⟨primeFacePath hedge (twoVertex B) (by simp)
      (primeVertex p hp hpN) (vertex_mem_supportFace (mem_insert_self _ _))⟩

/-- The connected core and the isolated primes are exactly the path components. -/
theorem primeHeight_joined_iff {B N : ℕ} (hN : 4≤N) (x y : PrimeHeightSpace B N) :
    Joined x y ↔ (InPrimeCore x ∧ InPrimeCore y) ∨ x=y := by
  constructor
  · intro h
    rcases primeCore_or_upperPrime x with hx|⟨p,hp,hpN,hlate,hx⟩
    · rcases primeCore_or_upperPrime y with hy|⟨p,hp,hpN,hlate,hy⟩
      · exact Or.inl ⟨hx,hy⟩
      · right
        rw [hy] at h
        obtain ⟨γ⟩ := h.symm
        exact (upperPrime_path_target p hp hpN hlate γ).trans hy.symm
    · right
      rw [hx] at h
      obtain ⟨γ⟩ := h
      exact hx.trans (upperPrime_path_target p hp hpN hlate γ).symm
  · rintro (⟨hx,hy⟩|rfl)
    · exact (primeCore_joined_two hN x hx).trans (primeCore_joined_two hN y hy).symm
    · exact Joined.refl x

/-- Upper-half primes in the finite ambient vertex set. -/
def upperPrimeVertices (B N : ℕ) : Finset (Fin (B+3)) :=
  univ.filter (fun p => p.val.Prime ∧ p.val≤N ∧ N<2*p.val)

/-- The actual fixed-point set contains a distinct point for every upper-half prime. -/
def upperPrimeFixedEmbedding {B N : ℕ}
    (f : C(PrimeHeightSpace B N, PrimeHeightSpace B N))
    (H : (ContinuousMap.id _).Homotopy f) :
    upperPrimeVertices B N ↪ {x : PrimeHeightSpace B N // f x=x} where
  toFun p := by
    have hp := (mem_filter.mp p.property).2
    exact ⟨primeVertex p.val hp.1 hp.2.1,
      homotopy_fixes_upperPrime f H p.val hp.1 hp.2.1 hp.2.2⟩
  inj' := by
    intro p q h
    have he : stdSimplex.vertex (S := ℝ) p.val = stdSimplex.vertex (S := ℝ) q.val :=
      congrArg (fun z : {x : PrimeHeightSpace B N // f x=x} => z.val.val) h
    exact Subtype.ext (stdSimplex.vertex_injective he)

/-- Every finite set containing all fixed points must contain all upper-half primes. -/
theorem upperPrime_card_le_fixedPoint_cover {B N : ℕ}
    (f : C(PrimeHeightSpace B N, PrimeHeightSpace B N))
    (H : (ContinuousMap.id _).Homotopy f) (A : Finset (PrimeHeightSpace B N))
    (hA : ∀ x, f x=x → x∈A) : (upperPrimeVertices B N).card≤A.card := by
  classical
  let e : upperPrimeVertices B N ↪ A :=
    { toFun := fun p => ⟨(upperPrimeFixedEmbedding f H p).val,
        hA _ (upperPrimeFixedEmbedding f H p).property⟩
      inj' := by
        intro p q h
        have hv : (upperPrimeFixedEmbedding f H p).val =
            (upperPrimeFixedEmbedding f H q).val :=
          congrArg (fun z : A => (z : PrimeHeightSpace B N)) h
        exact (upperPrimeFixedEmbedding f H).injective (Subtype.ext hv) }
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective e e.injective

#print axioms upperPrime_card_le_fixedPoint_cover
#print axioms primeHeight_joined_iff
#print axioms upperPrimeFixedEmbedding

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
