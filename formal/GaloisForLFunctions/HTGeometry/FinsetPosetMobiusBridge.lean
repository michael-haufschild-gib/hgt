import GaloisForLFunctions.HTGeometry.SpectralClusterTransfer

/-!
# Equality of Boolean Möbius conventions

The explicit inclusion--exclusion response and the incidence-algebra Möbius
probe are the same linear functional on every finite Boolean lattice.  This
bridge lets exact local spectral cancellation feed directly into the existing
Steiner reconstruction and capacity theorems.
-/

open scoped BigOperators
open IncidenceAlgebra

namespace GaloisForLFunctions.HTGeometry

/-- Explicit inclusion--exclusion is biorthogonal to the Boolean zeta basis. -/
theorem finsetMobiusResponse_booleanZetaFeature
    {E R : Type*} [Fintype E] [DecidableEq E] [CommRing R]
    (packet feature : Finset E) :
    finsetMobiusResponse packet (booleanZetaFeature (R := R) feature) =
      if feature = packet then 1 else 0 := by
  by_cases hsub : feature ⊆ packet
  · by_cases heq : feature = packet
    · subst feature
      rw [if_pos rfl]
      unfold finsetMobiusResponse booleanZetaFeature
      simp only [zeta_apply]
      rw [Finset.sum_eq_single ∅]
      · simp
      · intro d hd hne
        simp only [Finset.mem_powerset] at hd
        have hnsub : ¬packet ⊆ packet \ d := by
          intro hs
          have hdempty : d = ∅ := by
            ext e
            simp only [Finset.notMem_empty, iff_false]
            intro he
            have hep := hs (hd he)
            exact (Finset.mem_sdiff.mp hep).2 he
          exact hne hdempty
        simp [hnsub]
      · simp
    · rw [if_neg heq]
      obtain ⟨e, hepacket, hefeature⟩ := Finset.not_subset.mp
        (fun hp => heq (Finset.Subset.antisymm hsub hp))
      apply finsetMobiusResponse_eq_zero_of_insert_invariant hepacket
      intro active
      unfold booleanZetaFeature
      simp only [zeta_apply]
      congr 1
      apply propext
      constructor
      · intro hs x hx
        have hxi := hs hx
        rcases Finset.mem_insert.mp hxi with hxe | hxa
        · exact False.elim (hefeature (hxe ▸ hx))
        · exact hxa
      · exact fun hs => hs.trans (Finset.subset_insert e active)
  · have hne : feature ≠ packet :=
      fun heq => hsub (heq ▸ Finset.Subset.rfl)
    rw [if_neg hne]
    have hzero : ∀ active ⊆ packet,
        booleanZetaFeature (R := R) feature active = 0 := by
      intro active ha
      have hn : ¬feature ⊆ active := fun hs => hsub (hs.trans ha)
      simp [booleanZetaFeature, zeta_apply, hn]
    unfold finsetMobiusResponse
    apply Finset.sum_eq_zero
    intro d hd
    rw [hzero (packet \ d) Finset.sdiff_subset]
    simp

/-- Explicit Boolean inclusion--exclusion as a linear functional. -/
noncomputable def finsetMobiusResponseLinear
    {E R : Type*} [DecidableEq E] [CommRing R]
    (packet : Finset E) : (Finset E → R) →ₗ[R] R where
  toFun := finsetMobiusResponse packet
  map_add' f g := finsetMobiusResponse_add packet f g
  map_smul' c f := by
    unfold finsetMobiusResponse
    simp [Finset.mul_sum, mul_left_comm]

@[simp]
theorem finsetMobiusResponseLinear_apply
    {E R : Type*} [DecidableEq E] [CommRing R]
    (packet : Finset E) (response : Finset E → R) :
    finsetMobiusResponseLinear packet response =
      finsetMobiusResponse packet response := rfl

/-- **Möbius-observer identity.**  On every finite Boolean lattice, explicit
inclusion--exclusion and incidence-algebra Möbius probing agree on every
response over every coefficient field. -/
theorem finsetMobiusResponse_eq_posetMobiusProbe
    {E R : Type*} [Fintype E] [DecidableEq E] [Field R]
    (packet : Finset E) (response : Finset E → R) :
    finsetMobiusResponse packet response =
      posetMobiusProbe packet response := by
  let b := booleanZetaBasis (V := E) (R := R)
  have hmaps : finsetMobiusResponseLinear (R := R) packet =
      posetMobiusProbeLinear (R := R) packet := by
    apply LinearMap.ext_on (Module.Basis.span_eq b)
    intro f hf
    obtain ⟨feature, rfl⟩ := hf
    simp only [finsetMobiusResponseLinear_apply,
      posetMobiusProbeLinear_apply]
    rw [show b feature = booleanZetaFeature (R := R) feature by
      exact booleanZetaBasis_apply feature]
    rw [finsetMobiusResponse_booleanZetaFeature]
    change (if feature = packet then 1 else 0) =
      booleanMobiusProbe packet (booleanZetaFeature feature)
    rw [booleanMobiusProbe_booleanZetaFeature]
  exact congrArg (fun m => m response) hmaps

/-- Boolean Möbius response is invariant under arbitrary relabelling of the
finite coordinate universe. -/
theorem finsetMobiusResponse_equiv
    {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R]
    (e : α ≃ β) (packet : Finset α) (response : Finset α → R) :
    finsetMobiusResponse (e.finsetCongr packet)
        (fun active => response (e.symm.finsetCongr active)) =
      finsetMobiusResponse packet response := by
  unfold finsetMobiusResponse
  symm
  apply Finset.sum_bij (fun d _ => e.finsetCongr d)
  · intro d hd
    simp only [Finset.mem_powerset] at hd ⊢
    simpa only [Equiv.finsetCongr_apply] using
      (Finset.map_subset_map.mpr hd)
  · intro d₁ hd₁ d₂ hd₂ heq
    exact e.finsetCongr.injective heq
  · intro d hd
    let a := e.symm.finsetCongr d
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_powerset] at hd ⊢
      intro x hx
      have hxe : e x ∈ d := by
        simpa [a] using hx
      have hxmap := hd hxe
      simpa using hxmap
    · exact e.finsetCongr.apply_symm_apply d
  · intro d hd
    rw [Equiv.finsetCongr_apply, Finset.card_map]
    congr 1
    apply congrArg response
    ext x
    simp

/-- Möbius response on a packet equals the response on the full finite subtype
of that packet after forgetting subtype labels. -/
theorem finsetMobiusResponse_subtype_univ
    {E R : Type*} [Fintype E] [DecidableEq E] [CommRing R]
    (packet : Finset E) (response : Finset E → R) :
    finsetMobiusResponse
        (Finset.univ : Finset {e : E // e ∈ packet})
        (fun active =>
          response (active.map (Function.Embedding.subtype _))) =
      finsetMobiusResponse packet response := by
  unfold finsetMobiusResponse
  symm
  apply Finset.sum_bij
    (fun d _ => d.subtype (fun e => e ∈ packet))
  · intro d hd
    simp only [Finset.mem_powerset] at hd ⊢
    intro e he
    exact Finset.mem_univ e
  · intro d₁ hd₁ d₂ hd₂ heq
    simp only [Finset.mem_powerset] at hd₁ hd₂
    have hmap₁ := Finset.subtype_map_of_mem
      (p := fun e => e ∈ packet) (s := d₁)
      (fun e he => hd₁ he)
    have hmap₂ := Finset.subtype_map_of_mem
      (p := fun e => e ∈ packet) (s := d₂)
      (fun e he => hd₂ he)
    rw [← hmap₁, ← hmap₂, heq]
  · intro d hd
    let a :=
      d.map (Function.Embedding.subtype fun e : E => e ∈ packet)
    refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_powerset]
      intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
      exact x.2
    · ext x
      simp [a]
  · intro d hd
    simp only [Finset.mem_powerset] at hd
    have hcard :
        (d.subtype (fun e => e ∈ packet)).card = d.card := by
      have hmap := Finset.subtype_map_of_mem
        (p := fun e => e ∈ packet) (s := d)
        (fun e he => hd he)
      calc
        (d.subtype (fun e => e ∈ packet)).card =
            ((d.subtype (fun e => e ∈ packet)).map
              (Function.Embedding.subtype _)).card := by
                rw [Finset.card_map]
        _ = d.card := congrArg Finset.card hmap
    rw [hcard]
    congr 1
    apply congrArg response
    ext e
    simp [and_comm]

/-- **Exact Boolean Möbius reconstruction.**  Every response at full
activation is the sum of its irreducible packet responses. -/
theorem sum_finsetMobiusResponse_eq_full
    {E R : Type*} [Fintype E] [DecidableEq E] [Field R]
    (response : Finset E → R) :
    ∑ packet : Finset E, finsetMobiusResponse packet response =
      response Finset.univ := by
  have hexpand :=
    (booleanZetaBasis (V := E) (R := R)).sum_repr response
  have hvalue :=
    congrFun hexpand (Finset.univ : Finset E)
  simp only [Finset.sum_apply, Pi.smul_apply] at hvalue
  rw [← hvalue]
  apply Finset.sum_congr rfl
  intro packet hpacket
  rw [finsetMobiusResponse_eq_posetMobiusProbe]
  rw [booleanZetaBasis_repr, booleanZetaBasis_apply]
  change booleanMobiusProbe packet response =
    booleanMobiusProbe packet response *
      booleanZetaFeature packet Finset.univ
  simp [booleanZetaFeature, zeta_apply]

end GaloisForLFunctions.HTGeometry
