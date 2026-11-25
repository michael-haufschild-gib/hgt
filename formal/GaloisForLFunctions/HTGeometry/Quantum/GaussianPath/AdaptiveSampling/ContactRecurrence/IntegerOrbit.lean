import Mathlib

/-! # Bounded gaps on an integer orbit through a one-sided contact -/

open Filter Set Metric Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
noncomputable section
variable {G : Type*} [NormedAddCommGroup G] [CompactSpace G]

/-- Every neighbourhood of an integer orbit point is visited in
boundedly many ticks after every starting index, including negative ones. -/
theorem orbit_neighbourhood (f : ℤ →+ G) (k : ℤ) {A : Set G} (hA : A∈𝓝 (f k)) :
    ∃ B : ℕ, ∀ n : ℤ, ∃ j ∈ Icc n (n+B), f j∈A := by
  classical
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hA
  have ht : TotallyBounded (range f) := isCompact_univ.totallyBounded.subset (subset_univ _)
  obtain ⟨S,hS,hf,hcover⟩ := Metric.finite_approx_of_totallyBounded ht ε hε
  letI : Fintype S := hf.fintype
  choose t htime using fun p : S => hS p.property
  let B := ∑ p : S, (t p).natAbs
  have hbound (p : S) : -(B:ℤ)≤t p ∧ t p≤(B:ℤ) := by
    have h : (t p).natAbs≤B := Finset.single_le_sum (fun i _ => Nat.zero_le (t i).natAbs)
      (Finset.mem_univ p)
    apply abs_le.mp
    rw [←Int.natCast_natAbs]
    exact_mod_cast h
  refine ⟨2*B,fun n => ?_⟩
  obtain ⟨p,hp,hd⟩ := mem_iUnion₂.mp (hcover (mem_range_self (n+B-k)))
  let s : S := ⟨p,hp⟩
  have hb := hbound s
  refine ⟨n+B-t s,⟨by omega,by push_cast; omega⟩,hball ?_⟩
  rw [mem_ball,dist_eq_norm]
  rw [mem_ball,dist_eq_norm] at hd
  have hts : f (t s)=p := htime s
  rw [←hts] at hd
  have he : f (n+B-t s)-f k=f (n+B-k)-f (t s) := by
    rw [←map_sub,←map_sub]
    congr 1
    abel
  rwa [he]

/-- If a closed target admits at least one of each pair of opposite
small displacements, every integer orbit through the contact hits it
with bounded gaps. This includes orbits lying in the boundary. -/
theorem opposite_contact (f : ℤ →+ G) {A : Set G} (hc : IsClosed A)
    (h : ∀ᶠ x in 𝓝 (0:G), x∈A ∨ -x∈A) :
    ∃ B : ℕ, ∀ n : ℤ, ∃ j ∈ Icc n (n+B), f j∈A := by
  obtain ⟨U,hU,hu,h0⟩ := _root_.mem_nhds_iff.mp h
  by_cases hall : ∀ j : ℤ, f j∈U → f j∈A
  · obtain ⟨B,hB⟩ := orbit_neighbourhood f 0 (by simpa using hu.mem_nhds h0)
    exact ⟨B,fun n => (hB n).imp fun j hj => ⟨hj.1,hall j hj.2⟩⟩
  push Not at hall
  obtain ⟨i,hi,hout⟩ := hall
  let V := (fun z : G => -z) ⁻¹' (U ∩ Aᶜ)
  have hv : IsOpen V := (hu.inter hc.isOpen_compl).preimage continuous_neg
  have hin : f (-i)∈V := by
    change -f (-i)∈U ∩ Aᶜ
    rw [map_neg,neg_neg]
    exact ⟨hi,hout⟩
  obtain ⟨B,hB⟩ := orbit_neighbourhood f (-i) (hv.mem_nhds hin)
  refine ⟨B,fun n => ?_⟩
  obtain ⟨j,hj,hv'⟩ := hB n
  have hs : -f j∈U ∧ -f j∉A := hv'
  have hh := (hU hs.1).resolve_left hs.2
  exact ⟨j,hj,by simpa only [neg_neg] using hh⟩

#print axioms opposite_contact
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
