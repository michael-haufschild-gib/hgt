import GaloisForLFunctions.HTGeometry.MilnorBassTateResidue
import GaloisForLFunctions.HTGeometry.MilnorSymbolPermutation
import GaloisForLFunctions.HTGeometry.MilnorKGradedRing
import GaloisForLFunctions.HTGeometry.MilnorKRationalEntries
import GaloisForLFunctions.HTGeometry.MilnorLiftUniqueness

/-!
# Bass and Tate's degree drop

If the Milnor `K`-theory of a field is torsion from degree `n₀` on, then the Milnor `K`-theory of a
simple extension of degree `d` is torsion from degree `n₀ + d − 1` on.

Bass and Tate's generators of `K_m^M(F[X]/π)` have all their non-constant entries of pairwise
distinct degrees below `d`, so at most `d − 1` of the `m` entries are non-constant; the remaining
ones are constants, and the corresponding sub-symbol comes from `K_{m-d+1}^M(F)`, which is torsion.

* `polyConstHom` : the constants, as a ring map into the residue field.
* `milnorKDeg_torsion_of_bassTate` : **the degree drop.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDedekindDomain

variable {F : Type*} [Field F]

/-- The constants, as a ring map into the residue field at `π`. -/
noncomputable def polyConstHom {π : Polynomial F} (hπ : Irreducible π) :
    F →+* polyResidueField hπ :=
  ((residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ)).symm : _ →+* _).comp
    ((Ideal.Quotient.mk (polyPlace hπ).asIdeal).comp (Polynomial.C : F →+* Polynomial F))

/-- The constant term of an entry, as a unit when it is nonzero. -/
noncomputable def constUnit (p : NZPoly F) : Fˣ :=
  open Classical in
  if h : p.1.coeff 0 = 0 then 1 else Units.mk0 (p.1.coeff 0) h

theorem constUnit_val {p : NZPoly F} (h : p.1.natDegree = 0) :
    ((constUnit p : Fˣ) : F) = p.1.coeff 0 := by
  have hne : p.1.coeff 0 ≠ 0 := by
    intro hcon
    exact p.2 (by rw [Polynomial.eq_C_of_natDegree_eq_zero h, hcon, map_zero])
  classical
  rw [constUnit, dif_neg hne]
  rfl

/-- **The residue of a constant entry is the image of that constant.** -/
theorem resEntry_const {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree)
    {p : NZPoly F} (h : p.1.natDegree = 0) :
    resEntry hπ p = Units.map (polyConstHom hπ : F →* polyResidueField hπ) (constUnit p) := by
  refine Units.ext ?_
  have hpm : p.1 ∉ Ideal.span {π} :=
    notMem_span_of_natDegree_lt p.2 (by omega)
  have hval := residueFieldEquiv_polyUnit hπ p.2 hpm
  have hC : Polynomial.C (p.1.coeff 0) = p.1 :=
    (Polynomial.eq_C_of_natDegree_eq_zero h).symm
  show ((resEntry hπ p : (polyResidueField hπ)ˣ) : polyResidueField hπ)
    = polyConstHom hπ ((constUnit p : Fˣ) : F)
  rw [constUnit_val h]
  have hgoal : (residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ))
      ((resEntry hπ p : (polyResidueField hπ)ˣ) : polyResidueField hπ)
      = (residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ)) (polyConstHom hπ (p.1.coeff 0)) := by
    rw [show (resEntry hπ p : (polyResidueField hπ)ˣ)
        = (polyResidueData hπ).residueUnit (polyUnit p.2) from rfl, hval]
    show _ = (residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ))
      ((residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ)).symm
        (Ideal.Quotient.mk (polyPlace hπ).asIdeal (Polynomial.C (p.1.coeff 0))))
    rw [RingEquiv.apply_symm_apply, hC]
  exact (residueFieldAtPlaceEquiv (RatFunc F) (polyPlace hπ)).injective hgoal

/-- **At most `d − 1` entries can have pairwise distinct positive degrees below `d`.** -/
theorem length_le_of_distinctDegrees {d : ℕ} {u : List (NZPoly F)}
    (hdist : DistinctDegrees u) (hpos : ∀ r ∈ u, r.1.natDegree ≠ 0)
    (hlt : ∀ r ∈ u, r.1.natDegree < d) : u.length ≤ d - 1 := by
  classical
  have hnodup : (u.map (fun r => r.1.natDegree)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hdist
    intro a b ha hb hab
    rcases hab with h0 | h0 | h0
    · exact absurd h0 (hpos a ha)
    · exact absurd h0 (hpos b hb)
    · exact h0
  have hsub : (u.map (fun r => r.1.natDegree)).toFinset ⊆ Finset.Icc 1 (d - 1) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    refine Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (hpos r hr), ?_⟩
    have := hlt r hr
    omega
  calc u.length = (u.map (fun r => r.1.natDegree)).length := (List.length_map _).symm
    _ = (u.map (fun r => r.1.natDegree)).toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (Finset.Icc 1 (d - 1)).card := Finset.card_le_card hsub
    _ = d - 1 := by rw [Nat.card_Icc]; omega

/-- An additive map sends torsion to torsion. -/
theorem addMonoidHom_mem_torsion {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    {x : A} (hx : x ∈ torsionAddSubgroup A) : f x ∈ torsionAddSubgroup B := by
  obtain ⟨N, hN, hNx⟩ := hx
  exact ⟨N, hN, by rw [← map_zsmul, hNx, map_zero]⟩

/-- **Bass and Tate's degree drop.**  If the Milnor `K`-theory of `F` is torsion from degree `n₀`
on, then that of a simple extension of degree `d` is torsion from degree `n₀ + d − 1` on. -/
theorem milnorKDeg_torsion_of_bassTate {π : Polynomial F} (hπ : Irreducible π) (hmπ : π.Monic)
    (hd : 1 ≤ π.natDegree) {n₀ : ℕ}
    (hF : ∀ j, n₀ ≤ j → ∀ x : MilnorKDeg F j, x ∈ torsionAddSubgroup (MilnorKDeg F j))
    (m : ℕ) (hm : n₀ + (π.natDegree - 1) ≤ m) (y : MilnorKDeg (polyResidueField hπ) m) :
    y ∈ torsionAddSubgroup (MilnorKDeg (polyResidueField hπ) m) := by
  classical
  refine (AddSubgroup.closure_le _).2 ?_ (mem_bassTateSpan hπ hmπ hd m y)
  rintro z ⟨ps, hlen, hgood, hdeg, hdist, rfl⟩
  set P : NZPoly F → Bool := fun r => decide (r.1.natDegree ≠ 0) with hP
  set u : List (NZPoly F) := ps.filter P with hu
  set v : List (NZPoly F) := ps.filter (fun r => !P r) with hv
  have hperm : (u ++ v).Perm ps := List.filter_append_perm P ps
  have hu_pos : ∀ r ∈ u, r.1.natDegree ≠ 0 := by
    intro r hr
    have := (List.mem_filter.1 hr).2
    simpa [hP] using this
  have hv_zero : ∀ r ∈ v, r.1.natDegree = 0 := by
    intro r hr
    have := (List.mem_filter.1 hr).2
    simpa [hP] using this
  have hu_mem : ∀ r ∈ u, r ∈ ps := fun r hr => (List.mem_filter.1 hr).1
  have hv_mem : ∀ r ∈ v, r ∈ ps := fun r hr => (List.mem_filter.1 hr).1
  have hu_dist : DistinctDegrees u := hdist.sublist List.filter_sublist
  have hu_lt : ∀ r ∈ u, r.1.natDegree < π.natDegree := fun r hr => hdeg r (hu_mem r hr)
  have hulen : u.length ≤ π.natDegree - 1 := length_le_of_distinctDegrees hu_dist hu_pos hu_lt
  have hpslen : ps.length = m := by rw [← hlen, List.length_map]
  have hsum : u.length + v.length = m := by
    rw [← hpslen, ← hperm.length_eq, List.length_append]
  have hvlen : n₀ ≤ v.length := by omega
  -- reorder the entries so that the constants come last
  have hlen' : ((u ++ v).map (resEntry hπ)).length = m := by
    rw [List.length_map, List.length_append, hsum]
  obtain ⟨ε, hε⟩ := milnorClassDeg_perm
    (List.Perm.map (resEntry hπ) hperm.symm) [] (by simpa using hlen) (by simpa using hlen')
  have hcastL : milnorClassDeg (polyResidueField hπ) m ⟨[] ++ ps.map (resEntry hπ), by simpa using hlen⟩
      = milnorClassDeg (polyResidueField hπ) m ⟨ps.map (resEntry hπ), hlen⟩ :=
    congrArg (milnorClassDeg (polyResidueField hπ) m) (Subtype.ext (by simp))
  have hcastR : milnorClassDeg (polyResidueField hπ) m
        ⟨[] ++ (u ++ v).map (resEntry hπ), by simpa using hlen'⟩
      = milnorClassDeg (polyResidueField hπ) m ⟨(u ++ v).map (resEntry hπ), hlen'⟩ :=
    congrArg (milnorClassDeg (polyResidueField hπ) m) (Subtype.ext (by simp))
  rw [hcastL, hcastR] at hε
  rw [SetLike.mem_coe, hε]
  refine AddSubgroup.zsmul_mem _ ?_ _
  clear hε hcastL hcastR
  -- rewrite the index
  obtain rfl : m = u.length + v.length := hsum.symm
  have hlenU : (u.map (resEntry hπ)).length = u.length := List.length_map _
  have hlenV : (v.map (resEntry hπ)).length = v.length := List.length_map _
  have hmul : milnorClassDeg (polyResidueField hπ) (u.length + v.length)
        ⟨(u ++ v).map (resEntry hπ), hlen'⟩
      = milnorMul (polyResidueField hπ) u.length v.length
        (milnorClassDeg (polyResidueField hπ) u.length ⟨u.map (resEntry hπ), hlenU⟩)
        (milnorClassDeg (polyResidueField hπ) v.length ⟨v.map (resEntry hπ), hlenV⟩) := by
    rw [milnorMul_class]
    exact congrArg (milnorClassDeg (polyResidueField hπ) (u.length + v.length))
      (Subtype.ext (by simp))
  rw [hmul]
  -- the constant part comes from the base field
  have hconstLen : (v.map constUnit).length = v.length := List.length_map _
  have hmapEq : v.map (resEntry hπ)
      = (v.map constUnit).map (milnorUnitMap (polyConstHom hπ)) := by
    rw [List.map_map]
    refine List.map_congr_left fun r hr => ?_
    exact resEntry_const hπ hd (hv_zero r hr)
  have hlenV' : ((v.map constUnit).map (milnorUnitMap (polyConstHom hπ))).length = v.length := by
    rw [← hmapEq]; exact hlenV
  have hbase : milnorClassDeg (polyResidueField hπ) v.length ⟨v.map (resEntry hπ), hlenV⟩
      = milnorKDegMap (polyConstHom hπ) v.length
        (milnorClassDeg F v.length ⟨v.map constUnit, hconstLen⟩) := by
    rw [milnorKDegMap_class]
    exact congrArg (milnorClassDeg (polyResidueField hπ) v.length) (Subtype.ext hmapEq)
  rw [hbase]
  refine addMonoidHom_mem_torsion _ (milnorKDegMap_mem_torsion _ v.length ?_)
  exact hF v.length hvlen _

end GaloisForLFunctions.HTGeometry
