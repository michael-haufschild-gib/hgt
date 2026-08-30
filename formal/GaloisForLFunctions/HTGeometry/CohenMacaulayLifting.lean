import GaloisForLFunctions.HTGeometry.CohenMacaulayDepth

/-!
# Concatenating regular sequences, and lifting Cohen–Macaulayness

A regular sequence followed by a sequence that is regular in the quotient is again regular: the
third isomorphism theorem identifies the intermediate quotients, so each nonzerodivisor condition
transports.  Consequently, if a regular sequence cuts the Krull dimension by exactly its length and
the quotient is Cohen–Macaulay, then so is the ring — the two maximal regular sequences concatenate
to one of full length.

This is the inductive backbone for every later Cohen–Macaulay computation.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {R : Type u} [CommRing R]

theorem ofList_append (l l' : List R) :
    Ideal.ofList (l ++ l') = Ideal.ofList l ⊔ Ideal.ofList l' := by
  have hset : {x : R | x ∈ l ++ l'} = {x : R | x ∈ l} ∪ {x : R | x ∈ l'} := by
    ext x; simp
  rw [Ideal.ofList, Ideal.ofList, Ideal.ofList, hset, Ideal.span_union]

/-- **Concatenation of regular sequences.**  A regular sequence followed by a sequence that is
regular in the quotient is regular. -/
theorem isRingRegularSeq_append {rs ss : List R} (hrs : IsRingRegularSeq rs)
    (hss : IsRingRegularSeq (ss.map (Ideal.Quotient.mk (Ideal.ofList rs)))) :
    IsRingRegularSeq (rs ++ ss) := by
  classical
  set I : Ideal R := Ideal.ofList rs with hI
  constructor
  · intro i hi
    rw [List.length_append] at hi
    by_cases hlt : i < rs.length
    · have htake : (rs ++ ss).take i = rs.take i := by
        rw [List.take_append_of_le_length (le_of_lt hlt)]
      have hidx : (rs ++ ss)[i] = rs[i] := by
        rw [List.getElem_append_left hlt]
      rw [htake, hidx]
      exact hrs.regular i hlt
    · push Not at hlt
      obtain ⟨k, rfl⟩ : ∃ k, i = rs.length + k := ⟨i - rs.length, by omega⟩
      have hk : k < ss.length := by omega
      have htake : (rs ++ ss).take (rs.length + k) = rs ++ ss.take k :=
        List.take_length_add_append k
      have hidx : (rs ++ ss)[rs.length + k] = ss[k] := by
        rw [List.getElem_append_right (by omega)]
        congr 1
        omega
      rw [htake, hidx, ofList_append, ← hI]
      set J : Ideal R := Ideal.ofList (ss.take k) with hJ
      have hreg := hss.regular k (by simpa using hk)
      rw [IsRegularOn, ← List.map_take, ofList_map, List.getElem_map] at hreg
      have helt := mem_nonZeroDivisors_of_ringEquiv
        (DoubleQuot.quotQuotEquivQuotSup I J) hreg
      have hval : (DoubleQuot.quotQuotEquivQuotSup I J)
            (Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk I) J)
              ((Ideal.Quotient.mk I) ss[k]))
          = Ideal.Quotient.mk (I ⊔ J) ss[k] :=
        DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I J ss[k]
      rw [hval] at helt
      exact helt
  · rw [ofList_append, ← hI]
    intro htop
    apply hss.proper
    rw [ofList_map]
    have hcong := congrArg (Ideal.map (Ideal.Quotient.mk I)) htop
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_top] at hcong
    exact hcong

/-- Every list in a quotient lifts. -/
theorem exists_list_map_mk (I : Ideal R) (l : List (R ⧸ I)) :
    ∃ l' : List R, l'.map (Ideal.Quotient.mk I) = l := by
  classical
  refine ⟨l.map (Function.surjInv Ideal.Quotient.mk_surjective), ?_⟩
  rw [List.map_map]
  have hid : (⇑(Ideal.Quotient.mk I)) ∘ (Function.surjInv Ideal.Quotient.mk_surjective) = id := by
    funext x
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective x
  rw [hid, List.map_id]

/-- **Cohen–Macaulayness lifts through a regular sequence.**  If a regular sequence cuts the Krull
dimension by its length and the quotient is Cohen–Macaulay, so is the ring. -/
theorem isCohenMacaulayRing_of_quotient {rs : List R} (hrs : IsRingRegularSeq rs)
    (hCM : IsCohenMacaulayRing (R ⧸ Ideal.ofList rs))
    (hdim : ringKrullDim (R ⧸ Ideal.ofList rs) + ((rs.length : ℕ∞) : WithBot ℕ∞)
      = ringKrullDim R) :
    IsCohenMacaulayRing R := by
  obtain ⟨ss, hss, hlen⟩ := hCM
  obtain ⟨ss', hss'⟩ := exists_list_map_mk (Ideal.ofList rs) ss
  refine ⟨rs ++ ss', isRingRegularSeq_append hrs (by rw [hss']; exact hss), ?_⟩
  rw [List.length_append]
  have hlen' : ss'.length = ss.length := by rw [← hss', List.length_map]
  rw [hlen']
  rw [← hdim, ← hlen]
  push_cast
  ring


end GaloisForLFunctions.HTGeometry
