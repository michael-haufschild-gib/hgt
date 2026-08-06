import GaloisForLFunctions.HTGeometry.MultipleSineLadderStep

/-!
# Face coordinates: iterating the ladder step down the simplex

The ladder step deletes one direction and flips the sign.  Iterating it along a list of distinct
directions gives the face coordinate law

```text
x_J L_V = (-1)^{|J|} L_{V∖J}   modulo the differentially algebraic sector,
```

where `x_J` is the composite of the shift differences `x_j = σ_{ω_j} - 1` for `j ∈ J`.  The
induction consumes one direction at a time: the differentially algebraic sector is stable under the
translations, so the defect accumulated so far stays inside it, and the ladder step supplies the new
defect for the current direction.

The only constraint is that the deleted set never exhausts the frame: every intermediate frame keeps
at least one direction, which is exactly `|J| ≤ N - 1`.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The source of a nonempty set of directions -/

/-- The multiple-sine source of a nonempty finite set of directions, with the nonemptiness carried
as an argument rather than an instance. -/
def frameSourceMero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (S : Finset ι) (hS : S.Nonempty) :
    meroField (Set.univ : Set ℂ) :=
  haveI : Nonempty {i : ι // i ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  multipleSineSourceMero ω hω S

omit [Fintype ι] [DecidableEq ι] in
theorem frameSourceMero_eq (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (S : Finset ι) (hS : S.Nonempty)
    [Nonempty {i : ι // i ∈ S}] :
    frameSourceMero ω hω S hS = multipleSineSourceMero ω hω S := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The source depends only on the set of directions. -/
theorem frameSourceMero_congr (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {S T : Finset ι} (h : S = T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    frameSourceMero ω hω S hS = frameSourceMero ω hω T hT := by
  subst h; rfl

omit [Fintype ι] in
/-- **The ladder step in the nonemptiness-as-argument form.** -/
theorem differentialAlgebraicOver_frameSource_ladder_step (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (k : ι) (hk : k ∈ S) (hS : S.Nonempty) (hE : (S.erase k).Nonempty) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv (ω k) (frameSourceMero ω hω S hS) - frameSourceMero ω hω S hS
        + frameSourceMero ω hω (S.erase k) hE) := by
  haveI : Nonempty {i : ι // i ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  haveI : Nonempty {i : ι // i ∈ S.erase k} := ⟨⟨hE.choose, hE.choose_spec⟩⟩
  have h2 : 2 ≤ S.card := by
    have hcard : S.card = (S.erase k).card + 1 := by
      rw [Finset.card_erase_of_mem hk]
      have : 1 ≤ S.card := Finset.card_pos.2 ⟨k, hk⟩
      omega
    have hpos : 1 ≤ (S.erase k).card := Finset.card_pos.2 hE
    omega
  exact differentialAlgebraicOver_multipleSine_ladder_step ω hω S k hk h2

/-! ### The iterated shift difference -/

/-- The composite `x_{j_1} ⋯ x_{j_r}` of shift differences along a list of directions. -/
def listShiftDiff (ω : ι → ℂ) :
    List ι → meroField (Set.univ : Set ℂ) → meroField (Set.univ : Set ℂ)
  | [], x => x
  | j :: l, x =>
      addTranslationMeroEquiv (ω j) (listShiftDiff ω l x) - listShiftDiff ω l x

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem listShiftDiff_nil (ω : ι → ℂ) (x : meroField (Set.univ : Set ℂ)) :
    listShiftDiff ω [] x = x := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem listShiftDiff_cons (ω : ι → ℂ) (j : ι) (l : List ι)
    (x : meroField (Set.univ : Set ℂ)) :
    listShiftDiff ω (j :: l) x =
      addTranslationMeroEquiv (ω j) (listShiftDiff ω l x) - listShiftDiff ω l x := rfl

/-! ### The face coordinate law -/

omit [Fintype ι] in
/-- **Face coordinates.**  Applying the shift differences of a list of distinct directions of a
frame to the source of that frame gives, modulo the differentially algebraic sector, the source of
the frame with those directions deleted, times the parity of the list. -/
theorem differentialAlgebraicOver_frameSource_face (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (hS : S.Nonempty) :
    ∀ (l : List ι), l.Nodup → (∀ j ∈ l, j ∈ S) → ∀ hne : (S \ l.toFinset).Nonempty,
      DifferentialAlgebraicOver (RatFunc ℂ)
        (listShiftDiff ω l (frameSourceMero ω hω S hS)
          - (-1 : meroField (Set.univ : Set ℂ)) ^ l.length *
              frameSourceMero ω hω (S \ l.toFinset) hne) := by
  intro l
  induction l with
  | nil =>
      intro _ _ hne
      have hset : S \ (([] : List ι).toFinset) = S := by
        simp
      rw [listShiftDiff_nil, List.length_nil, pow_zero, one_mul,
        frameSourceMero_congr ω hω hset hne hS, sub_self]
      simpa using differentialAlgebraicOver_algebraMap
        (F := RatFunc ℂ) (E := meroField (Set.univ : Set ℂ)) 0
  | cons j l ih =>
      intro hnd hsub hne
      have hjS : j ∈ S := hsub j (List.mem_cons_self ..)
      have hjl : j ∉ l.toFinset := by
        simpa using (List.nodup_cons.mp hnd).1
      have hne' : (S \ l.toFinset).Nonempty :=
        ⟨j, Finset.mem_sdiff.mpr ⟨hjS, hjl⟩⟩
      have hjmem : j ∈ S \ l.toFinset := Finset.mem_sdiff.mpr ⟨hjS, hjl⟩
      have hset : S \ (j :: l).toFinset = (S \ l.toFinset).erase j := by
        rw [List.toFinset_cons, Finset.sdiff_insert]
      have hEr : ((S \ l.toFinset).erase j).Nonempty := by
        rw [← hset]; exact hne
      have hIH := ih (List.nodup_cons.mp hnd).2 (fun i hi => hsub i (List.mem_cons_of_mem _ hi)) hne'
      have hstep := differentialAlgebraicOver_frameSource_ladder_step ω hω
        (S \ l.toFinset) j hjmem hne' hEr
      rw [frameSourceMero_congr ω hω hset hne hEr, listShiftDiff_cons, List.length_cons]
      set A := listShiftDiff ω l (frameSourceMero ω hω S hS) with hA
      set B := frameSourceMero ω hω (S \ l.toFinset) hne' with hB
      set C := frameSourceMero ω hω ((S \ l.toFinset).erase j) hEr with hC
      have hT : addTranslationMeroEquiv (ω j)
            ((-1 : meroField (Set.univ : Set ℂ)) ^ l.length * B)
          = (-1 : meroField (Set.univ : Set ℂ)) ^ l.length *
              addTranslationMeroEquiv (ω j) B := by
        rw [RingEquiv.map_mul]
        congr 1
        rw [map_pow, RingEquiv.map_neg, RingEquiv.map_one]
      have hid : addTranslationMeroEquiv (ω j) A - A
            - (-1 : meroField (Set.univ : Set ℂ)) ^ (l.length + 1) * C
          = (addTranslationMeroEquiv (ω j)
                (A - (-1 : meroField (Set.univ : Set ℂ)) ^ l.length * B)
              - (A - (-1 : meroField (Set.univ : Set ℂ)) ^ l.length * B))
            + (-1 : meroField (Set.univ : Set ℂ)) ^ l.length *
                (addTranslationMeroEquiv (ω j) B - B + C) := by
        rw [RingEquiv.map_sub, hT, pow_succ]
        ring
      rw [hid]
      exact differentialAlgebraicOver_add
        (differentialAlgebraicOver_sub
          (differentialAlgebraicOver_addTranslationMeroEquiv _ hIH) hIH)
        (_root_.HTGeometry.differentialAlgebraicOver_neg_one_pow_mul hstep)

end

end GaloisForLFunctions.HTGeometry
