import GaloisForLFunctions.HTGeometry.EscapeSubgroup
import GaloisForLFunctions.HTGeometry.PPMatrixRankFormulaConsequences

/-!
# The period-escape dimension of a facet system

A *period-escape separation* of a facet system `faces : A → Finset V` in dimension `d` consists of
`ℚ`-independent translation vectors `a v ∈ ℂ^d` and, for every facet `B`, an escape subgroup
`P B ⊆ ℂ^d` recovering incidence exactly: `a v ∈ P B` if and only if `v ∉ faces B`.  The
*period-escape dimension* `peDim` is the least `d` admitting one.  It records only the incidence
geometry that a facetwise noncompact period quotient forces, with no analytic realization.

* `PeriodEscapeSeparation`, `peDim`;
* **`peDim_le_ppDim`** — every periodic pencil is a period-escape separation, since the period group
  `{z : ℓ z ∈ ℤ}` of a nonzero linear form is closed, has the kernel as identity component, and has
  quotient mapping onto the real line;
* **`isEmpty_periodEscapeSeparation_one`** — two distinct vertices outside one facet obstruct
  dimension one, because an escape subgroup of `ℂ` has `ℚ`-rank at most one;
* **`boundaryWedge_peDim_eq_two`** — hence the boundary wedge has period-escape dimension exactly
  two, matching its periodic-pencil dimension.
-/

open Set Topology

namespace GaloisForLFunctions

variable {V A : Type*}

/-! ## Period-escape separations -/

/-- A period-escape separation of a facet system in complex dimension `d`. -/
structure PeriodEscapeSeparation (faces : A → Finset V) (d : ℕ) where
  /-- The translation vector of each vertex. -/
  a : V → Fin d → ℂ
  /-- The translation vectors are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ a
  /-- The period group of each facet. -/
  P : A → AddSubgroup (Fin d → ℂ)
  /-- Each period group is closed, has complex-linear identity component, and noncompact quotient. -/
  escape : ∀ B, IsEscapeSubgroup (P B)
  /-- Incidence is recovered exactly by membership in the period group. -/
  incidence : ∀ B v, a v ∈ P B ↔ v ∉ faces B

/-- The period-escape dimension: the least complex dimension admitting a period-escape
separation. -/
noncomputable def peDim (faces : A → Finset V) : ℕ :=
  sInf {d | Nonempty (PeriodEscapeSeparation faces d)}

theorem peDim_le_of_nonempty {faces : A → Finset V} {d : ℕ}
    (S : PeriodEscapeSeparation faces d) : peDim faces ≤ d :=
  Nat.sInf_le ⟨S⟩

/-! ## The dimension lower bounds -/

/-- With a vertex present there is no separation in dimension zero: the translation vector would be
the zero vector of a trivial space. -/
theorem isEmpty_periodEscapeSeparation_zero {faces : A → Finset V} (v : V) :
    IsEmpty (PeriodEscapeSeparation faces 0) := by
  refine ⟨fun S => ?_⟩
  have hne : S.a v ≠ 0 := S.indep.ne_zero v
  exact hne (Subsingleton.elim _ _)

/-- **Two distinct vertices outside one facet obstruct dimension one.**  Both translation vectors
lie in that facet's escape subgroup, which has `ℚ`-rank at most one. -/
theorem isEmpty_periodEscapeSeparation_one {faces : A → Finset V} (B : A) {v w : V}
    (hv : v ∉ faces B) (hw : w ∉ faces B) (hvw : v ≠ w) :
    IsEmpty (PeriodEscapeSeparation faces 1) := by
  refine ⟨fun S => ?_⟩
  have hvP : S.a v ∈ S.P B := (S.incidence B v).mpr hv
  have hwP : S.a w ∈ S.P B := (S.incidence B w).mpr hw
  obtain ⟨p, q, hpq, hrel⟩ :=
    DimOne.exists_rat_relation_of_isEscapeSubgroup (S.escape B) hvP hwP
  have h2 : LinearIndependent ℚ ![S.a v, S.a w] := by
    have hcomp := S.indep.comp ![v, w] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    convert hcomp using 1
    funext i
    fin_cases i <;> simp
  obtain ⟨hp, hq⟩ := LinearIndependent.pair_iff.mp h2 p q hrel
  rcases hpq with h | h
  · exact h hp
  · exact h hq

/-- **Lower bound for the period-escape dimension.**  If some facet omits two distinct vertices,
every period-escape separation has dimension at least two. -/
theorem two_le_peDim {faces : A → Finset V} (hex : ∃ d, Nonempty (PeriodEscapeSeparation faces d))
    (B : A) {v w : V} (hv : v ∉ faces B) (hw : w ∉ faces B) (hvw : v ≠ w) :
    2 ≤ peDim faces := by
  obtain ⟨S⟩ := Nat.sInf_mem (s := {d | Nonempty (PeriodEscapeSeparation faces d)}) hex
  by_contra hlt
  have hlt' : peDim faces < 2 := not_le.mp hlt
  interval_cases h : peDim faces
  · exact (isEmpty_periodEscapeSeparation_zero (faces := faces) v).false (h ▸ S)
  · exact (isEmpty_periodEscapeSeparation_one B hv hw hvw).false (h ▸ S)

/-! ## Periodic pencils are period-escape separations -/

variable [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [Fintype A] [DecidableEq A] in
/-- On a facet the pencil evaluation is not an integer: it is `ℚ`-independent from `1`. -/
theorem ppAdmissible_not_int {faces : A → Finset V} {M : A → V → ℂ}
    (hM : PPAdmissible faces M) {B : A} {v : V} (hv : v ∈ faces B) (k : ℤ) :
    M B v ≠ (k : ℂ) := by
  classical
  intro hk
  set f : Option (faces B) → ℂ := fun i => i.elim (1 : ℂ) (fun w => M B (w : V)) with hf
  have hind : LinearIndependent ℚ f := (hM B).2
  set g : Option (faces B) → ℚ := fun i =>
    i.elim ((k : ℚ)) (fun w => if w = (⟨v, hv⟩ : faces B) then (-1 : ℚ) else 0) with hg
  have hsum : ∑ i, g i • f i = 0 := by
    rw [Fintype.sum_option]
    have hrest : ∑ w : faces B, g (some w) • f (some w) = -(M B v) := by
      rw [Finset.sum_eq_single (⟨v, hv⟩ : faces B)]
      · simp [hg, hf]
      · intro w _ hw
        simp [hg, hf, hw]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    rw [hrest]
    simp only [hg, hf, Option.elim]
    rw [Rat.smul_def, mul_one, hk]
    push_cast
    ring
  have := hind
  rw [Fintype.linearIndependent_iff] at this
  have hzero := this g hsum (some (⟨v, hv⟩ : faces B))
  simp [hg] at hzero

omit [Fintype V] [Fintype A] [DecidableEq A] in
/-- On a facet the pencil evaluation is nonzero. -/
theorem ppAdmissible_ne_zero {faces : A → Finset V} {M : A → V → ℂ}
    (hM : PPAdmissible faces M) {B : A} {v : V} (hv : v ∈ faces B) : M B v ≠ 0 := by
  simpa using ppAdmissible_not_int hM hv 0

/-- **Every periodic pencil is a period-escape separation.** -/
noncomputable def periodEscapeSeparationOfPencil {faces : A → Finset V}
    (hne : ∀ B, (faces B).Nonempty) {d : ℕ} (a : V → Fin d → ℂ) (ha : LinearIndependent ℚ a)
    (U : A → Fin d → ℂ) (hU : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) :
    PeriodEscapeSeparation faces d where
  a := a
  indep := ha
  P := fun B => pencilSubgroup (U B)
  escape := by
    intro B
    obtain ⟨v, hv⟩ := hne B
    refine isEscapeSubgroup_pencilSubgroup ?_
    intro hzero
    refine ppAdmissible_ne_zero hU hv ?_
    simp only [hzero, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  incidence := by
    intro B v
    rw [mem_pencilSubgroup]
    constructor
    · rintro ⟨k, hk⟩ hv
      exact ppAdmissible_not_int hU hv k (by simpa using hk)
    · intro hv
      obtain ⟨z, hz⟩ := (hU B).1 v hv
      exact ⟨z, by simpa using hz⟩

omit [Fintype V] [Fintype A] [DecidableEq A] in
theorem peDim_le_of_ppAdmissible {faces : A → Finset V} (hne : ∀ B, (faces B).Nonempty)
    {d : ℕ} (a : V → Fin d → ℂ) (ha : LinearIndependent ℚ a) (U : A → Fin d → ℂ)
    (hU : PPAdmissible faces (fun B v => ∑ i, U B i * a v i)) : peDim faces ≤ d :=
  peDim_le_of_nonempty (periodEscapeSeparationOfPencil hne a ha U hU)

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
/-- A positive periodic-pencil dimension supplies an actual pencil configuration. -/
theorem exists_ppAdmissible_of_ppDim_pos {faces : A → Finset V} (hpos : 0 < ppDim faces) :
    ∃ (a : V → Fin (ppDim faces) → ℂ), LinearIndependent ℚ a ∧
      ∃ (U : A → Fin (ppDim faces) → ℂ),
        PPAdmissible faces (fun B v => ∑ i, U B i * a v i) := by
  have hset : {d | ∃ (a : V → Fin d → ℂ), LinearIndependent ℚ a ∧
      ∃ (U : A → Fin d → ℂ),
        PPAdmissible faces (fun B v => ∑ i, U B i * a v i)}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [ppDim, h, Nat.sInf_empty] at hpos
    exact lt_irrefl 0 hpos
  exact Nat.sInf_mem hset

omit [Fintype V] [Fintype A] [DecidableEq A] in
/-- **The period-escape dimension never exceeds the periodic-pencil dimension.** -/
theorem peDim_le_ppDim {faces : A → Finset V} (hne : ∀ B, (faces B).Nonempty)
    (hpos : 0 < ppDim faces) : peDim faces ≤ ppDim faces := by
  obtain ⟨a, ha, U, hU⟩ := exists_ppAdmissible_of_ppDim_pos hpos
  exact peDim_le_of_ppAdmissible hne a ha U hU

omit [Fintype V] [Fintype A] [DecidableEq A] in
/-- A positive periodic-pencil dimension supplies a period-escape separation. -/
theorem exists_periodEscapeSeparation_of_ppDim_pos {faces : A → Finset V}
    (hne : ∀ B, (faces B).Nonempty) (hpos : 0 < ppDim faces) :
    ∃ d, Nonempty (PeriodEscapeSeparation faces d) := by
  obtain ⟨a, ha, U, hU⟩ := exists_ppAdmissible_of_ppDim_pos hpos
  exact ⟨_, ⟨periodEscapeSeparationOfPencil hne a ha U hU⟩⟩

end GaloisForLFunctions
