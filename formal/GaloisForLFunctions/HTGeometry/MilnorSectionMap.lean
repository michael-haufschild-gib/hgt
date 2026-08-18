import GaloisForLFunctions.HTGeometry.MilnorSectionMultiplicative
import GaloisForLFunctions.HTGeometry.MilnorSlotPermutation

/-!
# Milnor's section on symbols, and the Steinberg relation

Milnor's section sends a symbol of the residue field at `π` to the symbol of its canonical lifts
followed by `π`.  On the free abelian group of symbols this is immediate; the content is that the
defining relations of Milnor `K`-theory are killed.

The Steinberg relation is killed **on the nose**: the canonical lifts of `ȳ` and `1 − ȳ` have degree
below `deg π` and sum to `1` modulo `π`, hence sum to `1` exactly, so their symbol vanishes.

* `liftUnit`, `sectionSymbol`, `sectionFree` : the section on symbols and on formal sums.
* `sectionSymbol_steinberg` : **the Steinberg relation is killed.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- The canonical lift of a residue class, as a unit of `F(t)`. -/
noncomputable def liftUnit {π : Polynomial F} (hπ : Irreducible π)
    (y : (polyResidueField hπ)ˣ) : (RatFunc F)ˣ := polyUnit (liftPoly_ne_zero hπ y)

theorem liftUnit_natDegree_lt {π : Polynomial F} (hπ : Irreducible π)
    (y : (polyResidueField hπ)ˣ) : (liftPoly hπ y).natDegree < π.natDegree :=
  liftPoly_natDegree_lt hπ y

theorem liftPoly_notMem_span {π : Polynomial F} (hπ : Irreducible π)
    (y : (polyResidueField hπ)ˣ) : liftPoly hπ y ∉ Ideal.span {π} :=
  notMem_span_of_natDegree_lt (liftPoly_ne_zero hπ y) (liftPoly_natDegree_lt hπ y)

/-- The section on a symbol: the canonical lifts, followed by `π`. -/
noncomputable def sectionSymbol {π : Polynomial F} (hπ : Irreducible π) {n : ℕ}
    (s : MilnorSymbolDeg (polyResidueField hπ) n) : MilnorKDeg (RatFunc F) (n + 1) :=
  milnorClassDeg (RatFunc F) (n + 1)
    ⟨(s.val.map (liftUnit hπ)) ++ [polyUnit hπ.ne_zero], by
      simp [s.property]⟩

/-- **The Steinberg relation is killed by the section.** -/
theorem sectionSymbol_steinberg {π : Polynomial F} (hπ : Irreducible π) {n : ℕ}
    {y : (polyResidueField hπ)ˣ} (hy : ((y : polyResidueField hπ)) ≠ 1)
    (l₁ l₂ : List (polyResidueField hπ)ˣ) (h : (l₁ ++ l₂).length + 2 = n) :
    sectionSymbol hπ (n := n) ⟨l₁ ++ y :: oneSubUnit hy :: l₂, by
      rw [length_middle, length_middle]; exact h⟩ = 0 := by
  classical
  set u : Polynomial F := liftPoly hπ y with hu
  set t : Polynomial F := liftPoly hπ (oneSubUnit hy) with ht
  have hune : u ≠ 0 := liftPoly_ne_zero hπ y
  have htne : t ≠ 0 := liftPoly_ne_zero hπ (oneSubUnit hy)
  have hud : u.natDegree < π.natDegree := liftPoly_natDegree_lt hπ y
  have htd : t.natDegree < π.natDegree := liftPoly_natDegree_lt hπ (oneSubUnit hy)
  have hdvd : π ∣ (u + t - 1) :=
    dvd_add_sub_one_of_residueUnit hπ hune htne (liftPoly_notMem_span hπ y)
      (liftPoly_notMem_span hπ (oneSubUnit hy)) hy (liftPoly_residue hπ y)
      (liftPoly_residue hπ (oneSubUnit hy))
  have hn2 : ((l₁.map (liftUnit hπ)) ++ (l₂.map (liftUnit hπ) ++
      [polyUnit hπ.ne_zero])).length + 2 = n + 1 := by
    have h' := h
    simp only [List.length_append] at h'
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  have hcast : sectionSymbol hπ (n := n) ⟨l₁ ++ y :: oneSubUnit hy :: l₂, by
        rw [length_middle, length_middle]; exact h⟩
      = twoSlot (l₁.map (liftUnit hπ)) (l₂.map (liftUnit hπ) ++ [polyUnit hπ.ne_zero]) hn2
        (polyUnit hune) (polyUnit htne) := by
    refine congrArg (milnorClassDeg (RatFunc F) (n + 1)) (Subtype.ext ?_)
    simp [liftUnit, hu, ht]
  rw [hcast]
  exact twoSlot_lift_steinberg _ _ hn2 hune htne hud htd hdvd

/-- **The multilinearity relation is killed modulo the previous stage of the filtration.** -/
theorem sectionSymbol_mul {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree) {n : ℕ}
    (a b : (polyResidueField hπ)ˣ) (l₁ l₂ : List (polyResidueField hπ)ˣ)
    (h : (l₁ ++ l₂).length + 1 = n) :
    sectionSymbol hπ (n := n) ⟨l₁ ++ (a * b) :: l₂, by rw [length_middle]; exact h⟩
        - sectionSymbol hπ (n := n) ⟨l₁ ++ a :: l₂, by rw [length_middle]; exact h⟩
        - sectionSymbol hπ (n := n) ⟨l₁ ++ b :: l₂, by rw [length_middle]; exact h⟩
      ∈ degreeFiltration (F := F) (π.natDegree - 1) (n + 1) := by
  classical
  set A : List (RatFunc F)ˣ := l₁.map (liftUnit hπ) with hA
  set B : List (RatFunc F)ˣ := l₂.map (liftUnit hπ) with hB
  have hlen : (A ++ B).length + 2 = n + 1 := by
    have h' := h
    simp only [List.length_append] at h' ⊢
    simp only [hA, hB, List.length_map]
    omega
  have hmove : ∀ x : (polyResidueField hπ)ˣ,
      sectionSymbol hπ (n := n) ⟨l₁ ++ x :: l₂, by rw [length_middle]; exact h⟩
        = ((-1 : ℤ) ^ B.length) • twoSlot A B hlen (liftUnit hπ x) (polyUnit hπ.ne_zero) := by
    intro x
    have hmv : ((A ++ [liftUnit hπ x]) ++ B ++ (polyUnit hπ.ne_zero) :: []).length = n + 1 := by
      have h' := h
      simp only [List.length_append] at h'
      simp only [List.length_append, List.length_cons, List.length_nil, hA, hB, List.length_map]
      omega
    have hc1 : sectionSymbol hπ (n := n) ⟨l₁ ++ x :: l₂, by rw [length_middle]; exact h⟩
        = milnorClassDeg (RatFunc F) (n + 1)
          ⟨(A ++ [liftUnit hπ x]) ++ B ++ (polyUnit hπ.ne_zero) :: [], hmv⟩ :=
      congrArg (milnorClassDeg (RatFunc F) (n + 1)) (Subtype.ext (by simp [hA, hB]))
    rw [hc1, milnorClassDeg_move (K := RatFunc F) (n := n + 1) B (A ++ [liftUnit hπ x]) []
      (polyUnit hπ.ne_zero) hmv]
    congr 1
    exact congrArg (milnorClassDeg (RatFunc F) (n + 1)) (Subtype.ext (by simp))
  rw [hmove, hmove, hmove, ← smul_sub, ← smul_sub]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have hentries : ∀ (l : List (polyResidueField hπ)ˣ) (c : (RatFunc F)ˣ),
      c ∈ l.map (liftUnit hπ) → polyDegLt (F := F) π.natDegree c := by
    intro l c hc
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hc
    exact ⟨liftPoly hπ y, liftPoly_ne_zero hπ y, liftPoly_natDegree_lt hπ y, rfl⟩
  have hdvd : π ∣ (liftPoly hπ a * liftPoly hπ b - liftPoly hπ (a * b)) := by
    refine dvd_mul_sub_of_residueUnit hπ (liftPoly_ne_zero hπ a) (liftPoly_ne_zero hπ b)
      (liftPoly_ne_zero hπ (a * b)) (liftPoly_notMem_span hπ a) (liftPoly_notMem_span hπ b)
      (liftPoly_notMem_span hπ (a * b)) ?_
    rw [liftPoly_residue hπ a, liftPoly_residue hπ b, liftPoly_residue hπ (a * b)]
  have hmul := twoSlot_lift_mul (F := F) (n := n + 1) hd A B hlen hπ.ne_zero
    (liftPoly_ne_zero hπ a) (liftPoly_ne_zero hπ b) (liftPoly_ne_zero hπ (a * b))
    rfl (liftPoly_natDegree_lt hπ a) (liftPoly_natDegree_lt hπ b)
    (liftPoly_natDegree_lt hπ (a * b)) hdvd
  have hle := lowTwoSlot_le_degreeFiltration (F := F) (d := π.natDegree) A B hlen
    (fun c hc => hentries l₁ c (by rw [hA] at hc; exact hc))
    (fun c hc => hentries l₂ c (by rw [hB] at hc; exact hc))
  have hmem := hle hmul
  have hneg : twoSlot A B hlen (liftUnit hπ (a * b)) (polyUnit hπ.ne_zero)
      - twoSlot A B hlen (liftUnit hπ a) (polyUnit hπ.ne_zero)
      - twoSlot A B hlen (liftUnit hπ b) (polyUnit hπ.ne_zero)
      = -(twoSlot A B hlen (polyUnit (liftPoly_ne_zero hπ a)) (polyUnit hπ.ne_zero)
        + twoSlot A B hlen (polyUnit (liftPoly_ne_zero hπ b)) (polyUnit hπ.ne_zero)
        - twoSlot A B hlen (polyUnit (liftPoly_ne_zero hπ (a * b))) (polyUnit hπ.ne_zero)) := by
    simp only [liftUnit]
    abel
  rw [hneg]
  exact AddSubgroup.neg_mem _ hmem

/-- The section on formal sums of symbols, landing in `K_{n+1}^M(F(t))` modulo the previous stage of
the degree filtration. -/
noncomputable def sectionFree {π : Polynomial F} (hπ : Irreducible π) (n : ℕ) :
    FreeAbelianGroup (MilnorSymbolDeg (polyResidueField hπ) n) →+
      (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (π.natDegree - 1) (n + 1)) :=
  FreeAbelianGroup.lift fun s => QuotientAddGroup.mk (sectionSymbol hπ s)

@[simp]
theorem sectionFree_of {π : Polynomial F} (hπ : Irreducible π) (n : ℕ)
    (s : MilnorSymbolDeg (polyResidueField hπ) n) :
    sectionFree hπ n (FreeAbelianGroup.of s) = QuotientAddGroup.mk (sectionSymbol hπ s) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The defining relations of Milnor `K`-theory are killed by the section.** -/
theorem sectionFree_kills_relations {π : Polynomial F} (hπ : Irreducible π)
    (hd : 1 ≤ π.natDegree) (n : ℕ) :
    milnorRelSubgroupDeg (polyResidueField hπ) n ≤ (sectionFree hπ n).ker := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro x (⟨a, b, l₁, l₂, hlen, rfl⟩ | ⟨y, hy, l₁, l₂, hlen, rfl⟩)
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub, sectionFree_of, sectionFree_of,
      sectionFree_of, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub,
      QuotientAddGroup.eq_zero_iff]
    exact sectionSymbol_mul hπ hd a b l₁ l₂ hlen
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, sectionFree_of,
      sectionSymbol_steinberg hπ hy l₁ l₂ hlen]
    exact QuotientAddGroup.mk_zero _

/-- **Milnor's section** `K_n^M(F[X]/π) → K_{n+1}^M(F(t)) / L_{deg π − 1}`. -/
noncomputable def sectionMap {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree)
    (n : ℕ) :
    MilnorKDeg (polyResidueField hπ) n →+
      (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (π.natDegree - 1) (n + 1)) :=
  QuotientAddGroup.lift _ (sectionFree hπ n) (sectionFree_kills_relations hπ hd n)

@[simp]
theorem sectionMap_class {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree) (n : ℕ)
    (s : MilnorSymbolDeg (polyResidueField hπ) n) :
    sectionMap hπ hd n (milnorClassDeg (polyResidueField hπ) n s)
      = QuotientAddGroup.mk (sectionSymbol hπ s) := by
  show sectionFree hπ n (FreeAbelianGroup.of s) = _
  exact sectionFree_of hπ n s

/-- The residue at `π`, taken with `π` as its own uniformizer, kills the lower stage of the degree
filtration. -/
theorem polyResidue_degreeFiltration_eq_zero {π : Polynomial F} (hπ : Irreducible π) {d n : ℕ}
    (hdlt : d < π.natDegree) :
    ∀ x ∈ degreeFiltration (F := F) d n, milnorResidue (polyResidueData hπ) n x = 0 := by
  intro x hx
  have hle : degreeFiltration (F := F) d n
      ≤ (milnorResidue (polyResidueData hπ) n).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro y ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker]
    refine milnorResidue_eq_zero_of_units _ n s ?_
    intro a ha
    obtain ⟨p, hp, hple, rfl⟩ := hs a ha
    exact polyResidueData_val'_eq_zero hπ hp
      (notMem_span_of_natDegree_lt hp (by omega))
  exact hle hx

/-- The residue at `π`, descended to the quotient by the lower stage of the filtration. -/
noncomputable def residueQuot {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree)
    (n : ℕ) :
    (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (π.natDegree - 1) (n + 1))
      →+ MilnorKDeg (polyResidueField hπ) n :=
  QuotientAddGroup.lift _ (milnorResidue (polyResidueData hπ) (n + 1))
    (fun x hx => polyResidue_degreeFiltration_eq_zero hπ (by omega) x hx)

/-- The residue of a symbol ending in the uniformizer, with the length given by an equation. -/
theorem milnorResidue_append_unif' {K k : Type*} [Field K] [Field k] (D : ResidueData K k)
    {m : ℕ} (l : List Kˣ) (hl : l.length = m) (hval : ∀ a ∈ l, D.val' a = 0)
    (h : (l ++ [D.unif]).length = m + 1) (hm : (l.map D.residueUnit).length = m) :
    milnorResidue D (m + 1) (milnorClassDeg K (m + 1) ⟨l ++ [D.unif], h⟩)
      = milnorClassDeg k m ⟨l.map D.residueUnit, hm⟩ := by
  subst hl
  exact milnorResidue_append_unif D l hval h

/-- **The residue recovers the symbol from Milnor's section.** -/
theorem milnorResidue_sectionSymbol {π : Polynomial F} (hπ : Irreducible π) {n : ℕ}
    (s : MilnorSymbolDeg (polyResidueField hπ) n) :
    milnorResidue (polyResidueData hπ) (n + 1) (sectionSymbol hπ s)
      = milnorClassDeg (polyResidueField hπ) n s := by
  classical
  have hlen : (s.val.map (liftUnit hπ)).length = n := by
    rw [List.length_map]; exact s.property
  have hval : ∀ a ∈ s.val.map (liftUnit hπ), (polyResidueData hπ).val' a = 0 := by
    intro a ha
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 ha
    exact polyResidueData_val'_eq_zero hπ (liftPoly_ne_zero hπ y) (liftPoly_notMem_span hπ y)
  have hres : (s.val.map (liftUnit hπ)).map (polyResidueData hπ).residueUnit = s.val := by
    calc (s.val.map (liftUnit hπ)).map (polyResidueData hπ).residueUnit
        = s.val.map (fun y => (polyResidueData hπ).residueUnit (liftUnit hπ y)) := by
          rw [List.map_map]; rfl
      _ = s.val.map id := List.map_congr_left (fun y _ => liftPoly_residue hπ y)
      _ = s.val := List.map_id _
  have hm : ((s.val.map (liftUnit hπ)).map (polyResidueData hπ).residueUnit).length = n := by
    rw [hres]; exact s.property
  have hstep := milnorResidue_append_unif' (polyResidueData hπ) (s.val.map (liftUnit hπ))
    hlen hval (by simp [hlen]) hm
  refine hstep.trans ?_
  exact congrArg (milnorClassDeg (polyResidueField hπ) n) (Subtype.ext hres)

/-- **The residue inverts Milnor's section.** -/
theorem residueQuot_sectionMap {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree)
    (n : ℕ) (x : MilnorKDeg (polyResidueField hπ) n) :
    residueQuot hπ hd n (sectionMap hπ hd n x) = x := by
  classical
  have hcomp : (residueQuot hπ hd n).comp (sectionMap hπ hd n) = AddMonoidHom.id _ := by
    refine milnorKDeg_hom_ext (F := polyResidueField hπ) ?_
    intro s
    show residueQuot hπ hd n (sectionMap hπ hd n (milnorClassDeg _ n s)) = milnorClassDeg _ n s
    rw [sectionMap_class]
    exact milnorResidue_sectionSymbol hπ s
  exact congrArg
    (fun f : MilnorKDeg (polyResidueField hπ) n →+ MilnorKDeg (polyResidueField hπ) n => f x)
    hcomp

/-- **The section at `π` has vanishing residue at every other place of the same degree.** -/
theorem milnorResidue_sectionSymbol_of_ne {π π' : Polynomial F} (hπ : Irreducible π)
    (hπ' : Irreducible π') (hne : ¬ Associated π π') (hdeg : π.natDegree = π'.natDegree)
    {n : ℕ} (s : MilnorSymbolDeg (polyResidueField hπ) n) :
    milnorResidue (polyResidueData hπ') (n + 1) (sectionSymbol hπ s) = 0 := by
  classical
  refine milnorResidue_eq_zero_of_units _ (n + 1) _ ?_
  intro a ha
  have hmem : a ∈ (s.val.map (liftUnit hπ)) ++ [polyUnit hπ.ne_zero] := ha
  rcases List.mem_append.1 hmem with h1 | h2
  · obtain ⟨y, _, rfl⟩ := List.mem_map.1 h1
    refine polyResidueData_val'_eq_zero hπ' (liftPoly_ne_zero hπ y) ?_
    exact notMem_span_of_natDegree_lt (liftPoly_ne_zero hπ y)
      (by rw [← hdeg]; exact liftPoly_natDegree_lt hπ y)
  · rw [List.mem_singleton] at h2
    subst h2
    exact polyResidueData_val'_eq_zero hπ' hπ.ne_zero
      (notMem_span_of_not_associated hπ hπ' hne)

/-! ## The section and the residue with the filtration index supplied separately

For the assembly over all places of a fixed degree it is convenient to name the stage of the
filtration explicitly, so that sections at different places land in the *same* quotient. -/

/-- The section on formal sums, landing in the quotient by a named stage of the filtration. -/
noncomputable def sectionFreeAt {π : Polynomial F} (hπ : Irreducible π) (m n : ℕ) :
    FreeAbelianGroup (MilnorSymbolDeg (polyResidueField hπ) n) →+
      (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) m (n + 1)) :=
  FreeAbelianGroup.lift fun s => QuotientAddGroup.mk (sectionSymbol hπ s)

@[simp]
theorem sectionFreeAt_of {π : Polynomial F} (hπ : Irreducible π) (m n : ℕ)
    (s : MilnorSymbolDeg (polyResidueField hπ) n) :
    sectionFreeAt hπ m n (FreeAbelianGroup.of s) = QuotientAddGroup.mk (sectionSymbol hπ s) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem sectionFreeAt_kills_relations {π : Polynomial F} (hπ : Irreducible π)
    (hd : 1 ≤ π.natDegree) {m : ℕ} (hm : π.natDegree - 1 ≤ m) (n : ℕ) :
    milnorRelSubgroupDeg (polyResidueField hπ) n ≤ (sectionFreeAt hπ m n).ker := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro x (⟨a, b, l₁, l₂, hlen, rfl⟩ | ⟨y, hy, l₁, l₂, hlen, rfl⟩)
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub, sectionFreeAt_of,
      sectionFreeAt_of, sectionFreeAt_of, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub,
      QuotientAddGroup.eq_zero_iff]
    exact degreeFiltration_mono hm (sectionSymbol_mul hπ hd a b l₁ l₂ hlen)
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, sectionFreeAt_of,
      sectionSymbol_steinberg hπ hy l₁ l₂ hlen]
    exact QuotientAddGroup.mk_zero _

/-- **Milnor's section**, landing in the quotient by a named stage of the filtration. -/
noncomputable def sectionMapAt {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree)
    {m : ℕ} (hm : π.natDegree - 1 ≤ m) (n : ℕ) :
    MilnorKDeg (polyResidueField hπ) n →+
      (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) m (n + 1)) :=
  QuotientAddGroup.lift _ (sectionFreeAt hπ m n) (sectionFreeAt_kills_relations hπ hd hm n)

@[simp]
theorem sectionMapAt_class {π : Polynomial F} (hπ : Irreducible π) (hd : 1 ≤ π.natDegree)
    {m : ℕ} (hm : π.natDegree - 1 ≤ m) (n : ℕ)
    (s : MilnorSymbolDeg (polyResidueField hπ) n) :
    sectionMapAt hπ hd hm n (milnorClassDeg (polyResidueField hπ) n s)
      = QuotientAddGroup.mk (sectionSymbol hπ s) :=
  sectionFreeAt_of hπ m n s

/-- The residue at `π`, descended from a named stage of the filtration. -/
noncomputable def residueQuotAt {π : Polynomial F} (hπ : Irreducible π) {m : ℕ}
    (hm : m < π.natDegree) (n : ℕ) :
    (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) m (n + 1))
      →+ MilnorKDeg (polyResidueField hπ) n :=
  QuotientAddGroup.lift _ (milnorResidue (polyResidueData hπ) (n + 1))
    (fun x hx => polyResidue_degreeFiltration_eq_zero hπ hm x hx)

@[simp]
theorem residueQuotAt_mk {π : Polynomial F} (hπ : Irreducible π) {m : ℕ}
    (hm : m < π.natDegree) (n : ℕ) (y : MilnorKDeg (RatFunc F) (n + 1)) :
    residueQuotAt hπ hm n (QuotientAddGroup.mk y)
      = milnorResidue (polyResidueData hπ) (n + 1) y := rfl

/-- **The residue inverts the section**, at a named stage of the filtration. -/
theorem residueQuotAt_sectionMapAt {π : Polynomial F} (hπ : Irreducible π)
    (hd : 1 ≤ π.natDegree) {m : ℕ} (hm : π.natDegree - 1 ≤ m) (hm' : m < π.natDegree) (n : ℕ)
    (x : MilnorKDeg (polyResidueField hπ) n) :
    residueQuotAt hπ hm' n (sectionMapAt hπ hd hm n x) = x := by
  classical
  have hcomp : (residueQuotAt hπ hm' n).comp (sectionMapAt hπ hd hm n) = AddMonoidHom.id _ := by
    refine milnorKDeg_hom_ext (F := polyResidueField hπ) ?_
    intro s
    show residueQuotAt hπ hm' n (sectionMapAt hπ hd hm n (milnorClassDeg _ n s))
      = milnorClassDeg _ n s
    rw [sectionMapAt_class, residueQuotAt_mk]
    exact milnorResidue_sectionSymbol hπ s
  exact congrArg
    (fun f : MilnorKDeg (polyResidueField hπ) n →+ MilnorKDeg (polyResidueField hπ) n => f x)
    hcomp

/-- **The section at `π` is killed by the residue at any other place of the same degree.** -/
theorem residueQuotAt_sectionMapAt_of_ne {π π' : Polynomial F} (hπ : Irreducible π)
    (hπ' : Irreducible π') (hne : ¬ Associated π π') (hdeg : π.natDegree = π'.natDegree)
    (hd : 1 ≤ π.natDegree) {m : ℕ} (hm : π.natDegree - 1 ≤ m) (hm' : m < π'.natDegree) (n : ℕ)
    (x : MilnorKDeg (polyResidueField hπ) n) :
    residueQuotAt hπ' hm' n (sectionMapAt hπ hd hm n x) = 0 := by
  classical
  have hcomp : (residueQuotAt hπ' hm' n).comp (sectionMapAt hπ hd hm n) = 0 := by
    refine milnorKDeg_hom_ext (F := polyResidueField hπ) ?_
    intro s
    show residueQuotAt hπ' hm' n (sectionMapAt hπ hd hm n (milnorClassDeg _ n s)) = 0
    rw [sectionMapAt_class, residueQuotAt_mk]
    exact milnorResidue_sectionSymbol_of_ne hπ hπ' hne hdeg s
  have := congrArg
    (fun f : MilnorKDeg (polyResidueField hπ) n →+ MilnorKDeg (polyResidueField hπ') n => f x)
    hcomp
  simpa using this

/-- A polynomial unit of degree below `deg π` **is** the canonical lift of its own residue. -/
theorem eq_liftUnit_residue {π : Polynomial F} (hπ : Irreducible π) {p : Polynomial F}
    (hp : p ≠ 0) (hpd : p.natDegree < π.natDegree) :
    liftUnit hπ ((polyResidueData hπ).residueUnit (polyUnit hp)) = polyUnit hp := by
  refine Units.ext ?_
  have heq : liftPoly hπ ((polyResidueData hπ).residueUnit (polyUnit hp)) = p :=
    (liftPoly_eq_of_residue_eq hπ hp hpd rfl).symm
  show algebraMap (Polynomial F) (RatFunc F)
      (liftPoly hπ ((polyResidueData hπ).residueUnit (polyUnit hp)))
    = algebraMap (Polynomial F) (RatFunc F) p
  rw [heq]

/-- A list of polynomial units of degree below `deg π` is the list of canonical lifts of its
residues. -/
theorem map_liftUnit_residue {π : Polynomial F} (hπ : Irreducible π) :
    ∀ l : List (RatFunc F)ˣ, (∀ a ∈ l, polyDegLt (F := F) π.natDegree a) →
      (l.map (polyResidueData hπ).residueUnit).map (liftUnit hπ) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro hl
      obtain ⟨p, hp, hpd, rfl⟩ := hl a (by simp)
      rw [List.map_cons, List.map_cons, ih (fun b hb => hl b (by simp [hb])),
        eq_liftUnit_residue hπ hp hpd]

/-- **A reduced generator with leading entry `π` is, up to sign, a section symbol.** -/
theorem class_cons_eq_sectionSymbol {π : Polynomial F} (hπ : Irreducible π) {n : ℕ}
    (l : List (RatFunc F)ˣ) (hl : ∀ a ∈ l, polyDegLt (F := F) π.natDegree a)
    (hlen : l.length = n) (h : (polyUnit hπ.ne_zero :: l).length = n + 1) :
    milnorClassDeg (RatFunc F) (n + 1) ⟨polyUnit hπ.ne_zero :: l, h⟩
      = ((-1 : ℤ) ^ n) • sectionSymbol hπ
          (n := n) ⟨l.map (polyResidueData hπ).residueUnit, by
            rw [List.length_map]; exact hlen⟩ := by
  classical
  have hmv : ([] ++ l ++ polyUnit hπ.ne_zero :: []).length = n + 1 := by
    simp only [List.nil_append, List.length_append, List.length_cons, List.length_nil, hlen]
  have hmove := milnorClassDeg_move (K := RatFunc F) (n := n + 1) l [] [] (polyUnit hπ.ne_zero) hmv
  have hsec : sectionSymbol hπ (n := n) ⟨l.map (polyResidueData hπ).residueUnit, by
        rw [List.length_map]; exact hlen⟩
      = milnorClassDeg (RatFunc F) (n + 1) ⟨[] ++ l ++ polyUnit hπ.ne_zero :: [], hmv⟩ := by
    refine congrArg (milnorClassDeg (RatFunc F) (n + 1)) (Subtype.ext ?_)
    show (l.map (polyResidueData hπ).residueUnit).map (liftUnit hπ) ++ [polyUnit hπ.ne_zero]
      = [] ++ l ++ polyUnit hπ.ne_zero :: []
    rw [map_liftUnit_residue hπ l hl]
    simp
  have hhead : milnorClassDeg (RatFunc F) (n + 1)
        ⟨[] ++ polyUnit hπ.ne_zero :: (l ++ []), length_move [] l [] (polyUnit hπ.ne_zero) hmv⟩
      = milnorClassDeg (RatFunc F) (n + 1) ⟨polyUnit hπ.ne_zero :: l, h⟩ :=
    congrArg (milnorClassDeg (RatFunc F) (n + 1)) (Subtype.ext (by simp))
  rw [hsec, hmove, hhead, smul_smul, ← pow_add, hlen]
  have hsq : ((-1 : ℤ) ^ (n + n)) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  rw [hsq, one_zsmul]

end GaloisForLFunctions.HTGeometry
