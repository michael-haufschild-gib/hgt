import GaloisForLFunctions.HTGeometry.MilnorSlotProduct
import GaloisForLFunctions.HTGeometry.MilnorMonicFactorization
import GaloisForLFunctions.HTGeometry.MilnorClassProduct

/-!
# Symbols with constant or monic irreducible entries

Every entry of a Milnor symbol over a rational function field is a nonzero constant times a product
of monic irreducible polynomials, so multilinearity rewrites any symbol of polynomials as a
combination of symbols all of whose entries are constants or monic irreducibles.  Factoring never
raises the total degree, so the rewriting stays inside a fixed total-degree bound.

* `GoodEntry` : a constant, or a monic irreducible.
* `goodSpan` : the classes of symbols with good entries, bounded degree and bounded total degree.
* `nzList_class_mem_goodSpan` : **every symbol of polynomials is a combination of good symbols.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F] {n : ℕ}

/-- A symbol entry is **good** when it is a constant or a monic irreducible polynomial. -/
def GoodEntry (p : NZPoly F) : Prop :=
  p.1.natDegree = 0 ∨ (p.1.Monic ∧ Irreducible p.1)

theorem exists_nzList_of_ne_zero :
    ∀ (qs : List (Polynomial F)), (∀ q ∈ qs, q ≠ 0) →
      ∃ qsN : List (NZPoly F), qsN.map Subtype.val = qs := by
  intro qs
  induction qs with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons q t ih =>
      intro h
      obtain ⟨tN, htN⟩ := ih fun r hr => h r (by simp [hr])
      exact ⟨⟨q, h q (by simp)⟩ :: tN, by simp [htN]⟩

theorem polyUnit_nzProd :
    ∀ ps : List (NZPoly F), polyUnit (nzProd_ne_zero ps) = (nzList ps).prod := by
  intro ps
  induction ps with
  | nil =>
      rw [nzList, List.map_nil, List.prod_nil]
      refine Units.ext ?_
      show algebraMap (Polynomial F) (RatFunc F) (nzProd ([] : List (NZPoly F))) = _
      rw [nzProd_nil, map_one]
      rfl
  | cons p t ih =>
      rw [nzList_cons, List.prod_cons, ← ih]
      refine Units.ext ?_
      rw [Units.val_mul]
      show algebraMap (Polynomial F) (RatFunc F) (nzProd (p :: t))
        = algebraMap (Polynomial F) (RatFunc F) p.1
          * algebraMap (Polynomial F) (RatFunc F) (nzProd t)
      rw [nzProd_cons, map_mul]

/-- The classes of symbols all of whose entries are good, of degree at most `d`, and of total
degree at most `N`. -/
noncomputable def goodSpan (d N n : ℕ) : AddSubgroup (MilnorKDeg (RatFunc F) n) :=
  AddSubgroup.closure {x | ∃ (ps : List (NZPoly F)) (h : (nzList ps).length = n),
    (∀ p ∈ ps, GoodEntry p) ∧ (∀ p ∈ ps, p.1.natDegree ≤ d) ∧ nzTotal ps ≤ N ∧
      x = milnorClassDeg (RatFunc F) n ⟨nzList ps, h⟩}

theorem mem_goodSpan {d N : ℕ} {ps : List (NZPoly F)} (h : (nzList ps).length = n)
    (hgood : ∀ p ∈ ps, GoodEntry p) (hdeg : ∀ p ∈ ps, p.1.natDegree ≤ d)
    (htot : nzTotal ps ≤ N) :
    milnorClassDeg (RatFunc F) n ⟨nzList ps, h⟩ ∈ goodSpan (F := F) d N n :=
  AddSubgroup.subset_closure ⟨ps, h, hgood, hdeg, htot, rfl⟩

/-- **Every symbol of polynomials is a combination of symbols with good entries**, without raising
either the entry degrees or the total degree. -/
theorem nzList_class_mem_goodSpan {d N : ℕ} :
    ∀ (rest good : List (NZPoly F)), (∀ p ∈ good, GoodEntry p) →
      (∀ p ∈ good ++ rest, p.1.natDegree ≤ d) → nzTotal (good ++ rest) ≤ N →
      ∀ h : (nzList (good ++ rest)).length = n,
      milnorClassDeg (RatFunc F) n ⟨nzList (good ++ rest), h⟩ ∈ goodSpan (F := F) d N n := by
  intro rest
  induction rest with
  | nil =>
      intro good hgood hdeg htot h
      simp only [List.append_nil] at hdeg htot h ⊢
      exact mem_goodSpan h hgood hdeg htot
  | cons p rest' ih =>
      intro good hgood hdeg htot h
      classical
      obtain ⟨c, qs0, hc, hqs0, hpeq, hsum⟩ := exists_monic_irreducible_factorization p.2
      obtain ⟨qs, hqsval⟩ := exists_nzList_of_ne_zero qs0 fun q hq => (hqs0 q hq).1.ne_zero
      have hCc : (Polynomial.C c : Polynomial F) ≠ 0 := by simpa using hc
      have hnzProd : nzProd qs = qs0.prod := by rw [nzProd, hqsval]
      have hnzTotal : nzTotal qs = p.1.natDegree := by
        rw [nzTotal, ← hsum, ← hqsval, List.map_map]
        rfl
      have hlen1 : (nzList good ++ nzList rest').length + 1 = n := by
        have := h
        simp only [nzList, List.map_append, List.map_cons, List.length_append,
          List.length_cons] at this ⊢
        omega
      have hcast : milnorClassDeg (RatFunc F) n ⟨nzList (good ++ p :: rest'), h⟩
          = slotClass (nzList good) (nzList rest') hlen1 (nzUnit p) :=
        congrArg (milnorClassDeg (RatFunc F) n) (Subtype.ext (by simp [nzList]))
      have hunitsplit : nzUnit p = polyUnit hCc * (nzList qs).prod := by
        rw [← polyUnit_nzProd qs]
        refine Units.ext ?_
        rw [Units.val_mul]
        show algebraMap (Polynomial F) (RatFunc F) p.1
          = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c)
            * algebraMap (Polynomial F) (RatFunc F) (nzProd qs)
        rw [← map_mul, hnzProd, ← hpeq]
      -- degree bookkeeping
      have hpdeg : p.1.natDegree ≤ d := hdeg p (by simp)
      have hgooddeg : ∀ r ∈ good, r.1.natDegree ≤ d := fun r hr => hdeg r (by simp [hr])
      have hrestdeg : ∀ r ∈ rest', r.1.natDegree ≤ d := fun r hr => hdeg r (by simp [hr])
      have htotsplit : nzTotal (good ++ p :: rest')
          = nzTotal good + p.1.natDegree + nzTotal rest' := by
        simp only [nzTotal_append, nzTotal_cons]
        omega
      -- the general step: replacing `p` by an entry of no larger degree
      have hstep : ∀ r : NZPoly F, GoodEntry r → r.1.natDegree ≤ p.1.natDegree →
          slotClass (nzList good) (nzList rest') hlen1 (nzUnit r)
            ∈ goodSpan (F := F) d N n := by
        intro r hr hrdeg
        have hgoodapp : ∀ x ∈ good ++ [r], GoodEntry x := by
          intro x hx
          rcases List.mem_append.1 hx with h1 | h2
          · exact hgood x h1
          · rw [List.mem_singleton.1 h2]; exact hr
        have hlist : (good ++ [r]) ++ rest' = good ++ r :: rest' := by simp
        have hdeg' : ∀ x ∈ (good ++ [r]) ++ rest', x.1.natDegree ≤ d := by
          rw [hlist]
          intro x hx
          rcases List.mem_append.1 hx with h1 | h2
          · exact hgooddeg x h1
          · rcases List.mem_cons.1 h2 with rfl | h3
            · exact le_trans hrdeg hpdeg
            · exact hrestdeg x h3
        have htot' : nzTotal ((good ++ [r]) ++ rest') ≤ N := by
          rw [hlist]
          have : nzTotal (good ++ r :: rest')
              = nzTotal good + r.1.natDegree + nzTotal rest' := by
            simp only [nzTotal_append, nzTotal_cons]
            omega
          rw [this]
          rw [htotsplit] at htot
          omega
        have hlen' : (nzList ((good ++ [r]) ++ rest')).length = n := by
          rw [hlist]
          have := h
          simp only [nzList, List.map_append, List.map_cons, List.length_append,
            List.length_cons] at this ⊢
          omega
        have := ih (good ++ [r]) hgoodapp hdeg' htot' hlen'
        have hcast2 : milnorClassDeg (RatFunc F) n ⟨nzList ((good ++ [r]) ++ rest'), hlen'⟩
            = slotClass (nzList good) (nzList rest') hlen1 (nzUnit r) :=
          congrArg (milnorClassDeg (RatFunc F) n) (Subtype.ext (by simp [nzList]))
        rwa [hcast2] at this
      rw [hcast, hunitsplit, slotClass_mul, slotClass_prod]
      refine AddSubgroup.add_mem _ ?_ ?_
      · have hCcgood : GoodEntry (⟨Polynomial.C c, hCc⟩ : NZPoly F) := by
          left
          exact Polynomial.natDegree_C c
        exact hstep ⟨Polynomial.C c, hCc⟩ hCcgood (by simp [Polynomial.natDegree_C])
      · have hmapeq : (nzList qs).map (slotClass (nzList good) (nzList rest') hlen1)
            = qs.map (fun q => slotClass (nzList good) (nzList rest') hlen1 (nzUnit q)) :=
          List.map_map
        rw [hmapeq]
        refine AddSubgroup.list_sum_mem _ ?_
        intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
        have hq0 : q.1 ∈ qs0 := by
          rw [← hqsval]
          exact List.mem_map_of_mem hq
        refine hstep q (Or.inr ⟨(hqs0 q.1 hq0).1, (hqs0 q.1 hq0).2.1⟩) ?_
        rw [← hnzTotal]
        have : q.1.natDegree ∈ qs.map (fun r => r.1.natDegree) := List.mem_map_of_mem hq
        exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ this

end GaloisForLFunctions.HTGeometry
