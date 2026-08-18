import GaloisForLFunctions.HTGeometry.MilnorSumSplitting
import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue

/-!
# Lowering one of two entries of equal degree

Milnor's degree induction rests on one move: if two entries of a symbol are polynomials of the same
degree `d ≥ 1`, divide one by the other.  With `g = c·f + r` and `deg r < d`, the sum-splitting
identity rewrites `{…, c·f, r, …}` in terms of `{…, c·f, g, …}`, `{…, g, r, …}` and `{…, g, g, …}`,
and the last is `{…, g, −1, …}`.  Solving for `{…, f, g, …}` therefore expresses it as a combination
of symbols in which **at most one** of the two slots still has degree `d`.

* `exists_const_mul_add_of_natDegree_eq` : the division of two polynomials of equal degree.
* `twoSlot_polyUnit_reduce` : **the reduction move.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- **Division at equal degrees.**  Two nonzero polynomials of the same degree differ by a constant
multiple up to a remainder of smaller degree. -/
theorem exists_const_mul_add_of_natDegree_eq {f g : Polynomial F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hdeg : g.natDegree = f.natDegree) :
    ∃ c : F, c ≠ 0 ∧ ∃ r : Polynomial F, g = Polynomial.C c * f + r ∧
      (r = 0 ∨ r.natDegree < f.natDegree) := by
  refine ⟨g.leadingCoeff / f.leadingCoeff, div_ne_zero (leadingCoeff_ne_zero.2 hg)
    (leadingCoeff_ne_zero.2 hf), g - Polynomial.C (g.leadingCoeff / f.leadingCoeff) * f,
    by ring, ?_⟩
  set c : F := g.leadingCoeff / f.leadingCoeff with hc
  have hcne : c ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.2 hg) (leadingCoeff_ne_zero.2 hf)
  have hCf : Polynomial.C c * f ≠ 0 := mul_ne_zero (by simpa using hcne) hf
  have hdegCf : (Polynomial.C c * f).degree = g.degree := by
    rw [degree_mul, degree_C hcne, zero_add,
      degree_eq_natDegree hf, degree_eq_natDegree hg, hdeg]
  have hlc : g.leadingCoeff = (Polynomial.C c * f).leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C, hc, div_mul_cancel₀]
    exact leadingCoeff_ne_zero.2 hf
  have hlt : (g - Polynomial.C c * f).degree < g.degree := degree_sub_lt hdegCf.symm hg hlc
  by_cases hr : g - Polynomial.C c * f = 0
  · exact Or.inl hr
  · refine Or.inr ?_
    have h1 : (g - Polynomial.C c * f).natDegree < g.natDegree := by
      have := hlt
      rw [degree_eq_natDegree hr, degree_eq_natDegree hg] at this
      exact_mod_cast this
    rw [← hdeg]
    exact h1

/-- A polynomial unit of a product is the product of the polynomial units. -/
theorem polyUnit_mul {p q : Polynomial F} (hp : p ≠ 0) (hq : q ≠ 0) :
    polyUnit (mul_ne_zero hp hq) = polyUnit hp * polyUnit hq := by
  refine Units.ext ?_
  rw [Units.val_mul]
  show algebraMap (Polynomial F) (RatFunc F) (p * q)
    = algebraMap (Polynomial F) (RatFunc F) p * algebraMap (Polynomial F) (RatFunc F) q
  rw [map_mul]

/-- The polynomial unit of `−1` is `−1`. -/
theorem polyUnit_neg_one (h : (-1 : Polynomial F) ≠ 0) : polyUnit h = (-1 : (RatFunc F)ˣ) := by
  refine Units.ext ?_
  show algebraMap (Polynomial F) (RatFunc F) (-1) = _
  rw [map_neg, map_one]
  rfl

/-- The entries of degree at most `d`. -/
def polyDegLe (d : ℕ) (u : (RatFunc F)ˣ) : Prop :=
  ∃ (p : Polynomial F) (hp : p ≠ 0), p.natDegree ≤ d ∧ u = polyUnit hp

/-- The entries of degree below `d`. -/
def polyDegLt (d : ℕ) (u : (RatFunc F)ˣ) : Prop :=
  ∃ (p : Polynomial F) (hp : p ≠ 0), p.natDegree < d ∧ u = polyUnit hp

theorem polyDegLe_of_polyDegLt {d : ℕ} {u : (RatFunc F)ˣ} (h : polyDegLt d u) :
    polyDegLe d u := by
  obtain ⟨p, hp, hlt, hu⟩ := h
  exact ⟨p, hp, le_of_lt hlt, hu⟩

variable {n : ℕ}

/-- The classes of two-slot symbols in which at most one of the two slots has degree exactly `d`. -/
noncomputable def reducedTwoSlot (d : ℕ) (l₁ l₂ : List (RatFunc F)ˣ) (hn : (l₁ ++ l₂).length + 2 = n) :
    AddSubgroup (MilnorKDeg (RatFunc F) n) :=
  AddSubgroup.closure {x | ∃ a b : (RatFunc F)ˣ, polyDegLe d a ∧ polyDegLe d b
    ∧ (polyDegLt d a ∨ polyDegLt d b) ∧ x = twoSlot l₁ l₂ hn a b}

theorem mem_reducedTwoSlot {d : ℕ} {l₁ l₂ : List (RatFunc F)ˣ} {hn : (l₁ ++ l₂).length + 2 = n}
    {a b : (RatFunc F)ˣ} (ha : polyDegLe d a) (hb : polyDegLe d b)
    (h : polyDegLt d a ∨ polyDegLt d b) : twoSlot l₁ l₂ hn a b ∈ reducedTwoSlot d l₁ l₂ hn :=
  AddSubgroup.subset_closure ⟨a, b, ha, hb, h, rfl⟩

/-- **The reduction move.**  Two entries of the same degree `d ≥ 1` can be traded for symbols in
which at most one slot still has degree `d`. -/
theorem twoSlot_polyUnit_reduce {d : ℕ} (hd : 1 ≤ d) (l₁ l₂ : List (RatFunc F)ˣ)
    (hn : (l₁ ++ l₂).length + 2 = n) {f g : Polynomial F} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfd : f.natDegree = d) (hgd : g.natDegree = d) :
    twoSlot l₁ l₂ hn (polyUnit hf) (polyUnit hg) ∈ reducedTwoSlot d l₁ l₂ hn := by
  classical
  obtain ⟨c, hcne, r, hgr, hrdeg⟩ :=
    exists_const_mul_add_of_natDegree_eq hf hg (by rw [hfd, hgd])
  have hCne : (Polynomial.C c : Polynomial F) ≠ 0 := by simpa using hcne
  have hCdeg : (Polynomial.C c).natDegree < d := by
    rw [natDegree_C]
    omega
  have hCf : Polynomial.C c * f ≠ 0 := mul_ne_zero hCne hf
  have hCfdeg : (Polynomial.C c * f).natDegree = d := by
    rw [natDegree_mul hCne hf, natDegree_C, zero_add, hfd]
  have hCfsplit : polyUnit hCf = polyUnit hCne * polyUnit hf := polyUnit_mul hCne hf
  have hneg : (-1 : Polynomial F) ≠ 0 := by
    intro hcon
    exact one_ne_zero (neg_eq_zero.mp hcon)
  have hnegdeg : (-1 : Polynomial F).natDegree < d := by
    have hz : (-1 : Polynomial F).natDegree = 0 := by simp
    omega
  by_cases hr0 : r = 0
  · -- `g = c · f`, so `{f, g} = {f, C c} + {f, −1}`
    have hgeq : polyUnit hg = polyUnit hCne * polyUnit hf := by
      refine Units.ext ?_
      rw [Units.val_mul]
      show algebraMap (Polynomial F) (RatFunc F) g
        = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c)
          * algebraMap (Polynomial F) (RatFunc F) f
      rw [← map_mul, hgr, hr0, add_zero]
    rw [hgeq, twoSlot_mul_right, twoSlot_self]
    refine AddSubgroup.add_mem _ ?_ ?_
    · exact mem_reducedTwoSlot ⟨f, hf, le_of_eq hfd, rfl⟩
        ⟨Polynomial.C c, hCne, le_of_lt hCdeg, rfl⟩
        (Or.inr ⟨Polynomial.C c, hCne, hCdeg, rfl⟩)
    · rw [show (-1 : (RatFunc F)ˣ) = polyUnit hneg from (polyUnit_neg_one hneg).symm]
      exact mem_reducedTwoSlot ⟨f, hf, le_of_eq hfd, rfl⟩
        ⟨(-1 : Polynomial F), hneg, le_of_lt hnegdeg, rfl⟩
        (Or.inr ⟨(-1 : Polynomial F), hneg, hnegdeg, rfl⟩)
  · -- `g = c · f + r` with `deg r < d`
    have hrne : r ≠ 0 := hr0
    have hrlt : r.natDegree < d := by
      rw [← hfd]
      exact hrdeg.resolve_left hr0
    have hsum : ((polyUnit hCf : (RatFunc F)ˣ) : RatFunc F)
        + ((polyUnit hrne : (RatFunc F)ˣ) : RatFunc F)
        = ((polyUnit hg : (RatFunc F)ˣ) : RatFunc F) := by
      show algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c * f)
        + algebraMap (Polynomial F) (RatFunc F) r = algebraMap (Polynomial F) (RatFunc F) g
      rw [← map_add, hgr]
    have hsplit := twoSlot_add_split l₁ l₂ hn (polyUnit hCf) (polyUnit hrne) (polyUnit hg) hsum
    have hself : twoSlot l₁ l₂ hn (polyUnit hg) (polyUnit hg)
        = twoSlot l₁ l₂ hn (polyUnit hg) (-1) := twoSlot_self l₁ l₂ hn _
    have hCfg : twoSlot l₁ l₂ hn (polyUnit hCf) (polyUnit hg)
        = twoSlot l₁ l₂ hn (polyUnit hCne) (polyUnit hg)
          + twoSlot l₁ l₂ hn (polyUnit hf) (polyUnit hg) := by
      rw [hCfsplit, twoSlot_mul_left]
    rw [hself, hCfg] at hsplit
    have hfg : twoSlot l₁ l₂ hn (polyUnit hf) (polyUnit hg)
        = twoSlot l₁ l₂ hn (polyUnit hCf) (polyUnit hrne)
          - twoSlot l₁ l₂ hn (polyUnit hCne) (polyUnit hg)
          - twoSlot l₁ l₂ hn (polyUnit hg) (polyUnit hrne)
          + twoSlot l₁ l₂ hn (polyUnit hg) (-1) := by
      refine sub_eq_zero.mp ?_
      have hrearrange : twoSlot l₁ l₂ hn (polyUnit hf) (polyUnit hg)
          - (twoSlot l₁ l₂ hn (polyUnit hCf) (polyUnit hrne)
            - twoSlot l₁ l₂ hn (polyUnit hCne) (polyUnit hg)
            - twoSlot l₁ l₂ hn (polyUnit hg) (polyUnit hrne)
            + twoSlot l₁ l₂ hn (polyUnit hg) (-1))
          = (twoSlot l₁ l₂ hn (polyUnit hCne) (polyUnit hg)
              + twoSlot l₁ l₂ hn (polyUnit hf) (polyUnit hg)
              + twoSlot l₁ l₂ hn (polyUnit hg) (polyUnit hrne)
              - twoSlot l₁ l₂ hn (polyUnit hg) (-1))
            - twoSlot l₁ l₂ hn (polyUnit hCf) (polyUnit hrne) := by abel
      rw [hrearrange, ← hsplit, sub_self]
    rw [hfg]
    have hCfmem : twoSlot l₁ l₂ hn (polyUnit hCf) (polyUnit hrne) ∈ reducedTwoSlot d l₁ l₂ hn :=
      mem_reducedTwoSlot ⟨Polynomial.C c * f, hCf, le_of_eq hCfdeg, rfl⟩
        ⟨r, hrne, le_of_lt hrlt, rfl⟩ (Or.inr ⟨r, hrne, hrlt, rfl⟩)
    have hCgmem : twoSlot l₁ l₂ hn (polyUnit hCne) (polyUnit hg) ∈ reducedTwoSlot d l₁ l₂ hn :=
      mem_reducedTwoSlot ⟨Polynomial.C c, hCne, le_of_lt hCdeg, rfl⟩
        ⟨g, hg, le_of_eq hgd, rfl⟩ (Or.inl ⟨Polynomial.C c, hCne, hCdeg, rfl⟩)
    have hgrmem : twoSlot l₁ l₂ hn (polyUnit hg) (polyUnit hrne) ∈ reducedTwoSlot d l₁ l₂ hn :=
      mem_reducedTwoSlot ⟨g, hg, le_of_eq hgd, rfl⟩ ⟨r, hrne, le_of_lt hrlt, rfl⟩
        (Or.inr ⟨r, hrne, hrlt, rfl⟩)
    have hgnegmem : twoSlot l₁ l₂ hn (polyUnit hg) (-1) ∈ reducedTwoSlot d l₁ l₂ hn := by
      rw [show (-1 : (RatFunc F)ˣ) = polyUnit hneg from (polyUnit_neg_one hneg).symm]
      exact mem_reducedTwoSlot ⟨g, hg, le_of_eq hgd, rfl⟩
        ⟨(-1 : Polynomial F), hneg, le_of_lt hnegdeg, rfl⟩
        (Or.inr ⟨(-1 : Polynomial F), hneg, hnegdeg, rfl⟩)
    exact AddSubgroup.add_mem _
      (AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ hCfmem hCgmem) hgrmem) hgnegmem

end GaloisForLFunctions.HTGeometry
