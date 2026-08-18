import GaloisForLFunctions.HTGeometry.MilnorSectionMap
import GaloisForLFunctions.HTGeometry.MilnorFiltrationReduction

/-!
# Splitting the leading entry of a symbol into factors

Multilinearity in the first slot turns a symbol whose leading entry is a product into the sum of the
symbols of the factors.  Applied to the factorisation of a polynomial into irreducibles, this is
what isolates the single irreducible factor of top degree in Milnor's degree induction.

* `nzProd`, `nzProd_ne_zero` : the product of a list of nonzero polynomials.
* `class_cons_nzProd` : **the leading entry splits into its factors.**
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {F : Type*} [Field F]

/-- The product of a list of nonzero polynomials. -/
noncomputable def nzProd (ps : List (NZPoly F)) : Polynomial F := (ps.map Subtype.val).prod

theorem nzProd_ne_zero (ps : List (NZPoly F)) : nzProd ps ≠ 0 := by
  induction ps with
  | nil => simp [nzProd]
  | cons p t ih =>
      rw [nzProd, List.map_cons, List.prod_cons]
      exact mul_ne_zero p.2 ih

@[simp]
theorem nzProd_nil : nzProd ([] : List (NZPoly F)) = 1 := by simp [nzProd]

theorem nzProd_cons (p : NZPoly F) (t : List (NZPoly F)) :
    nzProd (p :: t) = p.1 * nzProd t := by
  rw [nzProd, List.map_cons, List.prod_cons, nzProd]

theorem polyUnit_one (h : (1 : Polynomial F) ≠ 0) : polyUnit h = (1 : (RatFunc F)ˣ) := by
  refine Units.ext ?_
  show algebraMap (Polynomial F) (RatFunc F) 1 = _
  rw [map_one]
  rfl

/-- **The leading entry of a symbol splits into its factors.** -/
theorem class_cons_nzProd {n : ℕ} (l : List (RatFunc F)ˣ) (hlen : l.length = n) :
    ∀ ps : List (NZPoly F),
      milnorClassDeg (RatFunc F) (n + 1)
          ⟨polyUnit (nzProd_ne_zero ps) :: l, by simp [hlen]⟩
        = (ps.map (fun p => milnorClassDeg (RatFunc F) (n + 1)
            ⟨polyUnit p.2 :: l, by simp [hlen]⟩)).sum := by
  intro ps
  induction ps with
  | nil =>
      rw [List.map_nil, List.sum_nil]
      have hone : polyUnit (nzProd_ne_zero ([] : List (NZPoly F))) = (1 : (RatFunc F)ˣ) := by
        refine Units.ext ?_
        show algebraMap (Polynomial F) (RatFunc F) (nzProd ([] : List (NZPoly F))) = _
        rw [nzProd_nil, map_one]
        rfl
      rw [hone]
      exact milnorClassDeg_one_of_eq (K := RatFunc F) [] l rfl _
  | cons p t ih =>
      have hsplit : polyUnit (nzProd_ne_zero (p :: t))
          = polyUnit p.2 * polyUnit (nzProd_ne_zero t) := by
        refine Units.ext ?_
        rw [Units.val_mul]
        show algebraMap (Polynomial F) (RatFunc F) (nzProd (p :: t))
          = algebraMap (Polynomial F) (RatFunc F) p.1
            * algebraMap (Polynomial F) (RatFunc F) (nzProd t)
        rw [nzProd_cons, map_mul]
      rw [List.map_cons, List.sum_cons, ← ih]
      have hmul := milnorClassDeg_mul_of_eq (F := RatFunc F) (n := n + 1)
        (polyUnit p.2) (polyUnit (nzProd_ne_zero t)) [] l
        (Lab := polyUnit (nzProd_ne_zero (p :: t)) :: l)
        (La := polyUnit p.2 :: l) (Lb := polyUnit (nzProd_ne_zero t) :: l)
        (by rw [hsplit]; simp) (by simp) (by simp)
        (by simp [hlen]) (by simp [hlen]) (by simp [hlen])
      exact hmul

/-- The range of Milnor's section at a place of degree `d`. -/
noncomputable def sectionRange (d n : ℕ) (hd : 1 ≤ d)
    (p : {q : Polynomial F // Irreducible q ∧ q.natDegree = d ∧ q.Monic}) :
    AddSubgroup (MilnorKDeg (RatFunc F) (n + 1) ⧸ degreeFiltration (F := F) (d - 1) (n + 1)) :=
  (sectionMapAt p.2.1 (by rw [p.2.2.1]; exact hd) (by rw [p.2.2.1]) n).range

/-- A symbol of polynomial units all of degree below `d` lies in the previous stage. -/
theorem class_cons_mem_pred {d n : ℕ} {c : Polynomial F} (hc : c ≠ 0) (hcd : c.natDegree < d)
    (l : List (RatFunc F)ˣ) (hl : ∀ a ∈ l, polyDegLt (F := F) d a) (hlen : l.length = n) :
    milnorClassDeg (RatFunc F) (n + 1) ⟨polyUnit hc :: l, by simp [hlen]⟩
      ∈ degreeFiltration (F := F) (d - 1) (n + 1) := by
  refine AddSubgroup.subset_closure ⟨⟨polyUnit hc :: l, by simp [hlen]⟩, ?_, rfl⟩
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha'
  · exact ⟨c, hc, by omega, rfl⟩
  · obtain ⟨p, hp, hpd, rfl⟩ := hl a ha'
    exact ⟨p, hp, by omega, rfl⟩

/-- **A reduced generator lands in the sum of the ranges of the sections.**  Pick an irreducible
factor of the leading entry: if it has degree `d` the cofactor is a constant and the generator is a
section symbol up to a term of the previous stage; otherwise both factors have degree below `d` and
the whole generator is of the previous stage. -/
theorem mk_class_cons_mem_iSup {d n : ℕ} (hd : 1 ≤ d) {b : Polynomial F} (hb : b ≠ 0)
    (hbd : b.natDegree ≤ d) (l : List (RatFunc F)ˣ)
    (hl : ∀ a ∈ l, polyDegLt (F := F) d a) (hlen : l.length = n) :
    (QuotientAddGroup.mk' (degreeFiltration (F := F) (d - 1) (n + 1)))
        (milnorClassDeg (RatFunc F) (n + 1) ⟨polyUnit hb :: l, by simp [hlen]⟩)
      ∈ ⨆ p : {q : Polynomial F // Irreducible q ∧ q.natDegree = d ∧ q.Monic},
          sectionRange (F := F) d n hd p := by
  classical
  by_cases hbdeg : b.natDegree < d
  · have hmem := class_cons_mem_pred hb hbdeg l hl hlen
    rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff _).2 hmem]
    exact zero_mem _
  · have hbeq : b.natDegree = d := le_antisymm hbd (not_lt.1 hbdeg)
    have hbnu : ¬ IsUnit b := by
      intro hcon
      have := Polynomial.natDegree_eq_zero_of_isUnit hcon
      omega
    obtain ⟨π, hπ, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hbnu hb
    obtain ⟨c, hc⟩ := hdvd
    have hcne : c ≠ 0 := by
      intro hcon
      rw [hcon, mul_zero] at hc
      exact hb hc
    have hπne : π ≠ 0 := hπ.ne_zero
    have hdegsum : π.natDegree + c.natDegree = d := by
      rw [← hbeq, hc, Polynomial.natDegree_mul hπne hcne]
    have hπpos : 1 ≤ π.natDegree := by
      rcases Nat.eq_zero_or_pos π.natDegree with h0 | hpos
      · exact absurd (Polynomial.isUnit_iff_degree_eq_zero.2 (by
          rw [Polynomial.degree_eq_natDegree hπne, h0]; rfl)) hπ.not_isUnit
      · exact hpos
    have hsplit : polyUnit hb = polyUnit hπne * polyUnit hcne := by
      refine Units.ext ?_
      rw [Units.val_mul]
      show algebraMap (Polynomial F) (RatFunc F) b
        = algebraMap (Polynomial F) (RatFunc F) π * algebraMap (Polynomial F) (RatFunc F) c
      rw [← map_mul, hc]
    have hmul := milnorClassDeg_mul_of_eq (F := RatFunc F) (n := n + 1)
      (polyUnit hπne) (polyUnit hcne) [] l
      (Lab := polyUnit hb :: l) (La := polyUnit hπne :: l) (Lb := polyUnit hcne :: l)
      (by rw [hsplit]; simp) (by simp) (by simp)
      (by simp [hlen]) (by simp [hlen]) (by simp [hlen])
    have hzero : ∀ y ∈ degreeFiltration (F := F) (d - 1) (n + 1),
        (QuotientAddGroup.mk' (degreeFiltration (F := F) (d - 1) (n + 1))) y = 0 := by
      intro y hy
      rw [QuotientAddGroup.mk'_apply]
      exact (QuotientAddGroup.eq_zero_iff y).2 hy
    rw [hmul, map_add]
    by_cases hπd : π.natDegree = d
    · have hcdeg : c.natDegree < d := by omega
      rw [hzero _ (class_cons_mem_pred hcne hcdeg l hl hlen), add_zero]
      -- normalise `π` to be monic, at the cost of a constant entry
      have hlc : π.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hπne
      have hCinv : (Polynomial.C π.leadingCoeff⁻¹ : Polynomial F) ≠ 0 := by
        simpa using inv_ne_zero hlc
      have hClc : (Polynomial.C π.leadingCoeff : Polynomial F) ≠ 0 := by
        simpa using hlc
      have hπ₀ne : (Polynomial.C π.leadingCoeff⁻¹ * π) ≠ 0 := mul_ne_zero hCinv hπne
      have hunit : IsUnit (Polynomial.C π.leadingCoeff⁻¹ : Polynomial F) :=
        Polynomial.isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hlc))
      have hassoc : Associated π (Polynomial.C π.leadingCoeff⁻¹ * π) :=
        ⟨hunit.unit, by rw [mul_comm]; rfl⟩
      have hπ₀irr : Irreducible (Polynomial.C π.leadingCoeff⁻¹ * π) := hassoc.irreducible hπ
      have hπ₀deg : (Polynomial.C π.leadingCoeff⁻¹ * π).natDegree = d := by
        rw [Polynomial.natDegree_mul hCinv hπne, Polynomial.natDegree_C, zero_add, hπd]
      have hπ₀monic : (Polynomial.C π.leadingCoeff⁻¹ * π).Monic := by
        have hlead : (Polynomial.C π.leadingCoeff⁻¹ * π).leadingCoeff = 1 := by
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, inv_mul_cancel₀ hlc]
        exact hlead
      have hπsplit : polyUnit hπne = polyUnit hClc * polyUnit hπ₀ne := by
        refine Units.ext ?_
        rw [Units.val_mul]
        show algebraMap (Polynomial F) (RatFunc F) π
          = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C π.leadingCoeff)
            * algebraMap (Polynomial F) (RatFunc F) (Polynomial.C π.leadingCoeff⁻¹ * π)
        rw [← map_mul, ← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc, Polynomial.C_1,
          one_mul]
      have hmul2 := milnorClassDeg_mul_of_eq (F := RatFunc F) (n := n + 1)
        (polyUnit hClc) (polyUnit hπ₀ne) [] l
        (Lab := polyUnit hπne :: l) (La := polyUnit hClc :: l) (Lb := polyUnit hπ₀ne :: l)
        (by rw [hπsplit]; simp) (by simp) (by simp)
        (by simp [hlen]) (by simp [hlen]) (by simp [hlen])
      have hCdeg : (Polynomial.C π.leadingCoeff : Polynomial F).natDegree < d := by
        rw [Polynomial.natDegree_C]; omega
      rw [hmul2, map_add, hzero _ (class_cons_mem_pred hClc hCdeg l hl hlen), zero_add]
      refine AddSubgroup.mem_iSup_of_mem ⟨_, hπ₀irr, hπ₀deg, hπ₀monic⟩ ?_
      have hlπ : ∀ a ∈ l, polyDegLt (F := F)
          (Polynomial.C π.leadingCoeff⁻¹ * π).natDegree a := by
        intro a ha
        obtain ⟨p, hp, hpd, hap⟩ := hl a ha
        exact ⟨p, hp, by omega, hap⟩
      rw [class_cons_eq_sectionSymbol hπ₀irr l hlπ hlen (by simp [hlen]), map_zsmul]
      refine AddSubgroup.zsmul_mem _ ?_ _
      refine ⟨milnorClassDeg (polyResidueField hπ₀irr) n
        ⟨l.map (polyResidueData hπ₀irr).residueUnit, by rw [List.length_map]; exact hlen⟩, ?_⟩
      rw [sectionMapAt_class, QuotientAddGroup.mk'_apply]
    · have hπdeg : π.natDegree < d := by omega
      have hcdeg : c.natDegree < d := by omega
      rw [hzero _ (class_cons_mem_pred hπne hπdeg l hl hlen),
        hzero _ (class_cons_mem_pred hcne hcdeg l hl hlen), add_zero]
      exact zero_mem _

/-- **The image of `L_d` in `K_{n+1}^M(F(t))/L_{d−1}` is the sum of the ranges of the sections.** -/
theorem degreeFiltration_map_le_iSup {d n : ℕ} (hd : 1 ≤ d) :
    AddSubgroup.map (QuotientAddGroup.mk' (degreeFiltration (F := F) (d - 1) (n + 1)))
        (degreeFiltration (F := F) d (n + 1))
      ≤ ⨆ p : {q : Polynomial F // Irreducible q ∧ q.natDegree = d ∧ q.Monic},
          sectionRange (F := F) d n hd p := by
  classical
  rw [AddSubgroup.map_le_iff_le_comap]
  refine le_trans (degreeFiltration_le_reducedFiltration hd (Nat.succ_le_succ (Nat.zero_le n))) ?_
  refine (AddSubgroup.closure_le _).2 ?_
  rintro x ⟨b, l, h, hb, hl, rfl⟩
  obtain ⟨p, hp, hple, rfl⟩ := hb
  have hlen : l.length = n := by
    simp only [List.length_cons] at h
    omega
  exact mk_class_cons_mem_iSup hd hp hple l hl hlen

end GaloisForLFunctions.HTGeometry
