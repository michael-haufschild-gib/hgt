import GaloisForLFunctions.HTGeometry.DifferentialOperatorSubmoduleFree
import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreDiagonal

/-!
# A torsion-free quotient of a finite free module over the operator ring is free

Elementary row operations do not move the left row span, and an elementary column operation moves
it by an automorphism of the ambient module, so the diagonal form of
`DifferentialOperatorOreDiagonal` transports the quotient by the row span to a quotient by the span
of a set of coordinate lines.

On a diagonal matrix every nonzero entry `d` is alone in its row and column, so the `j`-coordinate
of every element of the row span lies in `R d`.  If the quotient is torsion-free then `d` has to be
a unit: otherwise the coordinate vector `e_j` is not in the row span while `d · e_j` is, and its
class is a nonzero element killed by `d`.  Once every entry is a unit the row span *is* the span of
its coordinate lines, and the quotient is the free module on the remaining coordinates.

* `rowSpanR`, `rowSpanR_rowAdd`, `rowSpanR_colAdd`, `exists_equiv_of_rowColEquiv`;
* `isUnit_of_torsionFree_quotient` — the diagonal entries are units;
* `free_of_torsionFree_quotient` — **the structure theorem**;
* `free_of_torsionFree_of_fg` — a finitely generated torsion-free module is free.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {ι κ : Type*}

/-- The left row span of a matrix, as a submodule over the operator ring. -/
def rowSpanR (P : ι → κ → DiffOp K) : Submodule (DiffOp K) (κ → DiffOp K) :=
  Submodule.span (DiffOp K) (Set.range P)

theorem row_mem_rowSpanR (P : ι → κ → DiffOp K) (i : ι) : P i ∈ rowSpanR P :=
  Submodule.subset_span ⟨i, rfl⟩

theorem rowSpanR_le {P : ι → κ → DiffOp K} {N : Submodule (DiffOp K) (κ → DiffOp K)}
    (h : ∀ i, P i ∈ N) : rowSpanR P ≤ N :=
  Submodule.span_le.mpr (by rintro w ⟨i, rfl⟩; exact h i)

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
theorem rowSpanR_rowAdd {i₀ k : ι} (hne : i₀ ≠ k) (q : DiffOp K) (P : ι → κ → DiffOp K) :
    rowSpanR (rowAdd i₀ k q P) = rowSpanR P := by
  have hrow0 : rowAdd i₀ k q P i₀ = P i₀ + q • P k := by
    funext j
    rw [rowAdd_apply_self]
    rfl
  have hrowne : ∀ i, i ≠ i₀ → rowAdd i₀ k q P i = P i := by
    intro i hi
    funext j
    exact rowAdd_apply_of_ne k q P j hi
  have hk : rowAdd i₀ k q P k = P k := hrowne k (Ne.symm hne)
  refine le_antisymm (rowSpanR_le fun i => ?_) (rowSpanR_le fun i => ?_)
  · by_cases hi : i = i₀
    · rw [hi, hrow0]
      exact Submodule.add_mem _ (row_mem_rowSpanR P i₀)
        (Submodule.smul_mem _ q (row_mem_rowSpanR P k))
    · rw [hrowne i hi]
      exact row_mem_rowSpanR P i
  · by_cases hi : i = i₀
    · have hback : P i₀ = rowAdd i₀ k q P i₀ - q • rowAdd i₀ k q P k := by
        rw [hrow0, hk]
        abel
      rw [hi, hback]
      exact Submodule.sub_mem _ (row_mem_rowSpanR _ i₀)
        (Submodule.smul_mem _ q (row_mem_rowSpanR _ k))
    · rw [← hrowne i hi]
      exact row_mem_rowSpanR _ i

/-- The column operation on vectors, as a linear map over the operator ring. -/
def colAddVecLinR (j₀ k : κ) (q : DiffOp K) : (κ → DiffOp K) →ₗ[DiffOp K] (κ → DiffOp K) where
  toFun := colAddVec j₀ k q
  map_add' w₁ w₂ := by
    funext j
    by_cases hj : j = j₀
    · subst hj
      have hgoal : (w₁ + w₂) j + (w₁ + w₂) k * q
          = (w₁ j + w₁ k * q) + (w₂ j + w₂ k * q) := by
        simp only [Pi.add_apply, add_mul]
        abel
      rw [colAddVec_apply_self, hgoal, ← colAddVec_apply_self j k q w₁,
        ← colAddVec_apply_self j k q w₂]
      rfl
    · rw [colAddVec_apply_of_ne _ _ _ _ hj]
      show (w₁ + w₂) j = colAddVec j₀ k q w₁ j + colAddVec j₀ k q w₂ j
      rw [colAddVec_apply_of_ne _ _ _ _ hj, colAddVec_apply_of_ne _ _ _ _ hj]
      rfl
  map_smul' r w := by
    funext j
    by_cases hj : j = j₀
    · subst hj
      have hgoal : (r • w) j + (r • w) k * q = r * (w j + w k * q) := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_add, mul_assoc]
      rw [colAddVec_apply_self, hgoal, ← colAddVec_apply_self j k q w]
      rfl
    · rw [colAddVec_apply_of_ne _ _ _ _ hj]
      show (r • w) j = (r • colAddVec j₀ k q w) j
      rw [Pi.smul_apply, Pi.smul_apply, colAddVec_apply_of_ne _ _ _ _ hj]

@[simp] theorem colAddVecLinR_apply (j₀ k : κ) (q : DiffOp K) (w : κ → DiffOp K) :
    colAddVecLinR j₀ k q w = colAddVec j₀ k q w := rfl

/-- The column operation, as an automorphism of the ambient module. -/
def colAddVecEquivR {j₀ k : κ} (h : j₀ ≠ k) (q : DiffOp K) :
    (κ → DiffOp K) ≃ₗ[DiffOp K] (κ → DiffOp K) where
  toLinearMap := colAddVecLinR j₀ k q
  invFun := colAddVec j₀ k (-q)
  left_inv w := colAddVec_cancel h q w
  right_inv w := by simpa using colAddVec_cancel h (-q) w

omit [DecidableEq ι] in
theorem rowSpanR_colAdd {j₀ k : κ} (h : j₀ ≠ k) (q : DiffOp K) (P : ι → κ → DiffOp K) :
    rowSpanR (colAdd j₀ k q P) =
      Submodule.map (colAddVecEquivR h q).toLinearMap (rowSpanR P) := by
  have hrows : (fun i => colAdd j₀ k q P i) = fun i => colAddVec j₀ k q (P i) := by
    funext i j
    rfl
  rw [rowSpanR, rowSpanR, Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  exact congrArg Set.range hrows

/-- **Row and column operations move the row span by an automorphism of the ambient module.** -/
theorem exists_equiv_of_rowColEquiv {P P' : ι → κ → DiffOp K} (h : RowColEquiv P P') :
    ∃ e : (κ → DiffOp K) ≃ₗ[DiffOp K] (κ → DiffOp K),
      Submodule.map e.toLinearMap (rowSpanR P) = rowSpanR P' := by
  induction h with
  | refl => exact ⟨LinearEquiv.refl _ _, by simp⟩
  | tail _ hstep ih =>
      obtain ⟨e, he⟩ := ih
      rcases hstep with ⟨i₀, k, q, hne, rfl⟩ | ⟨j₀, k, q, hne, rfl⟩
      · exact ⟨e, by rw [he, rowSpanR_rowAdd hne]⟩
      · refine ⟨e.trans (colAddVecEquivR hne q), ?_⟩
        rw [rowSpanR_colAdd hne, ← he, ← Submodule.map_comp]
        rfl

/-- The vectors whose `j`-coordinate lies in the left ideal generated by an entry. -/
def coordIdeal (P : ι → κ → DiffOp K) (i : ι) (j : κ) : Submodule (DiffOp K) (κ → DiffOp K) where
  carrier := {w : κ → DiffOp K | ∃ r : DiffOp K, w j = r * P i j}
  add_mem' := by
    rintro a b ⟨ra, hra⟩ ⟨rb, hrb⟩
    refine ⟨ra + rb, ?_⟩
    show a j + b j = (ra + rb) * P i j
    rw [hra, hrb, add_mul]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨ra, hra⟩
    refine ⟨c * ra, ?_⟩
    show c * a j = c * ra * P i j
    rw [hra, mul_assoc]

omit [DecidableEq κ] in
/-- Every element of the row span of a diagonal matrix has its `j`-coordinate in the left ideal of
the entry sitting in that column. -/
theorem exists_mul_of_mem_rowSpanR_diagonalized {P : ι → κ → DiffOp K} (hdiag : Diagonalized P)
    {i : ι} {j : κ} (hij : P i j ≠ 0) {w : κ → DiffOp K} (hw : w ∈ rowSpanR P) :
    ∃ r : DiffOp K, w j = r * P i j := by
  refine rowSpanR_le (N := coordIdeal P i j) (fun i' => ?_) hw
  by_cases hii : i' = i
  · exact ⟨1, by rw [hii, one_mul]⟩
  · exact ⟨0, by rw [(hdiag i j hij).1 i' hii, zero_mul]⟩

omit [DecidableEq ι] in
/-- A row of a diagonal matrix is a multiple of a coordinate vector. -/
theorem row_eq_smul_single {P : ι → κ → DiffOp K} (hdiag : Diagonalized P)
    {i : ι} {j : κ} (hij : P i j ≠ 0) : P i = (P i j) • (Pi.single j 1 : κ → DiffOp K) := by
  funext j'
  by_cases hj : j' = j
  · rw [hj]
    show P i j = P i j * (Pi.single j (1 : DiffOp K) : κ → DiffOp K) j
    rw [Pi.single_eq_same, mul_one]
  · rw [(hdiag i j hij).2 j' hj]
    show 0 = P i j * (Pi.single j (1 : DiffOp K) : κ → DiffOp K) j'
    rw [Pi.single_eq_of_ne hj, mul_zero]

/-- **A torsion-free quotient forces the diagonal entries to be units.** -/
theorem isUnit_of_torsionFree_quotient {P : ι → κ → DiffOp K} (hdiag : Diagonalized P)
    (htf : ∀ (r : DiffOp K) (x : (κ → DiffOp K) ⧸ rowSpanR P), r ≠ 0 → r • x = 0 → x = 0)
    {i : ι} {j : κ} (hij : P i j ≠ 0) : IsUnit (P i j) := by
  have hmem : (P i j) • (Pi.single j 1 : κ → DiffOp K) ∈ rowSpanR P := by
    rw [← row_eq_smul_single hdiag hij]
    exact row_mem_rowSpanR P i
  have hquot : (P i j) •
      (Submodule.Quotient.mk (Pi.single j 1 : κ → DiffOp K) :
        (κ → DiffOp K) ⧸ rowSpanR P) = 0 := by
    rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hmem
  have hejmem : (Pi.single j 1 : κ → DiffOp K) ∈ rowSpanR P :=
    (Submodule.Quotient.mk_eq_zero _).mp (htf _ _ hij hquot)
  obtain ⟨r, hr⟩ := exists_mul_of_mem_rowSpanR_diagonalized hdiag hij hejmem
  have hejj : (Pi.single j 1 : κ → DiffOp K) j = 1 := by simp
  have hone : r * P i j = 1 := by rw [← hr, hejj]
  have hcancel : (P i j * r - 1) * P i j = 0 := by
    rw [sub_mul, one_mul, mul_assoc, hone, mul_one, sub_self]
  have hother : P i j * r = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_right hij)
  exact ⟨⟨P i j, r, hother, hone⟩, rfl⟩


open Classical in
/-- The columns that carry a nonzero entry. -/
def hitCols [Fintype κ] (P : ι → κ → DiffOp K) : Finset κ :=
  Finset.univ.filter (fun j => ∃ i, P i j ≠ 0)

omit [DecidableEq ι] [DecidableEq κ] in
theorem mem_hitCols [Fintype κ] {P : ι → κ → DiffOp K} {j : κ} :
    j ∈ hitCols P ↔ ∃ i, P i j ≠ 0 := by
  classical
  rw [hitCols, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ j, h⟩⟩

omit [DecidableEq ι] in
/-- **With unit entries the row span of a diagonal matrix is the span of its coordinate lines.** -/
theorem rowSpanR_eq_coordSupport [Fintype ι] [Fintype κ] {P : ι → κ → DiffOp K}
    (hdiag : Diagonalized P) (hunit : ∀ i j, P i j ≠ 0 → IsUnit (P i j)) :
    rowSpanR P = coordSupport (hitCols P) := by
  classical
  refine le_antisymm (rowSpanR_le fun i => ?_) ?_
  · intro j hj
    by_contra hne
    exact hj (mem_hitCols.mpr ⟨i, hne⟩)
  · intro w hw
    have hsum : w = ∑ j : κ, (Pi.single j (w j) : κ → DiffOp K) :=
      (Finset.univ_sum_single w).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j ∈ hitCols P
    · obtain ⟨i, hi⟩ := mem_hitCols.mp hj
      obtain ⟨u, hu⟩ := hunit i j hi
      have hrow : P i = (P i j) • (Pi.single j 1 : κ → DiffOp K) := row_eq_smul_single hdiag hi
      have hval : (w j * (↑u⁻¹ : DiffOp K)) • P i = (Pi.single j (w j) : κ → DiffOp K) := by
        rw [hrow, smul_smul]
        have hcancel : w j * (↑u⁻¹ : DiffOp K) * P i j = w j := by
          rw [← hu, mul_assoc, Units.inv_mul, mul_one]
        rw [hcancel]
        funext j'
        by_cases hjj : j' = j
        · rw [hjj]
          show w j * (Pi.single j (1 : DiffOp K) : κ → DiffOp K) j = _
          rw [Pi.single_eq_same, mul_one, Pi.single_eq_same]
        · show w j * (Pi.single j (1 : DiffOp K) : κ → DiffOp K) j' = _
          rw [Pi.single_eq_of_ne hjj, mul_zero, Pi.single_eq_of_ne hjj]
      rw [← hval]
      exact Submodule.smul_mem _ _ (row_mem_rowSpanR P i)
    · have hzero : w j = 0 := hw j hj
      rw [hzero]
      simp

/-- The quotient by the span of a set of coordinate lines is free. -/
theorem free_quotient_coordSupport [Fintype κ] (C : Finset κ) :
    Module.Free (DiffOp K) ((κ → DiffOp K) ⧸ coordSupport (K := K) C) := by
  classical
  set res : (κ → DiffOp K) →ₗ[DiffOp K] ({j : κ // j ∉ C} → DiffOp K) :=
    { toFun := fun w j => w j.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } with hres
  have hker : LinearMap.ker res = coordSupport (K := K) C := by
    ext w
    constructor
    · intro hw j hj
      exact congrFun hw ⟨j, hj⟩
    · intro hw
      funext j
      exact hw j.1 j.2
  have hsurj : Function.Surjective res := by
    intro u
    refine ⟨fun j => if hj : j ∈ C then 0 else u ⟨j, hj⟩, ?_⟩
    funext j
    show (if hj : j.1 ∈ C then (0 : DiffOp K) else u ⟨j.1, hj⟩) = u j
    rw [dif_neg j.2]
  have hequiv : ((κ → DiffOp K) ⧸ coordSupport (K := K) C)
      ≃ₗ[DiffOp K] ({j : κ // j ∉ C} → DiffOp K) := by
    rw [← hker]
    exact res.quotKerEquivOfSurjective hsurj
  exact Module.Free.of_equiv hequiv.symm

/-- **A torsion-free quotient of a finite free module over the operator ring is free.** -/
theorem free_of_torsionFree_quotient [Fintype κ] (N : Submodule (DiffOp K) (κ → DiffOp K))
    (htf : ∀ (r : DiffOp K) (x : (κ → DiffOp K) ⧸ N), r ≠ 0 → r • x = 0 → x = 0) :
    Module.Free (DiffOp K) ((κ → DiffOp K) ⧸ N) := by
  classical
  obtain ⟨n, v, _, _, hspan⟩ := exists_basis_of_submodule N
  have hNrow : N = rowSpanR v := hspan.symm
  obtain ⟨P', hequivPP', hdiag⟩ := exists_diagonalized v
  obtain ⟨e, he⟩ := exists_equiv_of_rowColEquiv hequivPP'
  have hmap : Submodule.map e.toLinearMap N = rowSpanR P' := by rw [hNrow]; exact he
  have hq : ((κ → DiffOp K) ⧸ N) ≃ₗ[DiffOp K] ((κ → DiffOp K) ⧸ rowSpanR P') :=
    Submodule.Quotient.equiv N (rowSpanR P') e hmap
  have htf' : ∀ (r : DiffOp K) (x : (κ → DiffOp K) ⧸ rowSpanR P'), r ≠ 0 → r • x = 0 → x = 0 := by
    intro r x hr hx
    have hpre : r • hq.symm x = 0 := by
      rw [← map_smul, hx, map_zero]
    have := htf r _ hr hpre
    have hxx := congrArg hq this
    rwa [LinearEquiv.apply_symm_apply, map_zero] at hxx
  have hunit : ∀ i j, P' i j ≠ 0 → IsUnit (P' i j) := fun i j hij =>
    isUnit_of_torsionFree_quotient hdiag htf' hij
  have hcoord : rowSpanR P' = coordSupport (hitCols P') := rowSpanR_eq_coordSupport hdiag hunit
  have hfree : Module.Free (DiffOp K) ((κ → DiffOp K) ⧸ rowSpanR P') := by
    rw [hcoord]
    exact free_quotient_coordSupport _
  exact Module.Free.of_equiv hq.symm


/-- **A finitely generated torsion-free module over the operator ring is free.**  This is the
structure theorem in the form the Kähler module uses: `Ω[K⁄C]` is generated over `K[∂;δ]` by the
differentials of a differential generating set, and `M_K = Ω/Tor` is torsion-free. -/
theorem free_of_torsionFree_of_fg {M : Type*} [AddCommGroup M] [Module (DiffOp K) M]
    {n : ℕ} (g : Fin n → M) (hspan : Submodule.span (DiffOp K) (Set.range g) = ⊤)
    (htf : ∀ (r : DiffOp K) (x : M), r ≠ 0 → r • x = 0 → x = 0) :
    Module.Free (DiffOp K) M := by
  classical
  set φ : (Fin n → DiffOp K) →ₗ[DiffOp K] M :=
    { toFun := fun c => ∑ i, c i • g i
      map_add' := by
        intro c d
        simp only [Pi.add_apply, add_smul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro r c
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (Finset.smul_sum).symm } with hφ
  have hsurj : Function.Surjective φ := by
    intro x
    have hx : x ∈ Submodule.span (DiffOp K) (Set.range g) := by
      rw [hspan]
      trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (DiffOp K)).mp hx
    exact ⟨c, hc⟩
  have hequiv : ((Fin n → DiffOp K) ⧸ LinearMap.ker φ) ≃ₗ[DiffOp K] M :=
    φ.quotKerEquivOfSurjective hsurj
  have htf' : ∀ (r : DiffOp K) (x : (Fin n → DiffOp K) ⧸ LinearMap.ker φ),
      r ≠ 0 → r • x = 0 → x = 0 := by
    intro r x hr hx
    have himg : r • hequiv x = 0 := by rw [← map_smul, hx, map_zero]
    exact hequiv.map_eq_zero_iff.mp (htf r _ hr himg)
  haveI := free_of_torsionFree_quotient (LinearMap.ker φ) htf'
  exact Module.Free.of_equiv hequiv


end

end DiffOp

end GaloisForLFunctions.HTGeometry
