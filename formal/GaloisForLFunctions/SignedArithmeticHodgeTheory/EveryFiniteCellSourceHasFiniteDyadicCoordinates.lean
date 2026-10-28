import GaloisForLFunctions.SignedArithmeticHodgeTheory.BalancedCellDetailsFormTheWanderingBasis

/-!
# Exact finite coordinates before source completion

The inverse cell-pair rotation and induction on the integer label put every
finite cell source in the algebraic span of actual weighted dyadic generators.
Their orthonormality then supplies faithful Hilbert coordinates. No unbounded
form is passed through an infinite expansion in the finite-source theorem.
-/

noncomputable section

open RHTower Finset

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "W" => logCellShift 2
local notation "e" => fun n : ℕ+ => (lp.single 2 n (1 : ℂ) : CellH)

/-- The actual cell generator at a specified dyadic level. -/
def logCellDyadicOrbit (i : ℕ × Option ℕ+) : CellH :=
  (W ^ i.1) (logCellDyadicGenerator i.2)

/-- Finite linear combinations of the actual dyadic generators. -/
def logCellDyadicFiniteSpan : Submodule ℂ CellH :=
  Submodule.span ℂ (Set.range logCellDyadicOrbit)

/-- The inverse weighted rotation recovers the left cell exactly. -/
theorem dyadicLeftCell_eq_coarse_add_detail (a : ℕ+) :
    e (dyadicLeftCell a) = (dyadicLeftWeight a : ℂ) • W (e a) +
      (dyadicRightWeight a : ℂ) • logCellDyadicDetail a := by
  have hu : (dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2 = 1 := by
    exact_mod_cast dyadicCellWeights_sq a
  rw [logCellDyadic_single, logCellDyadicDetail]
  refine lp.ext (funext fun m => ?_)
  simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ((dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2) *
        (e (dyadicLeftCell a)) m := by rw [hu, one_mul]
    _ = _ := by ring

/-- The inverse weighted rotation recovers the right cell exactly. -/
theorem dyadicRightCell_eq_coarse_sub_detail (a : ℕ+) :
    e (dyadicRightCell a) = (dyadicRightWeight a : ℂ) • W (e a) -
      (dyadicLeftWeight a : ℂ) • logCellDyadicDetail a := by
  have hu : (dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2 = 1 := by
    exact_mod_cast dyadicCellWeights_sq a
  rw [logCellDyadic_single, logCellDyadicDetail]
  refine lp.ext (funext fun m => ?_)
  simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ((dyadicLeftWeight a : ℂ) ^ 2 + (dyadicRightWeight a : ℂ) ^ 2) *
        (e (dyadicRightCell a)) m := by rw [hu, one_mul]
    _ = _ := by ring

private theorem generator_mem_finiteSpan (i : Option ℕ+) :
    logCellDyadicGenerator i ∈ logCellDyadicFiniteSpan := by
  have h : logCellDyadicOrbit (0, i) ∈ logCellDyadicFiniteSpan :=
    Submodule.subset_span ⟨(0, i), rfl⟩
  exact h

/-- A finite dyadic expansion stays finite after one actual scale shift. -/
theorem logCellDyadic_shift_mem_finiteSpan {x : CellH}
    (hx : x ∈ logCellDyadicFiniteSpan) : W x ∈ logCellDyadicFiniteSpan := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    obtain ⟨⟨j, i⟩, rfl⟩ := hy
    have he : W (logCellDyadicOrbit (j, i)) = logCellDyadicOrbit (j + 1, i) := by
      simp only [logCellDyadicOrbit, pow_succ', mul_apply_eq_comp]
    rw [he]
    exact Submodule.subset_span ⟨(j + 1, i), rfl⟩
  · rw [map_zero]
    exact logCellDyadicFiniteSpan.zero_mem
  · intro y z _ _ hy hz
    rw [map_add]
    exact logCellDyadicFiniteSpan.add_mem hy hz
  · intro c y _ hy
    rw [map_smul]
    exact logCellDyadicFiniteSpan.smul_mem c hy

/-- Every single complete cell has an exact finite weighted dyadic expansion. -/
theorem single_mem_logCellDyadicFiniteSpan (m : ℕ+) :
    e m ∈ logCellDyadicFiniteSpan := by
  have h : ∀ n : ℕ, ∀ hn : 0 < n, e ⟨n, hn⟩ ∈ logCellDyadicFiniteSpan := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst n
        exact generator_mem_finiteSpan none
      have hn2 : 2 ≤ n := by omega
      let a : ℕ+ := ⟨n / 2, by omega⟩
      have hparent : n / 2 < n := by omega
      have ha : e a ∈ logCellDyadicFiniteSpan := ih (n / 2) hparent (by omega)
      have hc := logCellDyadic_shift_mem_finiteSpan ha
      have hd : logCellDyadicDetail a ∈ logCellDyadicFiniteSpan := generator_mem_finiteSpan (some a)
      have hcases : n = 2 * (a : ℕ) ∨ n = 2 * (a : ℕ) + 1 := by
        change n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1
        omega
      rcases hcases with he | he
      · have hi : (⟨n, hn⟩ : ℕ+) = dyadicLeftCell a := PNat.eq he
        rw [hi, dyadicLeftCell_eq_coarse_add_detail]
        exact logCellDyadicFiniteSpan.add_mem
          (logCellDyadicFiniteSpan.smul_mem _ hc) (logCellDyadicFiniteSpan.smul_mem _ hd)
      · have hi : (⟨n, hn⟩ : ℕ+) = dyadicRightCell a := PNat.eq he
        rw [hi, dyadicRightCell_eq_coarse_sub_detail]
        exact logCellDyadicFiniteSpan.sub_mem
          (logCellDyadicFiniteSpan.smul_mem _ hc) (logCellDyadicFiniteSpan.smul_mem _ hd)
  exact h m m.pos

/-- Compact finite cell sources need only finitely many actual dyadic coordinates. -/
theorem exists_finite_logCellDyadic_expansion (S : Finset ℕ+) (c : ℕ+ → ℂ) :
    ∃ d : (ℕ × Option ℕ+) →₀ ℂ,
      (d.sum fun i a => a • logCellDyadicOrbit i) = ∑ n ∈ S, c n • e n := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  exact logCellDyadicFiniteSpan.sum_mem fun n _ =>
    logCellDyadicFiniteSpan.smul_mem _ (single_mem_logCellDyadicFiniteSpan n)

/-- All levels and all explicit generators form one orthonormal family. -/
theorem orthonormal_logCellDyadicOrbit : Orthonormal ℂ logCellDyadicOrbit := by
  classical
  apply orthonormal_iff_ite.mpr
  rintro ⟨j, i⟩ ⟨k, l⟩
  rw [logCellDyadicOrbit, logCellDyadicOrbit,
    inner_logCellDyadic_wandering (logCellDyadicGenerator_mem i) (logCellDyadicGenerator_mem l),
    orthonormal_iff_ite.mp orthonormal_logCellDyadicGenerator i l]
  by_cases hjk : j = k
  · subst k
    simp only [ite_true, Prod.mk.injEq, true_and]
  · simp only [Prod.mk.injEq, hjk, false_and, if_false]

/-- Finite-source exhaustion yields the complete Hilbert coordinate space. -/
theorem logCellDyadicFiniteSpan_dense : logCellDyadicFiniteSpan.topologicalClosure = ⊤ := by
  have hspan : Submodule.span ℂ (Set.range e) ≤ logCellDyadicFiniteSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact single_mem_logCellDyadicFiniteSpan n
  have h := Submodule.topologicalClosure_mono hspan
  have hfull : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤ := by
    have he : ⇑(HilbertSchmidt.lpBasis ℕ+) = e := by
      funext n
      exact HilbertSchmidt.lpBasis_apply n
    simpa only [he] using (HilbertSchmidt.lpBasis ℕ+).dense_span
  rw [hfull] at h
  exact le_antisymm le_top h

/-- Faithful Hilbert coordinates indexed by dyadic level and arithmetic generator. -/
def logCellDyadicBasis : HilbertBasis (ℕ × Option ℕ+) ℂ CellH :=
  HilbertBasis.mk orthonormal_logCellDyadicOrbit (le_of_eq logCellDyadicFiniteSpan_dense.symm)

theorem logCellDyadicBasis_apply (i : ℕ × Option ℕ+) :
    logCellDyadicBasis i = logCellDyadicOrbit i :=
  congrFun (HilbertBasis.coe_mk orthonormal_logCellDyadicOrbit
    (le_of_eq logCellDyadicFiniteSpan_dense.symm)) i

/-- Arithmetic dyadic analysis is an isometric isomorphism, without a quotient. -/
def logCellDyadicCoordinates : CellH ≃ₗᵢ[ℂ] lp (fun _ : ℕ × Option ℕ+ => ℂ) 2 :=
  logCellDyadicBasis.repr

/-- Each coordinate reads the literal shifted cell generator. -/
theorem logCellDyadicCoordinates_apply (x : CellH) (i : ℕ × Option ℕ+) :
    logCellDyadicCoordinates x i = inner ℂ (logCellDyadicOrbit i) x := by
  change logCellDyadicBasis.repr x i = _
  rw [HilbertBasis.repr_apply_apply, logCellDyadicBasis_apply]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_finite_logCellDyadic_expansion
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.orthonormal_logCellDyadicOrbit
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicFiniteSpan_dense
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellDyadicCoordinates
