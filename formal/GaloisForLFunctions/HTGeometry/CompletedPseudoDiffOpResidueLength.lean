import GaloisForLFunctions.HTGeometry.DifferentialVariationalSubspaceLattice

/-!
# Residue length over the completed valuation ring

The degree of an invariant subspace is a difference of lengths of layers between commensurable
integral lattices, so those layers must have finite length.  This leaf supplies the counting input.

The completed valuation ring is local, and its maximal ideal is maximal as an ideal, so the residue
module is simple and has length one
(`DiffOp.isSimpleModule_quotient_maximalIdeal`, `DiffOp.length_quotient_maximalIdeal_eq_one`).
Every element of the maximal ideal is a right multiple of the canonical uniformizer
(`DiffOp.exists_mul_uniformizerInteger_of_mem_maximalIdeal`): its additive value is at least one, so
dividing by the uniformizer stays integral.

The consequence is the finiteness statement the degree needs:

```text
DiffOp.length_span_le_card_of_uniformizer_smul_eq_zero
    a finitely generated module killed by the uniformizer has length at most its generator count
```

The proof is an induction over the generating finset.  Splitting off one generator gives an exact
sequence whose sub-object is the span of the remaining generators and whose quotient is cyclic; the
cyclic quotient is a quotient of `O` by a left ideal containing the maximal ideal — because the
uniformizer already annihilates the module — hence of length at most one.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] [Differential K]

/-- The residue module of the completed valuation ring is simple. -/
theorem DiffOp.isSimpleModule_quotient_maximalIdeal :
    IsSimpleModule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (DiffOp.CompletedPseudoDiffOpInteger (K := K) ⧸
        (DiffOp.completedPseudoDiffOpMaximalIdeal (K := K))) :=
  isSimpleModule_iff_isCoatom.2 DiffOp.completedPseudoDiffOpMaximalIdeal_isMaximal.out

/-- The residue module of the completed valuation ring has length one. -/
theorem DiffOp.length_quotient_maximalIdeal_eq_one :
    Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (DiffOp.CompletedPseudoDiffOpInteger (K := K) ⧸
        (DiffOp.completedPseudoDiffOpMaximalIdeal (K := K))) = 1 :=
  Module.length_eq_one_iff.2 DiffOp.isSimpleModule_quotient_maximalIdeal

/-- The canonical uniformizer lies in the maximal ideal. -/
theorem DiffOp.uniformizer_mem_maximalIdeal :
    (⟨((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (1 : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K),
      DiffOp.uniformizer_natPow_mem_integer (K := K) 1⟩ :
      DiffOp.CompletedPseudoDiffOpInteger (K := K)) ∈
      DiffOp.completedPseudoDiffOpMaximalIdeal (K := K) := by
  rw [DiffOp.mem_completedPseudoDiffOpMaximalIdeal_iff]
  have hval : DiffOp.completedPseudoDiffOpAddValue
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (1 : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) =
      ((1 : ℤ) : WithTop ℤ) :=
    DiffOp.completedPseudoDiffOpAddValue_uniformizer_zpow (K := K) 1
  by_contra hle
  push_neg at hle
  have hge : (1 : _) ≤ DiffOp.completedPseudoDiffOpValuation
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (1 : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) := hle
  have heq : DiffOp.completedPseudoDiffOpAddValue
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (1 : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) ≤ 0 := by
    exact hge
  rw [hval] at heq
  exact absurd heq (by decide)


/-- Elements of the maximal ideal are right multiples of the canonical uniformizer. -/
theorem DiffOp.exists_mul_uniformizer_of_mem_maximalIdeal
    {a : DiffOp.CompletedPseudoDiffOpInteger (K := K)}
    (ha : a ∈ DiffOp.completedPseudoDiffOpMaximalIdeal (K := K)) :
    ∃ w : DiffOp.CompletedPseudoDiffOpInteger (K := K),
      (a : DiffOp.CompletedPseudoDiffOp K) =
        (w : DiffOp.CompletedPseudoDiffOp K) *
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (1 : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) := by
  have hpos : 0 < DiffOp.completedPseudoDiffOpAddValue
      ((a : DiffOp.CompletedPseudoDiffOp K)) := ha
  have hone : ((1 : ℤ) : WithTop ℤ) ≤ DiffOp.completedPseudoDiffOpAddValue
      ((a : DiffOp.CompletedPseudoDiffOp K)) := by
    by_contra hlt
    rw [not_le] at hlt
    have hne : DiffOp.completedPseudoDiffOpAddValue
        ((a : DiffOp.CompletedPseudoDiffOp K)) ≠ ⊤ := by
      intro htop
      rw [htop] at hlt
      exact absurd hlt (by simp)
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hn] at hlt hpos
    have h1 : n < (1 : ℤ) := by exact_mod_cast hlt
    have h2 : (0 : ℤ) < n := by exact_mod_cast hpos
    omega
  have hwval : (0 : WithTop ℤ) ≤ DiffOp.completedPseudoDiffOpAddValue
      ((a : DiffOp.CompletedPseudoDiffOp K) *
        ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-1 : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K)) := by
    rw [DiffOp.completedPseudoDiffOpAddValue_mul,
      DiffOp.completedPseudoDiffOpAddValue_uniformizer_zpow (K := K) (-1 : ℤ)]
    by_cases htop : DiffOp.completedPseudoDiffOpAddValue
        ((a : DiffOp.CompletedPseudoDiffOp K)) = ⊤
    · rw [htop]
      simp
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 htop
      rw [← hn] at hone ⊢
      have h1 : (1 : ℤ) ≤ n := by exact_mod_cast hone
      rw [← WithTop.coe_add]
      exact_mod_cast (by omega : (0 : ℤ) ≤ n + (-1))
  refine ⟨⟨(a : DiffOp.CompletedPseudoDiffOp K) *
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-1 : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K),
    (DiffOp.mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).2 hwval⟩, ?_⟩
  show (a : DiffOp.CompletedPseudoDiffOp K) =
    ((a : DiffOp.CompletedPseudoDiffOp K) *
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-1 : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K)) *
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (1 : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K)
  rw [mul_assoc, ← Units.val_mul, ← zpow_add]
  norm_num

/-- The canonical uniformizer as an element of the valuation ring. -/
def DiffOp.uniformizerInteger : DiffOp.CompletedPseudoDiffOpInteger (K := K) :=
  ⟨((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((1 : ℕ) : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K),
    DiffOp.uniformizer_natPow_mem_integer (K := K) 1⟩

theorem DiffOp.exists_mul_uniformizerInteger_of_mem_maximalIdeal
    {a : DiffOp.CompletedPseudoDiffOpInteger (K := K)}
    (ha : a ∈ DiffOp.completedPseudoDiffOpMaximalIdeal (K := K)) :
    ∃ w : DiffOp.CompletedPseudoDiffOpInteger (K := K),
      a = w * DiffOp.uniformizerInteger (K := K) := by
  obtain ⟨w, hw⟩ := DiffOp.exists_mul_uniformizer_of_mem_maximalIdeal ha
  exact ⟨w, Subtype.ext (by rw [hw]; norm_num [DiffOp.uniformizerInteger])⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **A finitely generated module killed by the uniformizer has finite length**, bounded by the
number of generators: each cyclic layer is a quotient of the simple residue module. -/
theorem DiffOp.length_span_le_card_of_uniformizer_smul_eq_zero
    {Q : Type*} [AddCommGroup Q] [Module (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q]
    (s : Finset Q)
    (hs : ∀ q ∈ Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (s : Set Q),
      DiffOp.uniformizerInteger (K := K) • q = 0) :
    Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      ↥(Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (s : Set Q)) ≤
      (s.card : ℕ∞) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hbot : Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K))
          ((∅ : Finset Q) : Set Q) = ⊥ := by simp
      rw [hbot]
      have hsubs : Subsingleton
          ↥(⊥ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) Q) := inferInstance
      rw [Module.length_eq_zero_iff.2 hsubs]
      simp
  | insert x t hx ih =>
      have hsub : Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (t : Set Q) ≤
          Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K))
            ((insert x t : Finset Q) : Set Q) := by
        apply Submodule.span_mono
        rw [Finset.coe_insert]
        exact Set.subset_insert _ _
      have ihq := ih (fun q hq => hs q (hsub hq))
      set R := Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K))
        ((insert x t : Finset Q) : Set Q) with hR
      set P : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥R :=
        (Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K))
          (t : Set Q)).comap R.subtype with hP
      have hsplit := Module.length_eq_add_of_exact P.subtype P.mkQ
        Subtype.val_injective (Submodule.mkQ_surjective P) (LinearMap.exact_subtype_mkQ P)
      have hPlen : Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥P =
          Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K))
            ↥(Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (t : Set Q)) := by
        refine le_antisymm ?_ ?_
        · exact Module.length_le_of_injective
            (Submodule.comapSubtypeEquivOfLe hsub).toLinearMap
            (Submodule.comapSubtypeEquivOfLe hsub).injective
        · exact Module.length_le_of_injective
            (Submodule.comapSubtypeEquivOfLe hsub).symm.toLinearMap
            (Submodule.comapSubtypeEquivOfLe hsub).symm.injective
      have hxR : x ∈ R := by
        apply Submodule.subset_span
        rw [Finset.coe_insert]
        exact Set.mem_insert _ _
      have hquot : Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (↥R ⧸ P) ≤ 1 := by
        let f : DiffOp.CompletedPseudoDiffOpInteger (K := K) →ₗ[
            DiffOp.CompletedPseudoDiffOpInteger (K := K)] (↥R ⧸ P) :=
          P.mkQ.comp (LinearMap.toSpanSingleton
            (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥R ⟨x, hxR⟩)
        have hfsurj : Function.Surjective f := by
          intro y
          induction y using Quotient.inductionOn with
          | _ z =>
              have hz2 : (z : Q) ∈ Submodule.span
                  (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (insert x (t : Set Q)) := by
                rw [← Finset.coe_insert]
                exact z.2
              obtain ⟨a, w, hw, hzeq⟩ := Submodule.mem_span_insert.1 hz2
              refine ⟨a, ?_⟩
              show P.mkQ (a • (⟨x, hxR⟩ : ↥R)) = Quotient.mk _ z
              apply (Submodule.Quotient.eq P).2
              show ((a • (⟨x, hxR⟩ : ↥R) - z : ↥R) : Q) ∈
                Submodule.span (DiffOp.CompletedPseudoDiffOpInteger (K := K)) (t : Set Q)
              have hval : ((a • (⟨x, hxR⟩ : ↥R) - z : ↥R) : Q) = a • x - (z : Q) := rfl
              rw [hval, hzeq]
              have hneg : a • x - (a • x + w) = -w := by abel
              rw [hneg]
              exact Submodule.neg_mem _ hw
        have hker : DiffOp.completedPseudoDiffOpMaximalIdeal (K := K) ≤ LinearMap.ker f := by
          intro a ha
          obtain ⟨w, hw⟩ := DiffOp.exists_mul_uniformizerInteger_of_mem_maximalIdeal ha
          show P.mkQ (a • (⟨x, hxR⟩ : ↥R)) = 0
          have hax : a • x = (0 : Q) := by
            rw [hw, mul_smul, hs x (by
              apply Submodule.subset_span
              rw [Finset.coe_insert]
              exact Set.mem_insert _ _), smul_zero]
          have hzero : a • (⟨x, hxR⟩ : ↥R) = 0 := Subtype.ext hax
          rw [hzero, map_zero]
        have hlift := Module.length_le_of_surjective
          (Submodule.liftQ _ f hker) (by
            intro y
            obtain ⟨a, ha⟩ := hfsurj y
            exact ⟨Submodule.Quotient.mk a, ha⟩)
        exact le_trans hlift (le_of_eq DiffOp.length_quotient_maximalIdeal_eq_one)
      rw [hsplit, hPlen, Finset.card_insert_of_notMem hx]
      push_cast
      exact add_le_add ihq hquot

end

end GaloisForLFunctions.HTGeometry
