import GaloisForLFunctions.HTGeometry.BorelWeil.LUDecomposition

/-!
# Uniqueness of the Borel–Weil highest weight vector

A section of the Borel–Weil line bundle that is invariant under left translation by the lower
unitriangular group is a scalar multiple of the minor product `bwPoly`.  Indeed such a section is
determined on the big cell `U⁻ · B` by its value at the identity, and the big cell is the
non-vanishing locus of the leading principal minors, hence dense in affine matrix space.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.lowerUniInvariants`

## Main results

* `polySections_eq_smul_bwPoly` — the uniqueness statement.
* `lowerUniInvariants_eq_span`, `finrank_lowerUniInvariants` — the invariants form a line.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

@[simp] theorem matEval_sub (g : Matrix (Fin N) (Fin N) k)
    (p q : MvPolynomial (Fin N × Fin N) k) :
    matEval g (p - q) = matEval g p - matEval g q := by simp [matEval]

theorem matEval_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin N × Fin N) k)
    (g : Matrix (Fin N) (Fin N) k) :
    matEval g (∏ i ∈ s, f i) = ∏ i ∈ s, matEval g (f i) := by simp [matEval]

theorem isLowerUni_truncate (j : ℕ) {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L) :
    IsLowerUni (truncate j L) := by
  refine ⟨fun i i' hii => ?_, fun i => ?_⟩
  · by_cases h1 : (i : ℕ) < j
    · by_cases h2 : (i' : ℕ) < j
      · rw [truncate_apply_of_both h1 h2]; exact hL.1 i i' hii
      · rw [truncate_apply_of_not_right h2, if_neg (ne_of_lt hii)]
    · rw [truncate_apply_of_not_left h1, if_neg (ne_of_lt hii)]
  · by_cases h1 : (i : ℕ) < j
    · rw [truncate_apply_of_both h1 h1]; exact hL.2 i
    · rw [truncate_apply_of_not_left h1, if_pos rfl]

@[simp] theorem leadingMinorMat_of_lowerUni (j : ℕ) {L : Matrix (Fin N) (Fin N) k}
    (hL : IsLowerUni L) : leadingMinorMat j L = 1 :=
  (isLowerUni_truncate j hL).det_eq_one

@[simp] theorem bwVectorMat_of_lowerUni (m : Fin N → ℕ) {L : Matrix (Fin N) (Fin N) k}
    (hL : IsLowerUni L) : bwVectorMat m L = 1 := by
  simp [bwVectorMat, hL]

/-- The minor product is invariant under left translation by lower unitriangular matrices. -/
theorem matEval_bwPoly_lowerUni_mul (m : Fin N → ℕ) {L : Matrix (Fin N) (Fin N) k}
    (hL : IsLowerUni L) (g : Matrix (Fin N) (Fin N) k) :
    matEval (L * g) (bwPoly m k) = matEval g (bwPoly m k) := by
  rw [matEval_bwPoly, matEval_bwPoly, bwVectorMat, bwVectorMat]
  exact Finset.prod_congr rfl fun j _ => by rw [leadingMinorMat_lowerUni_mul _ hL]

theorem bwPoly_ne_zero [Infinite k] (m : Fin N → ℕ) : bwPoly m k ≠ 0 := by
  intro hzero
  have := congrArg (matEval (1 : Matrix (Fin N) (Fin N) k)) hzero
  rw [matEval_one_bwPoly, matEval_zero] at this
  exact one_ne_zero this

/-- **Uniqueness of the highest weight vector.**  A section invariant under the lower unitriangular
group is the value at the identity times the minor product. -/
theorem polySections_eq_smul_bwPoly [Infinite k] {lam : Fin N → ℕ} (hlam : Antitone lam)
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p ∈ polySections lam)
    (hinv : ∀ L : Matrix (Fin N) (Fin N) k, IsLowerUni L →
      ∀ g : Matrix (Fin N) (Fin N) k, matEval (L * g) p = matEval g p) :
    p = (matEval (1 : Matrix (Fin N) (Fin N) k) p) • bwPoly (multOfWeight lam) k := by
  classical
  set m := multOfWeight lam with hm
  have hwm : weightOfMult m = lam := weightOfMult_multOfWeight hlam
  set c := matEval (1 : Matrix (Fin N) (Fin N) k) p with hc
  set q : MvPolynomial (Fin N × Fin N) k := p - c • bwPoly m k with hq
  -- `q` vanishes on the big cell
  have hbig : ∀ g : Matrix (Fin N) (Fin N) k,
      (∀ j : Fin N, leadingMinorMat ((j : ℕ) + 1) g ≠ 0) → matEval g q = 0 := by
    intro g hgm
    obtain ⟨L, B, hL, hB, rfl⟩ := exists_lu_of_leadingMinor_ne_zero g hgm
    have h1 : matEval (L * B) p = borelCharMat lam B * c := by
      have hb := hp 1 B hB
      rw [Matrix.one_mul] at hb
      rw [hinv L hL B, hb]
    have h2 : matEval (L * B) (bwPoly m k) = borelCharMat lam B := by
      rw [matEval_bwPoly, bwVectorMat_mul_borel m L hB.1, bwVectorMat_of_lowerUni m hL, mul_one,
        hwm]
    rw [hq, matEval_sub, matEval_smul, h1, h2]
    ring
  -- hence `q` times the product of the minors vanishes identically
  set D : MvPolynomial (Fin N × Fin N) k := ∏ j : Fin N, minorPoly ((j : ℕ) + 1) N k with hD
  have hDne : D ≠ 0 := by
    intro hzero
    have hval := congrArg (matEval (1 : Matrix (Fin N) (Fin N) k)) hzero
    rw [hD, matEval_prod, matEval_zero] at hval
    simp [matEval_minorPoly] at hval
  have hzero : q * D = 0 := by
    refine matEval_injective fun g => ?_
    rw [matEval_mul, matEval_zero]
    by_cases hgm : ∀ j : Fin N, leadingMinorMat ((j : ℕ) + 1) g ≠ 0
    · rw [hbig g hgm, zero_mul]
    · push Not at hgm
      obtain ⟨j, hj⟩ := hgm
      have : matEval g D = 0 := by
        rw [hD, matEval_prod]
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        rw [matEval_minorPoly]
        exact hj
      rw [this, mul_zero]
  have hq0 : q = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hDne
  rw [hq] at hq0
  exact sub_eq_zero.mp hq0

/-- The lower-unitriangular invariants of the Borel–Weil sections. -/
def lowerUniInvariants (lam : Fin N → ℕ) : Submodule k (MvPolynomial (Fin N × Fin N) k) where
  carrier := {p | p ∈ polySections lam ∧ ∀ L : Matrix (Fin N) (Fin N) k, IsLowerUni L →
    ∀ g : Matrix (Fin N) (Fin N) k, matEval (L * g) p = matEval g p}
  add_mem' hp hq := ⟨(polySections _).add_mem hp.1 hq.1, fun L hL g => by
    rw [matEval_add, matEval_add, hp.2 L hL g, hq.2 L hL g]⟩
  zero_mem' := ⟨(polySections _).zero_mem, fun L hL g => by simp⟩
  smul_mem' c p hp := ⟨(polySections _).smul_mem c hp.1, fun L hL g => by
    rw [matEval_smul, matEval_smul, hp.2 L hL g]⟩

/-- **The highest weight line.** -/
theorem lowerUniInvariants_eq_span [Infinite k] {lam : Fin N → ℕ} (hlam : Antitone lam) :
    lowerUniInvariants (k := k) lam = Submodule.span k {bwPoly (multOfWeight lam) k} := by
  apply le_antisymm
  · intro p hp
    rw [Submodule.mem_span_singleton]
    exact ⟨matEval (1 : Matrix (Fin N) (Fin N) k) p,
      (polySections_eq_smul_bwPoly hlam hp.1 hp.2).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨?_, fun L hL g => matEval_bwPoly_lowerUni_mul _ hL g⟩
    have h := bwPoly_mem_polySections (k := k) (multOfWeight lam)
    rwa [weightOfMult_multOfWeight hlam] at h

theorem finrank_lowerUniInvariants [Infinite k] {lam : Fin N → ℕ} (hlam : Antitone lam) :
    Module.finrank k (lowerUniInvariants (k := k) lam) = 1 := by
  rw [lowerUniInvariants_eq_span hlam]
  exact finrank_span_singleton (bwPoly_ne_zero _)

end GaloisForLFunctions.HTGeometry.BorelWeil
