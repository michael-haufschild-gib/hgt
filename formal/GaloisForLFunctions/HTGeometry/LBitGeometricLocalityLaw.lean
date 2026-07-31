import GaloisForLFunctions.HTGeometry.LBitTemporalDimensionLaw
import Mathlib.Order.Interval.Finset.Fin

/-!
# Geometric-locality ceiling for one-dimensional l-bit Hamiltonians

For binary l-bits on a finite chain, a coefficient is geometrically `R`-local when every two
active sites in its support are at distance at most `R`.  This file packages all nonempty
geometrically local supports into one finite family and proves:

* every coefficient family vanishing outside that family has temporal rank at most its
  cardinality;
* the bound is exact whenever the allowed coefficients are rationally independent;
* arbitrarily small coefficient families attain the exact bound while the Hamiltonian remains
  diagonal in the same configuration basis and every l-bit charge remains conserved.

The cardinality is kept intrinsic here.  A separate combinatorial theorem may identify it with a
closed one-dimensional interval count; none of the rank or sharpness statements depends on that
additional enumeration.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitGeometricLocalityFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- A finite support on a chain has geometric range at most `R` when every pair of active sites is
at lattice distance at most `R`.  For a nonempty support this is equivalent to
`max(S) - min(S) ≤ R`. -/
def LBitSupportRangeAtMost {n : ℕ} (R : ℕ)
    (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, Nat.dist i.val j.val ≤ R

/-- All nonempty supports of geometric range at most `R` on an `n`-site chain. -/
def lbitGeometricSupports (n R : ℕ) :
    Finset (Finset (Fin n)) :=
  by
    classical
    exact
      (Finset.univ.powerset).filter
        (fun S => S.Nonempty ∧ LBitSupportRangeAtMost R S)

@[simp]
theorem mem_lbitGeometricSupports
    {n R : ℕ} {S : Finset (Fin n)} :
    S ∈ lbitGeometricSupports n R ↔
      S.Nonempty ∧ LBitSupportRangeAtMost R S := by
  simp [lbitGeometricSupports]

/-- **Exact geometric-locality ceiling.**  If every nonempty coefficient whose active sites span
more than `R` lattice steps vanishes, temporal rank is at most the number of nonempty supports of
range at most `R`. -/
theorem lbitTemporalRank_le_geometricSupports
    {n R : ℕ} (J : Finset (Fin n) → ℝ)
    (hJ :
      ∀ S, S.Nonempty →
        ¬ LBitSupportRangeAtMost R S →
        J S = 0) :
    lbitTemporalRank J ≤ (lbitGeometricSupports n R).card := by
  apply lbitTemporalRank_le_support J (lbitGeometricSupports n R)
  intro S hSne hS
  apply hJ S hSne
  intro hRange
  exact hS (mem_lbitGeometricSupports.mpr ⟨hSne, hRange⟩)

/-- Allowed geometric supports index a coefficient packet. -/
abbrev LBitGeometricSupportIndex (n R : ℕ) :=
  {S : Finset (Fin n) // S ∈ lbitGeometricSupports n R}

/-- The coefficient packet carried by the allowed geometric supports. -/
def lbitGeometricCoefficientPacket
    {n R : ℕ} (J : Finset (Fin n) → ℝ) :
    LBitGeometricSupportIndex n R → ℝ :=
  fun S => J S.1

/-- **Sharpness criterion.**  The geometric-locality ceiling is attained exactly under the
displayed rational-independence premise on all allowed coefficients.  No coefficient outside the
allowed family contributes. -/
theorem lbitTemporalRank_eq_geometricSupports_card
    {n R : ℕ} (J : Finset (Fin n) → ℝ)
    (hJ :
      ∀ S, S.Nonempty →
        ¬ LBitSupportRangeAtMost R S →
        J S = 0)
    (hIndependent :
      LinearIndependent ℚ
        (lbitGeometricCoefficientPacket (R := R) J)) :
    lbitTemporalRank J = (lbitGeometricSupports n R).card := by
  let allowedSpace : Submodule ℚ ℝ :=
    Submodule.span ℚ
      (Set.range (lbitGeometricCoefficientPacket (R := R) J))
  letI : FiniteDimensional ℚ allowedSpace :=
    FiniteDimensional.span_of_finite ℚ
      (Set.finite_range
        (lbitGeometricCoefficientPacket (R := R) J))
  letI : FiniteDimensional ℚ (lbitCoefficientSubspace J) :=
    FiniteDimensional.span_of_finite ℚ
      (Set.finite_range
        (fun S : {S : Finset (Fin n) // S.Nonempty} => J S.1))
  have hAllowed :
      allowedSpace ≤ lbitCoefficientSubspace J := by
    apply Submodule.span_le.2
    rintro z ⟨S, rfl⟩
    apply Submodule.subset_span
    have hSne : S.1.Nonempty :=
      (mem_lbitGeometricSupports.mp S.2).1
    exact ⟨⟨S.1, hSne⟩, rfl⟩
  have hlower :
      (lbitGeometricSupports n R).card ≤ lbitTemporalRank J := by
    rw [lbitTemporalRank_eq]
    calc
      (lbitGeometricSupports n R).card =
          Fintype.card (LBitGeometricSupportIndex n R) := by
            rw [Fintype.card_coe]
      _ = Module.finrank ℚ allowedSpace := by
        symm
        exact finrank_span_eq_card hIndependent
      _ ≤ Module.finrank ℚ (lbitCoefficientSubspace J) :=
        Submodule.finrank_mono hAllowed
  exact Nat.le_antisymm
    (lbitTemporalRank_le_geometricSupports J hJ)
    hlower

/-- **Sharp local realization.**  At every positive coefficient scale there is an exactly
`R`-local l-bit Hamiltonian attaining the geometric-support ceiling.  It remains diagonal in the
Boolean configuration basis and conserves every l-bit charge. -/
theorem exists_small_geometricLBit_maximalLocalRank
    (n R : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : Finset (Fin n) → ℝ,
      J ∅ = 0 ∧
      (∀ S, S.Nonempty →
        ¬ LBitSupportRangeAtMost R S →
        J S = 0) ∧
      (∀ S, |J S| < δ) ∧
      lbitTemporalRank J =
        (lbitGeometricSupports n R).card ∧
      (∀ i,
        lbitChargeMatrix i * lbitHamiltonianMatrix J =
          lbitHamiltonianMatrix J * lbitChargeMatrix i) ∧
      (∀ {x y : Fin n → Bool}, x ≠ y →
        lbitHamiltonianMatrix J x y = 0) := by
  classical
  let C := LBitGeometricSupportIndex n R
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  obtain ⟨b, hb, hbclose⟩ :=
    exists_linearIndependent_close
      (Fintype.card C) (fun _ => 0) δ hδ
  let J : Finset (Fin n) → ℝ :=
    fun S =>
      if hS : S ∈ lbitGeometricSupports n R then
        b (e ⟨S, hS⟩)
      else 0
  have hJind :
      LinearIndependent ℚ
        (lbitGeometricCoefficientPacket (R := R) J) := by
    have hcomp :
        LinearIndependent ℚ (fun S : C => b (e S)) :=
      hb.comp e e.injective
    have heq :
        lbitGeometricCoefficientPacket (R := R) J =
          fun S : C => b (e S) := by
      funext S
      change J S.1 = b (e S)
      dsimp only [J]
      rw [dif_pos S.2]
    rw [heq]
    exact hcomp
  have hJlocal :
      ∀ S, S.Nonempty →
        ¬ LBitSupportRangeAtMost R S →
        J S = 0 := by
    intro S hSne hRange
    have hnot : S ∉ lbitGeometricSupports n R := by
      simpa [mem_lbitGeometricSupports, hSne] using hRange
    dsimp only [J]
    rw [dif_neg hnot]
  have hJsmall : ∀ S, |J S| < δ := by
    intro S
    by_cases hS : S ∈ lbitGeometricSupports n R
    · have hclose := hbclose (e ⟨S, hS⟩)
      dsimp only [J]
      rw [dif_pos hS]
      simpa [Real.dist_eq] using hclose
    · dsimp only [J]
      rw [dif_neg hS, abs_zero]
      exact hδ
  refine ⟨J, ?_, hJlocal, hJsmall, ?_, ?_, ?_⟩
  · have hempty :
        (∅ : Finset (Fin n)) ∉ lbitGeometricSupports n R := by
      simp
    dsimp only [J]
    rw [dif_neg hempty]
  · exact
      lbitTemporalRank_eq_geometricSupports_card
        J hJlocal hJind
  · exact fun i => lbitChargeMatrix_commutes J i
  · exact fun hxy => lbitHamiltonianMatrix_offDiagonal J hxy

/-- Right endpoint of the length-`R + 1` chain window beginning at `a`,
truncated at the physical boundary. -/
def lbitGeometricWindowUpper
    {n : ℕ} (R : ℕ) (a : Fin n) : Fin n :=
  ⟨min (n - 1) (a.val + R), by
    have ha : a.val < n := a.isLt
    omega⟩

/-- Chain interval of radius `R` to the right of one possible leftmost
active site. -/
def lbitGeometricWindow
    {n : ℕ} (R : ℕ) (a : Fin n) : Finset (Fin n) :=
  Finset.Icc a (lbitGeometricWindowUpper R a)

/-- Nonempty supports contained in at least one truncated window of length
at most `R + 1`. -/
def lbitGeometricWindowSupports
    (n R : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.biUnion fun a : Fin n =>
    (lbitGeometricWindow R a).powerset.erase ∅

/-- Every truncated geometric window contains at most `R + 1` sites. -/
theorem lbitGeometricWindow_card_le
    {n : ℕ} (R : ℕ) (a : Fin n) :
    (lbitGeometricWindow R a).card ≤ R + 1 := by
  rw [lbitGeometricWindow, Fin.card_Icc]
  have hupper :
      (lbitGeometricWindowUpper R a).val ≤ a.val + R := by
    exact min_le_right _ _
  omega

/-- Every nonempty support of pairwise range at most `R` lies in the
window beginning at its leftmost active site. -/
theorem lbitGeometricSupports_subset_windowSupports
    (n R : ℕ) :
    lbitGeometricSupports n R ⊆
      lbitGeometricWindowSupports n R := by
  intro S hS
  have hdata := mem_lbitGeometricSupports.mp hS
  let a : Fin n := S.min' hdata.1
  have haS : a ∈ S := Finset.min'_mem S hdata.1
  rw [lbitGeometricWindowSupports, Finset.mem_biUnion]
  refine ⟨a, Finset.mem_univ a, ?_⟩
  rw [Finset.mem_erase]
  refine ⟨hdata.1.ne_empty, Finset.mem_powerset.mpr ?_⟩
  intro i hiS
  rw [lbitGeometricWindow, Finset.mem_Icc]
  have hai : a ≤ i := Finset.min'_le S i hiS
  have hdist : Nat.dist a.val i.val ≤ R :=
    hdata.2 a haS i hiS
  have hival : i.val ≤ a.val + R := by
    rw [Nat.dist_eq_sub_of_le hai] at hdist
    omega
  constructor
  · exact hai
  · apply Fin.le_iff_val_le_val.mpr
    change i.val ≤ min (n - 1) (a.val + R)
    apply le_min
    · omega
    · exact hival

/-- **Dimension-linear geometric-locality law.** The number of nonempty
range-`R` supports is at most `n * 2^(R+1)`. Thus every fixed-range
commuting l-bit family has temporal rank at most linear in chain length. -/
theorem card_lbitGeometricSupports_le_linear
    (n R : ℕ) :
    (lbitGeometricSupports n R).card ≤
      n * 2 ^ (R + 1) := by
  calc
    (lbitGeometricSupports n R).card ≤
        (lbitGeometricWindowSupports n R).card :=
      Finset.card_le_card
        (lbitGeometricSupports_subset_windowSupports n R)
    _ ≤ ∑ a : Fin n,
          ((lbitGeometricWindow R a).powerset.erase ∅).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin n, 2 ^ (R + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        ((lbitGeometricWindow R a).powerset.erase ∅).card ≤
            (lbitGeometricWindow R a).powerset.card :=
          Finset.card_erase_le
        _ = 2 ^ (lbitGeometricWindow R a).card :=
          Finset.card_powerset _
        _ ≤ 2 ^ (R + 1) :=
          Nat.pow_le_pow_right
            (by norm_num)
            (lbitGeometricWindow_card_le R a)
    _ = n * 2 ^ (R + 1) := by simp

/-- Temporal rank inherits the explicit dimension-linear bound for every
fixed-range commuting l-bit Hamiltonian. -/
theorem lbitTemporalRank_le_geometric_linear
    {n R : ℕ} (J : Finset (Fin n) → ℝ)
    (hJ :
      ∀ S, S.Nonempty →
        ¬ LBitSupportRangeAtMost R S →
        J S = 0) :
    lbitTemporalRank J ≤ n * 2 ^ (R + 1) := by
  exact
    (lbitTemporalRank_le_geometricSupports J hJ).trans
      (card_lbitGeometricSupports_le_linear n R)

end

end GaloisForLFunctions.HTGeometry
