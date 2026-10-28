import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheFrobeniusLadderIsMetzler
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.UpperLefschetzBoundsAreBlindOnlyToRealZeros
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration
import Mathlib.FieldTheory.Finite.Extension

/-!
# The trickle-down inequality is the square-root count

Weil's theorem for curves from the Frobenius ladder, with no surface. For a curve datum the Gram
of `H, V, Γ_0, …, Γ_K` is Metzler iff the point counts are nonnegative, and then its Hodge index
is the weighted trickle-down inequality `(TD_π)` (`TheFrobeniusLadderIsMetzler`).

* **Depth exhausts the span** (`forall_isHyperbolic_frobeniusGram_iff_unitary`): every span class
  lives on a ladder `range (K + 1)` (`spanDefect_eq_of_subset`), so the Hodge index on all ladders is
  the Hodge index on the Frobenius span, which is `|β_i| = 1` (ArithmeticCastelnuovoSeveri).
* **The trickle-down inequality is the square-root count**
  (`forall_weightedTrickleDown_iff_exists_pointCount_ge`): for data with nonnegative counts,
  `(TD_π)` on every ladder ⇔ the one-sided Lefschetz bound `N_k ≥ q^k + 1 − C q^{k/2}` for all `k`.
* **Actual curves trickle down** (`hyperelliptic_weightedTrickleDown`,
  `hyperelliptic_hasHyperbolicLinks`): for `y² = f(x)`, `f` squarefree of odd degree over a finite
  field of odd characteristic, the counts are cardinalities of point sets over the extensions of
  every degree, and the datum is unitary by Stepanov's count. So every Frobenius ladder satisfies
  `(TD_π)`, and its weighted Gram has hyperbolic links, rank one plus negative semidefinite.
* **The fake fails the count** (`golden_not_exists_pointCount_ge`): the golden datum, Metzler and
  connected, violates every square-root lower bound.

Over `𝔽_q` the local-to-global inequality of Lorentzian theory is therefore supplied by a count
(an auxiliary function with many zeros) rather than by a surface; that count is the input a
construction over `ℤ` has to replace.
-/

noncomputable section

open Matrix Finset Polynomial

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι]

/-! ### Depth exhausts the span -/

/-- The span defect of `d` on `S` is the span defect of `d·1_S` on any larger window. -/
theorem spanDefect_eq_of_subset (D : CurveDatum ι) {S T : Finset ℕ} (hST : S ⊆ T)
    (d : ℕ → ℝ) : D.spanDefect S d = D.spanDefect T (fun k => if k ∈ S then d k else 0) := by
  unfold CurveDatum.spanDefect
  have h1 : ∑ k ∈ T, (if k ∈ S then d k else 0) = ∑ k ∈ S, d k := by
    rw [sum_ite_mem, inter_eq_right.mpr hST]
  have h2 : ∑ k ∈ T, (if k ∈ S then d k else 0) * D.q ^ k = ∑ k ∈ S, d k * D.q ^ k := by
    simp_rw [ite_mul, zero_mul]
    rw [sum_ite_mem, inter_eq_right.mpr hST]
  have h3 : ∑ k ∈ T, ∑ l ∈ T, (if k ∈ S then d k else 0) * (if l ∈ S then d l else 0) *
      D.graphPair k l = ∑ k ∈ S, ∑ l ∈ S, d k * d l * D.graphPair k l := by
    have hz : ∀ k ∈ T, k ∉ S → ∑ l ∈ T, (if k ∈ S then d k else 0) *
        (if l ∈ S then d l else 0) * D.graphPair k l = 0 := fun k _ hk => by simp [hk]
    rw [← sum_subset hST hz]
    refine sum_congr rfl fun k hk => ?_
    have hz' : ∀ l ∈ T, l ∉ S → (if k ∈ S then d k else 0) * (if l ∈ S then d l else 0) *
        D.graphPair k l = 0 := fun l _ hl => by simp [hl]
    rw [← sum_subset hST hz']
    exact sum_congr rfl fun l hl => by simp [hk, hl]
  rw [h1, h2, h3]

/-- **Depth exhausts the span.** The Frobenius Gram is hyperbolic on every ladder iff the datum is
unitary. -/
theorem forall_isHyperbolic_frobeniusGram_iff_unitary (D : CurveDatum ι) :
    (∀ K, IsHyperbolic (frobeniusGram D K)) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← D.hodgeIndexOnSpan_iff_unitary]
  constructor
  · intro h S d
    have hK : S ⊆ range (S.sup id + 1) := fun k hk =>
      mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hk))
    rw [spanDefect_eq_of_subset D hK]
    exact (frobeniusGram_isHyperbolic_iff D _).mp (h _) _
  · intro h K
    exact (frobeniusGram_isHyperbolic_iff D K).mpr fun d => h _ d

/-! ### The trickle-down inequality is the square-root count -/

/-- `(TD_π)` on every ladder ⇔ unitarity, for data with nonnegative counts. -/
theorem forall_weightedTrickleDown_iff_unitary (D : CurveDatum ι)
    (hN : ∀ j, 1 ≤ j → 0 ≤ D.pointCount j) :
    (∀ K, WeightedTrickleDown (frobeniusWeight D K) (frobeniusGram D K)) ↔
      ∀ i, ‖D.β i‖ = 1 := by
  rw [← forall_isHyperbolic_frobeniusGram_iff_unitary]
  exact forall_congr' fun K =>
    (frobeniusGram_isHyperbolic_iff_weightedTrickleDown D K fun j hj _ => hN j hj).symm

/-- Unitarity ⇔ the lower Lefschetz bound `N_k ≥ q^k + 1 − C q^{k/2}` for all `k`. -/
theorem unitary_iff_exists_pointCount_ge (D : CurveDatum ι) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∃ C : ℝ, ∀ k, D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k := by
  constructor
  · intro hU
    exact ⟨Fintype.card ι, fun k => (D.trace_le_iff_pointCount_ge k _).mp
      ((le_abs_self _).trans (D.abs_trace_le_card_of_unitary hU k))⟩
  · rintro ⟨C, hC⟩
    exact D.unitary_of_trace_le fun k => (D.trace_le_iff_pointCount_ge k C).mpr (hC k)

/-- **The trickle-down inequality is the square-root count.** For a curve datum with nonnegative
point counts, the weighted trickle-down inequality holds on every Frobenius ladder iff
`N_k ≥ q^k + 1 − C q^{k/2}` for all `k`, for some `C`. -/
theorem forall_weightedTrickleDown_iff_exists_pointCount_ge (D : CurveDatum ι)
    (hN : ∀ j, 1 ≤ j → 0 ≤ D.pointCount j) :
    (∀ K, WeightedTrickleDown (frobeniusWeight D K) (frobeniusGram D K)) ↔
      ∃ C : ℝ, ∀ k, D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k :=
  (forall_weightedTrickleDown_iff_unitary D hN).trans (unitary_iff_exists_pointCount_ge D)

/-- **The fake fails the count**: no square-root lower bound holds for the golden datum. -/
theorem golden_not_exists_pointCount_ge :
    ¬ ∃ C : ℝ, ∀ k, goldenDatum.q ^ k + 1 - C * goldenDatum.sqrtq ^ k ≤ goldenDatum.pointCount k :=
  fun h => goldenDatum_not_unitary ((unitary_iff_exists_pointCount_ge _).mpr h)

/-! ### Actual curves trickle down -/

theorem frobeniusGram_isSymm (D : CurveDatum ι) (K : ℕ) : (frobeniusGram D K).IsSymm := by
  unfold frobeniusGram Matrix.IsSymm
  rw [fromBlocks_transpose, transpose_transpose, (frobeniusGraphBlock_isSymm D K).eq]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- A hyperbolic Frobenius Gram with nonnegative counts has hyperbolic links after weighting by
`π`: its weighted Gram `diag(π) Q diag(π)` is connected Metzler with positive row sums. -/
theorem hasHyperbolicLinks_of_isHyperbolic (D : CurveDatum ι) (K : ℕ)
    (hN : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ D.pointCount j) (h : IsHyperbolic (frobeniusGram D K)) :
    HasHyperbolicLinks (diagConj (frobeniusWeight D K) (frobeniusGram D K)) := by
  have hπ := frobeniusWeight_pos D K
  refine (isHyperbolic_iff_hasHyperbolicLinks (diagConj_isSymm (frobeniusGram_isSymm D K))
    (diagConj_isMetzler hπ ((frobeniusGram_isMetzler_iff D K).mpr hN)) (fun i => ?_)
    (diagConj_isConnectedSupport hπ (frobeniusGram_isConnectedSupport D K))).mp
    ((isHyperbolic_diagConj_iff fun i => (hπ i).ne').mpr h)
  rw [rowSum_diagConj]
  exact mul_pos (hπ i) (frobeniusGram_mulVec_pos D K i)

section Hyperelliptic

open ArithmeticEffectivityTheory RHTower.Hyperelliptic

variable {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
  (hodd : Odd f.natDegree)

/-- The counts of `y² = f(x)` are positive: over the extension of degree `j ≥ 1` they count the
affine points plus the point at infinity. -/
theorem hyperellipticDatum_pointCount_pos {j : ℕ} (hj : 1 ≤ j) :
    0 < (hyperellipticDatum hF hsq hodd).pointCount j := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  haveI : NeZero j := ⟨by omega⟩
  letI : Fintype (FiniteField.Extension F (ringChar F) j) := Fintype.ofFinite _
  have h := hyperellipticDatum_pointCount hF hsq hodd (FiniteField.Extension F (ringChar F) j)
  rw [FiniteField.finrank_extension] at h
  rw [h]
  positivity

/-- **Actual curves trickle down.** Every Frobenius ladder of `y² = f(x)` satisfies the weighted
trickle-down inequality. -/
theorem hyperelliptic_weightedTrickleDown (K : ℕ) :
    WeightedTrickleDown (frobeniusWeight (hyperellipticDatum hF hsq hodd) K)
      (frobeniusGram (hyperellipticDatum hF hsq hodd) K) :=
  weightedTrickleDown_of_unitary _ (hyperellipticDatum_unitary hF hsq hodd) K
    fun _ hj _ => (hyperellipticDatum_pointCount_pos hF hsq hodd hj).le

/-- **The degree-three lift exists for actual curves.** The weighted Frobenius Gram of every ladder
of `y² = f(x)` is a connected Metzler form with positive row sums and hyperbolic links. -/
theorem hyperelliptic_hasHyperbolicLinks (K : ℕ) :
    HasHyperbolicLinks (diagConj (frobeniusWeight (hyperellipticDatum hF hsq hodd) K)
      (frobeniusGram (hyperellipticDatum hF hsq hodd) K)) :=
  hasHyperbolicLinks_of_isHyperbolic _ K
    (fun _ hj _ => (hyperellipticDatum_pointCount_pos hF hsq hodd hj).le)
    (frobeniusGram_isHyperbolic_of_unitary _ (hyperellipticDatum_unitary hF hsq hodd) K)

end Hyperelliptic

end GaloisForLFunctions.ArithmeticLorentzianGeometry
