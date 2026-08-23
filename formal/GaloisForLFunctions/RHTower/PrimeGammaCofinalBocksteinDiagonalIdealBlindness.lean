import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDiagonalCompact
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity

/-!
# Trace wall and norm-closed ideal blindness for the cofinal Gamma diagonal

The prime-enumerated Gamma reflection defect is Schatten-one exactly at neutral grade.  Its
finite diagonal cuts converge in operator norm throughout the open strip, so every norm-closed
set containing the finite-rank operators diagonal in the same basis contains the full defect.
This proves the operator-theoretic clauses without requiring an abstract ideal API: the stated
closed two-sided ideal hypothesis is stronger than the exact closure hypothesis used here.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Finite-rank operators diagonal in a fixed Hilbert basis. -/
def IsFiniteRankDiagonal {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (F : H →L[ℂ] H) : Prop :=
  (∃ n, HasRankLE F n) ∧ ∃ c : ι → ℂ, ∀ i, F (b i) = c i • b i

/-- A norm-closed set containing all finite-rank operators diagonal in `b` contains every
`b`-diagonal operator whose multipliers vanish along the cofinite filter. -/
theorem mem_closedSet_of_diag_tendsto_cofinite_of_contains_finiteRankDiagonal
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} {c : ι → ℂ}
    (hdiag : ∀ i, T (b i) = c i • b i)
    (hc : Tendsto (fun i ↦ ‖c i‖) cofinite (nhds 0))
    (J : Set (H →L[ℂ] H)) (hJ : IsClosed J)
    (hfiniteDiagonal : ∀ F : H →L[ℂ] H, IsFiniteRankDiagonal b F → F ∈ J) :
    T ∈ J := by
  classical
  apply hJ.closure_subset
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hev : ∀ᶠ i in cofinite, ‖c i‖ ≤ δ / 2 := by
    have hnear := Metric.tendsto_nhds.mp hc (δ / 2) hhalf
    filter_upwards [hnear] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hi
    exact le_of_lt hi
  have hfin : {i | ¬ ‖c i‖ ≤ δ / 2}.Finite := Filter.eventually_cofinite.mp hev
  let s := hfin.toFinset
  refine ⟨ContinuousLinearMap.hsTruncation b T s,
    hfiniteDiagonal _ ⟨⟨s.card, hasRankLE_hsTruncation b T s⟩, ?_⟩, ?_⟩
  · refine ⟨fun i ↦ if i ∈ s then c i else 0, fun i ↦ ?_⟩
    rw [ContinuousLinearMap.hsTruncation_apply_basis]
    by_cases hi : i ∈ s
    · simp [hi, hdiag]
    · simp [hi]
  · rw [dist_eq_norm]
    have hbdd : ∀ i, i ∉ s → ‖c i‖ ≤ δ / 2 := by
      intro i hi
      by_contra hcon
      exact hi (Set.Finite.mem_toFinset hfin |>.2 hcon)
    exact lt_of_le_of_lt
      (GaloisForLFunctions.HTGeometry.norm_sub_hsTruncation_diag_le
        b hdiag s (le_of_lt hhalf) hbdd) (by linarith)

/-- Clause (2): the literal cofinal Gamma diagonal is Schatten-one exactly at neutral grade. -/
theorem memSchattenClass_one_primeGammaCofinalBocksteinDiagonalOperator_iff
    {t : ℝ} (ht : |t| < 1) :
    MemSchattenClass 1 (primeGammaCofinalBocksteinDiagonalOperator t ht) ↔ t = 0 := by
  constructor
  · intro hT
    have hdiag := hT.one_summable_norm_inner_diag_basis (HilbertSchmidt.lpBasis ℕ)
    have hnat : Summable (fun n : ℕ ↦
        ‖primeGammaCofinalBocksteinDiagonalMultiplier t n‖) := by
      refine hdiag.congr (fun n ↦ ?_)
      rw [HilbertSchmidt.lpBasis_apply]
      rw [primeGammaCofinalBocksteinDiagonalOperator]
      rw [diagonalOperator_single]
      rw [lp.inner_single_left]
      simp
    have hprime : Summable (primeGammaCofinalBocksteinMagnitude t) := by
      apply natEquivPrimes.summable_iff.mp
      exact hnat.congr (fun n ↦ by
        simp only [primeGammaCofinalBocksteinDiagonalMultiplier,
          Complex.norm_real, Real.norm_eq_abs]
        rfl)
    exact summable_primeGammaCofinalBocksteinMagnitude_iff.mp hprime
  · rintro rfl
    apply memSchattenClass_of_hasRankLE one_pos (n := 0)
    rw [show primeGammaCofinalBocksteinDiagonalOperator 0 (by norm_num) =
        (0 : EllTwo →L[ℂ] EllTwo) by
      apply ContinuousLinearMap.ext
      intro f
      ext n
      simp [primeGammaCofinalBocksteinDiagonalOperator,
        primeGammaCofinalBocksteinDiagonalMultiplier,
        primeGammaCofinalBocksteinCoefficient]]
    exact hasRankLE_zero 0

/-- Clause (3): every norm-closed class containing the finite-rank prime-diagonal operators
contains the literal Gamma defect throughout the open strip.  In particular this applies to every
norm-closed two-sided ideal with the card's stated containment property. -/
theorem primeGammaCofinalBocksteinDiagonalOperator_mem_of_isClosed_of_contains_finiteRankDiagonal
    {t : ℝ} (ht : |t| < 1)
    (J : Set (EllTwo →L[ℂ] EllTwo)) (hJ : IsClosed J)
    (hfiniteDiagonal : ∀ F : EllTwo →L[ℂ] EllTwo,
      IsFiniteRankDiagonal (HilbertSchmidt.lpBasis ℕ) F → F ∈ J) :
    primeGammaCofinalBocksteinDiagonalOperator t ht ∈ J := by
  apply mem_closedSet_of_diag_tendsto_cofinite_of_contains_finiteRankDiagonal
    (b := HilbertSchmidt.lpBasis ℕ)
    (c := primeGammaCofinalBocksteinDiagonalMultiplier t)
    (J := J) (hJ := hJ) (hfiniteDiagonal := hfiniteDiagonal)
  · intro i
    rw [HilbertSchmidt.lpBasis_apply]
    rw [primeGammaCofinalBocksteinDiagonalOperator, diagonalOperator_single]
    ext n
    by_cases h : n = i
    · subst h; simp [lp.single_apply]
    · simp [lp.single_apply, h]
  · rw [Nat.cofinite_eq_atTop]
    exact tendsto_norm_primeGammaCofinalBocksteinDiagonalMultiplier_zero ht

end
end RHTower
