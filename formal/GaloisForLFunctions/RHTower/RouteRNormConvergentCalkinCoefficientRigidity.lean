import GaloisForLFunctions.RHTower.XiPrimeSeamSummableCalkinAggregate

/-!
# Route R norm-convergent Calkin coefficient rigidity

Absolute summability is not needed for all-prime Sonin Gram injectivity.  If coherent rectangular
sections approach arbitrary stage-dependent compact operators in operator norm, every stabilized
off-diagonal coefficient is zero.  The compact counterterms need not converge or remain bounded.
The proof applies the finite shell coefficient estimate separately at every stage and then sends
the rectangle size to infinity.

Thus conditionally norm-convergent or reordered coherent tails cannot cancel Route R's retained
finite cross-prime atom modulo compact operators.  A surviving renormalized producer must leave the
operator-norm Calkin-vanishing category.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **Eventual uniform Calkin gap.**  Once a fixed off-diagonal coefficient belongs to the
rectangle, its modulus is a lower bound for the distance to every compact operator. -/
theorem eventually_norm_matrixEntry_le_norm_rectangularEvenDilationGramCombination_sub_compact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    {i j : ℕ} (hij : i ≠ j) :
    ∀ᶠ N in atTop,
      ∀ K : evenSubspace →L[ℂ] evenSubspace,
        IsCompactOperator K →
          ‖A (i, j)‖ ≤
            ‖rectangularEvenDilationGramCombination a p hpReal A N - K‖ := by
  filter_upwards [eventually_ge_atTop (max i j + 1)] with N hN
  intro K hK
  let ii : Fin N := ⟨i, by omega⟩
  let jj : Fin N := ⟨j, by omega⟩
  have hijFin : jj ≠ ii := by
    intro h
    apply hij
    exact congrArg Fin.val h |>.symm
  have hle := norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
    a ha (fun k : Fin N => p k) (fun k => hp k)
    (fun _ _ h => Fin.ext (hinj h))
    (fun k l : Fin N => A (k, l)) jj ii hijFin K hK
  rw [finiteEvenDilationGramCombination_eq_rectangle a p hpReal A N] at hle
  simpa [ii, jj] using hle

/-- A retained coefficient forbids even frequently recurring compact approximations below its
fixed modulus.  Hence no subsequence or cofinal subnet can have Calkin distance tending to zero. -/
theorem not_frequently_exists_compact_norm_rectangularEvenDilationGramCombination_sub_lt_entry
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    {i j : ℕ} (hij : i ≠ j) :
    ¬∃ᶠ N in atTop,
      ∃ K : evenSubspace →L[ℂ] evenSubspace,
        IsCompactOperator K ∧
          ‖rectangularEvenDilationGramCombination a p hpReal A N - K‖ <
            ‖A (i, j)‖ := by
  rw [Filter.not_frequently]
  filter_upwards
    [eventually_norm_matrixEntry_le_norm_rectangularEvenDilationGramCombination_sub_compact
      a ha p hp hpReal hinj A hij] with N hN
  rintro ⟨K, hK, hlt⟩
  exact (not_lt_of_ge (hN K hK)) hlt

/-- Finite Sonin Gram stage with a coefficient matrix allowed to vary arbitrarily with cutoff. -/
def varyingRectangularEvenDilationGramCombination
    (a : ℝ) (p : ℕ → ℕ) (hpReal : ∀ i, 1 < (p i : ℝ))
    (A : ℕ → ℕ × ℕ → ℂ) (N : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  finiteEvenDilationGramCombination a
    (fun i : Fin N => (p i : ℝ)) (fun i => hpReal i)
    (fun i j : Fin N => A N (i, j))

/-- A varying finite-stage coefficient still has its full modulus recovered from Calkin distance
once its two indices enter the cutoff. -/
theorem eventually_norm_varyingMatrixEntry_le_norm_varyingRectangularGram_sub_compact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ → ℕ × ℕ → ℂ)
    {i j : ℕ} (hij : i ≠ j) :
    ∀ᶠ N in atTop,
      ∀ K : evenSubspace →L[ℂ] evenSubspace,
        IsCompactOperator K →
          ‖A N (i, j)‖ ≤
            ‖varyingRectangularEvenDilationGramCombination a p hpReal A N - K‖ := by
  filter_upwards [eventually_ge_atTop (max i j + 1)] with N hN
  intro K hK
  let ii : Fin N := ⟨i, by omega⟩
  let jj : Fin N := ⟨j, by omega⟩
  have hijFin : jj ≠ ii := by
    intro h
    apply hij
    exact congrArg Fin.val h |>.symm
  have hle := norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
    a ha (fun k : Fin N => p k) (fun k => hp k)
    (fun _ _ h => Fin.ext (hinj h))
    (fun k l : Fin N => A N (k, l)) jj ii hijFin K hK
  simpa [varyingRectangularEvenDilationGramCombination, ii, jj] using hle

/-- **Renormalized coefficient rigidity.**  If arbitrary varying finite-stage Sonin Gram operators
approach arbitrary compact counterterms in operator norm, every asymptotically recovered selected
coefficient has zero limit. -/
theorem coefficientLimit_eq_zero_of_varyingRectangularGram_tendsto_stageCompact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ → ℕ × ℕ → ℂ)
    {i j : ℕ} (hij : i ≠ j) (c : ℂ)
    (hcoeff : Tendsto (fun N => A N (i, j)) atTop (nhds c))
    (K : ℕ → evenSubspace →L[ℂ] evenSubspace)
    (hK : ∀ N, IsCompactOperator (K N))
    (hconv : Tendsto (fun N =>
      ‖varyingRectangularEvenDilationGramCombination a p hpReal A N - K N‖)
        atTop (nhds 0)) :
    c = 0 := by
  have hbound : ∀ᶠ N in atTop,
      ‖A N (i, j)‖ ≤
        ‖varyingRectangularEvenDilationGramCombination a p hpReal A N - K N‖ := by
    filter_upwards
      [eventually_norm_varyingMatrixEntry_le_norm_varyingRectangularGram_sub_compact
        a ha p hp hpReal hinj A hij] with N hN
    exact hN (K N) (hK N)
  have hnormzero : Tendsto (fun N => ‖A N (i, j)‖) atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hbound hconv
  have hcNorm : ‖c‖ = 0 := tendsto_nhds_unique hcoeff.norm hnormzero
  exact norm_eq_zero.mp hcNorm

/-- No varying finite-stage renormalization can recover a prescribed nonzero coefficient while
approaching compact counterterms in operator norm. -/
theorem no_varyingRectangularGram_stageCompact_renormalization_of_coefficientLimit_ne_zero
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ → ℕ × ℕ → ℂ)
    {i j : ℕ} (hij : i ≠ j) {c : ℂ} (hc : c ≠ 0)
    (hcoeff : Tendsto (fun N => A N (i, j)) atTop (nhds c)) :
    ¬∃ K : ℕ → evenSubspace →L[ℂ] evenSubspace,
      (∀ N, IsCompactOperator (K N)) ∧
        Tendsto (fun N =>
          ‖varyingRectangularEvenDilationGramCombination a p hpReal A N - K N‖)
            atTop (nhds 0) := by
  rintro ⟨K, hK, hconv⟩
  exact hc
    (coefficientLimit_eq_zero_of_varyingRectangularGram_tendsto_stageCompact
      a ha p hp hpReal hinj A hij c hcoeff K hK hconv)

/-- **Stage-dependent compact rigidity.**  Every stabilized off-diagonal coefficient vanishes if
coherent rectangular Sonin Gram sections approach arbitrary compact counterterms in operator norm.
The compact counterterms need not converge or be uniformly bounded. -/
theorem matrixEntry_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_stageCompact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    (K : ℕ → evenSubspace →L[ℂ] evenSubspace)
    (hK : ∀ N, IsCompactOperator (K N))
    (hconv : Tendsto (fun N =>
      ‖rectangularEvenDilationGramCombination a p hpReal A N - K N‖)
        atTop (nhds 0))
    {i j : ℕ} (hij : i ≠ j) :
    A (i, j) = 0 := by
  have hbound : ∀ᶠ N in atTop,
      ‖A (i, j)‖ ≤
        ‖rectangularEvenDilationGramCombination a p hpReal A N - K N‖ := by
    filter_upwards [eventually_ge_atTop (max i j + 1)] with N hN
    let ii : Fin N := ⟨i, by omega⟩
    let jj : Fin N := ⟨j, by omega⟩
    have hijFin : jj ≠ ii := by
      intro h
      apply hij
      exact congrArg Fin.val h |>.symm
    have hle := norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
      a ha (fun k : Fin N => p k) (fun k => hp k)
      (fun _ _ h => Fin.ext (hinj h))
      (fun k l : Fin N => A (k, l)) jj ii hijFin (K N) (hK N)
    rw [finiteEvenDilationGramCombination_eq_rectangle a p hpReal A N] at hle
    simpa [ii, jj] using hle
  have hle : ‖A (i, j)‖ ≤ 0 := ge_of_tendsto hconv hbound
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

/-- Every stabilized off-diagonal coefficient vanishes when coherent rectangular Sonin Gram
sections converge in operator norm to a compact operator.  No summability hypothesis occurs. -/
theorem matrixEntry_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_compact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K)
    (hconv : Tendsto (fun N =>
      ‖rectangularEvenDilationGramCombination a p hpReal A N - K‖)
        atTop (nhds 0))
    {i j : ℕ} (hij : i ≠ j) :
    A (i, j) = 0 := by
  have hbound : ∀ᶠ N in atTop,
      ‖A (i, j)‖ ≤
        ‖rectangularEvenDilationGramCombination a p hpReal A N - K‖ := by
    filter_upwards [eventually_ge_atTop (max i j + 1)] with N hN
    let ii : Fin N := ⟨i, by omega⟩
    let jj : Fin N := ⟨j, by omega⟩
    have hijFin : jj ≠ ii := by
      intro h
      apply hij
      exact congrArg Fin.val h |>.symm
    have hle := norm_matrixEntry_le_norm_finitePrimeEvenDilationGram_sub_compact
      a ha (fun k : Fin N => p k) (fun k => hp k)
      (fun _ _ h => Fin.ext (hinj h))
      (fun k l : Fin N => A (k, l)) jj ii hijFin K hK
    rw [finiteEvenDilationGramCombination_eq_rectangle a p hpReal A N] at hle
    simpa [ii, jj] using hle
  have hle : ‖A (i, j)‖ ≤ 0 := ge_of_tendsto hconv hbound
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

/-- **Norm-convergent infinite Calkin injectivity.**  A coherent zero-diagonal all-prime matrix
whose rectangular Sonin Gram sections have a compact operator-norm limit is identically zero. -/
theorem coefficients_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_compact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    (hdiag : ∀ i, A (i, i) = 0)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K)
    (hconv : Tendsto (fun N =>
      ‖rectangularEvenDilationGramCombination a p hpReal A N - K‖)
        atTop (nhds 0)) :
    A = 0 := by
  funext ij
  rcases ij with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · exact
      matrixEntry_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_compact
        a ha p hp hpReal hinj A K hK hconv hij

/-- A single retained nonzero off-diagonal coefficient forbids every compact operator-norm limit
of the coherent rectangular exhaustion. -/
theorem no_compact_normLimit_rectangularEvenDilationGramCombination_of_entry_ne_zero
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    {i j : ℕ} (hij : i ≠ j) (hAij : A (i, j) ≠ 0) :
    ¬∃ K : evenSubspace →L[ℂ] evenSubspace,
      IsCompactOperator K ∧
        Tendsto (fun N =>
          ‖rectangularEvenDilationGramCombination a p hpReal A N - K‖)
            atTop (nhds 0) := by
  rintro ⟨K, hK, hconv⟩
  exact hAij
    (matrixEntry_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_compact
      a ha p hp hpReal hinj A K hK hconv hij)

/-- A zero-diagonal coherent matrix is zero if its rectangular Sonin Gram sections approach any
stage-dependent compact counterterms in operator norm. -/
theorem coefficients_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_stageCompact
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    (hdiag : ∀ i, A (i, i) = 0)
    (K : ℕ → evenSubspace →L[ℂ] evenSubspace)
    (hK : ∀ N, IsCompactOperator (K N))
    (hconv : Tendsto (fun N =>
      ‖rectangularEvenDilationGramCombination a p hpReal A N - K N‖)
        atTop (nhds 0)) :
    A = 0 := by
  funext ij
  rcases ij with ⟨i, j⟩
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · exact
      matrixEntry_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_stageCompact
        a ha p hp hpReal hinj A K hK hconv hij

/-- One retained nonzero coefficient forbids asymptotic operator-norm cancellation by arbitrary
stage-dependent compact counterterms. -/
theorem no_stageCompact_approximation_rectangularEvenDilationGramCombination_of_entry_ne_zero
    (a : ℝ) (ha : 0 < a) (p : ℕ → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hpReal : ∀ i, 1 < (p i : ℝ))
    (hinj : Function.Injective p) (A : ℕ × ℕ → ℂ)
    {i j : ℕ} (hij : i ≠ j) (hAij : A (i, j) ≠ 0) :
    ¬∃ K : ℕ → evenSubspace →L[ℂ] evenSubspace,
      (∀ N, IsCompactOperator (K N)) ∧
        Tendsto (fun N =>
          ‖rectangularEvenDilationGramCombination a p hpReal A N - K N‖)
            atTop (nhds 0) := by
  rintro ⟨K, hK, hconv⟩
  exact hAij
    (matrixEntry_eq_zero_of_rectangularEvenDilationGramCombination_tendsto_stageCompact
      a ha p hp hpReal hinj A K hK hconv hij)

end

end RHTower
