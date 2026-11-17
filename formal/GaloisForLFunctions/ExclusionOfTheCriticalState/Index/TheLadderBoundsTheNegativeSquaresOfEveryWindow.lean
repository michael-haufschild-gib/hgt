import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder

/-!
# The ladder bounds the negative squares of every window

A critical ladder `Φ_0, …, Φ_m` at ratios `W₀ = R_0 ≤ … ≤ R_m` splits the confined form: for `Z`
`W₈`-orthogonal to the rungs, `Q_r(Z + Σ c_i Φ_i) = Q_r(Z) + Σ c_i² (a(r) − a(R_i)) W₈(Φ_i)`
(`fullEnergy_add_sum_nullVectors`), and `Q_r(Z) ≥ 0` for `r ≤ R_m` (the floor of the ladder).

* **Upper bound** (`IsCriticalLadder.hermNegIndex_confinedGram_le`). For `0 < r ≤ R_m` the confined
  Gram matrix of any finite family of half-line tests (tests supported in a window `[−A, 0]`) has at
  most `#{i : R_i < r}` negative squares: a real negative direction orthogonal to the rungs below `r`
  splits into a part orthogonal to all rungs and rungs at or above `r`, all of nonnegative energy.
* **The rungs realize the count** (`IsCriticalLadder.fullEnergy_sum_neg`): every nonzero combination of
  the rungs below `r` has negative energy at ratio `r`.
* **Transport to windows** (`IsCriticalLadder.hermNegIndex_confinedGram_le_of_le`): at a ratio
  `r ≤ R_k` no family of window tests carries `k + 1` negative squares. The ratio at which the window
  pictures first carry `k + 1` negative squares is at least the `k`-th rung of the ladder; for `k = 0`
  this is `W₀ ≤ R₁(A)`.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Matrix

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  HTGeometry HeckeKreinToeplitz

local notation "W8" => criticalHalfLineExponentialPair

variable {m : ℕ} {R : Fin (m + 1) → ℝ} {Φ : Fin (m + 1) → ℝ → ℝ}

private theorem alias_lt {R S : ℝ} (hR : 0 < R) (hRS : R < S) :
    criticalAliasCoefficient S < criticalAliasCoefficient R := by
  rw [criticalAliasCoefficient_eq_div R, criticalAliasCoefficient_eq_div S]
  exact div_lt_div_of_pos_left (criticalAliasCoefficient_positive one_pos) hR hRS

/-- **The ladder bounds the index at every ratio up to its top.** For `0 < r ≤ R_m` the confined
Gram matrix of half-line tests has at most `#{i : R_i < r}` negative squares. -/
theorem IsCriticalLadder.hermNegIndex_confinedGram_le (hL : IsCriticalLadder m R Φ) {r : ℝ}
    (hr0 : 0 < r) (hrm : r ≤ R (Fin.last m)) {S : Finset ℝ} {H : S → ℝ → ℝ}
    (hH : ∀ s, IsHalfLineTest (H s)) :
    hermNegIndex (confinedGram r H) ≤ (Finset.univ.filter fun i => R i < r).card := by
  classical
  set L : Finset (Fin (m + 1)) := Finset.univ.filter fun i => R i < r with hLdef
  by_contra hcon
  have hN : L.card + 1 ≤ hermNegIndex (confinedGram r H) := by omega
  set e : Fin L.card ≃ L := L.equivFin.symm
  have hD : ∀ i, CriticalHalfLineEnergyDomain (Φ i) := fun i => (hL.null i).1
  obtain ⟨X, hX, hXQ, hXo⟩ := exists_real_negative_orthogonal_family hH hN
    (Φ := fun j => Φ (e j : Fin (m + 1))) fun j => hD _
  -- the negative direction is orthogonal to every rung below the ratio
  have hXlow : ∀ i, R i < r → W8 (Φ i) X = 0 := by
    intro i hi
    have hmem : i ∈ L := Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    have h := hXo (e.symm ⟨i, hmem⟩)
    simpa using h
  have hpos : ∀ i, 0 < W8 (Φ i) (Φ i) := fun i => exponentialPair_self_pos (hD i) (hL.null i).2.1
  -- remove its components along the rungs at or above the ratio
  set P : Finset (Fin (m + 1)) := Finset.univ.filter fun i => r ≤ R i with hPdef
  set c : Fin (m + 1) → ℝ := fun i => W8 (Φ i) X / W8 (Φ i) (Φ i)
  set Z : ℝ → ℝ := fun u => X u + ∑ i ∈ P, (-c i) * Φ i u with hZdef
  have hZ : CriticalHalfLineEnergyDomain Z := criticalHalfLineEnergyDomain_add_sum hX hD _ P
  have hZo : ∀ i, W8 (Φ i) Z = 0 := by
    intro i
    rw [hZdef, exponentialPair_add_sum (hD i) hX hD _ P]
    by_cases hi : i ∈ P
    · rw [Finset.sum_eq_single i (fun j _ hji => by rw [hL.orth i j (Ne.symm hji), mul_zero])
        (fun h => absurd hi h), neg_mul, div_mul_cancel₀ _ (hpos i).ne', add_neg_cancel]
    · rw [Finset.sum_eq_zero fun j hj => by
          rw [hL.orth i j (fun h => hi (by rw [h]; exact hj)), mul_zero], add_zero]
      refine hXlow i ?_
      simpa [hPdef] using hi
  have hXZ : X = fun u => Z u + ∑ i ∈ P, c i * Φ i u := by
    funext u
    simp only [hZdef, neg_mul, Finset.sum_neg_distrib]
    ring
  have hexp := fullEnergy_add_sum_nullVectors r hL.null hL.orth hZ hZo c P
  rw [← hXZ] at hexp
  have hfl := hL.floor r hr0 hrm Z hZ hZo
  have hsum : 0 ≤ ∑ i ∈ P, c i ^ 2 *
      ((criticalAliasCoefficient r - criticalAliasCoefficient (R i)) * W8 (Φ i) (Φ i)) := by
    refine Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (mul_nonneg ?_ (hpos i).le)
    have := criticalAliasCoefficient_antitone hr0 (Finset.mem_filter.1 hi).2
    linarith
  linarith

/-- **The rungs below `r` are a negative space at ratio `r`.** A combination of rungs that vanishes
on the rungs at or above `r` and not on all rungs below `r` has negative energy at ratio `r`. -/
theorem IsCriticalLadder.fullEnergy_sum_neg (hL : IsCriticalLadder m R Φ) {r : ℝ} (hr0 : 0 < r)
    (c : Fin (m + 1) → ℝ) (hc0 : ∀ i, r ≤ R i → c i = 0) (hc : ∃ i, R i < r ∧ c i ≠ 0) :
    criticalHalfLineFullEnergy r (fun u => ∑ i, c i * Φ i u) < 0 := by
  classical
  have hD : ∀ i, CriticalHalfLineEnergyDomain (Φ i) := fun i => (hL.null i).1
  have hpos : ∀ i, 0 < W8 (Φ i) (Φ i) := fun i => exponentialPair_self_pos (hD i) (hL.null i).2.1
  have h0 : CriticalHalfLineEnergyDomain (fun u => (0 : ℝ) * Φ 0 u) := (hD 0).const_mul 0
  have h0o : ∀ i, W8 (Φ i) (fun u => (0 : ℝ) * Φ 0 u) = 0 := fun i => by
    rw [exponentialPair_const_mul, zero_mul]
  have hexp := fullEnergy_add_sum_nullVectors r hL.null hL.orth h0 h0o c Finset.univ
  have e : (fun u => (0 : ℝ) * Φ 0 u + ∑ i, c i * Φ i u) = fun u => ∑ i, c i * Φ i u := by
    funext u; ring
  rw [e, criticalHalfLineFullEnergy_const_mul, zero_pow two_ne_zero, zero_mul, zero_add] at hexp
  rw [hexp]
  obtain ⟨i₀, hi₀, hc₀⟩ := hc
  set f : Fin (m + 1) → ℝ := fun i => c i ^ 2 *
    ((criticalAliasCoefficient r - criticalAliasCoefficient (R i)) * W8 (Φ i) (Φ i))
  have hf : ∀ i, f i ≤ 0 := by
    intro i
    rcases lt_or_ge (R i) r with h | h
    · have := alias_lt (hL.pos i) h
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (hpos i).le)
    · simp only [f, hc0 i h]; ring_nf; exact le_rfl
  have hf₀ : f i₀ < 0 := by
    have := alias_lt (hL.pos i₀) hi₀
    exact mul_neg_of_pos_of_neg (pow_pos_of_ne_zero' hc₀)
      (mul_neg_of_neg_of_pos (by linarith) (hpos i₀))
  have hle : ∑ i, f i ≤ f i₀ := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => -f i)
      (Finset.singleton_subset_iff.2 (Finset.mem_univ i₀)) (fun i _ _ => by linarith [hf i])
    simp only [Finset.sum_singleton, Finset.sum_neg_distrib] at h
    linarith
  exact hle.trans_lt hf₀

/-- **Transport to windows.** At a ratio `0 < r ≤ R_k` no family of half-line (window) tests has
more than `k` negative squares: the windows reach `k + 1` negative squares only beyond the
`k`-th rung. -/
theorem IsCriticalLadder.hermNegIndex_confinedGram_le_of_le (hL : IsCriticalLadder m R Φ)
    (k : Fin (m + 1)) {r : ℝ} (hr0 : 0 < r) (hrk : r ≤ R k) {S : Finset ℝ} {H : S → ℝ → ℝ}
    (hH : ∀ s, IsHalfLineTest (H s)) : hermNegIndex (confinedGram r H) ≤ k := by
  classical
  have hle := hL.hermNegIndex_confinedGram_le hr0 (hrk.trans (hL.mono (Fin.le_last k))) hH
  refine hle.trans ?_
  have hsub : (Finset.univ.filter fun i => R i < r) ⊆ Finset.Iio k := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    refine Finset.mem_Iio.2 (lt_of_not_ge fun hki => ?_)
    have := hL.mono hki
    linarith
  exact (Finset.card_le_card hsub).trans (by simp)

end GaloisForLFunctions.ExclusionOfTheCriticalState

#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.IsCriticalLadder.hermNegIndex_confinedGram_le
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.IsCriticalLadder.fullEnergy_sum_neg
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.IsCriticalLadder.hermNegIndex_confinedGram_le_of_le
