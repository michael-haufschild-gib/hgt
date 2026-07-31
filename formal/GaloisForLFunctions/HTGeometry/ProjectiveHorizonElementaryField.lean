import GaloisForLFunctions.HTGeometry.ProjectiveHorizonChartCoordinateEquiv

/-!
# The exact elementary horizon field

Under the chart coordinate isomorphism the chart unipotent group acts by translating the
zeroth-order chart coordinates and fixing everything else: the denominator tower and the
positive-order chart jets.  Transporting the translation fixed-field theorem therefore identifies
the horizon field of an elementary covector span exactly.

`mathcal H_(ker e_i^*) = C(X_(i,l) : l) . C(x_k^(m) : k ≠ i, m ≥ 1)`

is the full-field form of the chart horizon law, and the `N-1` zeroth-order chart coordinates are
the complementary directions, matching the rank-one codimension `1·N-1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The chart unipotent group on the chart basis -/

theorem linearJetAction_chartBasis_chartUnitTranslation {i k : n} (hk : k ≠ i) (q : n × ℕ) :
    (chartUnitTranslation (K := K) hk) • chartBasis i q =
      chartBasis i q +
        algebraMap K (HomogeneousJetField n K) (if q = (k, 0) then 1 else 0) := by
  obtain ⟨m, l⟩ := q
  rw [chartBasis]
  by_cases hm : m = i
  · rw [if_pos hm]
    have hfix := (mem_horizonField_iff'.1
      (freeCoordinate_mem_horizonField_self (K := K) i l)) _ (chartUnitTranslation_mem hk)
    have hq : ((m, l) : n × ℕ) ≠ (k, 0) := by
      intro hcon
      exact hk (hm ▸ (congrArg Prod.fst hcon).symm)
    rw [if_neg hq, map_zero, add_zero, hm]
    exact hfix
  · rw [if_neg hm]
    cases l with
    | zero =>
        rw [affineJet_zero, linearJetAction_affineCoord_of_mem hm (chartUnitTranslation_mem hk),
          chartUnitTranslation_inv_apply hk m hm]
        congr 2
        by_cases hmk : m = k
        · simp [hmk]
        · simp [hmk, Prod.ext_iff]
    | succ l =>
        rw [linearJetAction_affineJet_succ_of_mem hm l (chartUnitTranslation_mem hk)]
        have hq : ((m, l + 1) : n × ℕ) ≠ (k, 0) := by
          intro hcon
          exact Nat.succ_ne_zero l (congrArg Prod.snd hcon)
        rw [if_neg hq, map_zero, add_zero]

theorem basisEval_translation {i k : n} (hk : k ≠ i)
    (z : FreeCoordinateRationalField K (n × ℕ)) :
    basisEval i (freeCoordinateTranslationAt K (n × ℕ) (k, 0) 1 z) =
      (chartUnitTranslation (K := K) hk) • basisEval i z := by
  classical
  have hgen : ∀ q : n × ℕ,
      basisEval i (freeCoordinateTranslationAt K (n × ℕ) (k, 0) 1
          (freeCoordinate K (n × ℕ) q)) =
        (chartUnitTranslation (K := K) hk) • basisEval i (freeCoordinate K (n × ℕ) q) := by
    intro q
    rw [basisEval_freeCoordinate, linearJetAction_chartBasis_chartUnitTranslation hk]
    rcases eq_or_ne q (k, 0) with rfl | hq
    · rw [freeCoordinateTranslationAt_self, map_add, basisEval_freeCoordinate,
        AlgHom.commutes, if_pos rfl]
    · rw [freeCoordinateTranslationAt_of_ne hq, basisEval_freeCoordinate, if_neg hq,
        map_zero, add_zero]
  have hL : ((basisEval (K := K) i).comp
      (((freeCoordinateTranslationAt K (n × ℕ) (k, 0) 1).toAlgHom).comp
        (IsScalarTower.toAlgHom K (MvPolynomial (n × ℕ) K)
          (FreeCoordinateRationalField K (n × ℕ))))) =
      (((linearJetFieldEquiv (chartUnitTranslation (K := K) hk)).toAlgHom).comp
        ((basisEval (K := K) i).comp
          (IsScalarTower.toAlgHom K (MvPolynomial (n × ℕ) K)
            (FreeCoordinateRationalField K (n × ℕ))))) := by
    apply MvPolynomial.algHom_ext
    intro q
    show basisEval i (freeCoordinateTranslationAt K (n × ℕ) (k, 0) 1
        (freeCoordinate K (n × ℕ) q)) =
      (chartUnitTranslation (K := K) hk) • basisEval i (freeCoordinate K (n × ℕ) q)
    exact hgen q
  have hpoly : ∀ p : MvPolynomial (n × ℕ) K,
      basisEval i (freeCoordinateTranslationAt K (n × ℕ) (k, 0) 1
          (algebraMap (MvPolynomial (n × ℕ) K)
            (FreeCoordinateRationalField K (n × ℕ)) p)) =
        (chartUnitTranslation (K := K) hk) •
          basisEval i (algebraMap (MvPolynomial (n × ℕ) K)
            (FreeCoordinateRationalField K (n × ℕ)) p) := fun p => AlgHom.congr_fun hL p
  obtain ⟨a, b, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial (n × ℕ) K) z
  rw [map_div₀, map_div₀, hpoly, hpoly]
  simp only [linearJetAction_apply, map_div₀]

/-! ## The exact elementary horizon field -/

/-- Indices of the chart basis that survive in the horizon field. -/
def chartHorizonIndex (i : n) : Set (n × ℕ) := {q | q.1 = i ∨ 1 ≤ q.2}

omit [Fintype n] [DecidableEq n] in
theorem notMem_chartHorizonIndex_iff {i : n} {q : n × ℕ} :
    q ∉ chartHorizonIndex i ↔ q.1 ≠ i ∧ q.2 = 0 := by
  constructor
  · intro hq
    constructor
    · intro hcon
      exact hq (Or.inl hcon)
    · by_contra hcon
      exact hq (Or.inr (Nat.one_le_iff_ne_zero.2 hcon))
  · rintro ⟨h1, h2⟩ (hcon | hcon)
    · exact h1 hcon
    · omega

omit [Fintype n] in
theorem basisEval_mem_chartHorizonAdjoin (i : n)
    {w : FreeCoordinateRationalField K (n × ℕ)}
    (hw : w ∈ freeCoordinateField K (n × ℕ) (chartHorizonIndex i)) :
    basisEval i w ∈ IntermediateField.adjoin K (chartHorizonGenerators i K) := by
  refine IntermediateField.adjoin_induction K
    (s := freeCoordinate K (n × ℕ) '' chartHorizonIndex i)
    (p := fun y _ => basisEval (K := K) i y ∈
      IntermediateField.adjoin K (chartHorizonGenerators i K)) ?_ ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨⟨m, l⟩, hq, rfl⟩
    rw [basisEval_freeCoordinate, chartBasis]
    by_cases hm : m = i
    · rw [if_pos hm, hm]
      exact IntermediateField.subset_adjoin K _ (Or.inl ⟨l, rfl⟩)
    · rw [if_neg hm]
      rcases hq with hcon | hl
      · exact absurd hcon hm
      · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by simp only at hl; omega⟩
        exact IntermediateField.subset_adjoin K _ (Or.inr ⟨m, hm, l', rfl⟩)
  · intro c
    rw [AlgHom.commutes]
    exact (IntermediateField.adjoin K _).algebraMap_mem c
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro x _ hx
    rw [map_inv₀]
    exact inv_mem hx
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy

/-- **Exact elementary horizon field.**  The horizon field of `ker e_i^*` is generated by the tower
of the chart denominator together with the positive-order chart jets. -/
theorem horizonField_singleton_eq [CharZero K] (i : n) :
    horizonField (K := K) {i} = IntermediateField.adjoin K (chartHorizonGenerators i K) := by
  refine le_antisymm ?_ (chartHorizonGenerators_adjoin_le_horizonField i)
  intro f hf
  obtain ⟨z, rfl⟩ := basisEval_surjective (K := K) i f
  have hz : z ∈ freeCoordinateField K (n × ℕ) (chartHorizonIndex i) := by
    rw [mem_freeCoordinateField_iff]
    intro q hq
    obtain ⟨hqi, hq0⟩ := notMem_chartHorizonIndex_iff.1 hq
    obtain ⟨k, l⟩ := q
    simp only at hqi hq0
    subst hq0
    have hfixed : freeCoordinateTranslationAt K (n × ℕ) (k, 0) 1 z = z := by
      apply basisEval_injective i
      rw [basisEval_translation hqi]
      exact (mem_horizonField_iff'.1 hf) _ (chartUnitTranslation_mem hqi)
    have hcompl :=
      mem_freeCoordinateField_complement_of_unitTranslation_fixed
        (C := K) (σ := n × ℕ) ((k, 0) : n × ℕ) hfixed
    exact (mem_freeCoordinateField_iff ({((k, 0) : n × ℕ)}ᶜ) z).1 hcompl (k, 0) (by simp)
  exact basisEval_mem_chartHorizonAdjoin i hz

end

end GaloisForLFunctions.HTGeometry
