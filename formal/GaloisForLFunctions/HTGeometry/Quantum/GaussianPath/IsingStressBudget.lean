import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsingStressCalibration

/-!
# Exact diagonal stress at every energy budget

The upper endpoint is the largest stress of a feasible basis configuration
or of a chord crossing the budget. Pairwise chord inequalities provide a
single nonnegative supporting slope, which certifies the bound for every
prepared state.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FiniteStrain

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private def admissibleStressBudgetCandidate (a : ι → ℝ) (B : ℝ) : ι ⊕ (ι × ι) → Prop
  | .inl i => a i ≤ B
  | .inr (i, j) => a i < B ∧ B < a j

private def stressBudgetCandidates (a : ι → ℝ) (B : ℝ) : Finset (ι ⊕ (ι × ι)) := by
  classical
  exact Finset.univ.filter (admissibleStressBudgetCandidate a B)

omit [Nonempty ι] in
private theorem mem_stressBudgetCandidates (a : ι → ℝ) (B : ℝ) (c : ι ⊕ (ι × ι)) :
    c ∈ stressBudgetCandidates a B ↔ admissibleStressBudgetCandidate a B c := by
  classical
  simp [stressBudgetCandidates]

private theorem stressBudgetCandidates_nonempty (a : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) :
    (stressBudgetCandidates a B).Nonempty := by
  obtain ⟨i, hi⟩ := groundConfigurations_nonempty a
  have he := mem_groundConfigurations.mp hi
  exact ⟨.inl i, (mem_stressBudgetCandidates a B _).mpr (he.le.trans hB)⟩

private def stressBudgetCandidateValue (a b : ι → ℝ) (B : ℝ) : ι ⊕ (ι × ι) → ℝ
  | .inl i => b i
  | .inr (i, j) => b i + ((B - a i) / (a j - a i)) * (b j - b i)

/-- The largest stress among feasible basis states and chords that
cross the energy budget. -/
def bestStressUnderBudget (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) : ℝ :=
  (stressBudgetCandidates a B).sup' (stressBudgetCandidates_nonempty a B hB)
    (stressBudgetCandidateValue a b B)

theorem stress_le_bestStressUnderBudget (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B)
    (i : ι) (hi : a i ≤ B) : b i ≤ bestStressUnderBudget a b B hB :=
  Finset.le_sup' (stressBudgetCandidateValue a b B) ((mem_stressBudgetCandidates a B (.inl i)).mpr hi)

theorem chord_le_bestStressUnderBudget (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B)
    (i j : ι) (hi : a i < B) (hj : B < a j) :
    b i + ((B - a i) / (a j - a i)) * (b j - b i) ≤ bestStressUnderBudget a b B hB :=
  Finset.le_sup' (stressBudgetCandidateValue a b B) ((mem_stressBudgetCandidates a B (.inr (i, j))).mpr ⟨hi, hj⟩)

private theorem stressBudget_cross_ratio_le {ai aj bi bj B M : ℝ}
    (hi : ai < B) (hj : B < aj)
    (h : bi + ((B - ai) / (aj - ai)) * (bj - bi) ≤ M) :
    (bj - M) / (aj - B) ≤ (M - bi) / (B - ai) := by
  have hd : 0 < aj - ai := sub_pos.mpr (hi.trans hj)
  have hclear : bi * (aj - ai) + (B - ai) * (bj - bi) ≤ M * (aj - ai) := by
    calc
      _ = (bi + ((B - ai) / (aj - ai)) * (bj - bi)) * (aj - ai) := by
        rw [add_mul, mul_right_comm ((B - ai) / (aj - ai)), div_mul_cancel₀ _ hd.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right h hd.le
  exact (div_le_div_iff₀ (sub_pos.mpr hj) (sub_pos.mpr hi)).mpr (by nlinarith only [hclear])

/-- The finite envelope has a nonnegative supporting slope at the budget.
Each crossing chord makes the lower and upper constraints on this slope compatible. -/
theorem exists_bestStressUnderBudget_supporting_slope (a b : ι → ℝ) (B : ℝ)
    (hB : groundEnergy a ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i, b i ≤ bestStressUnderBudget a b B hB + L * (a i - B) := by
  let M := bestStressUnderBudget a b B hB
  let need (j : ι) := if B < a j then max 0 ((b j - M) / (a j - B)) else 0
  let L := Finset.univ.sup' Finset.univ_nonempty need
  have hneed (j : ι) : 0 ≤ need j := by
    unfold need
    split
    · exact le_max_left _ _
    · exact le_rfl
  have hL : 0 ≤ L := (hneed (Classical.choice ‹Nonempty ι›)).trans
    (Finset.le_sup' need (Finset.mem_univ _))
  have hlow (i : ι) (hi : a i < B) : L ≤ (M - b i) / (B - a i) := by
    have hnonneg : 0 ≤ (M - b i) / (B - a i) :=
      div_nonneg (sub_nonneg.mpr (stress_le_bestStressUnderBudget a b B hB i hi.le)) (sub_nonneg.mpr hi.le)
    apply Finset.sup'_le
    intro j _
    by_cases hj : B < a j
    · change need j ≤ _
      dsimp only [need]
      rw [if_pos hj]
      exact max_le hnonneg
        (stressBudget_cross_ratio_le hi hj (chord_le_bestStressUnderBudget a b B hB i j hi hj))
    · simpa only [need, if_neg hj] using hnonneg
  refine ⟨L, hL, fun i => ?_⟩
  change b i ≤ M + L * (a i - B)
  rcases lt_trichotomy (a i) B with hi | hi | hi
  · have he := (le_div_iff₀ (sub_pos.mpr hi)).mp (hlow i hi)
    nlinarith only [he]
  · rw [hi, sub_self, mul_zero, add_zero]
    exact stress_le_bestStressUnderBudget a b B hB i hi.le
  · have hr : (b i - M) / (a i - B) ≤ L := by
      have h := Finset.le_sup' need (Finset.mem_univ i)
      exact (le_max_right (0 : ℝ) _).trans (by simpa only [need, if_pos hi] using h)
    have he := (div_le_iff₀ (sub_pos.mpr hi)).mp hr
    linarith only [he]

omit [Nonempty ι] in
private theorem diagonalMean_le_of_affine_majorant (a b : ι → ℝ) (B M L : ℝ)
    {p : ι → ℝ} (hp : IsBasisLaw p) (hL : 0 ≤ L) (he : diagonalMean p a ≤ B)
    (hmajor : ∀ i, b i ≤ M + L * (a i - B)) : diagonalMean p b ≤ M := by
  calc
    _ ≤ ∑ i, p i * (M + L * (a i - B)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmajor i) (hp.1 i)
    _ = (∑ i, p i) * M + L * diagonalMean p (fun i => a i - B) := by
      rw [Finset.sum_mul, diagonalMean, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = M + L * (diagonalMean p a - B) := by
      rw [hp.2, one_mul, diagonalMean_sub_const hp]
    _ ≤ M := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hL (sub_nonpos.mpr he))

theorem diagonalMean_le_bestStressUnderBudget (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B)
    {p : ι → ℝ} (hp : IsBasisLaw p) (he : diagonalMean p a ≤ B) :
    diagonalMean p b ≤ bestStressUnderBudget a b B hB := by
  obtain ⟨L, hL, hmajor⟩ := exists_bestStressUnderBudget_supporting_slope a b B hB
  exact diagonalMean_le_of_affine_majorant a b B _ L hp hL he hmajor

/-- One feasible basis state or two configurations straddling the budget
attain the upper endpoint. In the latter case the preparation uses the full budget. -/
theorem exists_twoConfig_bestStressUnderBudget (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) :
    ∃ (i j : ι) (t : ℝ), t ∈ Icc 0 1 ∧
      (i = j ∨ (a i < B ∧ B < a j ∧
        diagonalMean (mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t) a = B)) ∧
      diagonalMean (mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t) a ≤ B ∧
      diagonalMean (mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t) b = bestStressUnderBudget a b B hB := by
  obtain ⟨c, hc, hmax⟩ := Finset.exists_mem_eq_sup'
    (stressBudgetCandidates_nonempty a B hB) (stressBudgetCandidateValue a b B)
  have hgood := (mem_stressBudgetCandidates a B c).mp hc
  rcases c with i | ⟨i, j⟩
  · have hi : a i ≤ B := hgood
    change bestStressUnderBudget a b B hB = b i at hmax
    refine ⟨i, i, 0, ⟨le_rfl, zero_le_one⟩, Or.inl rfl, ?_, ?_⟩
    · simpa only [diagonalMean_mix, diagonalMean_point, sub_zero, one_mul, zero_mul, add_zero] using hi
    · simp only [diagonalMean_mix, diagonalMean_point, sub_zero, one_mul, zero_mul, add_zero, hmax]
  · obtain ⟨hi, hj⟩ : a i < B ∧ B < a j := hgood
    let t := (B - a i) / (a j - a i)
    have hd : 0 < a j - a i := sub_pos.mpr (hi.trans hj)
    have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr hi.le) hd.le
    have ht₁ : t ≤ 1 := (div_le_iff₀ hd).mpr (by
      rw [one_mul]
      exact sub_le_sub_right hj.le _)
    have ht : t * (a j - a i) = B - a i := div_mul_cancel₀ _ hd.ne'
    have ha : diagonalMean (mixBasisLaw (pointBasisLaw i) (pointBasisLaw j) t) a = B := by
      rw [diagonalMean_mix, diagonalMean_point, diagonalMean_point]
      calc
        _ = a i + t * (a j - a i) := by ring
        _ = B := by rw [ht]; ring
    refine ⟨i, j, t, ⟨ht₀, ht₁⟩, Or.inr ⟨hi, hj, ha⟩, ha.le, ?_⟩
    change bestStressUnderBudget a b B hB = b i + t * (b j - b i) at hmax
    rw [diagonalMean_mix, diagonalMean_point, diagonalMean_point, hmax]
    ring

/-- The exact optimum is attained by a normalized pure preparation
and bounds every normalized pure preparation with feasible energy. -/
theorem bestStressUnderBudget_isGreatest (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) :
    IsGreatest
      {s | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a ≤ B ∧ pureDiagonalMean ψ b = s}
      (bestStressUnderBudget a b B hB) := by
  constructor
  · obtain ⟨i, j, t, ht, _, ha, hb⟩ := exists_twoConfig_bestStressUnderBudget a b B hB
    have hp := isBasisLaw_mix (isBasisLaw_point i) (isBasisLaw_point j) ht.1 ht.2
    obtain ⟨ψ, hψ, hprob⟩ := exists_pureBasisLaw hp
    exact ⟨ψ, hψ, by rwa [pureDiagonalMean, hprob], by rwa [pureDiagonalMean, hprob]⟩
  · rintro _ ⟨ψ, hψ, ha, rfl⟩
    exact diagonalMean_le_bestStressUnderBudget a b B hB (isBasisLaw_pure ψ hψ) ha

theorem exists_pureState_underEnergyBudget_iff (a : ι → ℝ) (B : ℝ) :
    (∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a ≤ B) ↔ groundEnergy a ≤ B := by
  constructor
  · rintro ⟨ψ, hψ, ha⟩
    exact (groundEnergy_le_diagonalMean a (isBasisLaw_pure ψ hψ)).trans ha
  · intro hB
    obtain ⟨ψ, hψ, ha, _⟩ := (bestStressUnderBudget_isGreatest a a B hB).1
    exact ⟨ψ, hψ, ha⟩

/-- Negating stress converts the lower endpoint to the same finite optimum. -/
def leastStressUnderBudget (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) : ℝ :=
  -bestStressUnderBudget a (fun i => -b i) B hB

omit [Nonempty ι] in
private theorem pureDiagonalMean_neg (ψ : EuclideanSpace ℂ ι) (b : ι → ℝ) :
    pureDiagonalMean ψ (fun i => -b i) = -pureDiagonalMean ψ b :=
  diagonalMean_neg (pureBasisLaw ψ) b

theorem leastStressUnderBudget_isLeast (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) :
    IsLeast
      {s | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a ≤ B ∧ pureDiagonalMean ψ b = s}
      (leastStressUnderBudget a b B hB) := by
  have h := bestStressUnderBudget_isGreatest a (fun i => -b i) B hB
  constructor
  · obtain ⟨ψ, hψ, ha, hb⟩ := h.1
    refine ⟨ψ, hψ, ha, ?_⟩
    rw [pureDiagonalMean_neg] at hb
    rw [leastStressUnderBudget, ← hb, neg_neg]
  · rintro s ⟨ψ, hψ, ha, rfl⟩
    have hb : pureDiagonalMean ψ (fun i => -b i) ≤ bestStressUnderBudget a (fun i => -b i) B hB :=
      h.2 ⟨ψ, hψ, ha, rfl⟩
    rw [pureDiagonalMean_neg] at hb
    simpa only [leastStressUnderBudget, neg_neg] using neg_le_neg hb

/-- Every intermediate scalar stress at a feasible energy budget is
also attained by a normalized pure state. -/
theorem pureStressUnderBudgetRange_eq_Icc (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) :
    {s | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a ≤ B ∧ pureDiagonalMean ψ b = s} =
      Icc (leastStressUnderBudget a b B hB) (bestStressUnderBudget a b B hB) := by
  let S : Set ℝ :=
    {s | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a ≤ B ∧ pureDiagonalMean ψ b = s}
  let lo := leastStressUnderBudget a b B hB
  let hi := bestStressUnderBudget a b B hB
  have hlo : IsLeast S lo := leastStressUnderBudget_isLeast a b B hB
  have hhi : IsGreatest S hi := bestStressUnderBudget_isGreatest a b B hB
  change S = Icc lo hi
  ext s
  constructor
  · intro hs
    exact ⟨hlo.2 hs, hhi.2 hs⟩
  · intro hs
    by_cases h : lo = hi
    · have he : s = hi := le_antisymm hs.2 (h ▸ hs.1)
      rw [he]
      exact hhi.1
    · obtain ⟨ψ, hψ, ha, hb⟩ := hlo.1
      obtain ⟨ϕ, hϕ, ha', hb'⟩ := hhi.1
      have hg : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne (hs.1.trans hs.2) (show lo ≠ hi from h))
      let t := (s - lo) / (hi - lo)
      have ht₀ : 0 ≤ t := div_nonneg (sub_nonneg.mpr hs.1) hg.le
      have ht₁ : t ≤ 1 := (div_le_iff₀ hg).mpr (by rw [one_mul]; exact sub_le_sub_right hs.2 lo)
      have ht : t * (hi - lo) = s - lo := div_mul_cancel₀ _ hg.ne'
      let p := mixBasisLaw (pureBasisLaw ψ) (pureBasisLaw ϕ) t
      have hp : IsBasisLaw p := isBasisLaw_mix (isBasisLaw_pure ψ hψ) (isBasisLaw_pure ϕ hϕ) ht₀ ht₁
      obtain ⟨χ, hχ, hprob⟩ := exists_pureBasisLaw hp
      refine ⟨χ, hχ, ?_, ?_⟩
      · rw [pureDiagonalMean, hprob]
        change diagonalMean (mixBasisLaw (pureBasisLaw ψ) (pureBasisLaw ϕ) t) a ≤ B
        rw [diagonalMean_mix]
        calc
          _ ≤ (1 - t) * B + t * B := add_le_add
            (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht₁)) (mul_le_mul_of_nonneg_left ha' ht₀)
          _ = B := by ring
      · rw [pureDiagonalMean, hprob]
        change diagonalMean (mixBasisLaw (pureBasisLaw ψ) (pureBasisLaw ϕ) t) b = s
        rw [diagonalMean_mix]
        change (1 - t) * pureDiagonalMean ψ b + t * pureDiagonalMean ϕ b = s
        rw [hb, hb']
        calc
          _ = lo + t * (hi - lo) := by ring
          _ = _ := by rw [ht]; ring

/-- Upper bound obtained by penalizing energy above the budget at slope `L`. -/
def stressBudgetDual (a b : ι → ℝ) (B L : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => b i - L * (a i - B))

/-- Minimizing the finite penalty envelope over nonnegative slopes
gives the exact stress optimum, with an attained dual minimum. -/
theorem bestStressUnderBudget_dual_attained (a b : ι → ℝ) (B : ℝ) (hB : groundEnergy a ≤ B) :
    ∃ L : ℝ, 0 ≤ L ∧ stressBudgetDual a b B L = bestStressUnderBudget a b B hB ∧
      ∀ R : ℝ, 0 ≤ R → bestStressUnderBudget a b B hB ≤ stressBudgetDual a b B R := by
  obtain ⟨ψ, hψ, he, hb⟩ := (bestStressUnderBudget_isGreatest a b B hB).1
  have hp := isBasisLaw_pure ψ hψ
  have hweak (R : ℝ) (hR : 0 ≤ R) : bestStressUnderBudget a b B hB ≤ stressBudgetDual a b B R := by
    rw [← hb]
    apply diagonalMean_le_of_affine_majorant a b B _ R hp hR he
    intro i
    have hi : b i - R * (a i - B) ≤ stressBudgetDual a b B R :=
      Finset.le_sup' (fun i => b i - R * (a i - B)) (Finset.mem_univ i)
    linarith only [hi]
  obtain ⟨L, hL, hmajor⟩ := exists_bestStressUnderBudget_supporting_slope a b B hB
  refine ⟨L, hL, le_antisymm ?_ (hweak L hL), hweak⟩
  apply Finset.sup'_le
  intro i _
  linarith only [hmajor i]

end FiniteStrain

/-- For the encoded Ising path, the full stress range at any nonnegative
excess-energy budget is the interval between the two finite optima. -/
theorem isingStrain_pureStressRange_underBudget {n : ℕ}
    (h dh : Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) (η : ℝ) (hη : 0 ≤ η) :
    let a := pathDiagEnergy (strainPath h dh J 0)
    let b := onsiteResponse dh
    let B := FiniteStrain.groundEnergy a + η
    let hB : FiniteStrain.groundEnergy a ≤ B := le_add_of_nonneg_right hη
    {s | ∃ ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))), ‖ψ‖ = 1 ∧
      FiniteStrain.pureDiagonalMean ψ a ≤ B ∧ FiniteStrain.pureDiagonalMean ψ b = s} =
    Icc (FiniteStrain.leastStressUnderBudget a b B hB) (FiniteStrain.bestStressUnderBudget a b B hB) :=
  FiniteStrain.pureStressUnderBudgetRange_eq_Icc _ _ _ _

#print axioms FiniteStrain.chord_le_bestStressUnderBudget
#print axioms FiniteStrain.exists_bestStressUnderBudget_supporting_slope
#print axioms FiniteStrain.exists_twoConfig_bestStressUnderBudget
#print axioms FiniteStrain.bestStressUnderBudget_isGreatest
#print axioms FiniteStrain.leastStressUnderBudget_isLeast
#print axioms FiniteStrain.pureStressUnderBudgetRange_eq_Icc
#print axioms FiniteStrain.bestStressUnderBudget_dual_attained
#print axioms isingStrain_pureStressRange_underBudget

end

end GaloisForLFunctions.HTGeometry
