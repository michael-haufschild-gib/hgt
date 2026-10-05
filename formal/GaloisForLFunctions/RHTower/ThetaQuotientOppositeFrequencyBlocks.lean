import GaloisForLFunctions.RHTower.ThetaQuotientEigenvalueSums
import GaloisForLFunctions.RHTower.ThetaCdfActionClock
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.RHTower.SchattenLogResidueFiniteRankPerturbation

/-!
# The opposite-frequency blocks of the theta quotient

For `n ≥ 1` let `H_n = span{e_n, e_{−n}}` with orthogonal projection `Π_n`.  The exact diagonal
compressions `X_n = Π_n D Π_n` have the matrix
`(1/(2πn)) [[Φ_n, Φ_{2n} − Φ_n], [−(Φ_{2n} − Φ_n), −Φ_n]]`, with entry mass `Φ_{2n}/(πn)`.
Their ranges are mutually orthogonal, so finite sums have norm at most the largest block mass;
since `Φ_n = O(log log n)` the blocks sum in operator norm to `D₀ = Σ X_n`, and `R = D − D₀` is
the full cross-frequency operator.
-/

open MeasureTheory Set Filter Topology Module
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## Rank-one operators and the pair projections -/

/-- `x ↦ ⟨u, x⟩ v`. -/
def rankOneMap (u v : ThetaL2) : ThetaL2 →L[ℂ] ThetaL2 := (innerSL ℂ u).smulRight v

theorem rankOneMap_apply (u v x : ThetaL2) : rankOneMap u v x = ⟪u, x⟫_ℂ • v := by
  simp [rankOneMap, innerSL_apply_apply]

/-- The block indices `a_n = n + 1`, `b_n = −(n + 1)`. -/
def blockPos (n : ℕ) : ℤ := (n : ℤ) + 1

/-- The negative block index `b_n = −(n + 1)`. -/
def blockNeg (n : ℕ) : ℤ := -((n : ℤ) + 1)

theorem blockPos_ne_blockNeg (n : ℕ) : blockPos n ≠ blockNeg n := by
  simp only [blockPos, blockNeg]; omega

theorem inner_unitFourierBasis (i j : ℤ) :
    ⟪unitFourierBasis i, unitFourierBasis j⟫_ℂ = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; rw [inner_self_eq_norm_sq_to_K, unitFourierBasis.orthonormal.1]; simp
  · exact unitFourierBasis.orthonormal.2 h

/-- `Π_n x = ⟨e_{a}, x⟩ e_{a} + ⟨e_{b}, x⟩ e_{b}`. -/
def pairProj (n : ℕ) : ThetaL2 →L[ℂ] ThetaL2 :=
  rankOneMap (unitFourierBasis (blockPos n)) (unitFourierBasis (blockPos n)) +
    rankOneMap (unitFourierBasis (blockNeg n)) (unitFourierBasis (blockNeg n))

theorem pairProj_apply (n : ℕ) (x : ThetaL2) :
    pairProj n x = ⟪unitFourierBasis (blockPos n), x⟫_ℂ • unitFourierBasis (blockPos n) +
      ⟪unitFourierBasis (blockNeg n), x⟫_ℂ • unitFourierBasis (blockNeg n) := by
  simp [pairProj, rankOneMap_apply]

theorem inner_pairProj_left (n : ℕ) (x y : ThetaL2) :
    ⟪pairProj n x, y⟫_ℂ = ⟪x, pairProj n y⟫_ℂ := by
  rw [pairProj_apply, pairProj_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, inner_conj_symm, inner_conj_symm]
  ring

theorem inner_unitFourierBasis_pairProj (n : ℕ) (k : ℤ) (x : ThetaL2) :
    ⟪unitFourierBasis k, pairProj n x⟫_ℂ =
      if k = blockPos n ∨ k = blockNeg n then ⟪unitFourierBasis k, x⟫_ℂ else 0 := by
  rw [pairProj_apply, inner_add_right, inner_smul_right, inner_smul_right, inner_unitFourierBasis,
    inner_unitFourierBasis]
  have hne := blockPos_ne_blockNeg n
  by_cases h1 : k = blockPos n
  · rw [if_pos h1, if_neg (by rw [h1]; exact hne), if_pos (Or.inl h1), h1, mul_one, mul_zero, add_zero]
  · by_cases h2 : k = blockNeg n
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2), h2, mul_one, mul_zero, zero_add]
    · rw [if_neg h1, if_neg h2, if_neg (by tauto), mul_zero, mul_zero, add_zero]

theorem pairProj_unitFourierBasis_pos (n : ℕ) :
    pairProj n (unitFourierBasis (blockPos n)) = unitFourierBasis (blockPos n) := by
  rw [pairProj_apply, inner_unitFourierBasis, inner_unitFourierBasis, if_pos rfl,
    if_neg (Ne.symm (blockPos_ne_blockNeg n))]
  simp

theorem pairProj_unitFourierBasis_neg (n : ℕ) :
    pairProj n (unitFourierBasis (blockNeg n)) = unitFourierBasis (blockNeg n) := by
  rw [pairProj_apply, inner_unitFourierBasis, inner_unitFourierBasis, if_pos rfl,
    if_neg (blockPos_ne_blockNeg n)]
  simp

theorem pairProj_pairProj (n : ℕ) (x : ThetaL2) : pairProj n (pairProj n x) = pairProj n x := by
  conv_lhs => rw [pairProj_apply n x]
  rw [map_add, map_smul, map_smul, pairProj_unitFourierBasis_pos, pairProj_unitFourierBasis_neg,
    ← pairProj_apply]

theorem blockIndex_disjoint {n m : ℕ} (hnm : n ≠ m) (k : ℤ) :
    ¬ ((k = blockPos n ∨ k = blockNeg n) ∧ (k = blockPos m ∨ k = blockNeg m)) := by
  rintro ⟨h1 | h1, h2 | h2⟩ <;> subst h1 <;> simp only [blockPos, blockNeg] at h2 <;> omega

theorem pairProj_pairProj_of_ne {n m : ℕ} (hnm : n ≠ m) (x : ThetaL2) : pairProj n (pairProj m x) = 0 := by
  rw [pairProj_apply n, inner_unitFourierBasis_pairProj, inner_unitFourierBasis_pairProj]
  have h1 : ¬ (blockPos n = blockPos m ∨ blockPos n = blockNeg m) := fun h =>
    blockIndex_disjoint hnm (blockPos n) ⟨Or.inl rfl, h⟩
  have h2 : ¬ (blockNeg n = blockPos m ∨ blockNeg n = blockNeg m) := fun h =>
    blockIndex_disjoint hnm (blockNeg n) ⟨Or.inr rfl, h⟩
  rw [if_neg h1, if_neg h2]; simp

theorem inner_pairProj_pairProj_of_ne {n m : ℕ} (hnm : n ≠ m) (x y : ThetaL2) :
    ⟪pairProj n x, pairProj m y⟫_ℂ = 0 := by
  rw [inner_pairProj_left, pairProj_pairProj_of_ne hnm, inner_zero_right]

theorem norm_sq_pairProj (n : ℕ) (x : ThetaL2) :
    ‖pairProj n x‖ ^ 2 = ‖⟪unitFourierBasis (blockPos n), x⟫_ℂ‖ ^ 2 +
      ‖⟪unitFourierBasis (blockNeg n), x⟫_ℂ‖ ^ 2 := by
  rw [pairProj_apply]
  have horth : ⟪⟪unitFourierBasis (blockPos n), x⟫_ℂ • unitFourierBasis (blockPos n),
      ⟪unitFourierBasis (blockNeg n), x⟫_ℂ • unitFourierBasis (blockNeg n)⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, inner_unitFourierBasis, if_neg (blockPos_ne_blockNeg n)]
    simp
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [← sq, ← sq, ← sq] at h
  rw [h, norm_smul, norm_smul, unitFourierBasis.orthonormal.1, unitFourierBasis.orthonormal.1]
  ring

/-- **Bessel for the pair projections**: `Σ_{n ∈ F} ‖Π_n x‖² ≤ ‖x‖²`. -/
theorem sum_norm_sq_pairProj_le (F : Finset ℕ) (x : ThetaL2) :
    ∑ n ∈ F, ‖pairProj n x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  simp_rw [norm_sq_pairProj]
  rw [Finset.sum_add_distrib]
  have hdisj : Disjoint (F.image blockPos) (F.image blockNeg) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hk1
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 hk2
    simp only [blockPos, blockNeg] at hm; omega
  have h := unitFourierBasis.orthonormal.sum_inner_products_le x (s := F.image blockPos ∪ F.image blockNeg)
  rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => by simpa [blockPos] using h),
    Finset.sum_image (fun a _ b _ h => by simpa [blockNeg] using h)] at h
  exact h

theorem norm_pairProj_le (n : ℕ) (x : ThetaL2) : ‖pairProj n x‖ ≤ ‖x‖ := by
  have := sum_norm_sq_pairProj_le {n} x
  simp only [Finset.sum_singleton] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem pairProj_unitFourierBasis_of_ne {n : ℕ} {j : ℤ} (h1 : j ≠ blockPos n) (h2 : j ≠ blockNeg n) :
    pairProj n (unitFourierBasis j) = 0 := by
  rw [pairProj_apply, inner_unitFourierBasis, inner_unitFourierBasis, if_neg (Ne.symm h1), if_neg (Ne.symm h2)]
  simp

theorem pairProj_unitFourierBasis_of_ne_natAbs {n : ℕ} {j : ℤ} (h : n ≠ j.natAbs - 1) :
    pairProj n (unitFourierBasis j) = 0 :=
  pairProj_unitFourierBasis_of_ne (by simp only [blockPos]; omega) (by simp only [blockNeg]; omega)

/-! ## Families supported on the pair blocks -/

/-- `T_n` maps into `H_n` and is controlled by `c_n` on `H_n`. -/
def IsPairBlockFamily (T : ℕ → ThetaL2 →L[ℂ] ThetaL2) (c : ℕ → ℝ) : Prop :=
  (∀ n x, pairProj n (T n x) = T n x) ∧ ∀ n x, ‖T n x‖ ≤ c n * ‖pairProj n x‖

namespace IsPairBlockFamily

variable {T : ℕ → ThetaL2 →L[ℂ] ThetaL2} {c : ℕ → ℝ}

theorem inner_eq_zero (hT : IsPairBlockFamily T c) {n m : ℕ} (hnm : n ≠ m) (x y : ThetaL2) :
    ⟪T n x, T m y⟫_ℂ = 0 := by
  rw [← hT.1 n x, ← hT.1 m y]
  exact inner_pairProj_pairProj_of_ne hnm _ _

theorem apply_eq_zero (hT : IsPairBlockFamily T c) {n : ℕ} {x : ThetaL2} (hx : pairProj n x = 0) :
    T n x = 0 := by
  have := hT.2 n x
  rw [hx, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- **Orthogonal blocks**: `‖Σ_{n ∈ F} T_n‖ ≤ M` whenever `c_n ≤ M` on `F`. -/
theorem norm_sum_le (hT : IsPairBlockFamily T c) (F : Finset ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ n ∈ F, c n ≤ M) : ‖∑ n ∈ F, T n‖ ≤ M := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  have hpy : ∀ G : Finset ℕ, ‖∑ n ∈ G, T n x‖ ^ 2 = ∑ n ∈ G, ‖T n x‖ ^ 2 := by
    intro G
    induction G using Finset.induction_on with
    | empty => simp
    | insert m G hm ih =>
      rw [Finset.sum_insert hm, Finset.sum_insert hm, ← ih]
      have horth : ⟪T m x, ∑ n ∈ G, T n x⟫_ℂ = 0 := by
        rw [inner_sum]
        exact Finset.sum_eq_zero fun n hn => hT.inner_eq_zero (fun h => hm (by rw [h]; exact hn)) x x
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      rw [← sq, ← sq, ← sq] at h
      exact h
  have hsq : ‖(∑ n ∈ F, T n) x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [show (∑ n ∈ F, T n) x = ∑ n ∈ F, T n x from by simp, hpy F]
    calc ∑ n ∈ F, ‖T n x‖ ^ 2 ≤ ∑ n ∈ F, (M * ‖pairProj n x‖) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          have h1 := hT.2 n x
          have h2 : c n * ‖pairProj n x‖ ≤ M * ‖pairProj n x‖ :=
            mul_le_mul_of_nonneg_right (hF n hn) (norm_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = M ^ 2 * ∑ n ∈ F, ‖pairProj n x‖ ^ 2 := by rw [Finset.mul_sum]; ring_nf
      _ ≤ M ^ 2 * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_left (sum_norm_sq_pairProj_le F x) (by positivity)
      _ = (M * ‖x‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

theorem norm_le (hT : IsPairBlockFamily T c) (n : ℕ) (hc : 0 ≤ c n) : ‖T n‖ ≤ c n := by
  simpa using hT.norm_sum_le {n} hc (by simp)

/-- Blocks with `c_n → 0` sum in operator norm. -/
theorem summable (hT : IsPairBlockFamily T c) (hc : Tendsto c atTop (𝓝 0)) : Summable T := by
  refine summable_iff_vanishing_norm.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hc.eventually (Iic_mem_nhds (half_pos hε)))
  refine ⟨Finset.range N, fun t ht => ?_⟩
  refine lt_of_le_of_lt (hT.norm_sum_le t (half_pos hε).le fun n hn => hN n ?_) (half_lt_self hε)
  by_contra h
  exact Finset.disjoint_left.1 ht hn (Finset.mem_range.2 (not_le.1 h))

theorem norm_tsum_le (hT : IsPairBlockFamily T c) (hs : Summable T) {M : ℝ} (hM : 0 ≤ M)
    (hcM : ∀ n, c n ≤ M) : ‖∑' n, T n‖ ≤ M :=
  le_of_tendsto' hs.hasSum.tendsto_sum_nat.norm fun _ => hT.norm_sum_le _ hM fun n _ => hcM n

/-- The tail `Σ_{n ≥ N} T_n` has norm at most any bound for `c` on `n ≥ N`. -/
theorem norm_tsum_tail_le (hT : IsPairBlockFamily T c) (hs : Summable T) (N : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hcM : ∀ n, N ≤ n → c n ≤ M) : ‖∑' n, T (n + N)‖ ≤ M := by
  have hs' : Summable fun n => T (n + N) := (summable_nat_add_iff N).2 hs
  refine le_of_tendsto' hs'.hasSum.tendsto_sum_nat.norm fun K => ?_
  have h := hT.norm_sum_le ((Finset.range K).map (addRightEmbedding N)) hM fun n hn => by
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hn
    exact hcM _ (by simp)
  rwa [Finset.sum_map] at h

theorem tsum_apply (hs : Summable T) (x : ThetaL2) : (∑' n, T n) x = ∑' n, T n x := by
  have h := (ContinuousLinearMap.apply ℂ ThetaL2 x).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at h
  exact h

theorem tsum_apply_unitFourierBasis (hT : IsPairBlockFamily T c) (hs : Summable T) (j : ℤ) :
    (∑' n, T n) (unitFourierBasis j) = T (j.natAbs - 1) (unitFourierBasis j) := by
  rw [tsum_apply hs]
  exact tsum_eq_single _ fun m hm => hT.apply_eq_zero (pairProj_unitFourierBasis_of_ne_natAbs hm)

theorem norm_tsum_apply_unitFourierBasis_le (hT : IsPairBlockFamily T c) (hs : Summable T)
    (hc0 : ∀ n, 0 ≤ c n) (j : ℤ) : ‖(∑' n, T n) (unitFourierBasis j)‖ ≤ c (j.natAbs - 1) := by
  rw [hT.tsum_apply_unitFourierBasis hs]
  refine (hT.2 _ _).trans ?_
  calc c (j.natAbs - 1) * ‖pairProj (j.natAbs - 1) (unitFourierBasis j)‖
      ≤ c (j.natAbs - 1) * ‖unitFourierBasis j‖ :=
        mul_le_mul_of_nonneg_left (norm_pairProj_le _ _) (hc0 _)
    _ = c (j.natAbs - 1) := by rw [unitFourierBasis.orthonormal.1, mul_one]

/-- Square-summable controls give a Hilbert–Schmidt sum. -/
theorem isHilbertSchmidt_tsum (hT : IsPairBlockFamily T c) (hs : Summable T) (hc0 : ∀ n, 0 ≤ c n)
    (hc2 : Summable fun n => c n ^ 2) : (∑' n, T n).IsHilbertSchmidt := by
  refine ContinuousLinearMap.isHilbertSchmidt_of_summable unitFourierBasis ?_
  have hb : ∀ j : ℤ, ‖(∑' n, T n) (unitFourierBasis j)‖ ^ 2 ≤ c (j.natAbs - 1) ^ 2 := fun j =>
    pow_le_pow_left₀ (norm_nonneg _) (hT.norm_tsum_apply_unitFourierBasis_le hs hc0 j) 2
  refine Summable.of_nonneg_of_le (fun j => by positivity) hb ?_
  refine summable_int_iff_summable_nat_and_neg.2 ⟨?_, ?_⟩
  · refine (summable_nat_add_iff 1).1 (hc2.congr fun n => ?_)
    congr 2
  · refine (summable_nat_add_iff 1).1 (hc2.congr fun n => ?_)
    congr 2

end IsPairBlockFamily

/-! ## The blocks -/

/-- The exact `H_n` diagonal compression `X_n = Π_n D Π_n` (block of frequency `n + 1`). -/
def thetaDiagonalBlock (n : ℕ) : ThetaL2 →L[ℂ] ThetaL2 :=
  pairProj n ∘L thetaQuotientOperator ∘L pairProj n

/-- The entry mass of a block. -/
def blockMass (n : ℕ) : ℝ :=
  ‖⟪unitFourierBasis (blockPos n), thetaQuotientOperator (unitFourierBasis (blockPos n))⟫_ℂ‖ +
  ‖⟪unitFourierBasis (blockPos n), thetaQuotientOperator (unitFourierBasis (blockNeg n))⟫_ℂ‖ +
  ‖⟪unitFourierBasis (blockNeg n), thetaQuotientOperator (unitFourierBasis (blockPos n))⟫_ℂ‖ +
  ‖⟪unitFourierBasis (blockNeg n), thetaQuotientOperator (unitFourierBasis (blockNeg n))⟫_ℂ‖

theorem blockMass_nonneg (n : ℕ) : 0 ≤ blockMass n := by unfold blockMass; positivity

theorem thetaDiagonalBlock_apply (n : ℕ) (x : ThetaL2) :
    thetaDiagonalBlock n x = pairProj n (thetaQuotientOperator (pairProj n x)) := rfl

theorem norm_thetaDiagonalBlock_apply_le (n : ℕ) (x : ThetaL2) :
    ‖thetaDiagonalBlock n x‖ ≤ blockMass n * ‖pairProj n x‖ := by
  set a := unitFourierBasis (blockPos n)
  set b := unitFourierBasis (blockNeg n)
  set D := thetaQuotientOperator
  have hxa : ‖⟪a, x⟫_ℂ‖ ≤ ‖pairProj n x‖ := by
    have h := norm_sq_pairProj n x
    nlinarith [sq_nonneg ‖⟪b, x⟫_ℂ‖, norm_nonneg ⟪a, x⟫_ℂ, norm_nonneg (pairProj n x)]
  have hxb : ‖⟪b, x⟫_ℂ‖ ≤ ‖pairProj n x‖ := by
    have h := norm_sq_pairProj n x
    nlinarith [sq_nonneg ‖⟪a, x⟫_ℂ‖, norm_nonneg ⟪b, x⟫_ℂ, norm_nonneg (pairProj n x)]
  have hexp : thetaDiagonalBlock n x =
      (⟪a, x⟫_ℂ * ⟪a, D a⟫_ℂ + ⟪b, x⟫_ℂ * ⟪a, D b⟫_ℂ) • a +
        (⟪a, x⟫_ℂ * ⟪b, D a⟫_ℂ + ⟪b, x⟫_ℂ * ⟪b, D b⟫_ℂ) • b := by
    rw [thetaDiagonalBlock_apply, pairProj_apply n x, map_add, map_smul, map_smul, pairProj_apply,
      inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right,
      inner_smul_right]
  rw [hexp]
  have ha1 : ‖a‖ = 1 := unitFourierBasis.orthonormal.1 _
  have hb1 : ‖b‖ = 1 := unitFourierBasis.orthonormal.1 _
  calc ‖(⟪a, x⟫_ℂ * ⟪a, D a⟫_ℂ + ⟪b, x⟫_ℂ * ⟪a, D b⟫_ℂ) • a +
        (⟪a, x⟫_ℂ * ⟪b, D a⟫_ℂ + ⟪b, x⟫_ℂ * ⟪b, D b⟫_ℂ) • b‖
      ≤ ‖⟪a, x⟫_ℂ‖ * ‖⟪a, D a⟫_ℂ‖ + ‖⟪b, x⟫_ℂ‖ * ‖⟪a, D b⟫_ℂ‖ +
          (‖⟪a, x⟫_ℂ‖ * ‖⟪b, D a⟫_ℂ‖ + ‖⟪b, x⟫_ℂ‖ * ‖⟪b, D b⟫_ℂ‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, ha1, mul_one]
          refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul, norm_mul]
        · rw [norm_smul, hb1, mul_one]
          refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul, norm_mul]
    _ ≤ ‖pairProj n x‖ * ‖⟪a, D a⟫_ℂ‖ + ‖pairProj n x‖ * ‖⟪a, D b⟫_ℂ‖ +
          (‖pairProj n x‖ * ‖⟪b, D a⟫_ℂ‖ + ‖pairProj n x‖ * ‖⟪b, D b⟫_ℂ‖) := by gcongr
    _ = blockMass n * ‖pairProj n x‖ := by simp only [blockMass, a, b, D]; ring

theorem thetaDiagonalBlock_pairProj (n : ℕ) (x : ThetaL2) :
    thetaDiagonalBlock n (pairProj n x) = thetaDiagonalBlock n x := by
  rw [thetaDiagonalBlock_apply, thetaDiagonalBlock_apply, pairProj_pairProj]



theorem isPairBlockFamily_thetaDiagonalBlock : IsPairBlockFamily thetaDiagonalBlock blockMass :=
  ⟨fun n x => by rw [thetaDiagonalBlock_apply, pairProj_pairProj], norm_thetaDiagonalBlock_apply_le⟩

/-! ## The block entries -/

theorem cdfAction_zero : cdfAction 0 = 0 := by simp [cdfAction]

theorem blockPos_eq (n : ℕ) : blockPos n = ((n + 1 : ℕ) : ℤ) := by simp [blockPos]

theorem blockNeg_eq (n : ℕ) : blockNeg n = -((n + 1 : ℕ) : ℤ) := by simp [blockNeg]

theorem blockPos_ne_zero (n : ℕ) : blockPos n ≠ 0 := by simp only [blockPos]; omega

theorem blockNeg_ne_zero (n : ℕ) : blockNeg n ≠ 0 := by simp only [blockNeg]; omega

/-- The diagonal entry `α_n = Φ_k/(2πk)`, `k = n + 1`. -/
def blockDiag (n : ℕ) : ℝ := cdfAction (n + 1 : ℕ) / (2 * Real.pi * (n + 1))

/-- The off-diagonal entry `δ_n = (Φ_{2k} − Φ_k)/(2πk)`, `k = n + 1`. -/
def blockOff (n : ℕ) : ℝ :=
  (cdfAction (2 * ((n + 1 : ℕ) : ℤ)) - cdfAction (n + 1 : ℕ)) / (2 * Real.pi * (n + 1))

theorem blockDiag_pos (n : ℕ) : 0 < blockDiag n := by
  have := cdfAction_pos (n := n + 1) (by omega)
  unfold blockDiag; positivity

theorem blockOff_pos (n : ℕ) : 0 < blockOff n := by
  have := cdfAction_lt_two_mul (n := n + 1) (by omega)
  unfold blockOff
  have h : 0 < cdfAction (2 * ((n + 1 : ℕ) : ℤ)) - cdfAction (n + 1 : ℕ) := by linarith
  positivity

theorem inner_blockPos_blockPos (n : ℕ) :
    ⟪unitFourierBasis (blockPos n), thetaQuotientOperator (unitFourierBasis (blockPos n))⟫_ℂ =
      (blockDiag n : ℂ) := by
  rw [inner_unitFourierBasis_thetaQuotientOperator (blockPos_ne_zero n) (blockPos_ne_zero n), sub_self,
    cdfAction_zero, sub_zero, blockDiag, blockPos_eq]
  push_cast; ring_nf

theorem inner_blockPos_blockNeg (n : ℕ) :
    ⟪unitFourierBasis (blockPos n), thetaQuotientOperator (unitFourierBasis (blockNeg n))⟫_ℂ =
      (blockOff n : ℂ) := by
  rw [inner_unitFourierBasis_thetaQuotientOperator (blockPos_ne_zero n) (blockNeg_ne_zero n)]
  have h : blockNeg n - blockPos n = -(2 * ((n + 1 : ℕ) : ℤ)) := by
    simp only [blockPos, blockNeg]; push_cast; ring
  rw [h, cdfAction_neg, blockOff, blockPos_eq, blockNeg_eq]
  have hpi : (2 * Real.pi * ((n : ℝ) + 1)) ≠ 0 := by positivity
  congr 1
  push_cast
  field_simp
  ring

theorem inner_blockNeg_blockPos (n : ℕ) :
    ⟪unitFourierBasis (blockNeg n), thetaQuotientOperator (unitFourierBasis (blockPos n))⟫_ℂ =
      (-blockOff n : ℂ) := by
  rw [inner_unitFourierBasis_thetaQuotientOperator (blockNeg_ne_zero n) (blockPos_ne_zero n)]
  have h : blockPos n - blockNeg n = 2 * ((n + 1 : ℕ) : ℤ) := by
    simp only [blockPos, blockNeg]; push_cast; ring
  rw [h, blockNeg_eq, cdfAction_neg, blockOff, blockPos_eq]
  push_cast
  ring

theorem inner_blockNeg_blockNeg (n : ℕ) :
    ⟪unitFourierBasis (blockNeg n), thetaQuotientOperator (unitFourierBasis (blockNeg n))⟫_ℂ =
      (-blockDiag n : ℂ) := by
  rw [inner_unitFourierBasis_thetaQuotientOperator (blockNeg_ne_zero n) (blockNeg_ne_zero n), sub_self,
    cdfAction_zero, sub_zero, blockDiag, blockNeg_eq, cdfAction_neg]
  have hpi : (2 * Real.pi * ((n : ℝ) + 1)) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **The exact block**: in the basis `(e_k, e_{−k})`, `X_n` has matrix
`(1/(2πk)) [[Φ_k, Φ_{2k} − Φ_k], [−(Φ_{2k} − Φ_k), −Φ_k]]` (entries `⟨e_i, X e_j⟩`). -/
theorem thetaDiagonalBlock_eq (n : ℕ) :
    thetaDiagonalBlock n =
      (blockDiag n : ℂ) • rankOneMap (unitFourierBasis (blockPos n)) (unitFourierBasis (blockPos n)) -
      (blockOff n : ℂ) • rankOneMap (unitFourierBasis (blockPos n)) (unitFourierBasis (blockNeg n)) +
      (blockOff n : ℂ) • rankOneMap (unitFourierBasis (blockNeg n)) (unitFourierBasis (blockPos n)) -
      (blockDiag n : ℂ) • rankOneMap (unitFourierBasis (blockNeg n)) (unitFourierBasis (blockNeg n)) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [thetaDiagonalBlock_apply, pairProj_apply n x, map_add, map_smul, map_smul, map_add, map_smul, map_smul,
    pairProj_apply n (thetaQuotientOperator _), pairProj_apply n (thetaQuotientOperator _),
    inner_blockPos_blockPos, inner_blockPos_blockNeg, inner_blockNeg_blockPos, inner_blockNeg_blockNeg]
  simp only [add_apply, sub_apply, smul_apply, rankOneMap_apply]
  module

theorem blockMass_eq (n : ℕ) :
    blockMass n = cdfAction (2 * ((n + 1 : ℕ) : ℤ)) / (Real.pi * (n + 1)) := by
  rw [blockMass, inner_blockPos_blockPos, inner_blockPos_blockNeg, inner_blockNeg_blockPos,
    inner_blockNeg_blockNeg]
  simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (blockDiag_pos n), abs_of_pos (blockOff_pos n), blockDiag, blockOff]
  have hpi : Real.pi * ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem blockMass_pos (n : ℕ) : 0 < blockMass n := by
  have := cdfAction_pos (n := n + 1) (by omega)
  have h2 := cdfAction_lt_two_mul (n := n + 1) (by omega)
  rw [blockMass_eq]
  have : 0 < cdfAction (2 * ((n + 1 : ℕ) : ℤ)) := by linarith
  positivity

/-! ## The CDF-action ceiling and the block majorant -/

theorem two_le_log_add_sixteen {x : ℝ} (hx : 0 ≤ x) : 2 ≤ Real.log (x + 16) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

theorem half_le_log_log_add_sixteen {x : ℝ} (hx : 0 ≤ x) : 1 / 2 ≤ Real.log (Real.log (x + 16)) := by
  have h := two_le_log_add_sixteen hx
  have h2 := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) h
  linarith

theorem log_log_add_sixteen_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Real.log (Real.log (x + 16)) :=
  le_trans (by norm_num) (half_le_log_log_add_sixteen hx)

/-- **The CDF-action ceiling**: `Φ_{2k} ≤ C log log(k + 15)`. -/
theorem exists_cdfAction_two_mul_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, cdfAction (2 * ((n + 1 : ℕ) : ℤ)) ≤ C * Real.log (Real.log (n + 16)) := by
  obtain ⟨C₀, hC₀, N₀, hN₀⟩ := exists_abs_cdfAction_sub_loglog_le
  set N₁ := N₀ + 3
  -- the late range
  have hlate : ∀ n : ℕ, N₁ ≤ 2 * (n + 1) →
      cdfAction (2 * ((n + 1 : ℕ) : ℤ)) ≤ 2 * (1 + C₀) * Real.log (Real.log (n + 16)) := by
    intro n hn
    set m : ℕ := 2 * (n + 1)
    have hm : cdfAction (2 * ((n + 1 : ℕ) : ℤ)) = cdfAction (m : ℕ) := by simp [m]
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
    have hlog1 : 1 ≤ Real.log m := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hll0 : 0 ≤ Real.log (Real.log m) := Real.log_nonneg hlog1
    have h := (abs_le.1 (hN₀ m (by omega))).2
    have hπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
    have hfrac : Real.log (Real.log m) / Real.log m ≤ Real.log (Real.log m) :=
      div_le_self hll0 hlog1
    have hstep : cdfAction (m : ℕ) ≤ (1 + C₀) * Real.log (Real.log m) := by nlinarith
    -- `log log (2k) ≤ 2 log log (n + 16)`
    have hL := two_le_log_add_sixteen (x := n) (by positivity)
    have hcmp : Real.log m ≤ Real.log (n + 16) ^ 2 := by
      have h1 : Real.log m ≤ Real.log 2 + Real.log (n + 16) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]
        exact Real.log_le_log (by linarith) (by simp only [m]; push_cast; linarith)
      have h2 := Real.log_two_lt_d9
      nlinarith
    have hll : Real.log (Real.log m) ≤ 2 * Real.log (Real.log (n + 16)) := by
      have := Real.log_le_log (by linarith) hcmp
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    rw [hm]
    calc cdfAction (m : ℕ) ≤ (1 + C₀) * Real.log (Real.log m) := hstep
      _ ≤ (1 + C₀) * (2 * Real.log (Real.log (n + 16))) := by gcongr
      _ = 2 * (1 + C₀) * Real.log (Real.log (n + 16)) := by ring
  -- the early range
  set B := ∑ i ∈ Finset.range N₁, cdfAction (2 * ((i + 1 : ℕ) : ℤ))
  have hB : ∀ n : ℕ, n < N₁ → cdfAction (2 * ((n + 1 : ℕ) : ℤ)) ≤ B := by
    intro n hn
    refine Finset.single_le_sum (f := fun i => cdfAction (2 * ((i + 1 : ℕ) : ℤ))) (fun i _ => ?_)
      (Finset.mem_range.2 hn)
    have := cdfAction_pos (n := 2 * (i + 1)) (by omega)
    push_cast at this ⊢
    linarith
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => by
    have := cdfAction_pos (n := 2 * (i + 1)) (by omega)
    push_cast at this ⊢
    linarith
  refine ⟨2 * (1 + C₀) + 2 * B, by positivity, fun n => ?_⟩
  have hll := half_le_log_log_add_sixteen (x := n) (by positivity)
  by_cases hn : N₁ ≤ 2 * (n + 1)
  · have := hlate n hn
    nlinarith
  · have := hB n (by omega)
    nlinarith

/-- The majorant `w(n) = log log(n + 16)/(n + 1)`. -/
def blockMajorant (n : ℕ) : ℝ := Real.log (Real.log (n + 16)) / (n + 1)

theorem blockMajorant_nonneg (n : ℕ) : 0 ≤ blockMajorant n :=
  div_nonneg (log_log_add_sixteen_nonneg n (by positivity)) (by positivity)

theorem log_log_sub_le {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    Real.log (Real.log t) - Real.log (Real.log s) ≤ (t - s) / (s * Real.log s) := by
  have hls : 0 < Real.log s := Real.log_pos hs
  have hlt : 0 < Real.log t := Real.log_pos (hs.trans_le hst)
  have hs0 : 0 < s := by linarith
  have h1 : Real.log (Real.log t) - Real.log (Real.log s) ≤ Real.log t / Real.log s - 1 := by
    rw [← Real.log_div hlt.ne' hls.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log t - Real.log s ≤ t / s - 1 := by
    rw [← Real.log_div (by linarith) hs0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hs0)
  have h3 : Real.log t / Real.log s - 1 = (Real.log t - Real.log s) / Real.log s := by
    field_simp
  have h4 : t / s - 1 = (t - s) / s := by field_simp
  rw [h3] at h1
  calc Real.log (Real.log t) - Real.log (Real.log s) ≤ (Real.log t - Real.log s) / Real.log s := h1
    _ ≤ ((t - s) / s) / Real.log s := by rw [← h4]; exact div_le_div_of_nonneg_right h2 hls.le
    _ = (t - s) / (s * Real.log s) := by rw [div_div]

theorem blockMajorant_antitone : Antitone blockMajorant := by
  intro m n hmn
  have hx : (0 : ℝ) ≤ m := by positivity
  have hxy : (m : ℝ) ≤ n := by exact_mod_cast hmn
  set s : ℝ := m + 16
  set t : ℝ := n + 16
  have hL := two_le_log_add_sixteen hx
  have hℓ := half_le_log_log_add_sixteen hx
  have hconc := log_log_sub_le (s := s) (t := t) (by simp only [s]; linarith) (by simp only [s, t]; linarith)
  have hsL : 0 < s * Real.log s := by positivity
  -- `(m+1) log log t ≤ (n+1) log log s`
  have key : ((m : ℝ) + 1) * Real.log (Real.log t) ≤ ((n : ℝ) + 1) * Real.log (Real.log s) := by
    have hq : ((m : ℝ) + 1) * ((t - s) / (s * Real.log s)) ≤ (n - m) * Real.log (Real.log s) := by
      have hts : t - s = n - m := by simp only [s, t]; ring
      rw [hts]
      have hfrac : ((m : ℝ) + 1) / (s * Real.log s) ≤ Real.log (Real.log s) := by
        rw [div_le_iff₀ hsL]
        have : ((m : ℝ) + 1) ≤ s := by simp only [s]; linarith
        nlinarith
      have hnm : (0 : ℝ) ≤ n - m := by linarith
      calc ((m : ℝ) + 1) * ((n - m) / (s * Real.log s)) = (n - m) * (((m : ℝ) + 1) / (s * Real.log s)) := by
            ring
        _ ≤ (n - m) * Real.log (Real.log s) := mul_le_mul_of_nonneg_left hfrac hnm
    have hm1 : (0 : ℝ) ≤ m + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hconc hm1]
  unfold blockMajorant
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- `w(n) ≤ 8 (n + 1)^{−3/4}`. -/
theorem blockMajorant_le_rpow (n : ℕ) : blockMajorant n ≤ 8 * ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hL := two_le_log_add_sixteen (x := n) (by positivity)
  have h1 : Real.log (Real.log (n + 16)) ≤ Real.log (n + 16) := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log (n + 16) by linarith); linarith
  have h2 : Real.log (n + 16) ≤ ((n : ℝ) + 16) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (by positivity) (by norm_num)
  have h3 : ((n : ℝ) + 16) ^ (1 / 4 : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := by
    have h16 : ((n : ℝ) + 16) ≤ 16 * ((n : ℝ) + 1) := by linarith
    calc ((n : ℝ) + 16) ^ (1 / 4 : ℝ) ≤ (16 * ((n : ℝ) + 1)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h16 (by norm_num)
      _ = (16 : ℝ) ^ (1 / 4 : ℝ) * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) hn1.le
      _ = 2 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hpow : ((n : ℝ) + 1) ^ (1 / 4 : ℝ) / ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hn1]
    norm_num
  unfold blockMajorant
  calc Real.log (Real.log (n + 16)) / (n + 1) ≤ (8 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ)) / (n + 1) := by
        refine div_le_div_of_nonneg_right ?_ hn1.le
        linarith
    _ = 8 * (((n : ℝ) + 1) ^ (1 / 4 : ℝ) / ((n : ℝ) + 1)) := by ring
    _ = 8 * ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by rw [hpow]

theorem tendsto_blockMajorant : Tendsto blockMajorant atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 8 * ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 4 by norm_num)).comp
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    simpa using this.const_mul 8
  exact squeeze_zero blockMajorant_nonneg blockMajorant_le_rpow h

theorem summable_blockMajorant_sq : Summable fun n => blockMajorant n ^ 2 := by
  have hs : Summable fun n : ℕ => 64 * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    have h := Real.summable_nat_rpow_inv.2 (show (1 : ℝ) < 3 / 2 by norm_num)
    have h' := (summable_nat_add_iff 1).2 h
    refine (h'.mul_left 64).congr fun n => ?_
    push_cast
    rw [Real.rpow_neg (by positivity)]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have h := blockMajorant_le_rpow n
  have h0 := blockMajorant_nonneg n
  calc blockMajorant n ^ 2 ≤ (8 * ((n : ℝ) + 1) ^ (-(3 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 64 * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (((n : ℝ) + 1) ^ _), ← Real.rpow_mul (by positivity)]
        norm_num

/-- **Block decay**: `‖X_n‖ ≤ C w(n)`. -/
theorem exists_blockMass_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, blockMass n ≤ C * blockMajorant n := by
  obtain ⟨C, hC, hCn⟩ := exists_cdfAction_two_mul_le
  refine ⟨C / Real.pi, by positivity, fun n => ?_⟩
  rw [blockMass_eq, blockMajorant]
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc cdfAction (2 * ((n + 1 : ℕ) : ℤ)) ≤ C * Real.log (Real.log (n + 16)) := hCn n
    _ = C / Real.pi * (Real.log (Real.log (n + 16)) / (n + 1)) * (Real.pi * (n + 1)) := by
        field_simp

theorem tendsto_blockMass : Tendsto blockMass atTop (𝓝 0) := by
  obtain ⟨C, hC, hCn⟩ := exists_blockMass_le
  have := tendsto_blockMajorant.const_mul C
  rw [mul_zero] at this
  exact squeeze_zero (fun n => (blockMass_pos n).le) hCn this

/-! ## The block operator `D₀` -/

theorem summable_thetaDiagonalBlock : Summable thetaDiagonalBlock :=
  isPairBlockFamily_thetaDiagonalBlock.summable tendsto_blockMass

/-- **The block-diagonal part** `D₀ = ⊕_n X_n` of the theta quotient. -/
def thetaBlockDiagonal : ThetaL2 →L[ℂ] ThetaL2 := ∑' n, thetaDiagonalBlock n

/-- **`D₀` is Hilbert–Schmidt.** -/
theorem isHilbertSchmidt_thetaBlockDiagonal : thetaBlockDiagonal.IsHilbertSchmidt := by
  obtain ⟨C, hC, hCn⟩ := exists_blockMass_le
  refine isPairBlockFamily_thetaDiagonalBlock.isHilbertSchmidt_tsum summable_thetaDiagonalBlock
    (fun n => (blockMass_pos n).le) ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_blockMajorant_sq.mul_left (C ^ 2))
  have := pow_le_pow_left₀ (blockMass_pos n).le (hCn n) 2
  rw [mul_pow] at this
  exact this

theorem isCompactOperator_thetaBlockDiagonal : IsCompactOperator thetaBlockDiagonal :=
  isHilbertSchmidt_thetaBlockDiagonal.isCompactOperator

/-! ## Ky Fan sums of `D₀` -/

theorem kyFanSum_le_two_mul_norm {X : ThetaL2 →L[ℂ] ThetaL2} (hX : HasRankLE X 2) (N : ℕ) :
    kyFanSum X N ≤ 2 * ‖X‖ := by
  have hmono : kyFanSum X N ≤ kyFanSum X (N + 2) := kyFanSum_mono X (by omega)
  have hz : ∀ j, approxNumber X (j + 2) = 0 := fun j => le_antisymm
    ((approxNumber_antitone X (by omega : 2 ≤ j + 2)).trans (approxNumber_eq_zero_of_hasRankLE hX).le)
    (approxNumber_nonneg _ _)
  have h : kyFanSum X (N + 2) = approxNumber X 0 + approxNumber X 1 := by
    rw [kyFanSum, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [hz, Finset.sum_const_zero, zero_add]
    ring
  rw [h] at hmono
  linarith [approxNumber_le_norm X 0, approxNumber_le_norm X 1]

theorem kyFanSum_sum_le (F : Finset ℕ) (T : ℕ → ThetaL2 →L[ℂ] ThetaL2) (hT : ∀ n, IsCompactOperator (T n))
    (N : ℕ) : kyFanSum (∑ n ∈ F, T n) N ≤ ∑ n ∈ F, kyFanSum (T n) N := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simpa using kyFanSum_le_mul_norm (0 : ThetaL2 →L[ℂ] ThetaL2) N
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hc : IsCompactOperator (⇑(∑ n ∈ F, T n)) :=
      Finset.sum_induction _ (fun S : ThetaL2 →L[ℂ] ThetaL2 => IsCompactOperator S)
        (fun _ _ h1 h2 => h1.add h2) isCompactOperator_zero fun n _ => hT n
    exact (kyFanSum_add_le (hT a) hc N).trans (by linarith)

theorem hasRankLE_thetaDiagonalBlock (n : ℕ) : HasRankLE (thetaDiagonalBlock n) 2 := by
  set v : Fin 2 → ThetaL2 := ![unitFourierBasis (blockPos n), unitFourierBasis (blockNeg n)]
  refine ⟨Submodule.span ℂ (Set.range v), FiniteDimensional.span_of_finite ℂ (Set.finite_range v),
    (finrank_range_le_card v).trans (by simp), fun x => ?_⟩
  rw [thetaDiagonalBlock_apply, pairProj_apply]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

theorem isCompactOperator_thetaDiagonalBlock (n : ℕ) : IsCompactOperator (thetaDiagonalBlock n) :=
  isCompactOperator_of_hasRankLE (hasRankLE_thetaDiagonalBlock n)

theorem sum_range_inv_succ_le_one_add_log (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  have he : ((harmonic N : ℚ) : ℝ) = ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) := by
    simp [harmonic]
  rwa [he] at h

/-- **Ky Fan sums of `D₀`**: `K_N(D₀) ≤ C log log(N + 16) (3 + 2 log N)`. -/
theorem exists_kyFanSum_thetaBlockDiagonal_le_aux :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      kyFanSum thetaBlockDiagonal N ≤ C * (Real.log (Real.log (N + 16)) * (3 + 2 * Real.log N)) := by
  obtain ⟨C, hC, hCn⟩ := exists_blockMass_le
  refine ⟨C, hC, fun N => ?_⟩
  set ll := Real.log (Real.log ((N : ℝ) + 16))
  have hll0 : 0 ≤ ll := log_log_add_sixteen_nonneg N (by positivity)
  have hsplit := (summable_thetaDiagonalBlock.sum_add_tsum_nat_add N).symm
  set head := ∑ n ∈ Finset.range N, thetaDiagonalBlock n
  set tail := ∑' n, thetaDiagonalBlock (n + N)
  have hD : thetaBlockDiagonal = head + tail := hsplit
  have hhead_c : IsCompactOperator head :=
    Finset.sum_induction _ (fun S : ThetaL2 →L[ℂ] ThetaL2 => IsCompactOperator S)
      (fun _ _ h1 h2 => h1.add h2) isCompactOperator_zero fun n _ => isCompactOperator_thetaDiagonalBlock n
  have htail_c : IsCompactOperator tail := by
    have : tail = thetaBlockDiagonal - head := by rw [hD]; abel
    rw [this]; exact isCompactOperator_thetaBlockDiagonal.sub hhead_c
  -- the head
  have hblock : ∀ n ∈ Finset.range N, kyFanSum (thetaDiagonalBlock n) N ≤ 2 * C * ll * (1 / ((n : ℝ) + 1)) := by
    intro n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.1 hn).le
    have h1 := kyFanSum_le_two_mul_norm (hasRankLE_thetaDiagonalBlock n) N
    have h2 := isPairBlockFamily_thetaDiagonalBlock.norm_le n (blockMass_pos n).le
    have h3 := hCn n
    have h4 : blockMajorant n ≤ ll * (1 / ((n : ℝ) + 1)) := by
      unfold blockMajorant
      rw [mul_one_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hL := two_le_log_add_sixteen (x := n) (by positivity)
      exact Real.log_le_log (by linarith) (Real.log_le_log (by positivity) (by linarith))
    calc kyFanSum (thetaDiagonalBlock n) N ≤ 2 * ‖thetaDiagonalBlock n‖ := h1
      _ ≤ 2 * (C * blockMajorant n) := by linarith
      _ ≤ 2 * (C * (ll * (1 / ((n : ℝ) + 1)))) := by gcongr
      _ = 2 * C * ll * (1 / ((n : ℝ) + 1)) := by ring
  have hhead : kyFanSum head N ≤ 2 * C * ll * (1 + Real.log N) := by
    calc kyFanSum head N ≤ ∑ n ∈ Finset.range N, kyFanSum (thetaDiagonalBlock n) N :=
          kyFanSum_sum_le _ _ isCompactOperator_thetaDiagonalBlock N
      _ ≤ ∑ n ∈ Finset.range N, 2 * C * ll * (1 / ((n : ℝ) + 1)) := Finset.sum_le_sum hblock
      _ = 2 * C * ll * ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * C * ll * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left (sum_range_inv_succ_le_one_add_log N) (by positivity)
  -- the tail
  have htail_norm : ‖tail‖ ≤ C * blockMajorant N :=
    isPairBlockFamily_thetaDiagonalBlock.norm_tsum_tail_le summable_thetaDiagonalBlock N
      (mul_nonneg hC (blockMajorant_nonneg N)) fun n hn =>
        (hCn n).trans (mul_le_mul_of_nonneg_left (blockMajorant_antitone hn) hC)
  have htail : kyFanSum tail N ≤ C * ll := by
    calc kyFanSum tail N ≤ N * ‖tail‖ := kyFanSum_le_mul_norm tail N
      _ ≤ N * (C * blockMajorant N) := mul_le_mul_of_nonneg_left htail_norm (by positivity)
      _ = C * ll * (N / ((N : ℝ) + 1)) := by unfold blockMajorant; ring
      _ ≤ C * ll * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = C * ll := mul_one _
  rw [hD]
  calc kyFanSum (head + tail) N ≤ kyFanSum head N + kyFanSum tail N := kyFanSum_add_le hhead_c htail_c N
    _ ≤ 2 * C * ll * (1 + Real.log N) + C * ll := add_le_add hhead htail
    _ = C * (ll * (3 + 2 * Real.log N)) := by ring

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

theorem log_log_add_sixteen_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, Real.log (Real.log ((N : ℝ) + 16)) ≤ A * Real.log (Real.log ((N : ℝ) + 3)) := by
  have h3 := one_lt_log_three
  set c₃ := Real.log (Real.log 3)
  have hc₃ : 0 < c₃ := Real.log_pos h3
  set a := Real.log (1 + Real.log 6)
  have ha : 0 ≤ a := Real.log_nonneg (by have := Real.log_nonneg (show (1 : ℝ) ≤ 6 by norm_num); linarith)
  refine ⟨a / c₃ + 1, by positivity, fun N => ?_⟩
  set L := Real.log ((N : ℝ) + 3)
  have hL : Real.log 3 ≤ L := Real.log_le_log (by norm_num) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  have hL1 : 1 ≤ L := by linarith
  have hlogL : c₃ ≤ Real.log L := Real.log_le_log (by linarith) hL
  have h1 : Real.log ((N : ℝ) + 16) ≤ Real.log 6 + L := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  have h6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have h2 : Real.log 6 + L ≤ (1 + Real.log 6) * L := by nlinarith
  have h16pos : 0 < Real.log ((N : ℝ) + 16) := by
    have := two_le_log_add_sixteen (x := N) (by positivity); linarith
  have h4 : Real.log (Real.log ((N : ℝ) + 16)) ≤ a + Real.log L := by
    calc Real.log (Real.log ((N : ℝ) + 16)) ≤ Real.log ((1 + Real.log 6) * L) :=
          Real.log_le_log h16pos (h1.trans h2)
      _ = a + Real.log L := Real.log_mul (by positivity) (by positivity)
  have h5 : a ≤ a / c₃ * Real.log L := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₃]
    exact mul_le_mul_of_nonneg_left hlogL ha
  nlinarith

theorem three_add_two_mul_log_le (N : ℕ) : 3 + 2 * Real.log N ≤ 8 * Real.log ((N : ℝ) + 2) := by
  have h2 := Real.log_two_gt_d9
  have hl2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  have hlN : Real.log N ≤ Real.log ((N : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Nat.cast_zero, Real.log_zero, zero_add]; exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log (by exact_mod_cast hN) (by linarith)
  linarith

/-- **Item 1 (block layer)**: `K_N(D₀) = O(log(N + 2) log log(N + 3))`. -/
theorem exists_kyFanSum_thetaBlockDiagonal_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      kyFanSum thetaBlockDiagonal N ≤ C * Real.log ((N : ℝ) + 2) * Real.log (Real.log ((N : ℝ) + 3)) := by
  obtain ⟨C, hC, hCN⟩ := exists_kyFanSum_thetaBlockDiagonal_le_aux
  obtain ⟨A, hA, hAN⟩ := log_log_add_sixteen_le
  refine ⟨C * A * 8, by positivity, fun N => ?_⟩
  have h1 := hCN N
  have h2 := hAN N
  have h3 := three_add_two_mul_log_le N
  have hll0 : 0 ≤ Real.log (Real.log ((N : ℝ) + 16)) := log_log_add_sixteen_nonneg N (by positivity)
  have hl3 : 0 ≤ Real.log (Real.log ((N : ℝ) + 3)) := by
    have := one_lt_log_three
    exact Real.log_nonneg (by
      have : Real.log 3 ≤ Real.log ((N : ℝ) + 3) :=
        Real.log_le_log (by norm_num) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
      linarith)
  have hN3 : 0 ≤ 3 + 2 * Real.log N := by
    have := Real.log_natCast_nonneg N; linarith
  calc kyFanSum thetaBlockDiagonal N ≤ C * (Real.log (Real.log (N + 16)) * (3 + 2 * Real.log N)) := h1
    _ ≤ C * ((A * Real.log (Real.log ((N : ℝ) + 3))) * (8 * Real.log ((N : ℝ) + 2))) := by
        gcongr
    _ = C * A * 8 * Real.log ((N : ℝ) + 2) * Real.log (Real.log ((N : ℝ) + 3)) := by ring

/-- **`K_N(D₀) = o((log N)²)`**. -/
theorem tendsto_kyFanSum_thetaBlockDiagonal_div_log_sq :
    Tendsto (fun N : ℕ => kyFanSum thetaBlockDiagonal N / Real.log N ^ 2) atTop (𝓝 0) := by
  obtain ⟨C, hC, hCN⟩ := exists_kyFanSum_thetaBlockDiagonal_le_aux
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hℓ : Tendsto (fun N : ℕ => Real.log N) atTop atTop := Real.tendsto_log_atTop.comp hNat
  have hℓ16 : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 16 hNat)
  have hlo : Tendsto (fun N : ℕ => Real.log (Real.log ((N : ℝ) + 16)) / Real.log ((N : ℝ) + 16)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hℓ16
  have hratio : Tendsto (fun N : ℕ => (3 + 2 * Real.log N) / Real.log N) atTop (𝓝 2) := by
    have h := (tendsto_const_nhds (x := (3 : ℝ))).div_atTop hℓ
    have := h.add (tendsto_const_nhds (x := (2 : ℝ)))
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hℓ.eventually_gt_atTop 0] with N hN
    field_simp
  have hup : Tendsto (fun N : ℕ => C * (2 * (Real.log (Real.log ((N : ℝ) + 16)) / Real.log ((N : ℝ) + 16))) *
      ((3 + 2 * Real.log N) / Real.log N)) atTop (𝓝 0) := by
    have := ((hlo.const_mul 2).const_mul C).mul hratio
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun N => by
    have := kyFanSum_nonneg thetaBlockDiagonal N; positivity) ?_ hup
  filter_upwards [hNat.eventually_ge_atTop 16, hℓ.eventually_gt_atTop 0] with N hN16 hlN
  have hN := hCN N
  have hll0 : 0 ≤ Real.log (Real.log ((N : ℝ) + 16)) := log_log_add_sixteen_nonneg N (by positivity)
  have hl16 : 0 < Real.log ((N : ℝ) + 16) := by
    have := two_le_log_add_sixteen (x := N) (by positivity); linarith
  have hcmp : Real.log ((N : ℝ) + 16) ≤ 2 * Real.log N := by
    rw [← Real.log_rpow (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hN3 : 0 ≤ 3 + 2 * Real.log N := by linarith
  rw [div_le_iff₀ (by positivity)]
  calc kyFanSum thetaBlockDiagonal N ≤ C * (Real.log (Real.log (N + 16)) * (3 + 2 * Real.log N)) := hN
    _ = C * (2 * (Real.log (Real.log ((N : ℝ) + 16)) / (2 * Real.log N))) *
          ((3 + 2 * Real.log N) / Real.log N) * Real.log N ^ 2 := by
        field_simp
    _ ≤ C * (2 * (Real.log (Real.log ((N : ℝ) + 16)) / Real.log ((N : ℝ) + 16))) *
          ((3 + 2 * Real.log N) / Real.log N) * Real.log N ^ 2 := by
        gcongr

end

end RHTower
