import GaloisForLFunctions.HTGeometry.GammaSetPositiveRowEquiv

/-!
# The Poincaré series as a sum over `(c, d mod c, l)`

Splitting the coprime rows into `(0, ±1)`, rows with `c > 0` and rows with `c < 0`, and using
that negating a row multiplies the summand by `(-1)^k`,

  `P_m(z) = (1 + (-1)^k) e(mz) + (1 + (-1)^k) Σ_{c ≥ 1} Σ_{u ∈ (ℤ/c)ˣ} Σ_{l ∈ ℤ}
              (c(z+l) + u.val)^{-k} e(m M_{c,u}(z + l))`,

all sums absolutely convergent for `k ≥ 3`.
-/

open UpperHalfPlane hiding I
open EisensteinSeries ModularGroup Complex Set
open scoped MatrixGroups Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The two rows with `c = 0` -/

/-- The row `(0, 1)`. -/
def zeroRowPos : gammaSet 1 1 0 := ⟨![0, 1], by rw [gammaSet_one_mem_iff]; simp⟩

/-- The row `(0, -1)`. -/
def zeroRowNeg : gammaSet 1 1 0 := gammaSetNeg zeroRowPos

theorem zeroRowPos_ne_zeroRowNeg : zeroRowPos ≠ zeroRowNeg := by
  intro h
  have := congrArg (fun v : gammaSet 1 1 0 => v.1 1) h
  simp [zeroRowPos, zeroRowNeg, gammaSetNeg] at this

theorem mem_zero_rows_iff (v : gammaSet 1 1 0) :
    v.1 0 = 0 ↔ v ∈ ({zeroRowPos, zeroRowNeg} : Finset (gammaSet 1 1 0)) := by
  constructor
  · intro h
    rcases gammaSet_snd_eq_of_fst_eq_zero v h with h1 | h1
    · apply Finset.mem_insert.mpr
      left
      apply Subtype.ext
      funext i
      fin_cases i
      · exact h
      · exact h1
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_singleton.mpr
      apply Subtype.ext
      funext i
      fin_cases i
      · exact h
      · exact h1
  · intro h
    rcases Finset.mem_insert.mp h with rfl | h
    · rfl
    · rw [Finset.mem_singleton.mp h]
      rfl

theorem poincareSummand_zeroRowPos (k : ℤ) (m : ℕ) (z : ℍ) :
    poincareSummand k m zeroRowPos z = expSeed m z := by
  have h0 : gammaSetMatrix zeroRowPos 1 0 = (1 : SL(2, ℤ)) 1 0 := by
    rw [gammaSetMatrix_apply_one_zero]; rfl
  have h1 : gammaSetMatrix zeroRowPos 1 1 = (1 : SL(2, ℤ)) 1 1 := by
    rw [gammaSetMatrix_apply_one_one]; rfl
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_mul_of_bottomRow_eq _ _ h0 h1
  rw [poincareSummand, hn, mul_one]
  have heis : eisSummand k zeroRowPos.1 z = 1 := by
    simp [eisSummand, zeroRowPos]
  rw [heis, one_mul]
  exact expSeed_T_zpow_smul m n z

theorem poincareSummand_zeroRowNeg (k : ℤ) (m : ℕ) (z : ℍ) :
    poincareSummand k m zeroRowNeg z = (-1) ^ k * expSeed m z := by
  rw [zeroRowNeg, poincareSummand_gammaSetNeg, poincareSummand_zeroRowPos]

/-! ## The coset term -/

/-- The summand attached to `(c, u, l)`: `(c(z+l) + u.val)^{-k} e(m M_{c,u}(z + l))`. -/
def cosetTerm (k : ℤ) (m : ℕ) (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) (z : ℍ) : ℂ :=
  ((c : ℂ) * ((z : ℂ) + l) + ((u : ZMod c).val : ℂ)) ^ (-k) *
    expSeed m (unitRowMatrix c u • (ModularGroup.T ^ l • z))

theorem cosetTerm_eq_poincareSummand (k : ℤ) (m : ℕ) (c : ℕ+) (u : (ZMod c)ˣ) (l : ℤ) (z : ℍ) :
    cosetTerm k m c u l z = poincareSummand k m (shiftedRow c u l) z :=
  (poincareSummand_shiftedRow k m c u l z).symm

/-- The summand on the sigma type. -/
def cosetTermSigma (k : ℤ) (m : ℕ) (z : ℍ) (p : Σ c : ℕ+, (ZMod c)ˣ × ℤ) : ℂ :=
  cosetTerm k m p.1 p.2.1 p.2.2 z

theorem cosetTermSigma_eq (k : ℤ) (m : ℕ) (z : ℍ) (p : Σ c : ℕ+, (ZMod c)ˣ × ℤ) :
    cosetTermSigma k m z p = poincareSummand k m (positiveRowEquiv p).1 z := by
  rw [cosetTermSigma, cosetTerm_eq_poincareSummand, positiveRowEquiv_apply]

theorem summable_cosetTermSigma {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    Summable (cosetTermSigma k m z) := by
  have h : Summable fun v : {v : gammaSet 1 1 0 // 0 < v.1 0} => poincareSummand k m v.1 z :=
    (summable_poincareSummand hk m z).subtype _
  have := (positiveRowEquiv.summable_iff (f := fun v : {v : gammaSet 1 1 0 // 0 < v.1 0} =>
    poincareSummand k m v.1 z)).mpr h
  refine this.congr fun p => ?_
  exact (cosetTermSigma_eq k m z p).symm

theorem summable_cosetTerm_prod {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) (c : ℕ+) :
    Summable fun q : (ZMod c)ˣ × ℤ => cosetTerm k m c q.1 q.2 z :=
  (summable_cosetTermSigma hk m z).sigma_factor c

theorem summable_cosetTerm {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) (c : ℕ+) (u : (ZMod c)ˣ) :
    Summable fun l : ℤ => cosetTerm k m c u l z :=
  (summable_cosetTerm_prod hk m z c).prod_factor u

/-! ## The decomposition -/

/-- Negation exchanges rows with `c > 0` and rows with `c < 0`. -/
def negRowEquiv : {v : gammaSet 1 1 0 // 0 < v.1 0} ≃ {v : gammaSet 1 1 0 // v.1 0 < 0} where
  toFun v := ⟨gammaSetNeg v.1, by
    have := v.2
    simp only [gammaSetNeg_val, Pi.neg_apply]
    linarith⟩
  invFun v := ⟨gammaSetNeg v.1, by
    have := v.2
    simp only [gammaSetNeg_val, Pi.neg_apply]
    linarith⟩
  left_inv v := Subtype.ext (gammaSetNeg_gammaSetNeg v.1)
  right_inv v := Subtype.ext (gammaSetNeg_gammaSetNeg v.1)

/-- **The coset decomposition of the Poincaré series.** -/
theorem poincareSeries_eq_cosetSum {k : ℤ} (hk : 3 ≤ k) (m : ℕ) (z : ℍ) :
    poincareSeries k m z
      = (1 + (-1) ^ k) * expSeed m z +
        (1 + (-1) ^ k) * ∑' c : ℕ+, ∑' u : (ZMod c)ˣ, ∑' l : ℤ, cosetTerm k m c u l z := by
  set f : gammaSet 1 1 0 → ℂ := fun v => poincareSummand k m v z with hf
  have hS : Summable f := summable_poincareSummand hk m z
  set s₀ : Set (gammaSet 1 1 0) := {v | v.1 0 = 0} with hs₀
  set sPos : Set (gammaSet 1 1 0) := {v | 0 < v.1 0} with hsPos
  set sNeg : Set (gammaSet 1 1 0) := {v | v.1 0 < 0} with hsNeg
  have hsplit : f = s₀.indicator f + sPos.indicator f + sNeg.indicator f := by
    funext v
    simp only [Pi.add_apply, Set.indicator_apply, hs₀, hsPos, hsNeg, Set.mem_setOf_eq]
    rcases lt_trichotomy (v.1 0) 0 with h | h | h
    · simp [h, h.ne, h.le]
    · simp [h]
    · simp [h, h.ne', h.le]
  have hsum : poincareSeries k m z = ∑' v, f v := rfl
  rw [hsum, hsplit]
  simp only [Pi.add_apply]
  rw [Summable.tsum_add ((hS.indicator s₀).add (hS.indicator sPos)) (hS.indicator sNeg),
    Summable.tsum_add (hS.indicator s₀) (hS.indicator sPos), ← tsum_subtype, ← tsum_subtype,
    ← tsum_subtype]
  -- the zero rows
  have h₀ : ∑' v : s₀, f v = (1 + (-1) ^ k) * expSeed m z := by
    have hset : s₀ = ↑({zeroRowPos, zeroRowNeg} : Finset (gammaSet 1 1 0)) := by
      ext v
      rw [hs₀, Set.mem_setOf_eq, Finset.mem_coe]
      exact mem_zero_rows_iff v
    rw [tsum_congr_set_coe f hset, Finset.tsum_subtype', Finset.sum_pair zeroRowPos_ne_zeroRowNeg]
    simp only [hf, poincareSummand_zeroRowPos, poincareSummand_zeroRowNeg]
    ring
  -- the negative rows
  have hNeg : ∑' v : sNeg, f v = (-1) ^ k * ∑' v : sPos, f v := by
    change (∑' v : {v : gammaSet 1 1 0 // v.1 0 < 0}, f v.1)
      = (-1) ^ k * ∑' v : {v : gammaSet 1 1 0 // 0 < v.1 0}, f v.1
    rw [← negRowEquiv.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun v => ?_
    simp only [hf, negRowEquiv, Equiv.coe_fn_mk, poincareSummand_gammaSetNeg]
  -- the positive rows
  have hPos : ∑' v : sPos, f v = ∑' c : ℕ+, ∑' u : (ZMod c)ˣ, ∑' l : ℤ, cosetTerm k m c u l z := by
    change (∑' v : {v : gammaSet 1 1 0 // 0 < v.1 0}, f v.1) = _
    rw [← positiveRowEquiv.tsum_eq]
    have hcongr : (fun p : Σ c : ℕ+, (ZMod c)ˣ × ℤ => f (positiveRowEquiv p).1)
        = cosetTermSigma k m z := by
      funext p
      exact (cosetTermSigma_eq k m z p).symm
    rw [show (∑' p : Σ c : ℕ+, (ZMod c)ˣ × ℤ, f (positiveRowEquiv p).1)
        = ∑' p, cosetTermSigma k m z p from tsum_congr fun p => congrFun hcongr p,
      (summable_cosetTermSigma hk m z).tsum_sigma]
    refine tsum_congr fun c => ?_
    show (∑' q : (ZMod c)ˣ × ℤ, cosetTerm k m c q.1 q.2 z) = _
    rw [(summable_cosetTerm_prod hk m z c).tsum_prod]
  rw [h₀, hNeg, hPos]
  ring

end

end GaloisForLFunctions.HTGeometry
