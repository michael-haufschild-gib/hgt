import GaloisForLFunctions.RHTower.Sieve.LinearBlockEstimate

/-!
# Summing the block estimate over a range

The blocks `Y(1+ε)^k < x ≤ Y(1+ε)^{k+1}` tile `Y < x ≤ Y(1+ε)^K`, and on each of them the block
estimate applies with base point `Y(1+ε)^k ≥ Y`, so the multiplicative ratio is at most the one at
`Y`.  Adding them gives

    ∫_{log Y}^{log(Y(1+ε)^K)} |∑_{e^u < n ≤ e^u+L} a_n|² du
      ≤ K·( 2(M₁·log(1+L/Y) + M₂·2/(π²W)) + 2(εL+1)²·log(1+ε) ) .

`K` blocks of ratio `1+ε` cover a range of ratio `(1+ε)^K`, so covering a dyadic range costs
`K ≈ log 2 / log(1+ε)` blocks.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The per-block cost. -/
noncomputable def blockCost (L Y ε M₁ M₂ W : ℝ) : ℝ :=
  2 * (M₁ * Real.log (1 + L / Y) + M₂ * (2 / (Real.pi ^ 2 * W)))
    + 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε)

theorem blockCost_nonneg {L Y ε M₁ M₂ W : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε)
    (hW : 0 < W) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) : 0 ≤ blockCost L Y ε M₁ M₂ W := by
  have hlog1 : 0 ≤ Real.log (1 + L / Y) := by
    refine Real.log_nonneg ?_
    have : 0 < L / Y := by positivity
    linarith
  have hlog2 : 0 ≤ Real.log (1 + ε) := Real.log_nonneg (by linarith)
  have hpi : 0 < Real.pi ^ 2 * W := by positivity
  rw [blockCost]
  have h1 : 0 ≤ M₁ * Real.log (1 + L / Y) := mul_nonneg hM₁ hlog1
  have h2 : 0 ≤ M₂ * (2 / (Real.pi ^ 2 * W)) := by positivity
  have h3 : 0 ≤ 2 * (ε * L + 1) ^ 2 * Real.log (1 + ε) := by positivity
  linarith

/-- **The range estimate.**  `K` blocks of ratio `1+ε`, each paying the block cost. -/
theorem setIntegral_normSq_linWindowSum_range_le (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {L Y ε M₁ M₂ W : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hW : 0 < W)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2 ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) (K : ℕ) :
    (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε) ^ K)),
        ‖linWindowSum a s L u‖ ^ 2)
      ≤ (K : ℝ) * blockCost L Y ε M₁ M₂ W := by
  classical
  have hone : (0 : ℝ) < 1 + ε := by linarith
  induction K with
  | zero =>
      simp
  | succ K ih =>
      set Z : ℝ := Y * (1 + ε) ^ K with hZ
      have hZ0 : 0 < Z := by rw [hZ]; positivity
      have hZY : Y ≤ Z := by
        rw [hZ]
        nlinarith [one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε) (n := K), hY.le]
      have hnext : Y * (1 + ε) ^ (K + 1) = Z * (1 + ε) := by
        rw [hZ]; ring
      have hlogle : Real.log Y ≤ Real.log Z := Real.log_le_log hY hZY
      have hlogle2 : Real.log Z ≤ Real.log (Z * (1 + ε)) := by
        refine Real.log_le_log hZ0 ?_
        nlinarith [hZ0.le, hε]
      -- the two pieces
      have hunion : Set.Ioc (Real.log Y) (Real.log Z) ∪
          Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε)))
          = Set.Ioc (Real.log Y) (Real.log (Z * (1 + ε))) :=
        Set.Ioc_union_Ioc_eq_Ioc hlogle hlogle2
      have hdisj : Disjoint (Set.Ioc (Real.log Y) (Real.log Z))
          (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε)))) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx.2 (not_le.2 hx'.1)
      have hfin₁ : volume (Set.Ioc (Real.log Y) (Real.log Z)) ≠ ⊤ := by simp
      have hfin₂ : volume (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε)))) ≠ ⊤ := by simp
      have hsplit : (∫ u in Set.Ioc (Real.log Y) (Real.log (Z * (1 + ε))),
            ‖linWindowSum a s L u‖ ^ 2)
          = (∫ u in Set.Ioc (Real.log Y) (Real.log Z), ‖linWindowSum a s L u‖ ^ 2)
            + ∫ u in Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε))),
                ‖linWindowSum a s L u‖ ^ 2 := by
        rw [← hunion]
        exact setIntegral_union hdisj measurableSet_Ioc
          (integrableOn_normSq_linWindowSum a s L hfin₁)
          (integrableOn_normSq_linWindowSum a s L hfin₂)
      -- the new block
      have hblock := setIntegral_normSq_linWindowSum_block_le a s hs ha (L := L) (Y := Z)
        (ε := ε) (M₁ := M₁) (M₂ := M₂) (W := W) hL hZ0 hε hW hM₁ hM₂ h₁ h₂
      have hvol : volume.real (Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε))))
          = Real.log (1 + ε) := by
        rw [measureReal_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith), Real.log_mul (ne_of_gt hZ0) (ne_of_gt hone)]
        ring
      have hmono : Real.log (1 + L / Z) ≤ Real.log (1 + L / Y) := by
        refine Real.log_le_log (by positivity) ?_
        have : L / Z ≤ L / Y := by
          refine div_le_div_of_nonneg_left hL.le hY hZY
        linarith
      have hblock' : (∫ u in Set.Ioc (Real.log Z) (Real.log (Z * (1 + ε))),
            ‖linWindowSum a s L u‖ ^ 2) ≤ blockCost L Y ε M₁ M₂ W := by
        refine le_trans hblock ?_
        rw [hvol, blockCost]
        have := mul_le_mul_of_nonneg_left hmono hM₁
        linarith
      rw [hnext, hsplit]
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hIH := ih
      have hcost := blockCost_nonneg (L := L) (Y := Y) (ε := ε) (M₁ := M₁) (M₂ := M₂)
        (W := W) hL hY hε hW hM₁ hM₂
      nlinarith [hIH, hblock', hcost]

end RHTower.Sieve
