import GaloisForLFunctions.RHTower.WeilLogShiftCostReverseCauchy
import GaloisForLFunctions.RHTower.WeilLogShiftGramExactImage

/-! Actual native tail cost has a reverse triangle law on each distinct-node
nonnegative amplitude cone. This also holds on fixed nodes realizing every target. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

theorem finiteWeilGramTailCost_eq_absolute_pair {ι : Type} [Fintype ι] (x u : ι → ℝ) :
    finiteWeilGramTailCost 1 (finiteWeilGramTestOfFinite x u 1) =
      finiteWeilCostPair x (fun i => |u i|) (fun i => |u i|) := by
  rw [finiteWeilGramTailCost_ofFinite]
  simp only [NNReal.coe_one, one_mul, abs_mul, finiteWeilCostPair]

theorem finiteWeilGramTailCost_nonnegative_eq_pair {ι : Type} [Fintype ι]
    (x : ι → ℝ) (u : ι → NNReal) :
    finiteWeilGramTailCost 1 (finiteWeilGramTestOfFinite x (fun i => (u i : ℝ)) 1) =
      finiteWeilCostPair x (fun i => (u i : ℝ)) (fun i => (u i : ℝ)) := by
  rw [finiteWeilGramTailCost_eq_absolute_pair]
  simp only [abs_of_nonneg (NNReal.coe_nonneg _)]

/-- For actual tests, equality in reverse Minkowski means a common nonnegative ray. -/
theorem finiteWeilGramTailCost_sqrt_superadditive {ι : Type} [Fintype ι]
    (x : ι → ℝ) (hx : Function.Injective x) (u v : ι → NNReal) :
    let C := fun w : ι → NNReal =>
      finiteWeilGramTailCost 1 (finiteWeilGramTestOfFinite x (fun i => (w i : ℝ)) 1)
    Real.sqrt (C u) + Real.sqrt (C v) ≤ Real.sqrt (C (u + v)) ∧
      (Real.sqrt (C (u + v)) = Real.sqrt (C u) + Real.sqrt (C v) ↔
        v = 0 ∨ ∃ c : NNReal, u = fun i => c * v i) := by
  dsimp only
  simp only [finiteWeilGramTailCost_nonnegative_eq_pair]
  have hcast : (fun i => ((u + v) i : ℝ)) =
      (fun i => (u i : ℝ)) + (fun i => (v i : ℝ)) := rfl
  rw [hcast]
  have h := finiteWeilCostPair_sqrt_superadditive x
    (fun i => (u i : ℝ)) (fun i => (v i : ℝ)) hx
    (fun i => NNReal.coe_nonneg (u i)) (fun i => NNReal.coe_nonneg (v i))
  refine ⟨h.1, h.2.trans ?_⟩
  constructor
  · rintro (hz | ⟨c, hc⟩)
    · left
      funext i
      exact NNReal.coe_injective (congrFun hz i)
    · by_cases hz : v = 0
      · exact Or.inl hz
      · right
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
        have hvi : (v i : ℝ) ≠ 0 := fun he => hi (NNReal.coe_injective he)
        have hvpos := lt_of_le_of_ne (NNReal.coe_nonneg (v i)) (Ne.symm hvi)
        have hcpos : 0 ≤ c := by
          by_contra he
          have hn := mul_neg_of_neg_of_pos (lt_of_not_ge he) hvpos
          have hui := NNReal.coe_nonneg (u i)
          rw [congrFun hc i] at hui
          linarith
        refine ⟨NNReal.mk c hcpos, ?_⟩
        funext j
        exact NNReal.coe_injective (congrFun hc j)
  · rintro (rfl | ⟨c, hc⟩)
    · exact Or.inl rfl
    · right
      refine ⟨(c : ℝ), ?_⟩
      funext i
      exact congrArg (fun a : NNReal => (a : ℝ)) (congrFun hc i)

/-- Finite real node sets discharge distinctness; nonnegative amplitudes carry no hypotheses. -/
theorem finiteWeilGram_distinct_cost_geometry (s : Finset ℝ) :
    let C := fun w : s → NNReal => finiteWeilGramTailCost 1
      (finiteWeilGramTestOfFinite (fun i : s => (i : ℝ)) (fun i => (w i : ℝ)) 1)
    ∀ u v : s → NNReal,
      Real.sqrt (C u) + Real.sqrt (C v) ≤ Real.sqrt (C (u + v)) ∧
        (Real.sqrt (C (u + v)) = Real.sqrt (C u) + Real.sqrt (C v) ↔
          v = 0 ∨ ∃ c : NNReal, u = fun i => c * v i) := by
  intro C u v
  exact finiteWeilGramTailCost_sqrt_superadditive (fun i : s => (i : ℝ))
    (fun _ _ he => Subtype.ext he) u v

/-- One fixed node set has full coefficient image and the sharp cost geometry simultaneously. -/
theorem exists_finiteWeilGram_exact_image_cost_geometry (s : Finset ℕ) :
    ∃ N : ℕ, ∃ x : Fin N → ℝ, ∃ R : ℝ,
      Function.Injective x ∧
      Function.Surjective (fun u : Fin N → ℝ =>
        finiteWeilGramCoefficientVector s ⟨N, x, u, 1⟩) ∧
      0 < R ∧
      (∀ u : Fin N → ℝ,
        0 ≤ R * finiteWeilCostMoment x u ^ 2 - finiteWeilCostPair x u u ∧
          (R * finiteWeilCostMoment x u ^ 2 - finiteWeilCostPair x u u = 0 ↔ u = 0)) ∧
      (let C := fun w : Fin N → NNReal => finiteWeilGramTailCost 1
          (finiteWeilGramTestOfFinite x (fun i => (w i : ℝ)) 1)
        ∀ u v : Fin N → NNReal,
          Real.sqrt (C u) + Real.sqrt (C v) ≤ Real.sqrt (C (u + v)) ∧
            (Real.sqrt (C (u + v)) = Real.sqrt (C u) + Real.sqrt (C v) ↔
              v = 0 ∨ ∃ c : NNReal, u = fun i => c * v i)) := by
  obtain ⟨N, x, hx, hsurj⟩ := exists_finiteWeilGram_distinct_fixed_node_surjection s
  obtain ⟨R, hR, hd⟩ := exists_finiteWeilCostPair_strict_defect x hx
  exact ⟨N, x, R, hx, hsurj, hR, hd, fun u v =>
    finiteWeilGramTailCost_sqrt_superadditive x hx u v⟩

end RHTower
