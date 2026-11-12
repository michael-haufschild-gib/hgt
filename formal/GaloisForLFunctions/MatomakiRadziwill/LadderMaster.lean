import GaloisForLFunctions.MatomakiRadziwill.LadderRough

/-!
# The master inequality of the ladder

For a ladder configuration (`LadderScales`), block widths `H_j`, thresholds `c_j(v)`, exponents
`ℓ_j(u, v)` and a pointwise bound `ρ` for the top-scale blocks (`ladder_master`):

`∫_{|w|≤W} |Σ_{n∈S} f(n)/n · n^{2πiw}|²
   ≤ 2E_0 + 2#V_0 Σ_v c_0(v)² ∫|R_{0,v}|²
     + Σ_{1≤j<J} (2E_j + 2#V_j Σ_v Σ_u c_j(v)² c_{j−1}(u)^{-2ℓ} ∫|Q_{j−1,u}^ℓ R_{j,v}|²)
     + 2E* + 2#V* ρ² Σ_v ∫_E |R*_v|²`,

`E_j` the Ramaré error of scale `j` (`ramErr`) and `E = [−W, W] ∖ small_{J−1}` the exceptional set.
It combines the cover (`ladder_cover_integral`), Ramaré's decomposition at every scale
(`integral_normSq_rough_sub_pairPoly_le`, all scales seeing the same rough set), the first and later
ladder steps, and the pointwise bound on the exceptional set.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The Ramaré error of one scale. -/
def ramErr (W : ℝ) (X : ℕ) (H : ℝ) (P : ℕ) : ℝ :=
  (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((8 * X : ℕ) : ℝ))
    * (4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P))

theorem continuous_pairPoly (f : ℕ → ℂ) {Pr : Finset ℕ} (hPr : ∀ q ∈ Pr, q.Prime)
    (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) :
    Continuous (pairPoly f Pr rest X H) := by
  have h : pairPoly f Pr rest X H
      = fun w => ∑ v ∈ Pr.image (blk H), blockQ f Pr H v w * blockR f Pr rest X H v w :=
    funext fun w => pairPoly_eq_sum_blocks f hPr rest X H w
  rw [h]
  exact continuous_finsetSum _ fun v _ =>
    (continuous_logPoly _ _).mul (continuous_logPoly _ _)

namespace LadderScales

variable (L : LadderScales)

/-- The blocks of scale `j`. -/
def blocks (H : ℕ → ℝ) (j : ℕ) : Finset ℕ := (L.scale j).image (blk (H j))

/-- The blocks of the top scale. -/
def topBlocks (Htop : ℝ) : Finset ℕ := L.top.image (blk Htop)

/-- The frequencies where every block of scale `j` is small. -/
def smallSet (f : ℕ → ℂ) (H : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (j : ℕ) : Set ℝ :=
  smallAt (blockQ f (L.scale j) (H j)) (L.blocks H j) (c j)

theorem measurableSet_smallSet (f : ℕ → ℂ) (H : ℕ → ℝ) (c : ℕ → ℕ → ℝ) (j : ℕ) :
    MeasurableSet (L.smallSet f H c j) :=
  (isClosed_smallAt (fun _ => continuous_logPoly _ _) _ _).measurableSet

/-- **The master inequality of the ladder.** -/
theorem ladder_master {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hmul : ∀ a b, f (a * b) = f a * f b)
    (hJ : 1 ≤ L.J) {X : ℕ} (hX : 1 ≤ X) {W : ℝ} (hW : 1 ≤ W)
    {H : ℕ → ℝ} (hH : ∀ j, 2 ≤ H j) {Htop : ℝ} (hHtop : 2 ≤ Htop)
    {P : ℕ → ℕ} (hP : ∀ j, 2 ≤ P j) (hPmin : ∀ j, ∀ p ∈ L.scale j, P j ≤ p)
    {Ptop : ℕ} (hPtop : 2 ≤ Ptop) (hPtopmin : ∀ p ∈ L.top, Ptop ≤ p)
    (c : ℕ → ℕ → ℝ) (hc : ∀ j u, 0 < c j u) (ℓ : ℕ → ℕ → ℕ → ℕ)
    {ρ : ℝ} (hρ : ∀ v ∈ L.topBlocks Htop, ∀ w ∈ Icc (-W) W, ‖blockQ f L.top Htop v w‖ ≤ ρ) :
    (∫ w in Icc (-W) W, ‖logPoly (coefA f) (L.ladderS X) w‖ ^ 2)
      ≤ (2 * ramErr W X (H 0) (P 0)
          + 2 * ((L.blocks H 0).card * ∑ v ∈ L.blocks H 0, c 0 v ^ 2
              * (∫ w in Icc (-W) W, ‖blockR f (L.scale 0) (L.restAt 0) X (H 0) v w‖ ^ 2)))
        + ∑ j ∈ Finset.Ico 1 L.J, (2 * ramErr W X (H j) (P j)
          + 2 * ((L.blocks H j).card * ∑ v ∈ L.blocks H j, ∑ u ∈ L.blocks H (j - 1),
              c j v ^ 2 / c (j - 1) u ^ (2 * ℓ j u v)
              * (∫ w in Icc (-W) W, ‖blockQ f (L.scale (j - 1)) (H (j - 1)) u w ^ ℓ j u v
                  * blockR f (L.scale j) (L.restAt j) X (H j) v w‖ ^ 2)))
        + (2 * ramErr W X Htop Ptop
          + 2 * ((L.topBlocks Htop).card * ρ ^ 2 * ∑ v ∈ L.topBlocks Htop,
              (∫ w in Icc (-W) W ∩ (L.smallSet f H c (L.J - 1))ᶜ,
                ‖blockR f L.top L.restTop X Htop v w‖ ^ 2))) := by
  classical
  set F : ℝ → ℂ := logPoly (coefA f) (L.ladderS X) with hFdef
  set D : ℕ → ℝ → ℂ := fun j => pairPoly f (L.scale j) (L.restAt j) X (H j) with hDdef
  set Dtop : ℝ → ℂ := pairPoly f L.top L.restTop X Htop with hDtopdef
  have hcover := ladder_cover_integral (F := F) (D := D) (Dtop := Dtop) (continuous_logPoly _ _)
    (fun j => continuous_pairPoly f (L.prime_scale j) _ X (H j))
    (continuous_pairPoly f L.prime_top _ X Htop) (L.measurableSet_smallSet f H c) hJ W
  -- Ramaré's decomposition at every scale
  have hram : ∀ j ∈ range L.J, (∫ w in Icc (-W) W, ‖F w - D j w‖ ^ 2) ≤ ramErr W X (H j) (P j) := by
    intro j hj
    have h := integral_normSq_rough_sub_pairPoly_le hf hmul (L.prime_scale j) (hP j) (hPmin j)
      (fun p hp m => L.restAt_mul_iff hp m) hX (hH j) hW
    rw [L.roughSet_restAt_eq hj X] at h
    exact h
  have hramtop : (∫ w in Icc (-W) W, ‖F w - Dtop w‖ ^ 2) ≤ ramErr W X Htop Ptop := by
    have h := integral_normSq_rough_sub_pairPoly_le hf hmul L.prime_top hPtop hPtopmin
      (fun p hp m => L.restTop_mul_iff hp m) hX hHtop hW
    rw [L.roughSet_restTop_eq X] at h
    exact h
  -- the decomposition as a sum over blocks
  have hDj : ∀ j w, D j w = ∑ v ∈ L.blocks H j, blockQ f (L.scale j) (H j) v w
      * blockR f (L.scale j) (L.restAt j) X (H j) v w := fun j w =>
    pairPoly_eq_sum_blocks f (L.prime_scale j) _ X (H j) w
  -- the first step
  have hfirst : (∫ w in Icc (-W) W, (L.smallSet f H c 0).indicator (fun w => ‖D 0 w‖ ^ 2) w)
      ≤ (L.blocks H 0).card * ∑ v ∈ L.blocks H 0, c 0 v ^ 2
          * (∫ w in Icc (-W) W, ‖blockR f (L.scale 0) (L.restAt 0) X (H 0) v w‖ ^ 2) := by
    have heq : (L.smallSet f H c 0).indicator (fun w => ‖D 0 w‖ ^ 2)
        = (smallAt (blockQ f (L.scale 0) (H 0)) (L.blocks H 0) (c 0)).indicator
            (fun w => ‖∑ v ∈ L.blocks H 0, blockQ f (L.scale 0) (H 0) v w
              * blockR f (L.scale 0) (L.restAt 0) X (H 0) v w‖ ^ 2) := by
      funext w; rw [smallSet]; simp only [hDj]
    rw [heq]
    exact integral_indicator_small_le (fun v => continuous_logPoly _ _) _ _ W
  -- the later steps
  have hstep : ∀ j ∈ Finset.Ico 1 L.J,
      (∫ w in Icc (-W) W, (L.smallSet f H c j ∩ (L.smallSet f H c (j - 1))ᶜ).indicator
        (fun w => ‖D j w‖ ^ 2) w)
      ≤ (L.blocks H j).card * ∑ v ∈ L.blocks H j, ∑ u ∈ L.blocks H (j - 1),
          c j v ^ 2 / c (j - 1) u ^ (2 * ℓ j u v)
          * (∫ w in Icc (-W) W, ‖blockQ f (L.scale (j - 1)) (H (j - 1)) u w ^ ℓ j u v
              * blockR f (L.scale j) (L.restAt j) X (H j) v w‖ ^ 2) := by
    intro j _
    have heq : (L.smallSet f H c j ∩ (L.smallSet f H c (j - 1))ᶜ).indicator
          (fun w => ‖D j w‖ ^ 2)
        = (smallAt (blockQ f (L.scale j) (H j)) (L.blocks H j) (c j)
            ∩ (smallAt (blockQ f (L.scale (j - 1)) (H (j - 1))) (L.blocks H (j - 1))
              (c (j - 1)))ᶜ).indicator
            (fun w => ‖∑ v ∈ L.blocks H j, blockQ f (L.scale j) (H j) v w
              * blockR f (L.scale j) (L.restAt j) X (H j) v w‖ ^ 2) := by
      funext w; rw [smallSet, smallSet]; simp only [hDj]
    rw [heq]
    exact integral_indicator_small_not_small_le (fun v => continuous_logPoly _ _)
      (fun u => continuous_logPoly _ _) _ _ _ _ (fun u _ => hc (j - 1) u) (ℓ j) W
  -- the exceptional set
  have hEm : MeasurableSet (L.smallSet f H c (L.J - 1))ᶜ :=
    (L.measurableSet_smallSet f H c _).compl
  have htop : (∫ w in Icc (-W) W, (L.smallSet f H c (L.J - 1))ᶜ.indicator
        (fun w => ‖Dtop w‖ ^ 2) w)
      ≤ (L.topBlocks Htop).card * ρ ^ 2 * ∑ v ∈ L.topBlocks Htop,
          (∫ w in Icc (-W) W ∩ (L.smallSet f H c (L.J - 1))ᶜ,
            ‖blockR f L.top L.restTop X Htop v w‖ ^ 2) := by
    rw [integral_indicator hEm, Measure.restrict_restrict hEm, inter_comm]
    have hDt : ∀ w, Dtop w = ∑ v ∈ L.topBlocks Htop, blockQ f L.top Htop v w
        * blockR f L.top L.restTop X Htop v w := fun w =>
      pairPoly_eq_sum_blocks f L.prime_top _ X Htop w
    simp only [hDt]
    exact setIntegral_sum_blocks_le_of_bound (fun v => continuous_logPoly _ _) _
      (measurableSet_Icc.inter hEm) inter_subset_left hρ
  -- assemble
  refine le_trans hcover ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact add_le_add (by linarith [hram 0 (mem_range.mpr (by omega))])
      (by linarith [hfirst])
  · refine sum_le_sum fun j hj => ?_
    have hjr : j ∈ range L.J := mem_range.mpr (Finset.mem_Ico.mp hj).2
    exact add_le_add (by linarith [hram j hjr]) (by linarith [hstep j hj])
  · exact add_le_add (by linarith [hramtop]) (by linarith [htop])

end LadderScales

end

end GaloisForLFunctions.MatomakiRadziwill
