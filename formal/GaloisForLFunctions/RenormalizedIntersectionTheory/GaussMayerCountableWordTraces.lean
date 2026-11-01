import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerFixedPointTrace

/-!
# Countable Gauss words and actual Mayer power traces

Every positive power of the actual Mayer operator has an absolutely convergent
fixed-point trace expansion over the countable Gauss alphabet on `Re w > 1`.
Product bounds in the branch digits and geometric Cauchy bounds justify the
interchange; the source Hilbert factorization identifies the resulting trace.

Each word has an integral matrix of determinant `(-1)^k`, a real periodic point
in `(0,1)`, and an expanding multiplier satisfying its integral quadratic
characteristic equation. Its trace contribution is `λ^(-w)/(1-(-1)^k λ^(-2))`.
Shifting `w` by two and retaining the orientation sign cancels the denominator.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTrace

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords

/-- A word of length `k`; entry `a j` denotes the branch with digit `a j+1`. -/
abbrev Word (k : ℕ) := Fin k → ℕ

/-- The literal map of a composed Gauss branch word. -/
def wordMap : (k : ℕ) → Word k → ℂ → ℂ
  | 0, _, z => z
  | k+1, a, z => wordMap k (Fin.tail a) (((a 0 + 1 : ℕ) : ℂ) + z)⁻¹

/-- The product weight along the literal composed branch orbit. -/
def wordWeight (w : ℂ) : (k : ℕ) → Word k → ℂ → ℂ
  | 0, _, _ => 1
  | k+1, a, z => ((((a 0 + 1 : ℕ) : ℂ) + z)^(-w)) *
      wordWeight w k (Fin.tail a) (((a 0 + 1 : ℕ) : ℂ) + z)⁻¹

/-- The same word as a composition of the actual bounded branch operators. -/
def wordOperator (w : ℂ) (hw : 0 < w.re) :
    (k : ℕ) → Word k → DiscSpace →L[ℂ] DiscSpace
  | 0, _ => ContinuousLinearMap.id ℂ DiscSpace
  | k+1, a => (branch w hw (a 0+1) (Nat.succ_pos _)).comp
      (wordOperator w hw k (Fin.tail a))

private theorem digit_slit (n : ℕ) {z : ℂ} (hz : z ∈ outer) :
    ((n+1 : ℕ) : ℂ) + z ∈ Complex.slitPlane := by
  have hd : ‖z-1‖ ≤ (3/2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (neg_le_abs (z-1).re).trans ((Complex.abs_re_le_norm _).trans hd)
  simp only [Complex.sub_re, Complex.one_re] at hr
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [add_re, natCast_re]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  linarith only [hr, hn]

private theorem digit_ne_zero (n : ℕ) {z : ℂ} (hz : z ∈ outer) :
    ((n+1 : ℕ) : ℂ) + z ≠ 0 := by
  intro h
  have hs := Complex.mem_slitPlane_iff.mp (digit_slit n hz)
  rw [h] at hs
  norm_num at hs

private theorem digit_differentiable (n : ℕ) :
    DifferentiableOn ℂ (fun z : ℂ => (((n+1 : ℕ) : ℂ) + z)⁻¹) outer := by
  intro z hz
  exact ((differentiableAt_id.const_add _).inv (digit_ne_zero n hz)).differentiableWithinAt

/-- Every word preserves each concentric disc between radii one and three halves. -/
theorem wordMap_mapsTo (k : ℕ) (a : Word k) {r : ℝ} (hr : 1 ≤ r) (hr' : r ≤ 3/2) :
    MapsTo (wordMap k a) (closedBall 1 r) (closedBall 1 r) := by
  induction k with
  | zero => exact fun _ h => h
  | succ k ih =>
      intro z hz
      apply ih (Fin.tail a)
      exact closedBall_subset_closedBall hr
        (inverse_branch_inner (Nat.succ_pos _)
          (closedBall_subset_closedBall hr' hz))

/-- Every nonempty word lands in the same inner disc. -/
theorem wordMap_inner (k : ℕ) (a : Word (k+1)) :
    MapsTo (wordMap (k+1) a) outer (closedBall 1 1) := by
  intro z hz
  exact wordMap_mapsTo k (Fin.tail a) le_rfl (by norm_num)
    (inverse_branch_inner (Nat.succ_pos _) hz)

/-- Composed branch maps are holomorphic on the full closed source disc. -/
theorem wordMap_differentiable (k : ℕ) (a : Word k) :
    DifferentiableOn ℂ (wordMap k a) outer := by
  induction k with
  | zero => exact differentiableOn_id
  | succ k ih =>
      exact (ih (Fin.tail a)).comp (digit_differentiable (a 0))
        (fun z hz => closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner (Nat.succ_pos _) hz))

/-- Products of the actual principal-power branch weights are holomorphic. -/
theorem wordWeight_differentiable (w : ℂ) (k : ℕ) (a : Word k) :
    DifferentiableOn ℂ (wordWeight w k a) outer := by
  induction k with
  | zero => exact differentiableOn_const _
  | succ k ih =>
      have hd : DifferentiableOn ℂ (fun z : ℂ => ((((a 0+1 : ℕ) : ℂ)+z)^(-w))) outer := by
        intro z hz
        exact (((hasDerivAt_id z).const_add _).cpow_const
          (c := -w) (digit_slit (a 0) hz)).differentiableAt.differentiableWithinAt
      exact hd.mul ((ih (Fin.tail a)).comp (digit_differentiable (a 0))
        (fun z hz => closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner (Nat.succ_pos _) hz)))

/-- Word composition agrees pointwise with its literal orbit and weight. -/
theorem wordOperator_apply (w : ℂ) (hw : 0 < w.re) (k : ℕ) (a : Word k)
    (f : DiscSpace) (z : Disc) :
    (wordOperator w hw k a f).1 z = wordWeight w k a z * plane f (wordMap k a z) := by
  induction k generalizing z with
  | zero => simpa only [wordOperator, ContinuousLinearMap.id_apply, wordWeight, wordMap,
      one_mul] using (plane_eq f z).symm
  | succ k ih =>
      change (branch w hw (a 0+1) (Nat.succ_pos _) (wordOperator w hw k (Fin.tail a) f)).1 z = _
      rw [branch_apply]
      have hz : ((((a 0+1 : ℕ) : ℂ) + z.1)⁻¹) ∈ outer :=
        closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner (Nat.succ_pos _) z.2)
      rw [plane_eq _ ⟨_, hz⟩, ih (Fin.tail a) ⟨_, hz⟩]
      simp only [wordWeight, wordMap, mul_assoc]

/-- Product majorant with one summable digit factor per word position. -/
def wordBound (w : ℂ) (k : ℕ) (a : Word k) : ℝ :=
  ∏ j, powerBound w * ((a j+1 : ℕ) : ℝ)^(-w.re)

theorem wordBound_nonneg (w : ℂ) (k : ℕ) (a : Word k) : 0 ≤ wordBound w k a := by
  apply Finset.prod_nonneg
  intro j _
  exact mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Orbit weights satisfy the product majorant uniformly on the source disc. -/
theorem norm_wordWeight_le {w : ℂ} (hw : 0 < w.re) (k : ℕ) (a : Word k)
    {z : ℂ} (hz : z ∈ outer) : ‖wordWeight w k a z‖ ≤ wordBound w k a := by
  induction k generalizing z with
  | zero => simp [wordWeight, wordBound]
  | succ k ih =>
      rw [wordWeight, norm_mul]
      have hz' : ((((a 0+1 : ℕ) : ℂ) + z)⁻¹) ∈ outer :=
        closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner (Nat.succ_pos _) hz)
      have h := mul_le_mul (norm_branch_weight_le hw (Nat.succ_pos (a 0)) hz)
        (ih (Fin.tail a) hz') (norm_nonneg _)
        (mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      simpa only [wordBound, Fin.prod_univ_succ, Fin.tail] using h

/-- A nonempty word sends every Cauchy monomial to a function with the same
word majorant, independently of the monomial degree. -/
theorem norm_wordOperator_monomial_le {w : ℂ} (hw : 0 < w.re)
    (k : ℕ) (a : Word (k+1)) (j : ℕ) :
    ‖wordOperator w hw (k+1) a (monomial j)‖ ≤ wordBound w (k+1) a := by
  change ‖(wordOperator w hw (k+1) a (monomial j)).1‖ ≤ _
  apply (ContinuousMap.norm_le _ (wordBound_nonneg w _ a)).mpr
  intro z
  rw [wordOperator_apply]
  have hu := wordMap_inner k a z.2
  have hu' : wordMap (k+1) a z ∈ outer :=
    closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) hu
  rw [plane_eq _ ⟨_, hu'⟩]
  change ‖wordWeight w (k+1) a z * (wordMap (k+1) a z - 1)^j‖ ≤ _
  rw [norm_mul, norm_pow]
  have hnorm : ‖wordMap (k+1) a z-1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hu
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hnorm) (norm_nonneg _)).trans
    (by simpa only [mul_one] using norm_wordWeight_le hw (k+1) a z.2)

/-- The diagonal majorant separates the word and Cauchy indices. -/
theorem norm_word_diagonal_le {w : ℂ} (hw : 0 < w.re)
    (k : ℕ) (a : Word (k+1)) (j : ℕ) :
    ‖traceCoefficient j (wordOperator w hw (k+1) a (monomial j))‖ ≤
      coefficientRadius⁻¹^j * wordBound w (k+1) a := by
  apply ((traceCoefficient j).le_opNorm _).trans
  exact mul_le_mul (norm_coefficient_le coefficientRadius coefficientRadius_pos radii.2.2 j)
    (norm_wordOperator_monomial_le hw k a j) (norm_nonneg _)
    (pow_nonneg (inv_nonneg.mpr coefficientRadius_pos.le) _)

/-- Every nonempty actual Gauss word has a unique attracting fixed point. -/
theorem exists_word_fixedPoint (k : ℕ) (a : Word (k+1)) :
    ∃ p : ℂ, p ∈ closedBall 1 1 ∧ wordMap (k+1) a p = p ∧
      (∀ q ∈ ball 1 coefficientRadius, wordMap (k+1) a q = q → q = p) ∧
      ‖deriv (wordMap (k+1) a) p‖ < 1 := by
  have hmap : MapsTo (wordMap (k+1) a) (ball 1 coefficientRadius)
      (closedBall 1 ((25/32 : ℝ) * coefficientRadius)) := by
    norm_num [coefficientRadius]
    exact (wordMap_inner k a).mono_left
      (ball_subset_closedBall.trans (closedBall_subset_closedBall radii.2.2.le))
  obtain ⟨p,hp,hfix,huniq,hder⟩ := DiscFixedPoint.exists_unique_fixedPoint
    coefficientRadius_pos (by norm_num : (0 : ℝ) ≤ 25/32)
    (by norm_num : (25/32 : ℝ) < 1)
    ((wordMap_differentiable (k+1) a).mono
      (ball_subset_closedBall.trans (closedBall_subset_closedBall radii.2.2.le))) hmap
  refine ⟨p, ?_, hfix, huniq, hder.trans_lt ?_⟩
  · simpa only [coefficientRadius, show (25/32 : ℝ)*(32/25)=1 by norm_num] using hp
  · exact DiscFixedPoint.contractionFactor_lt_one (by norm_num) (by norm_num)

/-- The fixed point belongs to the actual composed branch, with no auxiliary data. -/
def fixedPoint (k : ℕ) (a : Word (k+1)) : ℂ := (exists_word_fixedPoint k a).choose

theorem fixedPoint_spec (k : ℕ) (a : Word (k+1)) :
    fixedPoint k a ∈ closedBall 1 1 ∧ wordMap (k+1) a (fixedPoint k a) = fixedPoint k a ∧
      (∀ q ∈ ball 1 coefficientRadius, wordMap (k+1) a q = q → q = fixedPoint k a) ∧
      ‖deriv (wordMap (k+1) a) (fixedPoint k a)‖ < 1 :=
  (exists_word_fixedPoint k a).choose_spec

/-- Fixed-point contribution of one actual nonempty Gauss word. -/
def wordTrace (w : ℂ) (k : ℕ) (a : Word (k+1)) : ℂ :=
  wordWeight w (k+1) a (fixedPoint k a) /
    (1 - deriv (wordMap (k+1) a) (fixedPoint k a))

/-- The actual word's Cauchy diagonal has precisely its fixed-point trace. -/
theorem hasSum_word_diagonal {w : ℂ} (hw : 0 < w.re) (k : ℕ) (a : Word (k+1)) :
    HasSum (fun j => traceCoefficient j (wordOperator w hw (k+1) a (monomial j)))
      (wordTrace w k a) := by
  have hsub : closedBall (1 : ℂ) coefficientRadius ⊆ outer :=
    closedBall_subset_closedBall radii.2.2.le
  have hmap : MapsTo (wordMap (k+1) a) (closedBall 1 coefficientRadius)
      (closedBall 1 ((25/32 : ℝ) * coefficientRadius)) := by
    norm_num [coefficientRadius]
    exact (wordMap_inner k a).mono_left hsub
  have hp : fixedPoint k a ∈ ball 1 coefficientRadius :=
    closedBall_subset_ball (by norm_num [coefficientRadius]) (fixedPoint_spec k a).1
  have h := DiscCoefficients.hasSum_coeff_diag coefficientRadius_pos
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 25/32)
    (by norm_num : (25/32 : ℝ) < 1)
    ((wordMap_differentiable (k+1) a).mono hsub) hmap
    ((wordWeight_differentiable w (k+1) a).mono hsub) hp (fixedPoint_spec k a).2.1
  change HasSum _ (wordTrace w k a) at h
  simp only [DiscCoefficients.coeff, Complex.ofReal_one, one_pow, one_mul, div_one] at h
  have heq : (fun j => DiscCoefficients.cauchyCoeff 1 coefficientRadius j
      (fun z => wordWeight w (k+1) a z * (wordMap (k+1) a z - 1)^j)) =
      (fun j => traceCoefficient j (wordOperator w hw (k+1) a (monomial j))) := by
    funext j
    unfold DiscCoefficients.cauchyCoeff
    congr 1
    apply circleIntegral.integral_congr coefficientRadius_pos.le
    intro z hz
    dsimp only
    have hzD := hsub (sphere_subset_closedBall hz)
    rw [show plane (wordOperator w hw (k+1) a (monomial j)) z =
        (wordOperator w hw (k+1) a (monomial j)).1 ⟨z,hzD⟩ from plane_eq _ ⟨z,hzD⟩,
      wordOperator_apply]
    have hu : wordMap (k+1) a z ∈ outer :=
      wordMap_mapsTo (k+1) a (by norm_num) le_rfl hzD
    rw [plane_eq _ ⟨_,hu⟩]
    rfl
  rw [heq] at h
  exact h

/-- Split off the first digit without changing the countable alphabet. -/
def splitWord (k : ℕ) : Word (k+1) ≃ ℕ × Word k where
  toFun a := (a 0, Fin.tail a)
  invFun p := Fin.cons p.1 p.2
  left_inv a := by simp
  right_inv p := by simp

/-- Each fixed word length has a summable product majorant. -/
theorem summable_wordBound {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    Summable (wordBound w k) := by
  have hd : Summable (fun n : ℕ => powerBound w * ((n+1 : ℕ) : ℝ)^(-w.re)) :=
    ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-w.re)) 1).mpr
      (RHTower.Sieve.summable_nat_rpow_neg hw)).mul_left _
  induction k with
  | zero => exact (hasSum_fintype (wordBound w 0)).summable
  | succ k ih =>
      have hp := summable_mul_of_summable_norm hd.norm ih.norm
      have he := (splitWord k).summable_iff.mpr hp
      change Summable (fun a : Word (k+1) => wordBound w (k+1) a)
      simpa only [Function.comp_def, splitWord, Equiv.coe_fn_mk,
        wordBound, Fin.prod_univ_succ, Fin.tail] using he

/-- The norm of a word operator is bounded by its digit product. -/
theorem norm_wordOperator_le {w : ℂ} (hw : 0 < w.re) (k : ℕ) (a : Word k) :
    ‖wordOperator w hw k a‖ ≤ wordBound w k a := by
  induction k with
  | zero =>
      simp only [wordOperator, wordBound, Fin.prod_univ_zero]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro f
      simp only [ContinuousLinearMap.id_apply, one_mul, le_refl]
  | succ k ih =>
      apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
      have h := mul_le_mul (norm_branch_le hw (Nat.succ_pos (a 0))) (ih (Fin.tail a))
        (norm_nonneg _) (mul_nonneg (powerBound_pos w).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      simpa only [wordBound, Fin.prod_univ_succ, Fin.tail] using h

theorem summable_norm_wordOperator {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    Summable (fun a : Word k => ‖wordOperator w (zero_lt_one.trans hw) k a‖) :=
  (summable_wordBound hw k).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_wordOperator_le (zero_lt_one.trans hw) k)

/-- The countable word sum is exactly the actual operator power. -/
theorem hasSum_wordOperator {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    HasSum (wordOperator w (zero_lt_one.trans hw) k)
      ((regularized w (zero_lt_one.trans hw))^k) := by
  have hb : HasSum (fun n : ℕ => branch w (zero_lt_one.trans hw) (n+1) (Nat.succ_pos _))
      (regularized w (zero_lt_one.trans hw)) := by
    rw [regularized_eq_tsum_branch hw]
    exact (summable_norm_branch hw).of_norm.hasSum
  induction k with
  | zero =>
      rw [pow_zero]
      change HasSum _ (ContinuousLinearMap.id ℂ DiscSpace)
      simpa only [wordOperator, Fintype.sum_unique] using
        (hasSum_fintype (wordOperator w (zero_lt_one.trans hw) 0))
  | succ k ih =>
      have hp := summable_mul_of_summable_norm (summable_norm_branch hw)
        (summable_norm_wordOperator hw k)
      have h := (splitWord k).hasSum_iff.mpr (hb.mul ih hp)
      simpa only [Function.comp_def, splitWord, Equiv.coe_fn_mk,
        wordOperator, ContinuousLinearMap.mul_def, pow_succ'] using h

/-- Absolute convergence in both the word and Cauchy indices. -/
theorem summable_norm_wordDiagonal {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    Summable (fun p : ℕ × Word (k+1) =>
      ‖traceCoefficient p.1 (wordOperator w (zero_lt_one.trans hw) (k+1) p.2 (monomial p.1))‖) := by
  have hg : Summable (fun j : ℕ => coefficientRadius⁻¹^j) :=
    summable_geometric_of_lt_one (by norm_num [coefficientRadius])
      (by norm_num [coefficientRadius])
  have hp := summable_mul_of_summable_norm hg.norm (summable_wordBound hw (k+1)).norm
  exact hp.of_nonneg_of_le (fun _ => norm_nonneg _) fun p =>
    norm_word_diagonal_le (zero_lt_one.trans hw) k p.2 p.1

/-- All actual power diagonals equal the countable fixed-point word sums. -/
theorem power_diagonal_eq_wordTrace {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    (∑' j : ℕ, traceCoefficient j
      (((regularized w (zero_lt_one.trans hw))^(k+1)) (monomial j))) =
      ∑' a : Word (k+1), wordTrace w k a := by
  have he (j : ℕ) : traceCoefficient j
      (((regularized w (zero_lt_one.trans hw))^(k+1)) (monomial j)) =
      ∑' a : Word (k+1), traceCoefficient j
        (wordOperator w (zero_lt_one.trans hw) (k+1) a (monomial j)) :=
    ((traceCoefficient j).hasSum ((ContinuousLinearMap.apply ℂ DiscSpace (monomial j)).hasSum
      (hasSum_wordOperator hw (k+1)))).tsum_eq.symm
  let d : ℕ → Word (k+1) → ℂ := fun j a => traceCoefficient j
    (wordOperator w (zero_lt_one.trans hw) (k+1) a (monomial j))
  have hs : Summable (Function.uncurry d) := (summable_norm_wordDiagonal hw k).of_norm
  calc
    _ = ∑' j, ∑' a, d j a := tsum_congr he
    _ = ∑' a, ∑' j, d j a := hs.tsum_comm.symm
    _ = _ := tsum_congr fun a => (hasSum_word_diagonal (zero_lt_one.trans hw) k a).tsum_eq

/-- Powers of the Hilbert realization retain the original Banach factorization. -/
theorem hilbertPower_apply {w : ℂ} (hw : 0 < w.re) (k : ℕ) (x : SequenceSpace) :
    (hilbertOperator w hw ^ (k+1)) x =
      analysisMap ((regularized w hw ^ k) (synthesisMap w hw x)) := by
  induction k with
  | zero =>
      simp only [Nat.zero_add, pow_one, pow_zero]
      rfl
  | succ k ih =>
      rw [pow_succ' (hilbertOperator w hw) (k+1)]
      change hilbertOperator w hw ((hilbertOperator w hw ^ (k+1)) x) = _
      rw [ih]
      change analysisMap (synthesisMap w hw
        (analysisMap ((regularized w hw ^ k) (synthesisMap w hw x)))) = _
      have he (f : DiscSpace) : synthesisMap w hw (analysisMap f) = regularized w hw f :=
        congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T f) (synthesis_comp_analysis hw)
      rw [he, pow_succ' (regularized w hw) k]
      rfl

/-- Rescaling cancels in every power diagonal, not only in the first trace. -/
theorem hilbertPower_diagonal {w : ℂ} (hw : 0 < w.re) (k j : ℕ) :
    (hilbertOperator w hw ^ (k+1)) (lp.single 2 j (1 : ℂ)) j =
      traceCoefficient j ((regularized w hw ^ (k+1)) (monomial j)) := by
  rw [hilbertPower_apply hw k, analysis_coordinate]
  have hs : synthesisMap w hw (lp.single 2 j (1 : ℂ)) = vector w hw j := synthesis_mode hw j
  rw [hs, vector, map_smul]
  change (balanceRadius : ℂ)^j *
    traceCoefficient j (((balanceRadius : ℂ)^j)⁻¹ •
      ((regularized w hw ^ k) (regularized w hw (monomial j)))) = _
  rw [map_smul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr balanceRadius_pos.ne')), one_mul,
    pow_succ (regularized w hw) k]
  rfl

private theorem inner_lpBasis (j : ℕ) (x : SequenceSpace) :
    inner ℂ (HilbertSchmidt.lpBasis ℕ j) x = x j := by
  rw [HilbertSchmidt.lpBasis_apply, lp.inner_eq_tsum, tsum_eq_single j]
  · rw [lp.single_apply_self, RCLike.inner_apply]
    simp
  · intro i hi
    rw [lp.single_apply_ne _ _ _ hi, inner_zero_left]

/-- The original source Cauchy diagonal is the actual Hilbert power trace. -/
theorem opTrace_power_eq_diagonal {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    ContinuousLinearMap.opTrace (hilbertOperator w hw ^ (k+1)) =
      ∑' j, traceCoefficient j ((regularized w hw ^ (k+1)) (monomial j)) := by
  have hn : RHTower.DeningerIsNuclear (hilbertOperator w hw ^ (k+1)) := by
    rw [pow_succ]
    exact (nuclear_hilbertOperator hw).compL (hilbertOperator w hw ^ k)
  obtain ⟨A,B,hA,hB,he⟩ := hn.memSchattenClass_one.one_isTraceClass
  have ht : ContinuousLinearMap.opTrace (hilbertOperator w hw ^ (k+1)) =
      ∑' j, inner ℂ (HilbertSchmidt.lpBasis ℕ j)
        ((hilbertOperator w hw ^ (k+1)) (HilbertSchmidt.lpBasis ℕ j)) := by
    rw [he]
    exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB (HilbertSchmidt.lpBasis ℕ)
  rw [ht]
  apply tsum_congr
  intro j
  rw [inner_lpBasis, HilbertSchmidt.lpBasis_apply, hilbertPower_diagonal]

/-- Every actual Mayer trace power is the countable Gauss-word fixed-point sum. -/
theorem opTrace_power_eq_wordTrace {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    ContinuousLinearMap.opTrace (hilbertOperator w (zero_lt_one.trans hw) ^ (k+1)) =
      ∑' a : Word (k+1), wordTrace w k a := by
  rw [opTrace_power_eq_diagonal, power_diagonal_eq_wordTrace hw]

/-- The composed principal-power weights multiply in their exponent. -/
theorem wordWeight_add (u v : ℂ) (k : ℕ) (a : Word k) {z : ℂ} (hz : z ∈ outer) :
    wordWeight (u+v) k a z = wordWeight u k a z * wordWeight v k a z := by
  induction k generalizing z with
  | zero => simp only [wordWeight, mul_one]
  | succ k ih =>
      have hz' : ((((a 0+1 : ℕ) : ℂ) + z)⁻¹) ∈ outer :=
        closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner (Nat.succ_pos _) hz)
      rw [wordWeight, neg_add, Complex.cpow_add _ _ (digit_ne_zero (a 0) hz),
        ih (Fin.tail a) hz', wordWeight, wordWeight]
      ring

/-- A word's derivative is its exponent-two weight with the orientation sign. -/
theorem hasDerivAt_wordMap (k : ℕ) (a : Word k) {z : ℂ} (hz : z ∈ outer) :
    HasDerivAt (wordMap k a) ((-1 : ℂ)^k * wordWeight 2 k a z) z := by
  induction k generalizing z with
  | zero =>
      simp only [wordMap, wordWeight, pow_zero, mul_one]
      exact hasDerivAt_id z
  | succ k ih =>
      have hz' : ((((a 0+1 : ℕ) : ℂ) + z)⁻¹) ∈ outer :=
        closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner (Nat.succ_pos _) hz)
      have h := (ih (Fin.tail a) hz').comp z
        (((hasDerivAt_id z).const_add _).inv (digit_ne_zero (a 0) hz))
      have he : (-1 : ℂ)^(k+1) * wordWeight 2 (k+1) a z =
          ((-1 : ℂ)^k * wordWeight 2 k (Fin.tail a) (((a 0+1 : ℕ) : ℂ)+z)⁻¹) *
            (-1 / ((((a 0+1 : ℕ) : ℂ)+z)^2)) := by
        rw [wordWeight, pow_succ, Complex.cpow_neg, Complex.cpow_two]
        ring
      rw [he]
      exact h

theorem deriv_wordMap (k : ℕ) (a : Word k) {z : ℂ} (hz : z ∈ outer) :
    deriv (wordMap k a) z = (-1 : ℂ)^k * wordWeight 2 k a z :=
  (hasDerivAt_wordMap k a hz).deriv

/-- Shifting the exponent by two cancels the fixed-point denominator exactly. -/
theorem wordTrace_shift (w : ℂ) (k : ℕ) (a : Word (k+1)) :
    wordTrace w k a - (-1 : ℂ)^(k+1) * wordTrace (w+2) k a =
      wordWeight w (k+1) a (fixedPoint k a) := by
  have hp : fixedPoint k a ∈ outer := closedBall_subset_closedBall
    (by norm_num : (1 : ℝ) ≤ 3/2) (fixedPoint_spec k a).1
  have hd := deriv_wordMap (k+1) a hp
  have hne : 1 - deriv (wordMap (k+1) a) (fixedPoint k a) ≠ 0 := by
    intro he
    have hder := (fixedPoint_spec k a).2.2.2
    rw [← sub_eq_zero.mp he, norm_one] at hder
    exact lt_irrefl _ hder
  rw [wordTrace, wordTrace, wordWeight_add w 2 (k+1) a hp]
  simp only [div_eq_mul_inv]
  calc
    _ = wordWeight w (k+1) a (fixedPoint k a) *
        ((1 - deriv (wordMap (k+1) a) (fixedPoint k a)) *
          (1 - deriv (wordMap (k+1) a) (fixedPoint k a))⁻¹) := by rw [hd]; ring
    _ = _ := by rw [mul_inv_cancel₀ hne, mul_one]

/-- The fixed-point traces are absolutely summable over every word length. -/
theorem summable_wordTrace {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    Summable (wordTrace w k) := by
  let d : ℕ → Word (k+1) → ℂ := fun j a => traceCoefficient j
    (wordOperator w (zero_lt_one.trans hw) (k+1) a (monomial j))
  have hs : Summable (Function.uncurry d) := (summable_norm_wordDiagonal hw k).of_norm
  have hswap : Summable (fun p : Word (k+1) × ℕ => d p.2 p.1) :=
    (Equiv.prodComm (Word (k+1)) ℕ).summable_iff.mpr hs
  exact hswap.prod.congr fun a => (hasSum_word_diagonal (zero_lt_one.trans hw) k a).tsum_eq

/-- The denominator-free periodic weights are absolutely summable. -/
theorem summable_fixedPoint_weight {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    Summable (fun a : Word (k+1) => wordWeight w (k+1) a (fixedPoint k a)) := by
  apply Summable.of_norm_bounded (summable_wordBound hw (k+1))
  intro a
  exact norm_wordWeight_le (zero_lt_one.trans hw) (k+1) a
    (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) (fixedPoint_spec k a).1)

/-- Exact parity-sensitive shift law for the actual source power traces. -/
theorem opTrace_power_shift {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    ContinuousLinearMap.opTrace (hilbertOperator w (zero_lt_one.trans hw) ^ (k+1)) -
      (-1 : ℂ)^(k+1) * ContinuousLinearMap.opTrace
        (hilbertOperator (w+2) (by simpa using (show (0 : ℝ) < w.re+2 by linarith only [hw])) ^ (k+1)) =
      ∑' a : Word (k+1), wordWeight w (k+1) a (fixedPoint k a) := by
  have hw2 : 1 < (w+2).re := by simpa using (show (1 : ℝ) < w.re+2 by linarith only [hw])
  rw [opTrace_power_eq_wordTrace hw, opTrace_power_eq_wordTrace hw2, ← tsum_mul_left,
    ← (summable_wordTrace hw k).tsum_sub ((summable_wordTrace hw2 k).mul_left ((-1 : ℂ)^(k+1)))]
  exact tsum_congr fun a => wordTrace_shift w k a

/-- The integral matrix of the branch with digit `n+1`. -/
def digitMatrix (n : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![0,1;1,n+1]

/-- Ordered matrix product of the actual composed inverse branches. -/
def wordMatrix : (k : ℕ) → Word k → Matrix (Fin 2) (Fin 2) ℕ
  | 0, _ => 1
  | k+1, a => wordMatrix k (Fin.tail a) * digitMatrix (a 0)

theorem wordMatrix_col_zero (k : ℕ) (a : Word (k+1)) (i : Fin 2) :
    wordMatrix (k+1) a i 0 = wordMatrix k (Fin.tail a) i 1 := by
  simp [wordMatrix, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem wordMatrix_col_one (k : ℕ) (a : Word (k+1)) (i : Fin 2) :
    wordMatrix (k+1) a i 1 = wordMatrix k (Fin.tail a) i 0 +
      wordMatrix k (Fin.tail a) i 1 * (a 0+1) := by
  simp [wordMatrix, digitMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix determinant records the orientation parity of the word. -/
theorem wordMatrix_unimodular (k : ℕ) (a : Word k) :
    (wordMatrix k a 0 0 : ℤ) * wordMatrix k a 1 1 -
      (wordMatrix k a 0 1 : ℤ) * wordMatrix k a 1 0 = (-1 : ℤ)^k := by
  induction k with
  | zero => norm_num [wordMatrix, Matrix.one_apply]
  | succ k ih =>
      simp only [wordMatrix_col_zero, wordMatrix_col_one, Nat.cast_add, Nat.cast_mul]
      calc
        _ = -((wordMatrix k (Fin.tail a) 0 0 : ℤ) * wordMatrix k (Fin.tail a) 1 1 -
          (wordMatrix k (Fin.tail a) 0 1 : ℤ) * wordMatrix k (Fin.tail a) 1 0) := by ring
        _ = _ := by rw [ih, pow_succ]; ring

/-- The denominator row is positive and dominates its first entry. -/
theorem wordMatrix_denominator_row (k : ℕ) (a : Word k) :
    wordMatrix k a 1 0 ≤ wordMatrix k a 1 1 ∧ 1 ≤ wordMatrix k a 1 1 := by
  induction k with
  | zero => norm_num [wordMatrix, Matrix.one_apply]
  | succ k ih =>
      rw [wordMatrix_col_zero, wordMatrix_col_one]
      have h := ih (Fin.tail a)
      have hm : wordMatrix k (Fin.tail a) 1 1 ≤
          wordMatrix k (Fin.tail a) 1 1 * (a 0+1) :=
        Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega

theorem wordMatrix_lowerLeft_pos (k : ℕ) (a : Word (k+1)) :
    0 < wordMatrix (k+1) a 1 0 := by
  rw [wordMatrix_col_zero]
  exact (wordMatrix_denominator_row k (Fin.tail a)).2

/-- Numerator of the actual word's fractional-linear map. -/
def wordNumerator (k : ℕ) (a : Word k) (z : ℂ) : ℂ :=
  (wordMatrix k a 0 0 : ℂ) * z + wordMatrix k a 0 1

/-- Denominator of the actual word's fractional-linear map. -/
def wordDenominator (k : ℕ) (a : Word k) (z : ℂ) : ℂ :=
  (wordMatrix k a 1 0 : ℂ) * z + wordMatrix k a 1 1

/-- No denominator of any actual word vanishes on the source disc. -/
theorem wordDenominator_ne_zero (k : ℕ) (a : Word k) {z : ℂ} (hz : z ∈ outer) :
    wordDenominator k a z ≠ 0 := by
  have hd : ‖z-1‖ ≤ (3/2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hr := (neg_le_abs (z-1).re).trans ((Complex.abs_re_le_norm _).trans hd)
  simp only [Complex.sub_re, Complex.one_re] at hr
  have hC : (0 : ℝ) ≤ wordMatrix k a 1 0 := Nat.cast_nonneg _
  have hCD : (wordMatrix k a 1 0 : ℝ) ≤ wordMatrix k a 1 1 :=
    by exact_mod_cast (wordMatrix_denominator_row k a).1
  have hD : (1 : ℝ) ≤ wordMatrix k a 1 1 :=
    by exact_mod_cast (wordMatrix_denominator_row k a).2
  have hm := mul_nonneg hC (show 0 ≤ z.re + 1/2 by linarith only [hr])
  have hpos : 0 < (wordDenominator k a z).re := by
    simp only [wordDenominator, add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    nlinarith only [hm, hCD, hD]
  intro he
  rw [he, zero_re] at hpos
  exact lt_irrefl _ hpos

private theorem fraction_at_inverse (A B C D u : ℂ) (hu : u ≠ 0) :
    (A*u⁻¹+B)/(C*u⁻¹+D) = (A+B*u)/(C+D*u) := by
  have hA : A*u⁻¹+B = (A+B*u)/u := by field_simp [hu]
  have hC : C*u⁻¹+D = (C+D*u)/u := by field_simp [hu]
  rw [hA, hC, div_div_div_cancel_right₀ hu]

/-- Matrix composition recovers each literal inverse-branch word. -/
theorem wordMap_eq_fraction (k : ℕ) (a : Word k) {z : ℂ} (hz : z ∈ outer) :
    wordMap k a z = wordNumerator k a z / wordDenominator k a z := by
  induction k generalizing z with
  | zero => simp [wordMap, wordNumerator, wordDenominator, wordMatrix]
  | succ k ih =>
      have hz' : ((((a 0+1 : ℕ) : ℂ) + z)⁻¹) ∈ outer :=
        closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2)
          (inverse_branch_inner (Nat.succ_pos _) hz)
      rw [wordMap, ih (Fin.tail a) hz']
      change ((wordMatrix k (Fin.tail a) 0 0 : ℂ) * ((((a 0+1 : ℕ) : ℂ)+z)⁻¹) +
          wordMatrix k (Fin.tail a) 0 1) /
        ((wordMatrix k (Fin.tail a) 1 0 : ℂ) * ((((a 0+1 : ℕ) : ℂ)+z)⁻¹) +
          wordMatrix k (Fin.tail a) 1 1) = _
      rw [fraction_at_inverse _ _ _ _ _ (digit_ne_zero (a 0) hz)]
      simp only [wordNumerator, wordDenominator, wordMatrix_col_zero, wordMatrix_col_one,
        Nat.cast_add, Nat.cast_mul]
      congr 1 <;> ring

open scoped ComplexConjugate

/-- Real restriction of the literal Gauss word. -/
def realWordMap : (k : ℕ) → Word k → ℝ → ℝ
  | 0, _, x => x
  | k+1, a, x => realWordMap k (Fin.tail a) (((a 0+1 : ℕ) : ℝ) + x)⁻¹

theorem wordMap_ofReal (k : ℕ) (a : Word k) (x : ℝ) :
    wordMap k a (x : ℂ) = (realWordMap k a x : ℂ) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [wordMap, realWordMap, ← ih (Fin.tail a)]
      congr 1
      push_cast
      rfl

theorem wordMap_conj (k : ℕ) (a : Word k) (z : ℂ) :
    wordMap k a (conj z) = conj (wordMap k a z) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp [wordMap, ← ih (Fin.tail a)]

private theorem real_digit_pos (n : ℕ) {x : ℝ} (hx : -1 < x) :
    0 < ((n+1 : ℕ) : ℝ) + x := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  linarith only [hn,hx]

theorem realWordMap_pos (k : ℕ) (a : Word (k+1)) {x : ℝ} (hx : -1 < x) :
    0 < realWordMap (k+1) a x := by
  induction k generalizing x with
  | zero => exact inv_pos.mpr (real_digit_pos (a 0) hx)
  | succ k ih =>
      apply ih (Fin.tail a)
      exact lt_trans (by norm_num : (-1 : ℝ) < 0) (inv_pos.mpr (real_digit_pos (a 0) hx))

theorem realWordMap_lt_one (k : ℕ) (a : Word (k+1)) {x : ℝ} (hx : 0 < x) :
    realWordMap (k+1) a x < 1 := by
  induction k generalizing x with
  | zero =>
      change (((a 0+1 : ℕ) : ℝ) + x)⁻¹ < 1
      apply (inv_lt_one₀ (real_digit_pos (a 0) (by linarith only [hx]))).mpr
      have hn : (0 : ℝ) ≤ a 0 := Nat.cast_nonneg _
      push_cast
      linarith only [hn,hx]
  | succ k ih =>
      exact ih (Fin.tail a) (inv_pos.mpr (real_digit_pos (a 0) (by linarith only [hx])))

/-- Uniqueness and real branch coefficients force the fixed point to be real. -/
theorem fixedPoint_eq_real (k : ℕ) (a : Word (k+1)) :
    fixedPoint k a = ((fixedPoint k a).re : ℂ) := by
  have hp := (fixedPoint_spec k a).1
  have hnorm : ‖fixedPoint k a-1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hp
  have hc : conj (fixedPoint k a) ∈ ball 1 coefficientRadius := by
    rw [mem_ball, dist_eq_norm,
      show conj (fixedPoint k a)-1 = conj (fixedPoint k a-1) by simp, Complex.norm_conj]
    exact hnorm.trans_lt (by norm_num [coefficientRadius])
  have hf : wordMap (k+1) a (conj (fixedPoint k a)) = conj (fixedPoint k a) := by
    rw [wordMap_conj, (fixedPoint_spec k a).2.1]
  have he := (fixedPoint_spec k a).2.2.1 _ hc hf
  have him := congrArg Complex.im he
  simp only [conj_im] at him
  apply Complex.ext
  · rfl
  · simp only [ofReal_im]
    linarith only [him]

/-- The genuine periodic point lies strictly between zero and one. -/
theorem fixedPoint_real_interval (k : ℕ) (a : Word (k+1)) :
    0 < (fixedPoint k a).re ∧ (fixedPoint k a).re < 1 := by
  have hn : ‖fixedPoint k a-1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using (fixedPoint_spec k a).1
  have hr := (neg_le_abs (fixedPoint k a-1).re).trans
    ((Complex.abs_re_le_norm _).trans hn)
  simp only [sub_re, one_re] at hr
  have hx : -1 < (fixedPoint k a).re := by linarith only [hr]
  have he : realWordMap (k+1) a (fixedPoint k a).re = (fixedPoint k a).re := by
    have h := (fixedPoint_spec k a).2.1
    rw [fixedPoint_eq_real k a, wordMap_ofReal] at h
    exact_mod_cast h
  have hp : 0 < (fixedPoint k a).re := by rw [← he]; exact realWordMap_pos k a hx
  refine ⟨hp, ?_⟩
  rw [← he]
  exact realWordMap_lt_one k a hp

/-- Expanding positive multiplier of the actual integral word matrix. -/
def wordMultiplier (k : ℕ) (a : Word (k+1)) : ℝ :=
  (wordMatrix (k+1) a 1 0 : ℝ) * (fixedPoint k a).re + wordMatrix (k+1) a 1 1

theorem one_lt_wordMultiplier (k : ℕ) (a : Word (k+1)) :
    1 < wordMultiplier k a := by
  have hC : (0 : ℝ) < wordMatrix (k+1) a 1 0 := by exact_mod_cast wordMatrix_lowerLeft_pos k a
  have hD : (1 : ℝ) ≤ wordMatrix (k+1) a 1 1 :=
    by exact_mod_cast (wordMatrix_denominator_row (k+1) a).2
  have hm := mul_pos hC (fixedPoint_real_interval k a).1
  unfold wordMultiplier
  linarith only [hD,hm]

/-- Real denominator of an integral word matrix. -/
def realDenominator (k : ℕ) (a : Word k) (x : ℝ) : ℝ :=
  (wordMatrix k a 1 0 : ℝ) * x + wordMatrix k a 1 1

theorem realDenominator_pos (k : ℕ) (a : Word k) {x : ℝ} (hx : 0 ≤ x) :
    0 < realDenominator k a x := by
  have hD : (1 : ℝ) ≤ wordMatrix k a 1 1 :=
    by exact_mod_cast (wordMatrix_denominator_row k a).2
  exact add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg _) hx)
    (zero_lt_one.trans_le hD)

theorem wordDenominator_ofReal (k : ℕ) (a : Word k) (x : ℝ) :
    wordDenominator k a (x : ℂ) = (realDenominator k a x : ℂ) := by
  simp only [wordDenominator, realDenominator, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_natCast]

/-- Denominator products telescope under the actual branch composition. -/
theorem realDenominator_step (k : ℕ) (a : Word (k+1)) {x : ℝ} (hx : -1 < x) :
    (((a 0+1 : ℕ) : ℝ)+x) *
      realDenominator k (Fin.tail a) ((((a 0+1 : ℕ) : ℝ)+x)⁻¹) =
      realDenominator (k+1) a x := by
  have hu := (real_digit_pos (a 0) hx).ne'
  calc
    _ = (wordMatrix k (Fin.tail a) 1 0 : ℝ) +
        (wordMatrix k (Fin.tail a) 1 1 : ℝ) * (((a 0+1 : ℕ) : ℝ)+x) := by
      change (((a 0+1 : ℕ) : ℝ)+x) *
        ((wordMatrix k (Fin.tail a) 1 0 : ℝ) * (((a 0+1 : ℕ) : ℝ)+x)⁻¹ +
          wordMatrix k (Fin.tail a) 1 1) = _
      calc
        _ = (wordMatrix k (Fin.tail a) 1 0 : ℝ) *
            ((((a 0+1 : ℕ) : ℝ)+x) * (((a 0+1 : ℕ) : ℝ)+x)⁻¹) +
          (wordMatrix k (Fin.tail a) 1 1 : ℝ) * (((a 0+1 : ℕ) : ℝ)+x) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hu, mul_one]
    _ = _ := by
      simp only [realDenominator, wordMatrix_col_zero, wordMatrix_col_one,
        Nat.cast_add, Nat.cast_mul]
      ring

/-- On the positive real axis the orbit weight is the matrix denominator power. -/
theorem wordWeight_real (w : ℂ) (k : ℕ) (a : Word k) {x : ℝ} (hx : 0 ≤ x) :
    wordWeight w k a (x : ℂ) = (realDenominator k a x : ℂ)^(-w) := by
  induction k generalizing x with
  | zero => simp [wordWeight, realDenominator, wordMatrix]
  | succ k ih =>
      let u : ℝ := ((a 0+1 : ℕ) : ℝ)+x
      have hu : 0 < u := real_digit_pos (a 0) (by linarith only [hx])
      have he : (((a 0+1 : ℕ) : ℂ)+(x : ℂ)) = (u : ℂ) := by
        simp only [u, Complex.ofReal_add, Complex.ofReal_natCast]
      rw [wordWeight, he, ← Complex.ofReal_inv, ih (Fin.tail a) (inv_nonneg.mpr hu.le),
        ← Complex.mul_cpow_ofReal_nonneg hu.le
          (realDenominator_pos k (Fin.tail a) (inv_nonneg.mpr hu.le)).le,
        ← Complex.ofReal_mul]
      congr 1
      exact_mod_cast realDenominator_step k a (show -1 < x by linarith only [hx])

/-- The fixed-point weight is the actual expanding multiplier to power `-w`. -/
theorem fixedPoint_weight_eq (w : ℂ) (k : ℕ) (a : Word (k+1)) :
    wordWeight w (k+1) a (fixedPoint k a) = (wordMultiplier k a : ℂ)^(-w) := by
  rw [fixedPoint_eq_real k a,
    wordWeight_real w (k+1) a (fixedPoint_real_interval k a).1.le]
  rfl

/-- Derivative multiplier, including the orientation sign of odd words. -/
theorem fixedPoint_deriv_eq (k : ℕ) (a : Word (k+1)) :
    deriv (wordMap (k+1) a) (fixedPoint k a) =
      (-1 : ℂ)^(k+1) / (wordMultiplier k a : ℂ)^2 := by
  rw [deriv_wordMap (k+1) a
    (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3/2) (fixedPoint_spec k a).1),
    fixedPoint_weight_eq, Complex.cpow_neg, Complex.cpow_two]
  rfl

/-- Integral quadratic equation of the expanding word multiplier. -/
theorem wordMultiplier_quadratic (k : ℕ) (a : Word (k+1)) :
    wordMultiplier k a ^ 2 -
      ((wordMatrix (k+1) a 0 0 + wordMatrix (k+1) a 1 1 : ℕ) : ℝ) *
        wordMultiplier k a + (-1 : ℝ)^(k+1) = 0 := by
  have hp : fixedPoint k a ∈ outer := closedBall_subset_closedBall
    (by norm_num : (1 : ℝ) ≤ 3/2) (fixedPoint_spec k a).1
  have he : fixedPoint k a = wordNumerator (k+1) a (fixedPoint k a) /
      wordDenominator (k+1) a (fixedPoint k a) := by
    exact (fixedPoint_spec k a).2.1.symm.trans (wordMap_eq_fraction (k+1) a hp)
  have hf := (eq_div_iff (wordDenominator_ne_zero (k+1) a hp)).mp he
  rw [fixedPoint_eq_real k a] at hf
  simp only [wordNumerator, wordDenominator] at hf
  have hfr : (fixedPoint k a).re *
      ((wordMatrix (k+1) a 1 0 : ℝ) * (fixedPoint k a).re + wordMatrix (k+1) a 1 1) =
      (wordMatrix (k+1) a 0 0 : ℝ) * (fixedPoint k a).re + wordMatrix (k+1) a 0 1 :=
    by exact_mod_cast hf
  have hd : (wordMatrix (k+1) a 0 0 : ℝ) * wordMatrix (k+1) a 1 1 -
      (wordMatrix (k+1) a 0 1 : ℝ) * wordMatrix (k+1) a 1 0 = (-1 : ℝ)^(k+1) :=
    by exact_mod_cast wordMatrix_unimodular (k+1) a
  simp only [wordMultiplier, Nat.cast_add]
  linear_combination (wordMatrix (k+1) a 1 0 : ℝ) * hfr - hd

/-- Explicit arithmetic contribution of each Gauss word to the trace. -/
theorem wordTrace_eq_multiplier (w : ℂ) (k : ℕ) (a : Word (k+1)) :
    wordTrace w k a = (wordMultiplier k a : ℂ)^(-w) /
      (1 - (-1 : ℂ)^(k+1) / (wordMultiplier k a : ℂ)^2) := by
  rw [wordTrace, fixedPoint_weight_eq, fixedPoint_deriv_eq]

/-- The actual source trace powers, expressed entirely in integral word multipliers. -/
theorem opTrace_power_eq_multipliers {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    ContinuousLinearMap.opTrace (hilbertOperator w (zero_lt_one.trans hw) ^ (k+1)) =
      ∑' a : Word (k+1), (wordMultiplier k a : ℂ)^(-w) /
        (1 - (-1 : ℂ)^(k+1) / (wordMultiplier k a : ℂ)^2) := by
  rw [opTrace_power_eq_wordTrace hw]
  exact tsum_congr fun a => wordTrace_eq_multiplier w k a

/-- The parity-shift difference of source traces is the pure multiplier sum. -/
theorem opTrace_power_shift_multipliers {w : ℂ} (hw : 1 < w.re) (k : ℕ) :
    ContinuousLinearMap.opTrace (hilbertOperator w (zero_lt_one.trans hw) ^ (k+1)) -
      (-1 : ℂ)^(k+1) * ContinuousLinearMap.opTrace
        (hilbertOperator (w+2) (by simpa using (show (0 : ℝ) < w.re+2 by linarith only [hw])) ^ (k+1)) =
      ∑' a : Word (k+1), (wordMultiplier k a : ℂ)^(-w) := by
  rw [opTrace_power_shift hw]
  exact tsum_congr fun a => fixedPoint_weight_eq w k a

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords

#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.hasSum_wordOperator
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.opTrace_power_eq_wordTrace
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.wordTrace_shift
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.opTrace_power_shift
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.wordMatrix_unimodular
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.wordMap_eq_fraction
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.one_lt_wordMultiplier
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.wordMultiplier_quadratic
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.opTrace_power_eq_multipliers
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.opTrace_power_shift_multipliers
#print axioms GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords.summable_fixedPoint_weight
