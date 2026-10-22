import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaCommutatorConvolution

/-!
# The Gamma cutoff commutator has an exponentially localized block matrix

Cutting the convolution bound into unit blocks turns it into the estimate the flat-flux Volterra
argument consumes:

`‖[R,χ]F(L)‖ ≤ 4Λe · Σ_{m ∈ ℤ} e^{-|n-m|} ‖F‖_{L²([m,m+1))}`,   `L ∈ [n, n+1]`.

Two elementary facts do the work.  On a pair of unit blocks the exponential kernel is almost
constant — `|L−t| ≥ |n−m| − 1` — so it comes out of the block integral at the cost of one factor
`e`.  And on a block of length one, Cauchy–Schwarz turns the `L¹` mass into the `L²` mass with no
constant at all.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {χ : ℝ → ℝ} {Λ : ℝ} {F : ℝ → X}

/-! ## Unit blocks -/

/-- The squared `L²` mass of a profile on the unit block `[m, m+1)`. -/
def blockNormSq (F : ℝ → X) (m : ℤ) : ℝ≥0∞ := ∫⁻ t in Ico (m : ℝ) (m + 1), ‖F t‖ₑ ^ 2

/-- The `L²` norm of a profile on the unit block `[m, m+1)`. -/
def blockNorm (F : ℝ → X) (m : ℤ) : ℝ≥0∞ := blockNormSq F m ^ ((1 : ℝ) / 2)

omit [NormedSpace ℝ X] in
/-- **Cauchy–Schwarz on a unit block.**  On an interval of length one the `L¹` mass is at most the
`L²` mass. -/
theorem lintegral_block_le_blockNorm (hFm : Measurable fun x => ‖F x‖ₑ) (m : ℤ) :
    (∫⁻ t in Ico (m : ℝ) (m + 1), ‖F t‖ₑ) ≤ blockNorm F m := by
  have hvol : (volume.restrict (Ico (m : ℝ) (m + 1))) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    norm_num
  have hcs := lintegral_weighted_sq_le (volume.restrict (Ico (m : ℝ) (m + 1)))
    (measurable_const (a := (1 : ℝ≥0∞))) hFm
  simp only [one_mul, lintegral_const, Measure.restrict_apply_univ] at hcs
  rw [Real.volume_Ico] at hcs
  have hone : ENNReal.ofReal ((m : ℝ) + 1 - m) = 1 := by
    norm_num
  rw [hone, one_mul] at hcs
  have hsq : (∫⁻ t in Ico (m : ℝ) (m + 1), ‖F t‖ₑ) ^ 2 ≤ blockNormSq F m := hcs
  have hrewrite : (∫⁻ t in Ico (m : ℝ) (m + 1), ‖F t‖ₑ)
      = (((∫⁻ t in Ico (m : ℝ) (m + 1), ‖F t‖ₑ) ^ 2) ^ ((1 : ℝ) / 2)) := by
    rw [← ENNReal.rpow_natCast (∫⁻ t in Ico (m : ℝ) (m + 1), ‖F t‖ₑ) 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hrewrite, blockNorm]
  exact ENNReal.rpow_le_rpow hsq (by norm_num)

/-- **The kernel is almost constant on a pair of unit blocks.** -/
theorem gammaCommKernel_block_le (hΛ : 0 ≤ Λ) {n m : ℤ} {L t : ℝ}
    (hL : L ∈ Icc (n : ℝ) ((n : ℝ) + 1)) (ht : t ∈ Ico (m : ℝ) ((m : ℝ) + 1)) :
    gammaCommKernel Λ (L - t)
      ≤ ENNReal.ofReal (4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|)) := by
  have hgap : |(n : ℝ) - m| ≤ |L - t| + 1 := by
    have heq : (n : ℝ) - m = (L - t) - ((L - (n : ℝ)) - (t - (m : ℝ))) := by ring
    have hshift : |(L - (n : ℝ)) - (t - (m : ℝ))| ≤ 1 := by
      rw [abs_le]
      constructor
      · linarith [hL.1, hL.2, ht.1, ht.2]
      · linarith [hL.1, hL.2, ht.1, ht.2]
    calc |(n : ℝ) - m| = |(L - t) - ((L - (n : ℝ)) - (t - (m : ℝ)))| := by rw [heq]
      _ ≤ |L - t| + |(L - (n : ℝ)) - (t - (m : ℝ))| := abs_sub _ _
      _ ≤ |L - t| + 1 := by linarith
  have hexp : Real.exp (-|L - t|) ≤ Real.exp 1 * Real.exp (-|(n : ℝ) - m|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [gammaCommKernel]
  refine ENNReal.ofReal_le_ofReal ?_
  have h4 : (0 : ℝ) ≤ 4 * Λ := by linarith
  calc 4 * Λ * Real.exp (-|L - t|)
      ≤ 4 * Λ * (Real.exp 1 * Real.exp (-|(n : ℝ) - m|)) :=
        mul_le_mul_of_nonneg_left hexp h4
    _ = 4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|) := by ring

/-- The unit blocks tile the line. -/
theorem pairwise_disjoint_unitBlocks :
    Pairwise (Function.onFun Disjoint (fun m : ℤ => Ico (m : ℝ) ((m : ℝ) + 1))) := by
  intro i j hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [Set.mem_Ico] at hx hx'
  have h1 : (i : ℝ) < (j : ℝ) + 1 := lt_of_le_of_lt hx.1 hx'.2
  have h2 : (j : ℝ) < (i : ℝ) + 1 := lt_of_le_of_lt hx'.1 hx.2
  have h1' : i < j + 1 := by exact_mod_cast h1
  have h2' : j < i + 1 := by exact_mod_cast h2
  exact hij (by omega)

/-- **`(7)`: the exponentially localized block estimate.**  On the unit block `[n, n+1]` the Gamma
cutoff commutator is bounded by the exponential block matrix applied to the block norms of its
argument. -/
theorem enorm_gammaWallCommutator_le_blockSum
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hΛ : 0 ≤ Λ) (hFm : Measurable fun x => ‖F x‖ₑ)
    {n : ℤ} {L : ℝ} (hL : L ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    ‖gammaWallCommutator χ F L‖ₑ
      ≤ ∑' m : ℤ, ENNReal.ofReal (4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|))
          * blockNorm F m := by
  refine (enorm_gammaWallCommutator_le_conv hlip hzero hone hFm L).trans ?_
  have hsub : (∫⁻ y, gammaCommKernel Λ y * ‖F (L - y)‖ₑ)
      = ∫⁻ t, gammaCommKernel Λ (L - t) * ‖F t‖ₑ := by
    have h := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
      (fun t : ℝ => gammaCommKernel Λ (L - t) * ‖F t‖ₑ) L
    simpa using h
  rw [hsub]
  have hcover : (⋃ m : ℤ, Ico (m : ℝ) ((m : ℝ) + 1)) = univ := iUnion_Ico_intCast ℝ
  have hdecomp : (∫⁻ t, gammaCommKernel Λ (L - t) * ‖F t‖ₑ)
      = ∑' m : ℤ, ∫⁻ t in Ico (m : ℝ) ((m : ℝ) + 1), gammaCommKernel Λ (L - t) * ‖F t‖ₑ := by
    have h := lintegral_iUnion (μ := (volume : Measure ℝ))
      (fun m : ℤ => measurableSet_Ico) pairwise_disjoint_unitBlocks
      (fun t => gammaCommKernel Λ (L - t) * ‖F t‖ₑ)
    rw [hcover, Measure.restrict_univ] at h
    exact h
  rw [hdecomp]
  refine ENNReal.tsum_le_tsum fun m => ?_
  calc (∫⁻ t in Ico (m : ℝ) ((m : ℝ) + 1), gammaCommKernel Λ (L - t) * ‖F t‖ₑ)
      ≤ ∫⁻ t in Ico (m : ℝ) ((m : ℝ) + 1),
          ENNReal.ofReal (4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|)) * ‖F t‖ₑ :=
        setLIntegral_mono' measurableSet_Ico fun t ht =>
          mul_le_mul' (gammaCommKernel_block_le hΛ hL ht) le_rfl
    _ = ENNReal.ofReal (4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|))
          * ∫⁻ t in Ico (m : ℝ) ((m : ℝ) + 1), ‖F t‖ₑ := by
        rw [lintegral_const_mul _ hFm]
    _ ≤ ENNReal.ofReal (4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|)) * blockNorm F m :=
        mul_le_mul' le_rfl (lintegral_block_le_blockNorm hFm m)

end GaloisForLFunctions.RHTower
