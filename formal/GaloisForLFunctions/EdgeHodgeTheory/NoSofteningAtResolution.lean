import GaloisForLFunctions.EdgeHodgeTheory.TheHorizonFlowAtFixedWidth
import GaloisForLFunctions.HTGeometry.TensorPolarizationAmplification
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheKunnethSquareOfWeilsKernelIsRH

/-!
# No softening at finite resolution

The Künneth square of a resolution family is the family of Kronecker squares of its Gram matrices.
At every resolution its Hodge defect is fixed by Sylvester inertia:
`n₋(G ⊗ G) = 2 n₊(G) n₋(G)` (`hermNegIndex_kronecker_self`).

* **The Künneth defect vanishes iff the defect vanishes or there is no positive square**
  (`hermNegIndex_kronecker_self_eq_zero_iff`).
* **The positive squares of the integer spline atoms** (`iSup_hermPosIndex_horizonGram_cubicSpline`):
  along the horizon flow they reach the positive index `κ₊(K_ζ)`, as the negative squares reach
  `κ(K_ζ)` (HKT).
* **The Künneth square is RH at every resolution** (`riemannHypothesis_iff_kunneth_horizon`): RH
  holds iff at every horizon the Kronecker square of the integer spline atoms has no negative
  square. Without RH both a negative and a positive square appear at a finite horizon, so the
  Künneth defect is at least `2` from then on (`eventually_two_le_kunneth_of_not_rh`).

Tensor squares do not soften the sign at any resolution: the edge of the Künneth family is the
edge of the family.
-/

open Matrix Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.EdgeHodgeTheory

open ArithmeticCastelnuovoSeveri (cx realTests)
open HeckeKreinToeplitz (gram zetaKernel intWindow scale_intWindow gram_zetaKernel_eq_weilGram
  negIndex_eq_iSup_intWindow hermNegIndex_submatrix_le riemannHypothesis_iff_negIndex_zetaKernel_eq_zero
  negIndex_zetaKernel_eq_iSup_integerAtoms negIndex_zetaKernel)
open BiScaleUncertainty.ChebyshevGauge (cubicSpline)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Künneth defect** of a Hermitian matrix: `n₋(H ⊗ H) = 2 n₊(H) n₋(H)`. -/
theorem hermNegIndex_kronecker_self {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    hermNegIndex (kronecker H H) = 2 * (hermPosIndex H * hermNegIndex H) := by
  rw [negIndex_kronecker hH hH]
  ring

theorem hermNegIndex_kronecker_self_eq_zero_iff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    hermNegIndex (kronecker H H) = 0 ↔ hermNegIndex H = 0 ∨ hermPosIndex H = 0 := by
  rw [hermNegIndex_kronecker_self hH]
  constructor
  · intro h
    rcases Nat.mul_eq_zero.mp (by omega : hermPosIndex H * hermNegIndex H = 0) with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  · rintro (h | h) <;> simp [h]

/-- The positive index of a submatrix is at most that of the matrix. -/
theorem hermPosIndex_submatrix_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix β β ℂ) (f : α → β) : hermPosIndex (M.submatrix f f) ≤ hermPosIndex M := by
  have h := hermNegIndex_submatrix_le (-M) f
  have e : (-M).submatrix f f = -(M.submatrix f f) := by ext; simp
  rw [e] at h
  unfold hermNegIndex at h
  rwa [neg_neg, neg_neg] at h

theorem hermPosIndex_horizonGram_mono (f : ℝ → ℝ) {N N' : ℕ} (h : N ≤ N') :
    hermPosIndex (horizonGram f N) ≤ hermPosIndex (horizonGram f N') := by
  rw [← horizonGram_submatrix h]
  exact hermPosIndex_submatrix_le _ _

theorem horizonGram_cubicSpline_eq_gram (N : ℕ) :
    horizonGram cubicSpline N = gram zetaKernel (intWindow N) := by
  rw [gram_zetaKernel_eq_weilGram]
  simp only [scale_intWindow]
  rfl

/-- **The positive squares of the integer spline atoms reach `κ₊(K_ζ)`.** -/
theorem iSup_hermPosIndex_horizonGram_cubicSpline :
    ⨆ N : ℕ, (hermPosIndex (horizonGram cubicSpline N) : ℕ∞) =
      RenormalizedIntersectionTheory.posIndex zetaKernel := by
  rw [RenormalizedIntersectionTheory.posIndex, negIndex_eq_iSup_intWindow]
  refine iSup_congr fun N => ?_
  rw [horizonGram_cubicSpline_eq_gram]
  have hneg : gram (fun g => -zetaKernel g) (intWindow N) = -gram zetaKernel (intWindow N) := by
    ext a b; simp [HeckeKreinToeplitz.gram]
  rw [hneg, hermNegIndex, neg_neg]

/-- The negative squares of the integer spline atoms reach `κ(K_ζ)`. -/
theorem iSup_horizonDefect_cubicSpline :
    ⨆ N : ℕ, (horizonDefect cubicSpline N : ℕ∞) = HeckeKreinToeplitz.negIndex zetaKernel := by
  rw [negIndex_zetaKernel, negIndex_zetaKernel_eq_iSup_integerAtoms]
  rfl

theorem horizonGram_isHermitian (f : ℝ → ℝ) (N : ℕ) : (horizonGram f N).IsHermitian :=
  ArithmeticCastelnuovoSeveri.weilGram_isHermitian _ _

/-- Without RH, the integer spline atoms carry a negative and a positive square from some horizon
on. -/
theorem eventually_one_le_pos_and_neg_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ hermPosIndex (horizonGram cubicSpline N) ∧
      1 ≤ horizonDefect cubicSpline N := by
  have hneg : HeckeKreinToeplitz.negIndex zetaKernel ≠ 0 :=
    fun h => hRH (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mpr h)
  have hpos : RenormalizedIntersectionTheory.posIndex zetaKernel ≠ 0 :=
    fun h => hRH (RenormalizedIntersectionTheory.riemannHypothesis_of_posIndex_zetaKernel_eq_zero h)
  rw [← iSup_horizonDefect_cubicSpline, Ne, ENat.iSup_eq_zero] at hneg
  rw [← iSup_hermPosIndex_horizonGram_cubicSpline, Ne, ENat.iSup_eq_zero] at hpos
  push Not at hneg hpos
  obtain ⟨N₁, h₁⟩ := hneg
  obtain ⟨N₂, h₂⟩ := hpos
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN
  refine ⟨?_, ?_⟩
  · have := hermPosIndex_horizonGram_mono cubicSpline (le_trans (le_max_right N₁ N₂) hN)
    have h₂' : hermPosIndex (horizonGram cubicSpline N₂) ≠ 0 := by exact_mod_cast h₂
    omega
  · have := horizonDefect_mono cubicSpline (le_trans (le_max_left N₁ N₂) hN)
    have h₁' : horizonDefect cubicSpline N₁ ≠ 0 := by exact_mod_cast h₁
    omega

/-- **The Künneth square is RH at every resolution.** -/
theorem riemannHypothesis_iff_kunneth_horizon :
    RiemannHypothesis ↔ ∀ N : ℕ,
      hermNegIndex (kronecker (horizonGram cubicSpline N) (horizonGram cubicSpline N)) = 0 := by
  constructor
  · intro hRH N
    have h0 : horizonDefect cubicSpline N = 0 := by
      have hk := riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH
      rw [← iSup_horizonDefect_cubicSpline, ENat.iSup_eq_zero] at hk
      exact_mod_cast hk N
    exact (hermNegIndex_kronecker_self_eq_zero_iff (horizonGram_isHermitian _ N)).mpr (Or.inl h0)
  · intro H
    by_contra hRH
    obtain ⟨N, hp, hn⟩ := (eventually_one_le_pos_and_neg_of_not_rh hRH).exists
    unfold horizonDefect at hn
    rcases (hermNegIndex_kronecker_self_eq_zero_iff (horizonGram_isHermitian _ N)).mp (H N) with h | h
    · omega
    · omega

/-- Without RH the Künneth defect of the integer spline atoms is at least `2` from some horizon
on. -/
theorem eventually_two_le_kunneth_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ hermNegIndex (kronecker (horizonGram cubicSpline N) (horizonGram cubicSpline N)) := by
  filter_upwards [eventually_one_le_pos_and_neg_of_not_rh hRH] with N ⟨hp, hn⟩
  rw [hermNegIndex_kronecker_self (horizonGram_isHermitian _ N)]
  unfold horizonDefect at hn
  nlinarith

end GaloisForLFunctions.EdgeHodgeTheory
