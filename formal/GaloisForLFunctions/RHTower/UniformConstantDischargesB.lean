import GaloisForLFunctions.RHTower.GammaDampedNearField
import GaloisForLFunctions.RHTower.GaussianCentralGapFiniteRangeConverse
import GaloisForLFunctions.RHTower.JointAncestryUnconditionalShellProducer
import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicFloor
import GaloisForLFunctions.RHTower.PoissonPrimeClockCommutator
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.PrimeTailCoPoissonBoundary
import GaloisForLFunctions.RHTower.RiemannKernelTruncationEnergyOrder
import GaloisForLFunctions.RHTower.RiemannKernelTruncationWeilPositive
import GaloisForLFunctions.RHTower.SmoothAFEReflectedDeepFullStrip
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepDualExpansion

/-!
# Uniform constants discharged in `RHTower` (B)

Each theorem is a corpus estimate whose constants were hypotheses, with those constants supplied
by the corpus theorems that prove the corresponding bounds (named in each docstring). A constant
that the conclusion still mentions is existentially quantified; one that it does not mention is
eliminated.
-/



open Complex Filter Function MeasureTheory Metric Set Topology Zeta23
open scoped ComplexConjugate ENNReal NNReal Real Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry XiAtlasFinitePart intervalIntegral


/-- `tendsto_nearRegEnergy` with its constants supplied by
`RHTower.exists_nearField_bound`. -/
theorem tendsto_nearRegEnergy_uniform :
    Tendsto nearRegEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_nearField_bound
  apply tendsto_nearRegEnergy <;> first | assumption | linarith

/-- `norm_filteredCentralGap_le_of_budget` with its constants supplied by
`RHTower.exists_abs_gaussianCentralGapLog_le_exp`. -/
theorem norm_filteredCentralGap_le_of_budget_uniform :
    ∃ (C₁ : ℝ), ∀ (ε : ℝ), 0 < ε → ∀ (τ : ℝ) (K : ℝ), 0 ≤ K → (∀ u ∈ Ioc (0 : ℝ) (4 * ε), |gaussianCentralGapLog u| ≤ K) →
      ‖gaussianFilteredCentralGap ε τ‖ ≤ K * Real.sqrt (2 * Real.pi * ε) + 4 / 3 * C₁ := by
  obtain ⟨C₁, h_0_0, h_0_1⟩ := RHTower.exists_abs_gaussianCentralGapLog_le_exp
  refine ⟨C₁, ?_⟩
  intro ε hε τ K hK hbud
  apply norm_filteredCentralGap_le_of_budget <;> first | assumption | linarith

/-- `unconditional_angle_xiZeroCopy` with its constants supplied by
`RHTower.exists_xiDivisorSupport_abs_im_lower_bound`. -/
theorem unconditional_angle_xiZeroCopy_uniform :
    ∃ (η : ℝ), ∀ (q : XiZeroCopy),
      η ^ 2 / (η ^ 2 + η + 1) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  obtain ⟨η, h_0_0, h_0_1⟩ := RHTower.exists_xiDivisorSupport_abs_im_lower_bound
  refine ⟨η, ?_⟩
  intro q
  apply unconditional_angle_xiZeroCopy <;> first | assumption | linarith

/-- `norm_sincGaussWindow_le` with its constants supplied by
`RHTower.exists_norm_complexSinc_le`. -/
theorem norm_sincGaussWindow_le_uniform :
    ∃ (C : ℝ), ∀ (L : ℝ) (γ : ℝ), 0 ≤ L → ∀ (z : ℂ), 1 / 2 ≤ z.re → z.re ≤ 3 →
      ‖sincGaussWindow L γ z‖ ≤ C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * Real.exp (-(z.im - γ) ^ 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_norm_complexSinc_le
  refine ⟨C, ?_⟩
  intro L γ hL z hz hz'
  apply norm_sincGaussWindow_le <;> first | assumption | linarith

/-- `norm_mobHilbertFloorWindowField_three_le` with its constants supplied by
`RHTower.exists_norm_complexSinc_le`. -/
theorem norm_mobHilbertFloorWindowField_three_le_uniform :
    ∃ (C : ℝ), ∀ (L : ℝ) (γ : ℝ) (N : ℕ), 1 ≤ N → 0 ≤ L → ∀ (y : ℝ),
      ‖mobHilbertFloorWindowField N L γ ((3 : ℂ) + (y : ℂ) * I)‖ ≤ C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (20 / N) * Real.exp (-(y - γ) ^ 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_norm_complexSinc_le
  refine ⟨C, ?_⟩
  intro L γ N hN hL y
  apply norm_mobHilbertFloorWindowField_three_le <;> first | assumption | linarith

/-- `norm_integral_mobHilbertFloorWindowField_three_le` with its constants supplied by
`RHTower.exists_norm_complexSinc_le`. -/
theorem norm_integral_mobHilbertFloorWindowField_three_le_uniform :
    ∃ (C : ℝ), ∀ (L : ℝ) (γ : ℝ) (N : ℕ), 1 ≤ N → 0 ≤ L →
      ‖∫ y : ℝ, mobHilbertFloorWindowField N L γ (((3 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ C ^ 4 * Real.exp (10 * L) * Real.exp (25 / 4) * (20 / N) * Real.sqrt Real.pi := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_norm_complexSinc_le
  refine ⟨C, ?_⟩
  intro L γ N hN hL
  apply norm_integral_mobHilbertFloorWindowField_three_le <;> first | assumption | linarith

/-- `orthonormal_mertensShellVec_shift` with its constants supplied by
`RHTower.exists_mertensShellMass_gt`. -/
theorem orthonormal_mertensShellVec_shift_uniform :
    ∃ (N : ℕ), ∀ (k : ℕ),
      Orthonormal ℂ fun n => mertensShellVec (N + n + k) := by
  obtain ⟨N, h_0_0⟩ := RHTower.exists_mertensShellMass_gt
  refine ⟨N, ?_⟩
  intro k
  apply orthonormal_mertensShellVec_shift <;> first | assumption | linarith

/-- `norm_xiCentralReciprocalMoment_le` with its constants supplied by
`RHTower.exists_xiZeroCopyReciprocalSquare_norm_bound`. -/
theorem norm_xiCentralReciprocalMoment_le_uniform :
    ∃ (M : ℝ), ∀ (n : ℕ),
      ‖xiCentralReciprocalMoment n‖ ≤ M ^ n * ∑' q : XiZeroCopy, ‖xiZeroCopyReciprocalSquare q‖ := by
  obtain ⟨M, h_0_0, h_0_1⟩ := RHTower.exists_xiZeroCopyReciprocalSquare_norm_bound
  refine ⟨M, ?_⟩
  intro n
  apply norm_xiCentralReciprocalMoment_le <;> first | assumption | linarith

/-- `primeTailCount_window` with its constants supplied by
`RHTower.exists_chebyshevPsiReal_le_linear`. -/
theorem primeTailCount_window_uniform :
    ∃ (C : ℝ), ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∀ᶠ X : ℝ in atTop, chebyshevPsiReal X / X - C * (X ^ (1 - ε) / X) ≤ primeTailCount X * Real.log X / X ∧ primeTailCount X * Real.log X / X ≤ C * (X ^ (1 - ε) * Real.log X / X) / Real.log 2 + chebyshevPsiReal X / X / (1 - ε) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_chebyshevPsiReal_le_linear
  refine ⟨C, ?_⟩
  intro ε hε0 hε1
  apply primeTailCount_window <;> first | assumption | linarith

/-- `re_arch_le` with its constants supplied by
`RHTower.exists_abs_gammaBracket_le`. -/
theorem re_arch_le_uniform :
    ∃ (C : ℝ), ∀ (f : ℝ → ℂ), ContDiff ℝ 3 f → HasCompactSupport f → ∀ (a : ℝ), tsupport f ⊆ Icc (-a) a → ∀ (s : ℝ), 0 < s →
      ((1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re ≤ (C + s / 2) * (∫ u, ‖f u‖ ^ 2) + 1 / (2 * s) * ∫ u, ‖deriv f u‖ ^ 2 := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_abs_gammaBracket_le
  refine ⟨C, ?_⟩
  intro f hf hfc a hfs s hs
  apply re_arch_le <;> first | assumption | linarith

/-- `re_W_edgeTail_le` with its constants supplied by
`RHTower.exists_abs_gammaBracket_le`. -/
theorem re_W_edgeTail_le_uniform :
    ∃ (C : ℝ), ∀ (L : ℝ) (R : ℝ), 1 ≤ L → L + 2 ≤ R → ∀ (s : ℝ), 0 < s →
      (zetaZeroConfig.W (fun u => (edgeTail L R u : ℂ)) (fun u => (edgeTail L R u : ℂ))).re ≤ 2 * (∫ u, edgeTail L R u * Real.exp (|u| / 2)) ^ 2 + ((C + s / 2) * (∫ u, edgeTail L R u ^ 2) + 1 / (2 * s) * ∫ u, deriv (edgeTail L R) u ^ 2) := by
  obtain ⟨C, h_0_0, h_0_1⟩ := RHTower.exists_abs_gammaBracket_le
  refine ⟨C, ?_⟩
  intro L R hL hR s hs
  apply re_W_edgeTail_le <;> first | assumption | linarith

/-- `abs_edgeCutoffD2_le` with its constants supplied by
`RHTower.exists_abs_deriv_deriv_smoothTransition_le`. -/
theorem abs_edgeCutoffD2_le_uniform :
    ∃ (S₂ : ℝ), ∀ (S₁ : ℝ), (∀ x, |deriv st x| ≤ S₁) → ∀ (L : ℝ) (η : ℝ), 0 < η → ∀ (u : ℝ),
      |edgeCutoffD2 L η u| ≤ (2 * S₂ + 2 * S₁ ^ 2) / η ^ 2 := by
  obtain ⟨S₂, h_0_0, h_0_1⟩ := RHTower.exists_abs_deriv_deriv_smoothTransition_le
  refine ⟨S₂, ?_⟩
  intro S₁ hS₁ L η hη u
  apply abs_edgeCutoffD2_le <;> first | assumption | linarith

/-- `norm_paperFT_edgeTail_le` with its constants supplied by
`RHTower.exists_abs_deriv_deriv_smoothTransition_le`. -/
theorem norm_paperFT_edgeTail_le_uniform :
    ∃ (S₂ : ℝ), ∀ (S₁ : ℝ), 0 ≤ S₁ → (∀ x, |deriv st x| ≤ S₁) → ∀ (L : ℝ) (R : ℝ) (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖paperFT (fun u => (edgeTail L R u : ℂ)) z‖ ≤ 4 * (2 * (1 + 2 * (2 * S₁ / 1 + 2 * S₁ / edgeWidth L) + ((2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2 + (2 * S₂ + 2 * S₁ ^ 2) / edgeWidth L ^ 2)) * kernelTailMass 0) / (1 + |z.re|) ^ 2 := by
  obtain ⟨S₂, h_0_0, h_0_1⟩ := RHTower.exists_abs_deriv_deriv_smoothTransition_le
  refine ⟨S₂, ?_⟩
  intro S₁ hS₁0 hS₁ L R z hz
  apply norm_paperFT_edgeTail_le <;> first | assumption | linarith

/-- `norm_paperFT_outerTail_le` with its constants supplied by
`RHTower.exists_abs_deriv_deriv_smoothTransition_le`. -/
theorem norm_paperFT_outerTail_le_uniform :
    ∃ (S₂ : ℝ), ∀ (S₁ : ℝ), 0 ≤ S₁ → (∀ x, |deriv st x| ≤ S₁) → ∀ (R : ℝ) (z : ℂ), |z.im| ≤ 1 / 2 →
      ‖paperFT (fun u => (outerTail R u : ℂ)) z‖ ≤ 4 * (2 * (1 + 2 * (2 * S₁ / 1) + (2 * S₂ + 2 * S₁ ^ 2) / 1 ^ 2) * kernelTailMass R) / (1 + |z.re|) ^ 2 := by
  obtain ⟨S₂, h_0_0, h_0_1⟩ := RHTower.exists_abs_deriv_deriv_smoothTransition_le
  refine ⟨S₂, ?_⟩
  intro S₁ hS₁0 hS₁ R z hz
  apply norm_paperFT_outerTail_le <;> first | assumption | linarith

/-- `norm_smoothAFEZetaReflectedTerm_displaced_deep_le_strip` with its constants supplied by
`RHTower.exists_norm_zetaChi_neg_seven_halves_poly_le`. -/
theorem norm_smoothAFEZetaReflectedTerm_displaced_deep_le_strip_uniform :
    ∃ (C : ℝ) (N : ℕ), ∀ (x : ℝ) (d : ℝ), 0 < x → 0 < d → d < 1 / 2 → ∀ (tau : ℝ) (n : ℕ) (v : ℝ),
      ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ (((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) * (Real.exp ((d - 4) ^ 2) / |d - 4|) * C) * ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2)))) := by
  obtain ⟨C, N, h_0_0, h_0_1⟩ := RHTower.exists_norm_zetaChi_neg_seven_halves_poly_le
  refine ⟨C, N, ?_⟩
  intro x d hx hd hdhalf tau n v
  apply norm_smoothAFEZetaReflectedTerm_displaced_deep_le_strip <;> first | assumption | linarith

/-- `norm_smoothAFEZetaReflectedTerm_displaced_deep_le` with its constants supplied by
`RHTower.exists_norm_zetaChi_neg_seven_halves_poly_le`. -/
theorem norm_smoothAFEZetaReflectedTerm_displaced_deep_le_uniform :
    ∃ (C : ℝ) (N : ℕ), ∀ (x : ℝ) (d : ℝ), 0 < x → 0 < d → d ≤ 1 / 4 → ∀ (tau : ℝ) (n : ℕ) (v : ℝ),
      ‖smoothAFEZetaReflectedTerm (displacedLinePt d tau) x n (((d - 4 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ (((1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) * x ^ (d - 4) * (Real.exp ((d - 4) ^ 2) / |d - 4|) * C) * ((1 + |tau| + |v|) ^ N * Real.exp (-(v ^ 2)))) := by
  obtain ⟨C, N, h_0_0, h_0_1⟩ := RHTower.exists_norm_zetaChi_neg_seven_halves_poly_le
  refine ⟨C, N, ?_⟩
  intro x d hx hd hdq tau n v
  apply norm_smoothAFEZetaReflectedTerm_displaced_deep_le <;> first | assumption | linarith

end RHTower
