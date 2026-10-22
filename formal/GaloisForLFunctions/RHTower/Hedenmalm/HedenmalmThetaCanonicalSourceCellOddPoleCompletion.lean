import GaloisForLFunctions.HTGeometry.SourcePairOddCellEscape
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtCompactOpen
import GaloisForLFunctions.HTGeometry.FiniteRankDeterminantCompletion
import GaloisForLFunctions.HTGeometry.HermitianDilationSecondJetObstruction
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSignedOrdinaryDeterminantCompletion

/-!
# Canonical theta source cells and escaping odd poles

Every coefficient of each actual finite signed theta stage is encoded by a fixed real source-pair
cell and recovered by a fixed decoder.  The associated four-channel odd cells are assembled over
all coefficients, with no spectral or zero selection.  A source-defined Hilbert--Schmidt aperture
makes their honest finite Fredholm determinants converge compact-open to one.  Consequently every
compact eventually contains no odd pole, while the graded quotient still converges compact-open to
normalized Xi.
-/

open Complex Matrix Filter Metric Set

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HilbertSchmidt

noncomputable section

/-- Decode one literal real source-pair cell back to its complex coefficient. -/
def sourcePairCellDecode (C : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  C 0 0 + C 1 0 * I

theorem sourcePairCellDecode_sourcePairBlock (z : ℂ) :
    sourcePairCellDecode (sourcePairBlock z.re z.im) = z := by
  simp [sourcePairCellDecode, sourcePairBlock]

/-- Actual finite signed theta stage matrix. -/
def thetaSourceSignedStageMatrix (k : ℕ) :
    Matrix ↥(thetaSourceSignedCutoff k) ↥(thetaSourceSignedCutoff k) ℂ :=
  blockMatrix (thetaSourceSignedKernel k) (thetaSourceSignedCutoff k)

/-- Canonical real source-pair cell of one actual theta-stage coefficient. -/
def thetaSourceSignedCoefficientCell (k : ℕ)
    (i j : ↥(thetaSourceSignedCutoff k)) : Matrix (Fin 2) (Fin 2) ℂ :=
  let z := thetaSourceSignedStageMatrix k i j
  sourcePairBlock z.re z.im

/-- Exact coefficient recovery; neither spectrum nor Xi divisor is inspected. -/
theorem thetaSourceSignedFiniteMatrix_cellDecode (k : ℕ)
    (i j : ↥(thetaSourceSignedCutoff k)) :
    sourcePairCellDecode (thetaSourceSignedCoefficientCell k i j) =
      thetaSourceSignedStageMatrix k i j := by
  exact sourcePairCellDecode_sourcePairBlock _

/-- Source-only scale: stage count times one plus actual Hilbert--Schmidt size. -/
def thetaSourceOddCellEscapeScale (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * (1 + hsNorm (thetaSourceSignedKernel k))

theorem thetaSourceOddCellEscapeScale_one_le (k : ℕ) :
    1 ≤ thetaSourceOddCellEscapeScale k := by
  rw [thetaSourceOddCellEscapeScale]
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  nlinarith [hsNorm_nonneg (thetaSourceSignedKernel k)]

/-- Four-channel odd source cell assembled entrywise from every actual theta coefficient. -/
def thetaSourceEscapingOddCellKernel (k : ℕ) :
    (thetaIndex × Fin 4) × (thetaIndex × Fin 4) → ℂ :=
  sourcePairOddCellKernel (thetaSourceOddCellEscapeScale k)
    (thetaSourceSignedKernel k)

theorem thetaSourceEscapingOddCellKernel_cell (k : ℕ) (i j : thetaIndex)
    (c d : Fin 4) :
    thetaSourceEscapingOddCellKernel k ((i, c), (j, d)) =
      sourcePairRealOddBlock (thetaSourceSignedKernel k (i, j)).im c d /
        (thetaSourceOddCellEscapeScale k : ℂ) := rfl

/-- Odd assembly is coefficient-faithful on the actual theta aperture. -/
theorem thetaSourceEscapingOddCellKernel_eq_decodedCoefficientCell (k : ℕ)
    (i j : ↥(thetaSourceSignedCutoff k)) (c d : Fin 4) :
    thetaSourceEscapingOddCellKernel k ((i.1, c), (j.1, d)) =
      sourcePairRealOddBlock
        (sourcePairCellDecode (thetaSourceSignedCoefficientCell k i j)).im c d /
          (thetaSourceOddCellEscapeScale k : ℂ) := by
  rw [thetaSourceSignedFiniteMatrix_cellDecode]
  rfl

theorem isHS_thetaSourceEscapingOddCellKernel (k : ℕ) :
    IsHS (thetaSourceEscapingOddCellKernel k) :=
  isHS_sourcePairOddCellKernel (thetaSourceOddCellEscapeScale_one_le k)
    (isHS_thetaSourceSignedKernel k)

/-- Explicit dimension-free Hilbert--Schmidt energy decay. -/
theorem hsNormSq_thetaSourceEscapingOddCellKernel_le (k : ℕ) :
    hsNormSq (thetaSourceEscapingOddCellKernel k) ≤ 4 / (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  let x : ℝ := hsNorm (thetaSourceSignedKernel k)
  have hx : 0 ≤ x := hsNorm_nonneg _
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hbase := hsNormSq_sourcePairOddCellKernel_le
    (thetaSourceOddCellEscapeScale_one_le k) (isHS_thetaSourceSignedKernel k)
  rw [thetaSourceEscapingOddCellKernel]
  refine hbase.trans ?_
  rw [thetaSourceOddCellEscapeScale]
  have hsquare : hsNormSq (thetaSourceSignedKernel k) = x ^ (2 : ℕ) := by
    dsimp only [x]
    rw [HilbertSchmidt.hsNorm]
    exact (Real.sq_sqrt (hsNormSq_nonneg _)).symm
  rw [hsquare]
  have hratio : x ^ (2 : ℕ) ≤ (1 + x) ^ (2 : ℕ) := by nlinarith
  change (4 / ((((k + 1 : ℕ) : ℝ) * (1 + x)) ^ (2 : ℕ))) * x ^ (2 : ℕ) ≤
    4 / (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  field_simp
  nlinarith [sq_nonneg (((k + 1 : ℕ) : ℝ)), sq_nonneg (1 + x)]

theorem hsNorm_thetaSourceEscapingOddCellKernel_le (k : ℕ) :
    hsNorm (thetaSourceEscapingOddCellKernel k) ≤ 2 / (((k + 1 : ℕ) : ℝ)) := by
  have hk : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  change Real.sqrt (hsNormSq (thetaSourceEscapingOddCellKernel k)) ≤ _
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have h := hsNormSq_thetaSourceEscapingOddCellKernel_le k
    convert h using 1
    all_goals field_simp
    all_goals ring

theorem thetaSourceEscapingOddCellKernel_tendsto_zero :
    Tendsto (fun k => hsNorm (thetaSourceEscapingOddCellKernel k)) atTop (nhds 0) := by
  apply squeeze_zero (fun k => hsNorm_nonneg _) hsNorm_thetaSourceEscapingOddCellKernel_le
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  simpa [div_eq_mul_inv] using h

/-- Canonical finite aperture after replacing every theta source coordinate by four odd channels. -/
def thetaSourceEscapingOddCellCutoff (k : ℕ) : Finset (thetaIndex × Fin 4) :=
  sourcePairOddCellCutoff (thetaSourceSignedCutoff k)

theorem thetaSourceEscapingOddCellKernel_support (k : ℕ)
    (p : (thetaIndex × Fin 4) × (thetaIndex × Fin 4))
    (hp : p ∉ thetaSourceEscapingOddCellCutoff k ×ˢ thetaSourceEscapingOddCellCutoff k) :
    thetaSourceEscapingOddCellKernel k p = 0 :=
  sourcePairOddCellKernel_support _ _ (thetaSourceSignedKernel_support k) p hp

theorem hsTraceDiag_thetaSourceEscapingOddCellKernel (k : ℕ) :
    hsTraceDiag (thetaSourceEscapingOddCellKernel k) = 0 :=
  hsTraceDiag_sourcePairOddCellKernel_eq_zero _ (thetaSourceSignedKernel_support k)

/-- Odd Fredholm denominator assembled from all actual finite theta coefficients. -/
noncomputable def thetaSourceEscapingOddCellDet (k : ℕ) (z : ℂ) : ℂ :=
  ((1 : Matrix ↥(thetaSourceEscapingOddCellCutoff k)
      ↥(thetaSourceEscapingOddCellCutoff k) ℂ) -
    z • blockMatrix (thetaSourceEscapingOddCellKernel k)
      (thetaSourceEscapingOddCellCutoff k)).det

/-- Trace cancellation identifies honest finite determinant with the regularized determinant. -/
theorem thetaSourceEscapingOddCellDet_eq_entireDet2 (k : ℕ) (z : ℂ) :
    thetaSourceEscapingOddCellDet k z =
      entireDet2 (thetaSourceEscapingOddCellKernel k) z := by
  rw [thetaSourceEscapingOddCellDet,
    det_one_sub_smul_blockMatrix (isHS_thetaSourceEscapingOddCellKernel k)
      (thetaSourceEscapingOddCellKernel_support k) z,
    hsTraceDiag_thetaSourceEscapingOddCellKernel]
  simp [completedDet2]

theorem thetaSourceEscapingOddCellDet_tendstoLocallyUniformly_one :
    TendstoLocallyUniformly thetaSourceEscapingOddCellDet (fun _ : ℂ => 1) atTop := by
  have hzero : Tendsto (fun k => hsNorm
      (thetaSourceEscapingOddCellKernel k -
        (0 : (thetaIndex × Fin 4) × (thetaIndex × Fin 4) → ℂ))) atTop (nhds 0) := by
    simpa using thetaSourceEscapingOddCellKernel_tendsto_zero
  have hdet := tendstoLocallyUniformly_entireDet2_of_hsNorm_sub_tendsto_zero
    thetaSourceEscapingOddCellKernel
    (0 : (thetaIndex × Fin 4) × (thetaIndex × Fin 4) → ℂ)
    isHS_thetaSourceEscapingOddCellKernel isHS_zero hzero
  rw [show thetaSourceEscapingOddCellDet =
      (fun k z => entireDet2 (thetaSourceEscapingOddCellKernel k) z) by
    funext k z
    exact thetaSourceEscapingOddCellDet_eq_entireDet2 k z]
  simpa [entireDet2_zero_kernel] using hdet

/-- Every compact set eventually contains no odd denominator zero: all odd poles escape. -/
theorem thetaSourceEscapingOddCellDet_eventually_ne_zero_on_compact
    (C : Set ℂ) (hC : IsCompact C) :
    ∀ᶠ k in atTop, ∀ z ∈ C, thetaSourceEscapingOddCellDet k z ≠ 0 := by
  have huni := (tendstoLocallyUniformly_iff_forall_isCompact.mp
    thetaSourceEscapingOddCellDet_tendstoLocallyUniformly_one) C hC
  rw [Metric.tendstoUniformlyOn_iff] at huni
  have hclose := huni 1 zero_lt_one
  filter_upwards [hclose] with k hk
  intro z hz hzero
  have hlt := hk z hz
  rw [hzero] at hlt
  norm_num [dist_eq] at hlt

/-- Actual signed theta numerator divided by escaping odd source cells. -/
noncomputable def thetaSourceCellGradedSuperdet (k : ℕ) (z : ℂ) : ℂ :=
  thetaSourceSignedOrdinaryDet k z / thetaSourceEscapingOddCellDet k z

/-- Adding the escaping odd sector preserves compact-open convergence to normalized Xi. -/
theorem thetaSourceCellGradedSuperdet_tendstoLocallyUniformly_XiC :
    TendstoLocallyUniformly thetaSourceCellGradedSuperdet
      (fun z => XiC z / XiC 0) atTop := by
  have h := thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC.div₀
    thetaSourceEscapingOddCellDet_tendstoLocallyUniformly_one
    (RHTower.XiC_differentiable.continuous.div_const _) continuous_const
    (fun _ => one_ne_zero)
  rw [show thetaSourceCellGradedSuperdet =
      thetaSourceSignedOrdinaryDet / thetaSourceEscapingOddCellDet by rfl]
  rw [show (fun z => XiC z / XiC 0) =
      (fun z => XiC z / XiC 0) / (fun _ : ℂ => 1) by
    funext z
    simp]
  exact h

/-- Closed certificate: source-coordinate decomposition, odd-pole escape, and Xi completion. -/
theorem thetaSourceCanonicalCellOddPoleEscapeXiCompletion :
    (∀ k i j, sourcePairCellDecode (thetaSourceSignedCoefficientCell k i j) =
      thetaSourceSignedStageMatrix k i j) ∧
    (∀ k, hsTraceDiag (thetaSourceEscapingOddCellKernel k) = 0) ∧
    Tendsto (fun k => hsNorm (thetaSourceEscapingOddCellKernel k)) atTop (nhds 0) ∧
    (∀ C : Set ℂ, IsCompact C →
      ∀ᶠ k in atTop, ∀ z ∈ C, thetaSourceEscapingOddCellDet k z ≠ 0) ∧
    TendstoLocallyUniformly thetaSourceCellGradedSuperdet
      (fun z => XiC z / XiC 0) atTop := by
  exact ⟨thetaSourceSignedFiniteMatrix_cellDecode,
    hsTraceDiag_thetaSourceEscapingOddCellKernel,
    thetaSourceEscapingOddCellKernel_tendsto_zero,
    thetaSourceEscapingOddCellDet_eventually_ne_zero_on_compact,
    thetaSourceCellGradedSuperdet_tendstoLocallyUniformly_XiC⟩

end
end RHTower.HedenmalmThetaSource
