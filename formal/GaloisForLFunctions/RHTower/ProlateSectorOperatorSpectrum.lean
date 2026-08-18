import GaloisForLFunctions.RHTower.ProlateSectorConstrainedSpectrum
import GaloisForLFunctions.RHTower.ConstrainedProlateParityExactTransfer

/-!
# The constrained spectrum of a prolate sector, in the operator's own terms

The sector ground vector is a genuine eigenvector of the compressed leakage operator: its leakage
defect is the Riesz vector of the integral functional, hence orthogonal to the constrained part of
the sector.  Combined with the converse bridge, the constrained spectrum of a sector inside the
first gap is exactly the secular root set, so the quantified secular spectral gap becomes a gap
between constrained eigenvalues of `B` itself.
-/

noncomputable section

open Filter Set
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- **The sector ground vector is a constrained eigenvector.**  Its leakage defect pairs with any
vector of the sector exactly as the integral functional does, so it annihilates the constrained
part. -/
theorem isSectorConstrainedEigen_ground {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ)
    (h01 : sectorLeakage a σ 0 < sectorLeakage a σ 1)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ0 : sectorCoord a σ 0 ≠ 0) (hℓ1 : sectorCoord a σ 1 ≠ 0)
    {f : evenSubspace}
    (hf : HasSum (fun j : ℕ => ((sectorGroundCoeff a σ j : ℝ) : ℂ) • sectorMode a σ j) f) :
    IsSectorConstrainedEigen a σ
      (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ)) f := by
  classical
  set D : ℕ → ℝ := sectorLeakage a σ with hDdef
  set L : ℕ → ℝ := sectorCoord a σ with hLdef
  set μ : ℝ := infiniteSecularRoot D L with hμdef
  obtain ⟨hne, hcon, _⟩ := sectorGround_properties ha hσ h01 h12 hd2 hℓ0 hℓ1 hf
  have hsumL : Summable fun j : ℕ => L j ^ 2 := summable_sectorCoord_sq a hσ
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsumL hℓ0 hℓ1
  have hpole : ∀ j : ℕ, D j - μ ≠ 0 := secular_pole_ne h12 hd2 hrmem
  have hvterm : ∀ j : ℕ, (D j - μ) * sectorGroundCoeff a σ j = L j := by
    intro j
    have h : sectorGroundCoeff a σ j = L j / (D j - μ) := rfl
    rw [h, mul_comm, div_mul_cancel₀ _ (hpole j)]
  have hvon := orthonormal_sectorMode ha hσ
  have hBf := hasSum_leakage_apply (evenProlateLeakage_apply_sectorMode a σ) hf
  have hcoordB : ∀ j : ℕ, inner ℂ (sectorMode a σ j) (evenProlateLeakage a f)
      = ((D j : ℝ) : ℂ) * ((sectorGroundCoeff a σ j : ℝ) : ℂ) :=
    fun j => inner_eq_of_hasSum_smul hvon hBf j
  have hcoord : ∀ j : ℕ, inner ℂ (sectorMode a σ j) f
      = ((sectorGroundCoeff a σ j : ℝ) : ℂ) :=
    fun j => inner_eq_of_hasSum_smul hvon hf j
  have hdefcoord : ∀ j : ℕ,
      inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (sectorMode a σ j)
        = ((L j : ℝ) : ℂ) := by
    intro j
    rw [inner_even_conj_symm (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (sectorMode a σ j),
      inner_even_sub_right, inner_even_smul_right, hcoordB j, hcoord j]
    have hreal : ((D j : ℝ) : ℂ) * ((sectorGroundCoeff a σ j : ℝ) : ℂ)
        - ((μ : ℝ) : ℂ) * ((sectorGroundCoeff a σ j : ℝ) : ℂ) = ((L j : ℝ) : ℂ) := by
      rw [← hvterm j]
      push_cast
      ring
    rw [hreal, Complex.conj_ofReal]
  refine ⟨⟨fun j => ((sectorGroundCoeff a σ j : ℝ) : ℂ), hf⟩, hne, hcon, ?_⟩
  intro z h hz hzcon
  have hmap : HasSum (fun j : ℕ =>
      inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (z j • sectorMode a σ j))
      (inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) h) :=
    (innerSL ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f)).hasSum hz
  have hfun : (fun j : ℕ =>
      inner ℂ (evenProlateLeakage a f - ((μ : ℝ) : ℂ) • f) (z j • sectorMode a σ j))
      = fun j : ℕ => z j * ((L j : ℝ) : ℂ) := by
    funext j
    rw [inner_even_smul_right, hdefcoord j]
  rw [hfun] at hmap
  have hcs : HasSum (fun j : ℕ => z j * ((L j : ℝ) : ℂ)) 0 := by
    have hh := hasSum_constraint_of_hasSum_smul (inner_evenCentralIndicator_sectorMode a σ) hz
    rwa [hzcon] at hh
  exact hmap.unique hcs

/-- **The constrained spectrum of a sector in the first gap is the secular root set.**  Any
constrained eigenvalue of the compressed leakage operator in the first gap other than the ground
root is separated from it by the secular gap. -/
theorem eventually_sectorConstrainedEigen_gap_positive {cst : ℝ} (hc : cst < 3 / 11) :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      μ ∈ Set.Ioo (sectorLeakage a positiveSectorIndex 0)
        (sectorLeakage a positiveSectorIndex 1) →
      IsSectorConstrainedEigen a positiveSectorIndex μ g →
      μ ≠ infiniteSecularRoot (sectorLeakage a positiveSectorIndex)
        (sectorCoord a positiveSectorIndex) →
      cst * sectorLeakage a positiveSectorIndex 1
        ≤ μ - infiniteSecularRoot (sectorLeakage a positiveSectorIndex)
            (sectorCoord a positiveSectorIndex) := by
  have hne1 : constrainedProlateHermiteCoordinate 1 ≠ 0 := by
    rw [constrainedProlateHermiteCoordinate_one_eq]
    positivity
  filter_upwards [constrainedProlatePositive_spectralGap_eventually hc,
    ladderEnvelope_evenProlateSignedLeakage.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_atTop 1).eventually_ne hne1,
    eventually_gt_atTop (0 : ℝ)] with a hgap hs h1 ha μ g hμ hg hne
  exact hgap μ (infiniteSecular_eq_zero_of_isSectorConstrainedEigen ha
    positiveSectorIndex_injective hs.1.2.2 hs.2 h1 hμ hg) hne

/-- **The quantified negative-sector secular spectral gap.**  For every constant below `5/13`,
every competing secular zero of the Fourier-odd sector eventually sits that far above the ground
root, measured in units of the first leakage. -/
theorem constrainedProlateNegative_spectralGap_eventually {cst : ℝ} (hc : cst < 5 / 13) :
    let D : ℝ → ℕ → ℝ := fun a j => evenProlateSignedLeakage a (2 * j + 1)
    let ℓ : ℝ → ℕ → ℝ := fun lam j => ‖evenProlateConstraintCoord lam (2 * j + 1)‖
    ∀ᶠ lam : ℝ in atTop, ∀ μ' : ℝ, infiniteSecular (D lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (D lam) (ℓ lam) →
      cst * D lam 1 ≤ μ' - infiniteSecularRoot (D lam) (ℓ lam) := by
  intro D ℓ
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have hc' : cst < (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2 /
      (((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 + (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2) := by
    rwa [ccm_negativeSector_hermite_weight_complement_eq]
  have hl0 : Tendsto (fun lam : ℝ => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))) := by
    have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 0
    rwa [constrainedProlateNegativeCoordinate_zero] at h
  have hl1 : Tendsto (fun lam : ℝ => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4))) := by
    have h := tendsto_norm_evenProlateConstraintCoord_negative_atTop 1
    rwa [constrainedProlateNegativeCoordinate_one] at h
  exact infiniteSecularRoot_spectralGap_eventually ha0 ha1
    ladderEnvelope_evenProlateSignedLeakage_negative.first_struct
    negativeSector_sum negativeSector_bessel
    (ladderEnvelope_evenProlateSignedLeakage_negative.ratio_tendsto_zero 0)
    (ladderEnvelope_evenProlateSignedLeakage_negative.tail_tendsto_zero 0)
    hl0 hl1 hc'

/-- The same on the Fourier-odd sector. -/
theorem eventually_sectorConstrainedEigen_gap_negative {cst : ℝ} (hc : cst < 5 / 13) :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      μ ∈ Set.Ioo (sectorLeakage a negativeSectorIndex 0)
        (sectorLeakage a negativeSectorIndex 1) →
      IsSectorConstrainedEigen a negativeSectorIndex μ g →
      μ ≠ infiniteSecularRoot (sectorLeakage a negativeSectorIndex)
        (sectorCoord a negativeSectorIndex) →
      cst * sectorLeakage a negativeSectorIndex 1
        ≤ μ - infiniteSecularRoot (sectorLeakage a negativeSectorIndex)
            (sectorCoord a negativeSectorIndex) := by
  have hne1 : constrainedProlateNegativeCoordinate 1 ≠ 0 := by
    rw [constrainedProlateNegativeCoordinate_one]
    positivity
  filter_upwards [constrainedProlateNegative_spectralGap_eventually hc,
    ladderEnvelope_evenProlateSignedLeakage_negative.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 1).eventually_ne hne1,
    eventually_gt_atTop (0 : ℝ)] with a hgap hs h1 ha μ g hμ hg hne
  exact hgap μ (infiniteSecular_eq_zero_of_isSectorConstrainedEigen ha
    negativeSectorIndex_injective hs.1.2.2 hs.2 h1 hμ hg) hne

end RHTower

end
