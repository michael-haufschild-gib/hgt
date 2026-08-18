import GaloisForLFunctions.RHTower.ProlateSectorGroundLaws
import GaloisForLFunctions.RHTower.ProlateSectorOperatorSpectrum

/-!
# The constrained spectral gap of a prolate sector, non-vacuously

`ProlateSectorOperatorSpectrum` separates the ground root from competing *secular* zeros lying in
the first gap.  That statement is empty as it stands: the secular root is unique there.  The card's
equations `(6)`--`(7)` are about the next constrained eigenvalue of the operator, which lies in the
*next* gap, so what is needed is the dichotomy

```text
every constrained sector eigenvalue is either the ground value or at least d_1 ,
```

after which the complementary ground ratio `(d_1 − mu_0)/d_1 → 3/11` (resp. `5/13`) becomes a
genuine lower bound on the spectral gap of the compressed leakage operator.

The dichotomy needs two facts about a constrained sector eigenvector `g`: its Rayleigh value is its
own eigenvalue (test the weak equation against `g` itself, which is legitimate because `g` is a
constrained vector of the sector), so the ground floor puts the eigenvalue above `mu_0 > d_0`; and
the converse bridge plus uniqueness of the secular root close the interval `(d_0, d_1)`.
-/

noncomputable section

open Filter Set Topology
open scoped InnerProduct InnerProductSpace

namespace RHTower

theorem inner_even_sub_left (u w y : evenSubspace) :
    inner ℂ (u - w) y = inner ℂ u y - inner ℂ w y := inner_sub_left u w y

/-- **A constrained sector eigenvector realizes its eigenvalue as its Rayleigh value.**  Testing
the weak compressed equation against the eigenvector itself is legitimate, since the eigenvector is
itself a constrained vector of the sector. -/
theorem IsSectorConstrainedEigen.rayleigh_eq {a : ℝ} {σ : ℕ → ℕ} {μ : ℝ} {g : evenSubspace}
    (hg : IsSectorConstrainedEigen a σ μ g) :
    (inner ℂ (evenProlateLeakage a g) g : ℂ).re = μ * ‖g‖ ^ 2 := by
  obtain ⟨z, hz⟩ := hg.expansion
  have h := hg.weak_eigen z g hz hg.constraint
  rw [inner_even_sub_left, inner_even_smul_left, Complex.conj_ofReal,
    inner_even_self_eq_norm_sq, sub_eq_zero] at h
  rw [h, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The constrained ground value is a floor for every constrained sector eigenvalue.** -/
theorem IsSectorConstrainedGround.le_of_eigen {a : ℝ} {σ : ℕ → ℕ} {μ₀ μ : ℝ} {g : evenSubspace}
    (hground : IsSectorConstrainedGround a σ μ₀) (hg : IsSectorConstrainedEigen a σ μ g) :
    μ₀ ≤ μ := by
  obtain ⟨z, hz⟩ := hg.expansion
  have hgpos : 0 < ‖g‖ ^ 2 := by
    have hgn : 0 < ‖g‖ := norm_pos_iff.mpr hg.ne_zero
    positivity
  have hle := hground.1 z g hz hg.constraint
  rw [hg.rayleigh_eq] at hle
  exact le_of_mul_le_mul_right hle hgpos

/-! ## The dichotomy, in each Fourier sector -/

/-- **Every constrained eigenvalue of the Fourier-even sector is the ground value or at least the
first leakage.** -/
theorem eventually_sectorConstrainedEigen_dichotomy_positive :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      IsSectorConstrainedEigen a positiveSectorIndex μ g →
      μ = infiniteSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖)
        ∨ evenProlateSignedLeakage a 2 ≤ μ := by
  filter_upwards [ladderEnvelope_evenProlateSignedLeakage.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_atTop 0).eventually_ne
      (constrainedProlateHermiteCoordinate_ne_zero 0),
    (tendsto_norm_evenProlateConstraintCoord_atTop 1).eventually_ne
      (constrainedProlateHermiteCoordinate_ne_zero 1),
    eventually_isSectorConstrainedGround_positive,
    eventually_gt_atTop (0 : ℝ)] with a hs h0 h1 hgr ha μ g hg
  by_cases hlt : evenProlateSignedLeakage a 2 ≤ μ
  · exact Or.inr hlt
  refine Or.inl ?_
  have hsumL : Summable fun j : ℕ => sectorCoord a positiveSectorIndex j ^ 2 :=
    summable_sectorCoord_sq a positiveSectorIndex_injective
  obtain ⟨hrmem, hrzero, -⟩ :=
    infiniteSecularRoot_spec (d := sectorLeakage a positiveSectorIndex)
      (ℓ := sectorCoord a positiveSectorIndex) hs.1.2.1 hs.1.2.2 hs.2 hsumL h0 h1
  have hground := hgr.le_of_eigen hg
  have hlow : sectorLeakage a positiveSectorIndex 0 < μ := lt_of_lt_of_le hrmem.1 hground
  have hhigh : μ < sectorLeakage a positiveSectorIndex 1 := by
    have : ¬ sectorLeakage a positiveSectorIndex 1 ≤ μ := hlt
    linarith [not_le.mp this]
  have hzero := infiniteSecular_eq_zero_of_isSectorConstrainedEigen ha
    positiveSectorIndex_injective hs.1.2.2 hs.2 h1 ⟨hlow, hhigh⟩ hg
  exact infiniteSecular_root_unique hs.1.2.2 hs.2 hsumL h0 ⟨hlow, hhigh⟩ hrmem hzero hrzero

/-- **The same dichotomy in the Fourier-odd sector.** -/
theorem eventually_sectorConstrainedEigen_dichotomy_negative :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      IsSectorConstrainedEigen a negativeSectorIndex μ g →
      μ = infiniteSecularRoot (fun j => evenProlateSignedLeakage a (2 * j + 1))
            (fun j => ‖evenProlateConstraintCoord a (2 * j + 1)‖)
        ∨ evenProlateSignedLeakage a 3 ≤ μ := by
  filter_upwards [ladderEnvelope_evenProlateSignedLeakage_negative.first_struct,
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 0).eventually_ne
      (constrainedProlateNegativeCoordinate_pos 0).ne',
    (tendsto_norm_evenProlateConstraintCoord_negative_atTop 1).eventually_ne
      (constrainedProlateNegativeCoordinate_pos 1).ne',
    eventually_isSectorConstrainedGround_negative,
    eventually_gt_atTop (0 : ℝ)] with a hs h0 h1 hgr ha μ g hg
  by_cases hlt : evenProlateSignedLeakage a 3 ≤ μ
  · exact Or.inr hlt
  refine Or.inl ?_
  have hsumL : Summable fun j : ℕ => sectorCoord a negativeSectorIndex j ^ 2 :=
    summable_sectorCoord_sq a negativeSectorIndex_injective
  obtain ⟨hrmem, hrzero, -⟩ :=
    infiniteSecularRoot_spec (d := sectorLeakage a negativeSectorIndex)
      (ℓ := sectorCoord a negativeSectorIndex) hs.1.2.1 hs.1.2.2 hs.2 hsumL h0 h1
  have hground := hgr.le_of_eigen hg
  have hlow : sectorLeakage a negativeSectorIndex 0 < μ := lt_of_lt_of_le hrmem.1 hground
  have hhigh : μ < sectorLeakage a negativeSectorIndex 1 := by
    have : ¬ sectorLeakage a negativeSectorIndex 1 ≤ μ := hlt
    linarith [not_le.mp this]
  have hzero := infiniteSecular_eq_zero_of_isSectorConstrainedEigen ha
    negativeSectorIndex_injective hs.1.2.2 hs.2 h1 ⟨hlow, hhigh⟩ hg
  exact infiniteSecular_root_unique hs.1.2.2 hs.2 hsumL h0 ⟨hlow, hhigh⟩ hrmem hzero hrzero

/-! ## The quantified constrained spectral gaps -/

/-- **Equations `(6)`--`(7)` of the two-mode ground-state card, in the operator's own terms.**  For
every constant below `3/11`, every constrained eigenvalue of the compressed leakage operator on the
Fourier-even sector other than the ground value eventually exceeds it by that multiple of the
dominant leakage `d_4`. -/
theorem constrainedProlatePositive_operator_spectralGap_eventually {cst : ℝ} (hc : cst < 3 / 11)
    {μ₀ : ℝ → ℝ} (hμ₀ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a positiveSectorIndex (μ₀ a)) :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      IsSectorConstrainedEigen a positiveSectorIndex μ g → μ ≠ μ₀ a →
      cst * evenProlateSignedLeakage a 2 ≤ μ - μ₀ a := by
  have hgapratio := constrainedProlatePositive_operator_gap_ratio_tendsto hμ₀
  filter_upwards [eventually_sectorConstrainedEigen_dichotomy_positive,
    eventually_eq_infiniteSecularRoot_positive hμ₀,
    hgapratio.eventually (eventually_gt_nhds hc),
    eventually_evenProlateSignedLeakage_pos 2 (by omega)] with a hdic hroot hgap hpos μ g hg hne
  rcases hdic μ g hg with h | h
  · exact absurd (h.trans hroot.symm) hne
  · have hstrict : cst * evenProlateSignedLeakage a 2
        ≤ evenProlateSignedLeakage a 2 - μ₀ a := by
      rw [lt_div_iff₀ hpos] at hgap
      linarith
    linarith

/-- **Equation `(10)` of the parity card, in the operator's own terms.**  For every constant below
`5/13`, every constrained eigenvalue of the compressed leakage operator on the Fourier-odd sector
other than the ground value eventually exceeds it by that multiple of the dominant leakage `d_6`. -/
theorem constrainedProlateNegative_operator_spectralGap_eventually {cst : ℝ} (hc : cst < 5 / 13)
    {μ₀ : ℝ → ℝ} (hμ₀ : ∀ᶠ a : ℝ in atTop, IsSectorConstrainedGround a negativeSectorIndex (μ₀ a)) :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      IsSectorConstrainedEigen a negativeSectorIndex μ g → μ ≠ μ₀ a →
      cst * evenProlateSignedLeakage a 3 ≤ μ - μ₀ a := by
  have hgapratio := constrainedProlateNegative_operator_gap_ratio_tendsto hμ₀
  filter_upwards [eventually_sectorConstrainedEigen_dichotomy_negative,
    eventually_eq_infiniteSecularRoot_negative hμ₀,
    hgapratio.eventually (eventually_gt_nhds hc),
    eventually_evenProlateSignedLeakage_pos 3 (by omega)] with a hdic hroot hgap hpos μ g hg hne
  rcases hdic μ g hg with h | h
  · exact absurd (h.trans hroot.symm) hne
  · have hstrict : cst * evenProlateSignedLeakage a 3
        ≤ evenProlateSignedLeakage a 3 - μ₀ a := by
      rw [lt_div_iff₀ hpos] at hgap
      linarith
    linarith

end RHTower

end
