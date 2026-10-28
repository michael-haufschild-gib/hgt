import GaloisForLFunctions.ArithmeticIndexDescent.TheSeparatedMixedSourceIsBounded
import GaloisForLFunctions.ArithmeticIndexDescent.EveryShortCellPaysAnyFixedMassCharge

/-!
# A new cell pays its interaction while retaining the old diagonal

Across a geometric gap, a sufficiently short new cell absorbs the full mixed
prime, Gamma and pole interaction. The estimate retains the exact old Weil
diagonal and spends only a prescribed fraction of its square mass. It therefore
applies to successive extensions without an assumed sign of the old form.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

/-- Disjoint real profiles have exactly additive square mass. -/
theorem sectionMass_add_of_disjoint (p g : realTests)
    (hdisj : ∀ u, p.1 u * g.1 u = 0) :
    sectionMass (p + g).1 = sectionMass p.1 + sectionMass g.1 := by
  have hps : HasCompactSupport (fun u => p.1 u ^ 2) :=
    HasCompactSupport.comp_left (f := p.1) (g := fun t : ℝ => t ^ 2) p.2.2 (by simp)
  have hgs : HasCompactSupport (fun u => g.1 u ^ 2) :=
    HasCompactSupport.comp_left (f := g.1) (g := fun t : ℝ => t ^ 2) g.2.2 (by simp)
  have hpc : Continuous (fun u => p.1 u ^ 2) := p.2.1.continuous.pow 2
  have hgc : Continuous (fun u => g.1 u ^ 2) := g.2.1.continuous.pow 2
  have hp : Integrable (fun u => p.1 u ^ 2) := hpc.integrable_of_hasCompactSupport hps
  have hg : Integrable (fun u => g.1 u ^ 2) := hgc.integrable_of_hasCompactSupport hgs
  change (∫ u, (p.1 u + g.1 u) ^ 2) = _
  calc
    _ = ∫ u, p.1 u ^ 2 + g.1 u ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with u
      nlinarith only [hdisj u]
    _ = _ := integral_add hp hg

/-- The new width pays any prescribed new mass while changing the old diagonal
by at most the chosen square-mass charge. All mixed estimates come from the source. -/
theorem exists_shortCell_diagonal_extension {R d ε : ℝ}
    (hR : 0 < R) (hd : 0 < d) (hε : 0 < ε) (b L : ℝ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ p g : realTests,
        (∀ u, R < |u| → p.1 u = 0) →
        (∀ u, p.1 u ≠ 0 → d < |u - b|) →
        (∀ u, δ / 2 < |u - b| → g.1 u = 0) →
        realWeilForm p p - ε * sectionMass p.1 + L * sectionMass g.1 ≤
          realWeilForm (p + g) (p + g) := by
  let R' := R + |b| + 2
  have hR' : 0 < R' := by dsimp [R']; positivity
  have hd2 : 0 < d / 2 := div_pos hd (by norm_num)
  obtain ⟨D, _, hpayment⟩ := exists_separatedWeil_mass_payment hR' hd2 hε
  obtain ⟨η, hη, hcell⟩ := exists_shortCell_weil_coercivity (D + L)
  refine ⟨min 1 (min d η), lt_min zero_lt_one (lt_min hd hη), ?_⟩
  intro δ hδ hδlt p g hps hgap hgs
  have hδ1 : δ ≤ 1 := (hδlt.trans_le (min_le_left _ _)).le
  have hδd : δ ≤ d := (hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδη : δ < η := hδlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hps' : ∀ u, R' < |u| → p.1 u = 0 := by
    intro u hu
    apply hps
    have hRR : R ≤ R' := by dsimp [R']; linarith only [abs_nonneg b]
    exact hRR.trans_lt hu
  have hgs' : ∀ u, R' < |u| → g.1 u = 0 := by
    intro u hu
    by_contra hne
    have hcenter : |u - b| ≤ δ / 2 := le_of_not_gt fun hh => hne (hgs u hh)
    have htri := abs_add_le (u - b) b
    rw [sub_add_cancel] at htri
    dsimp [R'] at hu
    linarith only [hu, hcenter, htri, hδ1, hR]
  have hseparated : ∀ u v, p.1 u ≠ 0 → g.1 v ≠ 0 → d / 2 < |u - v| := by
    intro u v hu hv
    have hold := hgap u hu
    have hnew : |v - b| ≤ δ / 2 := le_of_not_gt fun hh => hv (hgs v hh)
    have htri : |u - b| ≤ |u - v| + |v - b| := by
      rw [show u - b = (u - v) + (v - b) by ring]
      exact abs_add_le _ _
    linarith only [hold, hnew, htri, hδd]
  have hmix := hpayment p g hps' hgs' hseparated
  have hnew := hcell δ hδ hδη b g hgs
  have hsum : realWeilForm (p + g) (p + g) =
      realWeilForm p p + 2 * realWeilForm p g + realWeilForm g g := by
    simp only [map_add, LinearMap.add_apply]
    rw [realWeilForm_symm g p]
    ring
  rw [hsum]
  have hsign := neg_abs_le (realWeilForm p g)
  linarith only [hmix, hnew, hsign]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_shortCell_diagonal_extension
