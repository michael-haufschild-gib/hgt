import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDegreeFiltrationOfTheHodgeDefect
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations

/-!
# The visibility degree of an isolated off-line pair

**Degree-`a` Hodge index is Weil positivity at aperture `a`** (`hodgeDefectAt_eq_zero_iff`): on a
tempered configuration the Hodge defect at degree `a` vanishes iff `Re W(f, f) ≥ 0` for every `C²`
test supported in `[−a, a]`. So every visibility law for the Weil form is a statement about the
degree filtration of the Hodge defect.

For the isolated pair `½ ± δ + iγ₀` in the doubled on-line lattice of spacing `2π/L`
(`SquareRootThreshold.isolatedPairConfig`, one zero right of the line) the visibility law
`isolatedPairConfig_weil_nonneg_iff` becomes an exact **degree law** (`hodgeDefectAt_isolatedPair`):
for `0 < a ≤ L/2`

    hodgeDefectAt a = 0   if sinh(2δa)/δ ≤ 2L + 2a,       hodgeDefectAt a = 1   otherwise,

and the total defect is `1` (`iSup_hodgeDefectAt_isolatedPair`). The off-line cycle is seen
exactly from the degree at which the pair energy `sinh(2δa)/(2δ) − a` exceeds the background
density `L`: deep pairs at degree about `log(4δL)/(2δ)`, shallow pairs (`sinh(δL) ≤ 3δL`) not
below `L/2`.

**Hiding over `ℚ`** (`exists_hidden_at_degree`): for every degree `a` and depth `δ` there is a
configuration with a zero right of the line and Hodge defect `0` at degree `a`. This is the
analogue of the finite-field window law (`exists_hidden_on_window`): no finite degree certifies
the Hodge index for all configurations, and the degree at which an off-line zero is seen depends
on the density of the zeros around it.
-/

open Complex Set
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig isolatedPairConfig offLinePoint
  temperedConfig_isolatedPairConfig isolatedPairConfig_weil_nonneg_iff)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- **Degree-`a` Hodge index is Weil positivity at aperture `a`.** -/
theorem hodgeDefectAt_eq_zero_iff (Z : ZeroConfig) (hZ : TemperedConfig Z) (a : ℝ) :
    hodgeDefectAt Z a = 0 ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re := by
  constructor
  · intro h0 f hf hfs
    by_contra hneg
    push Not at hneg
    -- the one-test family has a negative square
    set F : Fin 1 → ℝ → ℂ := fun _ => f
    have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfs
    have hq : hermQuad (zeroGram Z F) (fun _ => 1) < 0 := by
      rw [hermQuad_zeroGram_of_tempered Z hZ F (fun _ => hf) (fun _ => hfc)]
      simpa [F] using hneg
    have hne : hermNegIndex (zeroGram Z F) ≠ 0 := fun h =>
      absurd (hermQuad_nonneg_of_negIndex_eq_zero h _) (not_le.mpr hq)
    have hle := le_hodgeDefectAt Z F (a := a) fun _ => ⟨hf, hfs⟩
    rw [h0, nonpos_iff_eq_zero, Nat.cast_eq_zero] at hle
    exact hne hle
  · intro h
    refine le_antisymm (iSup₂_le fun _ f => iSup_le fun hf => ?_) zero_le
    have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hf i).2
    rw [negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_, Nat.cast_zero]
    rw [hermQuad_zeroGram_of_tempered Z hZ f (fun i => (hf i).1) hfc]
    refine h _ (contDiff_sum_smul f (fun i => (hf i).1) _) (closure_minimal (fun u hu => ?_)
      isClosed_Icc)
    by_contra hout
    apply hu
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : f i u = 0 := image_eq_zero_of_notMem_tsupport fun h => hout ((hf i).2 h)
    simp [this]

section IsolatedPair

variable {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ)

/-- The isolated pair configuration has exactly one zero right of the line, `½ + δ + iγ₀`. -/
theorem rightZeros_isolatedPair :
    rightZeros (isolatedPairConfig hL hδ hδ' γ₀) = {offLinePoint δ γ₀} := by
  ext ρ
  simp only [rightZeros, isolatedPairConfig, Set.mem_setOf_eq, Set.mem_union, Set.mem_range,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨((⟨k, rfl⟩ | h) | h), hre⟩
    · simp [RHTower.verticalLatticePoint] at hre
    · exact h
    · subst h
      simp only [offLinePoint] at hre
      linarith
  · rintro rfl
    exact ⟨Or.inl (Or.inr rfl), by simp only [offLinePoint]; linarith⟩

theorem encard_rightZeros_isolatedPair :
    (rightZeros (isolatedPairConfig hL hδ hδ' γ₀)).encard = 1 := by
  rw [rightZeros_isolatedPair, Set.encard_singleton]

/-- **The degree law of an isolated pair.** Below the Nyquist aperture `L/2` the Hodge defect is
`0` while `sinh(2δa)/δ ≤ 2L + 2a` and `1` afterwards. -/
theorem hodgeDefectAt_isolatedPair {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    hodgeDefectAt (isolatedPairConfig hL hδ hδ' γ₀) a =
      if Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a then 0 else 1 := by
  have hZ := temperedConfig_isolatedPairConfig hL hδ hδ' γ₀
  split_ifs with h
  · exact (hodgeDefectAt_eq_zero_iff _ hZ a).mpr
      ((isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ ha haL).mpr h)
  · have hne : hodgeDefectAt (isolatedPairConfig hL hδ hδ' γ₀) a ≠ 0 := fun h0 =>
      h ((isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ ha haL).mp
        ((hodgeDefectAt_eq_zero_iff _ hZ a).mp h0))
    have hle := hodgeDefectAt_le _ hZ a
    rw [encard_rightZeros_isolatedPair] at hle
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

/-- The total Hodge defect of the isolated pair configuration is `1`. -/
theorem iSup_hodgeDefectAt_isolatedPair :
    ⨆ a, hodgeDefectAt (isolatedPairConfig hL hδ hδ' γ₀) a = 1 := by
  rw [iSup_hodgeDefectAt _ (temperedConfig_isolatedPairConfig hL hδ hδ' γ₀),
    encard_rightZeros_isolatedPair]

end IsolatedPair

/-- **Hiding over `ℚ`.** For every degree `a > 0` and depth `δ ∈ (0, ½]` there is a tempered
configuration with a zero right of the line whose Hodge defect vanishes at degree `a`. -/
theorem exists_hidden_at_degree {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ (rightZeros Z).encard = 1 ∧ hodgeDefectAt Z a = 0 := by
  set L : ℝ := max (2 * a) (Real.sinh (2 * δ * a) / δ) with hLdef
  have hL : 0 < L := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨isolatedPairConfig hL hδ hδ' 0, temperedConfig_isolatedPairConfig hL hδ hδ' 0,
    encard_rightZeros_isolatedPair hL hδ hδ' 0, ?_⟩
  have haL : a ≤ L / 2 := by have := le_max_left (2 * a) (Real.sinh (2 * δ * a) / δ); linarith
  rw [hodgeDefectAt_isolatedPair hL hδ hδ' 0 ha haL, if_pos]
  have := le_max_right (2 * a) (Real.sinh (2 * δ * a) / δ)
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
