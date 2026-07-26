/-
# Localized mass and the first half of the double large sieve

Finite coefficients placed on normalized localization boxes define a
piecewise-constant mass.  Expanding its square turns the integral into
intersection volumes.  Two boxes can intersect only for a sharp
scaled-near pair, giving an unconditional `L²` bound by the corresponding
weighted spacing energy.
-/
import GaloisForLFunctions.RHTower.BourgainBoxLocalization

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

theorem measurableSet_bourgainLocalBox
    (Y L x : BourgainPhaseSpace) :
    MeasurableSet (bourgainLocalBox Y L x) := by
  unfold bourgainLocalBox
  exact MeasurableSet.univ_pi fun j => measurableSet_Ioc

theorem volume_bourgainLocalBox_ne_top
    (Y L x : BourgainPhaseSpace) :
    volume (bourgainLocalBox Y L x) ≠ ⊤ := by
  unfold bourgainLocalBox
  rw [Real.volume_pi_Ioc]
  exact ENNReal.prod_ne_top fun j hj => ENNReal.ofReal_ne_top

/-- Nonnegative mass obtained by putting weight `a i` on the local box
centered at `p i`. -/
def bourgainLocalBoxMass
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (z : BourgainPhaseSpace) : ℝ := by
  classical
  exact ∑ i : ι,
    if z ∈ bourgainLocalBox Y L (p i) then a i else 0

def bourgainLocalBoxPairTerm
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (i j : ι) (z : BourgainPhaseSpace) : ℝ := by
  classical
  exact if z ∈ bourgainLocalBox Y L (p i) ∩
      bourgainLocalBox Y L (p j)
    then a i * a j else 0

def bourgainScaledNearPairWeight
    {ι : Type*} [Fintype ι]
    (Y : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (i j : ι) : ℝ := by
  classical
  exact if BourgainScaledNear Y (p i) (p j)
    then a i * a j else 0

theorem bourgainLocalBoxMass_sq
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (z : BourgainPhaseSpace) :
    bourgainLocalBoxMass Y L p a z ^ (2 : ℕ) =
      ∑ i : ι, ∑ j : ι,
        bourgainLocalBoxPairTerm Y L p a i j z := by
  classical
  unfold bourgainLocalBoxMass
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hi' : z ∈ bourgainLocalBox Y L (p i)
  · by_cases hj' : z ∈ bourgainLocalBox Y L (p j)
    · simp [hi', hj', bourgainLocalBoxPairTerm]
    · simp [hi', hj', bourgainLocalBoxPairTerm]
  · simp [hi', bourgainLocalBoxPairTerm]

theorem integrable_bourgainLocalBoxPairTerm
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (i j : ι) :
    Integrable (bourgainLocalBoxPairTerm Y L p a i j) := by
  classical
  let S :=
    bourgainLocalBox Y L (p i) ∩ bourgainLocalBox Y L (p j)
  have hS : MeasurableSet S :=
    (measurableSet_bourgainLocalBox Y L (p i)).inter
      (measurableSet_bourgainLocalBox Y L (p j))
  have hfin : volume S ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (volume_bourgainLocalBox_ne_top Y L (p i))
      (measure_mono Set.inter_subset_left)
  have hintOn :
      IntegrableOn (fun _ : BourgainPhaseSpace => a i * a j) S :=
    integrableOn_const (C := a i * a j) hfin (by finiteness)
  have hint :
      Integrable (S.indicator (fun _ => a i * a j)) :=
    hintOn.integrable_indicator hS
  have heq :
      bourgainLocalBoxPairTerm Y L p a i j =
        S.indicator (fun _ => a i * a j) := by
    funext z
    by_cases hz : z ∈ S
    · simp [bourgainLocalBoxPairTerm, S, hz]
    · simp [bourgainLocalBoxPairTerm, S, hz]
  rw [heq]
  exact hint

theorem integrable_bourgainLocalBoxMass_sq
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) :
    Integrable
      (fun z => bourgainLocalBoxMass Y L p a z ^ (2 : ℕ)) := by
  rw [show
      (fun z => bourgainLocalBoxMass Y L p a z ^ (2 : ℕ)) =
        fun z => ∑ i : ι, ∑ j : ι,
          bourgainLocalBoxPairTerm Y L p a i j z by
    funext z
    exact bourgainLocalBoxMass_sq Y L p a z]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact integrable_bourgainLocalBoxPairTerm Y L p a i j

theorem integral_bourgainLocalBoxPairTerm_le
    {ι : Type*} [Fintype ι]
    {Y L : BourgainPhaseSpace} (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (hY : ∀ j, 0 < Y j)
    (hL : ∀ j, 0 < L j) (ha : ∀ i, 0 ≤ a i)
    (i j : ι) :
    (∫ z : BourgainPhaseSpace,
      bourgainLocalBoxPairTerm Y L p a i j z) ≤
      (∏ k : Fin 4,
        (2 * bourgainLocalizationEpsilon (Y k) / L k)) *
        bourgainScaledNearPairWeight Y p a i j := by
  classical
  let S :=
    bourgainLocalBox Y L (p i) ∩ bourgainLocalBox Y L (p j)
  have hS : MeasurableSet S :=
    (measurableSet_bourgainLocalBox Y L (p i)).inter
      (measurableSet_bourgainLocalBox Y L (p j))
  rw [show
      bourgainLocalBoxPairTerm Y L p a i j =
      S.indicator (fun _ => a i * a j) by
    funext z
    by_cases hz : z ∈ S
    · simp [bourgainLocalBoxPairTerm, S, hz]
    · simp [bourgainLocalBoxPairTerm, S, hz]]
  rw [integral_indicator_const _ hS, smul_eq_mul]
  by_cases hnear : BourgainScaledNear Y (p i) (p j)
  · simp only [bourgainScaledNearPairWeight, hnear, ↓reduceIte]
    have hmeasure :
        volume.real S ≤ volume.real (bourgainLocalBox Y L (p i)) := by
      rw [Measure.real, Measure.real]
      exact ENNReal.toReal_mono
        (volume_bourgainLocalBox_ne_top Y L (p i))
        (measure_mono Set.inter_subset_left)
    have hweight : 0 ≤ a i * a j :=
      mul_nonneg (ha i) (ha j)
    calc
      volume.real S * (a i * a j) ≤
          volume.real (bourgainLocalBox Y L (p i)) * (a i * a j) :=
        mul_le_mul_of_nonneg_right hmeasure hweight
      _ = (∏ k : Fin 4,
            (2 * bourgainLocalizationEpsilon (Y k) / L k)) *
            (a i * a j) := by
        rw [Measure.real,
          volume_bourgainLocalBox_toReal hY hL]
  · simp only [bourgainScaledNearPairWeight, hnear, ↓reduceIte, mul_zero]
    have hempty : S = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨z, hz⟩
      exact hnear
        (bourgainScaledNear_of_mem_localBoxes hY hL hz.1 hz.2)
    simp [hempty]

/-- Localized-mass `L²` bound by sharp weighted spacing energy. -/
theorem integral_bourgainLocalBoxMass_sq_le
    {ι : Type*} [Fintype ι]
    {Y L : BourgainPhaseSpace} (p : ι → BourgainPhaseSpace)
    (a : ι → ℝ) (hY : ∀ j, 0 < Y j)
    (hL : ∀ j, 0 < L j) (ha : ∀ i, 0 ≤ a i) :
    (∫ z : BourgainPhaseSpace,
        bourgainLocalBoxMass Y L p a z ^ (2 : ℕ)) ≤
      (∏ k : Fin 4,
        (2 * bourgainLocalizationEpsilon (Y k) / L k)) *
        bourgainWeightedScaledNearEnergy Y p a := by
  classical
  rw [show
      (fun z => bourgainLocalBoxMass Y L p a z ^ (2 : ℕ)) =
        fun z => ∑ i : ι, ∑ j : ι,
          bourgainLocalBoxPairTerm Y L p a i j z by
    funext z
    exact bourgainLocalBoxMass_sq Y L p a z]
  unfold bourgainWeightedScaledNearEnergy
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      exact
        integral_bourgainLocalBoxPairTerm_le p a hY hL ha i j
    · intro j hj
      exact integrable_bourgainLocalBoxPairTerm Y L p a i j
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact integrable_bourgainLocalBoxPairTerm Y L p a i j

end

end RHTower
