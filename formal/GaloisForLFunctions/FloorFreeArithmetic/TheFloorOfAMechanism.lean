import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations
import GaloisForLFunctions.SquareRootThreshold.EveryWidthDecidesTheCriticalLine
import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCriticalProjectionPreservesTheCounts

/-!
# The floor of a mechanism

A **mechanism** is a property of zero configurations: the structures a method uses together
with the estimate it proves. It **excludes beyond** a depth `δ` if every configuration with the
property has all zeros at real part `≤ ½ + δ`. Its **floor** is the infimum of such depths, and
a **model at depth `δ`** is a configuration with the property and a zero of that depth.

* A model bounds the floor from below; exclusion bounds it from above
  (`le_floor_of_hasModelAt`, `floor_le_of_excludesBeyond`).
* The floor is zero exactly when the mechanism forces purity
  (`floor_eq_zero_iff_floorFree`, `floorFree_iff_forall_pure`). A mechanism with a model of
  positive depth proves purity of nothing by itself, and one with a finite-stratum model does not
  prove the abscissa law (`not_forall_pure_of_hasModelAt`,
  `not_forall_abscissaLaw_of_hasFiniteStratumModel`).
* Strengthening a mechanism lowers its floor (`floor_anti`).
* First row of the census: what holds for every tempered configuration with the reflection
  symmetry has floor `½`, the whole strip, and admits finite strata
  (`floor_temperedConfig`, `hasFiniteStratumModel_temperedConfig`). This is the class in which
  every identity of the explicit formula lives.
* Second row, the exchange rate: a floor `−C e^{σv}` of the spline two-bump form at large lags
  is a mechanism with floor exactly `σ` (`floor_exponentialFloor`). A size estimate with a
  positive exponent is a half-plane and nothing more.
* Third row: a mechanism that reads a configuration only through its ordinate counts and holds
  on every pure configuration holds on every configuration; its floor is `½`
  (`floor_eq_half_of_countInvariant`). Counting laws are blind to the depth.
-/

open Complex Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-- A mechanism: a property of zero configurations. -/
abbrev Mechanism := ZeroConfig → Prop

/-- The mechanism excludes every zero of depth beyond `δ`. -/
def ExcludesBeyond (M : Mechanism) (δ : ℝ) : Prop :=
  ∀ Z, M Z → ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + δ

/-- A model at depth `δ`: a configuration with the property and a zero of depth `δ`. -/
def HasModelAt (M : Mechanism) (δ : ℝ) : Prop :=
  ∃ Z, M Z ∧ ∃ ρ ∈ Z.carrier, ρ.re = 1 / 2 + δ

/-- A finite-stratum model: a configuration with the property and a finite nonempty set of
zeros right of the critical line. -/
def HasFiniteStratumModel (M : Mechanism) : Prop :=
  ∃ Z, M Z ∧ (rightOf Z 0).Finite ∧ (rightOf Z 0).Nonempty

/-- The floor of a mechanism: the least depth beyond which it excludes. -/
def floor (M : Mechanism) : ℝ := sInf {δ : ℝ | 0 ≤ δ ∧ ExcludesBeyond M δ}

/-- A mechanism without a floor: it excludes every positive depth. -/
def FloorFree (M : Mechanism) : Prop := ExcludesBeyond M 0

variable {M M' : Mechanism} {δ δ' : ℝ}

/-! ### General laws -/

theorem ExcludesBeyond.mono (h : ExcludesBeyond M δ) (hδ : δ ≤ δ') : ExcludesBeyond M δ' :=
  fun Z hZ ρ hρ => (h Z hZ ρ hρ).trans (by linarith only [hδ])

theorem ExcludesBeyond.anti (h : ExcludesBeyond M δ) (hM : ∀ Z, M' Z → M Z) :
    ExcludesBeyond M' δ := fun Z hZ => h Z (hM Z hZ)

/-- Every mechanism excludes beyond the edge of the strip. -/
theorem excludesBeyond_half (M : Mechanism) : ExcludesBeyond M (1 / 2) := fun Z _ ρ hρ => by
  have := (Z.strip ρ hρ).2
  linarith only [this]

theorem floor_set_nonempty (M : Mechanism) :
    {δ : ℝ | 0 ≤ δ ∧ ExcludesBeyond M δ}.Nonempty :=
  ⟨1 / 2, by norm_num, excludesBeyond_half M⟩

theorem floor_set_bddBelow (M : Mechanism) : BddBelow {δ : ℝ | 0 ≤ δ ∧ ExcludesBeyond M δ} :=
  ⟨0, fun _ h => h.1⟩

theorem floor_nonneg (M : Mechanism) : 0 ≤ floor M :=
  le_csInf (floor_set_nonempty M) fun _ h => h.1

/-- Exclusion bounds the floor from above. -/
theorem floor_le_of_excludesBeyond (hδ : 0 ≤ δ) (h : ExcludesBeyond M δ) : floor M ≤ δ :=
  csInf_le (floor_set_bddBelow M) ⟨hδ, h⟩

theorem floor_le_half (M : Mechanism) : floor M ≤ 1 / 2 :=
  floor_le_of_excludesBeyond (by norm_num) (excludesBeyond_half M)

/-- A model bounds the floor from below. -/
theorem le_floor_of_hasModelAt (h : HasModelAt M δ) : δ ≤ floor M := by
  obtain ⟨Z, hZ, ρ, hρ, hre⟩ := h
  refine le_csInf (floor_set_nonempty M) fun δ' hδ' => ?_
  have := hδ'.2 Z hZ ρ hρ
  linarith only [this, hre]

/-- A stronger mechanism has a lower floor. -/
theorem floor_anti (hM : ∀ Z, M' Z → M Z) : floor M' ≤ floor M :=
  le_csInf (floor_set_nonempty M) fun _ hδ =>
    floor_le_of_excludesBeyond hδ.1 (hδ.2.anti hM)

/-- Every depth above the floor is excluded. -/
theorem excludesBeyond_of_floor_lt (h : floor M < δ) : ExcludesBeyond M δ := by
  obtain ⟨δ', hδ', hlt⟩ := exists_lt_of_csInf_lt (floor_set_nonempty M) h
  exact hδ'.2.mono hlt.le

/-- Floor-free mechanisms are those that force purity. -/
theorem floorFree_iff_forall_pure : FloorFree M ↔ ∀ Z, M Z → Pure Z := by
  constructor
  · intro h Z hZ
    rw [pure_iff_forall_re_le]
    intro ρ hρ
    simpa using h Z hZ ρ hρ
  · intro h Z hZ ρ hρ
    rw [h Z hZ ρ hρ, add_zero]

/-- The floor vanishes exactly for the floor-free mechanisms. -/
theorem floor_eq_zero_iff_floorFree : floor M = 0 ↔ FloorFree M := by
  constructor
  · intro h0 Z hZ ρ hρ
    by_contra hgt
    have hpos : 0 < ρ.re - 1 / 2 := by linarith only [lt_of_not_ge hgt]
    have hex : ExcludesBeyond M ((ρ.re - 1 / 2) / 2) :=
      excludesBeyond_of_floor_lt (by rw [h0]; linarith only [hpos])
    have := hex Z hZ ρ hρ
    linarith only [this, hpos]
  · intro h
    exact le_antisymm (floor_le_of_excludesBeyond le_rfl h) (floor_nonneg M)

/-- A model of positive depth: the mechanism does not force purity. -/
theorem not_forall_pure_of_hasModelAt (hδ : 0 < δ) (h : HasModelAt M δ) :
    ¬ ∀ Z, M Z → Pure Z := by
  intro hall
  obtain ⟨Z, hZ, ρ, hρ, hre⟩ := h
  have := hall Z hZ ρ hρ
  linarith only [this, hre, hδ]

/-- A finite-stratum model: the mechanism does not force the abscissa law. -/
theorem not_forall_abscissaLaw_of_hasFiniteStratumModel (h : HasFiniteStratumModel M) :
    ¬ ∀ Z, M Z → AbscissaLaw Z := by
  intro hall
  obtain ⟨Z, hZ, hfin, ρ, hρ, hgt⟩ := h
  have := hall Z hZ 0 le_rfl hfin ρ hρ
  linarith only [this, hgt]

/-! ### The census begins: tempered configurations -/

/-- The isolated pair is a model of temperedness at every depth of the strip. -/
theorem hasModelAt_temperedConfig (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    HasModelAt TemperedConfig δ :=
  ⟨isolatedPairConfig one_pos hδ hδ' 0, temperedConfig_isolatedPairConfig one_pos hδ hδ' 0,
    offLinePoint δ 0, Or.inl (Or.inr rfl), rfl⟩

/-- **Temperedness and the reflection symmetry have floor `½`.** -/
theorem floor_temperedConfig : floor TemperedConfig = 1 / 2 :=
  le_antisymm (floor_le_half _)
    (le_floor_of_hasModelAt (hasModelAt_temperedConfig (by norm_num) le_rfl))

/-- The zeros of the isolated pair right of the line: the one point `½ + δ + iγ₀`. -/
theorem rightOf_isolatedPairConfig {L : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (γ₀ : ℝ) : rightOf (isolatedPairConfig hL hδ hδ' γ₀) 0 = {offLinePoint δ γ₀} := by
  ext ρ
  simp only [rightOf, isolatedPairConfig, Set.mem_setOf_eq, Set.mem_union, Set.mem_range,
    Set.mem_singleton_iff, add_zero]
  constructor
  · rintro ⟨((⟨k, rfl⟩ | h) | h), hre⟩
    · simp [RHTower.verticalLatticePoint] at hre
    · exact h
    · subst h
      simp only [offLinePoint] at hre
      linarith only [hre, hδ]
  · rintro rfl
    exact ⟨Or.inl (Or.inr rfl), by simp only [offLinePoint]; linarith only [hδ]⟩

/-- **Temperedness and the reflection symmetry admit finite strata.** -/
theorem hasFiniteStratumModel_temperedConfig : HasFiniteStratumModel TemperedConfig := by
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have hδ' : (1 / 4 : ℝ) ≤ 1 / 2 := by norm_num
  refine ⟨isolatedPairConfig one_pos hδ hδ' 0, temperedConfig_isolatedPairConfig one_pos hδ hδ' 0,
    ?_, ?_⟩
  · rw [rightOf_isolatedPairConfig]
    exact Set.finite_singleton _
  · rw [rightOf_isolatedPairConfig]
    exact Set.singleton_nonempty _

/-- No statement that holds for every tempered configuration gives the abscissa law or purity:
the explicit formula with its archimedean density is such a statement. -/
theorem not_forall_abscissaLaw_of_tempered :
    ¬ ∀ Z : ZeroConfig, TemperedConfig Z → AbscissaLaw Z :=
  not_forall_abscissaLaw_of_hasFiniteStratumModel hasFiniteStratumModel_temperedConfig

/-! ### The floor of a size estimate is its exponent -/

/-- The mechanism "floor of exponent `σ`": a tempered configuration inside the open strip whose
polar-free spline two-bump form is at least `−C e^{σv}` at all large lags `v`. -/
def ExponentialFloor (σ : ℝ) : Mechanism := fun Z =>
  TemperedConfig Z ∧ (∀ ρ ∈ Z.carrier, 0 < ρ.re) ∧ (∀ ρ ∈ Z.carrier, ρ.re < 1) ∧
    ∃ C V : ℝ, ∀ v : ℝ, V ≤ v →
      -(C * Real.exp (σ * v)) ≤
        (Z.W (twoBump (splinePolarFree 1) v (-1)) (twoBump (splinePolarFree 1) v (-1))).re

/-- A floor of exponent `σ` excludes every depth beyond `σ`. -/
theorem excludesBeyond_exponentialFloor {σ : ℝ} (hσ : 0 ≤ σ) :
    ExcludesBeyond (ExponentialFloor σ) σ := fun Z hZ =>
  (re_le_iff_polarFree_lag_splineTwoBump_ge_neg_exp Z hZ.1 hZ.2.1 hZ.2.2.1 one_pos hσ).mpr
    hZ.2.2.2

/-- The isolated pair of depth `σ` satisfies the floor of exponent `σ`. -/
theorem hasModelAt_exponentialFloor {σ : ℝ} (hσ : 0 < σ) (hσ' : σ < 1 / 2) :
    HasModelAt (ExponentialFloor σ) σ := by
  have hle : ∀ ρ ∈ (isolatedPairConfig one_pos hσ hσ'.le 0).carrier, ρ.re ≤ 1 / 2 + σ := by
    intro ρ hρ
    by_cases h : 1 / 2 + 0 < ρ.re
    · have hm : ρ ∈ rightOf (isolatedPairConfig one_pos hσ hσ'.le 0) 0 := ⟨hρ, h⟩
      rw [rightOf_isolatedPairConfig] at hm
      rw [Set.mem_singleton_iff.mp hm]
      exact le_of_eq rfl
    · linarith only [not_lt.mp h, hσ]
  have hge : ∀ ρ ∈ (isolatedPairConfig one_pos hσ hσ'.le 0).carrier, 1 / 2 - σ ≤ ρ.re := by
    intro ρ hρ
    have h := hle _ ((isolatedPairConfig one_pos hσ hσ'.le 0).reflect_mem ρ hρ)
    rw [ArithmeticCastelnuovoSeveri.re_reflect] at h
    linarith only [h]
  have hgt : ∀ ρ ∈ (isolatedPairConfig one_pos hσ hσ'.le 0).carrier, 0 < ρ.re :=
    fun ρ hρ => by linarith only [hge ρ hρ, hσ']
  have hlt : ∀ ρ ∈ (isolatedPairConfig one_pos hσ hσ'.le 0).carrier, ρ.re < 1 :=
    fun ρ hρ => by linarith only [hle ρ hρ, hσ']
  have hT := temperedConfig_isolatedPairConfig one_pos hσ hσ'.le 0
  exact ⟨isolatedPairConfig one_pos hσ hσ'.le 0,
    ⟨hT, hgt, hlt, (re_le_iff_polarFree_lag_splineTwoBump_ge_neg_exp _ hT hgt hlt one_pos
      hσ.le).mp hle⟩, offLinePoint σ 0, Or.inl (Or.inr rfl), rfl⟩

/-- **The floor of a size estimate is its exponent.** For `0 ≤ σ < ½` the mechanism "floor of
exponent `σ`" has floor exactly `σ`. -/
theorem floor_exponentialFloor {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    floor (ExponentialFloor σ) = σ := by
  refine le_antisymm (floor_le_of_excludesBeyond hσ (excludesBeyond_exponentialFloor hσ)) ?_
  rcases hσ.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact floor_nonneg _
  · exact le_floor_of_hasModelAt (hasModelAt_exponentialFloor hpos hσ')

/-! ### Ordinate counts are blind to the depth -/

/-- A mechanism that reads a configuration only through its ordinate counts with multiplicity. -/
def CountInvariant (M : Mechanism) : Prop :=
  ∀ Z Z' : ZeroConfig, (∀ T₁ T₂ : ℝ, Z.N T₁ T₂ = Z'.N T₁ T₂) → M Z → M Z'

/-- A count-invariant mechanism that holds on the projection of a configuration to the line
holds on the configuration: the projection keeps every ordinate count. -/
theorem of_criticalProjection_of_countInvariant (hM : CountInvariant M) {Z : ZeroConfig}
    (h : M (criticalProjectionConfig Z)) : M Z :=
  hM _ _ (fun T₁ T₂ => criticalProjectionConfig_N Z T₁ T₂) h

/-- **Counting laws have floor `½`.** A mechanism that reads only the ordinate counts and holds
on every pure configuration holds on every configuration. -/
theorem floor_eq_half_of_countInvariant (hM : CountInvariant M)
    (hpure : ∀ Z : ZeroConfig, Pure Z → M Z) : floor M = 1 / 2 := by
  have hall : ∀ Z : ZeroConfig, M Z := fun Z =>
    of_criticalProjection_of_countInvariant hM
      (hpure _ (criticalProjectionConfig_onLine Z))
  refine le_antisymm (floor_le_half M) (le_floor_of_hasModelAt ?_)
  exact ⟨pairConfig 1 (by norm_num) (by norm_num), hall _, 1, Or.inl rfl, by norm_num⟩

end GaloisForLFunctions.FloorFreeArithmetic
