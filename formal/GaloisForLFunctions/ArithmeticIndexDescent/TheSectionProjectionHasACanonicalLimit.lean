import GaloisForLFunctions.ArithmeticIndexDescent.TheProjectionCostIsBoundedOnEachWindow
import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionComplementCarriesAllNegativeSquares
import GaloisForLFunctions.ArithmeticIndexDescent.FiniteGramDescent
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Completion of a positive arithmetic section space

Finite subsets of one narrow section space form a directed family. Their actual
Weil projections have increasing energy, and the energy gained under refinement
is exactly the energy of the new projected component. Its actual square mass is
at most that increment. The fixed-window source bound controls the entire family.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

variable {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
  (hw : w ≤ fullSectionRatio * atomSpacing N)

include hN hw0 hw

/-- Projection indexed by actual sections rather than a coefficient presentation. -/
def finiteSectionProjection (S : Finset (arithmeticSectionTests N w)) (g : realTests) :
    realTests := arithmeticSectionProjection hN hw0 hw (fun p : S => p.1) g

/-- Completed energy removed by one finite source subspace. -/
def finiteSectionEnergy (S : Finset (arithmeticSectionTests N w)) (g : realTests) : ℝ :=
  realWeilForm (finiteSectionProjection hN hw0 hw S g)
    (finiteSectionProjection hN hw0 hw S g)

theorem finiteSectionProjection_mem (S : Finset (arithmeticSectionTests N w)) (g : realTests) :
    finiteSectionProjection hN hw0 hw S g ∈ arithmeticSectionTests N w :=
  arithmeticSectionProjection_mem hN hw0 hw (fun p : S => p.1) g

theorem finiteSectionEnergy_nonneg (S : Finset (arithmeticSectionTests N w)) (g : realTests) :
    0 ≤ finiteSectionEnergy hN hw0 hw S g :=
  arithmeticSectionProjection_energy_nonneg hN hw0 hw (fun p : S => p.1) g

/-- A section is reproduced once it occurs in the actual finite source family. -/
theorem finiteSectionProjection_reproduces_mem
    {S : Finset (arithmeticSectionTests N w)} {g : arithmeticSectionTests N w} (hg : g ∈ S) :
    finiteSectionProjection hN hw0 hw S g.1 = g.1 := by
  classical
  let i : S := ⟨g, hg⟩
  let c : S → ℝ := fun j => if i = j then 1 else 0
  have hs : realTestSynthesis (fun j : S => j.1.1) c = g.1 := by
    simp [realTestSynthesis, c, ite_smul, i]
  have h := arithmeticSectionProjection_reproduces hN hw0 hw (fun p : S => p.1) c
  rw [hs] at h
  exact h

theorem finiteSectionProjection_pair_self (S : Finset (arithmeticSectionTests N w))
    (g : realTests) :
    realWeilForm (finiteSectionProjection hN hw0 hw S g) g =
      finiteSectionEnergy hN hw0 hw S g := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw (fun p : S => p.1) g).1
  have horth := arithmeticSectionProjection_orthogonal hN hw0 hw (fun p : S => p.1) c g
  rw [← hc, map_sub] at horth
  exact sub_eq_zero.mp horth

/-- A larger source projection retains every pairing already captured by a smaller one. -/
theorem finiteSectionProjection_nested_pair
    {S T : Finset (arithmeticSectionTests N w)} (hST : S ⊆ T) (g : realTests) :
    realWeilForm (finiteSectionProjection hN hw0 hw S g)
      (finiteSectionProjection hN hw0 hw T g) = finiteSectionEnergy hN hw0 hw S g := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw (fun p : S => p.1) g).1
  have horth : realWeilForm (finiteSectionProjection hN hw0 hw S g)
      (g - finiteSectionProjection hN hw0 hw T g) = 0 := by
    change realWeilForm (arithmeticSectionProjection hN hw0 hw (fun p : S => p.1) g) _ = 0
    rw [hc, realWeilForm_synthesis_left]
    apply Finset.sum_eq_zero
    intro i _
    have hi := (arithmeticSectionProjection_spec hN hw0 hw (fun p : T => p.1) g).2
      ⟨i.1, hST i.2⟩
    change realWeilForm i.1.1 (g - finiteSectionProjection hN hw0 hw T g) = 0 at hi
    rw [hi, mul_zero]
  rw [map_sub] at horth
  exact (sub_eq_zero.mp horth).symm.trans (finiteSectionProjection_pair_self hN hw0 hw S g)

/-- Refinement energy is the exact energy of the new actual section component. -/
theorem finiteSectionProjection_increment
    {S T : Finset (arithmeticSectionTests N w)} (hST : S ⊆ T) (g : realTests) :
    realWeilForm
        (finiteSectionProjection hN hw0 hw T g - finiteSectionProjection hN hw0 hw S g)
        (finiteSectionProjection hN hw0 hw T g - finiteSectionProjection hN hw0 hw S g) =
      finiteSectionEnergy hN hw0 hw T g - finiteSectionEnergy hN hw0 hw S g := by
  have h := finiteSectionProjection_nested_pair hN hw0 hw hST g
  dsimp only [finiteSectionEnergy] at h ⊢
  simp only [map_sub, LinearMap.sub_apply]
  rw [realWeilForm_symm (finiteSectionProjection hN hw0 hw T g)
    (finiteSectionProjection hN hw0 hw S g), h]
  ring

/-- The source floor controls refinement in actual L², without coefficient norms. -/
theorem integral_sq_projection_increment_le
    {S T : Finset (arithmeticSectionTests N w)} (hST : S ⊆ T) (g : realTests) :
    (∫ u, ((finiteSectionProjection hN hw0 hw T g).1 u -
      (finiteSectionProjection hN hw0 hw S g).1 u) ^ 2) ≤
      finiteSectionEnergy hN hw0 hw T g - finiteSectionEnergy hN hw0 hw S g := by
  have hmem := (arithmeticSectionTests N w).sub_mem
    (finiteSectionProjection_mem hN hw0 hw T g) (finiteSectionProjection_mem hN hw0 hw S g)
  have hfloor := integral_sq_le_weilPair_arithmeticSection hN hw0 hw
    ⟨finiteSectionProjection hN hw0 hw T g - finiteSectionProjection hN hw0 hw S g, hmem⟩
  change (∫ u, ((finiteSectionProjection hN hw0 hw T g).1 u -
    (finiteSectionProjection hN hw0 hw S g).1 u) ^ 2) ≤ realWeilForm _ _ at hfloor
  rw [finiteSectionProjection_increment hN hw0 hw hST g] at hfloor
  exact hfloor

theorem monotone_finiteSectionEnergy (g : realTests) :
    Monotone (fun S : Finset (arithmeticSectionTests N w) =>
      finiteSectionEnergy hN hw0 hw S g) := by
  intro S T hST
  have h := integral_sq_projection_increment_le hN hw0 hw hST g
  have hnonneg : 0 ≤ ∫ u, ((finiteSectionProjection hN hw0 hw T g).1 u -
      (finiteSectionProjection hN hw0 hw S g).1 u) ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  linarith only [h, hnonneg]

theorem bddAbove_finiteSectionEnergy (g : realTests) :
    BddAbove (Set.range (fun S : Finset (arithmeticSectionTests N w) =>
      finiteSectionEnergy hN hw0 hw S g)) := by
  obtain ⟨B, _, hB⟩ := exists_uniform_arithmeticSectionProjection_energy_bound hN hw0 hw g
  refine ⟨B, ?_⟩
  rintro _ ⟨S, rfl⟩
  exact hB ↥S (fun p : S => p.1)

/-- Energy removed by the completion of the entire fixed arithmetic section space. -/
def sectionCompletionEnergy (g : realTests) : ℝ :=
  ⨆ S : Finset (arithmeticSectionTests N w), finiteSectionEnergy hN hw0 hw S g

theorem finiteSectionEnergy_le_completion (S : Finset (arithmeticSectionTests N w))
    (g : realTests) : finiteSectionEnergy hN hw0 hw S g ≤ sectionCompletionEnergy hN hw0 hw g :=
  le_ciSup (bddAbove_finiteSectionEnergy hN hw0 hw g) S

theorem sectionCompletionEnergy_nonneg (g : realTests) :
    0 ≤ sectionCompletionEnergy hN hw0 hw g :=
  (finiteSectionEnergy_nonneg hN hw0 hw ∅ g).trans
    (finiteSectionEnergy_le_completion hN hw0 hw ∅ g)

/-- Actual finite source energies converge; no convergence premise is introduced. -/
theorem tendsto_finiteSectionEnergy (g : realTests) :
    Tendsto (fun S : Finset (arithmeticSectionTests N w) => finiteSectionEnergy hN hw0 hw S g)
      atTop (𝓝 (sectionCompletionEnergy hN hw0 hw g)) :=
  tendsto_atTop_ciSup (monotone_finiteSectionEnergy hN hw0 hw g)
    (bddAbove_finiteSectionEnergy hN hw0 hw g)

private theorem section_difference_energy_le (p q : arithmeticSectionTests N w) :
    realWeilForm (p.1 - q.1) (p.1 - q.1) ≤
      2 * realWeilForm p.1 p.1 + 2 * realWeilForm q.1 q.1 := by
  have hpos : 0 ≤ realWeilForm (p.1 + q.1) (p.1 + q.1) :=
    (integral_nonneg fun u => sq_nonneg ((p.1 + q.1).1 u)).trans
      (integral_sq_le_weilPair_arithmeticSection hN hw0 hw
        ⟨p.1 + q.1, (arithmeticSectionTests N w).add_mem p.2 q.2⟩)
  have hpar : realWeilForm (p.1 - q.1) (p.1 - q.1) +
      realWeilForm (p.1 + q.1) (p.1 + q.1) =
      2 * realWeilForm p.1 p.1 + 2 * realWeilForm q.1 q.1 := by
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    ring
  linarith only [hpar, hpos]

/-- All finite source projections form a Cauchy net in actual square mass. -/
theorem finiteSectionProjection_square_mass_cauchy (g : realTests) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : Finset (arithmeticSectionTests N w),
      ∀ S T : Finset (arithmeticSectionTests N w), S₀ ⊆ S → S₀ ⊆ T →
        (∫ u, ((finiteSectionProjection hN hw0 hw S g).1 u -
          (finiteSectionProjection hN hw0 hw T g).1 u) ^ 2) < ε := by
  obtain ⟨S₀, hS₀⟩ := exists_lt_of_lt_ciSup
    (show sectionCompletionEnergy hN hw0 hw g - ε / 4 <
      ⨆ S : Finset (arithmeticSectionTests N w), finiteSectionEnergy hN hw0 hw S g by
        change sectionCompletionEnergy hN hw0 hw g - ε / 4 <
          sectionCompletionEnergy hN hw0 hw g
        linarith only [hε])
  refine ⟨S₀, ?_⟩
  intro S T hS hT
  let p := finiteSectionProjection hN hw0 hw S g
  let q := finiteSectionProjection hN hw0 hw T g
  let r := finiteSectionProjection hN hw0 hw S₀ g
  have hp := finiteSectionProjection_mem hN hw0 hw S g
  have hq := finiteSectionProjection_mem hN hw0 hw T g
  have hr := finiteSectionProjection_mem hN hw0 hw S₀ g
  have hfloor := integral_sq_le_weilPair_arithmeticSection hN hw0 hw
    ⟨p - q, (arithmeticSectionTests N w).sub_mem hp hq⟩
  have hquad := section_difference_energy_le hN hw0 hw
    ⟨p - r, (arithmeticSectionTests N w).sub_mem hp hr⟩
    ⟨q - r, (arithmeticSectionTests N w).sub_mem hq hr⟩
  change realWeilForm ((p - r) - (q - r)) ((p - r) - (q - r)) ≤
    2 * realWeilForm (p - r) (p - r) + 2 * realWeilForm (q - r) (q - r) at hquad
  rw [show (p - r) - (q - r) = p - q by abel] at hquad
  have hpinc := finiteSectionProjection_increment hN hw0 hw hS g
  have hqinc := finiteSectionProjection_increment hN hw0 hw hT g
  have hpbound := finiteSectionEnergy_le_completion hN hw0 hw S g
  have hqbound := finiteSectionEnergy_le_completion hN hw0 hw T g
  change realWeilForm (p - r) (p - r) = _ at hpinc
  change realWeilForm (q - r) (q - r) = _ at hqinc
  rw [hpinc, hqinc] at hquad
  change (∫ u, (p.1 u - q.1 u) ^ 2) ≤ realWeilForm (p - q) (p - q) at hfloor
  change (∫ u, (p.1 u - q.1 u) ^ 2) < ε
  linarith only [hfloor, hquad, hpbound, hqbound, hS₀]

/-- Polarization of the completed removal energy. -/
def sectionCompletionPair (g h : realTests) : ℝ :=
  (1 / 4 : ℝ) * (sectionCompletionEnergy hN hw0 hw (g + h) -
    sectionCompletionEnergy hN hw0 hw (g - h))

theorem finiteSectionProjection_polarization
    (S : Finset (arithmeticSectionTests N w)) (g h : realTests) :
    realWeilForm (finiteSectionProjection hN hw0 hw S g)
      (finiteSectionProjection hN hw0 hw S h) =
    (1 / 4 : ℝ) * (finiteSectionEnergy hN hw0 hw S (g + h) -
      finiteSectionEnergy hN hw0 hw S (g - h)) := by
  have hadd : finiteSectionProjection hN hw0 hw S (g + h) =
      finiteSectionProjection hN hw0 hw S g + finiteSectionProjection hN hw0 hw S h :=
    arithmeticSectionProjection_add hN hw0 hw (fun p : S => p.1) g h
  have hsub : finiteSectionProjection hN hw0 hw S (g - h) =
      finiteSectionProjection hN hw0 hw S g - finiteSectionProjection hN hw0 hw S h :=
    map_sub (arithmeticSectionProjectionMap hN hw0 hw (fun p : S => p.1)) g h
  dsimp only [finiteSectionEnergy]
  rw [hadd, hsub]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [realWeilForm_symm (finiteSectionProjection hN hw0 hw S h)
    (finiteSectionProjection hN hw0 hw S g)]
  ring

/-- All mixed removal entries converge, with the same finite source refinement. -/
theorem tendsto_finiteSectionProjection_pair (g h : realTests) :
    Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      realWeilForm (finiteSectionProjection hN hw0 hw S g)
        (finiteSectionProjection hN hw0 hw S h)) atTop
      (𝓝 (sectionCompletionPair hN hw0 hw g h)) := by
  have ht := Filter.Tendsto.const_mul (1 / 4 : ℝ)
    ((tendsto_finiteSectionEnergy hN hw0 hw (g + h)).sub
      (tendsto_finiteSectionEnergy hN hw0 hw (g - h)))
  simpa only [← finiteSectionProjection_polarization, sectionCompletionPair] using ht

theorem sectionCompletionPair_symm (g h : realTests) :
    sectionCompletionPair hN hw0 hw g h = sectionCompletionPair hN hw0 hw h g := by
  have ht := (tendsto_finiteSectionProjection_pair hN hw0 hw h g).congr
    (fun S => realWeilForm_symm (finiteSectionProjection hN hw0 hw S h)
      (finiteSectionProjection hN hw0 hw S g))
  exact tendsto_nhds_unique (tendsto_finiteSectionProjection_pair hN hw0 hw g h) ht

theorem sectionCompletionPair_add_left (f g h : realTests) :
    sectionCompletionPair hN hw0 hw (f + g) h =
      sectionCompletionPair hN hw0 hw f h + sectionCompletionPair hN hw0 hw g h := by
  have ht := (tendsto_finiteSectionProjection_pair hN hw0 hw f h).add
    (tendsto_finiteSectionProjection_pair hN hw0 hw g h)
  apply tendsto_nhds_unique (tendsto_finiteSectionProjection_pair hN hw0 hw (f + g) h)
  exact ht.congr fun S => by
    simp only [finiteSectionProjection, arithmeticSectionProjection_add,
      map_add, LinearMap.add_apply]

theorem sectionCompletionPair_smul_left (a : ℝ) (g h : realTests) :
    sectionCompletionPair hN hw0 hw (a • g) h = a * sectionCompletionPair hN hw0 hw g h := by
  have ht := Filter.Tendsto.const_mul a (tendsto_finiteSectionProjection_pair hN hw0 hw g h)
  apply tendsto_nhds_unique (tendsto_finiteSectionProjection_pair hN hw0 hw (a • g) h)
  exact ht.congr fun S => by
    simp only [finiteSectionProjection, arithmeticSectionProjection_smul,
      map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem sectionCompletionPair_add_right (f g h : realTests) :
    sectionCompletionPair hN hw0 hw f (g + h) =
      sectionCompletionPair hN hw0 hw f g + sectionCompletionPair hN hw0 hw f h := by
  rw [sectionCompletionPair_symm hN hw0 hw f (g + h), sectionCompletionPair_add_left,
    sectionCompletionPair_symm hN hw0 hw g f, sectionCompletionPair_symm hN hw0 hw h f]

theorem sectionCompletionPair_smul_right (a : ℝ) (g h : realTests) :
    sectionCompletionPair hN hw0 hw g (a • h) = a * sectionCompletionPair hN hw0 hw g h := by
  rw [sectionCompletionPair_symm hN hw0 hw g (a • h), sectionCompletionPair_smul_left,
    sectionCompletionPair_symm hN hw0 hw h g]

theorem sectionCompletionPair_self (g : realTests) :
    sectionCompletionPair hN hw0 hw g g = sectionCompletionEnergy hN hw0 hw g :=
  tendsto_nhds_unique (tendsto_finiteSectionProjection_pair hN hw0 hw g g)
    (tendsto_finiteSectionEnergy hN hw0 hw g)

theorem sectionCompletionPair_self_nonneg (g : realTests) :
    0 ≤ sectionCompletionPair hN hw0 hw g g := by
  rw [sectionCompletionPair_self]
  exact sectionCompletionEnergy_nonneg hN hw0 hw g

/-- The removed part is an actual positive semidefinite bilinear form on ambient tests. -/
def sectionCompletionForm : LinearMap.BilinForm ℝ realTests where
  toFun g :=
    { toFun := sectionCompletionPair hN hw0 hw g
      map_add' := sectionCompletionPair_add_right hN hw0 hw g
      map_smul' := fun a h => sectionCompletionPair_smul_right hN hw0 hw a g h }
  map_add' f g := by
    ext h
    exact sectionCompletionPair_add_left hN hw0 hw f g h
  map_smul' a g := by
    ext h
    exact sectionCompletionPair_smul_left hN hw0 hw a g h

/-- The completed residual form retains the original signed pairing after source removal. -/
def completedSectionResidualForm : LinearMap.BilinForm ℝ realTests :=
  realWeilForm - sectionCompletionForm hN hw0 hw

theorem completedSectionResidualForm_symm (g h : realTests) :
    completedSectionResidualForm hN hw0 hw g h = completedSectionResidualForm hN hw0 hw h g := by
  change realWeilForm g h - sectionCompletionPair hN hw0 hw g h =
    realWeilForm h g - sectionCompletionPair hN hw0 hw h g
  rw [realWeilForm_symm g h, sectionCompletionPair_symm hN hw0 hw g h]

theorem completedSectionResidualForm_self_le (g : realTests) :
    completedSectionResidualForm hN hw0 hw g g ≤ realWeilForm g g :=
  sub_le_self _ (sectionCompletionPair_self_nonneg hN hw0 hw g)

/-- The completed removal agrees with the original form on every actual source section. -/
theorem sectionCompletionPair_section_left (g : arithmeticSectionTests N w) (h : realTests) :
    sectionCompletionPair hN hw0 hw g.1 h = realWeilForm g.1 h := by
  classical
  have hevent :
      (fun S : Finset (arithmeticSectionTests N w) =>
        realWeilForm (finiteSectionProjection hN hw0 hw S g.1)
          (finiteSectionProjection hN hw0 hw S h)) =ᶠ[atTop]
      (fun _ => realWeilForm g.1 h) := by
    filter_upwards [eventually_ge_atTop ({g} : Finset (arithmeticSectionTests N w))] with S hS
    have hg : g ∈ S := Finset.singleton_subset_iff.mp hS
    rw [finiteSectionProjection_reproduces_mem hN hw0 hw hg]
    have horth := (arithmeticSectionProjection_spec hN hw0 hw (fun p : S => p.1) h).2 ⟨g, hg⟩
    rw [map_sub] at horth
    exact (sub_eq_zero.mp horth).symm
  have ht := Filter.Tendsto.congr' hevent.symm tendsto_const_nhds
  exact tendsto_nhds_unique (tendsto_finiteSectionProjection_pair hN hw0 hw g.1 h) ht

/-- The completed residual descends through the entire narrow source subspace. -/
theorem completedSectionResidualForm_section_left
    (g : arithmeticSectionTests N w) (h : realTests) :
    completedSectionResidualForm hN hw0 hw g.1 h = 0 := by
  change realWeilForm g.1 h - sectionCompletionPair hN hw0 hw g.1 h = 0
  rw [sectionCompletionPair_section_left, sub_self]

theorem completedSectionResidualForm_section_right
    (g : realTests) (h : arithmeticSectionTests N w) :
    completedSectionResidualForm hN hw0 hw g h.1 = 0 := by
  rw [completedSectionResidualForm_symm, completedSectionResidualForm_section_left]

/-- All mixed residual entries converge in the original completed pairing. -/
theorem tendsto_finiteSectionProjection_residual_pair (g h : realTests) :
    Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      realWeilForm (g - finiteSectionProjection hN hw0 hw S g)
        (h - finiteSectionProjection hN hw0 hw S h)) atTop
      (𝓝 (realWeilForm g h - sectionCompletionPair hN hw0 hw g h)) := by
  have hc : Tendsto (fun _ : Finset (arithmeticSectionTests N w) => realWeilForm g h)
      atTop (𝓝 (realWeilForm g h)) := tendsto_const_nhds
  have ht := hc.sub (tendsto_finiteSectionProjection_pair hN hw0 hw g h)
  exact ht.congr fun S =>
    (arithmeticSectionProjection_residual_pair hN hw0 hw (fun p : S => p.1) g h).symm

/-- Canonical finite residual matrix after completing the entire narrow source space. -/
def completedSectionResidualGram {m : ℕ} (g : Fin m → realTests) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (realWeilForm (g i) (g j) - sectionCompletionPair hN hw0 hw (g i) (g j) : ℝ)

theorem completedSectionResidualGram_isHermitian {m : ℕ} (g : Fin m → realTests) :
    (completedSectionResidualGram hN hw0 hw g).IsHermitian := by
  ext i j
  change (starRingEnd ℂ) (completedSectionResidualForm hN hw0 hw (g j) (g i) : ℂ) =
    (completedSectionResidualForm hN hw0 hw (g i) (g j) : ℂ)
  rw [Complex.conj_ofReal, completedSectionResidualForm_symm]

/-- The canonical residual matrix is an actual mixed-Gram limit. -/
theorem tendsto_completedSectionResidualGram {m : ℕ} (g : Fin m → realTests) (i j : Fin m) :
    Tendsto (fun S : Finset (arithmeticSectionTests N w) =>
      complexWeilMixed (fun k => g k - finiteSectionProjection hN hw0 hw S (g k))
        (fun k => g k - finiteSectionProjection hN hw0 hw S (g k)) i j) atTop
      (𝓝 (completedSectionResidualGram hN hw0 hw g i j)) :=
  (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_finiteSectionProjection_residual_pair hN hw0 hw (g i) (g j))

/-- Each negative square of the completed source complement is witnessed at a finite refinement. -/
theorem eventually_negIndex_completedSectionResidual_le {m : ℕ} (g : Fin m → realTests) :
    ∀ᶠ S : Finset (arithmeticSectionTests N w) in atTop,
      HTGeometry.hermNegIndex (completedSectionResidualGram hN hw0 hw g) ≤
        HTGeometry.hermNegIndex (complexWeilMixed
          (fun k => g k - finiteSectionProjection hN hw0 hw S (g k))
          (fun k => g k - finiteSectionProjection hN hw0 hw S (g k))) :=
  eventually_negIndex_limit_le _ _ (tendsto_completedSectionResidualGram hN hw0 hw g)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.finiteSectionProjection_square_mass_cauchy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.tendsto_completedSectionResidualGram
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_negIndex_completedSectionResidual_le
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completedSectionResidualForm_section_left
