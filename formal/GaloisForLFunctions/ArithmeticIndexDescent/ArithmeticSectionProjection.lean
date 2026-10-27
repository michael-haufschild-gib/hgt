import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionsHaveOnlyPresentationRadicals

/-!
# Orthogonal removal of a narrow arithmetic section space

Every ambient real test has a unique actual section in a prescribed finite narrow
section span with the same mixed Weil pairings. Redundant coefficients do not
affect this section. Subtracting it is orthogonal removal inside the original
completed Weil form, and its residual Gram is the exact Schur complement.
-/

open Matrix MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

variable {ι : Type*} [Fintype ι] {N : ℕ} (hN : 1 ≤ N)
  {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
  (f : ι → arithmeticSectionTests N w)

/-- A finite narrow section span has a unique actual Weil-orthogonal projection of every test. -/
theorem arithmeticSection_exists_unique_projection (g : realTests) :
    ∃! p : realTests,
      (∃ c : ι → ℝ, p = realTestSynthesis (fun i => (f i).1) c) ∧
        ∀ i, realWeilForm (f i).1 (g - p) = 0 := by
  obtain ⟨c, hc⟩ := arithmeticSection_exists_mixed_lift hN hw0 hw f g
  let p := realTestSynthesis (fun i => (f i).1) c
  have hp (i : ι) : realWeilForm (f i).1 (g - p) = 0 := by
    rw [map_sub, ← realWeilMixed_mulVec]
    exact sub_eq_zero.mpr (congrFun hc i).symm
  refine ⟨p, ⟨⟨c, rfl⟩, hp⟩, ?_⟩
  rintro q ⟨⟨d, rfl⟩, hq⟩
  apply arithmeticSection_lift_unique_test hN hw0 hw f
  funext i
  have hd := hq i
  rw [map_sub, ← realWeilMixed_mulVec] at hd
  exact (sub_eq_zero.mp hd).symm.trans (congrFun hc i).symm

/-- The actual projected section, independent of any nonunique coefficient lift. -/
def arithmeticSectionProjection (g : realTests) : realTests :=
  Classical.choose (arithmeticSection_exists_unique_projection hN hw0 hw f g)

theorem arithmeticSectionProjection_spec (g : realTests) :
    (∃ c : ι → ℝ,
      arithmeticSectionProjection hN hw0 hw f g = realTestSynthesis (fun i => (f i).1) c) ∧
    ∀ i, realWeilForm (f i).1 (g - arithmeticSectionProjection hN hw0 hw f g) = 0 :=
  (Classical.choose_spec (arithmeticSection_exists_unique_projection hN hw0 hw f g)).1

theorem arithmeticSectionProjection_unique (g p : realTests)
    (hp : ∃ c : ι → ℝ, p = realTestSynthesis (fun i => (f i).1) c)
    (horth : ∀ i, realWeilForm (f i).1 (g - p) = 0) :
    p = arithmeticSectionProjection hN hw0 hw f g :=
  (Classical.choose_spec (arithmeticSection_exists_unique_projection hN hw0 hw f g)).2
    p ⟨hp, horth⟩

/-- Every old section combination annihilates the new residual. -/
theorem arithmeticSectionProjection_orthogonal (c : ι → ℝ) (g : realTests) :
    realWeilForm (realTestSynthesis (fun i => (f i).1) c)
      (g - arithmeticSectionProjection hN hw0 hw f g) = 0 := by
  rw [realWeilForm_synthesis_left]
  simp only [(arithmeticSectionProjection_spec hN hw0 hw f g).2,
    mul_zero, Finset.sum_const_zero]

theorem arithmeticSectionProjection_reproduces (c : ι → ℝ) :
    arithmeticSectionProjection hN hw0 hw f (realTestSynthesis (fun i => (f i).1) c) =
      realTestSynthesis (fun i => (f i).1) c := by
  symm
  apply arithmeticSectionProjection_unique hN hw0 hw f _ _ ⟨c, rfl⟩
  intro i
  rw [sub_self, map_zero]

theorem arithmeticSectionProjection_idempotent (g : realTests) :
    arithmeticSectionProjection hN hw0 hw f (arithmeticSectionProjection hN hw0 hw f g) =
      arithmeticSectionProjection hN hw0 hw f g := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  rw [hc, arithmeticSectionProjection_reproduces]

theorem arithmeticSectionProjection_add (g h : realTests) :
    arithmeticSectionProjection hN hw0 hw f (g + h) =
      arithmeticSectionProjection hN hw0 hw f g + arithmeticSectionProjection hN hw0 hw f h := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  obtain ⟨d, hd⟩ := (arithmeticSectionProjection_spec hN hw0 hw f h).1
  symm
  apply arithmeticSectionProjection_unique hN hw0 hw f
  · refine ⟨c + d, ?_⟩
    rw [hc, hd]
    exact (map_add (realTestSynthesisMap (fun i => (f i).1)) c d).symm
  · intro i
    have hg := (arithmeticSectionProjection_spec hN hw0 hw f g).2 i
    have hh := (arithmeticSectionProjection_spec hN hw0 hw f h).2 i
    rw [map_sub] at hg hh
    rw [map_sub, map_add, map_add]
    linarith only [hg, hh]

theorem arithmeticSectionProjection_smul (a : ℝ) (g : realTests) :
    arithmeticSectionProjection hN hw0 hw f (a • g) =
      a • arithmeticSectionProjection hN hw0 hw f g := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  symm
  apply arithmeticSectionProjection_unique hN hw0 hw f
  · refine ⟨a • c, ?_⟩
    rw [hc]
    exact (map_smul (realTestSynthesisMap (fun i => (f i).1)) a c).symm
  · intro i
    have hg := (arithmeticSectionProjection_spec hN hw0 hw f g).2 i
    rw [map_sub] at hg
    rw [map_sub, map_smul, map_smul, ← smul_sub, hg, smul_zero]

/-- A source-defined idempotent projection for the original Weil pairing. -/
def arithmeticSectionProjectionMap : realTests →ₗ[ℝ] realTests where
  toFun := arithmeticSectionProjection hN hw0 hw f
  map_add' := arithmeticSectionProjection_add hN hw0 hw f
  map_smul' := arithmeticSectionProjection_smul hN hw0 hw f

/-- The residual identity retains the entire completed form, with both pole moments. -/
theorem arithmeticSectionProjection_residual_pair (g h : realTests) :
    realWeilForm (g - arithmeticSectionProjection hN hw0 hw f g)
      (h - arithmeticSectionProjection hN hw0 hw f h) =
    realWeilForm g h - realWeilForm (arithmeticSectionProjection hN hw0 hw f g)
      (arithmeticSectionProjection hN hw0 hw f h) := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  obtain ⟨d, hd⟩ := (arithmeticSectionProjection_spec hN hw0 hw f h).1
  have hleft := arithmeticSectionProjection_orthogonal hN hw0 hw f c h
  have hright := arithmeticSectionProjection_orthogonal hN hw0 hw f d g
  rw [← hc, map_sub] at hleft
  rw [← hd, map_sub, realWeilForm_symm _ g,
    realWeilForm_symm _ (arithmeticSectionProjection hN hw0 hw f g)] at hright
  simp only [map_sub, LinearMap.sub_apply]
  linarith only [hleft, hright]

/-- The removed section has nonnegative completed energy, from its arithmetic square-mass floor. -/
theorem arithmeticSectionProjection_energy_nonneg (g : realTests) :
    0 ≤ realWeilForm (arithmeticSectionProjection hN hw0 hw f g)
      (arithmeticSectionProjection hN hw0 hw f g) := by
  obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  let p := arithmeticSectionProjection hN hw0 hw f g
  have hp : p ∈ arithmeticSectionTests N w := by
    rw [show p = realTestSynthesis (fun i => (f i).1) c from hc]
    exact (arithmeticSectionTests N w).sum_mem fun i _ =>
      (arithmeticSectionTests N w).smul_mem (c i) (f i).2
  exact (integral_nonneg fun u => sq_nonneg (p.1 u)).trans
    (integral_sq_le_weilPair_arithmeticSection hN hw0 hw ⟨p, hp⟩)

/-- Removing a positive section does not improve the signed energy of a negative witness. -/
theorem arithmeticSectionProjection_residual_energy_le (g : realTests) :
    realWeilForm (g - arithmeticSectionProjection hN hw0 hw f g)
      (g - arithmeticSectionProjection hN hw0 hw f g) ≤ realWeilForm g g := by
  rw [arithmeticSectionProjection_residual_pair]
  exact sub_le_self _ (arithmeticSectionProjection_energy_nonneg hN hw0 hw f g)

/-- Orthogonal removal minimizes residual Weil energy with an actual-test square-mass gap.
No norm on a redundant coefficient presentation is used. -/
theorem arithmeticSectionProjection_minimizes_with_square_gap
    (g : realTests) (c : ι → ℝ) :
    realWeilForm (g - arithmeticSectionProjection hN hw0 hw f g)
        (g - arithmeticSectionProjection hN hw0 hw f g) +
      (∫ u, ((arithmeticSectionProjection hN hw0 hw f g).1 u -
        (realTestSynthesis (fun i => (f i).1) c).1 u) ^ 2) ≤
    realWeilForm (g - realTestSynthesis (fun i => (f i).1) c)
      (g - realTestSynthesis (fun i => (f i).1) c) := by
  let p := arithmeticSectionProjection hN hw0 hw f g
  let q := realTestSynthesis (fun i => (f i).1) c
  obtain ⟨d, hd⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
  have hp : p ∈ arithmeticSectionTests N w := by
    rw [show p = realTestSynthesis (fun i => (f i).1) d from hd]
    exact (arithmeticSectionTests N w).sum_mem fun i _ =>
      (arithmeticSectionTests N w).smul_mem (d i) (f i).2
  have hq : q ∈ arithmeticSectionTests N w :=
    (arithmeticSectionTests N w).sum_mem fun i _ =>
      (arithmeticSectionTests N w).smul_mem (c i) (f i).2
  have hfloor := integral_sq_le_weilPair_arithmeticSection hN hw0 hw
    ⟨p - q, (arithmeticSectionTests N w).sub_mem hp hq⟩
  have hporth := arithmeticSectionProjection_orthogonal hN hw0 hw f d g
  rw [← hd] at hporth
  have hqorth := arithmeticSectionProjection_orthogonal hN hw0 hw f c g
  have horth : realWeilForm (p - q) (g - p) = 0 := by
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.mpr (hporth.trans hqorth.symm)
  have hsum : g - q = (g - p) + (p - q) := by abel
  have henergy : realWeilForm (g - q) (g - q) =
      realWeilForm (g - p) (g - p) + realWeilForm (p - q) (p - q) := by
    rw [hsum, map_add, LinearMap.add_apply, map_add, map_add,
      realWeilForm_symm (g - p) (p - q), horth]
    ring
  change realWeilForm (g - p) (g - p) + (∫ u, (p.1 u - q.1 u) ^ 2) ≤
    realWeilForm (g - q) (g - q)
  rw [henergy]
  exact add_le_add_left hfloor _

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSection_exists_unique_projection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSectionProjection_residual_pair
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSectionProjection_residual_energy_le
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSectionProjection_minimizes_with_square_gap
