import GaloisForLFunctions.HTGeometry.F1TwoFaceCriterion
import GaloisForLFunctions.HTGeometry.RationalPhaseRankConsequences

/-!
# Function-field weight and Frobenius boundaries

Two distinctions are required before a function-field border comparison can be functorial.

* Base Frobenius corank and an individual object's weight-character image are different invariants.
  A nontrivial pure weight spans one rational direction, while weight zero spans none; the base
  Frobenius value group remains nontrivial for `q > 1`.
* Multiplicative variable dilation `z ↦ q⁻¹z` is not the variable power map `z ↦ z^q`.  In an Anderson
  `t`-motive the semilinear operator is instead a coefficient Frobenius with additional rigid analytic
  triviality hypotheses.  Corank-one collapse alone cannot identify these operator categories.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational direction carried by a pure weight. -/
def pureWeightValueGroup (w : ℚ) : Submodule ℚ ℝ :=
  Submodule.span ℚ ({(w : ℝ)} : Set ℝ)

/-- Every nonzero pure weight carries exactly one rational direction. -/
theorem pureWeightValueGroup_rank_of_ne_zero {w : ℚ} (hw : w ≠ 0) :
    Module.rank ℚ (pureWeightValueGroup w) = 1 := by
  apply rank_span_rat_singleton
  exact_mod_cast hw

/-- Weight zero carries no weight-character direction. -/
theorem pureWeightZero_valueGroup_eq_bot :
    pureWeightValueGroup 0 = ⊥ := by
  simp [pureWeightValueGroup]

/-- The nontrivial base Frobenius value group cannot be identified with the weight direction of a
weight-zero object.  Thus base corank one does not force every object's weight torus to have
dimension one. -/
theorem functionFieldBaseValueGroup_ne_pureWeightZeroValueGroup
    (q : ℕ) (hq : 1 < q) :
    (F1TwoFace.functionFieldDatum q).valueGroup ≠ pureWeightValueGroup 0 := by
  intro h
  have hmem : Real.log (q : ℝ) ∈ (F1TwoFace.functionFieldDatum q).valueGroup := by
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [h, pureWeightZero_valueGroup_eq_bot] at hmem
  have hlog : Real.log (q : ℝ) ≠ 0 := by
    have hqR : (1 : ℝ) < q := by exact_mod_cast hq
    exact ne_of_gt (Real.log_pos hqR)
  exact hlog hmem

/-- Closed smallest finite-field witness: base Frobenius over `F₂` has a nonzero value direction,
while a weight-zero object's weight direction is zero. -/
theorem functionFieldTwoBaseValueGroup_ne_pureWeightZeroValueGroup :
    (F1TwoFace.functionFieldDatum 2).valueGroup ≠ pureWeightValueGroup 0 :=
  functionFieldBaseValueGroup_ne_pureWeightZeroValueGroup 2 (by norm_num)

/-- Multiplicative scaling of a characteristic-zero variable. -/
def variableDilation (q : ℕ) (z : ℂ) : ℂ := (q : ℂ)⁻¹ * z

/-- Variable power map, included to expose the operator-category mismatch. -/
def variablePowerMap (q : ℕ) (z : ℂ) : ℂ := z ^ q

/-- For every genuine finite-field size, variable dilation and variable powering are different
operators.  They already disagree at `1`. -/
theorem variableDilation_ne_variablePowerMap (q : ℕ) (hq : 1 < q) :
    variableDilation q ≠ variablePowerMap q := by
  intro h
  have h1 := congrFun h 1
  have hqne : (q : ℂ) ≠ 1 := by exact_mod_cast (Nat.ne_of_gt hq)
  apply hqne
  have hinv : (q : ℂ)⁻¹ = 1 := by
    simpa [variableDilation, variablePowerMap] using h1
  exact inv_eq_one.mp hinv

/-- Closed operator witness at the smallest prime power. -/
theorem variableDilation_two_ne_variablePowerMap :
    variableDilation 2 ≠ variablePowerMap 2 :=
  variableDilation_ne_variablePowerMap 2 (by norm_num)

end
end GaloisForLFunctions.HTGeometry
