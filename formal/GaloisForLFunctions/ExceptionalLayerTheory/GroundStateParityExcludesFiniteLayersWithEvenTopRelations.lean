import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster
import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerNoGo
import GaloisForLFunctions.RHTower.ZerosApproachLineAttainment
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine

/-!
# Ground-state parity excludes every finite layer with even top relations

Let `Q_a` be the CCM restricted Weil form at aperture `a`. The parity half of Connes' step 1 says
that at every large aperture `Q_a` has a ground state that is not reflection-odd
(`EventuallyGroundNotOdd`). Under a finite off-line set whose deepest zeros `t_j + i·w`
(`w` the zero width) have top ordinates `t_j` satisfying only integer relations with even
coefficient sum, the CCM parity theorem makes every ground state odd at arbitrarily large
apertures (`RHTower.CCMParityTopLayer.not_finiteTopLayer_of_eventually_ground_not_odd`). Since
finitely many off-line zeros always form such a top layer
(`SquareRootThreshold.exists_finiteTopLayer_of_finite_offLine`), this is a statement about B13:

* `riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd`: step 1, a finite off-line set and
  even top relations give RH;
* `finiteOffLine_imp_riemannHypothesis_or_not_evenTopRelations`: under step 1, a finite off-line set
  is empty or its top ordinates satisfy an integer relation with odd coefficient sum;
* `riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd_of_subsingleton`: one top ordinate
  (in particular a single off-line quartet) is excluded by step 1 outright.
* `finiteOffLine_imp_riemannHypothesis_or_balance_nonpos`: **the exact residue.** Under step 1 a
  finite off-line set is empty, or the leading-order parity balance `F` of its top layer is `≤ 0` at
  every aperture phase `θ(a) = −2a·t`. Such a layer has odd top relations
  (`evenTopRelations_false_of_balance_nonpos`); by `CCMParityDeepLimit` and
  `CCMParityLargeHeightCluster` its depth is not small and its height is not large relative to its
  ordinate shape.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

open _root_.RHTower _root_.RHTower.CCMParityQuartet _root_.RHTower.CCMParityTopLayer
  _root_.RHTower.CCMParityCauchy
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth)

/-- **The parity half of Connes' step 1**: at every large aperture the CCM restricted Weil form has
a ground state that is not reflection-odd. -/
def EventuallyGroundNotOdd : Prop :=
  ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A < a.1 →
    ∃ u : CCMArchimedeanFormDomain a,
      ccmRestrictedWeilSourceQuadratic a u =
          ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ∧
        ccmArchimedeanFormReflection a u ≠ -u

/-- The top ordinates: the ordinates `t > 0` of the spectral points `t + i·w` of the deepest zeros,
`w` the zero width. -/
def zetaTopOrdinates : Set ℝ :=
  {x : ℝ | 0 < x ∧ ∃ q : XiZeroCopy, xiSpectralPoint q = (x : ℂ) + (zetaZeroWidth : ℂ) * I}

/-- Every integer relation among distinct top ordinates has even coefficient sum. -/
def TopOrdinatesHaveEvenRelations : Prop :=
  ∀ (m : ℕ) (t : Fin m → ℝ), Function.Injective t → (∀ j, t j ∈ zetaTopOrdinates) →
    ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → Even (∑ j, k j)

/-- The ordinates of a finite top layer at the zero width are top ordinates. -/
theorem mem_zetaTopOrdinates_of_finiteTopLayer {m : ℕ} {t : Fin m → ℝ}
    (h : FiniteTopLayer zetaZeroWidth t) (j : Fin m) : t j ∈ zetaTopOrdinates := by
  obtain ⟨q, hq⟩ := h.exists_top j
  exact ⟨h.t_pos j, q, hq⟩

/-- Off RH some zero copy has a nonreal spectral point. -/
theorem nonempty_offLine_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Nonempty := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
  refine ⟨q, ?_⟩
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  show (xiSpectralPoint q).im ≠ 0
  rw [him]
  exact ne_of_lt (by linarith)

/-- **Step 1 and even top relations exclude a finite off-line layer.** -/
theorem riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd
    (hg : EventuallyGroundNotOdd) (hF : BacklundConverse.FiniteOffLine)
    (hrel : TopOrdinatesHaveEvenRelations) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨m, t, h⟩ := SquareRootThreshold.exists_finiteTopLayer_of_finite_offLine hF
    (nonempty_offLine_of_not_riemannHypothesis hRH)
  exact not_finiteTopLayer_of_eventually_ground_not_odd hg h
    (hrel m t h.injective (mem_zetaTopOrdinates_of_finiteTopLayer h))

/-- **Step 1 implies B13 up to odd top relations.** Under step 1 a finite off-line set is empty, or
its top ordinates satisfy an integer relation with odd coefficient sum. -/
theorem finiteOffLine_imp_riemannHypothesis_or_not_evenTopRelations
    (hg : EventuallyGroundNotOdd) (hF : BacklundConverse.FiniteOffLine) :
    RiemannHypothesis ∨ ¬ TopOrdinatesHaveEvenRelations := by
  by_cases hrel : TopOrdinatesHaveEvenRelations
  · exact Or.inl (riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd hg hF hrel)
  · exact Or.inr hrel

/-- Top ordinates without nontrivial integer relations (e.g. `ℚ`-independent) have even relations. -/
theorem topOrdinatesHaveEvenRelations_of_independent
    (h : ∀ (m : ℕ) (t : Fin m → ℝ), Function.Injective t → (∀ j, t j ∈ zetaTopOrdinates) →
      ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → k = 0) :
    TopOrdinatesHaveEvenRelations := by
  intro m t ht hmem k hk
  rw [h m t ht hmem k hk]
  simp

/-- A single top ordinate has only the trivial relation. -/
theorem topOrdinatesHaveEvenRelations_of_subsingleton (h : zetaTopOrdinates.Subsingleton) :
    TopOrdinatesHaveEvenRelations := by
  intro m t ht hmem k hk
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · set j₀ : Fin m := ⟨0, hm⟩
    haveI : Subsingleton (Fin m) :=
      ⟨fun a b => (ht (h (hmem a) (hmem j₀))).trans (ht (h (hmem b) (hmem j₀))).symm⟩
    rw [Fintype.sum_subsingleton _ j₀] at hk ⊢
    have hk0 : (k j₀ : ℝ) = 0 := (mul_eq_zero.mp hk).resolve_right (hmem j₀).1.ne'
    rw [show k j₀ = 0 by exact_mod_cast hk0]
    exact ⟨0, by simp⟩

/-- **Step 1 excludes a layer with one top ordinate**, in particular a single off-line quartet. -/
theorem riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd_of_subsingleton
    (hg : EventuallyGroundNotOdd) (hF : BacklundConverse.FiniteOffLine)
    (h : zetaTopOrdinates.Subsingleton) : RiemannHypothesis :=
  riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd hg hF
    (topOrdinatesHaveEvenRelations_of_subsingleton h)

/-- **The exact residue of step 1 on the finite stratum.** Under step 1 a finite off-line set is
empty, or its top layer has a nonpositive parity balance at every aperture phase. -/
theorem finiteOffLine_imp_riemannHypothesis_or_balance_nonpos
    (hg : EventuallyGroundNotOdd) (hF : BacklundConverse.FiniteOffLine) :
    RiemannHypothesis ∨ ∃ (m : ℕ) (t : Fin m → ℝ) (h : FiniteTopLayer zetaZeroWidth t),
      ∀ a : ℝ, ccmParityBalance zetaZeroWidth t h.mult (aperturePhase t a) ≤ 0 := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  obtain ⟨m, t, h⟩ := SquareRootThreshold.exists_finiteTopLayer_of_finite_offLine hF
    (nonempty_offLine_of_not_riemannHypothesis hRH)
  refine Or.inr ⟨m, t, h, fun a => not_lt.mp fun hpos => ?_⟩
  obtain ⟨A, hA⟩ := hg
  obtain ⟨a', ha', hodd⟩ := exists_aperture_ground_odd h ⟨a, hpos⟩ A
  obtain ⟨u, hu, hne⟩ := hA a' ha'
  exact hne (hodd u hu)

/-- A top layer whose parity balance is nonpositive along the whole aperture line has an integer
relation among its ordinates with odd coefficient sum. -/
theorem evenTopRelations_false_of_balance_nonpos {m : ℕ} {t : Fin m → ℝ}
    (h : FiniteTopLayer zetaZeroWidth t)
    (hle : ∀ a : ℝ, ccmParityBalance zetaZeroWidth t h.mult (aperturePhase t a) ≤ 0) :
    ¬ TopOrdinatesHaveEvenRelations := by
  intro hrel
  obtain ⟨a, -, hpos⟩ := ccm_exists_large_aperture_odd_wins_of_even_relations h.pos h.injective
    h.t_pos h.mult_pos h.nonempty (hrel m t h.injective (mem_zetaTopOrdinates_of_finiteTopLayer h)) 0
  exact absurd (hle a) (not_le.mpr hpos)

end GaloisForLFunctions.ExceptionalLayerTheory
