import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedRadialPackets

/-!
# Exact integration of one p-adic valuation shell

The multiplicative group `ℚ_pˣ` is the product of the discrete valuation
group and the compact unit group.  This file turns that decomposition into a
reusable exact integration theorem: a complex function with one nonzero
valuation shell is integrable precisely from its angular profile, and its
full multiplicative-Haar integral is the normalized unit-Haar integral.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

variable (p : ℕ) [Fact p.Prime]

/-- A one-shell function on `ℚ_pˣ` is multiplicatively integrable whenever
its angular profile is integrable on `ℤ_pˣ`. -/
theorem integrable_fieldOnePadicMultiplicativeHaar_of_singleShell
    (f : ℚ_[p]ˣ → ℂ) (m : ℤ) (g : ℤ_[p]ˣ → ℂ)
    (hg : Integrable g (fieldOnePadicUnitNormalizedHaar p))
    (hcoord : ∀ (k : ℤ) (u : ℤ_[p]ˣ),
      f (fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u)) =
        if k = m then g u else 0) :
    Integrable f (fieldOnePadicMultiplicativeHaar p) := by
  let e := fieldOnePadicValuationUnitContinuousMulEquiv p
  let μ := fieldOnePadicValuationUnitProductHaar p
  let F : Multiplicative ℤ × ℤ_[p]ˣ → ℂ := fun z =>
    if z.1.toAdd = m then g z.2 else 0
  have hcomp : (fun z => f (e z)) = F := by
    funext z
    have hz := Multiplicative.ofAdd.apply_symm_apply z.1
    have hzpair : z = (Multiplicative.ofAdd z.1.toAdd, z.2) := by
      exact Prod.ext hz.symm rfl
    change f (e z) = F z
    rw [hzpair]
    simpa [F] using hcoord z.1.toAdd z.2
  have hmeasSet : MeasurableSet
      ({k : Multiplicative ℤ | k.toAdd = m}) := by
    exact (measurableSet_singleton m).preimage
      (continuous_of_discreteTopology.measurable)
  have hFmeas : AEStronglyMeasurable F μ := by
    have hbase : AEStronglyMeasurable
        (fun z : Multiplicative ℤ × ℤ_[p]ˣ => g z.2) μ := by
      exact hg.aestronglyMeasurable.comp_snd
    have hi := hbase.indicator (hmeasSet.preimage measurable_fst)
    convert hi using 1
    funext z
    simp only [F, Set.indicator, Set.mem_preimage, Set.mem_setOf_eq]
  have hFint : Integrable F μ := by
    change Integrable F
      (Measure.count.prod (fieldOnePadicUnitNormalizedHaar p))
    refine (integrable_prod_iff hFmeas).mpr ⟨?_, ?_⟩
    · filter_upwards with k
      by_cases hk : k.toAdd = m
      · simpa [F, hk] using hg
      · simp [F, hk]
    · have houter : (fun k : Multiplicative ℤ =>
          ∫ u, ‖F (k, u)‖ ∂fieldOnePadicUnitNormalizedHaar p) =
          fun k => if k.toAdd = m then
            ∫ u, ‖g u‖ ∂fieldOnePadicUnitNormalizedHaar p else 0 := by
        funext k
        by_cases hk : k.toAdd = m
        · simp [F, hk]
        · simp [F, hk]
      rw [houter, integrable_count_iff]
      refine summable_of_ne_finset_zero
        (s := {Multiplicative.ofAdd m}) ?_
      intro k hk
      simp only [Finset.mem_singleton] at hk
      have hk' : k.toAdd ≠ m := by
        intro heq
        apply hk
        rw [← heq]
        exact Multiplicative.ofAdd.apply_symm_apply k
      simp [hk']
  change Integrable f (Measure.map e μ)
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv f).mpr
  change Integrable (fun z => f (e z)) μ
  rw [hcomp]
  exact hFint

/-- Exact multiplicative-Haar integral of a one-shell function. -/
theorem fieldOnePadicMultiplicativeHaar_integral_singleShell
    (f : ℚ_[p]ˣ → ℂ) (m : ℤ) (g : ℤ_[p]ˣ → ℂ)
    (hg : Integrable g (fieldOnePadicUnitNormalizedHaar p))
    (hcoord : ∀ (k : ℤ) (u : ℤ_[p]ˣ),
      f (fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd k, u)) =
        if k = m then g u else 0) :
    ∫ a, f a ∂fieldOnePadicMultiplicativeHaar p =
      ∫ u, g u ∂fieldOnePadicUnitNormalizedHaar p := by
  have hf := integrable_fieldOnePadicMultiplicativeHaar_of_singleShell
    p f m g hg hcoord
  rw [fieldOnePadicMultiplicativeHaar_integral_eq_tsum p f hf]
  have hterms : (fun k : Multiplicative ℤ =>
      ∫ u : ℤ_[p]ˣ,
        f (fieldOnePadicValuationUnitContinuousMulEquiv p (k, u))
        ∂fieldOnePadicUnitNormalizedHaar p) =
      fun k => if k = Multiplicative.ofAdd m then
        ∫ u, g u ∂fieldOnePadicUnitNormalizedHaar p else 0 := by
    funext k
    have hkrep := Multiplicative.ofAdd.apply_symm_apply k
    have hpoint : ∀ u : ℤ_[p]ˣ,
        f (fieldOnePadicValuationUnitContinuousMulEquiv p (k, u)) =
          if Multiplicative.ofAdd.symm k = m then g u else 0 := by
      intro u
      rw [← hkrep]
      exact hcoord (Multiplicative.ofAdd.symm k) u
    by_cases hkm : Multiplicative.ofAdd.symm k = m
    · have hkeq : k = Multiplicative.ofAdd m := by
        rw [← hkm]
        exact hkrep.symm
      rw [if_pos hkeq]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        have hu := hpoint u
        rw [if_pos hkm] at hu
        exact hu
    · have hkne : k ≠ Multiplicative.ofAdd m := by
        intro hkeq
        apply hkm
        exact Multiplicative.ofAdd.injective (hkrep.trans hkeq)
      rw [if_neg hkne]
      have hz : (fun u : ℤ_[p]ˣ =>
            f (fieldOnePadicValuationUnitContinuousMulEquiv p (k, u))) = 0 := by
        funext u
        have hu := hpoint u
        rw [if_neg hkm] at hu
        exact hu
      rw [hz]
      simp
  rw [hterms]
  exact tsum_ite_eq _ _

end
end GaloisForLFunctions.RHTower
