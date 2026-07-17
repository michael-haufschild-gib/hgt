import GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale
import Mathlib.Data.Fintype.Option

/-!
# Finite same-sign Gamma products

A finite nonempty product of shifted Gamma clocks with strictly positive integer charges is
hypertranscendental, without any separation hypothesis on the shifts.  Integer-translation
collisions do not cancel: one collided pair is merged by the Gamma recurrence, its two positive
charges add, and induction removes all presentation collisions.  A separated factor instead
closes the argument immediately by the existing orbit theorem.

Gauss multiplication then upgrades the result to every nonempty finite family of positive
integer-scale Gamma clocks.  This is the unconditional parent theorem needed by normalization
constants whose refined Gamma shifts can collide at special parameter values.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance gammaSameSignDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance gammaSameSignDifferential : Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gammaSameSignRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gammaSameSignRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaSameSignDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gammaSameSignCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

private theorem gammaFintypeOrbitProductMero_option_merge_ofNat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Option ι → ℂ) (m : Option ι → ℤ) (i : ι) (n : ℕ)
    (hshift : b (some i) = b none + (n : ℂ)) :
    gammaFintypeOrbitProductMero b m =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaOrbitNatFactor (b none) n) ^ m (some i) *
        gammaFintypeOrbitProductMero
          (Function.update (fun j => b (some j)) i (b none))
          (Function.update (fun j => m (some j)) i (m none + m (some i))) := by
  rw [gammaFintypeOrbitProductMero, Fintype.prod_option,
    gammaFintypeOrbitProductMero]
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  rw [← Finset.mul_prod_erase Finset.univ
      (fun j => gammaShiftMero (b (some j)) ^ m (some j)) hmem,
    ← Finset.mul_prod_erase Finset.univ
      (fun j => gammaShiftMero
          (Function.update (fun k => b (some k)) i (b none) j) ^
        Function.update (fun k => m (some k)) i (m none + m (some i)) j) hmem]
  simp only [Function.update_self]
  have hrest :
      (∏ j ∈ (Finset.univ : Finset ι).erase i,
          gammaShiftMero
              (Function.update (fun k => b (some k)) i (b none) j) ^
            Function.update (fun k => m (some k)) i
              (m none + m (some i)) j) =
        ∏ j ∈ (Finset.univ : Finset ι).erase i,
          gammaShiftMero (b (some j)) ^ m (some j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Function.update_of_ne hji]
  rw [hrest, hshift, gammaShiftMero_add_nat, mul_zpow]
  change gammaShiftMero (b none) ^ m none *
      ((algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaOrbitNatFactor (b none) n)) ^ m (some i) *
        gammaShiftMero (b none) ^ m (some i) *
        ∏ j ∈ (Finset.univ : Finset ι).erase i,
          gammaShiftMero (b (some j)) ^ m (some j)) = _
  rw [zpow_add₀ (gammaShiftMero_ne_zero (b none))]
  ring

private theorem gammaFintypeOrbitProductMero_option_merge_of_negSucc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Option ι → ℂ) (m : Option ι → ℤ) (i : ι) (n : ℕ)
    (hshift : b (some i) - b none = ((Int.negSucc n : ℤ) : ℂ)) :
    gammaFintypeOrbitProductMero b m =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaOrbitNatFactor (b (some i)) (n + 1)) ^ m none *
        gammaFintypeOrbitProductMero
          (fun j => b (some j))
          (Function.update (fun j => m (some j)) i (m none + m (some i))) := by
  rw [gammaFintypeOrbitProductMero, Fintype.prod_option,
    gammaFintypeOrbitProductMero]
  have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  rw [← Finset.mul_prod_erase Finset.univ
      (fun j => gammaShiftMero (b (some j)) ^ m (some j)) hmem,
    ← Finset.mul_prod_erase Finset.univ
      (fun j => gammaShiftMero (b (some j)) ^
        Function.update (fun k => m (some k)) i (m none + m (some i)) j) hmem]
  simp only [Function.update_self]
  have hrest :
      (∏ j ∈ (Finset.univ : Finset ι).erase i,
          gammaShiftMero (b (some j)) ^
            Function.update (fun k => m (some k)) i
              (m none + m (some i)) j) =
        ∏ j ∈ (Finset.univ : Finset ι).erase i,
          gammaShiftMero (b (some j)) ^ m (some j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Function.update_of_ne hji]
  rw [hrest]
  have hnone : b none = b (some i) + ((n + 1 : ℕ) : ℂ) := by
    rw [Int.cast_negSucc] at hshift
    push_cast at hshift ⊢
    linear_combination -hshift
  rw [hnone, gammaShiftMero_add_nat, mul_zpow]
  change
      ((algebraMap (RatFunc ℂ) (meroField Set.univ)
          (gammaOrbitNatFactor (b (some i)) (n + 1))) ^ m none *
        gammaShiftMero (b (some i)) ^ m none) *
          (gammaShiftMero (b (some i)) ^ m (some i) *
            ∏ j ∈ (Finset.univ : Finset ι).erase i,
              gammaShiftMero (b (some j)) ^ m (some j)) = _
  rw [zpow_add₀ (gammaShiftMero_ne_zero (b (some i)))]
  ring

set_option maxHeartbeats 800000 in
private theorem hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos_over
    (ι : Type) [Fintype ι] (b : ι → ℂ) (m : ι → ℤ)
    (hm : ∀ i, 0 < m i) (hι : Nonempty ι) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaFintypeOrbitProductMero b m) := by
  classical
  let P : ∀ (α : Type) [Fintype α], Prop := fun α _ =>
    ∀ (b : α → ℂ) (m : α → ℤ),
      (∀ i, 0 < m i) → Nonempty α →
        HypertranscendentalOver (RatFunc ℂ)
          (gammaFintypeOrbitProductMero b m)
  apply Fintype.induction_empty_option (P := P)
  · intro α γ _ e h b m hm hγ
    letI : Fintype α := Fintype.ofEquiv γ e.symm
    let b' : α → ℂ := fun i => b (e i)
    let m' : α → ℤ := fun i => m (e i)
    have h' := h b' m' (fun i => hm (e i))
      (hγ.map e.symm)
    have hprod : gammaFintypeOrbitProductMero b' m' =
        gammaFintypeOrbitProductMero b m := by
      rw [gammaFintypeOrbitProductMero, gammaFintypeOrbitProductMero]
      exact Fintype.prod_equiv e
        (fun i : α => gammaShiftMero (b' i) ^ m' i)
        (fun j : γ => gammaShiftMero (b j) ^ m j)
        (by intro i; rfl)
    rwa [hprod] at h'
  · intro b m hm hEmpty
    exact PEmpty.elim (Classical.choice hEmpty)
  · intro α _ h b m hm _
    by_cases hcollision :
        ∃ i : α, ∃ q : ℤ, b (some i) - b none = (q : ℂ)
    · obtain ⟨i, q, hq⟩ := hcollision
      have hmergedPos : ∀ j : α,
          0 < Function.update (fun k => m (some k)) i
            (m none + m (some i)) j := by
        intro j
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self]
          exact add_pos (hm none) (hm (some i))
        · rw [Function.update_of_ne hji]
          exact hm (some j)
      cases q with
      | ofNat n =>
          have hshift : b (some i) = b none + (n : ℂ) := by
            norm_num at hq
            linear_combination hq
          rw [gammaFintypeOrbitProductMero_option_merge_ofNat
            b m i n hshift]
          have hind := h
            (Function.update (fun j => b (some j)) i (b none))
            (Function.update (fun j => m (some j)) i
              (m none + m (some i))) hmergedPos ⟨i⟩
          have hgaugeDA : DifferentialAlgebraicOver (RatFunc ℂ)
              (algebraMap (RatFunc ℂ) (meroField Set.univ)
                (gammaOrbitNatFactor (b none) n) ^ m (some i)) :=
            HTGeometry.differentialAlgebraicOver_zpow
              (HTGeometry.differentialAlgebraicOver_algebraMap
                (gammaOrbitNatFactor (b none) n)) (m (some i))
          have hgauge0 :
              algebraMap (RatFunc ℂ) (meroField Set.univ)
                (gammaOrbitNatFactor (b none) n) ^ m (some i) ≠ 0 :=
            zpow_ne_zero _ ((map_ne_zero_iff _
              (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective).mpr
                (gammaOrbitNatFactor_ne_zero (b none) n))
          rw [mul_comm]
          exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
            hgaugeDA hgauge0).2 hind
      | negSucc n =>
          rw [gammaFintypeOrbitProductMero_option_merge_of_negSucc
            b m i n hq]
          have hind := h (fun j => b (some j))
            (Function.update (fun j => m (some j)) i
              (m none + m (some i))) hmergedPos ⟨i⟩
          have hgaugeDA : DifferentialAlgebraicOver (RatFunc ℂ)
              (algebraMap (RatFunc ℂ) (meroField Set.univ)
                (gammaOrbitNatFactor (b (some i)) (n + 1)) ^ m none) :=
            HTGeometry.differentialAlgebraicOver_zpow
              (HTGeometry.differentialAlgebraicOver_algebraMap
                (gammaOrbitNatFactor (b (some i)) (n + 1))) (m none)
          have hgauge0 :
              algebraMap (RatFunc ℂ) (meroField Set.univ)
                (gammaOrbitNatFactor (b (some i)) (n + 1)) ^ m none ≠ 0 :=
            zpow_ne_zero _ ((map_ne_zero_iff _
              (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective).mpr
                (gammaOrbitNatFactor_ne_zero (b (some i)) (n + 1)))
          rw [mul_comm]
          exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
            hgaugeDA hgauge0).2 hind
    · apply hypertranscendentalOver_gammaFintypeOrbitProductMero b m none
      · exact ne_of_gt (hm none)
      · intro x hx q
        cases x with
        | none => exact (hx rfl).elim
        | some i =>
            exact fun hq => hcollision ⟨i, q, hq⟩
  · exact hm
  · exact hι

/-- **Finite positive-charge Gamma theorem.**  Every nonempty finite product of shifted Gamma
functions with strictly positive integer charges is hypertranscendental, even when arbitrarily
many shifts collide modulo integer translation. -/
theorem hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos
    {ι : Type} [Fintype ι] [Nonempty ι]
    (b : ι → ℂ) (m : ι → ℤ) (hm : ∀ i, 0 < m i) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaFintypeOrbitProductMero b m) :=
  hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos_over
    ι b m hm inferInstance

/-- **Unconditional positive commensurable-family theorem.**  Every nonempty finite family of
positive-integer-scale Gamma clocks with positive charges is hypertranscendental for arbitrary
complex affine shifts.  Special-value collisions in the Gauss refinement require no hypotheses. -/
theorem hypertranscendentalOver_gammaNatScaleFamilyMero_of_pos
    {d : ℕ} (hd : 0 < d) (n : Fin d → ℕ) (a : Fin d → ℂ)
    (m : Fin d → ℤ) (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 < m i) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaNatScaleFamilyMero n a m) := by
  rw [hypertranscendentalOver_gammaNatScaleFamilyMero_iff_refined n a m hn,
    gammaNatScaleFamilyRefinedMero_eq_slotProduct]
  let i0 : Fin d := ⟨0, hd⟩
  let x0 : Σ i, Fin (n i) := ⟨i0, ⟨0, hn i0⟩⟩
  letI : Nonempty (Σ i, Fin (n i)) := ⟨x0⟩
  exact hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos
    (gammaNatScaleRefinedSlotShift n a)
    (gammaNatScaleRefinedSlotCharge m)
    (fun x => hm x.1)

/-- A finite positive-charge product of negative-orientation shifted Gamma clocks. -/
def gammaFintypeNegativeOrbitProductMero
    {ι : Type} [Fintype ι] (b : ι → ℂ) (m : ι → ℤ) :
    meroField Set.univ :=
  ∏ i, gammaNegativeShiftMero (b i) ^ m i

/-- The total Euler-reflection gauge of a finite negative-orientation Gamma product. -/
def gammaFintypeNegativeReflectionGaugeMero
    {ι : Type} [Fintype ι] (b : ι → ℂ) (m : ι → ℤ) :
    meroField Set.univ :=
  ∏ i, gammaReflectionGaugeMero (b i) ^ m i

/-- Euler reflection converts every negative-orientation factor into a DA gauge times the
inverse of a positive-orientation product with the same charges. -/
theorem gammaFintypeNegativeOrbitProductMero_reflectionNormalForm
    {ι : Type} [Fintype ι] (b : ι → ℂ) (m : ι → ℤ) :
    gammaFintypeNegativeOrbitProductMero b m =
      gammaFintypeNegativeReflectionGaugeMero b m *
        (gammaFintypeOrbitProductMero (fun i => 1 - b i) m)⁻¹ := by
  rw [gammaFintypeNegativeOrbitProductMero,
    gammaFintypeNegativeReflectionGaugeMero,
    gammaFintypeOrbitProductMero]
  simp_rw [gammaNegativeShiftMero_reflection, mul_zpow, inv_zpow]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem gammaFintypeNegativeReflectionGaugeMero_ne_zero
    {ι : Type} [Fintype ι] (b : ι → ℂ) (m : ι → ℤ) :
    gammaFintypeNegativeReflectionGaugeMero b m ≠ 0 := by
  rw [gammaFintypeNegativeReflectionGaugeMero, Finset.prod_ne_zero_iff]
  intro i _
  exact zpow_ne_zero _ (gammaReflectionGaugeMero_ne_zero (b i))

theorem differentialAlgebraicOver_gammaFintypeNegativeReflectionGaugeMero
    {ι : Type} [Fintype ι] (b : ι → ℂ) (m : ι → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaFintypeNegativeReflectionGaugeMero b m) := by
  rw [gammaFintypeNegativeReflectionGaugeMero]
  apply HTGeometry.differentialAlgebraicOver_finset_prod
  intro i _
  exact HTGeometry.differentialAlgebraicOver_zpow
    (differentialAlgebraicOver_gammaReflectionGaugeMero (b i)) (m i)

/-- Every nonempty finite product of negative-orientation Gamma clocks with positive charges is
hypertranscendental.  Reflection changes orientation but cannot create cancellation. -/
theorem hypertranscendentalOver_gammaFintypeNegativeOrbitProductMero_of_pos
    {ι : Type} [Fintype ι] [Nonempty ι]
    (b : ι → ℂ) (m : ι → ℤ) (hm : ∀ i, 0 < m i) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaFintypeNegativeOrbitProductMero b m) := by
  rw [gammaFintypeNegativeOrbitProductMero_reflectionNormalForm, mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaFintypeNegativeReflectionGaugeMero b m)
    (gammaFintypeNegativeReflectionGaugeMero_ne_zero b m)).2
      ((HTGeometry.hypertranscendentalOver_inv_iff).2
        (hypertranscendentalOver_gammaFintypeOrbitProductMero_of_pos
          (fun i => 1 - b i) m hm))

/-- A finite family of negative-orientation positive-integer-scale Gamma clocks. -/
def gammaNegativeNatScaleFamilyMero {d : ℕ} (n : Fin d → ℕ)
    (b : Fin d → ℂ) (m : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNegativeNatScaleMero (n i) (b i) ^ m i

/-- The DA Gauss gauge of a negative-orientation integer-scale family. -/
def gammaNegativeNatScaleFamilyGaugeMero {d : ℕ} (n : Fin d → ℕ)
    (b : Fin d → ℂ) (m : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNegativeNatScaleGaussGaugeMero (n i) (b i) ^ m i

/-- The unit-scale negative Gamma product left by simultaneous Gauss refinement. -/
def gammaNegativeNatScaleFamilyRefinedMero {d : ℕ} (n : Fin d → ℕ)
    (b : Fin d → ℂ) (m : Fin d → ℤ) : meroField Set.univ :=
  ∏ i, gammaNegativeNatScaleGaussProductMero (n i) (b i) ^ m i

theorem gammaNegativeNatScaleFamilyMero_normalForm
    {d : ℕ} (n : Fin d → ℕ) (b : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    gammaNegativeNatScaleFamilyMero n b m =
      gammaNegativeNatScaleFamilyGaugeMero n b m *
        gammaNegativeNatScaleFamilyRefinedMero n b m := by
  rw [gammaNegativeNatScaleFamilyMero,
    gammaNegativeNatScaleFamilyGaugeMero,
    gammaNegativeNatScaleFamilyRefinedMero]
  simp_rw [gammaNegativeNatScaleMero_gauss (hn _), mul_zpow]
  exact Finset.prod_mul_distrib

theorem gammaNegativeNatScaleFamilyGaugeMero_ne_zero
    {d : ℕ} (n : Fin d → ℕ) (b : Fin d → ℂ) (m : Fin d → ℤ)
    (hn : ∀ i, 0 < n i) :
    gammaNegativeNatScaleFamilyGaugeMero n b m ≠ 0 := by
  rw [gammaNegativeNatScaleFamilyGaugeMero, Finset.prod_ne_zero_iff]
  intro i _
  exact zpow_ne_zero _
    (gammaNegativeNatScaleGaussGaugeMero_ne_zero (hn i) (b i))

theorem differentialAlgebraicOver_gammaNegativeNatScaleFamilyGaugeMero
    {d : ℕ} (n : Fin d → ℕ) (b : Fin d → ℂ) (m : Fin d → ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (gammaNegativeNatScaleFamilyGaugeMero n b m) := by
  rw [gammaNegativeNatScaleFamilyGaugeMero]
  apply HTGeometry.differentialAlgebraicOver_finset_prod
  intro i _
  exact HTGeometry.differentialAlgebraicOver_zpow
    (differentialAlgebraicOver_gammaNegativeNatScaleGaussGaugeMero
      (n i) (b i)) (m i)

/-- The shift of a dependent slot in a negative-orientation Gauss refinement. -/
def gammaNegativeNatScaleRefinedSlotShift {d : ℕ} (n : Fin d → ℕ)
    (b : Fin d → ℂ) (x : Σ i, Fin (n i)) : ℂ :=
  (b x.1 + (x.2 : ℕ)) / n x.1

/-- Flatten a negative-orientation Gauss refinement into one finite product. -/
theorem gammaNegativeNatScaleFamilyRefinedMero_eq_slotProduct
    {d : ℕ} (n : Fin d → ℕ) (b : Fin d → ℂ) (m : Fin d → ℤ) :
    gammaNegativeNatScaleFamilyRefinedMero n b m =
      gammaFintypeNegativeOrbitProductMero
        (gammaNegativeNatScaleRefinedSlotShift n b)
        (gammaNatScaleRefinedSlotCharge m) := by
  classical
  rw [gammaNegativeNatScaleFamilyRefinedMero,
    gammaFintypeNegativeOrbitProductMero, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [gammaNegativeNatScaleGaussProductMero,
    ← Fin.prod_univ_eq_prod_range, ← Finset.prod_zpow]
  rfl

/-- **Unconditional negative commensurable-family theorem.**  Every nonempty finite family of
negative-orientation positive-integer-scale Gamma clocks with positive charges is HT for arbitrary
complex shifts. -/
theorem hypertranscendentalOver_gammaNegativeNatScaleFamilyMero_of_pos
    {d : ℕ} (hd : 0 < d) (n : Fin d → ℕ) (b : Fin d → ℂ)
    (m : Fin d → ℤ) (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 < m i) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaNegativeNatScaleFamilyMero n b m) := by
  rw [gammaNegativeNatScaleFamilyMero_normalForm n b m hn, mul_comm]
  apply (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaNegativeNatScaleFamilyGaugeMero n b m)
    (gammaNegativeNatScaleFamilyGaugeMero_ne_zero n b m hn)).2
  rw [gammaNegativeNatScaleFamilyRefinedMero_eq_slotProduct]
  let i0 : Fin d := ⟨0, hd⟩
  let x0 : Σ i, Fin (n i) := ⟨i0, ⟨0, hn i0⟩⟩
  letI : Nonempty (Σ i, Fin (n i)) := ⟨x0⟩
  exact hypertranscendentalOver_gammaFintypeNegativeOrbitProductMero_of_pos
    (gammaNegativeNatScaleRefinedSlotShift n b)
    (gammaNatScaleRefinedSlotCharge m)
    (fun x => hm x.1)

end

end GaloisForLFunctions
