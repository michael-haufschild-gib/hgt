import GaloisForLFunctions.HTGeometry.AffineSpectrumRelationEscape
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.AnalyticNondegeneracy

/-!
# Extremality of the gap and gap-ratio maps of a Hermitian family

A spectral family whose energies admit no constant nonzero balanced real combination on a chart has
nondegenerate gap maps there, so Kleinbock--Margulis extremality applies: almost every parameter is
not simultaneously very well approximable.

Two maps are treated.  The **anchored gap map** `(E_{ι k} - E_anchor)/scale` carries the discrete
recurrence problem, and its constancy is an *affine* relation among the energies.  The **gap-ratio
map** `(E_{ι k} - E_anchor)/(E_clock - E_anchor)` carries the continuous one; its constancy is a
*homogeneous* relation, because the constant is absorbed by the anchor gap.

## Main results

* `anchoredRelationCoefficient`, `gapRatioRelationCoefficient` — the balanced coefficient vectors a
  constant combination produces.
* `theoremA_anchoredGap`, `theoremA_gapRatio` — extremality of the two maps.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section AnchoredRelation

variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- Transport a weight vector indexed by a list of spectral labels to the label type. -/
def anchoredWeight (ι : Fin n → I) (w : Fin n → ℝ) : I → ℝ :=
  fun i => ∑ k, if ι k = i then w k else 0

theorem sum_anchoredWeight (ι : Fin n → I) (w : Fin n → ℝ) :
    ∑ i, anchoredWeight ι w i = ∑ k, w k := by
  unfold anchoredWeight
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by simp

theorem sum_anchoredWeight_mul (ι : Fin n → I) (w : Fin n → ℝ) (E : I → ℝ) :
    ∑ i, anchoredWeight ι w i * E i = ∑ k, w k * E (ι k) := by
  unfold anchoredWeight
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_mul _ _ (E i)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single (ι k)]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · intro hmem
    exact absurd (Finset.mem_univ (ι k)) hmem

omit [Fintype I] in
theorem anchoredWeight_apply {ι : Fin n → I} (hι : Function.Injective ι)
    (w : Fin n → ℝ) (k : Fin n) :
    anchoredWeight ι w (ι k) = w k := by
  unfold anchoredWeight
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    exact if_neg fun h => hj (hι h)
  · intro hmem
    exact absurd (Finset.mem_univ k) hmem

/-- The balanced coefficient vector produced by a weighted combination of anchored gaps. -/
def anchoredRelationCoefficient (anchor : I) (ι : Fin n → I) (w : Fin n → ℝ) : I → ℝ :=
  fun i => anchoredWeight ι w i - (if i = anchor then ∑ k, w k else 0)

theorem sum_anchoredRelationCoefficient (anchor : I) (ι : Fin n → I) (w : Fin n → ℝ) :
    ∑ i, anchoredRelationCoefficient anchor ι w i = 0 := by
  unfold anchoredRelationCoefficient
  rw [Finset.sum_sub_distrib, sum_anchoredWeight, Finset.sum_ite_eq' Finset.univ anchor]
  simp

theorem sum_anchoredRelationCoefficient_mul
    (anchor : I) (ι : Fin n → I) (w : Fin n → ℝ) (E : I → ℝ) :
    ∑ i, anchoredRelationCoefficient anchor ι w i * E i
      = ∑ k, w k * (E (ι k) - E anchor) := by
  unfold anchoredRelationCoefficient
  have hsplit :
      ∑ i, (anchoredWeight ι w i - (if i = anchor then ∑ k, w k else 0)) * E i
        = (∑ i, anchoredWeight ι w i * E i)
          - ∑ i, (if i = anchor then ∑ k, w k else 0) * E i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, sum_anchoredWeight_mul]
  have hsingle :
      ∑ i, (if i = anchor then ∑ k, w k else 0) * E i = (∑ k, w k) * E anchor := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      (by split_ifs with h <;> simp [h] :
        (if i = anchor then ∑ k, w k else 0) * E i
          = if i = anchor then (∑ k, w k) * E anchor else 0)]
    simp
  rw [hsingle, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [Fintype I] in
theorem anchoredRelationCoefficient_apply
    {anchor : I} {ι : Fin n → I} (hι : Function.Injective ι) (hanchor : ∀ k, ι k ≠ anchor)
    (w : Fin n → ℝ) (k : Fin n) :
    anchoredRelationCoefficient anchor ι w (ι k) = w k := by
  unfold anchoredRelationCoefficient
  rw [anchoredWeight_apply hι, if_neg (hanchor k), sub_zero]

omit [Fintype I] in
theorem anchoredRelationCoefficient_ne_zero
    {anchor : I} {ι : Fin n → I} (hι : Function.Injective ι) (hanchor : ∀ k, ι k ≠ anchor)
    {w : Fin n → ℝ} (hw : w ≠ 0) :
    anchoredRelationCoefficient anchor ι w ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hcon
    exact hw (funext fun k => by
      by_contra h
      exact hcon ⟨k, h⟩)
  intro h0
  apply hk
  rw [← anchoredRelationCoefficient_apply hι hanchor w k, h0]
  rfl

/-- The balanced coefficient vector produced by a weighted combination of anchored gap ratios with
constant value `κ`: the constant is absorbed by the anchor gap, so the relation is homogeneous. -/
def gapRatioRelationCoefficient (anchor clock : I) (ι : Fin n → I) (w : Fin n → ℝ) (κ : ℝ) :
    I → ℝ :=
  fun i => anchoredRelationCoefficient anchor ι w i
    + (if i = anchor then κ else 0) - (if i = clock then κ else 0)

theorem sum_gapRatioRelationCoefficient
    (anchor clock : I) (ι : Fin n → I) (w : Fin n → ℝ) (κ : ℝ) :
    ∑ i, gapRatioRelationCoefficient anchor clock ι w κ i = 0 := by
  unfold gapRatioRelationCoefficient
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_anchoredRelationCoefficient,
    Finset.sum_ite_eq' Finset.univ anchor, Finset.sum_ite_eq' Finset.univ clock]
  simp

theorem sum_gapRatioRelationCoefficient_mul
    (anchor clock : I) (ι : Fin n → I) (w : Fin n → ℝ) (κ : ℝ) (E : I → ℝ) :
    ∑ i, gapRatioRelationCoefficient anchor clock ι w κ i * E i
      = (∑ k, w k * (E (ι k) - E anchor)) + κ * (E anchor - E clock) := by
  unfold gapRatioRelationCoefficient
  have hsplit :
      ∑ i, (anchoredRelationCoefficient anchor ι w i
            + (if i = anchor then κ else 0) - (if i = clock then κ else 0)) * E i
        = (∑ i, anchoredRelationCoefficient anchor ι w i * E i)
          + (∑ i, (if i = anchor then κ else 0) * E i)
          - ∑ i, (if i = clock then κ else 0) * E i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpoint : ∀ j : I, ∑ i, (if i = j then κ else 0) * E i = κ * E j := by
    intro j
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      (by split_ifs with h <;> simp [h] :
        (if i = j then κ else 0) * E i = if i = j then κ * E j else 0)]
    simp
  rw [hsplit, sum_anchoredRelationCoefficient_mul, hpoint, hpoint]
  ring

omit [Fintype I] in
theorem gapRatioRelationCoefficient_apply
    {anchor clock : I} {ι : Fin n → I} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock)
    (w : Fin n → ℝ) (κ : ℝ) (k : Fin n) :
    gapRatioRelationCoefficient anchor clock ι w κ (ι k) = w k := by
  unfold gapRatioRelationCoefficient
  rw [anchoredRelationCoefficient_apply hι hanchor, if_neg (hanchor k), if_neg (hclock k)]
  ring

omit [Fintype I] in
theorem gapRatioRelationCoefficient_ne_zero
    {anchor clock : I} {ι : Fin n → I} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock)
    {w : Fin n → ℝ} (hw : w ≠ 0) (κ : ℝ) :
    gapRatioRelationCoefficient anchor clock ι w κ ≠ 0 := by
  obtain ⟨k, hk⟩ : ∃ k, w k ≠ 0 := by
    by_contra hcon
    exact hw (funext fun k => by
      by_contra h
      exact hcon ⟨k, h⟩)
  intro h0
  apply hk
  rw [← gapRatioRelationCoefficient_apply hι hanchor hclock w κ k, h0]
  rfl

end AnchoredRelation

/-- The anchored gap map of a spectrum, rescaled by a fixed nonzero factor. -/
def anchoredGapMap {I : Type*} {n : ℕ} (scale : ℝ) (spec : I → ℝ) (anchor : I) (ι : Fin n → I) :
    Fin n → ℝ :=
  fun k => (spec (ι k) - spec anchor) / scale

/-- The anchored gap-ratio map of a spectrum, with one gap used as the clock. -/
def anchoredGapRatioMap {I : Type*} {n : ℕ} (spec : I → ℝ) (anchor clock : I) (ι : Fin n → I) :
    Fin n → ℝ :=
  fun k => (spec (ι k) - spec anchor) / (spec clock - spec anchor)

section Extremality

variable {m n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

/-- **No constant combination of anchored gaps.**  On a family escaping every constant real
relation, a weighted sum of anchored gaps is constant on a nonempty open set of parameters only for
the zero weight. -/
theorem no_constant_combination_anchoredGap
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hS : SpectrumEscapesAffineRelations (Set.range (realAffineMatrix base generator)))
    {anchor : I} {ι : Fin n → I} (hι : Function.Injective ι) (hanchor : ∀ k, ι k ≠ anchor)
    {scale : ℝ} (hscale : scale ≠ 0)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation (realAffineMatrix base generator q, ((spec q i : ℝ) : ℂ)) = 0)
    (w : Fin n → ℝ)
    (hconst : ∀ x ∈ U, ∀ y ∈ U,
      ∑ k, w k * anchoredGapMap scale (spec x) anchor ι k
        = ∑ k, w k * anchoredGapMap scale (spec y) anchor ι k) :
    w = 0 := by
  by_contra hw
  obtain ⟨x₀, hx₀⟩ := hUne
  set κ : ℝ := ∑ k, w k * anchoredGapMap scale (spec x₀) anchor ι k with hκ
  refine not_affineRelation_on_open_of_spectrumEscapes base generator hS
    (sum_anchoredRelationCoefficient anchor ι w)
    (anchoredRelationCoefficient_ne_zero hι hanchor hw)
    (scale * κ) hU ⟨x₀, hx₀⟩ spec hinj hroot ?_
  intro q hq
  rw [sum_anchoredRelationCoefficient_mul]
  have h : ∑ k, w k * anchoredGapMap scale (spec q) anchor ι k = κ := hconst q hq x₀ hx₀
  have hexpand : ∀ k : Fin n,
      w k * (spec q (ι k) - spec q anchor)
        = scale * (w k * anchoredGapMap scale (spec q) anchor ι k) := by
    intro k
    unfold anchoredGapMap
    field_simp
  calc ∑ k, w k * (spec q (ι k) - spec q anchor)
      = ∑ k, scale * (w k * anchoredGapMap scale (spec q) anchor ι k) :=
        Finset.sum_congr rfl fun k _ => hexpand k
    _ = scale * ∑ k, w k * anchoredGapMap scale (spec q) anchor ι k := by
        rw [Finset.mul_sum]
    _ = scale * κ := by rw [h]

/-- **No constant combination of anchored gap ratios.**  The constant is absorbed by the clock gap,
so this needs only the homogeneous escape property. -/
theorem no_constant_combination_gapRatio
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hS : SpectrumEscapesRealRelations (Set.range (realAffineMatrix base generator)))
    {anchor clock : I} {ι : Fin n → I} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock) (hac : anchor ≠ clock)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation (realAffineMatrix base generator q, ((spec q i : ℝ) : ℂ)) = 0)
    (w : Fin n → ℝ)
    (hconst : ∀ x ∈ U, ∀ y ∈ U,
      ∑ k, w k * anchoredGapRatioMap (spec x) anchor clock ι k
        = ∑ k, w k * anchoredGapRatioMap (spec y) anchor clock ι k) :
    w = 0 := by
  by_contra hw
  obtain ⟨x₀, hx₀⟩ := hUne
  set κ : ℝ := ∑ k, w k * anchoredGapRatioMap (spec x₀) anchor clock ι k with hκ
  refine not_relation_on_open_of_spectrumEscapes base generator hS
    (sum_gapRatioRelationCoefficient anchor clock ι w κ)
    (gapRatioRelationCoefficient_ne_zero hι hanchor hclock hw κ)
    hU ⟨x₀, hx₀⟩ spec hinj hroot ?_
  intro q hq
  have hne : spec q clock - spec q anchor ≠ 0 := by
    intro h
    exact hac ((hinj q hq) (sub_eq_zero.mp h)).symm
  have h : ∑ k, w k * anchoredGapRatioMap (spec q) anchor clock ι k = κ := hconst q hq x₀ hx₀
  have hexpand : ∀ k : Fin n,
      w k * (spec q (ι k) - spec q anchor)
        = (spec q clock - spec q anchor) *
            (w k * anchoredGapRatioMap (spec q) anchor clock ι k) := by
    intro k
    unfold anchoredGapRatioMap
    field_simp
  have hsum : ∑ k, w k * (spec q (ι k) - spec q anchor)
      = κ * (spec q clock - spec q anchor) := by
    calc ∑ k, w k * (spec q (ι k) - spec q anchor)
        = ∑ k, (spec q clock - spec q anchor) *
            (w k * anchoredGapRatioMap (spec q) anchor clock ι k) :=
          Finset.sum_congr rfl fun k _ => hexpand k
      _ = (spec q clock - spec q anchor) *
            ∑ k, w k * anchoredGapRatioMap (spec q) anchor clock ι k := by
          rw [Finset.mul_sum]
      _ = κ * (spec q clock - spec q anchor) := by rw [h]; ring
  rw [sum_gapRatioRelationCoefficient_mul, hsum]
  ring

/-- **Extremality of the anchored gap map.**  Almost every parameter of an analytic simple-spectrum
chart of a family escaping every constant real relation is not simultaneously very well
approximable in the anchored gaps. -/
theorem theoremA_anchoredGap [NeZero m] (hn : 0 < n)
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hS : SpectrumEscapesAffineRelations (Set.range (realAffineMatrix base generator)))
    {anchor : I} {ι : Fin n → I} (hι : Function.Injective ι) (hanchor : ∀ k, ι k ≠ anchor)
    {scale : ℝ} (hscale : scale ≠ 0)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation (realAffineMatrix base generator q, ((spec q i : ℝ) : ℂ)) = 0)
    (hF : AnalyticOnNhd ℝ (fun q => anchoredGapMap scale (spec q) anchor ι) U) :
    volume {x ∈ U | KleinbockMargulis.VWA fun k => anchoredGapMap scale (spec x) anchor ι k} = 0 :=
  KleinbockMargulis.theoremA_analytic hn hU hUc hF
    (fun w hw =>
      no_constant_combination_anchoredGap base generator hS hι hanchor hscale hU hUne
        spec hinj hroot w hw)

/-- **Extremality of the anchored gap-ratio map.** -/
theorem theoremA_gapRatio [NeZero m] (hn : 0 < n)
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hS : SpectrumEscapesRealRelations (Set.range (realAffineMatrix base generator)))
    {anchor clock : I} {ι : Fin n → I} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock) (hac : anchor ≠ clock)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation (realAffineMatrix base generator q, ((spec q i : ℝ) : ℂ)) = 0)
    (hF : AnalyticOnNhd ℝ (fun q => anchoredGapRatioMap (spec q) anchor clock ι) U) :
    volume {x ∈ U |
      KleinbockMargulis.VWA fun k => anchoredGapRatioMap (spec x) anchor clock ι k} = 0 :=
  KleinbockMargulis.theoremA_analytic hn hU hUc hF
    (fun w hw =>
      no_constant_combination_gapRatio base generator hS hι hanchor hclock hac hU hUne
        spec hinj hroot w hw)

end Extremality

end

end GaloisForLFunctions.HTGeometry
