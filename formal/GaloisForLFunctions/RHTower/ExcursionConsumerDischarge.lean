import GaloisForLFunctions.RHTower.ExcursionBoundDischarge
import GaloisForLFunctions.RHTower.ParityCounting
import GaloisForLFunctions.RHTower.ThickDips

/-!
# High-level relay consumers with excursion input discharged

The canonical absorbing completion supplies `ExcursionBound` internally to the two high-level
parity/thick-kernel spread obstructions.  All floor, separation, and measure hypotheses retain their
original mathematical content; only the now-constructible ephemerality interface disappears.
-/

namespace RHTower

noncomputable section

open MeasureTheory Set

/-- Parity-selected kernel obstruction for the canonically completed walk, with no excursion
hypothesis. -/
theorem spread_lt_of_upcross_selected_kernel_absorbingCompletion
    {D₀ : ℝ} {pushes : List ℝ} {k M K : ℕ} {levels : ℕ → ℕ}
    [DecidablePred (UpcrossAt D₀ (absorbingCompletion D₀ pushes))]
    (hD₀ : D₀ ≤ 0)
    (hgap : ∀ i, i < k → levels i + (pushes.length + 1) ≤ levels (i + 1))
    (hpres : ∀ i, i ≤ k →
      0 < signedDepth D₀ (absorbingCompletion D₀ pushes) (levels i))
    (hM : levels k ≤ M)
    {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F)
    {w B : ℝ} (hw : 0 < w) (hBnonneg : 0 ≤ B) (S : Finset ℝ)
    (sel : ℝ → Prop) [DecidablePred sel]
    (hup : ((Finset.range M).filter
      (UpcrossAt D₀ (absorbingCompletion D₀ pushes))).card ≤ (S.filter sel).card)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * w ≤ |x - y|)
    (hdip : ∀ γ ∈ S, sel γ →
      ENNReal.ofReal w ≤ volume (E ∩ Icc (γ - w) (γ + w)))
    (hdisj : ∀ γ ∈ S, sel γ → F ∩ Icc (γ - w) (γ + w) = ∅)
    (hker : volume (E \ F) ≤ ENNReal.ofReal B)
    (hK : B < (K + 1 : ℝ) * w) :
    k < K :=
  spread_lt_of_upcross_selected_kernel hD₀
    (absorbingCompletion_excursionBound_length_succ D₀ pushes)
    hgap hpres hM hE hF hw hBnonneg S sel hup hsep hdip hdisj hker hK

/-- Width-refined thick-kernel obstruction for the canonically completed walk, with no excursion
hypothesis. -/
theorem spread_lt_of_upcross_thick_kernel_absorbingCompletion
    {D₀ : ℝ} {pushes : List ℝ} {k M K : ℕ} {levels : ℕ → ℕ}
    [DecidablePred (UpcrossAt D₀ (absorbingCompletion D₀ pushes))]
    (hD₀ : D₀ ≤ 0)
    (hgap : ∀ i, i < k → levels i + (pushes.length + 1) ≤ levels (i + 1))
    (hpres : ∀ i, i ≤ k →
      0 < signedDepth D₀ (absorbingCompletion D₀ pushes) (levels i))
    (hM : levels k ≤ M)
    {h B2 L2 β C r U : ℝ} (hh : 0 < h) (hpos : 0 < B2 + 2 * h * L2)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hCU : 0 ≤ C * r ^ 2 * U)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ t, 0 ≤ f t) (S : Finset ℝ)
    (hup : ((Finset.range M).filter
      (UpcrossAt D₀ (absorbingCompletion D₀ pushes))).card ≤ S.card)
    (hsep : (↑S : Set ℝ).Pairwise fun x y => 3 * h ≤ |x - y|)
    (havg : ∀ γ ∈ S,
      ∫ t in Icc (γ - h) (γ + h), f t ≤ 2 * h * B2 + 4 * h ^ 2 * L2)
    {A B : Set ℝ} (hA : MeasurableSet A)
    (hsub : {t | f t ≤ 2 * (B2 + 2 * h * L2)} ⊆ A ∪ B)
    (hB : ∀ t : ℝ, volume (B ∩ Icc (t - 2 * h) (t + 2 * h))
      ≤ ENNReal.ofReal (β * h))
    (hker : volume A ≤ ENNReal.ofReal (C * r ^ 2 * U))
    (hK : (4 / (1 - β)) * (C * r ^ 2 * U) < (K + 1 : ℝ) * h) :
    k < K :=
  spread_lt_of_upcross_thick_kernel hD₀
    (absorbingCompletion_excursionBound_length_succ D₀ pushes)
    hgap hpres hM hh hpos hβ0 hβ1 hCU hf hnn S hup hsep havg hA hsub hB hker hK

end

end RHTower
