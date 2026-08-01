import GaloisForLFunctions.RHTower.SoninOuterTailIntegral
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# Shifting an energy density past a band

Translating the integration variable turns the energy of a shifted density inside a central band
into the energy of the density itself outside a band, and likewise outside a band into outside a
smaller band.  Both radii are the distance between the shift and the band edge, so a shift growing
faster than the band drives the energy to zero.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- Energy of a shifted density inside a central band is energy of the density beyond the gap. -/
theorem integral_indicator_centralInterval_comp_add_le
    {G : ℝ → ℝ} (hG : Integrable G volume) (hnn : ∀ x, 0 ≤ G x) (t d : ℝ) :
    ∫ ξ : ℝ, (centralInterval t).indicator (fun η : ℝ => G (η + d)) ξ ≤
      ∫ η : ℝ, {η : ℝ | |d| - t ≤ |η|}.indicator G η := by
  have hkey : ∀ ξ : ℝ, (centralInterval t).indicator (fun η : ℝ => G (η + d)) ξ =
      ({η : ℝ | |d| - t ≤ |η|}.indicator G) (ξ + d) +
        ((centralInterval t).indicator (fun η : ℝ => G (η + d)) ξ -
          ({η : ℝ | |d| - t ≤ |η|}.indicator G) (ξ + d)) := by
    intro ξ
    ring
  have hle : ∀ ξ : ℝ, (centralInterval t).indicator (fun η : ℝ => G (η + d)) ξ ≤
      ({η : ℝ | |d| - t ≤ |η|}.indicator G) (ξ + d) := by
    intro ξ
    by_cases hmem : ξ ∈ centralInterval t
    · rw [Set.indicator_of_mem hmem]
      have habs : |ξ| ≤ t := abs_le.mpr ⟨hmem.1, hmem.2⟩
      have hout : ξ + d ∈ {η : ℝ | |d| - t ≤ |η|} := by
        simp only [Set.mem_setOf_eq]
        have h1 : |d| - |ξ| ≤ |ξ + d| := by
          have := abs_sub_abs_le_abs_sub d (-ξ)
          have habsneg : |(-ξ)| = |ξ| := abs_neg ξ
          rw [habsneg] at this
          calc |d| - |ξ| ≤ |d - -ξ| := this
            _ = |ξ + d| := by rw [sub_neg_eq_add, add_comm]
        linarith
      rw [Set.indicator_of_mem hout]
    · rw [Set.indicator_of_notMem hmem]
      exact Set.indicator_nonneg (fun x _ => hnn x) _
  clear hkey
  calc ∫ ξ : ℝ, (centralInterval t).indicator (fun η : ℝ => G (η + d)) ξ
      ≤ ∫ ξ : ℝ, ({η : ℝ | |d| - t ≤ |η|}.indicator G) (ξ + d) := by
        refine integral_mono ?_ ?_ hle
        · refine Integrable.indicator ?_ (measurableSet_centralInterval t)
          exact (hG.comp_add_right d)
        · exact (hG.indicator (measurableSet_outer (|d| - t))).comp_add_right d
    _ = ∫ η : ℝ, {η : ℝ | |d| - t ≤ |η|}.indicator G η := integral_add_right_eq_self _ d

/-- Energy of a shifted density outside a band is energy of the density outside a smaller band. -/
theorem integral_indicator_outer_comp_add_le
    {G : ℝ → ℝ} (hG : Integrable G volume) (hnn : ∀ x, 0 ≤ G x) (t d : ℝ) :
    ∫ ξ : ℝ, {ξ : ℝ | t ≤ |ξ|}.indicator (fun η : ℝ => G (η + d)) ξ ≤
      ∫ η : ℝ, {η : ℝ | t - |d| ≤ |η|}.indicator G η := by
  have hle : ∀ ξ : ℝ, {ξ : ℝ | t ≤ |ξ|}.indicator (fun η : ℝ => G (η + d)) ξ ≤
      ({η : ℝ | t - |d| ≤ |η|}.indicator G) (ξ + d) := by
    intro ξ
    by_cases hmem : ξ ∈ {ξ : ℝ | t ≤ |ξ|}
    · rw [Set.indicator_of_mem hmem]
      have habs : t ≤ |ξ| := hmem
      have hout : ξ + d ∈ {η : ℝ | t - |d| ≤ |η|} := by
        simp only [Set.mem_setOf_eq]
        have h1 : |ξ| - |d| ≤ |ξ + d| := by
          have := abs_sub_abs_le_abs_sub ξ (-d)
          have habsneg : |(-d)| = |d| := abs_neg d
          rw [habsneg] at this
          calc |ξ| - |d| ≤ |ξ - -d| := this
            _ = |ξ + d| := by rw [sub_neg_eq_add]
        linarith
      rw [Set.indicator_of_mem hout]
    · rw [Set.indicator_of_notMem hmem]
      exact Set.indicator_nonneg (fun x _ => hnn x) _
  calc ∫ ξ : ℝ, {ξ : ℝ | t ≤ |ξ|}.indicator (fun η : ℝ => G (η + d)) ξ
      ≤ ∫ ξ : ℝ, ({η : ℝ | t - |d| ≤ |η|}.indicator G) (ξ + d) := by
        refine integral_mono ?_ ?_ hle
        · exact (hG.comp_add_right d).indicator (measurableSet_outer t)
        · exact (hG.indicator (measurableSet_outer (t - |d|))).comp_add_right d
    _ = ∫ η : ℝ, {η : ℝ | t - |d| ≤ |η|}.indicator G η := integral_add_right_eq_self _ d

end RHTower
