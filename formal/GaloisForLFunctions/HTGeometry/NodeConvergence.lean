import GaloisForLFunctions.HTGeometry.KernelOffDiag
import GaloisForLFunctions.HTGeometry.NevDenominatorFactor

/-!
# Nodes accumulate at every fiber point

The limiting denominator takes opposite signs at `ξ ± δ`, and the truncations converge to it
uniformly there, so for large `n` the truncated denominator also takes opposite signs at the two
endpoints.  The intermediate value theorem then puts a zero of the truncation inside — and those
zeros are the quasi-orthogonal nodes.

Nothing here uses complex analysis: it is the sign change of link 168 plus uniform convergence.
-/

open scoped BigOperators
open Filter Set

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A level-`n` zero of the denominator near every fiber point.** -/
theorem eventually_exists_denominator_zero_near (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {t ξ : ℝ}
    (hξ : nevBrealInf s ξ * t - nevDrealInf s ξ = 0) :
    ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ᶠ n in atTop, ∃ x : ℝ, |x - ξ| ≤ δ ∧ nevBreal s n x * t - nevDreal s n x = 0 := by
  obtain ⟨η, hη, hsign⟩ := nevDenominator_opposite_signs h h0b hξ
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  have hprod := hsign δ hδ hδη
  set Ga : ℝ := nevBrealInf s (ξ - δ) * t - nevDrealInf s (ξ - δ) with hGa
  set Gb : ℝ := nevBrealInf s (ξ + δ) * t - nevDrealInf s (ξ + δ) with hGb
  have hGane : Ga ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hprod
    exact absurd hprod (lt_irrefl 0)
  have hGbne : Gb ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hprod
    exact absurd hprod (lt_irrefl 0)
  set ε : ℝ := min |Ga| |Gb| / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have h1 : 0 < |Ga| := abs_pos.mpr hGane
    have h2 : 0 < |Gb| := abs_pos.mpr hGbne
    have : 0 < min |Ga| |Gb| := lt_min h1 h2
    linarith
  have hr : (0:ℝ) < |ξ| + δ + 1 := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_nevDenominator_close h hS hP t hr hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hneg := neg_abs_le ξ
  have hself := le_abs_self ξ
  have hxa : |ξ - δ| < |ξ| + δ + 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hxb : |ξ + δ| < |ξ| + δ + 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have hda := hN n hn (ξ - δ) hxa
  have hdb := hN n hn (ξ + δ) hxb
  set fa : ℝ := nevBreal s n (ξ - δ) * t - nevDreal s n (ξ - δ) with hfa
  set fb : ℝ := nevBreal s n (ξ + δ) * t - nevDreal s n (ξ + δ) with hfb
  have habs_a : |fa - Ga| < ε := hda
  have habs_b : |fb - Gb| < ε := hdb
  have hεa : ε ≤ |Ga| / 2 := by
    rw [hεdef]
    have : min |Ga| |Gb| ≤ |Ga| := min_le_left _ _
    linarith
  have hεb : ε ≤ |Gb| / 2 := by
    rw [hεdef]
    have : min |Ga| |Gb| ≤ |Gb| := min_le_right _ _
    linarith
  have hcont : ContinuousOn (fun x : ℝ => nevBreal s n x * t - nevDreal s n x)
      (Icc (ξ - δ) (ξ + δ)) :=
    (((continuous_nevBreal s n).mul continuous_const).sub
      (continuous_nevDreal s n)).continuousOn
  have hab : ξ - δ ≤ ξ + δ := by linarith
  have habs_ab : ∀ x ∈ Icc (ξ - δ) (ξ + δ), |x - ξ| ≤ δ := by
    intro x hx
    rw [abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the truncation inherits the opposite signs
  rcases lt_or_gt_of_ne hGane with hGaneg | hGapos
  · have hGbpos : 0 < Gb := by nlinarith [hprod]
    have hfaneg : fa < 0 := by
      have hA := (abs_lt.mp habs_a).2
      have hE : |Ga| = -Ga := abs_of_neg hGaneg
      rw [hE] at hεa
      linarith
    have hfbpos : 0 < fb := by
      have hB := (abs_lt.mp habs_b).1
      have hE : |Gb| = Gb := abs_of_pos hGbpos
      rw [hE] at hεb
      linarith
    obtain ⟨x, hxmem, hxz⟩ := intermediate_value_Icc hab hcont
      (mem_Icc.mpr ⟨hfaneg.le, hfbpos.le⟩)
    exact ⟨x, habs_ab x hxmem, hxz⟩
  · have hGbneg : Gb < 0 := by nlinarith [hprod]
    have hfapos : 0 < fa := by
      have hA := (abs_lt.mp habs_a).1
      have hE : |Ga| = Ga := abs_of_pos hGapos
      rw [hE] at hεa
      linarith
    have hfbneg : fb < 0 := by
      have hB := (abs_lt.mp habs_b).2
      have hE : |Gb| = -Gb := abs_of_neg hGbneg
      rw [hE] at hεb
      linarith
    obtain ⟨x, hxmem, hxz⟩ := intermediate_value_Icc' hab hcont
      (mem_Icc.mpr ⟨hfbneg.le, hfapos.le⟩)
    exact ⟨x, habs_ab x hxmem, hxz⟩

/-- **A quasi-orthogonal node near every fiber point, at every good level.** -/
theorem eventually_exists_quasiNode_near (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {t ξ : ℝ} (hξ : nevBrealInf s ξ * t - nevDrealInf s ξ = 0) :
    ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ᶠ n in atTop, nevAlpha s n t ≠ 0 →
        ∃ x ∈ quasiNodes s n (nevBeta s n t / nevAlpha s n t), |x - ξ| ≤ δ := by
  obtain ⟨η, hη, hall⟩ := eventually_exists_denominator_zero_near h h0b hξ
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  filter_upwards [hall δ hδ hδη] with n hn hα
  obtain ⟨x, hxδ, hxz⟩ := hn
  exact ⟨x, (nevDenominator_zero_iff h n hα x).mp hxz, hxδ⟩

end HTGeometry
