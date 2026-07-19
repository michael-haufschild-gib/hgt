import GaloisForLFunctions.HTGeometry.KernelOffDiag
import GaloisForLFunctions.HTGeometry.InfinityDenominator
import GaloisForLFunctions.HTGeometry.NodeConvergence

/-!
# Sign change and node convergence at the parameter infinity

At a zero of `B` the Wronskian identity reads `B(x)·D(ξ) = h₀·(x − ξ)·K(x,ξ)`, with `D(ξ) ≠ 0` because
the two entries have no common zero.  That is the same factorisation as in the finite case with the
roles of `B` and `D` exchanged, so the sign change and the intermediate-value argument carry over
unchanged.
-/

open scoped BigOperators
open Filter Set

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem nevDrealInf_ne_zero_of_nevBrealInf_eq_zero (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {ξ : ℝ} (hξ : nevBrealInf s ξ = 0) : nevDrealInf s ξ ≠ 0 := by
  rcases nevBrealInf_ne_zero_or_nevDrealInf_ne_zero h h0b ξ with hc | hd
  · exact absurd hξ hc
  · exact hd

/-- **`B` factors through the kernel at each of its zeros.** -/
theorem nevBrealInf_factor_at_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {ξ : ℝ} (hξ : nevBrealInf s ξ = 0) (x : ℝ) :
    nevBrealInf s x * nevDrealInf s ξ
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) * ((x - ξ) * kernelInf s x ξ) := by
  have hw := nevBD_wronskian_limit h h0b x ξ
  rw [hξ, mul_zero, sub_zero] at hw
  exact hw

/-- **`B` changes sign at each of its zeros.** -/
theorem nevBrealInf_opposite_signs (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {ξ : ℝ} (hξ : nevBrealInf s ξ = 0) :
    ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η →
      nevBrealInf s (ξ - δ) * nevBrealInf s (ξ + δ) < 0 := by
  obtain ⟨η, hη, hpos⟩ := eventually_kernelInf_pos h h0b ξ
  have hD : nevDrealInf s ξ ≠ 0 := nevDrealInf_ne_zero_of_nevBrealInf_eq_zero h h0b hξ
  have hD2 : 0 < nevDrealInf s ξ ^ 2 := by positivity
  have h0v : 0 < momentInner s (monicOrtho s 0) (monicOrtho s 0) := monicOrtho_inner_self_pos h 0
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  have hplus := nevBrealInf_factor_at_zero h h0b hξ (ξ + δ)
  have hminus := nevBrealInf_factor_at_zero h h0b hξ (ξ - δ)
  have hKp : 0 < kernelInf s (ξ + δ) ξ := hpos _ (by rw [add_sub_cancel_left]; rwa [abs_of_pos hδ])
  have hKm : 0 < kernelInf s (ξ - δ) ξ := by
    refine hpos _ ?_
    have hsub : ξ - δ - ξ = -δ := by ring
    rw [hsub, abs_neg, abs_of_pos hδ]
    exact hδη
  have hp : 0 < nevBrealInf s (ξ + δ) * nevDrealInf s ξ := by
    rw [hplus, add_sub_cancel_left]
    positivity
  have hm : nevBrealInf s (ξ - δ) * nevDrealInf s ξ < 0 := by
    rw [hminus]
    have hsub : ξ - δ - ξ = -δ := by ring
    rw [hsub]
    nlinarith [hKm, h0v, hδ]
  nlinarith [hp, hm, hD2]

/-- **A level-`n` zero of `B` near every zero of the limit.** -/
theorem eventually_exists_nevBreal_zero_near (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {ξ : ℝ} (hξ : nevBrealInf s ξ = 0) :
    ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ᶠ n in atTop, ∃ x : ℝ, |x - ξ| ≤ δ ∧ nevBreal s n x = 0 := by
  obtain ⟨η, hη, hsign⟩ := nevBrealInf_opposite_signs h h0b hξ
  obtain ⟨S, P, hSpos, hPpos, hS, hP⟩ := h0b
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  have hprod := hsign δ hδ hδη
  set Ga : ℝ := nevBrealInf s (ξ - δ) with hGa
  set Gb : ℝ := nevBrealInf s (ξ + δ) with hGb
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
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_nevBreal_close h hS hP hr hε)
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
  set fa : ℝ := nevBreal s n (ξ - δ) with hfa
  set fb : ℝ := nevBreal s n (ξ + δ) with hfb
  have hεa : ε ≤ |Ga| / 2 := by
    rw [hεdef]
    have : min |Ga| |Gb| ≤ |Ga| := min_le_left _ _
    linarith
  have hεb : ε ≤ |Gb| / 2 := by
    rw [hεdef]
    have : min |Ga| |Gb| ≤ |Gb| := min_le_right _ _
    linarith
  have hcont : ContinuousOn (fun x : ℝ => nevBreal s n x) (Icc (ξ - δ) (ξ + δ)) :=
    (continuous_nevBreal s n).continuousOn
  have hab : ξ - δ ≤ ξ + δ := by linarith
  have habs_ab : ∀ x ∈ Icc (ξ - δ) (ξ + δ), |x - ξ| ≤ δ := by
    intro x hx
    rw [abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rcases lt_or_gt_of_ne hGane with hGaneg | hGapos
  · have hGbpos : 0 < Gb := by nlinarith [hprod]
    have hfaneg : fa < 0 := by
      have hA := (abs_lt.mp hda).2
      have hE : |Ga| = -Ga := abs_of_neg hGaneg
      rw [hE] at hεa
      linarith
    have hfbpos : 0 < fb := by
      have hB := (abs_lt.mp hdb).1
      have hE : |Gb| = Gb := abs_of_pos hGbpos
      rw [hE] at hεb
      linarith
    obtain ⟨x, hxmem, hxz⟩ := intermediate_value_Icc hab hcont
      (mem_Icc.mpr ⟨hfaneg.le, hfbpos.le⟩)
    exact ⟨x, habs_ab x hxmem, hxz⟩
  · have hGbneg : Gb < 0 := by nlinarith [hprod]
    have hfapos : 0 < fa := by
      have hA := (abs_lt.mp hda).1
      have hE : |Ga| = Ga := abs_of_pos hGapos
      rw [hE] at hεa
      linarith
    have hfbneg : fb < 0 := by
      have hB := (abs_lt.mp hdb).2
      have hE : |Gb| = -Gb := abs_of_neg hGbneg
      rw [hE] at hεb
      linarith
    obtain ⟨x, hxmem, hxz⟩ := intermediate_value_Icc' hab hcont
      (mem_Icc.mpr ⟨hfbneg.le, hfapos.le⟩)
    exact ⟨x, habs_ab x hxmem, hxz⟩

/-- **A quasi-orthogonal node near every zero of `B`, at every good level.** -/
theorem eventually_exists_quasiNode_near_inf (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) {ξ : ℝ} (hξ : nevBrealInf s ξ = 0) :
    ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ᶠ n in atTop, nevAlphaInf s n ≠ 0 →
        ∃ x ∈ quasiNodes s n (nevBetaInf s n / nevAlphaInf s n), |x - ξ| ≤ δ := by
  obtain ⟨η, hη, hall⟩ := eventually_exists_nevBreal_zero_near h h0b hξ
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  filter_upwards [hall δ hδ hδη] with n hn hα
  obtain ⟨x, hxδ, hxz⟩ := hn
  exact ⟨x, (nevBreal_zero_iff h n hα x).mp hxz, hxδ⟩

end HTGeometry
