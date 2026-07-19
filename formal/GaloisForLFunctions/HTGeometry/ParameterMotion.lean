import GaloisForLFunctions.HTGeometry.KernelOffDiag

/-!
# How the fiber moves with the parameter

The denominator depends on the parameter affinely, `B(x)t − D(x)`, so a change of `t` perturbs it by
`B(x)(t − t₀)`, which is uniformly small on a compact set.  The two arguments used in the level
direction therefore both work in the parameter direction, and more cheaply — no series convergence is
involved:

* where the denominator at `t₀` is nonvanishing on a compact set, it stays nonvanishing for nearby
  `t`;
* at a fiber point of `t₀` the sign change persists, so nearby `t` has a fiber point nearby.

Together these say the fiber varies continuously: no points appear from nowhere and none vanish.
-/

open scoped BigOperators
open Set

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **No fiber point appears from nowhere.**  On a compact set avoiding the fiber of `t₀`, nearby
parameters also have no fiber point. -/
theorem exists_param_radius_no_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (t₀ : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hKF : ∀ x ∈ K, nevBrealInf s x * t₀ - nevDrealInf s x ≠ 0) :
    ∃ ρ > 0, ∀ t : ℝ, |t - t₀| < ρ → ∀ x ∈ K, nevBrealInf s x * t - nevDrealInf s x ≠ 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun t _ x hx => absurd hx (notMem_empty x)⟩
  have hcontG : Continuous fun x : ℝ => |nevBrealInf s x * t₀ - nevDrealInf s x| :=
    (((continuous_nevBrealInf h h0b).mul continuous_const).sub
      (continuous_nevDrealInf h h0b)).abs
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hKne hcontG.continuousOn
  set δ : ℝ := |nevBrealInf s x₀ * t₀ - nevDrealInf s x₀| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (hKF x₀ hx₀K)
  have hcontB : Continuous fun x : ℝ => |nevBrealInf s x| := (continuous_nevBrealInf h h0b).abs
  obtain ⟨x₁, hx₁K, hmax⟩ := hK.exists_isMaxOn hKne hcontB.continuousOn
  set M : ℝ := |nevBrealInf s x₁| with hMdef
  have hMnn : 0 ≤ M := abs_nonneg _
  refine ⟨δ / (2 * (M + 1)), by positivity, fun t ht x hx => ?_⟩
  intro hzero
  have hlow : δ ≤ |nevBrealInf s x * t₀ - nevDrealInf s x| := hmin hx
  have hBx : |nevBrealInf s x| ≤ M := hmax hx
  have hdiff : (nevBrealInf s x * t₀ - nevDrealInf s x)
      = nevBrealInf s x * (t₀ - t) := by
    have : nevBrealInf s x * t - nevDrealInf s x = 0 := hzero
    linarith [this]
  have hbound : |nevBrealInf s x * (t₀ - t)| < δ := by
    rw [abs_mul]
    have h1 : |t₀ - t| < δ / (2 * (M + 1)) := by
      rw [abs_sub_comm]
      exact ht
    have h2 : |nevBrealInf s x| * |t₀ - t| ≤ M * (δ / (2 * (M + 1))) := by
      refine mul_le_mul hBx h1.le (abs_nonneg _) hMnn
    have h3 : M * (δ / (2 * (M + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [← hdiff] at hbound
  linarith

/-- **No fiber point disappears.**  At a fiber point of `t₀` the sign change persists for nearby
parameters, so each of them has a fiber point nearby. -/
theorem exists_param_radius_zero_near (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    {t₀ ξ : ℝ} (hξ : nevBrealInf s ξ * t₀ - nevDrealInf s ξ = 0) :
    ∃ η > 0, ∀ δ : ℝ, 0 < δ → δ < η → ∃ ρ > 0, ∀ t : ℝ, |t - t₀| < ρ →
      ∃ x : ℝ, |x - ξ| ≤ δ ∧ nevBrealInf s x * t - nevDrealInf s x = 0 := by
  obtain ⟨η, hη, hsign⟩ := nevDenominator_opposite_signs h h0b hξ
  refine ⟨η, hη, fun δ hδ hδη => ?_⟩
  have hprod := hsign δ hδ hδη
  set Ga : ℝ := nevBrealInf s (ξ - δ) * t₀ - nevDrealInf s (ξ - δ) with hGa
  set Gb : ℝ := nevBrealInf s (ξ + δ) * t₀ - nevDrealInf s (ξ + δ) with hGb
  have hGane : Ga ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hprod
    exact absurd hprod (lt_irrefl 0)
  have hGbne : Gb ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hprod
    exact absurd hprod (lt_irrefl 0)
  set M : ℝ := |nevBrealInf s (ξ - δ)| + |nevBrealInf s (ξ + δ)| + 1 with hMdef
  have hMpos : 0 < M := by positivity
  set ε : ℝ := min |Ga| |Gb| / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have h1 : 0 < |Ga| := abs_pos.mpr hGane
    have h2 : 0 < |Gb| := abs_pos.mpr hGbne
    have : 0 < min |Ga| |Gb| := lt_min h1 h2
    linarith
  refine ⟨ε / M, by positivity, fun t ht => ?_⟩
  have hεa : ε ≤ |Ga| / 2 := by
    rw [hεdef]
    have : min |Ga| |Gb| ≤ |Ga| := min_le_left _ _
    linarith
  have hεb : ε ≤ |Gb| / 2 := by
    rw [hεdef]
    have : min |Ga| |Gb| ≤ |Gb| := min_le_right _ _
    linarith
  set fa : ℝ := nevBrealInf s (ξ - δ) * t - nevDrealInf s (ξ - δ) with hfa
  set fb : ℝ := nevBrealInf s (ξ + δ) * t - nevDrealInf s (ξ + δ) with hfb
  have hda : |fa - Ga| < ε := by
    have heq : fa - Ga = nevBrealInf s (ξ - δ) * (t - t₀) := by
      rw [hfa, hGa]; ring
    rw [heq, abs_mul]
    have h1 : |nevBrealInf s (ξ - δ)| ≤ M := by
      rw [hMdef]
      have := abs_nonneg (nevBrealInf s (ξ + δ))
      linarith
    calc |nevBrealInf s (ξ - δ)| * |t - t₀|
        ≤ M * |t - t₀| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ < M * (ε / M) := mul_lt_mul_of_pos_left ht hMpos
      _ = ε := mul_div_cancel₀ _ hMpos.ne'
  have hdb : |fb - Gb| < ε := by
    have heq : fb - Gb = nevBrealInf s (ξ + δ) * (t - t₀) := by
      rw [hfb, hGb]; ring
    rw [heq, abs_mul]
    have h1 : |nevBrealInf s (ξ + δ)| ≤ M := by
      rw [hMdef]
      have := abs_nonneg (nevBrealInf s (ξ - δ))
      linarith
    calc |nevBrealInf s (ξ + δ)| * |t - t₀|
        ≤ M * |t - t₀| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ < M * (ε / M) := mul_lt_mul_of_pos_left ht hMpos
      _ = ε := mul_div_cancel₀ _ hMpos.ne'
  have hcont : ContinuousOn (fun x : ℝ => nevBrealInf s x * t - nevDrealInf s x)
      (Icc (ξ - δ) (ξ + δ)) :=
    (((continuous_nevBrealInf h h0b).mul continuous_const).sub
      (continuous_nevDrealInf h h0b)).continuousOn
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

end HTGeometry
