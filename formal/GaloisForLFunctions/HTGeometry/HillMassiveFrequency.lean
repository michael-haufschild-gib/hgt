import Mathlib.Analysis.SpecialFunctions.Sqrt
import GaloisForLFunctions.HTGeometry.HillFlowFrequencyDependence

/-!
# The massive frequency of a time-dependent principal part

For the field equation of a massive species on the chart `-dt² + c(t)²δ`, the frequency of the
fibrewise oscillator is not `c(t)·s` but

`ω(t) = √(m² + c(t)²s²)`.

The energy estimate needs the logarithmic derivative of that frequency to be bounded independently of
both parameters, and it is: differentiating the square root gives `ω' = c c' s²/ω`, and `c²s² ≤ ω²`
absorbs the frequency, leaving `|ω'| ≤ (|c'|/c)·ω`. The constant is the one of the speed alone — the
mass and the spatial frequency drop out.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

section MassiveFrequency

variable {c dc : ℝ → ℝ} {m s K C S : ℝ}

/-- The frequency of the massive oscillator at spatial frequency `s`. -/
noncomputable def massiveFreq (m : ℝ) (c : ℝ → ℝ) (s : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt (m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ))

theorem massiveFreq_pos (hm : 0 < m) (c : ℝ → ℝ) (s t : ℝ) : 0 < massiveFreq m c s t := by
  refine Real.sqrt_pos.mpr ?_
  have h1 : (0 : ℝ) < m ^ (2 : ℕ) := by positivity
  have h2 : (0 : ℝ) ≤ (c t * s) ^ (2 : ℕ) := sq_nonneg _
  linarith

theorem massiveFreq_sq (hm : 0 < m) (c : ℝ → ℝ) (s t : ℝ) :
    massiveFreq m c s t ^ (2 : ℕ) = m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ) := by
  refine Real.sq_sqrt ?_
  have h1 : (0 : ℝ) < m ^ (2 : ℕ) := by positivity
  have h2 : (0 : ℝ) ≤ (c t * s) ^ (2 : ℕ) := sq_nonneg _
  linarith

theorem continuous_massiveFreq (hc : Continuous c) (m s : ℝ) :
    Continuous (massiveFreq m c s) := by
  refine Real.continuous_sqrt.comp ?_
  exact continuous_const.add ((hc.mul continuous_const).pow 2)

/-- The frequency is bounded by the mass and the speed. -/
theorem massiveFreq_sq_le (hm : 0 < m) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ))
    (t : ℝ) :
    massiveFreq m c s t ^ (2 : ℕ) ≤ m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ) := by
  rw [massiveFreq_sq hm]
  have hfac : (c t * s) ^ (2 : ℕ) = c t ^ (2 : ℕ) * s ^ (2 : ℕ) := by ring
  have hle : c t ^ (2 : ℕ) * s ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * S ^ (2 : ℕ) := by
    have h1 : (0 : ℝ) ≤ c t ^ (2 : ℕ) := sq_nonneg _
    have h2 : (0 : ℝ) ≤ s ^ (2 : ℕ) := sq_nonneg _
    nlinarith [hC t, sq_nonneg C, sq_nonneg S]
  rw [hfac]
  linarith

/-- **The derivative of the massive frequency.** -/
theorem hasDerivAt_massiveFreq (hm : 0 < m) (hc : ∀ t, HasDerivAt c (dc t) t) (s t : ℝ) :
    HasDerivAt (massiveFreq m c s) (c t * dc t * s ^ (2 : ℕ) / massiveFreq m c s t) t := by
  have hinner : HasDerivAt (fun r => m ^ (2 : ℕ) + (c r * s) ^ (2 : ℕ))
      (2 * (c t * s) * (dc t * s)) t := by
    have h := ((hc t).mul_const s).pow 2
    simpa using (h.const_add (m ^ (2 : ℕ)))
  have hpos : 0 < m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ) := by
    have h1 : (0 : ℝ) < m ^ (2 : ℕ) := by positivity
    have h2 : (0 : ℝ) ≤ (c t * s) ^ (2 : ℕ) := sq_nonneg _
    linarith
  have hsqrt := HasDerivAt.sqrt hinner (ne_of_gt hpos)
  have hval : 2 * (c t * s) * (dc t * s) / (2 * Real.sqrt (m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ)))
      = c t * dc t * s ^ (2 : ℕ) / massiveFreq m c s t := by
    rw [massiveFreq]
    have hne : Real.sqrt (m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    field_simp
  rw [hval] at hsqrt
  exact hsqrt

/-- **The logarithmic derivative of the massive frequency is that of the speed** — uniformly in the
mass and in the spatial frequency. -/
theorem abs_deriv_massiveFreq_le (hm : 0 < m) (hcpos : ∀ t, 0 < c t)
    (hK : ∀ t, |dc t| ≤ K * c t) (s t : ℝ) :
    |c t * dc t * s ^ (2 : ℕ) / massiveFreq m c s t| ≤ K * massiveFreq m c s t := by
  have hωpos : 0 < massiveFreq m c s t := massiveFreq_pos hm c s t
  have hct : 0 < c t := hcpos t
  have hK0 : 0 ≤ K := by
    have h0 : (0 : ℝ) ≤ |dc t| := abs_nonneg _
    have := hK t
    nlinarith
  have hnum : |c t * dc t * s ^ (2 : ℕ)| ≤ K * (c t * s) ^ (2 : ℕ) := by
    have habs : |c t * dc t * s ^ (2 : ℕ)| = c t * |dc t| * s ^ (2 : ℕ) := by
      rw [abs_mul, abs_mul, abs_of_pos hct, abs_of_nonneg (sq_nonneg s)]
    rw [habs]
    have := hK t
    nlinarith [sq_nonneg s, le_of_lt hct]
  have hsq : (c t * s) ^ (2 : ℕ) ≤ massiveFreq m c s t ^ (2 : ℕ) := by
    rw [massiveFreq_sq hm]
    nlinarith [sq_nonneg m]
  rw [abs_div, abs_of_pos hωpos, div_le_iff₀ hωpos]
  calc |c t * dc t * s ^ (2 : ℕ)| ≤ K * (c t * s) ^ (2 : ℕ) := hnum
    _ ≤ K * massiveFreq m c s t ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hsq hK0
    _ = K * massiveFreq m c s t * massiveFreq m c s t := by ring

/-- **The massive oscillator inherits the energy bound**, with a constant that sees neither the mass
nor the spatial frequency. -/
theorem hillEnergy_massive_le (hm : 0 < m) (hc : Continuous c) (hcd : ∀ t, HasDerivAt c (dc t) t)
    (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (y₀ : ℝ × ℝ) {t a b : ℝ}
    (ht : t ∈ Icc a b) :
    hillEnergy (massiveFreq m c s) (hillSolution (massiveFreq m c s) y₀)
        (hillSolutionDeriv (massiveFreq m c s) y₀) t ≤
      hillEnergy (massiveFreq m c s) (hillSolution (massiveFreq m c s) y₀)
        (hillSolutionDeriv (massiveFreq m c s) y₀) a * Real.exp (2 * K * (t - a)) :=
  hillEnergy_hillSolution_le (M := max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)))
    (continuous_massiveFreq hc m s) (le_max_left _ _)
    (fun r => (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _))
    (fun r => hasDerivAt_massiveFreq hm hcd s r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) y₀ ht

/-! ## The fibrewise solution is bounded uniformly in the spatial frequency -/

/-- The frequency ratio between two times is bounded by the ratio of the speeds, whatever the mass
and the spatial frequency. -/
theorem massiveFreq_le_mul (hcpos : ∀ t, 0 < c t) (s t : ℝ) :
    massiveFreq m c s 0 ≤ max 1 (c 0 / c t) * massiveFreq m c s t := by
  set R : ℝ := max 1 (c 0 / c t) with hR
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hct : 0 < c t := hcpos t
  have hc0 : 0 < c 0 := hcpos 0
  have hratio : c 0 / c t ≤ R := le_max_right _ _
  have hc0le : c 0 ≤ R * c t := by
    rw [div_le_iff₀ hct] at hratio
    exact hratio
  have hsq : (c 0 * s) ^ (2 : ℕ) ≤ R ^ (2 : ℕ) * (c t * s) ^ (2 : ℕ) := by
    have hc0sq : c 0 ^ (2 : ℕ) ≤ R ^ (2 : ℕ) * c t ^ (2 : ℕ) := by
      nlinarith [le_of_lt hc0, le_of_lt hct, hc0le]
    nlinarith [sq_nonneg s, hc0sq]
  have hR2 : (1 : ℝ) ≤ R ^ (2 : ℕ) := by nlinarith
  have hkey : m ^ (2 : ℕ) + (c 0 * s) ^ (2 : ℕ) ≤ R ^ (2 : ℕ) * (m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg m, hsq, hR2]
  have hfac : R * massiveFreq m c s t = Real.sqrt (R ^ (2 : ℕ) * (m ^ (2 : ℕ) + (c t * s) ^ (2 : ℕ))) := by
    rw [massiveFreq, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR0]
  rw [massiveFreq, hfac]
  exact Real.sqrt_le_sqrt hkey

/-- **The fibrewise oscillator with datum `(1,0)` is bounded uniformly in the spatial frequency.**
The bound is the ratio of the speeds times the Grönwall factor: neither the mass nor the frequency
appears. This is what lets a synthesis over all frequencies keep the weight of its initial datum. -/
theorem abs_hillSolution_massive_cos_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) {t b : ℝ} (ht : t ∈ Icc 0 b) :
    |hillSolution (massiveFreq m c s) (1, 0) t| ≤ max 1 (c 0 / c t) * Real.exp (K * t) := by
  have hωpos : 0 < massiveFreq m c s t := massiveFreq_pos hm c s t
  have hbase := mul_abs_hillSolution_cos_le (M := max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)))
    (continuous_massiveFreq hc m s) (le_max_left _ _)
    (fun r => (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _))
    (fun r => hasDerivAt_massiveFreq hm hcd s r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) ht
  have hratio := massiveFreq_le_mul (m := m) hcpos s t
  have hexp : (0 : ℝ) ≤ Real.exp (K * t) := le_of_lt (Real.exp_pos _)
  have hstep : massiveFreq m c s t * |hillSolution (massiveFreq m c s) (1, 0) t|
      ≤ (max 1 (c 0 / c t) * Real.exp (K * t)) * massiveFreq m c s t := by
    refine hbase.trans ?_
    nlinarith [hratio, hexp, le_of_lt hωpos]
  refine le_of_mul_le_mul_right ?_ hωpos
  calc |hillSolution (massiveFreq m c s) (1, 0) t| * massiveFreq m c s t
      = massiveFreq m c s t * |hillSolution (massiveFreq m c s) (1, 0) t| := by ring
    _ ≤ (max 1 (c 0 / c t) * Real.exp (K * t)) * massiveFreq m c s t := hstep

/-- **The velocity costs exactly one power of the frequency.** -/
theorem abs_hillSolutionDeriv_massive_cos_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) {t b : ℝ} (ht : t ∈ Icc 0 b) :
    |hillSolutionDeriv (massiveFreq m c s) (1, 0) t| ≤
      massiveFreq m c s 0 * Real.exp (K * t) := by
  have hcont := continuous_massiveFreq (m := m) hc s
  have hM1 : (1 : ℝ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) := le_max_left _ _
  have hMb : ∀ r, massiveFreq m c s r ^ (2 : ℕ) ≤ max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) := fun r =>
    (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _)
  have hbase := abs_hillSolutionDeriv_le (M := max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ))) hcont hM1 hMb
    (fun r => hasDerivAt_massiveFreq hm hcd s r) (fun r => massiveFreq_pos hm c s r)
    (fun r => abs_deriv_massiveFreq_le hm hcpos hK s r) (1, 0) ht
  rw [hillEnergy_cos_zero hcont hM1 hMb, Real.sqrt_sq (le_of_lt (massiveFreq_pos hm c s 0)),
    sub_zero] at hbase
  exact hbase

/-- **The acceleration costs two powers of the frequency**, and nothing else: it is the equation
itself, evaluated on the uniform bound. -/
theorem abs_hillSolutionSecond_massive_cos_le (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ t, HasDerivAt c (dc t) t) (hcpos : ∀ t, 0 < c t) (hK : ∀ t, |dc t| ≤ K * c t)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hs : s ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) {t b : ℝ} (ht : t ∈ Icc 0 b) :
    |(-(massiveFreq m c s t ^ (2 : ℕ))) * hillSolution (massiveFreq m c s) (1, 0) t| ≤
      massiveFreq m c s t ^ (2 : ℕ) * (max 1 (c 0 / c t) * Real.exp (K * t)) := by
  have huni := abs_hillSolution_massive_cos_le hm hc hcd hcpos hK hC hs ht
  have hsq : (0 : ℝ) ≤ massiveFreq m c s t ^ (2 : ℕ) := sq_nonneg _
  have habs : |(-(massiveFreq m c s t ^ (2 : ℕ))) * hillSolution (massiveFreq m c s) (1, 0) t|
      = massiveFreq m c s t ^ (2 : ℕ) * |hillSolution (massiveFreq m c s) (1, 0) t| := by
    rw [abs_mul, abs_neg, abs_of_nonneg hsq]
  rw [habs]
  exact mul_le_mul_of_nonneg_left huni hsq

/-! ## Continuity in the spatial frequency -/

/-- **Two massive fibres compared.** The mass cancels from the difference of the squared
frequencies, so the estimate is the one of the speeds alone. -/
theorem norm_hillFlow_massive_sub_le (hm : 0 < m) (hc : Continuous c) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    {s₁ s₂ : ℝ} (hs₁ : s₁ ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (hs₂ : s₂ ^ (2 : ℕ) ≤ S ^ (2 : ℕ)) (y₀ : ℝ × ℝ) {t b : ℝ}
    (ht : t ∈ Icc 0 b) :
    ‖hillFlow (massiveFreq m c s₁) y₀ t - hillFlow (massiveFreq m c s₂) y₀ t‖ ≤
      gronwallBound 0 (max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)))
        (C ^ (2 : ℕ) * |s₁ ^ (2 : ℕ) - s₂ ^ (2 : ℕ)| *
          (‖y₀‖ * Real.exp (max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) * b))) t := by
  have hδ : ∀ r, |massiveFreq m c s₁ r ^ (2 : ℕ) - massiveFreq m c s₂ r ^ (2 : ℕ)|
      ≤ C ^ (2 : ℕ) * |s₁ ^ (2 : ℕ) - s₂ ^ (2 : ℕ)| := by
    intro r
    rw [massiveFreq_sq hm, massiveFreq_sq hm]
    have hfac : m ^ (2 : ℕ) + (c r * s₁) ^ (2 : ℕ) - (m ^ (2 : ℕ) + (c r * s₂) ^ (2 : ℕ))
        = c r ^ (2 : ℕ) * (s₁ ^ (2 : ℕ) - s₂ ^ (2 : ℕ)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (sq_nonneg (c r))]
    exact mul_le_mul_of_nonneg_right (hC r) (abs_nonneg _)
  exact norm_hillFlow_sub_le (continuous_massiveFreq hc m s₁) (continuous_massiveFreq hc m s₂)
    (le_max_left _ _)
    (fun r => (massiveFreq_sq_le hm hC hs₁ r).trans (le_max_right _ _))
    (fun r => (massiveFreq_sq_le hm hC hs₂ r).trans (le_max_right _ _)) hδ
    (mul_nonneg (sq_nonneg _) (abs_nonneg _)) y₀ ht

/-- **The massive fibre is continuous in the spatial frequency**, hence measurable — the hypothesis a
synthesis over frequencies needs. -/
theorem continuousAt_hillFlow_massive (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (y₀ : ℝ × ℝ) {t b : ℝ} (ht : t ∈ Icc 0 b) (s₀ : ℝ) :
    ContinuousAt (fun s => hillFlow (massiveFreq m c s) y₀ t) s₀ := by
  set S : ℝ := |s₀| + 1 with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hs₀ : s₀ ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by
    have h1 : |s₀| ≤ S := by simp [hSdef]
    nlinarith [sq_abs s₀, abs_nonneg s₀]
  set M : ℝ := max 1 (m ^ (2 : ℕ) + C ^ (2 : ℕ) * S ^ (2 : ℕ)) with hM
  set B : ℝ := ‖y₀‖ * Real.exp (M * b) with hB
  have hnear : ∀ᶠ s in nhds s₀, s ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by
    have hball : Metric.ball s₀ 1 ∈ nhds s₀ := Metric.ball_mem_nhds s₀ one_pos
    refine Filter.eventually_of_mem hball fun s hs => ?_
    have hdist : |s - s₀| < 1 := by simpa [Real.dist_eq] using hs
    have habs : |s| ≤ S := by
      have hle : |s| ≤ |s - s₀| + |s₀| := by
        cases abs_cases (s - s₀) with
        | inl h => cases abs_cases s with
          | inl h1 => cases abs_cases s₀ with
            | inl h2 => linarith [h.1, h1.1, h2.1]
            | inr h2 => linarith [h.1, h1.1, h2.1]
          | inr h1 => cases abs_cases s₀ with
            | inl h2 => linarith [h.1, h1.1, h2.1]
            | inr h2 => linarith [h.1, h1.1, h2.1]
        | inr h => cases abs_cases s with
          | inl h1 => cases abs_cases s₀ with
            | inl h2 => linarith [h.1, h1.1, h2.1]
            | inr h2 => linarith [h.1, h1.1, h2.1]
          | inr h1 => cases abs_cases s₀ with
            | inl h2 => linarith [h.1, h1.1, h2.1]
            | inr h2 => linarith [h.1, h1.1, h2.1]
      rw [hSdef]
      linarith
    nlinarith [sq_abs s, abs_nonneg s]
  have hle : ∀ᶠ s in nhds s₀,
      dist (hillFlow (massiveFreq m c s) y₀ t) (hillFlow (massiveFreq m c s₀) y₀ t) ≤
        gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t := by
    filter_upwards [hnear] with s hs
    rw [dist_eq_norm]
    exact norm_hillFlow_massive_sub_le hm hc hC hs hs₀ y₀ ht
  have hzero : Filter.Tendsto
      (fun s => gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t) (nhds s₀) (nhds 0) := by
    have hcontε : Continuous fun ε : ℝ => gronwallBound 0 M ε t :=
      gronwallBound_continuous_ε 0 M t
    have hmap : Filter.Tendsto (fun s : ℝ => C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) (nhds s₀) (nhds 0) := by
      have hcont : Continuous fun s : ℝ => C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B := by fun_prop
      have := hcont.tendsto s₀
      simpa using this
    have hcomp := (hcontε.tendsto 0).comp hmap
    have hval : ((fun ε : ℝ => gronwallBound 0 M ε t) ∘
        fun s : ℝ => C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B)
        = fun s : ℝ => gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t := rfl
    rw [hval] at hcomp
    simpa [gronwallBound_ε0_δ0] using hcomp
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hzero' := Metric.tendsto_nhds.mp hzero ε hε
  filter_upwards [hle, hzero'] with s hs hz
  have habs : |gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t| < ε := by
    simpa [Real.dist_eq] using hz
  calc dist (hillFlow (massiveFreq m c s) y₀ t) (hillFlow (massiveFreq m c s₀) y₀ t)
      ≤ gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t := hs
    _ ≤ |gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t| := le_abs_self _
    _ < ε := habs

end MassiveFrequency

end GaloisForLFunctions.HTGeometry
