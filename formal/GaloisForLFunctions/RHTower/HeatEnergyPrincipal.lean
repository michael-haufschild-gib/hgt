import GaloisForLFunctions.RHTower.HeatMomentSplit
import GaloisForLFunctions.RHTower.BoundaryGermL2

/-!
# The principal part of the boundary germ on the window

The two-sided Jonquière expansion gives a principal approximation `P` of the boundary germ with a
linear error.  This module records `P`, the error bound, and the resulting bound on
`|f_s|² - |P|²`.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The side-dependent leading Jonquière coefficient. -/
noncomputable def jonquiereLeadAt (s : ℂ) (θ : ℝ) : ℂ :=
  if 0 < θ then jonquiereLead s else jonquiereLeadNeg s

/-- The principal part of the boundary germ. -/
noncomputable def germPrincipal (s : ℂ) (θ : ℝ) : ℂ :=
  jonquiereLeadAt s θ * ((|θ| : ℝ) : ℂ) ^ (s - 1) + riemannZeta s

theorem norm_jonquiereLeadAt_le (s : ℂ) (θ : ℝ) :
    ‖jonquiereLeadAt s θ‖ ≤ ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ := by
  rw [jonquiereLeadAt]
  split
  · have := norm_nonneg (jonquiereLeadNeg s)
    linarith
  · have := norm_nonneg (jonquiereLead s)
    linarith

/-- **The Jonquière error is linear in the phase.** -/
theorem norm_phaseGerm_sub_principal_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∀ θ ∈ Ioc (-Real.pi) Real.pi, θ ≠ 0 →
      ‖phaseGerm s θ - germPrincipal s θ‖ ≤ jonquiereConst s * |θ| := by
  intro θ hθ hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hu : (0 : ℝ) < -θ := by linarith
    have hu2 : -θ ≤ Real.pi := by linarith [hθ.1]
    have hgerm : phaseGerm s θ = expZeta ((-((-θ) / (2 * Real.pi)) : ℝ) : UnitAddCircle) s := by
      rw [phaseGerm]; congr 2; ring
    have hb := norm_expZeta_neg_sub_jonquiere_le h0 h1 hu hu2
    have habs : |θ| = -θ := abs_of_neg hneg
    have hP : germPrincipal s θ
        = jonquiereLeadNeg s * (((-θ : ℝ)) : ℂ) ^ (s - 1) + riemannZeta s := by
      rw [germPrincipal, jonquiereLeadAt, if_neg (by linarith : ¬ (0 < θ)), habs]
    rw [hgerm, hP, habs]
    exact hb
  · have hu2 : θ ≤ Real.pi := hθ.2
    have hb := norm_expZeta_sub_jonquiere_le h0 h1 hpos hu2
    have habs : |θ| = θ := abs_of_pos hpos
    have hP : germPrincipal s θ
        = jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s := by
      rw [germPrincipal, jonquiereLeadAt, if_pos hpos, habs]
    rw [phaseGerm, hP, habs]
    exact hb

theorem norm_germPrincipal_le {s : ℂ} (θ : ℝ) (hne : θ ≠ 0) :
    ‖germPrincipal s θ‖
      ≤ (‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖)
        * (|θ| ^ (s.re - 1) + 1) := by
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hpow : ‖(((|θ| : ℝ)) : ℂ) ^ (s - 1)‖ = |θ| ^ (s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.one_re]
  have hnn : (0 : ℝ) ≤ |θ| ^ (s.re - 1) := Real.rpow_nonneg (abs_nonneg θ) _
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, hpow]
  have hlead := norm_jonquiereLeadAt_le s θ
  nlinarith [norm_nonneg (jonquiereLead s), norm_nonneg (jonquiereLeadNeg s),
    norm_nonneg (riemannZeta s)]

/-- The constant in the quadratic error bound. -/
noncomputable def heatEnergyErrorConst (s : ℂ) : ℝ :=
  jonquiereConst s
    * ((‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
          + jonquiereConst s * Real.pi)
      + (‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖))

theorem heatEnergyErrorConst_nonneg (s : ℂ) : 0 ≤ heatEnergyErrorConst s := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have := jonquiereConst_nonneg s
  rw [heatEnergyErrorConst]
  positivity

/-- **The squared germ differs from its principal part by `O(|θ|^σ + |θ|)`.** -/
theorem norm_germSq_sub_principalSq_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∀ θ ∈ Ioc (-Real.pi) Real.pi, θ ≠ 0 →
      ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)
          - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)‖
        ≤ heatEnergyErrorConst s * (|θ| ^ s.re + |θ|) := by
  intro θ hθ hne
  have hpos : (0 : ℝ) < |θ| := abs_pos.mpr hne
  have hd := norm_phaseGerm_sub_principal_le h0 h1 θ hθ hne
  have hg := norm_phaseGerm_le h0 h1 θ hθ hne
  have hp := norm_germPrincipal_le (s := s) θ hne
  have hid : phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)
      - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)
      = (phaseGerm s θ - germPrincipal s θ) * (starRingEnd ℂ) (phaseGerm s θ)
        + germPrincipal s θ * (starRingEnd ℂ) (phaseGerm s θ - germPrincipal s θ) := by
    rw [map_sub]
    ring
  have hstep : ‖phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)
      - germPrincipal s θ * (starRingEnd ℂ) (germPrincipal s θ)‖
      ≤ ‖phaseGerm s θ - germPrincipal s θ‖ * (‖phaseGerm s θ‖ + ‖germPrincipal s θ‖) := by
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    ring_nf
    nlinarith [norm_nonneg (phaseGerm s θ - germPrincipal s θ), norm_nonneg (phaseGerm s θ),
      norm_nonneg (germPrincipal s θ)]
  refine hstep.trans ?_
  set Cg : ℝ := ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
    + jonquiereConst s * Real.pi with hCg
  set Cp : ℝ := ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖ with hCp
  have hsum : ‖phaseGerm s θ‖ + ‖germPrincipal s θ‖ ≤ (Cg + Cp) * (|θ| ^ (s.re - 1) + 1) := by
    have := hg
    have := hp
    nlinarith [hg, hp]
  have hprod : |θ| * (|θ| ^ (s.re - 1) + 1) = |θ| ^ s.re + |θ| := by
    have h1' : |θ| * |θ| ^ (s.re - 1) = |θ| ^ s.re := by
      nth_rewrite 1 [← Real.rpow_one |θ|]
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rw [mul_add, h1', mul_one]
  have hnn : (0 : ℝ) ≤ (Cg + Cp) * (|θ| ^ (s.re - 1) + 1) := by
    have hcg : 0 ≤ Cg := by
      rw [hCg]
      have := jonquiereConst_nonneg s
      have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
      positivity
    have hcp : 0 ≤ Cp := by
      rw [hCp]
      positivity
    have : (0 : ℝ) ≤ |θ| ^ (s.re - 1) := Real.rpow_nonneg (abs_nonneg θ) _
    positivity
  calc ‖phaseGerm s θ - germPrincipal s θ‖ * (‖phaseGerm s θ‖ + ‖germPrincipal s θ‖)
      ≤ (jonquiereConst s * |θ|) * ((Cg + Cp) * (|θ| ^ (s.re - 1) + 1)) := by
        refine mul_le_mul hd hsum (by positivity) ?_
        exact mul_nonneg (jonquiereConst_nonneg s) (abs_nonneg θ)
    _ = heatEnergyErrorConst s * (|θ| ^ s.re + |θ|) := by
        rw [heatEnergyErrorConst, ← hCg, ← hCp, ← hprod]
        ring

end RHTower
