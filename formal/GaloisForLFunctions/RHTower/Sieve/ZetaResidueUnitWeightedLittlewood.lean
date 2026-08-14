import GaloisForLFunctions.RHTower.WeightedLittlewoodRectangle
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling

/-!
# Multiplicity-exact Littlewood identity for the zeta residue unit

The entire residue unit `G(s) = (s - 1) * ζ(s)` has a finite, exact zero packet in every closed
rectangle.  Combining that packet's weighted argument principle with the fixed-contour Littlewood
identity gives the first horizontal moment of the actual zeta zeros, with analytic multiplicity.

The selected-contour capstone has no boundary-avoidance premise: finite zero avoidance chooses all
four admissible edges inside arbitrary prescribed separated ranges.
-/

open Complex MeasureTheory intervalIntegral Set Topology

namespace RHTower.Sieve

noncomputable section

private theorem analyticAt_logDeriv_zetaResidueUnit_of_ne {z : ℂ}
    (hz : zetaResidueUnit z ≠ 0) :
    AnalyticAt ℂ (logDeriv zetaResidueUnit) z := by
  have hGz : AnalyticAt ℂ zetaResidueUnit z := analyticAt_zetaResidueUnit z
  have h : AnalyticAt ℂ (fun w => deriv zetaResidueUnit w / zetaResidueUnit w) z :=
    hGz.deriv.div hGz hz
  refine h.congr ?_
  filter_upwards with w
  rw [logDeriv_apply]

/-- **Multiplicity-exact Littlewood rectangle identity for the zeta residue unit.**  Interior zeros
are retained with analytic multiplicity; only boundary nonvanishing is assumed. -/
theorem zetaResidueUnit_weighted_littlewood_rectangle
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂,
      zetaResidueUnit ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc T₁ T₂,
      zetaResidueUnit ((c : ℂ) + t * I) ≠ 0) :
    2 * Real.pi *
        (∑ w ∈ zetaResidueUnitClosedRectangleZeros
            ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I),
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) =
      (∫ t in T₁..T₂, Real.log ‖zetaResidueUnit ((c : ℂ) + t * I)‖)
        - (∫ t in T₁..T₂, Real.log ‖zetaResidueUnit ((d : ℂ) + t * I)‖)
        + (d - c) *
          (∫ t in T₁..T₂, (logDeriv zetaResidueUnit ((d : ℂ) + t * I)).re)
        + (∫ x in c..d,
          (x - c) * (logDeriv zetaResidueUnit ((x : ℂ) + T₁ * I)).im)
        - ∫ x in c..d,
          (x - c) * (logDeriv zetaResidueUnit ((x : ℂ) + T₂ * I)).im := by
  have hval : rectIntegral
      (fun z => (z - (c : ℂ)) * logDeriv zetaResidueUnit z)
      ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I) =
        2 * Real.pi * I *
          ∑ w ∈ zetaResidueUnitClosedRectangleZeros
              ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I),
            ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) * (w - (c : ℂ)) := by
    have harg := rectIntegral_mul_logDeriv_zetaResidueUnit_eq_closedRectangleZeroSum
      (g := fun z => z - (c : ℂ))
      (z₁ := (c : ℂ) + T₁ * I) (z₂ := (d : ℂ) + T₂ * I)
      (U := Set.univ) isOpen_univ
      (fun z _ => analyticAt_id.sub analyticAt_const)
      (by simp) (by simpa using hcd) (by simpa using hT)
      (by simpa using hbot) (by simpa using htop)
      (by simpa using hright) (by simpa using hleft)
    simpa using harg
  have hqbot : ContinuousOn
      (fun x : ℝ => logDeriv zetaResidueUnit ((x : ℂ) + T₁ * I)) (uIcc c d) := by
    intro x hx
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₁ * I)
      (analyticAt_logDeriv_zetaResidueUnit_of_ne (hbot x hx)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₁ * I) x)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqtop : ContinuousOn
      (fun x : ℝ => logDeriv zetaResidueUnit ((x : ℂ) + T₂ * I)) (uIcc c d) := by
    intro x hx
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₂ * I)
      (analyticAt_logDeriv_zetaResidueUnit_of_ne (htop x hx)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₂ * I) x)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqright : ContinuousOn
      (fun t : ℝ => logDeriv zetaResidueUnit ((d : ℂ) + t * I)) (uIcc T₁ T₂) := by
    intro t ht
    have hc := ContinuousAt.comp (f := fun y : ℝ => (d : ℂ) + y * I)
      (analyticAt_logDeriv_zetaResidueUnit_of_ne (hright t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (d : ℂ) + y * I) t)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hqleft : ContinuousOn
      (fun t : ℝ => logDeriv zetaResidueUnit ((c : ℂ) + t * I)) (uIcc T₁ T₂) := by
    intro t ht
    have hc := ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + y * I)
      (analyticAt_logDeriv_zetaResidueUnit_of_ne (hleft t ht)).continuousAt
      (by fun_prop : ContinuousAt (fun y : ℝ => (c : ℂ) + y * I) t)
    simpa [Function.comp_def] using hc.continuousWithinAt
  apply weighted_littlewood_from_rectIntegral hval hqbot hqtop hqright hqleft
  · intro x _
    exact (analyticAt_zetaResidueUnit _).differentiableAt.hasDerivAt
  · intro x _
    exact (analyticAt_zetaResidueUnit _).differentiableAt.hasDerivAt
  · intro t _
    exact (analyticAt_zetaResidueUnit _).differentiableAt.hasDerivAt
  · intro t _
    exact (analyticAt_zetaResidueUnit _).differentiableAt.hasDerivAt
  · exact hbot
  · exact htop
  · exact hright
  · exact hleft

/-- Analytic-multiplicity-weighted first horizontal moment of residue-unit zeros in the symmetric
rectangle `[c,d] × [-T,T]`. -/
noncomputable def zetaLittlewoodZeroMass (c d T : ℝ) : ℝ :=
  ∑ w ∈ zetaResidueUnitClosedRectangleZeros
      ((c : ℂ) + (-T : ℝ) * I) ((d : ℂ) + T * I),
    ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)

/-- Analytic-multiplicity-weighted count of zeros in the symmetric rectangle whose real part is at
least `σ`. -/
noncomputable def zetaLittlewoodZeroCountAbove (c d T σ : ℝ) : ℝ :=
  ∑ w ∈ (zetaResidueUnitClosedRectangleZeros
      ((c : ℂ) + (-T : ℝ) * I) ((d : ℂ) + T * I)).filter (fun w => σ ≤ w.re),
    ((analyticOrderAt zetaResidueUnit w).toNat : ℝ)

/-- The first horizontal zeta-zero moment controls the multiplicity-weighted count to the right of
every threshold `σ`. -/
theorem zetaLittlewoodZeroCountAbove_mul_le_zeroMass
    {c d T σ : ℝ} (hcd : c ≤ d) :
    (σ - c) * zetaLittlewoodZeroCountAbove c d T σ ≤
      zetaLittlewoodZeroMass c d T := by
  let Z : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + (-T : ℝ) * I) ((d : ℂ) + T * I)
  have hleft : ∀ w ∈ Z, c ≤ w.re := by
    intro w hw
    have hwK := (mem_zetaResidueUnitClosedRectangleZeros.mp hw).1
    have hwre := (Complex.mem_reProdIm.mp hwK).1
    have hwre' : w.re ∈ Set.Icc c d := by
      simpa [Z, uIcc_of_le hcd] using hwre
    exact hwre'.1
  simpa [Z, zetaLittlewoodZeroCountAbove, zetaLittlewoodZeroMass] using
    (weighted_count_mul_le_firstMoment Z
      (fun w => (analyticOrderAt zetaResidueUnit w).toNat) Complex.re hleft
      (σ := σ))

/-- Branch-free boundary functional equal to `2π` times `zetaLittlewoodZeroMass` on an admissible
rectangle. -/
noncomputable def zetaLittlewoodBoundary (c d T : ℝ) : ℝ :=
  (∫ t in (-T)..T, Real.log ‖zetaResidueUnit ((c : ℂ) + t * I)‖)
    - (∫ t in (-T)..T, Real.log ‖zetaResidueUnit ((d : ℂ) + t * I)‖)
    + (d - c) *
      (∫ t in (-T)..T, (logDeriv zetaResidueUnit ((d : ℂ) + t * I)).re)
    + (∫ x in c..d,
      (x - c) * (logDeriv zetaResidueUnit ((x : ℂ) + (-T : ℝ) * I)).im)
    - ∫ x in c..d,
      (x - c) * (logDeriv zetaResidueUnit ((x : ℂ) + T * I)).im

/-- Exact Littlewood identity for the actual zeta residue unit on an admissible symmetric
rectangle. -/
theorem two_pi_mul_zetaLittlewoodZeroMass_eq_boundary
    {c d T : ℝ} (hcd : c < d) (hT : 0 < T)
    (hbot : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + (-T : ℝ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + T * I) ≠ 0)
    (hright : ∀ t ∈ uIcc (-T) T,
      zetaResidueUnit ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + t * I) ≠ 0) :
    2 * Real.pi * zetaLittlewoodZeroMass c d T = zetaLittlewoodBoundary c d T := by
  simpa [zetaLittlewoodZeroMass, zetaLittlewoodBoundary] using
    (zetaResidueUnit_weighted_littlewood_rectangle
      (c := c) (d := d) (T₁ := -T) (T₂ := T) hcd (by linarith)
      hbot htop hright hleft)

/-- On an admissible symmetric rectangle, Littlewood's boundary controls every
analytic-multiplicity-weighted zero count to the right of `σ`. -/
theorem two_pi_mul_zeroCountAbove_le_zetaLittlewoodBoundary
    {c d T σ : ℝ} (hcd : c < d) (hT : 0 < T)
    (hbot : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + (-T : ℝ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + T * I) ≠ 0)
    (hright : ∀ t ∈ uIcc (-T) T,
      zetaResidueUnit ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + t * I) ≠ 0) :
    2 * Real.pi * ((σ - c) * zetaLittlewoodZeroCountAbove c d T σ) ≤
      zetaLittlewoodBoundary c d T := by
  calc
    _ ≤ 2 * Real.pi * zetaLittlewoodZeroMass c d T :=
      mul_le_mul_of_nonneg_left
        (zetaLittlewoodZeroCountAbove_mul_le_zeroMass hcd.le) (by positivity)
    _ = _ := two_pi_mul_zetaLittlewoodZeroMass_eq_boundary
      hcd hT hbot htop hright hleft

/-- **Unconditional selected-contour Littlewood identity for zeta.**  Every prescribed separated
box of positive abscissae and heights contains a symmetric rectangle on which the exact
multiplicity-weighted Littlewood identity holds.  Boundary nonvanishing is discharged by finite
zero avoidance and does not occur in the conclusion. -/
theorem exists_zetaLittlewoodZeroMass_eq_boundary
    {a b d₀ d₁ T₀ T₁ : ℝ}
    (ha : 0 < a) (hab : a < b) (hsep : b < d₀) (hdd : d₀ < d₁)
    (hT₀ : 0 < T₀) (hTT : T₀ < T₁) :
    ∃ c d T : ℝ,
      c ∈ Ioo a b ∧ d ∈ Ioo d₀ d₁ ∧ T ∈ Ioo T₀ T₁ ∧
      2 * Real.pi * zetaLittlewoodZeroMass c d T = zetaLittlewoodBoundary c d T := by
  obtain ⟨c, d, T, hcI, hdI, hTI, hbot, htop, hright, hleft⟩ :=
    exists_zetaResidueUnit_zeroFreeBoundary_rectangle
      ha hab hsep hdd hT₀ hTT
  have hcd : c < d := lt_trans hcI.2 (hsep.trans hdI.1)
  have hT : 0 < T := hT₀.trans hTI.1
  exact ⟨c, d, T, hcI, hdI, hTI,
    two_pi_mul_zetaLittlewoodZeroMass_eq_boundary hcd hT hbot htop hright hleft⟩

/-- **Unconditional selected-contour zero-count inequality.**  Given a threshold strictly between
the prescribed left and right abscissa ranges, finite avoidance selects a contour whose exact
Littlewood boundary controls the multiplicity-weighted zeros to the right of that threshold. -/
theorem exists_zetaLittlewoodZeroCountAbove_le_boundary
    {a b σ d₀ d₁ T₀ T₁ : ℝ}
    (ha : 0 < a) (hab : a < b) (hbσ : b < σ) (hσd : σ < d₀) (hdd : d₀ < d₁)
    (hT₀ : 0 < T₀) (hTT : T₀ < T₁) :
    ∃ c d T : ℝ,
      c ∈ Ioo a b ∧ d ∈ Ioo d₀ d₁ ∧ T ∈ Ioo T₀ T₁ ∧
      c < σ ∧ σ < d ∧
      2 * Real.pi * ((σ - c) * zetaLittlewoodZeroCountAbove c d T σ) ≤
        zetaLittlewoodBoundary c d T := by
  obtain ⟨c, d, T, hcI, hdI, hTI, hbot, htop, hright, hleft⟩ :=
    exists_zetaResidueUnit_zeroFreeBoundary_rectangle
      ha hab (hbσ.trans hσd) hdd hT₀ hTT
  have hcσ : c < σ := hcI.2.trans hbσ
  have hσd' : σ < d := hσd.trans hdI.1
  have hcd : c < d := hcσ.trans hσd'
  have hT : 0 < T := hT₀.trans hTI.1
  exact ⟨c, d, T, hcI, hdI, hTI, hcσ, hσd',
    two_pi_mul_zeroCountAbove_le_zetaLittlewoodBoundary
      hcd hT hbot htop hright hleft⟩

end

end RHTower.Sieve
