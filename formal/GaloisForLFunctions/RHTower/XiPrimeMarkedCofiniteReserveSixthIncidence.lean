import GaloisForLFunctions.RHTower.XiPrimeMarkedFiniteSixthStrictCone
import GaloisForLFunctions.RHTower.XiPrimeMarkedCofiniteReserveAllPowerSmall

/-!
# Finite sixth-moment incidence with a positive-scale cofinite reserve

The actual completed source lies in a strict three-moment cone.  Its interior
margin absorbs the first three power energies of one cofinite RVM-plus-cycle
reserve, and a finite nonnegative head matches the residual triple exactly.
This is a finite sixth-order incidence statement; it does not match higher
moments or identify the Xi divisor.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem strictThreeMomentCone_stable_under_nonnegative_debit
    {E F G : ℝ} (hE : 0 < E) (hF : 0 < F) (hG : 0 < G)
    (h9 : 9 * F < E ^ (2 : ℕ))
    (hstrong : 247 * F ^ (2 : ℕ) < 243 * E * G)
    (hceil : G ^ (2 : ℕ) < F ^ (3 : ℕ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r₁ r₂ r₃ : ℝ,
      0 ≤ r₁ → r₁ < ε → 0 ≤ r₂ → r₂ < ε → 0 ≤ r₃ → r₃ < ε →
      0 < E-r₁ ∧ 0 < F-r₂ ∧
      9 * (F-r₂) < (E-r₁) ^ (2 : ℕ) ∧
      247 * (F-r₂) ^ (2 : ℕ) < 243 * (E-r₁) * (G-r₃) ∧
      (G-r₃) ^ (2 : ℕ) < (F-r₂) ^ (3 : ℕ) := by
  have hev : ∀ᶠ r : ℝ in 𝓝 0,
      0 < E-r ∧ 0 < F-r ∧ 0 < G-r ∧
      9*F < (E-r)^2 ∧
      247*F^2 < 243*(E-r)*(G-r) ∧
      G^2 < (F-r)^3 := by
    have h₁ : ∀ᶠ r : ℝ in 𝓝 0, 0 < E-r := by
      have hc : ContinuousAt (fun r : ℝ => E-r) 0 := by fun_prop
      exact continuousAt_const.eventually_lt hc (by simpa using hE)
    have h₂ : ∀ᶠ r : ℝ in 𝓝 0, 0 < F-r := by
      have hc : ContinuousAt (fun r : ℝ => F-r) 0 := by fun_prop
      exact continuousAt_const.eventually_lt hc (by simpa using hF)
    have h₃ : ∀ᶠ r : ℝ in 𝓝 0, 0 < G-r := by
      have hc : ContinuousAt (fun r : ℝ => G-r) 0 := by fun_prop
      exact continuousAt_const.eventually_lt hc (by simpa using hG)
    have h₄ : ∀ᶠ r : ℝ in 𝓝 0, 9*F < (E-r)^2 := by
      have hc : ContinuousAt (fun r : ℝ => (E-r)^2) 0 := by fun_prop
      simpa using (continuousAt_const.eventually_lt hc (by simpa using h9))
    have h₅ : ∀ᶠ r : ℝ in 𝓝 0,
        247*F^2 < 243*(E-r)*(G-r) := by
      have hc : ContinuousAt (fun r : ℝ => 243*(E-r)*(G-r)) 0 := by fun_prop
      simpa using (continuousAt_const.eventually_lt hc (by simpa using hstrong))
    have h₆ : ∀ᶠ r : ℝ in 𝓝 0, G^2 < (F-r)^3 := by
      have hc : ContinuousAt (fun r : ℝ => (F-r)^3) 0 := by fun_prop
      simpa using (continuousAt_const.eventually_lt hc (by simpa using hceil))
    filter_upwards [h₁,h₂,h₃,h₄,h₅,h₆] with r hr₁ hr₂ hr₃ hr₄ hr₅ hr₆
    exact ⟨hr₁,hr₂,hr₃,hr₄,hr₅,hr₆⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hev
  let ε : ℝ := δ/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεball : ε ∈ Metric.ball (0:ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp [ε]
    linarith
  obtain ⟨hEε,hFε,hGε,h9ε,hstrongε,hceilε⟩ := hball hεball
  refine ⟨ε,hε,?_⟩
  intro r₁ r₂ r₃ hr₁ hr₁ε hr₂ hr₂ε hr₃ hr₃ε
  have hE' : 0 < E-r₁ := by linarith
  have hF' : 0 < F-r₂ := by linarith
  have hG' : 0 < G-r₃ := by linarith
  have hEcmp : E-ε ≤ E-r₁ := by linarith
  have hFcmp : F-ε ≤ F-r₂ := by linarith
  have hGcmp : G-ε ≤ G-r₃ := by linarith
  have hEsq : (E-ε)^2 ≤ (E-r₁)^2 := by gcongr
  have hFsq : (F-r₂)^2 ≤ F^2 := by gcongr; linarith
  have hFcube : (F-ε)^3 ≤ (F-r₂)^3 := by gcongr
  have hGsq : (G-r₃)^2 ≤ G^2 := by gcongr; linarith
  have hprod : (E-ε)*(G-ε) ≤ (E-r₁)*(G-r₃) := by
    exact mul_le_mul hEcmp hGcmp hGε.le hE'.le
  refine ⟨hE',hF',?_,?_,?_⟩
  · nlinarith [hEsq]
  · nlinarith [hFsq,hprod]
  · exact (hGsq.trans_lt hceilε).trans_le hFcube

/-- Half of the even trace contribution of one self-adjoint reserve power. -/
def routeKReservePowerEnergy (N : ℕ) (δ : ℝ) (j : ℕ) : ℝ :=
  ContinuousLinearMap.hsNormSq ((routeKVariableCofiniteReserve N δ) ^ (j+1))

def routeKResidualHalfMass (N : ℕ) (δ : ℝ) : ℝ :=
  routeKQuarticHalfMass - routeKReservePowerEnergy N δ 0

def routeKResidualHalfEnergy (N : ℕ) (δ : ℝ) : ℝ :=
  routeKQuarticHalfEnergy - routeKReservePowerEnergy N δ 1

def routeKResidualHalfSixth (N : ℕ) (δ : ℝ) : ℝ :=
  normalizedPrimeArchMoment 2 / 2 - routeKReservePowerEnergy N δ 2

/-- A cofinite RVM tail with a genuinely positive cycle scale and one finite
nonnegative head exactly share the actual source's quadratic, quartic and
sixth half-moments.  The prime prefix is arbitrary. -/
theorem exists_routeKFiniteSixthMatchedHead_with_cofiniteReserve (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧ ∃ δ : ℝ, 0 < δ ∧
      ∃ M : ℕ, 10 ≤ M ∧ ∃ x : ℝ,
        0 ≤ x ∧
        (∀ i : Fin (M-1), 0 ≤ reverseResidualSelectorAux
          (routeKResidualHalfMass N δ-x)
          (routeKResidualHalfEnergy N δ-x^2) (M-1) (M-3) i) ∧
        x + (∑ i : Fin (M-1), reverseResidualSelectorAux
          (routeKResidualHalfMass N δ-x)
          (routeKResidualHalfEnergy N δ-x^2) (M-1) (M-3) i) +
            routeKReservePowerEnergy N δ 0 = routeKQuarticHalfMass ∧
        x^2 + (∑ i : Fin (M-1),
          (reverseResidualSelectorAux
            (routeKResidualHalfMass N δ-x)
            (routeKResidualHalfEnergy N δ-x^2) (M-1) (M-3) i)^2) +
            routeKReservePowerEnergy N δ 1 = routeKQuarticHalfEnergy ∧
        x^3 + (∑ i : Fin (M-1),
          (reverseResidualSelectorAux
            (routeKResidualHalfMass N δ-x)
            (routeKResidualHalfEnergy N δ-x^2) (M-1) (M-3) i)^3) +
            routeKReservePowerEnergy N δ 2 = normalizedPrimeArchMoment 2 / 2 := by
  let E : ℝ := routeKQuarticHalfMass
  let F : ℝ := routeKQuarticHalfEnergy
  let G : ℝ := normalizedPrimeArchMoment 2 / 2
  have hE : 0 < E := routeKQuarticHalfMass_pos
  have hF : 0 < F := routeKQuarticHalfEnergy_pos
  have hG : 0 < G := by
    dsimp [G]
    have h := normalizedPrimeArchMoment_two_pos
    linarith
  have h9 : 9 * F < E^2 := routeKQuarticHalfMass_sq_gt_nine_mul_halfEnergy
  have hstrong : 247 * F^2 < 243 * E * G :=
    routeK_sourceStrongHankel_247_243_strict
  have hceil : G^2 < F^3 := routeKHalfSixth_sq_lt_halfFourth_cube
  obtain ⟨ε,hε,hstable⟩ :=
    strictThreeMomentCone_stable_under_nonnegative_debit
      hE hF hG h9 hstrong hceil
  obtain ⟨N,hN,δ,hδ,hsmall⟩ :=
    exists_routeKVariableCofiniteReserve_allPowerEnergiesSmall hε Nmin
  have hr₁ : routeKReservePowerEnergy N δ 0 < ε := by
    simpa only [routeKReservePowerEnergy] using hsmall 0
  have hr₂ : routeKReservePowerEnergy N δ 1 < ε := by
    simpa only [routeKReservePowerEnergy] using hsmall 1
  have hr₃ : routeKReservePowerEnergy N δ 2 < ε := by
    simpa only [routeKReservePowerEnergy] using hsmall 2
  have hr₁nonneg : 0 ≤ routeKReservePowerEnergy N δ 0 :=
    ContinuousLinearMap.hsNormSq_nonneg _
  have hr₂nonneg : 0 ≤ routeKReservePowerEnergy N δ 1 :=
    ContinuousLinearMap.hsNormSq_nonneg _
  have hr₃nonneg : 0 ≤ routeKReservePowerEnergy N δ 2 :=
    ContinuousLinearMap.hsNormSq_nonneg _
  obtain ⟨hE',hF',h9',hstrong',hceil'⟩ := hstable
    (routeKReservePowerEnergy N δ 0)
    (routeKReservePowerEnergy N δ 1)
    (routeKReservePowerEnergy N δ 2)
    hr₁nonneg hr₁ hr₂nonneg hr₂ hr₃nonneg hr₃
  change 0 < routeKResidualHalfMass N δ at hE'
  change 0 < routeKResidualHalfEnergy N δ at hF'
  change 9 * routeKResidualHalfEnergy N δ <
    (routeKResidualHalfMass N δ)^2 at h9'
  change 247 * (routeKResidualHalfEnergy N δ)^2 <
    243 * routeKResidualHalfMass N δ * routeKResidualHalfSixth N δ at hstrong'
  change (routeKResidualHalfSixth N δ)^2 <
    (routeKResidualHalfEnergy N δ)^3 at hceil'
  obtain ⟨M,hM,x,hx,hpt,hmass,henergy,hsixth⟩ :=
    exists_finiteThreeMomentHead_of_strictCone
      hE' hF' h9' hstrong' hceil'
  refine ⟨N,hN,δ,hδ,M,hM,x,hx,hpt,?_,?_,?_⟩
  · dsimp [routeKResidualHalfMass] at hmass ⊢
    linarith
  · dsimp [routeKResidualHalfEnergy] at henergy ⊢
    linarith
  · dsimp [routeKResidualHalfSixth] at hsixth ⊢
    linarith

end
end RHTower
