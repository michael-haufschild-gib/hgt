import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.RHTower.FermiNymanCorrelationJets

/-!
# The transform of the critical state has its poles at the zeros

The state equation continues the transform `L F` from `Re w > -4` to `Re w > -8`:
`L F(w) = -R(w + 8)/a`, where `R` is the pole-free remainder (written with `(s-1)ζ(s)`). On
`Re w > -8` this continuation is holomorphic exactly off the points `ρ - 17/2`, `ρ` a zero of `ζ`
right of the critical line; at each such point it has a simple pole with residue

  `-m_ρ · L F(ρ - ½) / a`,

nonzero because the transform of the state has no zero on `Re w ≥ 0`. The zeros of `ζ` right of the
line are, eight units to the left, exactly the singularities of the state.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The continuation of the state's transform through the state equation. -/
def stateContinuation (W₀ : ℝ) (F : ℝ → ℝ) (w : ℂ) : ℂ :=
  -stateRemainder F (w + 8) / criticalAliasCoefficient W₀

/-- `(s - 1)ζ(s)` vanishes exactly at the zeros of `ζ`. -/
theorem zetaEntire_ne_zero_of_riemannZeta_ne_zero {s : ℂ} (h : riemannZeta s ≠ 0) :
    zetaEntire s ≠ 0 := by
  by_cases hs : s = 1
  · subst hs; rw [zetaEntire_eval_one]; exact one_ne_zero
  · rw [zetaEntire_eq hs]; exact mul_ne_zero (sub_ne_zero.mpr hs) h

/-- **Agreement.** On `Re w > -4` the continuation is the transform of the state. -/
theorem stateContinuation_eq_laplace {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : -4 < w.re) :
    stateContinuation W₀ F w = negativeHalfLineLaplace (cx F) w := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hLap := differentiableOn_laplace_of_sq hd.meas hd.support hd.exponential
  have hEq := stateEquation_eqOn_zero hW hthreshold hF (κ := -(8 / 2)) (by norm_num) hLap
  have hp : max 1 (-(8 / 2) + 8) < (w + 8).re := by
    rw [max_lt_iff]; simp; constructor <;> linarith
  have h0 := hEq hp
  have hne : w + 8 ≠ 1 / 2 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hζ : riemannZeta (1 / 2 + (w + 8)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  rw [stateEquation_eq_remainder hd hne hζ, add_sub_cancel_right] at h0
  have hα : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  unfold stateContinuation
  rw [div_eq_iff hα]
  simp only [Pi.zero_apply] at h0
  linear_combination -h0

/-- **Holomorphy.** On `Re w > -8` the continuation is holomorphic wherever `ζ(w + 17/2) ≠ 0`. -/
theorem differentiableAt_stateContinuation {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {w : ℂ} (hw : -8 < w.re)
    (hζ : riemannZeta (w + 17 / 2) ≠ 0) : DifferentiableAt ℂ (stateContinuation W₀ F) w := by
  have hz : zetaEntire (1 / 2 + (w + 8)) ≠ 0 := by
    rw [show (1 : ℂ) / 2 + (w + 8) = w + 17 / 2 by ring]
    exact zetaEntire_ne_zero_of_riemannZeta_ne_zero hζ
  have hR := (differentiableAt_stateRemainder hF (p := w + 8) (by simp; linarith) hz).comp w
    (differentiableAt_id.add_const (8 : ℂ))
  exact hR.neg.div_const _

/-- **Residue law.** At `ρ - 17/2`, `ρ` a zero right of the line, the continuation has a simple pole
with residue `-m_ρ L F(ρ - ½)/a`. -/
theorem tendsto_stateContinuation_residue {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ : 1 / 2 < ρ.re) :
    Tendsto (fun w => (w - (ρ - 17 / 2)) * stateContinuation W₀ F w) (𝓝[≠] (ρ - 17 / 2))
      (𝓝 (-(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
        negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / criticalAliasCoefficient W₀)) := by
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at hζ; exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hζ
  set z₀ := ρ - 1 / 2 with hz₀
  have hz₀re : 0 < z₀.re := by rw [hz₀]; simp; linarith
  -- residue of the logarithmic derivative of `(s-1)ζ(s)` at `ρ`
  have hzE : zetaEntire ρ = 0 := by rw [zetaEntire_eq hρ1, hζ, mul_zero]
  have hord : analyticOrderAt zetaEntire ρ = analyticOrderAt riemannZeta ρ :=
    analyticOrderAt_zetaEntire_of_ne_one hρ1
  have hres := logDeriv_iteratedDeriv_residue_of_zero (differentiable_zetaEntire.analyticAt ρ)
    (by rw [hord]; exact RHTower.analyticOrderAt_riemannZeta_ne_top hρ1) hzE 0
  simp only [zero_add, pow_one, iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one, hord] at hres
  -- the remainder splits into a holomorphic part and the Euler part
  set A : ℂ → ℂ := fun p => stateGamma F p - dslope (negativeHalfLineLaplace (cx F)) (1 / 2) p -
    stateTail F p + negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2) with hAdef
  have hsplit : ∀ p, stateRemainder F p = A p +
      negativeHalfLineLaplace (cx F) p * logDeriv zetaEntire (1 / 2 + p) := fun p => by
    simp only [stateRemainder, hAdef]; ring
  have hopen0 : IsOpen {p : ℂ | 0 < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopen4 : IsOpen {p : ℂ | -(8 / 2) < p.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLap := differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
  have hLc : ContinuousAt (negativeHalfLineLaplace (cx F)) z₀ :=
    (hLap.differentiableAt (hopen4.mem_nhds (by show -(8 / 2) < z₀.re; linarith))).continuousAt
  have hAc : ContinuousAt A z₀ := by
    have hG := (differentiableOn_stateGamma hF).differentiableAt (hopen0.mem_nhds hz₀re)
    have hT := (differentiableOn_stateTail hF).differentiableAt (hopen0.mem_nhds hz₀re)
    have hD : DifferentiableAt ℂ (dslope (negativeHalfLineLaplace (cx F)) (1 / 2)) z₀ := by
      have hhalf : {p : ℂ | -(8 / 2) < p.re} ∈ 𝓝 ((1 : ℂ) / 2) :=
        hopen4.mem_nhds (by show -(8 / 2) < ((1 : ℂ) / 2).re; norm_num)
      exact ((differentiableOn_dslope hhalf).mpr hLap).differentiableAt
        (hopen4.mem_nhds (by show -(8 / 2) < z₀.re; linarith))
    have hP : DifferentiableAt ℂ
        (fun p : ℂ => negativeHalfLineLaplace (cx F) (-(1 / 2)) / (p + 1 / 2)) z₀ :=
      (differentiableAt_const _).div (differentiableAt_id.add_const _)
        (by intro h; have := congrArg Complex.re h; simp at this; linarith)
    exact (((hG.sub hD).sub hT).add hP).continuousAt
  -- shift to the zero
  have hshift : Tendsto (fun w : ℂ => 1 / 2 + (w + 8)) (𝓝[≠] (ρ - 17 / 2)) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun w : ℂ => 1 / 2 + (w + 8)) (𝓝 (ρ - 17 / 2))
          (𝓝 (1 / 2 + (ρ - 17 / 2 + 8))) :=
        tendsto_const_nhds.add (tendsto_id.add tendsto_const_nhds)
      rw [show (1 : ℂ) / 2 + (ρ - 17 / 2 + 8) = ρ by ring] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw h
      apply hw
      rw [Set.mem_singleton_iff] at h ⊢
      linear_combination h
  have hp8 : Tendsto (fun w : ℂ => w + 8) (𝓝[≠] (ρ - 17 / 2)) (𝓝 z₀) := by
    have h : Tendsto (fun w : ℂ => w + 8) (𝓝 (ρ - 17 / 2)) (𝓝 (ρ - 17 / 2 + 8)) :=
      tendsto_id.add tendsto_const_nhds
    rw [show ρ - 17 / 2 + 8 = z₀ by rw [hz₀]; ring] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlogres : Tendsto (fun w : ℂ => (w - (ρ - 17 / 2)) * logDeriv zetaEntire (1 / 2 + (w + 8)))
      (𝓝[≠] (ρ - 17 / 2)) (𝓝 ((analyticOrderAt riemannZeta ρ).toNat : ℂ)) := by
    refine (hres.comp hshift).congr fun w => ?_
    simp only [Function.comp, logDeriv_apply]
    ring_nf
  have hzero : Tendsto (fun w : ℂ => w - (ρ - 17 / 2)) (𝓝[≠] (ρ - 17 / 2)) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => w - (ρ - 17 / 2)) (𝓝 (ρ - 17 / 2)) (𝓝 (ρ - 17 / 2 - (ρ - 17 / 2))) :=
      tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have htot : Tendsto (fun w : ℂ => (w - (ρ - 17 / 2)) * A (w + 8) +
      negativeHalfLineLaplace (cx F) (w + 8) *
        ((w - (ρ - 17 / 2)) * logDeriv zetaEntire (1 / 2 + (w + 8)))) (𝓝[≠] (ρ - 17 / 2))
      (𝓝 (0 * A z₀ + negativeHalfLineLaplace (cx F) z₀ *
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ))) :=
    (hzero.mul (hAc.tendsto.comp hp8)).add ((hLc.tendsto.comp hp8).mul hlogres)
  rw [zero_mul, zero_add] at htot
  have hlim := (htot.div_const (criticalAliasCoefficient W₀ : ℂ)).neg
  have hfun : (fun w : ℂ => (w - (ρ - 17 / 2)) * stateContinuation W₀ F w) = fun w : ℂ =>
      -(((w - (ρ - 17 / 2)) * A (w + 8) + negativeHalfLineLaplace (cx F) (w + 8) *
        ((w - (ρ - 17 / 2)) * logDeriv zetaEntire (1 / 2 + (w + 8)))) /
          (criticalAliasCoefficient W₀ : ℂ)) := by
    funext w
    unfold stateContinuation
    rw [hsplit]
    ring
  rw [hfun, show -(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
      negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / (criticalAliasCoefficient W₀ : ℂ) =
      -(negativeHalfLineLaplace (cx F) z₀ * ((analyticOrderAt riemannZeta ρ).toNat : ℂ) /
        (criticalAliasCoefficient W₀ : ℂ)) by rw [hz₀]; ring]
  exact hlim

/-- At `ρ - 17/2` the continuation is singular: its residue is nonzero. -/
theorem not_differentiableAt_stateContinuation {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hρ : 1 / 2 < ρ.re) : ¬ DifferentiableAt ℂ (stateContinuation W₀ F) (ρ - 17 / 2) := by
  intro hdiff
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at hζ; exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hζ
  have h0 : Tendsto (fun w => (w - (ρ - 17 / 2)) * stateContinuation W₀ F w)
      (𝓝[≠] (ρ - 17 / 2)) (𝓝 0) := by
    have h := (tendsto_id.sub (tendsto_const_nhds (x := ρ - 17 / 2))).mul
      hdiff.continuousAt.tendsto
    simp only [id, sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h1 := tendsto_stateContinuation_residue (W₀ := W₀) hd hζ hρ
  have heq := tendsto_nhds_unique h1 h0
  have hm : ((analyticOrderAt riemannZeta ρ).toNat : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := one_le_toNat_analyticOrderAt_riemannZeta hρ1 hζ; omega)
  have hL : negativeHalfLineLaplace (cx F) (ρ - 1 / 2) ≠ 0 :=
    criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF
      (by simp; linarith)
  have hα : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  rw [neg_div, neg_eq_zero, div_eq_zero_iff] at heq
  rcases heq with h | h
  · exact mul_ne_zero hm hL h
  · exact hα h

/-- **The singularities of the state on `Re w > -8` are exactly the zeros right of the line,
shifted by `-17/2`.** -/
theorem differentiableAt_stateContinuation_iff {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ} (hw : -8 < w.re) :
    DifferentiableAt ℂ (stateContinuation W₀ F) w ↔ riemannZeta (w + 17 / 2) ≠ 0 := by
  refine ⟨fun hdiff hz => ?_, fun hz =>
    differentiableAt_stateContinuation (criticalHalfLineEnergyDomain_of_groundState hF) hw hz⟩
  have := not_differentiableAt_stateContinuation hW hthreshold hF hz (by simp; linarith)
  rw [show w + 17 / 2 - 17 / 2 = w by ring] at this
  exact this hdiff

/-- **Meromorphic continuation of the state.** Either RH holds, or the critical state exists, its
transform continues from `Re w > -4` to `Re w > -8`, and the continuation is singular exactly at the
points `ρ - 17/2` with `ζ(ρ) = 0`, each a simple pole of residue `-m_ρ L F(ρ - ½)/a`. -/
theorem riemannHypothesis_or_criticalState_poles_at_zeros :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        (∀ w : ℂ, -4 < w.re → stateContinuation W₀ F w = negativeHalfLineLaplace (cx F) w) ∧
        (∀ w : ℂ, -8 < w.re →
          (DifferentiableAt ℂ (stateContinuation W₀ F) w ↔ riemannZeta (w + 17 / 2) ≠ 0)) ∧
        ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re →
          Tendsto (fun w => (w - (ρ - 17 / 2)) * stateContinuation W₀ F w) (𝓝[≠] (ρ - 17 / 2))
            (𝓝 (-(((analyticOrderAt riemannZeta ρ).toNat : ℂ) *
              negativeHalfLineLaplace (cx F) (ρ - 1 / 2)) / criticalAliasCoefficient W₀)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, fun w hw => stateContinuation_eq_laplace hW ht hF hw,
      fun w hw => differentiableAt_stateContinuation_iff hW ht hF hw,
      fun ρ hζ hρ => tendsto_stateContinuation_residue
        (criticalHalfLineEnergyDomain_of_groundState hF) hζ hρ⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
