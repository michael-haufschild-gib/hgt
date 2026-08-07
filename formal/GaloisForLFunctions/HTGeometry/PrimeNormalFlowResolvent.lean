import Mathlib
import GaloisForLFunctions.HTGeometry.CfcNormBound
import GaloisForLFunctions.HTGeometry.PrimeNormalBinomialResolvent

/-!
# The prime normal flow as an operator resolvent

For a bounded self-adjoint `T` and `L > ‖T‖/2` the operator `(L − T/2)^{-1/2}` solves the
differentiated prime-only boundary normal equation `(2L − T) F' + F = 0` with half-log trace the
identity.  The derivative is obtained from the isometric functional calculus: the difference
quotient of the symbol is uniformly small on the spectrum, so the difference quotient of the
operator converges in norm.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

section Scalar

/-- **The slope estimate for the inverse square root.**  The second-order defect of the difference
quotient is linear in the increment, uniformly over base points bounded away from the singularity.
The proof is algebraic: in the variables `p = √a`, `q = √b` the defect factors as
`(q−p)(q+2p) / (2p³q(p+q))`, and `q − p = (b−a)/(p+q)`. -/
theorem abs_flowSlope_le {a b s : ℝ} (hs : 0 < s) (ha : s ≤ Real.sqrt a) (hb : s ≤ Real.sqrt b)
    (hab : a ≠ b) :
    |((Real.sqrt b)⁻¹ - (Real.sqrt a)⁻¹) / (b - a) + (1 / 2) * (Real.sqrt a)⁻¹ ^ 3|
      ≤ |b - a| / (2 * s ^ 5) := by
  set p := Real.sqrt a with hpdef
  set q := Real.sqrt b with hqdef
  have hp0 : 0 < p := lt_of_lt_of_le hs ha
  have hq0 : 0 < q := lt_of_lt_of_le hs hb
  have hapos : 0 < a := by
    by_contra hc
    rw [not_lt] at hc
    rw [hpdef, Real.sqrt_eq_zero_of_nonpos hc] at hp0
    exact lt_irrefl 0 hp0
  have hbpos : 0 < b := by
    by_contra hc
    rw [not_lt] at hc
    rw [hqdef, Real.sqrt_eq_zero_of_nonpos hc] at hq0
    exact lt_irrefl 0 hq0
  have hpa : p ^ 2 = a := Real.sq_sqrt hapos.le
  have hqb : q ^ 2 = b := Real.sq_sqrt hbpos.le
  have hd : q ^ 2 - p ^ 2 ≠ 0 := by rw [hpa, hqb]; exact sub_ne_zero.mpr (Ne.symm hab)
  have hpq : 0 < p + q := by linarith
  have hexpr : (q⁻¹ - p⁻¹) / (b - a) + (1 / 2) * p⁻¹ ^ 3
      = (q ^ 2 - p ^ 2) * (q + 2 * p) / (2 * p ^ 3 * q * (p + q) ^ 2) := by
    rw [← hpa, ← hqb]
    field_simp
    ring
  rw [hexpr, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * p ^ 3 * q * (p + q) ^ 2),
    abs_mul, abs_of_pos (by positivity : (0:ℝ) < q + 2 * p), hpa, hqb]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : q + 2 * p ≤ 2 * (p + q) := by linarith
  have hs3 : s ^ 3 ≤ p ^ 3 := by gcongr
  have e1 : s ^ 3 * s ≤ p ^ 3 * q := mul_le_mul hs3 hb hs.le (by positivity)
  have h2 : 2 * s ^ 5 ≤ p ^ 3 * q * (p + q) := by
    have e2 : s ^ 3 * s * (2 * s) ≤ p ^ 3 * q * (p + q) :=
      mul_le_mul e1 (by linarith) (by positivity) (by positivity)
    calc 2 * s ^ 5 = s ^ 3 * s * (2 * s) := by ring
      _ ≤ p ^ 3 * q * (p + q) := e2
  have h3 : (q + 2 * p) * (2 * s ^ 5) ≤ 2 * p ^ 3 * q * (p + q) ^ 2 := by
    have e3 : (q + 2 * p) * (2 * s ^ 5) ≤ (2 * (p + q)) * (2 * s ^ 5) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have e4 : (2 * (p + q)) * (2 * s ^ 5) ≤ (2 * (p + q)) * (p ^ 3 * q * (p + q)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc (q + 2 * p) * (2 * s ^ 5) ≤ (2 * (p + q)) * (2 * s ^ 5) := e3
      _ ≤ (2 * (p + q)) * (p ^ 3 * q * (p + q)) := e4
      _ = 2 * p ^ 3 * q * (p + q) ^ 2 := by ring
  calc |b - a| * (q + 2 * p) * (2 * s ^ 5)
      = |b - a| * ((q + 2 * p) * (2 * s ^ 5)) := by ring
    _ ≤ |b - a| * (2 * p ^ 3 * q * (p + q) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)

end Scalar

section Flow

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- The symbol of the prime normal flow: `(L − t/2)^{-1/2}` in the spectral variable. -/
noncomputable def flowSymbol (L t : ℝ) : ℝ := (Real.sqrt (L - t / 2))⁻¹

/-- **The prime normal flow** `F(L) = (L I − T/2)^{-1/2}`. -/
noncomputable def primeNormalFlow (T : A) (L : ℝ) : A := cfc (flowSymbol L) T

/-- Spectral values of a self-adjoint element are bounded by its norm. -/
theorem abs_le_norm_of_mem_spectrum {T : A} {t : ℝ} (ht : t ∈ spectrum ℝ T) : |t| ≤ ‖T‖ := by
  simpa using spectrum.norm_le_norm_of_mem (𝕜 := ℝ) ht

/-- Past the spectral threshold the shifted spectral variable is positive. -/
theorem flow_shift_pos {T : A} {L t : ℝ} (hL : ‖T‖ / 2 < L) (ht : t ∈ spectrum ℝ T) :
    0 < L - t / 2 := by
  have h := abs_le_norm_of_mem_spectrum ht
  have : t ≤ ‖T‖ := le_trans (le_abs_self t) h
  linarith

theorem continuousOn_flowSymbol {T : A} {L : ℝ} (hL : ‖T‖ / 2 < L) :
    ContinuousOn (flowSymbol L) (spectrum ℝ T) := by
  refine ContinuousOn.inv₀ ?_ ?_
  · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
  · intro t ht
    exact ne_of_gt (Real.sqrt_pos.mpr (flow_shift_pos hL ht))

/-- The defect of the difference quotient of the flow symbol. -/
noncomputable def flowSlopeSymbol (L L' t : ℝ) : ℝ :=
  (L' - L)⁻¹ * (flowSymbol L' t - flowSymbol L t) + (1 / 2) * flowSymbol L t ^ 3

/-- **The uniform slope estimate on the spectrum.** -/
theorem abs_flowSlopeSymbol_le {T : A} {L L' t : ℝ} (hL : ‖T‖ / 2 < L)
    (hne : L' ≠ L) (hclose : |L' - L| < (L - ‖T‖ / 2) / 2) (ht : t ∈ spectrum ℝ T) :
    |flowSlopeSymbol L L' t| ≤ |L' - L| / (2 * Real.sqrt ((L - ‖T‖ / 2) / 2) ^ 5) := by
  have hδ : 0 < L - ‖T‖ / 2 := by linarith
  have hs : 0 < Real.sqrt ((L - ‖T‖ / 2) / 2) := Real.sqrt_pos.mpr (by linarith)
  have htn : t ≤ ‖T‖ := le_trans (le_abs_self t) (abs_le_norm_of_mem_spectrum ht)
  have h1 : L - L' ≤ |L' - L| := by rw [abs_sub_comm]; exact le_abs_self _
  have ha : (L - ‖T‖ / 2) / 2 ≤ L - t / 2 := by linarith
  have hb : (L - ‖T‖ / 2) / 2 ≤ L' - t / 2 := by linarith
  have hsa : Real.sqrt ((L - ‖T‖ / 2) / 2) ≤ Real.sqrt (L - t / 2) := Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt ((L - ‖T‖ / 2) / 2) ≤ Real.sqrt (L' - t / 2) := Real.sqrt_le_sqrt hb
  have hab : L - t / 2 ≠ L' - t / 2 := fun h => hne (by linarith)
  have hkey := abs_flowSlope_le hs hsa hsb hab
  rw [show (L' - t / 2) - (L - t / 2) = L' - L by ring] at hkey
  rw [show flowSlopeSymbol L L' t
      = ((Real.sqrt (L' - t / 2))⁻¹ - (Real.sqrt (L - t / 2))⁻¹) / (L' - L)
        + (1 / 2) * (Real.sqrt (L - t / 2))⁻¹ ^ 3 by
    simp only [flowSlopeSymbol, flowSymbol]; ring]
  exact hkey

theorem continuousOn_flowSlopeSymbol {T : A} {L L' : ℝ} (hL : ‖T‖ / 2 < L) (hL' : ‖T‖ / 2 < L') :
    ContinuousOn (flowSlopeSymbol L L') (spectrum ℝ T) := by
  refine ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_) ?_
  · exact (continuousOn_flowSymbol hL').sub (continuousOn_flowSymbol hL)
  · exact continuousOn_const.mul ((continuousOn_flowSymbol hL).pow 3)

/-- **The prime normal flow is differentiable in `L`, with derivative `−(1/2)(L I − T/2)^{-3/2}`.**
This is the operator form of the card's `(10)`: the difference quotient of the symbol is uniformly
small on the spectrum, so the isometric functional calculus transports the scalar derivative. -/
theorem hasDerivAt_primeNormalFlow {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    HasDerivAt (primeNormalFlow T) (cfc (fun t => -(1 / 2) * flowSymbol L t ^ 3) T) L := by
  have hδ : 0 < L - ‖T‖ / 2 := by linarith
  have hs : 0 < Real.sqrt ((L - ‖T‖ / 2) / 2) := Real.sqrt_pos.mpr (by linarith)
  set D : A := cfc (fun t => -(1 / 2) * flowSymbol L t ^ 3) T with hDdef
  have hwin : ∀ᶠ L' in 𝓝[≠] L, |L' - L| < (L - ‖T‖ / 2) / 2 := by
    have hball := Metric.ball_mem_nhds L (by linarith : (0:ℝ) < (L - ‖T‖ / 2) / 2)
    have hb2 : ∀ᶠ L' in 𝓝 L, |L' - L| < (L - ‖T‖ / 2) / 2 := by
      filter_upwards [hball] with L' hL'
      rwa [Metric.mem_ball, Real.dist_eq] at hL'
    exact hb2.filter_mono nhdsWithin_le_nhds
  have hL'pos : ∀ᶠ L' in 𝓝[≠] L, ‖T‖ / 2 < L' := by
    filter_upwards [hwin] with L' h
    have hh : L - L' ≤ |L' - L| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have hident : ∀ᶠ L' in 𝓝[≠] L,
      ‖cfc (flowSlopeSymbol L L') T‖ = ‖slope (primeNormalFlow T) L L' - D‖ := by
    filter_upwards [hL'pos, self_mem_nhdsWithin] with L' hpos hne
    have hcL := continuousOn_flowSymbol (T := T) hL
    have hcL' := continuousOn_flowSymbol (T := T) hpos
    have hsub : cfc (fun t => flowSymbol L' t - flowSymbol L t) T
        = primeNormalFlow T L' - primeNormalFlow T L := cfc_sub _ _ T
    have hcd : ContinuousOn (fun t => flowSymbol L' t - flowSymbol L t) (spectrum ℝ T) :=
      hcL'.sub hcL
    have hslope : slope (primeNormalFlow T) L L'
        = cfc (fun t => (L' - L)⁻¹ * (flowSymbol L' t - flowSymbol L t)) T := by
      rw [slope_def_module, ← hsub]
      exact (cfc_const_mul _ _ T hcd).symm
    have hD : D = cfc (fun t => -((1 / 2) * flowSymbol L t ^ 3)) T := by
      rw [hDdef]; congr 1; funext t; ring
    have hsplit := cfc_sub (fun t => (L' - L)⁻¹ * (flowSymbol L' t - flowSymbol L t))
      (fun t => -((1 / 2) * flowSymbol L t ^ 3)) T
      (continuousOn_const.mul (hcL'.sub hcL)) ((continuousOn_const.mul (hcL.pow 3)).neg)
    have heqfun : (fun t => (L' - L)⁻¹ * (flowSymbol L' t - flowSymbol L t)
        - -((1 / 2) * flowSymbol L t ^ 3)) = flowSlopeSymbol L L' := by
      funext t; rw [flowSlopeSymbol]; ring
    rw [heqfun] at hsplit
    rw [hsplit, ← hslope, ← hD]
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ L' in 𝓝[≠] L,
      ∀ t ∈ spectrum ℝ T, ‖flowSlopeSymbol L L' t‖ ≤ ε := by
    intro ε hε
    have hbound : Tendsto
        (fun L' : ℝ => |L' - L| / (2 * Real.sqrt ((L - ‖T‖ / 2) / 2) ^ 5)) (𝓝[≠] L) (𝓝 0) := by
      have h1 : Tendsto (fun L' : ℝ => |L' - L|) (𝓝[≠] L) (𝓝 0) := by
        have hc : ContinuousAt (fun L' : ℝ => |L' - L|) L := by fun_prop
        have h0 : Tendsto (fun L' : ℝ => |L' - L|) (𝓝 L) (𝓝 0) := by simpa using hc.tendsto
        exact h0.mono_left nhdsWithin_le_nhds
      simpa using h1.div_const (2 * Real.sqrt ((L - ‖T‖ / 2) / 2) ^ 5)
    filter_upwards [hwin, self_mem_nhdsWithin,
      hbound.eventually (eventually_lt_nhds hε)] with L' hw hne hsm t ht
    rw [Real.norm_eq_abs]
    exact le_trans (abs_flowSlopeSymbol_le (T := T) hL hne hw ht) hsm.le
  have hcont : ∀ᶠ L' in 𝓝[≠] L, ContinuousOn (flowSlopeSymbol L L') (spectrum ℝ T) := by
    filter_upwards [hL'pos] with L' hpos
    exact continuousOn_flowSlopeSymbol hL hpos
  have hmain : Tendsto (fun L' => ‖cfc (flowSlopeSymbol L L') T‖) (𝓝[≠] L) (𝓝 0) :=
    tendsto_norm_cfc_zero (𝕜 := ℝ) (flowSlopeSymbol L) T hT hcont hsmall
  rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff,
    tendsto_zero_iff_norm_tendsto_zero]
  exact hmain.congr' hident

end Flow

end GaloisForLFunctions.HTGeometry
