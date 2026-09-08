import GaloisForLFunctions.RHTower.MontgomeryLeadingOrderLimits

/-!
# The unconditional pair-correlation asymptotic at leading order

For fixed `0 < α < 1` and `x = T^α`, Montgomery's pair form over the zeros of `ξ` with
`0 < γ ≤ T` (all zeros, with multiplicity, no hypothesis on their real parts) satisfies

`F(T^α, T) / ((T/2π) · α log T) → 1` as `T → ∞`.

The proof assembles the corpus chain: `(π/2) F = ∫_0^T |S|² + O(x L² log T)` (truncation of the
height mean square), `4x |S|² = |P + E|²` (Montgomery's lemma in prime-side form),
`∫_0^T |P|² = T Σ d_n² + O(Σ n d_n²)` (Montgomery–Vaughan), `Σ d_n² ~ x log x` (prime number
theorem), and the remainder energy `∫_0^T |E|² = O(x² + T log²T / x)`; the cross term is absorbed
by the `δ`-inequality `|P+E|² ≤ (1+δ)|P|² + (1+1/δ)|E|²` and its reverse.
-/

open Filter Topology Set

namespace RHTower

/-! ## The abstract inequalities of the assembly -/

/-- From `|IP − A| ≤ (δ/8) Q` and `|A − Q| ≤ (δ/8) Q`: `IP ∈ [Q(1 − δ/4), Q(1 + δ/4)]`. -/
theorem assembly_ip_bounds {δ Q IP A : ℝ} (h4 : |IP - A| ≤ δ / 8 * Q) (h5 : |A - Q| ≤ δ / 8 * Q) :
    Q * (1 - δ / 4) ≤ IP ∧ IP ≤ Q * (1 + δ / 4) := by
  have := abs_le.mp h4
  have := abs_le.mp h5
  constructor <;> nlinarith

/-- The assembly: `(π/2) F` lies within `3δ N` of `N`. -/
theorem assembly_bound {δ N x IS IP IE J F Q : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (hN0 : 0 < N)
    (hx0 : 0 < x) (hQN : Q = 4 * x * N)
    (h1 : |IS - Real.pi / 2 * F| ≤ δ / 8 * N) (h2 : IS = 1 / (4 * x) * J)
    (h3u : J ≤ (1 + δ) * IP + (1 + 1 / δ) * IE)
    (h3l : IP - (1 + 1 / δ) * IE ≤ (1 + δ) * J)
    (hIPu : IP ≤ Q * (1 + δ / 4)) (hIPl : Q * (1 - δ / 4) ≤ IP)
    (h6 : (1 + 1 / δ) * IE ≤ δ / 8 * Q) :
    |Real.pi / 2 * F - N| ≤ 3 * δ * N := by
  have hx4 : 0 < 4 * x := by positivity
  have hQ0 : 0 < Q := by rw [hQN]; positivity
  -- `J ≤ Q ((1+δ)(1+δ/4) + δ/8)`
  have hJu : J ≤ Q * ((1 + δ) * (1 + δ / 4) + δ / 8) := by
    have := mul_le_mul_of_nonneg_left hIPu (by positivity : (0 : ℝ) ≤ 1 + δ)
    nlinarith
  -- `(1+δ) J ≥ Q(1 − 3δ/8)`
  have hJl : Q * (1 - 3 * δ / 8) ≤ (1 + δ) * J := by nlinarith
  -- `IS ≤ N(1 + 2δ)`
  have hISu : IS ≤ N * (1 + 2 * δ) := by
    have hcoef : (1 + δ) * (1 + δ / 4) + δ / 8 ≤ 1 + 2 * δ := by nlinarith
    calc IS = 1 / (4 * x) * J := h2
      _ ≤ 1 / (4 * x) * (Q * ((1 + δ) * (1 + δ / 4) + δ / 8)) := by gcongr
      _ = N * ((1 + δ) * (1 + δ / 4) + δ / 8) := by rw [hQN]; field_simp
      _ ≤ N * (1 + 2 * δ) := by gcongr
  -- `IS ≥ N(1 − 2δ)`
  have hISl : N * (1 - 2 * δ) ≤ IS := by
    have hJ' : Q * (1 - 3 * δ / 8) / (1 + δ) ≤ J := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hcoef : 1 - 2 * δ ≤ (1 - 3 * δ / 8) / (1 + δ) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    calc N * (1 - 2 * δ) ≤ N * ((1 - 3 * δ / 8) / (1 + δ)) := by gcongr
      _ = 1 / (4 * x) * (Q * (1 - 3 * δ / 8) / (1 + δ)) := by rw [hQN]; field_simp
      _ ≤ 1 / (4 * x) * J := by gcongr
      _ = IS := h2.symm
  have := abs_le.mp h1
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The theorem -/

/-- **Montgomery's pair correlation at leading order, unconditionally.** -/
theorem tendsto_montgomeryForm_div_leadingOrder {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun T : ℝ =>
        (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          / ((T / (2 * Real.pi)) * (α * Real.log T))) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ0, hδ1, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ δ ≤ ε / 8 :=
    ⟨min (ε / 8) (1 / 8), lt_min (by positivity) (by norm_num), min_le_right _ _, min_le_left _ _⟩
  -- the eventual smallness statements
  have E1 := (tendsto_truncation_error_div hα0 hα1 xiLineTwoLogDerivConstant
    xiLineTwoLogDerivConstant_nonneg).eventually (eventually_le_nhds (show (0 : ℝ) < δ / 8 by positivity))
  have E2 := (tendsto_remainder_energy_div hα0 hα1 xbBlockConstant xbBlockConstant_nonneg).eventually
    (eventually_le_nhds (show (0 : ℝ) < δ ^ 2 / (8 * (1 + δ)) by positivity))
  have E3 := (tendsto_prime_error_div hα1).eventually (eventually_le_nhds (show (0 : ℝ) < δ / 8 by positivity))
  have E4 := Metric.tendsto_nhds.mp (tendsto_tsum_primeAmp_sq_div.comp (tendsto_rpow_atTop hα0))
    (δ / 8) (by positivity)
  have E5 := (tendsto_rpow_atTop hα0).eventually eventually_tsum_mul_primeAmp_sq_le
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (E1.and (E2.and (E3.and (E4.and (E5.and (eventually_gt_atTop (1 : ℝ)))))))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, hT1⟩ := hT₀ T hT
  simp only [Function.comp] at e4
  have hT0 : 0 < T := by linarith
  have hx1 : 1 < T ^ α := Real.one_lt_rpow hT1 hα0
  have hx0 : 0 < T ^ α := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hlogx : Real.log (T ^ α) = α * Real.log T := Real.log_rpow hT0 α
  have hlogx0 : 0 < Real.log (T ^ α) := by rw [hlogx]; positivity
  have hN0 : 0 < (T / 4) * (α * Real.log T) := by positivity
  have hQN : T * T ^ α * Real.log (T ^ α) = 4 * T ^ α * ((T / 4) * (α * Real.log T)) := by
    rw [hlogx]; ring
  have hQ0 : 0 < T * T ^ α * Real.log (T ^ α) := by positivity
  -- (1) truncation
  have h1 : |(∫ t in (0 : ℝ)..T, ‖lorentzZeroSumAll (T ^ α) t‖ ^ 2)
      - Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re|
      ≤ δ / 8 * ((T / 4) * (α * Real.log T)) := by
    have := integral_normSq_lorentzZeroSumAll_sub_montgomeryForm_le (x := T ^ α) (T := T) hx1.le hT0.le
    rw [setIntegral_Icc_normSq_lorentzZeroSumAll hT0.le] at this
    refine this.trans ?_
    rw [div_le_iff₀ hN0] at e1
    unfold truncationLog
    exact e1
  -- (2) `IS = J/(4x)`
  have h2 := integral_normSq_lorentzZeroSumAll_eq hx1 T
  -- (3) the `δ`-inequalities
  have h3u := integral_normSq_add_le_delta hx1 hT0.le hδ0
  have h3l := integral_normSq_add_ge_delta hx1 hT0.le hδ0
  -- (4) the prime-side mean square
  have h4 : |(∫ t in (0 : ℝ)..T, ‖primeSide (T ^ α) t‖ ^ 2) - T * ∑' n : ℕ, primeAmp (T ^ α) n ^ 2|
      ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by
    refine (integral_normSq_primeSide_sub_le hx1.le hT0.le).trans ?_
    calc 104 * ∑' n : ℕ, (n : ℝ) * primeAmp (T ^ α) n ^ 2
        ≤ 104 * (3 * ((T ^ α) ^ 2 * Real.log (T ^ α))) := by gcongr
      _ = 312 * (T ^ α / T) * (T * T ^ α * Real.log (T ^ α)) := by field_simp; ring
      _ ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by gcongr
  -- (5) `|T Σd − Q| ≤ (δ/8) Q`
  have h5 : |T * ∑' n : ℕ, primeAmp (T ^ α) n ^ 2 - T * T ^ α * Real.log (T ^ α)|
      ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by
    rw [Real.dist_eq] at e4
    have hxl : 0 < T ^ α * Real.log (T ^ α) := by positivity
    have heq : |T * ∑' n : ℕ, primeAmp (T ^ α) n ^ 2 - T * T ^ α * Real.log (T ^ α)|
        = T * (T ^ α * Real.log (T ^ α)) *
          |(∑' n : ℕ, primeAmp (T ^ α) n ^ 2) / (T ^ α * Real.log (T ^ α)) - 1| := by
      rw [← abs_of_pos (show 0 < T * (T ^ α * Real.log (T ^ α)) by positivity), ← abs_mul]
      congr 1
      field_simp
    rw [heq]
    calc T * (T ^ α * Real.log (T ^ α)) *
          |(∑' n : ℕ, primeAmp (T ^ α) n ^ 2) / (T ^ α * Real.log (T ^ α)) - 1|
        ≤ T * (T ^ α * Real.log (T ^ α)) * (δ / 8) := by gcongr
      _ = δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by ring
  -- (6) the remainder energy
  have h6 : (1 + 1 / δ) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder (T ^ α) t‖ ^ 2
      ≤ δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by
    have hIE := integral_normSq_montgomeryRemainder_le hx1 hT0.le (x := T ^ α) (T := T)
    rw [div_le_iff₀ (by positivity), ← hlogx] at e2
    have hIE0 : 0 ≤ ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder (T ^ α) t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT0.le fun t _ => by positivity
    calc (1 + 1 / δ) * ∫ t in (0 : ℝ)..T, ‖montgomeryRemainder (T ^ α) t‖ ^ 2
        ≤ (1 + 1 / δ) * (δ ^ 2 / (8 * (1 + δ)) * (T * T ^ α * Real.log (T ^ α))) := by
          gcongr; exact hIE.trans e2
      _ = δ / 8 * (T * T ^ α * Real.log (T ^ α)) := by field_simp; ring
  -- assemble
  obtain ⟨hIPl, hIPu⟩ := assembly_ip_bounds h4 h5
  have hmain := assembly_bound hδ0 hδ1 hN0 hx0 hQN h1 h2 h3u h3l hIPu hIPl h6
  -- conclude
  have hden : (T / (2 * Real.pi)) * (α * Real.log T) = ((T / 4) * (α * Real.log T)) * (2 / Real.pi) := by
    field_simp; ring
  rw [Real.dist_eq, hden]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hratio : (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        / (((T / 4) * (α * Real.log T)) * (2 / Real.pi)) - 1
      = (Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        - (T / 4) * (α * Real.log T)) / ((T / 4) * (α * Real.log T)) := by
    field_simp
  rw [hratio, abs_div, abs_of_pos hN0, div_lt_iff₀ hN0]
  calc |Real.pi / 2 * (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        - (T / 4) * (α * Real.log T)|
      ≤ 3 * δ * ((T / 4) * (α * Real.log T)) := hmain
    _ < ε * ((T / 4) * (α * Real.log T)) := by
        have : 3 * δ < ε := by linarith
        exact mul_lt_mul_of_pos_right this hN0

end RHTower
