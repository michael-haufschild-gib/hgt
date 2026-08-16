import GaloisForLFunctions.RHTower.ProlateWKBSharpAction

/-!
# The sharp barrier ratio from above, anchored strictly inside the forbidden band

A positive solution of the angular prolate equation decays across the forbidden band at least as
fast as the WKB clock.  Transporting the Riccati subsolution from an anchor `a` to a point `b`
closer to the endpoint gives

```text
Phi a · exp(−c·A(s))  ≤  Phi b        (A(s) the full angular action).
```

Two features distinguish this from the transport anchored at the turning point itself.  The
Riccati potential `prolateWKB c (−s c²) y = sqrt((c²y² − c²s)/(1 − y²))` vanishes at `y = sqrt s`,
so the hypothesis `0 < −(s c²) + c² y²` cannot hold on a window whose left endpoint *is* the
turning point: an anchor strictly inside the band is forced.  And because the potential blows up at
`y = 1`, the initial Riccati inequality holds automatically near the endpoint, so the transported
inequality survives the limit `b → 1⁻`:

```text
Phi a  ≤  Phi 1 · exp(c·A(s))  ≤  Phi 1 · exp(c + (c s/4)·log s) .
```

That is the barrier ratio *from above*, at the sharp action and with no loss whatsoever — the
companion of the lower bound and the input the interior mass estimate needs.
-/

noncomputable section

open Real Set intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The transported action -/

/-- The Riccati potential is continuous, hence interval integrable, on any window of the band that
stays strictly inside `(-1, 1)`. -/
theorem intervalIntegrable_prolateWKB {c χ a b : ℝ} (ha : -1 < a) (hb : b < 1) (hab : a ≤ b) :
    IntervalIntegrable (prolateWKB c χ) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  have hne : ∀ y ∈ Icc a b, (1 : ℝ) - y ^ 2 ≠ 0 := by
    intro y hy
    have h1 : -1 < y := lt_of_lt_of_le ha hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 hb
    nlinarith
  have hdiv : ContinuousOn (fun y : ℝ => (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2)) (Icc a b) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) hne
  show ContinuousOn (fun y : ℝ => Real.sqrt ((χ + c ^ 2 * y ^ 2) / (1 - y ^ 2))) (Icc a b)
  exact Real.continuous_sqrt.comp_continuousOn hdiv

/-- **The transported action is at most the full angular action.**  The potential is a square root,
hence nonnegative, so discarding the stretch from the turning point to the anchor only helps. -/
theorem integral_prolateWKB_le_angleAction_anchor {c s a b : ℝ} (hc : 0 ≤ c) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hsa : Real.sqrt s ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (∫ y in a..b, prolateWKB c (-(s * c ^ 2)) y) ≤ c * prolateAngleAction s := by
  have hs : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
  have ha : (-1 : ℝ) < a := lt_of_lt_of_le (by linarith) hsa
  have ha1 : a < 1 := lt_of_le_of_lt hab hb
  have hsb : Real.sqrt s ≤ b := le_trans hsa hab
  have h1 := intervalIntegrable_prolateWKB (c := c) (χ := -(s * c ^ 2)) (a := Real.sqrt s) (b := a)
    (by linarith) ha1 hsa
  have h2 := intervalIntegrable_prolateWKB (c := c) (χ := -(s * c ^ 2)) (a := a) (b := b) ha hb hab
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hnn : 0 ≤ ∫ y in Real.sqrt s..a, prolateWKB c (-(s * c ^ 2)) y :=
    intervalIntegral.integral_nonneg hsa fun _ _ => Real.sqrt_nonneg _
  have hfull := integral_prolateWKB_le_angleAction hc hs0 hs1 hsb hb
  linarith [hadd, hnn, hfull]

/-! ## The anchored endpoint bound -/

/-- **The outer-band endpoint bound from an interior anchor.**  Across the forbidden band a positive
solution loses at most the factor `exp(−c·A(s))`, and the anchor may be any point past the turning
point at which the potential is genuinely positive. -/
theorem exp_neg_angleAction_le_endpoint_anchor {c s a b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hc : 0 ≤ c) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hsa : Real.sqrt s ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hpos : ∀ y ∈ Icc a b, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a b, 0 < -(s * c ^ 2) + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a b, c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2))
    (hinit : prolateLogDeriv Φ b ≤ prolateWKB c (-(s * c ^ 2)) b) :
    Φ a * Real.exp (-(c * prolateAngleAction s)) ≤ Φ b := by
  have hs : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
  have ha0 : (0 : ℝ) ≤ a := le_trans hs hsa
  have hmain := le_endpoint_prolateWKB hsm heig hab ha0 (by linarith) hb hpos hQ houter hinit
  have hbound := integral_prolateWKB_le_angleAction_anchor hc hs0 hs1 hsa hab hb
  have hexp : Real.exp (-(c * prolateAngleAction s))
      ≤ Real.exp (-∫ t in a..b, prolateWKB c (-(s * c ^ 2)) t) :=
    Real.exp_le_exp.mpr (by linarith)
  have hΦa : 0 < Φ a := hpos _ (left_mem_Icc.mpr hab)
  calc Φ a * Real.exp (-(c * prolateAngleAction s))
      ≤ Φ a * Real.exp (-∫ t in a..b, prolateWKB c (-(s * c ^ 2)) t) :=
        mul_le_mul_of_nonneg_left hexp hΦa.le
    _ ≤ Φ b := hmain

/-! ## Passing to the endpoint -/

/-- **The Riccati potential blows up at the band endpoint.**  The numerator tends to `c²(1 − s) > 0`
while the denominator tends to `0` from above. -/
theorem tendsto_prolateWKB_atTop {c s : ℝ} (hc : 0 < c) (hs1 : s < 1) :
    Tendsto (fun b : ℝ => prolateWKB c (-(s * c ^ 2)) b) (𝓝[<] (1 : ℝ)) atTop := by
  have hnum : Tendsto (fun b : ℝ => -(s * c ^ 2) + c ^ 2 * b ^ 2) (𝓝[<] (1 : ℝ))
      (𝓝 (c ^ 2 * (1 - s))) := by
    have hcont : Continuous (fun b : ℝ => -(s * c ^ 2) + c ^ 2 * b ^ 2) := by fun_prop
    have h : Tendsto (fun b : ℝ => -(s * c ^ 2) + c ^ 2 * b ^ 2) (𝓝[<] (1 : ℝ))
        (𝓝 (-(s * c ^ 2) + c ^ 2 * (1 : ℝ) ^ 2)) := (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    have hval : -(s * c ^ 2) + c ^ 2 * (1 : ℝ) ^ 2 = c ^ 2 * (1 - s) := by ring
    rwa [hval] at h
  have hden : Tendsto (fun b : ℝ => 1 - b ^ 2) (𝓝[<] (1 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hcont : Continuous (fun b : ℝ => 1 - b ^ 2) := by fun_prop
      have h : Tendsto (fun b : ℝ => 1 - b ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 (1 - (1 : ℝ) ^ 2)) :=
        (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
      simpa using h
    · filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds
          (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1))] with b hb1 hb0
      have hlt : b < 1 := hb1
      simp only [Set.mem_Ioi]
      nlinarith
  have hinv : Tendsto (fun b : ℝ => (1 - b ^ 2)⁻¹) (𝓝[<] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hden
  have hcs : (0 : ℝ) < c ^ 2 * (1 - s) := by
    have : (0 : ℝ) < c ^ 2 := by positivity
    nlinarith
  have hquot : Tendsto (fun b : ℝ => (-(s * c ^ 2) + c ^ 2 * b ^ 2) * (1 - b ^ 2)⁻¹)
      (𝓝[<] (1 : ℝ)) atTop := Filter.Tendsto.pos_mul_atTop hcs hnum hinv
  have hsq := Real.tendsto_sqrt_atTop.comp hquot
  refine hsq.congr fun b => ?_
  simp [prolateWKB, div_eq_mul_inv]

/-- Near the band endpoint the logarithmic derivative of a smooth solution positive at `1` is below
the Riccati potential, because the former stays bounded and the latter diverges. -/
theorem eventually_prolateLogDeriv_le_prolateWKB {c s : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hΦ1 : 0 < Φ 1) (hc : 0 < c) (hs1 : s < 1) :
    ∀ᶠ b in 𝓝[<] (1 : ℝ), prolateLogDeriv Φ b ≤ prolateWKB c (-(s * c ^ 2)) b := by
  have hd : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hdc : Continuous (deriv Φ) := (contDiff_infty_iff_deriv.mp hsm).2.continuous
  have hfun : prolateLogDeriv Φ = fun y : ℝ => -(deriv Φ y / Φ y) := rfl
  have hCA : ContinuousAt (fun y : ℝ => -(deriv Φ y / Φ y)) 1 :=
    ((hdc.continuousAt).div (hd.continuous.continuousAt) hΦ1.ne').neg
  have hlim : Tendsto (prolateLogDeriv Φ) (𝓝[<] (1 : ℝ)) (𝓝 (prolateLogDeriv Φ 1)) := by
    rw [hfun]
    exact hCA.tendsto.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ b in 𝓝[<] (1 : ℝ), prolateLogDeriv Φ b < prolateLogDeriv Φ 1 + 1 :=
    hlim.eventually_lt_const (by linarith)
  have h2 := (tendsto_prolateWKB_atTop (c := c) (s := s) hc hs1).eventually_ge_atTop
    (prolateLogDeriv Φ 1 + 1)
  filter_upwards [h1, h2] with b hb1 hb2 using le_trans hb1.le hb2

/-- **The barrier ratio from above, at the sharp action.**  A positive smooth solution of the
angular prolate equation obeys `Phi a ≤ Phi 1 · exp(c·A(s))` for every anchor `a` past the turning
point, with `A(s)` the full angular action.  No loss is incurred: the bound is the limit of the
transported Riccati inequality as the target approaches the band endpoint. -/
theorem prolate_anchor_le_exp_angleAction {c s a : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1)
    (hsa : Real.sqrt s ≤ a) (ha1 : a < 1)
    (hpos : ∀ y ∈ Icc a 1, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a 1, 0 < -(s * c ^ 2) + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a 1, c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2)) :
    Φ a * Real.exp (-(c * prolateAngleAction s)) ≤ Φ 1 := by
  have hΦcont : Continuous Φ := hsm.continuous
  have hΦ1 : 0 < Φ 1 := hpos 1 (right_mem_Icc.mpr ha1.le)
  have hev : ∀ᶠ b in 𝓝[<] (1 : ℝ), Φ a * Real.exp (-(c * prolateAngleAction s)) ≤ Φ b := by
    filter_upwards [eventually_prolateLogDeriv_le_prolateWKB (c := c) (s := s) hsm hΦ1 hc hs1,
      self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds ha1)] with b hinit hb1 hab
    have hb : b < 1 := hb1
    have hsub : Icc a b ⊆ Icc a 1 := Icc_subset_Icc le_rfl hb.le
    exact exp_neg_angleAction_le_endpoint_anchor hsm heig hc.le hs0 hs1.le hsa hab.le hb
      (fun y hy => hpos y (hsub hy)) (fun y hy => hQ y (hsub hy))
      (fun y hy => houter y (hsub hy)) hinit
  exact ge_of_tendsto ((hΦcont.tendsto 1).mono_left nhdsWithin_le_nhds) hev

/-- **The barrier ratio from above, explicitly.**  The crude clock `exp c` is improved by the factor
`s^(c s/4)`; for a fixed mode, where `c·s` is bounded, that is a negative power of the bandwidth. -/
theorem prolate_anchor_le_exp_sharp {c s a : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1)
    (hsa : Real.sqrt s ≤ a) (ha1 : a < 1)
    (hpos : ∀ y ∈ Icc a 1, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a 1, 0 < -(s * c ^ 2) + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a 1, c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2)) :
    Φ a ≤ Φ 1 * Real.exp (c + c * s / 4 * Real.log s) := by
  have hmain := prolate_anchor_le_exp_angleAction hsm heig hc hs0 hs1 hsa ha1 hpos hQ houter
  have hA := (prolateAngleAction_sub_bounds hs0 hs1.le).1
  have hΦa : 0 < Φ a := hpos a (left_mem_Icc.mpr ha1.le)
  have hle : c * prolateAngleAction s ≤ c + c * s / 4 * Real.log s := by
    have hstep : prolateAngleAction s ≤ 1 + s / 4 * Real.log s := by linarith
    nlinarith [hstep, hc.le]
  have hexp : Real.exp (-(c + c * s / 4 * Real.log s))
      ≤ Real.exp (-(c * prolateAngleAction s)) := Real.exp_le_exp.mpr (by linarith)
  have hstep : Φ a * Real.exp (-(c + c * s / 4 * Real.log s)) ≤ Φ 1 :=
    le_trans (mul_le_mul_of_nonneg_left hexp hΦa.le) hmain
  have hpos' : (0 : ℝ) < Real.exp (c + c * s / 4 * Real.log s) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv] at hstep
  exact (div_le_iff₀ hpos').mp hstep

/-- The normalised form: for a mode with `Phi 1 = 1` the interior amplitude is bounded by the sharp
barrier factor outright. -/
theorem prolate_anchor_le_exp_sharp_of_one {c s a : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1)
    (hsa : Real.sqrt s ≤ a) (ha1 : a < 1)
    (hpos : ∀ y ∈ Icc a 1, 0 < Φ y)
    (hQ : ∀ y ∈ Icc a 1, 0 < -(s * c ^ 2) + c ^ 2 * y ^ 2)
    (houter : ∀ y ∈ Icc a 1, c ^ 2 * (1 - 2 * y ^ 2) ≤ -(s * c ^ 2))
    (hΦ1 : Φ 1 = 1) :
    Φ a ≤ Real.exp (c + c * s / 4 * Real.log s) := by
  have h := prolate_anchor_le_exp_sharp hsm heig hc hs0 hs1 hsa ha1 hpos hQ houter
  rwa [hΦ1, one_mul] at h

end GaloisForLFunctions.RHTower

end
