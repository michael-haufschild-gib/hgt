import GaloisForLFunctions.RHTower.HarmonicPrimitiveMassAdjoint
import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic

/-!
# The mean value form and the exact scale of the adjoint cell quotient

The adjoint cell quotient of a receiver `K_n = P(log n)` is a difference quotient over the window
`[log n, log(n+1)]` divided by the harmonic increment.  The mean value theorem turns it into

`A_n = -P'(ξ)·ρ_n`,  `ρ_n = (log(n+1) - log n)/w_n`,  `ξ ∈ (log n, log(n+1))`,

and `n ≤ ρ_n ≤ n+1`, so `ρ_n/n → 1`.  For the half-density gauge `P(h) = e^{-h/2}F(h)` the
derivative is `-P'(h) = e^{-h/2}(F(h)/2 - F'(h))`, so with the outgoing symbol
`S = F/2 - F'`,

`A_n = e^{-ξ/2}·S(ξ)·ρ_n = (1+o(1))·√n·S(log n)`

whenever `S` is uniformly continuous and stays away from zero along the sample: the window has
width `O(1/n)`, the exponential factor is pinned between `√(n/(n+1))` and `1`, and the harmonic
ratio is pinned between `1` and `(n+1)/n`.

Against this, a power source `R(n) = n^β` with `β < 1` has harmonic primitive tail
`∑_{n > N} n^β w_n = (1+o(1))·N^{β-1}/(1-β)`, so the product of the two carries the exponent
`β - 1/2`: the primitive lowers the source exponent by one and the adjoint quotient raises it by
one half.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## The harmonic ratio of the logarithmic window -/

/-- The ratio of the logarithmic window to the harmonic increment. -/
def logGapRatio (n : ℕ) : ℝ :=
  (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) / harmonicGap n

theorem harmonicGap_eq_inv_mul {n : ℕ} (hn : 1 ≤ n) :
    harmonicGap n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [harmonicGap]
  field_simp
  ring

/-- The logarithmic window is pinned between the two harmonic endpoints. -/
theorem log_succ_sub_log_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)
      ∧ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hsplit : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)
      = Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
    rw [Real.log_div (ne_of_gt hn1) (ne_of_gt hn0)]
  have hsplit' : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)
      = -Real.log ((n : ℝ) / ((n : ℝ) + 1)) := by
    rw [Real.log_div (ne_of_gt hn0) (ne_of_gt hn1)]
    ring
  constructor
  · rw [hsplit']
    have h := Real.log_le_sub_one_of_pos (x := (n : ℝ) / ((n : ℝ) + 1)) (by positivity)
    have hval : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [hval] at h
    linarith
  · rw [hsplit]
    have h := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / (n : ℝ)) (by positivity)
    have hval : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp
      ring
    rw [hval] at h
    exact h

/-- The harmonic ratio of the window is pinned between `n` and `n+1`. -/
theorem logGapRatio_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ logGapRatio n ∧ logGapRatio n ≤ (n : ℝ) + 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  obtain ⟨hlow, hhigh⟩ := log_succ_sub_log_bounds hn
  have hgap : harmonicGap n = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := harmonicGap_eq_inv_mul hn
  have hgap0 : (0 : ℝ) < harmonicGap n := by
    rw [hgap]
    positivity
  rw [logGapRatio, hgap]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have : (n : ℝ) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 / ((n : ℝ) + 1) := by
      field_simp
    rw [this]
    exact hlow
  · rw [div_le_iff₀ (by positivity)]
    have : ((n : ℝ) + 1) * (1 / ((n : ℝ) * ((n : ℝ) + 1))) = 1 / (n : ℝ) := by
      field_simp
    rw [this]
    exact hhigh

/-- **The harmonic ratio is asymptotically the index.** -/
theorem tendsto_logGapRatio_div : Tendsto (fun n : ℕ => logGapRatio n / (n : ℝ)) atTop (𝓝 1) := by
  have hup : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [le_div_iff₀ hn0, one_mul]
    exact (logGapRatio_bounds hn).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right (logGapRatio_bounds hn).2 hn0.le

/-! ## The mean value form -/

/-- **(24.66) The exact mean value form of the adjoint cell quotient.** -/
theorem adjointCellQuotient_logProfile_mvt {P P' : ℝ → ℝ}
    (hP : ∀ x, HasDerivAt P (P' x) x) {n : ℕ} (hn : 1 ≤ n) :
    ∃ ξ ∈ Set.Ioo (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)),
      adjointCellQuotient (fun m => P (Real.log (m : ℝ))) n = -P' ξ * logGapRatio n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlt : Real.log (n : ℝ) < Real.log ((n : ℝ) + 1) :=
    Real.log_lt_log hn0 (by linarith)
  have hcont : ContinuousOn P (Set.Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :=
    fun x _ => (hP x).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope P P' hlt hcont
    (fun x _ => hP x)
  refine ⟨ξ, hξ, ?_⟩
  have hgap0 : harmonicGap n ≠ 0 := harmonicGap_ne_zero hn
  have hwin : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≠ 0 :=
    sub_ne_zero.2 (ne_of_gt hlt)
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [adjointCellQuotient, logGapRatio, hcast]
  rw [eq_div_iff hwin] at hslope
  field_simp
  linarith [hslope]

/-- The half-density gauge of a profile. -/
theorem hasDerivAt_halfDensityGauge {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x) (h : ℝ) :
    HasDerivAt (fun x => Real.exp (-x / 2) * F x)
      (-(Real.exp (-h / 2) * (F h / 2 - F' h))) h := by
  have hlin : HasDerivAt (fun x : ℝ => -x / 2) (-(1 : ℝ) / 2) h := by
    simpa using ((hasDerivAt_id h).neg.div_const 2)
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
      (Real.exp (-h / 2) * (-(1 : ℝ) / 2)) h := hlin.exp
  have heq : -(Real.exp (-h / 2) * (F h / 2 - F' h))
      = Real.exp (-h / 2) * (-(1 : ℝ) / 2) * F h + Real.exp (-h / 2) * F' h := by ring
  rw [heq]
  exact hexp.mul (hF h)

/-- The exponential window factor is pinned between `√(n/(n+1))` and `1`. -/
theorem exp_neg_half_log (x : ℝ) (hx : 0 < x) :
    Real.exp (-Real.log x / 2) = 1 / Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem exp_window_bounds {n : ℕ} (hn : 1 ≤ n) {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :
    Real.sqrt ((n : ℝ) / ((n : ℝ) + 1)) ≤ Real.exp (-ξ / 2) * Real.sqrt (n : ℝ)
      ∧ Real.exp (-ξ / 2) * Real.sqrt (n : ℝ) ≤ 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hs1 : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 hn1
  constructor
  · have hle : Real.exp (-Real.log ((n : ℝ) + 1) / 2) ≤ Real.exp (-ξ / 2) := by
      refine Real.exp_le_exp.2 ?_
      linarith [hξ.2]
    have hlow : Real.exp (-Real.log ((n : ℝ) + 1) / 2) * Real.sqrt (n : ℝ)
        ≤ Real.exp (-ξ / 2) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right hle hs0.le
    refine le_trans (le_of_eq ?_) hlow
    rw [exp_neg_half_log _ hn1, Real.sqrt_div hn0.le]
    ring
  · have hle : Real.exp (-ξ / 2) ≤ Real.exp (-Real.log (n : ℝ) / 2) := by
      refine Real.exp_le_exp.2 ?_
      linarith [hξ.1]
    have hup : Real.exp (-ξ / 2) * Real.sqrt (n : ℝ)
        ≤ Real.exp (-Real.log (n : ℝ) / 2) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_right hle hs0.le
    refine hup.trans (le_of_eq ?_)
    rw [exp_neg_half_log _ hn0]
    field_simp

/-! ## The asymptotic form on a fixed profile -/

/-- **(24.66) The adjoint cell quotient of a half-density gauge is `(1+o(1))·√n·S(log n)`,**
where `S = F/2 - F'` is the outgoing symbol. -/
theorem tendsto_adjointCellQuotient_div_sqrt {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    (hunif : UniformContinuous fun h => F h / 2 - F' h)
    {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ᶠ n : ℕ in atTop, c ≤ |F (Real.log (n : ℝ)) / 2 - F' (Real.log (n : ℝ))|) :
    Tendsto (fun n : ℕ =>
        adjointCellQuotient
            (fun m => Real.exp (-Real.log (m : ℝ) / 2) * F (Real.log (m : ℝ))) n
          / (Real.sqrt (n : ℝ) * (F (Real.log (n : ℝ)) / 2 - F' (Real.log (n : ℝ)))))
      atTop (𝓝 1) := by
  set S : ℝ → ℝ := fun h => F h / 2 - F' h with hSdef
  have hex : ∀ n : ℕ, ∃ ξ : ℝ, 1 ≤ n →
      ξ ∈ Set.Ioo (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)) ∧
      adjointCellQuotient
          (fun m => Real.exp (-Real.log (m : ℝ) / 2) * F (Real.log (m : ℝ))) n
        = Real.exp (-ξ / 2) * S ξ * logGapRatio n := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨ζ, hζ, hval⟩ := adjointCellQuotient_logProfile_mvt
        (P := fun x => Real.exp (-x / 2) * F x)
        (P' := fun x => -(Real.exp (-x / 2) * S x))
        (fun x => hasDerivAt_halfDensityGauge hF x) hn
      refine ⟨ζ, fun _ => ⟨hζ, ?_⟩⟩
      rw [hval]
      ring
    · exact ⟨0, fun h => absurd h hn⟩
  choose ξ hξ using hex
  have hwidth : Tendsto (fun n : ℕ => ξ n - Real.log (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ tendsto_one_div_atTop_nhds_zero_nat
    · filter_upwards [eventually_ge_atTop 1] with n hn
      linarith [(hξ n hn).1.1]
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hb := (log_succ_sub_log_bounds hn).2
      linarith [(hξ n hn).1.2]
  have hSdiff : Tendsto (fun n : ℕ => S (ξ n) - S (Real.log (n : ℝ))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop] at hwidth ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := (Metric.uniformContinuous_iff.1 hunif) ε hε
    obtain ⟨N, hN⟩ := hwidth δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have hd : dist (ξ n) (Real.log (n : ℝ)) < δ := by
      have := hN n hn
      simpa [Real.dist_eq, sub_zero] using this
    have := hδ' hd
    simpa [Real.dist_eq, sub_zero] using this
  have hf1 : Tendsto (fun n : ℕ => Real.exp (-ξ n / 2) * Real.sqrt (n : ℝ)) atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 1) := by
      have hbase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
        have h : Tendsto (fun n : ℕ => 1 / (1 + 1 / (n : ℝ))) atTop (𝓝 (1 / (1 + 0))) :=
          tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat)
            (by norm_num)
        rw [add_zero, div_one] at h
        refine h.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        field_simp
      have := (Real.continuous_sqrt.tendsto 1).comp hbase
      simpa [Function.comp_def] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (exp_window_bounds hn (Set.mem_Icc.2 ⟨(hξ n hn).1.1.le, (hξ n hn).1.2.le⟩)).1
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (exp_window_bounds hn (Set.mem_Icc.2 ⟨(hξ n hn).1.1.le, (hξ n hn).1.2.le⟩)).2
  have hf3 : Tendsto (fun n : ℕ => S (ξ n) / S (Real.log (n : ℝ))) atTop (𝓝 1) := by
    have hbound : Tendsto (fun n : ℕ => |S (ξ n) / S (Real.log (n : ℝ)) - 1|) atTop (𝓝 0) := by
      have hmaj : Tendsto (fun n : ℕ => (1 / c) * |S (ξ n) - S (Real.log (n : ℝ))|) atTop
          (𝓝 0) := by
        have := hSdiff.abs.const_mul (1 / c)
        simpa using this
      refine squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) ?_ hmaj
      filter_upwards [hfloor] with n hfl
      have hSabs : c ≤ |S (Real.log (n : ℝ))| := hfl
      have hSne : S (Real.log (n : ℝ)) ≠ 0 := by
        intro h
        rw [h, abs_zero] at hSabs
        linarith
      rw [div_sub_one hSne, abs_div]
      rw [div_le_iff₀ (abs_pos.2 hSne)]
      have h1 : (1 / c) * |S (ξ n) - S (Real.log (n : ℝ))| * c
          ≤ (1 / c) * |S (ξ n) - S (Real.log (n : ℝ))| * |S (Real.log (n : ℝ))| :=
        mul_le_mul_of_nonneg_left hSabs (by positivity)
      refine le_trans (le_of_eq ?_) h1
      field_simp
    rw [← tendsto_sub_nhds_zero_iff]
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    simpa [Real.norm_eq_abs] using hbound
  have hprod := (hf1.mul tendsto_logGapRatio_div).mul hf3
  rw [one_mul, one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hfloor] with n hn hfl
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  have hSabs2 : c ≤ |S (Real.log (n : ℝ))| := hfl
  have hSne : S (Real.log (n : ℝ)) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hSabs2
    linarith
  have hsplit : logGapRatio n / (n : ℝ)
      = logGapRatio n / (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by rw [hsq]
  have halg : ∀ e s ρ r sh : ℝ, r ≠ 0 → sh ≠ 0 →
      e * r * (ρ / (r * r)) * (s / sh) = e * s * ρ / (r * sh) := by
    intro e s ρ r sh hr hsh
    field_simp
  rw [(hξ n hn).2, hsplit]
  exact halg _ _ _ _ _ (ne_of_gt hs0) hSne

/-! ## The primitive tail of a power source -/

/-- The harmonic-primitive tail of the power source `n^β`. -/
def rpowHarmonicTail (β : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ β
    * (1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1))

theorem rpowHarmonicTail_term_eq {β x : ℝ} (hx : 0 < x) :
    x ^ β * (1 / x - 1 / (x + 1)) = x ^ (β - 2) * (x / (x + 1)) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hpow : x ^ β = x ^ (β - 2) * x ^ (2 : ℝ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [hpow]
  have hx2 : x ^ (2 : ℝ) = x * x := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hx2]
  field_simp
  ring

theorem rpowHarmonicTail_term_bounds {β : ℝ} {N k : ℕ} (_hN : 1 ≤ N) :
    ((N : ℝ) + 1) / ((N : ℝ) + 2) * ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2)
        ≤ ((N : ℝ) + 1 + (k : ℝ)) ^ β
          * (1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1))
      ∧ ((N : ℝ) + 1 + (k : ℝ)) ^ β
          * (1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1))
        ≤ ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hx : (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by linarith
  have hpow : (0 : ℝ) < ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2) := Real.rpow_pos_of_pos hx _
  rw [rpowHarmonicTail_term_eq hx]
  have hratio1 : ((N : ℝ) + 1 + (k : ℝ)) / ((N : ℝ) + 1 + (k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hratio2 : ((N : ℝ) + 1) / ((N : ℝ) + 2)
      ≤ ((N : ℝ) + 1 + (k : ℝ)) / ((N : ℝ) + 1 + (k : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  constructor
  · rw [mul_comm (((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2))]
    exact mul_le_mul_of_nonneg_right hratio2 hpow.le
  · calc ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2)
          * (((N : ℝ) + 1 + (k : ℝ)) / ((N : ℝ) + 1 + (k : ℝ) + 1))
        ≤ ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2) * 1 :=
          mul_le_mul_of_nonneg_left hratio1 hpow.le
      _ = ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2) := by ring

theorem summable_rpowHarmonicTail {β : ℝ} (hβ : β < 1) (N : ℕ) (hN : 1 ≤ N) :
    Summable fun k : ℕ => ((N : ℝ) + 1 + (k : ℝ)) ^ β
      * (1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1)) := by
  have hq : β - 1 < 0 := by linarith
  have hmaj := GaloisForLFunctions.HTGeometry.summable_shift_rpow hq N
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (hmaj.congr fun k => by rw [show β - 1 - 1 = β - 2 by ring])
  · have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hx : (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by linarith
    rw [rpowHarmonicTail_term_eq hx]
    have hpow : (0 : ℝ) < ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2) := Real.rpow_pos_of_pos hx _
    positivity
  · exact (rpowHarmonicTail_term_bounds (β := β) (N := N) (k := k) hN).2

/-- **(24.67) The primitive tail of a power source.**  For `β < 1`,
`∑_{n > N} n^β w_n = (1 + o(1))·N^{β-1}/(1-β)`. -/
theorem tendsto_rpowHarmonicTail {β : ℝ} (hβ : β < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - β) * rpowHarmonicTail β N) atTop
      (𝓝 (1 / (1 - β))) := by
  have hq : β - 1 < 0 := by linarith
  have hmain := GaloisForLFunctions.HTGeometry.tendsto_tsum_shift_rpow hq
  have hneg : -(β - 1) = 1 - β := by ring
  have hqm : β - 1 - 1 = β - 2 := by ring
  rw [hneg] at hmain
  simp only [hqm] at hmain
  have hupper : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - β)
      * ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2)) atTop (𝓝 (1 / (1 - β))) := by
    simpa [hneg] using hmain
  have hshrink : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / ((N : ℝ) + 2)) atTop (𝓝 1) := by
    have h : Tendsto (fun N : ℕ => (1 + 1 / (N : ℝ)) / (1 + 2 / (N : ℝ))) atTop
        (𝓝 ((1 + 0) / (1 + 0))) := by
      refine Tendsto.div (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat) ?_ (by norm_num)
      have h2 : Tendsto (fun N : ℕ => 2 * (1 / (N : ℝ))) atTop (𝓝 (2 * 0)) :=
        tendsto_one_div_atTop_nhds_zero_nat.const_mul 2
      rw [mul_zero] at h2
      refine tendsto_const_nhds.add (h2.congr fun N => ?_)
      ring
    rw [add_zero, div_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    field_simp
  have hlower : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / ((N : ℝ) + 2)
      * ((N : ℝ) ^ (1 - β) * ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2))) atTop
      (𝓝 (1 / (1 - β))) := by
    have := hshrink.mul hupper
    rwa [one_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hsum := summable_rpowHarmonicTail hβ N hN
    have hmaj := (GaloisForLFunctions.HTGeometry.summable_shift_rpow hq N).congr
      (fun k => by rw [hqm])
    have hle : ∑' k : ℕ, ((N : ℝ) + 1) / ((N : ℝ) + 2) * ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2)
        ≤ rpowHarmonicTail β N := by
      refine Summable.tsum_le_tsum (fun k => (rpowHarmonicTail_term_bounds hN).1)
        (hmaj.mul_left _) hsum
    have hpull : ∑' k : ℕ, ((N : ℝ) + 1) / ((N : ℝ) + 2) * ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2)
        = ((N : ℝ) + 1) / ((N : ℝ) + 2)
          * ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2) := tsum_mul_left
    rw [hpull] at hle
    calc ((N : ℝ) + 1) / ((N : ℝ) + 2)
          * ((N : ℝ) ^ (1 - β) * ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2))
        = (N : ℝ) ^ (1 - β) * (((N : ℝ) + 1) / ((N : ℝ) + 2)
            * ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2)) := by ring
      _ ≤ (N : ℝ) ^ (1 - β) * rpowHarmonicTail β N :=
          mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hN0.le _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hsum := summable_rpowHarmonicTail hβ N hN
    have hmaj := (GaloisForLFunctions.HTGeometry.summable_shift_rpow hq N).congr
      (fun k => by rw [hqm])
    have hle : rpowHarmonicTail β N
        ≤ ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (β - 2) :=
      Summable.tsum_le_tsum (fun k => (rpowHarmonicTail_term_bounds hN).2) hsum hmaj
    exact mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hN0.le _)

/-- **(24.67) The primitive tail against the adjoint quotient carries the exponent `β - 1/2`.**
The harmonic primitive lowers the source exponent by one and the adjoint cell quotient raises it
by one half, so their product reproduces the displacement exponent exactly. -/
theorem tendsto_rpowHarmonicTail_mul_adjointCellQuotient {β : ℝ} (hβ : β < 1)
    {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hunif : UniformContinuous fun h => F h / 2 - F' h)
    {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ᶠ n : ℕ in atTop, c ≤ |F (Real.log (n : ℝ)) / 2 - F' (Real.log (n : ℝ))|) :
    Tendsto (fun N : ℕ =>
        (N : ℝ) ^ (1 / 2 - β) / (F (Real.log (N : ℝ)) / 2 - F' (Real.log (N : ℝ)))
          * (rpowHarmonicTail β N
              * adjointCellQuotient
                  (fun m => Real.exp (-Real.log (m : ℝ) / 2) * F (Real.log (m : ℝ))) N))
      atTop (𝓝 (1 / (1 - β))) := by
  have hprod := (tendsto_rpowHarmonicTail hβ).mul
    (tendsto_adjointCellQuotient_div_sqrt hF hunif hc hfloor)
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1, hfloor] with N hN hfl
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs0 : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN0
  have hSne : F (Real.log (N : ℝ)) / 2 - F' (Real.log (N : ℝ)) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hfl
    linarith
  have hkey : (N : ℝ) ^ (1 - β) / Real.sqrt (N : ℝ) = (N : ℝ) ^ (1 / 2 - β) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hN0]
    congr 1
    ring
  have halg : ∀ a t A r sh : ℝ, r ≠ 0 → sh ≠ 0 →
      a * t * (A / (r * sh)) = a / r / sh * (t * A) := by
    intro a t A r sh hr hsh
    field_simp
  rw [halg _ _ _ _ _ (ne_of_gt hs0) hSne, hkey]


end

end RHTower
