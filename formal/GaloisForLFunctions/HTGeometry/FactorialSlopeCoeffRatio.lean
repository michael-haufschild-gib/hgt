import GaloisForLFunctions.HTGeometry.GammaRayRealEnvelope

/-!
# The fixed-shift ratio of a factorial-slope coefficient sequence

A sequence with a complex factorial slope,

`aₙ = C Λⁿ Γ(1 + αn)(1 + O(e^{-cn}))`,   `Re α > 0`,

has, for every fixed forward shift `h`, the ratio

`a_{N+h} / (a_N · (Λ α^α)^h · N^{αh}) ⟶ 1`.

Three factors each tend to `1`: the normalisation `aₙ / (C Λⁿ Γ(1+αn))`, whose defect is
exponentially small; the Gamma ray shift ratio, which is the corpus's oblique asymptotic; and the
comparison of the ray base point `1 + αN` with the pure ray point `αN`, which is the exponential of
`α h log(1 + 1/(αN))`.

This is the card's `(3)`: the fixed-shift factorial chirp.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The card's coefficient hypothesis: a complex factorial slope with exponentially small
relative error. -/
structure FactorialSlope (a : ℕ → ℂ) (α Λ Cc : ℂ) (c : ℝ) : Prop where
  re_pos : 0 < α.re
  Cc_ne : Cc ≠ 0
  lam_ne : Λ ≠ 0
  c_pos : 0 < c
  approx : ∀ n : ℕ, ‖a n - Cc * Λ ^ n * Complex.Gamma (rayPoint α n)‖
      ≤ Real.exp (-c * n) * ‖Cc * Λ ^ n * Complex.Gamma (rayPoint α n)‖

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- The factorial model of the coefficient sequence. -/
def slopeModel (α Λ Cc : ℂ) (n : ℕ) : ℂ := Cc * Λ ^ n * Complex.Gamma (rayPoint α n)

theorem slopeModel_ne_zero (hyp : FactorialSlope a α Λ Cc c) (n : ℕ) :
    slopeModel α Λ Cc n ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero hyp.Cc_ne (pow_ne_zero _ hyp.lam_ne)) ?_
  exact gamma_ne_zero_of_re_pos (rayPoint_re_pos hyp.re_pos n)

/-- The normalised coefficient. -/
def slopeNorm (a : ℕ → ℂ) (α Λ Cc : ℂ) (n : ℕ) : ℂ := a n / slopeModel α Λ Cc n

theorem norm_slopeNorm_sub_one_le (hyp : FactorialSlope a α Λ Cc c) (n : ℕ) :
    ‖slopeNorm a α Λ Cc n - 1‖ ≤ Real.exp (-c * n) := by
  have hne := slopeModel_ne_zero hyp n
  have hpos : (0 : ℝ) < ‖slopeModel α Λ Cc n‖ := norm_pos_iff.mpr hne
  have hval : slopeNorm a α Λ Cc n - 1
      = (a n - slopeModel α Λ Cc n) / slopeModel α Λ Cc n := by
    rw [slopeNorm, sub_div, div_self hne]
  rw [hval, norm_div, div_le_iff₀ hpos]
  exact hyp.approx n

/-- **The normalisation tends to one.** -/
theorem tendsto_slopeNorm (hyp : FactorialSlope a α Λ Cc c) :
    Tendsto (fun n : ℕ => slopeNorm a α Λ Cc n) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (norm_slopeNorm_sub_one_le hyp) ?_
  have hc := hyp.c_pos
  have hlim : Tendsto (fun n : ℕ => Real.exp (-c * n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
    have hto : Tendsto (fun n : ℕ => -c * (n : ℝ)) atTop atBot := by
      have := Filter.tendsto_neg_atTop_atBot.comp h1
      simpa [Function.comp_def, neg_mul] using this
    exact Real.tendsto_exp_atBot.comp hto
  exact hlim

theorem slopeNorm_ne_zero_of_le (hyp : FactorialSlope a α Λ Cc c) {n : ℕ}
    (hn : Real.exp (-c * n) < 1) : slopeNorm a α Λ Cc n ≠ 0 := by
  intro hzero
  have h := norm_slopeNorm_sub_one_le hyp n
  rw [hzero, zero_sub, norm_neg, norm_one] at h
  linarith

theorem eventually_slopeNorm_ne_zero (hyp : FactorialSlope a α Λ Cc c) :
    ∀ᶠ n : ℕ in atTop, slopeNorm a α Λ Cc n ≠ 0 := by
  have hc := hyp.c_pos
  have hlim : Tendsto (fun n : ℕ => Real.exp (-c * n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => c * (n : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop
    have hto : Tendsto (fun n : ℕ => -c * (n : ℝ)) atTop atBot := by
      have := Filter.tendsto_neg_atTop_atBot.comp h1
      simpa [Function.comp_def, neg_mul] using this
    exact Real.tendsto_exp_atBot.comp hto
  filter_upwards [hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))] with n hn
  exact slopeNorm_ne_zero_of_le hyp hn

/-! ## Comparing the ray base point with the pure ray -/

/-- **The base point and the pure ray point give the same complex power, asymptotically.** -/
theorem tendsto_rayPoint_cpow_ratio {α : ℂ} (hre : 0 < α.re) (w : ℂ) :
    Tendsto (fun N : ℕ => rayPoint α N ^ w / ((α * (N : ℂ)) ^ w)) atTop (𝓝 1) := by
  have hα : α ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hαpos : (0 : ℝ) < ‖α‖ := by
    refine norm_pos_iff.mpr hα
  -- eventually the ratio is the exponential of a vanishing quantity
  have hexp : Tendsto
      (fun N : ℕ => Complex.exp (w * Complex.log (1 + (α * (N : ℂ))⁻¹))) atTop (𝓝 1) := by
    have hinv : Tendsto (fun N : ℕ => Complex.log (1 + (α * (N : ℂ))⁻¹)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' ?_ ?_ (g := fun N : ℕ => 2 / (‖α‖ * N)) ?_
      · exact Eventually.of_forall fun N => norm_nonneg _
      · filter_upwards [eventually_ge_atTop (max 1 ⌈2 / ‖α‖⌉₊)] with N hN
        have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
        have hNc : ⌈2 / ‖α‖⌉₊ ≤ N := le_trans (le_max_right _ _) hN
        have hNR : (2 : ℝ) / ‖α‖ ≤ (N : ℝ) := by
          refine le_trans (Nat.le_ceil _) ?_
          exact_mod_cast hNc
        have hbig : (2 : ℝ) ≤ ‖α‖ * N := by
          rw [div_le_iff₀ hαpos] at hNR
          linarith
        have hnormprod : ‖α * (N : ℂ)‖ = ‖α‖ * N := by
          rw [norm_mul, Complex.norm_natCast]
        have hhalf : ‖(α * (N : ℂ))⁻¹‖ ≤ 1 / 2 := by
          rw [norm_inv, hnormprod, inv_le_comm₀ (by positivity) (by norm_num)]
          linarith
        refine le_trans (norm_log_one_add_le_two_mul hhalf) ?_
        rw [norm_inv, hnormprod, div_eq_mul_inv]
      · have hto : Tendsto (fun N : ℕ => ‖α‖ * (N : ℝ)) atTop atTop :=
          Filter.Tendsto.const_mul_atTop hαpos tendsto_natCast_atTop_atTop
        have := hto.inv_tendsto_atTop.const_mul (2 : ℝ)
        simpa [div_eq_mul_inv] using this
    have hmul : Tendsto (fun N : ℕ => w * Complex.log (1 + (α * (N : ℂ))⁻¹)) atTop (𝓝 0) := by
      have := hinv.const_mul w
      simpa using this
    have := (Complex.continuous_exp.tendsto 0).comp hmul
    simpa [Function.comp_def] using this
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpos := re_mul_natCast_pos hre hN
  have hne : α * (N : ℂ) ≠ 0 := by
    intro hc
    rw [hc] at hpos
    simp at hpos
  have hz0 := rayPoint_ne_zero hre N
  have hsplit : Complex.log (rayPoint α N)
      = Complex.log (α * (N : ℂ)) + Complex.log (1 + (α * (N : ℂ))⁻¹) := by
    have hfac := rayPoint_factor hre hN
    have honere : 0 < (1 + (α * (N : ℂ))⁻¹).re := by
      have := re_inv_mul_natCast_nonneg hre N
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hone0 : (1 + (α * (N : ℂ))⁻¹) ≠ 0 := by
      intro hc
      rw [hc] at honere
      simp at honere
    have harg1 : |Complex.arg (α * (N : ℂ))| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)
    have harg2 : |Complex.arg (1 + (α * (N : ℂ))⁻¹)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl honere)
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [hfac]
    refine (Complex.log_mul_eq_add_log_iff hne hone0).mpr ?_
    constructor
    · have h1 := (abs_lt.mp harg1).1
      have h2 := (abs_lt.mp harg2).1
      linarith
    · have h1 := (abs_lt.mp harg1).2
      have h2 := (abs_lt.mp harg2).2
      linarith
  rw [Complex.cpow_def_of_ne_zero hz0, Complex.cpow_def_of_ne_zero hne, hsplit,
    ← Complex.exp_sub]
  congr 1
  ring

/-! ## The fixed-shift ratio -/

theorem rayPoint_add_nat (α : ℂ) (N h : ℕ) :
    rayPoint α (N + h) = rayPoint α N + α * (h : ℂ) := by
  rw [rayPoint, rayPoint]
  push_cast
  ring

/-- **Equation (3).**  The fixed forward-shift ratio of a factorial-slope sequence is the
corresponding complex power of the ray point. -/
theorem tendsto_coeff_shift_ratio (hyp : FactorialSlope a α Λ Cc c) (h : ℕ) :
    Tendsto (fun N : ℕ => a (N + h)
        / (a N * (Λ ^ h * (α * (N : ℂ)) ^ (α * (h : ℂ))))) atTop (𝓝 1) := by
  have hre := hyp.re_pos
  have hα : α ≠ 0 := by
    intro hc
    rw [hc] at hre
    simp at hre
  have h1 : Tendsto (fun N : ℕ => slopeNorm a α Λ Cc (N + h) / slopeNorm a α Λ Cc N)
      atTop (𝓝 1) := by
    have hA : Tendsto (fun N : ℕ => slopeNorm a α Λ Cc (N + h)) atTop (𝓝 1) :=
      (tendsto_slopeNorm hyp).comp (tendsto_add_atTop_nat h)
    have hB := tendsto_slopeNorm hyp
    have hdiv : Tendsto (fun N : ℕ => slopeNorm a α Λ Cc (N + h) / slopeNorm a α Λ Cc N)
        atTop (𝓝 (1 / 1)) := hA.div hB one_ne_zero
    rwa [div_one] at hdiv
  have h2 : Tendsto (fun N : ℕ => Complex.Gamma (rayPoint α N + α * (h : ℂ))
      / (Complex.Gamma (rayPoint α N) * rayPoint α N ^ (α * (h : ℂ)))) atTop (𝓝 1) :=
    tendsto_gamma_ray_shift_ratio hre
  have h3 := tendsto_rayPoint_cpow_ratio hre (α * (h : ℂ))
  have hprod := (h1.mul h2).mul h3
  simp only [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_slopeNorm_ne_zero hyp, eventually_ge_atTop 1] with N hgN hN1
  have hmodN := slopeModel_ne_zero hyp N
  have hmodNh := slopeModel_ne_zero hyp (N + h)
  have hΓ : Complex.Gamma (rayPoint α N) ≠ 0 :=
    gamma_ne_zero_of_re_pos (rayPoint_re_pos hre N)
  have hz0 := rayPoint_ne_zero hre N
  have hzpow : rayPoint α N ^ (α * (h : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hz0]
    exact Complex.exp_ne_zero _
  have hpos := re_mul_natCast_pos hre hN1
  have hne : α * (N : ℂ) ≠ 0 := by
    intro hc
    rw [hc] at hpos
    simp at hpos
  have hnepow : (α * (N : ℂ)) ^ (α * (h : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hne]
    exact Complex.exp_ne_zero _
  have haN : a N = slopeNorm a α Λ Cc N * slopeModel α Λ Cc N := by
    rw [slopeNorm, div_mul_cancel₀ _ hmodN]
  have haNh : a (N + h) = slopeNorm a α Λ Cc (N + h) * slopeModel α Λ Cc (N + h) := by
    rw [slopeNorm, div_mul_cancel₀ _ hmodNh]
  have hmod : slopeModel α Λ Cc (N + h)
      = Cc * (Λ ^ N * Λ ^ h) * Complex.Gamma (rayPoint α N + α * (h : ℂ)) := by
    rw [slopeModel, rayPoint_add_nat, pow_add]
  have hmodN' : slopeModel α Λ Cc N = Cc * Λ ^ N * Complex.Gamma (rayPoint α N) := rfl
  have hCc := hyp.Cc_ne
  have hlam := hyp.lam_ne
  have hlamN : Λ ^ N ≠ 0 := pow_ne_zero _ hlam
  have hlamh : Λ ^ h ≠ 0 := pow_ne_zero _ hlam
  rw [haN, haNh, hmod, hmodN']
  field_simp

/-- **Equation (3), split form.**  The ray direction can be separated from the size. -/
theorem tendsto_coeff_shift_ratio_split (hyp : FactorialSlope a α Λ Cc c) (h : ℕ) :
    Tendsto (fun N : ℕ => a (N + h)
        / (a N * (Λ ^ h * (α ^ (α * (h : ℂ)) * (N : ℂ) ^ (α * (h : ℂ))))))
      atTop (𝓝 1) := by
  refine (tendsto_coeff_shift_ratio hyp h).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN1
  rw [cpow_mul_natCast_of_re_pos hyp.re_pos (α * (h : ℂ)) hN1]

end

end GaloisForLFunctions.HTGeometry
