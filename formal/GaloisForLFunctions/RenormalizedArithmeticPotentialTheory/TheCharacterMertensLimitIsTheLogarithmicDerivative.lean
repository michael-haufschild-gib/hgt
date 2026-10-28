import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCharacterMertensSumConverges

/-!
# The character Mertens limit is the logarithmic derivative

The character Mertens sum converges, `A_χ(y) → α_χ` (`tendsto_charMertensSum`). This file
identifies the limit: `α_χ = −L′/L(1, χ)` (`charMertensLimit_eq_neg_logDeriv`).

* **Abel's theorem for the Dirichlet series** (`tendsto_LSeries_twist_vonMangoldt`): with
  `w_n(σ) = n^{1−σ} − (n + 1)^{1−σ} ≥ 0`, summation by parts gives
  `Σ_{n ≤ N} χ(n)Λ(n) n^{−σ} = A_χ(N)(N + 1)^{1−σ} + Σ_{n ≤ N} A_χ(n) w_n(σ)` and
  `Σ_{n ≤ N} w_n(σ) = 1 − (N + 1)^{1−σ}`. The weights form a summation method that is regular at
  `σ = 1`, so `Σ_n χ(n)Λ(n) n^{−σ} → α_χ` as `σ → 1+`.
* **The logarithmic derivative** (`charMertensLimit_eq_neg_logDeriv`): for `Re s > 1` the series is
  `−L′/L(s, χ)`, which is continuous at `s = 1` because `L(·, χ)` is entire and `L(1, χ) ≠ 0`.
* **The finite part of a character gauge, explicitly**
  (`tendsto_gaugeMertensSum_charGauge_logDeriv`): for a real character `χ ≠ 1` mod a prime `ℓ`,
  the gauge `ε(n) = χ(n')` has Mertens limit `Re(−L′/L(1, χ))` plus the limit of
  `Σ_{t ≤ y, ℓ ∣ t} Λ(t)/t`, and the horizon finite part is twice this number.

The finite part of `ζ` at the horizon is `−2γ`, twice the constant term of `−ζ′/ζ` at its pole;
the finite part of a character gauge is twice the value of `−L′/L` at `1`, corrected at `ℓ`. The
renormalized horizon reads the logarithmic derivative of the `L`-function at the edge of the
critical strip.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ}

/-- The **Abel weight** `w_n(σ) = n^{1−σ} − (n + 1)^{1−σ}`. -/
def abelWeight (σ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 - σ) - ((n : ℝ) + 1) ^ (1 - σ)

theorem abelWeight_nonneg {σ : ℝ} (hσ : 1 ≤ σ) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ abelWeight σ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact sub_nonneg.mpr (Real.rpow_le_rpow_of_nonpos hn' (by linarith) (by linarith))

/-- The weights telescope: `Σ_{n ≤ N} w_n(σ) = 1 − (N + 1)^{1−σ}`. -/
theorem sum_abelWeight (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, abelWeight σ n = 1 - ((N : ℝ) + 1) ^ (1 - σ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, abelWeight]
    push_cast
    ring

/-- **Summation by parts**:
`Σ_{n ≤ N} b_n n^{1−σ} = A_χ(N)(N + 1)^{1−σ} + Σ_{n ≤ N} A_χ(n) w_n(σ)`, `b_n = χ(n)Λ(n)/n`. -/
theorem sum_charMertens_rpow_eq (χ : DirichletCharacter ℂ q) (σ : ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, χ (n : ZMod q) * ((Λ n / n : ℝ) : ℂ) * (((n : ℝ) ^ (1 - σ) : ℝ) : ℂ) =
      charMertensSum χ N * ((((N : ℝ) + 1) ^ (1 - σ) : ℝ) : ℂ) +
        ∑ n ∈ Icc 1 N, charMertensSum χ n * ((abelWeight σ n : ℝ) : ℂ) := by
  induction N with
  | zero => simp [charMertensSum]
  | succ N ih =>
    have hA : charMertensSum χ (N + 1) = charMertensSum χ N +
        χ ((N + 1 : ℕ) : ZMod q) * ((Λ (N + 1) / (N + 1 : ℕ) : ℝ) : ℂ) := by
      rw [charMertensSum, charMertensSum, sum_Icc_succ_top (by omega)]
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega), hA, abelWeight]
    push_cast
    ring

/-- The `n`-th term of the `L`-series of `χΛ` at real `σ` is `b_n n^{1−σ}`. -/
theorem term_twist_vonMangoldt_eq (χ : DirichletCharacter ℂ q) (σ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    LSeries.term ((fun n : ℕ => χ n) * fun n : ℕ => (Λ n : ℂ)) σ n =
      χ (n : ZMod q) * ((Λ n / n : ℝ) : ℂ) * (((n : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [LSeries.term_def, if_neg (by omega), Pi.mul_apply,
    ← Complex.ofReal_natCast n, ← Complex.ofReal_cpow hn'.le, Real.rpow_sub hn', Real.rpow_one]
  have hs : (n : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hn' σ).ne'
  push_cast
  field_simp
  rw [mul_div_mul_right]
  exact_mod_cast hn'.ne'

/-- **Abel's theorem for `χΛ`**: `Σ_n χ(n)Λ(n) n^{−σ} → α_χ` as `σ → 1+`. -/
theorem tendsto_LSeries_twist_vonMangoldt [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun σ : ℝ => LSeries ((fun n : ℕ => χ n) * fun n : ℕ => (Λ n : ℂ)) σ) (𝓝[>] 1)
      (𝓝 (charMertensLimit χ)) := by
  set α := charMertensLimit χ
  have hA := tendsto_charMertensSum χ hχ
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- far out, the Mertens sum is `ε/2`-close to its limit
  obtain ⟨n₀, hn₀⟩ := Metric.tendsto_atTop.mp hA (ε / 2) (by positivity)
  -- the finitely many early weights vanish at `σ = 1`
  set R : ℝ → ℝ := fun σ => ∑ n ∈ Icc 1 n₀, ‖charMertensSum χ n - α‖ * abelWeight σ n with hRdef
  have hRcont : Continuous R := by
    refine continuous_finsetSum _ fun n hn => continuous_const.mul ?_
    have hn' : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    exact (continuous_const.rpow (continuous_const.sub continuous_id) fun _ => Or.inl hn'.ne').sub
      (continuous_const.rpow (continuous_const.sub continuous_id) fun _ => Or.inl (by positivity))
  have hR1 : R 1 = 0 := by
    simp only [hRdef, abelWeight, sub_self, Real.rpow_zero, mul_zero, sum_const_zero]
  have hRlim : ∀ᶠ σ in 𝓝[>] (1 : ℝ), R σ < ε / 2 := by
    have h := hRcont.continuousAt (x := 1)
    rw [ContinuousAt, hR1] at h
    exact nhdsWithin_le_nhds (h.eventually (gt_mem_nhds (by positivity)))
  filter_upwards [hRlim, self_mem_nhdsWithin] with σ hRσ hσ
  have hσ1 : (1 : ℝ) < σ := hσ
  -- the partial sums of the `L`-series converge to it
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
    (show 1 < (σ : ℂ).re by simpa using hσ1)
  have hpart : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      χ (n : ZMod q) * ((Λ n / n : ℝ) : ℂ) * (((n : ℝ) ^ (1 - σ) : ℝ) : ℂ)) atTop
      (𝓝 (LSeries ((fun n : ℕ => χ n) * fun n : ℕ => (Λ n : ℂ)) σ)) := by
    have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun N => ?_
    simp only [Function.comp]
    rw [sum_range_succ_eq_sum_Icc (by simp [LSeries.term_def])]
    exact sum_congr rfl fun n hn => term_twist_vonMangoldt_eq χ σ (mem_Icc.mp hn).1
  -- for `N ≥ n₀`: `‖S_N(σ) − α‖ ≤ ε/2 + R(σ)`
  have hbound : ∀ᶠ N : ℕ in atTop, ‖∑ n ∈ Icc 1 N,
      χ (n : ZMod q) * ((Λ n / n : ℝ) : ℂ) * (((n : ℝ) ^ (1 - σ) : ℝ) : ℂ) - α‖ ≤
        ε / 2 + R σ := by
    filter_upwards [eventually_ge_atTop n₀] with N hN
    have hw := sum_abelWeight σ N
    have hT : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (1 - σ) := by positivity
    -- `S_N − α = (A(N) − α)(N + 1)^{1−σ} + Σ_{n ≤ N} (A(n) − α) w_n`
    have hid : ∑ n ∈ Icc 1 N,
        χ (n : ZMod q) * ((Λ n / n : ℝ) : ℂ) * (((n : ℝ) ^ (1 - σ) : ℝ) : ℂ) - α =
        (charMertensSum χ N - α) * ((((N : ℝ) + 1) ^ (1 - σ) : ℝ) : ℂ) +
          ∑ n ∈ Icc 1 N, (charMertensSum χ n - α) * ((abelWeight σ n : ℝ) : ℂ) := by
      rw [sum_charMertens_rpow_eq]
      simp only [sub_mul, sum_sub_distrib, ← mul_sum]
      rw [← Complex.ofReal_sum, hw]
      push_cast
      ring
    rw [hid]
    have hN' : ‖charMertensSum χ N - α‖ ≤ ε / 2 := by
      have := hn₀ N hN
      rw [dist_eq_norm] at this
      exact this.le
    have hterm : ∀ n ∈ Icc 1 N, ‖(charMertensSum χ n - α) * ((abelWeight σ n : ℝ) : ℂ)‖ ≤
        (if n ≤ n₀ then ‖charMertensSum χ n - α‖ * abelWeight σ n else 0) +
          ε / 2 * abelWeight σ n := by
      intro n hn
      have hw0 := abelWeight_nonneg hσ1.le (mem_Icc.mp hn).1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      split_ifs with hn₀'
      · have : 0 ≤ ε / 2 * abelWeight σ n := by positivity
        linarith
      · have h := hn₀ n (by omega)
        rw [dist_eq_norm] at h
        rw [zero_add]
        exact mul_le_mul_of_nonneg_right h.le hw0
    have hfilt : ∑ n ∈ Icc 1 N, (if n ≤ n₀ then ‖charMertensSum χ n - α‖ * abelWeight σ n else 0)
        = R σ := by
      rw [← sum_filter, hRdef]
      congr 1
      ext n
      simp only [mem_filter, mem_Icc]
      omega
    have hsumT := (norm_sum_le _ _).trans (sum_le_sum hterm)
    rw [sum_add_distrib, hfilt, ← mul_sum, hw] at hsumT
    calc ‖(charMertensSum χ N - α) * ((((N : ℝ) + 1) ^ (1 - σ) : ℝ) : ℂ) +
          ∑ n ∈ Icc 1 N, (charMertensSum χ n - α) * ((abelWeight σ n : ℝ) : ℂ)‖
        ≤ ε / 2 * ((N : ℝ) + 1) ^ (1 - σ) + (R σ + ε / 2 * (1 - ((N : ℝ) + 1) ^ (1 - σ))) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ hsumT)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
          exact mul_le_mul_of_nonneg_right hN' hT
      _ = ε / 2 + R σ := by ring
  have hlim := le_of_tendsto ((hpart.sub_const α).norm) hbound
  rw [dist_eq_norm]
  linarith

/-- **The character Mertens limit is the logarithmic derivative**: `α_χ = −L′/L(1, χ)`. -/
theorem charMertensLimit_eq_neg_logDeriv [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    charMertensLimit χ =
      -deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 := by
  set F : ℂ → ℂ := fun s =>
    -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
  -- `F` is continuous at `1`
  have hdiff := DirichletCharacter.differentiable_LFunction hχ
  have hF : ContinuousAt F 1 :=
    (((hdiff.analyticAt 1).deriv).continuousAt.neg).div (hdiff.continuous.continuousAt)
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  have hFlim : Tendsto (fun σ : ℝ => F σ) (𝓝[>] 1) (𝓝 (F 1)) := by
    have hF' : ContinuousAt F ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_one]
      exact hF
    have h : ContinuousAt (fun σ : ℝ => F σ) 1 := hF'.comp Complex.continuous_ofReal.continuousAt
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  -- on `σ > 1` the `L`-series of `χΛ` is `F`
  have heq : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      LSeries ((fun n : ℕ => χ n) * fun n : ℕ => (Λ n : ℂ)) σ = F σ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hσ']
    have hev : (fun s => LSeries (fun n : ℕ => χ n) s) =ᶠ[𝓝 (σ : ℂ)]
        DirichletCharacter.LFunction χ := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσ'] with s hs
      exact (DirichletCharacter.LFunction_eq_LSeries χ hs).symm
    simp only [F]
    rw [hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hσ']
  exact tendsto_nhds_unique (tendsto_LSeries_twist_vonMangoldt χ hχ)
    (hFlim.congr' (heq.mono fun σ h => h.symm))

/-- **The Mertens limit of a character gauge, explicitly**: for a real character `χ ≠ 1` mod a
prime `ℓ`, `A_ε(y) → Re(−L′/L(1, χ)) + lim_y Σ_{t ≤ y, ℓ ∣ t} Λ(t)/t`. -/
theorem tendsto_gaugeMertensSum_charGauge_logDeriv {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (χ : DirichletCharacter ℂ ℓ) (hχ : χ ≠ 1) (hreal : ∀ a, (χ a).im = 0) :
    Tendsto (gaugeMertensSum (charGauge χ)) atTop
      (𝓝 ((-deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re +
        ⨆ y, primePowerMertens ℓ y)) := by
  rw [← charMertensLimit_eq_neg_logDeriv χ hχ]
  exact (exists_abs_charGaugeForm_stepProfile_finitePart_le hℓ χ hχ hreal).1

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
