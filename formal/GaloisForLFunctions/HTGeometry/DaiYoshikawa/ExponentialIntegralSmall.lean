import GaloisForLFunctions.RHTower.EulerMascheroniExponentialIntegral

/-!
# `E₁(λ) + log λ → −γ`: the constant in Theorem 3.9

Theorem 3.9 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), converts the large-time part of the analytic torsion into the
product of the small eigenvalues.  The conversion rests on the identity

```text
∫_λ^∞ e^{−t} dt/t  =  −log λ + ∫_1^∞ e^{−t} dt/t + ∫_0^1 (e^{−t} − 1) dt/t + o(1)   (λ → 0⁺),
```

whose constant is exactly the constant `c/(N−1)` of that theorem.  The two Frullani integrals are
`frullaniTail − frullaniHead = −γ`, so the constant is `−γ` and Dai–Yoshikawa's `c` equals
`−(N−1)γ`.

The identity is proved here in sharp form: for `0 < λ ≤ 1`,

```text
E₁(λ) + log λ = Ein(λ) − γ,        0 ≤ Ein(λ) ≤ λ,
```

so the error term is not merely `o(1)` but `O(λ)`.
-/

open Real MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The exponential integral `E₁(a) = ∫_a^∞ e^{−t} dt/t`. -/
noncomputable def expIntegralE1 (a : ℝ) : ℝ := ∫ t in Ioi a, Real.exp (-t) / t

/-- Splitting `E₁` at `1`: for `0 < a ≤ 1`, `E₁(a) = ∫_a^1 e^{−t}dt/t + ∫_1^∞ e^{−t}dt/t`. -/
theorem expIntegralE1_eq_add {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    expIntegralE1 a = (∫ t in a..1, Real.exp (-t) / t) + RHTower.frullaniTail := by
  have hsplit : Ioc a 1 ∪ Ioi (1 : ℝ) = Ioi a := Ioc_union_Ioi_eq_Ioi ha1
  have hdisj : Disjoint (Ioc a (1 : ℝ)) (Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_lt.mpr hx.2)
  have hIoc : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioc a 1) volume := by
    have h := RHTower.intervalIntegrable_exp_neg_div ha ha1
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ha1] at h
  have hunion := MeasureTheory.setIntegral_union (μ := volume)
    (f := fun t : ℝ => Real.exp (-t) / t) hdisj measurableSet_Ioi hIoc
    RHTower.integrableOn_exp_neg_div_Ioi_one
  rw [hsplit] at hunion
  have hval : (∫ t in Ioc a (1 : ℝ), Real.exp (-t) / t) = ∫ t in a..1, Real.exp (-t) / t :=
    (intervalIntegral.integral_of_le ha1).symm
  rw [hval] at hunion
  rw [expIntegralE1, RHTower.frullaniTail]
  exact hunion

/-- The head of the exponential integral, regularized: for `0 < a ≤ 1`,
`∫_a^1 e^{−t}dt/t = log(1/a) − (∫_0^1 (1−e^{−t})dt/t − Ein(a))`. -/
theorem integral_exp_neg_div_eq {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ t in a..1, Real.exp (-t) / t)
      = Real.log (1 / a) - (RHTower.frullaniHead - RHTower.ein a) := by
  have hcongr : (∫ t in a..1, Real.exp (-t) / t)
      = ∫ t in a..1, (1 / t - RHTower.einProfile t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le ha1] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
    rw [RHTower.einProfile, if_neg (ne_of_gt ht0)]
    field_simp
    ring
  have htail : (∫ t in a..1, RHTower.einProfile t) = RHTower.frullaniHead - RHTower.ein a := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (a := (0 : ℝ)) (b := a) (c := (1 : ℝ)) (f := RHTower.einProfile)
      (RHTower.intervalIntegrable_einProfile ha.le)
      (RHTower.intervalIntegrable_einProfile_pos ha ha1)
    rw [← RHTower.ein, ← RHTower.frullaniHead] at hadd
    linarith
  rw [hcongr, intervalIntegral.integral_sub
    (RHTower.intervalIntegrable_one_div_pos ha ha1)
    (RHTower.intervalIntegrable_einProfile_pos ha ha1),
    integral_one_div_of_pos ha zero_lt_one, htail]

/-- **The sharp small-parameter expansion of `E₁`.**  For `0 < λ ≤ 1`,
`E₁(λ) + log λ = Ein(λ) − γ`. -/
theorem expIntegralE1_add_log_eq {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    expIntegralE1 a + Real.log a = RHTower.ein a - Real.eulerMascheroniConstant := by
  rw [expIntegralE1_eq_add ha ha1, integral_exp_neg_div_eq ha ha1,
    ← RHTower.frullani_eq_eulerMascheroni]
  rw [one_div, Real.log_inv]
  ring

/-! ## The error term -/

theorem ein_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ RHTower.ein a :=
  intervalIntegral.integral_nonneg ha fun _ hx => RHTower.einProfile_nonneg hx.1

theorem ein_le_self {a : ℝ} (ha : 0 ≤ a) : RHTower.ein a ≤ a := by
  have hmono := intervalIntegral.integral_mono_on (f := RHTower.einProfile)
    (g := fun _ : ℝ => (1 : ℝ)) ha (RHTower.intervalIntegrable_einProfile ha)
    intervalIntegrable_const (fun _ hx => RHTower.einProfile_le_one hx.1)
  rw [RHTower.ein]
  simpa using hmono

theorem tendsto_ein_nhdsWithin_zero : Tendsto RHTower.ein (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun a : ℝ => a) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : (0 : ℝ) ≤ a := le_of_lt ha
    rw [Real.norm_eq_abs, abs_of_nonneg (ein_nonneg ha')]
    exact ein_le_self ha'
  · exact tendsto_id.mono_left nhdsWithin_le_nhds

/-- **The constant of Theorem 3.9.**  `E₁(λ) + log λ → −γ` as `λ → 0⁺`. -/
theorem tendsto_expIntegralE1_add_log :
    Tendsto (fun a : ℝ => expIntegralE1 a + Real.log a) (𝓝[>] (0 : ℝ))
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hlim := tendsto_ein_nhdsWithin_zero.sub
    (tendsto_const_nhds (x := Real.eulerMascheroniConstant) (f := 𝓝[>] (0 : ℝ)))
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  have hlt : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), a < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hlt] with a ha ha1
  exact (expIntegralE1_add_log_eq ha ha1.le).symm


/-! ## The sum over the small eigenvalues -/

/-- **The identity of Theorem 3.9.**

For finitely many parameters in `(0,1]`,
`Σᵢ E₁(λᵢ) = −log ∏ᵢ λᵢ + Σᵢ Ein(λᵢ) − m γ`, and the error `Σᵢ Ein(λᵢ)` is squeezed between `0`
and `Σᵢ λᵢ`.  This is the step converting the large-time part of the analytic torsion into the
logarithm of the product of the small eigenvalues. -/
theorem sum_expIntegralE1_eq {m : ℕ} (lam : Fin m → ℝ)
    (hpos : ∀ i, 0 < lam i) (hle : ∀ i, lam i ≤ 1) :
    ∑ i, expIntegralE1 (lam i)
      = -Real.log (∏ i, lam i) + (∑ i, RHTower.ein (lam i))
        - (m : ℝ) * Real.eulerMascheroniConstant := by
  have hterm : ∀ i : Fin m,
      expIntegralE1 (lam i) + Real.log (lam i)
        = RHTower.ein (lam i) - Real.eulerMascheroniConstant :=
    fun i => expIntegralE1_add_log_eq (hpos i) (hle i)
  have hsum : (∑ i, expIntegralE1 (lam i)) + ∑ i, Real.log (lam i)
      = (∑ i, RHTower.ein (lam i)) - (m : ℝ) * Real.eulerMascheroniConstant := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hlog : Real.log (∏ i, lam i) = ∑ i, Real.log (lam i) :=
    Real.log_prod fun i _ => (hpos i).ne'
  rw [hlog]
  linarith [hsum]

/-- The error term of Theorem 3.9 is nonnegative and at most the sum of the parameters. -/
theorem sum_ein_bounds {m : ℕ} (lam : Fin m → ℝ) (hpos : ∀ i, 0 < lam i) :
    0 ≤ (∑ i, RHTower.ein (lam i)) ∧ (∑ i, RHTower.ein (lam i)) ≤ ∑ i, lam i := by
  constructor
  · exact Finset.sum_nonneg fun i _ => ein_nonneg (hpos i).le
  · exact Finset.sum_le_sum fun i _ => ein_le_self (hpos i).le

/-- **Dai–Yoshikawa's constant `c`.**  In Theorem 3.9 the constant is
`c = (N−1)(∫_1^∞ e^{−t}dt/t + ∫_0^1 (e^{−t}−1)dt/t)`; it equals `−(N−1)γ`. -/
theorem daiYoshikawa_constant (N : ℕ) :
    ((N : ℝ) - 1) * (RHTower.frullaniTail - RHTower.frullaniHead)
      = -(((N : ℝ) - 1) * Real.eulerMascheroniConstant) := by
  rw [← RHTower.frullani_eq_eulerMascheroni]
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
