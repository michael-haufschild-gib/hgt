import GaloisForLFunctions.HTGeometry.ProfileRatioLimits
import GaloisForLFunctions.HTGeometry.TaylorDefectUniformExponent
import GaloisForLFunctions.HTGeometry.NonlinearMailletUnconditional

/-!
# The irrational-power Barnes tail satisfies no algebraic differential equation

The formal Barnes tail `R̂_s(t) = ∑_{k ≥ 1} (−1)^k ζ(−sk) t^k` has a two-sided profile of exponent
`s`: its coefficients are bounded by `Θ(k) = C Γ(1+sk) ((2π)^{-s})^k` everywhere and bounded below by
a fixed multiple of `Θ` along an infinite set.  For irrational `s` that already rules out every
linear analytic equation, because the leading Newton vertex of the operator is unique and dominates
the whole coefficient recursion.

The nonlinear case reduces to the linear one by linearizing along a **truncation**.  Writing
`F = Y + H` with `Y` the truncation at order `N` and `H` the tail, the equation becomes

```text
L_Y H = −P(Y) − defect ,      L_Y = ∑_j (∂_j P)(Y) θ^j ,
```

where `L_Y` is convergent, `P(Y)` is convergent, and the defect is quadratic in `H`.  Three facts
make the reduction unconditional.

* The polynomial exponent in the defect estimate is fixed by the equation alone, so it can be chosen
  **before** the truncation order.
* The linearization along the truncation agrees with the linearization along the solution up to
  level `N`, so the leading vertex of the truncated operator sits below a ceiling that does not move
  with `N`.
* The defect carries the profile shifted to `Θ(N+1) Θ(n−N−1)`, which loses to the leading Newton term
  by `n^{−s(N+1−ν)}`: the truncation order is free, so it can be taken past the fixed exponent.

Taking a minimal-degree annihilator removes the nondegeneracy hypothesis, and the result is that the
Barnes tail is **hypertranscendental** for every irrational `s > 0`.
-/

open Filter Topology
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The tail of the Barnes series -/

/-- The tail of the Barnes series past a truncation is bounded by the profile. -/
theorem norm_coeff_barnesTail_sub_truncPowerSeries_le {s : ℝ} (hs : 0 < s) (N k : ℕ) :
    ‖PowerSeries.coeff k
        (barnesTailSeries s - truncPowerSeries N (barnesTailSeries s))‖
      ≤ zetaTailProfile s k := by
  rw [map_sub, coeff_truncPowerSeries]
  by_cases hk : k ≤ N
  · rw [if_pos hk, sub_self, norm_zero]
    exact (zetaTailProfile_pos hs k).le
  · rw [if_neg hk, sub_zero, norm_coeff_barnesTailSeries]
    exact abs_zetaTailModulus_le_profile hs k

theorem coeff_barnesTail_sub_truncPowerSeries_of_lt {s : ℝ} {N k : ℕ} (hk : N < k) :
    PowerSeries.coeff k (barnesTailSeries s - truncPowerSeries N (barnesTailSeries s))
      = PowerSeries.coeff k (barnesTailSeries s) := by
  rw [map_sub, coeff_truncPowerSeries, if_neg (by omega), sub_zero]

/-- **The jets of the tail are profile bounded with an exponent fixed by the order of the
equation.** -/
theorem hasProfileBoundExp_eulerJetVector_barnesTail_tail {m : ℕ} {s : ℝ} (hs : 0 < s)
    (N : ℕ) (j : Fin (m + 1)) :
    HasProfileBoundExp s (zetaTailBase s) m
      (eulerJetVector (m := m)
        (barnesTailSeries s - truncPowerSeries N (barnesTailSeries s)) j) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hK : (0 : ℝ) ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi := by positivity
  refine ⟨max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi, hK, fun k => ?_⟩
  have hjet : eulerJetVector (m := m)
      (barnesTailSeries s - truncPowerSeries N (barnesTailSeries s)) j
      = formalEulerOp^[(j : ℕ)]
        (barnesTailSeries s - truncPowerSeries N (barnesTailSeries s)) := rfl
  rw [hjet, coeff_formalEulerOp_iterate, norm_mul, norm_pow, Complex.norm_natCast]
  have hbase : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hstep : ((k : ℝ)) ^ (j : ℕ) ≤ ((k : ℝ) + 1) ^ m := by
    calc ((k : ℝ)) ^ (j : ℕ) ≤ ((k : ℝ) + 1) ^ (j : ℕ) :=
          pow_le_pow_left₀ hbase (by linarith) _
      _ ≤ ((k : ℝ) + 1) ^ m :=
          pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.mp j.2)
  have htail := norm_coeff_barnesTail_sub_truncPowerSeries_le hs N k
  have hmul : ((k : ℝ)) ^ (j : ℕ) *
      ‖PowerSeries.coeff k
        (barnesTailSeries s - truncPowerSeries N (barnesTailSeries s))‖
      ≤ ((k : ℝ) + 1) ^ m * zetaTailProfile s k :=
    mul_le_mul hstep htail (norm_nonneg _) (by positivity)
  refine le_trans hmul (le_of_eq ?_)
  rw [zetaTailProfile]
  ring

/-! ### The obstruction under a nondegeneracy hypothesis -/

/-- **The irrational-power Barnes tail is not annihilated by an analytic differential polynomial
whose linearization along it is nonzero.** -/
theorem not_isFormalEulerADESolution_barnesTail_of_nondegenerate {m : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hQa : IsAnalyticDifferentialPolynomial Q)
    {s : ℝ} (hs : 0 < s) (hirr : Irrational s)
    (hnd : ∃ j : Fin (m + 1),
      MvPolynomial.aeval (eulerJetVector (m := m) (barnesTailSeries s))
        (MvPolynomial.pderiv j Q) ≠ 0) :
    ¬ IsFormalEulerADESolution Q (barnesTailSeries s) := by
  classical
  intro hQs
  set F : PowerSeries ℂ := barnesTailSeries s with hFdef
  set β : ℝ := zetaTailBase s with hβdef
  have hβ : 0 < β := zetaTailBase_pos s
  set Θ : ℕ → ℝ := zetaTailProfile s with hΘdef
  obtain ⟨c₁, c₂, hprof⟩ := exists_isRegularFactorialProfile_zetaTailProfile hs hirr
  have hΘpos : ∀ k, 0 < Θ k := hprof.pos
  -- the linearization along the solution, and its least shift
  obtain ⟨j0, hj0⟩ := hnd
  set Bf : Fin (m + 1) → PowerSeries ℂ :=
    fun j => MvPolynomial.aeval (eulerJetVector (m := m) F) (MvPolynomial.pderiv j Q) with hBfdef
  have hexv : ∃ μ, shiftPolynomial Bf μ ≠ 0 := by
    obtain ⟨μ, hμ⟩ : ∃ μ, PowerSeries.coeff μ (Bf j0) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hj0 (PowerSeries.ext hc)
    exact ⟨μ, shiftPolynomial_ne_zero_of_coeff hμ⟩
  set v : ℕ := Nat.find hexv with hvdef
  have hv : shiftPolynomial Bf v ≠ 0 := Nat.find_spec hexv
  -- the exponent of the defect estimate, chosen before the truncation order
  obtain ⟨A, hAdef⟩ :=
    exists_uniform_norm_coeff_taylorDefect_le (m := m) hs hirr hβ Q hQa m
  -- the ceiling for the leading vertex, and the truncation order
  set νmax : ℕ := ⌈(m : ℝ) / s⌉₊ + v with hνmaxdef
  set N : ℕ := νmax + ⌈(A : ℝ) / s⌉₊ + 1 with hNdef
  set Y : PowerSeries ℂ := truncPowerSeries N F with hYdef
  set H : PowerSeries ℂ := F - Y with hHdef
  set B : Fin (m + 1) → PowerSeries ℂ := linearizationCoeff Q Y with hBdef
  -- the linearized equation
  have hYH : Y + H = F := by rw [hYdef, hHdef]; ring
  have hlin := eulerLinearOp_linearization_eq Q Y H (by rw [hYH]; exact hQs)
  set W : PowerSeries ℂ := MvPolynomial.aeval (eulerJetVector (m := m) Y) Q with hWdef
  set Def : PowerSeries ℂ :=
    taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) Q with hDefdef
  set G : PowerSeries ℂ := -W - Def with hGdef
  have hsol : eulerLinearOp B H = G := hlin
  -- the shift polynomials of the truncated operator agree with those of the solution up to `N`
  have hagree : ∀ μ, μ ≤ N → shiftPolynomial B μ = shiftPolynomial Bf μ := by
    intro μ hμ
    rw [shiftPolynomial, shiftPolynomial]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    exact coeff_aeval_eulerJetVector_truncPowerSeries_eq (MvPolynomial.pderiv j Q) F hμ
  have hvN : v ≤ N := by
    have : v ≤ νmax := by rw [hνmaxdef]; omega
    omega
  have hBv : shiftPolynomial B v ≠ 0 := by rw [hagree v hvN]; exact hv
  -- the leading Newton vertex
  have hdeg : ∀ μ, (shiftPolynomial B μ).natDegree ≤ m := natDegree_shiftPolynomial_le B
  obtain ⟨ν, hν, hνmaxle⟩ := exists_max_weightedLevel hs hdeg hBv
  have hmax : ∀ μ, shiftPolynomial B μ ≠ 0 → μ ≠ ν →
      weightedLevel s (shiftPolynomial B) μ < weightedLevel s (shiftPolynomial B) ν := by
    intro μ hΦ hμν
    rcases lt_or_eq_of_le (hνmaxle μ hΦ) with h | h
    · exact h
    · exact absurd (weightedLevel_injective_of_irrational hirr (shiftPolynomial B) h) hμν
  -- the vertex stays below the ceiling
  have hνle : ν ≤ νmax := by
    have hle := hνmaxle v hBv
    rw [weightedLevel, weightedLevel] at hle
    have hdν : (((shiftPolynomial B ν).natDegree : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hdeg ν
    have hdv : (0 : ℝ) ≤ (((shiftPolynomial B v).natDegree : ℕ) : ℝ) := Nat.cast_nonneg _
    have hkey : s * (ν : ℝ) ≤ (m : ℝ) + s * (v : ℝ) := by linarith
    have hdiv : (ν : ℝ) ≤ (m : ℝ) / s + (v : ℝ) := by
      rw [← sub_le_iff_le_add, le_div_iff₀ hs]
      nlinarith [hkey]
    have hceil : ((⌈(m : ℝ) / s⌉₊ : ℕ) : ℝ) ≥ (m : ℝ) / s := Nat.le_ceil _
    have : (ν : ℝ) ≤ ((νmax : ℕ) : ℝ) := by
      rw [hνmaxdef]
      push_cast
      linarith
    exact_mod_cast this
  have hνN : ν ≤ N + 1 := by omega
  -- the defect exponent is beaten by the shift of the profile
  have hAlt : (A : ℝ) < (((shiftPolynomial B ν).natDegree : ℕ) : ℝ)
      + s * ((N + 1 - ν : ℕ) : ℝ) := by
    have hdpos : (0 : ℝ) ≤ (((shiftPolynomial B ν).natDegree : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcount : ⌈(A : ℝ) / s⌉₊ + 2 ≤ N + 1 - ν := by omega
    have hcast : (((⌈(A : ℝ) / s⌉₊ + 2 : ℕ)) : ℝ) ≤ ((N + 1 - ν : ℕ) : ℝ) := by
      exact_mod_cast hcount
    have hceil : (A : ℝ) / s ≤ ((⌈(A : ℝ) / s⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hAs : (A : ℝ) ≤ s * ((⌈(A : ℝ) / s⌉₊ : ℕ) : ℝ) := by
      have h2 : s * ((A : ℝ) / s) ≤ s * ((⌈(A : ℝ) / s⌉₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hceil hs.le
      have hid : s * ((A : ℝ) / s) = (A : ℝ) := by field_simp
      rwa [hid] at h2
    have hmul : s * (((⌈(A : ℝ) / s⌉₊ + 2 : ℕ)) : ℝ) ≤ s * ((N + 1 - ν : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hs.le
    have hexp : s * (((⌈(A : ℝ) / s⌉₊ + 2 : ℕ)) : ℝ)
        = s * ((⌈(A : ℝ) / s⌉₊ : ℕ) : ℝ) + 2 * s := by
      push_cast
      ring
    linarith
  -- the ingredients of the transfer
  have hB : ∀ j, IsGevreySeries 0 (B j) := fun j =>
    isGevreySeries_zero_linearizationCoeff Q hQa F j
  obtain ⟨C, ρ, hC, hρ, hbd⟩ := exists_bound_shiftPolynomial_natDegree B hB
  set dν : ℕ := (shiftPolynomial B ν).natDegree with hdνdef
  have hZpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν) := fun n =>
    mul_pos (Real.rpow_pos_of_pos (by positivity) _) (hΘpos (n - ν))
  have hup : ∀ k, ‖PowerSeries.coeff k H‖ ≤ Θ k := fun k =>
    norm_coeff_barnesTail_sub_truncPowerSeries_le hs N k
  have hδ : (0 : ℝ) < 1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖) := by
    have h1 : (1 : ℝ) ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := le_max_left _ _
    positivity
  have hSinf := infinite_setOf_profile_le_abs_zetaTailModulus hs hirr
  have hS : ({k : ℕ | (1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖)) *
      zetaTailProfile s k ≤ |zetaTailModulus s k|} \ Set.Iic N).Infinite :=
    hSinf.sdiff (Set.finite_Iic N)
  have hlow : ∀ k ∈ ({k : ℕ | (1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖)) *
      zetaTailProfile s k ≤ |zetaTailModulus s k|} \ Set.Iic N),
      (1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖)) * Θ k
        ≤ ‖PowerSeries.coeff k H‖ := by
    intro k hk
    have hk1 : (1 / (2 * max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖)) * zetaTailProfile s k
        ≤ |zetaTailModulus s k| := hk.1
    have hk2 : N < k := by
      have := hk.2
      simpa using this
    rw [hHdef, hYdef, coeff_barnesTail_sub_truncPowerSeries_of_lt hk2,
      norm_coeff_barnesTailSeries, hΘdef]
    exact hk1
  obtain ⟨cl, hcl, N₀, hNl⟩ := exists_lower_bound_eval_natCast (shiftPolynomial B ν) hν
  set D : ℕ → ℝ := fun n => (cl / 2 ^ dν) * (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))
    with hDdef
  have hDpos : ∀ n, 0 < D n := fun n => mul_pos (by positivity) (hZpos n)
  have hdom : ∀ᶠ n : ℕ in atTop,
      D n ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ)‖ * Θ (n - ν) := by
    filter_upwards [eventually_ge_atTop (N₀ + ν), eventually_ge_atTop (2 * ν)] with n hn1 hn2
    have hshift : N₀ ≤ n - ν := by omega
    have hlowev := hNl (n - ν) hshift
    have hhalf : ((n : ℝ) + 1) / 2 ≤ (((n - ν : ℕ) : ℝ)) + 1 := half_le_cast_sub_add_one hn2
    have hmono : ((((n : ℝ) + 1) / 2)) ^ dν ≤ ((((n - ν : ℕ) : ℝ)) + 1) ^ dν :=
      pow_le_pow_left₀ (by positivity) hhalf dν
    have hrw : ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) = ((n : ℝ) + 1) ^ dν := Real.rpow_natCast _ _
    have hchain : (cl / 2 ^ dν) * ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ)
        ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ)‖ := by
      rw [hrw]
      refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left hmono hcl.le) hlowev)
      rw [div_pow]
      field_simp
    calc D n = ((cl / 2 ^ dν) * ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ)) * Θ (n - ν) := by
          rw [hDdef]; ring
      _ ≤ ‖(shiftPolynomial B ν).eval (((n - ν : ℕ) : ℕ) : ℂ)‖ * Θ (n - ν) :=
          mul_le_mul_of_nonneg_right hchain (hΘpos (n - ν)).le
  -- the three negligible sources
  have hWconv : IsGevreySeries 0 W := isGevreySeries_zero_aeval_truncPowerSeries Q hQa F
  have hlim1 : Tendsto (fun n : ℕ => ‖PowerSeries.coeff n W‖ /
      (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))) atTop (𝓝 0) :=
    tendsto_convergent_div_leading hprof hs hWconv dν ν
  have hHprof : ∀ j : Fin (m + 1), HasProfileBoundExp s β m (eulerJetVector (m := m) H j) :=
    fun j => hasProfileBoundExp_eulerJetVector_barnesTail_tail hs N j
  have hH0 : ∀ j : Fin (m + 1),
      (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ eulerJetVector (m := m) H j := fun j =>
    X_pow_dvd_formalEulerOp_iterate (j : ℕ) (X_pow_dvd_sub_truncPowerSeries N F)
  obtain ⟨cd, hcd, hdefbd⟩ :=
    hAdef N Y H (isGevreySeries_zero_truncPowerSeries N F) hHprof hH0
  have hKc : (0 : ℝ) < max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi := by
    have h1 : (1 : ℝ) ≤ max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ := le_max_left _ _
    have h2 : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have hgamma : ∀ k : ℕ,
      gammaProfile s β k = Θ k / (max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi) := by
    intro k
    rw [hΘdef, zetaTailProfile, hβdef]
    field_simp
  have hlim2 : Tendsto (fun n : ℕ => ‖PowerSeries.coeff n Def‖ /
      (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))) atTop (𝓝 0) := by
    have hbase := tendsto_shiftedProfile_div_leading (A := (A : ℝ)) (d := ((dν : ℕ) : ℝ))
      hprof hs hνN hAlt
    have hmaj := hbase.const_mul
      (cd / (max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi) ^ 2)
    rw [mul_zero] at hmaj
    refine squeeze_zero' (Eventually.of_forall fun n => ?_)
      (Eventually.of_forall fun n => ?_) hmaj
    · exact div_nonneg (norm_nonneg _) (hZpos n).le
    · rw [div_le_iff₀ (hZpos n)]
      have hbd1 := hdefbd n
      rw [hgamma (N + 1), hgamma (n - (N + 1))] at hbd1
      have hrw : ((n : ℝ) + 1) ^ A = ((n : ℝ) + 1) ^ ((A : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
      rw [hrw] at hbd1
      refine le_trans hbd1 (le_of_eq ?_)
      have hne1 : zetaTailProfile s (n - ν) ≠ 0 := ne_of_gt (zetaTailProfile_pos hs _)
      have hne2 : max 1 ‖riemannZeta ((1 + s : ℝ) : ℂ)‖ / Real.pi ≠ 0 := ne_of_gt hKc
      simp only [hΘdef]
      field_simp
  have hlim3 := tendsto_shiftTail_div_leading hC hρ hs hdeg hbd hprof hmax
  have hrest : Tendsto (fun n : ℕ =>
      (‖PowerSeries.coeff n G‖ + ∑ μ ∈ (Finset.range (n + 1)).erase ν,
        ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)) / D n)
      atTop (𝓝 0) := by
    have hsum3 : Tendsto (fun n : ℕ =>
        ‖PowerSeries.coeff n W‖ / (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))
          + ‖PowerSeries.coeff n Def‖ / (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))
          + (∑ μ ∈ (Finset.range (n + 1)).erase ν,
              ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)) /
            (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))) atTop (𝓝 0) := by
      have h := (hlim1.add hlim2).add hlim3
      simpa using h
    have hmaj := hsum3.const_mul ((2 : ℝ) ^ dν / cl)
    rw [mul_zero] at hmaj
    refine squeeze_zero' (Eventually.of_forall fun n => ?_)
      (Eventually.of_forall fun n => ?_) hmaj
    · refine div_nonneg ?_ (hDpos n).le
      exact add_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun μ _ => mul_nonneg (norm_nonneg _) (hΘpos (n - μ)).le)
    · have hGn : ‖PowerSeries.coeff n G‖
          ≤ ‖PowerSeries.coeff n W‖ + ‖PowerSeries.coeff n Def‖ := by
        rw [hGdef, map_sub, map_neg]
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_neg]
      have hDval : D n = (cl / 2 ^ dν) * (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν)) := rfl
      rw [hDval, div_le_iff₀ (mul_pos (by positivity) (hZpos n))]
      have hexp : (2 : ℝ) ^ dν / cl *
          (‖PowerSeries.coeff n W‖ / (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))
            + ‖PowerSeries.coeff n Def‖ / (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))
            + (∑ μ ∈ (Finset.range (n + 1)).erase ν,
                ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ)) /
              (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν))) *
          (cl / 2 ^ dν * (((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) * Θ (n - ν)))
          = ‖PowerSeries.coeff n W‖ + ‖PowerSeries.coeff n Def‖
            + ∑ μ ∈ (Finset.range (n + 1)).erase ν,
                ‖(shiftPolynomial B μ).eval (((n - μ : ℕ) : ℕ) : ℂ)‖ * Θ (n - μ) := by
        have hne1 : Θ (n - ν) ≠ 0 := ne_of_gt (hΘpos _)
        have hne2 : ((n : ℝ) + 1) ^ ((dν : ℕ) : ℝ) ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
        have hne3 : cl ≠ 0 := ne_of_gt hcl
        field_simp
      rw [hexp]
      linarith [hGn]
  exact false_of_dominant_transfer B hsol Θ hup hδ hS hlow ν D hDpos hdom hrest

/-! ### Hypertranscendence -/

/-- **The irrational-power Barnes tail is hypertranscendental.**  No nonzero algebraic differential
polynomial with convergent coefficients annihilates it. -/
theorem not_isFormalEulerADESolution_barnesTail {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P) (hP0 : P ≠ 0)
    {s : ℝ} (hs : 0 < s) (hirr : Irrational s) :
    ¬ IsFormalEulerADESolution P (barnesTailSeries s) := by
  intro hsol
  obtain ⟨Q, hQ0, hQa, hQs, j0, hj0⟩ :=
    exists_nondegenerate_annihilator P.totalDegree P rfl hP0 hP hsol
  exact not_isFormalEulerADESolution_barnesTail_of_nondegenerate Q hQa hs hirr ⟨j0, hj0⟩ hQs

end GaloisForLFunctions.HTGeometry
