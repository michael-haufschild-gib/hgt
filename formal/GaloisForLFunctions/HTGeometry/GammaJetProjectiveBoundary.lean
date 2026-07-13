import GaloisForLFunctions.HTGeometry.GammaProjectiveBoundary

/-!
# The full Gamma-jet projective boundary

For every order `n` and every `σ > 0`,
`Γ⁽ⁿ⁾(σ + it) / Γ⁽ⁿ⁺¹⁾(σ + it) → 0` as `t → +∞`.
This is the all-orders form of the two-jet boundary already in `GammaProjectiveBoundary`, and it
realizes the one-point projective boundary (§1, eq. 5) for the canonical Gamma jet tuple: chaining
the ratios shows `Γ⁽ⁱ⁾ / Γ⁽ʳ⁾ → 0` for `i < r`, so the tuple `(Γ, Γ', …, Γ⁽ʳ⁾)` normalized by its
dominant component tends to the single constant point `(0, …, 0, 1)`.

The mechanism: `Γ⁽ⁿ⁾ = Γ · Pₙ` with `Pₙ = eval(ψ, ψ', …) (gammaBell n)` the digamma jet Bell value.
On the upper vertical line `ψ = digamma → ∞` while every positive-order polygamma `ψ⁽ʲ⁾ → 0`.  The
Bell value therefore has leading term `ψⁿ`: `Pₙ / ψⁿ → 1`.  A uniform `MvPolynomial.eval` norm bound
of degree `totalDegree (gammaBell n) ≤ n` controls the correction, and the ratio
`Γ⁽ⁿ⁾/Γ⁽ⁿ⁺¹⁾ = Pₙ/Pₙ₊₁ = (Pₙ/ψⁿ)(ψⁿ⁺¹/Pₙ₊₁)(1/ψ) → 1·1·0 = 0`.
-/

open Filter MvPolynomial

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- A uniform norm bound for a multivariate polynomial evaluated at a jet: with every coordinate
bounded by `B ≥ 1`, the value is bounded by the coefficient `ℓ¹`-mass times `B^{totalDegree}`. -/
theorem norm_eval_le_pow {m : ℕ} (G : MvPolynomial (Fin m) ℂ) (v : Fin m → ℂ) (B : ℝ)
    (hB : 1 ≤ B) (hv : ∀ i : Fin m, ‖v i‖ ≤ B) :
    ‖MvPolynomial.eval v G‖ ≤ (∑ d ∈ G.support, ‖MvPolynomial.coeff d G‖) * B ^ G.totalDegree := by
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  have hprod : ‖∏ i, v i ^ (d i)‖ ≤ B ^ G.totalDegree := by
    rw [norm_prod]
    have h1 : ∏ i : Fin m, ‖v i ^ (d i)‖ ≤ ∏ i : Fin m, B ^ (d i) := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hv i) _
    refine h1.trans ?_
    rw [Finset.prod_pow_eq_pow_sum]
    apply pow_le_pow_right₀ hB
    calc ∑ i, d i = d.sum (fun _ e => e) :=
          (Finsupp.sum_fintype d (fun _ e => e) (fun _ => rfl)).symm
      _ ≤ G.totalDegree := MvPolynomial.le_totalDegree hd
  exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)

/-- Partial differentiation does not raise total degree. -/
theorem totalDegree_pderiv_le {σ : Type*} (i : σ) (p : MvPolynomial σ ℂ) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro d hd
  rw [pderiv_monomial]
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  rw [Finsupp.sum, Finsupp.sum]
  have hsub : (d - Finsupp.single i 1).support ⊆ d.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk ⊢
    intro h; apply hk; simp [Finsupp.tsub_apply, h]
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => Nat.zero_le _))
  exact Nat.sub_le _ _

/-- The order-`n` Gamma Bell polynomial has total degree at most `n`. -/
theorem totalDegree_gammaBell_le : ∀ n, (gammaBell n).totalDegree ≤ n
  | 0 => by simp [gammaBell]
  | n + 1 => by
      simp only [gammaBell]
      refine (MvPolynomial.totalDegree_add _ _).trans ?_
      apply max_le
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_X]
        have h := (MvPolynomial.totalDegree_rename_le Fin.castSucc (gammaBell n)).trans
          (totalDegree_gammaBell_le n)
        omega
      · apply MvPolynomial.totalDegree_finsetSum_le
        intro j _
        refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_X]
        have h1 : (MvPolynomial.rename Fin.castSucc (pderiv j (gammaBell n))).totalDegree ≤ n :=
          (MvPolynomial.totalDegree_rename_le _ _).trans
            ((totalDegree_pderiv_le j (gammaBell n)).trans (totalDegree_gammaBell_le n))
        omega

/-- The digamma-jet Bell value: `Pₙ(s) = eval(ψ(s), ψ'(s), …) (gammaBell n)`, so that
`Γ⁽ⁿ⁾(s) = Γ(s) · bellVal n s` off the poles. -/
def bellVal (n : ℕ) (s : ℂ) : ℂ :=
  MvPolynomial.eval (fun j : Fin n => iteratedDeriv (j : ℕ) Complex.digamma s) (gammaBell n)

/-- The Bell-value recurrence obtained by evaluating the `gammaBell` recursion at the jet. -/
theorem bellVal_succ (n : ℕ) (s : ℂ) :
    bellVal (n + 1) s = Complex.digamma s * bellVal n s
      + ∑ j : Fin n, MvPolynomial.eval
          (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma s) (pderiv j (gammaBell n))
          * iteratedDeriv ((j : ℕ) + 1) Complex.digamma s := by
  unfold bellVal
  simp only [gammaBell, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_succ,
    Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero]

/-- Digamma has unbounded norm on every upper vertical line in the open right half-plane. -/
theorem norm_digamma_vertical_tendsto_atTop {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ => ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (re_digamma_vertical_tendsto_atTop hσ)
  exact Filter.Eventually.of_forall (fun _ => Complex.re_le_norm _)

/-- **The Bell value has leading term `ψⁿ`**: `bellVal n (σ+it) / ψ(σ+it)ⁿ → 1` for `σ > 0`. -/
theorem bellVal_div_pow_tendsto_one (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => bellVal n ((σ : ℂ) + (t : ℂ) * Complex.I) /
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n) atTop (nhds 1) := by
  induction n with
  | zero =>
      have h : (fun t : ℝ => bellVal 0 ((σ : ℂ) + (t : ℂ) * Complex.I) /
          (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ 0) = fun _ => 1 := by
        funext t; simp [bellVal, gammaBell]
      rw [h]; exact tendsto_const_nhds
  | succ n ih =>
      have hψinf : Tendsto
          (fun t : ℝ => ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop :=
        norm_digamma_vertical_tendsto_atTop hσ.le
      have hψge1 : ∀ᶠ (t : ℝ) in atTop,
          (1 : ℝ) ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
        hψinf.eventually_ge_atTop 1
      have hψne : ∀ᶠ (t : ℝ) in atTop, Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        filter_upwards [hψge1] with t ht
        intro h; rw [h, norm_zero] at ht; linarith
      -- eventual uniform jet bound: every jet coordinate is ≤ 1 + ‖ψ‖
      have hjetEv : ∀ᶠ (t : ℝ) in atTop, ∀ k : Fin n,
          ‖iteratedDeriv (k : ℕ) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ 1 + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [eventually_all]
        intro k
        rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
        · filter_upwards with t
          rw [hk, iteratedDeriv_zero]
          linarith [norm_nonneg (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))]
        · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
          have hz0 : Tendsto (fun t : ℝ => ‖iteratedDeriv (m + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop (nhds 0) := by
            simpa using (iteratedDeriv_digamma_vertical_tendsto_zero m hσ).norm
          have hev : ∀ᶠ (t : ℝ) in atTop, ‖iteratedDeriv (m + 1) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I)‖ < 1 :=
            hz0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
          filter_upwards [hev] with t htv
          rw [hm]
          linarith [norm_nonneg (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))]
      -- the jet-correction term divided by ψ^{n+1} tends to 0
      have hQdiv : Tendsto (fun t : ℝ => (∑ j : Fin n, MvPolynomial.eval
          (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I)) (pderiv j (gammaBell n))
          * iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
          / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (n + 1)) atTop (nhds 0) := by
        have hrw : (fun t : ℝ => (∑ j : Fin n, MvPolynomial.eval
            (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I)) (pderiv j (gammaBell n))
            * iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (n + 1))
            = fun t : ℝ => ∑ j : Fin n, (MvPolynomial.eval
              (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I)) (pderiv j (gammaBell n))
              * iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
              / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (n + 1) := by
          funext t; rw [Finset.sum_div]
        rw [hrw, show (0 : ℂ) = ∑ _j : Fin n, (0 : ℂ) by simp]
        apply tendsto_finsetSum
        intro j _
        set Cj : ℝ := ∑ d ∈ (pderiv j (gammaBell n)).support,
          ‖MvPolynomial.coeff d (pderiv j (gammaBell n))‖ with hCjdef
        have hCj0 : 0 ≤ Cj := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        have htd : (pderiv j (gammaBell n)).totalDegree ≤ n :=
          (totalDegree_pderiv_le j (gammaBell n)).trans (totalDegree_gammaBell_le n)
        refine squeeze_zero_norm' ?_
          (by
            have hz : Tendsto (fun t : ℝ => iteratedDeriv ((j : ℕ) + 1) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) :=
              iteratedDeriv_digamma_vertical_tendsto_zero (j : ℕ) hσ
            have := hz.norm.const_mul (Cj * 2 ^ n)
            simpa using this)
        filter_upwards [hψge1, hjetEv] with t ht hjet
        have hB : (1 : ℝ) ≤ 1 + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
          linarith [norm_nonneg (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))]
        have hw0 : (0 : ℝ) < ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by linarith
        have heval : ‖MvPolynomial.eval (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I)) (pderiv j (gammaBell n))‖
            ≤ Cj * (1 + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ^ n := by
          refine (norm_eval_le_pow (pderiv j (gammaBell n)) _
            (1 + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) hB hjet).trans ?_
          rw [← hCjdef]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB htd) hCj0
        have hstep : ‖MvPolynomial.eval (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I)) (pderiv j (gammaBell n))‖
            ≤ Cj * 2 ^ n * ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ n := by
          refine heval.trans ?_
          have hple : (1 + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ^ n
              ≤ (2 * ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ^ n :=
            pow_le_pow_left₀ (by positivity) (by linarith) n
          calc Cj * (1 + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ^ n
              ≤ Cj * (2 * ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ^ n :=
                mul_le_mul_of_nonneg_left hple hCj0
            _ = Cj * 2 ^ n * ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ n := by
                rw [mul_pow]; ring
        rw [norm_div, norm_mul, norm_pow]
        calc ‖MvPolynomial.eval (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma
                  ((σ : ℂ) + (t : ℂ) * Complex.I)) (pderiv j (gammaBell n))‖
              * ‖iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              / ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ (n + 1)
            ≤ (Cj * 2 ^ n * ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ n)
              * ‖iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              / ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ (n + 1) := by
                gcongr
          _ = Cj * 2 ^ n
              * ‖iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              * (‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ n
                  / ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ (n + 1)) := by ring
          _ ≤ Cj * 2 ^ n
              * ‖iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              * 1 := by
                have hle1 : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ n
                    / ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ (n + 1) ≤ 1 := by
                  rw [div_le_one (by positivity), pow_succ]
                  nlinarith [pow_pos hw0 n, ht]
                have hA0 : (0 : ℝ) ≤ Cj * 2 ^ n
                    * ‖iteratedDeriv ((j : ℕ) + 1) Complex.digamma
                        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
                  mul_nonneg (mul_nonneg hCj0 (by positivity)) (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left hle1 hA0
          _ = Cj * 2 ^ n
              * ‖iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
                ring
      -- combine via the recurrence
      have hmodel : Tendsto (fun t : ℝ =>
          bellVal n ((σ : ℂ) + (t : ℂ) * Complex.I)
            / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n
          + (∑ j : Fin n, MvPolynomial.eval
              (fun k : Fin n => iteratedDeriv (k : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I)) (pderiv j (gammaBell n))
              * iteratedDeriv ((j : ℕ) + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
            / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (n + 1)) atTop (nhds 1) := by
        simpa using ih.add hQdiv
      refine hmodel.congr' ?_
      filter_upwards [hψne] with t ht
      rw [bellVal_succ]
      field_simp
      ring

/-- **The full Gamma-jet projective boundary.**  For every order `n` and every `σ > 0`,
`Γ⁽ⁿ⁾(σ + it) / Γ⁽ⁿ⁺¹⁾(σ + it) → 0` as `t → +∞`.  This is the all-orders form of
`Gamma_div_deriv_vertical_tendsto_zero` (`n = 0`) and
`deriv_Gamma_div_second_vertical_tendsto_zero` (`n = 1`). -/
theorem iteratedDeriv_Gamma_div_succ_vertical_tendsto_zero (n : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
      iteratedDeriv n Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        iteratedDeriv (n + 1) Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hA := bellVal_div_pow_tendsto_one n hσ
  have hB := bellVal_div_pow_tendsto_one (n + 1) hσ
  have hBinv : Tendsto (fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (n + 1) /
      bellVal (n + 1) ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hB.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hψinv : Tendsto (fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      atTop (nhds 0) := inv_digamma_vertical_tendsto_zero hσ.le
  have hmodel : Tendsto (fun t : ℝ =>
      (bellVal n ((σ : ℂ) + (t : ℂ) * Complex.I)
        / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n)
      * ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (n + 1)
        / bellVal (n + 1) ((σ : ℂ) + (t : ℂ) * Complex.I))
      * (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) atTop (nhds 0) := by
    simpa using (hA.mul hBinv).mul hψinv
  have hψinf : Tendsto
      (fun t : ℝ => ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop :=
    norm_digamma_vertical_tendsto_atTop hσ.le
  have hψge1 : ∀ᶠ (t : ℝ) in atTop,
      (1 : ℝ) ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hψinf.eventually_ge_atTop 1
  have hbne : ∀ᶠ (t : ℝ) in atTop, bellVal (n + 1) ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    have hb := hB.eventually (isOpen_ne.mem_nhds (show (1 : ℂ) ≠ 0 by norm_num))
    filter_upwards [hb] with t ht
    intro h; rw [h, zero_div] at ht; exact ht rfl
  refine hmodel.congr' ?_
  filter_upwards [hψge1, hbne] with t ht hbnet
  have hψnet : Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h; rw [h, norm_zero] at ht; linarith
  have hpoles : ∀ p : ℕ, ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ -(p : ℂ) := by
    intro p heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hΓ : Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := Complex.Gamma_ne_zero hpoles
  have hGn : iteratedDeriv n Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        * bellVal n ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    gamma_iteratedDeriv_eq_gamma_mul_eval_gammaBell n ((σ : ℂ) + (t : ℂ) * Complex.I) hpoles
  have hGn1 : iteratedDeriv (n + 1) Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        * bellVal (n + 1) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    gamma_iteratedDeriv_eq_gamma_mul_eval_gammaBell (n + 1) ((σ : ℂ) + (t : ℂ) * Complex.I) hpoles
  rw [hGn, hGn1]
  field_simp
  ring

/-- **The one-point projective boundary of the Gamma jet tuple (§1, eq. 5).**  For every pair of
orders `i < r` and every `σ > 0`, `Γ⁽ⁱ⁾(σ + it) / Γ⁽ʳ⁾(σ + it) → 0` as `t → +∞`.  Consequently the
tuple `(Γ, Γ', …, Γ⁽ʳ⁾)(σ + it)` normalized by its dominant (highest-order) component tends to the
single constant point `(0, …, 0, 1)`: every lower-order coordinate ratio collapses to `0`. -/
theorem iteratedDeriv_Gamma_div_higher_vertical_tendsto_zero (i r : ℕ) (hir : i < r) {σ : ℝ}
    (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
      iteratedDeriv i Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        iteratedDeriv r Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hA := bellVal_div_pow_tendsto_one i hσ
  have hB := bellVal_div_pow_tendsto_one r hσ
  have hBinv : Tendsto (fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ r /
      bellVal r ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hB.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hψinf : Tendsto
      (fun t : ℝ => ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop :=
    norm_digamma_vertical_tendsto_atTop hσ.le
  have hψge1 : ∀ᶠ (t : ℝ) in atTop,
      (1 : ℝ) ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hψinf.eventually_ge_atTop 1
  have hψne : ∀ᶠ (t : ℝ) in atTop, Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [hψge1] with t ht
    intro h; rw [h, norm_zero] at ht; linarith
  -- the pure-power ratio ψ^i / ψ^r = (ψ⁻¹)^{r-i} → 0 since i < r
  have hpow : Tendsto (fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ i /
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ r) atTop (nhds 0) := by
    have hψinv : Tendsto (fun t : ℝ => (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
        atTop (nhds 0) := inv_digamma_vertical_tendsto_zero hσ.le
    have hpp : Tendsto (fun t : ℝ => ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) ^ (r - i))
        atTop (nhds 0) := by
      simpa [zero_pow (Nat.sub_ne_zero_of_lt hir)] using hψinv.pow (r - i)
    refine hpp.congr' ?_
    filter_upwards [hψne] with t ht
    have h1r : (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ r
        = (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (r - i)
          * (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ i := by
      rw [← pow_add]; congr 1; omega
    rw [eq_div_iff (pow_ne_zero r ht), inv_pow, h1r, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero (r - i) ht), one_mul]
  have hmodel : Tendsto (fun t : ℝ =>
      (bellVal i ((σ : ℂ) + (t : ℂ) * Complex.I)
        / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ i)
      * ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ r
        / bellVal r ((σ : ℂ) + (t : ℂ) * Complex.I))
      * ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ i
        / (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ r)) atTop (nhds 0) := by
    simpa using (hA.mul hBinv).mul hpow
  have hbne : ∀ᶠ (t : ℝ) in atTop, bellVal r ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    have hb := hB.eventually (isOpen_ne.mem_nhds (show (1 : ℂ) ≠ 0 by norm_num))
    filter_upwards [hb] with t ht
    intro h; rw [h, zero_div] at ht; exact ht rfl
  refine hmodel.congr' ?_
  filter_upwards [hψne, hbne] with t hψnet hbnet
  have hpoles : ∀ p : ℕ, ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ -(p : ℂ) := by
    intro p heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hΓ : Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := Complex.Gamma_ne_zero hpoles
  have hGi : iteratedDeriv i Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        * bellVal i ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    gamma_iteratedDeriv_eq_gamma_mul_eval_gammaBell i ((σ : ℂ) + (t : ℂ) * Complex.I) hpoles
  have hGr : iteratedDeriv r Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        * bellVal r ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    gamma_iteratedDeriv_eq_gamma_mul_eval_gammaBell r ((σ : ℂ) + (t : ℂ) * Complex.I) hpoles
  rw [hGi, hGr]
  field_simp

end

end GaloisForLFunctions
