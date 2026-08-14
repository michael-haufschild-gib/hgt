import GaloisForLFunctions.HTGeometry.NonlinearMailletAux

/-!
# Maillet's theorem for a nonlinear analytic algebraic differential equation

Every formal solution of

```text
P(t, θF, …, θ^m F) = 0 ,      θ = t d/dt ,
```

with convergent coefficients and a nondegenerate indicial polynomial along a truncation of the
solution is Gevrey of a finite integral order.

The proof linearizes along the truncation `Y` of the solution at order `N`.  Writing `H = F − Y`,

```text
L(H) = −P(jets Y) − defect ,      L = ∑_j (∂_j P)(jets Y) θ^j ,
```

with `L` convergent, `P(jets Y)` convergent, and the defect a finite sum of monomials of degree at
least two in the jets of `H`.  The coefficient recursion of `L` then reads

```text
Φ_0(n) h_n = coeff_n(−P(jets Y) − defect) − ∑_{k<n} Φ_{n−k}(k) h_k ,
```

and is estimated in the weighted norm `‖h_n‖ (n+1)^{m+2} ≤ ε A^n (n!)^r`.  Three features make the
estimate close.

* Each `θ^j` costs one unit of weight, so the jets of `H` still carry weight `2`.
* A monomial of degree at least two in series vanishing to order `N+1` gains `(N+1) r` units of
  weight, which for `N + 1 ≥ m` restores the weight the jets cost.
* The defect at level `n` only sees `H` below level `n`, because every one of its monomials carries
  two factors that vanish to high order; so the recursion is a recursion.

The size `ε` of the induction is then chosen small enough that the defect, which is quadratic in it,
is dominated by the indicial lower bound, and the geometric base `A` large enough that the
convolution and the value at the truncation are.
-/

open PowerSeries MvPolynomial
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 4000000 in
/-- **Maillet's theorem, nonlinear case.**  A formal solution of an analytic algebraic differential
equation whose linearization along a truncation has a nonzero indicial polynomial is Gevrey of a
finite integral order. -/
theorem exists_isGevreySeries_of_isFormalEulerADESolution {m N : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P)
    {F : PowerSeries ℂ} (hsol : IsFormalEulerADESolution P F)
    (hNm : m ≤ N + 1)
    (hΦ : shiftPolynomial (linearizationCoeff P (truncSeries N F)) 0 ≠ 0) :
    ∃ r : ℕ, IsGevreySeries (r : ℝ) F := by
  classical
  -- the linearization along the truncation
  have hHdvd0 : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ (F - truncSeries N F) :=
    X_pow_dvd_sub_truncSeries N F
  have hYH0 : truncSeries N F + (F - truncSeries N F) = F := by ring
  have hsol'0 : IsFormalEulerADESolution P (truncSeries N F + (F - truncSeries N F)) := by
    rw [hYH0]; exact hsol
  have hBconv0 : ∀ j, IsGevreySeries 0 (linearizationCoeff P (truncSeries N F) j) := fun j =>
    isGevreySeries_zero_linearizationCoeff P hP F j
  have hVconv0 : IsGevreySeries 0 (MvPolynomial.aeval (eulerJetVector (truncSeries N F)) P) :=
    isGevreySeries_zero_aeval_truncSeries P hP F
  have hYconv0 : IsGevreySeries 0 (truncSeries N F) := isGevreySeries_zero_truncSeries N F
  have hLH0 : eulerLinearOp (linearizationCoeff P (truncSeries N F)) (F - truncSeries N F)
      = -(MvPolynomial.aeval (eulerJetVector (truncSeries N F)) P)
        - taylorDefect (eulerJetVector (truncSeries N F))
            (eulerJetVector (F - truncSeries N F)) P :=
    eulerLinearOp_linearization_eq P (truncSeries N F) (F - truncSeries N F) hsol'0
  obtain ⟨T, hTs, hTc, hTsum⟩ :=
    hasTaylorDefectFamily (A := PowerSeries ℂ) convergentSubsemiring P hP
  set Y : PowerSeries ℂ := truncSeries N F with hYdef
  set H : PowerSeries ℂ := F - Y with hHdef
  set B : Fin (m + 1) → PowerSeries ℂ := linearizationCoeff P Y with hBdef
  set V : PowerSeries ℂ := MvPolynomial.aeval (eulerJetVector Y) P with hVdef
  set d : ℕ := (shiftPolynomial B 0).natDegree with hddef
  set r : ℕ := max (m - d) 1 with hrdef
  set a : ℕ := m + 2 with hadef
  set w : ℕ := 2 + (N + 1) * r with hwdef
  refine ⟨r, ?_⟩
  -- arithmetic of the exponents
  have hr1 : 1 ≤ r := le_max_right _ _
  have hmdr : m ≤ d + r := by
    have h1 : m - d ≤ r := le_max_left _ _
    omega
  have hw2 : 2 ≤ w := by omega
  have haw : a ≤ w := by
    have h1 : (N + 1) * 1 ≤ (N + 1) * r := Nat.mul_le_mul_left _ hr1
    omega
  -- the coefficients of the Taylor family, evaluated at the truncation
  set W : (Fin (m + 1) →₀ ℕ) → PowerSeries ℂ :=
    fun α => MvPolynomial.aeval (eulerJetVector Y) (T α) with hWdef
  have hWconv : ∀ α, IsGevreySeries ((0 : ℕ) : ℝ) (W α) := by
    intro α
    have h := isGevreySeries_aeval_eulerJetVector (r := 0) le_rfl (T α) (fun σ => hTc α σ) hYconv0
    rw [Nat.cast_zero]
    exact h
  -- the constants of the recursion
  obtain ⟨c, hc, N₀, hlow⟩ := exists_lower_bound_eval_natCast (shiftPolynomial B 0) hΦ
  obtain ⟨Cb, ρ, hCb, hρ, hshift⟩ := exists_bound_shiftPolynomial B hBconv0
  obtain ⟨Ca, hCa1, hCa⟩ := exists_succ_pow_le_const_mul_pow a (by norm_num : (1 : ℝ) < 2)
  have hVconv0' : IsGevreySeries ((0 : ℕ) : ℝ) V := by simpa using hVconv0
  obtain ⟨Cv, Av, hCv, hAv, hVb⟩ := exists_gevreyWeightBound hVconv0' a
  obtain ⟨Cw, Aw, hCw, hAw, hWb⟩ :=
    exists_common_gevreyWeightBound W w 0 T.support (fun α _ => hWconv α)
  set N₁ : ℕ := max N₀ 1 with hN₁def
  -- the size of the induction
  set K : ℝ := ∑ α ∈ T.support,
      (2 : ℝ) ^ (w + 2) * Cw * ((2 : ℝ) ^ (2 + 2)) ^ (jetDegree α)
        * (((N + 1)! : ℝ)) ^ r * 2 ^ ((N + 1) * r) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    refine Finset.sum_nonneg fun α _ => ?_
    positivity
  set ε : ℝ := min 1 (c / (3 * (K + 1))) with hεdef
  have hεpos : 0 < ε := by
    refine lt_min one_pos ?_
    positivity
  have hε0 : (0 : ℝ) ≤ ε := le_of_lt hεpos
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεK : K * ε ≤ c / 3 := by
    have h1 : ε ≤ c / (3 * (K + 1)) := min_le_right _ _
    have h2 : K * ε ≤ K * (c / (3 * (K + 1))) := mul_le_mul_of_nonneg_left h1 hK0
    have h3 : K * (c / (3 * (K + 1))) ≤ c / 3 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hK0, le_of_lt hc]
    linarith
  -- the geometric base
  set A : ℝ := Aw + Av + 4 * ρ + 12 * Cb * Ca * ρ / c + 3 * Cv * Av / (c * ε) + 1
      + (∑ k ∈ Finset.range N₁,
          ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a / (ε * ((k ! : ℝ)) ^ r)) with hAdef
  have hsum0 : (0 : ℝ) ≤ ∑ k ∈ Finset.range N₁,
      ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a / (ε * ((k ! : ℝ)) ^ r) :=
    Finset.sum_nonneg fun k _ => by positivity
  have hpos1 : (0 : ℝ) < 12 * Cb * Ca * ρ / c := by positivity
  have hpos2 : (0 : ℝ) < 3 * Cv * Av / (c * ε) := by positivity
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hA1 : (1 : ℝ) ≤ A := by
    rw [hAdef]
    have := le_of_lt hAw; have := le_of_lt hAv; have := le_of_lt hρ
    linarith [hsum0, le_of_lt hpos1, le_of_lt hpos2]
  have hAAw : Aw ≤ A := by
    rw [hAdef]
    have := le_of_lt hAv; have := le_of_lt hρ
    linarith [hsum0, le_of_lt hpos1, le_of_lt hpos2]
  have hAAv : Av ≤ A := by
    rw [hAdef]
    have := le_of_lt hAw; have := le_of_lt hρ
    linarith [hsum0, le_of_lt hpos1, le_of_lt hpos2]
  have hA4ρ : 4 * ρ ≤ A := by
    rw [hAdef]
    have := le_of_lt hAw; have := le_of_lt hAv
    linarith [hsum0, le_of_lt hpos1, le_of_lt hpos2]
  have hAgeom : 12 * Cb * Ca * ρ / c ≤ A := by
    rw [hAdef]
    have := le_of_lt hAw; have := le_of_lt hAv; have := le_of_lt hρ
    linarith [hsum0, le_of_lt hpos2]
  have hAval : 3 * Cv * Av / (c * ε) ≤ A := by
    rw [hAdef]
    have := le_of_lt hAw; have := le_of_lt hAv; have := le_of_lt hρ
    linarith [hsum0, le_of_lt hpos1]
  have hAbase : (∑ k ∈ Finset.range N₁,
      ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a / (ε * ((k ! : ℝ)) ^ r)) ≤ A := by
    rw [hAdef]
    have := le_of_lt hAw; have := le_of_lt hAv; have := le_of_lt hρ
    linarith [le_of_lt hpos1, le_of_lt hpos2]
  -- the geometric ratio
  set q : ℝ := ρ / A with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq2 : 2 * q ≤ 1 / 2 := by
    rw [hqdef, ← mul_div_assoc, div_le_div_iff₀ hApos (by norm_num : (0 : ℝ) < 2)]
    linarith [hA4ρ]
  have hq21 : 2 * q < 1 := by linarith
  have hqden : (1 : ℝ) / 2 ≤ 1 - 2 * q := by linarith
  have hqgeom : Cb * (Ca * ((2 * q) / (1 - 2 * q))) ≤ c / 3 := by
    have hstep : (2 * q) / (1 - 2 * q) ≤ 4 * q := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hq0, hqden]
    have hq4 : 4 * q ≤ c / (3 * Cb * Ca) := by
      have hform : 4 * q = 4 * ρ / A := by rw [hqdef]; ring
      rw [hform, div_le_div_iff₀ hApos (by positivity)]
      have hAc : (12 * Cb * Ca * ρ / c) * c ≤ A * c :=
        mul_le_mul_of_nonneg_right hAgeom (le_of_lt hc)
      have hexp : (12 * Cb * Ca * ρ / c) * c = 12 * Cb * Ca * ρ := by field_simp
      rw [hexp] at hAc
      nlinarith [hAc]
    calc Cb * (Ca * ((2 * q) / (1 - 2 * q))) ≤ Cb * (Ca * (4 * q)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep ?_) (le_of_lt hCb)
          linarith [hCa1]
      _ ≤ Cb * (Ca * (c / (3 * Cb * Ca))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq4 ?_) (le_of_lt hCb)
          linarith [hCa1]
      _ = c / 3 := by field_simp
  -- the main induction
  have hmain : GevreyWeightBound a ε A r H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hfacpos : (0 : ℝ) < ((n ! : ℝ)) ^ r := by positivity
      have hfac1 : (1 : ℝ) ≤ ((n ! : ℝ)) ^ r := one_le_pow₀ (one_le_factorial_cast n)
      have hApown : (0 : ℝ) < A ^ n := pow_pos hApos n
      by_cases hnN : n < N₁
      · rcases Nat.eq_zero_or_pos n with hn0 | hn0
        · subst hn0
          have h0 : PowerSeries.coeff 0 H = 0 := (PowerSeries.X_pow_dvd_iff.mp hHdvd0) 0 (by omega)
          rw [h0, norm_zero, zero_mul]
          positivity
        · have hmem : n ∈ Finset.range N₁ := Finset.mem_range.mpr hnN
          have hterm : ‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a / (ε * ((n ! : ℝ)) ^ r)
              ≤ ∑ k ∈ Finset.range N₁,
                  ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a / (ε * ((k ! : ℝ)) ^ r) :=
            Finset.single_le_sum
              (f := fun k : ℕ =>
                ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a / (ε * ((k ! : ℝ)) ^ r))
              (fun k _ => by positivity) hmem
          have hAn : A ≤ A ^ n := le_self_pow₀ hA1 (by omega)
          have hkey : ‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a / (ε * ((n ! : ℝ)) ^ r) ≤ A ^ n :=
            le_trans hterm (le_trans hAbase hAn)
          rw [div_le_iff₀ (by positivity)] at hkey
          calc ‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a
              ≤ A ^ n * (ε * ((n ! : ℝ)) ^ r) := hkey
            _ = ε * A ^ n * ((n ! : ℝ)) ^ r := by ring
      · push Not at hnN
        have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hnN
        have hN₀n : N₀ ≤ n := le_trans (le_max_left N₀ 1) hnN
        have hpowd : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by positivity
        have hpowd1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d := by
          refine one_le_pow₀ ?_
          have := Nat.cast_nonneg (α := ℝ) n
          linarith
        have hΦlow : c * ((n : ℝ) + 1) ^ d ≤ ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ :=
          hlow n hN₀n
        -- the truncated perturbation
        have hH'bound : GevreyWeightBound a ε A r (truncSeries (n - 1) H) :=
          gevreyWeightBound_truncSeries hApos hε0 (fun k hk => ih k (by omega))
        have hH'dvd : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ truncSeries (n - 1) H :=
          X_pow_dvd_truncSeries hHdvd0
        have hdiff : (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (H - truncSeries (n - 1) H) := by
          have h := X_pow_dvd_sub_truncSeries (n - 1) H
          rwa [show (n - 1) + 1 = n by omega] at h
        have hloc : PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)
            = PowerSeries.coeff n
                (taylorDefect (eulerJetVector Y) (eulerJetVector (truncSeries (n - 1) H)) P) :=
          coeff_taylorDefect_eq_of_sub_dvd P Y H (truncSeries (n - 1) H) (by omega)
            hHdvd0 hH'dvd hdiff
        -- the defect estimate
        have hjets : ∀ j : Fin (m + 1),
            GevreyWeightBound 2 ε A r (eulerJetVector (m := m) (truncSeries (n - 1) H) j) := by
          intro j
          have hjm : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
          have hsplit : (a - (j : ℕ)) + (j : ℕ) = a := by omega
          have h1 : GevreyWeightBound (a - (j : ℕ)) ε A r
              (GaloisForLFunctions.HTGeometry.eulerOp^[(j : ℕ)] (truncSeries (n - 1) H)) := by
            refine GevreyWeightBound.eulerOp_iterate ?_
            rw [hsplit]
            exact hH'bound
          exact h1.mono_weight (by omega)
        have hjetsdvd : ∀ j : Fin (m + 1), (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣
            eulerJetVector (m := m) (truncSeries (n - 1) H) j :=
          fun j => X_pow_dvd_eulerOp_iterate (j : ℕ) hH'dvd
        have hDterm : ∀ α ∈ T.support,
            GevreyWeightBound w
              ((2 : ℝ) ^ (w + 2) * Cw * ((2 : ℝ) ^ (2 + 2)) ^ (jetDegree α)
                * (((N + 1)! : ℝ)) ^ r * 2 ^ ((N + 1) * r) * ε ^ 2) A r
              (W α * jetMonomial (eulerJetVector (m := m) (truncSeries (n - 1) H)) α) := by
          intro α hα
          have hmono := gevreyWeightBound_jetMonomial_dvd (a := 2) (M := N + 1) (r := r)
            le_rfl hApos hε0 hε1 (eulerJetVector (m := m) (truncSeries (n - 1) H))
            hjetsdvd hjets α (hTs α hα)
          have hWbound : GevreyWeightBound w Cw A r (W α) :=
            (((hWb α hα).mono_order (Nat.zero_le r) (le_of_lt hCw) hAw).mono_base hAw hAAw
              (le_of_lt hCw))
          have hprod := GevreyWeightBound.mul hw2 hApos (le_of_lt hCw)
            (by positivity) hWbound hmono
          refine hprod.mono_const (le_of_eq ?_) hApos
          ring
        have hDsum : taylorDefect (eulerJetVector Y)
              (eulerJetVector (truncSeries (n - 1) H)) P
            = ∑ α ∈ T.support,
                W α * jetMonomial (eulerJetVector (m := m) (truncSeries (n - 1) H)) α := by
          rw [hTsum (eulerJetVector Y) (eulerJetVector (truncSeries (n - 1) H))]
          rfl
        have hDbound : GevreyWeightBound w
            (∑ α ∈ T.support,
              (2 : ℝ) ^ (w + 2) * Cw * ((2 : ℝ) ^ (2 + 2)) ^ (jetDegree α)
                * (((N + 1)! : ℝ)) ^ r * 2 ^ ((N + 1) * r) * ε ^ 2) A r
            (taylorDefect (eulerJetVector Y)
              (eulerJetVector (truncSeries (n - 1) H)) P) := by
          rw [hDsum]
          exact GevreyWeightBound.finsetSum _ _ _ hDterm
        have hDconst : (∑ α ∈ T.support,
              (2 : ℝ) ^ (w + 2) * Cw * ((2 : ℝ) ^ (2 + 2)) ^ (jetDegree α)
                * (((N + 1)! : ℝ)) ^ r * 2 ^ ((N + 1) * r) * ε ^ 2) = K * ε ^ 2 := by
          rw [hKdef, Finset.sum_mul]
        have hDest : ‖PowerSeries.coeff n
              (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖ * ((n : ℝ) + 1) ^ a
            ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          rw [hloc]
          have hbw := (hDbound.mono_weight haw) n
          rw [hDconst] at hbw
          have hstep : K * ε ^ 2 * A ^ n * ((n ! : ℝ)) ^ r
              ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
            have h1 : K * ε ^ 2 ≤ (c / 3) * ε := by nlinarith [hεK, hε0]
            have h2 : (c / 3) * ε * A ^ n * ((n ! : ℝ)) ^ r
                ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
              have hbase : (0 : ℝ) ≤ c / 3 * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by positivity
              nlinarith [hpowd1, hbase]
            have h3 : K * ε ^ 2 * (A ^ n * ((n ! : ℝ)) ^ r)
                ≤ (c / 3) * ε * (A ^ n * ((n ! : ℝ)) ^ r) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
            calc K * ε ^ 2 * A ^ n * ((n ! : ℝ)) ^ r
                = K * ε ^ 2 * (A ^ n * ((n ! : ℝ)) ^ r) := by ring
              _ ≤ (c / 3) * ε * (A ^ n * ((n ! : ℝ)) ^ r) := h3
              _ = (c / 3) * ε * A ^ n * ((n ! : ℝ)) ^ r := by ring
              _ ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := h2
          linarith [hbw, hstep]
        -- the value at the truncation
        have hVest : ‖PowerSeries.coeff n V‖ * ((n : ℝ) + 1) ^ a
            ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          have hb := hVb n
          simp only [pow_zero, mul_one] at hb
          have hAvA : Av / A ≤ 1 := by
            rw [div_le_one hApos]; exact hAAv
          have hAvA0 : (0 : ℝ) ≤ Av / A := by positivity
          have hpow : (Av / A) ^ n ≤ (Av / A) ^ 1 := pow_le_pow_of_le_one hAvA0 hAvA hn1
          have hrewrite : Av ^ n = (Av / A) ^ n * A ^ n := by
            rw [div_pow]
            field_simp
          have hchain : Cv * Av ^ n ≤ c / 3 * ε * A ^ n := by
            rw [hrewrite]
            have h1 : Cv * ((Av / A) ^ n * A ^ n) ≤ Cv * ((Av / A) * A ^ n) := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCv)
              refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hApown)
              simpa using hpow
            have h2 : Cv * (Av / A) ≤ c / 3 * ε := by
              have hAc : (3 * Cv * Av / (c * ε)) * (c * ε) ≤ A * (c * ε) :=
                mul_le_mul_of_nonneg_right hAval (by positivity)
              have hexp : (3 * Cv * Av / (c * ε)) * (c * ε) = 3 * Cv * Av := by field_simp
              rw [hexp] at hAc
              rw [← mul_div_assoc, div_le_iff₀ hApos]
              nlinarith [hAc]
            calc Cv * ((Av / A) ^ n * A ^ n) ≤ Cv * ((Av / A) * A ^ n) := h1
              _ = (Cv * (Av / A)) * A ^ n := by ring
              _ ≤ (c / 3 * ε) * A ^ n := mul_le_mul_of_nonneg_right h2 (le_of_lt hApown)
              _ = c / 3 * ε * A ^ n := by ring
          have hlast : c / 3 * ε * A ^ n
              ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
            have hbase : (0 : ℝ) ≤ c / 3 * ε * A ^ n := by positivity
            have hprod : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d * ((n ! : ℝ)) ^ r := by
              nlinarith [hpowd1, hfac1]
            calc c / 3 * ε * A ^ n = (c / 3 * ε * A ^ n) * 1 := by ring
              _ ≤ (c / 3 * ε * A ^ n) * (((n : ℝ) + 1) ^ d * ((n ! : ℝ)) ^ r) :=
                  mul_le_mul_of_nonneg_left hprod hbase
              _ = c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by ring
          linarith [hb, hchain, hlast]
        -- the convolution
        have hconv : (∑ k ∈ Finset.range n,
              ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖)
              * ((n : ℝ) + 1) ^ a
            ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          have hstep : ∀ k ∈ Finset.range n,
              ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                  * ((n : ℝ) + 1) ^ a
                ≤ (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                  * ((((n - k : ℕ) : ℝ) + 1) ^ a * q ^ (n - k)) := by
            intro k hk
            have hkn : k < n := Finset.mem_range.mp hk
            have hμ : (n - k) + k = n := by omega
            have hμR : (((n - k : ℕ) : ℝ)) + (k : ℝ) = (n : ℝ) := by
              have : ((((n - k) + k : ℕ)) : ℝ) = (n : ℝ) := by exact_mod_cast hμ
              push_cast at this
              linarith
            have hsplitn : ((n : ℝ) + 1) ≤ ((((n - k : ℕ) : ℝ)) + 1) * (((k : ℝ)) + 1) := by
              have hnn : (0 : ℝ) ≤ (((n - k : ℕ) : ℝ)) * (k : ℝ) := by positivity
              nlinarith [hμR, hnn]
            have hpowsplit : ((n : ℝ) + 1) ^ a
                ≤ ((((n - k : ℕ) : ℝ)) + 1) ^ a * (((k : ℝ)) + 1) ^ a := by
              calc ((n : ℝ) + 1) ^ a
                  ≤ (((((n - k : ℕ) : ℝ)) + 1) * (((k : ℝ)) + 1)) ^ a :=
                    pow_le_pow_left₀ (by positivity) hsplitn a
                _ = ((((n - k : ℕ) : ℝ)) + 1) ^ a * (((k : ℝ)) + 1) ^ a := by rw [mul_pow]
            have h1 : ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖
                ≤ Cb * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m := hshift (n - k) k
            have h2 : ‖PowerSeries.coeff k H‖ * (((k : ℝ)) + 1) ^ a ≤ ε * A ^ k * ((k ! : ℝ)) ^ r :=
              ih k hkn
            have hfactor : (((k : ℝ)) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r)
                ≤ ((n : ℝ) + 1) ^ d := shiftFactor_nat_le hmdr hkn
            have hApow : A ^ n = A ^ (n - k) * A ^ k := by
              rw [← pow_add, hμ]
            have hqpow : q ^ (n - k) = ρ ^ (n - k) / A ^ (n - k) := by
              rw [hqdef, div_pow]
            have hmid : ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖
                  * (‖PowerSeries.coeff k H‖ * (((k : ℝ)) + 1) ^ a)
                ≤ (Cb * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m) * (ε * A ^ k * ((k ! : ℝ)) ^ r) := by
              refine mul_le_mul h1 h2 (by positivity) (by positivity)
            have hfinal : (Cb * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m) * (ε * A ^ k * ((k ! : ℝ)) ^ r)
                ≤ (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by
              have hid : (Cb * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m) * (ε * A ^ k * ((k ! : ℝ)) ^ r)
                  = (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r)) * (q ^ (n - k)
                      * ((((k : ℝ)) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r))) := by
                rw [hqpow, hApow]
                field_simp
              rw [hid]
              have hleft0 : (0 : ℝ) ≤ Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by positivity
              have hqk0 : (0 : ℝ) ≤ q ^ (n - k) := pow_nonneg hq0 _
              calc (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r)) * (q ^ (n - k)
                    * ((((k : ℝ)) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r)))
                  ≤ (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r)) * (q ^ (n - k) * ((n : ℝ) + 1) ^ d) := by
                    refine mul_le_mul_of_nonneg_left ?_ hleft0
                    exact mul_le_mul_of_nonneg_left hfactor hqk0
                _ = (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by
                    ring
            have hnn0 : (0 : ℝ) ≤ ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖
                * ‖PowerSeries.coeff k H‖ := by positivity
            calc ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                  * ((n : ℝ) + 1) ^ a
                ≤ ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                    * (((((n - k : ℕ) : ℝ)) + 1) ^ a * (((k : ℝ)) + 1) ^ a) :=
                  mul_le_mul_of_nonneg_left hpowsplit hnn0
              _ = (((((n - k : ℕ) : ℝ)) + 1) ^ a)
                    * (‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖
                      * (‖PowerSeries.coeff k H‖ * (((k : ℝ)) + 1) ^ a)) := by ring
              _ ≤ (((((n - k : ℕ) : ℝ)) + 1) ^ a)
                    * ((Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k)) := by
                  refine mul_le_mul_of_nonneg_left (le_trans hmid hfinal) (by positivity)
              _ = (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                    * (((((n - k : ℕ) : ℝ)) + 1) ^ a * q ^ (n - k)) := by ring
          have hbig0 : (0 : ℝ) ≤ Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d := by
            positivity
          calc (∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖)
                * ((n : ℝ) + 1) ^ a
              = ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                    * ((n : ℝ) + 1) ^ a := by rw [Finset.sum_mul]
            _ ≤ ∑ k ∈ Finset.range n,
                  (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                    * ((((n - k : ℕ) : ℝ) + 1) ^ a * q ^ (n - k)) := Finset.sum_le_sum hstep
            _ = (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                  * ∑ k ∈ Finset.range n, (((n - k : ℕ) : ℝ) + 1) ^ a * q ^ (n - k) := by
                rw [Finset.mul_sum]
            _ ≤ (Cb * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                  * (Ca * ((2 * q) / (1 - 2 * q))) :=
                mul_le_mul_of_nonneg_left
                  (polyGeom_shift_sum_le hCa (by linarith [hCa1]) hq0 hq21 n) hbig0
            _ = (Cb * (Ca * ((2 * q) / (1 - 2 * q))))
                  * (((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)) := by ring
            _ ≤ (c / 3) * (((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)) :=
                mul_le_mul_of_nonneg_right hqgeom (by positivity)
            _ = c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by ring
        -- assembling the recursion
        have hrec := shiftPolynomial_zero_mul_coeff B H n
        rw [hLH0] at hrec
        have hnormrec : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n H‖
            ≤ ‖PowerSeries.coeff n V‖
              + ‖PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
              + ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖ := by
          have hleft : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n H‖
              = ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n H‖ := norm_mul _ _
          have hA' : ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n H‖
              ≤ ‖PowerSeries.coeff n
                    (-V - taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
                + ‖∑ k ∈ Finset.range n,
                    (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k H‖ := by
            rw [hrec]
            exact norm_sub_le _ _
          have hB' : ‖∑ k ∈ Finset.range n,
                (shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k H‖
              ≤ ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖ := by
            refine le_trans (norm_sum_le _ _) ?_
            exact le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _)
          have hC' : ‖PowerSeries.coeff n
                (-V - taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
              ≤ ‖PowerSeries.coeff n V‖
                + ‖PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖ := by
            rw [map_sub, map_neg]
            refine le_trans (norm_sub_le _ _) ?_
            rw [norm_neg]
          rw [hleft] at hA'
          linarith
        have hmid : c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n H‖
            ≤ ‖(shiftPolynomial B 0).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n H‖ :=
          mul_le_mul_of_nonneg_right hΦlow (norm_nonneg _)
        have htotal : (‖PowerSeries.coeff n V‖
              + ‖PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
              + ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖)
              * ((n : ℝ) + 1) ^ a
            ≤ c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          have hexp : (‖PowerSeries.coeff n V‖
                + ‖PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
                + ∑ k ∈ Finset.range n,
                    ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖)
                * ((n : ℝ) + 1) ^ a
              = ‖PowerSeries.coeff n V‖ * ((n : ℝ) + 1) ^ a
                + ‖PowerSeries.coeff n
                    (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖ * ((n : ℝ) + 1) ^ a
                + (∑ k ∈ Finset.range n,
                    ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖)
                  * ((n : ℝ) + 1) ^ a := by ring
          rw [hexp]
          have hsum3 : c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)
              + c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)
              + c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)
              = c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by ring
          linarith [hVest, hDest, hconv, hsum3]
        have hfinal : c * ((n : ℝ) + 1) ^ d * (‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a)
            ≤ c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          have hmul := mul_le_mul_of_nonneg_right (le_trans hmid hnormrec)
            (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ a)
          calc c * ((n : ℝ) + 1) ^ d * (‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a)
              = (c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n H‖) * ((n : ℝ) + 1) ^ a := by ring
            _ ≤ (‖PowerSeries.coeff n V‖
                  + ‖PowerSeries.coeff n (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
                  + ∑ k ∈ Finset.range n,
                      ‖(shiftPolynomial B (n - k)).eval ((k : ℕ) : ℂ)‖
                        * ‖PowerSeries.coeff k H‖) * ((n : ℝ) + 1) ^ a := hmul
            _ ≤ c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := htotal
        exact le_of_mul_le_mul_left hfinal (by positivity)
  -- from the perturbation back to the solution
  have hHgev : IsGevreySeries ((r : ℕ) : ℝ) H := hmain.isGevreySeries hεpos hApos
  have hYgev : IsGevreySeries ((r : ℕ) : ℝ) Y := hYconv0.mono (by positivity)
  rw [← hYH0]
  exact hYgev.add hHgev

end GaloisForLFunctions.HTGeometry
