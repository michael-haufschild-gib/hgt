import GaloisForLFunctions.HTGeometry.NonlinearMailletAux

/-!
# Maillet's theorem for a nonlinear equation with a degenerate indicial polynomial

The indicial polynomial of the linearization of an algebraic differential equation along a
truncation of a formal solution may vanish; what cannot vanish, once the linearization itself is
nonzero, is the shift polynomial at the order `v` to which the linearization vanishes.  The
recursion is then

```text
Φ_v(n) h_n = coeff_{n+v}(−P(jets Y) − defect) − ∑_{k<n} Φ_{n+v−k}(k) h_k ,
```

which is the same recursion read one level higher.  Three costs appear and are each paid.

* The convolution weights become `Φ_{n+v−k}`, whose size gains the fixed factor `ρ^v`.
* The value at the truncation is read at level `n+v`, and is therefore compared against `A^n`
  rather than `A^{n+v}`; the loss `A^v` is repaid by the order `N+1−v` to which that value
  vanishes, which is where `N + 1 > 2v` is used.
* The defect is read at level `n+v` as well; its factorial loses `((n+v)!/n!)^r ≤ ((v+1)(n+1))^{vr}`
  and its weight has exactly that much slack, because the truncation order supplies `(N+1)r` units
  of weight and only `m + v r` are consumed.

Because the induction size `ε` must now absorb the factor `A^v`, it is defined **after** the
geometric base `A`, as `ε = c / (3 (K+1)(c+1) A^v)`; every constraint on `A` is then free of `ε`.
-/

open PowerSeries MvPolynomial
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### A factorial shifted by a bounded amount -/

theorem factorial_add_le (v : ℕ) : ∀ n : ℕ, (n + v)! ≤ n ! * ((v + 1) * (n + 1)) ^ v := by
  induction v with
  | zero => intro n; simp
  | succ v ih =>
      intro n
      have hprev := ih n
      have hstep : (n + (v + 1))! = (n + v + 1) * (n + v)! := by
        rw [show n + (v + 1) = (n + v) + 1 by omega, Nat.factorial_succ]
      rw [hstep]
      have hbase : (v + 1 + 1) * (n + 1) ≥ n + v + 1 := by nlinarith
      have hmono : ((v + 1) * (n + 1)) ^ v ≤ ((v + 1 + 1) * (n + 1)) ^ v :=
        Nat.pow_le_pow_left (by nlinarith) v
      calc (n + v + 1) * (n + v)!
          ≤ (n + v + 1) * (n ! * ((v + 1) * (n + 1)) ^ v) := Nat.mul_le_mul_left _ hprev
        _ ≤ ((v + 1 + 1) * (n + 1)) * (n ! * ((v + 1 + 1) * (n + 1)) ^ v) := by
            refine Nat.mul_le_mul hbase (Nat.mul_le_mul_left _ hmono)
        _ = n ! * ((v + 1 + 1) * (n + 1)) ^ (v + 1) := by ring

theorem factorial_add_rpow_le (v r n : ℕ) :
    (((n + v)! : ℝ)) ^ r
      ≤ ((n ! : ℝ)) ^ r * (((v : ℝ) + 1)) ^ (v * r) * (((n : ℝ) + 1)) ^ (v * r) := by
  have hnat : (((n + v)! : ℕ) : ℝ) ≤ ((n ! : ℕ) : ℝ) * (((v : ℝ) + 1) * ((n : ℝ) + 1)) ^ v := by
    have h := factorial_add_le v n
    have h' : (((n + v)! : ℕ) : ℝ) ≤ (((n ! * ((v + 1) * (n + 1)) ^ v : ℕ)) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    exact h'
  calc (((n + v)! : ℝ)) ^ r
      ≤ (((n ! : ℝ)) * (((v : ℝ) + 1) * ((n : ℝ) + 1)) ^ v) ^ r :=
        pow_le_pow_left₀ (by positivity) hnat r
    _ = ((n ! : ℝ)) ^ r * ((((v : ℝ) + 1) * ((n : ℝ) + 1)) ^ v) ^ r := by rw [mul_pow]
    _ = ((n ! : ℝ)) ^ r * (((v : ℝ) + 1) * ((n : ℝ) + 1)) ^ (v * r) := by rw [← pow_mul]
    _ = ((n ! : ℝ)) ^ r * (((v : ℝ) + 1)) ^ (v * r) * (((n : ℝ) + 1)) ^ (v * r) := by
        rw [mul_pow, mul_assoc]

set_option maxHeartbeats 400000 in
/-- **Maillet's theorem, nonlinear case, at an arbitrary leading shift.**  A formal solution of an
analytic algebraic differential equation whose linearization along the truncation at order `N`
vanishes exactly to order `v`, with `m + 2v ≤ N`, is Gevrey of a finite integral order. -/
theorem exists_isGevreySeries_of_isFormalEulerADESolution_shift {m N v : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : IsAnalyticDifferentialPolynomial P)
    {F : PowerSeries ℂ} (hsol : IsFormalEulerADESolution P F)
    (hNm : m + 2 * v ≤ N)
    (hvlow : ∀ μ, μ < v → shiftPolynomial (linearizationCoeff P (truncPowerSeries N F)) μ = 0)
    (hΦ : shiftPolynomial (linearizationCoeff P (truncPowerSeries N F)) v ≠ 0) :
    ∃ r : ℕ, IsGevreySeries (r : ℝ) F := by
  classical
  -- the linearization along the truncation
  have hHdvd0 : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ (F - truncPowerSeries N F) :=
    X_pow_dvd_sub_truncPowerSeries N F
  have hYH0 : truncPowerSeries N F + (F - truncPowerSeries N F) = F := by ring
  have hsol'0 : IsFormalEulerADESolution P (truncPowerSeries N F + (F - truncPowerSeries N F)) := by
    rw [hYH0]; exact hsol
  have hBconv0 : ∀ j, IsGevreySeries 0 (linearizationCoeff P (truncPowerSeries N F) j) := fun j =>
    isGevreySeries_zero_linearizationCoeff P hP F j
  have hVconv0 : IsGevreySeries 0 (MvPolynomial.aeval (eulerJetVector (truncPowerSeries N F)) P) :=
    isGevreySeries_zero_aeval_truncPowerSeries P hP F
  have hVdvd0 : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣
      MvPolynomial.aeval (eulerJetVector (truncPowerSeries N F)) P :=
    X_pow_dvd_aeval_truncPowerSeries P hsol
  have hYconv0 : IsGevreySeries 0 (truncPowerSeries N F) := isGevreySeries_zero_truncPowerSeries N F
  have hLH0 : eulerLinearOp (linearizationCoeff P (truncPowerSeries N F)) (F - truncPowerSeries N F)
      = -(MvPolynomial.aeval (eulerJetVector (truncPowerSeries N F)) P)
        - taylorDefect (eulerJetVector (truncPowerSeries N F))
            (eulerJetVector (F - truncPowerSeries N F)) P :=
    eulerLinearOp_linearization_eq P (truncPowerSeries N F) (F - truncPowerSeries N F) hsol'0
  obtain ⟨T, hTs, hTc, hTsum⟩ :=
    hasTaylorDefectFamily (A := PowerSeries ℂ) convergentSubsemiring P hP
  set Y : PowerSeries ℂ := truncPowerSeries N F with hYdef
  set H : PowerSeries ℂ := F - Y with hHdef
  set B : Fin (m + 1) → PowerSeries ℂ := linearizationCoeff P Y with hBdef
  set V : PowerSeries ℂ := MvPolynomial.aeval (eulerJetVector Y) P with hVdef
  set d : ℕ := (shiftPolynomial B v).natDegree with hddef
  set r : ℕ := max (m - d) 1 with hrdef
  set a : ℕ := m + 2 with hadef
  set w : ℕ := 2 + (N + 1) * r with hwdef
  refine ⟨r, ?_⟩
  -- arithmetic of the exponents
  have hr1 : 1 ≤ r := le_max_right _ _
  have hmdr : m ≤ d + r := by
    have h1 : m - d ≤ r := le_max_left _ _
    omega
  have hvN : v ≤ N := by omega
  have hw2 : 2 ≤ w := by omega
  have hawv : a + v * r ≤ w := by
    have h1 : (m + v) * 1 ≤ (m + v) * r := Nat.mul_le_mul_left _ hr1
    have h2 : (m + v) * r ≤ (N + 1) * r := Nat.mul_le_mul_right _ (by omega)
    have h3 : v * r + m * r = (m + v) * r := by ring
    have h4 : m ≤ m * r := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have haw : a ≤ w := by omega
  -- the coefficients of the Taylor family, evaluated at the truncation
  set W : (Fin (m + 1) →₀ ℕ) → PowerSeries ℂ :=
    fun α => MvPolynomial.aeval (eulerJetVector Y) (T α) with hWdef
  have hWconv : ∀ α, IsGevreySeries ((0 : ℕ) : ℝ) (W α) := by
    intro α
    have h := isGevreySeries_aeval_eulerJetVector (r := 0) le_rfl (T α) (fun σ => hTc α σ) hYconv0
    rw [Nat.cast_zero]
    exact h
  -- the constants of the recursion
  obtain ⟨c, hc, N₀, hlow⟩ := exists_lower_bound_eval_natCast (shiftPolynomial B v) hΦ
  obtain ⟨Cb, ρ, hCb, hρ, hshift⟩ := exists_bound_shiftPolynomial B hBconv0
  obtain ⟨Ca, hCa1, hCa⟩ := exists_succ_pow_le_const_mul_pow a (by norm_num : (1 : ℝ) < 2)
  have hVconv0' : IsGevreySeries ((0 : ℕ) : ℝ) V := by simpa using hVconv0
  obtain ⟨Cv, Av, hCv, hAv, hVb⟩ := exists_gevreyWeightBound hVconv0' a
  obtain ⟨Cw, Aw, hCw, hAw, hWb⟩ :=
    exists_common_gevreyWeightBound W w 0 T.support (fun α _ => hWconv α)
  set N₁ : ℕ := max N₀ 1 with hN₁def
  set Cb' : ℝ := Cb * ρ ^ v with hCb'def
  have hCb' : 0 < Cb' := by rw [hCb'def]; positivity
  -- each constant is fixed by the estimates already proved about it; keeping the defining
  -- bodies out of the context is what keeps the recursion below tractable
  clear_value Cb'
  set K₀ : ℝ := ∑ α ∈ T.support,
      (2 : ℝ) ^ (w + 2) * Cw * ((2 : ℝ) ^ (2 + 2)) ^ (jetDegree α)
        * (((N + 1)! : ℝ)) ^ r * 2 ^ ((N + 1) * r) with hK₀def
  have hK₀0 : (0 : ℝ) ≤ K₀ := Finset.sum_nonneg fun α _ => by positivity
  clear_value K₀
  set K : ℝ := K₀ * (((v : ℝ) + 1)) ^ (v * r) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  clear_value K
  set S : ℝ := ∑ k ∈ Finset.range N₁,
      ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a / ((k ! : ℝ)) ^ r with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun k _ => by positivity
  clear_value S
  -- the geometric base, chosen free of the induction size
  set A : ℝ := 1 + Aw + Av + 4 * ρ + 12 * Cb' * Ca * ρ / c
      + 9 * (K + 1) * (c + 1) * Cv * Av ^ (N + 1) / c ^ 2
      + 3 * (K + 1) * (c + 1) * S / c with hAdef
  have hp1 : (0 : ℝ) < 12 * Cb' * Ca * ρ / c := by positivity
  have hp2 : (0 : ℝ) < 9 * (K + 1) * (c + 1) * Cv * Av ^ (N + 1) / c ^ 2 := by positivity
  have hp3 : (0 : ℝ) ≤ 3 * (K + 1) * (c + 1) * S / c := by positivity
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hA1 : (1 : ℝ) ≤ A := by
    rw [hAdef]
    linarith only [le_of_lt hAw, le_of_lt hAv, le_of_lt hρ, le_of_lt hp1, le_of_lt hp2, hp3]
  have hAAw : Aw ≤ A := by
    rw [hAdef]
    linarith only [le_of_lt hAv, le_of_lt hρ, le_of_lt hp1, le_of_lt hp2, hp3]
  have hAAv : Av ≤ A := by
    rw [hAdef]
    linarith only [le_of_lt hAw, le_of_lt hρ, le_of_lt hp1, le_of_lt hp2, hp3]
  have hA4ρ : 4 * ρ ≤ A := by
    rw [hAdef]
    linarith only [le_of_lt hAw, le_of_lt hAv, le_of_lt hp1, le_of_lt hp2, hp3]
  have hAgeom : 12 * Cb' * Ca * ρ / c ≤ A := by
    rw [hAdef]
    linarith only [le_of_lt hAw, le_of_lt hAv, le_of_lt hρ, le_of_lt hp2, hp3]
  have hAval : 9 * (K + 1) * (c + 1) * Cv * Av ^ (N + 1) / c ^ 2 ≤ A := by
    rw [hAdef]
    linarith only [le_of_lt hAw, le_of_lt hAv, le_of_lt hρ, le_of_lt hp1, hp3]
  have hAbase : 3 * (K + 1) * (c + 1) * S / c ≤ A := by
    rw [hAdef]
    linarith only [le_of_lt hAw, le_of_lt hAv, le_of_lt hρ, le_of_lt hp1, le_of_lt hp2]
  clear_value A
  have hApowpos : ∀ k : ℕ, (0 : ℝ) < A ^ k := fun k => pow_pos hApos k
  have hApow1 : ∀ k : ℕ, (1 : ℝ) ≤ A ^ k := fun k => one_le_pow₀ hA1
  -- the induction size
  set ε : ℝ := c / (3 * (K + 1) * (c + 1) * A ^ v) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε0 : (0 : ℝ) ≤ ε := le_of_lt hεpos
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]
    have h1 : (3 : ℝ) * 1 ≤ 3 * (K + 1) := by linarith
    have h2 : (3 : ℝ) * 1 * (c + 1) ≤ 3 * (K + 1) * (c + 1) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h3 : (3 : ℝ) * 1 * (c + 1) * 1 ≤ 3 * (K + 1) * (c + 1) * A ^ v :=
      mul_le_mul h2 (hApow1 v) (by norm_num) (by positivity)
    linarith
  have hεK : K * ε * A ^ v ≤ c / 3 := by
    have hid : K * ε * A ^ v = K * c / (3 * (K + 1) * (c + 1)) := by
      rw [hεdef]
      field_simp
    rw [hid, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
    nlinarith only [hK0, le_of_lt hc, mul_nonneg hK0 (le_of_lt hc)]
  -- the base-case bound
  have hSA : S ≤ ε * A ^ (N + 1) := by
    have hsplit : A ^ (N + 1) = A ^ v * A ^ (N + 1 - v) := by
      rw [← pow_add]
      congr 1
      omega
    have hid : ε * A ^ (N + 1) = c * A ^ (N + 1 - v) / (3 * (K + 1) * (c + 1)) := by
      rw [hεdef, hsplit]
      field_simp
    rw [hid, le_div_iff₀ (by positivity)]
    have hAle : A ≤ A ^ (N + 1 - v) := le_self_pow₀ hA1 (by omega)
    have h1 : 3 * (K + 1) * (c + 1) * S / c * c ≤ A * c :=
      mul_le_mul_of_nonneg_right hAbase (le_of_lt hc)
    have h2 : 3 * (K + 1) * (c + 1) * S / c * c = 3 * (K + 1) * (c + 1) * S := by field_simp
    rw [h2] at h1
    nlinarith only [h1, hAle, le_of_lt hc]
  -- the value estimate
  have hVA : ∀ n : ℕ, N + 1 ≤ n + v →
      Cv * Av ^ (n + v) ≤ c / 3 * ε * A ^ n := by
    intro n hn
    have hAvA : Av / A ≤ 1 := by rw [div_le_one hApos]; exact hAAv
    have hAvA0 : (0 : ℝ) ≤ Av / A := by positivity
    have hnge : N + 1 - v ≤ n := by omega
    have hpow : (Av / A) ^ n ≤ (Av / A) ^ (N + 1 - v) :=
      pow_le_pow_of_le_one hAvA0 hAvA hnge
    have hrew : Av ^ (n + v) = Av ^ v * ((Av / A) ^ n * A ^ n) := by
      rw [div_pow, pow_add]
      field_simp
    rw [hrew]
    have hstep : Cv * (Av ^ v * ((Av / A) ^ n * A ^ n))
        ≤ Cv * (Av ^ v * ((Av / A) ^ (N + 1 - v) * A ^ n)) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (le_of_lt (hApowpos n))) (by positivity))
        (le_of_lt hCv)
    refine le_trans hstep ?_
    have hid : Cv * (Av ^ v * ((Av / A) ^ (N + 1 - v) * A ^ n))
        = (Cv * Av ^ v * Av ^ (N + 1 - v) / A ^ (N + 1 - v)) * A ^ n := by
      rw [div_pow]
      field_simp
    rw [hid]
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hApowpos n))
    have hAvsplit : Av ^ v * Av ^ (N + 1 - v) = Av ^ (N + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hgoal : Cv * Av ^ v * Av ^ (N + 1 - v) = Cv * Av ^ (N + 1) := by
      rw [mul_assoc, hAvsplit]
    rw [hgoal, div_le_iff₀ (by positivity)]
    have hid2 : c / 3 * ε = c ^ 2 / (9 * (K + 1) * (c + 1) * A ^ v) := by
      rw [hεdef]
      field_simp
      ring
    rw [hid2]
    have hAsplit : A ^ (N + 1 - v) = A ^ v * A ^ (N + 1 - 2 * v) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hAsplit]
    have hAle : A ≤ A ^ (N + 1 - 2 * v) := le_self_pow₀ hA1 (by omega)
    have h1 : 9 * (K + 1) * (c + 1) * Cv * Av ^ (N + 1) / c ^ 2 * c ^ 2 ≤ A * c ^ 2 :=
      mul_le_mul_of_nonneg_right hAval (by positivity)
    have h2 : 9 * (K + 1) * (c + 1) * Cv * Av ^ (N + 1) / c ^ 2 * c ^ 2
        = 9 * (K + 1) * (c + 1) * Cv * Av ^ (N + 1) := by field_simp
    rw [h2] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hstep1 : 9 * (K + 1) * (c + 1) * Cv * Av ^ (N + 1) * A ^ v ≤ (A * c ^ 2) * A ^ v :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt (hApowpos v))
    have hstep2 : (A * c ^ 2) * A ^ v ≤ (A ^ (N + 1 - 2 * v) * c ^ 2) * A ^ v := by
      refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hApowpos v))
      exact mul_le_mul_of_nonneg_right hAle (by positivity)
    nlinarith only [hstep1, hstep2]
  clear_value ε
  -- the geometric ratio
  set q : ℝ := ρ / A with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; positivity
  have hq2 : 2 * q ≤ 1 / 2 := by
    rw [hqdef, ← mul_div_assoc, div_le_div_iff₀ hApos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hA4ρ]
  have hq21 : 2 * q < 1 := by linarith
  have hqden : (1 : ℝ) / 2 ≤ 1 - 2 * q := by linarith
  have hqgeom : Cb' * (Ca * ((2 * q) / (1 - 2 * q))) ≤ c / 3 := by
    have hstep : (2 * q) / (1 - 2 * q) ≤ 4 * q := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith only [hq0, hqden]
    have hq4 : 4 * q ≤ c / (3 * Cb' * Ca) := by
      have hform : 4 * q = 4 * ρ / A := by rw [hqdef]; ring
      rw [hform, div_le_div_iff₀ hApos (by positivity)]
      have hAc : (12 * Cb' * Ca * ρ / c) * c ≤ A * c :=
        mul_le_mul_of_nonneg_right hAgeom (le_of_lt hc)
      have hexp : (12 * Cb' * Ca * ρ / c) * c = 12 * Cb' * Ca * ρ := by field_simp
      rw [hexp] at hAc
      nlinarith only [hAc]
    calc Cb' * (Ca * ((2 * q) / (1 - 2 * q))) ≤ Cb' * (Ca * (4 * q)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep ?_) (le_of_lt hCb')
          linarith only [hCa1]
      _ ≤ Cb' * (Ca * (c / (3 * Cb' * Ca))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq4 ?_) (le_of_lt hCb')
          linarith only [hCa1]
      _ = c / 3 := by field_simp
  clear_value q
  -- the main induction
  have hmain : GevreyWeightBound a ε A r H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hfacpos : (0 : ℝ) < ((n ! : ℝ)) ^ r := by positivity
      have hfac1 : (1 : ℝ) ≤ ((n ! : ℝ)) ^ r := one_le_pow₀ (one_le_factorial_cast n)
      by_cases hnN : n < N₁
      · by_cases hnv : n ≤ N
        · have h0 : PowerSeries.coeff n H = 0 :=
            (PowerSeries.X_pow_dvd_iff.mp hHdvd0) n (by omega)
          rw [h0, norm_zero, zero_mul]
          positivity
        · push Not at hnv
          have hmem : n ∈ Finset.range N₁ := Finset.mem_range.mpr hnN
          have hterm : ‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a / ((n ! : ℝ)) ^ r ≤ S := by
            rw [hSdef]
            exact Finset.single_le_sum
              (f := fun k : ℕ => ‖PowerSeries.coeff k H‖ * ((k : ℝ) + 1) ^ a / ((k ! : ℝ)) ^ r)
              (fun k _ => by positivity) hmem
          have hAn : A ^ (N + 1) ≤ A ^ n := pow_le_pow_right₀ hA1 (by omega)
          have hkey : ‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a / ((n ! : ℝ)) ^ r ≤ ε * A ^ n := by
            refine le_trans hterm (le_trans hSA ?_)
            exact mul_le_mul_of_nonneg_left hAn hε0
          rw [div_le_iff₀ (by positivity)] at hkey
          exact hkey
      · push Not at hnN
        have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hnN
        have hN₀n : N₀ ≤ n := le_trans (le_max_left N₀ 1) hnN
        have hpowd : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by positivity
        have hpowd1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d := by
          refine one_le_pow₀ ?_
          have := Nat.cast_nonneg (α := ℝ) n
          linarith
        have hΦlow : c * ((n : ℝ) + 1) ^ d ≤ ‖(shiftPolynomial B v).eval ((n : ℕ) : ℂ)‖ :=
          hlow n hN₀n
        -- the truncated perturbation
        have hH'bound : GevreyWeightBound a ε A r (truncPowerSeries (n - 1) H) :=
          gevreyWeightBound_truncPowerSeries hApos hε0 (fun k hk => ih k (by omega))
        have hH'dvd : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ truncPowerSeries (n - 1) H :=
          X_pow_dvd_truncPowerSeries hHdvd0
        have hdiff : (PowerSeries.X : PowerSeries ℂ) ^ n ∣ (H - truncPowerSeries (n - 1) H) := by
          have h := X_pow_dvd_sub_truncPowerSeries (n - 1) H
          rwa [show (n - 1) + 1 = n by omega] at h
        have hloc : PowerSeries.coeff (n + v)
              (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)
            = PowerSeries.coeff (n + v)
                (taylorDefect (eulerJetVector Y) (eulerJetVector (truncPowerSeries (n - 1) H)) P) := by
          exact coeff_taylorDefect_eq_of_sub_dvd (n := n) (M := N + 1) (j := n + v)
            P Y H (truncPowerSeries (n - 1) H) (by omega) hHdvd0 hH'dvd hdiff
        -- the defect estimate
        have hjets : ∀ j : Fin (m + 1),
            GevreyWeightBound 2 ε A r (eulerJetVector (m := m) (truncPowerSeries (n - 1) H) j) := by
          intro j
          have hjm : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
          have hsplit : (a - (j : ℕ)) + (j : ℕ) = a := by omega
          have h1 : GevreyWeightBound (a - (j : ℕ)) ε A r
              (GaloisForLFunctions.HTGeometry.formalEulerOp^[(j : ℕ)] (truncPowerSeries (n - 1) H)) := by
            refine GevreyWeightBound.formalEulerOp_iterate ?_
            rw [hsplit]
            exact hH'bound
          exact h1.mono_weight (by omega)
        have hjetsdvd : ∀ j : Fin (m + 1), (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣
            eulerJetVector (m := m) (truncPowerSeries (n - 1) H) j :=
          fun j => X_pow_dvd_formalEulerOp_iterate (j : ℕ) hH'dvd
        have hDterm : ∀ α ∈ T.support,
            GevreyWeightBound w
              ((2 : ℝ) ^ (w + 2) * Cw * ((2 : ℝ) ^ (2 + 2)) ^ (jetDegree α)
                * (((N + 1)! : ℝ)) ^ r * 2 ^ ((N + 1) * r) * ε ^ 2) A r
              (W α * jetMonomialValue (eulerJetVector (m := m) (truncPowerSeries (n - 1) H)) α) := by
          intro α hα
          have hmono := gevreyWeightBound_jetMonomialValue_dvd (a := 2) (M := N + 1) (r := r)
            le_rfl hApos hε0 hε1 (eulerJetVector (m := m) (truncPowerSeries (n - 1) H))
            hjetsdvd hjets α (hTs α hα)
          have hWbound : GevreyWeightBound w Cw A r (W α) :=
            (((hWb α hα).mono_order (Nat.zero_le r) (le_of_lt hCw) hAw).mono_base hAw hAAw
              (le_of_lt hCw))
          have hprod := GevreyWeightBound.mul hw2 hApos (le_of_lt hCw)
            (by positivity) hWbound hmono
          refine hprod.mono_const (le_of_eq ?_) hApos
          ring
        have hDsum : taylorDefect (eulerJetVector Y)
              (eulerJetVector (truncPowerSeries (n - 1) H)) P
            = ∑ α ∈ T.support,
                W α * jetMonomialValue (eulerJetVector (m := m) (truncPowerSeries (n - 1) H)) α := by
          rw [hTsum (eulerJetVector Y) (eulerJetVector (truncPowerSeries (n - 1) H))]
          rfl
        have hDbound : GevreyWeightBound w (K₀ * ε ^ 2) A r
            (taylorDefect (eulerJetVector Y)
              (eulerJetVector (truncPowerSeries (n - 1) H)) P) := by
          rw [hDsum]
          have h := GevreyWeightBound.finsetSum (w := w) (r := r) (A := A) T.support
            (fun α => W α * jetMonomialValue (eulerJetVector (m := m) (truncPowerSeries (n - 1) H)) α)
            (fun α => (2 : ℝ) ^ (w + 2) * Cw * ((2 : ℝ) ^ (2 + 2)) ^ (jetDegree α)
                * (((N + 1)! : ℝ)) ^ r * 2 ^ ((N + 1) * r) * ε ^ 2) hDterm
          refine h.mono_const (le_of_eq ?_) hApos
          rw [hK₀def, Finset.sum_mul]
        have hDest : ‖PowerSeries.coeff (n + v)
              (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖ * ((n : ℝ) + 1) ^ a
            ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          rw [hloc]
          have hnv1 : (1 : ℝ) ≤ (((n + v : ℕ) : ℝ) + 1) := by
            have := Nat.cast_nonneg (α := ℝ) (n + v)
            linarith
          have hle : ((n : ℝ) + 1) ≤ (((n + v : ℕ) : ℝ) + 1) := by
            push_cast
            have := Nat.cast_nonneg (α := ℝ) v
            linarith
          have hpowstep : ((n : ℝ) + 1) ^ a * ((n : ℝ) + 1) ^ (v * r)
              ≤ (((n + v : ℕ) : ℝ) + 1) ^ w := by
            calc ((n : ℝ) + 1) ^ a * ((n : ℝ) + 1) ^ (v * r)
                = ((n : ℝ) + 1) ^ (a + v * r) := (pow_add ((n : ℝ) + 1) a (v * r)).symm
              _ ≤ (((n + v : ℕ) : ℝ) + 1) ^ (a + v * r) :=
                  pow_le_pow_left₀ (by positivity) hle _
              _ ≤ (((n + v : ℕ) : ℝ) + 1) ^ w := pow_le_pow_right₀ hnv1 hawv
          have hstep1 : ‖PowerSeries.coeff (n + v)
                (taylorDefect (eulerJetVector Y)
                  (eulerJetVector (truncPowerSeries (n - 1) H)) P)‖
                * (((n : ℝ) + 1) ^ a * ((n : ℝ) + 1) ^ (v * r))
              ≤ K₀ * ε ^ 2 * A ^ (n + v) * (((n + v)! : ℝ)) ^ r := by
            refine le_trans (mul_le_mul_of_nonneg_left hpowstep (norm_nonneg _)) ?_
            exact hDbound (n + v)
          have hstep2 : K₀ * ε ^ 2 * A ^ (n + v) * (((n + v)! : ℝ)) ^ r
              ≤ (K * ε ^ 2 * A ^ v * (A ^ n * ((n ! : ℝ)) ^ r)) * ((n : ℝ) + 1) ^ (v * r) := by
            have hfac := factorial_add_rpow_le v r n
            have hApowsplit : A ^ (n + v) = A ^ v * A ^ n := by rw [pow_add]; ring
            have hbase : (0 : ℝ) ≤ K₀ * ε ^ 2 * A ^ (n + v) := by positivity
            calc K₀ * ε ^ 2 * A ^ (n + v) * (((n + v)! : ℝ)) ^ r
                ≤ K₀ * ε ^ 2 * A ^ (n + v)
                    * (((n ! : ℝ)) ^ r * (((v : ℝ) + 1)) ^ (v * r) * (((n : ℝ) + 1)) ^ (v * r)) :=
                  mul_le_mul_of_nonneg_left hfac hbase
              _ = (K₀ * (((v : ℝ) + 1)) ^ (v * r) * ε ^ 2 * A ^ v * (A ^ n * ((n ! : ℝ)) ^ r))
                    * ((n : ℝ) + 1) ^ (v * r) := by
                  rw [hApowsplit]
                  ring
              _ = (K * ε ^ 2 * A ^ v * (A ^ n * ((n ! : ℝ)) ^ r)) * ((n : ℝ) + 1) ^ (v * r) := by
                  rw [hKdef]
          have hcancel : ‖PowerSeries.coeff (n + v)
                (taylorDefect (eulerJetVector Y)
                  (eulerJetVector (truncPowerSeries (n - 1) H)) P)‖ * ((n : ℝ) + 1) ^ a
              ≤ K * ε ^ 2 * A ^ v * (A ^ n * ((n ! : ℝ)) ^ r) := by
            refine le_of_mul_le_mul_right ?_
              (show (0 : ℝ) < ((n : ℝ) + 1) ^ (v * r) by positivity)
            calc ‖PowerSeries.coeff (n + v)
                  (taylorDefect (eulerJetVector Y)
                    (eulerJetVector (truncPowerSeries (n - 1) H)) P)‖ * ((n : ℝ) + 1) ^ a
                  * ((n : ℝ) + 1) ^ (v * r)
                = ‖PowerSeries.coeff (n + v)
                    (taylorDefect (eulerJetVector Y)
                      (eulerJetVector (truncPowerSeries (n - 1) H)) P)‖
                    * (((n : ℝ) + 1) ^ a * ((n : ℝ) + 1) ^ (v * r)) := by ring
              _ ≤ K₀ * ε ^ 2 * A ^ (n + v) * (((n + v)! : ℝ)) ^ r := hstep1
              _ ≤ (K * ε ^ 2 * A ^ v * (A ^ n * ((n ! : ℝ)) ^ r))
                    * ((n : ℝ) + 1) ^ (v * r) := hstep2
          refine le_trans hcancel ?_
          have hcoef : K * ε ^ 2 * A ^ v ≤ c / 3 * ε := by
            have h1 : K * ε * A ^ v * ε ≤ (c / 3) * ε := mul_le_mul_of_nonneg_right hεK hε0
            calc K * ε ^ 2 * A ^ v = K * ε * A ^ v * ε := by ring
              _ ≤ (c / 3) * ε := h1
          have hstep3 : K * ε ^ 2 * A ^ v * (A ^ n * ((n ! : ℝ)) ^ r)
              ≤ (c / 3 * ε) * (A ^ n * ((n ! : ℝ)) ^ r) :=
            mul_le_mul_of_nonneg_right hcoef (by positivity)
          refine le_trans hstep3 ?_
          have hbase2 : (0 : ℝ) ≤ c / 3 * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by positivity
          calc (c / 3 * ε) * (A ^ n * ((n ! : ℝ)) ^ r)
              = (c / 3 * (ε * A ^ n * ((n ! : ℝ)) ^ r)) * 1 := by ring
            _ ≤ (c / 3 * (ε * A ^ n * ((n ! : ℝ)) ^ r)) * ((n : ℝ) + 1) ^ d :=
                mul_le_mul_of_nonneg_left hpowd1 hbase2
            _ = c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by ring
        -- the value at the truncation
        have hVest : ‖PowerSeries.coeff (n + v) V‖ * ((n : ℝ) + 1) ^ a
            ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          by_cases hnvN : n + v < N + 1
          · have h0 : PowerSeries.coeff (n + v) V = 0 :=
              (PowerSeries.X_pow_dvd_iff.mp hVdvd0) (n + v) hnvN
            rw [h0, norm_zero, zero_mul]
            positivity
          · push Not at hnvN
            have hb := hVb (n + v)
            simp only [pow_zero, mul_one] at hb
            have hle : ((n : ℝ) + 1) ≤ (((n + v : ℕ) : ℝ) + 1) := by
              push_cast
              have := Nat.cast_nonneg (α := ℝ) v
              linarith
            have h1 : ‖PowerSeries.coeff (n + v) V‖ * ((n : ℝ) + 1) ^ a
                ≤ Cv * Av ^ (n + v) := by
              refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hb
              exact pow_le_pow_left₀ (by positivity) hle a
            have h2 := hVA n hnvN
            have h3 : c / 3 * ε * A ^ n
                ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
              have hbase : (0 : ℝ) ≤ c / 3 * ε * A ^ n := by positivity
              have hprod : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d * ((n ! : ℝ)) ^ r := by
                nlinarith only [hpowd1, hfac1]
              calc c / 3 * ε * A ^ n = (c / 3 * ε * A ^ n) * 1 := by ring
                _ ≤ (c / 3 * ε * A ^ n) * (((n : ℝ) + 1) ^ d * ((n ! : ℝ)) ^ r) :=
                    mul_le_mul_of_nonneg_left hprod hbase
                _ = c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by ring
            linarith only [h1, h2, h3]
        -- the convolution
        have hconv : (∑ k ∈ Finset.range n,
              ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖)
              * ((n : ℝ) + 1) ^ a
            ≤ c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          have hstep : ∀ k ∈ Finset.range n,
              ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                  * ((n : ℝ) + 1) ^ a
                ≤ (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                  * ((((n - k : ℕ) : ℝ) + 1) ^ a * q ^ (n - k)) := by
            intro k hk
            have hkn : k < n := Finset.mem_range.mp hk
            have hμ : (n - k) + k = n := by omega
            have hidx : n + v - k = v + (n - k) := by omega
            have hμR : (((n - k : ℕ) : ℝ)) + (k : ℝ) = (n : ℝ) := by
              have hc' : ((((n - k) + k : ℕ)) : ℝ) = (n : ℝ) := by exact_mod_cast hμ
              push_cast at hc'
              linarith
            have hsplitn : ((n : ℝ) + 1) ≤ ((((n - k : ℕ) : ℝ)) + 1) * (((k : ℝ)) + 1) := by
              have hnn : (0 : ℝ) ≤ (((n - k : ℕ) : ℝ)) * (k : ℝ) := by positivity
              nlinarith only [hμR, hnn]
            have hpowsplit : ((n : ℝ) + 1) ^ a
                ≤ ((((n - k : ℕ) : ℝ)) + 1) ^ a * (((k : ℝ)) + 1) ^ a := by
              calc ((n : ℝ) + 1) ^ a
                  ≤ (((((n - k : ℕ) : ℝ)) + 1) * (((k : ℝ)) + 1)) ^ a :=
                    pow_le_pow_left₀ (by positivity) hsplitn a
                _ = ((((n - k : ℕ) : ℝ)) + 1) ^ a * (((k : ℝ)) + 1) ^ a := by rw [mul_pow]
            have h1 : ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                ≤ Cb' * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m := by
              have h := hshift (n + v - k) k
              rw [hidx, pow_add] at h
              rw [hidx, hCb'def]
              have heq : Cb * (ρ ^ v * ρ ^ (n - k)) * (((k : ℝ)) + 1) ^ m
                  = Cb * ρ ^ v * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m := by ring
              rw [← heq]
              exact h
            have h2 : ‖PowerSeries.coeff k H‖ * (((k : ℝ)) + 1) ^ a
                ≤ ε * A ^ k * ((k ! : ℝ)) ^ r := ih k hkn
            have hfactor : (((k : ℝ)) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r)
                ≤ ((n : ℝ) + 1) ^ d := shiftFactor_nat_le hmdr hkn
            have hApow : A ^ n = A ^ (n - k) * A ^ k := by rw [← pow_add, hμ]
            have hqpow : q ^ (n - k) = ρ ^ (n - k) / A ^ (n - k) := by rw [hqdef, div_pow]
            have hmid : ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                  * (‖PowerSeries.coeff k H‖ * (((k : ℝ)) + 1) ^ a)
                ≤ (Cb' * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m) * (ε * A ^ k * ((k ! : ℝ)) ^ r) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
            have hfinal : (Cb' * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m)
                  * (ε * A ^ k * ((k ! : ℝ)) ^ r)
                ≤ (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by
              have hid : (Cb' * ρ ^ (n - k) * (((k : ℝ)) + 1) ^ m)
                    * (ε * A ^ k * ((k ! : ℝ)) ^ r)
                  = (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r)) * (q ^ (n - k)
                      * ((((k : ℝ)) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r))) := by
                rw [hqpow, hApow]
                field_simp
              rw [hid]
              have hleft0 : (0 : ℝ) ≤ Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by positivity
              have hqk0 : (0 : ℝ) ≤ q ^ (n - k) := pow_nonneg hq0 _
              calc (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r)) * (q ^ (n - k)
                    * ((((k : ℝ)) + 1) ^ m * (((k ! : ℝ)) ^ r / ((n ! : ℝ)) ^ r)))
                  ≤ (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r))
                      * (q ^ (n - k) * ((n : ℝ) + 1) ^ d) := by
                    refine mul_le_mul_of_nonneg_left ?_ hleft0
                    exact mul_le_mul_of_nonneg_left hfactor hqk0
                _ = (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d) * q ^ (n - k) := by
                    ring
            have hnn0 : (0 : ℝ) ≤ ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                * ‖PowerSeries.coeff k H‖ := by positivity
            calc ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                  * ((n : ℝ) + 1) ^ a
                ≤ ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                    * (((((n - k : ℕ) : ℝ)) + 1) ^ a * (((k : ℝ)) + 1) ^ a) :=
                  mul_le_mul_of_nonneg_left hpowsplit hnn0
              _ = (((((n - k : ℕ) : ℝ)) + 1) ^ a)
                    * (‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                      * (‖PowerSeries.coeff k H‖ * (((k : ℝ)) + 1) ^ a)) := by ring
              _ ≤ (((((n - k : ℕ) : ℝ)) + 1) ^ a)
                    * ((Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                      * q ^ (n - k)) := by
                  refine mul_le_mul_of_nonneg_left (le_trans hmid hfinal) (by positivity)
              _ = (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                    * (((((n - k : ℕ) : ℝ)) + 1) ^ a * q ^ (n - k)) := by ring
          have hbig0 : (0 : ℝ) ≤ Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d := by
            positivity
          calc (∑ k ∈ Finset.range n,
                ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖)
                * ((n : ℝ) + 1) ^ a
              = ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖ * ‖PowerSeries.coeff k H‖
                    * ((n : ℝ) + 1) ^ a := by rw [Finset.sum_mul]
            _ ≤ ∑ k ∈ Finset.range n,
                  (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                    * ((((n - k : ℕ) : ℝ) + 1) ^ a * q ^ (n - k)) := Finset.sum_le_sum hstep
            _ = (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                  * ∑ k ∈ Finset.range n, (((n - k : ℕ) : ℝ) + 1) ^ a * q ^ (n - k) := by
                rw [Finset.mul_sum]
            _ ≤ (Cb' * (ε * A ^ n * ((n ! : ℝ)) ^ r) * ((n : ℝ) + 1) ^ d)
                  * (Ca * ((2 * q) / (1 - 2 * q))) :=
                mul_le_mul_of_nonneg_left
                  (polyGeom_shift_sum_le hCa (by linarith only [hCa1]) hq0 hq21 n) hbig0
            _ = (Cb' * (Ca * ((2 * q) / (1 - 2 * q))))
                  * (((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)) := by ring
            _ ≤ (c / 3) * (((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)) :=
                mul_le_mul_of_nonneg_right hqgeom (by positivity)
            _ = c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by ring
        -- assembling the recursion
        have hrec := shiftPolynomial_shift_mul_coeff B v hvlow H n
        rw [hLH0] at hrec
        have hnormrec : ‖(shiftPolynomial B v).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n H‖
            ≤ ‖PowerSeries.coeff (n + v) V‖
              + ‖PowerSeries.coeff (n + v)
                  (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
              + ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                    * ‖PowerSeries.coeff k H‖ := by
          have hleft : ‖(shiftPolynomial B v).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n H‖
              = ‖(shiftPolynomial B v).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n H‖ := norm_mul _ _
          have hA' : ‖(shiftPolynomial B v).eval ((n : ℕ) : ℂ) * PowerSeries.coeff n H‖
              ≤ ‖PowerSeries.coeff (n + v)
                    (-V - taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
                + ‖∑ k ∈ Finset.range n,
                    (shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)
                      * PowerSeries.coeff k H‖ := by
            rw [hrec]
            exact norm_sub_le _ _
          have hB' : ‖∑ k ∈ Finset.range n,
                (shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k H‖
              ≤ ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                    * ‖PowerSeries.coeff k H‖ := by
            refine le_trans (norm_sum_le _ _) ?_
            exact le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _)
          have hC' : ‖PowerSeries.coeff (n + v)
                (-V - taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
              ≤ ‖PowerSeries.coeff (n + v) V‖
                + ‖PowerSeries.coeff (n + v)
                    (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖ := by
            rw [map_sub, map_neg]
            refine le_trans (norm_sub_le _ _) ?_
            rw [norm_neg]
          rw [hleft] at hA'
          linarith only [hA', hB', hC']
        have hmid : c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n H‖
            ≤ ‖(shiftPolynomial B v).eval ((n : ℕ) : ℂ)‖ * ‖PowerSeries.coeff n H‖ :=
          mul_le_mul_of_nonneg_right hΦlow (norm_nonneg _)
        have htotal : (‖PowerSeries.coeff (n + v) V‖
              + ‖PowerSeries.coeff (n + v)
                  (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
              + ∑ k ∈ Finset.range n,
                  ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                    * ‖PowerSeries.coeff k H‖)
              * ((n : ℝ) + 1) ^ a
            ≤ c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          have hexp : (‖PowerSeries.coeff (n + v) V‖
                + ‖PowerSeries.coeff (n + v)
                    (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
                + ∑ k ∈ Finset.range n,
                    ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                      * ‖PowerSeries.coeff k H‖)
                * ((n : ℝ) + 1) ^ a
              = ‖PowerSeries.coeff (n + v) V‖ * ((n : ℝ) + 1) ^ a
                + ‖PowerSeries.coeff (n + v)
                    (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖ * ((n : ℝ) + 1) ^ a
                + (∑ k ∈ Finset.range n,
                    ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                      * ‖PowerSeries.coeff k H‖) * ((n : ℝ) + 1) ^ a := by ring
          rw [hexp]
          have hsum3 : c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)
              + c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)
              + c / 3 * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r)
              = c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by ring
          linarith only [hVest, hDest, hconv, hsum3]
        have hfinal : c * ((n : ℝ) + 1) ^ d * (‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a)
            ≤ c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := by
          have hmul := mul_le_mul_of_nonneg_right (le_trans hmid hnormrec)
            (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ a)
          calc c * ((n : ℝ) + 1) ^ d * (‖PowerSeries.coeff n H‖ * ((n : ℝ) + 1) ^ a)
              = (c * ((n : ℝ) + 1) ^ d * ‖PowerSeries.coeff n H‖) * ((n : ℝ) + 1) ^ a := by ring
            _ ≤ (‖PowerSeries.coeff (n + v) V‖
                  + ‖PowerSeries.coeff (n + v)
                      (taylorDefect (eulerJetVector Y) (eulerJetVector H) P)‖
                  + ∑ k ∈ Finset.range n,
                      ‖(shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ)‖
                        * ‖PowerSeries.coeff k H‖) * ((n : ℝ) + 1) ^ a := hmul
            _ ≤ c * ((n : ℝ) + 1) ^ d * (ε * A ^ n * ((n ! : ℝ)) ^ r) := htotal
        exact le_of_mul_le_mul_left hfinal (by positivity)
  -- from the perturbation back to the solution
  have hHgev : IsGevreySeries ((r : ℕ) : ℝ) H := hmain.isGevreySeries hεpos hApos
  have hYgev : IsGevreySeries ((r : ℕ) : ℝ) Y := hYconv0.mono (by positivity)
  rw [← hYH0]
  exact hYgev.add hHgev

end GaloisForLFunctions.HTGeometry
