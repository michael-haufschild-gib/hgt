import GaloisForLFunctions.RHTower.PrimeLogExponentialTypeUniqueness
import GaloisForLFunctions.RHTower.SelbergClass.EntireFiniteOrderAdditiveAlgebra

/-!
# Prime logarithms are a uniqueness set at every finite entire order

Jensen's formula gives a polynomial zero-count envelope for any nonzero entire function satisfying
`A * exp (B * ‖z‖ ^ ρ)` growth. Prime logarithms supply exponentially many zeros in radius `t`, so
no nonzero finite-order entire function can vanish on all, or all but finitely many, prime logs.

Classical finite-order zero-density theory is `[BRIDGE]` infrastructure. The cofinite prime-log
uniqueness theorem is the route-facing boundary needed to classify fixed analytic T1 symbols.
-/

open Complex Metric Set Filter Topology

namespace RHTower

/-- Jensen's formula with an exponential-power boundary envelope. -/
theorem exponentialPower_zeroCount_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hfc : f c ≠ 0)
    {A B ρ : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ))
    {r : ℝ} (hr : 1 ≤ r) :
    (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) ≤
      (Real.log A + B * (‖c‖ + 2 * r) ^ ρ - Real.log ‖f c‖) / Real.log 2 := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  let R : ℝ := 2 * r
  let M : ℝ := A * Real.exp (B * (‖c‖ + 2 * r) ^ ρ)
  have hR0 : 0 < R := by dsimp [R]; linarith
  have hrR : r < R := by dsimp [R]; linarith
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have harg : 0 ≤ B * (‖c‖ + 2 * r) ^ ρ :=
    mul_nonneg hB (Real.rpow_nonneg (by positivity) ρ)
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact le_trans hA (by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left (Real.one_le_exp harg) hA0.le))
  have hfan : AnalyticOnNhd ℂ f (closedBall c R) :=
    (hf.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)
  have hbound : ∀ z ∈ sphere c R, ‖f z‖ ≤ M := by
    intro z hz
    have hzdist : ‖z - c‖ = R := by simpa [mem_sphere_iff_norm] using hz
    have hznorm : ‖z‖ ≤ ‖c‖ + 2 * r := by
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        have := norm_add_le (z - c) c
        simpa [sub_add_cancel] using this
      rw [hzdist] at htri
      dsimp [R] at htri
      linarith
    calc
      ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ) := hgrow z
      _ ≤ A * Real.exp (B * (‖c‖ + 2 * r) ^ ρ) := by
        gcongr
      _ = M := rfl
  have hfanAbs : AnalyticOnNhd ℂ f (closedBall c |R|) := by
    simpa [abs_of_pos hR0] using hfan
  have hsum := hfanAbs.sum_divisor_le
    (r := r) (R := R) (M := M)
    (by simpa [abs_of_pos hr0] using hr0)
    (by simpa [abs_of_pos hr0, abs_of_pos hR0] using hrR)
    hM1 hfc (by simpa [abs_of_pos hR0] using hbound)
  have hnorm0 : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hRr : R / r = 2 := by dsimp [R]; field_simp
  rw [abs_of_pos hr0] at hsum
  dsimp [M] at hsum
  rw [hRr, Real.log_div (by positivity) hnorm0.ne',
    Real.log_mul hA0.ne' (Real.exp_ne_zero _), Real.log_exp] at hsum
  exact hsum

/-- A nonzero entire function of finite order has a polynomial zero-count envelope. -/
theorem exponentialPower_zeroCount_polynomial
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} (hfc : f c ≠ 0)
    {A B ρ : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ)) :
    ∃ d : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 1 ≤ r →
      (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) ≤
        K * (1 + r) ^ d := by
  obtain ⟨d0 : ℕ, hd0⟩ := exists_nat_ge ρ
  let d : ℕ := d0 + 1
  let C0 : ℝ := |Real.log A| + |Real.log ‖f c‖| + Real.log 2
  let D : ℝ := (‖c‖ + 2) ^ ρ
  let K : ℝ := (C0 + B * D) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) ρ
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨d, K, hK, ?_⟩
  intro r hr
  have hraw := exponentialPower_zeroCount_le hf hfc hA hB hρ hgrow hr
  have hbase : 0 ≤ ‖c‖ + 2 * r := by positivity
  have hgeom : ‖c‖ + 2 * r ≤ (‖c‖ + 2) * (1 + r) := by
    nlinarith [norm_nonneg c]
  have hpowGeom : (‖c‖ + 2 * r) ^ ρ ≤ D * (1 + r) ^ d := by
    calc
      (‖c‖ + 2 * r) ^ ρ ≤ ((‖c‖ + 2) * (1 + r)) ^ ρ :=
        Real.rpow_le_rpow hbase hgeom hρ
      _ = (‖c‖ + 2) ^ ρ * (1 + r) ^ ρ := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ (‖c‖ + 2) ^ ρ * (1 + r) ^ (d : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply Real.rpow_le_rpow_of_exponent_le
        · linarith
        · dsimp [d]
          exact hd0.trans (by exact_mod_cast Nat.le_add_right d0 1)
      _ = D * (1 + r) ^ d := by rw [Real.rpow_natCast]
  have hpowOne : 1 ≤ (1 + r) ^ d := one_le_pow₀ (by linarith)
  have hlogA : Real.log A ≤ |Real.log A| := le_abs_self _
  have hlogfc : -Real.log ‖f c‖ ≤ |Real.log ‖f c‖| := neg_le_abs _
  have hnum :
      Real.log A + B * (‖c‖ + 2 * r) ^ ρ - Real.log ‖f c‖ ≤
        (C0 + B * D) * (1 + r) ^ d := by
    have hBpow := mul_le_mul_of_nonneg_left hpowGeom hB
    dsimp [C0]
    nlinarith [mul_nonneg hB hD]
  calc
    (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ)
        ≤ (Real.log A + B * (‖c‖ + 2 * r) ^ ρ - Real.log ‖f c‖) /
            Real.log 2 := hraw
    _ ≤ ((C0 + B * D) * (1 + r) ^ d) / Real.log 2 :=
      div_le_div_of_nonneg_right hnum hlog2.le
    _ = K * (1 + r) ^ d := by dsimp [K]; ring

/-- Chebyshev's lower bound at prime-log scale beats every fixed polynomial zero-count envelope. -/
theorem exists_chebyshev_primeLog_count_gt_polynomial
    (d : ℕ) (K : ℝ) (hK : 0 < K) (c : ℂ) :
    ∃ t : ℝ, 1 ≤ t ∧ 2 + ‖c‖ ≤ t ∧ Real.log 2 < t ∧
      K * (2 + ‖c‖ + t) ^ d <
        ((Real.exp t - 1) * Real.log 2 - Real.log (Real.exp t + 2)) / t := by
  let m : ℕ := d + 2
  let B : ℝ := K * 2 ^ d + 1 + Real.log 3 + Real.log 2
  let D : ℝ := B / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := div_pos hB hlog2
  have htend := Real.tendsto_exp_div_pow_atTop m
  have hevent : ∀ᶠ t : ℝ in atTop, D + 1 ≤ Real.exp t / t ^ m :=
    tendsto_atTop.1 htend (D + 1)
  have hall : ∀ᶠ t : ℝ in atTop,
      D + 1 ≤ Real.exp t / t ^ m ∧ 1 ≤ t ∧ 2 + ‖c‖ ≤ t ∧ Real.log 2 < t := by
    filter_upwards [hevent, eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (2 + ‖c‖), eventually_gt_atTop (Real.log 2)]
      with t hratio ht1 htc htlog2
    exact ⟨hratio, ht1, htc, htlog2⟩
  obtain ⟨t, hratio, ht1, htc, htlog2⟩ := hall.exists
  refine ⟨t, ht1, htc, htlog2, ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hexp1 : 1 ≤ Real.exp t := Real.one_le_exp ht0.le
  have hlogBound : Real.log (Real.exp t + 2) ≤ t + Real.log 3 := by
    calc
      Real.log (Real.exp t + 2) ≤ Real.log (3 * Real.exp t) := by
        apply Real.log_le_log
        · positivity
        · nlinarith
      _ = Real.log 3 + Real.log (Real.exp t) := by
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero t)]
      _ = t + Real.log 3 := by rw [Real.log_exp]; ring
  have hbase : 2 + ‖c‖ + t ≤ 2 * t := by linarith
  have hpow : (2 + ‖c‖ + t) ^ d ≤ 2 ^ d * t ^ d := by
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 + ‖c‖ + t) hbase d
    simpa [mul_pow] using this
  have hpowSucc : t ^ (d + 1) ≤ t ^ m := by
    apply pow_le_pow_right₀ ht1
    dsimp [m]
    omega
  have hpoly : t * (K * (2 + ‖c‖ + t) ^ d) ≤ K * 2 ^ d * t ^ m := by
    calc
      t * (K * (2 + ‖c‖ + t) ^ d) ≤ t * (K * (2 ^ d * t ^ d)) := by
        gcongr
      _ = K * 2 ^ d * t ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ K * 2 ^ d * t ^ m := by gcongr
  have htPow : t ≤ t ^ m := by
    calc
      t = t ^ 1 := by ring
      _ ≤ t ^ m := by
        apply pow_le_pow_right₀ ht1
        dsimp [m]
        omega
  have honePow : 1 ≤ t ^ m := one_le_pow₀ ht1
  have hsmall : t + Real.log 3 + Real.log 2 ≤
      (1 + Real.log 3 + Real.log 2) * t ^ m := by
    have hlogs : Real.log 3 + Real.log 2 ≤
        (Real.log 3 + Real.log 2) * t ^ m := by
      nlinarith [mul_le_mul_of_nonneg_left honePow
        (by positivity : 0 ≤ Real.log 3 + Real.log 2)]
    nlinarith
  have hbudget :
      t * (K * (2 + ‖c‖ + t) ^ d) + t + Real.log 3 + Real.log 2 ≤
        B * t ^ m := by
    dsimp [B]
    nlinarith
  have hm0 : 0 < t ^ m := pow_pos ht0 m
  have hratio' : D < Real.exp t / t ^ m := lt_of_lt_of_le (lt_add_one D) hratio
  have hmul : D * t ^ m < Real.exp t := (lt_div_iff₀ hm0).mp hratio'
  have hBD : B = D * Real.log 2 := by
    dsimp [D]
    field_simp
  have hexpDom : B * t ^ m < Real.exp t * Real.log 2 := by
    calc
      B * t ^ m = (D * t ^ m) * Real.log 2 := by rw [hBD]; ring
      _ < Real.exp t * Real.log 2 := mul_lt_mul_of_pos_right hmul hlog2
  rw [lt_div_iff₀ ht0]
  nlinarith

/-- Prime logarithms are a uniqueness set for every entire function with one finite-order global
growth witness. -/
theorem eq_zero_of_exponentialPower_of_primeLog_zeros
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B ρ : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ ρ))
    (hprime : ∀ p : ℕ, p.Prime → f (Real.log p) = 0) :
    f = 0 := by
  funext c
  by_contra hfc
  obtain ⟨d, K, hK, hzeroCount⟩ :=
    exponentialPower_zeroCount_polynomial hf hfc hA hB hρ hgrow
  obtain ⟨t, ht1, htc, htlog2, hdom⟩ :=
    exists_chebyshev_primeLog_count_gt_polynomial d K hK c
  let n : ℕ := ⌊Real.exp t⌋₊
  have hexp2 : (2 : ℝ) < Real.exp t := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := by
        rw [Real.exp_log (by norm_num)]
      _ < Real.exp t := Real.exp_lt_exp.mpr htlog2
  have hn : 2 ≤ n := by
    apply Nat.le_floor
    exact hexp2.le
  have hn0 : (0 : ℝ) < n := by positivity
  have hnexp : (n : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  have hlogn : Real.log n ≤ t := (Real.log_le_iff_le_exp hn0).2 hnexp
  have hprimeLower :
      ((Real.exp t - 1) * Real.log 2 - Real.log (Real.exp t + 2)) / t ≤
        (n.primeCounting : ℝ) := by
    have h := Chebyshev.pi_ge' (x := Real.exp t) (by linarith [Real.exp_pos t])
    simpa [n, Real.log_exp] using h
  let r : ℝ := 1 + ‖c‖ + Real.log n
  have hr : 1 ≤ r := by
    have hlogn0 : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    dsimp [r]
    linarith [norm_nonneg c]
  have hdivLowerInt := primeCounting_le_sum_divisor_of_primeLog_zeros
    hf hfc hprime hn
  have hdivLower : (n.primeCounting : ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) := by
    exact_mod_cast hdivLowerInt
  have hdivUpper :
      (↑(∑ᶠ u, (MeromorphicOn.divisor f (closedBall c r)) u) : ℝ) ≤
        K * (1 + r) ^ d := hzeroCount r hr
  have hbase : 0 ≤ 1 + r := by linarith
  have hshift : 1 + r ≤ 2 + ‖c‖ + t := by
    dsimp [r]
    linarith
  have hKmono : K * (1 + r) ^ d ≤ K * (2 + ‖c‖ + t) ^ d := by
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact pow_le_pow_left₀ hbase hshift d
  linarith

/-- The carrier-level form of finite-order prime-log uniqueness. -/
theorem EntireFiniteOrder.eq_zero_of_primeLog_zeros
    (F : EntireFiniteOrder)
    (hprime : ∀ p : ℕ, p.Prime → F (Real.log p) = 0) :
    (fun z : ℂ ↦ F z) = 0 := by
  rcases F.growth with ⟨A, B, ρ, hA, hB, hρ, hgrow⟩
  have hFdiff : Differentiable ℂ (fun z : ℂ ↦ F z) := fun z ↦ by
    simpa only [differentiableWithinAt_univ] using
      F.analytic.differentiableOn z (mem_univ z)
  apply eq_zero_of_exponentialPower_of_primeLog_zeros hFdiff
      (le_max_left (1 : ℝ) A) hB.le hρ ?_ hprime
  intro z
  exact (hgrow z).trans (mul_le_mul_of_nonneg_right
    (le_max_right (1 : ℝ) A) (Real.exp_pos _).le)

/-- Dropping finitely many prime logarithms does not restore a nonzero finite-order entire
function. -/
theorem EntireFiniteOrder.eq_zero_of_cofinite_primeLog_zeros
    (F : EntireFiniteOrder) (E : Finset ℕ)
    (hprime : ∀ p : ℕ, p.Prime → p ∉ E → F (Real.log p : ℂ) = 0) :
    (fun z : ℂ ↦ F z) = 0 := by
  classical
  let Q : Polynomial ℂ :=
    ∏ q ∈ E, (Polynomial.X - Polynomial.C ((Real.log ((q : ℕ) : ℝ) : ℝ) : ℂ))
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    refine Finset.prod_ne_zero_iff.mpr (fun q _ ↦ ?_)
    exact (Polynomial.monic_X_sub_C _).ne_zero
  let G : EntireFiniteOrder := F.mul (entireFiniteOrderPolynomial Q)
  have hGprime : ∀ p : ℕ, p.Prime → G (Real.log p : ℂ) = 0 := by
    intro p hp
    by_cases hpE : p ∈ E
    · have hroot : Q.eval ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) = 0 := by
        dsimp [Q]
        rw [Polynomial.eval_prod]
        refine Finset.prod_eq_zero hpE ?_
        simp
      simp only [G, EntireFiniteOrder.mul_apply, entireFiniteOrderPolynomial_apply, hroot, mul_zero]
    · simp only [G, EntireFiniteOrder.mul_apply, hprime p hp hpE, zero_mul]
  have hGzero : (fun z : ℂ ↦ G z) = 0 := G.eq_zero_of_primeLog_zeros hGprime
  have hdense : Dense ({z : ℂ | Q.eval z = 0}ᶜ) :=
    Set.Countable.dense_compl ℂ (Polynomial.finite_setOf_isRoot hQ0).countable
  have hFdiff : Differentiable ℂ (fun z : ℂ ↦ F z) := fun z ↦ by
    simpa only [differentiableWithinAt_univ] using
      F.analytic.differentiableOn z (mem_univ z)
  refine Continuous.ext_on hdense hFdiff.continuous continuous_const ?_
  intro z hz
  have hgz : F z * Q.eval z = 0 := by
    have := congrFun hGzero z
    simpa only [G, Pi.zero_apply, EntireFiniteOrder.mul_apply,
      entireFiniteOrderPolynomial_apply] using this
  rcases mul_eq_zero.mp hgz with h1 | h2
  · exact h1
  · exact absurd h2 hz

end RHTower
