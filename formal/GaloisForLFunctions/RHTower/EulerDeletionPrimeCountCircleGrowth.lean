import GaloisForLFunctions.RHTower.EulerDeletionPrimeCountAmplification
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Complete prime-count source on complex circles

The complex deformation `P_N(z) = sum_(n <= N) mu(n) z^omega(n) b_n` retains
the complete physical Hilbert carrier. On every fixed circle of positive
radius its maximum squared norm lies between `c N^(1-epsilon)` and
`C N^(1+epsilon)`, for every positive epsilon and sufficiently large N.

The divisor bound makes every fixed exponential in the degree subpower.
Cauchy's coefficient estimate then transports the physical aperture lower
bound to any fixed circle. This concerns the circle maximum; it gives no
lower bound for the distinguished endpoint `z=1`.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower.PrimeCountDamping

private theorem two_pow_count_le_divisors {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n.divisors.card := by
  rw [Nat.card_divisors (by omega : n ≠ 0)]
  calc
    _ = ∏ p ∈ n.primeFactors, 2 := by simp
    _ ≤ _ := Finset.prod_le_prod' fun p hp => by
      have h := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
        (by omega : n ≠ 0) (Nat.dvd_of_mem_primeFactors hp)
      omega

/-- Every fixed exponential in the number of distinct prime factors is subpower. -/
theorem pow_primeCount_le_const_rpow {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      B ^ n.primeFactors.card ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨j, hj⟩ := exists_nat_gt B
  have hj0 : 0 < j := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hB).trans hj
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  have hBj : B ≤ (2 : ℝ)^j := by
    have htwo : (j : ℝ) < (2 : ℝ)^j := by exact_mod_cast (Nat.lt_two_pow_self (n := j))
    exact (hj.trans htwo).le
  obtain ⟨C, hC, hdiv⟩ := card_divisors_le_const_mul_rpow (div_pos hε hjR)
  refine ⟨C^j, pow_pos hC _, fun n hn => ?_⟩
  have hd : (2 : ℝ)^n.primeFactors.card ≤ n.divisors.card := by
    exact_mod_cast two_pow_count_le_divisors hn
  calc
    B^n.primeFactors.card ≤ ((2 : ℝ)^j)^n.primeFactors.card :=
      pow_le_pow_left₀ (by linarith) hBj _
    _ = ((2 : ℝ)^n.primeFactors.card)^j := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (n.divisors.card : ℝ)^j := pow_le_pow_left₀ (by positivity) hd _
    _ ≤ (C*(n : ℝ)^(ε/(j : ℝ)))^j :=
      pow_le_pow_left₀ (by positivity) (hdiv n hn) _
    _ = C^j*(n : ℝ)^ε := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      field_simp

/-- Largest number of distinct prime factors below the actual integer cutoff. -/
def primeCountDegree (N : ℕ) : ℕ := (Icc 1 N).sup (fun n => n.primeFactors.card)

theorem primeCount_le_degree {N n : ℕ} (hn : n ∈ Icc 1 N) :
    n.primeFactors.card ≤ primeCountDegree N :=
  Finset.le_sup (f := fun n => n.primeFactors.card) hn

/-- The degree of the complete prime-count deformation has subpower exponential cost. -/
theorem pow_primeCountDegree_le_const_rpow {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      B ^ primeCountDegree N ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨C, hC, h⟩ := pow_primeCount_le_const_rpow hB hε
  refine ⟨C, hC, fun N hN => ?_⟩
  obtain ⟨n, hn, heq⟩ := Finset.exists_mem_eq_sup (Icc 1 N)
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩ (fun n => n.primeFactors.card)
  change B ^ ((Icc 1 N).sup _) ≤ _
  rw [heq]
  exact (h n (Finset.mem_Icc.mp hn).1).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hε.le) hC.le)

private theorem polynomial_iteratedDeriv (P : Polynomial ℂ) (k : ℕ) (x : ℂ) :
    iteratedDeriv k (fun y : ℂ => P.eval y) x =
      (Polynomial.derivative^[k] P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
    rw [show k+1=k.succ by omega, Function.iterate_succ_apply]
    rw [show iteratedDeriv k.succ (fun y : ℂ => P.eval y) =
        iteratedDeriv k (deriv fun y : ℂ => P.eval y) by
        simpa using (iteratedDeriv_succ' (n := k) (f := fun y : ℂ => P.eval y))]
    have hderiv : deriv (fun y : ℂ => P.eval y) = fun y : ℂ => P.derivative.eval y := by
      funext y
      exact (P.hasDerivAt y).deriv
    rw [hderiv, ih]

private theorem polynomial_iteratedDeriv_taylor (P : Polynomial ℂ) (k : ℕ) (a : ℂ) :
    iteratedDeriv k (fun y : ℂ => P.eval y) a =
      (k.factorial : ℂ) * (Polynomial.taylor a P).coeff k := by
  rw [polynomial_iteratedDeriv, Polynomial.taylor_coeff]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := k)) P
  have he := congrArg (fun Q : Polynomial ℂ => Q.eval a) h
  simpa using he.symm

private theorem polynomial_circle_transport (P : Polynomial ℂ) {D : ℕ} (hD : P.natDegree ≤ D)
    {a w : ℂ} {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ z ∈ Metric.sphere a r, ‖P.eval z‖ ≤ M) :
    ‖P.eval w‖ ≤ M * (D+1) * max 1 (‖w-a‖/r)^D := by
  have hc (j : ℕ) : ‖(Polynomial.taylor a P).coeff j‖ ≤ M/r^j := by
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      j hr P.differentiable.diffContOnCl hb
    rw [polynomial_iteratedDeriv_taylor, norm_mul, Complex.norm_natCast] at h
    have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    apply (mul_le_mul_iff_right₀ hf).mp
    simpa only [mul_div_assoc] using h
  rw [← Polynomial.taylor_eval_sub a P w,
    Polynomial.eval_eq_sum_range' (by rw [Polynomial.natDegree_taylor]; omega :
      (Polynomial.taylor a P).natDegree < D+1)]
  calc
    _ ≤ ∑ j ∈ range (D+1), ‖(Polynomial.taylor a P).coeff j * (w-a)^j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range (D+1), M * max 1 (‖w-a‖/r)^D := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow]
      calc
        _ ≤ (M/r^j)*‖w-a‖^j := mul_le_mul_of_nonneg_right (hc j) (by positivity)
        _ = M*(‖w-a‖/r)^j := by rw [div_pow]; ring
        _ ≤ M*max 1 (‖w-a‖/r)^j := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _) hM
        _ ≤ M*max 1 (‖w-a‖/r)^D := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.mem_range.mp hj)) hM
    _ = _ := by simp [mul_assoc, mul_left_comm]

/-- Prime-count deformation on the complete physical Hilbert carrier. -/
def complexSource (N : ℕ) (z : ℂ) : BDCarrier :=
  ∑ n ∈ Icc 1 N, ((ArithmeticFunction.moebius n : ℂ) * z^n.primeFactors.card) •
    bdGen (1/(n : ℝ))

theorem complexSource_real (N : ℕ) (u : ℝ) : complexSource N u = source N u := by
  simp [complexSource, source, Sieve.fullPrimeDampedMoebius]

theorem continuous_complexSource (N : ℕ) : Continuous (complexSource N) := by
  unfold complexSource
  fun_prop

private def sourceScalarPolynomial (N : ℕ) (v : BDCarrier) : Polynomial ℂ :=
  ∑ n ∈ Icc 1 N, Polynomial.monomial n.primeFactors.card
    ((ArithmeticFunction.moebius n : ℂ) * inner ℂ v (bdGen (1/(n : ℝ))))

private theorem sourceScalarPolynomial_eval (N : ℕ) (v : BDCarrier) (z : ℂ) :
    (sourceScalarPolynomial N v).eval z = inner ℂ v (complexSource N z) := by
  simp [sourceScalarPolynomial, Polynomial.eval_finsetSum, complexSource, inner_sum,
    inner_smul_right, mul_comm, mul_left_comm]

private theorem sourceScalarPolynomial_degree (N : ℕ) (v : BDCarrier) :
    (sourceScalarPolynomial N v).natDegree ≤ primeCountDegree N := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_monomial_le _).trans (primeCount_le_degree hn)

/-- Finite polynomial extrapolation for the complete Hilbert-valued source. -/
theorem complexSource_circle_transport (N : ℕ) {a w : ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ z ∈ Metric.sphere a r, ‖complexSource N z‖ ≤ M) :
    ‖complexSource N w‖ ≤ M * (primeCountDegree N+1) * max 1 (‖w-a‖/r)^primeCountDegree N := by
  let v := complexSource N w
  have h := polynomial_circle_transport (sourceScalarPolynomial N v)
    (sourceScalarPolynomial_degree N v) (w := w) hr (mul_nonneg (norm_nonneg v) hM)
    (fun z hz => by
      rw [sourceScalarPolynomial_eval]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb z hz) (norm_nonneg v)))
  rw [sourceScalarPolynomial_eval] at h
  change ‖inner ℂ v v‖ ≤ _ at h
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg v)] at h
  by_cases hv : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hv]
    positivity
  · have hvp := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    change ‖v‖ ≤ _
    apply (mul_le_mul_iff_right₀ hvp).mp
    nlinarith [h]

theorem complexSource_norm_le (N : ℕ) {z : ℂ} {B : ℝ} (hB : 1 ≤ B) (hz : ‖z‖ ≤ B) :
    ‖complexSource N z‖ ≤ 4*Real.sqrt N * B^primeCountDegree N := by
  have hc (n : ℕ) (hn : n ∈ Icc 1 N) :
      ‖(ArithmeticFunction.moebius n : ℂ)*z^n.primeFactors.card‖ ≤ B^primeCountDegree N := by
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ‖z‖^n.primeFactors.card := mul_le_of_le_one_left (by positivity) hm
      _ ≤ B^n.primeFactors.card := pow_le_pow_left₀ (norm_nonneg _) hz _
      _ ≤ B^primeCountDegree N := pow_le_pow_right₀ hB (primeCount_le_degree hn)
  unfold complexSource
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖((ArithmeticFunction.moebius n : ℂ)*z^n.primeFactors.card) •
          bdGen (1/(n : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, B^primeCountDegree N * ‖bdGen (1/(n : ℝ))‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hc n hn) (norm_nonneg _)
    _ = B^primeCountDegree N * ∑ n ∈ Icc 1 N, ‖bdGen (1/(n : ℝ))‖ := by rw [Finset.mul_sum]
    _ ≤ B^primeCountDegree N * (4*Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (sum_generator_norm_le N) (by positivity)
    _ = _ := by ring

/-- Nearly linear energy uniformly on any fixed bounded set of parameters. -/
theorem complexSource_energy_upper {B ε : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ z : ℂ, ‖z‖ ≤ B →
      ‖complexSource N z‖^2 ≤ C*(N : ℝ)^(1+ε) := by
  obtain ⟨C, hC, h⟩ := pow_primeCountDegree_le_const_rpow hB (half_pos hε)
  refine ⟨16*C^2, by positivity, fun N hN z hz => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn := (complexSource_norm_le N hB hz).trans
    (mul_le_mul_of_nonneg_left (h N hN) (by positivity))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have he : (4*Real.sqrt N * (C*(N : ℝ)^(ε/2)))^2 = 16*C^2*(N : ℝ)^(1+ε) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hN0.le,
      ← Real.rpow_mul_natCast hN0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2 : ℝ)=ε by ring, Real.rpow_add hN0, Real.rpow_one]
    ring
  exact he ▸ hs

/-- Transport from any fixed circle to the physical aperture costs only a subpower factor. -/
theorem aperture_circle_transport_subpower (a : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ Metric.sphere a r, ‖complexSource N z‖ ≤ M) →
      ‖source N (aperture N)‖ ≤ C*(N : ℝ)^ε*M := by
  let A : ℝ := max 1 ((‖a‖+1)/r)
  have hA : 1 ≤ A := le_max_left _ _
  obtain ⟨C, hC, h⟩ := pow_primeCountDegree_le_const_rpow
    (B := 2*A) (by linarith) hε
  refine ⟨2*C, by positivity, fun N hN M hM hb => ?_⟩
  have hw : ‖(aperture N : ℂ)-a‖/r ≤ A := by
    apply le_trans (div_le_div_of_nonneg_right (norm_sub_le _ _) hr.le)
    apply le_trans _ (le_max_right _ _)
    apply div_le_div_of_nonneg_right _ hr.le
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (aperture_mem N).1]
    linarith [(aperture_mem N).2]
  have ht := complexSource_circle_transport N (w := (aperture N : ℂ)) hr hM hb
  rw [complexSource_real] at ht
  calc
    _ ≤ M*(primeCountDegree N+1)*max 1 (‖(aperture N : ℂ)-a‖/r)^primeCountDegree N := ht
    _ ≤ M*(primeCountDegree N+1)*A^primeCountDegree N := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (max_le hA hw) _) (by positivity)
    _ ≤ M*((2 : ℝ)^(primeCountDegree N+1))*A^primeCountDegree N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by exact_mod_cast (Nat.lt_two_pow_self (n := primeCountDegree N+1)).le) hM) (by positivity)
    _ = 2*M*(2*A)^primeCountDegree N := by rw [mul_pow, pow_succ]; ring
    _ ≤ 2*M*(C*(N : ℝ)^ε) := mul_le_mul_of_nonneg_left (h N hN) (by positivity)
    _ = _ := by ring


/-- Every fixed circle has nearly linear maximal complete-source energy. -/
theorem complexSource_circle_energy_growth (a : ℂ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∃ z ∈ Metric.sphere a r,
        (∀ w ∈ Metric.sphere a r, ‖complexSource N w‖^2 ≤ ‖complexSource N z‖^2) ∧
        c*(N : ℝ)^(1-ε) ≤ ‖complexSource N z‖^2 ∧
        ‖complexSource N z‖^2 ≤ C*(N : ℝ)^(1+ε) := by
  obtain ⟨K, hK, ht⟩ := aperture_circle_transport_subpower a hr
    (show 0 < ε/4 by linarith)
  obtain ⟨C, hC, hu⟩ := complexSource_energy_upper (B := max 1 (‖a‖+r))
    (le_max_left _ _) hε
  have hlog : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ)^4 ≤ (N : ℝ)^(ε/2) := by
    have h := ((isLittleO_log_rpow_rpow_atTop ((4 : ℕ) : ℝ) (half_pos hε)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).bound
      (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [h] with N hN
    have hb : |Real.log (N : ℝ)^4| ≤ (N : ℝ)^(ε/2) := by
      simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) _), one_mul] using hN
    exact (le_abs_self _).trans hb
  refine ⟨1/(amplificationConstant*K^2), C, by positivity [amplificationConstant_pos], hC, ?_⟩
  filter_upwards [aperture_energy_eventually_lower, hlog, eventually_ge_atTop 2]
    with N hlower hl hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < amplificationConstant * Real.log (N : ℝ)^4 :=
    mul_pos amplificationConstant_pos (pow_pos (Real.log_pos hN1) _)
  obtain ⟨z, hz, hzmax⟩ := (isCompact_sphere a r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (continuous_complexSource N).norm.continuousOn
  have hb : ∀ w ∈ Metric.sphere a r, ‖complexSource N w‖ ≤ ‖complexSource N z‖ :=
    isMaxOn_iff.mp hzmax
  have htN := ht N (by omega) _ (norm_nonneg _) hb
  have hs := pow_le_pow_left₀ (norm_nonneg _) htN 2
  have hsq : (K*(N : ℝ)^(ε/4)*‖complexSource N z‖)^2 =
      K^2*(N : ℝ)^(ε/2)*‖complexSource N z‖^2 := by
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hN0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/4*2=ε/2 by ring]
  rw [hsq] at hs
  have he := (div_le_iff₀ hL).mp (hlower.trans hs)
  have he' : (N : ℝ) ≤ amplificationConstant*K^2*(N : ℝ)^ε*‖complexSource N z‖^2 := by
    calc
      (N : ℝ) ≤ (K^2*(N : ℝ)^(ε/2)*‖complexSource N z‖^2)*
          (amplificationConstant*Real.log (N : ℝ)^4) := he
      _ ≤ (K^2*(N : ℝ)^(ε/2)*‖complexSource N z‖^2)*
          (amplificationConstant*(N : ℝ)^(ε/2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl amplificationConstant_pos.le)
          (by positivity)
      _ = amplificationConstant*K^2*((N : ℝ)^(ε/2)*(N : ℝ)^(ε/2))*
          ‖complexSource N z‖^2 := by ring
      _ = _ := by rw [← Real.rpow_add hN0, add_halves]
  have hc : (N : ℝ)^(1-ε) ≤ amplificationConstant*K^2*‖complexSource N z‖^2 := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hN0 ε)).mp
    calc
      (N : ℝ)^(1-ε)*(N : ℝ)^ε = (N : ℝ) := by
        rw [← Real.rpow_add hN0, sub_add_cancel, Real.rpow_one]
      _ ≤ _ := he'
      _ = _ := by ring
  refine ⟨z, hz, fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hb w hw) 2, ?_, ?_⟩
  · rw [one_div_mul_eq_div]
    exact (div_le_iff₀ (mul_pos amplificationConstant_pos (pow_pos hK _))).mpr (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hc)
  · apply hu N (by omega) z
    apply le_trans _ (le_max_right _ _)
    have hzn := norm_add_le (z-a) a
    rw [sub_add_cancel, mem_sphere_iff_norm.mp hz] at hzn
    linarith


end RHTower.PrimeCountDamping
