import GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall

/-!
# The Poisson-subordinate smooth Cartier entrance wall

Damping the all-prime Burnol boundary by the Poisson subordination weight

`A_{y,p} = p⁻¹ exp(-y √(log p))`

keeps every prime-log differential domain: `∑ (log p)^{2k} A_{y,p}²` converges for every `k`,
because `u^{2k} e^{-2y√u} ≤ C/u²`.  No positive analytic radius survives: multiplying by
`exp(2a log p)` with `a > 0` makes the same sum diverge, since `√u = o(u)` and `∑ 1/p` diverges.

The inverse-completed Cartier jet of this smooth source has exactly the same entrance wall as the
rough one: it lies in every prime-log differential domain when `Re ρ ≤ 1/2`, and fails to be square
summable at all when `Re ρ > 1/2`.  Smoothness of the source is therefore not the obstruction.
-/

open Complex Real Filter Topology

noncomputable section

namespace RHTower

/-- The Poisson subordination weight `A_{y,p} = p⁻¹ exp(-y √(log p))`. -/
def burnolPoissonWeight (y : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-(y * Real.sqrt (Real.log (p : ℝ)))) / (p : ℝ)

theorem burnolPoissonWeight_pos {y : ℝ} {p : ℕ} (hp : 2 ≤ p) : 0 < burnolPoissonWeight y p := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  rw [burnolPoissonWeight]
  positivity

/-! ## Full prime-log smoothness -/

/-- **Every prime-log differential domain contains the subordinate boundary.** -/
theorem burnolSummable_poissonWeight_logPow {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) ^ (2 * k) *
      Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) / ((p : ℕ) : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := burnolPow_mul_exp_neg_sqrt_le hy (2 * k)
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (burnolSummable_prime_one_div_mul_log_sq.mul_left C)
  · have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    positivity
  · have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    have hbase := hC (Real.log ((p : ℕ) : ℝ)) hLpos
    rw [div_le_iff₀ hppos]
    have hstep : Real.log ((p : ℕ) : ℝ) ^ (2 * k) *
        Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) ≤
        C / Real.log ((p : ℕ) : ℝ) ^ 2 := hbase
    have hval : C * (1 / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) ^ 2)) * ((p : ℕ) : ℝ) =
        C / Real.log ((p : ℕ) : ℝ) ^ 2 := by
      field_simp
    rw [hval]
    exact hstep

/-! ## Zero analytic radius -/

/-- **No positive prime-log analytic radius survives.** -/
theorem burnolNotSummable_poissonWeight_expGain {y : ℝ} (hy : 0 < y) {a : ℝ} (ha : 0 < a) :
    ¬ Summable (fun p : Nat.Primes =>
      Real.exp (2 * a * Real.log ((p : ℕ) : ℝ)) *
        Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) / ((p : ℕ) : ℝ)) := by
  intro hsum
  classical
  set N : ℝ := Real.exp ((y / a) ^ 2) with hN
  set s : Set Nat.Primes := {p : Nat.Primes | ((p : ℕ) : ℝ) < N} with hs
  have hsfin : s.Finite := by
    have himg : s ⊆ Subtype.val ⁻¹' (Set.Iio ⌈N⌉₊) := by
      intro p hp
      have hlt : ((p : ℕ) : ℝ) < N := hp
      have hlt' : ((p : ℕ) : ℝ) < (⌈N⌉₊ : ℝ) := lt_of_lt_of_le hlt (Nat.le_ceil N)
      exact_mod_cast hlt'
    exact Set.Finite.subset
      (Set.Finite.preimage (Subtype.val_injective.injOn) (Set.finite_Iio ⌈N⌉₊)) himg
  have hsub : Summable (fun x : ↥sᶜ =>
      Real.exp (2 * a * Real.log (((x : Nat.Primes) : ℕ) : ℝ)) *
        Real.exp (-(2 * y * Real.sqrt (Real.log (((x : Nat.Primes) : ℕ) : ℝ)))) /
          (((x : Nat.Primes) : ℕ) : ℝ)) := hsum.subtype _
  have hcomp : Summable (fun x : ↥sᶜ => 1 / ((((x : Nat.Primes) : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) ?_ hsub
    rintro ⟨p, hp⟩
    have hple : N ≤ ((p : ℕ) : ℝ) := by
      have hnot : ¬ (((p : ℕ) : ℝ) < N) := hp
      linarith [not_lt.mp hnot]
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    -- past the threshold the exponential gain dominates the square-root loss
    have hthr : (y / a) ^ 2 ≤ Real.log ((p : ℕ) : ℝ) := by
      have := Real.log_le_log (by positivity) hple
      rwa [hN, Real.log_exp] at this
    have hsqrtle : Real.sqrt (Real.log ((p : ℕ) : ℝ)) ≥ y / a := by
      have h := Real.sqrt_le_sqrt hthr
      rwa [Real.sqrt_sq (by positivity)] at h
    have hsq : Real.sqrt (Real.log ((p : ℕ) : ℝ)) ^ 2 = Real.log ((p : ℕ) : ℝ) :=
      Real.sq_sqrt hLpos.le
    have hgain : 2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)) ≤
        2 * a * Real.log ((p : ℕ) : ℝ) := by
      have hsnn : 0 ≤ Real.sqrt (Real.log ((p : ℕ) : ℝ)) := Real.sqrt_nonneg _
      have hya : y ≤ a * Real.sqrt (Real.log ((p : ℕ) : ℝ)) := (div_le_iff₀' ha).mp hsqrtle
      nlinarith [mul_le_mul_of_nonneg_right hya hsnn, hsq]
    have hexp : (1 : ℝ) ≤ Real.exp (2 * a * Real.log ((p : ℕ) : ℝ)) *
        Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    rw [div_le_div_iff₀ hppos hppos]
    nlinarith [hexp, hppos]
  exact burnolNotSummable_prime_one_div ((Set.Finite.summable_compl_iff hsfin).mp hcomp)

/-! ## The smooth inverse-completion wall -/

/-- The inverse-completed Cartier jet of the Poisson-subordinate source. -/
def burnolPoissonInverseCompletionCoefficient (y : ℝ) (c ρ : ℂ) (p : ℕ) : ℂ :=
  ((burnolPoissonWeight y p : ℝ) : ℂ) * c / burnolAllPrimeCompletionMultiplier p ρ

theorem burnolPoissonInverseCompletionCoefficient_eq {y : ℝ} {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    burnolPoissonInverseCompletionCoefficient y c ρ p =
      burnolAllPrimeInverseCompletionConstant c ρ *
        ((Real.exp (-(y * Real.sqrt (Real.log (p : ℝ)))) : ℝ) : ℂ) *
        (((p : ℂ) ^ ρ - 1) / (p : ℂ)) := by
  have hρne0 : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; linarith
  have hρne1 : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hρ1; linarith
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hdil : (p : ℂ) ^ ρ - 1 ≠ 0 := nat_cpow_sub_one_ne_zero hp hρ0
  rw [burnolPoissonInverseCompletionCoefficient, burnolAllPrimeInverseCompletionConstant,
    burnolAllPrimeCompletionMultiplier, burnolPoissonWeight]
  push_cast
  field_simp

theorem norm_burnolPoissonInverseCompletionCoefficient {y : ℝ} {c ρ : ℂ} {p : ℕ} (hp : 2 ≤ p)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    ‖burnolPoissonInverseCompletionCoefficient y c ρ p‖ =
      ‖burnolAllPrimeInverseCompletionConstant c ρ‖ *
        Real.exp (-(y * Real.sqrt (Real.log (p : ℝ)))) *
        (‖(p : ℂ) ^ ρ - 1‖ / (p : ℝ)) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  rw [burnolPoissonInverseCompletionCoefficient_eq hp hρ0 hρ1, norm_mul, norm_mul, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_natCast]

/-- **Convergent side of the smooth wall, in every prime-log differential domain.** -/
theorem burnolSummable_poissonInverseCompletion_of_re_le_half {y : ℝ} (hy : 0 < y) {c ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρhalf : ρ.re ≤ 1 / 2) (k : ℕ) :
    Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) ^ (2 * k) *
      ‖burnolPoissonInverseCompletionCoefficient y c ρ (p : ℕ)‖ ^ 2) := by
  have hρ1 : ρ.re < 1 := by linarith
  set K : ℝ := ‖burnolAllPrimeInverseCompletionConstant c ρ‖ with hK
  have hKnn : 0 ≤ K := norm_nonneg _
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    ((burnolSummable_poissonWeight_logPow hy k).mul_left (4 * K ^ 2))
  · have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    positivity
  · have hp : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    have hnum : ‖((p : ℕ) : ℂ) ^ ρ - 1‖ ≤ 2 * Real.sqrt ((p : ℕ) : ℝ) := by
      refine (norm_nat_cpow_sub_one_le hp ρ).trans ?_
      have h1 : ((p : ℕ) : ℝ) ^ ρ.re ≤ ((p : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
      have h2 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hp1.le (by norm_num)
      rw [Real.sqrt_eq_rpow]
      linarith
    have hsqrtpos : 0 < Real.sqrt ((p : ℕ) : ℝ) := Real.sqrt_pos.mpr hppos
    have hsqrt : Real.sqrt ((p : ℕ) : ℝ) ^ 2 = ((p : ℕ) : ℝ) := Real.sq_sqrt hppos.le
    have hE : 0 < Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) := Real.exp_pos _
    have hexpsq : Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) ^ 2 =
        Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hdiv : 2 * Real.sqrt ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) = 2 / Real.sqrt ((p : ℕ) : ℝ) := by
      rw [div_eq_div_iff (ne_of_gt hppos) (ne_of_gt hsqrtpos)]
      linear_combination 2 * hsqrt
    rw [norm_burnolPoissonInverseCompletionCoefficient hp hρ0 hρ1, ← hK]
    have hb : K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
        (‖((p : ℕ) : ℂ) ^ ρ - 1‖ / ((p : ℕ) : ℝ)) ≤
        2 * K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) /
          Real.sqrt ((p : ℕ) : ℝ) := by
      have hstep : ‖((p : ℕ) : ℂ) ^ ρ - 1‖ / ((p : ℕ) : ℝ) ≤
          2 * Real.sqrt ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      have h2 := mul_le_mul_of_nonneg_left hstep
        (by positivity : (0 : ℝ) ≤ K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))))
      rw [hdiv] at h2
      calc K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
            (‖((p : ℕ) : ℂ) ^ ρ - 1‖ / ((p : ℕ) : ℝ))
          ≤ K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
            (2 / Real.sqrt ((p : ℕ) : ℝ)) := h2
        _ = 2 * K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) /
            Real.sqrt ((p : ℕ) : ℝ) := by ring
    have hnn : 0 ≤ K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
        (‖((p : ℕ) : ℂ) ^ ρ - 1‖ / ((p : ℕ) : ℝ)) := by positivity
    have hval : (2 * K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) /
        Real.sqrt ((p : ℕ) : ℝ)) ^ 2 =
        4 * K ^ 2 * (Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) /
          ((p : ℕ) : ℝ)) := by
      rw [div_pow, hsqrt, ← hexpsq]
      ring
    calc Real.log ((p : ℕ) : ℝ) ^ (2 * k) *
          (K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
            (‖((p : ℕ) : ℂ) ^ ρ - 1‖ / ((p : ℕ) : ℝ))) ^ 2
        ≤ Real.log ((p : ℕ) : ℝ) ^ (2 * k) *
          (2 * K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) /
            Real.sqrt ((p : ℕ) : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hb 2) (by positivity)
      _ = 4 * K ^ 2 * (Real.log ((p : ℕ) : ℝ) ^ (2 * k) *
            Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) / ((p : ℕ) : ℝ)) := by
          rw [hval]
          ring

/-- **Divergent side of the smooth wall.**  Past the critical abscissa the smooth jet is not even
square summable. -/
theorem burnolNotSummable_poissonInverseCompletion_of_half_lt_re {y : ℝ} (hy : 0 < y) {c ρ : ℂ}
    (hc : c ≠ 0) (hρhalf : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) :
    ¬ Summable (fun p : Nat.Primes =>
      ‖burnolPoissonInverseCompletionCoefficient y c ρ (p : ℕ)‖ ^ 2) := by
  have hρ0 : 0 < ρ.re := by linarith
  have hρne0 : ρ ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hρ0; linarith
  have hρne1 : ρ ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hρ1; linarith
  set K : ℝ := ‖burnolAllPrimeInverseCompletionConstant c ρ‖ with hK
  have hKpos : 0 < K :=
    norm_pos_iff.mpr (burnolAllPrimeInverseCompletionConstant_ne_zero hc hρne0 hρne1)
  intro hsum
  set δ : ℝ := ρ.re - 1 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  refine burnolNotSummable_poissonWeight_expGain hy (a := δ) hδpos ?_
  obtain ⟨N, hN⟩ := burnolPrimeWallThreshold hρhalf
  classical
  set s : Set Nat.Primes := {p : Nat.Primes | (p : ℕ) < N} with hs
  have hsfin : s.Finite :=
    Set.Finite.preimage (Subtype.val_injective.injOn) (Set.finite_Iio N)
  have hsub : Summable (fun x : ↥sᶜ =>
      ‖burnolPoissonInverseCompletionCoefficient y c ρ ((x : Nat.Primes) : ℕ)‖ ^ 2) :=
    hsum.subtype _
  have hcomp : Summable (fun x : ↥sᶜ =>
      Real.exp (2 * δ * Real.log ((((x : Nat.Primes) : ℕ)) : ℝ)) *
        Real.exp (-(2 * y * Real.sqrt (Real.log ((((x : Nat.Primes) : ℕ)) : ℝ)))) /
          ((((x : Nat.Primes) : ℕ)) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) ?_
      (hsub.mul_left (4 / K ^ 2)) |>.congr (fun x => rfl)
    rintro ⟨p, hp⟩
    have hple : N ≤ (p : ℕ) := by
      have : ¬ ((p : ℕ) < N) := hp
      omega
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
      have : (0 : ℕ) < (p : ℕ) := by omega
      exact_mod_cast this
    have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hp2.trans_lt' one_lt_two
    have hLpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos hp1
    have hPN : (N : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hple
    obtain ⟨hge2, hlog⟩ := hN ((p : ℕ) : ℝ) hPN
    have hnum : ((p : ℕ) : ℝ) ^ ρ.re / 2 ≤ ‖((p : ℕ) : ℂ) ^ ρ - 1‖ := by
      have := le_norm_nat_cpow_sub_one hp2 ρ
      linarith
    have hE : 0 < Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) := Real.exp_pos _
    have hexpsq : Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) ^ 2 =
        Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hrpow : (((p : ℕ) : ℝ) ^ ρ.re) ^ 2 =
        Real.exp (2 * δ * Real.log ((p : ℕ) : ℝ)) * ((p : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ ρ.re) 2, ← Real.rpow_mul hppos.le]
      rw [show ((p : ℕ) : ℝ) = Real.exp (Real.log ((p : ℕ) : ℝ)) from
          (Real.exp_log hppos).symm]
      rw [← Real.exp_add, Real.exp_log hppos, Real.rpow_def_of_pos hppos]
      congr 1
      rw [hδ]
      push_cast
      ring
    have hnn : 0 ≤ K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
        (((p : ℕ) : ℝ) ^ ρ.re / 2 / ((p : ℕ) : ℝ)) := by positivity
    have hstep : K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
        (((p : ℕ) : ℝ) ^ ρ.re / 2 / ((p : ℕ) : ℝ)) ≤
        K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
          (‖((p : ℕ) : ℂ) ^ ρ - 1‖ / ((p : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity))
        (by positivity)
    have hval : 4 / K ^ 2 * (K * Real.exp (-(y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) *
        (((p : ℕ) : ℝ) ^ ρ.re / 2 / ((p : ℕ) : ℝ))) ^ 2 =
        Real.exp (2 * δ * Real.log ((p : ℕ) : ℝ)) *
          Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) / ((p : ℕ) : ℝ) := by
      rw [mul_pow, mul_pow, div_pow, div_pow, hexpsq, hrpow]
      field_simp
      ring
    have hlow : Real.exp (2 * δ * Real.log ((p : ℕ) : ℝ)) *
        Real.exp (-(2 * y * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) / ((p : ℕ) : ℝ) ≤
        4 / K ^ 2 * ‖burnolPoissonInverseCompletionCoefficient y c ρ (p : ℕ)‖ ^ 2 := by
      rw [norm_burnolPoissonInverseCompletionCoefficient hp2 hρ0 hρ1, ← hK, ← hval]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hstep 2) (by positivity)
    exact hlow
  exact (Set.Finite.summable_compl_iff hsfin).mp hcomp

/-- **The smooth entrance wall.**  Full prime-log differential regularity of the inverse-completed
jet is exactly the closed left half of the critical strip. -/
theorem burnolPoissonSmoothWall {y : ℝ} (hy : 0 < y) {c ρ : ℂ} (hc : c ≠ 0)
    (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    (∀ k : ℕ, Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) ^ (2 * k) *
        ‖burnolPoissonInverseCompletionCoefficient y c ρ (p : ℕ)‖ ^ 2)) ↔ ρ.re ≤ 1 / 2 := by
  constructor
  · intro hall
    by_contra hlt
    have hhalf : 1 / 2 < ρ.re := lt_of_not_ge hlt
    refine burnolNotSummable_poissonInverseCompletion_of_half_lt_re hy hc hhalf hρ1 ?_
    have h0 := hall 0
    refine h0.congr (fun p => ?_)
    norm_num
  · intro hle k
    exact burnolSummable_poissonInverseCompletion_of_re_le_half hy hρ0 hle k

end RHTower
