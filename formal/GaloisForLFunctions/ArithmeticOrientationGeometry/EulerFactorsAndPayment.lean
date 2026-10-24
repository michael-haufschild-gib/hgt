import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver

/-!
# Euler factors and payment: what Euler-product structure decides

The damped Möbius receiver `μ_ε(d) = μ(d) d^{−ε}` is paid exactly when its repairing ideal in the
critical Wiener algebra `𝒲_{1/2}` is the whole algebra (Arithmetic Orientation Theory). Its Dirichlet
series is the Euler product `Π_p (1 − p^{−ε−s})`, and every local factor `δ₁ − p^{−ε} δ_p` is a unit
of `𝒲_{1/2}` (`|p^{−ε}| < √p`). What can Euler-product structure decide?

* **Tail law** (`receiverBounded_roughMoebius_iff`, `paidIdeal_roughMoebius_eq`). For every finite set
  `P` of primes, deleting the Euler factors at `P` — restricting `μ_ε` to integers prime to `P` —
  changes neither payment nor the repairing ideal nor the obstruction hull. Removing one factor is a
  convolution identity, `μ_ε^{(P)} = (δ₁ − p^{−ε} δ_p) ⋆ μ_ε^{(P ∪ {p})}`
  (`roughMoebius_eq_localFactor_conv`), and units preserve payment. So whether `μ_ε` is paid is a
  property of the tail of its Euler product: it is invisible to any finite set of local factors.
* **Absolute convergence decides** (`isWienerUnit_moebius_of_half_lt`). For `ε > ½` the weight `μ_ε`
  lies in `𝒲_{1/2}` and is a unit, with inverse `d^{−ε}`: the Euler product converges in the algebra.
* **Below and at half damping the product leaves the algebra** (`not_criticalWiener_moebius`). For
  `ε ≤ ½`, `Σ |μ(d)| d^{−ε−½} ≥ Σ_p 1/p = ∞`.

Together: Euler-product structure decides payment only where the product converges absolutely,
`ε > ½`, which is the trivial region. In `0 < ε ≤ ½` every finite truncation of the product is a
unit and therefore carries no information, while the full product is not an element of the
algebra. Repair below half damping must use cancellation across infinitely many primes.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticOrientationTheory TransHorizonIncidenceMechanics BezoutValuationIncidence

/-- The damped Möbius weight with the Euler factors at the primes of `P` deleted. -/
def roughMoebius (P : Finset ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  if ∀ q ∈ P, ¬ q ∣ d then pmPowerDampedRealWeight ε d else 0

theorem roughMoebius_empty (ε : ℝ) : roughMoebius ∅ ε = pmPowerDampedRealWeight ε := by
  funext d; simp [roughMoebius]

theorem pmPowerDampedRealWeight_zero (ε : ℝ) : pmPowerDampedRealWeight ε 0 = 0 := by
  simp [pmPowerDampedRealWeight, moebiusReal]

theorem pmPowerDampedRealWeight_prime_mul {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) (ε : ℝ) :
    pmPowerDampedRealWeight ε (p * m) = -((p : ℝ) ^ (-ε)) * pmPowerDampedRealWeight ε m := by
  have hμ : μ (p * m) = -μ m := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm), ArithmeticFunction.moebius_apply_prime hp]
    ring
  simp only [pmPowerDampedRealWeight, moebiusReal, hμ, Int.cast_neg, Nat.cast_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem pmPowerDampedRealWeight_of_sq_dvd {p n : ℕ} (hp : p.Prime) (h : p * p ∣ n) (ε : ℝ) :
    pmPowerDampedRealWeight ε n = 0 := by
  have hns : ¬ Squarefree n := fun hsq => hp.not_isUnit (hsq p h)
  simp [pmPowerDampedRealWeight, moebiusReal, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]

/-- **Deleting one Euler factor.** For a prime `p ∉ P`, all of `P` prime,
`μ_ε^{(P)} = (δ₁ − p^{−ε} δ_p) ⋆ μ_ε^{(P ∪ {p})}`. -/
theorem roughMoebius_eq_localFactor_conv {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {p : ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (ε : ℝ) :
    roughMoebius P ε =
      RHTower.dirichletConv (localFactorKernel p ((p : ℝ) ^ (-ε))) (roughMoebius (insert p P) ε) := by
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [RHTower.dirichletConv, roughMoebius, pmPowerDampedRealWeight_zero]
  rw [dirichletConv_localFactorKernel hp _ _ hn.ne']
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    have h1 : roughMoebius (insert p P) ε n = 0 := by
      simp only [roughMoebius]
      rw [if_neg]
      push Not
      exact ⟨p, mem_insert_self p P, hpn⟩
    rw [h1, zero_sub]
    obtain ⟨m, rfl⟩ := hpn
    have hm : p * m / p = m := Nat.mul_div_cancel_left m hp.pos
    rw [hm]
    by_cases hpm : p ∣ m
    · have hsq : p * p ∣ p * m := Nat.mul_dvd_mul_left p hpm
      have h2 : roughMoebius (insert p P) ε m = 0 := by
        simp only [roughMoebius]
        rw [if_neg]
        push Not
        exact ⟨p, mem_insert_self p P, hpm⟩
      rw [h2, mul_zero, neg_zero]
      simp only [roughMoebius, pmPowerDampedRealWeight_of_sq_dvd hp hsq, ite_self]
    · -- `q ∣ p m ↔ q ∣ m` for the primes `q ∈ P`
      have hiff : (∀ q ∈ P, ¬ q ∣ p * m) ↔ ∀ q ∈ insert p P, ¬ q ∣ m := by
        constructor
        · intro h q hq
          rcases mem_insert.mp hq with rfl | hq
          · exact hpm
          · exact fun hqm => h q hq (Dvd.dvd.mul_left hqm p)
        · intro h q hq hqpm
          have hqp : q ≠ p := fun e => hpP (e ▸ hq)
          rcases (Nat.Prime.dvd_mul (hP q hq)).mp hqpm with hqp' | hqm
          · exact hqp ((Nat.prime_dvd_prime_iff_eq (hP q hq) hp).mp hqp')
          · exact h q (mem_insert_of_mem hq) hqm
      simp only [roughMoebius]
      by_cases hc : ∀ q ∈ insert p P, ¬ q ∣ m
      · rw [if_pos (hiff.mpr hc), if_pos hc, pmPowerDampedRealWeight_prime_mul hp hpm]
        ring
      · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
        ring
  · rw [if_neg hpn, mul_zero, sub_zero]
    simp only [roughMoebius]
    have hiff : (∀ q ∈ P, ¬ q ∣ n) ↔ ∀ q ∈ insert p P, ¬ q ∣ n := by
      constructor
      · intro h q hq
        rcases mem_insert.mp hq with rfl | hq
        · exact hpn
        · exact h q hq
      · exact fun h q hq => h q (mem_insert_of_mem hq)
    by_cases hc : ∀ q ∈ P, ¬ q ∣ n
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

theorem summable_abs_roughMoebius_div (P : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun d : ℕ => |roughMoebius P ε d / d| :=
  (summable_abs_moebius_div hε).of_nonneg_of_le (fun _ => abs_nonneg _) fun d => by
    unfold roughMoebius; split_ifs <;> simp

/-- The local factor `δ₁ − p^{−ε} δ_p` is a unit of the critical Wiener monoid for `ε ≥ 0`. -/
theorem isWienerUnit_moebiusLocalFactor {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 ≤ ε) :
    IsWienerUnit (localFactorKernel p ((p : ℝ) ^ (-ε))) := by
  rw [isWienerUnit_localFactor_iff hp]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h1 : (p : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1.le (by linarith)
  have h2 : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hp1
  rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  linarith

/-- **The tail law of payment.** For every finite set `P` of primes, the damped Möbius receiver is
paid iff its restriction to integers prime to `P` is. -/
theorem receiverBounded_roughMoebius_iff (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) {ε : ℝ}
    (hε : 0 < ε) :
    ReceiverBounded (roughMoebius P ε) ↔ ReceiverBounded (pmPowerDampedRealWeight ε) := by
  induction P using Finset.induction_on with
  | empty => rw [roughMoebius_empty]
  | insert p P hpP ih =>
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hp : p.Prime := hP p (mem_insert_self p P)
    rw [← ih hP', roughMoebius_eq_localFactor_conv hP' hp hpP ε,
      receiverBounded_dirichletConv_iff_of_isWienerUnit (isWienerUnit_moebiusLocalFactor hp hε.le)
        (summable_abs_roughMoebius_div _ hε)]

theorem paidIdeal_congr {c c' : ℕ → ℝ} (h : c = c') (hc : Summable fun d : ℕ => |c d / d|)
    (hc' : Summable fun d : ℕ => |c' d / d|) : paidIdeal c hc = paidIdeal c' hc' := by
  subst h; rfl

/-- **The repairing ideal does not see finitely many Euler factors.** -/
theorem paidIdeal_roughMoebius_eq (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) {ε : ℝ} (hε : 0 < ε) :
    paidIdeal (roughMoebius P ε) (summable_abs_roughMoebius_div P hε) =
      paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) := by
  induction P using Finset.induction_on with
  | empty => exact paidIdeal_congr (roughMoebius_empty ε) _ _
  | insert p P hpP ih =>
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hp : p.Prime := hP p (mem_insert_self p P)
    rw [← ih hP', paidIdeal_congr (roughMoebius_eq_localFactor_conv hP' hp hpP ε) _
      (summable_abs_dirichletConv_div (isWienerUnit_moebiusLocalFactor hp hε.le).1
        (summable_abs_roughMoebius_div (insert p P) hε)),
      paidIdeal_unit _ _ (isWienerUnit_moebiusLocalFactor hp hε.le)]

/-- **The obstruction hull does not see finitely many Euler factors.** -/
theorem obstructionHull_roughMoebius_eq (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) {ε : ℝ}
    (hε : 0 < ε) :
    obstructionHull (roughMoebius P ε) (summable_abs_roughMoebius_div P hε) =
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) := by
  unfold obstructionHull
  rw [paidIdeal_roughMoebius_eq P hP hε]

/-! ### Absolute convergence -/

theorem criticalWiener_dampedPower {ε : ℝ} (hε : 1 / 2 < ε) :
    CriticalWiener fun d : ℕ => (d : ℝ) ^ (-ε) := by
  unfold CriticalWiener
  refine (Real.summable_nat_rpow.mpr (by linarith : -ε + -(1 / 2) < -1)).congr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · norm_num [Real.zero_rpow (show -ε ≠ 0 by linarith),
      Real.zero_rpow (show -ε + -(1 / 2 : ℝ) ≠ 0 by linarith)]
  · rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), ← Real.rpow_add (by exact_mod_cast hd)]

theorem criticalWiener_moebius_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    CriticalWiener (pmPowerDampedRealWeight ε) := by
  refine (criticalWiener_dampedPower hε).of_nonneg_of_le (fun _ => by positivity) fun d => ?_
  rw [pmPowerDampedRealWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hμ : |moebiusReal d| ≤ 1 := by
    simp only [moebiusReal]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h0 : 0 ≤ (d : ℝ) ^ (-ε) * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  calc |moebiusReal d| * (d : ℝ) ^ (-ε) * (d : ℝ) ^ (-(1 / 2 : ℝ))
      ≤ 1 * (d : ℝ) ^ (-ε) * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hμ h0
    _ = (d : ℝ) ^ (-ε) * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [one_mul]

/-- **Above half damping the Euler product converges in the algebra**: `μ_ε` is a unit of the
critical Wiener monoid with inverse `d^{−ε}`. -/
theorem isWienerUnit_moebius_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    IsWienerUnit (pmPowerDampedRealWeight ε) := by
  refine ⟨criticalWiener_moebius_of_half_lt hε, fun d => (d : ℝ) ^ (-ε),
    criticalWiener_dampedPower hε, fun n hn => ?_⟩
  unfold RHTower.dirichletConv pmPowerDampedRealWeight unitKernel
  have hterm : ∀ d ∈ n.divisors,
      moebiusReal d * (d : ℝ) ^ (-ε) * ((n / d : ℕ) : ℝ) ^ (-ε) = moebiusReal d * (n : ℝ) ^ (-ε) := by
    intro d hd
    rw [mul_assoc, ← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← Nat.cast_mul,
      Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [sum_congr rfl hterm, ← sum_mul]
  have hsum : ∑ d ∈ n.divisors, moebiusReal d = if n = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℝ))
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    push_cast at h
    simpa [moebiusReal] using h
  rw [hsum]
  split_ifs with h1
  · subst h1; simp
  · simp

/-- **At and below half damping the product leaves the algebra.** -/
theorem not_criticalWiener_moebius {ε : ℝ} (hε : ε ≤ 1 / 2) :
    ¬ CriticalWiener (pmPowerDampedRealWeight ε) := by
  intro h
  unfold CriticalWiener at h
  have hp := h.comp_injective (Subtype.val_injective : Function.Injective
    (Subtype.val : Nat.Primes → ℕ))
  apply Nat.Primes.not_summable_one_div
  refine hp.of_nonneg_of_le (fun p => by positivity) fun p => ?_
  have hpp : (p : ℕ).Prime := p.2
  have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hpp.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
  simp only [Function.comp, pmPowerDampedRealWeight, moebiusReal,
    ArithmeticFunction.moebius_apply_prime hpp, Int.cast_neg, Int.cast_one, abs_mul, abs_neg,
    abs_one, one_mul, abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
  rw [← Real.rpow_add hp0, one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

end GaloisForLFunctions.ArithmeticOrientationGeometry
