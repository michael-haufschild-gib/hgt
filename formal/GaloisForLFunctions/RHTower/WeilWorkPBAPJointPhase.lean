import GaloisForLFunctions.RHTower.WeilWorkPBAPJointConvex
import GaloisForLFunctions.HTGeometry.SmoothNumbers
import GaloisForLFunctions.HTGeometry.InfiniteTorusForwardDensity
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier

/-!
# Sharp mass threshold for simultaneous shifted-prime phase cancellation

For every prime `p ≥ 5`, every lower frequency threshold and every total
correction mass `M`, exact nonnegative finite cancellation of all phases
`log n - log p / 2`, `2 ≤ n < p`, exists if and only if `M > 1`.

Unique factorization supplies the dense phase flow and forbids simultaneous
negative endpoint phases at `n = 2, 3`. No RH, Weil positivity, or external
producer is assumed. The theorem controls total correction weight only; it
makes no claim about logarithmic frequency cost or full Weil energy.
-/

open Filter Topology MeasureTheory
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilWorkPBAP

private def jointExponent (p : Nat.Primes) (n : ℕ) : Nat.Primes →₀ ℤ :=
  (primeExponentVector n).mapRange (fun k : ℕ => 2*(k : ℤ)) (by simp) - Finsupp.single p 1

private def primeLogs (p : Nat.Primes) : ℝ := Real.log (p : ℕ)

private theorem detuning_linear (e : Nat.Primes →₀ ℤ) :
    characterDetuning e primeLogs = (Finsupp.linearCombination ℤ primeLogs) e := by
  simp [characterDetuning, Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul]

private theorem jointExponent_detuning (p : Nat.Primes) {n : ℕ} (hn : n ≠ 0) :
    characterDetuning (jointExponent p n) primeLogs = 2 * Real.log n - Real.log (p : ℕ) := by
  rw [detuning_linear, jointExponent, map_sub, Finsupp.linearCombination_single, one_smul]
  have he : (Finsupp.linearCombination ℤ primeLogs)
      ((primeExponentVector n).mapRange (fun k : ℕ => 2*(k : ℤ)) (by simp)) =
        2*Real.log n := by
    rw [← detuning_linear]
    change ((primeExponentVector n).mapRange (fun k : ℕ => 2*(k : ℤ)) (by simp)).sum
      (fun q k => (k : ℝ)*primeLogs q) = _
    rw [Finsupp.sum_mapRange_index]
    · rw [log_nat_eq_sum_factorization hn]
      simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, primeLogs,
        Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    · intro q
      simp
  rw [he]
  rfl

private theorem jointExponent_at_prime (p : Nat.Primes) {n : ℕ}
    (hn : 0 < n) (hnp : n < (p : ℕ)) : jointExponent p n p = -1 := by
  have hf : n.factorization (p : ℕ) = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hn hnp)
  simp [jointExponent, primeExponentVector_apply, hf]

private def oppositePrimePoint (p : Nat.Primes) : UnitAddTorus Nat.Primes :=
  fun q => if q = p then ((1/2 : ℝ) : UnitAddCircle) else 0

private theorem jointExponent_oppositePrimePoint (p : Nat.Primes) {n : ℕ}
    (hn : 0 < n) (hnp : n < (p : ℕ)) :
    torusCharacter (jointExponent p n) (oppositePrimePoint p) = -1 := by
  classical
  rw [torusCharacter_apply]
  rw [Finset.prod_eq_single p]
  · rw [oppositePrimePoint, if_pos rfl, jointExponent_at_prime p hn hnp,
      fourier_coe_apply]
    have he : 2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) * ((1/2 : ℝ) : ℂ) / (1 : ℝ) =
        -((Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  · intro q _ hq
    rw [oppositePrimePoint, if_neg hq]
    exact fourier_eval_zero _
  · intro hp
    have hmem : p ∈ (jointExponent p n).support :=
      Finsupp.mem_support_iff.mpr (by rw [jointExponent_at_prime p hn hnp]; norm_num)
    exact False.elim (hp hmem)

private theorem primeLogs_independent : RationallyIndependentSequence primeLogs :=
  rationallyIndependentSequence_of_linearIndependent_int logPrime_linearIndependent_int


def jointFrequency (p : Nat.Primes) (i : Fin ((p : ℕ)-2)) : ℝ :=
  2 * Real.log (i.val+2 : ℕ) - Real.log (p : ℕ)

private theorem joint_index_lt (p : Nat.Primes) (i : Fin ((p : ℕ)-2)) :
    i.val + 2 < (p : ℕ) := by omega

private theorem jointFrequency_nonzero (p : Nat.Primes) (i : Fin ((p : ℕ)-2)) :
    jointFrequency p i ≠ 0 := by
  intro h
  have he : jointExponent p (i.val+2) = 0 :=
    (characterDetuning_eq_zero_iff primeLogs_independent _).mp
      ((jointExponent_detuning p (by omega : i.val+2 ≠ 0)).trans h)
  have hp := congrArg (fun e : Nat.Primes →₀ ℤ => e p) he
  rw [jointExponent_at_prime p (by omega) (joint_index_lt p i)] at hp
  norm_num at hp

private theorem jointFrequency_injective (p : Nat.Primes) :
    Function.Injective (jointFrequency p) := by
  intro i j hij
  have hl : Real.log (i.val+2 : ℕ) = Real.log (j.val+2 : ℕ) := by
    unfold jointFrequency at hij
    linarith
  have he := Real.log_injOn_pos (by positivity : (0:ℝ) < (i.val+2 : ℕ))
    (by positivity : (0:ℝ) < (j.val+2 : ℕ)) hl
  have hn : i.val+2 = j.val+2 := by exact_mod_cast he
  apply Fin.ext
  omega

private theorem jointFrequency_not_opposite (p : Nat.Primes)
    (i j : Fin ((p : ℕ)-2)) : jointFrequency p i ≠ -jointFrequency p j := by
  intro h
  have hd : characterDetuning (jointExponent p (i.val+2) + jointExponent p (j.val+2))
      primeLogs = 0 := by
    rw [detuning_linear, map_add, ← detuning_linear, ← detuning_linear,
      jointExponent_detuning p (by omega), jointExponent_detuning p (by omega)]
    change jointFrequency p i + jointFrequency p j = 0
    linarith
  have he := (characterDetuning_eq_zero_iff primeLogs_independent _).mp hd
  have hp := congrArg (fun e : Nat.Primes →₀ ℤ => e p) he
  simp only [Finsupp.add_apply, jointExponent_at_prime p (by omega) (joint_index_lt p i),
    jointExponent_at_prime p (by omega) (joint_index_lt p j), Finsupp.zero_apply] at hp
  norm_num at hp

private def jointTorusReadout (p : Nat.Primes) (z : UnitAddTorus Nat.Primes)
    (i : Fin ((p : ℕ)-2)) : ℝ := (torusCharacter (jointExponent p (i.val+2)) z).re

private theorem continuous_jointTorusReadout (p : Nat.Primes) :
    Continuous (jointTorusReadout p) :=
  continuous_pi fun i => Complex.continuous_re.comp
    (torusCharacter (jointExponent p (i.val+2))).continuous

private theorem jointTorusReadout_flow (p : Nat.Primes) (t : ℝ) :
    jointTorusReadout p (clockPhasePoint primeLogs t) =
      fun i => Real.cos (jointFrequency p i*t) := by
  funext i
  rw [jointTorusReadout, torusCharacter_clockPhasePoint,
    jointExponent_detuning p (by omega)]
  rw [Complex.exp_ofReal_mul_I_re]
  congr 1
  unfold jointFrequency
  ring

private theorem jointTorusReadout_opposite (p : Nat.Primes) :
    jointTorusReadout p (oppositePrimePoint p) = fun _ => -1 := by
  funext i
  rw [jointTorusReadout, jointExponent_oppositePrimePoint p (by omega) (joint_index_lt p i)]
  rfl

theorem jointFrequency_opposite_in_closure (p : Nat.Primes) (R : ℝ) :
    (fun _ : Fin ((p : ℕ)-2) => (-1:ℝ)) ∈ closure
      ((fun t i => Real.cos (jointFrequency p i*t)) '' Set.Ioi R) := by
  have hd := dense_forwardOrbit primeLogs_independent (R+1)
  have he := image_closure_subset_closure_image (continuous_jointTorusReadout p)
    (s := {z | ∃ t, R+1 ≤ t ∧ clockPhasePoint primeLogs t = z})
    ⟨oppositePrimePoint p, hd _, rfl⟩
  rw [jointTorusReadout_opposite] at he
  refine closure_mono ?_ he
  rintro _ ⟨z, ⟨t, ht, rfl⟩, rfl⟩
  refine ⟨t, (by change R<t; linarith), ?_⟩
  exact (jointTorusReadout_flow p t).symm

/-- Exact cancellation at every shifted integer node below the prime cut. -/
theorem exists_joint_phase_correction (p : Nat.Primes) (R M : ℝ) (hM : 1 < M) :
    ∃ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, R < t i) ∧ (∑ i, w i) = M ∧
      ∀ n : ℕ, 2 ≤ n → n < (p : ℕ) →
        1 + (∑ i, w i * Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i)) = 0 := by
  obtain ⟨ι, hi, w, t, hw, ht, hsum, hcos⟩ := exists_exact_cosine_correction
    (jointFrequency p) (jointFrequency_nonzero p) (jointFrequency_injective p)
    (jointFrequency_not_opposite p) (R/2) M hM (jointFrequency_opposite_in_closure p (R/2))
  letI : Fintype ι := hi
  refine ⟨ι, hi, w, (fun i => 2*t i), hw, (fun i => by linarith [ht i]), hsum, ?_⟩
  intro n hn hnp
  let j : Fin ((p : ℕ)-2) := ⟨n-2, by omega⟩
  have hj : j.val+2 = n := by dsimp [j]; omega
  have he := hcos j
  have harg : ∀ i, (Real.log n - Real.log (p : ℕ)/2)*(2*t i) = jointFrequency p j*t i := by
    intro i
    rw [jointFrequency, hj]
    ring
  simp only [harg, he]
  ring

/-- Two of the shifted prime phases can never both equal the negative endpoint. -/
theorem joint_no_common_antiphase (p : Nat.Primes) (hp : 5 ≤ (p : ℕ)) (t : ℝ) :
    ¬(Real.cos ((2*Real.log 2 - Real.log (p : ℕ))*t) = -1 ∧
      Real.cos ((2*Real.log 3 - Real.log (p : ℕ))*t) = -1) := by
  rintro ⟨h2, h3⟩
  have ht : t ≠ 0 := by intro ht; subst t; norm_num at h2
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp h2
  obtain ⟨l, hl⟩ := Real.cos_eq_neg_one_iff.mp h3
  let u : ℤ := 2*l+1
  let v : ℤ := 2*k+1
  have hrel : (u : ℝ)*(2*Real.log 2 - Real.log (p : ℕ)) -
      (v : ℝ)*(2*Real.log 3 - Real.log (p : ℕ)) = 0 := by
    apply (mul_eq_zero.mp (show ((u : ℝ)*(2*Real.log 2 - Real.log (p : ℕ)) -
      (v : ℝ)*(2*Real.log 3 - Real.log (p : ℕ)))*t = 0 from ?_)).resolve_right ht
    dsimp [u, v]
    push_cast
    linear_combination -(2*(l : ℝ)+1)*hk + (2*(k : ℝ)+1)*hl
  have hd : characterDetuning (u • jointExponent p 2 - v • jointExponent p 3) primeLogs = 0 := by
    rw [detuning_linear, map_sub, map_zsmul, map_zsmul, ← detuning_linear,
      ← detuning_linear, jointExponent_detuning p (by norm_num : (2:ℕ) ≠ 0),
      jointExponent_detuning p (by norm_num : (3:ℕ) ≠ 0)]
    simpa only [zsmul_eq_mul, Nat.cast_ofNat] using hrel
  have he := (characterDetuning_eq_zero_iff primeLogs_independent _).mp hd
  let q : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hpq : p ≠ q := by
    intro he
    have hv := congrArg (fun z : Nat.Primes => (z : ℕ)) he
    dsimp [q] at hv
    omega
  have he2 : jointExponent p 2 q = 2 := by
    simp [jointExponent, primeExponentVector_apply, Nat.prime_two.factorization,
      q, Ne.symm hpq]
  have he3 : jointExponent p 3 q = 0 := by
    simp [jointExponent, primeExponentVector_apply, Nat.prime_three.factorization,
      q, Ne.symm hpq]
  have hval := congrArg (fun e : Nat.Primes →₀ ℤ => e q) he
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, he2, he3, Finsupp.zero_apply,
    zsmul_eq_mul, mul_zero, sub_zero] at hval
  dsimp [u] at hval
  omega

/-- Nonnegative exact correction weights have total mass strictly greater than one. -/
theorem joint_phase_mass_gt_one (p : Nat.Primes) (hp : 5 ≤ (p : ℕ))
    {ι : Type} [Fintype ι] (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ n : ℕ, 2 ≤ n → n < (p : ℕ) →
      1 + (∑ i, w i * Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i)) = 0) :
    1 < ∑ i, w i := by
  classical
  have hc2 := hc 2 le_rfl (by omega)
  have hlo : -(∑ i, w i) ≤ ∑ i, w i * Real.cos ((Real.log 2 - Real.log (p : ℕ)/2)*t i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have he := Real.neg_one_le_cos ((Real.log 2 - Real.log (p : ℕ)/2)*t i)
    nlinarith [hw i]
  have hge : 1 ≤ ∑ i, w i := by linarith
  by_contra hlt
  have hmass : (∑ i, w i) = 1 := le_antisymm (not_lt.mp hlt) hge
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra hn
    push Not at hn
    have hw0 : ∀ i, w i = 0 := fun i => le_antisymm (hn i) (hw i)
    simp [hw0] at hmass
  have hminus (n : ℕ) (hn : 2 ≤ n) (hnp : n < (p : ℕ)) :
      Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i) = -1 := by
    have hsum : (∑ j, w j * (1+Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t j))) = 0 := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hmass]
      exact hc n hn hnp
    have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
        0 ≤ w j * (1+Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t j)) := by
      intro j _
      have hx := Real.neg_one_le_cos ((Real.log n - Real.log (p : ℕ)/2)*t j)
      exact mul_nonneg (hw j) (by linarith)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
    have hz' := (mul_eq_zero.mp hz).resolve_left hi.ne'
    linarith
  apply joint_no_common_antiphase p hp (t i/2)
  constructor
  · rw [show (2*Real.log 2 - Real.log (p : ℕ))*(t i/2) =
      (Real.log 2 - Real.log (p : ℕ)/2)*t i by ring]
    exact hminus 2 le_rfl (by omega)
  · rw [show (2*Real.log 3 - Real.log (p : ℕ))*(t i/2) =
      (Real.log 3 - Real.log (p : ℕ)/2)*t i by ring]
    exact hminus 3 (by omega) (by omega)

/-- Complete mass classification, including arbitrary lower frequency thresholds. -/
theorem joint_phase_correction_iff (p : Nat.Primes) (hp : 5 ≤ (p : ℕ)) (R M : ℝ) :
    (∃ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, R < t i) ∧ (∑ i, w i) = M ∧
      ∀ n : ℕ, 2 ≤ n → n < (p : ℕ) →
        1 + (∑ i, w i * Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i)) = 0) ↔ 1 < M := by
  constructor
  · rintro ⟨ι, hi, w, t, hw, _, hm, hc⟩
    letI : Fintype ι := hi
    rw [← hm]
    exact joint_phase_mass_gt_one p hp w t hw hc
  · exact exists_joint_phase_correction p R M

end RHTower.WeilWorkPBAP
