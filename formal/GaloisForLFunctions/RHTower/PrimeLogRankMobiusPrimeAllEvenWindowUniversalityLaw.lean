import GaloisForLFunctions.RHTower.DirichletPolynomialSincEnergy
import GaloisForLFunctions.RHTower.PrimeLogRankMobiusDistortionUniversalityLaw
import GaloisForLFunctions.RHTower.SquareSupportPrimeMass

/-!
# Prime-log rank, Möbius distortion, and all even prime windows

At every positive moment order, unique prime-power factorization transfers one finite prime
packet simultaneously into phase rank, critical Möbius distortion, exact random even moments,
and deterministic finite-window lower mass.
-/

open Complex MeasureTheory intervalIntegral Finset Filter Topology
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- Every prime power `p^k` occurs in the `k`-fold product support of a set containing `p`. -/
theorem prime_pow_mem_powSupport
    (P : Finset ℕ) {p : ℕ} (hpP : p ∈ P) :
    ∀ k : ℕ, p ^ k ∈ powSupport P k := by
  intro k
  induction k with
  | zero => simp [powSupport]
  | succ k ih =>
      rw [powSupport]
      exact Finset.mem_image.mpr
        ⟨(p ^ k, p), by simp [ih, hpP], by simp [pow_succ]⟩

/-- On prime support, the convolution fiber over `p^k` is the single constant factorization,
so its coefficient is `(a p)^k`. -/
theorem powConv_primePower
    (a : ℕ → ℝ) (P : Finset ℕ) (hprime : ∀ q ∈ P, q.Prime)
    {p : ℕ} (hpP : p ∈ P) :
    ∀ k : ℕ, powConv a P k (p ^ k) = (a p) ^ k := by
  intro k
  induction k with
  | zero => simp [powConv]
  | succ k ih =>
      have hp : p.Prime := hprime p hpP
      have hfilter :
          (powSupport P k ×ˢ P).filter
              (fun jq => jq.1 * jq.2 = p ^ (k + 1)) =
            {(p ^ k, p)} := by
        ext jq
        rcases jq with ⟨j, q⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hj, hqP⟩, hjq⟩
          have hq : q.Prime := hprime q hqP
          have hqdiv : q ∣ p ^ (k + 1) := by
            rw [← hjq]
            exact dvd_mul_left q j
          have hqp : q = p :=
            (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdiv)
          subst q
          have hjp : j = p ^ k := by
            apply Nat.mul_right_cancel hp.pos
            simpa [pow_succ] using hjq
          simp [hjp]
        · intro hjq
          injection hjq with hj hp'
          subst j
          subst p
          exact ⟨⟨prime_pow_mem_powSupport P hpP k, hpP⟩, by simp [pow_succ]⟩
      rw [powConv]
      unfold dpolyConv
      rw [hfilter]
      simp only [Finset.sum_singleton, ih, pow_succ]

/-- The order-dependent prime weight whose `k`-fold product is `p⁻¹/²`. -/
def primeEvenMomentCoeff (k n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / (2 * (k : ℝ))))

/-- The normalized `k`-fold prime-power convolution coefficient is exactly `p⁻¹/²`. -/
theorem powConv_primeEvenMomentCoeff_primePower
    (P : Finset ℕ) (hprime : ∀ q ∈ P, q.Prime)
    {p k : ℕ} (hpP : p ∈ P) (hk : k ≠ 0) :
    powConv (primeEvenMomentCoeff k) P k (p ^ k) =
      (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [powConv_primePower (primeEvenMomentCoeff k) P hprime hpP k]
  unfold primeEvenMomentCoeff
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp

/-- **Prime-packet all-even-window universality law.**  At every positive order `k`, one finite
prime packet simultaneously carries independent logarithmic phases, rank-controlled critical
Möbius distortion, exact Steinhaus `2k`-moment diagonal, full reciprocal-prime mass, and its
deterministic finite-window survival, with the long-window average converging to the exact random
moment. -/
theorem primeLogRank_mobiusDistortion_primeAllEvenWindow
    (N k : ℕ) (hN : 2 ≤ N) (hk : k ≠ 0) (T : ℝ) (hT : 0 < T) :
    LinearIndependent ℤ
        (fun p : ((N + 1).primesBelow : Finset ℕ) => Real.log (p : ℕ)) ∧
      1 + 4 * ((Nat.primeCounting' (N + 1) : ℝ) / (N : ℝ)) ≤
        finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (N + 1)) ∧
      (∫ ω,
          ‖∑ p ∈ Nat.primesBelow (N + 1),
            (primeEvenMomentCoeff k p : ℂ) * X p ω‖ ^ (2 * k)
            ∂steinhausMeasure =
        ∑ j ∈ powSupport (Nat.primesBelow (N + 1)) k,
          powConv (primeEvenMomentCoeff k)
            (Nat.primesBelow (N + 1)) k j ^ 2) ∧
      (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ)⁻¹) ≤
        ∫ ω,
          ‖∑ p ∈ Nat.primesBelow (N + 1),
            (primeEvenMomentCoeff k p : ℂ) * X p ω‖ ^ (2 * k)
            ∂steinhausMeasure ∧
      (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ)⁻¹) -
          dpolySincOffDiagonalEnergy
            (powConv (primeEvenMomentCoeff k)
              (Nat.primesBelow (N + 1)) k)
            (powSupport (Nat.primesBelow (N + 1)) k) T ≤
        (∫ t in (-T)..T,
          ‖dpoly (primeEvenMomentCoeff k)
            (Nat.primesBelow (N + 1)) t‖ ^ (2 * k)) / (2 * T) ∧
      (∀ A U : ℝ, 0 < U →
        (∑ p ∈ Nat.primesBelow (N + 1), (p : ℝ)⁻¹) -
            dpolyWindowOffDiagonalEnergy
              (powConv (primeEvenMomentCoeff k)
                (Nat.primesBelow (N + 1)) k)
              (powSupport (Nat.primesBelow (N + 1)) k) U ≤
          (∫ t in A..(A + U),
            ‖dpoly (primeEvenMomentCoeff k)
              (Nat.primesBelow (N + 1)) t‖ ^ (2 * k)) / U) ∧
      Tendsto
        (fun U : ℝ =>
          (∫ t in (0 : ℝ)..U,
            ‖dpoly (primeEvenMomentCoeff k)
              (Nat.primesBelow (N + 1)) t‖ ^ (2 * k)) / U)
        atTop
        (𝓝 (∫ ω,
          ‖∑ p ∈ Nat.primesBelow (N + 1),
            (primeEvenMomentCoeff k p : ℂ) * X p ω‖ ^ (2 * k)
            ∂steinhausMeasure)) := by
  let P := Nat.primesBelow (N + 1)
  have hprime : ∀ p ∈ P, p.Prime :=
    fun p hp => Nat.prime_of_mem_primesBelow hp
  have hpositive : ∀ p ∈ P, 1 ≤ p :=
    fun p hp => (hprime p hp).one_le
  have hmass :
      (∑ p ∈ P, (p : ℝ)⁻¹) ≤
        ∑ j ∈ powSupport P k,
          powConv (primeEvenMomentCoeff k) P k j ^ 2 := by
    simpa only [one_pow, one_mul] using
      (primeMass_le_pow_sum_of_forced
        (S := powSupport P k) (P := P)
        (b := powConv (primeEvenMomentCoeff k) P k)
        (δ := 1) (m := k) hk zero_le_one
        (fun p hp => prime_pow_mem_powSupport P hp k)
        (fun p hp => by
          rw [one_mul,
            powConv_primeEvenMomentCoeff_primePower P hprime hp hk,
            abs_of_pos
              (Real.rpow_pos_of_pos (by exact_mod_cast (hprime p hp).pos) _)]))
  have hrandom :=
    integral_normPow_dpoly (primeEvenMomentCoeff k) P hpositive k
  have herror :=
    evenMoment_symmetric_independence_error_le
      (primeEvenMomentCoeff k) P hpositive k T hT
  have hdeterministic :
      (∑ p ∈ P, (p : ℝ)⁻¹) -
          dpolySincOffDiagonalEnergy
            (powConv (primeEvenMomentCoeff k) P k) (powSupport P k) T ≤
        (∫ t in (-T)..T,
          ‖dpoly (primeEvenMomentCoeff k) P t‖ ^ (2 * k)) / (2 * T) := by
    have hlower := neg_le_of_abs_le herror
    rw [hrandom] at hlower
    linarith
  have hshifted : ∀ A U : ℝ, 0 < U →
      (∑ p ∈ P, (p : ℝ)⁻¹) -
          dpolyWindowOffDiagonalEnergy
            (powConv (primeEvenMomentCoeff k) P k) (powSupport P k) U ≤
        (∫ t in A..(A + U),
          ‖dpoly (primeEvenMomentCoeff k) P t‖ ^ (2 * k)) / U := by
    intro A U hU
    have herrorShifted :=
      evenMoment_window_independence_error_le
        (primeEvenMomentCoeff k) P hpositive k A U hU
    have hlower := neg_le_of_abs_le herrorShifted
    rw [hrandom] at hlower
    linarith
  have hpacket := primeLogRank_and_mobiusPhaseDistortion N hN
  have hbohr :=
    tendsto_evenMoment_average_steinhaus
      (primeEvenMomentCoeff k) P hpositive k
  exact ⟨hpacket.1, hpacket.2, by simpa only [P] using hrandom,
    by rw [hrandom]; exact hmass, by simpa only [P] using hdeterministic,
    by simpa only [P] using hshifted, by simpa only [P] using hbohr⟩

end

end RHTower
