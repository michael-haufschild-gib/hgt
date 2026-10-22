import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSwapBulkStratification

/-!
# Prime-square conormal sign wall for the theta-likelihood swap bulk

Prime shells have strict negative upper-half-plane current throughout the closed nonnegative
likelihood quadrant. This file attacks the first composite stratum. A prime-square fibre has two
reflected endpoint modes and one zero-rapidity diagonal mode. The diagonal changes shell value but
not its derivative, producing an exact sign wall.

At `pi / log p + i y`, current is a positive scalar times diagonal mass minus hyperbolically
amplified endpoint mass. On either normal-crossing face, current divided by boundary coordinate
has a strictly positive right limit. Hence every prime-square shell has positive current
arbitrarily near the face, refuting universal nonpositive composite orientation and isolating the
square-diagonal correction any subsequent RH current must retain.

All statements are exact and unconditional. No estimate, computation, or RH hypothesis is used.
-/

open Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- The first three powers of a prime are strictly increasing. -/
theorem prime_lt_sq_and_sq_lt_cube {p : ℕ} (hp : p.Prime) :
    p < p ^ (2 : ℕ) ∧ p ^ (2 : ℕ) < p ^ (3 : ℕ) := by
  refine ⟨?_, ?_⟩
  · calc
      p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
      _ = p ^ (2 : ℕ) := by ring
  · calc
      p ^ (2 : ℕ) < p ^ (2 : ℕ) * p := lt_mul_of_one_lt_right (pow_pos hp.pos 2) hp.one_lt
      _ = p ^ (3 : ℕ) := by ring

theorem thetaPositiveFactorPairs_prime_sq {p : ℕ} (hp : p.Prime) :
    thetaPositiveFactorPairs (p ^ (2 : ℕ)) =
      {(0, p ^ (2 : ℕ) - 1), (p - 1, p - 1), (p ^ (2 : ℕ) - 1, 0)} := by
  ext q
  constructor
  · intro hq
    have hprod : (q.1 + 1) * (q.2 + 1) = p ^ (2 : ℕ) :=
      (Finset.mem_filter.mp hq).2
    have hdvd : q.1 + 1 ∣ p ^ (2 : ℕ) := ⟨q.2 + 1, hprod.symm⟩
    obtain ⟨i, hi, hqi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases q with ⟨a, b⟩
    simp only at hprod hqi
    interval_cases i
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [pow_zero] at hqi
      left
      have hb : b + 1 = p ^ (2 : ℕ) := by simpa [hqi] using hprod
      apply Prod.ext <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      simp only [pow_one] at hqi
      right
      left
      have hab : b + 1 = p := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        simpa [pow_two, hqi] using hprod
      apply Prod.ext <;> omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      right
      have hb : b + 1 = 1 := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
        simpa [hqi] using hprod
      apply Prod.ext <;> omega
  · intro hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · have hp0 : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr
        · exact pow_pos hp.pos 2
        · omega
      · omega
    · have hp2 : 2 ≤ p := hp.two_le
      have hpp : p < p ^ (2 : ℕ) := by
        calc p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
          _ = p ^ (2 : ℕ) := by ring
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr <;> omega
      · rw [Nat.sub_add_cancel hp.pos]
        ring
    · have hp0 : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr
        · omega
        · exact pow_pos hp.pos 2
      · omega

theorem thetaFactorPairLogDisplacement_primeSq_left {p : ℕ} (hp : p.Prime) :
    thetaFactorPairLogDisplacement (0, p ^ (2 : ℕ) - 1) = -Real.log p := by
  unfold thetaFactorPairLogDisplacement
  simp only [Nat.zero_add, Nat.cast_one, Real.log_one, zero_sub, neg_div]
  have hp0 : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p ^ (2 : ℕ)), Nat.cast_pow, Real.log_pow]
  norm_num

theorem thetaFactorPairLogDisplacement_primeSq_central {p : ℕ} (hp : p.Prime) :
    thetaFactorPairLogDisplacement (p - 1, p - 1) = 0 := by
  unfold thetaFactorPairLogDisplacement
  rw [Nat.sub_add_cancel hp.pos]
  ring

theorem thetaFactorPairLogDisplacement_primeSq_right {p : ℕ} (hp : p.Prime) :
    thetaFactorPairLogDisplacement (p ^ (2 : ℕ) - 1, 0) = Real.log p := by
  unfold thetaFactorPairLogDisplacement
  simp only [Nat.zero_add, Nat.cast_one, Real.log_one, sub_zero]
  have hp0 : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p ^ (2 : ℕ)), Nat.cast_pow, Real.log_pow]
  norm_num

def thetaCuspLikelihoodPrimeSquareEndpointScale (p : ℕ) (B D : ℝ) : ℝ :=
  B * thetaCuspLikelihoodScaledBoundaryTerm (p ^ (2 : ℕ)) D +
    D * thetaCuspLikelihoodScaledBoundaryTerm (p ^ (2 : ℕ)) B

def thetaCuspLikelihoodPrimeSquareCentralScale (p : ℕ) (B D : ℝ) : ℝ :=
  2 * thetaCuspLikelihoodScaledBoundaryTerm p B *
    thetaCuspLikelihoodScaledBoundaryTerm p D

theorem thetaCuspLikelihoodSwapMassShellPhase_eq_prime_sq {p : ℕ} (hp : p.Prime) (B D : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhase (p ^ (2 : ℕ)) B D z =
      (thetaCuspLikelihoodPrimeSquareEndpointScale p B D : ℂ) *
          (Complex.exp (Complex.I * ((-Real.log p : ℝ) : ℂ) * z) +
            Complex.exp (Complex.I * (Real.log p : ℂ) * z)) +
        (thetaCuspLikelihoodPrimeSquareCentralScale p B D : ℂ) := by
  unfold thetaCuspLikelihoodSwapMassShellPhase
  rw [thetaPositiveFactorPairs_prime_sq hp]
  have hp2 := hp.two_le
  have hpPow : 1 < p ^ (2 : ℕ) := by nlinarith
  have hleft : (0, p ^ (2 : ℕ) - 1) ∉
      ({(p - 1, p - 1), (p ^ (2 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h
    · have hfst := congrArg Prod.fst h
      omega
    · have hfst := congrArg Prod.fst h
      omega
  have hmid : (p - 1, p - 1) ∉ ({(p ^ (2 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]
    intro h
    have hsnd := congrArg Prod.snd h
    omega
  rw [Finset.sum_insert hleft, Finset.sum_insert hmid, Finset.sum_singleton]
  have hpSub : p - 1 + 1 = p := by omega
  have hpSqSub : p ^ (2 : ℕ) - 1 + 1 = p ^ (2 : ℕ) := by omega
  rw [hpSub, hpSqSub]
  simp only [Nat.zero_add]
  rw [thetaCuspLikelihoodScaledBoundaryTerm_one B,
    thetaCuspLikelihoodScaledBoundaryTerm_one D]
  simp only [thetaFactorPairLogDisplacement_primeSq_left hp,
    thetaFactorPairLogDisplacement_primeSq_central hp,
    thetaFactorPairLogDisplacement_primeSq_right hp]
  have hzero : Complex.I * ((0 : ℝ) : ℂ) * z = 0 := by norm_num
  rw [hzero, Complex.exp_zero]
  unfold thetaCuspLikelihoodPrimeSquareEndpointScale thetaCuspLikelihoodPrimeSquareCentralScale
  push_cast
  ring

theorem thetaCuspLikelihoodSwapMassShellPhaseDerivative_eq_prime_sq {p : ℕ} (hp : p.Prime) (B D : ℝ) (z : ℂ) :
    thetaCuspLikelihoodSwapMassShellPhaseDerivative (p ^ (2 : ℕ)) B D z =
      Complex.I * (Real.log p : ℂ) * (thetaCuspLikelihoodPrimeSquareEndpointScale p B D : ℂ) *
        (Complex.exp (Complex.I * (Real.log p : ℂ) * z) -
          Complex.exp (Complex.I * ((-Real.log p : ℝ) : ℂ) * z)) := by
  unfold thetaCuspLikelihoodSwapMassShellPhaseDerivative
  rw [thetaPositiveFactorPairs_prime_sq hp]
  have hp2 := hp.two_le
  have hpPow : 1 < p ^ (2 : ℕ) := by nlinarith
  have hleft : (0, p ^ (2 : ℕ) - 1) ∉
      ({(p - 1, p - 1), (p ^ (2 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h
    · have hfst := congrArg Prod.fst h
      omega
    · have hfst := congrArg Prod.fst h
      omega
  have hmid : (p - 1, p - 1) ∉ ({(p ^ (2 : ℕ) - 1, 0)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton]
    intro h
    have hsnd := congrArg Prod.snd h
    omega
  rw [Finset.sum_insert hleft, Finset.sum_insert hmid, Finset.sum_singleton]
  have hpSub : p - 1 + 1 = p := by omega
  have hpSqSub : p ^ (2 : ℕ) - 1 + 1 = p ^ (2 : ℕ) := by omega
  rw [hpSub, hpSqSub]
  simp only [Nat.zero_add]
  rw [thetaCuspLikelihoodScaledBoundaryTerm_one B,
    thetaCuspLikelihoodScaledBoundaryTerm_one D]
  simp only [thetaFactorPairLogDisplacement_primeSq_left hp,
    thetaFactorPairLogDisplacement_primeSq_central hp,
    thetaFactorPairLogDisplacement_primeSq_right hp]
  unfold thetaCuspLikelihoodPrimeSquareEndpointScale
  push_cast
  ring

def thetaCuspLikelihoodPrimeSquareReflectionWallPoint (p : ℕ) (y : ℝ) : ℂ :=
  ⟨Real.pi / Real.log p, y⟩

@[simp] theorem thetaCuspLikelihoodPrimeSquareReflectionWallPoint_re (p : ℕ) (y : ℝ) :
    (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y).re = Real.pi / Real.log p := rfl

@[simp] theorem thetaCuspLikelihoodPrimeSquareReflectionWallPoint_im (p : ℕ) (y : ℝ) :
    (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y).im = y := rfl

theorem thetaCuspLikelihoodPrimeSquare_exp_plus_wall {p : ℕ} (hp : p.Prime) (y : ℝ) :
    Complex.exp (Complex.I * (Real.log p : ℂ) * thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
      -(Real.exp (-Real.log p * y) : ℂ) := by
  let lam : ℝ := Real.log (p : ℝ)
  have hlog : lam ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hpi : lam * (Real.pi / lam) = Real.pi := by
    field_simp
  have hpi' : lam * (Real.pi / Real.log (p : ℝ)) = Real.pi := by
    simpa [lam] using hpi
  change Complex.exp (Complex.I * (lam : ℂ) * thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
    -(Real.exp (-lam * y) : ℂ)
  have harg : Complex.I * (lam : ℂ) * thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y =
      ((-lam * y : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [thetaCuspLikelihoodPrimeSquareReflectionWallPoint, Complex.mul_re, Complex.mul_im]
    · simp [thetaCuspLikelihoodPrimeSquareReflectionWallPoint, Complex.mul_re, Complex.mul_im, hpi']
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
  apply Complex.ext <;> simp

theorem thetaCuspLikelihoodPrimeSquare_exp_minus_wall {p : ℕ} (hp : p.Prime) (y : ℝ) :
    Complex.exp (Complex.I * ((-Real.log p : ℝ) : ℂ) * thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
      -(Real.exp (Real.log p * y) : ℂ) := by
  let lam : ℝ := Real.log (p : ℝ)
  have hlog : lam ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hpi : lam * (Real.pi / lam) = Real.pi := by
    field_simp
  have hpi' : lam * (Real.pi / Real.log (p : ℝ)) = Real.pi := by
    simpa [lam] using hpi
  change Complex.exp (Complex.I * ((-lam : ℝ) : ℂ) * thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
    -(Real.exp (lam * y) : ℂ)
  have harg : Complex.I * ((-lam : ℝ) : ℂ) * thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y =
      ((lam * y : ℝ) : ℂ) + ((-Real.pi : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [thetaCuspLikelihoodPrimeSquareReflectionWallPoint, Complex.mul_re, Complex.mul_im]
    · simp [thetaCuspLikelihoodPrimeSquareReflectionWallPoint, Complex.mul_re, Complex.mul_im, hpi']
  have hnegpi : Complex.exp (((-Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
    rw [show (((-Real.pi : ℝ) : ℂ) * Complex.I) =
      -((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [harg, Complex.exp_add, hnegpi]
  apply Complex.ext <;> simp

theorem thetaCuspLikelihoodSwapPrimeSquarePhase_wall {p : ℕ} (hp : p.Prime) (B D y : ℝ) :
    thetaCuspLikelihoodSwapMassShellPhase (p ^ (2 : ℕ)) B D (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
      ((thetaCuspLikelihoodPrimeSquareCentralScale p B D -
        2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D * Real.cosh (Real.log p * y) : ℝ) : ℂ) := by
  rw [thetaCuspLikelihoodSwapMassShellPhase_eq_prime_sq hp, thetaCuspLikelihoodPrimeSquare_exp_minus_wall hp, thetaCuspLikelihoodPrimeSquare_exp_plus_wall hp]
  have hcosh :
      -(Real.exp (Real.log p * y) : ℂ) +
          -(Real.exp (-Real.log p * y) : ℂ) =
        -2 * (Real.cosh (Real.log p * y) : ℂ) := by
    apply Complex.ext <;> simp [Real.cosh_eq] <;> ring
  rw [hcosh]
  push_cast
  ring

theorem thetaCuspLikelihoodSwapPrimeSquarePhaseDerivative_wall {p : ℕ} (hp : p.Prime) (B D y : ℝ) :
    thetaCuspLikelihoodSwapMassShellPhaseDerivative (p ^ (2 : ℕ)) B D
        (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
      2 * Complex.I * (Real.log p : ℂ) * (thetaCuspLikelihoodPrimeSquareEndpointScale p B D : ℂ) *
        (Real.sinh (Real.log p * y) : ℂ) := by
  rw [thetaCuspLikelihoodSwapMassShellPhaseDerivative_eq_prime_sq hp, thetaCuspLikelihoodPrimeSquare_exp_plus_wall hp, thetaCuspLikelihoodPrimeSquare_exp_minus_wall hp]
  have hsinh :
      -(Real.exp (-Real.log p * y) : ℂ) -
          -(Real.exp (Real.log p * y) : ℂ) =
        2 * (Real.sinh (Real.log p * y) : ℂ) := by
    apply Complex.ext <;> simp [Real.sinh_eq] <;> ring
  rw [hsinh]
  push_cast
  ring

def thetaCuspLikelihoodSwapMassShellCurrent (k : ℕ) (B D : ℝ) (z : ℂ) : ℝ :=
  (thetaCuspLikelihoodSwapMassShellPhaseDerivative k B D z *
    (starRingEnd ℂ) (thetaCuspLikelihoodSwapMassShellPhase k B D z)).im

theorem thetaCuspLikelihoodSwapPrimeSquareCurrent_wall {p : ℕ} (hp : p.Prime) (B D y : ℝ) :
    thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B D (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
      2 * Real.log p * thetaCuspLikelihoodPrimeSquareEndpointScale p B D * Real.sinh (Real.log p * y) *
        (thetaCuspLikelihoodPrimeSquareCentralScale p B D -
          2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D * Real.cosh (Real.log p * y)) := by
  unfold thetaCuspLikelihoodSwapMassShellCurrent
  rw [thetaCuspLikelihoodSwapPrimeSquarePhaseDerivative_wall hp, thetaCuspLikelihoodSwapPrimeSquarePhase_wall hp]
  rw [Complex.conj_ofReal]
  let lam : ℝ := Real.log (p : ℝ)
  let E : ℝ := thetaCuspLikelihoodPrimeSquareEndpointScale p B D
  let S : ℝ := Real.sinh (Real.log p * y)
  let A : ℝ := thetaCuspLikelihoodPrimeSquareCentralScale p B D -
    2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D * Real.cosh (Real.log p * y)
  change (2 * Complex.I * (lam : ℂ) * (E : ℂ) * (S : ℂ) * (A : ℂ)).im =
    2 * lam * E * S * A
  rw [show 2 * Complex.I * (lam : ℂ) * (E : ℂ) * (S : ℂ) * (A : ℂ) =
      ((2 * lam * E * S * A : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  simp

/-- Current after removing exactly the prime-square zero-rapidity diagonal mode. -/
def thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent
    (p : ℕ) (B D : ℝ) (z : ℂ) : ℝ :=
  (thetaCuspLikelihoodSwapMassShellPhaseDerivative (p ^ (2 : ℕ)) B D z *
    (starRingEnd ℂ) (thetaCuspLikelihoodSwapMassShellPhase (p ^ (2 : ℕ)) B D z -
      (thetaCuspLikelihoodPrimeSquareCentralScale p B D : ℂ))).im

theorem thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent_wall
    {p : ℕ} (hp : p.Prime) (B D y : ℝ) :
    thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent p B D
        (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) =
      -4 * Real.log p * thetaCuspLikelihoodPrimeSquareEndpointScale p B D ^ (2 : ℕ) *
        Real.sinh (Real.log p * y) * Real.cosh (Real.log p * y) := by
  unfold thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent
  rw [thetaCuspLikelihoodSwapPrimeSquarePhaseDerivative_wall hp,
    thetaCuspLikelihoodSwapPrimeSquarePhase_wall hp]
  simp only [map_sub, Complex.conj_ofReal]
  rw [show
      ((thetaCuspLikelihoodPrimeSquareCentralScale p B D -
        2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D *
          Real.cosh (Real.log p * y) : ℝ) : ℂ) -
          (thetaCuspLikelihoodPrimeSquareCentralScale p B D : ℂ) =
        ((-2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D *
          Real.cosh (Real.log p * y) : ℝ) : ℂ) by
    push_cast
    ring]
  let lam : ℝ := Real.log (p : ℝ)
  let E : ℝ := thetaCuspLikelihoodPrimeSquareEndpointScale p B D
  let S : ℝ := Real.sinh (Real.log p * y)
  let H : ℝ := Real.cosh (Real.log p * y)
  change (2 * Complex.I * (lam : ℂ) * (E : ℂ) * (S : ℂ) *
      ((-2 * E * H : ℝ) : ℂ)).im = -4 * lam * E ^ (2 : ℕ) * S * H
  have hmul :
      2 * Complex.I * (lam : ℂ) * (E : ℂ) * (S : ℂ) *
          ((-2 * E * H : ℝ) : ℂ) =
        ((-4 * lam * E * E * S * H : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  calc
    (2 * Complex.I * (lam : ℂ) * (E : ℂ) * (S : ℂ) *
        ((-2 * E * H : ℝ) : ℂ)).im =
        (((-4 * lam * E * E * S * H : ℝ) : ℂ) * Complex.I).im :=
      congrArg Complex.im hmul
    _ = -4 * lam * E * E * S * H := by simp
    _ = -4 * lam * E ^ (2 : ℕ) * S * H := by ring

theorem thetaCuspLikelihoodPrimeSquareEndpointScale_pos {p : ℕ} (hp : p.Prime) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hBD : 0 < B + D) :
    0 < thetaCuspLikelihoodPrimeSquareEndpointScale p B D := by
  have hpSq : 2 ≤ p ^ (2 : ℕ) := by nlinarith [hp.two_le]
  have hSB := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg hpSq hB
  have hSD := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg hpSq hD
  unfold thetaCuspLikelihoodPrimeSquareEndpointScale
  by_cases hB0 : B = 0
  · subst B
    simp only [zero_mul, zero_add] at hBD ⊢
    exact mul_pos hBD hSB
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    exact add_pos_of_pos_of_nonneg (mul_pos hBpos hSD)
      (mul_nonneg hD hSB.le)

theorem thetaCuspLikelihoodPrimeSquareCentralScale_pos {p : ℕ} (hp : p.Prime) {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) :
    0 < thetaCuspLikelihoodPrimeSquareCentralScale p B D := by
  have hSB := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg hp.two_le hB
  have hSD := thetaCuspLikelihoodScaledBoundaryTerm_pos_of_nonneg hp.two_le hD
  unfold thetaCuspLikelihoodPrimeSquareCentralScale
  positivity

theorem thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent_wall_neg
    {p : ℕ} (hp : p.Prime) {B D y : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hBD : 0 < B + D) (hy : 0 < y) :
    thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent p B D
        (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) < 0 := by
  rw [thetaCuspLikelihoodSwapPrimeSquareDiagonalRenormalizedCurrent_wall hp]
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hE := thetaCuspLikelihoodPrimeSquareEndpointScale_pos hp hB hD hBD
  have hsinh : 0 < Real.sinh (Real.log p * y) :=
    Real.sinh_pos_iff.mpr (mul_pos hlog hy)
  have hcosh : 0 < Real.cosh (Real.log p * y) := Real.cosh_pos _
  have hfac :
      0 < 4 * Real.log p * thetaCuspLikelihoodPrimeSquareEndpointScale p B D ^ (2 : ℕ) *
        Real.sinh (Real.log p * y) * Real.cosh (Real.log p * y) := by
    positivity
  calc
    -4 * Real.log p * thetaCuspLikelihoodPrimeSquareEndpointScale p B D ^ (2 : ℕ) *
          Real.sinh (Real.log p * y) * Real.cosh (Real.log p * y) =
        -(4 * Real.log p * thetaCuspLikelihoodPrimeSquareEndpointScale p B D ^ (2 : ℕ) *
          Real.sinh (Real.log p * y) * Real.cosh (Real.log p * y)) := by ring
    _ < 0 := neg_lt_zero.mpr hfac

theorem thetaCuspLikelihoodSwapPrimeSquareCurrent_wall_pos_iff {p : ℕ} (hp : p.Prime) {B D y : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hBD : 0 < B + D) (hy : 0 < y) :
    0 < thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B D (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) ↔
      2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D * Real.cosh (Real.log p * y) <
        thetaCuspLikelihoodPrimeSquareCentralScale p B D := by
  rw [thetaCuspLikelihoodSwapPrimeSquareCurrent_wall hp]
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hE := thetaCuspLikelihoodPrimeSquareEndpointScale_pos hp hB hD hBD
  have hsinh : 0 < Real.sinh (Real.log p * y) :=
    Real.sinh_pos_iff.mpr (mul_pos hlog hy)
  rw [mul_pos_iff_of_pos_left (mul_pos (mul_pos (mul_pos two_pos hlog) hE) hsinh)]
  exact sub_pos

theorem thetaCuspLikelihoodSwapPrimeSquareCurrent_wall_eq_zero_iff {p : ℕ} (hp : p.Prime) {B D y : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hBD : 0 < B + D) (hy : 0 < y) :
    thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B D (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) = 0 ↔
      thetaCuspLikelihoodPrimeSquareCentralScale p B D =
        2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D * Real.cosh (Real.log p * y) := by
  rw [thetaCuspLikelihoodSwapPrimeSquareCurrent_wall hp]
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hE := thetaCuspLikelihoodPrimeSquareEndpointScale_pos hp hB hD hBD
  have hsinh : 0 < Real.sinh (Real.log p * y) :=
    Real.sinh_pos_iff.mpr (mul_pos hlog hy)
  rw [mul_eq_zero_iff_left (mul_pos (mul_pos (mul_pos two_pos hlog) hE) hsinh).ne']
  exact sub_eq_zero

theorem thetaCuspLikelihoodSwapPrimeSquareCurrent_wall_neg_iff {p : ℕ} (hp : p.Prime) {B D y : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hBD : 0 < B + D) (hy : 0 < y) :
    thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B D (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) < 0 ↔
      thetaCuspLikelihoodPrimeSquareCentralScale p B D <
        2 * thetaCuspLikelihoodPrimeSquareEndpointScale p B D * Real.cosh (Real.log p * y) := by
  rw [thetaCuspLikelihoodSwapPrimeSquareCurrent_wall hp]
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hE := thetaCuspLikelihoodPrimeSquareEndpointScale_pos hp hB hD hBD
  have hsinh : 0 < Real.sinh (Real.log p * y) :=
    Real.sinh_pos_iff.mpr (mul_pos hlog hy)
  have hfac : 0 < 2 * Real.log p * thetaCuspLikelihoodPrimeSquareEndpointScale p B D *
      Real.sinh (Real.log p * y) :=
    mul_pos (mul_pos (mul_pos two_pos hlog) hE) hsinh
  constructor <;> intro h <;> nlinarith

@[simp] theorem thetaCuspLikelihoodPrimeSquareEndpointScale_boundary (p : ℕ) (B : ℝ) :
    thetaCuspLikelihoodPrimeSquareEndpointScale p B 0 =
      B * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) := by
  simp [thetaCuspLikelihoodPrimeSquareEndpointScale]

@[simp] theorem thetaCuspLikelihoodPrimeSquareCentralScale_boundary (p : ℕ) (B : ℝ) :
    thetaCuspLikelihoodPrimeSquareCentralScale p B 0 =
      2 * thetaCuspLikelihoodScaledBoundaryTerm p B *
        thetaCuspLikelihoodRayWeight p := by
  simp [thetaCuspLikelihoodPrimeSquareCentralScale]

theorem thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_div {p : ℕ} (hp : p.Prime) {B : ℝ}
    (hB : 0 < B) (y : ℝ) :
    thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) / B =
      4 * Real.log p * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) *
        Real.sinh (Real.log p * y) *
        (thetaCuspLikelihoodScaledBoundaryTerm p B *
            thetaCuspLikelihoodRayWeight p -
          B * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) *
            Real.cosh (Real.log p * y)) := by
  rw [thetaCuspLikelihoodSwapPrimeSquareCurrent_wall hp, thetaCuspLikelihoodPrimeSquareEndpointScale_boundary,
    thetaCuspLikelihoodPrimeSquareCentralScale_boundary]
  field_simp [hB.ne']
  ring

theorem tendsto_thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_div {p : ℕ} (hp : p.Prime) (y : ℝ) :
    Tendsto
      (fun B : ℝ => thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) / B)
      (𝓝[>] 0)
      (𝓝 (4 * Real.log p * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) *
        Real.sinh (Real.log p * y) * thetaCuspLikelihoodRayWeight p ^ (2 : ℕ))) := by
  let F : ℝ → ℝ := fun B =>
    4 * Real.log p * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) *
      Real.sinh (Real.log p * y) *
      (thetaCuspLikelihoodScaledBoundaryTerm p B *
          thetaCuspLikelihoodRayWeight p -
        B * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) *
          Real.cosh (Real.log p * y))
  have hcont : ContinuousAt F 0 := by
    dsimp [F]
    unfold thetaCuspLikelihoodScaledBoundaryTerm
    fun_prop
  have hlim : Tendsto F (𝓝[>] 0)
      (𝓝 (4 * Real.log p * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) *
        Real.sinh (Real.log p * y) * thetaCuspLikelihoodRayWeight p ^ (2 : ℕ))) := by
    simpa [F, thetaCuspLikelihoodScaledBoundaryTerm_zero, pow_two] using
      hcont.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with B hB
  exact (thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_div hp hB y).symm

theorem thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_conormal_residue_pos {p : ℕ} (hp : p.Prime)
    {y : ℝ} (hy : 0 < y) :
    0 < 4 * Real.log p * thetaCuspLikelihoodRayWeight (p ^ (2 : ℕ)) *
      Real.sinh (Real.log p * y) * thetaCuspLikelihoodRayWeight p ^ (2 : ℕ) := by
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpSq : 2 ≤ p ^ (2 : ℕ) := by nlinarith [hp.two_le]
  have hRp := thetaCuspLikelihoodRayWeight_pos hp.two_le
  have hRpSq := thetaCuspLikelihoodRayWeight_pos hpSq
  have hsinh : 0 < Real.sinh (Real.log p * y) :=
    Real.sinh_pos_iff.mpr (mul_pos hlog hy)
  positivity

theorem eventually_thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_pos {p : ℕ} (hp : p.Prime)
    {y : ℝ} (hy : 0 < y) :
    ∀ᶠ B : ℝ in 𝓝[>] 0,
      0 < thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) := by
  have hlim := tendsto_thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_div hp y
  have hL := thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_conormal_residue_pos hp hy
  have hquot : ∀ᶠ B : ℝ in 𝓝[>] 0,
      0 < thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) / B :=
    hlim.eventually (Ioi_mem_nhds hL)
  filter_upwards [hquot, self_mem_nhdsWithin] with B hq hB
  change 0 < B at hB
  calc
    0 < B * (thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) / B) :=
      mul_pos hB hq
    _ = thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) := by
      field_simp [hB.ne']

theorem exists_thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_pos {p : ℕ} (hp : p.Prime)
    {y : ℝ} (hy : 0 < y) :
    ∃ B : ℝ, 0 < B ∧
      0 < thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) := by
  have h : ∀ᶠ B : ℝ in 𝓝[>] 0, 0 < B ∧
      0 < thetaCuspLikelihoodSwapMassShellCurrent (p ^ (2 : ℕ)) B 0 (thetaCuspLikelihoodPrimeSquareReflectionWallPoint p y) := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_thetaCuspLikelihoodSwapPrimeSquareCurrent_boundary_pos hp hy] with B hB hcurrent
    exact ⟨hB, hcurrent⟩
  exact h.exists

end
end RHTower
