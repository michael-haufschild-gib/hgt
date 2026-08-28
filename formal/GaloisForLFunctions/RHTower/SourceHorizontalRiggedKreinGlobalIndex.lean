import GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinPhaseObject
import GaloisForLFunctions.RHTower.FiniteEulerLocalRatio

/-!
# Global index of the source-horizontal rigged prime form

Finite prime-axis restrictions do not by themselves determine the inertia of the literal
all-prime form: an infinite carrier could contain additional negative directions or a hidden
radical.  This file closes both gaps.

On a left critical-strip fibre the form is a nonnegative all-prime diagonal minus the square of
one common reservoir functional.  Hence it has at most one negative square on the full nuclear
source, and two prime deltas show that this bound is attained.  Its radical is exactly the vectors
whose real coefficients vanish on every retained prime axis.  The nontrivial direction uses the
infinite prime set: a radical vector with nonzero reservoir charge would make every summable
diagonal term equal to the same nonzero constant.  Reflection exchanges the exact negative and
positive classifications on the right half of the strip.

Thus the quotient by the explicit coefficient radical is a genuine index-one source form, not
merely a compatible family of finite index-one restrictions.  No Xi zero, spectral reality,
finite measure, positivity assumption, or added logical primitive is used.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Every pre-divisor prime weight is strictly positive away from the critical wall. -/
theorem preDivisorRiggedPrimeWeight_pos_of_offWall
    (s : ℂ) (hoff : s.re ≠ 1 / 2) (p : Nat.Primes) :
    0 < preDivisorRiggedPrimeWeight s p := by
  have h :=
    PreDivisorReflectionDefectStabilization.preDivisorSharedWeights_pos_of_offLine
      s hoff (fun _ : Fin 1 => p) (0 : Fin 1)
  simpa [PreDivisorReflectionDefectStabilization.preDivisorSharedWeights,
    preDivisorRiggedPrimeWeight] using h

/-- The infinite weighted prime diagonal is nonnegative on every source vector. -/
theorem preDivisorRiggedPrimeDiagonal_self_nonneg
    (s : ℂ) (a : DeningerHeightKothe) :
    0 ≤ preDivisorRiggedPrimeDiagonal s a a := by
  apply tsum_nonneg
  intro p
  rw [preDivisorRiggedPrimeDiagonalTerm, mul_assoc]
  exact mul_nonneg (abs_nonneg _) (mul_self_nonneg _)

/-- Carrier-level meaning of at most one negative square, valid without finite dimensionality. -/
def RiggedFormHasAtMostOneNegativeSquare
    (B : DeningerHeightKothe → DeningerHeightKothe → ℝ) : Prop :=
  ∀ x y : DeningerHeightKothe, B x x < 0 → B y y < 0 →
    ∃ c d : ℝ, (c ≠ 0 ∨ d ≠ 0) ∧
      0 ≤ B (c • x + d • y) (c • x + d • y)

/-- Reflected carrier-level meaning of at most one positive square. -/
def RiggedFormHasAtMostOnePositiveSquare
    (B : DeningerHeightKothe → DeningerHeightKothe → ℝ) : Prop :=
  ∀ x y : DeningerHeightKothe, 0 < B x x → 0 < B y y →
    ∃ c d : ℝ, (c ≠ 0 ∨ d ≠ 0) ∧
      B (c • x + d • y) (c • x + d • y) ≤ 0

/-- Exact one-negative-square classification on an infinite carrier. -/
def RiggedFormHasExactlyOneNegativeSquare
    (B : DeningerHeightKothe → DeningerHeightKothe → ℝ) : Prop :=
  RiggedFormHasAtMostOneNegativeSquare B ∧
    ∃ x : DeningerHeightKothe, B x x < 0

/-- Exact one-positive-square classification on an infinite carrier. -/
def RiggedFormHasExactlyOnePositiveSquare
    (B : DeningerHeightKothe → DeningerHeightKothe → ℝ) : Prop :=
  RiggedFormHasAtMostOnePositiveSquare B ∧
    ∃ x : DeningerHeightKothe, 0 < B x x

/-- The left all-prime form has at most one negative square globally. -/
theorem preDivisorRiggedPrimeWittPairing_atMostOneNegativeSquare_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2) :
    RiggedFormHasAtMostOneNegativeSquare
      (preDivisorRiggedPrimeWittPairing s) := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  intro x y hx hy
  have hformula (a : DeningerHeightKothe) :
      preDivisorRiggedPrimeWittPairing s a a =
        preDivisorRiggedPrimeDiagonal s a a -
          preDivisorRiggedPrimeLinear s a ^ 2 := by
    rw [preDivisorRiggedPrimeWittPairing,
      preDivisorOrientation_eq_one_of_left s hleft]
    ring
  have hLx : preDivisorRiggedPrimeLinear s x ≠ 0 := by
    intro hzero
    have hx' := hx
    rw [hformula x, hzero] at hx'
    have hx'' : preDivisorRiggedPrimeDiagonal s x x < 0 := by
      simpa only [pow_two, zero_mul, sub_zero] using hx'
    exact (not_lt_of_ge (preDivisorRiggedPrimeDiagonal_self_nonneg s x)) hx''
  have hLy : preDivisorRiggedPrimeLinear s y ≠ 0 := by
    intro hzero
    have hy' := hy
    rw [hformula y, hzero] at hy'
    have hy'' : preDivisorRiggedPrimeDiagonal s y y < 0 := by
      simpa only [pow_two, zero_mul, sub_zero] using hy'
    exact (not_lt_of_ge (preDivisorRiggedPrimeDiagonal_self_nonneg s y)) hy''
  let c := preDivisorRiggedPrimeLinear s y
  let d := -preDivisorRiggedPrimeLinear s x
  refine ⟨c, d, Or.inl hLy, ?_⟩
  have hlinear :
      preDivisorRiggedPrimeLinear s (c • x + d • y) = 0 := by
    rw [preDivisorRiggedPrimeLinear_add hs,
      preDivisorRiggedPrimeLinear_smul,
      preDivisorRiggedPrimeLinear_smul]
    dsimp [c, d]
    ring
  rw [hformula, hlinear]
  simpa only [pow_two, zero_mul, sub_zero] using
    preDivisorRiggedPrimeDiagonal_self_nonneg s (c • x + d • y)

/-- The right all-prime form has at most one positive square globally. -/
theorem preDivisorRiggedPrimeWittPairing_atMostOnePositiveSquare_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1) :
    RiggedFormHasAtMostOnePositiveSquare
      (preDivisorRiggedPrimeWittPairing s) := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨lt_trans (by norm_num) hright, hs1⟩
  intro x y hx hy
  have hformula (a : DeningerHeightKothe) :
      preDivisorRiggedPrimeWittPairing s a a =
        -(preDivisorRiggedPrimeDiagonal s a a -
          preDivisorRiggedPrimeLinear s a ^ 2) := by
    rw [preDivisorRiggedPrimeWittPairing,
      PreDivisorReflectionDefectStabilization.preDivisorOrientation_eq_neg_one_of_right
        s hright]
    ring
  have hLx : preDivisorRiggedPrimeLinear s x ≠ 0 := by
    intro hzero
    have hx' := hx
    rw [hformula x, hzero] at hx'
    have hx'' : 0 < -preDivisorRiggedPrimeDiagonal s x x := by
      simpa only [pow_two, zero_mul, sub_zero] using hx'
    exact (not_lt_of_ge
      (neg_nonpos.mpr (preDivisorRiggedPrimeDiagonal_self_nonneg s x))) hx''
  have hLy : preDivisorRiggedPrimeLinear s y ≠ 0 := by
    intro hzero
    have hy' := hy
    rw [hformula y, hzero] at hy'
    have hy'' : 0 < -preDivisorRiggedPrimeDiagonal s y y := by
      simpa only [pow_two, zero_mul, sub_zero] using hy'
    exact (not_lt_of_ge
      (neg_nonpos.mpr (preDivisorRiggedPrimeDiagonal_self_nonneg s y))) hy''
  let c := preDivisorRiggedPrimeLinear s y
  let d := -preDivisorRiggedPrimeLinear s x
  refine ⟨c, d, Or.inl hLy, ?_⟩
  have hlinear :
      preDivisorRiggedPrimeLinear s (c • x + d • y) = 0 := by
    rw [preDivisorRiggedPrimeLinear_add hs,
      preDivisorRiggedPrimeLinear_smul,
      preDivisorRiggedPrimeLinear_smul]
    dsimp [c, d]
    ring
  rw [hformula, hlinear]
  have hdiag := preDivisorRiggedPrimeDiagonal_self_nonneg s (c • x + d • y)
  simpa only [pow_two, zero_mul, sub_zero] using neg_nonpos.mpr hdiag

/-- Real bilinearity in the second argument on the open critical strip. -/
theorem preDivisorRiggedPrimeWittPairing_add_right
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b c : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s a (b + c) =
      preDivisorRiggedPrimeWittPairing s a b +
        preDivisorRiggedPrimeWittPairing s a c := by
  rw [preDivisorRiggedPrimeWittPairing_comm s a (b + c),
    preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimeWittPairing_comm s b a,
    preDivisorRiggedPrimeWittPairing_comm s c a]

/-- Two prime deltas exhibit a negative square on every left fibre. -/
theorem exists_preDivisorRiggedPrimeWittPairing_negative_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2) :
    ∃ a : DeningerHeightKothe,
      preDivisorRiggedPrimeWittPairing s a a < 0 := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  let p : Nat.Primes := nthPrimePoint 0
  let q : Nat.Primes := nthPrimePoint 1
  have hpq : p ≠ q := by
    apply preDivisorRiggedNthPrimePoint_injective.ne
    norm_num
  have hqp : q ≠ p := Ne.symm hpq
  have hwp : 0 < preDivisorRiggedPrimeWeight s p :=
    preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_lt hleft) p
  have hwq : 0 < preDivisorRiggedPrimeWeight s q :=
    preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_lt hleft) q
  refine ⟨preDivisorRiggedPrimeDelta p + preDivisorRiggedPrimeDelta q, ?_⟩
  rw [preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorOrientation_eq_one_of_left s hleft]
  simp [hpq, hqp]
  have hsqrtp : 0 < Real.sqrt (preDivisorRiggedPrimeWeight s p) :=
    Real.sqrt_pos.2 hwp
  have hsqrtq : 0 < Real.sqrt (preDivisorRiggedPrimeWeight s q) :=
    Real.sqrt_pos.2 hwq
  rw [mul_comm (Real.sqrt (preDivisorRiggedPrimeWeight s q))]
  nlinarith [mul_pos hsqrtp hsqrtq]

/-- Two prime deltas exhibit a positive square on every right fibre. -/
theorem exists_preDivisorRiggedPrimeWittPairing_positive_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1) :
    ∃ a : DeningerHeightKothe,
      0 < preDivisorRiggedPrimeWittPairing s a a := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨lt_trans (by norm_num) hright, hs1⟩
  let p : Nat.Primes := nthPrimePoint 0
  let q : Nat.Primes := nthPrimePoint 1
  have hpq : p ≠ q := by
    apply preDivisorRiggedNthPrimePoint_injective.ne
    norm_num
  have hqp : q ≠ p := Ne.symm hpq
  have hwp : 0 < preDivisorRiggedPrimeWeight s p :=
    preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_gt hright) p
  have hwq : 0 < preDivisorRiggedPrimeWeight s q :=
    preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_gt hright) q
  refine ⟨preDivisorRiggedPrimeDelta p + preDivisorRiggedPrimeDelta q, ?_⟩
  rw [preDivisorRiggedPrimeWittPairing_add_left hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_add_right hs,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    preDivisorRiggedPrimeWittPairing_delta,
    PreDivisorReflectionDefectStabilization.preDivisorOrientation_eq_neg_one_of_right
      s hright]
  simp [hpq, hqp]
  have hsqrtp : 0 < Real.sqrt (preDivisorRiggedPrimeWeight s p) :=
    Real.sqrt_pos.2 hwp
  have hsqrtq : 0 < Real.sqrt (preDivisorRiggedPrimeWeight s q) :=
    Real.sqrt_pos.2 hwq
  rw [mul_comm (Real.sqrt (preDivisorRiggedPrimeWeight s q))]
  nlinarith [mul_pos hsqrtp hsqrtq]

/-- Left radical of the all-prime rigged form.  Symmetry makes it the full radical. -/
def PreDivisorRiggedPrimeRadical (s : ℂ) (a : DeningerHeightKothe) : Prop :=
  ∀ b : DeningerHeightKothe,
    preDivisorRiggedPrimeWittPairing s a b = 0

/-- Pairing a source vector against one prime delta reads its weighted real coefficient. -/
theorem preDivisorRiggedPrimeDiagonal_delta_right
    (s : ℂ) (a : DeningerHeightKothe) (p : Nat.Primes) :
    preDivisorRiggedPrimeDiagonal s a (preDivisorRiggedPrimeDelta p) =
      preDivisorRiggedPrimeWeight s p *
        (((a : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis p)).re) := by
  rw [preDivisorRiggedPrimeDiagonal_comm,
    preDivisorRiggedPrimeDiagonal, tsum_eq_single p]
  · simp [preDivisorRiggedPrimeDiagonalTerm]
  · intro q hq
    simp [preDivisorRiggedPrimeDiagonalTerm, hq]

/-- Vanishing of every visible real prime coefficient puts a vector in the radical. -/
theorem preDivisorRiggedPrimeRadical_of_prime_re_eq_zero
    (s : ℂ) (a : DeningerHeightKothe)
    (ha : ∀ p : Nat.Primes,
      (((a : DeningerPrimeLattice → ℂ)
        (preDivisorRiggedPrimeAxis p)).re) = 0) :
    PreDivisorRiggedPrimeRadical s a := by
  intro b
  have hlinear : preDivisorRiggedPrimeLinear s a = 0 := by
    rw [preDivisorRiggedPrimeLinear]
    have hterm : (fun p : Nat.Primes =>
        preDivisorRiggedPrimeLinearTerm s a p) = 0 := by
      funext p
      simp [preDivisorRiggedPrimeLinearTerm, ha p]
    rw [hterm]
    exact tsum_zero
  have hdiagonal : preDivisorRiggedPrimeDiagonal s a b = 0 := by
    rw [preDivisorRiggedPrimeDiagonal]
    have hterm : (fun p : Nat.Primes =>
        preDivisorRiggedPrimeDiagonalTerm s a b p) = 0 := by
      funext p
      simp [preDivisorRiggedPrimeDiagonalTerm, ha p]
    rw [hterm]
    exact tsum_zero
  rw [preDivisorRiggedPrimeWittPairing, hlinear, hdiagonal]
  ring

/-- A radical vector on a left fibre has zero real coefficient on every retained prime axis. -/
theorem prime_re_eq_zero_of_preDivisorRiggedPrimeRadical_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (a : DeningerHeightKothe) (hrad : PreDivisorRiggedPrimeRadical s a) :
    ∀ p : Nat.Primes,
      (((a : DeningerPrimeLattice → ℂ)
        (preDivisorRiggedPrimeAxis p)).re) = 0 := by
  have hs : 0 < s.re ∧ s.re < 1 :=
    ⟨hs0, lt_trans hleft (by norm_num)⟩
  let L : ℝ := preDivisorRiggedPrimeLinear s a
  have hcoordinate (p : Nat.Primes) :
      preDivisorRiggedPrimeWeight s p *
          (((a : DeningerPrimeLattice → ℂ)
            (preDivisorRiggedPrimeAxis p)).re) =
        L * Real.sqrt (preDivisorRiggedPrimeWeight s p) := by
    have h := hrad (preDivisorRiggedPrimeDelta p)
    rw [preDivisorRiggedPrimeWittPairing,
      preDivisorOrientation_eq_one_of_left s hleft,
      preDivisorRiggedPrimeDiagonal_delta_right,
      preDivisorRiggedPrimeLinear_delta] at h
    dsimp [L]
    linarith
  have hterm (p : Nat.Primes) :
      preDivisorRiggedPrimeDiagonalTerm s a a p = L ^ 2 := by
    have hw : 0 < preDivisorRiggedPrimeWeight s p :=
      preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_lt hleft) p
    have hsqrt := Real.sq_sqrt hw.le
    have hsq := congrArg (fun t : ℝ => t ^ 2) (hcoordinate p)
    rw [mul_pow, mul_pow, hsqrt] at hsq
    rw [preDivisorRiggedPrimeDiagonalTerm]
    nlinarith [hsq]
  have hconst : Summable (fun _ : Nat.Primes => L ^ 2) := by
    have hsum := summable_preDivisorRiggedPrimeDiagonalTerm hs a a
    exact hsum.congr hterm
  have hL : L = 0 := by
    by_contra hL0
    have hLsq : L ^ 2 ≠ 0 := pow_ne_zero 2 hL0
    have hone : Summable (fun _ : Nat.Primes => (1 : ℝ)) := by
      have hscaled := hconst.mul_left (L ^ 2)⁻¹
      simpa [hLsq] using hscaled
    exact GaloisForLFunctions.RHTower.not_summable_constant_one_on_primes hone
  intro p
  have hw : 0 < preDivisorRiggedPrimeWeight s p :=
    preDivisorRiggedPrimeWeight_pos_of_offWall s (ne_of_lt hleft) p
  have hp := hcoordinate p
  rw [hL] at hp
  simp only [zero_mul] at hp
  exact (mul_eq_zero.mp hp).resolve_left hw.ne'

/-- Exact radical classification on every left critical-strip fibre. -/
theorem preDivisorRiggedPrimeRadical_iff_left
    (s : ℂ) (hs0 : 0 < s.re) (hleft : s.re < 1 / 2)
    (a : DeningerHeightKothe) :
    PreDivisorRiggedPrimeRadical s a ↔
      ∀ p : Nat.Primes,
        (((a : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis p)).re) = 0 := by
  constructor
  · exact prime_re_eq_zero_of_preDivisorRiggedPrimeRadical_left s hs0 hleft a
  · exact preDivisorRiggedPrimeRadical_of_prime_re_eq_zero s a

/-- Exact radical classification on every reflected right critical-strip fibre. -/
theorem preDivisorRiggedPrimeRadical_iff_right
    (s : ℂ) (hright : 1 / 2 < s.re) (hs1 : s.re < 1)
    (a : DeningerHeightKothe) :
    PreDivisorRiggedPrimeRadical s a ↔
      ∀ p : Nat.Primes,
        (((a : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis p)).re) = 0 := by
  let t := PreDivisorReflectionDefectStabilization.preDivisorLineConj s
  have ht0 : 0 < t.re := by
    change 0 < 1 - s.re
    linarith
  have htleft : t.re < 1 / 2 := by
    change 1 - s.re < 1 / 2
    linarith
  constructor
  · intro hsrad
    apply (preDivisorRiggedPrimeRadical_iff_left t ht0 htleft a).1
    intro b
    change preDivisorRiggedPrimeWittPairing
      (PreDivisorReflectionDefectStabilization.preDivisorLineConj s) a b = 0
    rw [preDivisorRiggedPrimeWittPairing_lineConj, hsrad b, neg_zero]
  · exact preDivisorRiggedPrimeRadical_of_prime_re_eq_zero s a

/--
**Global SC index classification.**  The literal all-prime source form has one negative square
modulo its exact coefficient radical on every left fibre, and one positive square modulo the same
radical on every right fibre.
-/
theorem preDivisorRiggedPrimeWittPairing_globalIndexClassification :
    (∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      (∀ a : DeningerHeightKothe,
        PreDivisorRiggedPrimeRadical s a ↔
          ∀ p : Nat.Primes,
            (((a : DeningerPrimeLattice → ℂ)
              (preDivisorRiggedPrimeAxis p)).re) = 0) ∧
      RiggedFormHasExactlyOneNegativeSquare
        (preDivisorRiggedPrimeWittPairing s)) ∧
    (∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∀ a : DeningerHeightKothe,
        PreDivisorRiggedPrimeRadical s a ↔
          ∀ p : Nat.Primes,
            (((a : DeningerPrimeLattice → ℂ)
              (preDivisorRiggedPrimeAxis p)).re) = 0) ∧
      RiggedFormHasExactlyOnePositiveSquare
        (preDivisorRiggedPrimeWittPairing s)) := by
  constructor
  · intro s hs0 hleft
    exact ⟨preDivisorRiggedPrimeRadical_iff_left s hs0 hleft,
      preDivisorRiggedPrimeWittPairing_atMostOneNegativeSquare_left s hs0 hleft,
      exists_preDivisorRiggedPrimeWittPairing_negative_left s hs0 hleft⟩
  · intro s hright hs1
    exact ⟨preDivisorRiggedPrimeRadical_iff_right s hright hs1,
      preDivisorRiggedPrimeWittPairing_atMostOnePositiveSquare_right s hright hs1,
      exists_preDivisorRiggedPrimeWittPairing_positive_right s hright hs1⟩

end

end RHTower
