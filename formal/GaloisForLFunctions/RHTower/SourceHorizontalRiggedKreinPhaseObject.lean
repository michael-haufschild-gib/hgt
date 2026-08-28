import GaloisForLFunctions.RHTower.XiPreDivisorReflectionDefectStabilization
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesDualCurrent

/-!
# Source-horizontal rigged Krein phase object

Finite source-horizontal reservoir packets have one negative square in one orientation and
arbitrarily large negative index after reflection.  Hence no fixed finite sum of Stokes one-port
carriers can receive the literal all-prime object.  This file constructs the positive survivor:
one pre-divisor, all-prime symmetric form on the nuclear Deninger height--Köthe test source.

For a spectral point `s`, its prime-axis coefficients are the absolute pre-divisor Gamma
Bocksteins.  The diagonal pairing and common reservoir functional converge against the zeroth
Köthe seminorm throughout the open critical strip.  Their rank-one difference is jointly bounded,
reflection-odd, zero on the critical wall, and coefficient-faithful: every injective finite
prime-axis Gram restriction is exactly the existing pre-divisor shared-reservoir matrix.  Thus all
finite inertia laws assemble compatibly in one source-to-dual object without selecting Xi zeros.

This closes the algebraic/topological infinite phase-object part of SC.  It does not construct a
meromorphic Xi determinant, a positive polarization, or RH.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

open PreDivisorReflectionDefectStabilization

/-- Positive valuation-one axis for one ordinary prime in the Deninger Kummer lattice. -/
def preDivisorRiggedPrimeAxis (p : Nat.Primes) : DeningerPrimeLattice :=
  gammaSewnMobiusApertureStokesPrimePowerAxis (p, 0)

/-- Distinct primes remain distinct on the positive valuation-one axis. -/
theorem preDivisorRiggedPrimeAxis_injective :
    Function.Injective preDivisorRiggedPrimeAxis := by
  intro p q h
  have hpq := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  exact congrArg Prod.fst hpq

/-- Unsigned coefficient of the pre-divisor Gamma Bockstein. -/
def preDivisorRiggedPrimeWeight (s : ℂ) (p : Nat.Primes) : ℝ :=
  |preDivisorPrimeCarrier s p|

/-- Throughout the open critical strip every rigged prime weight lies in the unit interval. -/
theorem preDivisorRiggedPrimeWeight_mem_unit
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (p : Nat.Primes) :
    0 ≤ preDivisorRiggedPrimeWeight s p ∧
      preDivisorRiggedPrimeWeight s p ≤ 1 := by
  constructor
  · exact abs_nonneg _
  · have ht : |preDivisorCenteredRate s| < 1 := by
      rw [abs_lt]
      constructor <;> simp only [preDivisorCenteredRate] <;> linarith [hs.1, hs.2]
    have hmag :=
      (primeGammaCofinalBocksteinMagnitude_bounds
        (preDivisorCenteredRate s) p).2
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
    have hexp : |preDivisorCenteredRate s| - 1 ≤ 0 := by linarith
    have hpow : (p : ℝ) ^ (|preDivisorCenteredRate s| - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 hexp
    change |primeGammaCofinalBocksteinCoefficient
      (preDivisorCenteredRate s) p| ≤ 1
    exact hmag.trans hpow

/-- One coefficient of the common all-prime reservoir functional. -/
def preDivisorRiggedPrimeLinearTerm
    (s : ℂ) (a : DeningerHeightKothe) (p : Nat.Primes) : ℝ :=
  Real.sqrt (preDivisorRiggedPrimeWeight s p) *
    (((a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re)

/-- The common reservoir functional is absolutely summable on every open-strip fibre. -/
theorem summable_preDivisorRiggedPrimeLinearTerm
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (a : DeningerHeightKothe) :
    Summable (preDivisorRiggedPrimeLinearTerm s a) := by
  have hbase : Summable (fun p : Nat.Primes =>
      ‖(a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      preDivisorRiggedPrimeAxis_injective
  refine Summable.of_norm_bounded hbase fun p => ?_
  rw [Real.norm_eq_abs, preDivisorRiggedPrimeLinearTerm, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrt : Real.sqrt (preDivisorRiggedPrimeWeight s p) ≤ 1 :=
    Real.sqrt_le_one.mpr (preDivisorRiggedPrimeWeight_mem_unit hs p).2
  calc
    Real.sqrt (preDivisorRiggedPrimeWeight s p) *
        |((a : DeningerPrimeLattice → ℂ)
          (preDivisorRiggedPrimeAxis p)).re| ≤
      1 * ‖(a : DeningerPrimeLattice → ℂ)
        (preDivisorRiggedPrimeAxis p)‖ := by
          exact mul_le_mul hsqrt (Complex.abs_re_le_norm _)
            (abs_nonneg _) (by positivity)
    _ = _ := one_mul _

/-- Common all-prime reservoir functional on the rapid Deninger test source. -/
def preDivisorRiggedPrimeLinear
    (s : ℂ) (a : DeningerHeightKothe) : ℝ :=
  ∑' p : Nat.Primes, preDivisorRiggedPrimeLinearTerm s a p

/-- The all-prime reservoir functional is bounded by the zeroth Köthe seminorm. -/
theorem abs_preDivisorRiggedPrimeLinear_le
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (a : DeningerHeightKothe) :
    |preDivisorRiggedPrimeLinear s a| ≤ deningerHeightSeminorm 0 a := by
  have hterm := summable_preDivisorRiggedPrimeLinearTerm hs a
  have haxis : Summable (fun p : Nat.Primes =>
      ‖(a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      preDivisorRiggedPrimeAxis_injective
  calc
    |preDivisorRiggedPrimeLinear s a| =
        ‖preDivisorRiggedPrimeLinear s a‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' p : Nat.Primes, ‖preDivisorRiggedPrimeLinearTerm s a p‖ :=
      norm_tsum_le_tsum_norm hterm.norm
    _ ≤ ∑' p : Nat.Primes,
        ‖(a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖ := by
      refine Summable.tsum_le_tsum (fun p => ?_) hterm.norm haxis
      rw [Real.norm_eq_abs, preDivisorRiggedPrimeLinearTerm, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hsqrt : Real.sqrt (preDivisorRiggedPrimeWeight s p) ≤ 1 :=
        Real.sqrt_le_one.mpr (preDivisorRiggedPrimeWeight_mem_unit hs p).2
      exact (mul_le_mul hsqrt (Complex.abs_re_le_norm _)
        (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
    _ ≤ ∑' m : DeningerPrimeLattice,
        ‖(a : DeningerPrimeLattice → ℂ) m‖ := by
      exact haxis.tsum_le_tsum_of_inj preDivisorRiggedPrimeAxis
        preDivisorRiggedPrimeAxis_injective (fun _ _ => norm_nonneg _)
        (fun _ => le_rfl) (deningerHeightKothe_summable_norm a)
    _ = deningerHeightSeminorm 0 a :=
      (deningerHeightSeminorm_zero_eq a).symm

/-- One coefficient of the diagonal part of the rigged prime form. -/
def preDivisorRiggedPrimeDiagonalTerm
    (s : ℂ) (a b : DeningerHeightKothe) (p : Nat.Primes) : ℝ :=
  preDivisorRiggedPrimeWeight s p *
    (((a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re) *
    (((b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re)

/-- The all-prime diagonal pairing is absolutely summable on every open-strip fibre. -/
theorem summable_preDivisorRiggedPrimeDiagonalTerm
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    Summable (preDivisorRiggedPrimeDiagonalTerm s a b) := by
  have hbase : Summable (fun p : Nat.Primes =>
      deningerHeightSeminorm 0 a *
        ‖(b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖) :=
    ((deningerHeightKothe_summable_norm b).comp_injective
      preDivisorRiggedPrimeAxis_injective).mul_left _
  refine Summable.of_norm_bounded hbase fun p => ?_
  rw [Real.norm_eq_abs, preDivisorRiggedPrimeDiagonalTerm, abs_mul, abs_mul]
  have hw := preDivisorRiggedPrimeWeight_mem_unit hs p
  have ha := deningerHeightKothe_norm_le a (preDivisorRiggedPrimeAxis p)
  calc
    |preDivisorRiggedPrimeWeight s p| *
        |((a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re| *
        |((b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re| ≤
      1 * deningerHeightSeminorm 0 a *
        ‖(b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖ := by
          gcongr
          · simpa [abs_of_nonneg hw.1] using hw.2
          · exact (Complex.abs_re_le_norm _).trans ha
          · exact Complex.abs_re_le_norm _
    _ = _ := by ring

/-- Diagonal all-prime part of the rigged source form. -/
def preDivisorRiggedPrimeDiagonal
    (s : ℂ) (a b : DeningerHeightKothe) : ℝ :=
  ∑' p : Nat.Primes, preDivisorRiggedPrimeDiagonalTerm s a b p

/-- Joint zeroth-seminorm bound for the all-prime diagonal pairing. -/
theorem abs_preDivisorRiggedPrimeDiagonal_le
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    |preDivisorRiggedPrimeDiagonal s a b| ≤
      deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b := by
  have hterm := summable_preDivisorRiggedPrimeDiagonalTerm hs a b
  have haxis : Summable (fun p : Nat.Primes =>
      ‖(b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖) :=
    (deningerHeightKothe_summable_norm b).comp_injective
      preDivisorRiggedPrimeAxis_injective
  calc
    |preDivisorRiggedPrimeDiagonal s a b| =
        ‖preDivisorRiggedPrimeDiagonal s a b‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' p : Nat.Primes,
        ‖preDivisorRiggedPrimeDiagonalTerm s a b p‖ :=
      norm_tsum_le_tsum_norm hterm.norm
    _ ≤ ∑' p : Nat.Primes,
        deningerHeightSeminorm 0 a *
          ‖(b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖ := by
      refine Summable.tsum_le_tsum (fun p => ?_) hterm.norm (haxis.mul_left _)
      rw [Real.norm_eq_abs, preDivisorRiggedPrimeDiagonalTerm, abs_mul, abs_mul]
      have hw := preDivisorRiggedPrimeWeight_mem_unit hs p
      have ha := deningerHeightKothe_norm_le a (preDivisorRiggedPrimeAxis p)
      calc
        |preDivisorRiggedPrimeWeight s p| *
            |((a : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re| *
            |((b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)).re| ≤
          1 * deningerHeightSeminorm 0 a *
            ‖(b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖ := by
              gcongr
              · simpa [abs_of_nonneg hw.1] using hw.2
              · exact (Complex.abs_re_le_norm _).trans ha
              · exact Complex.abs_re_le_norm _
        _ = _ := by ring
    _ = deningerHeightSeminorm 0 a *
        (∑' p : Nat.Primes,
          ‖(b : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis p)‖) :=
      tsum_mul_left
    _ ≤ deningerHeightSeminorm 0 a *
        (∑' m : DeningerPrimeLattice,
          ‖(b : DeningerPrimeLattice → ℂ) m‖) := by
      gcongr
      exact haxis.tsum_le_tsum_of_inj preDivisorRiggedPrimeAxis
        preDivisorRiggedPrimeAxis_injective (fun _ _ => norm_nonneg _)
        (fun _ => le_rfl) (deningerHeightKothe_summable_norm b)
    _ = _ := by rw [deningerHeightSeminorm_zero_eq b]

/--
All-prime rigged Krein form.  It is the positive diagonal prime pairing minus the square of one
common reservoir functional, with the pre-divisor source orientation retained before Xi selection.
-/
def preDivisorRiggedPrimeWittPairing
    (s : ℂ) (a b : DeningerHeightKothe) : ℝ :=
  preDivisorOrientation s *
    (preDivisorRiggedPrimeDiagonal s a b -
      preDivisorRiggedPrimeLinear s a * preDivisorRiggedPrimeLinear s b)

/-- **Rigged continuity law.**  The all-prime form is jointly bounded by `2 p₀(a) p₀(b)`. -/
theorem abs_preDivisorRiggedPrimeWittPairing_le
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    |preDivisorRiggedPrimeWittPairing s a b| ≤
      2 * deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b := by
  have ho : |preDivisorOrientation s| ≤ 1 := by
    rw [preDivisorOrientation]
    by_cases hp : 0 < preDivisorTailLog s
    · rw [Real.sign_of_pos hp]
      norm_num
    · by_cases hn : preDivisorTailLog s < 0
      · rw [Real.sign_of_neg hn]
        norm_num
      · have hz : preDivisorTailLog s = 0 := by
          exact le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
        rw [hz, Real.sign_zero]
        norm_num
  have hd := abs_preDivisorRiggedPrimeDiagonal_le hs a b
  have hla := abs_preDivisorRiggedPrimeLinear_le hs a
  have hlb := abs_preDivisorRiggedPrimeLinear_le hs b
  have hinside :
      |preDivisorRiggedPrimeDiagonal s a b -
          preDivisorRiggedPrimeLinear s a * preDivisorRiggedPrimeLinear s b| ≤
        |preDivisorRiggedPrimeDiagonal s a b| +
          |preDivisorRiggedPrimeLinear s a| *
            |preDivisorRiggedPrimeLinear s b| := by
    calc
      |preDivisorRiggedPrimeDiagonal s a b -
          preDivisorRiggedPrimeLinear s a * preDivisorRiggedPrimeLinear s b| ≤
        |preDivisorRiggedPrimeDiagonal s a b| +
          |preDivisorRiggedPrimeLinear s a * preDivisorRiggedPrimeLinear s b| :=
        abs_sub _ _
      _ = _ := by rw [abs_mul]
  rw [preDivisorRiggedPrimeWittPairing, abs_mul]
  calc
    |preDivisorOrientation s| *
        |preDivisorRiggedPrimeDiagonal s a b -
          preDivisorRiggedPrimeLinear s a * preDivisorRiggedPrimeLinear s b| ≤
      1 * (|preDivisorRiggedPrimeDiagonal s a b| +
        |preDivisorRiggedPrimeLinear s a| *
          |preDivisorRiggedPrimeLinear s b|) := by
            apply mul_le_mul ho
            · exact hinside
            · positivity
            · positivity
    _ ≤ 1 * (deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b +
        deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b) := by
      gcongr
    _ = 2 * deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b := by ring

/-! ## Reflection and wall laws -/

/-- Reflection preserves every unsigned prime weight. -/
@[simp] theorem preDivisorRiggedPrimeWeight_lineConj
    (s : ℂ) (p : Nat.Primes) :
    preDivisorRiggedPrimeWeight (preDivisorLineConj s) p =
      preDivisorRiggedPrimeWeight s p := by
  simp [preDivisorRiggedPrimeWeight]

/-- Reflection fixes the common unsigned reservoir functional. -/
@[simp] theorem preDivisorRiggedPrimeLinear_lineConj
    (s : ℂ) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeLinear (preDivisorLineConj s) a =
      preDivisorRiggedPrimeLinear s a := by
  rw [preDivisorRiggedPrimeLinear, preDivisorRiggedPrimeLinear]
  apply tsum_congr
  intro p
  simp [preDivisorRiggedPrimeLinearTerm]

/-- Reflection fixes the unsigned diagonal pairing. -/
@[simp] theorem preDivisorRiggedPrimeDiagonal_lineConj
    (s : ℂ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeDiagonal (preDivisorLineConj s) a b =
      preDivisorRiggedPrimeDiagonal s a b := by
  rw [preDivisorRiggedPrimeDiagonal, preDivisorRiggedPrimeDiagonal]
  apply tsum_congr
  intro p
  simp [preDivisorRiggedPrimeDiagonalTerm]

/-- **Global orientation law.**  Critical-line reflection negates the entire rigged form. -/
@[simp] theorem preDivisorRiggedPrimeWittPairing_lineConj
    (s : ℂ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing (preDivisorLineConj s) a b =
      -preDivisorRiggedPrimeWittPairing s a b := by
  simp [preDivisorRiggedPrimeWittPairing]

/-- Every prime weight vanishes on the reflection-fixed wall. -/
theorem preDivisorRiggedPrimeWeight_eq_zero_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) (p : Nat.Primes) :
    preDivisorRiggedPrimeWeight s p = 0 := by
  rw [preDivisorRiggedPrimeWeight, preDivisorPrimeCarrier]
  have hrate : preDivisorCenteredRate s = 0 := by
    rw [preDivisorCenteredRate, hs]
    norm_num
  rw [hrate]
  simp [primeGammaCofinalBocksteinCoefficient]

/-- **Wall radical.**  The full rigged form vanishes on the critical wall. -/
theorem preDivisorRiggedPrimeWittPairing_eq_zero_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s a b = 0 := by
  rw [preDivisorRiggedPrimeWittPairing]
  have ho : preDivisorOrientation s = 0 := by
    rw [preDivisorOrientation, preDivisorTailLog, hs]
    norm_num
  rw [ho, zero_mul]

/-! ## Exact finite prime-axis restrictions -/

/-- Unit test vector at one positive prime axis. -/
def preDivisorRiggedPrimeDelta (p : Nat.Primes) : DeningerHeightKothe :=
  deningerKotheDelta deningerHeightKotheData (preDivisorRiggedPrimeAxis p)

/-- Prime-axis delta coordinates retain their labels exactly. -/
@[simp] theorem preDivisorRiggedPrimeDelta_axis
    (p q : Nat.Primes) :
    ((preDivisorRiggedPrimeDelta p : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis q) =
      if q = p then 1 else 0 := by
  rw [preDivisorRiggedPrimeDelta, deningerKotheDelta_coe, Pi.single_apply]
  by_cases hqp : q = p
  · subst q
    simp
  · have haxis : preDivisorRiggedPrimeAxis q ≠
        preDivisorRiggedPrimeAxis p :=
      preDivisorRiggedPrimeAxis_injective.ne hqp
    simp [hqp, haxis]

/-- The common reservoir functional reads the square root of the selected prime weight. -/
theorem preDivisorRiggedPrimeLinear_delta
    (s : ℂ) (p : Nat.Primes) :
    preDivisorRiggedPrimeLinear s (preDivisorRiggedPrimeDelta p) =
      Real.sqrt (preDivisorRiggedPrimeWeight s p) := by
  rw [preDivisorRiggedPrimeLinear, tsum_eq_single p]
  · simp [preDivisorRiggedPrimeLinearTerm]
  · intro q hq
    simp [preDivisorRiggedPrimeLinearTerm, hq]

/-- The diagonal pairing of two prime deltas is the corresponding weighted Kronecker delta. -/
theorem preDivisorRiggedPrimeDiagonal_delta
    (s : ℂ) (p q : Nat.Primes) :
    preDivisorRiggedPrimeDiagonal s
        (preDivisorRiggedPrimeDelta p) (preDivisorRiggedPrimeDelta q) =
      if p = q then preDivisorRiggedPrimeWeight s p else 0 := by
  by_cases hpq : p = q
  · subst q
    rw [preDivisorRiggedPrimeDiagonal, tsum_eq_single p]
    · simp [preDivisorRiggedPrimeDiagonalTerm]
    · intro r hr
      simp [preDivisorRiggedPrimeDiagonalTerm, hr]
  · rw [preDivisorRiggedPrimeDiagonal]
    have hzero : (fun r : Nat.Primes =>
        preDivisorRiggedPrimeDiagonalTerm s
          (preDivisorRiggedPrimeDelta p) (preDivisorRiggedPrimeDelta q) r) = 0 := by
      funext r
      by_cases hrp : r = p
      · subst r
        simp [preDivisorRiggedPrimeDiagonalTerm, hpq]
      · simp [preDivisorRiggedPrimeDiagonalTerm, hrp]
    rw [hzero]
    change tsum (fun _ : Nat.Primes => (0 : ℝ)) = _
    rw [tsum_zero]
    simp [hpq]

/-- The rigged form's delta kernel is exactly the signed shared-reservoir kernel. -/
theorem preDivisorRiggedPrimeWittPairing_delta
    (s : ℂ) (p q : Nat.Primes) :
    preDivisorRiggedPrimeWittPairing s
        (preDivisorRiggedPrimeDelta p) (preDivisorRiggedPrimeDelta q) =
      if p = q then 0 else
        -preDivisorOrientation s *
          (Real.sqrt (preDivisorRiggedPrimeWeight s p) *
            Real.sqrt (preDivisorRiggedPrimeWeight s q)) := by
  rw [preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeDiagonal_delta,
    preDivisorRiggedPrimeLinear_delta,
    preDivisorRiggedPrimeLinear_delta]
  by_cases hpq : p = q
  · subst q
    simp only [if_true]
    have hw : 0 ≤ preDivisorRiggedPrimeWeight s p := abs_nonneg _
    rw [Real.mul_self_sqrt hw]
    ring
  · rw [if_neg hpq, if_neg hpq]
    ring

/-- Finite Gram restriction of the all-prime rigged form. -/
def preDivisorRiggedPrimeWittGram {m : ℕ}
    (s : ℂ) (p : Fin m → Nat.Primes) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => preDivisorRiggedPrimeWittPairing s
    (preDivisorRiggedPrimeDelta (p i))
    (preDivisorRiggedPrimeDelta (p j))

/--
**Coefficient-faithful completion law.**  Every injective finite prime-axis Gram restriction of
the one all-prime rigged form is exactly the corpus pre-divisor shared-reservoir matrix.
-/
theorem preDivisorRiggedPrimeWittGram_eq_sharedReservoirMatrix
    {m : ℕ} (s : ℂ) (p : Fin m → Nat.Primes)
    (hp : Function.Injective p) :
    preDivisorRiggedPrimeWittGram s p =
      preDivisorSharedReservoirMatrix s p := by
  ext i j
  rw [preDivisorRiggedPrimeWittGram,
    preDivisorRiggedPrimeWittPairing_delta]
  rw [preDivisorSharedReservoirMatrix,
    orientedSourceSharedReservoirMatrix_apply]
  · by_cases hij : i = j
    · rw [if_pos hij, if_pos (congrArg p hij)]
    · rw [if_neg hij, if_neg (hp.ne hij)]
      rfl
  · intro k
    exact abs_nonneg _

/-! ## Exact inertia inherited by every finite restriction -/

/-- On the left half-strip the pre-divisor orientation is positive. -/
theorem preDivisorOrientation_eq_one_of_left
    (s : ℂ) (hleft : s.re < 1 / 2) :
    preDivisorOrientation s = 1 := by
  rw [preDivisorOrientation, Real.sign_of_pos]
  rw [preDivisorTailLog]
  exact mul_pos (sub_pos.mpr hleft) (Real.log_pos (by norm_num))

/-- Left-oriented finite restrictions are the positive weighted reservoir form. -/
theorem preDivisorSharedReservoirMatrix_toQuadraticForm_of_left
    {m : ℕ} (s : ℂ) (hleft : s.re < 1 / 2)
    (p : Fin m → Nat.Primes) :
    (preDivisorSharedReservoirMatrix s p).toQuadraticForm' =
      reservoirWeightedForm (preDivisorSharedWeights s p) := by
  rw [preDivisorSharedReservoirMatrix,
    preDivisorOrientation_eq_one_of_left s hleft]
  exact orientedSourceSharedReservoirMatrix_toQuadraticForm_one
    (fun i => (preDivisorSharedWeights_pos_of_offLine s
      (ne_of_lt hleft) p i).le)

/-- Every left-half finite Gram restriction has exact inertia `(m-1,1,0)`. -/
theorem preDivisorRiggedPrimeWittGram_inertia_of_left
    {m : ℕ} (s : ℂ) (hleft : s.re < 1 / 2)
    (p : Fin m → Nat.Primes) (hp : Function.Injective p) (hm : 2 ≤ m) :
    sigPos (preDivisorRiggedPrimeWittGram s p).toQuadraticForm' = m - 1 ∧
      sigNeg (preDivisorRiggedPrimeWittGram s p).toQuadraticForm' = 1 ∧
      Module.finrank ℝ
        (preDivisorRiggedPrimeWittGram s p).toQuadraticForm'.radical = 0 := by
  rw [preDivisorRiggedPrimeWittGram_eq_sharedReservoirMatrix s p hp,
    preDivisorSharedReservoirMatrix_toQuadraticForm_of_left s hleft p]
  have hw : ∀ i, 0 < preDivisorSharedWeights s p i :=
    fun i => preDivisorSharedWeights_pos_of_offLine s (ne_of_lt hleft) p i
  exact ⟨reservoirWeightedForm_sigPos hw hm,
    reservoirWeightedForm_sigNeg hw hm,
    reservoirWeightedForm_radical_finrank hw hm⟩

/-- Every right-half finite Gram restriction has exact reflected inertia `(1,m-1,0)`. -/
theorem preDivisorRiggedPrimeWittGram_inertia_of_right
    {m : ℕ} (s : ℂ) (hright : 1 / 2 < s.re)
    (p : Fin m → Nat.Primes) (hp : Function.Injective p) (hm : 2 ≤ m) :
    sigPos (preDivisorRiggedPrimeWittGram s p).toQuadraticForm' = 1 ∧
      sigNeg (preDivisorRiggedPrimeWittGram s p).toQuadraticForm' = m - 1 ∧
      Module.finrank ℝ
        (preDivisorRiggedPrimeWittGram s p).toQuadraticForm'.radical = 0 := by
  rw [preDivisorRiggedPrimeWittGram_eq_sharedReservoirMatrix s p hp,
    preDivisorSharedReservoirMatrix_toQuadraticForm_of_right s hright p]
  have hw : ∀ i, 0 < preDivisorSharedWeights s p i :=
    fun i => preDivisorSharedWeights_pos_of_offLine s (ne_of_gt hright) p i
  refine ⟨?_, ?_, ?_⟩
  · rw [sigPos_neg]
    exact reservoirWeightedForm_sigNeg hw hm
  · rw [sigNeg_neg]
    exact reservoirWeightedForm_sigPos hw hm
  · have hsignature := (-(reservoirWeightedForm
        (preDivisorSharedWeights s p))).sigPos_add_sigNeg_add_radical
    rw [sigPos_neg, sigNeg_neg, reservoirWeightedForm_sigNeg hw hm,
      reservoirWeightedForm_sigPos hw hm, Module.finrank_fin_fun ℝ] at hsignature
    omega

/-! ## Symmetry and real bilinearity -/

/-- The diagonal all-prime pairing is symmetric. -/
theorem preDivisorRiggedPrimeDiagonal_comm
    (s : ℂ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeDiagonal s a b =
      preDivisorRiggedPrimeDiagonal s b a := by
  rw [preDivisorRiggedPrimeDiagonal, preDivisorRiggedPrimeDiagonal]
  apply tsum_congr
  intro p
  simp only [preDivisorRiggedPrimeDiagonalTerm]
  ring

/-- The completed rigged prime form is symmetric. -/
theorem preDivisorRiggedPrimeWittPairing_comm
    (s : ℂ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s a b =
      preDivisorRiggedPrimeWittPairing s b a := by
  rw [preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeDiagonal_comm s a b]
  ring

/-- The common reservoir functional is additive on every open-strip fibre. -/
theorem preDivisorRiggedPrimeLinear_add
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeLinear s (a + b) =
      preDivisorRiggedPrimeLinear s a +
        preDivisorRiggedPrimeLinear s b := by
  rw [preDivisorRiggedPrimeLinear, preDivisorRiggedPrimeLinear,
    preDivisorRiggedPrimeLinear,
    ← (summable_preDivisorRiggedPrimeLinearTerm hs a).tsum_add
      (summable_preDivisorRiggedPrimeLinearTerm hs b)]
  apply tsum_congr
  intro p
  simp [preDivisorRiggedPrimeLinearTerm]
  ring

/-- The common reservoir functional is homogeneous for real scalars. -/
theorem preDivisorRiggedPrimeLinear_smul
    (s : ℂ) (c : ℝ) (a : DeningerHeightKothe) :
    preDivisorRiggedPrimeLinear s (c • a) =
      c * preDivisorRiggedPrimeLinear s a := by
  rw [preDivisorRiggedPrimeLinear, preDivisorRiggedPrimeLinear,
    ← tsum_mul_left]
  apply tsum_congr
  intro p
  simp [preDivisorRiggedPrimeLinearTerm]
  ring

/-- The diagonal pairing is additive in its first argument on every open-strip fibre. -/
theorem preDivisorRiggedPrimeDiagonal_add_left
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b c : DeningerHeightKothe) :
    preDivisorRiggedPrimeDiagonal s (a + b) c =
      preDivisorRiggedPrimeDiagonal s a c +
        preDivisorRiggedPrimeDiagonal s b c := by
  rw [preDivisorRiggedPrimeDiagonal, preDivisorRiggedPrimeDiagonal,
    preDivisorRiggedPrimeDiagonal,
    ← (summable_preDivisorRiggedPrimeDiagonalTerm hs a c).tsum_add
      (summable_preDivisorRiggedPrimeDiagonalTerm hs b c)]
  apply tsum_congr
  intro p
  simp [preDivisorRiggedPrimeDiagonalTerm]
  ring

/-- The diagonal pairing is homogeneous in its first argument for real scalars. -/
theorem preDivisorRiggedPrimeDiagonal_smul_left
    (s : ℂ) (c : ℝ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeDiagonal s (c • a) b =
      c * preDivisorRiggedPrimeDiagonal s a b := by
  rw [preDivisorRiggedPrimeDiagonal, preDivisorRiggedPrimeDiagonal,
    ← tsum_mul_left]
  apply tsum_congr
  intro p
  simp [preDivisorRiggedPrimeDiagonalTerm]
  ring

/-- The rigged prime form is additive in its first argument on the open critical strip. -/
theorem preDivisorRiggedPrimeWittPairing_add_left
    {s : ℂ} (hs : 0 < s.re ∧ s.re < 1)
    (a b c : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s (a + b) c =
      preDivisorRiggedPrimeWittPairing s a c +
        preDivisorRiggedPrimeWittPairing s b c := by
  rw [preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeDiagonal_add_left hs,
    preDivisorRiggedPrimeLinear_add hs]
  ring

/-- The rigged prime form is homogeneous in its first argument for real scalars. -/
theorem preDivisorRiggedPrimeWittPairing_smul_left
    (s : ℂ) (c : ℝ) (a b : DeningerHeightKothe) :
    preDivisorRiggedPrimeWittPairing s (c • a) b =
      c * preDivisorRiggedPrimeWittPairing s a b := by
  rw [preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeWittPairing,
    preDivisorRiggedPrimeDiagonal_smul_left,
    preDivisorRiggedPrimeLinear_smul]
  ring

/-! ## Closed all-prime capstones -/

/-- The canonical enumeration of ordinary primes is injective. -/
theorem preDivisorRiggedNthPrimePoint_injective :
    Function.Injective nthPrimePoint := by
  intro m n hmn
  apply (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
  exact congrArg Subtype.val hmn

/--
**Infinite negative-index exhaustion.**  On every right-half pre-divisor fibre, the one rigged
source form contains injective finite prime-axis restrictions with negative index `m-1` for every
`m ≥ 2`.
-/
theorem preDivisorRiggedPrimeWittPairing_unboundedNegativeIndex_right :
    ∀ m : ℕ, 2 ≤ m → ∀ s : ℂ, 1 / 2 < s.re →
      ∃ p : Fin m → Nat.Primes,
        Function.Injective p ∧
          sigNeg (preDivisorRiggedPrimeWittGram s p).toQuadraticForm' = m - 1 := by
  intro m hm s hright
  let p : Fin m → Nat.Primes := fun i => nthPrimePoint i
  have hp : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    exact preDivisorRiggedNthPrimePoint_injective hij
  exact ⟨p, hp,
    (preDivisorRiggedPrimeWittGram_inertia_of_right s hright p hp hm).2.1⟩

/--
**Infinite positive-index exhaustion.**  On every left-half pre-divisor fibre, the reflected rigged
source form contains finite prime-axis restrictions with positive index `m-1` for every `m ≥ 2`.
-/
theorem preDivisorRiggedPrimeWittPairing_unboundedPositiveIndex_left :
    ∀ m : ℕ, 2 ≤ m → ∀ s : ℂ, s.re < 1 / 2 →
      ∃ p : Fin m → Nat.Primes,
        Function.Injective p ∧
          sigPos (preDivisorRiggedPrimeWittGram s p).toQuadraticForm' = m - 1 := by
  intro m hm s hleft
  let p : Fin m → Nat.Primes := fun i => nthPrimePoint i
  have hp : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    exact preDivisorRiggedNthPrimePoint_injective hij
  exact ⟨p, hp,
    (preDivisorRiggedPrimeWittGram_inertia_of_left s hleft p hp hm).1⟩

/--
**SC rigged-phase-object capstone.**  One pre-divisor all-prime form is jointly Köthe-bounded,
reflection-odd, coefficient-faithful on every injective finite prime packet, and carries the exact
unbounded reflected inertia forced by source-horizontal packets.
-/
theorem preDivisorRiggedPrimeWittPhaseObject_capstone :
    (∀ s : ℂ, 0 < s.re ∧ s.re < 1 → ∀ a b : DeningerHeightKothe,
      |preDivisorRiggedPrimeWittPairing s a b| ≤
        2 * deningerHeightSeminorm 0 a * deningerHeightSeminorm 0 b) ∧
    (∀ s : ℂ, ∀ a b : DeningerHeightKothe,
      preDivisorRiggedPrimeWittPairing (preDivisorLineConj s) a b =
        -preDivisorRiggedPrimeWittPairing s a b) ∧
    (∀ m : ℕ, ∀ s : ℂ, ∀ p : Fin m → Nat.Primes,
      Function.Injective p →
        preDivisorRiggedPrimeWittGram s p =
          preDivisorSharedReservoirMatrix s p) ∧
    (∀ m : ℕ, 2 ≤ m → ∀ s : ℂ, 1 / 2 < s.re →
      ∃ p : Fin m → Nat.Primes,
        Function.Injective p ∧
          sigNeg (preDivisorRiggedPrimeWittGram s p).toQuadraticForm' = m - 1) := by
  refine ⟨?_, ?_, ?_, preDivisorRiggedPrimeWittPairing_unboundedNegativeIndex_right⟩
  · intro s hs a b
    exact abs_preDivisorRiggedPrimeWittPairing_le hs a b
  · intro s a b
    exact preDivisorRiggedPrimeWittPairing_lineConj s a b
  · intro m s p hp
    exact preDivisorRiggedPrimeWittGram_eq_sharedReservoirMatrix s p hp

end

end RHTower
