import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaCompletedMatrixLanding
import GaloisForLFunctions.RHTower.DirichletCharacterCoprimePrimitiveProduct
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicPrimitive
import GaloisForLFunctions.RHTower.MirrorPencil

/-!
# Primitive completed interaction carried by the Euler--Wick quadratic gauge

The literal EWQ residue profile assigns value `1` at the ramified primes `2` and `3`, whereas
the primitive quadratic Dirichlet character modulo twelve vanishes there.  This file performs the
canonical two-column ramification projection before any divisor is selected.  Every unramified
prime-depth coefficient is unchanged, and the projected Euler logarithm exponentiates to the
literal primitive `L(s, χ₁₂)` on `re s > 1`.

The hand-built EWQ character is proved equal to a product of lifted primitive characters of
conductors `3` and `4`.  Consequently it is primitive, quadratic, self-dual, and its globally
completed interaction satisfies the actual constant-root-number functional equation.  This closes
the analytic-continuation part of the EWQ open core; no continuation hypothesis is introduced.
-/

namespace GaloisForLFunctions.RHTower

open Complex LSeries ArithmeticFunction
open GaloisForLFunctions.HTGeometry
open scoped LSeries.notation

noncomputable section

/-- The modulo-three EWQ character is the certified primitive odd-prime quadratic character. -/
theorem quadraticCharacterThree_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterThree := by
  change DirichletCharacter.IsPrimitive
    (_root_.RHTower.oddPrimeQuadraticCharacter
      (⟨3, by norm_num⟩ : _root_.RHTower.OddPrime))
  exact _root_.RHTower.oddPrimeQuadraticCharacter_isPrimitive
    (⟨3, by norm_num⟩ : _root_.RHTower.OddPrime)

/-- Product of the two local EWQ characters after lifting both to level twelve. -/
def quadraticCharacterTwelveCanonical : DirichletCharacter ℂ 12 :=
  DirichletCharacter.changeLevel (by norm_num : 3 ∣ 12) quadraticCharacterThree *
    DirichletCharacter.changeLevel (by norm_num : 4 ∣ 12)
      _root_.RHTower.quadraticCharacterFour

/-- The CRT-defined EWQ character is exactly the lifted local product, including on nonunits. -/
theorem quadraticCharacterTwelve_eq_canonical :
    quadraticCharacterTwelve = quadraticCharacterTwelveCanonical := by
  apply MulChar.ext'
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  by_cases hz : IsCoprime z (12 : ℤ)
  · have hcoord :
        ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4)
            (z : ZMod 12) = ((z : ZMod 3), (z : ZMod 4)) := by
      exact map_intCast _ z
    rw [quadraticCharacterTwelve, _root_.RHTower.crtProductCharacter_apply, hcoord,
      quadraticCharacterTwelveCanonical, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' quadraticCharacterThree
        (by norm_num : 3 ∣ 12) hz,
      DirichletCharacter.changeLevel_eq_cast_of_dvd'
        _root_.RHTower.quadraticCharacterFour (by norm_num : 4 ∣ 12) hz]
  · have hnonunit : ¬ IsUnit ((z : ℤ) : ZMod 12) := by
      rw [ZMod.coe_int_isUnit_iff_isCoprime]
      exact fun h => hz h.symm
    rw [MulChar.map_nonunit _ hnonunit, MulChar.map_nonunit _ hnonunit]

/-- The EWQ joint character has its full conductor twelve. -/
theorem quadraticCharacterTwelve_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterTwelve := by
  rw [quadraticCharacterTwelve_eq_canonical]
  exact _root_.RHTower.lifted_coprime_product_isPrimitive_at_level
    quadraticCharacterThree _root_.RHTower.quadraticCharacterFour
    (by norm_num : Nat.Coprime 3 4)
    quadraticCharacterThree_isPrimitive
    _root_.RHTower.quadraticCharacterFour_isPrimitive
    (by norm_num : 3 ∣ 12) (by norm_num : 4 ∣ 12) (by norm_num : 12 = 3 * 4)

/-- The joint EWQ character remains quadratic after CRT bundling. -/
theorem quadraticCharacterTwelve_isQuadratic : quadraticCharacterTwelve.IsQuadratic := by
  exact _root_.RHTower.crtProductCharacter_isQuadratic
    (ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4))
    quadraticCharacterThree _root_.RHTower.quadraticCharacterFour
    ((quadraticChar_isQuadratic (ZMod 3)).comp (Int.castRingHom ℂ))
    _root_.RHTower.quadraticCharacterFour_isQuadratic

/-- Quadraticity makes the primitive EWQ carrier literally self-dual. -/
theorem quadraticCharacterTwelve_inv : quadraticCharacterTwelve⁻¹ = quadraticCharacterTwelve :=
  quadraticCharacterTwelve_isQuadratic.inv

/-- The two odd local residue gauges have even joint parity. -/
theorem quadraticCharacterTwelve_even : quadraticCharacterTwelve.Even := by
  change quadraticCharacterTwelve (-1 : ZMod 12) = 1
  rw [quadraticCharacterTwelve, _root_.RHTower.crtProductCharacter_apply]
  have hcoord :
      ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4) (-1 : ZMod 12) =
        ((-1 : ZMod 3), (-1 : ZMod 4)) := by
    exact map_neg (ZMod.chineseRemainder (by norm_num : Nat.Coprime 3 4)) 1
  rw [hcoord]
  change quadraticCharacterThreeUnit (-1) * quadraticCharacterFourUnit (-1) = 1
  rw [quadraticCharacterThreeUnit_neg_one, quadraticCharacterFourUnit_neg_one]
  ring

/-- The primitive EWQ logarithmic coefficient at a prime-power clock coordinate. -/
def eulerWickQuadraticPrimitiveEulerLogReplica (x : PrimePowerClockIndex) : ℂ :=
  quadraticCharacterTwelve (x.1 : ℕ) ^ (x.2 + 1) / ((x.2 + 1 : ℕ) : ℂ)

/-- Projected arithmetic source: the raw EWQ logarithm with both ramified prime columns removed. -/
def eulerWickQuadraticPrimitiveEulerLogSource : ArithmeticFunction ℂ :=
  arithmeticFunctionOfPrimePowerProfile eulerWickQuadraticPrimitiveEulerLogReplica

/-- Primitive projection leaves every unramified prime-depth coefficient unchanged. -/
theorem eulerWickQuadraticPrimitiveEulerLogReplica_eq_raw_of_isUnit
    (x : PrimePowerClockIndex) (hx : IsUnit (((x.1 : ℕ) : ZMod 12))) :
    eulerWickQuadraticPrimitiveEulerLogReplica x =
      eulerWickQuadraticEulerLogReplica x := by
  rw [eulerWickQuadraticPrimitiveEulerLogReplica, eulerWickQuadraticEulerLogReplica,
    eulerWickQuadraticDepthCharacter,
    quadraticResidueProductPrimeCoefficient_eq_quadraticCharacterTwelve_of_isUnit x.1 hx]

/-- Primitive projection kills every depth over either ramified prime. -/
theorem eulerWickQuadraticPrimitiveEulerLogReplica_eq_zero_of_not_isUnit
    (x : PrimePowerClockIndex) (hx : ¬ IsUnit (((x.1 : ℕ) : ZMod 12))) :
    eulerWickQuadraticPrimitiveEulerLogReplica x = 0 := by
  have hchar : quadraticCharacterTwelve (x.1 : ℕ) = 0 :=
    MulChar.map_nonunit quadraticCharacterTwelve hx
  simp [eulerWickQuadraticPrimitiveEulerLogReplica, hchar]

/-- Exact two-column projection law at every prime and every valuation depth. -/
theorem eulerWickQuadraticPrimitiveEulerLogReplica_eq_ite
    (x : PrimePowerClockIndex) :
    eulerWickQuadraticPrimitiveEulerLogReplica x =
      if IsUnit (((x.1 : ℕ) : ZMod 12)) then eulerWickQuadraticEulerLogReplica x else 0 := by
  by_cases hx : IsUnit (((x.1 : ℕ) : ZMod 12))
  · rw [if_pos hx, eulerWickQuadraticPrimitiveEulerLogReplica_eq_raw_of_isUnit x hx]
  · rw [if_neg hx, eulerWickQuadraticPrimitiveEulerLogReplica_eq_zero_of_not_isUnit x hx]

theorem norm_eulerWickQuadraticPrimitiveEulerLogSource_le_one (n : ℕ) :
    ‖eulerWickQuadraticPrimitiveEulerLogSource n‖ ≤ 1 := by
  by_cases hpow : IsPrimePow n
  · let x : PrimePowerClockIndex := Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
    have hx := congrArg Subtype.val
      (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
    have hn : (x.1 : Nat) ^ (x.2 + 1) = n := by
      simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using! hx
    rw [← hn]
    have hprimitive := primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile
      eulerWickQuadraticPrimitiveEulerLogReplica x
    change eulerWickQuadraticPrimitiveEulerLogSource
      ((x.1 : Nat) ^ (x.2 + 1)) =
        eulerWickQuadraticPrimitiveEulerLogReplica x at hprimitive
    rw [hprimitive, eulerWickQuadraticPrimitiveEulerLogReplica_eq_ite]
    split_ifs with hunit
    · have hraw := primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile
        eulerWickQuadraticEulerLogReplica x
      change eulerWickQuadraticEulerLogCharacterSource
        ((x.1 : Nat) ^ (x.2 + 1)) = eulerWickQuadraticEulerLogReplica x at hraw
      rw [← hraw]
      exact norm_eulerWickQuadraticEulerLogCharacterSource_le_one _
    · norm_num
  · simp [eulerWickQuadraticPrimitiveEulerLogSource,
      arithmeticFunctionOfPrimePowerProfile, hpow]

theorem eulerWickQuadraticPrimitiveEulerLogSource_summable
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable eulerWickQuadraticPrimitiveEulerLogSource s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => norm_eulerWickQuadraticPrimitiveEulerLogSource_le_one n) hs

/-- The projected source is the literal Euler logarithm of the primitive character. -/
theorem LSeries_eulerWickQuadraticPrimitiveEulerLogSource_eq_primeLog
    {s : ℂ} (hs : 1 < s.re) :
    LSeries eulerWickQuadraticPrimitiveEulerLogSource s =
      ∑' p : Nat.Primes,
        -Complex.log (1 - quadraticCharacterTwelve p * (p : ℂ) ^ (-s)) := by
  rw [LSeries]
  have hsum : Summable (LSeries.term eulerWickQuadraticPrimitiveEulerLogSource s) :=
    eulerWickQuadraticPrimitiveEulerLogSource_summable hs
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hsum]
  · apply tsum_congr
    intro p
    have hnorm : ‖quadraticCharacterTwelve p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul]
      have hp_le : ‖quadraticCharacterTwelve p‖ ≤ 1 := by
        rcases quadraticCharacterTwelve_isQuadratic (p : ZMod 12) with h | h | h <;>
          rw [h] <;> norm_num
      have hpow_lt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast p.prop.pos), Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.prop.one_lt) (by linarith)
      calc
        ‖quadraticCharacterTwelve p‖ * ‖(p : ℂ) ^ (-s)‖ ≤
            1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hp_le (norm_nonneg _)
        _ < 1 := by simpa using hpow_lt
    have hseries := Complex.hasSum_taylorSeries_neg_log hnorm
    rw [← hseries.tsum_eq, hseries.summable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, div_zero, zero_add]
    apply tsum_congr
    intro k
    rw [LSeries.term_of_ne_zero (pow_ne_zero (k + 1) p.prop.ne_zero)]
    have hcoord := primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile
      eulerWickQuadraticPrimitiveEulerLogReplica (p, k)
    change eulerWickQuadraticPrimitiveEulerLogSource ((p : Nat) ^ (k + 1)) =
      eulerWickQuadraticPrimitiveEulerLogReplica (p, k) at hcoord
    rw [hcoord, eulerWickQuadraticPrimitiveEulerLogReplica]
    rw [mul_pow]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    rw [← Complex.cpow_nat_mul]
    rw [show ((k + 1 : ℕ) : ℂ) * (-s) = -(((k + 1 : ℕ) : ℂ) * s) by ring,
      Complex.cpow_neg]
    push_cast
    ring
  · intro n hn
    by_contra hpp
    change ¬ IsPrimePow n at hpp
    apply hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0]
      simp [eulerWickQuadraticPrimitiveEulerLogSource,
        arithmeticFunctionOfPrimePowerProfile, hpp]

/-- **Coefficient-faithful primitive landing.**  Exponentiating the projected EWQ logarithm gives
the actual primitive Dirichlet L-function on its Euler half-plane. -/
theorem exp_LSeries_eulerWickQuadraticPrimitiveEulerLogSource_eq_LFunction
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries eulerWickQuadraticPrimitiveEulerLogSource s) =
      DirichletCharacter.LFunction quadraticCharacterTwelve s := by
  rw [LSeries_eulerWickQuadraticPrimitiveEulerLogSource_eq_primeLog hs,
    DirichletCharacter.LSeries_eulerProduct_exp_log quadraticCharacterTwelve hs,
    ← DirichletCharacter.LFunction_eq_LSeries quadraticCharacterTwelve hs]

/-- Globally completed primitive interaction exposed by the EWQ joint residue class. -/
def eulerWickQuadraticPrimitiveCompletedInteraction : ℂ → ℂ :=
  _root_.RHTower.dirichletXi quadraticCharacterTwelve

/-- The primitive completed EWQ interaction is entire. -/
theorem eulerWickQuadraticPrimitiveCompletedInteraction_differentiable :
    Differentiable ℂ eulerWickQuadraticPrimitiveCompletedInteraction := by
  have hne : quadraticCharacterTwelve ≠ 1 := by
    intro h
    have hp := quadraticCharacterTwelve_isPrimitive
    rw [DirichletCharacter.isPrimitive_def, h,
      DirichletCharacter.conductor_one] at hp
    norm_num at hp
  change Differentiable ℂ (fun s : ℂ =>
    (12 : ℂ) ^ (s / 2) * DirichletCharacter.completedLFunction quadraticCharacterTwelve s)
  apply Differentiable.mul
  · apply Differentiable.const_cpow (differentiable_id.div_const (2 : ℂ))
    exact Or.inl (by norm_num)
  · exact DirichletCharacter.differentiable_completedLFunction hne

/-- **Global EWQ functional equation.**  The completed interaction reflects into itself with one
constant root number; no analytic-continuation or functional-equation premise remains. -/
theorem eulerWickQuadraticPrimitiveCompletedInteraction_one_sub (s : ℂ) :
    eulerWickQuadraticPrimitiveCompletedInteraction (1 - s) =
      quadraticCharacterTwelve.rootNumber *
        eulerWickQuadraticPrimitiveCompletedInteraction s := by
  have h := _root_.RHTower.dirichletXi_one_sub
    quadraticCharacterTwelve_isPrimitive s
  rw [quadraticCharacterTwelve_inv] at h
  exact h

end

end GaloisForLFunctions.RHTower
