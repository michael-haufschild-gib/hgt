import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheQuotientIncidenceKernelIsIndefinite

/-!
# The dilation inversion law of the source

The dilation form is indefinite on arbitrary rows, so the continuation sign can only come from a
property the actual source has and a general row does not.  Here is such a property, exact and
unconditional.

The damping twist `f ↦ (n ↦ f(n) n^{-ε})` is a ring homomorphism of the Dirichlet ring
(`dampedTwist_mul`, `dampedTwist_one`), so the damped Möbius row inverts the damped unit row:
`μ_ε * ζ_ε = δ`.  Convolving with the undamped unit and summing a prefix with the hyperbola
rearrangement gives the **inversion law**

`Σ_{j ≤ n} j^{-ε} A^raw_ε(⌊n/j⌋) = n`  (`sum_rpow_mul_rawPrefix_eq`),

and, after the pole subtraction,

`Σ_{j ≤ n} j^{-ε} A_ε(⌊n/j⌋) = n − m₀(ε) Σ_{j ≤ n} j^{-ε} ⌊n/j⌋`
(`sum_rpow_mul_centeredPrefix_eq`).

So one positive-weight dilation average of the centred source is *explicitly computable* at every
horizon and every damping: the source carries an exact linear constraint, with positive weights,
against the same kind of dilation kernel that the signed work pairs it with.  A general row obeys
no such constraint, which is precisely the gap the indefiniteness of the quotient incidence kernel
leaves open.  One immediate consequence: the centred source cannot stay below a negative level
across a whole dilation range (`exists_centeredPrefix_ge_of_dilation_law`).
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The damping twist is a ring homomorphism of the Dirichlet ring -/

/-- The damping twist of an arithmetic function: `f(n) ↦ f(n) n^{-ε}`. -/
def dampedTwist (ε : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => f n * (n : ℝ) ^ (-ε), by simp⟩

@[simp] theorem dampedTwist_apply (ε : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    dampedTwist ε f n = f n * (n : ℝ) ^ (-ε) := rfl

/-- The twist is multiplicative for Dirichlet convolution: the weight `n^{-ε}` is completely
multiplicative. -/
theorem dampedTwist_mul (ε : ℝ) (f g : ArithmeticFunction ℝ) :
    dampedTwist ε (f * g) = dampedTwist ε f * dampedTwist ε g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [dampedTwist_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  rw [dampedTwist_apply, dampedTwist_apply, ← hprod]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem dampedTwist_one (ε : ℝ) : dampedTwist ε (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · simp [hn]

/-- **The damped Möbius row inverts the damped unit row.** -/
theorem dampedTwist_moebius_mul_dampedTwist_zeta (ε : ℝ) :
    dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * dampedTwist ε (↑ζ : ArithmeticFunction ℝ) = 1 := by
  rw [← dampedTwist_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta, dampedTwist_one]

/-! ## §2. The inversion law for the source prefix -/

/-- The source row is the damped Möbius row convolved with the unit row. -/
theorem pmPowerDampedDivisorCoeff_eq_mul (ε : ℝ) (k : ℕ) :
    pmPowerDampedDivisorCoeff ε k =
      (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * ↑ζ) k := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  unfold pmPowerDampedDivisorCoeff
  exact Finset.sum_congr rfl fun d _ => by rw [dampedTwist_apply]; simp

/-- The damped unit dilation of the source row is the unit row: a cell-by-cell inversion. -/
theorem sum_divisors_rpow_mul_coeff (ε : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (∑ j ∈ k.divisors, (j : ℝ) ^ (-ε) * pmPowerDampedDivisorCoeff ε (k / j)) = 1 := by
  have hk0 : k ≠ 0 := by omega
  have hcoeff : (fun m : ℕ => pmPowerDampedDivisorCoeff ε m) =
      fun m : ℕ => (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * ↑ζ) m :=
    funext (pmPowerDampedDivisorCoeff_eq_mul ε)
  have hprod : dampedTwist ε (↑ζ : ArithmeticFunction ℝ) *
      (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * ↑ζ) = (↑ζ : ArithmeticFunction ℝ) := by
    rw [← mul_assoc, mul_comm (dampedTwist ε (↑ζ : ArithmeticFunction ℝ)),
      dampedTwist_moebius_mul_dampedTwist_zeta, one_mul]
  have hval : (∑ j ∈ k.divisors, (j : ℝ) ^ (-ε) * pmPowerDampedDivisorCoeff ε (k / j)) =
      (dampedTwist ε (↑ζ : ArithmeticFunction ℝ) *
        (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * ↑ζ)) k := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => dampedTwist ε (↑ζ : ArithmeticFunction ℝ) a *
        (dampedTwist ε (↑moebius : ArithmeticFunction ℝ) * ↑ζ) b)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj0 : j ≠ 0 := (Nat.pos_of_mem_divisors hj).ne'
    rw [dampedTwist_apply, ← pmPowerDampedDivisorCoeff_eq_mul]
    simp [hj0]
  rw [hval, hprod]
  simp [hk0]

/-- **The inversion law for the raw prefix.**  The damped unit dilation average of the source's
prefixes is exactly the horizon. -/
theorem sum_rpow_mul_rawPrefix_eq (ε : ℝ) (n : ℕ) :
    (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) *
        ∑ m ∈ Icc 1 (n / j), pmPowerDampedDivisorCoeff ε m) = (n : ℝ) := by
  rw [← sum_Icc_divisor_convolution_eq_dilation (fun j => (j : ℝ) ^ (-ε))
    (pmPowerDampedDivisorCoeff ε) n]
  have hterm : ∀ k ∈ Icc 1 n,
      (∑ j ∈ k.divisors, (j : ℝ) ^ (-ε) * pmPowerDampedDivisorCoeff ε (k / j)) = 1 :=
    fun k hk => sum_divisors_rpow_mul_coeff ε (mem_Icc.mp hk).1
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  push_cast
  ring

/-- The damped unit floor sum `Σ_{j ≤ n} j^{-ε} ⌊n/j⌋`. -/
def dampedUnitFloorSum (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) * ((n / j : ℕ) : ℝ)

/-- **The inversion law for the centred source.**  One positive-weight dilation average of the
centred damped Möbius prefix is explicitly computable at every horizon and damping. -/
theorem sum_rpow_mul_centeredPrefix_eq (ε : ℝ) (n : ℕ) :
    (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) * pmPowerDampedCenteredDivisorPrefix ε (n / j)) =
      (n : ℝ) - (pmPowerDampedDivisorDensity ε).re * dampedUnitFloorSum ε n := by
  have hcentre : ∀ j ∈ Icc 1 n,
      (j : ℝ) ^ (-ε) * ∑ m ∈ Icc 1 (n / j), pmPowerDampedDivisorCoeff ε m =
        (j : ℝ) ^ (-ε) * pmPowerDampedCenteredDivisorPrefix ε (n / j) +
          (pmPowerDampedDivisorDensity ε).re * ((j : ℝ) ^ (-ε) * ((n / j : ℕ) : ℝ)) := by
    intro j _
    rw [pmPowerDampedCenteredDivisorPrefix_eq]
    ring
  have h := sum_rpow_mul_rawPrefix_eq ε n
  rw [Finset.sum_congr rfl hcentre, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [dampedUnitFloorSum]
  linarith

/-! ## §3. The source cannot stay below a negative level -/

/-- **No uniformly negative source.**  Because the dilation average of the centred prefix is the
explicit value of the inversion law, and the weights are positive, some level of the dilation range
carries a centred prefix at least that average.  A general row obeys no such constraint. -/
theorem exists_centeredPrefix_ge_of_dilation_law (ε : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m ∈ Icc 1 n, ((n : ℝ) - (pmPowerDampedDivisorDensity ε).re * dampedUnitFloorSum ε n) /
      (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε)) ≤ pmPowerDampedCenteredDivisorPrefix ε m := by
  set W : ℝ := ∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) with hW
  have hWpos : 0 < W := by
    rw [hW]
    refine Finset.sum_pos (fun j hj => ?_) ⟨1, mem_Icc.mpr ⟨le_rfl, hn⟩⟩
    exact Real.rpow_pos_of_pos (by exact_mod_cast (mem_Icc.mp hj).1) _
  by_contra hcon
  push Not at hcon
  have hlt : (∑ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) *
      pmPowerDampedCenteredDivisorPrefix ε (n / j)) <
      ((n : ℝ) - (pmPowerDampedDivisorDensity ε).re * dampedUnitFloorSum ε n) := by
    have hbound : ∀ j ∈ Icc 1 n, (j : ℝ) ^ (-ε) *
        pmPowerDampedCenteredDivisorPrefix ε (n / j) <
        (j : ℝ) ^ (-ε) * (((n : ℝ) - (pmPowerDampedDivisorDensity ε).re *
          dampedUnitFloorSum ε n) / W) := by
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hjn := (mem_Icc.mp hj).2
      have hmem : n / j ∈ Icc 1 n :=
        mem_Icc.mpr ⟨(Nat.one_le_div_iff hj1).mpr hjn, Nat.div_le_self n j⟩
      exact mul_lt_mul_of_pos_left (hcon (n / j) hmem)
        (Real.rpow_pos_of_pos (by exact_mod_cast hj1) _)
    have hsum := Finset.sum_lt_sum_of_nonempty ⟨1, mem_Icc.mpr ⟨le_rfl, hn⟩⟩ hbound
    rw [← Finset.sum_mul, ← hW] at hsum
    rw [mul_div_assoc'] at hsum
    rw [mul_comm] at hsum
    rw [mul_div_assoc] at hsum
    rw [div_self hWpos.ne', mul_one] at hsum
    exact hsum
  rw [sum_rpow_mul_centeredPrefix_eq] at hlt
  exact absurd hlt (lt_irrefl _)

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
