import GaloisForLFunctions.TransHorizonIncidenceMechanics.SecondVonMangoldtMomentSeparatesTheBlindPair
import GaloisForLFunctions.HTGeometry.ArithmeticPowerDilation

/-!
# The Möbius and Liouville receivers are equivalent

`λ = 1_□ ⋆ μ`, and the square dilation of `μ` inverts the square indicator
(`μ(√·)1_□ ⋆ 1_□ = δ₁`, the square-dilated Möbius inversion), so `μ = μ(√·)1_□ ⋆ λ`. Both kernels
`1_□(q) q^{-ε}` and `μ(√q)1_□(q) q^{-ε}` lie in the critical Wiener algebra (`Σ_j j^{-1-2ε} < ∞`), and
critical Wiener convolutions preserve bounded receivers. Hence, **at every damping `ε > 0`, the
receiver of `μ(d)d^{-ε}` is bounded if and only if the receiver of `λ(d)d^{-ε}` is**, and the
Möbius and Liouville parity pairs exist at exactly the same dampings. With the cofinal discrete
budget criterion this gives an RH criterion read on the Liouville weight alone: bounded Liouville
receivers at arbitrarily small damping imply RH.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The square-dilated Möbius function `μ(√q) 1_□(q)`. -/
def squareMoebius (q : ℕ) : ℝ := RHTower.mPart 2 (ArithmeticFunction.moebius : ArithmeticFunction ℝ) q

theorem squareMoebius_sq (j : ℕ) :
    squareMoebius (j ^ 2) = ((ArithmeticFunction.moebius j : ℤ) : ℝ) := by
  rw [squareMoebius, RHTower.mPart_apply_pow two_ne_zero]
  simp

theorem squareMoebius_of_not_square {q : ℕ} (hq : ∀ j : ℕ, j ^ 2 ≠ q) : squareMoebius q = 0 :=
  RHTower.mPart_apply_of_forall_pow_ne _ _ hq

/-- The square dilation of `ζ` is the square indicator off zero. -/
theorem mPart_two_zeta_apply {q : ℕ} (hq : q ≠ 0) :
    RHTower.mPart 2 ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) q =
      RHTower.squareIndicatorR q := by
  by_cases hsq : ∃ j : ℕ, j ^ 2 = q
  · obtain ⟨j, rfl⟩ := hsq
    have hj : j ≠ 0 := by rintro rfl; exact hq (by simp)
    rw [RHTower.mPart_apply_pow two_ne_zero, RHTower.squareIndicatorR, if_pos ⟨j, sq j⟩]
    simp [hj]
  · rw [RHTower.mPart_apply_of_forall_pow_ne _ _ (fun j hj => hsq ⟨j, hj⟩), RHTower.squareIndicatorR,
      if_neg]
    rintro ⟨r, rfl⟩
    exact hsq ⟨r, sq r⟩

/-- `μ = μ(√·)1_□ ⋆ λ` pointwise. -/
theorem moebiusR_eq_dirichletConv_squareMoebius (n : ℕ) :
    RHTower.moebiusR n = RHTower.dirichletConv squareMoebius RHTower.liouvilleR n := by
  set Hμ := RHTower.mPart 2 (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  set S := RHTower.mPart 2 ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
  have hcancel := RHTower.powerDilation_moebius_zeta_cancel (R := ℝ) 1
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  -- `λ = S ⋆ μ` pointwise on ℕ
  have hlam : ∀ m : ℕ, (S * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) m =
      RHTower.liouvilleR m := fun m => by
    rcases eq_or_ne m 0 with rfl | hm
    · simp [RHTower.liouvilleR]
    rw [RHTower.liouvilleR_eq_dirichletConv, RHTower.dirichletConv, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => S a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    rw [mPart_two_zeta_apply hd0]
    simp [RHTower.moebiusR]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [RHTower.moebiusR, RHTower.dirichletConv]
  have h : (Hμ * (S * (ArithmeticFunction.moebius : ArithmeticFunction ℝ))) n =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) n := congrArg (fun f => f n) hcancel
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun a b => Hμ a * (S * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) b)] at h
  rw [RHTower.moebiusR, show ((ArithmeticFunction.moebius n : ℤ) : ℝ) =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) n by simp, ← h, RHTower.dirichletConv]
  exact sum_congr rfl fun d _ => by rw [hlam]; rfl

theorem dampedMoebius_eq_dirichletConv (ε : ℝ) (n : ℕ) :
    pmPowerDampedRealWeight ε n =
      RHTower.dirichletConv (dampedSignWeight squareMoebius ε)
        (dampedSignWeight RHTower.liouvilleR ε) n := by
  rw [pmPowerDampedRealWeight, show moebiusReal n = RHTower.moebiusR n from rfl,
    moebiusR_eq_dirichletConv_squareMoebius, RHTower.dirichletConv, RHTower.dirichletConv, sum_mul]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hq
  have hq0 : 0 < q := Nat.pos_of_mem_divisors hq
  rw [Nat.mul_div_cancel_left k hq0]
  simp only [dampedSignWeight, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem criticalWiener_dampedSquareMoebius {ε : ℝ} (hε : 0 < ε) :
    CriticalWiener (dampedSignWeight squareMoebius ε) := by
  refine (criticalWiener_dampedSquare hε).of_nonneg_of_le
    (fun q => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _))
    fun q => mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  unfold dampedSignWeight
  rw [abs_mul, abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  by_cases hsq : ∃ j : ℕ, j ^ 2 = q
  · obtain ⟨j, rfl⟩ := hsq
    rw [squareMoebius_sq, RHTower.squareIndicatorR, if_pos ⟨j, sq j⟩, abs_one]
    rcases ArithmeticFunction.moebius_eq_or j with h | h | h <;> simp [h]
  · rw [squareMoebius_of_not_square (fun j hj => hsq ⟨j, hj⟩), abs_zero]
    exact abs_nonneg _

theorem summable_abs_dampedLiouville_div {ε : ℝ} (hε : 0 < ε) :
    Summable (fun d : ℕ => |dampedSignWeight RHTower.liouvilleR ε d / d|) := by
  refine (Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun d => ?_
  rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have : |RHTower.liouvilleR d| ≤ 1 := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp [RHTower.liouvilleR]
    · rw [abs_liouvilleR hd]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _) this

/-- **The Möbius receiver is paid by the Liouville receiver** at every damping. -/
theorem receiverBounded_moebius_of_liouville {ε : ℝ} (hε : 0 < ε)
    (h : ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε)) :
    ReceiverBounded (pmPowerDampedRealWeight ε) := by
  rw [show pmPowerDampedRealWeight ε = RHTower.dirichletConv (dampedSignWeight squareMoebius ε)
      (dampedSignWeight RHTower.liouvilleR ε) from funext (dampedMoebius_eq_dirichletConv ε)]
  exact receiverBounded_dirichletConv (criticalWiener_dampedSquareMoebius hε)
    (summable_abs_dampedLiouville_div hε) h

/-- **The Möbius and Liouville receivers are equivalent** at every damping `ε > 0`. -/
theorem receiverBounded_moebius_iff_liouville {ε : ℝ} (hε : 0 < ε) :
    ReceiverBounded (pmPowerDampedRealWeight ε) ↔
      ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) :=
  ⟨receiverBounded_liouville_of_moebius hε, receiverBounded_moebius_of_liouville hε⟩

/-- **A Liouville receiver criterion for RH.** Bounded Liouville receivers at arbitrarily small
damping imply the Riemann Hypothesis. -/
theorem riemannHypothesis_of_liouville_cofinal_receiver
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε)) :
    RiemannHypothesis := by
  refine RHTower.riemannHypothesis_of_pmPowerDamped_cofinal_discrete_budget fun δ hδ => ?_
  obtain ⟨ε, hε, hεδ, hL⟩ := h δ hδ
  obtain ⟨B, hB⟩ := receiverBounded_moebius_of_liouville hε hL
  refine ⟨ε, hε, hεδ, B, fun T => ?_⟩
  rw [← weightPronicEnergy_pmPowerDamped]
  have := hB T
  rwa [(hasSum_pmPowerDampedRealWeight_div hε).tsum_eq] at this

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
