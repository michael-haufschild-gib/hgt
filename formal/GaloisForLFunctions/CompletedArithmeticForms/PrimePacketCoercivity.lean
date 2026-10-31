import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.PrimePacketDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimeDefectConfinementMustRetainLowEnergyConductors

set_option autoImplicit false

/-!
# Logarithmic coercivity on high conductor packets

The harmonic lower frame applied to prime-dilation squares retains the exact
arithmetic energy with a linear logarithmic loss. The bounded row counterterm
then gives numerical prime coercivity, independent of confinement.
-/

noncomputable section
open Finset
open scoped BigOperators RealInnerProductSpace Classical
namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  ArithmeticElectrostatics

/-- Polarized Gram discrepancy for arbitrary coefficient pairs over `Icc 1 Q` (`Q * Q ≤ N`). -/
theorem abs_inner_sum_normalizedRamanujanHorizonVector_sub_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (a b : ℕ → ℝ) :
    |⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N,
        ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N⟫ -
      ∑ m ∈ Icc 1 Q, a m * b m| ≤
      9 * (1 + Real.log Q) / Real.log N *
        Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) * Real.sqrt (∑ m ∈ Icc 1 Q, b m ^ 2) := by
  let A := ∑ m ∈ Icc 1 Q, a m ^ 2
  let B := ∑ m ∈ Icc 1 Q, b m ^ 2
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => sq_nonneg _
  by_cases hAz : A = 0
  · have ha0 : ∀ m ∈ Icc 1 Q, a m = 0 := fun m hm =>
      sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k))).mp hAz m hm)
    have hu0 : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = 0 :=
      sum_eq_zero fun m hm => by rw [ha0 m hm, zero_smul]
    have hs0 : (∑ m ∈ Icc 1 Q, a m * b m) = 0 :=
      sum_eq_zero fun m hm => by rw [ha0 m hm, zero_mul]
    simp [A, hAz, hu0, hs0]
  by_cases hBz : B = 0
  · have hb0 : ∀ m ∈ Icc 1 Q, b m = 0 := fun m hm =>
      sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (b k))).mp hBz m hm)
    have hv0 : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) = 0 :=
      sum_eq_zero fun m hm => by rw [hb0 m hm, zero_smul]
    have hs0 : (∑ m ∈ Icc 1 Q, a m * b m) = 0 :=
      sum_eq_zero fun m hm => by rw [hb0 m hm, mul_zero]
    simp [B, hBz, hv0, hs0]
  have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBz)
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  let a' : ℕ → ℝ := fun m => a m / Real.sqrt A
  let b' : ℕ → ℝ := fun m => b m / Real.sqrt B
  have ha'sq : (∑ m ∈ Icc 1 Q, a' m ^ 2) = 1 := by
    have h1 : (∑ m ∈ Icc 1 Q, a' m ^ 2) = A / A := by
      dsimp only [a', A]; rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [div_pow, Real.sq_sqrt hAp.le]
    rw [h1, div_self hAp.ne']
  have hb'sq : (∑ m ∈ Icc 1 Q, b' m ^ 2) = 1 := by
    have h1 : (∑ m ∈ Icc 1 Q, b' m ^ 2) = B / B := by
      dsimp only [b', B]; rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [div_pow, Real.sq_sqrt hBp.le]
    rw [h1, div_self hBp.ne']
  let S := ∑ m ∈ Icc 1 Q, a' m * b' m
  have hplus_mass : (∑ m ∈ Icc 1 Q, (a' m + b' m) ^ 2) = 2 + 2 * S := by
    have hexp : (∑ m ∈ Icc 1 Q, (a' m + b' m) ^ 2) =
        (∑ m ∈ Icc 1 Q, a' m ^ 2) + (∑ m ∈ Icc 1 Q, b' m ^ 2) + 2 * S := by
      dsimp only [S]
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hexp, ha'sq, hb'sq]; ring
  have hminus_mass : (∑ m ∈ Icc 1 Q, (a' m - b' m) ^ 2) = 2 - 2 * S := by
    have hexp : (∑ m ∈ Icc 1 Q, (a' m - b' m) ^ 2) =
        (∑ m ∈ Icc 1 Q, a' m ^ 2) + (∑ m ∈ Icc 1 Q, b' m ^ 2) - 2 * S := by
      dsimp only [S]
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hexp, ha'sq, hb'sq]; ring
  let u' := ∑ m ∈ Icc 1 Q, a' m • normalizedRamanujanHorizonVector m N
  let v' := ∑ m ∈ Icc 1 Q, b' m • normalizedRamanujanHorizonVector m N
  have hu'pv' : (∑ m ∈ Icc 1 Q, (a' m + b' m) • normalizedRamanujanHorizonVector m N) = u' + v' := by
    simp only [u', v', add_smul, sum_add_distrib]
  have hu'mv' : (∑ m ∈ Icc 1 Q, (a' m - b' m) • normalizedRamanujanHorizonVector m N) = u' - v' := by
    simp only [u', v', sub_smul, sum_sub_distrib]
  have hgp := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hQ hQN (fun m => a' m + b' m)
  have hgm := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hQ hQN (fun m => a' m - b' m)
  rw [hu'pv', hplus_mass] at hgp
  rw [hu'mv', hminus_mass] at hgm
  have hpol : (‖u' + v'‖ ^ 2 - (2 + 2 * S)) - (‖u' - v'‖ ^ 2 - (2 - 2 * S)) =
      4 * (⟪u', v'⟫ - S) := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v' u']
    ring
  have h4 : 4 * |⟪u', v'⟫ - S| ≤ 4 * (9 * (1 + Real.log Q) / Real.log N) := by
    have habs : |4 * (⟪u', v'⟫ - S)| ≤
        |‖u' + v'‖ ^ 2 - (2 + 2 * S)| + |‖u' - v'‖ ^ 2 - (2 - 2 * S)| := by
      rw [← hpol]; exact abs_sub _ _
    rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num] at habs
    linarith only [habs, hgp, hgm]
  have h1 : |⟪u', v'⟫ - S| ≤ 9 * (1 + Real.log Q) / Real.log N := by linarith only [h4]
  have hu_eq : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = Real.sqrt A • u' := by
    dsimp only [u', a']; rw [Finset.smul_sum]
    exact sum_congr rfl fun m _ => by rw [smul_smul, mul_div_cancel₀ _ hsA.ne']
  have hv_eq : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) = Real.sqrt B • v' := by
    dsimp only [v', b']; rw [Finset.smul_sum]
    exact sum_congr rfl fun m _ => by rw [smul_smul, mul_div_cancel₀ _ hsB.ne']
  have hS_eq : (∑ m ∈ Icc 1 Q, a m * b m) = Real.sqrt A * (Real.sqrt B * S) := by
    dsimp only [S, a', b']
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    field_simp [hsA.ne', hsB.ne']
  rw [hu_eq, hv_eq, real_inner_smul_left, real_inner_smul_right, hS_eq,
    show Real.sqrt A * (Real.sqrt B * ⟪u', v'⟫) - Real.sqrt A * (Real.sqrt B * S) =
      Real.sqrt A * (Real.sqrt B * (⟪u', v'⟫ - S)) by ring,
    abs_mul, abs_mul, abs_of_pos hsA, abs_of_pos hsB]
  calc
    Real.sqrt A * (Real.sqrt B * |⟪u', v'⟫ - S|) ≤
        Real.sqrt A * (Real.sqrt B * (9 * (1 + Real.log Q) / Real.log N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hsB.le) hsA.le
    _ = 9 * (1 + Real.log Q) / Real.log N * Real.sqrt A * Real.sqrt B := by ring

/-- Direct prime-dilation squares give a numerical logarithmic slope above `Q`.
Only the logarithmic lower frame and the bounded row counterterm are lost. -/
theorem primePacket_energy_ge_log {Q R N : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hRR : R * R ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    (a : ℕ → ℝ) (ha : ∀ m ∈ Icc 1 Q, a m = 0) :
    (Real.log Q / 2 - (Real.log 4 + 4)) *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      renormalizedPrimeEnergy N
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  have hR : 2 ≤ R := hQ.trans hQR
  have hN : 2 ≤ N := by
    have hh := Nat.mul_le_mul hR hR
    omega
  let y := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let S := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := ∑ m ∈ Icc 1 R,
    (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * a m ^ 2
  have hE : 0 ≤ E := sum_nonneg fun m _ =>
    mul_nonneg (add_nonneg (Real.log_natCast_nonneg m)
      (RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m)) (sq_nonneg _)
  have hdiag : Real.log Q * S ≤ E := by
    dsimp only [S, E]
    rw [mul_sum]
    apply sum_le_sum
    intro m hm
    by_cases hmQ : m ≤ Q
    · rw [ha m (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hmQ⟩)]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    · have hlQm : Real.log (Q : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log
        (by exact_mod_cast (show 0 < Q by omega))
        (by exact_mod_cast (not_le.mp hmQ).le)
      exact mul_le_mul_of_nonneg_right
        (hlQm.trans (le_add_of_nonneg_right
          (RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m))) (sq_nonneg _)
  have hlogR : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hL : 0 < Real.log N := by linarith only [hlog, hlogR]
  have htheta : (3 / 4 : ℝ) ≤ (Real.log N - 3 * Real.log R - 1) / Real.log N := by
    rw [le_div_iff₀ hL]
    linarith only [hlog, hlogR]
  have hdef := poleDefect_normalizedRamanujanPacket_ge_logarithmic hR hN a
  have hdef' : (3 / 4 : ℝ) * E ≤ poleDefect N (primeHorizonExtension y) :=
    (mul_le_mul_of_nonneg_right htheta hE).trans hdef
  have hriesz := (half_and_three_halves_riesz_of_log_le hR hRR hlog a).2
  have hnorm := mul_le_mul_of_nonneg_left hriesz
    (div_nonneg (Real.log_natCast_nonneg Q) zero_le_two)
  have hdiag' := mul_le_mul_of_nonneg_left hdiag (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hrow := poleDefect_le_primeEnergy_add_row_cost y
  nlinarith only [hdef', hnorm, hdiag', hrow]

/-- A uniform numerical constant suffices for prime coercivity on conductor bands. -/
theorem exists_primePacket_energy_ge_log :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q R N : ℕ},
      2 ≤ Q → Q ≤ R → R * R ≤ N →
      18 * (1 + Real.log R) ≤ Real.log N →
      ∀ a : ℕ → ℝ, (∀ m ∈ Icc 1 Q, a m = 0) →
        (Real.log Q / 2 - C) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          renormalizedPrimeEnergy N
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  refine ⟨Real.log 4 + 4, ?_, ?_⟩
  · have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith only [hlog4]
  · intro Q R N hQ hQR hRR hlog a ha
    exact primePacket_energy_ge_log hQ hQR hRR hlog a ha

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.primePacket_energy_ge_log
#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_primePacket_energy_ge_log

