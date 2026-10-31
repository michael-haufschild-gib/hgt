import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergySeparatesValuations

/-!
# Logarithmic coercivity on high conductor packets

The arithmetic adjunction energy grows at least logarithmically. Uniform prime
residuals and polarized Gram bounds transfer this growth to finite-horizon
packets, with a numerical logarithmic coefficient independent of confinement.
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

/-- Above conductor `Q`, prime energy has a numerical logarithmic slope.
The residual constant affects only the additive loss. -/
theorem exists_primePacket_energy_ge_log :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q R N : ℕ},
      2 ≤ Q → Q ≤ R → R ^ 6 ≤ N →
      18 * (1 + Real.log R) ≤ Real.log N →
      (1 + Real.log R) ^ 2 / Real.sqrt (Real.log N) ≤ 1 →
      ∀ a : ℕ → ℝ, (∀ m ∈ Icc 1 Q, a m = 0) →
        (Real.log Q / 2 - C) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          renormalizedPrimeEnergy N
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨C_res, hC_res, hres⟩ := exists_fullPrimeMatrix_packet_residual_norm_le
  let g := |Real.eulerMascheroniConstant|
  have hg : 0 ≤ g := abs_nonneg _
  refine ⟨37 * g + 36 + 2 * C_res, by positivity, ?_⟩
  intro Q R N hQ hQR hR6 hlog hsmall a ha
  have hR : 2 ≤ R := hQ.trans hQR
  have hRR : R * R ≤ N := by
    have hp : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [pow_two] using hp.trans hR6
  have hlogR : 0 ≤ Real.log R := Real.log_natCast_nonneg _
  have hL1 : 1 ≤ Real.log N := by linarith only [hlog, hlogR]
  have hL : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsqrtL : Real.sqrt (Real.log N) ≤ Real.log N := by
    have hs : 1 ≤ Real.sqrt (Real.log N) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
    nlinarith only [hs, Real.sq_sqrt hL.le]
  have hsmall' : (1 + Real.log R) ^ 2 / Real.log N ≤ 1 :=
    (div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.mpr hL) hsqrtL).trans hsmall
  let y := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let S := ∑ m ∈ Icc 1 R, a m ^ 2
  let M := 2 * (g + 1) * (1 + Real.log R)
  let d := ∑ m ∈ Icc 1 R,
    (a m * (ramanujanAdjunctionEnergy m + g)) • normalizedRamanujanHorizonVector m N
  let d₀ := ∑ m ∈ Icc 1 R,
    (a m * (Real.log N - ramanujanAdjunctionEnergy m)) • normalizedRamanujanHorizonVector m N
  let r := Matrix.toEuclideanLin (fullPrimeMatrix N) y - d₀
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hriesz := half_and_three_halves_riesz_of_log_le hR hRR hlog a
  have hSupper : S ≤ 2 * ‖y‖ ^ 2 := by linarith only [hriesz.1]
  have hSlower : ‖y‖ ^ 2 / 2 ≤ S := by linarith only [hriesz.2, hS]
  have hE (m : ℕ) (hm : m ∈ Icc 1 R) :
      0 ≤ ramanujanAdjunctionEnergy m + g ∧ ramanujanAdjunctionEnergy m + g ≤ M := by
    obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
    have htm := CompletedArithmeticForms.tameDifferent_le_log hm1
    have htm0 := RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m
    have hlm := Real.log_natCast_nonneg m
    have hlmR := Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmR)
    have hg₋ := neg_abs_le Real.eulerMascheroniConstant
    have hg₊ := le_abs_self Real.eulerMascheroniConstant
    dsimp only [ramanujanAdjunctionEnergy, M, g]
    constructor
    · linarith only [htm0, hlm, hg₋]
    · nlinarith only [htm, hlmR, hg₊, hg, hlogR, mul_nonneg hg hlogR]
  have hdiagLower : Real.log Q * S ≤
      ∑ m ∈ Icc 1 R, (a m * (ramanujanAdjunctionEnergy m + g)) * a m := by
    dsimp only [S]
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    by_cases hmQ : m ≤ Q
    · rw [ha m (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hmQ⟩)]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, le_refl]
    · have hlQm := Real.log_le_log
        (by exact_mod_cast (show 0 < Q by omega))
        (by exact_mod_cast (not_le.mp hmQ).le)
      have htm := RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m
      have hg₋ := neg_abs_le Real.eulerMascheroniConstant
      have he : Real.log Q ≤ ramanujanAdjunctionEnergy m + g := by
        dsimp only [ramanujanAdjunctionEnergy, g]
        linarith only [hlQm, htm, hg₋]
      have hh := mul_le_mul_of_nonneg_right he (sq_nonneg (a m))
      nlinarith only [hh]
  have hweighted : (∑ m ∈ Icc 1 R, (a m * (ramanujanAdjunctionEnergy m + g)) ^ 2) ≤
      M ^ 2 * S := by
    dsimp only [S]
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have he := pow_le_pow_left₀ (hE m hm).1 (hE m hm).2 2
    have hh := mul_le_mul_of_nonneg_left he (sq_nonneg (a m))
    nlinarith only [hh]
  have hsqrtWeighted :
      Real.sqrt (∑ m ∈ Icc 1 R, (a m * (ramanujanAdjunctionEnergy m + g)) ^ 2) ≤
        M * Real.sqrt S := by
    calc
      _ ≤ Real.sqrt (M ^ 2 * S) := Real.sqrt_le_sqrt hweighted
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
  let ε := 9 * (1 + Real.log R) / Real.log N
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hεM : ε * M ≤ 18 * (g + 1) := by
    have hh := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ 18 * (g + 1) by positivity)
    dsimp only [ε, M]
    nlinarith only [hh]
  have hgram := abs_inner_sum_normalizedRamanujanHorizonVector_sub_le hR hRR
    (fun m => a m * (ramanujanAdjunctionEnergy m + g)) a
  have herr : |⟪d, y⟫ - ∑ m ∈ Icc 1 R,
      (a m * (ramanujanAdjunctionEnergy m + g)) * a m| ≤
      36 * (g + 1) * ‖y‖ ^ 2 := by
    calc
      _ ≤ ε * Real.sqrt (∑ m ∈ Icc 1 R,
            (a m * (ramanujanAdjunctionEnergy m + g)) ^ 2) * Real.sqrt S := hgram
      _ ≤ ε * (M * Real.sqrt S) * Real.sqrt S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrtWeighted hε)
          (Real.sqrt_nonneg S)
      _ = (ε * M) * S := by
        rw [mul_assoc, mul_assoc, Real.mul_self_sqrt hS]
        ring
      _ ≤ (18 * (g + 1)) * (2 * ‖y‖ ^ 2) :=
        mul_le_mul hεM hSupper hS (by positivity)
      _ = _ := by ring
  have hr : ‖r‖ ≤ 2 * C_res * ‖y‖ := by
    have hh := hres hR hR6 hlog a
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by nlinarith only [hsmall, hC_res]) (norm_nonneg y))
  have hresInner : |⟪r, y⟫| ≤ 2 * C_res * ‖y‖ ^ 2 := by
    calc
      _ ≤ ‖r‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * C_res * ‖y‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right hr (norm_nonneg y)
      _ = _ := by ring
  have hd : d = (Real.log N + g) • y - d₀ := by
    dsimp only [d, d₀, y]
    rw [Finset.smul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [smul_smul, ← sub_smul]
    congr 1
    ring
  have henergy : renormalizedPrimeEnergy N y =
      ⟪d, y⟫ - g * ‖y‖ ^ 2 - ⟪r, y⟫ := by
    rw [hd]
    dsimp only [r, renormalizedPrimeEnergy]
    rw [inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hlead := mul_le_mul_of_nonneg_left hSlower (Real.log_natCast_nonneg Q)
  rw [henergy]
  nlinarith only [hlead, hdiagLower, (abs_le.mp herr).1, (abs_le.mp hresInner).2]

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.exists_primePacket_energy_ge_log

