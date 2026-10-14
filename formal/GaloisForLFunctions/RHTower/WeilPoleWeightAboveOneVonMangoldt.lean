import GaloisForLFunctions.RHTower.WeilPoleWeightBelowOneEmpty

/-!
# Above the residue `Λ` is not Weil-positive: an odd-type null test

The Weil functional with pole weight `β` (`weilPoleWeightFunctional β lam`) replaces the pole term
`k̂(i/2) + k̂(−i/2)` of `ζ` by `β` times it.  Below the residue (`β < 1`) the cone is empty
(`not_forall_re_weilPoleWeightFunctional_nonneg`): the twisted-arc null tests have the positive
pole term `w₀/2`.

**Theorem** (`not_forall_re_weilPoleWeightFunctional_vonMangoldt_nonneg_of_one_lt`).  For `β > 1`
the functional with weights `Λ` is negative on the autocorrelation of some real `C²` compactly
supported test.  Unconditional.  Together with the case `β < 1`, `Λ` is Weil-positive at pole weight
`β` only if `β = 1`.

Proof.  Take the strip test `F` with transform `Ξ(z)·(Q₁(z) − ¼) = Ξ(z)·(iz/2)` (`oddNullSymbol`):
the difference of the shifted-Gamma tests `F₁ − ¼F₀`, an odd-type multiple of `Ξ`.
* `F̂` vanishes at every zero of `ζ`, so the zeta sides of its truncations tend to `0`
  (`tendsto_tsum_W_truncTest`), and the prime deviation of `Λ` from itself is `0`.
* `F̂(i/2) = Ξ(i/2)(Q₁(i/2) − ¼) = −⅛` and `F̂(−i/2) = Ξ(−i/2)(Q₁(−i/2) − ¼) = ⅛`, so the pole term
  is `2·(−⅛)·⅛ = −1/32 < 0`.
* So the functionals of the truncations tend to `(β − 1)·(−1/32) < 0`.

The sign of the pole term of a `Ξ`-divisible test is the parity of its multiplier: even multipliers
(`Q_j`, the twisted-arc family) give `pole ≥ 0`, odd ones (`z·H`) give `pole ≤ 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.WeilPoleWeight

open WeilSpectral

/-- The odd-type null multiplier `Ξ(z)(Q₁(z) − ¼) = Ξ(z)·(iz/2)`. -/
def oddNullSymbol (z : ℂ) : ℂ := xiShiftedGamma 1 z - (1 / 4 : ℂ) * xiShiftedGamma 0 z

/-- The odd-type null test, the strip test of `oddNullSymbol`. -/
def oddNullTest : ℝ → ℝ := stripTest oddNullSymbol

theorem exists_stripDecay_oddNullSymbol :
    ∃ C : ℝ, StripDecay oddNullSymbol (3 / 4) xiShiftedGammaRate C := by
  obtain ⟨C, hC, hj⟩ := exists_stripDecay_xiShiftedGamma
  set C₁ := C * ((1 ! : ℝ) * (3 / 2 : ℝ) ^ 1) with hC₁
  set C₀ := C * ((0 ! : ℝ) * (3 / 2 : ℝ) ^ 0) with hC₀
  refine ⟨C₁ + C₀ / 4, fun z hz => ?_, fun z hz => ?_⟩
  · exact ((hj 1).diff z hz).sub ((differentiableAt_const _).mul ((hj 0).diff z hz))
  · have h1 := (hj 1).bound z hz
    have h0 := (hj 0).bound z hz
    unfold oddNullSymbol
    calc ‖xiShiftedGamma 1 z - (1 / 4 : ℂ) * xiShiftedGamma 0 z‖
        ≤ ‖xiShiftedGamma 1 z‖ + ‖(1 / 4 : ℂ)‖ * ‖xiShiftedGamma 0 z‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ C₁ * Real.exp (-(xiShiftedGammaRate * |z.re|)) +
          1 / 4 * (C₀ * Real.exp (-(xiShiftedGammaRate * |z.re|))) := by
          have : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
          rw [this]
          exact add_le_add h1 (mul_le_mul_of_nonneg_left h0 (by norm_num))
      _ = (C₁ + C₀ / 4) * Real.exp (-(xiShiftedGammaRate * |z.re|)) := by ring

theorem oddNullSymbol_neg_ofReal (r : ℝ) : oddNullSymbol (-(r : ℂ)) = conj (oddNullSymbol r) := by
  unfold oddNullSymbol
  rw [xiShiftedGamma_neg_ofReal 1, xiShiftedGamma_neg_ofReal 0, map_sub, map_mul]
  congr 2
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]

theorem exists_decayBound_oddNullTest : ∃ C : ℝ, DecayBound oddNullTest (1 / 4) C := by
  obtain ⟨C, hC⟩ := exists_stripDecay_oddNullSymbol
  have h := decayBound_stripTest (by norm_num : (1 / 2 : ℝ) < 3 / 4) xiShiftedGammaRate_pos hC
  rw [show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num] at h
  exact ⟨_, h⟩

theorem paperFT_oddNullTest {z : ℂ} (hz : |z.im| < 3 / 4) :
    paperFT (fun u => (oddNullTest u : ℂ)) z = oddNullSymbol z := by
  obtain ⟨C, hC⟩ := exists_stripDecay_oddNullSymbol
  exact paperFT_stripTest (by norm_num) xiShiftedGammaRate_pos hC oddNullSymbol_neg_ofReal hz

/-- The odd-type null test vanishes at every zero of `ζ`. -/
theorem paperFT_oddNullTest_gammaOf (ρ : zetaZeroConfig.carrier) :
    paperFT (fun u => (oddNullTest u : ℂ)) (gammaOf ρ) = 0 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(gammaOf (ρ : ℂ)).im| < 1 / 2 := WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have h34 : |(gammaOf (ρ : ℂ)).im| < 3 / 4 := by linarith
  rw [paperFT_oddNullTest h34]
  unfold oddNullSymbol
  rw [← paperFT_xiShiftedGammaTest 1 h34, ← paperFT_xiShiftedGammaTest 0 h34,
    paperFT_xiShiftedGammaTest_gammaOf 1 ρ, paperFT_xiShiftedGammaTest_gammaOf 0 ρ]
  ring

theorem integral_oddNullTest_mul_exp_neg_half :
    ∫ u, oddNullTest u * Real.exp (-u / 2) = -1 / 8 := by
  have h := paperFT_ofRealFun_I_div_two oddNullTest
  rw [paperFT_oddNullTest (by simp; norm_num)] at h
  unfold oddNullSymbol xiShiftedGamma at h
  rw [shiftedGammaPoly_I_div_two le_rfl] at h
  simp only [shiftedGammaPoly, Finset.range_zero, Finset.prod_empty, mul_one, mul_zero,
    zero_sub, RHTower.XiC] at h
  rw [show (1 / 2 : ℂ) + I / 2 * I = 0 by rw [mul_comm, ← mul_div_assoc, Complex.I_mul_I]; ring,
    xi_zero_eq_half] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re] at this
  rw [← this]
  norm_num

theorem integral_oddNullTest_mul_exp_half :
    ∫ u, oddNullTest u * Real.exp (u / 2) = 1 / 8 := by
  have h := paperFT_ofRealFun_neg_I_div_two oddNullTest
  rw [paperFT_oddNullTest (by simp; norm_num)] at h
  unfold oddNullSymbol xiShiftedGamma at h
  simp only [shiftedGammaPoly, Finset.range_one, Finset.prod_singleton, Finset.range_zero,
    Finset.prod_empty, mul_one, RHTower.XiC, Nat.cast_zero, zero_add] at h
  rw [show (1 / 2 : ℂ) + -I / 2 * I = 1 by
    rw [mul_comm, ← mul_div_assoc, mul_neg, Complex.I_mul_I]; ring, xi_one] at h
  rw [show (1 / 4 : ℂ) + I * (-I / 2) / 2 = 1 / 2 by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]; ring] at h
  have := congrArg Complex.re h
  simp only [Complex.ofReal_re] at this
  rw [← this]
  norm_num

/-- The pole term of the odd-type null test is `−1/32`. -/
theorem pole_oddNullTest :
    2 * ((∫ u, oddNullTest u * Real.exp (-u / 2)) * ∫ u, oddNullTest u * Real.exp (u / 2)) =
      -1 / 32 := by
  rw [integral_oddNullTest_mul_exp_neg_half, integral_oddNullTest_mul_exp_half]
  norm_num

theorem atomPairing_zero (g : ℝ → ℝ) : atomPairing (fun _ => 0) g = 0 := by
  simp [atomPairing]

/-- **Above the residue `Λ` is not Weil-positive.**  For `β > 1` the Weil functional with pole
weight `β` and weights `Λ` is negative on some real autocorrelation. -/
theorem not_forall_re_weilPoleWeightFunctional_vonMangoldt_nonneg_of_one_lt {β : ℝ} (hβ : 1 < β) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilPoleWeightFunctional β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re := by
  intro hpos
  obtain ⟨C, hF⟩ := exists_decayBound_oddNullTest
  set F := oddNullTest with hFdef
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  -- the zeta side of the truncations tends to `0` (one-member family)
  set w : ℕ → ℝ := fun j => if j = 0 then 1 else 0 with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => by simp only [hw]; split_ifs <;> norm_num
  have hsum : Summable fun j => w j * C ^ 2 :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hw, hj]
  have h1 := tendsto_tsum_W_truncTest (F := fun _ => F) (C := fun _ => C) hδ (fun _ => hF) hw0
    hsum hΛ0 hΛ (fun _ ρ => paperFT_oddNullTest_gammaOf ρ)
  have hsingle : ∀ L : ℝ, (∑' j, w j * (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ))
      (fun u => (truncTest F L u : ℂ))).re) =
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re := by
    intro L
    rw [tsum_eq_single 0 fun j hj => by simp [hw, hj]]
    simp [hw]
  simp_rw [hsingle] at h1
  -- the pole term
  have hneg : ∀ u : ℝ, -u / 2 = (-1 / 2 : ℝ) * u := fun u => by ring
  have hpos2 : ∀ u : ℝ, u / 2 = (1 / 2 : ℝ) * u := fun u => by ring
  have ta := tendsto_integral_truncTest_mul_exp hδ hF (c := -1 / 2) (by norm_num [abs_of_neg])
  have tb := tendsto_integral_truncTest_mul_exp hδ hF (c := 1 / 2) (by norm_num)
  simp_rw [← hneg] at ta
  simp_rw [← hpos2] at tb
  have h3 := ((ta.mul tb).const_mul 2).const_mul (β - 1)
  rw [pole_oddNullTest] at h3
  -- the functional on the truncations
  set S : ℝ → ℝ := fun L => (weilPoleWeightFunctional β
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))).re with hS
  have hSnn : ∀ L, 0 ≤ S L := fun L =>
    hpos _ (contDiff_ofReal_truncTest hF.1 L) (hasCompactSupport_truncTest F L)
  have hsplit : ∀ L, S L =
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) (fun u => (truncTest F L u : ℂ))).re +
        (β - 1) * (2 * ((∫ u, truncTest F L u * Real.exp (-u / 2)) *
          ∫ u, truncTest F L u * Real.exp (u / 2))) := by
    intro L
    show (weilPoleWeightFunctional β (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))).re = _
    rw [re_weilPoleWeightFunctional_ofReal β _ (contDiff_ofReal_truncTest hF.1 L)
      (contDiff_truncTest hF.1 L).continuous (hasCompactSupport_truncTest F L)]
    simp only [sub_self, atomPairing_zero, sub_zero]
  have hlim : Tendsto S atTop (𝓝 (0 + (β - 1) * (-1 / 32))) :=
    (h1.add h3).congr fun L => (hsplit L).symm
  have hge := ge_of_tendsto hlim (Eventually.of_forall hSnn)
  nlinarith

end RHTower.WeilPoleWeight
