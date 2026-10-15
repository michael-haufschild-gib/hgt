import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import GaloisForLFunctions.RHTower.EvenSectorStripPositivity
import GaloisForLFunctions.RHTower.WeilPoleWeightBelowOneEmpty

/-!
# The even window of pole weights lies in `[1, ∞)`

`PrimeBlindPositiveEvenAt β` is prime-blind positivity at pole weight `β` on nonnegative
combinations of autocorrelations of even tests.  Since the pole term of an even autocorrelation is
`2(∫ F cosh(u/2))² ≥ 0`, the set of admissible `β` is an up-set (`primeBlindPositiveEvenAt_mono`).

**Theorem** (`one_le_of_primeBlindPositiveEvenAt`).  If prime-blind positivity holds on the even
cone at pole weight `β`, then `β ≥ 1`.  No hypothesis on `ζ` is used.

Proof.  Even Farkas gives weights `lam` that are Weil-positive at pole weight `β` on every even
test.  If `β < 1`, monotonicity in the pole weight makes `lam` Weil-positive at pole weight `1`, so
the even cone uniqueness gives the Riemann hypothesis and `lam = Λ` on `n ≥ 2`.  Now evaluate on
the even truncations of the test `F₀` with `F̂₀ = Ξ`: the prime pairing of `lam − Λ` vanishes, the
zeta side tends to `0` because `Ξ` vanishes at every zero, and the pole term tends to
`2 ξ(0) ξ(1) = ½`.  The limit is `(β − 1)/2 < 0`, against positivity.

Consequences:
* `not_primeBlindPositiveEvenAt_of_lt_one`: the Gamma factor of `ζ` with a reduced pole (in
  particular with no pole, `β = 0`) is never prime-blind positive on the even cone.
* `riemannHypothesis_iff_forall_primeBlindPositiveEvenAt_iff`: RH holds iff the even window is
  exactly `[1, ∞)`.  Without RH the window is empty or a half-line strictly to the right of `1`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral WeilPoleWeight

/-- The test `F₀` with `F̂₀ = Ξ` is even. -/
theorem xiShiftedGammaTest_zero_neg (x : ℝ) :
    xiShiftedGammaTest 0 (-x) = xiShiftedGammaTest 0 x := by
  unfold xiShiftedGammaTest
  refine stripTest_neg (fun z => ?_) x
  simp only [xiShiftedGamma, shiftedGammaPoly, Finset.range_zero, Finset.prod_empty, mul_one,
    RHTower.XiC_even]

/-- The prime pairing of a weight that vanishes on `n ≥ 2` is zero. -/
theorem atomPairing_eq_zero_of_eq_zero {w : ℕ → ℝ} (hw : ∀ n, 2 ≤ n → w n = 0) (g : ℝ → ℝ) :
    atomPairing w g = 0 := by
  unfold atomPairing
  refine (tsum_congr fun n => ?_).trans tsum_zero
  split_ifs with hn
  · rw [hw n hn, zero_div, zero_mul]
  · rw [zero_mul]

/-- The zeta side of the truncations of `F₀` tends to `0`. -/
theorem tendsto_re_W_truncTest_xiShiftedGammaTest_zero :
    Tendsto (fun L : ℝ => (zetaZeroConfig.W (fun u => (truncTest (xiShiftedGammaTest 0) L u : ℂ))
      (fun u => (truncTest (xiShiftedGammaTest 0) L u : ℂ))).re) atTop (𝓝 0) := by
  obtain ⟨C, hC, hF⟩ := exists_decayBound_xiShiftedGammaTest
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set w : ℕ → ℝ := fun j => if j = 0 then 1 else 0 with hw
  have hsum : Summable fun j => w j * (C * ((0 ! : ℝ) * (3 / 2 : ℝ) ^ 0)) ^ 2 :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      rw [Finset.mem_singleton] at hj
      simp only [hw, if_neg hj, zero_mul]
  have h := tendsto_tsum_W_truncTest (F := fun _ => xiShiftedGammaTest 0)
    (C := fun _ => C * ((0 ! : ℝ) * (3 / 2 : ℝ) ^ 0)) (by norm_num : (0 : ℝ) < 1 / 4)
    (fun _ => hF 0) (fun j => by simp only [hw]; split_ifs <;> norm_num) hsum hΛ0 hΛ
    (fun _ ρ => paperFT_xiShiftedGammaTest_gammaOf 0 ρ)
  refine h.congr fun L => ?_
  rw [tsum_eq_single 0 fun j hj => by simp only [hw, if_neg hj, zero_mul]]
  simp only [hw, if_pos, one_mul]

/-- **The even window lies in `[1, ∞)`.** -/
theorem one_le_of_primeBlindPositiveEvenAt {β : ℝ} (h : PrimeBlindPositiveEvenAt β) : 1 ≤ β := by
  by_contra hβ
  rw [not_le] at hβ
  obtain ⟨lam, hlam⟩ := (exists_weilPositiveEvenAt_iff β).mpr h
  obtain ⟨-, hΛlam⟩ := weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_mono hβ.le hlam)
  obtain ⟨C, -, hF⟩ := exists_decayBound_xiShiftedGammaTest
  set F : ℝ → ℝ := xiShiftedGammaTest 0 with hFdef
  have hF0 := hF 0
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  set a : ℝ → ℝ := fun L => ∫ u, truncTest F L u * Real.exp (-u / 2) with ha
  set b : ℝ → ℝ := fun L => ∫ u, truncTest F L u * Real.exp (u / 2) with hb
  have hpos : ∀ L, 0 ≤ (weilPoleWeightFunctional β lam
      (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))).re :=
    fun L => hlam _ (contDiff_ofReal_truncTest hF0.1 L)
      ((hasCompactSupport_truncTest F L).comp_left Complex.ofReal_zero)
      (fun x => congrArg Complex.ofReal (truncTest_neg (F := F) xiShiftedGammaTest_zero_neg L x))
  have hsplit : ∀ L, (weilPoleWeightFunctional β lam
      (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))).re =
      (zetaZeroConfig.W (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ)).re +
        (β - 1) * (2 * (a L * b L)) := fun L => by
    rw [re_weilPoleWeightFunctional_ofReal β lam (contDiff_ofReal_truncTest hF0.1 L)
      (contDiff_truncTest hF0.1 L).continuous (hasCompactSupport_truncTest F L),
      atomPairing_eq_zero_of_eq_zero (fun n hn => by rw [hΛlam n hn, sub_self])]
    ring
  have ta := tendsto_integral_truncTest_mul_exp hδ hF0 (c := -1 / 2) (by norm_num [abs_of_neg])
  have tb := tendsto_integral_truncTest_mul_exp hδ hF0 (c := 1 / 2) (by norm_num)
  have hneg : ∀ u : ℝ, (-1 / 2 : ℝ) * u = -u / 2 := fun u => by ring
  have hpos2 : ∀ u : ℝ, (1 / 2 : ℝ) * u = u / 2 := fun u => by ring
  simp_rw [hneg] at ta
  simp_rw [hpos2] at tb
  have hpole : Tendsto (fun L => 2 * (a L * b L)) atTop (𝓝 (1 / 2)) := by
    rw [← pole_xiShiftedGammaTest_zero]
    exact (ta.mul tb).const_mul 2
  have hlim : Tendsto (fun L => (weilPoleWeightFunctional β lam
      (EF.weilTest (fun u => (truncTest F L u : ℂ)) fun u => (truncTest F L u : ℂ))).re) atTop
      (𝓝 (0 + (β - 1) * (1 / 2))) :=
    (tendsto_re_W_truncTest_xiShiftedGammaTest_zero.add (hpole.const_mul (β - 1))).congr
      fun L => (hsplit L).symm
  have hge := ge_of_tendsto hlim (Eventually.of_forall hpos)
  linarith

/-- **A reduced pole is never enough on the even cone.** -/
theorem not_primeBlindPositiveEvenAt_of_lt_one {β : ℝ} (hβ : β < 1) :
    ¬ PrimeBlindPositiveEvenAt β := fun h =>
  absurd (one_le_of_primeBlindPositiveEvenAt h) (not_le.mpr hβ)

/-- **RH is the statement that the even window is exactly `[1, ∞)`.** -/
theorem riemannHypothesis_iff_forall_primeBlindPositiveEvenAt_iff :
    RiemannHypothesis ↔ ∀ β : ℝ, PrimeBlindPositiveEvenAt β ↔ 1 ≤ β :=
  ⟨fun hRH _ => ⟨one_le_of_primeBlindPositiveEvenAt,
      fun hβ => primeBlindPositiveEvenAt_of_riemannHypothesis hRH hβ⟩,
    fun h => riemannHypothesis_iff_primeBlindPositiveEvenAt.mpr ((h 1).mpr le_rfl)⟩

end RHTower.EvenSector

end
