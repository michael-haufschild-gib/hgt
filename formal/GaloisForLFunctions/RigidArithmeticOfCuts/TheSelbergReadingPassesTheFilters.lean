import GaloisForLFunctions.RigidArithmeticOfCuts.TheQuadraticGapIsTheHarmonicMass
import GaloisForLFunctions.ArithmeticProduction.BilinearFormsAreParityBlind

/-!
# The Selberg reading passes the filters

A parity-breaking input has to pass three filters: the Liouville twin, Type I data and Type II data. Type I data are tests
`Σ_{n ≤ N} a(n) W(n)` with a divisor sum `W`. Type II data are the admissible constants of the forms `Σ α_m β_n a(mn)`.

The quadratic Selberg reading passes all three.

* **The twin.** The reading of `−λΛ` leaves that of `Λ` at the exact rate `4 L (−ζ′/ζ(2))` (`tendsto_selberg_twin_gap`).
* **Type I.** A linear test of size `B` moves by at most `2 B ψ(√N)` from `Λ` to any filtered twin
  (`abs_sum_sub_filteredTwin_mul_le`). So a Type I test computing the Selberg gap has size at least `δ √N`
  (`exists_le_of_typeI_represents_gap`). A divisor sum of level `N^{1−δ}` with coefficients `≪ log N` has size `N^{o(1)}`.
* **Type II.** The constants of `λΛ` and `Λ` agree on every box, and the reading separates them, so it is not a function of
  Type II data (`not_isBilinearStatement_selberg`).

What the reading sees is the harmonic mass of even prime powers. So passing these filters is not yet control of `λ` on all integers.
-/

open Finset Filter Topology
open ArithmeticFunction (vonMangoldt)
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics
open GaloisForLFunctions.ArithmeticOfSquareRootPrecision
open GaloisForLFunctions.ArithmeticProduction

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- **A bounded linear test cannot see a filtered twin above `√N`.** -/
theorem abs_sum_sub_filteredTwin_mul_le {b : ℕ → ℝ} (hb : IsEvenFilter b) {W : ℕ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (N : ℕ) (hW : ∀ n ∈ Ioc 0 N, |W n| ≤ D) :
    |∑ n ∈ Ioc 0 N, (vonMangoldtWeight n - filteredTwin b n) * W n| ≤
      2 * D * ((Real.log 4 + 4) * (Nat.sqrt N : ℝ)) := by
  have hexp : ∀ n, vonMangoldtWeight n - filteredTwin b n = 2 * b n := fun n => by
    rw [filteredTwin]
    ring
  simp_rw [hexp]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Ioc 0 N, |2 * b n * W n| ≤ 2 * D * b n := by
    intro n hn
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (hb.nonneg n)]
    have := mul_le_mul_of_nonneg_left (hW n hn) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hb.nonneg n))
    linarith
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (hb.sum_le N) (by positivity)

theorem primeSquareMass_pos : 0 < primeSquareMass := by
  have h := levelConstant_pos 0
  have h0 : harmonicMass evenVonMangoldt 0 = 0 := by simp [harmonicMass]
  rwa [levelConstant, h0, sub_zero] at h

/-- **Type I data do not compute the gap.** A linear test `W_N` that computes the Selberg gap of the twin has size at least
`δ √N`. -/
theorem exists_le_of_typeI_represents_gap (hP : IsProducer c m B) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (W : ℕ → ℝ) (D : ℝ), 0 ≤ D →
      (∀ n ∈ Ioc 0 N, |W n| ≤ D) →
      ledger c (selbergWeight vonMangoldtWeight) N - ledger c (selbergWeight twinWeight) N =
        ∑ n ∈ Ioc 0 N, (vonMangoldtWeight n - twinWeight n) * W n →
      δ * Real.sqrt N ≤ D := by
  have hL := stencilSlope_pos hP
  have hκ := primeSquareMass_pos
  have hC : (0 : ℝ) < Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  have hlim := tendsto_selberg_twin_gap hP
  have hpos : 2 * stencilSlope c * primeSquareMass < 4 * stencilSlope c * primeSquareMass := by
    have : 0 < stencilSlope c * primeSquareMass := mul_pos hL hκ
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds hpos))
  refine ⟨stencilSlope c * primeSquareMass / (Real.log 4 + 4), by positivity, N₀ + 1, fun N hN W D hD hW hrep => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hgap := hN₀ N (by omega)
  rw [lt_div_iff₀ hN0] at hgap
  have htw : twinWeight = filteredTwin evenVonMangoldt := filteredTwin_even.symm
  have hbound := abs_sum_sub_filteredTwin_mul_le isEvenFilter_even hD N hW
  rw [← htw, ← hrep] at hbound
  have h1 := (le_abs_self _).trans hbound
  have hsq : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have hprod : 2 * D * ((Real.log 4 + 4) * (Nat.sqrt N : ℝ)) ≤
      2 * D * ((Real.log 4 + 4) * Real.sqrt N) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hC.le) (by positivity)
  have hmain : stencilSlope c * primeSquareMass * N ≤ D * ((Real.log 4 + 4) * Real.sqrt N) := by
    nlinarith
  have hrt : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hrtpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have h2 : stencilSlope c * primeSquareMass * Real.sqrt N * Real.sqrt N ≤
      D * (Real.log 4 + 4) * Real.sqrt N := by
    calc _ = stencilSlope c * primeSquareMass * N := by rw [mul_assoc _ (Real.sqrt N), hrt]
      _ ≤ _ := by linarith
  exact le_of_mul_le_mul_right h2 hrtpos

/-- The quadratic reading of a weight stays within the fixed margin of that of `Λ`. -/
def SelbergReadingNearLambda (c : ℕ →₀ ℤ) (a : ℕ → ℝ) : Prop :=
  ¬ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ledger c (conv a a) N ≤
    ledger c (conv vonMangoldtWeight vonMangoldtWeight) N - Real.log 2 / 2 * stencilSlope c * N

/-- **Type II data do not compute the reading.** The constants of `λΛ` and `Λ` agree on every box, and the reading separates
them. So the reading is not a function of Type II data. -/
theorem not_isBilinearStatement_selberg (hP : IsProducer c m B) :
    ¬ IsBilinearStatement (SelbergReadingNearLambda c) := by
  intro hS
  have hiff := hS.iff_liouvilleTwist vonMangoldtWeight
  rw [liouvilleTwist_vonMangoldt] at hiff
  have hconv : conv liouvilleWeight liouvilleWeight = conv twinWeight twinWeight := by
    funext n
    simp [conv, twinWeight]
  have htwin : ¬ SelbergReadingNearLambda c liouvilleWeight := by
    intro h
    apply h
    rw [hconv]
    exact exists_ledger_conv_twin_gap hP
  have hΛ : SelbergReadingNearLambda c vonMangoldtWeight := by
    rintro ⟨N₀, hN₀⟩
    have hL := stencilSlope_pos hP
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h := hN₀ (N₀ + 1) (by omega)
    have hpos : 0 < Real.log 2 / 2 * stencilSlope c * ((N₀ + 1 : ℕ) : ℝ) := by positivity
    linarith
  exact htwin (hiff.mpr hΛ)

end GaloisForLFunctions.RigidArithmeticOfCuts
