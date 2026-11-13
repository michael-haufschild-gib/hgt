import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsAtMostItsPoleCapacity
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsCarriedByItsFloorTrees
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# The exponent of the window matrices bounds the abscissa of the zeros

Weil's form `𝔚` on the step packets of a window `(R, (3K + 1)R]` of ratio `ρ = 3K + 1` is
bounded below by a power of the ratio. The trivial exponent is `½`:

  `𝔚(σ) ≥ −C √K Σ σ²`   (`exists_packetForm_stepPacket_ge_sqrt`),

since the jets bind at most `5.4`, each floor tree adds at most `2 Λ(k)/√k` and Chebyshev gives
`Σ_{k ≤ ρ} Λ(k)/√k ≤ 34 √ρ`, while the pole term `2 (Σ σ d)(Σ σ)` is at least `−2 √K Σ σ²`
(weighted Cauchy–Schwarz). Every saving in the exponent is a zero-free strip:

  **if `𝔚(σ) ≥ −C K^θ Σ σ²` with `θ < ½`, then every zero has `|Re ρ − ½| ≤ θ`**
  (`zetaZeroWidth_le_of_packetForm_stepPacket_ge`).

The proof is the transfer of
`AUniformLowerBoundOnTheMarginOfTheWindowMatricesForcesTheRiemannHypothesis` at a fixed ratio: a lower bound `−D Σ σ²` on the step packets of ratio `3K + 1` passes to the comb
and to the zeros on the samples of the antisymmetric state of the two ends at lag `v`, for
`log K ≥ log 3 + 12 + v` (`two_re_lagStructure_le_of_packetForm_ge`). With `K ≍ e^v` the depth
`D = C K^θ` grows like `e^{θ v}`, and the rate law of the antisymmetric state
(`zetaZeroWidth_le_iff_twoEndOdd_rate`) turns this growth into the zero width.

So the trivial bound `θ = ½` is the trivial statement that the zeros lie in the strip, RH is
`θ = 0` (with any constant), and a power saving `ρ^{½ − δ}` in the lower bound of the window
matrices is the quasi-Riemann hypothesis `Re ρ ≤ 1 − δ`.
-/

open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.HodgeTheoryOfAFixedPart (combForm)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.SquareRootThreshold (lagStructure)
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### The trivial exponent -/

/-- **The pole term of a window of ratio `3K + 1` is at least `−2√K` times the mass**: weighted
Cauchy–Schwarz with the weight `q² = R √K` on the degrees `d_j ≤ 1/(R + j)`. -/
theorem neg_two_sqrt_mul_le_two_mul_charges {K R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R) (σ : ℕ → ℝ) :
    -(2 * Real.sqrt K * ∑ j ∈ range (3 * K * R), σ j ^ 2) ≤
      2 * ((∑ j ∈ range (3 * K * R), σ j * blockDegree (R + j)) *
        ∑ j ∈ range (3 * K * R), σ j) := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hRJ : (0 : ℝ) < ((R + 3 * K * R : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + 3 * K * R)
  have hq : 0 < Real.sqrt (R * Real.sqrt K) := Real.sqrt_pos.mpr (mul_pos hR0 hsK)
  have hq2 : Real.sqrt (R * Real.sqrt K) ^ 2 = R * Real.sqrt K := Real.sq_sqrt (by positivity)
  -- the degrees, with the opposite sign
  have hD : ∑ j ∈ range (3 * K * R), (-blockDegree (R + j)) ^ 2 ≤ 1 / (R : ℝ) := by
    simp only [neg_sq]
    have h := sum_sq_blockDegree_le hR (3 * K * R)
    have : 0 ≤ 1 / ((R + 3 * K * R : ℕ) : ℝ) := by positivity
    linarith
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (((R + 3 * K * R : ℕ) : ℝ) / R) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by
    rw [hL]
    exact Real.log_nonneg ((one_le_div hR0).mpr (by exact_mod_cast (by omega : R ≤ R + 3 * K * R)))
  have hsum : ∑ j ∈ range (3 * K * R), -blockDegree (R + j) = -L := by
    rw [Finset.sum_neg_distrib, sum_blockDegree_window, hL, Real.log_div hRJ.ne' hR0.ne']
  have h : 2 * ((∑ j ∈ range (3 * K * R), σ j * -blockDegree (R + j)) *
        ∑ j ∈ range (3 * K * R), σ j) ≤
      (Real.sqrt (R * Real.sqrt K) ^ 2 * (1 / (R : ℝ)) + 2 * -L +
        ((3 * K * R : ℕ) : ℝ) / Real.sqrt (R * Real.sqrt K) ^ 2) / 2 *
        ∑ j ∈ range (3 * K * R), σ j ^ 2 :=
    two_mul_sum_mul_sum_le (J := 3 * K * R) σ (fun j => -blockDegree (R + j)) hq hD hsum
  rw [hq2] at h
  have hneg : ∑ j ∈ range (3 * K * R), σ j * -blockDegree (R + j) =
      -∑ j ∈ range (3 * K * R), σ j * blockDegree (R + j) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e1 : (R : ℝ) * Real.sqrt K * (1 / (R : ℝ)) = Real.sqrt K := by
    rw [mul_comm (R : ℝ) _, mul_assoc, mul_one_div_cancel hR0.ne', mul_one]
  have e2 : ((3 * K * R : ℕ) : ℝ) / (R * Real.sqrt K) = 3 * Real.sqrt K := by
    rw [div_eq_iff (mul_pos hR0 hsK).ne']
    push_cast
    rw [show (3 : ℝ) * Real.sqrt K * (R * Real.sqrt K) = 3 * R * (Real.sqrt K * Real.sqrt K) by
      ring, Real.mul_self_sqrt hK0.le]
    ring
  rw [hneg, e1, e2] at h
  have hm : 0 ≤ ∑ j ∈ range (3 * K * R), σ j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith [mul_le_mul_of_nonneg_right hL0 hm]

/-- Chebyshev in square-root form on the contacts of a window of ratio `3K + 1`. -/
theorem sum_Icc_vonMangoldt_div_sqrt_le {K : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ Icc 2 (3 * K + 1), (Λ k : ℝ) / Real.sqrt k ≤ 68 * Real.sqrt K := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : ∑ k ∈ Icc 2 (3 * K + 1), (Λ k : ℝ) / Real.sqrt k ≤
      ∑ k ∈ Ioc 0 (3 * K + 1), (Λ k : ℝ) / Real.sqrt k :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => by
        rw [Finset.mem_Icc] at hk
        rw [Finset.mem_Ioc]
        omega)
      fun k _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have h2 := RHTower.sum_vonMangoldt_div_sqrt_le (3 * K + 1)
  have h3 : Real.sqrt ((3 * K + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt K := by
    have h4 : Real.sqrt (4 * (K : ℝ)) = 2 * Real.sqrt K := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4]
    refine Real.sqrt_le_sqrt ?_
    push_cast
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  linarith

/-- **The trivial exponent `½`**: Weil's form on the step packets of every window of ratio
`3K + 1` is at least `−C √K` times the mass. -/
theorem exists_packetForm_stepPacket_ge_sqrt :
    ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K → ∀ R : ℕ, 1 ≤ R → ∀ σ : ℕ → ℝ,
      -(C * Real.sqrt K * ∑ j ∈ range (3 * K * R), σ j ^ 2) ≤
        packetForm (3 * K + 1) (stepPacket R (3 * K * R) σ) := by
  refine ⟨138 + |EF.gammaBracket 0|, fun K hK R hR σ => ?_⟩
  have hm : 0 ≤ ∑ j ∈ range (3 * K * R), σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsK : 1 ≤ Real.sqrt K := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hK1
  rw [packetForm_stepPacket_eq_sum_blockMatrix hR, sum_blockMatrix_eq_charges_add_neutral]
  have hN := sum_neutralBlock_ge hR (3 * K + 1) (3 * K * R) σ
  have hP := neg_two_sqrt_mul_le_two_mul_charges hK hR σ
  have hS := mul_le_mul_of_nonneg_right (sum_Icc_vonMangoldt_div_sqrt_le hK) hm
  have hA : -EF.gammaBracket 0 ≤ |EF.gammaBracket 0| * Real.sqrt K := by
    have := neg_le_abs (EF.gammaBracket 0)
    nlinarith [abs_nonneg (EF.gammaBracket 0)]
  have hA' := mul_le_mul_of_nonneg_right hA hm
  have hsm := mul_le_mul_of_nonneg_right hsK hm
  linarith

/-! ### A saving in the exponent is a zero-free strip -/

/-- **A lower bound at one ratio controls the lag structure at the lags it contains.** If Weil's
form on the step packets of the windows of ratio `3K + 1` is at least `−D Σ σ²`, and
`log K ≥ log 3 + 12 + |v|`, then `2 Re S(v) ≤ 2 Re S(0) + 4 (D + 2) ∫ f₀²`. -/
theorem two_re_lagStructure_le_of_packetForm_ge {K : ℕ} (hK1 : 1 ≤ K) {v D : ℝ} (hD0 : 0 ≤ D)
    (hK : Real.log 3 + 12 + |v| ≤ Real.log K)
    (h : ∀ R : ℕ, 1 ≤ R → ∀ σ : ℕ → ℝ,
      -(D * ∑ j ∈ range (3 * K * R), σ j ^ 2) ≤
        packetForm (3 * K + 1) (stepPacket R (3 * K * R) σ)) :
    2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re ≤
      2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re +
        (D + 1 + 1) * (4 * ∫ u, poleFreeProfile u ^ 2) := by
  have hcomb : ∃ᶠ N : ℕ in atTop, ∀ c : ℕ → ℝ,
      -((D + 1) + 1) * ∑ n ∈ Ioc N (N + 3 * K * N), c n ^ 2 ≤
        combForm (Ioc N (N + 3 * K * N)) c :=
    frequently_combForm_ge_neg (by linarith) one_pos fun R hR =>
      (eventually_combForm_blockFunction_ge_neg (by omega) (le_of_eq (by ring)) one_pos
        (h R (by omega))).frequently
  have hz := neg_mul_le_zeroSum_of_frequently (contDiff_shiftedOdd v)
    (hasCompactSupport_shiftedOdd v) hK1
    (fun u hu => shiftedOdd_eq_zero v (by
      rcases hu with h | h
      · exact Or.inl h
      · exact Or.inr (hK.trans h)))
    hcomb
  rw [zeroSum_shiftedOdd] at hz
  have hm := mul_le_mul_of_nonneg_left (intervalIntegral_shiftedOdd_sq_le v K)
    (show (0 : ℝ) ≤ D + 1 + 1 by linarith)
  linarith

/-- A ratio `3K + 1` with `log 3 + 12 + v ≤ log K` and `K ≤ 6 e^{12} e^v`. -/
theorem exists_ratio_le {v : ℝ} (hv : 0 ≤ v) :
    ∃ K : ℕ, 1 ≤ K ∧ Real.log 3 + 12 + |v| ≤ Real.log K ∧
      (K : ℝ) ≤ 2 * Real.exp (Real.log 3 + 12) * Real.exp v := by
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp (Real.log 3 + 12 + v) := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by
    rw [hX]
    exact Real.one_le_exp (by have := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num); linarith)
  refine ⟨⌈X⌉₊, Nat.ceil_pos.mpr (by linarith), ?_, ?_⟩
  · rw [abs_of_nonneg hv]
    calc Real.log 3 + 12 + v = Real.log X := by rw [hX, Real.log_exp]
      _ ≤ Real.log (⌈X⌉₊ : ℕ) := Real.log_le_log (by linarith) (Nat.le_ceil _)
  · have h1 := Nat.ceil_lt_add_one (show 0 ≤ X by linarith)
    have h2 : X = Real.exp (Real.log 3 + 12) * Real.exp v := by rw [hX, Real.exp_add]
    linarith

/-- **A saving in the exponent of the window matrices is a zero-free strip.** If for some
`θ < ½` Weil's form on the step packets of every window of ratio `3K + 1` is at least
`−C K^θ Σ σ²`, every zero of `ζ` satisfies `|Re ρ − ½| ≤ θ`. -/
theorem zetaZeroWidth_le_of_packetForm_stepPacket_ge {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (h : ∀ K : ℕ, 1 ≤ K → ∀ R : ℕ, 1 ≤ R → ∀ σ : ℕ → ℝ,
      -(C * (K : ℝ) ^ θ * ∑ j ∈ range (3 * K * R), σ j ^ 2) ≤
        packetForm (3 * K + 1) (stepPacket R (3 * K * R) σ)) :
    SquareRootThreshold.zetaZeroWidth ≤ θ := by
  obtain ⟨m₀, hm₀⟩ : ∃ m, m = ∫ u, poleFreeProfile u ^ 2 := ⟨_, rfl⟩
  have hm₀0 : 0 ≤ m₀ := by rw [hm₀]; exact integral_nonneg fun u => sq_nonneg _
  obtain ⟨B, hB⟩ : ∃ B, B = (2 * Real.exp (Real.log 3 + 12)) ^ θ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine (zetaZeroWidth_le_iff_twoEndOdd_rate hθ0 hθ).mpr
    ⟨(|C| * B + 1 + 1) * (4 * m₀), fun v hv Q hQ => ?_⟩
  obtain ⟨K, hK1, hKlog, hKle⟩ := exists_ratio_le hv
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- `K^θ ≤ B e^{θ v}`
  have hKθ : (K : ℝ) ^ θ ≤ B * Real.exp (θ * v) := by
    calc (K : ℝ) ^ θ ≤ (2 * Real.exp (Real.log 3 + 12) * Real.exp v) ^ θ :=
          Real.rpow_le_rpow hK0 hKle hθ0
      _ = B * Real.exp (θ * v) := by
          rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, hB, ← Real.exp_mul, mul_comm v θ]
  have hD0 : 0 ≤ |C| * (K : ℝ) ^ θ := mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hK0 θ)
  have hlag := two_re_lagStructure_le_of_packetForm_ge hK1 hD0 hKlog fun R hR σ => by
    have h1 := h K hK1 R hR σ
    have hs : 0 ≤ ∑ j ∈ range (3 * K * R), σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hK0 θ)) hs
    linarith
  rw [← hm₀] at hlag
  rw [neutralForm_twoEndOdd v hQ]
  have he : 1 ≤ Real.exp (θ * v) := Real.one_le_exp (mul_nonneg hθ0 hv)
  have h1 := mul_le_mul_of_nonneg_left hKθ (abs_nonneg C)
  have h2 : (|C| * (K : ℝ) ^ θ + 1 + 1) * (4 * m₀) ≤
      (|C| * B + 1 + 1) * (4 * m₀) * Real.exp (θ * v) := by
    have h3 : |C| * (K : ℝ) ^ θ + 1 + 1 ≤ (|C| * B + 1 + 1) * Real.exp (θ * v) := by
      linarith
    have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : (0 : ℝ) ≤ 4 * m₀)
    linarith
  linarith

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
