import GaloisForLFunctions.RHTower.Sieve.GuthMaynardTheoremOneOne
import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervalsTwoFifteenths
import GaloisForLFunctions.RHTower.PrimeCountingShortIntervalsSeventeenThirtiethsSharp
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsSharp
import GaloisForLFunctions.RHTower.ZetaZeroDensityGuthMaynardBox
import GaloisForLFunctions.RHTower.ZetaZeroDensityGuthMaynardClassCount
import GaloisForLFunctions.RHTower.ZetaZeroDensityThirtyThirteenths

/-!
# Guth–Maynard corollaries with the large values estimate discharged

The large values estimate `GuthMaynardLargeValuesBound` (Guth–Maynard Theorem 1.1) is proved by
`guthMaynardLargeValuesBound_holds`.  Feeding it into the corpus' conditional corollaries gives:

* almost all intervals `(x, x + x^θ]`, `θ > 2/15`, carry the expected `ψ`-mass (Corollary 1.4);
* the sharp short-interval asymptotics for `ψ` and `π` at length `x^{17/30+ε}` (Corollary 1.3);
* the zero-density bounds at fixed `σ` (Theorem 1.2 in its pointwise forms);
* the bounded-coefficient and dyadic-range forms of Theorem 1.1, and the window class count.
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Filter Topology MeasureTheory RHTower.Sieve RHTower.GuthMaynard

/-- **Primes in almost all short intervals, `θ > 2/15`.**  Outside a set of measure at most
`X e^{-(log X)^{1/4}}`, every `x ∈ [X, 2X]` has
`|ψ(x + h) − ψ(x) − h| ≤ e^{-(log X)^{1/4}} h` with `h = X^{θ−1} x`. -/
theorem exists_volume_psi_almost_all_short_le_unconditional {θ : ℝ}
    (hθ : 2 / 15 < θ) (hθ1 : θ < 1) :
    ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧
        Real.exp (-(Real.log X ^ ((1 : ℝ) / 4))) * (X ^ (θ - 1) * x)
          < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x
              - X ^ (θ - 1) * x|}).toReal
        ≤ X * Real.exp (-(Real.log X ^ ((1 : ℝ) / 4))) :=
  exists_volume_psi_almost_all_short_le guthMaynardLargeValuesBound_holds hθ hθ1

/-- **Sharp prime count in `(x, x + y]`, `x^{17/30+ε} ≤ y ≤ x^{99/100}`.** -/
theorem exists_abs_primeCounting_short_interval_le_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 4 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |(Nat.primeCounting ⌊x + y⌋₊ : ℝ) - Nat.primeCounting ⌊x⌋₊ - y / Real.log x|
        ≤ y * Real.exp (-(Real.log x ^ ((1 : ℝ) / 4))) :=
  exists_abs_primeCounting_short_interval_le guthMaynardLargeValuesBound_holds hε

/-- **Sharp `ψ`-increment in `(x, x + y]`, `x^{17/30+ε} ≤ y ≤ x^{99/100}`**, with saving
`e^{-K (log x)^{1/4}}` for every constant `K`. -/
theorem exists_abs_psi_short_interval_le_unconditional {ε K : ℝ} (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ x₀ : ℝ, 4 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ y : ℝ,
      x ^ (17 / 30 + ε) ≤ y → y ≤ x ^ ((99 : ℝ) / 100) →
      |Chebyshev.psi (x + y) - Chebyshev.psi x - y|
        ≤ y * Real.exp (-(K * Real.log x ^ ((1 : ℝ) / 4))) :=
  exists_abs_psi_short_interval_le guthMaynardLargeValuesBound_holds hε hK

/-- **Guth–Maynard large values for coefficients bounded by `B`.** -/
theorem guthMaynardLargeValuesBound_scaled {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ V B : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ N → 2 ≤ T → 0 < V → 0 < B → (∀ n, ‖b n‖ ≤ B) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) →
      (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, V ≤ ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * (B ^ 2 * (N : ℝ) ^ 2 / V ^ 2
        + B ^ 4 * (N : ℝ) ^ (18/5 : ℝ) / V ^ 4 + T * B ^ 4 * (N : ℝ) ^ (12/5 : ℝ) / V ^ 4) :=
  guthMaynardLargeValuesBound_holds.scaled hε

/-- **Guth–Maynard large values on `R` dyadic blocks** `(N₀, 2^R N₀]`. -/
theorem guthMaynardLargeValuesBound_card_le_of_dyadic_range {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N₀ R : ℕ) (T T₀ V B : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ N₀ → 1 ≤ R → 2 ≤ T → 0 < V → 0 < B → (∀ n, ‖b n‖ ≤ B) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, V ≤
        ‖∑ n ∈ Finset.Ioc N₀ (N₀ * 2 ^ R), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ R * (C * T ^ ε * (B ^ 2 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ 2 / (V / R) ^ 2
        + B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (18/5 : ℝ) / (V / R) ^ 4
        + T * B ^ 4 * ((N₀ * 2 ^ R : ℕ) : ℝ) ^ (12/5 : ℝ) / (V / R) ^ 4)) :=
  guthMaynardLargeValuesBound_holds.card_le_of_dyadic_range hε

/-- **Zero density at a fixed `σ ∈ [7/10, 8/10]`** with the Guth–Maynard exponent. -/
theorem exists_zeroHeightBox_ncard_le_gm_unconditional {σ ε : ℝ}
    (hσ0 : 7 / 10 ≤ σ) (hσ1 : σ ≤ 8 / 10) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ 12 * T ^ (gmDensityExponent σ + ε) :=
  exists_zeroHeightBox_ncard_le_gm guthMaynardLargeValuesBound_holds hσ0 hσ1 hε

/-- **The exponent `30/13` at a fixed `σ ∈ [1/2, 5/6]`.** -/
theorem exists_zeroHeightBox_ncard_le_fixed_thirty_thirteenths_unconditional
    {σ ε : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 6) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ((zeroHeightBox σ T).ncard : ℝ)
        ≤ D * (1 + Real.log T) ^ B * T ^ ((30 / 13) * (1 - σ) + ε) :=
  exists_zeroHeightBox_ncard_le_fixed_thirty_thirteenths guthMaynardLargeValuesBound_holds
    hσ0 hσ1 hε hε1

/-- **The Guth–Maynard class count at a fixed `σ ∈ (3/5, 9/10)`**: well-spaced heights where a
detector block's abscissa Taylor polynomial is large are at most `K T^{E₀+ε}` in number. -/
theorem exists_gm_window_class_card_le_unconditional
    {a δ σ α E₀ ε : ℝ} {M : ℕ} (ha0 : 0 < a) (ha1 : a ≤ 1) (hδ0 : 0 < δ)
    (hM : 2 * a / δ ≤ M) (hM2 : 2 ≤ M) (hσ0 : 3 / 5 < σ) (hσ1 : σ < 9 / 10) (hε : 0 < ε)
    (hd : 3 * a * (1 - σ) ≤ E₀) (hg2 : α * (18 / 5 - 4 * σ) ≤ E₀)
    (hg3 : 1 + a * (12 / 5 - 4 * σ) ≤ E₀) (hm : 1 + α * (1 - 2 * σ) ≤ E₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (j i : ℕ) (σ' : ℝ), σ ≤ σ' → ∀ W : Finset ℝ,
        (∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) →
        (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
        (∀ t ∈ W, 1 / (48 * (gDetBlockCount (pDetCut (3 * a / 4) T) : ℝ)) ≤
          ‖abscissaTaylorPoly (gDetBlock (pDetCut (3 * a / 4) T) j)
            (fun k => ((gDetCoeff (pDetMoll δ T) (pDetSmooth (3 * a / 4) T) k : ℝ) : ℂ))
            (gDetLog (pDetCut (3 * a / 4) T)) i σ' t‖) →
        (W.card : ℝ) ≤ K * T ^ (E₀ + ε) :=
  exists_gm_window_class_card_le guthMaynardLargeValuesBound_holds ha0 ha1 hδ0 hM hM2 hσ0 hσ1 hε
    hd hg2 hg3 hm

end RHTower

end
