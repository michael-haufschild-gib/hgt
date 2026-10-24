import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationRateIsTheDepthOfTheDeepestSeenZero

/-!
# Eventual Hasse–Weil is Hasse–Weil

Over `𝔽_q` a bound `|N_m − q^m − 1| ≤ C q^{m/2}` for all large `m`, with any constant `C`,
already implies the Riemann hypothesis for the curve and hence the sharp bound with `C = 2g` for
every `m`: the eigenvalues are read off from the growth of `N_m`. The same self-improvement holds
on the orbit of every cycle of a symmetric tempered configuration.

* **Eventual rate bounds are rate bounds** (`blindAbove_of_eventually_le`). If
  `|c_x(t)| ≤ K e^{σ t}` for all `t ≥ T`, then `x` sees no zero deeper than `σ`: on `[0, T]` the
  orbit correlation is bounded by the trivial rate `½` (`orbitCorr_le_of_blindAbove`).
* **Eventual Hasse–Weil is Hasse–Weil** (`hasseWeilAt_of_eventually_bounded`). If the orbit
  correlation of `x` is bounded, by any constant, at all sufficiently large scales, then `x`
  satisfies the sharp Hasse–Weil bound `|c_x(t)| ≤ c_x(0)` at every scale. No finite set of scales
  is needed and no constant is lost.
* **For `ζ`** (`riemannHypothesis_iff_eventually_bounded_of_generic`): for a spectrally generic real
  test, RH holds iff `W(f, f(· − t))` stays bounded as `t → ∞`.
-/

noncomputable section

open Complex Finset
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

/-- Every test sees no zero deeper than `½`: the zeros lie in the strip. -/
theorem blindAbove_half (Z : ZeroConfig) (f : ℝ → ℝ) : BlindAbove Z (1 / 2) f := by
  intro ρ hρ hdeep
  have h := Z.strip ρ hρ
  exact absurd hdeep (not_lt.mpr (abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩))

/-- **Eventual rate bounds are rate bounds.** On a symmetric tempered configuration, if
`|c_x(t)| ≤ K e^{σ t}` for all `t ≥ T` (`σ ≥ 0`), then `x` sees no zero deeper than `σ`. -/
theorem blindAbove_of_eventually_le (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {σ : ℝ} (hσ : 0 ≤ σ) (x : ScalingCycle) {T K : ℝ}
    (hK : ∀ t : ℝ, T ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (σ * t)) :
    BlindAbove Z σ x.2.2 := by
  set C := ∑' ρ : Z.carrier, ‖Z.Wsummand (cx x.2.2) (cx x.2.2) ρ‖ with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  refine blindAbove_of_orbitCorr_le Z hZ hFE hσ x (K := max K 0 + C * Real.exp (max T 0 / 2))
    fun t ht => ?_
  have he : 1 ≤ Real.exp (σ * t) := Real.one_le_exp (mul_nonneg hσ ht)
  have hpos : 0 ≤ C * Real.exp (max T 0 / 2) := mul_nonneg hC0 (Real.exp_pos _).le
  rcases le_or_gt T t with hTt | htT
  · calc |(configScalingDatum Z hZ).orbitCorr x t| ≤ K * Real.exp (σ * t) := hK t hTt
      _ ≤ max K 0 * Real.exp (σ * t) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ (max K 0 + C * Real.exp (max T 0 / 2)) * Real.exp (σ * t) := by
          nlinarith [Real.exp_pos (σ * t)]
  · have h := orbitCorr_le_of_blindAbove Z hZ x (blindAbove_half Z x.2.2) t
    rw [abs_of_nonneg ht] at h
    have hT : 1 / 2 * t ≤ max T 0 / 2 := by
      have : t ≤ max T 0 := le_max_of_le_left htT.le
      linarith
    calc |(configScalingDatum Z hZ).orbitCorr x t| ≤ C * Real.exp (1 / 2 * t) := h
      _ ≤ C * Real.exp (max T 0 / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hT) hC0
      _ ≤ (max K 0 + C * Real.exp (max T 0 / 2)) * 1 := by
          nlinarith [le_max_right K 0]
      _ ≤ (max K 0 + C * Real.exp (max T 0 / 2)) * Real.exp (σ * t) :=
          mul_le_mul_of_nonneg_left he (by nlinarith [le_max_right K 0])

/-- **Eventual Hasse–Weil is Hasse–Weil.** On a symmetric tempered configuration, a cycle whose
orbit correlation is bounded, by any constant, at all sufficiently large scales satisfies the
sharp Hasse–Weil bound at every scale. -/
theorem hasseWeilAt_of_eventually_bounded (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) (x : ScalingCycle) {T K : ℝ}
    (hK : ∀ t : ℝ, T ≤ t → |(configScalingDatum Z hZ).orbitCorr x t| ≤ K) (t : ℝ) :
    (configScalingDatum Z hZ).HasseWeilAt x t := by
  have hb := blindAbove_of_eventually_le Z hZ hFE le_rfl x (T := T) (K := K) fun s hs => by
    rw [zero_mul, Real.exp_zero, mul_one]; exact hK s hs
  rw [blindAbove_zero_iff] at hb
  exact (configScalingDatum Z hZ).hasseWeilAt_of_orbitHodgeIndex
    (orbitHodgeIndex_of_blindOffLine Z hZ x hb) t

/-- **For `ζ`: RH iff one generic orbit correlation stays bounded at large scales.** -/
theorem riemannHypothesis_iff_eventually_bounded_of_generic (x : ScalingCycle)
    (hgen : RealSpectrallyGeneric zetaZeroConfig x.2.2) :
    RiemannHypothesis ↔ ∃ T K : ℝ, ∀ t : ℝ, T ≤ t → |zetaScalingDatum.orbitCorr x t| ≤ K := by
  rw [riemannHypothesis_iff_hasseWeil_of_generic x hgen]
  constructor
  · intro h
    refine ⟨0, zetaScalingDatum.orbitCorr x 0, fun t _ => ?_⟩
    exact h t
  · rintro ⟨T, K, hK⟩ t
    rw [zeta_hasseWeilAt_iff]
    refine hasseWeilAt_of_eventually_bounded zetaZeroConfig temperedConfig_zetaZeroConfig
      fesSymmetric_zetaZeroConfig x (T := T) (K := K) (fun s hs => ?_) t
    rw [configScalingDatum_zeta_orbitCorr]
    exact hK s hs

end GaloisForLFunctions.ArithmeticOrientationGeometry
