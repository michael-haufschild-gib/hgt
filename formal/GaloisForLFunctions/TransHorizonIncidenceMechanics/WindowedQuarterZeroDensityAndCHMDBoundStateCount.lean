import GaloisForLFunctions.TransHorizonIncidenceMechanics.CollectiveLowPrimeChebyshevTransportAndSinhAbsorption
import GaloisForLFunctions.RHTower.CHMDQuarterZeroBound
import GaloisForLFunctions.RHTower.WeilDeletionZeroSide
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley
import GaloisForLFunctions.RHTower.XiZeroFreeHeightBox
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovPrimeNumberTheorem

/-!
# Windowed Quarter-Zero Density, Route-T Annihilation, and Vinogradov–Korobov Chebyshev Transport

This module resolves the unwindowed `offLineZeros.Finite` bottleneck in `CHMDQuarterZeroBound.lean`
and connects `TransHorizonIncidenceMechanics` to the unconditional zero-density, zero-free region,
and Vinogradov–Korobov prime number theorem machinery in `RHTower/` and `RHTower/Sieve/`:

1. **Unconditional Finiteness and `zeroHeightBox` Injection for `windowedQuarterZeros`
   (`windowedQuarterZeros`, `windowedQuarterZeros_finite`, `ncard_windowedQuarterZeros_le_zeroHeightBox`):**
   Whereas `quarterFinset (hfin : offLineZeros.Finite)` in `CHMDQuarterZeroBound.lean:94` requires
   the unproved global finiteness hypothesis `offLineZeros.Finite`, restricting `quarterZeros` to
   any height-abscissa box `windowedQuarterZeros σ T = {ρ ∈ quarterZeros | σ ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ 2 * T}`
   embeds injectively into `RHTower.zeroHeightBox σ T` via `WeilDeletion.toCopy`. Since
   `zeroHeightBox_finite σ T` holds unconditionally, `windowedQuarterZeros σ T` is unconditionally
   finite with `(windowedQuarterZeros σ T).ncard ≤ (zeroHeightBox σ T).ncard`.

2. **Ingham–Huxley Density Bound on `windowedQuarterZeros σ T`
   (`exists_windowedQuarterZeros_ncard_le_ingham_huxley`):**
   Combines `ncard_windowedQuarterZeros_le_zeroHeightBox` with
   `RHTower.exists_zeroHeightBox_ncard_le_ingham_huxley` (`ZetaZeroDensityInghamHuxley.lean:226`)
   to bound `((windowedQuarterZeros σ T).ncard : ℝ)` unconditionally by
   `D * (1 + log T)^B * T^((inghamHuxleyExponent σ + ε) * (1 - σ))` for every `1/2 < σ ≤ 1`.

3. **Route-T Zero-Free Annihilation of `windowedQuarterZeros σ T`
   (`exists_windowedQuarterZeros_eq_empty_of_gt_routeT`,
   `exists_windowedQuarterZeros_ncard_eq_zero_of_gt_routeT`):**
   Combines `ncard_windowedQuarterZeros_le_zeroHeightBox` with `RHTower.exists_zeroHeightBox_zeroFree`
   (`XiZeroFreeHeightBox.lean:27`) to prove that `windowedQuarterZeros σ T = ∅` whenever `T ≥ T₁`
   and `σ > 1 - routeTWidthPolylogLower A (4 * T / 3)`.

4. **Vinogradov–Korobov Chebyshev Transport Bound on Dyadic Prime-Support Shells
   (`exists_abs_sum_vonMangoldt_Ioc_sub_le_vk_rate`):**
   Connects the prime-support shells of `TransHorizonIncidenceMechanics` to
   `RHTower.Sieve.exists_abs_sum_vonMangoldt_sub_self_vk_rate`
   (`VinogradovKorobovPrimeNumberTheorem.lean:178`), bounding `|(∑ d ∈ Finset.Ioc N Q, vonMangoldt d) - (Q - N)|`
   at Vinogradov–Korobov strength for all `N ≤ Q`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open scoped Real BigOperators
open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.WeilDeletion
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Unconditional Finiteness and `zeroHeightBox` Comparison for `windowedQuarterZeros` -/

/-- The quarter-strip off-line zeros in the height-abscissa box `σ ≤ Re ρ` and `T ≤ Im ρ ≤ 2T`. -/
def windowedQuarterZeros (σ T : ℝ) : Set ℂ :=
  {ρ | ρ ∈ quarterZeros ∧ σ ≤ ρ.re ∧ T ≤ ρ.im ∧ ρ.im ≤ 2 * T}

theorem windowedQuarterZeros_subset_quarterZeros (σ T : ℝ) :
    windowedQuarterZeros σ T ⊆ quarterZeros :=
  fun _ h => h.1

/-- Canonical map sending a nontrivial zero `ρ ∈ zetaZeroConfig.carrier` to its `0`-th `XiZeroCopy`
and landing in `zeroHeightBox σ T` whenever `ρ ∈ windowedQuarterZeros σ T`. -/
def windowedQuarterZeroToCopy {σ T : ℝ} (ρ : windowedQuarterZeros σ T) : XiZeroCopy :=
  WeilDeletion.toCopy ⟨ρ.1, ρ.2.1.1⟩

theorem windowedQuarterZeroToCopy_mem_zeroHeightBox {σ T : ℝ} (ρ : windowedQuarterZeros σ T) :
    windowedQuarterZeroToCopy ρ ∈ zeroHeightBox σ T := by
  obtain ⟨_, hσ, hT1, hT2⟩ := ρ.2
  exact ⟨hσ, hT1, hT2⟩

theorem windowedQuarterZeroToCopy_injective (σ T : ℝ) :
    Function.Injective (@windowedQuarterZeroToCopy σ T) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun q : XiZeroCopy => ((q.1 : XiDivisorSupport) : ℂ)) hab
  exact h

/-- **Unconditional Finiteness of `windowedQuarterZeros σ T` (`windowedQuarterZeros_finite`):**
Requires no `offLineZeros.Finite` hypothesis. -/
theorem windowedQuarterZeros_finite (σ T : ℝ) :
    (windowedQuarterZeros σ T).Finite := by
  have hsub :
      windowedQuarterZeros σ T ⊆
        (fun q : XiZeroCopy => ((q.1 : XiDivisorSupport) : ℂ)) '' zeroHeightBox σ T := by
    intro ρ hρ
    refine ⟨windowedQuarterZeroToCopy ⟨ρ, hρ⟩,
      windowedQuarterZeroToCopy_mem_zeroHeightBox ⟨ρ, hρ⟩, rfl⟩
  exact ((zeroHeightBox_finite σ T).image _).subset hsub

/-- **Unconditional Cardinality Comparison (`ncard_windowedQuarterZeros_le_zeroHeightBox`):**
For every `σ, T : ℝ`, `(windowedQuarterZeros σ T).ncard ≤ (zeroHeightBox σ T).ncard`. -/
theorem ncard_windowedQuarterZeros_le_zeroHeightBox (σ T : ℝ) :
    (windowedQuarterZeros σ T).ncard ≤ (zeroHeightBox σ T).ncard := by
  have hsub :
      windowedQuarterZeros σ T ⊆
        (fun q : XiZeroCopy => ((q.1 : XiDivisorSupport) : ℂ)) '' zeroHeightBox σ T := by
    intro ρ hρ
    refine ⟨windowedQuarterZeroToCopy ⟨ρ, hρ⟩,
      windowedQuarterZeroToCopy_mem_zeroHeightBox ⟨ρ, hρ⟩, rfl⟩
  have hfin : ((fun q : XiZeroCopy => ((q.1 : XiDivisorSupport) : ℂ)) '' zeroHeightBox σ T).Finite :=
    (zeroHeightBox_finite σ T).image _
  exact (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_image_le (zeroHeightBox_finite σ T))

/-! ## §2. Ingham–Huxley Density Bound & Route-T Zero-Free Annihilation for `windowedQuarterZeros` -/

/-- **Unconditional Ingham–Huxley Bound on `windowedQuarterZeros σ T`
(`exists_windowedQuarterZeros_ncard_le_ingham_huxley`):**
For every `1 / 2 < σ ≤ 1` and `0 < ε ≤ 1`, there exist `D ≥ 0`, `B : ℕ`, and `T₀ ≥ 1` such that for
all `T ≥ T₀`, `((windowedQuarterZeros σ T).ncard : ℝ)` is bounded by
`D * (1 + log T)^B * T^((inghamHuxleyExponent σ + ε) * (1 - σ))` with no `offLineZeros.Finite`
assumption. -/
theorem exists_windowedQuarterZeros_ncard_le_ingham_huxley {σ ε : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ((windowedQuarterZeros σ T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ B * T ^ ((inghamHuxleyExponent σ + ε) * (1 - σ)) := by
  obtain ⟨D, hD0, B, T₀, hT₀, hbound⟩ :=
    exists_zeroHeightBox_ncard_le_ingham_huxley hσ hσ1 hε hε1
  refine ⟨D, hD0, B, T₀, hT₀, fun T hT => ?_⟩
  have hle : ((windowedQuarterZeros σ T).ncard : ℝ) ≤ ((zeroHeightBox σ T).ncard : ℝ) := by
    exact_mod_cast ncard_windowedQuarterZeros_le_zeroHeightBox σ T
  exact hle.trans (hbound T hT)

/-- **Route-T Zero-Free Annihilation of `windowedQuarterZeros σ T`
(`exists_windowedQuarterZeros_eq_empty_of_gt_routeT`):**
There exist `A, T₁ : ℝ` (`1 ≤ T₁`) such that for all `T ≥ T₁` and all
`σ > 1 - routeTWidthPolylogLower A (4 * T / 3)`, `windowedQuarterZeros σ T = ∅` and
`(windowedQuarterZeros σ T).ncard = 0`. -/
theorem exists_windowedQuarterZeros_eq_empty_of_gt_routeT :
    ∃ A T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T → ∀ σ : ℝ,
      1 - routeTWidthPolylogLower A (4 * T / 3) < σ →
        windowedQuarterZeros σ T = ∅ ∧ (windowedQuarterZeros σ T).ncard = 0 := by
  obtain ⟨A, T₁, hT₁, hzf⟩ := exists_zeroHeightBox_zeroFree
  refine ⟨A, T₁, hT₁, fun T hT σ hσ => ?_⟩
  have hemp : windowedQuarterZeros σ T = ∅ := by
    by_contra hne
    obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hbox : (zeroHeightBox σ T).Nonempty :=
      ⟨windowedQuarterZeroToCopy ⟨ρ, hρ⟩, windowedQuarterZeroToCopy_mem_zeroHeightBox ⟨ρ, hρ⟩⟩
    have hle := hzf T hT σ hbox
    linarith
  exact ⟨hemp, by rw [hemp, Set.ncard_empty]⟩

/-! ## §3. Vinogradov–Korobov Chebyshev Transport Bound on Prime-Support Windows -/

/-- Exact decomposition of any Chebyshev interval sum `(∑ d ∈ Finset.Ioc N Q, vonMangoldt d) - (Q - N)`
into the difference of prefix Chebyshev errors at `Q` and `N` when `N ≤ Q`. -/
theorem abs_sum_Ioc_vonMangoldt_sub_le {N Q : ℕ} (hNQ : N ≤ Q) :
    |(∑ d ∈ Finset.Ioc N Q, (vonMangoldt d : ℝ)) - ((Q : ℝ) - (N : ℝ))| ≤
      |(∑ d ∈ Finset.range (Q + 1), (vonMangoldt d : ℝ)) - (Q : ℝ)| +
        |(∑ d ∈ Finset.range (N + 1), (vonMangoldt d : ℝ)) - (N : ℝ)| := by
  have heq : Finset.Ioc N Q = Finset.Ico (N + 1) (Q + 1) := by
    ext d
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [heq, Finset.sum_Ico_eq_sub _ (by omega : N + 1 ≤ Q + 1)]
  set EQ := (∑ d ∈ Finset.range (Q + 1), (vonMangoldt d : ℝ)) - (Q : ℝ)
  set EN := (∑ d ∈ Finset.range (N + 1), (vonMangoldt d : ℝ)) - (N : ℝ)
  have hid :
      (∑ d ∈ Finset.range (Q + 1), (vonMangoldt d : ℝ)) -
        (∑ d ∈ Finset.range (N + 1), (vonMangoldt d : ℝ)) - ((Q : ℝ) - (N : ℝ)) =
        EQ - EN := by
    dsimp [EQ, EN]
    ring
  rw [hid]
  exact abs_sub _ _

/-- **Vinogradov–Korobov Chebyshev Transport Bound on Prime Windows `(N, Q]`
(`exists_abs_sum_Ioc_vonMangoldt_sub_le_vk_rate`):**
There exists `B ≥ 0` such that eventually as `N → ∞`, for every `Q ≥ N`, the Chebyshev window
discrepancy `|(∑ d ∈ Finset.Ioc N Q, vonMangoldt d) - (Q - N)|` is bounded by the sum of the
Vinogradov–Korobov rates at `Q` and `N`. -/
theorem exists_abs_sum_Ioc_vonMangoldt_sub_le_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, ∀ {Q : ℕ}, N ≤ Q →
      |(∑ d ∈ Finset.Ioc N Q, (vonMangoldt d : ℝ)) - ((Q : ℝ) - (N : ℝ))| ≤
        B * (Q : ℝ) * Real.exp (-(vkKappa * vkScale (Q : ℝ) / 24)) +
          B * (N : ℝ) * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) := by
  obtain ⟨B, hB0, hrate⟩ := exists_abs_sum_vonMangoldt_sub_self_vk_rate
  have hev := tendsto_natCast_atTop_atTop.eventually hrate
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨B, hB0, Filter.eventually_atTop.mpr ⟨N₀, fun N hN {Q} hNQ => ?_⟩⟩
  have h1 := abs_sum_Ioc_vonMangoldt_sub_le hNQ
  have hQ :
      |(∑ d ∈ Finset.range (Q + 1), (vonMangoldt d : ℝ)) - (Q : ℝ)| ≤
        B * (Q : ℝ) * Real.exp (-(vkKappa * vkScale (Q : ℝ) / 24)) := by
    simpa only [Nat.floor_natCast] using hN₀ Q (le_trans hN hNQ)
  have hN' :
      |(∑ d ∈ Finset.range (N + 1), (vonMangoldt d : ℝ)) - (N : ℝ)| ≤
        B * (N : ℝ) * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) := by
    simpa only [Nat.floor_natCast] using hN₀ N hN
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
