import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkDeterminesTheSecondOrderTerm
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface

/-!
# The window index

The second-order term of a horizon window at the multiple `K` of the critical curve is
`L_K(h) = κ Q(H) + (βJ/K) ‖H‖²_{−(β+1)}`. On a finite family of windows `h_i` it polarizes to the
**pencil Gram matrix** `P_K = κ Q(H_i, H_j) + (βJ/K) ⟨H_i, H_j⟩_{−(β+1)}`, and the complete Weil
family restricted to the horizon blocks of the family has the Gram matrix `G_N` (Weil's form of the
atomic tests). This file proves:

* **Matrix convergence** (`tendsto_horizonGram`): `(c⁻¹/∫g²) G_N → P_K` entrywise along the
  critical curve, by polarization of the scalar second-order theorem (EAHT `weilPair_real_eq`).
* **The window index is read by the complete family** (`eventually_hermNegIndex_pencilGram_le`):
  eventually `ind₋(P_K) ≤ ind₋(G_N)`, by lower semicontinuity of the index (HKT).
* **Its structural bound** (`hermNegIndex_pencilGram_le_offLineCount`): `ind₋(P_K)` is at most the
  number of zeros of `ζ` right of the critical line (ACS), for every family and every multiple.

The window index at multiple `K` is the integer of carrier C in the language of the degeneration: it
counts the directions in which Weil's form is more negative than the aliasing norm pays at `K`; it is
`0` for every family and every `K` under RH and it never exceeds the number of right zeros.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ} {A : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The horizon test of a window profile `h`: the atomic test of the block `x_n = h(log(n/N))/√n`. -/
def horizonTest (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) : ℝ → ℝ :=
  atomicTest N (horizonWeights h N) (atomDilate φ (c / N))

/-- The second-order limit of a window at the multiple `K` of the critical curve. -/
def secondOrderLimit (φ : ℝ → ℝ) (β J K : ℝ) (h : ℝ → ℝ) : ℝ :=
  (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h) +
    β * J / K * ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2

/-- The pencil Gram matrix: the polarization of the second-order limit on a family of windows. -/
def pencilGram (φ : ℝ → ℝ) (β J K : ℝ) (h : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  fun i j => (((secondOrderLimit φ β J K (fun y => h i y + h j y) -
    secondOrderLimit φ β J K (fun y => h i y - h j y)) / 4 : ℝ) : ℂ)

/-- The Gram matrix of Weil's form on the horizon tests of a family of windows. -/
def horizonGram (φ : ℝ → ℝ) (h : ι → ℝ → ℝ) (c : ℝ) (N : ℕ) : Matrix ι ι ℂ :=
  weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) fun i => cx (horizonTest φ (h i) c N)

/-! ### Linearity of horizon tests -/

theorem horizonTest_add (φ h h' : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (fun u => horizonTest φ h c N u + horizonTest φ h' c N u) =
      horizonTest φ (fun y => h y + h' y) c N := by
  funext u
  simp only [horizonTest, atomicTest, horizonWeights, add_div, add_mul, sum_add_distrib]

theorem horizonTest_sub (φ h h' : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (fun u => horizonTest φ h c N u - horizonTest φ h' c N u) =
      horizonTest φ (fun y => h y - h' y) c N := by
  funext u
  simp only [horizonTest, atomicTest, horizonWeights, sub_div, sub_mul, sum_sub_distrib]

theorem contDiff_horizonTest (hφ : ContDiff ℝ 2 φ) (h : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    ContDiff ℝ 2 (horizonTest φ h c N) := by
  unfold horizonTest
  have hg : ContDiff ℝ 2 (atomDilate φ (c / N)) := by
    unfold atomDilate; exact hφ.comp (contDiff_id.div_const _)
  exact contDiff_atomicTest hg N _

theorem hasCompactSupport_horizonTest (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (h : ℝ → ℝ)
    {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) : HasCompactSupport (horizonTest φ h c N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := fun u hu => by
    unfold atomDilate
    refine hφsupp _ fun hm => hu ?_
    obtain ⟨h0, h1⟩ := hm
    exact ⟨by rw [le_div_iff₀ hw, zero_mul] at h0; exact h0,
      by rw [div_le_one hw] at h1; exact h1⟩
  exact hasCompactSupport_atomicTest hg N _

omit [Fintype ι] [DecidableEq ι] in
/-- The entries of the horizon Gram matrix by polarization. -/
theorem horizonGram_apply (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (h : ι → ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (i j : ι) :
    horizonGram φ h c N i j =
      (((weilQuad (horizonTest φ (fun y => h i y + h j y) c N) -
        weilQuad (horizonTest φ (fun y => h i y - h j y) c N)) / 4 : ℝ) : ℂ) := by
  unfold horizonGram weilGram
  rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (contDiff_horizonTest hφ _ c N)
    (hasCompactSupport_horizonTest hφsupp _ hc hN) (contDiff_horizonTest hφ _ c N)
    (hasCompactSupport_horizonTest hφsupp _ hc hN), horizonTest_add, horizonTest_sub]

/-! ### Matrix convergence and the index -/

omit [Fintype ι] [DecidableEq ι] in
/-- **Matrix convergence**: along the critical curve, `(c⁻¹/∫g²) G_N → P_K` entrywise. -/
theorem tendsto_horizonGram (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 ≤ A)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    (i j : ι) :
    Tendsto (fun N : ℕ => ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
      horizonGram φ h (c N) N) i j) atTop (𝓝 (pencilGram φ β J K h i j)) := by
  have hlim : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → (∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) →
      Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (horizonTest φ g (c N) N) /
        ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop (𝓝 (secondOrderLimit φ β J K g)) :=
    fun g hg hgs => horizon_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hp hCφ hdecay hβ
      hbulk hg hA hgs hc1 hK hcrit
  have hp' := hlim (fun y => h i y + h j y) ((hh i).add (hh j)) fun y hy => by
    simp [hsupp i y hy, hsupp j y hy]
  have hm' := hlim (fun y => h i y - h j y) ((hh i).sub (hh j)) fun y hy => by
    simp [hsupp i y hy, hsupp j y hy]
  have hreal := ((hp'.sub hm').div_const 4)
  refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hc0 : 0 < c N := by linarith [hc1 N]
  simp only [Function.comp_apply, Matrix.smul_apply, smul_eq_mul]
  rw [horizonGram_apply hφ hφsupp h hc0 hN, ← Complex.ofReal_mul]
  congr 1
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem pencilGram_isHermitian (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 ≤ A)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    (pencilGram φ β J K h).IsHermitian := by
  ext j i
  have h1 := tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit j i
  have h2 := (continuous_star.tendsto _).comp
    (tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit i j)
  have hsym : ∀ N : ℕ, star (((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
      horizonGram φ h (c N) N) i j) = ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
        horizonGram φ h (c N) N) j i := fun N => by
    have hG := (weilGram_isHermitian (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      fun i => cx (horizonTest φ (h i) (c N) N)).apply j i
    simp only [Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
    unfold horizonGram
    rw [← Complex.star_def, hG]
  have h3 : Tendsto (fun N : ℕ => ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
      horizonGram φ h (c N) N) j i) atTop (𝓝 (star (pencilGram φ β J K h i j))) :=
    h2.congr fun N => hsym N
  rw [Matrix.conjTranspose_apply]
  exact tendsto_nhds_unique h3 h1

/-- **The complete family reads the window index**: eventually `ind₋(P_K) ≤ ind₋(G_N)`. -/
theorem eventually_hermNegIndex_pencilGram_le (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 ≤ A)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, hermNegIndex (pencilGram φ β J K h) ≤
      hermNegIndex (horizonGram φ h (c N) N) := by
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex
    (pencilGram_isHermitian hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit)
    (tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  rwa [hermNegIndex_ofReal_smul hs] at hN

/-- **The structural bound of the window index**: `ind₋(P_K)` never exceeds the number of zeros of
`ζ` right of the critical line. -/
theorem hermNegIndex_pencilGram_le_offLineCount (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 ≤ A)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    (hermNegIndex (pencilGram φ β J K h) : ℕ∞) ≤
      {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  obtain ⟨N, hN, hN1⟩ := ((eventually_hermNegIndex_pencilGram_le hφ hφsupp hφ2 hp hCφ hdecay hβ
    hbulk hh hA hsupp hc1 hK hcrit).and (eventually_ge_atTop 1)).exists
  have hc0 : 0 < c N := by linarith [hc1 N]
  have hub := negIndex_weilGram_le_offLineCount (fun i => cx (horizonTest φ (h i) (c N) N))
    (fun i => cx_contDiff (contDiff_horizonTest hφ _ _ _))
    (fun i => cx_hasCompactSupport (hasCompactSupport_horizonTest hφsupp _ hc0 hN1))
  exact (ENat.coe_le_coe.mpr hN).trans hub

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
