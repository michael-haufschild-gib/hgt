import GaloisForLFunctions.DilutionCrystallizationPincer.DilutedPatternAndCrystalVisibilityLaw
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon

/-!
# Archimedean Domination of Diluted Off-Line Visibility

This module establishes the second leg of the **Dilution–Crystallization–Incommensurability (DCI)
Pincer**: coupling the logarithmic visibility aperture `a ≍ (1/2δ) log(L/ℓ)` of diluted off-line
lattices and crystals (`DilutedOffLineLatticeHidingLaw`, `DilutedPatternAndCrystalVisibilityLaw`)
with the unconditional single-height archimedean positivity of `ζ`
(`ZetaSingleHeightPositivityAboveArchimedeanHorizon`).

1. **Visibility witnesses have strictly positive `L²` norm (`integral_norm_sq_pos_of_re_W_neg`):**
   Every `C²` test `f` supported in `[-a, a]` with `Re Z.W(f, f) < 0` satisfies `0 < ∫ t, ‖f t‖²`.
2. **Explicit single-height archimedean dominance (`zetaZeroConfig_re_W_heightShift_pos_of_dominance`,
   `exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq`):**
   Whenever the digamma main term `log(1 + π|ξ|/4)` dominates `horizonExponent(e^{2a}) + 2 pairEnergy(½, a)`
   and the `O(1/|ξ|)` polar tail on a nonzero test `f` of aperture `a`, the localized Weil form
   `Re W_ζ(S_ξ f, S_ξ f)` is strictly positive and bounded below by `∫ t, ‖f t‖²`.
3. **Sub-barrier DCI comparison for diluted lattices (`archimedean_dominates_diluted_lattice_visibility`):**
   At any aperture `a ≤ L/2` past the logarithmic diluted threshold `2L + 2a + ℓ < ℓ e^{δ(2a - ℓ)}`,
   there exist a polar-constrained `C²` witness `f` supported in `[-a, a]` and a height horizon
   `Ξ > 0` such that `f` makes the diluted off-line lattice strictly negative
   (`Re W_{dil}(f, f) < 0`) while `ζ`'s localized Weil form is strictly positive at every height
   `|ξ| ≥ Ξ` (`Re W_ζ(S_ξ f, S_ξ f) ≥ ∫ ‖f‖² > 0`).
4. **Sub-barrier DCI comparison for diluted multi-pair crystals
   (`archimedean_dominates_diluted_crystal_visibility`):**
   The same separation holds for any `P`-pair uniform crystal of depth `δ` in background `L` as soon
   as its `k`-th constructive harmonic `2Pℓ cosh(δ k P ℓ)` exceeds `2Pℓ + 2L`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.DilutionCrystallizationPincer

open Zeta23 _root_.RHTower GaloisForLFunctions.SquareRootThreshold

/-! ### Non-vanishing of visibility witnesses and strict archimedean positivity -/

/-- Any `C²` test `f` supported in `[-a, a]` that makes the real part of a Weil form strictly
negative has strictly positive `L²` norm `0 < ∫ t, ‖f t‖ ^ 2`. -/
theorem integral_norm_sq_pos_of_re_W_neg (Z : ZeroConfig) {a : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hneg : (Z.W f f).re < 0) :
    0 < ∫ t, ‖f t‖ ^ 2 := by
  have hfsq : Integrable fun t => ‖f t‖ ^ 2 :=
    (hf.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.intro
      (isCompact_Icc (a := -a) (b := a))
      fun u (hu : u ∉ Icc (-a) a) => by simp [eq_zero_of_not_mem_Icc hfs hu])
  have hN0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rcases hN0.lt_or_eq with hNpos | hNzero
  · exact hNpos
  · exfalso
    have hae : (fun t => ‖f t‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hfsq).mp hNzero.symm
    have heq : (fun t => ‖f t‖ ^ 2) = fun _ => (0 : ℝ) :=
      (Continuous.ae_eq_iff_eq volume (hf.continuous.norm.pow 2) continuous_const).mp hae
    have hf0 : f = 0 := by
      funext t
      have := congrFun heq t
      simpa using this
    rw [hf0] at hneg
    simp [ZeroConfig.W, ZeroConfig.Wsummand, paperFT] at hneg

/-- **Explicit single-height archimedean dominance.** At any height `ξ` where the archimedean
logarithm `log(1 + π|ξ|/4)` dominates the prime-sum horizon `horizonExponent(e^{2a})`, the boundary
pair energy `2 pairEnergy(½, a)`, and the polar tail, `Re W_ζ(S_ξ f, S_ξ f) > 0`. -/
theorem zetaZeroConfig_re_W_heightShift_pos_of_dominance {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ)
    (hdom : (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 / (8 * (1 + π * |ξ|)) <
      (Real.log (1 + π * |ξ| / 4) - horizonExponent (Real.exp (2 * a)) -
        2 * pairEnergy (1 / 2) a) * ∫ t, ‖f t‖ ^ 2) :
    0 < (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have hbound := zetaZeroConfig_re_W_heightShift_ge ha hf hfs ξ
  linarith

/-- **Quantitative height horizon for strict `L²`-coercivity of `W_ζ`.** For any `C²` test `f`
supported in `[-a, a]` (`0 < a`) with `0 < ∫ t, ‖f t‖ ^ 2`, there exists `Ξ > 0` such that for
every height `ξ` with `Ξ ≤ |ξ|`,
`∫ t, ‖f t‖ ^ 2 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re`. -/
theorem exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hNpos : 0 < ∫ t, ‖f t‖ ^ 2) :
    ∃ Ξ : ℝ, 0 < Ξ ∧ ∀ ξ : ℝ, Ξ ≤ |ξ| →
      ∫ t, ‖f t‖ ^ 2 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  set N := ∫ t, ‖f t‖ ^ 2 with hN
  set B := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hB
  set E' := horizonExponent (Real.exp (2 * a)) + 2 * pairEnergy (1 / 2) a + 2 with hE'
  have hΞpos : 0 < max (4 / π * Real.exp E') (B ^ 2 / (8 * π * N)) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨max (4 / π * Real.exp E') (B ^ 2 / (8 * π * N)), hΞpos, fun ξ hξ => ?_⟩
  have h1 : 4 / π * Real.exp E' ≤ |ξ| := le_trans (le_max_left _ _) hξ
  have h2 : B ^ 2 / (8 * π * N) ≤ |ξ| := le_trans (le_max_right _ _) hξ
  have hlog : E' ≤ Real.log (1 + π * |ξ| / 4) := by
    have hexp : Real.exp E' ≤ 1 + π * |ξ| / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos] at h1
      linarith
    calc E' = Real.log (Real.exp E') := (Real.log_exp E').symm
      _ ≤ Real.log (1 + π * |ξ| / 4) := Real.log_le_log (Real.exp_pos _) hexp
  have htail : B ^ 2 / (8 * (1 + π * |ξ|)) ≤ N := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith [abs_nonneg ξ, Real.pi_pos]
  have hbound := zetaZeroConfig_re_W_heightShift_ge ha hf hfs ξ
  have hcoef : 2 * N ≤ (Real.log (1 + π * |ξ| / 4) - horizonExponent (Real.exp (2 * a)) -
      2 * pairEnergy (1 / 2) a) * N := by
    have : 2 ≤ Real.log (1 + π * |ξ| / 4) - horizonExponent (Real.exp (2 * a)) -
        2 * pairEnergy (1 / 2) a := by rw [hE'] at hlog; linarith
    nlinarith
  linarith

/-! ### Sub-barrier DCI comparison theorems -/

/-- **Sub-Barrier DCI Comparison for Diluted Lattices.** Whenever the aperture `0 < a ≤ L/2` exceeds
the logarithmic diluted hiding threshold `2L + 2a + ℓ < ℓ e^{δ(2a - ℓ)}`, there exist a
polar-constrained `C²` test `f` supported in `[-a, a]` and a height horizon `Ξ > 0` such that:
1. `f` annihilates both polar nodes (`paperFT f (I/2) = 0` and `paperFT f (-I/2) = 0`);
2. `f` detects the diluted off-line lattice (`Re W_{dil}(f, f) < 0`);
3. At every height `|ξ| ≥ Ξ`, `ζ`'s localized Weil form on `f` is strictly positive and satisfies
   `Re W_ζ(S_ξ f, S_ξ f) ≥ ∫ t, ‖f t‖² > 0`. -/
theorem archimedean_dominates_diluted_lattice_visibility {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hlarge : 2 * L + 2 * a + ℓ < ℓ * Real.exp (δ * (2 * a - ℓ))) :
    ∃ f : ℝ → ℂ, ∃ Ξ : ℝ, 0 < Ξ ∧ ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re < 0 ∧
      0 < ∫ t, ‖f t‖ ^ 2 ∧
      ∀ ξ : ℝ, Ξ ≤ |ξ| →
        ∫ t, ‖f t‖ ^ 2 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have hnot := dilutedLattice_not_hodgeIndex_of_lt hℓ hL hδ hδ' ha haL hlarge
  unfold HodgeIndexAtLevel at hnot
  push Not at hnot
  obtain ⟨f, hf, hfs, hp, hm, hneg⟩ := hnot
  have hNpos := integral_norm_sq_pos_of_re_W_neg (dilutedLatticeConfig hℓ hL hδ hδ') hf hfs hneg
  obtain ⟨Ξ, hΞ, hzeta⟩ := exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq ha hf hfs hNpos
  exact ⟨f, Ξ, hΞ, hf, hfs, hp, hm, hneg, hNpos, hzeta⟩

/-- **Sub-Barrier DCI Comparison for Diluted Multi-Pair Crystals.** For any `P`-pair uniform crystal
`(θ, d)` of depth `δ` superposed on an on-line lattice of density `L`, as soon as a harmonic lag
`kPℓ < 2a` (`1 ≤ k`, `a ≤ L/2`) satisfies `2Pℓ + 2L < 2Pℓ cosh(δ k P ℓ)`, there exist a `C²` test
`f` supported in `[-a, a]` and a height horizon `Ξ > 0` such that `f` makes the diluted crystal
strictly negative while `ζ`'s localized Weil form on `f` is strictly positive (`≥ ∫ ‖f‖² > 0`) at
all heights `|ξ| ≥ Ξ`. -/
theorem archimedean_dominates_diluted_crystal_visibility {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    {P : ℕ} (hP : 0 < P) (θ d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hunif : ∀ r, d r = δ) (hcr : ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k)
    {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (hka : ((k * P : ℕ) : ℝ) * ℓ < 2 * a) (haL : a ≤ L / 2)
    (hlarge : 2 * P * ℓ + 2 * L < 2 * P * ℓ * Real.cosh (δ * ((k * P : ℕ) * ℓ))) :
    ∃ f : ℝ → ℂ, ∃ Ξ : ℝ, 0 < Ξ ∧ ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((dilutedPatternConfig hℓ hL (scaledOffset ℓ θ) d hd0 hd1).W f f).re < 0 ∧
      0 < ∫ t, ‖f t‖ ^ 2 ∧
      ∀ ξ : ℝ, Ξ ≤ |ξ| →
        ∫ t, ‖f t‖ ^ 2 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re := by
  have ha : 0 < a := by
    have : (0 : ℝ) ≤ ((k * P : ℕ) : ℝ) * ℓ := by positivity
    linarith
  obtain ⟨f, hf, hfs, hneg⟩ := diluted_crystal_visible_at_harmonic hℓ hL hP θ d hd0 hd1 hθ
    hunif hcr hk hka haL hlarge
  have hNpos := integral_norm_sq_pos_of_re_W_neg
    (dilutedPatternConfig hℓ hL (scaledOffset ℓ θ) d hd0 hd1) hf hfs hneg
  obtain ⟨Ξ, hΞ, hzeta⟩ := exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq ha hf hfs hNpos
  exact ⟨f, Ξ, hΞ, hf, hfs, hneg, hNpos, hzeta⟩

end GaloisForLFunctions.DilutionCrystallizationPincer
