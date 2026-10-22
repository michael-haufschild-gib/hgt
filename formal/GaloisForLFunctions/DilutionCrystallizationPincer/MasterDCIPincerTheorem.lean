import GaloisForLFunctions.DilutionCrystallizationPincer.PrimeTorusCrystallineResonanceObstruction
import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster

/-!
# The Master Dilution–Crystallization–Incommensurability (DCI) Pincer Theorem

This module establishes the fourth leg of the **Dilution–Crystallization–Incommensurability (DCI)
Pincer** and assembles the complete unconditional five-part master theorem across **Wall 3**
(Single-Window Clustering vs. Global Zero-Density Dilution) and **Wall 1.3** (The `√X` Prime-Side
Harnack / Cauchy–Schwarz Barrier).

1. **Sub-exponential depth-floor closure of the ground-energy rate
   (`exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_subexponential_depthFloor`,
   `polarGroundEnergyRate_eq_zetaZeroWidth_of_subexponential_depthFloor`):**
   Strengthening `TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster`, we prove that the
   effective depth-mass factor `W(A)` in `-(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A`
   need **not** be bounded by a constant `O(1)`: any sub-exponential growth bound
   `∀ ε > 0, ∃ C₀ ≥ 0, ∀ A ≥ 0, W(A) ≤ C₀ e^{εA}` (including any polynomial or logarithmic growth in
   the aperture `A`) already forces `polarGroundEnergyRate = zetaZeroWidth`.
2. **Super-exponential depth-floor obstruction (`exists_superexponential_depthFloor_of_lt`):**
   Contrapositively, if `zetaZeroWidth < polarGroundEnergyRate`, then there exists `ε > 0` such that
   no `C₀ ≥ 0` can bound the effective depth-floor factor by `C₀ e^{εA}` across all apertures `A`.
3. **Exponential height lower bound for high-depth-mass unit windows
   (`exp_depthMass_lt_height_of_window_depthMass_gt`):**
   Combining the unconditional Riemann–von Mangoldt unit-window depth-mass bound
   `∑_{q ∈ s} (Im z_q)² ≤ 40 · zetaZeroWidth² · log(180|T|)` (`sum_sq_im_xiSpectralPoint_window_le`)
   with any lower bound `W < ∑_{q ∈ s} (Im z_q)²` on `[T-1, T+1]` (`|T| ≥ 4`, `0 < zetaZeroWidth`)
   forces the exponential height lower bound
   `exp(W / (40 · zetaZeroWidth²)) < 180 |T|`.
   Thus, to sustain a super-exponential depth-floor factor `W(A) ≳ e^{εA}` at aperture `A`, unit
   windows would have to lie at double-exponential heights `180|T| > exp(e^{εA} / (40 · zetaZeroWidth²))`.
4. **Master DCI Pincer Theorem (`dci_pincer_master_theorem`):**
   Packages all five unconditional legs of the DCI Pincer into a single dependency-closed theorem.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.DilutionCrystallizationPincer

open Zeta23 _root_.RHTower GaloisForLFunctions.SquareRootThreshold

/-! ### Sub-exponential depth-floor closure of `polarGroundEnergyRate = zetaZeroWidth` -/

/-- **Pure exponential floors at every rate `σ > zetaZeroWidth` from a sub-exponential depth-floor
factor.** If `-(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A` for a function
`W : ℝ → ℝ` satisfying `W(A) ≤ C₀ e^{εA}` for every `ε > 0`, then at every rate `σ > zetaZeroWidth`
the restricted Weil ground energy satisfies `-(C e^{2σA}) ≤ ccmRestrictedWeilGroundEnergy A`. -/
theorem exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_subexponential_depthFloor
    (W : ℝ → ℝ)
    (hfloor : ∀ A : SuzukiPositiveAperture,
      -(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A)
    (hsubexp : ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ A : ℝ, 0 ≤ A → W A ≤ C₀ * Real.exp (ε * A))
    {σ : ℝ} (hσ : zetaZeroWidth < σ) :
    ∃ C : ℝ, ∀ A : SuzukiPositiveAperture,
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A := by
  set δ := (σ - zetaZeroWidth) / 2 with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨C₀, hC₀0, hWle⟩ := hsubexp (2 * δ) (by positivity)
  refine ⟨(12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀, fun A => ?_⟩
  refine le_trans ?_ (hfloor A)
  apply neg_le_neg
  have hA : 0 < A.1 := A.2
  have hpoly := sq_mul_linear_le_exp hδ0 hA.le
  have hWA := hWle A.1 hA.le
  have hsplit : Real.exp (2 * σ * A.1) =
      Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) * Real.exp (2 * δ * A.1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hδ]
    ring
  unfold depthFloorConst
  rw [hsplit]
  have h1 : A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
      Real.exp (2 * zetaZeroWidth * A.1)) * W A.1 ≤
      A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
        Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1)) := by
    refine mul_le_mul_of_nonneg_left hWA ?_
    positivity
  have h2 : A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
      Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1)) ≤
      ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
        (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
          (C₀ * Real.exp (2 * δ * A.1))) := by
    calc A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
          Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1))
        = (A.1 ^ 2 * (2 * A.1 + 2 * π)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) := by ring
      _ ≤ ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) :=
          mul_le_mul_of_nonneg_right hpoly (by positivity)
  calc A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
        Real.exp (2 * zetaZeroWidth * A.1)) * W A.1
      ≤ ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
          (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
            (C₀ * Real.exp (2 * δ * A.1))) := h1.trans h2
    _ = (12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀ *
          (Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) *
            Real.exp (2 * δ * A.1)) := by ring

/-- **Sub-exponential depth-floor closure of the ground-energy rate.** Whenever the aperture-dependent
depth-floor factor `W(A)` grows sub-exponentially in `A`, `polarGroundEnergyRate = zetaZeroWidth`. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_of_subexponential_depthFloor
    (W : ℝ → ℝ)
    (hfloor : ∀ A : SuzukiPositiveAperture,
      -(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A)
    (hsubexp : ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ A : ℝ, 0 ≤ A → W A ≤ C₀ * Real.exp (ε * A)) :
    polarGroundEnergyRate = zetaZeroWidth := by
  refine le_antisymm ?_ zetaZeroWidth_le_polarGroundEnergyRate
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨C, hC⟩ :=
    exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_subexponential_depthFloor W hfloor hsubexp
      (show zetaZeroWidth < zetaZeroWidth + ε by linarith)
  refine csInf_le bddBelow_polarGroundEnergyRates
    ⟨by linarith [zetaZeroWidth_nonneg], C, 0, fun A _ => ?_⟩
  exact (hC A).trans (ccmRestrictedWeilGroundEnergy_le_polar A)

/-- **Super-exponential depth-floor obstruction when `zetaZeroWidth < polarGroundEnergyRate`.** If
the ground-energy rate strictly exceeds the zero width, then there is an exponential rate `ε > 0`
such that for every `C₀ ≥ 0`, some aperture `A` violates the depth floor with factor
`C₀ e^{ε A}`. -/
theorem exists_superexponential_depthFloor_of_lt
    (hlt : zetaZeroWidth < polarGroundEnergyRate) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ A : SuzukiPositiveAperture,
      ccmRestrictedWeilGroundEnergy A < -(depthFloorConst (C₀ * Real.exp (ε * A.1)) A.1) := by
  set δ := (polarGroundEnergyRate - zetaZeroWidth) / 4 with hδ
  have hδ0 : 0 < δ := by linarith
  refine ⟨2 * δ, by positivity, fun C₀ hC₀0 => ?_⟩
  by_contra h
  push Not at h
  set C := (12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀ with hC
  have hbound : ∀ A : SuzukiPositiveAperture,
      -(C * Real.exp (2 * (zetaZeroWidth + 2 * δ) * A.1)) ≤
        ccmRestrictedWeilGroundEnergy A := by
    intro A
    refine le_trans ?_ (h A)
    apply neg_le_neg
    have hA : 0 < A.1 := A.2
    have hpoly := sq_mul_linear_le_exp hδ0 hA.le
    have hsplit : Real.exp (2 * (zetaZeroWidth + 2 * δ) * A.1) =
        Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) *
          Real.exp (2 * δ * A.1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    unfold depthFloorConst
    rw [hsplit, hC]
    calc A.1 ^ 2 * ((2 * A.1 + 2 * π) * Real.exp (2 * π) *
          Real.exp (2 * zetaZeroWidth * A.1)) * (C₀ * Real.exp (2 * δ * A.1))
        = (A.1 ^ 2 * (2 * A.1 + 2 * π)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) := by ring
      _ ≤ ((12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * δ * A.1)) *
            (Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1) *
              (C₀ * Real.exp (2 * δ * A.1))) :=
          mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = (12 / (2 * δ) ^ 3 + 4 * π / (2 * δ) ^ 2) * Real.exp (2 * π) * C₀ *
            (Real.exp (2 * δ * A.1) * Real.exp (2 * zetaZeroWidth * A.1) *
              Real.exp (2 * δ * A.1)) := by ring
  have hle : polarGroundEnergyRate ≤ zetaZeroWidth + 2 * δ :=
    csInf_le bddBelow_polarGroundEnergyRates
      ⟨by linarith [zetaZeroWidth_nonneg], C, 0, fun A _ =>
        (hbound A).trans (ccmRestrictedWeilGroundEnergy_le_polar A)⟩
  linarith

/-! ### Exponential height escape of high-depth-mass unit windows -/

/-- **Exponential height lower bound for high-depth-mass unit windows.** Any unit window
`[T - 1, T + 1]` at height `|T| ≥ 4` carrying squared off-line depth mass `> W` (`0 < zetaZeroWidth`)
must lie at height `180 |T| > exp(W / (40 · zetaZeroWidth²))`. -/
theorem exp_depthMass_lt_height_of_window_depthMass_gt {T W : ℝ} (hσ : 0 < zetaZeroWidth)
    (hT : 4 ≤ |T|) (s : Finset XiZeroCopy) (hs : ∀ q ∈ s, |(xiSpectralPoint q).re - T| ≤ 1)
    (hW : W < ∑ q ∈ s, (xiSpectralPoint q).im ^ 2) :
    Real.exp (W / (40 * zetaZeroWidth ^ 2)) < 180 * |T| := by
  have hsum := sum_sq_im_xiSpectralPoint_window_le hT s hs
  have hlt : W < 40 * zetaZeroWidth ^ 2 * Real.log (180 * |T|) := hW.trans_le hsum
  have hdiv : W / (40 * zetaZeroWidth ^ 2) < Real.log (180 * |T|) := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have h180 : 0 < 180 * |T| := by linarith
  calc Real.exp (W / (40 * zetaZeroWidth ^ 2))
      < Real.exp (Real.log (180 * |T|)) := Real.exp_lt_exp.mpr hdiv
    _ = 180 * |T| := Real.exp_log h180

/-! ### The Five-Part Master DCI Pincer Theorem -/

/-- **The Master Dilution–Crystallization–Incommensurability (DCI) Pincer Theorem.**
Synthesizes the five unconditional legs of the DCI Pincer across Wall 3 and Wall 1.3:
1. **Diluted Crystal Harmonic Visibility:** Any `P`-pair uniform crystal of depth `δ` in an on-line
   background `L` is strictly visible at aperture `a ≤ L/2` as soon as a crystal harmonic `kPℓ < 2a`
   satisfies `2Pℓ + 2L < 2Pℓ cosh(δ k P ℓ)`.
2. **Sub-Barrier Archimedean Domination:** Past the logarithmic diluted threshold
   `2L + 2a + ℓ < ℓ e^{δ(2a - ℓ)}`, there exist a polar-constrained `C²` test `f` of aperture `a`
   and a height horizon `Ξ > 0` where `Re W_{dil}(f, f) < 0` while `Re W_ζ(S_ξ f, S_ξ f) ≥ ∫ ‖f‖² > 0`
   for all `|ξ| ≥ Ξ`.
3. **Crystal-Gap vs. Prime-Torus Incompatibility:** In every gap `|v − nL| > 2w` of an off-line
   crystal (`4w < L`), the difference test `g_v` sees zero off-diagonal crystal response
   (`W_{crystal}(g_v, g_v) = 4L ∫ ‖κ_w‖² > 0`), while on `ζ` Kronecker alignment on the prime torus
   forces `Re Π_{g_v}(ξ) > B` and either `Re W_ζ(S_ξ g_v, S_ξ g_v) < 0` or exponential height escape.
4. **Sub-Exponential Depth-Floor Closure of the Ground-Energy Rate:** Any sub-exponential
   aperture-dependent depth-floor factor `W(A) = o(e^{εA})` forces
   `polarGroundEnergyRate = zetaZeroWidth`.
5. **Exponential Height Escape of High-Depth-Mass Unit Windows:** Any unit window `[T-1, T+1]`
   (`|T| ≥ 4`, `0 < zetaZeroWidth`) with squared depth mass `> W` must lie at height
   `180 |T| > exp(W / (40 · zetaZeroWidth²))`. -/
theorem dci_pincer_master_theorem :
    -- (1) Diluted crystal harmonic visibility
    (∀ (ℓ L δ : ℝ) (hℓ : 0 < ℓ) (hL : 0 < L) (P : ℕ) (_hP : 0 < P) (θ d : Fin P → ℝ)
      (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
      (_hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
      (_hunif : ∀ r, d r = δ) (_hcr : ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k)
      (k : ℕ) (_hk : 1 ≤ k) (a : ℝ) (_hka : ((k * P : ℕ) : ℝ) * ℓ < 2 * a) (_haL : a ≤ L / 2),
      2 * P * ℓ + 2 * L < 2 * P * ℓ * Real.cosh (δ * ((k * P : ℕ) * ℓ)) →
      ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((dilutedPatternConfig hℓ hL (scaledOffset ℓ θ) d hd0 hd1).W f f).re < 0) ∧
    -- (2) Sub-barrier archimedean domination of diluted lattice visibility
    (∀ (ℓ L δ : ℝ) (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
      (a : ℝ) (_ha : 0 < a) (_haL : a ≤ L / 2),
      2 * L + 2 * a + ℓ < ℓ * Real.exp (δ * (2 * a - ℓ)) →
      ∃ f : ℝ → ℂ, ∃ Ξ : ℝ, 0 < Ξ ∧ ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
        ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re < 0 ∧
        0 < ∫ t, ‖f t‖ ^ 2 ∧
        ∀ ξ : ℝ, Ξ ≤ |ξ| →
          ∫ t, ‖f t‖ ^ 2 ≤ (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re) ∧
    -- (3) Crystal-gap vs. prime-torus incompatibility
    (∀ (L δ C B : ℝ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (_hC0 : 0 ≤ C)
      (_hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C)
      (w : ℝ) (_hw : 0 < w) (_hwL : 4 * w < L) (v : ℝ) (_hv : 2 * w < v)
      (_hgap : ∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * L|),
      B < primeOnlyEnvelope (twoBump (modScaledBump w 0) v (-1)) ⌊Real.exp (2 * (v / 2 + w))⌋₊ -
        primePowerTailEnvelope (twoBump (modScaledBump w 0) v (-1)) ⌊Real.exp (2 * (v / 2 + w))⌋₊ →
      (offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)) =
        ((4 * L * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) ∧
      0 < ((offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re ∧
      ∃ ξ : ℝ, B < (primePolynomial (twoBump (modScaledBump w 0) v (-1))
          ⌊Real.exp (2 * (v / 2 + w))⌋₊ ξ).re ∧
        ((zetaZeroConfig.W (heightShift ξ (twoBump (modScaledBump w 0) v (-1)))
            (heightShift ξ (twoBump (modScaledBump w 0) v (-1)))).re < 0 ∨
          B - 2 * Real.exp (v / 2 + w) * (∫ u, ‖twoBump (modScaledBump w 0) v (-1) u‖) ^ 2 -
            (4 * ((∫ u, ‖twoBump (modScaledBump w 0) v (-1) u‖) +
              ∫ u, ‖deriv (deriv (twoBump (modScaledBump w 0) v (-1))) u‖)) ^ 2 * (1 / 2 + π * C) <
            (∫ t, ‖twoBump (modScaledBump w 0) v (-1) t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|))) ∧
    -- (4) Sub-exponential depth-floor closure of the ground-energy rate
    (∀ (W : ℝ → ℝ),
      (∀ A : SuzukiPositiveAperture,
        -(depthFloorConst (W A.1) A.1) ≤ ccmRestrictedWeilGroundEnergy A) →
      (∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ A : ℝ, 0 ≤ A → W A ≤ C₀ * Real.exp (ε * A)) →
      polarGroundEnergyRate = zetaZeroWidth) ∧
    -- (5) Exponential height lower bound for high-depth-mass unit windows
    (∀ (T W : ℝ), 0 < zetaZeroWidth → 4 ≤ |T| → ∀ s : Finset XiZeroCopy,
      (∀ q ∈ s, |(xiSpectralPoint q).re - T| ≤ 1) →
      W < ∑ q ∈ s, (xiSpectralPoint q).im ^ 2 →
      Real.exp (W / (40 * zetaZeroWidth ^ 2)) < 180 * |T|) :=
  ⟨fun _ _ _ hℓ hL _ hP θ d hd0 hd1 hθ hunif hcr _ hk _ hka haL hlarge =>
    diluted_crystal_visible_at_harmonic hℓ hL hP θ d hd0 hd1 hθ hunif hcr hk hka haL hlarge,
   fun _ _ _ hℓ hL hδ hδ' _ ha haL hlarge =>
    archimedean_dominates_diluted_lattice_visibility hℓ hL hδ hδ' ha haL hlarge,
   fun _ _ _ _ hL hδ hδ' hC0 hC _ hw hwL _ hv hgap hB =>
    crystal_gap_prime_torus_incompatibility hL hδ hδ' hC0 hC hw hwL hv hgap hB,
   fun W hfloor hsubexp =>
    polarGroundEnergyRate_eq_zetaZeroWidth_of_subexponential_depthFloor W hfloor hsubexp,
   fun _ _ hσ hT s hs hW =>
    exp_depthMass_lt_height_of_window_depthMass_gt hσ hT s hs hW⟩

end GaloisForLFunctions.DilutionCrystallizationPincer
