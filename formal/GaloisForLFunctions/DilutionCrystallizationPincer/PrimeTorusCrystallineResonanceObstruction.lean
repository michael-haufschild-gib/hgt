import GaloisForLFunctions.DilutionCrystallizationPincer.ArchimedeanDominationOfDilutedVisibility
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold
import GaloisForLFunctions.SquareRootThreshold.KroneckerBohrPrimePhaseRealizationAndExponentialHeightEscape
import GaloisForLFunctions.SquareRootThreshold.ZetaLocalizedFormWindowedVarianceLaw

/-!
# Prime-Torus vs. Crystalline Resonance Obstruction

This module establishes the third leg of the **Dilution–Crystallization–Incommensurability (DCI)
Pincer**: contrasting the rank-1 harmonic support of crystalline off-line configurations against the
infinite-rank Kronecker–Bohr prime-torus support of `ζ`.

1. **Global non-harmonic vanishing for `P`-pair uniform crystals
   (`patternSymbol_crystal_nat_eq_zero_of_not_dvd`, `patternSymbol_crystal_int_eq_zero_of_not_dvd`):**
   For any `P`-pair uniform crystal `(θ, d)` (`d_r = δ` and `P(θ_r − θ_{r'}) ∈ ℤ`), not only do the
   fundamental sub-harmonics `1 ≤ m < P` vanish, but **every** integer mode `m ∈ ℤ` not divisible by
   `P` (`¬ (P : ℤ) ∣ m`) vanishes identically: `D(m) = 0`.
2. **Crystal comb-teeth vs. comb-gaps dichotomy (`offLineLattice_comb_teeth_and_gap_dichotomy`):**
   On a uniform off-line crystal of period `2π/L` (`L > 4w`), the difference test
   `g_v(t) = κ_w(t + v/2) − κ_w(t − v/2)` has:
   - Strictly negative Weil form `4L‖κ_w‖²(1 − cosh(nδL)) < 0` on every harmonic tooth `v = nL`
     (`n ≥ 1`);
   - Purely diagonal, depth-independent positive Weil form `4L‖κ_w‖² > 0` at every lag `v > 2w` in
     the inter-harmonic gaps `|v − nL| > 2w`.
3. **Crystal-gap vs. prime-torus incompatibility (`crystal_gap_prime_torus_incompatibility`):**
   At any lag `v > 2w` lying in a crystal gap (`∀ n ≥ 1, 2w < |v − nL|`), the difference test
   `g_v = twoBump (modScaledBump w 0) v (-1)` (supported in `[-(v/2+w), v/2+w]`) sees zero
   off-diagonal contribution from the off-line crystal (`W_{crystal}(g_v, g_v) = 4L‖κ_w‖²`), while
   on `ζ`, for any prime-torus threshold
   `B < primeOnlyEnvelope g_v ⌊e^{v+2w}⌋₊ − primePowerTailEnvelope g_v ⌊e^{v+2w}⌋₊`, Kronecker
   phase alignment on the prime torus (`loggedPrimes_linearIndependent`) produces a height `ξ ∈ ℝ`
   where `Re Π_{g_v}(ξ) > B` and forces either `Re W_ζ(S_ξ g_v, S_ξ g_v) < 0` or exponential height
   escape.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.DilutionCrystallizationPincer

open Zeta23 _root_.RHTower GaloisForLFunctions.SquareRootThreshold

/-! ### Global non-harmonic mode vanishing for `P`-pair uniform crystals -/

/-- **All non-multiple modes of a `P`-pair uniform crystal vanish (`ℕ` version).** If `d_r = δ` and
`P(θ_r − θ_{r'}) ∈ ℤ`, then for every `m : ℕ` with `¬ (P ∣ m)`, the `m`-th Fourier/lag mode
`patternSymbol ℓ (scaledOffset ℓ θ) d m` is identically zero. -/
theorem patternSymbol_crystal_nat_eq_zero_of_not_dvd {ℓ δ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P)
    (θ d : Fin P → ℝ) (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hunif : ∀ r, d r = δ) (hcr : ∀ r r' : Fin P, ∃ k : ℤ, P * θ r - P * θ r' = k)
    {m : ℕ} (hndvd : ¬ (P ∣ m)) :
    patternSymbol ℓ (scaledOffset ℓ θ) d (m : ℤ) = 0 := by
  let r₀ : Fin P := ⟨0, hP⟩
  rw [patternSymbol_scaledOffset hℓ]
  have hdr : ∀ r, d r = δ := hunif
  simp_rw [hdr, ← Finset.mul_sum]
  have hmod1 : 1 ≤ m % P := by
    have hne : m % P ≠ 0 := fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
    omega
  have hmodP : m % P < P := Nat.mod_lt m hP
  have hpow : ∀ r : Fin P, phasePoint θ r ^ m =
      (phasePoint θ r₀ ^ P) ^ (m / P) * phasePoint θ r ^ (m % P) := by
    intro r
    conv_lhs => rw [← Nat.div_add_mod m P]
    rw [pow_add, pow_mul, phasePoint_pow_eq_of_crystal θ hcr r r₀]
  simp_rw [hpow, ← Finset.mul_sum]
  rw [powerSum_eq_zero_of_pow_eq _ (phasePoint_injective hθ)
    (fun i => phasePoint_pow_eq_of_crystal θ hcr i r₀) hmod1 hmodP, mul_zero, mul_zero]

/-- **All non-multiple modes of a `P`-pair uniform crystal vanish (`ℤ` version).** For every `m : ℤ`
with `¬ ((P : ℤ) ∣ m)`, `patternSymbol ℓ (scaledOffset ℓ θ) d m = 0`. -/
theorem patternSymbol_crystal_int_eq_zero_of_not_dvd {ℓ δ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P)
    (θ d : Fin P → ℝ) (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hunif : ∀ r, d r = δ) (hcr : ∀ r r' : Fin P, ∃ k : ℤ, P * θ r - P * θ r' = k)
    {m : ℤ} (hndvd : ¬ ((P : ℤ) ∣ m)) :
    patternSymbol ℓ (scaledOffset ℓ θ) d m = 0 := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have hndvd_nat : ¬ (P ∣ k) := fun h => hndvd (Int.ofNat_dvd.mpr h)
    exact patternSymbol_crystal_nat_eq_zero_of_not_dvd hℓ hP θ d hθ hunif hcr hndvd_nat
  · have hndvd_nat : ¬ (P ∣ k) := fun h => hndvd (dvd_neg.mpr (Int.ofNat_dvd.mpr h))
    rw [patternSymbol_neg, patternSymbol_crystal_nat_eq_zero_of_not_dvd hℓ hP θ d hθ hunif hcr
      hndvd_nat, map_zero]

/-- **Complete spectral classification of a `P`-pair uniform crystal.** For any `P`-pair uniform
crystal `(θ, d)` of depth `δ`, every mode `m : ℕ` satisfies either:
- `P ∣ m`, in which case `‖D(m)‖ = 2P cosh(δmℓ)` (constructive resonance); or
- `¬ (P ∣ m)`, in which case `D(m) = 0` (destructive cancellation). -/
theorem patternSymbol_crystal_dichotomy {ℓ δ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P)
    (θ d : Fin P → ℝ) (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    (hunif : ∀ r, d r = δ) (hcr : ∀ r r' : Fin P, ∃ k : ℤ, P * θ r - P * θ r' = k) (m : ℕ) :
    (P ∣ m ∧ ‖patternSymbol ℓ (scaledOffset ℓ θ) d (m : ℤ)‖ = 2 * P * Real.cosh (δ * (m * ℓ))) ∨
      (¬ (P ∣ m) ∧ patternSymbol ℓ (scaledOffset ℓ θ) d (m : ℤ) = 0) := by
  by_cases hdvd : P ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    refine Or.inl ⟨⟨k, rfl⟩, ?_⟩
    rw [mul_comm P k]
    exact norm_patternSymbol_crystal_mul_period hℓ hP θ d hunif hcr k
  · exact Or.inr ⟨hdvd, patternSymbol_crystal_nat_eq_zero_of_not_dvd hℓ hP θ d hθ hunif hcr hdvd⟩

/-! ### Comb-teeth vs. comb-gaps dichotomy and prime-torus incompatibility -/

/-- **Comb-teeth vs. comb-gaps dichotomy for an off-line crystal.** For `L > 4w`, the difference
test family `g_v = twoBump (modScaledBump w 0) v (-1)` on `offLineLatticeConfig hL hδ hδ'` is:
1. Nonnegative throughout the sub-Nyquist interval `0 ≤ v ≤ L − 2w`;
2. Strictly negative with value `4L‖κ_w‖²(1 − cosh(nδL)) < 0` at every harmonic tooth `v = nL`
   (`n ≥ 1`);
3. Depth-independently constant with value `4L‖κ_w‖² > 0` at every lag `v > 2w` in the gaps
   `|v − nL| > 2w`. -/
theorem offLineLattice_comb_teeth_and_gap_dichotomy {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) (hwL : 4 * w < L) :
    (∀ v : ℝ, 0 ≤ v → v ≤ L - 2 * w →
      0 ≤ ((offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re) ∧
    (∀ n : ℕ, 1 ≤ n →
      (offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) (n * L) (-1))
        (twoBump (modScaledBump w 0) (n * L) (-1)) =
        ((4 * L * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) * (1 - Real.cosh (n * δ * L)) : ℝ) : ℂ) ∧
      ((offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) (n * L) (-1))
        (twoBump (modScaledBump w 0) (n * L) (-1))).re < 0) ∧
    (∀ v : ℝ, 2 * w < v → (∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * L|) →
      (offLineLatticeConfig hL hδ hδ').W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)) =
        ((4 * L * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ)) :=
  ⟨fun _ hv0 hv => re_W_offLineLattice_lag_nonneg_of_le hL hδ hδ' hw hv0 hv,
   fun _ hn => ⟨W_offLineLattice_lag_nat_mul hL hδ hδ' hw hwL hn,
     re_W_offLineLattice_lag_nat_mul_neg hL hδ hδ' hw hwL hn⟩,
   fun _ hv hgap => W_offLineLattice_lag_eq_of_gap hL hδ hδ' hw hwL hv hgap⟩

/-- **Crystal-Gap vs. Prime-Torus Incompatibility Theorem.** Let `v > 2w` lie in any gap of the
harmonic crystal lattice `nL` (`∀ n ≥ 1, 2w < |v − nL|`, `4w < L`), and set
`g_v = twoBump (modScaledBump w 0) v (-1)` (supported in `[-(v/2+w), v/2+w]`). Then:
1. On the off-line crystal `offLineLatticeConfig hL hδ hδ'`, `g_v` sees zero off-diagonal response:
   `W_{crystal}(g_v, g_v) = 4L ∫ ‖κ_w‖² > 0`;
2. On `ζ`, for every threshold
   `B < primeOnlyEnvelope g_v ⌊e^{2(v/2+w)}⌋₊ − primePowerTailEnvelope g_v ⌊e^{2(v/2+w)}⌋₊`,
   Kronecker alignment on the prime torus produces a height `ξ ∈ ℝ` where
   `Re Π_{g_v}(ξ) > B` and either `Re W_ζ(S_ξ g_v, S_ξ g_v) < 0` or `ξ` escapes exponentially. -/
theorem crystal_gap_prime_torus_incompatibility {L δ C B : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C)
    {w : ℝ} (hw : 0 < w) (hwL : 4 * w < L) {v : ℝ} (hv : 2 * w < v)
    (hgap : ∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * L|)
    (hB : B < primeOnlyEnvelope (twoBump (modScaledBump w 0) v (-1)) ⌊Real.exp (2 * (v / 2 + w))⌋₊ -
      primePowerTailEnvelope (twoBump (modScaledBump w 0) v (-1)) ⌊Real.exp (2 * (v / 2 + w))⌋₊) :
    let g := twoBump (modScaledBump w 0) v (-1)
    let a := v / 2 + w
    (offLineLatticeConfig hL hδ hδ').W g g =
      ((4 * L * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) ∧
    0 < ((offLineLatticeConfig hL hδ hδ').W g g).re ∧
    ∃ ξ : ℝ, B < (primePolynomial g ⌊Real.exp (2 * a)⌋₊ ξ).re ∧
      ((zetaZeroConfig.W (heightShift ξ g) (heightShift ξ g)).re < 0 ∨
        B - 2 * Real.exp a * (∫ u, ‖g u‖) ^ 2 -
          (4 * ((∫ u, ‖g u‖) + ∫ u, ‖deriv (deriv g) u‖)) ^ 2 * (1 / 2 + π * C) <
          (∫ t, ‖g t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|)) := by
  set g := twoBump (modScaledBump w 0) v (-1)
  set a := v / 2 + w
  have hv0 : 0 ≤ v := by linarith
  have hgd : ContDiff ℝ 2 g := contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]
  have hgs : tsupport g ⊆ Icc (-a) a := tsupport_twoBump_modScaledBump_subset hw hv0
  have hWgap := W_offLineLattice_lag_eq_of_gap hL hδ hδ' hw hwL hv hgap
  have hWpos : 0 < ((offLineLatticeConfig hL hδ hδ').W g g).re := by
    rw [hWgap, Complex.ofReal_re]
    have hK := integral_norm_sq_modScaledBump_pos hw
    positivity
  exact ⟨hWgap, hWpos, exists_re_W_neg_or_height_escape hC0 hC hgd hgs hB⟩

end GaloisForLFunctions.DilutionCrystallizationPincer
