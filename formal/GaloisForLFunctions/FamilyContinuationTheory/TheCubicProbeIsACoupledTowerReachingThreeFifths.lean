import GaloisForLFunctions.FamilyContinuationTheory.GrossencharacterLFunctionsHaveZerosInTheRightHalfStrip
import GaloisForLFunctions.FamilyContinuationTheory.TheFamilyStepReadsTheZerosOfTheLFunctions
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalOfAHeckeKernelIsASumOverSquarefreeIdeals

/-!
# The Cubic Probe Is a Coupled Grossencharacter Tower Reaching Three-Fifths

This module establishes the sharp reach of the cubic-theta probe over `K = ℚ(ω)` (`O = ℤ[ω]`)
together with its coupled Grossencharacter tower and universal classification across probe
variants:

1. **Sharp uncoupled reach `2/3` with fixed cutoff `N₀ = 160`:**
   Because `continuedProbeCorrection 𝔪 η S` agrees with `probeCorrection 𝔪 η S` on `Re s ≥ 7/8`,
   is holomorphic and bounded on `Re s ≥ 2`, and is everywhere nonvanishing on the closed
   half-plane `Re s ≥ 2/3`, reciprocal-signal estimates for the cubic probe imply
   `HeckeHalfPlane K σ₀` and `zetaZeroAbscissa ≤ σ₀` for every `σ₀ ∈ [2/3, 1)` at the fixed prime
   cutoff `N₀ = 160`.

2. **Exact zero-transfer law below `2/3` and conditional `7/12` reach:**
   At any zero `ρ ≠ 1` of `L(s, η)` in `1/2 < Re ρ < 1`, direct and comparison signal bounds for
   the probe kernel with exponents strictly below `Re ρ` force `L(6ρ − 3, ψ₆ χ_{𝔣(η⁶)}) = 0`.
   Under zero-freeness of weight-`1` sextic Grossencharacter `L`-functions on `Re w > 1/2`, the
   probe estimates yield `HeckeHalfPlane K σ₀` and `zetaZeroAbscissa ≤ σ₀` down to `7/12`.

3. **Exact signal Möbius inversion and unconditional `Z^{2/3}` squarefree norm barrier:**
   On `Z > 0`, the uncoupled residual signal (whose correction `fullResidualCorrection` is
   holomorphic and nonvanishing on all of `Re s > 1/2`) equals the infinite convolution of the
   probe signal over finite sets `T` of primes outside `S` at shifted scales `Z / N(T)⁶` weighted
   by `μ_{ψ₆ η⁶}(T) · N(T)³`. For every `(𝔪, η, S)` and every exponent `a : ℝ`, the finite sum of
   `‖μ_{ψ₆ η⁶}(T) · N(T)³‖ · (Z / N(T)⁶)^a` over `N(T)⁶ ≤ Z` exceeds `c · Z^{2/3}` (`c > 0`) for
   all sufficiently large `Z`.

4. **Coupled Grossencharacter tower reaching `max(σ₀, 3/5)` unconditionally:**
   Feeding the level-`k` Grossencharacter coefficients `ψ₆(v)^k ψ(v)` (`k ≥ 1`) into the cubic
   probe produces a continued correction `continuedTowerCorrection 𝔪 ψ k S` that is holomorphic on
   `Re s > 1/2`, uniformly bounded on `Re s ≥ 2`, agrees with the `S`-deleted principal row on
   `Re s > 1`, and vanishes on `Re s > 1/2` if and only if `L(6s − 3, ψ₆^{6k + 1} χ_{𝔣(ψ⁶)}) = 0`.
   Iterating across the tower weights `k₀ = 0`, `k_{r+1} = 6 k_r + 1` contracts the threshold
   map `θ ↦ (3 + θ)/6` from the unconditional `Re w ≥ 1` seed to its unique fixed point `3/5`,
   yielding `HeckeHalfPlane K (max σ₀ (3/5))` and `zetaZeroAbscissa ≤ max σ₀ (3/5)` for every
   `σ₀ ∈ [1/2, 1)`.

5. **Universal classification across contour shears, `6r`-periodic Gauss pairings, and cubings:**
   - The local sextic resonance `κ_v⁶ N(v)^{4 − 6x − 6z}` is invariant under all complex contour
     shears `(x, z) ↦ (x − δ, z + δ)`, and its prime-norm series diverges whenever
     `Re(x + z) ≤ 5/6` (`Re x ≤ 2/3` at `z = 1/6`).
   - Every nontrivial cubic character `φ` (`φ³ = 1`) has `φ(−1) = 1` and Gauss pairing sign `+1`
     instead of Möbius `−1`, while any twist `φ` whose product with a nontrivial cubic character
     `χ` has order `2` must have exact order `6`.
   - Every `6r`-periodic Gauss pairing (`r ≥ 1`) has uncoupled boundary `2/3` and coupled fixed
     point `(4r − 1)/(6r − 1) ≥ 3/5` (equal to `3/5` iff `r = 1`), while multi-theta cubing gives
     uncoupled boundary `5/6 > 2/3` and coupled fixed point `3/4 > 3/5`.
-/

noncomputable section

open Complex Filter Topology Set NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open _root_.RHTower EisensteinNorm

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### 1. Sharp uncoupled reach `2/3` with fixed cutoff `N₀ = 160` -/

/-- On the signal line `Re s = 2`, the probe kernel with `probeCorrection` has the exact same
Mellin signal as the continued kernel with `continuedProbeCorrection` whenever `S` contains all
primes of norm `≤ 160`. -/
theorem signal_probeCorrection_eq_continuedProbeCorrection (𝔪 : Modulus K)
    (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ) :
    signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) * probeCorrection 𝔪 η S s /
      heckeLFunction 𝔪 η s) 2 =
    signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s /
      heckeLFunction 𝔪 η s) 2 :=
  signal_congr_line fun s hs => by
    rw [continuedProbeCorrection_eq_probeCorrection 𝔪 η S hS (by rw [hs]; norm_num)]

/-- **Sharp uncoupled Hecke half-plane down to `2/3` with fixed cutoff `N₀ = 160`.** For any
`σ₀ ∈ [2/3, 1)` and any finite set `S` containing the primes of `O` of norm `≤ 160`, two-sided
signal estimates for the cubic probe down to `σ₀` imply `HeckeHalfPlane K σ₀`. -/
theorem heckeHalfPlane_of_probe_estimates_down_to_two_thirds {σ₀ : ℝ} (h23 : 2 / 3 ≤ σ₀)
    (hσ₀ : σ₀ < 1) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
                probeCorrection η.1 η.2 S s / heckeLFunction η.1 η.2 s) 2 Z‖ ≤
                  C * Z ^ a₂)) :
    HeckeHalfPlane K σ₀ := by
  have hsub : {s : ℂ | σ₀ < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs => by
    simp only [mem_setOf_eq] at hs ⊢; linarith
  refine heckeHalfPlane_of_family_reciprocal_signal K hσ₀ c
    (fun η => continuedProbeCorrection η.1 η.2 S)
    (fun η => (differentiableOn_continuedProbeCorrection η.1 η.2 S).mono hsub)
    (fun η s hs => continuedProbeCorrection_ne_zero_of_two_thirds_le η.1 η.2 S
      (h23.trans hs.le))
    (fun η => exists_norm_continuedProbeCorrection_le η.1 η.2 S)
    fun β hβ hβ1 hfree => ?_
  obtain ⟨a₁, a₂, ha₁, ha₂, hη⟩ := hstep β hβ hβ1 hfree
  refine ⟨a₁, a₂, ha₁, ha₂, fun η => ?_⟩
  obtain ⟨J, C, Z₀, hZ₀, h1, h2⟩ := hη η
  refine ⟨J, C, Z₀, hZ₀, h1, fun Z hZ => ?_⟩
  rw [← signal_probeCorrection_eq_continuedProbeCorrection η.1 η.2 S hS c]
  exact h2 Z hZ

/-- **Sharp uncoupled Riemann zeta abscissa bound down to `2/3` with fixed cutoff `N₀ = 160`.** -/
theorem zetaZeroAbscissa_le_of_probe_estimates_down_to_two_thirds {σ₀ : ℝ} (h23 : 2 / 3 ≤ σ₀)
    (hσ₀ : σ₀ < 1) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
                probeCorrection η.1 η.2 S s / heckeLFunction η.1 η.2 s) 2 Z‖ ≤
                  C * Z ^ a₂)) :
    zetaZeroAbscissa ≤ σ₀ :=
  zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic
    (heckeHalfPlane_of_probe_estimates_down_to_two_thirds h23 hσ₀ S hS c hstep)

/-! ### 2. Exact zero-transfer law below `2/3` and conditional `7/12` reach -/

/-- Helper: combine direct and comparison signal bounds into a single signal bound at `max a₁ a₂`. -/
private theorem norm_signal_le_of_direct_and_comp {G : ℂ → ℂ} {a₁ a₂ C Z₀ : ℝ} (J : ℝ → ℂ)
    (hZ₀ : 1 ≤ Z₀) (h1 : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁)
    (h2 : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - signal G 2 Z‖ ≤ C * Z ^ a₂)
    {b : ℝ} (hb₁ : a₁ ≤ b) (hb₂ : a₂ ≤ b) {Z : ℝ} (hZ : Z₀ ≤ Z) :
    ‖signal G 2 Z‖ ≤ 2 * |C| * Z ^ b := by
  have hZ1 : 1 ≤ Z := hZ₀.trans hZ
  have hp1 : Z ^ a₁ ≤ Z ^ b := Real.rpow_le_rpow_of_exponent_le hZ1 hb₁
  have hp2 : Z ^ a₂ ≤ Z ^ b := Real.rpow_le_rpow_of_exponent_le hZ1 hb₂
  have hn1 : 0 ≤ Z ^ a₁ := Real.rpow_nonneg (by linarith) _
  have hn2 : 0 ≤ Z ^ a₂ := Real.rpow_nonneg (by linarith) _
  calc ‖signal G 2 Z‖ = ‖J Z - (J Z - signal G 2 Z)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖J Z‖ + ‖J Z - signal G 2 Z‖ := norm_sub_le _ _
    _ ≤ C * Z ^ a₁ + C * Z ^ a₂ := add_le_add (h1 Z hZ) (h2 Z hZ)
    _ ≤ |C| * Z ^ b + |C| * Z ^ b :=
        add_le_add
          ((mul_le_mul_of_nonneg_right (le_abs_self C) hn1).trans
            (mul_le_mul_of_nonneg_left hp1 (abs_nonneg C)))
          ((mul_le_mul_of_nonneg_right (le_abs_self C) hn2).trans
            (mul_le_mul_of_nonneg_left hp2 (abs_nonneg C)))
    _ = 2 * |C| * Z ^ b := by ring

/-- **Exact zero-transfer law below `2/3`.** If `heckeLFunction 𝔪 η ρ = 0` at `ρ ≠ 1` with
`1/2 < Re ρ`, and the cubic probe signal for `(𝔪, η)` admits direct and comparison bounds with
exponents `a₁, a₂ < min (Re ρ) 1`, then `grossenLFunction 𝔪 (η ^ 6) 1 (6 * ρ - 3) = 0`. -/
theorem grossenLFunction_zero_of_hecke_zero_and_probe_estimates (𝔪 : Modulus K)
    (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ)
    {ρ : ℂ} (hρ_half : 1 / 2 < ρ.re) (hρ1 : ρ ≠ 1) (hzero : heckeLFunction 𝔪 η ρ = 0)
    {a₁ a₂ C Z₀ : ℝ} (J : ℝ → ℂ) (ha₁ : a₁ < ρ.re) (ha₂ : a₂ < ρ.re)
    (ha₁_one : a₁ < 1) (ha₂_one : a₂ < 1) (hZ₀ : 1 ≤ Z₀)
    (hJ1 : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁)
    (hJ2 : ∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
      probeCorrection 𝔪 η S s / heckeLFunction 𝔪 η s) 2 Z‖ ≤ C * Z ^ a₂) :
    grossenLFunction 𝔪 (η ^ 6) 1 (6 * ρ - 3) = 0 := by
  set b : ℝ := max (1 / 2) (max a₁ a₂)
  have hb_half : 1 / 2 ≤ b := le_max_left _ _
  have hb_lt_ρ : b < ρ.re := max_lt hρ_half (max_lt ha₁ ha₂)
  have hb_lt_one : b < 1 := max_lt (by norm_num) (max_lt ha₁_one ha₂_one)
  obtain ⟨M, hM⟩ := exists_norm_continuedProbeCorrection_le 𝔪 η S
  have hH_open : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const continuous_re
  have hG : IsSignalKernel (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
      continuedProbeCorrection 𝔪 η S s / heckeLFunction 𝔪 η s) :=
    isSignalKernel_gauss_mul_div_of_bounded (Real.exp_pos _)
      (fun s hs => differentiableAt_heckeLFunction 𝔪 η (ne_one_of_one_lt_re hs))
      (fun s hs => heckeLFunction_ne_zero_of_one_lt_re 𝔪 η hs)
      (fun s hs => by
        rw [heckeLFunction_eq_heckeL 𝔪 η (by linarith : (1 : ℝ) < s.re)]
        exact exp_neg_le_norm_heckeL 𝔪 η hs)
      (fun s hs => (differentiableOn_continuedProbeCorrection 𝔪 η S).differentiableAt
        (hH_open.mem_nhds (by linarith : (1 / 2 : ℝ) < s.re)))
      hM c
  have hsig_le : ∀ Z : ℝ, Z₀ ≤ Z →
      ‖signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
        continuedProbeCorrection 𝔪 η S s / heckeLFunction 𝔪 η s) 2 Z‖ ≤ 2 * |C| * Z ^ b := by
    intro Z hZ
    rw [← signal_probeCorrection_eq_continuedProbeCorrection 𝔪 η S hS c]
    exact norm_signal_le_of_direct_and_comp J hZ₀ hJ1 hJ2
      ((le_max_left a₁ a₂).trans (le_max_right _ _))
      ((le_max_right a₁ a₂).trans (le_max_right _ _)) hZ
  obtain ⟨F, hF, hFG⟩ :=
    exists_differentiableOn_eq_of_signal_le hG (by linarith : b < 2) (by linarith : 0 < Z₀) hsig_le
  rw [max_eq_right hb_lt_one.le] at hFG
  have hU_open : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const continuous_re
  have hE_diff : DifferentiableOn ℂ
      (fun s : ℂ => Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s *
        (if η = 1 then s - 1 else 1)) {s : ℂ | b < s.re} := by
    refine (((by fun_prop : Differentiable ℂ fun s : ℂ =>
        Complex.exp ((s - c) ^ 2)).differentiableOn).mul
      ((differentiableOn_continuedProbeCorrection 𝔪 η S).mono fun s hs =>
        lt_of_le_of_lt hb_half hs)).mul ?_
    split_ifs
    · exact (differentiable_id.sub_const 1).differentiableOn
    · exact differentiableOn_const 1
  have h2_mem : ((2 : ℝ) : ℂ) ∈ {s : ℂ | b < s.re} := by
    show b < ((2 : ℝ) : ℂ).re; rw [ofReal_re]; linarith
  have hev : (fun s : ℂ => F s * heckeZeroFunction 𝔪 η s) =ᶠ[𝓝 ((2 : ℝ) : ℂ)]
      fun s : ℂ => Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s *
        (if η = 1 then s - 1 else 1) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by show (1 : ℝ) < ((2 : ℝ) : ℂ).re; rw [ofReal_re]; norm_num)] with s hs
    have hL0 := heckeLFunction_ne_zero_of_one_lt_re 𝔪 η hs
    rw [hFG s hs]
    unfold heckeZeroFunction
    split_ifs
    · rw [heckePoleCleared_eq 𝔪 η (ne_one_of_one_lt_re hs)]
      field_simp
    · field_simp
  have heq := ((hF.mul (differentiable_heckeZeroFunction 𝔪 η).differentiableOn).analyticOnNhd
    hU_open).eqOn_of_preconnected_of_eventuallyEq (hE_diff.analyticOnNhd hU_open)
    (convex_halfSpace_re_gt b).isPreconnected h2_mem hev hb_lt_ρ
  have hZ0 : heckeZeroFunction 𝔪 η ρ = 0 := by
    by_contra hne
    exact heckeLFunction_ne_zero_of_heckeZeroFunction_ne_zero 𝔪 hρ1 hne hzero
  simp only [Pi.mul_apply, hZ0, mul_zero] at heq
  have hfac_ne : (if η = 1 then ρ - 1 else 1) ≠ 0 := by
    split_ifs
    · exact sub_ne_zero.mpr hρ1
    · exact one_ne_zero
  have hcont0 : continuedProbeCorrection 𝔪 η S ρ = 0 := by
    rcases mul_eq_zero.mp heq.symm with h1 | h2
    · exact (mul_eq_zero.mp h1).resolve_left (Complex.exp_ne_zero _)
    · exact absurd h2 hfac_ne
  exact (continuedProbeCorrection_eq_zero_iff 𝔪 η S hρ_half).mp hcont0

/-- **Conditional `7/12` reach under weight-`1` Grossencharacter GRH.** If weight-`1` sextic
Grossencharacter `L`-functions have no zeros in `Re w > 1/2`, then probe estimates down to any
`σ₀ ∈ [7/12, 1)` yield `HeckeHalfPlane K σ₀` and `zetaZeroAbscissa ≤ σ₀`. -/
theorem zetaZeroAbscissa_le_of_probe_estimates_and_sextic_grh {σ₀ : ℝ} (h712 : 7 / 12 ≤ σ₀)
    (hσ₀ : σ₀ < 1) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ)
    (hgrh : ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (w : ℂ),
      1 / 2 < w.re → grossenLFunction 𝔪 ψ 1 w ≠ 0)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
                probeCorrection η.1 η.2 S s / heckeLFunction η.1 η.2 s) 2 Z‖ ≤
                  C * Z ^ a₂)) :
    HeckeHalfPlane K σ₀ ∧ zetaZeroAbscissa ≤ σ₀ := by
  have hsub : {s : ℂ | σ₀ < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs => by
    simp only [mem_setOf_eq] at hs ⊢; linarith
  have hHP : HeckeHalfPlane K σ₀ := by
    refine heckeHalfPlane_of_family_reciprocal_signal K hσ₀ c
      (fun η => continuedProbeCorrection η.1 η.2 S)
      (fun η => (differentiableOn_continuedProbeCorrection η.1 η.2 S).mono hsub)
      (fun η s hs => by
        have hs' : σ₀ < s.re := hs
        rw [ne_eq, continuedProbeCorrection_eq_zero_iff η.1 η.2 S (by linarith)]
        refine hgrh η.1 (η.2 ^ 6) (6 * s - 3) ?_
        simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
        linarith)
      (fun η => exists_norm_continuedProbeCorrection_le η.1 η.2 S)
      fun β hβ hβ1 hfree => ?_
    obtain ⟨a₁, a₂, ha₁, ha₂, hη⟩ := hstep β hβ hβ1 hfree
    refine ⟨a₁, a₂, ha₁, ha₂, fun η => ?_⟩
    obtain ⟨J, C, Z₀, hZ₀, h1, h2⟩ := hη η
    refine ⟨J, C, Z₀, hZ₀, h1, fun Z hZ => ?_⟩
    rw [← signal_probeCorrection_eq_continuedProbeCorrection η.1 η.2 S hS c]
    exact h2 Z hZ
  exact ⟨hHP, zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic hHP⟩

/-! ### 3. Exact signal Möbius inversion and unconditional `Z^{2/3}` squarefree norm barrier -/

/-- Squarefree Grossencharacter Möbius coefficient `(−1)^{|T|} ∏_{v ∈ T} ψ₆(v)^k ψ(v)` on a finite
subset `T` of primes outside `S`. -/
def deletedSquarefreeCoeff (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {S : Finset (HeightOneSpectrum O)} (T : Finset {v : HeightOneSpectrum O // v ∉ S}) : ℂ :=
  ∏ u ∈ T, -(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal)

/-- Absolute norm `∏_{v ∈ T} N(v)` of a squarefree product of primes outside `S`. -/
def deletedSquarefreeNorm {S : Finset (HeightOneSpectrum O)}
    (T : Finset {v : HeightOneSpectrum O // v ∉ S}) : ℕ :=
  ∏ u ∈ T, u.1.asIdeal.absNorm

theorem deletedSquarefreeNorm_pos {S : Finset (HeightOneSpectrum O)}
    (T : Finset {v : HeightOneSpectrum O // v ∉ S}) :
    0 < deletedSquarefreeNorm T :=
  Finset.prod_pos fun u _ =>
    lt_of_lt_of_le zero_lt_two (ArtinMertens.two_le_absNorm_of_isPrime u.1.isPrime u.1.ne_bot)

theorem norm_deletedSquarefreeCoeff_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {S : Finset (HeightOneSpectrum O)} (T : Finset {v : HeightOneSpectrum O // v ∉ S}) :
    ‖deletedSquarefreeCoeff 𝔪 ψ k T‖ ≤ 1 := by
  unfold deletedSquarefreeCoeff
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun u _ => ?_
  rw [norm_neg, norm_mul, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one _))
    (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _)

private theorem norm_heckeValue_prime_of_not_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {w : HeightOneSpectrum O} (hv : ¬ (𝔪.fin ≤ w.asIdeal)) :
    ‖heckeValue 𝔪 ψ w.asIdeal‖ = 1 := by
  have hm : idealUnit w.ne_bot ∈ idealGroup 𝔪 := by
    rw [idealUnit_mem_idealGroup_iff]
    by_contra hnot
    exact hv (le_sup_right.trans (w.isMaximal.eq_of_le hnot le_sup_left).symm.le)
  rw [heckeValue_of_mem 𝔪 ψ w.ne_bot hm]
  exact norm_char_eq_one ψ _

/-- On primes coprime to `𝔪.fin`, `‖deletedSquarefreeCoeff 𝔪 ψ k T‖ = 1`. -/
theorem norm_deletedSquarefreeCoeff_eq_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {S : Finset (HeightOneSpectrum O)} {T : Finset {v : HeightOneSpectrum O // v ∉ S}}
    (hcop : ∀ u ∈ T, ¬ (𝔪.fin ≤ u.1.asIdeal)) :
    ‖deletedSquarefreeCoeff 𝔪 ψ k T‖ = 1 := by
  unfold deletedSquarefreeCoeff
  rw [norm_prod]
  refine Finset.prod_eq_one fun u hu => ?_
  rw [norm_neg, norm_mul, norm_pow, norm_idealPsiSix_prime, one_pow, one_mul,
    norm_heckeValue_prime_of_not_le 𝔪 ψ (hcop u hu)]

private theorem prod_neg_deletedGrossenTerm (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (w : ℂ) {S : Finset (HeightOneSpectrum O)}
    (T : Finset {v : HeightOneSpectrum O // v ∉ S}) :
    (∏ u ∈ T, -(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w))) =
      deletedSquarefreeCoeff 𝔪 ψ k T * ((deletedSquarefreeNorm T : ℝ) : ℂ) ^ (-w) := by
  have key : (∏ u ∈ T, -(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
      (primeNorm u.1 : ℂ) ^ (-w))) =
      (∏ u ∈ T, -(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal)) *
        ((∏ u ∈ T, u.1.asIdeal.absNorm : ℕ) : ℂ) ^ (-w) := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert u T hu ih =>
      rw [Finset.prod_insert hu, Finset.prod_insert hu, Finset.prod_insert hu, ih,
        Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      unfold primeNorm
      rw [Complex.ofReal_natCast]
      ring
  unfold deletedSquarefreeCoeff deletedSquarefreeNorm
  rw [key, Complex.ofReal_natCast]

/-- **Squarefree Möbius series for `(grossenEulerProductModS 𝔪 ψ k S w)⁻¹` on `Re w > 1`.** -/
theorem hasSum_inv_grossenEulerProductModS (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun T : Finset {v : HeightOneSpectrum O // v ∉ S} =>
      deletedSquarefreeCoeff 𝔪 ψ k T * ((deletedSquarefreeNorm T : ℝ) : ℂ) ^ (-w))
      (grossenEulerProductModS 𝔪 ψ k S w)⁻¹ := by
  have hmaj : Summable fun u : {v : HeightOneSpectrum O // v ∉ S} =>
      (primeNorm u.1) ^ (-w.re) :=
    (numberField_summable_finitePlace_absNorm_rpow (K := K) hw).subtype _
  have hbd : ∀ u : {v : HeightOneSpectrum O // v ∉ S},
      ‖idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w)‖ ≤ (primeNorm u.1) ^ (-w.re) := by
    intro u
    have hu1 : 1 ≤ primeNorm u.1 := by linarith [two_le_primeNorm u.1]
    have hc : ‖idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one _))
        (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans
      (norm_ofReal_cpow_le hu1 (by rw [neg_re]))
  have hsum_term : Summable fun u : {v : HeightOneSpectrum O // v ∉ S} =>
      ‖-(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w))‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun u => ?_) hmaj
    rw [norm_neg]
    exact hbd u
  have hS_prod : Summable fun T : Finset {v : HeightOneSpectrum O // v ∉ S} =>
      ∏ u ∈ T, -(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w)) :=
    summable_finsetProd_of_summable_norm hsum_term
  have hP1 := hasProd_one_add_of_hasSum_prod hS_prod.hasSum
  have hmul_inv : Multipliable fun u : {v : HeightOneSpectrum O // v ∉ S} =>
      (1 - idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w))⁻¹ := by
    refine multipliable_one_sub_inv
      (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hbd) fun u => (hbd u).trans ?_
    have hu2 := two_le_primeNorm u.1
    calc (primeNorm u.1) ^ (-w.re) ≤ (primeNorm u.1) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (primeNorm u.1)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hP2 : HasProd (fun u : {v : HeightOneSpectrum O // v ∉ S} =>
      (1 - idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w))⁻¹) (grossenEulerProductModS 𝔪 ψ k S w) :=
    hmul_inv.hasProd
  have hprod_one : HasProd (fun _ : {v : HeightOneSpectrum O // v ∉ S} => (1 : ℂ))
      ((∑' T : Finset {v : HeightOneSpectrum O // v ∉ S},
          ∏ u ∈ T, -(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
            (primeNorm u.1 : ℂ) ^ (-w))) *
        grossenEulerProductModS 𝔪 ψ k S w) := by
    refine (hP1.mul hP2).congr fun s => Finset.prod_congr rfl fun u _ => ?_
    have hlt : ‖idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w)‖ < 1 := by
      have hu2 := two_le_primeNorm u.1
      exact (hbd u).trans_lt (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith))
    have hne : 1 - idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
        (primeNorm u.1 : ℂ) ^ (-w) ≠ 0 := by
      intro h0
      have htri := norm_sub_norm_le (1 : ℂ)
        (idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal * (primeNorm u.1 : ℂ) ^ (-w))
      rw [h0, norm_zero, norm_one] at htri
      linarith
    dsimp only
    rw [← sub_eq_add_neg]
    exact mul_inv_cancel₀ hne
  have hinv : (grossenEulerProductModS 𝔪 ψ k S w)⁻¹ =
      ∑' T : Finset {v : HeightOneSpectrum O // v ∉ S},
        ∏ u ∈ T, -(idealPsiSix u.1.asIdeal ^ k * heckeValue 𝔪 ψ u.1.asIdeal *
          (primeNorm u.1 : ℂ) ^ (-w)) :=
    (eq_inv_of_mul_eq_one_left (hprod_one.unique hasProd_one)).symm
  have h := hS_prod.hasSum
  rw [← hinv] at h
  simpa only [prod_neg_deletedGrossenTerm] using h

private theorem natCast_pow_six_cpow_neg (n : ℕ) (s : ℂ) :
    (((n ^ 6 : ℕ) : ℝ) : ℂ) ^ (-s) = ((n : ℝ) : ℂ) ^ (-(6 * s)) := by
  have hpow : ∀ m : ℕ, ((n ^ m : ℕ) : ℂ) ^ (-s) = ((n : ℂ) ^ (-s)) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]
  rw [Complex.ofReal_natCast, Complex.ofReal_natCast, hpow 6, ← Complex.cpow_nat_mul]
  ring_nf

/-- **Exact signal Möbius inversion identity.** Clearing `L_{𝔪}^S(6s − 3, ψ₆ η⁶)` to pass from the
cubic probe signal to the cutoff-free residual signal (whose correction `fullResidualCorrection`
is holomorphic and nonvanishing on all of `Re s > 1/2`) expresses the residual signal at `Z > 0` as
the infinite squarefree sixth-power Möbius sum of the probe signal at scales `Z / N(T)⁶`. -/
theorem signal_residualKernel_eq_tsum_probeKernel (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ) {Z : ℝ}
    (hZ : 0 < Z) :
    signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
      fullResidualCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s /
        heckeLFunction 𝔪 η s) 2 Z =
      ∑' T : Finset {v : HeightOneSpectrum O // v ∉ S},
        deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T * (deletedSquarefreeNorm T : ℂ) ^ 3 *
          signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
            probeCorrection 𝔪 η S s / heckeLFunction 𝔪 η s) 2
              (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) := by
  haveI : Countable (HeightOneSpectrum O) := _root_.RHTower.deningerHeightOneSpectrum_countable K
  obtain ⟨M, hM⟩ := exists_norm_continuedProbeCorrection_le 𝔪 η S
  have hH_open : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const continuous_re
  have hE_kern : IsSignalKernel (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
      continuedProbeCorrection 𝔪 η S s / heckeLFunction 𝔪 η s) :=
    isSignalKernel_gauss_mul_div_of_bounded (Real.exp_pos _)
      (fun s hs => differentiableAt_heckeLFunction 𝔪 η (ne_one_of_one_lt_re hs))
      (fun s hs => heckeLFunction_ne_zero_of_one_lt_re 𝔪 η hs)
      (fun s hs => by
        rw [heckeLFunction_eq_heckeL 𝔪 η (by linarith : (1 : ℝ) < s.re)]
        exact exp_neg_le_norm_heckeL 𝔪 η hs)
      (fun s hs => (differentiableOn_continuedProbeCorrection 𝔪 η S).differentiableAt
        (hH_open.mem_nhds (by linarith : (1 / 2 : ℝ) < s.re)))
      hM c
  obtain ⟨C₀, hC₀⟩ := hE_kern.decay 2
  have hEc : Continuous fun y : ℝ =>
      (fun s : ℂ => Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s /
        heckeLFunction 𝔪 η s) (linePoint y) :=
    continuous_iff_continuousAt.mpr fun y =>
      (hE_kern.differentiableAt (linePoint y)
        (by rw [linePoint_re]; norm_num)).continuousAt.comp continuous_linePoint.continuousAt
  have hEb : ∀ y : ℝ,
      ‖(fun s : ℂ => Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s /
        heckeLFunction 𝔪 η s) (linePoint y)‖ ≤ C₀ * (1 + y ^ 2)⁻¹ := by
    intro y
    rw [← div_eq_mul_inv]
    have h := hC₀ (linePoint y) (by rw [linePoint_re]) (by rw [linePoint_re])
    rwa [linePoint_im, neg_sq] at h
  have hr : ∀ T : Finset {v : HeightOneSpectrum O // v ∉ S},
      (0 : ℝ) < ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) :=
    fun T => Nat.cast_pos.mpr (pow_pos (deletedSquarefreeNorm_pos T) 6)
  have hN9 : Summable fun u : {v : HeightOneSpectrum O // v ∉ S} =>
      ((u.1.asIdeal.absNorm : ℝ) ^ 9)⁻¹ := by
    refine ((numberField_summable_finitePlace_absNorm_rpow (K := K)
      (by norm_num : (1 : ℝ) < 9)).subtype _).congr fun u => ?_
    dsimp only [Function.comp_def]
    rw [show (-9 : ℝ) = -((9 : ℕ) : ℝ) by norm_num, Real.rpow_neg (Nat.cast_nonneg _),
      Real.rpow_natCast]
  have hprod9 : Summable fun T : Finset {v : HeightOneSpectrum O // v ∉ S} =>
      ∏ u ∈ T, ((u.1.asIdeal.absNorm : ℝ) ^ 9)⁻¹ :=
    summable_finsetProd_of_summable_nonneg (fun _ => by positivity) hN9
  have ha : Summable fun T : Finset {v : HeightOneSpectrum O // v ∉ S} =>
      ‖deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T * (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
        (1 / (((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun T => ?_) hprod9
    have hposT : (0 : ℝ) < deletedSquarefreeNorm T :=
      Nat.cast_pos.mpr (deletedSquarefreeNorm_pos T)
    have hprod_eq : ∏ u ∈ T, ((u.1.asIdeal.absNorm : ℝ) ^ 9)⁻¹ =
        ((deletedSquarefreeNorm T : ℝ) ^ 9)⁻¹ := by
      unfold deletedSquarefreeNorm
      rw [Nat.cast_prod, ← Finset.prod_pow, Finset.prod_inv_distrib]
    have hrat : (deletedSquarefreeNorm T : ℝ) ^ 3 *
        (1 / (((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ 2) =
        ((deletedSquarefreeNorm T : ℝ) ^ 9)⁻¹ := by
      push_cast
      field_simp [hposT.ne']
    rw [hprod_eq, ← hrat, norm_mul, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (by positivity) (norm_deletedSquarefreeCoeff_le 𝔪 (η ^ 6) 1 T))
      (by positivity)
  have hconv := signal_eq_tsum_of_hasSum
    (E := fun s : ℂ => Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s /
      heckeLFunction 𝔪 η s)
    (G := fun s : ℂ => Complex.exp ((s - c) ^ 2) *
      fullResidualCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s /
        heckeLFunction 𝔪 η s)
    (a := fun T => deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T * (deletedSquarefreeNorm T : ℂ) ^ 3)
    (r := fun T => ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ))
    hr hEc hEb ha (fun y => ?_) hZ
  · rw [hconv]
    refine tsum_congr fun T => ?_
    rw [signal_probeCorrection_eq_continuedProbeCorrection 𝔪 η S hS c]
  · set s : ℂ := linePoint y
    have hs78 : 7 / 8 ≤ s.re := by dsimp [s]; rw [linePoint_re]; norm_num
    have hw1 : 1 < (6 * s - 3).re := by
      dsimp [s]
      simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, linePoint_re]
      norm_num
    have hsum_inv := (hasSum_inv_grossenEulerProductModS 𝔪 (η ^ 6) 1 S hw1).mul_right
      (Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s / heckeLFunction 𝔪 η s)
    have hge_ne : grossenEulerProductModS 𝔪 (η ^ 6) 1 S (6 * s - 3) ≠ 0 := by
      rw [grossenEulerProductModS_eq_mul_deletedFactors 𝔪 (η ^ 6) le_rfl S hw1]
      exact mul_ne_zero (grossenLFunction_ne_zero_of_one_lt_re 𝔪 (η ^ 6) le_rfl hw1)
        (grossenDeletedFactors_ne_zero 𝔪 (η ^ 6) 1 S (by linarith))
    have hrhs : (grossenEulerProductModS 𝔪 (η ^ 6) 1 S (6 * s - 3))⁻¹ *
        (Complex.exp ((s - c) ^ 2) * continuedProbeCorrection 𝔪 η S s /
          heckeLFunction 𝔪 η s) =
        Complex.exp ((s - c) ^ 2) *
          fullResidualCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s /
            heckeLFunction 𝔪 η s := by
      rw [continuedProbeCorrection_eq_probeCorrection 𝔪 η S hS hs78,
        probeCorrection_eq_grossen_mul_residual 𝔪 η S hS hs78]
      field_simp [hge_ne]
    rw [hrhs] at hsum_inv
    refine hsum_inv.congr_fun fun T => ?_
    have hNT_ne : ((deletedSquarefreeNorm T : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (deletedSquarefreeNorm_pos T).ne'
    have hcpow : ((deletedSquarefreeNorm T : ℝ) : ℂ) ^ (-(6 * s - 3)) =
        (deletedSquarefreeNorm T : ℂ) ^ 3 *
          (((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) : ℂ) ^ (-s) := by
      rw [natCast_pow_six_cpow_neg,
        show -(6 * s - 3) = (3 : ℂ) + -(6 * s) by ring,
        Complex.cpow_add _ _ hNT_ne, show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num,
        Complex.cpow_natCast, Complex.ofReal_natCast]
    rw [hcpow]
    ring

/-! #### Elementary dyadic counting of squarefree ideals coprime to a modulus -/

private def idealSpanOfEis (z : BourgainEisensteinInt) : Ideal O :=
  Ideal.span ({(eisCoord K).symm z} : Set O)

private theorem absNorm_idealSpanOfEis (z : BourgainEisensteinInt) :
    (Ideal.absNorm (idealSpanOfEis z) : ℤ) = BourgainEisensteinInt.norm z := by
  rw [idealSpanOfEis, Ideal.absNorm_span_singleton, algebraNorm_eq_eisNorm K,
    Equiv.apply_symm_apply, Int.natAbs_of_nonneg (BourgainEisensteinInt.norm_nonneg z)]

private def idealFinset (L U : ℕ) : Finset (Ideal O) :=
  ((Finset.Icc (max L 1) U).biUnion normSet).image idealSpanOfEis

private theorem mem_idealFinset_iff {L U : ℕ} (hL : 1 ≤ L) {I : Ideal O} :
    I ∈ idealFinset L U ↔ L ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ U := by
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨n, hn, hzn⟩ := Finset.mem_biUnion.mp hz
    rw [Finset.mem_Icc, max_eq_left hL] at hn
    have hnorm : Ideal.absNorm (idealSpanOfEis z) = n := by
      exact_mod_cast (absNorm_idealSpanOfEis z).trans (mem_normSet.mp hzn)
    omega
  · rintro ⟨hlo, hhi⟩
    set n : ℕ := Ideal.absNorm I
    set g : O := Submodule.IsPrincipal.generator I
    have hg_span : Ideal.span ({g} : Set O) = I := Ideal.span_singleton_generator I
    have hNg : BourgainEisensteinInt.norm (eisCoord K g) = n :=
      (algebraNorm_eq_eisNorm K g).symm.trans (algebraNorm_eq_of_absNorm_span K (by rw [hg_span]))
    refine Finset.mem_image.mpr ⟨eisCoord K g, Finset.mem_biUnion.mpr
      ⟨n, Finset.mem_Icc.mpr ⟨max_le hlo (hL.trans hlo), hhi⟩, mem_normSet.mpr hNg⟩, ?_⟩
    simp [idealSpanOfEis, hg_span]

private theorem le_six_mul_card_idealFinset {R : ℕ} (hR : 1 ≤ R) :
    R ^ 2 ≤ 6 * (idealFinset (2 * R ^ 2) (9 * R ^ 2)).card := by
  haveI : Finite Oˣ := Nat.finite_of_card_ne_zero (by rw [card_units_thirdCyclotomic K]; norm_num)
  letI : Fintype Oˣ := Fintype.ofFinite Oˣ
  have hcard_u : Fintype.card Oˣ = 6 := by
    rw [← Nat.card_eq_fintype_card, card_units_thirdCyclotomic K]
  set box : Finset BourgainEisensteinInt :=
    ((Finset.Icc (2 * (R : ℤ)) (3 * (R : ℤ) - 1) ×ˢ
      Finset.Icc (0 : ℤ) ((R : ℤ) - 1))).image fun ab : ℤ × ℤ => ⟨ab.1, ab.2⟩
  have hbox_card : box.card = R ^ 2 := by
    rw [Finset.card_image_of_injective _ (fun p q h =>
      Prod.ext (congrArg BourgainEisensteinInt.re h) (congrArg BourgainEisensteinInt.im h)),
      Finset.card_product, Int.card_Icc, Int.card_Icc]
    have h1 : (3 * (R : ℤ) - 1 + 1 - 2 * (R : ℤ)).toNat = R := by omega
    have h2 : ((R : ℤ) - 1 + 1 - 0).toNat = R := by omega
    rw [h1, h2, sq]
  have hsub : box ⊆ (idealFinset (2 * R ^ 2) (9 * R ^ 2) ×ˢ (Finset.univ : Finset Oˣ)).image
      (fun p => eisCoord K (Submodule.IsPrincipal.generator p.1 * (p.2 : O))) := by
    intro z hz
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hab
    have hN_lo : 2 * (R : ℤ) ^ 2 ≤ BourgainEisensteinInt.norm ⟨a, b⟩ := by
      rw [BourgainEisensteinInt.norm_def]
      nlinarith [hab.1.1, hab.1.2, hab.2.1, hab.2.2, sq_nonneg b]
    have hN_hi : BourgainEisensteinInt.norm ⟨a, b⟩ ≤ 9 * (R : ℤ) ^ 2 := by
      rw [BourgainEisensteinInt.norm_def]
      nlinarith [hab.1.1, hab.1.2, hab.2.1, hab.2.2]
    have hmem : idealSpanOfEis ⟨a, b⟩ ∈ idealFinset (2 * R ^ 2) (9 * R ^ 2) := by
      rw [mem_idealFinset_iff (by nlinarith)]
      have habs := absNorm_idealSpanOfEis ⟨a, b⟩
      have hlo_z : ((2 * R ^ 2 : ℕ) : ℤ) ≤ Ideal.absNorm (idealSpanOfEis ⟨a, b⟩) := by
        rw [habs]; push_cast; exact hN_lo
      have hhi_z : (Ideal.absNorm (idealSpanOfEis ⟨a, b⟩) : ℤ) ≤ ((9 * R ^ 2 : ℕ) : ℤ) := by
        rw [habs]; push_cast; exact hN_hi
      exact ⟨Nat.cast_le.mp hlo_z, Nat.cast_le.mp hhi_z⟩
    obtain ⟨u, hu⟩ : Associated
        (Submodule.IsPrincipal.generator (idealSpanOfEis ⟨a, b⟩))
        ((eisCoord K).symm ⟨a, b⟩) :=
      Ideal.span_singleton_eq_span_singleton.mp (Ideal.span_singleton_generator _)
    refine Finset.mem_image.mpr ⟨(idealSpanOfEis ⟨a, b⟩, u),
      Finset.mem_product.mpr ⟨hmem, Finset.mem_univ u⟩, ?_⟩
    rw [hu, Equiv.apply_symm_apply]
  calc R ^ 2 = box.card := hbox_card.symm
    _ ≤ ((idealFinset (2 * R ^ 2) (9 * R ^ 2) ×ˢ (Finset.univ : Finset Oˣ)).image
          (fun p => eisCoord K (Submodule.IsPrincipal.generator p.1 * (p.2 : O)))).card :=
        Finset.card_le_card hsub
    _ ≤ (idealFinset (2 * R ^ 2) (9 * R ^ 2) ×ˢ (Finset.univ : Finset Oˣ)).card :=
        Finset.card_image_le
    _ = 6 * (idealFinset (2 * R ^ 2) (9 * R ^ 2)).card := by
        rw [Finset.card_product, Finset.card_univ, hcard_u, mul_comm]

private theorem card_idealFinset_le (X : ℕ) :
    (idealFinset 1 X).card ≤ 49 * X := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [idealFinset]
  · set M : ℕ := 2 * Nat.sqrt X + 1
    set fullBox : Finset (ℤ × ℤ) := Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M
    have hsub : idealFinset 1 X ⊆ fullBox.image (fun ab => idealSpanOfEis ⟨ab.1, ab.2⟩) := by
      intro I hI
      obtain ⟨_, hIX⟩ := (mem_idealFinset_iff le_rfl).mp hI
      set g : O := Submodule.IsPrincipal.generator I
      set z : BourgainEisensteinInt := eisCoord K g
      have hg_span : Ideal.span ({g} : Set O) = I := Ideal.span_singleton_generator I
      have hNz : BourgainEisensteinInt.norm z = Ideal.absNorm I :=
        (algebraNorm_eq_eisNorm K g).symm.trans (algebraNorm_eq_of_absNorm_span K (by rw [hg_span]))
      have h4N : 4 * BourgainEisensteinInt.norm z ≤ 4 * (X : ℤ) := by
        rw [hNz]; exact_mod_cast Nat.mul_le_mul_left 4 hIX
      have hX_lt : (X : ℤ) < ((Nat.sqrt X + 1 : ℕ) : ℤ) ^ 2 := by
        have hX_nat : X < (Nat.sqrt X + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt X
        exact_mod_cast hX_nat
      have hre_sq : z.re ^ 2 < ((M : ℤ) + 1) ^ 2 := by
        have h3 : 3 * z.re ^ 2 ≤ 4 * BourgainEisensteinInt.norm z := by
          rw [BourgainEisensteinInt.norm_def]
          nlinarith [sq_nonneg (z.re - 2 * z.im)]
        have hM_eq : (M : ℤ) + 1 = 2 * ((Nat.sqrt X + 1 : ℕ) : ℤ) := by
          dsimp [M]; ring
        rw [hM_eq]
        nlinarith [sq_nonneg z.re]
      have him_sq : z.im ^ 2 < ((M : ℤ) + 1) ^ 2 := by
        have h3 : 3 * z.im ^ 2 ≤ 4 * BourgainEisensteinInt.norm z := by
          rw [BourgainEisensteinInt.norm_def]
          nlinarith [sq_nonneg (2 * z.re - z.im)]
        have hM_eq : (M : ℤ) + 1 = 2 * ((Nat.sqrt X + 1 : ℕ) : ℤ) := by
          dsimp [M]; ring
        rw [hM_eq]
        nlinarith [sq_nonneg z.im]
      have hre_mem : -(M : ℤ) ≤ z.re ∧ z.re ≤ M := by
        constructor <;> by_contra hc <;> nlinarith [not_le.mp hc]
      have him_mem : -(M : ℤ) ≤ z.im ∧ z.im ≤ M := by
        constructor <;> by_contra hc <;> nlinarith [not_le.mp hc]
      refine Finset.mem_image.mpr ⟨(z.re, z.im),
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hre_mem, Finset.mem_Icc.mpr him_mem⟩, ?_⟩
      change idealSpanOfEis z = I
      simp [idealSpanOfEis, z, hg_span]
    have hcard_box : fullBox.card = (4 * Nat.sqrt X + 3) ^ 2 := by
      dsimp [fullBox]
      rw [Finset.card_product, Int.card_Icc]
      have h1 : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 4 * Nat.sqrt X + 3 := by dsimp [M]; omega
      rw [h1, sq]
    have hs_ge1 : 1 ≤ Nat.sqrt X := Nat.sqrt_pos.mpr hX
    have hs_sq : Nat.sqrt X ^ 2 ≤ X := by rw [sq]; exact Nat.sqrt_le X
    calc (idealFinset 1 X).card
        ≤ (fullBox.image (fun ab => idealSpanOfEis ⟨ab.1, ab.2⟩)).card :=
          Finset.card_le_card hsub
      _ ≤ fullBox.card := Finset.card_image_le
      _ = (4 * Nat.sqrt X + 3) ^ 2 := hcard_box
      _ ≤ (7 * Nat.sqrt X) ^ 2 := by nlinarith
      _ = 49 * Nat.sqrt X ^ 2 := by ring
      _ ≤ 49 * X := Nat.mul_le_mul_left 49 hs_sq

private def sqfPartOfIdeal (I : Ideal O) : Finset (HeightOneSpectrum O) :=
  if hI : I = ⊥ then ∅
  else (idealPrimeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩).support.filter
    fun v => idealPrimeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ v % 2 = 1

private def sqPartOfIdeal (I : Ideal O) : Ideal O :=
  if hI : I = ⊥ then ⊥
  else ∏ v ∈ (idealPrimeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩).support,
    v.asIdeal ^ (idealPrimeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ v / 2)

private theorem mul_sq_sqPartOfIdeal {I : Ideal O} (hI : I ≠ ⊥) :
    (∏ v ∈ sqfPartOfIdeal I, v.asIdeal) * sqPartOfIdeal I ^ 2 = I := by
  unfold sqfPartOfIdeal sqPartOfIdeal
  rw [dif_neg hI, dif_neg hI]
  set ν := idealPrimeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩
  have hsqf : ∏ v ∈ ν.support.filter (fun v => ν v % 2 = 1), v.asIdeal =
      ∏ v ∈ ν.support, v.asIdeal ^ (ν v % 2) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ => ?_
    rcases Nat.mod_two_eq_zero_or_one (ν v) with h0 | h1
    · rw [h0, if_neg zero_ne_one, pow_zero]
    · rw [h1, if_pos rfl, pow_one]
  have hsq : (∏ v ∈ ν.support, v.asIdeal ^ (ν v / 2)) ^ 2 =
      ∏ v ∈ ν.support, v.asIdeal ^ (2 * (ν v / 2)) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun v _ => by rw [← pow_mul, mul_comm]
  rw [hsqf, hsq, ← Finset.prod_mul_distrib]
  have hcomb : (∏ v ∈ ν.support, v.asIdeal ^ (ν v % 2) * v.asIdeal ^ (2 * (ν v / 2))) =
      ∏ v ∈ ν.support, v.asIdeal ^ (ν v) :=
    Finset.prod_congr rfl fun v _ => by rw [← pow_add, Nat.mod_add_div]
  rw [hcomb]
  have heq := congrArg Subtype.val
    (idealOfPrimeExponents_idealPrimeExponents ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩)
  simpa only [idealOfPrimeExponents, Finsupp.prod] using heq

private theorem exists_pow_two_le_and_lt {q : ℕ} (hq : 1 ≤ q) :
    ∃ j : ℕ, 2 ^ j ≤ q ∧ q < 2 ^ (j + 1) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    rcases eq_or_ne q 1 with rfl | hq1
    · exact ⟨0, by norm_num, by norm_num⟩
    · have hdiv_pos : 1 ≤ q / 2 := by omega
      have hdiv_lt : q / 2 < q := by omega
      obtain ⟨j, hj1, hj2⟩ := ih (q / 2) hdiv_lt hdiv_pos
      refine ⟨j + 1, ?_, ?_⟩ <;> rw [pow_succ] <;> omega

private theorem sum_half_pow_le_two (m : ℕ) :
    ∑ j ∈ Finset.range m, ((1 / 2 : ℝ) ^ j) ≤ 2 := by
  have heq : ∀ n : ℕ, ∑ j ∈ Finset.range n, ((1 / 2 : ℝ) ^ j) = 2 - 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq m]
  linarith [show (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ m by positivity]

private def sqPartHead (B₀ R : ℕ) : Finset (Ideal O) :=
  (idealFinset (2 * R ^ 2) (9 * R ^ 2)).filter fun I => ¬ (B₀ < Ideal.absNorm (sqPartOfIdeal I))

private theorem card_sqPartHead_ge {B₀ R : ℕ} (hB₀ : 1100000 ≤ B₀) (hR : 1 ≤ R) :
    (1 / 12 : ℝ) * (R : ℝ) ^ 2 ≤ ((sqPartHead B₀ R).card : ℝ) := by
  have hB₀_pos : 0 < B₀ := by omega
  have hB₀_rpos : (0 : ℝ) < B₀ := Nat.cast_pos.mpr hB₀_pos
  have hB₀_rge : (1100000 : ℝ) ≤ B₀ := by exact_mod_cast hB₀
  set shell := idealFinset (2 * R ^ 2) (9 * R ^ 2)
  set tail := shell.filter fun I => B₀ < Ideal.absNorm (sqPartOfIdeal I)
  have htail_sub : tail ⊆ (Finset.range (3 * R)).biUnion fun j =>
      ((idealFinset 1 ((9 * R ^ 2) / (2 ^ j * B₀) ^ 2)) ×ˢ
        (idealFinset 1 (2 ^ (j + 1) * B₀))).image (fun p => p.1 * p.2 ^ 2) := by
    intro I hI
    obtain ⟨hIshell, hB_gt⟩ := Finset.mem_filter.mp hI
    obtain ⟨hI_lo, hI_hi⟩ := (mem_idealFinset_iff (by nlinarith)).mp hIshell
    have hI_ne : I ≠ ⊥ := by
      rintro rfl
      rw [Ideal.absNorm_bot] at hI_lo
      nlinarith
    set J := ∏ v ∈ sqfPartOfIdeal I, v.asIdeal
    set B := sqPartOfIdeal I
    have hB_gt' : B₀ < Ideal.absNorm B := hB_gt
    have hJB : J * B ^ 2 = I := mul_sq_sqPartOfIdeal hI_ne
    have hnorm_JB : Ideal.absNorm J * Ideal.absNorm B ^ 2 = Ideal.absNorm I := by
      rw [← map_pow, ← map_mul, hJB]
    have hJ_pos : 1 ≤ Ideal.absNorm J := by
      by_contra h0
      have hJ0 : Ideal.absNorm J = 0 := by omega
      rw [hJ0, zero_mul] at hnorm_JB
      nlinarith
    have hB_le_3R : Ideal.absNorm B ≤ 3 * R := by
      by_contra hgt
      have hgt' : 3 * R + 1 ≤ Ideal.absNorm B := by omega
      have hsq_gt : 9 * R ^ 2 < Ideal.absNorm B ^ 2 := by nlinarith
      nlinarith
    obtain ⟨j, hj_lo, hj_hi⟩ := exists_pow_two_le_and_lt
      (q := (Ideal.absNorm B - 1) / B₀)
      ((Nat.le_div_iff_mul_le hB₀_pos).mpr (by simp only [one_mul]; omega))
    have hB_lo : 2 ^ j * B₀ < Ideal.absNorm B := by
      have h1 : 2 ^ j * B₀ ≤ ((Ideal.absNorm B - 1) / B₀) * B₀ := Nat.mul_le_mul_right B₀ hj_lo
      have h2 : ((Ideal.absNorm B - 1) / B₀) * B₀ ≤ Ideal.absNorm B - 1 := Nat.div_mul_le_self _ _
      omega
    have hB_hi : Ideal.absNorm B ≤ 2 ^ (j + 1) * B₀ := by
      have h1 : Ideal.absNorm B - 1 < 2 ^ (j + 1) * B₀ :=
        (Nat.div_lt_iff_lt_mul hB₀_pos).mp hj_hi
      omega
    have hj_lt : j < 3 * R := by
      have hj_pow : j < 2 ^ j := j.lt_two_pow_self
      have h1 : 2 ^ j ≤ 2 ^ j * B₀ := Nat.le_mul_of_pos_right _ hB₀_pos
      omega
    have hJ_hi : Ideal.absNorm J ≤ (9 * R ^ 2) / (2 ^ j * B₀) ^ 2 := by
      have hpow_pos : 0 < (2 ^ j * B₀) ^ 2 := by positivity
      refine (Nat.le_div_iff_mul_le hpow_pos).mpr ?_
      have hsq_le : (2 ^ j * B₀) ^ 2 ≤ Ideal.absNorm B ^ 2 := Nat.pow_le_pow_left hB_lo.le 2
      exact (Nat.mul_le_mul_left _ hsq_le).trans (hnorm_JB.le.trans hI_hi)
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt,
      Finset.mem_image.mpr ⟨(J, B), Finset.mem_product.mpr
        ⟨(mem_idealFinset_iff le_rfl).mpr ⟨hJ_pos, hJ_hi⟩,
         (mem_idealFinset_iff le_rfl).mpr ⟨Nat.one_le_of_lt hB_gt', hB_hi⟩⟩, hJB⟩⟩
  have htail_card : (tail.card : ℝ) ≤ (1 / 12 : ℝ) * (R : ℝ) ^ 2 := by
    have h1 : tail.card ≤ ∑ j ∈ Finset.range (3 * R),
        (idealFinset 1 ((9 * R ^ 2) / (2 ^ j * B₀) ^ 2)).card *
          (idealFinset 1 (2 ^ (j + 1) * B₀)).card := by
      refine (Finset.card_le_card htail_sub).trans (Finset.card_biUnion_le.trans ?_)
      refine Finset.sum_le_sum fun j _ => ?_
      exact Finset.card_image_le.trans (Finset.card_product _ _).le
    have h1r : (tail.card : ℝ) ≤ ∑ j ∈ Finset.range (3 * R),
        ((idealFinset 1 ((9 * R ^ 2) / (2 ^ j * B₀) ^ 2)).card : ℝ) *
          ((idealFinset 1 (2 ^ (j + 1) * B₀)).card : ℝ) := by
      exact_mod_cast h1
    refine h1r.trans ?_
    have hcoef : (43218 / (B₀ : ℝ)) * 2 ≤ 1 / 12 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB₀_rpos]
      linarith
    calc ∑ j ∈ Finset.range (3 * R),
          ((idealFinset 1 ((9 * R ^ 2) / (2 ^ j * B₀) ^ 2)).card : ℝ) *
            ((idealFinset 1 (2 ^ (j + 1) * B₀)).card : ℝ)
        ≤ ∑ j ∈ Finset.range (3 * R),
            (43218 / (B₀ : ℝ)) * (R : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hc1 : ((idealFinset 1 ((9 * R ^ 2) / (2 ^ j * B₀) ^ 2)).card : ℝ) ≤
              49 * ((9 * (R : ℝ) ^ 2) / ((2 : ℝ) ^ j * (B₀ : ℝ)) ^ 2) := by
            have hn1 : ((idealFinset 1 ((9 * R ^ 2) / (2 ^ j * B₀) ^ 2)).card : ℝ) ≤
                49 * (((9 * R ^ 2) / (2 ^ j * B₀) ^ 2 : ℕ) : ℝ) := by
              exact_mod_cast card_idealFinset_le _
            refine hn1.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            refine (Nat.cast_div_le (m := 9 * R ^ 2) (n := (2 ^ j * B₀) ^ 2)).trans (le_of_eq ?_)
            push_cast
            rfl
          have hc2 : ((idealFinset 1 (2 ^ (j + 1) * B₀)).card : ℝ) ≤
              49 * ((2 : ℝ) ^ (j + 1) * (B₀ : ℝ)) := by
            have hn2 := card_idealFinset_le (2 ^ (j + 1) * B₀)
            exact_mod_cast hn2
          refine (mul_le_mul hc1 hc2 (Nat.cast_nonneg _) (by positivity)).trans
            (le_of_eq ?_)
          have h2ne : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
          have hBne : (B₀ : ℝ) ≠ 0 := hB₀_rpos.ne'
          rw [one_div_pow, pow_succ]
          field_simp [h2ne, hBne]
          ring
      _ = (43218 / (B₀ : ℝ)) * (R : ℝ) ^ 2 *
            ∑ j ∈ Finset.range (3 * R), ((1 / 2 : ℝ) ^ j) := by
          rw [← Finset.mul_sum]
      _ ≤ (43218 / (B₀ : ℝ)) * (R : ℝ) ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left (sum_half_pow_le_two (3 * R)) (by positivity)
      _ = ((43218 / (B₀ : ℝ)) * 2) * (R : ℝ) ^ 2 := by ring
      _ ≤ (1 / 12 : ℝ) * (R : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg (R : ℝ))
  have hsplit : (sqPartHead B₀ R).card + tail.card = shell.card := by
    dsimp [sqPartHead, tail, shell]
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _
  have hshell_ge : (R : ℝ) ^ 2 ≤ 6 * (shell.card : ℝ) := by
    exact_mod_cast le_six_mul_card_idealFinset hR
  have hsplit_r : ((sqPartHead B₀ R).card : ℝ) + (tail.card : ℝ) = (shell.card : ℝ) := by
    exact_mod_cast hsplit
  linarith

private def sqfShellOfCutoff (B₀ R : ℕ) : Finset (Finset (HeightOneSpectrum O)) :=
  (sqPartHead B₀ R).image sqfPartOfIdeal

private theorem card_sqfShellOfCutoff_ge {B₀ R : ℕ} (hB₀ : 1100000 ≤ B₀) (hR : 1 ≤ R) :
    (1 / (12 * 49 * (B₀ : ℝ))) * (R : ℝ) ^ 2 ≤ ((sqfShellOfCutoff B₀ R).card : ℝ) := by
  have hB₀_pos : 0 < B₀ := by omega
  have hB₀_rpos : (0 : ℝ) < B₀ := Nat.cast_pos.mpr hB₀_pos
  have hhead_card := card_sqPartHead_ge hB₀ hR
  have hhead_sub : sqPartHead B₀ R ⊆ (sqfShellOfCutoff B₀ R ×ˢ idealFinset 1 B₀).image
      (fun p => (∏ v ∈ p.1, v.asIdeal) * p.2 ^ 2) := by
    intro I hI
    obtain ⟨hIshell, hB_le⟩ := Finset.mem_filter.mp hI
    obtain ⟨hI_lo, _⟩ := (mem_idealFinset_iff (by nlinarith)).mp hIshell
    have hI_ne : I ≠ ⊥ := by
      rintro rfl; rw [Ideal.absNorm_bot] at hI_lo; nlinarith
    have hJB := mul_sq_sqPartOfIdeal hI_ne
    have hB_pos : 1 ≤ Ideal.absNorm (sqPartOfIdeal I) := by
      by_contra h0
      have hB0 : Ideal.absNorm (sqPartOfIdeal I) = 0 := by omega
      have hnorm : Ideal.absNorm ((∏ v ∈ sqfPartOfIdeal I, v.asIdeal) * sqPartOfIdeal I ^ 2) =
          Ideal.absNorm I := congrArg Ideal.absNorm hJB
      rw [map_mul, map_pow, hB0, zero_pow (by norm_num), mul_zero] at hnorm
      nlinarith
    exact Finset.mem_image.mpr ⟨(sqfPartOfIdeal I, sqPartOfIdeal I),
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,
        (mem_idealFinset_iff le_rfl).mpr ⟨hB_pos, not_lt.mp hB_le⟩⟩, hJB⟩
  have hle : (sqPartHead B₀ R).card ≤ (sqfShellOfCutoff B₀ R).card * (49 * B₀) := by
    calc (sqPartHead B₀ R).card
        ≤ ((sqfShellOfCutoff B₀ R ×ˢ idealFinset 1 B₀).image
            (fun p => (∏ v ∈ p.1, v.asIdeal) * p.2 ^ 2)).card := Finset.card_le_card hhead_sub
      _ ≤ (sqfShellOfCutoff B₀ R ×ˢ idealFinset 1 B₀).card := Finset.card_image_le
      _ = (sqfShellOfCutoff B₀ R).card * (idealFinset 1 B₀).card := Finset.card_product _ _
      _ ≤ (sqfShellOfCutoff B₀ R).card * (49 * B₀) :=
          Nat.mul_le_mul_left _ (card_idealFinset_le B₀)
  have hle_r : ((sqPartHead B₀ R).card : ℝ) ≤
      ((sqfShellOfCutoff B₀ R).card : ℝ) * (49 * (B₀ : ℝ)) := by exact_mod_cast hle
  have hBpos : (0 : ℝ) < 49 * (B₀ : ℝ) := by positivity
  have hmul_eq : (1 / (12 * 49 * (B₀ : ℝ))) * (R : ℝ) ^ 2 * (49 * (B₀ : ℝ)) =
      (1 / 12 : ℝ) * (R : ℝ) ^ 2 := by
    field_simp [hB₀_rpos.ne']
  exact le_of_mul_le_mul_right (by linarith [hhead_card, hle_r, hmul_eq]) hBpos

private def stripBadPrimes (𝔪 : Modulus K) (S : Finset (HeightOneSpectrum O))
    (T : Finset (HeightOneSpectrum O)) : Finset {v : HeightOneSpectrum O // v ∉ S} :=
  (T.subtype fun v => v ∉ S).filter fun u => ¬ (𝔪.fin ≤ u.1.asIdeal)

private theorem exists_coprime_squarefree_shell_of_cutoff (𝔪 : Modulus K)
    (S : Finset (HeightOneSpectrum O)) {B₀ : ℕ} (hB₀ : 1100000 ≤ B₀) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ R : ℕ, 1 ≤ R →
      ∃ ℱ : Finset (Finset {v : HeightOneSpectrum O // v ∉ S}),
        c₀ * (R : ℝ) ^ 2 ≤ (ℱ.card : ℝ) ∧
        ∀ U ∈ ℱ, (∀ u ∈ U, ¬ (𝔪.fin ≤ u.1.asIdeal)) ∧
          c₁ * (R : ℝ) ^ 2 ≤ (deletedSquarefreeNorm U : ℝ) ∧
          deletedSquarefreeNorm U ≤ 9 * R ^ 2 := by
  have hB₀_pos : 0 < B₀ := by omega
  have hB₀_rpos : (0 : ℝ) < B₀ := Nat.cast_pos.mpr hB₀_pos
  obtain ⟨Bfin, hBfin⟩ := (finite_grossenBadPrimesSet 𝔪 S).exists_finset_coe
  have hmem_Bfin : ∀ v : HeightOneSpectrum O, v ∈ Bfin ↔ v ∈ grossenBadPrimesSet 𝔪 S :=
    fun v => by rw [← Finset.mem_coe, hBfin]
  have hM_pos : 0 < ∏ v ∈ Bfin, v.asIdeal.absNorm := Finset.prod_pos fun v _ =>
    lt_of_lt_of_le zero_lt_two (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
  have hM_rpos : (0 : ℝ) < ((∏ v ∈ Bfin, v.asIdeal.absNorm : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hM_pos
  have hK_rpos : (0 : ℝ) < ((2 ^ Bfin.card : ℕ) : ℝ) := by positivity
  refine ⟨1 / (12 * 49 * (B₀ : ℝ) * ((2 ^ Bfin.card : ℕ) : ℝ)),
    2 / ((B₀ : ℝ) ^ 2 * ((∏ v ∈ Bfin, v.asIdeal.absNorm : ℕ) : ℝ)),
    by positivity, by positivity, fun R hR => ?_⟩
  have hsqf_card := card_sqfShellOfCutoff_ge hB₀ hR
  set ℱ := (sqfShellOfCutoff B₀ R).image (stripBadPrimes 𝔪 S)
  have hsqf_sub : sqfShellOfCutoff B₀ R ⊆
      (Bfin.powerset ×ˢ ℱ).image (fun p => p.1 ∪ p.2.image Subtype.val) := by
    intro T hT
    refine Finset.mem_image.mpr ⟨(T ∩ Bfin, stripBadPrimes 𝔪 S T),
      Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_image_of_mem _ hT⟩, ?_⟩
    ext v
    rw [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hvT, _⟩ | h2)
      · exact hvT
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h2
        exact Finset.mem_subtype.mp (Finset.mem_filter.mp hu).1
    · intro hvT
      by_cases hbad : v ∈ Bfin
      · exact Or.inl ⟨hvT, hbad⟩
      · have hnot_bad : v ∉ grossenBadPrimesSet 𝔪 S := fun h => hbad ((hmem_Bfin v).mpr h)
        have hvS : v ∉ S := fun hS => hnot_bad (Or.inl hS)
        have hnot_le : ¬ (𝔪.fin ≤ v.asIdeal) := fun hle => hnot_bad (Or.inr hle)
        refine Or.inr (Finset.mem_image.mpr ⟨⟨v, hvS⟩, ?_, rfl⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_subtype.mpr hvT, hnot_le⟩
  have hℱ_card :
      (1 / (12 * 49 * (B₀ : ℝ) * ((2 ^ Bfin.card : ℕ) : ℝ))) * (R : ℝ) ^ 2 ≤ (ℱ.card : ℝ) := by
    have hle : (sqfShellOfCutoff B₀ R).card ≤ 2 ^ Bfin.card * ℱ.card := by
      calc (sqfShellOfCutoff B₀ R).card
          ≤ ((Bfin.powerset ×ˢ ℱ).image (fun p => p.1 ∪ p.2.image Subtype.val)).card :=
            Finset.card_le_card hsqf_sub
        _ ≤ (Bfin.powerset ×ˢ ℱ).card := Finset.card_image_le
        _ = 2 ^ Bfin.card * ℱ.card := by rw [Finset.card_product, Finset.card_powerset]
    have hle_r : ((sqfShellOfCutoff B₀ R).card : ℝ) ≤
        ((2 ^ Bfin.card : ℕ) : ℝ) * (ℱ.card : ℝ) := by exact_mod_cast hle
    have hdiv : ((2 ^ Bfin.card : ℕ) : ℝ) *
        ((1 / (12 * 49 * (B₀ : ℝ) * ((2 ^ Bfin.card : ℕ) : ℝ))) * (R : ℝ) ^ 2) =
        (1 / (12 * 49 * (B₀ : ℝ))) * (R : ℝ) ^ 2 := by
      field_simp [hK_rpos.ne', hB₀_rpos.ne']
    exact le_of_mul_le_mul_left (by linarith [hsqf_card, hle_r, hdiv]) hK_rpos
  refine ⟨ℱ, hℱ_card, fun U hU => ?_⟩
  obtain ⟨T, hTshell, rfl⟩ := Finset.mem_image.mp hU
  obtain ⟨I, hIhead, rfl⟩ := Finset.mem_image.mp hTshell
  obtain ⟨hIshell, hB_le⟩ := Finset.mem_filter.mp hIhead
  obtain ⟨hI_lo, hI_hi⟩ := (mem_idealFinset_iff (by nlinarith)).mp hIshell
  have hI_ne : I ≠ ⊥ := by rintro rfl; rw [Ideal.absNorm_bot] at hI_lo; nlinarith
  have hJB := mul_sq_sqPartOfIdeal hI_ne
  have hnorm_JB : (∏ v ∈ sqfPartOfIdeal I, v.asIdeal.absNorm) *
      Ideal.absNorm (sqPartOfIdeal I) ^ 2 = Ideal.absNorm I := by
    rw [← map_prod Ideal.absNorm, ← map_pow, ← map_mul, hJB]
  have hcop : ∀ u ∈ stripBadPrimes 𝔪 S (sqfPartOfIdeal I), ¬ (𝔪.fin ≤ u.1.asIdeal) :=
    fun _ hu => (Finset.mem_filter.mp hu).2
  have hgood_norm : deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) =
      ∏ v ∈ (sqfPartOfIdeal I).filter (fun v => v ∉ Bfin), v.asIdeal.absNorm := by
    unfold deletedSquarefreeNorm
    let emb : {v : HeightOneSpectrum O // v ∉ S} ↪ HeightOneSpectrum O :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have himg : (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)).map emb =
        (sqfPartOfIdeal I).filter (fun v => v ∉ Bfin) := by
      ext v
      rw [Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨u, hu, rfl⟩
        dsimp [emb]
        obtain ⟨huT, hnot_le⟩ := Finset.mem_filter.mp hu
        exact ⟨Finset.mem_subtype.mp huT, fun hB => ((hmem_Bfin u.1).mp hB).elim u.2 hnot_le⟩
      · rintro ⟨hvT, hvB⟩
        have hnot_bad : v ∉ grossenBadPrimesSet 𝔪 S := fun h => hvB ((hmem_Bfin v).mpr h)
        have hvS : v ∉ S := fun hS => hnot_bad (Or.inl hS)
        have hnot_le : ¬ (𝔪.fin ≤ v.asIdeal) := fun hle => hnot_bad (Or.inr hle)
        exact ⟨⟨v, hvS⟩, Finset.mem_filter.mpr ⟨Finset.mem_subtype.mpr hvT, hnot_le⟩, rfl⟩
    rw [← himg, Finset.prod_map]
    rfl
  have hsplit_T : (∏ v ∈ sqfPartOfIdeal I, v.asIdeal.absNorm) =
      deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) *
        ∏ v ∈ (sqfPartOfIdeal I).filter (fun v => v ∈ Bfin), v.asIdeal.absNorm := by
    rw [hgood_norm, mul_comm]
    exact (Finset.prod_filter_mul_prod_filter_not (sqfPartOfIdeal I)
      (fun v => v ∈ Bfin) (fun v => v.asIdeal.absNorm)).symm
  have hbad_le_M : (∏ v ∈ (sqfPartOfIdeal I).filter (fun v => v ∈ Bfin),
      v.asIdeal.absNorm) ≤ ∏ v ∈ Bfin, v.asIdeal.absNorm :=
    Finset.prod_le_prod_of_subset_of_one_le'
      (fun v hv => (Finset.mem_filter.mp hv).2) fun v _ _ =>
        (lt_of_lt_of_le one_lt_two
          (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)).le
  have hbad_pos : 1 ≤ ∏ v ∈ (sqfPartOfIdeal I).filter (fun v => v ∈ Bfin),
      v.asIdeal.absNorm :=
    Finset.prod_pos fun v _ =>
      lt_of_lt_of_le zero_lt_two (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
  have hU_hi : deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) ≤ 9 * R ^ 2 := by
    have hB_pos : 1 ≤ Ideal.absNorm (sqPartOfIdeal I) ^ 2 := by
      by_contra h0
      have hB0 : Ideal.absNorm (sqPartOfIdeal I) ^ 2 = 0 := by omega
      rw [hB0, mul_zero] at hnorm_JB
      nlinarith
    have h1 : deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) ≤
        ∏ v ∈ sqfPartOfIdeal I, v.asIdeal.absNorm := by
      rw [hsplit_T]
      exact Nat.le_mul_of_pos_right _ hbad_pos
    exact h1.trans ((Nat.le_mul_of_pos_right _ hB_pos).trans (hnorm_JB.le.trans hI_hi))
  have hU_lo :
      (2 / ((B₀ : ℝ) ^ 2 * ((∏ v ∈ Bfin, v.asIdeal.absNorm : ℕ) : ℝ))) * (R : ℝ) ^ 2 ≤
        (deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) : ℝ) := by
    have hB_le' : Ideal.absNorm (sqPartOfIdeal I) ≤ B₀ := not_lt.mp hB_le
    have hmul_nat : 2 * R ^ 2 ≤
        deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) *
          (B₀ ^ 2 * ∏ v ∈ Bfin, v.asIdeal.absNorm) := by
      calc 2 * R ^ 2 ≤ Ideal.absNorm I := hI_lo
        _ = (deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) *
              ∏ v ∈ (sqfPartOfIdeal I).filter (fun v => v ∈ Bfin),
                v.asIdeal.absNorm) * Ideal.absNorm (sqPartOfIdeal I) ^ 2 := by
            rw [← hnorm_JB, hsplit_T]
        _ ≤ (deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) *
              ∏ v ∈ Bfin, v.asIdeal.absNorm) * B₀ ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hbad_le_M) (Nat.pow_le_pow_left hB_le' 2)
        _ = deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) *
              (B₀ ^ 2 * ∏ v ∈ Bfin, v.asIdeal.absNorm) := by ring
    have hmul_r : 2 * (R : ℝ) ^ 2 ≤
        (deletedSquarefreeNorm (stripBadPrimes 𝔪 S (sqfPartOfIdeal I)) : ℝ) *
          ((B₀ : ℝ) ^ 2 * ((∏ v ∈ Bfin, v.asIdeal.absNorm : ℕ) : ℝ)) := by
      exact_mod_cast hmul_nat
    have hden_pos : (0 : ℝ) < (B₀ : ℝ) ^ 2 * ((∏ v ∈ Bfin, v.asIdeal.absNorm : ℕ) : ℝ) :=
      mul_pos (pow_pos hB₀_rpos 2) hM_rpos
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    exact hmul_r
  exact ⟨hcop, hU_lo, hU_hi⟩

/-- At least `c₀ · R²` squarefree ideals of `O` outside `grossenBadPrimesSet 𝔪 S` have norm in
`[c₁ · R², 9 · R²]` for every `R ≥ 1`. -/
private theorem exists_coprime_squarefree_shell (𝔪 : Modulus K)
    (S : Finset (HeightOneSpectrum O)) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ ∀ R : ℕ, 1 ≤ R →
      ∃ ℱ : Finset (Finset {v : HeightOneSpectrum O // v ∉ S}),
        c₀ * (R : ℝ) ^ 2 ≤ (ℱ.card : ℝ) ∧
        ∀ U ∈ ℱ, (∀ u ∈ U, ¬ (𝔪.fin ≤ u.1.asIdeal)) ∧
          c₁ * (R : ℝ) ^ 2 ≤ (deletedSquarefreeNorm U : ℝ) ∧
          deletedSquarefreeNorm U ≤ 9 * R ^ 2 :=
  exists_coprime_squarefree_shell_of_cutoff 𝔪 S (B₀ := 1100000) le_rfl

/-- **Unconditional `Z^{2/3}` squarefree sixth-power Möbius norm barrier.** For every modulus `𝔪`,
character `η : HeckeCharacter 𝔪`, finite prime set `S`, and real exponent `a`, there exist `c > 0`
and `Z₁ ≥ 1` such that for all `Z ≥ Z₁`, some finite family `ℱ` of prime subsets outside `S`
supported in `N(T)⁶ ≤ Z` satisfies
`c · Z^{2/3} ≤ ∑_{T ∈ ℱ} ‖deletedSquarefreeCoeff 𝔪 (η⁶) 1 T · N(T)³‖ · (Z / N(T)⁶)^a`. -/
theorem exists_lower_bound_squarefree_sixthPower_mobius_norm (𝔪 : Modulus K)
    (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O)) (a : ℝ) :
    ∃ c Z₁ : ℝ, 0 < c ∧ 1 ≤ Z₁ ∧ ∀ Z : ℝ, Z₁ ≤ Z →
      ∃ ℱ : Finset (Finset {v : HeightOneSpectrum O // v ∉ S}),
        (∀ T ∈ ℱ, ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) ≤ Z) ∧
        c * Z ^ (2 / 3 : ℝ) ≤
          ∑ T ∈ ℱ, ‖deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T *
            (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
              (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ a := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hshell⟩ := exists_coprime_squarefree_shell 𝔪 S
  set γ : ℝ := min ((c₁ / 36) ^ (3 - 6 * a)) 1
  have hγ_pos : 0 < γ := lt_min (Real.rpow_pos_of_pos (by positivity) _) zero_lt_one
  refine ⟨(c₀ / 36) * γ, (36 : ℝ) ^ 6, by positivity, by norm_num, fun Z hZ => ?_⟩
  have hZ_pos : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have hZ16_ge : 36 ≤ Z ^ (1 / 6 : ℝ) := by
    calc (36 : ℝ) = ((36 : ℝ) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ Z ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) hZ (by norm_num)
  set x : ℝ := Real.sqrt (Z ^ (1 / 6 : ℝ) / 9)
  have hx_ge2 : 2 ≤ x := by
    dsimp [x]
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  set R : ℕ := ⌊x⌋₊
  have hR_ge1 : 1 ≤ R := by
    have h2 : 2 ≤ R := (Nat.le_floor_iff (by linarith)).mpr hx_ge2
    omega
  have hR_le_x : (R : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx_lt_R1 : x < (R : ℝ) + 1 := Nat.lt_floor_add_one x
  have hR_ge_half : x / 2 ≤ (R : ℝ) := by
    have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast (show 2 ≤ R from
      (Nat.le_floor_iff (by linarith)).mpr hx_ge2)
    linarith
  have hx_sq : x ^ 2 = Z ^ (1 / 6 : ℝ) / 9 := Real.sq_sqrt (by positivity)
  have hR_sq_hi : 9 * (R : ℝ) ^ 2 ≤ Z ^ (1 / 6 : ℝ) := by
    have h1 : (R : ℝ) ^ 2 ≤ x ^ 2 := sq_le_sq' (by linarith) hR_le_x
    linarith
  have hR_sq_lo : (1 / 36 : ℝ) * Z ^ (1 / 6 : ℝ) ≤ (R : ℝ) ^ 2 := by
    have h1 : (x / 2) ^ 2 ≤ (R : ℝ) ^ 2 := sq_le_sq' (by linarith) hR_ge_half
    have h2 : (x / 2) ^ 2 = (1 / 36 : ℝ) * Z ^ (1 / 6 : ℝ) := by linear_combination hx_sq / 4
    linarith
  obtain ⟨ℱ, hℱ_card, hℱ_mem⟩ := hshell R hR_ge1
  refine ⟨ℱ, fun T hT => ?_, ?_⟩
  · have hT_hi : (deletedSquarefreeNorm T : ℝ) ≤ Z ^ (1 / 6 : ℝ) := by
      have h1 : (deletedSquarefreeNorm T : ℝ) ≤ 9 * (R : ℝ) ^ 2 := by
        exact_mod_cast (hℱ_mem T hT).2.2
      exact h1.trans hR_sq_hi
    calc ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)
        = (deletedSquarefreeNorm T : ℝ) ^ (6 : ℕ) := by push_cast; rfl
      _ ≤ (Z ^ (1 / 6 : ℝ)) ^ (6 : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hT_hi 6
      _ = Z := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hZ_pos.le]
          norm_num
  · have hterm_ge : ∀ T ∈ ℱ,
        γ * Z ^ (1 / 2 : ℝ) ≤
          ‖deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T * (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
            (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ a := by
      intro T hT
      obtain ⟨hcop, hlo, hhi⟩ := hℱ_mem T hT
      have hNT_pos : (0 : ℝ) < deletedSquarefreeNorm T :=
        Nat.cast_pos.mpr (deletedSquarefreeNorm_pos T)
      have hNT_lo : (c₁ / 36) * Z ^ (1 / 6 : ℝ) ≤ (deletedSquarefreeNorm T : ℝ) := by
        calc (c₁ / 36) * Z ^ (1 / 6 : ℝ)
            = c₁ * ((1 / 36 : ℝ) * Z ^ (1 / 6 : ℝ)) := by ring
          _ ≤ c₁ * (R : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hR_sq_lo hc₁.le
          _ ≤ (deletedSquarefreeNorm T : ℝ) := hlo
      have hNT_hi : (deletedSquarefreeNorm T : ℝ) ≤ Z ^ (1 / 6 : ℝ) := by
        have h1 : (deletedSquarefreeNorm T : ℝ) ≤ 9 * (R : ℝ) ^ 2 := by exact_mod_cast hhi
        exact h1.trans hR_sq_hi
      have hnorm_eq : ‖deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T *
          (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
            (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ a =
          Z ^ a * (deletedSquarefreeNorm T : ℝ) ^ (3 - 6 * a) := by
        rw [norm_mul, norm_deletedSquarefreeCoeff_eq_one 𝔪 (η ^ 6) 1 hcop, one_mul,
          norm_pow, Complex.norm_natCast, Real.div_rpow hZ_pos.le (Nat.cast_nonneg _),
          Nat.cast_pow, ← Real.rpow_natCast (deletedSquarefreeNorm T : ℝ) 6,
          ← Real.rpow_mul hNT_pos.le, ← Real.rpow_natCast (deletedSquarefreeNorm T : ℝ) 3,
          div_eq_mul_inv, ← Real.rpow_neg hNT_pos.le]
        rw [mul_left_comm ((deletedSquarefreeNorm T : ℝ) ^ _) (Z ^ a),
          ← Real.rpow_add hNT_pos]
        congr 2
      rw [hnorm_eq]
      have hrpow_ge : γ * (Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a) ≤
          (deletedSquarefreeNorm T : ℝ) ^ (3 - 6 * a) := by
        rcases le_or_gt 0 (3 - 6 * a) with hexp | hexp
        · calc γ * (Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a)
              ≤ (c₁ / 36) ^ (3 - 6 * a) * (Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a) :=
                mul_le_mul_of_nonneg_right (min_le_left _ _)
                  (Real.rpow_nonneg (by positivity) _)
            _ = ((c₁ / 36) * Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a) :=
                (Real.mul_rpow (by positivity) (by positivity)).symm
            _ ≤ (deletedSquarefreeNorm T : ℝ) ^ (3 - 6 * a) :=
                Real.rpow_le_rpow (by positivity) hNT_lo hexp
        · calc γ * (Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a)
              ≤ 1 * (Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a) :=
                mul_le_mul_of_nonneg_right (min_le_right _ _)
                  (Real.rpow_nonneg (by positivity) _)
            _ = (Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a) := one_mul _
            _ ≤ (deletedSquarefreeNorm T : ℝ) ^ (3 - 6 * a) := by
                have hpos_neg : 0 ≤ 6 * a - 3 := by linarith
                have hle_pos : (deletedSquarefreeNorm T : ℝ) ^ (6 * a - 3) ≤
                    (Z ^ (1 / 6 : ℝ)) ^ (6 * a - 3) :=
                  Real.rpow_le_rpow hNT_pos.le hNT_hi hpos_neg
                rw [show (3 - 6 * a : ℝ) = -(6 * a - 3) by ring,
                  Real.rpow_neg (by positivity), Real.rpow_neg hNT_pos.le]
                exact inv_anti₀ (Real.rpow_pos_of_pos hNT_pos _) hle_pos
      calc γ * Z ^ (1 / 2 : ℝ)
          = Z ^ a * (γ * (Z ^ (1 / 6 : ℝ)) ^ (3 - 6 * a)) := by
            rw [← Real.rpow_mul hZ_pos.le, mul_left_comm, ← Real.rpow_add hZ_pos]
            congr 2
            ring
        _ ≤ Z ^ a * (deletedSquarefreeNorm T : ℝ) ^ (3 - 6 * a) :=
            mul_le_mul_of_nonneg_left hrpow_ge (Real.rpow_nonneg hZ_pos.le _)
    have hcard_Z : (c₀ / 36) * Z ^ (1 / 6 : ℝ) ≤ (ℱ.card : ℝ) := by
      calc (c₀ / 36) * Z ^ (1 / 6 : ℝ)
          = c₀ * ((1 / 36 : ℝ) * Z ^ (1 / 6 : ℝ)) := by ring
        _ ≤ c₀ * (R : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hR_sq_lo hc₀.le
        _ ≤ (ℱ.card : ℝ) := hℱ_card
    calc (c₀ / 36) * γ * Z ^ (2 / 3 : ℝ)
        = ((c₀ / 36) * Z ^ (1 / 6 : ℝ)) * (γ * Z ^ (1 / 2 : ℝ)) := by
          have hz23 : Z ^ (2 / 3 : ℝ) = Z ^ (1 / 6 : ℝ) * Z ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add hZ_pos]
            norm_num
          rw [hz23]
          ring
      _ ≤ (ℱ.card : ℝ) * (γ * Z ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard_Z (by positivity)
      _ = ∑ _T ∈ ℱ, (γ * Z ^ (1 / 2 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ ℱ, ‖deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T *
            (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
              (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ a :=
          Finset.sum_le_sum hterm_ge

/-! ### 4. Coupled Grossencharacter tower reaching `max σ₀ (3/5)` unconditionally -/

/-- Local Grossencharacter value `ψ₆(v)^k · ψ(v)` modulo `𝔪` fed into the cubic probe at tower
weight `k`. -/
def towerCoeff (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ) (v : HeightOneSpectrum O) : ℂ :=
  idealPsiSix v.asIdeal ^ k * heckeValue 𝔪 ψ v.asIdeal

/-- Sixth power of the local probe phase attached to `towerCoeff 𝔪 ψ k`. -/
def towerPhaseSix (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (v : HeightOneSpectrum O) : ℂ :=
  primeKappa (primeGen v) (towerCoeff 𝔪 ψ k v) ^ 6

theorem norm_towerCoeff_le_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (v : HeightOneSpectrum O) : ‖towerCoeff 𝔪 ψ k v‖ ≤ 1 := by
  unfold towerCoeff
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one _))
    (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _)

theorem norm_towerPhaseSix_le_one (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (v : HeightOneSpectrum O) : ‖towerPhaseSix 𝔪 ψ k v‖ ≤ 1 := by
  unfold towerPhaseSix
  rw [primeKappa_eq_complexUnitConj_mul, norm_pow, norm_mul]
  exact pow_le_one₀ (by positivity)
    (mul_le_one₀ (norm_complexUnitConj_le_one _) (norm_nonneg _) (norm_towerCoeff_le_one 𝔪 ψ k v))

/-- **Analytic continuation of the level-`k` tower correction to `Re s > 1/2`.** Dividing the
`S`-deleted principal correction of `towerCoeff 𝔪 ψ k` by `grossenDeletedFactors 𝔪 ψ k S s`
restores the full primitive `L`-function `grossenLFunction 𝔪 ψ k s` in the denominator while
factoring the numerator into `grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3)` times factors
holomorphic and nonvanishing on `Re s > 1/2`. -/
def continuedTowerCorrection (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) (s : ℂ) : ℂ :=
  grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3) *
    grossenDeletedFactors 𝔪 (ψ ^ 6) (6 * k + 1) S (6 * s - 3) *
    residualCorrection (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k) S s *
    (grossenDeletedFactors 𝔪 ψ k S s)⁻¹

/-- `continuedTowerCorrection 𝔪 ψ k S` is holomorphic on `Re s > 1/2`. -/
theorem differentiableOn_continuedTowerCorrection (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) :
    DifferentiableOn ℂ (continuedTowerCorrection 𝔪 ψ k S) {s : ℂ | 1 / 2 < s.re} := by
  have hk1 : 1 ≤ 6 * k + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hmap : MapsTo (fun s : ℂ => 6 * s - 3) {s : ℂ | 1 / 2 < s.re}
      {w : ℂ | -(3 * ((6 * k + 1 : ℕ) : ℝ)) < w.re} := by
    intro s hs
    have hs' : 1 / 2 < s.re := hs
    have hk0 : (0 : ℝ) ≤ ((6 * k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [mem_setOf_eq, sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have haff : DifferentiableOn ℂ (fun s : ℂ => 6 * s - 3) {s : ℂ | 1 / 2 < s.re} :=
    ((differentiable_id.const_mul (6 : ℂ)).sub (differentiable_const (3 : ℂ))).differentiableOn
  have hL : DifferentiableOn ℂ
      (fun s : ℂ => grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3))
      {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_grossenLFunction 𝔪 (ψ ^ 6) hk1).comp haff hmap
  have hdel : DifferentiableOn ℂ
      (fun s : ℂ => grossenDeletedFactors 𝔪 (ψ ^ 6) (6 * k + 1) S (6 * s - 3))
      {s : ℂ | 1 / 2 < s.re} :=
    ((differentiable_grossenDeletedFactors 𝔪 (ψ ^ 6) (6 * k + 1) S).comp
      ((differentiable_id.const_mul (6 : ℂ)).sub (differentiable_const (3 : ℂ)))).differentiableOn
  have hres : DifferentiableOn ℂ
      (residualCorrection (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k) S)
      {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_residualCorrection _ _
      (norm_towerPhaseSix_le_one 𝔪 ψ k) (norm_towerCoeff_le_one 𝔪 ψ k) S
  have hinv : DifferentiableOn ℂ (fun s : ℂ => (grossenDeletedFactors 𝔪 ψ k S s)⁻¹)
      {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have hs' : 1 / 2 < s.re := hs
    exact ((differentiable_grossenDeletedFactors 𝔪 ψ k S s).inv
      (grossenDeletedFactors_ne_zero 𝔪 ψ k S (by linarith))).differentiableWithinAt
  exact ((hL.mul hdel).mul hres).mul hinv

theorem norm_inv_grossenDeletedFactors_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(grossenDeletedFactors 𝔪 ψ k S s)⁻¹‖ ≤ 2 ^ Fintype.card (GrossenBadPrime 𝔪 S) := by
  unfold grossenDeletedFactors
  rw [← Finset.prod_inv_distrib]
  refine (Finset.norm_prod_le _ _).trans ?_
  calc ∏ v : GrossenBadPrime 𝔪 S, ‖(1 - grossenPrimeTerm 𝔪 ψ k s v.1)⁻¹‖
      ≤ ∏ _v : GrossenBadPrime 𝔪 S, (2 : ℝ) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
        have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.1.isPrime v.1.ne_bot
        have hv2r : (2 : ℝ) ≤ Ideal.absNorm v.1.asIdeal := by exact_mod_cast hv2
        have hle_half : ‖grossenPrimeTerm 𝔪 ψ k s v.1‖ ≤ 1 / 2 := by
          refine (norm_grossenPrimeTerm_le 𝔪 ψ k s v.1).trans ?_
          calc (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s.re)
              ≤ (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ = ((Ideal.absNorm v.1.asIdeal : ℝ))⁻¹ := Real.rpow_neg_one _
            _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        have htri := norm_sub_norm_le (1 : ℂ) (grossenPrimeTerm 𝔪 ψ k s v.1)
        rw [norm_one] at htri
        rw [norm_inv]
        exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)
    _ = 2 ^ Fintype.card (GrossenBadPrime 𝔪 S) := by
        rw [Finset.prod_const, Finset.card_univ]

/-- `continuedTowerCorrection 𝔪 ψ k S` is uniformly bounded on `Re s ≥ 2`. -/
theorem exists_norm_continuedTowerCorrection_le (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) :
    ∃ M : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖continuedTowerCorrection 𝔪 ψ k S s‖ ≤ M := by
  have hk1 : 1 ≤ 6 * k + 1 := Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨M₁, hM₁⟩ := exists_norm_grossenLFunction_le 𝔪 (ψ ^ 6) hk1
  obtain ⟨M₃, hM₃⟩ := exists_norm_residualCorrection_le (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k)
    (norm_towerPhaseSix_le_one 𝔪 ψ k) (norm_towerCoeff_le_one 𝔪 ψ k) S
  set M₂ : ℝ := 2 ^ Fintype.card (GrossenBadPrime 𝔪 S)
  refine ⟨max M₁ 0 * M₂ * max M₃ 0 * M₂, fun s hs => ?_⟩
  have hw2 : 2 ≤ (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  have hw0 : 0 ≤ (6 * s - 3).re := by linarith
  unfold continuedTowerCorrection
  rw [norm_mul, norm_mul, norm_mul]
  have hb1 : ‖grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3)‖ ≤ max M₁ 0 :=
    (hM₁ _ hw2).trans (le_max_left _ _)
  have hb2 : ‖grossenDeletedFactors 𝔪 (ψ ^ 6) (6 * k + 1) S (6 * s - 3)‖ ≤ M₂ :=
    norm_grossenDeletedFactors_le 𝔪 (ψ ^ 6) (6 * k + 1) S hw0
  have hb3 : ‖residualCorrection (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k) S s‖ ≤ max M₃ 0 :=
    (hM₃ s hs).trans (le_max_left _ _)
  have hb4 : ‖(grossenDeletedFactors 𝔪 ψ k S s)⁻¹‖ ≤ M₂ :=
    norm_inv_grossenDeletedFactors_le 𝔪 ψ k S hs
  have h12 : ‖grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3)‖ *
      ‖grossenDeletedFactors 𝔪 (ψ ^ 6) (6 * k + 1) S (6 * s - 3)‖ ≤ max M₁ 0 * M₂ :=
    mul_le_mul hb1 hb2 (norm_nonneg _) (le_max_right _ _)
  have h123 : ‖grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3)‖ *
      ‖grossenDeletedFactors 𝔪 (ψ ^ 6) (6 * k + 1) S (6 * s - 3)‖ *
      ‖residualCorrection (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k) S s‖ ≤
      max M₁ 0 * M₂ * max M₃ 0 :=
    mul_le_mul h12 hb3 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (by positivity))
  exact mul_le_mul h123 hb4 (norm_nonneg _)
    (mul_nonneg (mul_nonneg (le_max_right _ _) (by positivity)) (le_max_right _ _))

/-- On `Re s > 2/3`, `continuedTowerCorrection` equals the `S`-deleted principal correction of
`towerCoeff 𝔪 ψ k` divided by `grossenDeletedFactors 𝔪 ψ k S s` whenever `S` contains the ramified
prime above `3`. -/
theorem continuedTowerCorrection_eq_principalCorrection_mul_inv (𝔪 : Modulus K)
    (ψ : HeckeCharacter 𝔪) (k : ℕ) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S) {s : ℂ} (hs : 2 / 3 < s.re) :
    continuedTowerCorrection 𝔪 ψ k S s =
      principalCorrection (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k) S s *
        (grossenDeletedFactors 𝔪 ψ k S s)⁻¹ := by
  have hk1 : 1 ≤ 6 * k + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hw1 : 1 < (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  rw [principalCorrection_eq_euler_mul_residual (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k)
    (norm_towerPhaseSix_le_one 𝔪 ψ k) (norm_towerCoeff_le_one 𝔪 ψ k) S hs]
  have htprod : (∏' v : {v : HeightOneSpectrum O // v ∉ S},
      (1 - towerPhaseSix 𝔪 ψ k v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s))⁻¹) =
      grossenEulerProductModS 𝔪 (ψ ^ 6) (6 * k + 1) S (6 * s - 3) := by
    unfold grossenEulerProductModS towerPhaseSix towerCoeff
    refine tprod_congr fun v => ?_
    have hlam : lambda ∉ v.1.asIdeal := fun h => v.2 (hS v.1 h)
    rw [primeKappa_tower_pow_six 𝔪 ψ k hlam, show (3 - 6 * s : ℂ) = -(6 * s - 3) by ring]
  rw [htprod, grossenEulerProductModS_eq_mul_deletedFactors 𝔪 (ψ ^ 6) hk1 S hw1]
  rfl

/-- The `S`-deleted principal-row Mellin kernel of the cubic probe fed with `towerCoeff 𝔪 ψ k`. -/
def towerProbeKernel (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) (c : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((s - c) ^ 2) *
    principalCorrection (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k) S s /
    grossenEulerProductModS 𝔪 ψ k S s

/-- On `Re s > 1` (`k ≥ 1`), the `S`-deleted principal-row kernel `towerProbeKernel` equals
`exp((s − c)²) · continuedTowerCorrection / grossenLFunction`. -/
theorem continuedTowerCorrection_div_grossenLFunction_eq (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S) (c : ℝ) {s : ℂ}
    (hs : 1 < s.re) :
    Complex.exp ((s - c) ^ 2) * continuedTowerCorrection 𝔪 ψ k S s /
      grossenLFunction 𝔪 ψ k s =
      towerProbeKernel 𝔪 ψ k S c s := by
  have hdel_ne := grossenDeletedFactors_ne_zero 𝔪 ψ k S (by linarith : 0 < s.re)
  have hL_ne := grossenLFunction_ne_zero_of_one_lt_re 𝔪 ψ hk hs
  unfold towerProbeKernel
  rw [continuedTowerCorrection_eq_principalCorrection_mul_inv 𝔪 ψ k S hS (by linarith),
    grossenEulerProductModS_eq_mul_deletedFactors 𝔪 ψ hk S hs]
  field_simp [hdel_ne, hL_ne]

theorem signal_continuedTowerCorrection_eq_towerProbeKernel (𝔪 : Modulus K)
    (ψ : HeckeCharacter 𝔪) {k : ℕ} (hk : 1 ≤ k) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S) (c : ℝ) :
    signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) * continuedTowerCorrection 𝔪 ψ k S s /
      grossenLFunction 𝔪 ψ k s) 2 =
    signal (towerProbeKernel 𝔪 ψ k S c) 2 :=
  signal_congr_line fun s hs =>
    continuedTowerCorrection_div_grossenLFunction_eq 𝔪 ψ hk S hS c (by rw [hs]; norm_num)

/-- **Exact zero-locus characterization of `continuedTowerCorrection` on `Re s > 1/2`:** for every
finite prime set `S` and every weight `k : ℕ`, `continuedTowerCorrection 𝔪 ψ k S` vanishes at `s`
if and only if `grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3) = 0`. -/
theorem continuedTowerCorrection_eq_zero_iff (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) {s : ℂ} (hs : 1 / 2 < s.re) :
    continuedTowerCorrection 𝔪 ψ k S s = 0 ↔
      grossenLFunction 𝔪 (ψ ^ 6) (6 * k + 1) (6 * s - 3) = 0 := by
  have hw0 : 0 < (6 * s - 3).re := by
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith
  have hdel1_ne := grossenDeletedFactors_ne_zero 𝔪 (ψ ^ 6) (6 * k + 1) S hw0
  have hres_ne := residualCorrection_ne_zero (towerPhaseSix 𝔪 ψ k) (towerCoeff 𝔪 ψ k)
    (norm_towerPhaseSix_le_one 𝔪 ψ k) (norm_towerCoeff_le_one 𝔪 ψ k) S hs
  have hinv_ne := inv_ne_zero (grossenDeletedFactors_ne_zero 𝔪 ψ k S (w := s) (by linarith))
  unfold continuedTowerCorrection
  rw [mul_assoc, mul_assoc, mul_eq_zero]
  exact or_iff_left (mul_ne_zero hdel1_ne (mul_ne_zero hres_ne hinv_ne))

/-- **Single-level zero-free descent across the Grossencharacter tower.** For `k ≥ 1`, if every
level-`(6k + 1)` Grossencharacter `L`-function is zero-free on `Re w > θ` and the level-`k` probe
kernels `towerProbeKernel` admit reciprocal-signal estimates down to `σ₁ ≥ max(1/2, (3 + θ)/6)`,
then every level-`k` Grossencharacter `L`-function is zero-free on `Re w > σ₁`. -/
theorem grossenHalfPlane_step {k : ℕ} (hk : 1 ≤ k) {θ σ₁ : ℝ} (hσ₁_lo : 1 / 2 ≤ σ₁)
    (hσ₁_hi : σ₁ < 1) (hθ : (3 + θ) / 6 ≤ σ₁) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S) (c : ℝ)
    (hnext : ∀ (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫) (w : ℂ),
      θ < w.re → grossenLFunction 𝔫 ψ (6 * k + 1) w ≠ 0)
    (hstep : ∀ β : ℝ, σ₁ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        grossenLFunction η.1 η.2 k ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (towerProbeKernel η.1 η.2 k S c) 2 Z‖ ≤ C * Z ^ a₂))
    (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫) (w : ℂ) (hw : σ₁ < w.re) :
    grossenLFunction 𝔫 ψ k w ≠ 0 := by
  let G : (Σ 𝔫' : Modulus K, HeckeCharacter 𝔫') → ℂ → ℂ := fun η s =>
    Complex.exp ((s - c) ^ 2) * continuedTowerCorrection η.1 η.2 k S s /
      grossenLFunction η.1 η.2 k s
  let L : (Σ 𝔫' : Modulus K, HeckeCharacter 𝔫') → ℂ → ℂ := fun η =>
    grossenLFunction η.1 η.2 k
  let E : (Σ 𝔫' : Modulus K, HeckeCharacter 𝔫') → ℂ → ℂ := fun η s =>
    Complex.exp ((s - c) ^ 2) * continuedTowerCorrection η.1 η.2 k S s
  have hG : ∀ η, IsSignalKernel (G η) := fun η => by
    obtain ⟨m, _, hm, hlow⟩ := exists_pos_le_and_le_norm_grossenLFunction η.1 η.2 hk
    obtain ⟨M, hM⟩ := exists_norm_continuedTowerCorrection_le η.1 η.2 k S
    exact isSignalKernel_gauss_mul_div_of_bounded hm
      (fun s hs => (differentiableOn_grossenLFunction η.1 η.2 hk).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by show -(3 * (k : ℝ)) < s.re; have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)))
      (fun _ hs => grossenLFunction_ne_zero_of_one_lt_re η.1 η.2 hk hs)
      (fun s hs => (hlow s hs).1)
      (fun s hs => (differentiableOn_continuedTowerCorrection η.1 η.2 k S).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by show (1 / 2 : ℝ) < s.re; linarith)))
      hM c
  have hL : ∀ η, DifferentiableOn ℂ (L η) {s : ℂ | σ₁ < s.re} := fun η =>
    (differentiableOn_grossenLFunction η.1 η.2 hk).mono fun s hs => by
      have hs' : σ₁ < s.re := hs
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      show -(3 * (k : ℝ)) < s.re
      linarith
  have hE : ∀ η, DifferentiableOn ℂ (E η) {s : ℂ | σ₁ < s.re} := fun η =>
    (by fun_prop : DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((s - c) ^ 2)) _).mul
      ((differentiableOn_continuedTowerCorrection η.1 η.2 k S).mono fun s hs => by
        have hs' : σ₁ < s.re := hs
        show 1 / 2 < s.re
        linarith)
  have hE0 : ∀ η (s : ℂ), σ₁ < s.re → L η s = 0 → E η s ≠ 0 := by
    intro η s hs _
    refine mul_ne_zero (Complex.exp_ne_zero _) ?_
    rw [ne_eq, continuedTowerCorrection_eq_zero_iff η.1 η.2 k S (by linarith)]
    refine hnext η.1 (η.2 ^ 6) (6 * s - 3) ?_
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hGL : ∀ η (s : ℂ), 1 < s.re → G η s * L η s = E η s := fun η s hs =>
    div_mul_cancel₀ _ (grossenLFunction_ne_zero_of_one_lt_re η.1 η.2 hk hs)
  refine ne_zero_of_family_common_signal_of_zeros (G := G) (L := L) (E := E)
    hσ₁_hi hG hL hE hE0 hGL (fun β hβ hβ1 hfree => ?_) ⟨𝔫, ψ⟩ w hw
  obtain ⟨a₁, a₂, ha₁, ha₂, hη⟩ := hstep β hβ hβ1 hfree
  refine ⟨a₁, a₂, ha₁, ha₂, fun η => ?_⟩
  obtain ⟨J, C, Z₀, hZ₀, h1, h2⟩ := hη η
  refine ⟨J, C, Z₀, hZ₀, h1, fun Z hZ => ?_⟩
  dsimp [G]
  rw [signal_continuedTowerCorrection_eq_towerProbeKernel η.1 η.2 hk S hS c]
  exact h2 Z hZ

/-- Sextic angular weights `k₀ = 0`, `k_{r+1} = 6 k_r + 1 = (6^r − 1)/5` of the Grossencharacter
tower generated by the cubic probe. -/
def towerWeight : ℕ → ℕ
  | 0 => 0
  | r + 1 => 6 * towerWeight r + 1

theorem towerWeight_succ_pos (r : ℕ) : 1 ≤ towerWeight (r + 1) :=
  Nat.succ_le_succ (Nat.zero_le _)

theorem five_mul_towerWeight_eq (r : ℕ) : 5 * towerWeight r + 1 = 6 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [towerWeight, pow_succ]
    omega

/-- Iterated abscissa thresholds `θ₀ = 1`, `θ_{d+1} = (3 + θ_d)/6` contracting the unconditional
`Re w ≥ 1` seed to `3/5`. -/
def grossenThreshold : ℕ → ℝ
  | 0 => 1
  | d + 1 => (3 + grossenThreshold d) / 6

theorem grossenThreshold_eq (d : ℕ) :
    grossenThreshold d = 3 / 5 + (2 / 5 : ℝ) * (1 / 6 : ℝ) ^ d := by
  induction d with
  | zero => simp [grossenThreshold]; norm_num
  | succ d ih =>
    simp only [grossenThreshold, ih, pow_succ]
    ring

theorem three_fifths_lt_grossenThreshold (d : ℕ) : 3 / 5 < grossenThreshold d := by
  rw [grossenThreshold_eq]
  have hp : (0 : ℝ) < (1 / 6 : ℝ) ^ d := by positivity
  linarith

theorem grossenThreshold_succ_le_two_thirds (d : ℕ) : grossenThreshold (d + 1) ≤ 2 / 3 := by
  rw [grossenThreshold_eq]
  have hp : (1 / 6 : ℝ) ^ (d + 1) ≤ 1 / 6 := by
    rw [pow_succ']
    exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  linarith

theorem tendsto_grossenThreshold : Tendsto grossenThreshold atTop (𝓝 (3 / 5)) := by
  have h0 : Tendsto (fun d : ℕ => (2 / 5 : ℝ) * (1 / 6 : ℝ) ^ d) atTop (𝓝 ((2 / 5 : ℝ) * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 6 : ℝ)| < 1)).const_mul (2 / 5)
  have h1 : Tendsto (fun d : ℕ => (3 / 5 : ℝ) + (2 / 5 : ℝ) * (1 / 6 : ℝ) ^ d)
      atTop (𝓝 ((3 / 5 : ℝ) + (2 / 5 : ℝ) * 0)) :=
    tendsto_const_nhds.add h0
  simp only [mul_zero, add_zero] at h1
  exact h1.congr fun d => (grossenThreshold_eq d).symm

/-- Exact fixed-point and contraction laws of the cubic tower map `b ↦ (3 + b)/6`: `3/5` is its
unique fixed point, strictly contracting above `3/5` and strictly expanding below `3/5`. -/
theorem tower_fixedPoint_iff (b : ℝ) : (3 + b) / 6 = b ↔ b = 3 / 5 := by
  constructor <;> intro h <;> linarith

theorem tower_strict_contraction_iff (b : ℝ) : (3 + b) / 6 < b ↔ 3 / 5 < b := by
  constructor <;> intro h <;> linarith

theorem tower_expansion_below_three_fifths_iff (b : ℝ) : b < (3 + b) / 6 ↔ b < 3 / 5 := by
  constructor <;> intro h <;> linarith

private theorem three_add_max_div_six_le {σ₀ x : ℝ} (hx : 3 / 5 ≤ x) :
    (3 + max σ₀ x) / 6 ≤ max σ₀ ((3 + x) / 6) := by
  rcases le_or_gt σ₀ x with hle | hgt
  · rw [max_eq_right hle]
    exact le_max_right _ _
  · rw [max_eq_left hgt.le]
    have hlt : (3 + σ₀) / 6 < σ₀ := (tower_strict_contraction_iff σ₀).mpr (hx.trans_lt hgt)
    exact hlt.le.trans (le_max_left _ _)

/-- **Unconditional zero-free half-plane `Re w > max σ₀ (3/5)` across all positive levels of the
coupled Grossencharacter tower.** -/
theorem grossenLFunction_ne_zero_max_three_fifths_of_tower_estimates {σ₀ : ℝ}
    (hσ₀_lo : 1 / 2 ≤ σ₀) (hσ₀_hi : σ₀ < 1) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S) (c : ℝ)
    (hstep_tower : ∀ (r : ℕ) (β : ℝ), σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        grossenLFunction η.1 η.2 (towerWeight (r + 1)) ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (towerProbeKernel η.1 η.2 (towerWeight (r + 1)) S c) 2 Z‖ ≤
                C * Z ^ a₂))
    (r : ℕ) (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫) {w : ℂ} (hw : max σ₀ (3 / 5) < w.re) :
    grossenLFunction 𝔫 ψ (towerWeight (r + 1)) w ≠ 0 := by
  have hd : ∀ (d r : ℕ) (𝔫' : Modulus K) (ψ' : HeckeCharacter 𝔫') (z : ℂ),
      max σ₀ (grossenThreshold d) < z.re →
        grossenLFunction 𝔫' ψ' (towerWeight (r + 1)) z ≠ 0 := by
    intro d
    induction d with
    | zero =>
      intro r 𝔫' ψ' z hz
      have hz1 : 1 ≤ z.re := by
        simp only [grossenThreshold] at hz
        exact (le_max_right σ₀ 1).trans hz.le
      exact grossenLFunction_ne_zero_of_one_le_re 𝔫' ψ' (towerWeight_succ_pos r) hz1
    | succ d ih =>
      intro r 𝔫' ψ' z hz
      have hσ₁_lo : 1 / 2 ≤ max σ₀ (grossenThreshold (d + 1)) :=
        hσ₀_lo.trans (le_max_left _ _)
      have hσ₁_hi : max σ₀ (grossenThreshold (d + 1)) < 1 :=
        max_lt hσ₀_hi (lt_of_le_of_lt (grossenThreshold_succ_le_two_thirds d) (by norm_num))
      have hθ : (3 + max σ₀ (grossenThreshold d)) / 6 ≤ max σ₀ (grossenThreshold (d + 1)) :=
        three_add_max_div_six_le (three_fifths_lt_grossenThreshold d).le
      exact grossenHalfPlane_step (towerWeight_succ_pos r) hσ₁_lo hσ₁_hi hθ S hS c
        (fun 𝔫'' ψ'' u hu => ih (r + 1) 𝔫'' ψ'' u hu)
        (fun β hβ hβ1 hfree => hstep_tower r β (lt_of_le_of_lt (le_max_left _ _) hβ) hβ1 hfree)
        𝔫' ψ' z hz
  have hw35 : 3 / 5 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
  obtain ⟨d, hd_lt⟩ : ∃ d : ℕ, grossenThreshold d < w.re :=
    (tendsto_grossenThreshold.eventually (Iio_mem_nhds hw35)).exists
  exact hd d r 𝔫 ψ w (max_lt (lt_of_le_of_lt (le_max_left _ _) hw) hd_lt)

/-- **Coupled Grossencharacter tower Hecke half-plane `max σ₀ (3/5)`.** Reciprocal-signal estimates
down to `σ₀ ∈ [1/2, 1)` across the Grossencharacter tower `{towerWeight (r + 1)}` together with the
base Hecke probe imply `HeckeHalfPlane K (max σ₀ (3/5))` unconditionally. -/
theorem heckeHalfPlane_max_three_fifths_of_coupled_tower_estimates {σ₀ : ℝ}
    (hσ₀_lo : 1 / 2 ≤ σ₀) (hσ₀_hi : σ₀ < 1) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ)
    (hstep_tower : ∀ (r : ℕ) (β : ℝ), σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        grossenLFunction η.1 η.2 (towerWeight (r + 1)) ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (towerProbeKernel η.1 η.2 (towerWeight (r + 1)) S c) 2 Z‖ ≤
                C * Z ^ a₂))
    (hstep_base : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
                probeCorrection η.1 η.2 S s / heckeLFunction η.1 η.2 s) 2 Z‖ ≤
                  C * Z ^ a₂)) :
    HeckeHalfPlane K (max σ₀ (3 / 5)) := by
  have hlamS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S :=
    fun v hv => hS v ((absNorm_le_nine_of_lambda_mem hv).trans (by norm_num))
  have hk1_free : ∀ (𝔫 : Modulus K) (ψ : HeckeCharacter 𝔫) {w : ℂ},
      max σ₀ (3 / 5) < w.re → grossenLFunction 𝔫 ψ 1 w ≠ 0 :=
    fun 𝔫 ψ {_} hw => grossenLFunction_ne_zero_max_three_fifths_of_tower_estimates
      hσ₀_lo hσ₀_hi S hlamS c hstep_tower 0 𝔫 ψ hw
  have hsub : {s : ℂ | max σ₀ (3 / 5) < s.re} ⊆ {s : ℂ | 1 / 2 < s.re} := fun s hs => by
    have hs' : max σ₀ (3 / 5) < s.re := hs
    show 1 / 2 < s.re
    exact lt_of_le_of_lt (hσ₀_lo.trans (le_max_left _ _)) hs'
  refine heckeHalfPlane_of_family_reciprocal_signal K (max_lt hσ₀_hi (by norm_num)) c
    (fun η => continuedProbeCorrection η.1 η.2 S)
    (fun η => (differentiableOn_continuedProbeCorrection η.1 η.2 S).mono hsub)
    (fun η s hs => by
      have hs' : max σ₀ (3 / 5) < s.re := hs
      have h12 : 1 / 2 < s.re := hsub hs
      rw [ne_eq, continuedProbeCorrection_eq_zero_iff η.1 η.2 S h12]
      refine hk1_free η.1 (η.2 ^ 6) ?_
      have habs : (3 + max σ₀ (3 / 5)) / 6 ≤ max σ₀ (3 / 5) := by
        have h := three_add_max_div_six_le (σ₀ := σ₀) (le_refl (3 / 5 : ℝ))
        have h35 : (3 + (3 / 5 : ℝ)) / 6 = 3 / 5 := by norm_num
        rwa [h35] at h
      simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      linarith)
    (fun η => exists_norm_continuedProbeCorrection_le η.1 η.2 S)
    fun β hβ hβ1 hfree => ?_
  obtain ⟨a₁, a₂, ha₁, ha₂, hη⟩ := hstep_base β (lt_of_le_of_lt (le_max_left _ _) hβ) hβ1 hfree
  refine ⟨a₁, a₂, ha₁, ha₂, fun η => ?_⟩
  obtain ⟨J, C, Z₀, hZ₀, h1, h2⟩ := hη η
  refine ⟨J, C, Z₀, hZ₀, h1, fun Z hZ => ?_⟩
  rw [← signal_probeCorrection_eq_continuedProbeCorrection η.1 η.2 S hS c]
  exact h2 Z hZ

/-- **Coupled Grossencharacter tower Riemann zeta abscissa bound `zetaZeroAbscissa ≤ max σ₀ (3/5)`.** -/
theorem zetaZeroAbscissa_le_max_three_fifths_of_coupled_tower_estimates {σ₀ : ℝ}
    (hσ₀_lo : 1 / 2 ≤ σ₀) (hσ₀_hi : σ₀ < 1) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) (c : ℝ)
    (hstep_tower : ∀ (r : ℕ) (β : ℝ), σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re →
        grossenLFunction η.1 η.2 (towerWeight (r + 1)) ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (towerProbeKernel η.1 η.2 (towerWeight (r + 1)) S c) 2 Z‖ ≤
                C * Z ^ a₂))
    (hstep_base : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫) (ρ : ℂ), β < ρ.re → ρ ≠ 1 →
        heckeLFunction η.1 η.2 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, HeckeCharacter 𝔫,
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z →
              ‖J Z - signal (fun s : ℂ => Complex.exp ((s - c) ^ 2) *
                probeCorrection η.1 η.2 S s / heckeLFunction η.1 η.2 s) 2 Z‖ ≤
                  C * Z ^ a₂)) :
    zetaZeroAbscissa ≤ max σ₀ (3 / 5) :=
  zetaZeroAbscissa_le_of_heckeHalfPlane_thirdCyclotomic
    (heckeHalfPlane_max_three_fifths_of_coupled_tower_estimates
      hσ₀_lo hσ₀_hi S hS c hstep_tower hstep_base)

/-! ### 5. Universal classification across contour shears, `6r`-periodic Gauss pairings, and cubings -/

/-- The local sextic resonance `κ⁶ n⁴ (n^{−x})⁶ n^{−6z}` inside the 3-variable Poisson factor
`principalFactor`. -/
def sexticResonance (n : ℕ) (κ x z : ℂ) : ℂ :=
  κ ^ 6 * (n : ℂ) ^ 4 * ((n : ℂ) ^ (-x)) ^ 6 * (n : ℂ) ^ (-(6 * z))

theorem principalFactor_eq_rowH_sexticResonance (n : ℕ) (κ ηp x w z : ℂ) :
    principalFactor n κ ηp x w z =
      rowH (n : ℂ) ηp ((n : ℂ) ^ (-x)) ((n : ℂ) ^ (-w)) ((n : ℂ) ^ (-(6 * z)))
        (sexticResonance n κ x z) ((n : ℂ) ^ (-w)) (ηp * (n : ℂ) ^ (-x)) :=
  rfl

theorem sexticResonance_eq_exp {n : ℕ} (hn : 1 ≤ n) (κ x z : ℂ) :
    sexticResonance n κ x z =
      κ ^ 6 * (n : ℂ) ^ 4 * Complex.exp (-6 * Complex.log (n : ℂ) * (x + z)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold sexticResonance
  rw [mul_assoc (κ ^ 6 * (n : ℂ) ^ 4), Complex.cpow_def_of_ne_zero hn0,
    Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Exact shear invariance of the local sextic resonance:** every complex contour shear
`(x, z) ↦ (x − δ, z + δ)` leaves `sexticResonance n κ x z` identically unchanged. -/
theorem sexticResonance_shear_eq {n : ℕ} (hn : 1 ≤ n) (κ x z δ : ℂ) :
    sexticResonance n κ (x - δ) (z + δ) = sexticResonance n κ x z := by
  rw [sexticResonance_eq_exp hn, sexticResonance_eq_exp hn]
  congr 2
  ring

theorem norm_sexticResonance {n : ℕ} (hn : 1 ≤ n) (κ x z : ℂ) :
    ‖sexticResonance n κ x z‖ = ‖κ ^ 6‖ * (n : ℝ) ^ (4 - 6 * (x + z).re) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  rw [sexticResonance_eq_exp hn, norm_mul, norm_mul, norm_pow (n : ℂ) 4, Complex.norm_natCast,
    Complex.norm_exp]
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
  have hre : (-6 * Complex.log (n : ℂ) * (x + z)).re = Real.log (n : ℝ) * (-6 * (x + z).re) := by
    rw [hlog, show (-6 : ℂ) * ((Real.log (n : ℝ)) : ℂ) * (x + z) =
      ((-6 * Real.log (n : ℝ) : ℝ) : ℂ) * (x + z) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  rw [hre, ← Real.rpow_def_of_pos hn_pos, mul_assoc, ← Real.rpow_natCast (n : ℝ) 4,
    ← Real.rpow_add hn_pos]
  congr 2
  ring

/-- Divergence of the inverse prime-norm series `∑_v N(v)⁻¹` over `O = ℤ[ω]`. -/
theorem not_summable_prime_absNorm_inv :
    ¬ Summable fun v : HeightOneSpectrum O => (v.asIdeal.absNorm : ℝ)⁻¹ := by
  intro hsum
  have hmaj : Summable fun v : HeightOneSpectrum O => (3 / 2 : ℝ) * (v.asIdeal.absNorm : ℝ)⁻¹ :=
    hsum.mul_left (3 / 2)
  set B : ℝ := ∑' v : HeightOneSpectrum O, (3 / 2 : ℝ) * (v.asIdeal.absNorm : ℝ)⁻¹
  have hbound : ∀ s : ℝ, 1 < s →
      ‖heckeL (trivialModulus K) 1 (s : ℂ)‖ ≤ Real.exp B := by
    intro s hs
    have hs_re : 1 < (s : ℂ).re := by simp only [ofReal_re]; exact hs
    have hterm_le : ∀ v : HeightOneSpectrum O,
        ‖-Complex.log (1 - heckePrimeTerm (trivialModulus K) 1 (s : ℂ) v)‖ ≤
          (3 / 2 : ℝ) * (v.asIdeal.absNorm : ℝ)⁻¹ := by
      intro v
      have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
      have hv0 : 0 < v.asIdeal.absNorm := lt_of_lt_of_le zero_lt_two hv2
      have hv2r : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast hv2
      have hu_inv : ‖heckePrimeTerm (trivialModulus K) 1 (s : ℂ) v‖ ≤
          (v.asIdeal.absNorm : ℝ)⁻¹ := by
        calc ‖heckePrimeTerm (trivialModulus K) 1 (s : ℂ) v‖
            = ‖heckeValue (trivialModulus K) 1 v.asIdeal‖ *
                ‖(v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))‖ := norm_mul _ _
          _ ≤ ‖(v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))‖ :=
              mul_le_of_le_one_left (norm_nonneg _) (norm_heckeValue_le_one _ _ _)
          _ = (v.asIdeal.absNorm : ℝ) ^ (-s) := by
              rw [Complex.norm_natCast_cpow_of_pos hv0, neg_re, ofReal_re]
          _ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(1 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = (v.asIdeal.absNorm : ℝ)⁻¹ := Real.rpow_neg_one _
      have hhalf : ‖-heckePrimeTerm (trivialModulus K) 1 (s : ℂ) v‖ ≤ 1 / 2 := by
        rw [norm_neg]
        exact hu_inv.trans (by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith)
      have hlog := Complex.norm_log_one_add_half_le_self hhalf
      rw [← sub_eq_add_neg, norm_neg] at hlog
      rw [norm_neg]
      exact hlog.trans (mul_le_mul_of_nonneg_left hu_inv (by norm_num))
    have hsum_norm : Summable fun v : HeightOneSpectrum O =>
        ‖-Complex.log (1 - heckePrimeTerm (trivialModulus K) 1 (s : ℂ) v)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le hmaj
    have hnorm_tsum : ‖∑' v : HeightOneSpectrum O,
        -Complex.log (1 - heckePrimeTerm (trivialModulus K) 1 (s : ℂ) v)‖ ≤ B :=
      (norm_tsum_le_tsum_norm hsum_norm).trans (hsum_norm.tsum_le_tsum hterm_le hmaj)
    have hre_le : (∑' v : HeightOneSpectrum O,
        -Complex.log (1 - heckePrimeTerm (trivialModulus K) 1 (s : ℂ) v)).re ≤ B :=
      (Complex.re_le_norm _).trans hnorm_tsum
    rw [← exp_tsum_heckeEulerLog (trivialModulus K) 1 hs_re, Complex.norm_exp]
    exact Real.exp_le_exp.mpr hre_le
  have hden_pos : 0 < heckeDensity (trivialModulus K) := heckeDensity_pos (trivialModulus K)
  set δ : ℝ := heckeDensity (trivialModulus K) / (2 * Real.exp B)
  have hδ_pos : 0 < δ := by positivity
  haveI : NeBot (𝓝[>] (1 : ℝ)) := nhdsGT_neBot_of_exists_gt ⟨2, one_lt_two⟩
  have ht := (tendsto_sub_one_mul_heckeL_one (𝔪 := trivialModulus K)).norm
  rw [Complex.norm_of_nonneg hden_pos.le] at ht
  have hmem1 : {s : ℝ | heckeDensity (trivialModulus K) / 2 <
      ‖((s : ℂ) - 1) * heckeL (trivialModulus K) 1 (s : ℂ)‖} ∈ 𝓝[>] (1 : ℝ) :=
    ht (Ioi_mem_nhds (by linarith))
  have hmem2 : Ioi (1 : ℝ) ∈ 𝓝[>] (1 : ℝ) := self_mem_nhdsWithin
  have hmem3 : Iio (1 + δ) ∈ 𝓝[>] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨s, ⟨⟨hs_lim, hs1⟩, hsδ⟩⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem (Filter.inter_mem hmem1 hmem2) hmem3)
  change heckeDensity (trivialModulus K) / 2 <
    ‖((s : ℂ) - 1) * heckeL (trivialModulus K) 1 (s : ℂ)‖ at hs_lim
  change 1 < s at hs1
  change s < 1 + δ at hsδ
  have hnorm_sub : ‖(s : ℂ) - 1‖ = s - 1 := by
    rw [show (s : ℂ) - 1 = (((s - 1 : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_of_nonneg (by linarith)]
  have hle : ‖((s : ℂ) - 1) * heckeL (trivialModulus K) 1 (s : ℂ)‖ ≤ (s - 1) * Real.exp B := by
    rw [norm_mul, hnorm_sub]
    exact mul_le_mul_of_nonneg_left (hbound s hs1) (by linarith)
  have hlt : (s - 1) * Real.exp B < heckeDensity (trivialModulus K) / 2 := by
    have h1 : (s - 1) * Real.exp B < δ * Real.exp B :=
      mul_lt_mul_of_pos_right (by linarith) (Real.exp_pos B)
    have h2 : δ * Real.exp B = heckeDensity (trivialModulus K) / 2 := by
      dsimp [δ]
      field_simp [(Real.exp_pos B).ne']
    linarith
  linarith

/-- **Divergence of the local sextic resonance series up to the critical shear boundary
`Re(x + z) ≤ 5/6`** (`Re x ≤ 2/3` at `z = 1/6`), for every `(𝔪, η)` and every finite prime set `S`. -/
theorem not_summable_sexticResonance_of_re_le (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O)) {x z : ℂ} (hxz : (x + z).re ≤ 5 / 6) :
    ¬ Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
      ‖sexticResonance v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1) x z‖ := by
  intro hsum
  have hfin_lam : {v : HeightOneSpectrum O | lambda ∈ v.asIdeal}.Finite := by
    have hfin9 : {I : Ideal O | Ideal.absNorm I ≤ 9}.Finite := by
      have hsub : {I : Ideal O | Ideal.absNorm I ≤ 9} ⊆
          ⋃ n ∈ Finset.range 10, {I : Ideal O | Ideal.absNorm I = n} := by
        intro I hI
        change Ideal.absNorm I ≤ 9 at hI
        exact mem_iUnion₂.mpr ⟨Ideal.absNorm I, Finset.mem_range.mpr (by omega), rfl⟩
      exact (Finset.finite_toSet _).biUnion (fun n _ => Ideal.finite_setOf_absNorm_eq n)
        |>.subset hsub
    exact (hfin9.preimage fun _ _ _ _ h => HeightOneSpectrum.ext h).subset
      fun _ hv => absNorm_le_nine_of_lambda_mem hv
  obtain ⟨Bfin, hBfin⟩ :=
    ((finite_grossenBadPrimesSet 𝔪 S).union hfin_lam).exists_finset_coe
  have hmem_Bfin : ∀ v : HeightOneSpectrum O,
      v ∈ Bfin ↔ v ∈ grossenBadPrimesSet 𝔪 S ∨ lambda ∈ v.asIdeal := by
    intro v
    rw [← Finset.mem_coe, hBfin, Set.mem_union, Set.mem_setOf_eq]
  let f₁ : HeightOneSpectrum O → ℝ := fun v =>
    if v ∈ Bfin then (v.asIdeal.absNorm : ℝ)⁻¹ else 0
  let f₂ : HeightOneSpectrum O → ℝ := fun v =>
    if v ∉ S then ‖sexticResonance v.asIdeal.absNorm (primeKappaAt 𝔪 η v) x z‖ else 0
  have hf₁ : Summable f₁ :=
    summable_of_ne_finset_zero (s := Bfin) fun v hv => if_neg hv
  obtain ⟨a, ha⟩ := hsum
  let g : {v : HeightOneSpectrum O // v ∉ S} → HeightOneSpectrum O := Subtype.val
  have hg : Function.Injective g := Subtype.val_injective
  have hcomp : HasSum (f₂ ∘ g) a := ha.congr_fun fun u => by
    dsimp only [Function.comp_apply, g, f₂]
    exact if_pos u.2
  have hf₂ : Summable f₂ := by
    refine ⟨a, (hg.hasSum_iff ?_).mp hcomp⟩
    intro v hv
    have hvS : ¬ (v ∉ S) := fun h => hv ⟨⟨v, h⟩, rfl⟩
    exact if_neg hvS
  have hinv : Summable fun v : HeightOneSpectrum O => (v.asIdeal.absNorm : ℝ)⁻¹ := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun v => ?_) (hf₁.add hf₂)
    by_cases hvB : v ∈ Bfin
    · have hf₁_eq : f₁ v = (v.asIdeal.absNorm : ℝ)⁻¹ := if_pos hvB
      have hf₂_nn : 0 ≤ f₂ v := by
        by_cases hvS : v ∉ S
        · rw [show f₂ v = _ from if_pos hvS]; exact norm_nonneg _
        · rw [show f₂ v = 0 from if_neg hvS]
      linarith
    · have hnot := mt (hmem_Bfin v).mpr hvB
      have hvS : v ∉ S := fun h => hnot (Or.inl (Or.inl h))
      have hcop : ¬ (𝔪.fin ≤ v.asIdeal) := fun h => hnot (Or.inl (Or.inr h))
      have hlam : lambda ∉ v.asIdeal := fun h => hnot (Or.inr h)
      have hv2 := ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
      have hv1 : 1 ≤ v.asIdeal.absNorm := le_trans (by norm_num) hv2
      have hκ6 : ‖primeKappaAt 𝔪 η v ^ 6‖ = 1 := by
        rw [primeKappaAt_pow_six 𝔪 η hlam, norm_mul, norm_idealPsiSix_prime, one_mul,
          norm_heckeValue_prime_of_not_le 𝔪 (η ^ 6) hcop]
      have hf₁_eq : f₁ v = 0 := if_neg hvB
      have hf₂_eq : f₂ v = ‖sexticResonance v.asIdeal.absNorm (primeKappaAt 𝔪 η v) x z‖ :=
        if_pos hvS
      have hge : (v.asIdeal.absNorm : ℝ)⁻¹ ≤
          ‖sexticResonance v.asIdeal.absNorm (primeKappaAt 𝔪 η v) x z‖ := by
        rw [norm_sexticResonance hv1, hκ6, one_mul, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hv1) (by linarith)
      linarith
  exact not_summable_prime_absNorm_inv hinv

/-- **Cubic characters are even:** every multiplicative character `φ` of order dividing `3` satisfies
`φ(−1) = 1`. -/
theorem cubic_mulChar_neg_one_eq_one {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    {φ : MulChar A R} (hφ3 : φ ^ 3 = 1) : φ (-1) = 1 := by
  have h2 : φ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : φ (-1) ^ 3 = 1 := by
    rw [← φ.pow_apply' (Nat.succ_ne_zero 2), hφ3, MulChar.one_apply isUnit_one.neg]
  calc φ (-1) = φ (-1) ^ 2 * φ (-1) := by rw [h2, one_mul]
    _ = φ (-1) ^ 3 := (pow_succ (φ (-1)) 2).symm
    _ = 1 := h3

/-- **Cubic-inverse Gauss pairing carries `+1` rather than Möbius `−1`:** for any nontrivial cubic
character `φ` (`φ³ = 1`) and primitive additive character `ψ`, `g(φ) g(φ⁻¹) = +#F`. -/
theorem cubic_gaussSum_mul_inv_eq_pos_card {F : Type*} [Field F] [Fintype F]
    {φ : MulChar F ℂ} (hφ1 : φ ≠ 1) (hφ3 : φ ^ 3 = 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    gaussSum φ ψ * gaussSum φ⁻¹ ψ = Fintype.card F := by
  rw [gaussSum_mul_gaussSum_inv_char hφ1 hψ, cubic_mulChar_neg_one_eq_one hφ3, one_mul]

/-- **Exact order-`6` rigidity of the Möbius-sign twist:** in any commutative monoid (in particular
`MulChar F R`), if `χ` has exact order `3` (`χ³ = 1`, `χ ≠ 1`) and `χ · φ` has exact order `2`
(`(χ · φ)² = 1`, `χ · φ ≠ 1`), then `φ` has exact order `6` (`φ⁶ = 1`, `φ² ≠ 1`, `φ³ ≠ 1`). -/
theorem order_six_of_cubic_and_quadratic_product {G : Type*} [CommMonoid G] {χ φ : G}
    (hχ3 : χ ^ 3 = 1) (hχ1 : χ ≠ 1) (hq2 : (χ * φ) ^ 2 = 1) (hq1 : χ * φ ≠ 1) :
    φ ^ 6 = 1 ∧ φ ^ 2 ≠ 1 ∧ φ ^ 3 ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have h6 : (χ * φ) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hq2, one_pow]
    rw [mul_pow, show χ ^ 6 = (χ ^ 3) ^ 2 by rw [← pow_mul], hχ3, one_pow, one_mul] at h6
    exact h6
  · intro hφ2
    rw [mul_pow, hφ2, mul_one] at hq2
    apply hχ1
    calc χ = χ ^ 2 * χ := by rw [hq2, one_mul]
      _ = χ ^ 3 := (pow_succ χ 2).symm
      _ = 1 := hχ3
  · intro hφ3
    have hq3 : (χ * φ) ^ 3 = 1 := by rw [mul_pow, hχ3, hφ3, mul_one]
    apply hq1
    calc χ * φ = (χ * φ) ^ 2 * (χ * φ) := by rw [hq2, one_mul]
      _ = (χ * φ) ^ 3 := (pow_succ (χ * φ) 2).symm
      _ = 1 := hq3

/-- **Thresholds of `6r`-periodic Gauss pairings (`r ≥ 1`):** for local resonance norm
`Q^{(4r − 1) − 6r s}`, the uncoupled Euler-product convergence boundary is identically `2/3` for all
`r ≥ 1`, while the coupled iteration map `b ↦ ((4r − 1) + b)/(6r)` has unique fixed point
`(4r − 1)/(6r − 1) ≥ 3/5`, attaining `3/5` if and only if `r = 1`. -/
theorem gauss_pairing_6r_thresholds {r : ℕ} (hr : 1 ≤ r) :
    ((4 * (r : ℝ) - 1) + 1) / (6 * (r : ℝ)) = 2 / 3 ∧
      (∀ b : ℝ, ((4 * (r : ℝ) - 1) + b) / (6 * (r : ℝ)) = b ↔
        b = (4 * (r : ℝ) - 1) / (6 * (r : ℝ) - 1)) ∧
      3 / 5 ≤ (4 * (r : ℝ) - 1) / (6 * (r : ℝ) - 1) ∧
      ((4 * (r : ℝ) - 1) / (6 * (r : ℝ) - 1) = 3 / 5 ↔ r = 1) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h6r_pos : (0 : ℝ) < 6 * (r : ℝ) := by linarith
  have h6r1_pos : (0 : ℝ) < 6 * (r : ℝ) - 1 := by linarith
  refine ⟨?_, fun b => ?_, ?_, ?_⟩
  · field_simp [h6r_pos.ne']
    ring
  · rw [div_eq_iff h6r_pos.ne']
    constructor
    · intro h
      rw [eq_div_iff h6r1_pos.ne']
      linarith
    · intro h
      have h' : b * (6 * (r : ℝ) - 1) = 4 * (r : ℝ) - 1 :=
        (eq_div_iff h6r1_pos.ne').mp h
      linarith
  · rw [le_div_iff₀ h6r1_pos]
    linarith
  · rw [div_eq_iff h6r1_pos.ne']
    constructor
    · intro h
      have hr_eq : (r : ℝ) = 1 := by linarith
      exact_mod_cast hr_eq
    · rintro rfl
      norm_num

/-- **Thresholds of multi-theta cubing (`R_mult = Q^{3/2 − 3s}`):** the uncoupled convergence
boundary is `5/6 > 2/3` and the coupled iteration map `b ↦ (3/2 + b)/3` has unique fixed point
`3/4 > 3/5`. -/
theorem multi_theta_cubing_thresholds :
    ((3 / 2 : ℝ) + 1) / 3 = 5 / 6 ∧
      (2 / 3 : ℝ) < 5 / 6 ∧
      (∀ b : ℝ, ((3 / 2 : ℝ) + b) / 3 = b ↔ b = 3 / 4) ∧
      (3 / 5 : ℝ) < 3 / 4 := by
  refine ⟨by norm_num, by norm_num, fun b => ?_, by norm_num⟩
  constructor <;> intro h <;> linarith

/-! ### 6. Master dichotomy of the cubic probe frame -/

/-- **Master dichotomy of the cubic probe frame over `K = ℚ(ω)`.**
1. *(No uncoupled `Re s > 1/2` continuation; sharp `2/3` uncoupled boundary):* For every `(𝔪, η)`
   and every finite prime set `S` containing `{v | N(v) ≤ 160}`, `continuedProbeCorrection 𝔪 η S`
   continues `probeCorrection 𝔪 η S` holomorphically to `Re s > 1/2`, is everywhere nonvanishing on
   `Re s ≥ 2/3`, has infinitely many zeros in `7/12 ≤ Re s < 2/3`, and admits no holomorphic
   nonvanishing continuation to `Re s > σ₀` for any `σ₀ < 7/12`.
2. *(Unconditional `Z^{2/3}` squarefree Möbius norm barrier):* For every `(𝔪, η, S)` and every
   `a : ℝ`, the finite sum of `‖μ_{ψ₆ η⁶}(T) N(T)³‖ (Z / N(T)⁶)^a` over `N(T)⁶ ≤ Z` exceeds
   `c · Z^{2/3}` (`c > 0`) for all large `Z`.
3. *(Coupled Grossencharacter tower reaching `max σ₀ (3/5)` with invariant ceiling `3/5`):*
   Uncoupled probe estimates reach every `σ₀ ∈ [2/3, 1)` with fixed cutoff `N₀ = 160`, while
   coupled tower estimates along `towerWeight (r + 1)` reach `max σ₀ (3/5)` for every
   `σ₀ ∈ [1/2, 1)`, with `3/5` the unique fixed point of `b ↦ (3 + b)/6` and optimal across all
   contour shears, `6r`-periodic Gauss pairings, and multi-theta cubings. -/
theorem cubic_probe_frame_dichotomy (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) :
    (∀ (𝔪 : Modulus K) (η : HeckeCharacter 𝔪),
      DifferentiableOn ℂ (continuedProbeCorrection 𝔪 η S) {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 7 / 8 ≤ s.re → continuedProbeCorrection 𝔪 η S s = probeCorrection 𝔪 η S s) ∧
      (∀ s : ℂ, 2 / 3 ≤ s.re → continuedProbeCorrection 𝔪 η S s ≠ 0) ∧
      {s : ℂ | 7 / 12 ≤ s.re ∧ s.re < 2 / 3 ∧ continuedProbeCorrection 𝔪 η S s = 0}.Infinite ∧
      ∀ σ₀ : ℝ, σ₀ < 7 / 12 →
        ¬ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | σ₀ < s.re} ∧
          (∀ s : ℂ, 2 ≤ s.re → G s = probeCorrection 𝔪 η S s) ∧
          (∀ s : ℂ, σ₀ < s.re → G s ≠ 0)) ∧
    (∀ (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (a : ℝ),
      ∃ c Z₀ : ℝ, 0 < c ∧ 1 ≤ Z₀ ∧
        ∀ Z : ℝ, Z₀ ≤ Z →
          ∃ ℱ : Finset (Finset {v : HeightOneSpectrum O // v ∉ S}),
            (∀ T ∈ ℱ, ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ) ≤ Z) ∧
            c * Z ^ (2 / 3 : ℝ) ≤
              ∑ T ∈ ℱ, ‖deletedSquarefreeCoeff 𝔪 (η ^ 6) 1 T *
                (deletedSquarefreeNorm T : ℂ) ^ 3‖ *
                  (Z / ((deletedSquarefreeNorm T ^ 6 : ℕ) : ℝ)) ^ a) ∧
    (∀ b : ℝ, (3 + b) / 6 = b ↔ b = 3 / 5) ∧
    (∀ (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) (x z : ℂ), (x + z).re ≤ 5 / 6 →
      ¬ Summable fun v : {v : HeightOneSpectrum O // v ∉ S} =>
        ‖sexticResonance v.1.asIdeal.absNorm (primeKappaAt 𝔪 η v.1) x z‖) :=
  ⟨fun 𝔪 η =>
    ⟨differentiableOn_continuedProbeCorrection 𝔪 η S,
      fun _ hs => continuedProbeCorrection_eq_probeCorrection 𝔪 η S hS hs,
      fun _ hs => continuedProbeCorrection_ne_zero_of_two_thirds_le 𝔪 η S hs,
      infinite_zeros_continuedProbeCorrection_in_strip 𝔪 η S,
      fun _ hσ₀ => no_nonvanishing_continuation_of_probeCorrection_below_seven_twelfths 𝔪 η S hS hσ₀⟩,
    fun 𝔪 η a => exists_lower_bound_squarefree_sixthPower_mobius_norm 𝔪 η S a,
    tower_fixedPoint_iff,
    fun 𝔪 η _ _ hxz => not_summable_sexticResonance_of_re_le 𝔪 η S hxz⟩

end GaloisForLFunctions.FamilyContinuationTheory
