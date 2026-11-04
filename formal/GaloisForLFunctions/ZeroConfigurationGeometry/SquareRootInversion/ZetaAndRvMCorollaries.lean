import GaloisForLFunctions.ZeroConfigurationGeometry.SquareRootInversion.SubSpacingLocalInversion
import GaloisForLFunctions.ZeroConfigurationGeometry.SquareRootInversion.ShiftedHalfLatticeCounterexample
import GaloisForLFunctions.ZeroConfigurationGeometry.ZetaZerosHaveTheSharpLocalDensity

/-!
# Riemann–von Mangoldt and `ζ` Corollaries of Sub-Spacing Local Inversion

This module specializes the quantitative sub-spacing local camera
(`SubSpacingLocalInversion`) and the shifted half-lattice counterexample
(`ShiftedHalfLatticeCounterexample`) to configurations with Riemann–von Mangoldt local counts
(excess `O(log T)`) and to `zetaZeroConfig` itself, giving a complete resolution of Route ZCG
Question 2.5.5 (`obstacles-summary.md:509–520`):

1. **Automatic temperedness and tail bound from unit-window counts**
   (`temperedConfig_and_tsum_le_of_unit_window_count`, `tsum_multDiff_le_of_unit_window_counts`).
   Any configuration satisfying `Z.N t (t + 1) ≤ A₀ log(|t| + 3)` for all `t ∈ ℝ` is automatically
   `TemperedConfig Z` with explicit global tail `≤ 4 max(A₀, 1) · totalWeight`, removing any
   separate global tail parameter `S`.
2. **Riemann–von Mangoldt local-count configurations** (`HasRvMLocalCount`, `rvmMainTerm_sub_le`,
   `hasRvMLocalCount_of_prefix_rvm`, `exists_hasRvMLocalCount_zeta`).
   Both prefix RvM asymptotics `|Z.N 0 t − (t / 2π)(log(t / 2π) − 1)| ≤ C log t` and the actual
   zeros `zetaZeroConfig` satisfy `HasRvMLocalCount` unconditionally.
3. **Complete resolution of Question 2.5.5** (`rvm_pair_coincide_outside_nearCollisions_above_one`,
   `rvm_coincide_of_extra_density_littleO`, `rvm_subset_carrier_coincide_at_squareRoot_littleO`,
   `rvm_local_inversion_dichotomy`):
   * For `0 < λ ≤ 1` (including the entire posed interval `½ < λ ≤ 1`), two critical-line simple
     RvM configurations with disjoint carriers and uniform gap `≥ π / log(T / 2π)` have identical
     Weil images on windows of aperture `λ · ½ log(T / 2π)`.
   * For every `λ > 1` (arbitrarily, with no carrier assumption), and for every `λ > ½` when one
     carrier contains the other near `T` (more generally `λ > (1 + μ) / 2` for extra-carrier
     density `μ`), two RvM configurations whose images agree on windows of aperture
     `λ · ½ log(T / 2π)` coincide with multiplicity across `|Im z − T| ≤ T / 4` outside
     near-collision clusters of diameter `< T^{−M}` (and hence `< δ / log T`, `o(1 / log T)`),
     uniformly in `T`.
4. **Unconditional `ζ` coincidence and single-zero multiplicity readout at `λ > ½`**
   (`zeta_coincide_of_extra_density_littleO`, `zeta_coincide_subset_carrier_at_squareRoot_littleO`,
   `zeta_coincide_with_rvm_above_one_littleO`,
   `zeta_isolated_zero_multiplicity_readout_at_squareRoot_rpow`,
   `zeta_isolated_zero_multiplicity_readout_at_squareRoot_littleO`).
   At the square-root threshold `λ > ½`, a single window pair of aperture `λ · ½ log(T / 2π)`
   unconditionally determines the exact integer multiplicity `zeroMult ρ₀` (within `1 / 4`, with
   `zetaZeroConfig.W F G ≠ 0`) of every `T^{−M}`- or `(δ / log T)`-isolated nontrivial zero `ρ₀`
   of `ζ` in `|Im ρ₀ − T| ≤ T / 4`.
-/

open MeasureTheory Complex Set Filter Real
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### 1. Automatic temperedness and global tail bound from unit-window counts -/

/-- **Unit-window counts discharge temperedness and the global `(1 + |γ|²)⁻¹` tail.**
If `Z.N t (t + 1) ≤ A₀ log(|t| + 3)` for all `t ∈ ℝ` (`0 ≤ A₀`), then `Z` is tempered and its
global `(1 + |γ_z|²)⁻¹`-weighted multiplicity sum is bounded by `4 max(A₀, 1) · totalWeight`. -/
theorem temperedConfig_and_tsum_le_of_unit_window_count (Z : ZeroConfig) {A₀ : ℝ}
    (_hA₀ : 0 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    TemperedConfig Z ∧
      ∑' z : ℂ, Z.carrier.indicator (fun w => (Z.mult w : ℝ)) z /
          (1 + Complex.normSq (gammaOf z)) ≤
        4 * max A₀ 1 * WeilEF.totalWeight ∧
      ∑' z : ℂ, ‖Z.carrier.indicator (fun w => (Z.mult w : ℂ)) z‖ /
          (1 + Complex.normSq (gammaOf z)) ≤
        4 * max A₀ 1 * WeilEF.totalWeight := by
  classical
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁, A₁ = max A₀ 1 := ⟨_, rfl⟩
  have hA₁1 : 1 ≤ A₁ := by rw [hA₁def]; exact le_max_right _ _
  have hA₀A₁ : A₀ ≤ A₁ := by rw [hA₁def]; exact le_max_left _ _
  have hloc₁ : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₁ * Real.log (|t| + 3) := fun t => by
    have hlog : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
    exact (hloc t).trans (mul_le_mul_of_nonneg_right hA₀A₁ hlog)
  have hLC := Tail.LocalCount.ofWindowCount Z hA₁1 hloc₁
  have hW := WeilEF.summable_weight
  have hnonneg : ∀ ρ : Z.carrier, 0 ≤ (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) :=
    fun ρ => div_nonneg (Nat.cast_nonneg _)
      (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))])
  have hsum_le : ∀ s : Finset Z.carrier,
      ∑ ρ ∈ s, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) ≤
        4 * A₁ * WeilEF.totalWeight := by
    intro s
    let κ : Z.carrier → ℤ := fun ρ => WeilEF.key (ρ : ℂ).im
    rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
      (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
    have hfiber : ∀ n ∈ s.image κ,
        ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) ≤
          4 * A₁ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
      intro n _
      have hwin := hLC.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        rw [← hρ.2]; exact ⟨WeilEF.key_lt _, WeilEF.le_key_add_one _⟩)
      have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
          (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) ≤
            (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by
        intro ρ hρ
        simp only [Finset.mem_filter] at hρ
        have h1 : (n : ℝ) < (ρ : ℂ).im := by rw [← hρ.2]; exact WeilEF.key_lt _
        have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by rw [← hρ.2]; exact WeilEF.le_key_add_one _
        have hge := WeilEF.one_add_sq_ge h1 h2
        have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (gammaOf ρ) := by
          rw [Complex.normSq_apply, WeilEF.gammaOf_re]
          nlinarith [sq_nonneg ((gammaOf (ρ : ℂ)).im)]
        have hm : (0 : ℝ) ≤ (Z.mult ρ : ℝ) := Nat.cast_nonneg _
        have hN0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
          linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
        have hinv : 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ hN0 (by positivity)]
          nlinarith [hge, hnorm]
        calc (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
            = (Z.mult ρ : ℝ) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring
          _ ≤ (Z.mult ρ : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
          _ = (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by ring
      calc ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) :=
            Finset.sum_le_sum hpt
        _ = (4 / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (A₁ * Real.log (|(n : ℝ)| + 3)) :=
            mul_le_mul_of_nonneg_left hwin (by positivity)
        _ = 4 * A₁ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
    calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n,
          (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ ∑ n ∈ s.image κ, 4 * A₁ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
          Finset.sum_le_sum hfiber
      _ = 4 * A₁ * ∑ n ∈ s.image κ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * A₁ * WeilEF.totalWeight := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact hW.sum_le_tsum _ fun n _ =>
            div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  have hZ : TemperedConfig Z := summable_of_sum_le hnonneg hsum_le
  have htsum_sub : ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) ≤
      4 * A₁ * WeilEF.totalWeight :=
    Real.tsum_le_of_sum_le hnonneg hsum_le
  have hind_eq : ∀ z : ℂ,
      Z.carrier.indicator (fun w => (Z.mult w : ℝ)) z / (1 + Complex.normSq (gammaOf z)) =
        Z.carrier.indicator (fun w => (Z.mult w : ℝ) / (1 + Complex.normSq (gammaOf w))) z := by
    intro z
    by_cases hz : z ∈ Z.carrier
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_div]
  have hnorm_eq : ∀ z : ℂ,
      ‖Z.carrier.indicator (fun w => (Z.mult w : ℂ)) z‖ / (1 + Complex.normSq (gammaOf z)) =
        Z.carrier.indicator (fun w => (Z.mult w : ℝ)) z / (1 + Complex.normSq (gammaOf z)) := by
    intro z
    congr 1
    by_cases hz : z ∈ Z.carrier
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Complex.norm_natCast]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero]
  have htsum_ind :
      ∑' z : ℂ, Z.carrier.indicator (fun w => (Z.mult w : ℝ)) z /
          (1 + Complex.normSq (gammaOf z)) ≤
        4 * A₁ * WeilEF.totalWeight := by
    rw [tsum_congr hind_eq, ← tsum_subtype Z.carrier
      (fun w => (Z.mult w : ℝ) / (1 + Complex.normSq (gammaOf w)))]
    exact htsum_sub
  rw [hA₁def] at htsum_ind
  exact ⟨hZ, htsum_ind, (tsum_congr hnorm_eq).le.trans htsum_ind⟩

/-- **Explicit `multDiff` tail bound for a pair of configurations with unit-window bounds.** -/
theorem tsum_multDiff_le_of_unit_window_counts (Z Z' : ZeroConfig) {A₀ A₀' : ℝ}
    (hA₀ : 0 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hA₀' : 0 ≤ A₀') (hloc' : ∀ t : ℝ, (Z'.N t (t + 1) : ℝ) ≤ A₀' * Real.log (|t| + 3)) :
    TemperedConfig Z ∧ TemperedConfig Z' ∧
      ∑' z : ℂ, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤
        4 * (max A₀ 1 + max A₀' 1) * WeilEF.totalWeight := by
  obtain ⟨hZ, htsZ, _⟩ := temperedConfig_and_tsum_le_of_unit_window_count Z hA₀ hloc
  obtain ⟨hZ', htsZ', _⟩ := temperedConfig_and_tsum_le_of_unit_window_count Z' hA₀' hloc'
  have hsZ := summable_indicator_tempered Z hZ
  have hsZ' := summable_indicator_tempered Z' hZ'
  have hle : ∀ z : ℂ, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤
      Z.carrier.indicator (fun w => (Z.mult w : ℝ)) z / (1 + Complex.normSq (gammaOf z)) +
        Z'.carrier.indicator (fun w => (Z'.mult w : ℝ)) z / (1 + Complex.normSq (gammaOf z)) := by
    intro z
    rw [← add_div]
    exact div_le_div_of_nonneg_right (norm_multDiff_le_add Z Z' z)
      (by linarith [Complex.normSq_nonneg (gammaOf z)])
  have hsM : Summable (fun z => ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z))) :=
    (hsZ.add hsZ').of_nonneg_of_le
      (fun z => div_nonneg (norm_nonneg _) (by linarith [Complex.normSq_nonneg (gammaOf z)])) hle
  refine ⟨hZ, hZ', ?_⟩
  calc ∑' z : ℂ, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z))
      ≤ ∑' z : ℂ, (Z.carrier.indicator (fun w => (Z.mult w : ℝ)) z /
            (1 + Complex.normSq (gammaOf z)) +
          Z'.carrier.indicator (fun w => (Z'.mult w : ℝ)) z /
            (1 + Complex.normSq (gammaOf z))) :=
        hsM.tsum_le_tsum hle (hsZ.add hsZ')
    _ = (∑' z : ℂ, Z.carrier.indicator (fun w => (Z.mult w : ℝ)) z /
          (1 + Complex.normSq (gammaOf z))) +
        (∑' z : ℂ, Z'.carrier.indicator (fun w => (Z'.mult w : ℝ)) z /
          (1 + Complex.normSq (gammaOf z))) := hsZ.tsum_add hsZ'
    _ ≤ 4 * max A₀ 1 * WeilEF.totalWeight + 4 * max A₀' 1 * WeilEF.totalWeight :=
        add_le_add htsZ htsZ'
    _ = 4 * (max A₀ 1 + max A₀' 1) * WeilEF.totalWeight := by ring

/-! ### 2. Riemann–von Mangoldt local-count configurations and `zetaZeroConfig` -/

/-- The smooth Riemann–von Mangoldt cumulative main term `(t / 2π) (log(t / 2π) − 1)`. -/
def rvmMainTerm (t : ℝ) : ℝ :=
  t / (2 * π) * (Real.log (t / (2 * π)) - 1)

/-- Exact convexity upper bound on increments of `rvmMainTerm`: for `0 < u ≤ v`,
`rvmMainTerm v − rvmMainTerm u ≤ ((v − u) / 2π) log(v / 2π)`. -/
theorem rvmMainTerm_sub_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    rvmMainTerm v - rvmMainTerm u ≤ (v - u) / (2 * π) * Real.log (v / (2 * π)) := by
  have h2π : 0 < 2 * π := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = u / (2 * π) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = v / (2 * π) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by rw [hb]; linarith [div_pos (hu.trans_le huv) h2π]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog ha0.le
  have hsimp : a * (b / a - 1) = b - a := by field_simp
  rw [hsimp] at hmul
  have hba : (v - u) / (2 * π) = b - a := by rw [ha, hb]; ring
  unfold rvmMainTerm
  rw [← ha, ← hb, hba]
  linarith [show a * (Real.log b - Real.log a) = a * Real.log b - a * Real.log a by ring,
    show (b - a) * Real.log b = b * Real.log b - a * Real.log b by ring]

/-- Additivity of `Z.N` across adjacent half-open intervals `(t₀, u] ⊔ (u, v] = (t₀, v]`. -/
theorem N_add_N_eq (Z : ZeroConfig) {t₀ u v : ℝ} (htu : t₀ ≤ u) (huv : u ≤ v) :
    Z.N t₀ u + Z.N u v = Z.N t₀ v := by
  classical
  have hf₀ := Z.window_finite t₀ u
  have hf₁ := Z.window_finite u v
  have hf := Z.window_finite t₀ v
  rw [ZeroConfig.N, ZeroConfig.N, ZeroConfig.N,
    finsum_mem_eq_finite_toFinset_sum _ hf₀,
    finsum_mem_eq_finite_toFinset_sum _ hf₁,
    finsum_mem_eq_finite_toFinset_sum _ hf]
  have hunion : hf.toFinset = hf₀.toFinset ∪ hf₁.toFinset := by
    ext z
    simp only [Set.Finite.mem_toFinset, Finset.mem_union, ZeroConfig.window, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨hzc, h1, h2⟩
      rcases le_or_gt z.im u with hle | hgt
      · exact Or.inl ⟨hzc, h1, hle⟩
      · exact Or.inr ⟨hzc, hgt, h2⟩
    · rintro (⟨hzc, h1, h2⟩ | ⟨hzc, h1, h2⟩)
      · exact ⟨hzc, h1, h2.trans huv⟩
      · exact ⟨hzc, htu.trans_lt h1, h2⟩
  have hdisj : Disjoint hf₀.toFinset hf₁.toFinset := by
    rw [Finset.disjoint_left]
    intro z hz0 hz1
    have h0 := (hf₀.mem_toFinset.mp hz0).2.2
    have h1 := (hf₁.mem_toFinset.mp hz1).2.1
    linarith
  rw [hunion, Finset.sum_union hdisj]

/-- **Quantitative Riemann–von Mangoldt local-count datum on `Z`.**
Combines the global unit-window bound `Z.N t (t + 1) ≤ A₀ log(|t| + 3)` with the local RvM upper
excess `Z.N u v ≤ ((v − u) / 2π) log(v / 2π) + C₁ log T` for all intervals `(u, v]` inside
`[T / 2 − 1, 3T / 2]` (`T ≥ T₁`). -/
structure HasRvMLocalCount (Z : ZeroConfig) (A₀ T₁ C₁ : ℝ) : Prop where
  nonneg_A₀ : 0 ≤ A₀
  eight_le_T₁ : 8 ≤ T₁
  nonneg_C₁ : 0 ≤ C₁
  unit_window : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)
  local_excess : ∀ T u v : ℝ, T₁ ≤ T → T / 2 - 1 ≤ u → u ≤ v → v ≤ 3 * T / 2 →
    (Z.N u v : ℝ) ≤ (v - u) / (2 * π) * Real.log (v / (2 * π)) + C₁ * Real.log T

/-- Prefix Riemann–von Mangoldt asymptotics `|Z.N 0 t − rvmMainTerm t| ≤ C log t` together with a
unit-window bound imply `HasRvMLocalCount`. -/
theorem hasRvMLocalCount_of_prefix_rvm (Z : ZeroConfig) {A₀ T₀ C : ℝ}
    (hA₀ : 0 ≤ A₀) (hT₀ : 2 ≤ T₀) (hC : 0 ≤ C)
    (hunit : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hrvm : ∀ t : ℝ, T₀ ≤ t → |(Z.N 0 t : ℝ) - rvmMainTerm t| ≤ C * Real.log t) :
    HasRvMLocalCount Z A₀ (max (2 * T₀ + 4) 8) (4 * C) := by
  refine ⟨hA₀, le_max_right _ _, by positivity, hunit, fun T u v hT hu huv hv => ?_⟩
  have hT1 : 2 * T₀ + 4 ≤ T := (le_max_left _ _).trans hT
  have hT8 : 8 ≤ T := (le_max_right _ _).trans hT
  have huT₀ : T₀ ≤ u := by linarith
  have hvT₀ : T₀ ≤ v := huT₀.trans huv
  have hu0 : 0 < u := by linarith
  have hadd : (Z.N 0 u : ℝ) + (Z.N u v : ℝ) = (Z.N 0 v : ℝ) := by
    exact_mod_cast N_add_N_eq Z hu0.le huv
  have h1 := (abs_le.mp (hrvm u huT₀)).1
  have h2 := (abs_le.mp (hrvm v hvT₀)).2
  have hinc := rvmMainTerm_sub_le hu0 huv
  have hvT2 : v ≤ T ^ 2 := by nlinarith
  have hlogv : Real.log v ≤ 2 * Real.log T := by
    calc Real.log v ≤ Real.log (T ^ 2) := Real.log_le_log (hu0.trans_le huv) hvT2
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hlogu : Real.log u ≤ 2 * Real.log T := (Real.log_le_log hu0 huv).trans hlogv
  have hCsum : C * Real.log u + C * Real.log v ≤ 4 * C * Real.log T := by
    have := add_le_add (mul_le_mul_of_nonneg_left hlogu hC) (mul_le_mul_of_nonneg_left hlogv hC)
    linarith
  linarith

/-- **The zeros of `ζ` satisfy `HasRvMLocalCount` unconditionally.** -/
theorem exists_hasRvMLocalCount_zeta :
    ∃ A₀ T₁ C₁ : ℝ, HasRvMLocalCount zetaZeroConfig A₀ T₁ C₁ := by
  obtain ⟨A₀, hA₀1, hunit⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨CB, TB, hB⟩ := Zeta23.RvM.backlund_horizontal
  obtain ⟨T₁, hT₁def⟩ : ∃ T₁, T₁ = 2 * max TB 8 + 32 := ⟨_, rfl⟩
  have hT₁32 : 32 ≤ T₁ := by rw [hT₁def]; linarith [le_max_right TB 8]
  refine ⟨A₀, T₁, 4 * |CB| + 60, ⟨by linarith, by linarith, by positivity, hunit,
    fun T u v hT hu huv hv => ?_⟩⟩
  have hT32 : 32 ≤ T := hT₁32.trans hT
  have hTB : 2 * max TB 8 + 32 ≤ T := by rwa [← hT₁def]
  have h2π : 0 < 2 * π := by positivity
  obtain ⟨T₁', hT₁'mem, hg1⟩ := Zeta23.RvM.exists_goodHeight (u - 2)
  obtain ⟨T₂', hT₂'mem, hg2⟩ := Zeta23.RvM.exists_goodHeight v
  have hT₁'a : u - 2 ≤ T₁' := hT₁'mem.1
  have hT₁'b : T₁' ≤ u - 1 := by linarith [hT₁'mem.2]
  have hT₂'a : v ≤ T₂' := hT₂'mem.1
  have hT₂'b : T₂' ≤ v + 1 := hT₂'mem.2
  have hmax_le : max TB 8 ≤ T₁' := by linarith [le_max_right TB 8]
  have h12 : T₁' < T₂' := by linarith
  have hsub : zetaZeroConfig.window u v ⊆ zetaZeroConfig.window T₁' T₂' := by
    rintro ρ ⟨hρ, ha, hb⟩
    exact ⟨hρ, by linarith, by linarith⟩
  have hNle : (zetaZeroConfig.N u v : ℝ) ≤ (Zeta23.Ncount T₁' T₂' : ℝ) := by
    have h' := zetaZeroConfig.finsum_mult_mono T₁' T₂' hsub subset_rfl
    rw [← zetaZeroConfig_N]
    exact_mod_cast h'
  have hcnt := ncount_le_of_goodHeight hB hmax_le h12 hg1 hg2
  have hv15 : 15 ≤ v := by linarith
  have hT₁'13 : 13 ≤ T₁' := by linarith
  have hlogT1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  -- bound `log((T₂' + 1) / 2π) ≤ log(v / 2π) + 2 / v`
  have hlog_shift : Real.log ((T₂' + 1) / (2 * π)) ≤ Real.log (v / (2 * π)) + 2 / v := by
    have hsplit : (T₂' + 1) / (2 * π) = (v / (2 * π)) * ((T₂' + 1) / v) := by field_simp
    rw [hsplit, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (T₂' + 1) / v by positivity)
    have h2 : (T₂' + 1) / v - 1 ≤ 2 / v := by
      rw [show (T₂' + 1) / v - 1 = (T₂' + 1 - v) / v by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hrec : 2 / v + 6 / T₁' ≤ 24 / T := by
    have hv_ge : T / 3 ≤ v := by linarith
    have hT₁'_ge : T / 3 ≤ T₁' := by linarith
    have h1 : 2 / v ≤ 2 / (T / 3) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hv_ge
    have h2 : 6 / T₁' ≤ 6 / (T / 3) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hT₁'_ge
    have heq : 2 / (T / 3) + 6 / (T / 3) = 24 / T := by field_simp; ring
    linarith
  have hlen : T₂' - T₁' ≤ v - u + 3 := by linarith
  have hlen0 : 0 ≤ T₂' - T₁' := by linarith
  have hlogv0 : 0 ≤ Real.log (v / (2 * π)) := by
    refine Real.log_nonneg ((one_le_div h2π).mpr ?_)
    linarith [Real.pi_le_four]
  have hlogvT : Real.log (v / (2 * π)) ≤ Real.log T := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ h2π]
    have : 2 * π * T ≥ 6 * T := by nlinarith [Real.pi_gt_three]
    linarith
  have hprod : (T₂' - T₁') * ((Real.log ((T₂' + 1) / (2 * π)) + 6 / T₁') / (2 * π)) ≤
      (v - u) / (2 * π) * Real.log (v / (2 * π)) + 52 * Real.log T := by
    have hD_le : (Real.log ((T₂' + 1) / (2 * π)) + 6 / T₁') / (2 * π) ≤
        (Real.log (v / (2 * π)) + 24 / T) / (2 * π) :=
      div_le_div_of_nonneg_right (by linarith) h2π.le
    have hD0 : 0 ≤ (Real.log ((T₂' + 1) / (2 * π)) + 6 / T₁') / (2 * π) := by
      have : 0 ≤ Real.log ((T₂' + 1) / (2 * π)) :=
        Real.log_nonneg ((one_le_div h2π).mpr (by linarith [Real.pi_le_four]))
      exact div_nonneg (by positivity) h2π.le
    have h1 := mul_le_mul hlen hD_le hD0 (by linarith)
    have hexpand : (v - u + 3) * ((Real.log (v / (2 * π)) + 24 / T) / (2 * π)) =
        (v - u) / (2 * π) * Real.log (v / (2 * π)) +
          3 / (2 * π) * Real.log (v / (2 * π)) +
          (v - u + 3) * (24 / T) / (2 * π) := by ring
    have h3log : 3 / (2 * π) * Real.log (v / (2 * π)) ≤ Real.log T := by
      have h32π : 3 / (2 * π) ≤ 1 := by rw [div_le_one h2π]; linarith [Real.pi_gt_three]
      calc 3 / (2 * π) * Real.log (v / (2 * π)) ≤ 1 * Real.log (v / (2 * π)) :=
            mul_le_mul_of_nonneg_right h32π hlogv0
        _ ≤ Real.log T := by linarith
    have hvuT : v - u + 3 ≤ 2 * T := by linarith
    have hrem : (v - u + 3) * (24 / T) / (2 * π) ≤ 51 * Real.log T := by
      have hmul : (v - u + 3) * (24 / T) ≤ 48 := by
        calc (v - u + 3) * (24 / T) ≤ (2 * T) * (24 / T) :=
              mul_le_mul_of_nonneg_right hvuT (by positivity)
          _ = 48 := by field_simp; ring
      have hdiv : (v - u + 3) * (24 / T) / (2 * π) ≤ 48 := by
        calc (v - u + 3) * (24 / T) / (2 * π) ≤ 48 / (2 * π) :=
              div_le_div_of_nonneg_right hmul h2π.le
          _ ≤ 48 / 1 := div_le_div_of_nonneg_left (by norm_num) one_pos
              (by linarith [Real.pi_gt_three])
          _ = 48 := div_one _
      linarith
    linarith
  have hT₂'sq : T₂' ≤ T ^ 2 := by nlinarith
  have hl2 : Real.log T₂' ≤ 2 * Real.log T := by
    calc Real.log T₂' ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hT₂'sq
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hl1 : Real.log T₁' ≤ 2 * Real.log T := (Real.log_le_log (by linarith) h12.le).trans hl2
  have hCB : |CB| * (Real.log T₁' + Real.log T₂') ≤ 4 * |CB| * Real.log T := by
    have := mul_le_mul_of_nonneg_left (add_le_add hl1 hl2) (abs_nonneg CB)
    linarith [show |CB| * (2 * Real.log T + 2 * Real.log T) = 4 * |CB| * Real.log T by ring]
  linarith [show (4 * |CB| + 60) * Real.log T = 4 * |CB| * Real.log T + 60 * Real.log T by ring]

/-! ### 3. Distinct-point carrier and cluster count bounds from `HasRvMLocalCount` -/

private theorem card_le_N_sub_one (Z : ZeroConfig) {x y : ℝ} (s : Finset ℂ)
    (hs : ∀ z ∈ s, z ∈ Z.carrier ∧ z.im ∈ Icc x y) :
    (s.card : ℝ) ≤ (Z.N (x - 1) y : ℝ) := by
  classical
  have hfin := Z.window_finite (x - 1) y
  have hle : s.card ≤ Z.N (x - 1) y := by
    rw [ZeroConfig.N, finsum_mem_eq_finite_toFinset_sum _ hfin]
    calc s.card = ∑ _z ∈ s, 1 := Finset.card_eq_sum_ones s
      _ ≤ ∑ z ∈ s, Z.mult z := Finset.sum_le_sum fun z hz => Z.one_le_mult z (hs z hz).1
      _ ≤ ∑ z ∈ hfin.toFinset, Z.mult z := Finset.sum_le_sum_of_subset fun z hz =>
          (hfin.mem_toFinset).mpr ⟨(hs z hz).1, by linarith [(hs z hz).2.1], (hs z hz).2.2⟩
  exact_mod_cast hle

/-- **Distinct-point local count on `[T / 2, 3T / 2]` from `HasRvMLocalCount`.**
For any `δ' > 0`, once `log(T / 2π) ≥ max 1 (1 / δ')` and `T ≥ T₁`, distinct points of `Z.carrier`
in `[T / 2, 3T / 2] ∩ [x, y]` number at most
`((1 + δ') / 2π) log(T / 2π) · (y − x) + (8 C₁ + 2) log(T / 2π)`. -/
theorem card_carrier_le_of_hasRvMLocalCount {Z : ZeroConfig} {A₀ T₁ C₁ δ' T : ℝ}
    (hZ : HasRvMLocalCount Z A₀ T₁ C₁) (hδ' : 0 < δ') (hT₁ : T₁ ≤ T)
    (hu1 : 1 ≤ Real.log (T / (2 * π))) (huδ : 1 / δ' ≤ Real.log (T / (2 * π))) :
    ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, z ∈ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ (1 + δ') / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
          (8 * C₁ + 2) * Real.log (T / (2 * π)) := by
  intro s x y hxy hs
  have h2π : 0 < 2 * π := by positivity
  have hT8 : 8 ≤ T := hZ.eight_le_T₁.trans hT₁
  have hT0 : 0 < T := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  rw [← hu] at hu1 huδ ⊢
  have hu0 : 0 < u := by linarith
  obtain ⟨x', hx'⟩ : ∃ x', x' = max x (T - T / 2) := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = min y (T + T / 2) := ⟨_, rfl⟩
  by_cases hne : x' ≤ y'
  · have hs' : ∀ z ∈ s, z ∈ Z.carrier ∧ z.im ∈ Icc x' y' := fun z hz => by
      obtain ⟨hzc, habs, hx_le, hy_le⟩ := hs z hz
      have habs' := abs_le.mp habs
      rw [hx', hy']
      exact ⟨hzc, max_le hx_le (by linarith), le_min hy_le (by linarith)⟩
    have hcard := card_le_N_sub_one Z s hs'
    have hx'lo : T / 2 - 1 ≤ x' - 1 := by
      have : T - T / 2 ≤ x' := by rw [hx']; exact le_max_right _ _
      linarith
    have hy'hi : y' ≤ 3 * T / 2 := by
      have : y' ≤ T + T / 2 := by rw [hy']; exact min_le_right _ _
      linarith
    have hN := hZ.local_excess T (x' - 1) y' hT₁ hx'lo (by linarith) hy'hi
    have hy'0 : 0 < y' := by linarith
    have hlog_y' : Real.log (y' / (2 * π)) ≤ u + 1 := by
      have h32 : (3 : ℝ) / 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have hmul : y' / (2 * π) ≤ (T / (2 * π)) * Real.exp 1 := by
        calc y' / (2 * π) ≤ (3 * T / 2) / (2 * π) :=
              div_le_div_of_nonneg_right hy'hi h2π.le
          _ = (T / (2 * π)) * (3 / 2) := by ring
          _ ≤ (T / (2 * π)) * Real.exp 1 := mul_le_mul_of_nonneg_left h32 (by positivity)
      calc Real.log (y' / (2 * π)) ≤ Real.log ((T / (2 * π)) * Real.exp 1) :=
            Real.log_le_log (by positivity) hmul
        _ = u + 1 := by rw [Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp, hu]
    have h1δu : 1 ≤ δ' * u := by
      have := (div_le_iff₀ hδ').mp huδ
      linarith
    have hu1_le : u + 1 ≤ (1 + δ') * u := by linarith
    have hlen : y' - x' ≤ y - x := by
      rw [hx', hy']
      linarith [min_le_left y (T + T / 2), le_max_left x (T - T / 2)]
    have hmain : (y' - (x' - 1)) / (2 * π) * Real.log (y' / (2 * π)) ≤
        (1 + δ') / (2 * π) * u * (y - x) + 2 * u := by
      have hlog_le : Real.log (y' / (2 * π)) ≤ (1 + δ') * u := hlog_y'.trans hu1_le
      have h1 : (y' - (x' - 1)) / (2 * π) * Real.log (y' / (2 * π)) ≤
          (y' - x' + 1) / (2 * π) * (u + 1) := by
        rw [show y' - (x' - 1) = y' - x' + 1 by ring]
        exact mul_le_mul_of_nonneg_left hlog_y' (div_nonneg (by linarith) h2π.le)
      have h2 : (y' - x') / (2 * π) * (u + 1) ≤ (y - x) / (2 * π) * ((1 + δ') * u) :=
        mul_le_mul (div_le_div_of_nonneg_right hlen h2π.le) hu1_le (by positivity)
          (div_nonneg (sub_nonneg.mpr hxy) h2π.le)
      have h3 : 1 / (2 * π) * (u + 1) ≤ 2 * u := by
        have h12π : 1 / (2 * π) ≤ 1 := by rw [div_le_one h2π]; linarith [Real.pi_gt_three]
        calc 1 / (2 * π) * (u + 1) ≤ 1 * (u + 1) :=
              mul_le_mul_of_nonneg_right h12π (by positivity)
          _ ≤ 2 * u := by linarith
      linarith [show (y' - x' + 1) / (2 * π) * (u + 1) =
          (y' - x') / (2 * π) * (u + 1) + 1 / (2 * π) * (u + 1) by ring,
        show (y - x) / (2 * π) * ((1 + δ') * u) =
          (1 + δ') / (2 * π) * u * (y - x) by ring]
    have hlogT : Real.log T ≤ 8 * u := by
      have hsplit : T = (2 * π) * (T / (2 * π)) := by field_simp
      rw [hsplit, Real.log_mul h2π.ne' (by positivity), ← hu]
      have := Real.log_le_sub_one_of_pos h2π
      linarith [Real.pi_le_four]
    have hC₁log : C₁ * Real.log T ≤ 8 * C₁ * u := by
      have := mul_le_mul_of_nonneg_left hlogT hZ.nonneg_C₁
      linarith [show C₁ * (8 * u) = 8 * C₁ * u by ring]
    linarith [show (8 * C₁ + 2) * u = 8 * C₁ * u + 2 * u by ring]
  · have hempty : s = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz => hne ?_
      obtain ⟨_, habs, hx_le, hy_le⟩ := hs z hz
      have habs' := abs_le.mp habs
      rw [hx', hy']
      exact (max_le hx_le (by linarith)).trans (le_min hy_le (by linarith))
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    have h1 : 0 ≤ (1 + δ') / (2 * π) * u * (y - x) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hxy)
    have h2 : 0 ≤ (8 * C₁ + 2) * u := mul_nonneg (by linarith [hZ.nonneg_C₁]) hu0.le
    linarith

private theorem card_cluster_split_extra {Z Z' : ZeroConfig} {T D₁ C₁ D₂ C₂ x y : ℝ}
    {s : Finset ℂ}
    (hZ : ∀ t : Finset ℂ, (∀ z ∈ t, z ∈ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
      (t.card : ℝ) ≤ D₁ * (y - x) + C₁)
    (hZ' : ∀ t : Finset ℂ,
      (∀ z ∈ t, z ∈ Z'.carrier ∧ z ∉ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
        (t.card : ℝ) ≤ D₂ * (y - x) + C₂)
    (hs : ∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) :
    (s.card : ℝ) ≤ (D₁ + D₂) * (y - x) + (C₁ + C₂) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun z => z ∈ Z.carrier)
  have h1 := hZ (s.filter fun z => z ∈ Z.carrier) fun z hz => by
    obtain ⟨hzs, hzc⟩ := Finset.mem_filter.mp hz
    exact ⟨hzc, (hs z hzs).2.1, (hs z hzs).2.2⟩
  have h2 := hZ' (s.filter fun z => z ∉ Z.carrier) fun z hz => by
    obtain ⟨hzs, hzc⟩ := Finset.mem_filter.mp hz
    obtain ⟨hmd, hR, hI⟩ := hs z hzs
    rcases mem_carrier_of_multDiff_ne_zero hmd with hzZ | hzZ'
    · exact absurd hzZ hzc
    · exact ⟨hzZ', hzc, hR, hI⟩
  have hcard : (s.card : ℝ) = ((s.filter fun z => z ∈ Z.carrier).card : ℝ) +
      ((s.filter fun z => z ∉ Z.carrier).card : ℝ) := by
    exact_mod_cast hsplit.symm
  rw [hcard]
  linarith

/-! ### 4. RvM local inversion theorems (with extra-carrier density, subset carrier, and arbitrary pairs) -/

/-- **Polynomial-scale local inversion for an RvM configuration against a mimic of extra-carrier
density `μ`, at `λ > (1 + μ) / 2`.**
No separate global tail constant `S` is needed: unit-window bounds discharge both `TemperedConfig`
and the global `(1 + |γ|²)⁻¹` tail automatically. -/
theorem rvm_coincide_of_extra_density_rpow {A₀ T₁ C₁ A₀' μ A' lam M : ℝ}
    (hA₀ : 0 ≤ A₀) (_hT₁ : 8 ≤ T₁) (hC₁ : 0 ≤ C₁) (hA₀' : 0 ≤ A₀')
    (hμ : 0 ≤ μ) (hA' : 0 ≤ A') (hlam : (1 + μ) / 2 < lam) (hM : 0 ≤ M) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig,
        HasRvMLocalCount Z A₀ T₁ C₁ →
        (∀ t : ℝ, (Z'.N t (t + 1) : ℝ) ≤ A₀' * Real.log (|t| + 3)) →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, z ∈ Z'.carrier ∧ z ∉ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ μ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A' * Real.log (T / (2 * π))) →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ ‖z - z₀‖ < T ^ (-M) := by
  obtain ⟨δ', hδ'def⟩ : ∃ δ', δ' = lam - (1 + μ) / 2 := ⟨_, rfl⟩
  have hδ' : 0 < δ' := by rw [hδ'def]; linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = 1 + μ + δ' := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθlam : θ / 2 < lam := by rw [hθdef, hδ'def]; linarith
  obtain ⟨S, hSdef⟩ : ∃ S, S = 4 * (max A₀ 1 + max A₀' 1) * WeilEF.totalWeight := ⟨_, rfl⟩
  have hW0 : 0 ≤ WeilEF.totalWeight :=
    tsum_nonneg fun n =>
      div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  obtain ⟨T_cam, hT_cam1, hcam⟩ := exists_nearCollision_of_mimic_above_half_density
    (θ := θ) (lam := lam) (A := 8 * C₁ + 2 + A') (S := S) (M := M)
    hθ0 hθlam (by positivity) hS0 hM
  refine ⟨max T_cam (max T₁ (2 * π * Real.exp (max 1 (1 / δ')))),
    hT_cam1.trans (le_max_left _ _),
    fun T hT Z Z' hZ hZ'unit hextra hW z₀ hz₀ hc => ?_⟩
  have h2π : 0 < 2 * π := by positivity
  have hT_c : T_cam ≤ T := (le_max_left _ _).trans hT
  have hT_1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT_u : 2 * π * Real.exp (max 1 (1 / δ')) ≤ T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hu_ge : max 1 (1 / δ') ≤ Real.log (T / (2 * π)) := by
    rw [← Real.log_exp (max 1 (1 / δ'))]
    exact Real.log_le_log (Real.exp_pos _) ((le_div_iff₀ h2π).mpr (by linarith))
  obtain ⟨hZt, hZ't, hStail⟩ :=
    tsum_multDiff_le_of_unit_window_counts Z Z' hA₀ hZ.unit_window hA₀' hZ'unit
  rw [← hSdef] at hStail
  have hZcard := card_carrier_le_of_hasRvMLocalCount hZ hδ' hT_1
    ((le_max_left _ _).trans hu_ge) ((le_max_right _ _).trans hu_ge)
  refine hcam T hT_c Z Z' hZt hZ't hW hStail (fun s x y hxy hs => ?_) z₀ hz₀ hc
  have hcl := card_cluster_split_extra (hZ := fun t ht => hZcard t x y hxy ht)
    (hZ' := fun t ht => hextra t x y hxy ht) hs
  have hD_eq : ((1 + δ') / (2 * π) * Real.log (T / (2 * π)) +
      μ / (2 * π) * Real.log (T / (2 * π))) * (y - x) =
      θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) := by
    rw [hθdef]; ring
  have hC_eq : (8 * C₁ + 2) * Real.log (T / (2 * π)) + A' * Real.log (T / (2 * π)) =
      (8 * C₁ + 2 + A') * Real.log (T / (2 * π)) := by ring
  linarith

/-- **`o(1 / log T)` local inversion for an RvM configuration against a mimic of extra-carrier
density `μ`, at `λ > (1 + μ) / 2`.** -/
theorem rvm_coincide_of_extra_density_littleO {A₀ T₁ C₁ A₀' μ A' lam δ : ℝ}
    (hA₀ : 0 ≤ A₀) (hT₁ : 8 ≤ T₁) (hC₁ : 0 ≤ C₁) (hA₀' : 0 ≤ A₀')
    (hμ : 0 ≤ μ) (hA' : 0 ≤ A') (hlam : (1 + μ) / 2 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig,
        HasRvMLocalCount Z A₀ T₁ C₁ →
        (∀ t : ℝ, (Z'.N t (t + 1) : ℝ) ≤ A₀' * Real.log (|t| + 3)) →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, z ∈ Z'.carrier ∧ z ∉ Z.carrier ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ μ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A' * Real.log (T / (2 * π))) →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  obtain ⟨T₁', hT₁'1, hrpow⟩ := rvm_coincide_of_extra_density_rpow (M := 1)
    hA₀ hT₁ hC₁ hA₀' hμ hA' hlam (by norm_num)
  refine ⟨max T₁' (2 / δ * max 0 (Real.log (2 / δ))), hT₁'1.trans (le_max_left _ _),
    fun T hT Z Z' hZ hZ'u hextra hW z₀ hz₀ hc => ?_⟩
  obtain ⟨z, hne, hcz, hzR, hlt⟩ :=
    hrpow T ((le_max_left _ _).trans hT) Z Z' hZ hZ'u hextra hW z₀ hz₀ hc
  have hT3 : 3 ≤ T := by
    have : 2 * π * 1 ≤ 2 * π * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.one_le_exp zero_le_one) (by positivity)
    linarith [Real.pi_gt_three, hT₁'1.trans ((le_max_left _ _).trans hT)]
  have hTδ : 2 / δ * max 0 (Real.log (2 / δ)) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hle : T ^ (-1 : ℝ) ≤ δ / Real.log T := by
    have h := log_le_mul_add_log_inv hT0 (show 0 < δ / 2 by positivity)
    rw [show (δ / 2)⁻¹ = 2 / δ by field_simp] at h
    have h1 : Real.log (2 / δ) ≤ max 0 (Real.log (2 / δ)) := le_max_right _ _
    have h2 : max 0 (Real.log (2 / δ)) ≤ δ / 2 * T := by
      calc max 0 (Real.log (2 / δ)) = δ / 2 * (2 / δ * max 0 (Real.log (2 / δ))) := by field_simp
        _ ≤ δ / 2 * T := mul_le_mul_of_nonneg_left hTδ (by positivity)
    rw [Real.rpow_neg_one, inv_eq_one_div, div_le_div_iff₀ hT0 hlog0]
    linarith
  exact ⟨z, hne, hcz, hzR, hlt.trans_le hle⟩

/-- **Square-root threshold (`λ > ½`) coincidence for shared/subset-carrier RvM configurations.**
Whenever `Z'.carrier ∩ [T / 2, 3T / 2] ⊆ Z.carrier`, aperture `λ · ½ log(T / 2π)` with `λ > ½`
forces `Z` and `Z'` to coincide across `|Im z − T| ≤ T / 4` outside near-collision clusters of
diameter `< δ / log T` (`o(1 / log T)`), uniformly in `T`. -/
theorem rvm_subset_carrier_coincide_at_squareRoot_littleO {A₀ T₁ C₁ A₀' lam δ : ℝ}
    (hA₀ : 0 ≤ A₀) (hT₁ : 8 ≤ T₁) (hC₁ : 0 ≤ C₁) (hA₀' : 0 ≤ A₀')
    (hlam : 1 / 2 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig,
        HasRvMLocalCount Z A₀ T₁ C₁ →
        (∀ t : ℝ, (Z'.N t (t + 1) : ℝ) ≤ A₀' * Real.log (|t| + 3)) →
        (∀ z ∈ Z'.carrier, |z.im - T| ≤ T / 2 → z ∈ Z.carrier) →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  have hlam' : (1 + 0) / 2 < lam := by linarith
  obtain ⟨T₀, hT₀1, hco⟩ := rvm_coincide_of_extra_density_littleO (μ := 0) (A' := 0)
    hA₀ hT₁ hC₁ hA₀' le_rfl le_rfl hlam' hδ
  refine ⟨T₀, hT₀1, fun T hT Z Z' hZ hZ'u hsub hW z₀ hz₀ hc => ?_⟩
  refine hco T hT Z Z' hZ hZ'u (fun s x y _ hs => ?_) hW z₀ hz₀ hc
  have hempty : s = ∅ := Finset.eq_empty_of_forall_notMem fun z hz =>
    (hs z hz).2.1 (hsub z (hs z hz).1 (hs z hz).2.2.1)
  rw [hempty, Finset.card_empty]
  simp

/-- **Arbitrary RvM pairs above `λ > 1` (polynomial diameter `< T^{−M}`).**
Without any shared-carrier assumption, any two RvM configurations whose images agree on windows of
aperture `λ · ½ log(T / 2π)` with `λ > 1` coincide across `|Im z − T| ≤ T / 4` outside
near-collision clusters of polynomial diameter `< T^{−M}`, uniformly in `T`. -/
theorem rvm_pair_coincide_outside_nearCollisions_above_one_rpow
    {A₀ T₁ C₁ A₀' T₁' C₁' lam M : ℝ}
    (hA₀ : 0 ≤ A₀) (hT₁ : 8 ≤ T₁) (hC₁ : 0 ≤ C₁)
    (hA₀' : 0 ≤ A₀') (_hT₁' : 8 ≤ T₁') (hC₁' : 0 ≤ C₁')
    (hlam : 1 < lam) (hM : 0 ≤ M) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig,
        HasRvMLocalCount Z A₀ T₁ C₁ → HasRvMLocalCount Z' A₀' T₁' C₁' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ ‖z - z₀‖ < T ^ (-M) := by
  obtain ⟨δ'', hδ''def⟩ : ∃ δ'', δ'' = lam - 1 := ⟨_, rfl⟩
  have hδ'' : 0 < δ'' := by rw [hδ''def]; linarith
  have hlam_mu : (1 + (1 + δ'')) / 2 < lam := by rw [hδ''def]; linarith
  obtain ⟨T_co, hT_co1, hco⟩ := rvm_coincide_of_extra_density_rpow
    (A₀ := A₀) (T₁ := T₁) (C₁ := C₁) (A₀' := A₀') (μ := 1 + δ'') (A' := 8 * C₁' + 2)
    (lam := lam) (M := M)
    hA₀ hT₁ hC₁ hA₀' (by positivity) (by positivity) hlam_mu hM
  refine ⟨max T_co (max T₁' (2 * π * Real.exp (max 1 (1 / δ'')))),
    hT_co1.trans (le_max_left _ _),
    fun T hT Z Z' hZ hZ' hW z₀ hz₀ hc => ?_⟩
  have h2π : 0 < 2 * π := by positivity
  have hT_c : T_co ≤ T := (le_max_left _ _).trans hT
  have hT_1' : T₁' ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT_u : 2 * π * Real.exp (max 1 (1 / δ'')) ≤ T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hu_ge : max 1 (1 / δ'') ≤ Real.log (T / (2 * π)) := by
    rw [← Real.log_exp (max 1 (1 / δ''))]
    exact Real.log_le_log (Real.exp_pos _) ((le_div_iff₀ h2π).mpr (by linarith))
  have hZ'card := card_carrier_le_of_hasRvMLocalCount hZ' hδ'' hT_1'
    ((le_max_left _ _).trans hu_ge) ((le_max_right _ _).trans hu_ge)
  exact hco T hT_c Z Z' hZ hZ'.unit_window
    (fun s x y hxy hs => hZ'card s x y hxy fun z hz =>
      ⟨(hs z hz).1, (hs z hz).2.2.1, (hs z hz).2.2.2⟩)
    hW z₀ hz₀ hc

/-- **Arbitrary RvM pairs above `λ > 1` (`o(1 / log T)` near-collision diameter).**
For every `λ > 1` and every `δ > 0`, uniformly for `T ≥ T₀`, two RvM configurations whose images
agree on windows of aperture `λ · ½ log(T / 2π)` coincide across `|Im z − T| ≤ T / 4` outside
near-collision clusters of diameter `< δ / log T`. -/
theorem rvm_pair_coincide_outside_nearCollisions_above_one
    {A₀ T₁ C₁ A₀' T₁' C₁' lam δ : ℝ}
    (hA₀ : 0 ≤ A₀) (hT₁ : 8 ≤ T₁) (hC₁ : 0 ≤ C₁)
    (hA₀' : 0 ≤ A₀') (hT₁' : 8 ≤ T₁') (hC₁' : 0 ≤ C₁')
    (hlam : 1 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig,
        HasRvMLocalCount Z A₀ T₁ C₁ → HasRvMLocalCount Z' A₀' T₁' C₁' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  obtain ⟨T₁'', hT₁''1, hrpow⟩ := rvm_pair_coincide_outside_nearCollisions_above_one_rpow (M := 1)
    hA₀ hT₁ hC₁ hA₀' hT₁' hC₁' hlam (by norm_num)
  refine ⟨max T₁'' (2 / δ * max 0 (Real.log (2 / δ))), hT₁''1.trans (le_max_left _ _),
    fun T hT Z Z' hZ hZ' hW z₀ hz₀ hc => ?_⟩
  obtain ⟨z, hne, hcz, hzR, hlt⟩ :=
    hrpow T ((le_max_left _ _).trans hT) Z Z' hZ hZ' hW z₀ hz₀ hc
  have hT3 : 3 ≤ T := by
    have : 2 * π * 1 ≤ 2 * π * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.one_le_exp zero_le_one) (by positivity)
    linarith [Real.pi_gt_three, hT₁''1.trans ((le_max_left _ _).trans hT)]
  have hTδ : 2 / δ * max 0 (Real.log (2 / δ)) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hle : T ^ (-1 : ℝ) ≤ δ / Real.log T := by
    have h := log_le_mul_add_log_inv hT0 (show 0 < δ / 2 by positivity)
    rw [show (δ / 2)⁻¹ = 2 / δ by field_simp] at h
    have h1 : Real.log (2 / δ) ≤ max 0 (Real.log (2 / δ)) := le_max_right _ _
    have h2 : max 0 (Real.log (2 / δ)) ≤ δ / 2 * T := by
      calc max 0 (Real.log (2 / δ)) = δ / 2 * (2 / δ * max 0 (Real.log (2 / δ))) := by field_simp
        _ ≤ δ / 2 * T := mul_le_mul_of_nonneg_left hTδ (by positivity)
    rw [Real.rpow_neg_one, inv_eq_one_div, div_le_div_iff₀ hT0 hlog0]
    linarith
  exact ⟨z, hne, hcz, hzR, hlt.trans_le hle⟩

/-- **Sharp threshold dichotomy for Route ZCG Question 2.5.5.**
1. *Failure on `0 < λ ≤ 1`*: for every `T ≥ 2π e^π` and `0 < λ ≤ 1`, two critical-line simple
   configurations with RvM local count error `≤ 1` and disjoint carriers separated by
   `≥ π / log(T / 2π)` have identical Weil images on windows of aperture `λ · ½ log(T / 2π)`.
2. *Unconditional coincidence on `λ > 1`*: for every `λ > 1` and `δ > 0`, any two RvM
   configurations whose images agree on windows of aperture `λ · ½ log(T / 2π)` coincide across
   `|Im z − T| ≤ T / 4` outside near-collision clusters of diameter `< δ / log T`.
3. *Square-root threshold (`λ > ½`) coincidence under carrier containment*: for every `λ > ½` and
   `δ > 0`, the same `o(1 / log T)` coincidence holds whenever `Z'.carrier ∩ [T/2, 3T/2] ⊆ Z.carrier`. -/
theorem rvm_local_inversion_dichotomy :
    (∀ T lam : ℝ, 2 * π * Real.exp π ≤ T → 0 < lam → lam ≤ 1 →
      ∃ Z₀ Z₁ : ZeroConfig,
        TemperedConfig Z₀ ∧ TemperedConfig Z₁ ∧
        (∀ z ∈ Z₀.carrier, z.re = 1 / 2 ∧ Z₀.mult z = 1) ∧
        (∀ z ∈ Z₁.carrier, z.re = 1 / 2 ∧ Z₁.mult z = 1) ∧
        (∀ x y : ℝ, x ≤ y →
          |(Z₀.N x y : ℝ) - Real.log (T / (2 * π)) / (2 * π) * (y - x)| ≤ 1 ∧
          |(Z₁.N x y : ℝ) - Real.log (T / (2 * π)) / (2 * π) * (y - x)| ≤ 1) ∧
        (∀ f g : ℝ → ℂ,
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f →
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) g →
          Z₀.W f g = Z₁.W f g) ∧
        Disjoint Z₀.carrier Z₁.carrier ∧
        (∃ z₀ ∈ Z₀.carrier, |z₀.im - T| ≤ 1) ∧
        (∀ z ∈ Z₀.carrier ∪ Z₁.carrier, ∀ w ∈ Z₀.carrier ∪ Z₁.carrier,
          z ≠ w → π / Real.log (T / (2 * π)) ≤ ‖z - w‖)) ∧
    (∀ A₀ T₁ C₁ A₀' T₁' C₁' lam δ : ℝ,
      0 ≤ A₀ → 8 ≤ T₁ → 0 ≤ C₁ → 0 ≤ A₀' → 8 ≤ T₁' → 0 ≤ C₁' → 1 < lam → 0 < δ →
      ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        ∀ Z Z' : ZeroConfig,
          HasRvMLocalCount Z A₀ T₁ C₁ → HasRvMLocalCount Z' A₀' T₁' C₁' →
          (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
          ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
            ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
              ‖z - z₀‖ < δ / Real.log T) ∧
    (∀ A₀ T₁ C₁ A₀' lam δ : ℝ,
      0 ≤ A₀ → 8 ≤ T₁ → 0 ≤ C₁ → 0 ≤ A₀' → 1 / 2 < lam → 0 < δ →
      ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        ∀ Z Z' : ZeroConfig,
          HasRvMLocalCount Z A₀ T₁ C₁ →
          (∀ t : ℝ, (Z'.N t (t + 1) : ℝ) ≤ A₀' * Real.log (|t| + 3)) →
          (∀ z ∈ Z'.carrier, |z.im - T| ≤ T / 2 → z ∈ Z.carrier) →
          (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
          ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff Z Z' z₀ ≠ 0 →
            ∃ z, z ≠ z₀ ∧ multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
              ‖z - z₀‖ < δ / Real.log T) :=
  ⟨fun _ _ hT hlam0 hlam1 => exists_rvm_pair_mimic_disjoint_up_to_one hT hlam0 hlam1,
    fun _ _ _ _ _ _ _ _ hA₀ hT₁ hC₁ hA₀' hT₁' hC₁' hlam hδ =>
      rvm_pair_coincide_outside_nearCollisions_above_one hA₀ hT₁ hC₁ hA₀' hT₁' hC₁' hlam hδ,
    fun _ _ _ _ _ _ hA₀ hT₁ hC₁ hA₀' hlam hδ =>
      rvm_subset_carrier_coincide_at_squareRoot_littleO hA₀ hT₁ hC₁ hA₀' hlam hδ⟩

/-! ### 5. Unconditional `ζ` corollaries and single-zero multiplicity readout at `λ > ½` -/

/-- **Unconditional `o(1 / log T)` coincidence for `ζ` against mimics of extra-carrier density `μ`
at `λ > (1 + μ) / 2`.** -/
theorem zeta_coincide_of_extra_density_littleO {A₀' μ A' lam δ : ℝ}
    (hA₀' : 0 ≤ A₀') (hμ : 0 ≤ μ) (hA' : 0 ≤ A')
    (hlam : (1 + μ) / 2 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z' : ZeroConfig,
        (∀ t : ℝ, (Z'.N t (t + 1) : ℝ) ≤ A₀' * Real.log (|t| + 3)) →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, z ∈ Z'.carrier ∧ ¬ IsNontrivialZero z ∧ |z.im - T| ≤ T / 2 ∧
            z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ μ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A' * Real.log (T / (2 * π))) →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f →
          zetaZeroConfig.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff zetaZeroConfig Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff zetaZeroConfig Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  obtain ⟨A₀, T₁, C₁, hζ⟩ := exists_hasRvMLocalCount_zeta
  obtain ⟨T₀, hT₀1, hco⟩ := rvm_coincide_of_extra_density_littleO
    hζ.nonneg_A₀ hζ.eight_le_T₁ hζ.nonneg_C₁ hA₀' hμ hA' hlam hδ
  refine ⟨T₀, hT₀1, fun T hT Z' hZ'u hextra hW z₀ hz₀ hc => ?_⟩
  exact hco T hT zetaZeroConfig Z' hζ hZ'u hextra hW z₀ hz₀ hc

/-- **Unconditional square-root threshold (`λ > ½`) coincidence for `ζ` on subset carriers.** -/
theorem zeta_coincide_subset_carrier_at_squareRoot_littleO {A₀' lam δ : ℝ}
    (hA₀' : 0 ≤ A₀') (hlam : 1 / 2 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z' : ZeroConfig,
        (∀ t : ℝ, (Z'.N t (t + 1) : ℝ) ≤ A₀' * Real.log (|t| + 3)) →
        (∀ z ∈ Z'.carrier, |z.im - T| ≤ T / 2 → IsNontrivialZero z) →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f →
          zetaZeroConfig.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff zetaZeroConfig Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff zetaZeroConfig Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  obtain ⟨A₀, T₁, C₁, hζ⟩ := exists_hasRvMLocalCount_zeta
  obtain ⟨T₀, hT₀1, hco⟩ := rvm_subset_carrier_coincide_at_squareRoot_littleO
    hζ.nonneg_A₀ hζ.eight_le_T₁ hζ.nonneg_C₁ hA₀' hlam hδ
  exact ⟨T₀, hT₀1, fun T hT Z' hZ'u hsub hW z₀ hz₀ hc =>
    hco T hT zetaZeroConfig Z' hζ hZ'u hsub hW z₀ hz₀ hc⟩

/-- **Unconditional `λ > 1` coincidence for `ζ` against arbitrary RvM configurations.** -/
theorem zeta_coincide_with_rvm_above_one_littleO {A₀' T₁' C₁' lam δ : ℝ}
    (hA₀' : 0 ≤ A₀') (hT₁' : 8 ≤ T₁') (hC₁' : 0 ≤ C₁')
    (hlam : 1 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z' : ZeroConfig, HasRvMLocalCount Z' A₀' T₁' C₁' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f →
          zetaZeroConfig.W f f = Z'.W f f) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → multDiff zetaZeroConfig Z' z₀ ≠ 0 →
          ∃ z, z ≠ z₀ ∧ multDiff zetaZeroConfig Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧
            ‖z - z₀‖ < δ / Real.log T := by
  obtain ⟨A₀, T₁, C₁, hζ⟩ := exists_hasRvMLocalCount_zeta
  obtain ⟨T₀, hT₀1, hco⟩ := rvm_pair_coincide_outside_nearCollisions_above_one
    hζ.nonneg_A₀ hζ.eight_le_T₁ hζ.nonneg_C₁ hA₀' hT₁' hC₁' hlam hδ
  exact ⟨T₀, hT₀1, fun T hT Z' hZ' hW z₀ hz₀ hc =>
    hco T hT zetaZeroConfig Z' hζ hZ' hW z₀ hz₀ hc⟩

/-- **Unconditional polynomial-isolation multiplicity readout for `ζ` at the square-root threshold
`λ > ½`.**
For every `λ > ½` and `M ≥ 0`, uniformly for `T ≥ T₀`, every nontrivial zero `ρ₀` of `ζ` in
`|Im ρ₀ − T| ≤ T / 4` that is `T^{−M}`-isolated from all other nontrivial zeros of `ζ` in
`[T / 2, 3T / 2]` admits windows `F, G` of aperture `λ · ½ log(T / 2π)` with `zetaZeroConfig.W F G ≠ 0`
and `‖zetaZeroConfig.W F G / pointImage F G ρ₀ − zeroMult ρ₀‖ ≤ 1 / 4`. -/
theorem zeta_isolated_zero_multiplicity_readout_at_squareRoot_rpow {lam M : ℝ}
    (hlam : 1 / 2 < lam) (hM : 0 ≤ M) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ ρ₀ : ℂ, IsNontrivialZero ρ₀ → |ρ₀.im - T| ≤ T / 4 →
        (∀ ρ : ℂ, IsNontrivialZero ρ → ρ ≠ ρ₀ → |ρ.im - T| ≤ T / 2 → T ^ (-M) ≤ ‖ρ - ρ₀‖) →
        ∃ F G : ℝ → ℂ,
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
          pointImage F G ρ₀ ≠ 0 ∧
          zetaZeroConfig.W F G ≠ 0 ∧
          (∀ ρ : ℂ, IsNontrivialZero ρ → ρ ≠ ρ₀ → |ρ.im - ρ₀.im| ≤ T / 4 →
            pointImage F G ρ = 0) ∧
          ‖zetaZeroConfig.W F G / pointImage F G ρ₀ - (zeroMult ρ₀ : ℂ)‖ ≤ 1 / 4 := by
  obtain ⟨A₀, T₁, C₁, hζ⟩ := exists_hasRvMLocalCount_zeta
  obtain ⟨hZt, _, hStail⟩ :=
    temperedConfig_and_tsum_le_of_unit_window_count zetaZeroConfig hζ.nonneg_A₀ hζ.unit_window
  obtain ⟨δ', hδ'def⟩ : ∃ δ', δ' = lam - 1 / 2 := ⟨_, rfl⟩
  have hδ' : 0 < δ' := by rw [hδ'def]; linarith
  have hθ0 : 0 ≤ 1 + δ' := by positivity
  have hθlam : (1 + δ') / 2 < lam := by rw [hδ'def]; linarith
  have hW0 : 0 ≤ WeilEF.totalWeight :=
    tsum_nonneg fun n =>
      div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  obtain ⟨T_rd, hT_rd1, hrd⟩ := exists_window_pair_reads_mult_subspacing
    (θ := 1 + δ') (lam := lam) (A := 8 * C₁ + 2)
    (S := 4 * max A₀ 1 * WeilEF.totalWeight) (M := M)
    hθ0 hθlam (by linarith [hζ.nonneg_C₁]) (by positivity) hM
  refine ⟨max T_rd (max T₁ (2 * π * Real.exp (max 1 (1 / δ')))),
    hT_rd1.trans (le_max_left _ _),
    fun T hT ρ₀ hρ₀ hz₀ hiso => ?_⟩
  have h2π : 0 < 2 * π := by positivity
  have hT_c : T_rd ≤ T := (le_max_left _ _).trans hT
  have hT_1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT_u : 2 * π * Real.exp (max 1 (1 / δ')) ≤ T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hu_ge : max 1 (1 / δ') ≤ Real.log (T / (2 * π)) := by
    rw [← Real.log_exp (max 1 (1 / δ'))]
    exact Real.log_le_log (Real.exp_pos _) ((le_div_iff₀ h2π).mpr (by linarith))
  have hcard := card_carrier_le_of_hasRvMLocalCount hζ hδ' hT_1
    ((le_max_left _ _).trans hu_ge) ((le_max_right _ _).trans hu_ge)
  exact hrd T hT_c zetaZeroConfig hZt hStail hcard ρ₀ hρ₀ hz₀ hiso

/-- **Unconditional `o(1 / log T)`-isolation multiplicity readout for `ζ` at the square-root
threshold `λ > ½`.** -/
theorem zeta_isolated_zero_multiplicity_readout_at_squareRoot_littleO {lam δ : ℝ}
    (hlam : 1 / 2 < lam) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ ρ₀ : ℂ, IsNontrivialZero ρ₀ → |ρ₀.im - T| ≤ T / 4 →
        (∀ ρ : ℂ, IsNontrivialZero ρ → ρ ≠ ρ₀ → |ρ.im - T| ≤ T / 2 →
          δ / Real.log T ≤ ‖ρ - ρ₀‖) →
        ∃ F G : ℝ → ℂ,
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
          pointImage F G ρ₀ ≠ 0 ∧
          zetaZeroConfig.W F G ≠ 0 ∧
          (∀ ρ : ℂ, IsNontrivialZero ρ → ρ ≠ ρ₀ → |ρ.im - ρ₀.im| ≤ T / 4 →
            pointImage F G ρ = 0) ∧
          ‖zetaZeroConfig.W F G / pointImage F G ρ₀ - (zeroMult ρ₀ : ℂ)‖ ≤ 1 / 4 := by
  obtain ⟨T₁, hT₁1, hrpow⟩ := zeta_isolated_zero_multiplicity_readout_at_squareRoot_rpow (M := 1)
    hlam (by norm_num)
  refine ⟨max T₁ (2 / δ * max 0 (Real.log (2 / δ))), hT₁1.trans (le_max_left _ _),
    fun T hT ρ₀ hρ₀ hz₀ hiso => ?_⟩
  have hT3 : 3 ≤ T := by
    have : 2 * π * 1 ≤ 2 * π * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.one_le_exp zero_le_one) (by positivity)
    linarith [Real.pi_gt_three, hT₁1.trans ((le_max_left _ _).trans hT)]
  have hTδ : 2 / δ * max 0 (Real.log (2 / δ)) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hle : T ^ (-1 : ℝ) ≤ δ / Real.log T := by
    have h := log_le_mul_add_log_inv hT0 (show 0 < δ / 2 by positivity)
    rw [show (δ / 2)⁻¹ = 2 / δ by field_simp] at h
    have h1 : Real.log (2 / δ) ≤ max 0 (Real.log (2 / δ)) := le_max_right _ _
    have h2 : max 0 (Real.log (2 / δ)) ≤ δ / 2 * T := by
      calc max 0 (Real.log (2 / δ)) = δ / 2 * (2 / δ * max 0 (Real.log (2 / δ))) := by field_simp
        _ ≤ δ / 2 * T := mul_le_mul_of_nonneg_left hTδ (by positivity)
    rw [Real.rpow_neg_one, inv_eq_one_div, div_le_div_iff₀ hT0 hlog0]
    linarith
  exact hrpow T ((le_max_left _ _).trans hT) ρ₀ hρ₀ hz₀ fun ρ hρ hne hzR =>
    hle.trans (hiso ρ hρ hne hzR)

end GaloisForLFunctions.ZeroConfigurationGeometry
