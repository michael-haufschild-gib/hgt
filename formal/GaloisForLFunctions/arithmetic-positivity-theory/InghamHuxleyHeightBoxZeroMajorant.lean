import GaloisForLFunctions.«arithmetic-positivity-theory».ZeroDiskOverlap
import GaloisForLFunctions.RHTower.XiZeroFoldedHeightCount
import GaloisForLFunctions.RHTower.ZetaZeroDensityInghamHuxley
import GaloisForLFunctions.RHTower.XiZeroFreeHeightBox
import GaloisForLFunctions.RHTower.ZeroLatticeDepthNyquistLaw

/-!
# Ingham–Huxley Height-Box Zero Majorant, Route-T Slab Truncation, and Nyquist Aperture Law

This module connects `ArithmeticPositivityTheory` to the unconditional abscissa-sensitive zero-density,
zero-free region, and Nyquist lattice theorems in `RHTower/`:

1. **Route-T Zero-Free Annihilation of High-Abscissa Height Boxes
   (`exists_zeroHeightBox_eq_empty_of_gt_routeT`, `exists_zeroHeightBox_ncard_eq_zero_of_gt_routeT`):**
   Using `RHTower.exists_zeroHeightBox_zeroFree` (`XiZeroFreeHeightBox.lean:27`), there exist
   `A, T₁ : ℝ` (`1 ≤ T₁`) such that for every `T ≥ T₁` and every abscissa
   `σ > 1 - routeTWidthPolylogLower A (4 * T / 3)`, the height box `zeroHeightBox σ T` is empty
   and `(zeroHeightBox σ T).ncard = 0`.

2. **Route-T Truncated Folded Layer-Cake Majorant
   (`exists_sum_rpow_re_le_zeroHeightBox_routeT_filter`):**
   Combining `RHTower.sum_rpow_re_le_zeroHeightBox` (`XiZeroFoldedHeightCount.lean:152`) with
   Route-T zero-free annihilation truncates the `M`-slab layer-cake sum for `∑ q ∈ G, x ^ (re q - 1)`
   on any dyadic height shell `T ≤ |im q| ≤ 2 * T` (`T ≥ T₁`) to slabs satisfying
   `slabAbscissa M m ≤ 1 - routeTWidthPolylogLower A (4 * T / 3)`.

3. **Ingham–Huxley Density Bound on Individual Abscissa Slabs
   (`exists_slab_zeroHeightBox_ncard_le_ingham_huxley`):**
   Applies `RHTower.exists_zeroHeightBox_ncard_le_ingham_huxley` (`ZetaZeroDensityInghamHuxley.lean:226`)
   to every strictly off-line slab `slabAbscissa M m` (`1 ≤ m ≤ M`), replacing the abscissa-blind
   $O(\log T)$ bound of `ZeroDiskOverlap.lean` by the $(1 - \sigma)$-weighted Ingham–Huxley exponent.

4. **Nyquist Support Threshold for Off-Line Vertical Zero Lattices
   (`offLineLattice_weil_positive_iff_aperture_le_half_period`,
   `exists_re_W_offLineLattice_neg_of_gt_half_period`):**
   Connects `RHTower.offLineLattice_weil_positive_iff` (`ZeroLatticeDepthNyquistLaw.lean:608`) to
   `ArithmeticPositivityTheory`, certifying that `a = L / 2` is the exact support threshold at which
   compactly supported `C²` test functions detect an off-line vertical zero lattice of spacing `2π / L`.
-/

open Complex MeasureTheory Set Filter Finset
open scoped BigOperators Topology
open _root_.RHTower _root_.RHTower.Sieve

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-! ## §1. Route-T Zero-Free Annihilation of High-Abscissa Height Boxes -/

/-- **Route-T Zero-Free Emptiness of High-Abscissa Height Boxes
(`exists_zeroHeightBox_eq_empty_of_gt_routeT`):**
There exist `A, T₁ : ℝ` with `1 ≤ T₁` such that for all `T ≥ T₁` and all
`σ > 1 - routeTWidthPolylogLower A (4 * T / 3)`, `zeroHeightBox σ T = ∅`. -/
theorem exists_zeroHeightBox_eq_empty_of_gt_routeT :
    ∃ A T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T → ∀ σ : ℝ,
      1 - routeTWidthPolylogLower A (4 * T / 3) < σ →
        zeroHeightBox σ T = ∅ := by
  obtain ⟨A, T₁, hT₁, hzf⟩ := exists_zeroHeightBox_zeroFree
  refine ⟨A, T₁, hT₁, fun T hT σ hσ => ?_⟩
  by_contra hne
  have hnonempty : (zeroHeightBox σ T).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hle := hzf T hT σ hnonempty
  linarith

/-- **Route-T Zero-Free Cardinality Vanishing (`exists_zeroHeightBox_ncard_eq_zero_of_gt_routeT`):**
There exist `A, T₁ : ℝ` with `1 ≤ T₁` such that for all `T ≥ T₁` and all
`σ > 1 - routeTWidthPolylogLower A (4 * T / 3)`, `(zeroHeightBox σ T).ncard = 0`. -/
theorem exists_zeroHeightBox_ncard_eq_zero_of_gt_routeT :
    ∃ A T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T → ∀ σ : ℝ,
      1 - routeTWidthPolylogLower A (4 * T / 3) < σ →
        (zeroHeightBox σ T).ncard = 0 := by
  obtain ⟨A, T₁, hT₁, hemp⟩ := exists_zeroHeightBox_eq_empty_of_gt_routeT
  refine ⟨A, T₁, hT₁, fun T hT σ hσ => ?_⟩
  rw [hemp T hT σ hσ, Set.ncard_empty]

/-! ## §2. Route-T Truncated Folded Layer-Cake Majorant -/

/-- **Route-T Truncated Folded Layer-Cake Majorant
(`exists_sum_rpow_re_le_zeroHeightBox_routeT_filter`):**
Combines `sum_rpow_re_le_zeroHeightBox` (`XiZeroFoldedHeightCount.lean:152`) with Route-T
zero-free annihilation (`exists_zeroHeightBox_ncard_eq_zero_of_gt_routeT`) so that slabs with
`slabAbscissa M m > 1 - routeTWidthPolylogLower A (4 * T / 3)` drop out identically. -/
theorem exists_sum_rpow_re_le_zeroHeightBox_routeT_filter :
    ∃ A T₁ : ℝ, 1 ≤ T₁ ∧ ∀ {T : ℝ}, T₁ ≤ T → ∀ {x : ℝ}, 1 ≤ x → ∀ {M : ℕ}, 0 < M →
      ∀ (G : Finset XiZeroCopy),
        (∀ q ∈ G, T ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * T) →
        ∑ q ∈ G, x ^ ((q.1 : ℂ).re - 1) ≤
          4 * ∑ m ∈ (Finset.range M).filter
              (fun m => slabAbscissa M m ≤ 1 - routeTWidthPolylogLower A (4 * T / 3)),
            x ^ (slabAbscissa M (m + 1) - 1) *
              ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ) := by
  obtain ⟨A, T₁, hT₁, hzero⟩ := exists_zeroHeightBox_ncard_eq_zero_of_gt_routeT
  refine ⟨A, T₁, hT₁, fun {T} hT {x} hx {M} hM G hG => ?_⟩
  refine (sum_rpow_re_le_zeroHeightBox hx hM G hG).trans (le_of_eq ?_)
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hle : slabAbscissa M m ≤ 1 - routeTWidthPolylogLower A (4 * T / 3)
  · rw [if_pos hle]
  · rw [if_neg hle, hzero T hT (slabAbscissa M m) (lt_of_not_ge hle), Nat.cast_zero, mul_zero]

/-! ## §3. Ingham–Huxley Density Bounds on Abscissa Slabs -/

/-- For `1 ≤ m ≤ M`, the slab abscissa `slabAbscissa M m = 1/2 + m / (2M)` lies strictly inside
`(1/2, 1]`. -/
theorem slabAbscissa_mem_Ioc {M m : ℕ} (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    1 / 2 < slabAbscissa M m ∧ slabAbscissa M m ≤ 1 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmle : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  unfold slabAbscissa
  constructor
  · have : (0 : ℝ) < (m : ℝ) / (2 * (M : ℝ)) := div_pos hmpos (by positivity)
    linarith
  · have : (m : ℝ) / (2 * (M : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith

/-- **Ingham–Huxley Density Bound for Off-Line Abscissa Slabs
(`exists_slab_zeroHeightBox_ncard_le_ingham_huxley`):**
For every `M, m : ℕ` with `1 ≤ m ≤ M` and every `0 < ε ≤ 1`, the number of zeros in the height box
`zeroHeightBox (slabAbscissa M m) T` satisfies the unconditional Ingham–Huxley density bound with
exponent `(inghamHuxleyExponent (slabAbscissa M m) + ε) * (1 - slabAbscissa M m)`. -/
theorem exists_slab_zeroHeightBox_ncard_le_ingham_huxley {M m : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ((zeroHeightBox (slabAbscissa M m) T).ncard : ℝ) ≤
          D * (1 + Real.log T) ^ B *
            T ^ ((inghamHuxleyExponent (slabAbscissa M m) + ε) * (1 - slabAbscissa M m)) := by
  obtain ⟨hσ, hσ1⟩ := slabAbscissa_mem_Ioc hm1 hmM
  exact exists_zeroHeightBox_ncard_le_ingham_huxley hσ hσ1 hε hε1

/-! ## §4. Nyquist Support Threshold for Off-Line Vertical Zero Lattices -/

/-- **Nyquist Support Equivalence for Off-Line Vertical Zero Lattices
(`offLineLattice_weil_positive_iff_aperture_le_half_period`):**
For any vertical lattice period `L > 0`, off-line depth `0 < δ ≤ 1/2`, and support radius `a : ℝ`,
the off-line lattice `offLineLatticeConfig hL hδ hδ'` has non-negative Weil form on all `C²` test
functions supported in `[-a, a]` if and only if `a ≤ L / 2`. -/
theorem offLineLattice_weil_positive_iff_aperture_le_half_period {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (a : ℝ) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((offLineLatticeConfig hL hδ hδ').W f f).re) ↔ a ≤ L / 2 :=
  offLineLattice_weil_positive_iff hL hδ hδ' a

/-- **Super-Nyquist Negative Witness for Off-Line Vertical Zero Lattices
(`exists_re_W_offLineLattice_neg_of_gt_half_period`):**
Whenever the support radius exceeds the Nyquist half-period (`L / 2 < a`), there exists a `C²` test
function supported in `[-a, a]` on which the Weil form of `offLineLatticeConfig hL hδ hδ'` is
strictly negative. -/
theorem exists_re_W_offLineLattice_neg_of_gt_half_period {L δ a : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (ha : L / 2 < a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      ((offLineLatticeConfig hL hδ hδ').W f f).re < 0 :=
  exists_re_W_offLineLatticeConfig_neg hL hδ hδ' ha

end

end GaloisForLFunctions.ArithmeticPositivityTheory
