import GaloisForLFunctions.ArithmeticIncidencePositivity.GlobalSharedSurplusAllocation
import GaloisForLFunctions.ArithmeticIncidencePositivity.SharedDerivativeEnergyAndGlobalAllocationSynthesis
import GaloisForLFunctions.RHTower.Sieve.PrimeInterval

/-!
# The Shared Surplus Between the Light Cone and the Thin Band: Capacity Law, Square-Root Width, and Signed Band Obstruction

This module resolves Open Problem 6 (a), (b), and (c) of `ArithmeticIncidencePositivity`:

1. **Two-Sided Logarithmic Capacity Law for Nested Strips (`IsPayableOddPartFamily`,
   `sum_geometricChain_oddPart_le_stripBoxEnergy`, `exists_payableOddPartFamily_log_lower_bound`,
   `sum_le_of_isPayableOddPartFamily`)**:
   - For any geometric chain of nested strips `S_j = [L_j − r, r]` (`L_j = 2(r − η_0 / 6^j)`,
     `0 < η_0 ≤ 1/12`, `r ≥ 7/6`), the corner width ratio `(r − p')/(p' − L/2) = 2η'/(η − 2η') = 1/2`
     is scale-invariant in `η`, giving a uniform shell fold constant `≥ 7/10` at every layer `j`.
     Telescoping the disjoint shells proves that for **every** continuous Lipschitz test `F` on
     `[0, r]`,
     `∑_{j=0}^N (7/10) ∫_{L_j − r}^r α_{L_j}² ≤ stripBoxEnergy F (L_0 − r) r ≤ stripBoxEnergy F 0 r`.
   - Consequently, the maximum total weight of nested strips wider than `ε` payable by one copy of
     `stripBoxEnergy F 0 r` across all tests satisfies the unconditional two-sided logarithmic law
     `(7 / (10 log 6)) log(1/(12ε)) ≤ Capacity(r, ε) ≤ 2 log(4/ε) + 84`.

2. **Exact Square-Root Width `δ ≍ e^{−r}` of the Light Cone (`eventually_sum_vonMangoldtAtom_lightConeBand_le_squareRoot`,
   `exists_squareRoot_lightCone_allocation`, `frequently_lightConeBox_oddPart_sharing_fails_at_squareRoot`)**:
   - Combining the Selberg-sieve prime interval bound (`RHTower.Sieve.card_prime_Ioc_le`) at level
     `Y = z = ⌊e^{r/3}⌋₊` with short-interval exponent injectivity on proper prime powers removes the
     `1/r` factor from `PrimeLightConeAllocation`: for all large `r` with `c₀ = 1/60`, and uniformly
     for all `r ≥ 2` with an explicit `c₀ > 0`, `∑_{lightConeBand r δ} 2Λ(n)/√n ≤ 16/10`,
     `sum_primeShift_le_lightCone`, and `tsum_primeShift_le_globalAllocation` hold for all
     `0 < δ ≤ c₀ e^{−r}`.
   - Conversely, on the local light-cone box `[r − 2δ, r]²`, the scaled edge tent
     `edgeTentOdd r (δ/2)` has `stripBoxEnergy (edgeTentOdd r (δ/2)) (r − 2δ) r ≤ 6 δ³`, while
     each odd part in the outer half `2r − 2δ ≤ log n ≤ 2r − δ` carries `≥ δ³/512`. The `δ³` factors
     cancel identically, and tiling `thinBand R` via the Intermediate Value Theorem on
     `g(r) = 2r − C e^{−r}` together with the Prime Number Theorem proves that for every `C ≥ 64000`
     there exist arbitrarily large apertures `r` (`∃ᶠ r in atTop`) where `T(r − 2 C e^{−r}, r)` fails
     to pay the odd parts at the exact square-root width `δ = C e^{−r}`.

3. **Unconditional Refutation of Signed Thin-Band Allocation via the Bipolar Edge-Dipole Witness
   (`bipolarEdgeTentOdd`, `exists_bipolarEdgeTent_signed_thinBand_sharing_fails`,
   `thinBand_signedCharge_eq_tsum_sub_complement`)**:
   - On the single edge tent `edgeTentOdd`, the even and odd strip parts cancel identically on
     `thinBand r` (`∫ F(x) F(x + log n) dx = 0`), leaving open whether keeping the even parts makes
     the signed inequality `∑_{n ∈ thinBand r} 2Λ(n)/√n ∫ F(x) F(x + log n) dx ≤ stripBoxEnergy F 0 r`
     hold unconditionally.
   - We construct the **bipolar edge-dipole witness**
     `bipolarEdgeTentOdd r x = edgeTentOdd r (1/48) x − edgeTentOdd (r − 1/12) (1/12) x`. Because the
     positive tent lives on `I₊ = (r − 1/48, r)` with `I₊ + I₊ = (2r − 1/24, 2r)` above `thinBand r`
     and the negative tent lives on `I₋ = (r − 1/6, r − 1/12)` with `I₋ + I₋ = (2r − 1/3, 2r − 1/6)`
     below `thinBand r`, every shift `L ∈ [2r − 1/6, 2r − 1/24]` couples only `−I₊` to `I₋` and
     `−I₋` to `I₊`, where `F(x)` and `F(x + L)` have the same sign. Thus `F(x) F(x + L) ≥ 0`
     pointwise on `ℝ` for every `n ∈ thinBand r`, and on the core sub-band
     `2r − 7/48 ≤ log n ≤ 2r − 1/8` (`⊆ thinBand r`) the correlation is at least `1/884736`, while
     `stripBoxEnergy F 0 r ≤ r`. By the Prime Number Theorem, for all large `r`, the signed
     `thinBand r` sum strictly exceeds `stripBoxEnergy F 0 r`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ## Part I: Universal Telescoping Chain and Two-Sided Logarithmic Capacity Law -/

/-- General bound on `|stripIntegrand F x y|` on `[0, r]²` for any `r ≥ 0` (without `r ≤ 1`),
using `archLevyDensity t ≤ 1/(2t) + 1/4` for all `t > 0`. -/
theorem abs_stripIntegrand_le_of_lipschitz {F : ℝ → ℝ} {K r x y : ℝ}
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hx : x ∈ Icc 0 r) (hy : y ∈ Icc 0 r) :
    0 ≤ stripIntegrand F x y ∧
      |stripIntegrand F x y| ≤ K ^ 2 * (r / 2 + r ^ 2 / 4) := by
  have hr0 : 0 ≤ r := hx.1.trans hx.2
  have hR0 : 0 ≤ K ^ 2 * (r / 2 + r ^ 2 / 4) := by positivity
  unfold stripIntegrand
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, abs_zero]
    exact ⟨le_rfl, hR0⟩
  have hk0 := surplusKernel_nonneg' hx.1 hy.1 hxy
  have hnonneg : 0 ≤ surplusKernel x y * (F x - F y) ^ 2 := mul_nonneg hk0 (sq_nonneg _)
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg]
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · rw [surplusKernel_zero_left hy.1, zero_mul]; exact hR0
  rcases eq_or_lt_of_le hy.1 with rfl | hy0
  · rw [surplusKernel_comm, surplusKernel_zero_left hx.1, zero_mul]; exact hR0
  have hd0 : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hdr : |x - y| ≤ r := by
    rw [abs_le]
    exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  have hk := (surplusKernel_le hx0 hy0).trans (archLevyDensity_le_inv hd0)
  have hlip := hFL x y
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg (F x - F y)).trans hlip
    exact nonneg_of_mul_nonneg_left this hd0
  have hsq : (F x - F y) ^ 2 ≤ (K * |x - y|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hlip 2
  have hprod : surplusKernel x y * (F x - F y) ^ 2 ≤
      (1 / (2 * |x - y|) + 1 / 4) * (K * |x - y|) ^ 2 :=
    mul_le_mul hk hsq (sq_nonneg _) (by positivity)
  have hexp : (1 / (2 * |x - y|) + 1 / 4) * (K * |x - y|) ^ 2 =
      K ^ 2 * (|x - y| / 2 + |x - y| ^ 2 / 4) := by
    have hd_ne : |x - y| ≠ 0 := hd0.ne'
    field_simp
  have hd2 : |x - y| ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hd0.le hdr 2
  nlinarith

theorem shellIntegrand_nonneg_of_nonneg (F : ℝ → ℝ) (p' : ℝ) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ shellIntegrand F p' x y := by
  unfold shellIntegrand
  split_ifs
  · exact le_rfl
  · unfold stripIntegrand
    by_cases hxy : x = y
    · rw [hxy, sub_self]; simp
    · exact mul_nonneg (surplusKernel_nonneg' hx hy hxy) (sq_nonneg _)

/-- Removing the inner box on `[p, r]²` for any `0 ≤ p ≤ p' ≤ r` (without `r - p ≤ 1`). -/
theorem integral_shellIntegrand_eq_of_nonneg {F : ℝ → ℝ} {K p p' r : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp0 : 0 ≤ p) (hpp' : p ≤ p') (hp'r : p' ≤ r) :
    (∫ x in p..r, ∫ y in p..r, shellIntegrand F p' x y) =
      stripBoxEnergy F p r - stripBoxEnergy F p' r := by
  have hpr : p ≤ r := hpp'.trans hp'r
  set C := K ^ 2 * (r / 2 + r ^ 2 / 4)
  have hmg := measurable_stripIntegrand hF
  have hbd : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |stripIntegrand F x y| ≤ C := fun x hx y hy =>
    (abs_stripIntegrand_le_of_lipschitz hFL ⟨hp0.trans hx.1, hx.2⟩ ⟨hp0.trans hy.1, hy.2⟩).2
  have hbs : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |shellIntegrand F p' x y| ≤ C := fun x hx y hy =>
    (abs_shellIntegrand_le F p' x y).trans (hbd x hx y hy)
  obtain ⟨hgi, hgo⟩ := intervalIntegrable_iterated hpr hmg hbd
  obtain ⟨hsi, hso⟩ := intervalIntegrable_iterated hpr (measurable_shellIntegrand hF p') hbs
  obtain ⟨-, hgo'⟩ := intervalIntegrable_iterated hp'r hmg fun x hx y hy =>
    hbd x ⟨hpp'.trans hx.1, hx.2⟩ y ⟨hpp'.trans hy.1, hy.2⟩
  have hsub1 : uIcc p p' ⊆ uIcc p r := by
    rw [uIcc_of_le hpp', uIcc_of_le hpr]; exact Icc_subset_Icc le_rfl hp'r
  have hsub2 : uIcc p' r ⊆ uIcc p r := by
    rw [uIcc_of_le hp'r, uIcc_of_le hpr]; exact Icc_subset_Icc hpp' le_rfl
  have hlow : (∫ x in p..p', ∫ y in p..r, shellIntegrand F p' x y) =
      ∫ x in p..p', ∫ y in p..r, stripIntegrand F x y := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hpp'] at hx
    have e : shellIntegrand F p' x = stripIntegrand F x := funext fun y => by
      unfold shellIntegrand; rw [if_neg fun h => absurd h.1 (not_lt.mpr hx.2)]
    rw [e]
  have hhigh : (∫ x in p'..r, ∫ y in p..r, shellIntegrand F p' x y) =
      ∫ x in p'..r, ((∫ y in p..r, stripIntegrand F x y) - ∫ y in p'..r, stripIntegrand F x y) := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hp'r] at hx
    have hxI : x ∈ Icc p r := ⟨hpp'.trans hx.1.le, hx.2⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ((hsi x hxI).mono_set hsub1)
        ((hsi x hxI).mono_set hsub2),
      ← intervalIntegral.integral_add_adjacent_intervals ((hgi x hxI).mono_set hsub1)
        ((hgi x hxI).mono_set hsub2)]
    have e1 : (∫ y in p..p', shellIntegrand F p' x y) = ∫ y in p..p', stripIntegrand F x y := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
      rw [uIoc_of_le hpp'] at hy
      unfold shellIntegrand; rw [if_neg fun h => absurd h.2 (not_lt.mpr hy.2)]
    have e2 : (∫ y in p'..r, shellIntegrand F p' x y) = ∫ _ in p'..r, (0 : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun y hy => ?_)
      rw [uIoc_of_le hp'r] at hy
      unfold shellIntegrand; rw [if_pos ⟨hx.1, hy.1⟩]
    rw [e1, e2, intervalIntegral.integral_zero]
    ring
  unfold stripBoxEnergy
  rw [← intervalIntegral.integral_add_adjacent_intervals (hso.mono_set hsub1) (hso.mono_set hsub2),
    hlow, hhigh, intervalIntegral.integral_sub (hgo.mono_set hsub2) hgo',
    ← intervalIntegral.integral_add_adjacent_intervals (hgo.mono_set hsub1) (hgo.mono_set hsub2)]
  ring

/-- **Nested box monotonicity on `[0, r]` without `r ≤ 1`.** For `0 ≤ p ≤ p' ≤ r` and any
continuous `K`-Lipschitz `F`, `stripBoxEnergy F p' r ≤ stripBoxEnergy F p r`. -/
theorem stripBoxEnergy_mono_of_nonneg {F : ℝ → ℝ} {K p p' r : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp0 : 0 ≤ p) (hpp' : p ≤ p') (hp'r : p' ≤ r) :
    stripBoxEnergy F p' r ≤ stripBoxEnergy F p r := by
  have h := integral_shellIntegrand_eq_of_nonneg hF hFL hp0 hpp' hp'r
  have h0 : 0 ≤ ∫ x in p..r, ∫ y in p..r, shellIntegrand F p' x y :=
    intervalIntegral.integral_nonneg (hpp'.trans hp'r) fun x hx =>
      intervalIntegral.integral_nonneg (hpp'.trans hp'r) fun y hy =>
        shellIntegrand_nonneg_of_nonneg F p' (hp0.trans hx.1) (hp0.trans hy.1)
  linarith

/-- **Scale-invariant shell micro-fold at geometric ratio `6`.** For any strip of half-width
`0 < η ≤ 1/12` at aperture `r ≥ 7/6`, with `L = 2(r − η)`, outer left endpoint `p = L − r = r − 2η`,
and inner left endpoint `p' = r − 2(η/6)`, the corner width ratio is `(r − p')/(p' − L/2) = 1/2`
independently of `η`, so the shell `[p, r]² \ (p', r]²` pays the odd part with constant `≥ 7/10`. -/
theorem sharpMicroFold_ratioSix_shell_ge {F : ℝ → ℝ} {K r η : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hr : 7 / 6 ≤ r) (hη0 : 0 < η) (hη12 : η ≤ 1 / 12) :
    (7 / 10 : ℝ) * (∫ a in (2 * (r - η) - r)..r, reflectedOddPart F (2 * (r - η)) a ^ 2) ≤
      stripBoxEnergy F (2 * (r - η) - r) r - stripBoxEnergy F (2 * (r - η / 6) - r) r := by
  set L := 2 * (r - η)
  set p := L - r
  set p' := 2 * (r - η / 6) - r
  have hp1 : 1 ≤ p := by dsimp [p, L]; linarith
  have hp0 : 0 < p := by linarith
  have hpr : p < r := by dsimp [p, L]; linarith
  have hL : p + r = L := by dsimp [p]; ring
  have hr3 : r - p ≤ 2 * p := by dsimp [p, L]; linarith
  have hr6 : r - p ≤ 1 / 6 := by dsimp [p, L]; linarith
  have hc : L / 2 < p' := by dsimp [p', L]; linarith
  have hp'r : p' ≤ r := by dsimp [p']; linarith
  have hshell := sharpMicroFold_shell_ge hF hFL hp0 hpr hL hr3 hr6 hc hp'r
  have h1 : r - p' = η / 3 := by dsimp [p']; ring
  have h2 : (r - p) / 2 = η := by dsimp [p, L]; ring
  have h3 : p' - L / 2 = 2 * η / 3 := by dsimp [p', L]; ring
  have hratio : (r - p') * ((2 + (r - p) / 2 / 2) / (p' - L / 2) + 1) = 1 + 7 * η / 12 := by
    rw [h1, h2, h3]
    have hη_ne : η ≠ 0 := hη0.ne'
    field_simp
    ring
  have hηp : (r - p) / 2 / p ≤ 1 / 12 := by
    rw [div_le_iff₀ hp0, h2]
    nlinarith
  have hη2 : 3 * ((r - p) / 2) ^ 2 ≤ 1 / 48 := by
    rw [h2]
    nlinarith
  have hlam : (7 / 10 : ℝ) ≤
      19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2 -
        (r - p') * ((2 + (r - p) / 2 / 2) / (p' - L / 2) + 1) := by
    rw [hratio]
    linarith
  have hα0 : 0 ≤ ∫ a in p..r, reflectedOddPart F L a ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  exact (mul_le_mul_of_nonneg_right hlam hα0).trans hshell

/-- **Base strip micro-fold at half-width `η ≤ 1/12`.** The innermost box `[L − r, r]²` pays its odd
part with constant `≥ 7/10`. -/
theorem sharpMicroFold_strip_ge_seven_tenths {F : ℝ → ℝ} {K r η : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hr : 7 / 6 ≤ r) (hη0 : 0 < η) (hη12 : η ≤ 1 / 12) :
    (7 / 10 : ℝ) * (∫ a in (2 * (r - η) - r)..r, reflectedOddPart F (2 * (r - η)) a ^ 2) ≤
      stripBoxEnergy F (2 * (r - η) - r) r := by
  set L := 2 * (r - η)
  set p := L - r
  have hp1 : 1 ≤ p := by dsimp [p, L]; linarith
  have hp0 : 0 < p := by linarith
  have hpr : p < r := by dsimp [p, L]; linarith
  have hL : p + r = L := by dsimp [p]; ring
  have hr3 : r - p ≤ 2 * p := by dsimp [p, L]; linarith
  have hr6 : r - p ≤ 1 / 6 := by dsimp [p, L]; linarith
  have hstrip := sharpMicroFold_strip_ge hF hFL hp0 hpr hL hr3 hr6
  have hηp : (r - p) / 2 / p ≤ 1 / 12 := by
    rw [div_le_iff₀ hp0]
    dsimp [p, L]
    nlinarith
  have hη2 : 3 * ((r - p) / 2) ^ 2 ≤ 1 / 48 := by
    dsimp [p, L]
    nlinarith
  have hlam : (7 / 10 : ℝ) ≤ 19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2 := by linarith
  have hα0 : 0 ≤ ∫ a in p..r, reflectedOddPart F L a ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  exact (mul_le_mul_of_nonneg_right hlam hα0).trans hstrip

/-- The `j`-th shift in the ratio-6 geometric telescoping chain: `L_j = 2(r − η_0 / 6^j)`. -/
def geometricStripShift (r η₀ : ℝ) (j : ℕ) : ℝ := 2 * (r - η₀ / 6 ^ j)

/-- **Universal geometric telescoping chain (`N + 1` nested shells).** For every `r ≥ 7/6`,
`0 < η₀ ≤ 1/12`, `N : ℕ`, and every continuous Lipschitz test `F`, one copy of `stripBoxEnergy F 0 r`
simultaneously pays all `N + 1` odd parts along `geometricStripShift r η₀ j` with weight `7/10` per
layer. -/
theorem sum_geometricChain_oddPart_le_stripBoxEnergy {F : ℝ → ℝ} {K r η₀ : ℝ} (hF : Continuous F)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hr : 7 / 6 ≤ r) (hη0 : 0 < η₀)
    (hη12 : η₀ ≤ 1 / 12) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1),
        (7 / 10 : ℝ) * (∫ a in (geometricStripShift r η₀ j - r)..r,
          reflectedOddPart F (geometricStripShift r η₀ j) a ^ 2) ≤
      stripBoxEnergy F 0 r := by
  have htel : ∀ m : ℕ,
      (∑ j ∈ Finset.range m,
          (7 / 10 : ℝ) * (∫ a in (geometricStripShift r η₀ j - r)..r,
            reflectedOddPart F (geometricStripShift r η₀ j) a ^ 2)) +
        stripBoxEnergy F (geometricStripShift r η₀ m - r) r ≤
      stripBoxEnergy F (geometricStripShift r η₀ 0 - r) r := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hpow : (1 : ℝ) ≤ (6 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      have hηm0 : 0 < η₀ / 6 ^ m := by positivity
      have hηm12 : η₀ / 6 ^ m ≤ 1 / 12 := (div_le_self hη0.le hpow).trans hη12
      have hstep := sharpMicroFold_ratioSix_shell_ge hF hFL hr hηm0 hηm12
      have hshift : 2 * (r - η₀ / 6 ^ m / 6) = geometricStripShift r η₀ (m + 1) := by
        unfold geometricStripShift; rw [pow_succ, div_div]
      have hshift0 : 2 * (r - η₀ / 6 ^ m) = geometricStripShift r η₀ m := rfl
      rw [hshift, hshift0] at hstep
      linarith
  have hpowN : (1 : ℝ) ≤ (6 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  have hηN0 : 0 < η₀ / 6 ^ N := by positivity
  have hηN12 : η₀ / 6 ^ N ≤ 1 / 12 := (div_le_self hη0.le hpowN).trans hη12
  have hbase := sharpMicroFold_strip_ge_seven_tenths hF hFL hr hηN0 hηN12
  have hshiftN : 2 * (r - η₀ / 6 ^ N) = geometricStripShift r η₀ N := rfl
  rw [hshiftN] at hbase
  have hN := htel N
  have hmono : stripBoxEnergy F (geometricStripShift r η₀ 0 - r) r ≤ stripBoxEnergy F 0 r := by
    refine stripBoxEnergy_mono_of_nonneg hF hFL le_rfl ?_ ?_
    · unfold geometricStripShift; simp; linarith
    · unfold geometricStripShift; simp; linarith
  rw [Finset.sum_range_succ]
  linarith

/-- A finite family of strips `(L_j, c_j)` wider than `ε` (`r ≤ L_j ≤ 2(r − ε)`) is universally
payable by `stripBoxEnergy F 0 r` if its weighted odd parts are dominated by `stripBoxEnergy F 0 r`
for every continuous Lipschitz test `F`. -/
def IsPayableOddPartFamily {ι : Type*} (r ε : ℝ) (s : Finset ι) (L c : ι → ℝ) : Prop :=
  (∀ j ∈ s, r ≤ L j ∧ L j ≤ 2 * (r - ε) ∧ 0 ≤ c j) ∧
    ∀ (F : ℝ → ℝ) (K : ℝ), Continuous F → (∀ a b, |F a - F b| ≤ K * |a - b|) →
      ∑ j ∈ s, c j * (∫ a in (L j - r)..r, reflectedOddPart F (L j) a ^ 2) ≤
        stripBoxEnergy F 0 r

/-- **Logarithmic capacity upper bound.** Every universally payable family of strips wider than `ε`
has total weight `∑_{j ∈ s} c_j ≤ 2 log(4/ε) + 84`. -/
theorem sum_le_of_isPayableOddPartFamily {ι : Type*} {r ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεr : ε < r) {s : Finset ι} {L c : ι → ℝ} (hpay : IsPayableOddPartFamily r ε s L c) :
    ∑ j ∈ s, c j ≤ 2 * (Real.log (4 / ε) + 42) := by
  by_contra hlt
  have hlt' : 2 * (Real.log (4 / ε) + 42) < ∑ j ∈ s, c j := not_le.mp hlt
  have h1 := stripBoxEnergy_edgeTent_lt_sum_oddPart hε0 hε1 hεr s L c
    (fun j hj => ⟨(hpay.1 j hj).1, (hpay.1 j hj).2.1⟩) hlt'
  have h2 := hpay.2 (edgeTentOdd r ε) 2 (continuous_edgeTentOdd r ε) (edgeTentOdd_lipschitz r ε)
  linarith

/-- **Logarithmic capacity lower bound.** For every `r ≥ 7/6` and `0 < ε ≤ 1/12`, the ratio-6
geometric chain truncated at `N = ⌊log(1/(12ε)) / log 6⌋₊` is a universally payable family of strips
wider than `ε` with total weight `≥ (7 / (10 log 6)) log(1/(12ε))`. -/
theorem exists_payableOddPartFamily_log_lower_bound {r ε : ℝ} (hr : 7 / 6 ≤ r) (hε0 : 0 < ε)
    (hε12 : ε ≤ 1 / 12) :
    ∃ (N : ℕ) (L c : ℕ → ℝ),
      IsPayableOddPartFamily r ε (Finset.range (N + 1)) L c ∧
        (7 / (10 * Real.log 6)) * Real.log (1 / (12 * ε)) ≤
          ∑ j ∈ Finset.range (N + 1), c j := by
  set X := Real.log (1 / (12 * ε)) / Real.log 6
  set N := ⌊X⌋₊
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have h12ε : 1 ≤ 1 / (12 * ε) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hX0 : 0 ≤ X := div_nonneg (Real.log_nonneg h12ε) hlog6.le
  refine ⟨N, geometricStripShift r (1 / 12), fun _ => 7 / 10, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjX : (j : ℝ) ≤ X := (Nat.cast_le.mpr hjN).trans (Nat.floor_le hX0)
    have hpow_log : Real.log ((6 : ℝ) ^ j) ≤ Real.log (1 / (12 * ε)) := by
      rw [Real.log_pow]
      exact (le_div_iff₀ hlog6).mp hjX
    have hpow_le : (6 : ℝ) ^ j ≤ 1 / (12 * ε) :=
      (Real.log_le_log_iff (by positivity) (by positivity)).mp hpow_log
    have hε_le : ε ≤ (1 / 12) / (6 : ℝ) ^ j := by
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hpow_le
      linarith
    have hpow1 : (1 : ℝ) ≤ (6 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hle12 : (1 / 12) / (6 : ℝ) ^ j ≤ 1 / 12 := div_le_self (by norm_num) hpow1
    unfold geometricStripShift
    exact ⟨by linarith, by linarith, by norm_num⟩
  · intro F K hF hFL
    exact sum_geometricChain_oddPart_le_stripBoxEnergy hF hFL hr (by norm_num) le_rfl N
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hlt : X < (N : ℝ) + 1 := Nat.lt_floor_add_one X
    have hmul : (7 / 10 : ℝ) * X ≤ ((N + 1 : ℕ) : ℝ) * (7 / 10) := by
      push_cast; linarith
    calc (7 / (10 * Real.log 6)) * Real.log (1 / (12 * ε))
        = (7 / 10) * X := by dsimp [X]; ring
      _ ≤ ((N + 1 : ℕ) : ℝ) * (7 / 10) := hmul

/-! ## Part II: Exact Square-Root Width `δ ≍ e^{−r}` of the Light Cone -/

/-- For `1 ≤ p` and `2 ≤ k`, `p ^ k ≤ (p ^ (k - 1)) ^ 2`. -/
theorem pow_le_sq_pow_pred {p k : ℕ} (hp : 1 ≤ p) (hk : 2 ≤ k) :
    p ^ k ≤ (p ^ (k - 1)) ^ 2 := by
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hp (by omega)

/-- For `p < q` and `2 ≤ k`, `p ^ k + 2 * p ^ (k - 1) ≤ q ^ k`. -/
theorem pow_add_two_mul_pow_pred_le_pow {p q k : ℕ} (hpq : p < q) (hk : 2 ≤ k) :
    p ^ k + 2 * p ^ (k - 1) ≤ q ^ k := by
  have hk2 : k - 2 + 2 = k := by omega
  have hk1 : k - 2 + 1 = k - 1 := by omega
  have h1 : p ^ (k - 2) ≤ (p + 1) ^ (k - 2) := Nat.pow_le_pow_left (Nat.le_succ p) (k - 2)
  have h2 : p ^ 2 + 2 * p ≤ (p + 1) ^ 2 := by ring_nf; omega
  have h3 : p ^ (k - 2) * (p ^ 2 + 2 * p) ≤ (p + 1) ^ (k - 2) * (p + 1) ^ 2 :=
    Nat.mul_le_mul h1 h2
  have h4 : p ^ (k - 2) * (p ^ 2 + 2 * p) = p ^ (k - 2 + 2) + 2 * p ^ (k - 2 + 1) := by ring
  have h5 : (p + 1) ^ (k - 2) * (p + 1) ^ 2 = (p + 1) ^ (k - 2 + 2) := (pow_add _ _ _).symm
  rw [h4, hk2, hk1, h5, hk2] at h3
  exact h3.trans (Nat.pow_le_pow_left hpq k)

/-- **Exponent injectivity on proper prime powers in a short interval.** When `r ≥ 2` and
`0 < δ ≤ (1/2) e^{−r}`, at most one proper prime power `p^k` (`k ≥ 2`) in `lightConeBand r δ` can
have each exponent `k`, so the number of proper prime powers in `lightConeBand r δ` is at most
`Nat.log 2 ⌈e^{2r}⌉₊`. -/
theorem card_properPrimePow_lightConeBand_le {r δ : ℝ} (hr : 2 ≤ r) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 / 2) * Real.exp (-r)) :
    ((lightConeBand r δ).filter (fun n => n.primeFactors.card = 1 ∧ ¬ n.Prime)).card ≤
      Nat.log 2 ⌈Real.exp (2 * r)⌉₊ := by
  classical
  set b := ⌈Real.exp (2 * r)⌉₊
  set S := (lightConeBand r δ).filter (fun n => n.primeFactors.card = 1 ∧ ¬ n.Prime)
  set T := Finset.Icc 2 (Nat.log 2 b)
  have hδ_lt_half : δ < 1 / 2 := by
    have : Real.exp (-r) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hrδ : δ < r := by linarith
  have key : ∀ n ∈ S,
      n.minFac ^ n.factorization n.minFac = n ∧
        2 ≤ n.minFac ∧
        2 ≤ n.factorization n.minFac ∧
        n.factorization n.minFac ≤ Nat.log 2 b := by
    intro n hn
    obtain ⟨hmem, hcard, hnp⟩ := Finset.mem_filter.mp hn
    have hnb : n ≤ b := (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1).le
    have hn2 : 2 ≤ n := (le_of_mem_lightConeBand hrδ hmem).2.1
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    have hprime : n.minFac.Prime := Nat.minFac_prime hn1
    have hmemf : n.minFac ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hprime, Nat.minFac_dvd n, hn0⟩
    have hsingle : n.primeFactors = {n.minFac} := by
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
      rw [hp] at hmemf ⊢
      rw [Finset.mem_singleton.mp hmemf]
    have hrecon : n.minFac ^ n.factorization n.minFac = n := by
      have h := Nat.prod_factorization_pow_eq_self hn0
      rw [Finsupp.prod, Nat.support_factorization, hsingle, Finset.prod_singleton] at h
      exact h
    have he2 : 2 ≤ n.factorization n.minFac := by
      have he1 : 0 < n.factorization n.minFac :=
        Nat.Prime.factorization_pos_of_dvd hprime hn0 (Nat.minFac_dvd n)
      rcases Nat.lt_or_ge (n.factorization n.minFac) 2 with h | h
      · exfalso
        have : n.factorization n.minFac = 1 := by omega
        rw [this, pow_one] at hrecon
        exact hnp (hrecon ▸ hprime)
      · exact h
    have hlg : n.factorization n.minFac ≤ Nat.log 2 b := by
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      have : (2 : ℕ) ^ n.factorization n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
        Nat.pow_le_pow_left hprime.two_le _
      omega
    exact ⟨hrecon, hprime.two_le, he2, hlg⟩
  have hmaps : Set.MapsTo (fun n => n.factorization n.minFac) S T := fun n hn =>
    Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨(key n hn).2.2.1, (key n hn).2.2.2⟩)
  have hgap_contra : ∀ x ∈ S, ∀ y ∈ S,
      x.factorization x.minFac = y.factorization y.minFac → x.minFac < y.minFac → False := by
    intro x hx y hy hkeq hpq
    obtain ⟨hrx, hp2, hk2, -⟩ := key x hx
    obtain ⟨hry, -, -, -⟩ := key y hy
    set k := x.factorization x.minFac
    set p := x.minFac
    set q := y.minFac
    have hry' : q ^ k = y := by rw [show k = y.factorization y.minFac from hkeq]; exact hry
    have hx_lo := (le_of_mem_lightConeBand hrδ (Finset.mem_filter.mp hx).1).1
    have hy_log := (le_of_mem_lightConeBand hrδ (Finset.mem_filter.mp hy).1).2.2.2
    have hy_pos : (0 : ℝ) < y := by
      have := (le_of_mem_lightConeBand hrδ (Finset.mem_filter.mp hy).1).2.1
      exact_mod_cast (by omega : 0 < y)
    have hy_hi : (y : ℝ) < Real.exp (2 * r) := by
      rw [← Real.exp_log hy_pos]
      exact Real.exp_lt_exp.mpr hy_log
    have hsq_nat : x ≤ (p ^ (k - 1)) ^ 2 := by
      rw [← hrx]
      exact pow_le_sq_pow_pred (by omega) hk2
    have hsq_real : Real.exp (r - δ) ^ 2 ≤ ((p ^ (k - 1) : ℕ) : ℝ) ^ 2 := by
      have hexp : Real.exp (r - δ) ^ 2 = Real.exp (2 * r - 2 * δ) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rw [hexp]
      exact hx_lo.trans (by exact_mod_cast hsq_nat)
    have hp_ge : Real.exp (r - δ) ≤ ((p ^ (k - 1) : ℕ) : ℝ) := by
      nlinarith [Real.exp_pos (r - δ), (Nat.cast_nonneg (p ^ (k - 1)) : (0 : ℝ) ≤ (p ^ (k - 1) : ℕ))]
    have hstep_nat : x + 2 * p ^ (k - 1) ≤ y := by
      rw [← hrx, ← hry']
      exact pow_add_two_mul_pow_pred_le_pow hpq hk2
    have hstep_real : (x : ℝ) + 2 * ((p ^ (k - 1) : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hstep_nat
    have hdiff_lo : 2 * Real.exp (r - δ) < Real.exp (2 * r) - Real.exp (2 * r - 2 * δ) := by
      linarith
    have hdiff_hi : Real.exp (2 * r) - Real.exp (2 * r - 2 * δ) ≤ 2 * δ * Real.exp (2 * r) := by
      have e : Real.exp (2 * r - 2 * δ) = Real.exp (2 * r) * Real.exp (-(2 * δ)) := by
        rw [← Real.exp_add]; ring_nf
      rw [e]
      have := Real.add_one_le_exp (-(2 * δ))
      nlinarith [Real.exp_pos (2 * r)]
    have hδE : 2 * δ * Real.exp (2 * r) ≤ Real.exp r := by
      have e : Real.exp (2 * r) = Real.exp r * Real.exp r := by rw [← Real.exp_add]; ring_nf
      have e2 : Real.exp (-r) * Real.exp r = 1 := by rw [← Real.exp_add]; simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hδ (Real.exp_pos r).le, Real.exp_pos r]
    have hlow_exp : Real.exp r * (1 - δ) ≤ Real.exp (r - δ) := by
      have e : Real.exp (r - δ) = Real.exp r * Real.exp (-δ) := by rw [← Real.exp_add]; ring_nf
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-δ)]) (Real.exp_pos r).le
    nlinarith [Real.exp_pos r]
  have hinj : Set.InjOn (fun n => n.factorization n.minFac) S := by
    intro x hx y hy hkeq
    rcases lt_trichotomy x.minFac y.minFac with hlt | heq | hgt
    · exact False.elim (hgap_contra x hx y hy hkeq hlt)
    · rw [← (key x hx).1, ← (key y hy).1, hkeq, heq]
    · exact False.elim (hgap_contra y hy x hx hkeq.symm hgt)
  have hcard := Finset.card_le_card_of_injOn (fun n => n.factorization n.minFac) hmaps hinj
  rw [Nat.card_Icc] at hcard
  omega

/-- Bound on `Nat.log 2 ⌈e^{2r}⌉₊` for `r ≥ 2`: `Nat.log 2 ⌈e^{2r}⌉₊ ≤ 4r + 2`. -/
theorem natLog_two_ceil_exp_le {r : ℝ} (hr : 2 ≤ r) :
    (Nat.log 2 ⌈Real.exp (2 * r)⌉₊ : ℝ) ≤ 4 * r + 2 := by
  set b := ⌈Real.exp (2 * r)⌉₊
  set k := Nat.log 2 b
  have hb1 : 1 ≤ b := Nat.ceil_pos.mpr (Real.exp_pos (2 * r))
  have hpow : (2 : ℕ) ^ k ≤ b := Nat.pow_log_le_self 2 (by omega)
  have hpowR : ((2 : ℝ) ^ k) ≤ (b : ℝ) := by exact_mod_cast hpow
  have hb_le : (b : ℝ) ≤ Real.exp (2 * r + 1) := by
    have h1 : (b : ℝ) < Real.exp (2 * r) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h2 : Real.exp (2 * r) + 1 ≤ Real.exp (2 * r + 1) := by
      rw [Real.exp_add]
      have := Real.add_one_le_exp (1 : ℝ)
      have := Real.add_one_le_exp (2 * r)
      nlinarith [Real.exp_pos (2 * r)]
    exact h1.le.trans h2
  have hlog : Real.log ((2 : ℝ) ^ k) ≤ Real.log (Real.exp (2 * r + 1)) :=
    Real.log_le_log (by positivity) (hpowR.trans hb_le)
  rw [Real.log_pow, Real.log_exp] at hlog
  have hl2 := Real.log_two_gt_d9
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- Decomposition of the light-cone `vonMangoldtAtom` sum into primes and proper prime powers. -/
theorem sum_vonMangoldtAtom_lightConeBand_le_prime_add_proper {r δ : ℝ}
    (hrδ : δ < r) (hδ1 : δ < 1) :
    ∑ n ∈ lightConeBand r δ, 2 * vonMangoldtAtom n ≤
      ((((lightConeBand r δ).filter Nat.Prime).card +
          ((lightConeBand r δ).filter (fun n => n.primeFactors.card = 1 ∧ ¬ n.Prime)).card : ℕ) : ℝ) *
        (4 * r / (Real.exp r * (1 - δ))) := by
  classical
  set P := (lightConeBand r δ).filter Nat.Prime
  set Q := (lightConeBand r δ).filter (fun n => n.primeFactors.card = 1 ∧ ¬ n.Prime)
  have hdisj : Disjoint P Q := Finset.disjoint_filter.mpr fun _ _ hp hq => hq.2 hp
  have hsub : P ∪ Q ⊆ lightConeBand r δ :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hzero : ∀ n ∈ lightConeBand r δ, n ∉ P ∪ Q → 2 * vonMangoldtAtom n = 0 := by
    intro n hn hnot
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hnot
    have hnot_prime : ¬ n.Prime := fun hp => hnot (Or.inl ⟨hn, hp⟩)
    have hnot_card : n.primeFactors.card ≠ 1 := fun hc => hnot (Or.inr ⟨hn, hc, hnot_prime⟩)
    have hnot_pp : ¬ IsPrimePow n := by
      rwa [isPrimePow_iff_card_primeFactors_eq_one]
    have hΛ0 : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot_pp
    unfold vonMangoldtAtom
    rw [hΛ0]
    split_ifs <;> simp
  rw [← Finset.sum_subset hsub hzero]
  have hterm : ∀ n ∈ P ∪ Q, 2 * vonMangoldtAtom n ≤ 4 * r / (Real.exp r * (1 - δ)) := by
    intro n hn
    have h := vonMangoldtAtom_le_of_mem_lightConeBand hrδ hδ1 (hsub hn)
    calc 2 * vonMangoldtAtom n ≤ 2 * (2 * r / (Real.exp r * (1 - δ))) := by linarith
      _ = 4 * r / (Real.exp r * (1 - δ)) := by ring
  have hsum := Finset.sum_le_card_nsmul (P ∪ Q) _ (4 * r / (Real.exp r * (1 - δ))) hterm
  rw [Finset.card_union_of_disjoint hdisj, nsmul_eq_mul] at hsum
  exact hsum

/-- Selberg-sieve bound on the number of primes in `lightConeBand r δ` at sieve level
`z = Y = ⌊e^{r/3}⌋₊` for `r ≥ 12`. -/
theorem card_prime_lightConeBand_le_sieve {r δ : ℝ} (hr : 12 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    (((lightConeBand r δ).filter Nat.Prime).card : ℝ) ≤
      8 * (2 * δ * Real.exp (2 * r) + 2) / r +
        (Real.exp (4 * RHTower.Sieve.mertensSecondUpperConst) * r ^ 4 + 1) * Real.exp (2 * r / 3) := by
  classical
  set A := Real.exp (2 * r - 2 * δ)
  set B := Real.exp (2 * r)
  set a := ⌈A⌉₊ - 1
  set b := ⌈B⌉₊
  set z := ⌊Real.exp (r / 3)⌋₊
  have hrδ : δ < r := by linarith
  have hA1 : 1 ≤ ⌈A⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hab : a ≤ b := by
    have : ⌈A⌉₊ ≤ ⌈B⌉₊ := Nat.ceil_le_ceil (Real.exp_le_exp.mpr (by linarith))
    omega
  have hsub : (lightConeBand r δ).filter Nat.Prime ⊆ (Finset.Ioc a b).filter Nat.Prime := by
    intro n hn
    obtain ⟨hmem, hp⟩ := Finset.mem_filter.mp hn
    have hlo := (le_of_mem_lightConeBand hrδ hmem).1
    have hceil : ⌈A⌉₊ ≤ n := Nat.ceil_le.mpr hlo
    have hhi : n < b := (Finset.mem_filter.mp hmem).1 |> Finset.mem_range.mp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hp⟩
  have hcard_le : (((lightConeBand r δ).filter Nat.Prime).card : ℝ) ≤
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hexp_r4 : Real.exp (r / 4) + 1 ≤ Real.exp (r / 3) := by
    have e : Real.exp (r / 3) = Real.exp (r / 4) * Real.exp (r / 12) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : 2 ≤ Real.exp (r / 12) := by linarith [Real.add_one_le_exp (r / 12)]
    have h2 : 4 ≤ Real.exp (r / 4) := by linarith [Real.add_one_le_exp (r / 4)]
    rw [e]; nlinarith
  have hz_ge_exp : Real.exp (r / 4) ≤ (z : ℝ) := by
    have := Nat.lt_floor_add_one (Real.exp (r / 3))
    linarith
  have hz_le_exp : (z : ℝ) ≤ Real.exp (r / 3) := Nat.floor_le (Real.exp_pos _).le
  have hz4 : 4 ≤ z := by
    have : (4 : ℝ) ≤ (z : ℝ) := by linarith [Real.add_one_le_exp (r / 4)]
    exact_mod_cast this
  have hlogz_lo : r / 4 ≤ Real.log z := by
    have := Real.log_le_log (Real.exp_pos _) hz_ge_exp
    rwa [Real.log_exp] at this
  have hlogz_hi : Real.log z ≤ r / 3 := by
    have := Real.log_le_log (by positivity) hz_le_exp
    rwa [Real.log_exp] at this
  have hlogz_pos : 0 < Real.log z := by linarith
  have hsieve := RHTower.Sieve.card_prime_Ioc_le a b z z hab (by omega) le_rfl (by omega) hlogz_pos
  have hba : (b : ℝ) - a ≤ 2 * δ * B + 2 := by
    have haR : (a : ℝ) = (⌈A⌉₊ : ℝ) - 1 := by
      dsimp [a]; rw [Nat.cast_sub hA1, Nat.cast_one]
    have hcB : (b : ℝ) < B + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have hcA : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have hBA : B - A ≤ 2 * δ * B := by
      have e : A = B * Real.exp (-(2 * δ)) := by
        dsimp [A, B]; rw [← Real.exp_add]; ring_nf
      have := Real.add_one_le_exp (-(2 * δ))
      rw [e]; nlinarith [Real.exp_pos (2 * r)]
    linarith
  have hba_pos : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hmain : 2 * ((b : ℝ) - a) / Real.log z ≤ 8 * (2 * δ * B + 2) / r := by
    calc 2 * ((b : ℝ) - a) / Real.log z
        ≤ 2 * (2 * δ * B + 2) / (r / 4) :=
          div_le_div₀ (by positivity) (by linarith) (by linarith) hlogz_lo
      _ = 8 * (2 * δ * B + 2) / r := by ring
  have herr : RHTower.Sieve.selbergFibreError z z + (z : ℝ) ≤
      (Real.exp (4 * RHTower.Sieve.mertensSecondUpperConst) * r ^ 4 + 1) * Real.exp (2 * r / 3) := by
    unfold RHTower.Sieve.selbergFibreError
    have hzz : ((z * z : ℕ) : ℝ) ≤ Real.exp (2 * r / 3) := by
      push_cast
      calc (z : ℝ) * z ≤ Real.exp (r / 3) * Real.exp (r / 3) :=
            mul_le_mul hz_le_exp hz_le_exp (by positivity) (by positivity)
        _ = Real.exp (2 * r / 3) := by rw [← Real.exp_add]; ring_nf
    have hlog4 : (Real.log z) ^ (4 : ℝ) ≤ r ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ hlogz_pos.le (by linarith) 4
    have hz_exp23 : (z : ℝ) ≤ Real.exp (2 * r / 3) :=
      hz_le_exp.trans (Real.exp_le_exp.mpr (by linarith))
    have hC0 : 0 ≤ Real.exp (4 * RHTower.Sieve.mertensSecondUpperConst) := (Real.exp_pos _).le
    have hprod : ((z * z : ℕ) : ℝ) *
        (Real.exp (4 * RHTower.Sieve.mertensSecondUpperConst) * (Real.log z) ^ (4 : ℝ)) ≤
        Real.exp (2 * r / 3) * (Real.exp (4 * RHTower.Sieve.mertensSecondUpperConst) * r ^ 4) := by
      refine mul_le_mul hzz (mul_le_mul_of_nonneg_left hlog4 hC0) (by positivity) (by positivity)
    linarith
  linarith

/-- **Asymptotic square-root light-cone mass bound (`δ ≤ (1/60) e^{−r}`).** Using the Selberg sieve
and proper-prime-power exponent injectivity, the `1/r` factor in `PrimeLightConeAllocation` is
removed: for all sufficiently large `r` and all `0 < δ ≤ (1/60) e^{−r}`,
`∑_{n ∈ lightConeBand r δ} 2Λ(n)/√n ≤ 16/10`. -/
theorem eventually_sum_vonMangoldtAtom_lightConeBand_le_squareRoot :
    ∀ᶠ r in atTop, ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 60) * Real.exp (-r) →
      ∑ n ∈ lightConeBand r δ, 2 * vonMangoldtAtom n ≤ 16 / 10 := by
  set C_m := Real.exp (4 * RHTower.Sieve.mertensSecondUpperConst)
  have hlin : Tendsto (fun r : ℝ => r / 3) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hexp5 := ((Real.tendsto_exp_div_pow_atTop 5).comp hlin).eventually
    (eventually_ge_atTop (243 * (32 * C_m + 32)))
  filter_upwards [hexp5, eventually_ge_atTop (12 : ℝ)] with r hexp hr δ hδ0 hδ
  simp only [Function.comp_apply] at hexp
  have hr3_pos : 0 < (r / 3) ^ 5 := by positivity
  rw [le_div_iff₀ hr3_pos] at hexp
  have hexp_r3 : (32 * C_m + 32) * r ^ 5 ≤ Real.exp (r / 3) := by
    have : 243 * (32 * C_m + 32) * (r / 3) ^ 5 = (32 * C_m + 32) * r ^ 5 := by ring
    linarith
  have hE_ge : (32 * C_m + 32) * r ^ 5 ≤ Real.exp r :=
    hexp_r3.trans (Real.exp_le_exp.mpr (by linarith))
  have hr1_le_r5 : r ≤ r ^ 5 := by
    have : r ^ 1 ≤ r ^ 5 := pow_le_pow_right₀ (by linarith) (by omega)
    simpa using this
  have hr2_le_r5 : r ^ 2 ≤ r ^ 5 := pow_le_pow_right₀ (by linarith) (by omega)
  have hδ_half : δ ≤ (1 / 2) * Real.exp (-r) := by linarith [Real.exp_pos (-r)]
  have hE_inv : Real.exp (-r) ≤ 1 / 7 := by
    have he := Real.exp_one_gt_d9
    have h2 : Real.exp 2 ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
    have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos r) (by norm_num)]
    nlinarith
  have hδ_small : δ ≤ 1 / 200 := by linarith
  have hdecomp := sum_vonMangoldtAtom_lightConeBand_le_prime_add_proper (r := r) (δ := δ)
    (by linarith) (by linarith)
  have hprime := card_prime_lightConeBand_le_sieve hr hδ0.le (by linarith)
  have hproper : (((lightConeBand r δ).filter (fun n => n.primeFactors.card = 1 ∧ ¬ n.Prime)).card : ℝ) ≤
      4 * r + 2 := by
    have h1 : (((lightConeBand r δ).filter (fun n => n.primeFactors.card = 1 ∧ ¬ n.Prime)).card : ℝ) ≤
        (Nat.log 2 ⌈Real.exp (2 * r)⌉₊ : ℝ) := by
      exact_mod_cast card_properPrimePow_lightConeBand_le (by linarith) hδ0 hδ_half
    exact h1.trans (natLog_two_ceil_exp_le (by linarith))
  have hcount : ((((lightConeBand r δ).filter Nat.Prime).card +
      ((lightConeBand r δ).filter (fun n => n.primeFactors.card = 1 ∧ ¬ n.Prime)).card : ℕ) : ℝ) ≤
      8 * (2 * δ * Real.exp (2 * r) + 2) / r +
        (C_m * r ^ 4 + 1) * Real.exp (2 * r / 3) + (4 * r + 2) := by
    push_cast; linarith
  have hfac_pos : 0 ≤ 4 * r / (Real.exp r * (1 - δ)) := by
    have : 0 < 1 - δ := by linarith
    positivity
  have hprod := hdecomp.trans (mul_le_mul_of_nonneg_right hcount hfac_pos)
  set E := Real.exp r
  have hE0 : 0 < E := Real.exp_pos r
  have h1δ : 0 < 1 - δ := by linarith
  have hδE : 60 * δ * E ≤ 1 := by
    have e : Real.exp (-r) * E = 1 := by dsimp [E]; rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_right hδ hE0.le]
  have hE2 : Real.exp (2 * r) = E ^ 2 := by
    dsimp [E]; rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hE23 : Real.exp (2 * r / 3) * Real.exp (r / 3) = E := by
    dsimp [E]; rw [← Real.exp_add]; ring_nf
  have hC_pos : 0 ≤ C_m := (Real.exp_pos _).le
  have hT1 : (8 * (2 * δ * Real.exp (2 * r) + 2) / r) * (4 * r / E) ≤ 70 / 60 := by
    rw [hE2]
    have heq : (8 * (2 * δ * E ^ 2 + 2) / r) * (4 * r / E) = 64 * δ * E + 64 / E := by
      have hr_ne : r ≠ 0 := by linarith
      have hE_ne : E ≠ 0 := hE0.ne'
      field_simp
      ring
    have h64E : 64 / E ≤ 6 / 60 := by
      rw [div_le_iff₀ hE0]
      nlinarith
    rw [heq]; linarith
  have hT2 : ((C_m * r ^ 4 + 1) * Real.exp (2 * r / 3) + (4 * r + 2)) * (4 * r / E) ≤ 15 / 60 := by
    rw [mul_div_assoc', div_le_iff₀ hE0]
    have h1 : (C_m * r ^ 4 + 1) * (4 * r) ≤ 4 * (C_m + 1) * r ^ 5 := by
      have hr45 : r ^ 4 * r = r ^ 5 := by ring
      nlinarith
    have h2 : (C_m * r ^ 4 + 1) * Real.exp (2 * r / 3) * (4 * r) ≤ (1 / 8) * E := by
      calc (C_m * r ^ 4 + 1) * Real.exp (2 * r / 3) * (4 * r)
          = Real.exp (2 * r / 3) * ((C_m * r ^ 4 + 1) * (4 * r)) := by ring
        _ ≤ Real.exp (2 * r / 3) * (4 * (C_m + 1) * r ^ 5) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ ≤ Real.exp (2 * r / 3) * ((1 / 8) * Real.exp (r / 3)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            linarith
        _ = (1 / 8) * E := by rw [← mul_assoc, mul_comm (Real.exp (2 * r / 3)), mul_assoc, hE23]
    have h3 : (4 * r + 2) * (4 * r) ≤ (1 / 8) * E := by
      nlinarith
    linarith
  set U := 8 * (2 * δ * Real.exp (2 * r) + 2) / r
  set V := (C_m * r ^ 4 + 1) * Real.exp (2 * r / 3) + (4 * r + 2)
  have hsplit : (U + V) * (4 * r / (E * (1 - δ))) =
      (U * (4 * r / E) + V * (4 * r / E)) / (1 - δ) := by
    rw [← div_div, mul_div_assoc', add_mul]
  have hUV : 8 * (2 * δ * Real.exp (2 * r) + 2) / r +
      (C_m * r ^ 4 + 1) * Real.exp (2 * r / 3) + (4 * r + 2) = U + V := by
    dsimp [U, V]; ring
  rw [hUV, hsplit] at hprod
  refine hprod.trans ?_
  rw [div_le_iff₀ h1δ]
  linarith

/-- General light-cone and global allocation whenever `∑_{lightConeBand r δ} 2Λ(n)/√n ≤ 16/10` and
`0 < δ ≤ 1/200`. -/
theorem sum_primeShift_le_lightCone_of_mass_le {F : ℝ → ℝ} {K r δ : ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hsupp : ∀ x, r < |x| → F x = 0)
    (hr : 2 ≤ r) (hδ0 : 0 < δ) (hδs : δ ≤ 1 / 200)
    (hmass : ∑ n ∈ lightConeBand r δ, 2 * vonMangoldtAtom n ≤ 16 / 10) :
    (∑ n ∈ lightConeBand r δ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) ≤
        stripBoxEnergy F (r - 2 * δ) r) ∧
      ((∑' n : ℕ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) ≤
        stripBoxEnergy F (r - 2 * δ) r +
          ∑ n ∈ primeSide r \ lightConeBand r δ, 2 * vonMangoldtAtom n * atomStripMass F r n) := by
  have hrδ : δ < r := by linarith
  set θ : ℕ → ℝ := fun n => 2 * vonMangoldtAtom n / (189 / 100) with hθdef
  have hθsum : ∑ n ∈ lightConeBand r δ, θ n ≤ 1 := by
    rw [hθdef, ← Finset.sum_div, div_le_one (by norm_num)]
    linarith
  have h := sum_primeStripCharge_le_union hF hFc hodd hFL hsupp (lightConeBand r δ)
    (p₀ := r - 2 * δ) (by linarith) (by linarith) (by linarith) θ (fun _ => 0) fun n hn => by
      obtain ⟨-, h2, hlo, hhi⟩ := le_of_mem_lightConeBand hrδ hn
      have hΛ0 := vonMangoldtAtom_nonneg n
      refine ⟨h2, ⟨by linarith, by linarith⟩, by linarith, by positivity, by norm_num, ?_⟩
      have hlam : 189 / 100 ≤ stripFoldConstant n r := by
        unfold stripFoldConstant
        have hp : 19 / 10 ≤ Real.log n - r := by linarith
        have hη0 : 0 ≤ (r - (Real.log n - r)) / 2 := by linarith
        have hη : (r - (Real.log n - r)) / 2 ≤ 1 / 200 := by linarith
        have hηp : (r - (Real.log n - r)) / 2 / (Real.log n - r) ≤ 1 / 300 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        have hη2 : 3 * ((r - (Real.log n - r)) / 2) ^ 2 ≤ 3 / 40000 := by nlinarith
        linarith
      rw [hθdef]
      simp only
      rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
      nlinarith
  have hcone := h hθsum
  simp only [primeStripCharge, mul_zero, zero_mul, add_zero] at hcone
  refine ⟨hcone, ?_⟩
  have hsub : lightConeBand r δ ⊆ primeSide r := fun n hn => by
    simp only [lightConeBand, Finset.mem_filter, Finset.mem_range] at hn
    simp only [primeSide, Finset.mem_range]
    have hn0 : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have : Real.log (n : ℝ) = 0 := by rw [h0, Nat.cast_zero, Real.log_zero]
        linarith [hn.2.1]
      · exact_mod_cast h0
    have hlt : (n : ℝ) < Real.exp (2 * r) := by
      rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr hn.2.2
    have : n ≤ ⌊Real.exp (2 * r)⌋₊ := Nat.le_floor hlt.le
    omega
  rw [tsum_primeShift_eq_sum_primeSide hsupp, ← Finset.sum_sdiff hsub]
  have hrest : (∑ n ∈ primeSide r \ lightConeBand r δ,
      2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) ≤
      ∑ n ∈ primeSide r \ lightConeBand r δ, 2 * vonMangoldtAtom n * atomStripMass F r n := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := (Finset.mem_sdiff.mp hn).1
    simp only [primeSide, Finset.mem_range] at hn'
    refine two_mul_primeShift_le_atomStripMass hF hFc hodd hsupp ?_
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast h0
      have hle : (n : ℝ) ≤ Real.exp (2 * r) :=
        (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hn')).trans (Nat.floor_le (Real.exp_pos _).le)
      have := Real.log_le_log hn0 hle
      rwa [Real.log_exp] at this
  linarith

/-- **Uniform square-root light-cone and global allocation (`δ ≤ c₀ e^{−r}`).** There exists an
explicit `c₀ > 0` such that for **every** `r ≥ 2`, **every** `0 < δ ≤ c₀ e^{−r}`, and **every** odd
continuous Lipschitz test `F` supported in `[−r, r]`, both the light-cone mass bound (`≤ 16/10`),
the light-cone allocation (`sum_primeShift_le_lightCone`), and the global allocation
(`tsum_primeShift_le_globalAllocation`) hold at the square-root scale `δ ≤ c₀ e^{−r}`. -/
theorem exists_squareRoot_lightCone_allocation :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ⦃r δ : ℝ⦄, 2 ≤ r → 0 < δ → δ ≤ c₀ * Real.exp (-r) →
      (∑ n ∈ lightConeBand r δ, 2 * vonMangoldtAtom n ≤ 16 / 10) ∧
      ∀ {F : ℝ → ℝ} {K : ℝ}, Continuous F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ a b, |F a - F b| ≤ K * |a - b|) →
        (∀ x, r < |x| → F x = 0) →
        (∑ n ∈ lightConeBand r δ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) ≤
            stripBoxEnergy F (r - 2 * δ) r) ∧
          ((∑' n : ℕ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) ≤
            stripBoxEnergy F (r - 2 * δ) r +
              ∑ n ∈ primeSide r \ lightConeBand r δ, 2 * vonMangoldtAtom n * atomStripMass F r n) := by
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp
    eventually_sum_vonMangoldtAtom_lightConeBand_le_squareRoot
  set R₀ := max r₀ 2
  set c₀ := min (1 / 60) (1 / (16 * R₀))
  have hR₀2 : 2 ≤ R₀ := le_max_right r₀ 2
  have hc₀_pos : 0 < c₀ := lt_min (by norm_num) (by positivity)
  refine ⟨c₀, hc₀_pos, fun r δ hr hδ0 hδ => ?_⟩
  have hmass : ∑ n ∈ lightConeBand r δ, 2 * vonMangoldtAtom n ≤ 16 / 10 := by
    rcases le_or_gt r R₀ with hle | hgt
    · refine sum_vonMangoldtAtom_lightConeBand_le hr hδ0 ?_
      have hc₀_le : c₀ ≤ 1 / (16 * r) :=
        (min_le_right _ _).trans (one_div_le_one_div_of_le (by positivity) (by linarith))
      calc δ ≤ c₀ * Real.exp (-r) := hδ
        _ ≤ (1 / (16 * r)) * Real.exp (-r) :=
            mul_le_mul_of_nonneg_right hc₀_le (Real.exp_pos _).le
        _ = Real.exp (-r) / (16 * r) := by ring
    · refine hr₀ r ((le_max_left r₀ 2).trans hgt.le) δ hδ0 ?_
      exact hδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le)
  have hδs : δ ≤ 1 / 200 := by
    have hc₀32 : c₀ ≤ 1 / 32 := (min_le_right _ _).trans
      (one_div_le_one_div_of_le (by norm_num) (by linarith))
    have hE2 : Real.exp (-r) ≤ 1 / 7 := by
      have he := Real.exp_one_gt_d9
      have h2 : Real.exp 2 ≤ Real.exp r := Real.exp_le_exp.mpr hr
      have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos r) (by norm_num)]
      nlinarith
    nlinarith [Real.exp_pos (-r)]
  exact ⟨hmass, fun hF hFc hodd hFL hsupp =>
    sum_primeShift_le_lightCone_of_mass_le hF hFc hodd hFL hsupp hr hδ0 hδs hmass⟩

/-- **Scale-invariant local light-cone box bound.** On the light-cone box `[r − 2δ, r]²` of side
length `2δ`, the odd edge tent `edgeTentOdd r (δ/2)` of width `ε = δ/2` has pointwise integrand
`≤ 3ε = (3/2)δ`, so `stripBoxEnergy (edgeTentOdd r (δ/2)) (r − 2δ) r ≤ 6 δ³`. -/
theorem stripBoxEnergy_edgeTent_lightConeBox_le {r δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (h2δr : 2 * δ ≤ r) :
    stripBoxEnergy (edgeTentOdd r (δ / 2)) (r - 2 * δ) r ≤ 6 * δ ^ 3 := by
  set ε := δ / 2
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by dsimp [ε]; linarith
  have hεr : ε < r := by dsimp [ε]; linarith
  have hpr : r - 2 * δ ≤ r := by linarith
  have hgm := measurable_stripIntegrand (continuous_edgeTentOdd r ε)
  have hgb : ∀ x ∈ Icc (r - 2 * δ) r, ∀ y ∈ Icc (r - 2 * δ) r,
      |stripIntegrand (edgeTentOdd r ε) x y| ≤ 3 * ε := fun x hx y hy => by
    obtain ⟨h0, h1⟩ := stripIntegrand_edgeTentOdd_bounds hε0 hε1 hεr
      ⟨by linarith [hx.1], hx.2⟩ ⟨by linarith [hy.1], hy.2⟩
    rw [abs_of_nonneg h0]
    refine h1.trans ?_
    unfold edgeTentWeight; split_ifs <;> linarith
  obtain ⟨hgi, hgo⟩ := intervalIntegrable_iterated hpr hgm hgb
  unfold stripBoxEnergy
  have hinner : ∀ x ∈ Icc (r - 2 * δ) r,
      (∫ y in (r - 2 * δ)..r, stripIntegrand (edgeTentOdd r ε) x y) ≤ 2 * δ * (3 * ε) := by
    intro x hx
    have h := intervalIntegral.integral_mono_on hpr (hgi x hx) intervalIntegrable_const
      fun y hy => (le_abs_self _).trans (hgb x hx y hy)
    rw [intervalIntegral.integral_const, smul_eq_mul, show r - (r - 2 * δ) = 2 * δ by ring] at h
    exact h
  have houter := intervalIntegral.integral_mono_on hpr hgo intervalIntegrable_const hinner
  rw [intervalIntegral.integral_const, smul_eq_mul, show r - (r - 2 * δ) = 2 * δ by ring] at houter
  refine houter.trans (le_of_eq ?_)
  dsimp [ε]; ring

/-- The outer half of the light-cone band: `2r − 2δ ≤ log n ≤ 2r − δ`. -/
def lightConeOuterHalf (r δ : ℝ) : Finset ℕ :=
  (lightConeBand r δ).filter fun n => Real.log n ≤ 2 * r - δ

/-- Whenever `∑_{n ∈ lightConeOuterHalf r δ} Λ(n)/√n > 1536`, the scaled edge tent
`edgeTentOdd r (δ/2)` breaks odd-part sharing on the light-cone box `[r − 2δ, r]²`: the `δ³`
factors in `6 δ³` and `2 · (δ³/512)` cancel identically. -/
theorem lightConeBox_oddPart_sharing_fails_of_outerHalf_sum {r δ : ℝ} (hr : 2 ≤ r)
    (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 12)
    (hsum : 1536 < ∑ n ∈ lightConeOuterHalf r δ, vonMangoldtAtom n) :
    ∃ F : ℝ → ℝ, Continuous F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ a b, |F a - F b| ≤ 2 * |a - b|) ∧ (∀ x, r < |x| → F x = 0) ∧
      (∀ n ∈ lightConeOuterHalf r δ, (∫ x, F x * F (x + Real.log n)) = 0 ∧
        2 * vonMangoldtAtom n * (∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2) ≤
          stripBoxEnergy F (Real.log n - r) r) ∧
      stripBoxEnergy F (r - 2 * δ) r <
        ∑ n ∈ lightConeBand r δ,
          2 * vonMangoldtAtom n *
            ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2 := by
  set ε := δ / 2
  have hε0 : 0 < ε := by positivity
  have hεr : ε < r := by dsimp [ε]; linarith
  set F := edgeTentOdd r ε
  refine ⟨F, continuous_edgeTentOdd r ε, hasCompactSupport_edgeTentOdd hε0 hεr,
    edgeTentOdd_odd r ε, edgeTentOdd_lipschitz r ε,
    fun x hx => edgeTentOdd_eq_zero_of_lt hε0 hεr hx, ?_, ?_⟩
  · intro n hn
    obtain ⟨hmem, hhi_outer⟩ := Finset.mem_filter.mp hn
    obtain ⟨-, -, hlo, hhi⟩ := le_of_mem_lightConeBand (by linarith) hmem
    obtain ⟨hz, -⟩ := edgeTent_oddPart_eq hε0 hεr (L := Real.log n) (by linarith)
      (by dsimp [ε]; linarith)
    refine ⟨hz, ?_⟩
    set L := Real.log n
    set p := L - r
    have hp : 1 / 2 ≤ p := by dsimp [p, L]; linarith
    have hpr : p < r := by dsimp [p, L]; linarith
    have hL : p + r = L := by dsimp [p]; ring
    have hms := sharpMicroFold_strip_ge (continuous_edgeTentOdd r ε) (edgeTentOdd_lipschitz r ε)
      (by linarith) hpr hL (by dsimp [p, L]; linarith) (by dsimp [p, L]; linarith)
    have hlam : 2 * vonMangoldtAtom n ≤ 19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2 := by
      have hη0 : 0 ≤ (r - p) / 2 := by linarith
      have hη : (r - p) / 2 ≤ 1 / 12 := by dsimp [p, L]; linarith
      have hηp : (r - p) / 2 / p ≤ 1 / 6 := by rw [div_le_iff₀ (by linarith)]; linarith
      have hη2 : 3 * ((r - p) / 2) ^ 2 ≤ 1 / 48 := by nlinarith
      linarith [vonMangoldtAtom_le n]
    have hα0 : 0 ≤ ∫ a in p..r, reflectedOddPart F L a ^ 2 :=
      intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
    have := mul_le_mul_of_nonneg_right hlam hα0
    unfold stripBoxEnergy stripIntegrand
    linarith
  · have hbox := stripBoxEnergy_edgeTent_lightConeBox_le (r := r) hδ0 (by linarith) (by linarith)
    have hterm : ∀ n ∈ lightConeOuterHalf r δ,
        2 * vonMangoldtAtom n * (ε ^ 3 / 64) ≤
          2 * vonMangoldtAtom n *
            ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2 := by
      intro n hn
      obtain ⟨hmem, hhi_outer⟩ := Finset.mem_filter.mp hn
      obtain ⟨-, -, hlo, -⟩ := le_of_mem_lightConeBand (by linarith) hmem
      obtain ⟨-, hodd⟩ := edgeTent_oddPart_eq hε0 hεr (L := Real.log n) (by linarith)
        (by dsimp [ε]; linarith)
      have hmass := edgeTent_sq_integral_ge hε0 hεr (L := Real.log n) (by dsimp [ε]; linarith)
      refine mul_le_mul_of_nonneg_left ?_ (by linarith [vonMangoldtAtom_nonneg n])
      linarith
    have hsub : lightConeOuterHalf r δ ⊆ lightConeBand r δ := Finset.filter_subset _ _
    have hnonneg : ∀ n ∈ lightConeBand r δ, n ∉ lightConeOuterHalf r δ →
        0 ≤ 2 * vonMangoldtAtom n *
          ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2 := by
      intro n hn _
      obtain ⟨-, -, hlo, hhi⟩ := le_of_mem_lightConeBand (by linarith) hn
      have hα0 : 0 ≤ ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2 :=
        intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _
      exact mul_nonneg (by linarith [vonMangoldtAtom_nonneg n]) hα0
    have hsum1 := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum1
    have hsum2 := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    have hlt : 6 * δ ^ 3 < 2 * (∑ n ∈ lightConeOuterHalf r δ, vonMangoldtAtom n) * (ε ^ 3 / 64) := by
      have hδ3 : 0 < δ ^ 3 := by positivity
      have heq : 2 * (∑ n ∈ lightConeOuterHalf r δ, vonMangoldtAtom n) * (ε ^ 3 / 64) =
          (∑ n ∈ lightConeOuterHalf r δ, vonMangoldtAtom n) * (δ ^ 3 / 256) := by
        dsimp [ε]; ring
      rw [heq]
      nlinarith
    exact lt_of_le_of_lt hbox (lt_of_lt_of_le hlt (hsum1.trans hsum2))

/-- For all large `R`, the thin band `thinBand R` (`2R − 1/6 ≤ log n ≤ 2R − 1/24`) has
`∑_{n ∈ thinBand R} Λ(n)/√n ≥ e^R / 22`. -/
theorem eventually_exp_div_le_sum_thinBand :
    ∀ᶠ R in atTop, Real.exp R / 22 ≤ ∑ n ∈ thinBand R, vonMangoldtAtom n := by
  have hpnt := RHTower.Sieve.tendsto_sum_vonMangoldt_div
  have hlin : ∀ c : ℝ, Tendsto (fun r : ℝ => Real.exp (2 * r - c)) atTop atTop := fun c =>
    Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have h1 := (hpnt.comp (hlin (1 / 24))).eventually
    (lt_mem_nhds (show (99 / 100 : ℝ) < 1 by norm_num))
  have h2 := (hpnt.comp (hlin (1 / 6))).eventually
    (gt_mem_nhds (show (1 : ℝ) < 101 / 100 by norm_num))
  filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with R h1 h2 hR
  simp only [Function.comp_apply] at h1 h2
  set X := Real.exp (2 * R - 1 / 24) with hX
  set Y := Real.exp (2 * R - 1 / 6) with hY
  set ψX := ∑ n ∈ Finset.range (⌊X⌋₊ + 1), ArithmeticFunction.vonMangoldt n with hψX
  set ψY := ∑ n ∈ Finset.range (⌊Y⌋₊ + 1), ArithmeticFunction.vonMangoldt n with hψY
  have hX0 : 0 < X := Real.exp_pos _
  have hY0 : 0 < Y := Real.exp_pos _
  rw [lt_div_iff₀ hX0] at h1
  rw [div_lt_iff₀ hY0] at h2
  have hYX : Y ≤ 8 / 9 * X := by
    have e : Y = X * Real.exp (-(1 / 8)) := by rw [hX, hY, ← Real.exp_add]; ring_nf
    have h8 : 9 / 8 ≤ Real.exp (1 / 8) := by linarith [Real.add_one_le_exp (1 / 8 : ℝ)]
    have h8' : Real.exp (-(1 / 8)) ≤ 8 / 9 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
    rw [e]; nlinarith
  have hgap : X / 11 ≤ ψX - ψY := by nlinarith
  have hsq : Real.sqrt X = Real.exp (R - 1 / 48) := by
    rw [hX, ← Real.exp_half]; ring_nf
  have hsq0 : 0 < Real.sqrt X := by rw [hsq]; exact Real.exp_pos _
  have hhalf : Real.exp R / 2 ≤ Real.sqrt X := by
    rw [hsq]
    have e : Real.exp (R - 1 / 48) = Real.exp R * Real.exp (-(1 / 48)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have := Real.add_one_le_exp (-(1 / 48) : ℝ)
    nlinarith [Real.exp_pos R]
  have hXs : X = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0.le).symm
  have hband := psi_sub_div_le_sum_thinBand hR
  rw [← hX, ← hY, ← hψX, ← hψY] at hband
  have hdiv : Real.sqrt X / 11 ≤ (ψX - ψY) / Real.sqrt X := by
    rw [le_div_iff₀ hsq0]; nlinarith
  linarith

/-- **Unconditional cofinal refutation of light-cone odd-part sharing at the exact square-root width
`δ = C e^{−r}`.** For every `C ≥ 64000`, there exist arbitrarily large apertures `r` (`∃ᶠ r in atTop`)
and an odd test `F` supported in `[−r, r]` such that every atom in the outer half of
`lightConeBand r (C e^{−r})` vanishes and has its odd part paid by its own strip, yet the sum of the
odd parts over `lightConeBand r (C e^{−r})` strictly exceeds the local light-cone box energy
`stripBoxEnergy F (r − 2 C e^{−r}) r`. -/
theorem frequently_lightConeBox_oddPart_sharing_fails_at_squareRoot {C : ℝ} (hC : 64000 ≤ C) :
    ∃ᶠ r in atTop, ∃ F : ℝ → ℝ, Continuous F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ a b, |F a - F b| ≤ 2 * |a - b|) ∧ (∀ x, r < |x| → F x = 0) ∧
      (∀ n ∈ lightConeOuterHalf r (C * Real.exp (-r)), (∫ x, F x * F (x + Real.log n)) = 0 ∧
        2 * vonMangoldtAtom n * (∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2) ≤
          stripBoxEnergy F (Real.log n - r) r) ∧
      stripBoxEnergy F (r - 2 * (C * Real.exp (-r))) r <
        ∑ n ∈ lightConeBand r (C * Real.exp (-r)),
          2 * vonMangoldtAtom n *
            ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2 := by
  rw [Filter.frequently_atTop]
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.mp eventually_exp_div_le_sum_thinBand
  intro R₀
  set R := max (max (R₀ + 1) R₁) (72 * C + 100000)
  have h1_max : R₀ + 1 ≤ max (R₀ + 1) R₁ := le_max_left _ _
  have h2_max : max (R₀ + 1) R₁ ≤ R := le_max_left _ _
  have hRC : 72 * C + 100000 ≤ R := le_max_right _ _
  have hRR₀ : R₀ ≤ R - 1 / 6 := by linarith
  have hRR₁ : R₁ ≤ R := (le_max_right (R₀ + 1) R₁).trans h2_max
  have hR_ge2 : 2 ≤ R - 1 / 6 := by linarith
  have hE_ge_R : R ≤ Real.exp (R - 1 / 6) := by
    have := Real.add_one_le_exp (R - 1 / 6)
    linarith
  have hE_ge : R ≤ Real.exp R :=
    hE_ge_R.trans (Real.exp_le_exp.mpr (by linarith))
  set η := C * Real.exp (-R)
  have hη_pos : 0 < η := by positivity
  have hη_small : C * Real.exp (-(R - 1 / 6)) ≤ 1 / 72 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith
  have hη72 : η ≤ 1 / 72 := by
    have : Real.exp (-R) ≤ Real.exp (-(R - 1 / 6)) := Real.exp_le_exp.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left this (by positivity)).trans hη_small
  set M := ⌈(1 / 8) / η⌉₊ + 1
  have hM_pos : 0 < M := Nat.succ_pos _
  -- For each `k < M`, choose `r_k ∈ [R - 1/6, R]` with `2 * r_k - C * e^{-r_k} = (2R - 1/6) + (k + 1)η`
  set g : ℝ → ℝ := fun r => 2 * r - C * Real.exp (-r)
  have hg_cont : Continuous g := by dsimp [g]; fun_prop
  have hex_r : ∀ k : ℕ, k < M →
      ∃ r ∈ Icc (R - 1 / 6) R, g r = (2 * R - 1 / 6) + (k + 1 : ℝ) * η := by
    intro k hk
    have hk_le : (k + 1 : ℝ) * η ≤ 1 / 8 + 2 * η := by
      have hk1 : (k + 1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk
      have hM_le : (M : ℝ) ≤ (1 / 8) / η + 2 := by
        dsimp [M]; push_cast
        have := Nat.ceil_lt_add_one (show 0 ≤ (1 / 8) / η by positivity)
        linarith
      have hmul := mul_le_mul_of_nonneg_right (hk1.trans hM_le) hη_pos.le
      have heq : ((1 / 8) / η + 2) * η = 1 / 8 + 2 * η := by field_simp
      linarith
    have hy_lo : g (R - 1 / 6) ≤ (2 * R - 1 / 6) + (k + 1 : ℝ) * η := by
      dsimp [g]
      have : 0 ≤ (k + 1 : ℝ) * η := by positivity
      have : 0 ≤ C * Real.exp (-(R - 1 / 6)) := by positivity
      linarith
    have hy_hi : (2 * R - 1 / 6) + (k + 1 : ℝ) * η ≤ g R := by
      have hgR : g R = 2 * R - η := rfl
      rw [hgR]
      linarith
    exact intermediate_value_Icc (by linarith) hg_cont.continuousOn ⟨hy_lo, hy_hi⟩
  choose r_fn hr_fn using fun k : Fin M => hex_r k.1 k.2
  -- Every `n ∈ thinBand R` lands in `lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k))` for some `k`
  have hcover : ∀ n ∈ thinBand R, ∃ k : Fin M,
      n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)) := by
    intro n hn
    obtain ⟨h1, hlo, hhi⟩ := Finset.mem_filter.mp hn
    set k₀ := ⌊(Real.log n - (2 * R - 1 / 6)) / η⌋₊
    have hk₀_lt : k₀ < M := by
      dsimp [M]
      have hle : (Real.log n - (2 * R - 1 / 6)) / η ≤ (1 / 8) / η :=
        div_le_div_of_nonneg_right (by linarith) hη_pos.le
      have hfl : k₀ ≤ ⌈(1 / 8) / η⌉₊ :=
        (Nat.floor_le_ceil _).trans (Nat.ceil_le_ceil hle)
      omega
    refine ⟨⟨k₀, hk₀_lt⟩, ?_⟩
    obtain ⟨hr_mem, hg_eq⟩ := hr_fn ⟨k₀, hk₀_lt⟩
    set rk := r_fn ⟨k₀, hk₀_lt⟩
    set δk := C * Real.exp (-rk)
    have hδk_ge : η ≤ δk :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hr_mem.2])) (by positivity)
    have hquot_nonneg : 0 ≤ (Real.log n - (2 * R - 1 / 6)) / η :=
      div_nonneg (by linarith) hη_pos.le
    have hlog_ge : (2 * R - 1 / 6) + (k₀ : ℝ) * η ≤ Real.log n := by
      have h := Nat.floor_le hquot_nonneg
      have h' := (le_div_iff₀ hη_pos).mp h
      dsimp [k₀] at h' ⊢
      linarith
    have hlog_lt : Real.log n < (2 * R - 1 / 6) + (k₀ + 1 : ℝ) * η := by
      have h := Nat.lt_floor_add_one ((Real.log n - (2 * R - 1 / 6)) / η)
      have h' := (div_lt_iff₀ hη_pos).mp h
      dsimp [k₀] at h' ⊢
      linarith
    have hg_eq' : 2 * rk - δk = (2 * R - 1 / 6) + (k₀ + 1 : ℝ) * η := hg_eq
    have hlo_cone : 2 * rk - 2 * δk ≤ Real.log n := by linarith
    have hhi_outer : Real.log n ≤ 2 * rk - δk := by linarith
    have hhi_cone : Real.log n < 2 * rk := by
      have : 0 < δk := by positivity
      linarith
    have hn_pos : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp at hlo; linarith
      · exact_mod_cast hpos
    have hn_lt : n < ⌈Real.exp (2 * rk)⌉₊ := by
      have hlt_exp : (n : ℝ) < Real.exp (2 * rk) := by
        rw [← Real.exp_log hn_pos]
        exact Real.exp_lt_exp.mpr hhi_cone
      have : (n : ℝ) < (⌈Real.exp (2 * rk)⌉₊ : ℝ) := hlt_exp.trans_le (Nat.le_ceil _)
      exact_mod_cast this
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn_lt, hlo_cone, hhi_cone⟩,
      hhi_outer⟩
  -- Sum over `thinBand R` is bounded by the sum over `k : Fin M`
  have hsum_cover : ∑ n ∈ thinBand R, vonMangoldtAtom n ≤
      ∑ k : Fin M, ∑ n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)), vonMangoldtAtom n := by
    classical
    calc ∑ n ∈ thinBand R, vonMangoldtAtom n
        ≤ ∑ n ∈ thinBand R, ∑ k : Fin M,
            if n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)) then vonMangoldtAtom n else 0 := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨k₀, hk₀⟩ := hcover n hn
          have hle := Finset.single_le_sum
            (f := fun k : Fin M =>
              if n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)) then vonMangoldtAtom n else 0)
            (fun k _ => by split_ifs; exact vonMangoldtAtom_nonneg n; exact le_rfl)
            (Finset.mem_univ k₀)
          rwa [if_pos hk₀] at hle
      _ = ∑ k : Fin M, ∑ n ∈ thinBand R,
            if n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)) then vonMangoldtAtom n else 0 :=
          Finset.sum_comm
      _ ≤ ∑ k : Fin M, ∑ n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)), vonMangoldtAtom n := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [Finset.sum_ite_mem]
          exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
            fun n _ _ => vonMangoldtAtom_nonneg n
  -- Compare `1536 * M` with `Real.exp R / 22`
  have hM_bound : (M : ℝ) * 1536 < ∑ n ∈ thinBand R, vonMangoldtAtom n := by
    have hM_le : (M : ℝ) ≤ Real.exp R / (8 * C) + 2 := by
      have h1 : (M : ℝ) ≤ (1 / 8) / η + 2 := by
        dsimp [M]; push_cast
        have := Nat.ceil_lt_add_one (show 0 ≤ (1 / 8) / η by positivity)
        linarith
      have h2 : (1 / 8) / η = Real.exp R / (8 * C) := by
        dsimp [η]
        rw [Real.exp_neg, div_mul_eq_div_div, div_inv_eq_mul]
        ring
      linarith
    have hdiv_le : Real.exp R / (8 * C) ≤ Real.exp R / 512000 :=
      div_le_div_of_nonneg_left (Real.exp_pos R).le (by norm_num) (by linarith)
    have hthin := hR₁ R hRR₁
    linarith
  -- By pigeonhole, some `k : Fin M` has `1536 < ∑ n ∈ lightConeOuterHalf (r_fn k) ...`
  have hex_k : ∃ k : Fin M,
      1536 < ∑ n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)), vonMangoldtAtom n := by
    by_contra h_all
    have h_le : ∀ k ∈ (Finset.univ : Finset (Fin M)),
        ∑ n ∈ lightConeOuterHalf (r_fn k) (C * Real.exp (-r_fn k)), vonMangoldtAtom n ≤ 1536 :=
      fun k _ => not_lt.mp (fun hlt => h_all ⟨k, hlt⟩)
    have hsum_le := Finset.sum_le_card_nsmul Finset.univ _ 1536 h_le
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_le
    linarith
  obtain ⟨k, hk⟩ := hex_k
  obtain ⟨hr_mem, -⟩ := hr_fn k
  have hrk_R₀ : R₀ ≤ r_fn k := hRR₀.trans hr_mem.1
  have hrk_2 : 2 ≤ r_fn k := hR_ge2.trans hr_mem.1
  have hδk_pos : 0 < C * Real.exp (-r_fn k) := by positivity
  have hδk_12 : C * Real.exp (-r_fn k) ≤ 1 / 12 := by
    have : Real.exp (-r_fn k) ≤ Real.exp (-(R - 1 / 6)) :=
      Real.exp_le_exp.mpr (by linarith [hr_mem.1])
    exact (mul_le_mul_of_nonneg_left this (by positivity)).trans (hη_small.trans (by norm_num))
  exact ⟨r_fn k, hrk_R₀,
    lightConeBox_oddPart_sharing_fails_of_outerHalf_sum hrk_2 hδk_pos hδk_12 hk⟩

/-! ## Part III: Bipolar Edge-Dipole Witness and Unconditional Refutation of Signed Thin-Band Allocation -/

/-- The bipolar edge-dipole witness at aperture `r`: a positive edge tent of width `1/48` at `r`
minus a negative edge tent of width `1/12` at `r − 1/12`, extended oddly to `[−r, r]`. -/
def bipolarEdgeTentOdd (r x : ℝ) : ℝ :=
  edgeTentOdd r (1 / 48) x - edgeTentOdd (r - 1 / 12) (1 / 12) x

theorem continuous_bipolarEdgeTentOdd (r : ℝ) : Continuous (bipolarEdgeTentOdd r) :=
  (continuous_edgeTentOdd r (1 / 48)).sub (continuous_edgeTentOdd (r - 1 / 12) (1 / 12))

theorem bipolarEdgeTentOdd_odd (r x : ℝ) :
    bipolarEdgeTentOdd r (-x) = -bipolarEdgeTentOdd r x := by
  unfold bipolarEdgeTentOdd
  rw [edgeTentOdd_odd, edgeTentOdd_odd]
  ring

theorem bipolarEdgeTentOdd_lipschitz (r a b : ℝ) :
    |bipolarEdgeTentOdd r a - bipolarEdgeTentOdd r b| ≤ 4 * |a - b| := by
  unfold bipolarEdgeTentOdd
  have h1 := edgeTentOdd_lipschitz r (1 / 48) a b
  have h2 := edgeTentOdd_lipschitz (r - 1 / 12) (1 / 12) a b
  have h3 := abs_sub (edgeTentOdd r (1 / 48) a - edgeTentOdd r (1 / 48) b)
    (edgeTentOdd (r - 1 / 12) (1 / 12) a - edgeTentOdd (r - 1 / 12) (1 / 12) b)
  rw [show edgeTentOdd r (1 / 48) a - edgeTentOdd (r - 1 / 12) (1 / 12) a -
      (edgeTentOdd r (1 / 48) b - edgeTentOdd (r - 1 / 12) (1 / 12) b) =
    edgeTentOdd r (1 / 48) a - edgeTentOdd r (1 / 48) b -
      (edgeTentOdd (r - 1 / 12) (1 / 12) a - edgeTentOdd (r - 1 / 12) (1 / 12) b) by ring]
  linarith

theorem bipolarEdgeTentOdd_eq_zero_of_lt {r x : ℝ} (hr : 1 ≤ r) (hx : r < |x|) :
    bipolarEdgeTentOdd r x = 0 := by
  unfold bipolarEdgeTentOdd
  rw [edgeTentOdd_eq_zero_of_lt (by norm_num) (by linarith) hx,
    edgeTentOdd_eq_zero_of_lt (by norm_num) (by linarith) (by linarith), sub_self]

theorem hasCompactSupport_bipolarEdgeTentOdd {r : ℝ} (hr : 1 ≤ r) :
    HasCompactSupport (bipolarEdgeTentOdd r) :=
  HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun x hx => by
    refine bipolarEdgeTentOdd_eq_zero_of_lt hr ?_
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h

/-- Two edge tents whose open supports cannot simultaneously contain `u` and `v` have zero product. -/
theorem edgeTent_mul_eq_zero_of_disjoint {r₁ ε₁ r₂ ε₂ u v : ℝ}
    (h : r₁ - ε₁ < u → u < r₁ → r₂ - ε₂ < v → v < r₂ → False) :
    edgeTent r₁ ε₁ u * edgeTent r₂ ε₂ v = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mem_of_edgeTent_ne_zero (left_ne_zero_of_mul hne)
  obtain ⟨h3, h4⟩ := mem_of_edgeTent_ne_zero (right_ne_zero_of_mul hne)
  exact h h1 h2 h3 h4

/-- **Exact shift-product decomposition on the thin band.** For every `r ≥ 1`, every shift
`L ∈ [2r − 1/6, 2r − 1/24]`, and every `x : ℝ`, all self-pairings of the two tents vanish and only
the two nonnegative cross-pairings survive:
`bipolarEdgeTentOdd r x * bipolarEdgeTentOdd r (x + L) =
  edgeTent r (1/48) (-x) * edgeTent (r − 1/12) (1/12) (x + L) +
  edgeTent (r − 1/12) (1/12) (-x) * edgeTent r (1/48) (x + L)`. -/
theorem bipolarEdgeTentOdd_mul_shift_eq {r L : ℝ} (hr : 1 ≤ r)
    (hL1 : 2 * r - 1 / 6 ≤ L) (hL2 : L ≤ 2 * r - 1 / 24) (x : ℝ) :
    bipolarEdgeTentOdd r x * bipolarEdgeTentOdd r (x + L) =
      edgeTent r (1 / 48) (-x) * edgeTent (r - 1 / 12) (1 / 12) (x + L) +
        edgeTent (r - 1 / 12) (1 / 12) (-x) * edgeTent r (1 / 48) (x + L) := by
  unfold bipolarEdgeTentOdd edgeTentOdd
  -- If `x > r - 1/6`, then `x + L > r` and `-(x + L) < r - 1/6`, so the second factor vanishes.
  by_cases hx_pos : r - 1 / 6 < x
  · have hC1 : edgeTent r (1 / 48) (x + L) = 0 := edgeTent_eq_zero_of_ge (by linarith)
    have hC2 : edgeTent r (1 / 48) (-(x + L)) = 0 := edgeTent_eq_zero_of_le (by linarith)
    have hD1 : edgeTent (r - 1 / 12) (1 / 12) (x + L) = 0 := edgeTent_eq_zero_of_ge (by linarith)
    have hD2 : edgeTent (r - 1 / 12) (1 / 12) (-(x + L)) = 0 := edgeTent_eq_zero_of_le (by linarith)
    rw [hC1, hC2, hD1, hD2]
    ring
  -- Otherwise `x ≤ r - 1/6`, so both positive-half tents at `x` vanish.
  have hA1 : edgeTent r (1 / 48) x = 0 := edgeTent_eq_zero_of_le (by linarith)
  have hB1 : edgeTent (r - 1 / 12) (1 / 12) x = 0 := edgeTent_eq_zero_of_le (by linarith)
  rw [hA1, hB1]
  -- If `-(x + L) > r - 1/6`, then `-x > r`, so both negative-half tents at `x` vanish.
  by_cases hy_neg : r - 1 / 6 < -(x + L)
  · have hA2 : edgeTent r (1 / 48) (-x) = 0 := edgeTent_eq_zero_of_ge (by linarith)
    have hB2 : edgeTent (r - 1 / 12) (1 / 12) (-x) = 0 := edgeTent_eq_zero_of_ge (by linarith)
    rw [hA2, hB2]
    ring
  have hC2 : edgeTent r (1 / 48) (-(x + L)) = 0 := edgeTent_eq_zero_of_le (by linarith)
  have hD2 : edgeTent (r - 1 / 12) (1 / 12) (-(x + L)) = 0 := edgeTent_eq_zero_of_le (by linarith)
  rw [hC2, hD2]
  have hAC : edgeTent r (1 / 48) (-x) * edgeTent r (1 / 48) (x + L) = 0 :=
    edgeTent_mul_eq_zero_of_disjoint fun _ _ _ _ => by linarith
  have hBD : edgeTent (r - 1 / 12) (1 / 12) (-x) * edgeTent (r - 1 / 12) (1 / 12) (x + L) = 0 :=
    edgeTent_mul_eq_zero_of_disjoint fun _ _ _ _ => by linarith
  linear_combination -hAC - hBD

/-- **Pointwise nonnegativity of the bipolar shift product across the entire thin band.** -/
theorem bipolarEdgeTentOdd_mul_shift_nonneg {r L : ℝ} (hr : 1 ≤ r)
    (hL1 : 2 * r - 1 / 6 ≤ L) (hL2 : L ≤ 2 * r - 1 / 24) (x : ℝ) :
    0 ≤ bipolarEdgeTentOdd r x * bipolarEdgeTentOdd r (x + L) := by
  rw [bipolarEdgeTentOdd_mul_shift_eq hr hL1 hL2 x]
  exact add_nonneg (mul_nonneg (edgeTent_nonneg _ _ _) (edgeTent_nonneg _ _ _))
    (mul_nonneg (edgeTent_nonneg _ _ _) (edgeTent_nonneg _ _ _))

/-- On the core sub-band `2r − 7/48 ≤ L ≤ 2r − 1/8` (`⊂ [2r − 1/6, 2r − 1/24]`), the correlation
`∫ F(x) F(x + L) dx` of `bipolarEdgeTentOdd r` is at least `1 / 884736`. -/
theorem integral_bipolarEdgeTentOdd_mul_shift_ge {r L : ℝ} (hr : 1 ≤ r)
    (hL1 : 2 * r - 7 / 48 ≤ L) (hL2 : L ≤ 2 * r - 1 / 8) :
    1 / 884736 ≤ ∫ x, bipolarEdgeTentOdd r x * bipolarEdgeTentOdd r (x + L) := by
  set g : ℝ → ℝ := fun x => bipolarEdgeTentOdd r x * bipolarEdgeTentOdd r (x + L)
  have hg_cont : Continuous g :=
    (continuous_bipolarEdgeTentOdd r).mul
      ((continuous_bipolarEdgeTentOdd r).comp (continuous_id.add continuous_const))
  have hg_supp : HasCompactSupport g :=
    (hasCompactSupport_bipolarEdgeTentOdd hr).mul_right
  have hg_int : Integrable g := hg_cont.integrable_of_hasCompactSupport hg_supp
  have hg_nonneg : ∀ x, 0 ≤ g x :=
    bipolarEdgeTentOdd_mul_shift_nonneg hr (by linarith) (by linarith)
  set a := -(r - 1 / 192)
  set b := -(r - 3 / 192)
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hsub : ∫ x in a..b, g x ≤ ∫ x, g x := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_le_integral hg_int (Eventually.of_forall hg_nonneg)
  have hpt : ∀ x ∈ Icc a b, (1 / 9216 : ℝ) ≤ g x := by
    intro x hx
    have hxa : -(r - 1 / 192) ≤ x := hx.1
    have hxb : x ≤ -(r - 3 / 192) := hx.2
    dsimp [g]
    rw [bipolarEdgeTentOdd_mul_shift_eq hr (by linarith) (by linarith) x]
    have h1 : (1 / 48 : ℝ) / 4 ≤ edgeTent r (1 / 48) (-x) :=
      edgeTent_ge_quarter (by linarith) (by linarith)
    have h2 : (1 / 12 : ℝ) / 4 ≤ edgeTent (r - 1 / 12) (1 / 12) (x + L) :=
      edgeTent_ge_quarter (by linarith) (by linarith)
    have h3 : 0 ≤ edgeTent (r - 1 / 12) (1 / 12) (-x) * edgeTent r (1 / 48) (x + L) :=
      mul_nonneg (edgeTent_nonneg _ _ _) (edgeTent_nonneg _ _ _)
    have hmul : (1 / 192 : ℝ) * (1 / 48) ≤
        edgeTent r (1 / 48) (-x) * edgeTent (r - 1 / 12) (1 / 12) (x + L) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (edgeTent_nonneg _ _ _)
    linarith
  have hlow := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (hg_cont.intervalIntegrable a b) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have hlen : (b - a) * (1 / 9216 : ℝ) = 1 / 884736 := by dsimp [a, b]; ring
  linarith

/-- Uniform height bound on `edgeTent`: `edgeTent r ε x ≤ ε / 2` for `0 ≤ ε`. -/
theorem edgeTent_le_half {r ε x : ℝ} (hε : 0 ≤ ε) : edgeTent r ε x ≤ ε / 2 := by
  unfold edgeTent
  exact max_le (by linarith [abs_nonneg (x - (r - ε / 2))]) (by positivity)

/-- Pointwise bound on `stripIntegrand (bipolarEdgeTentOdd r) x y` on `[0, r]²`:
vanishes on `[0, r − 1/6]²` and is at most `1` everywhere on `[0, r]²`. -/
theorem stripIntegrand_bipolarEdgeTentOdd_bounds {r x y : ℝ} (hr : 1 ≤ r)
    (hx : x ∈ Icc 0 r) (hy : y ∈ Icc 0 r) :
    0 ≤ stripIntegrand (bipolarEdgeTentOdd r) x y ∧
      stripIntegrand (bipolarEdgeTentOdd r) x y ≤
        (if r - 1 / 6 < x then (1 : ℝ) else 0) + (if r - 1 / 6 < y then (1 : ℝ) else 0) := by
  set F := bipolarEdgeTentOdd r
  have hnonneg := (abs_stripIntegrand_le_of_lipschitz (bipolarEdgeTentOdd_lipschitz r) hx hy).1
  refine ⟨hnonneg, ?_⟩
  rcases le_or_gt x (r - 1 / 6) with hxa | hxa <;> rcases le_or_gt y (r - 1 / 6) with hya | hya
  · have hFx : F x = 0 := by
      dsimp [F, bipolarEdgeTentOdd]
      rw [edgeTentOdd_of_nonneg (by linarith) hx.1, edgeTentOdd_of_nonneg (by linarith) hx.1,
        edgeTent_eq_zero_of_le (by linarith), edgeTent_eq_zero_of_le (by linarith), sub_self]
    have hFy : F y = 0 := by
      dsimp [F, bipolarEdgeTentOdd]
      rw [edgeTentOdd_of_nonneg (by linarith) hy.1, edgeTentOdd_of_nonneg (by linarith) hy.1,
        edgeTent_eq_zero_of_le (by linarith), edgeTent_eq_zero_of_le (by linarith), sub_self]
    unfold stripIntegrand
    rw [hFx, hFy, sub_self]
    split_ifs <;> simp
  all_goals
    have hR_ge_one : (1 : ℝ) ≤
        (if r - 1 / 6 < x then (1 : ℝ) else 0) + (if r - 1 / 6 < y then (1 : ℝ) else 0) := by
      split_ifs <;> linarith
    refine le_trans ?_ hR_ge_one
    unfold stripIntegrand
    by_cases hxy : x = y
    · subst hxy; simp
    rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · rw [surplusKernel_zero_left hy.1, zero_mul]; norm_num
    rcases eq_or_lt_of_le hy.1 with rfl | hy0
    · rw [surplusKernel_comm, surplusKernel_zero_left hx.1, zero_mul]; norm_num
    have hd0 : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hk := (surplusKernel_le hx0 hy0).trans (archLevyDensity_le_inv hd0)
    have hFx_bd : |F x| ≤ 1 / 16 := by
      dsimp [F, bipolarEdgeTentOdd]
      rw [edgeTentOdd_of_nonneg (by linarith) hx.1, edgeTentOdd_of_nonneg (by linarith) hx.1,
        abs_le]
      have := edgeTent_nonneg r (1 / 48) x
      have := edgeTent_le_half (r := r) (ε := 1 / 48) (x := x) (by norm_num)
      have := edgeTent_nonneg (r - 1 / 12) (1 / 12) x
      have := edgeTent_le_half (r := r - 1 / 12) (ε := 1 / 12) (x := x) (by norm_num)
      exact ⟨by linarith, by linarith⟩
    have hFy_bd : |F y| ≤ 1 / 16 := by
      dsimp [F, bipolarEdgeTentOdd]
      rw [edgeTentOdd_of_nonneg (by linarith) hy.1, edgeTentOdd_of_nonneg (by linarith) hy.1,
        abs_le]
      have := edgeTent_nonneg r (1 / 48) y
      have := edgeTent_le_half (r := r) (ε := 1 / 48) (x := y) (by norm_num)
      have := edgeTent_nonneg (r - 1 / 12) (1 / 12) y
      have := edgeTent_le_half (r := r - 1 / 12) (ε := 1 / 12) (x := y) (by norm_num)
      exact ⟨by linarith, by linarith⟩
    have hdiff_bd : |F x - F y| ≤ 1 / 8 :=
      (abs_sub (F x) (F y)).trans (by linarith)
    have hlip := bipolarEdgeTentOdd_lipschitz r x y
    have hsq1 : (F x - F y) ^ 2 ≤ |x - y| / 2 := by
      calc (F x - F y) ^ 2 = |F x - F y| * |F x - F y| := (sq_abs _).symm.trans (sq _)
        _ ≤ (4 * |x - y|) * (1 / 8) :=
            mul_le_mul hlip hdiff_bd (abs_nonneg _) (by positivity)
        _ = |x - y| / 2 := by ring
    have hsq2 : (F x - F y) ^ 2 ≤ (1 / 8) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hdiff_bd 2
    have hprod : surplusKernel x y * (F x - F y) ^ 2 ≤
        (1 / (2 * |x - y|)) * (|x - y| / 2) + (1 / 4) * (1 / 8) ^ 2 := by
      calc surplusKernel x y * (F x - F y) ^ 2
          ≤ (1 / (2 * |x - y|) + 1 / 4) * (F x - F y) ^ 2 :=
            mul_le_mul_of_nonneg_right hk (sq_nonneg _)
        _ = (1 / (2 * |x - y|)) * (F x - F y) ^ 2 + (1 / 4) * (F x - F y) ^ 2 := add_mul _ _ _
        _ ≤ (1 / (2 * |x - y|)) * (|x - y| / 2) + (1 / 4) * (1 / 8) ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hsq1 (by positivity))
              (mul_le_mul_of_nonneg_left hsq2 (by norm_num))
    have hsimp : (1 / (2 * |x - y|)) * (|x - y| / 2) + (1 / 4) * (1 / 8) ^ 2 ≤ 1 := by
      have hd_ne : |x - y| ≠ 0 := hd0.ne'
      have : (1 / (2 * |x - y|)) * (|x - y| / 2) = 1 / 4 := by field_simp; ring
      rw [this]; norm_num
    exact hprod.trans hsimp

/-- **Global box energy bound for `bipolarEdgeTentOdd r`.** For `r ≥ 1`,
`stripBoxEnergy (bipolarEdgeTentOdd r) 0 r ≤ r`. -/
theorem stripBoxEnergy_bipolarEdgeTentOdd_le {r : ℝ} (hr : 1 ≤ r) :
    stripBoxEnergy (bipolarEdgeTentOdd r) 0 r ≤ r := by
  have hr0 : (0 : ℝ) ≤ r := by linarith
  set W : ℝ → ℝ → ℝ := fun x y =>
    (if r - 1 / 6 < x then (1 : ℝ) else 0) + (if r - 1 / 6 < y then (1 : ℝ) else 0)
  have hi1 : Measurable fun z : ℝ × ℝ => if r - 1 / 6 < z.1 then (1 : ℝ) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
      measurable_const
  have hi2 : Measurable fun z : ℝ × ℝ => if r - 1 / 6 < z.2 then (1 : ℝ) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
      measurable_const
  have hWm : Measurable (Function.uncurry W) := hi1.add hi2
  have hWb : ∀ x ∈ Icc 0 r, ∀ y ∈ Icc 0 r, |W x y| ≤ 2 := fun x _ y _ => by
    dsimp [W]; split_ifs <;> rw [abs_of_nonneg (by positivity)] <;> linarith
  have hgm := measurable_stripIntegrand (continuous_bipolarEdgeTentOdd r)
  have hgb : ∀ x ∈ Icc 0 r, ∀ y ∈ Icc 0 r,
      |stripIntegrand (bipolarEdgeTentOdd r) x y| ≤ 2 := fun x hx y hy => by
    obtain ⟨h0, h1⟩ := stripIntegrand_bipolarEdgeTentOdd_bounds hr hx hy
    rw [abs_of_nonneg h0]
    exact h1.trans ((le_abs_self _).trans (hWb x hx y hy))
  obtain ⟨hgi, hgo⟩ := intervalIntegrable_iterated hr0 hgm hgb
  obtain ⟨hWi, hWo⟩ := intervalIntegrable_iterated hr0 hWm hWb
  have hmono : stripBoxEnergy (bipolarEdgeTentOdd r) 0 r ≤
      ∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, W x y := by
    unfold stripBoxEnergy
    refine intervalIntegral.integral_mono_on hr0 hgo hWo fun x hx => ?_
    exact intervalIntegral.integral_mono_on hr0 (hgi x hx) (hWi x hx) fun y hy =>
      (stripIntegrand_bipolarEdgeTentOdd_bounds hr hx hy).2
  have hind : (∫ y in (0 : ℝ)..r, if r - 1 / 6 < y then (1 : ℝ) else 0) = 1 / 6 := by
    rw [integral_ite_lt (φ := fun _ => (1 : ℝ)) (by linarith) (by linarith),
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  have hindi : IntervalIntegrable (fun y => if r - 1 / 6 < y then (1 : ℝ) else 0) volume 0 r :=
    intervalIntegrable_of_abs_le (C := 1) hr0
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const) fun y _ => by split_ifs <;> simp
  have hinner : ∀ x, (∫ y in (0 : ℝ)..r, W x y) =
      (if r - 1 / 6 < x then (1 : ℝ) else 0) * r + 1 / 6 := fun x => by
    dsimp [W]
    rw [intervalIntegral.integral_add intervalIntegrable_const hindi,
      intervalIntegral.integral_const, hind, smul_eq_mul]
    ring
  have houter : (∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, W x y) = r / 3 := by
    simp_rw [hinner]
    rw [intervalIntegral.integral_add (hindi.mul_const r) intervalIntegrable_const,
      intervalIntegral.integral_mul_const, hind, intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-- The core sub-band of `thinBand r`: `2r − 7/48 ≤ log n ≤ 2r − 1/8`. -/
def thinBandCore (r : ℝ) : Finset ℕ :=
  (thinBand r).filter fun n => 2 * r - 7 / 48 ≤ Real.log n ∧ Real.log n ≤ 2 * r - 1 / 8

/-- `(ψ(X) − ψ(Y))/√X ≤ Σ_{thinBandCore r} Λ(n)/√n` with `X = e^{2r − 1/8}`, `Y = e^{2r − 7/48}`. -/
theorem psi_sub_div_le_sum_thinBandCore {r : ℝ} (hr : 1 ≤ r) :
    ((∑ n ∈ Finset.range (⌊Real.exp (2 * r - 1 / 8)⌋₊ + 1), ArithmeticFunction.vonMangoldt n) -
        ∑ n ∈ Finset.range (⌊Real.exp (2 * r - 7 / 48)⌋₊ + 1), ArithmeticFunction.vonMangoldt n) /
        Real.sqrt (Real.exp (2 * r - 1 / 8)) ≤ ∑ n ∈ thinBandCore r, vonMangoldtAtom n := by
  set X := Real.exp (2 * r - 1 / 8) with hX
  set Y := Real.exp (2 * r - 7 / 48) with hY
  have hYX : Y ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hY2 : 2 < Y := by
    have := Real.add_one_le_exp (2 * r - 7 / 48); rw [← hY] at this; linarith
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hfl : ⌊Y⌋₊ + 1 ≤ ⌊X⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_le_floor hYX) 1
  rw [← Finset.sum_Ico_eq_sub _ hfl, Finset.sum_div]
  have hmem : ∀ n ∈ Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1), Y < n ∧ (n : ℝ) ≤ X := fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
    refine ⟨(Nat.lt_floor_add_one Y).trans_le (by exact_mod_cast h1), ?_⟩
    exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp h2)).trans (Nat.floor_le hX0)
  have hsub : Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1) ⊆ thinBandCore r := fun n hn => by
    obtain ⟨h1, h2⟩ := hmem n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog_lo : 2 * r - 7 / 48 < Real.log n := by
      have := Real.log_lt_log (by positivity) h1
      rwa [hY, Real.log_exp] at this
    have hlog_hi : Real.log n ≤ 2 * r - 1 / 8 := by
      have := Real.log_le_log hn0 h2
      rwa [hX, Real.log_exp] at this
    simp only [thinBandCore, thinBand, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨?_, by linarith, by linarith⟩, hlog_lo.le, hlog_hi⟩
    have hX2 : X < Real.exp (2 * r) := Real.exp_lt_exp.mpr (by linarith)
    have : (n : ℝ) < ⌈Real.exp (2 * r)⌉₊ := lt_of_lt_of_le (h2.trans_lt hX2) (Nat.le_ceil _)
    exact_mod_cast this
  calc ∑ n ∈ Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt X
      ≤ ∑ n ∈ Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1), vonMangoldtAtom n := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨h1, h2⟩ := hmem n hn
        have hn2 : 2 ≤ n := by
          have : (2 : ℝ) < n := hY2.trans h1
          exact_mod_cast this.le
        unfold vonMangoldtAtom
        rw [if_pos hn2]
        exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
          (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt h2)
    _ ≤ ∑ n ∈ thinBandCore r, vonMangoldtAtom n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => vonMangoldtAtom_nonneg n

/-- The core sub-band `thinBandCore r` outgrows every linear budget `C * r`. -/
theorem eventually_lt_sum_thinBandCore (C : ℝ) :
    ∀ᶠ r in atTop, C * r < ∑ n ∈ thinBandCore r, vonMangoldtAtom n := by
  have hpnt := RHTower.Sieve.tendsto_sum_vonMangoldt_div
  have hlin : ∀ c : ℝ, Tendsto (fun r : ℝ => Real.exp (2 * r - c)) atTop atTop := fun c =>
    Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have h1 := (hpnt.comp (hlin (1 / 8))).eventually
    (lt_mem_nhds (show (999 / 1000 : ℝ) < 1 by norm_num))
  have h2 := (hpnt.comp (hlin (7 / 48))).eventually
    (gt_mem_nhds (show (1 : ℝ) < 1001 / 1000 by norm_num))
  have h3 := (Real.tendsto_exp_div_pow_atTop 1).eventually (eventually_ge_atTop (400 * (C + 1)))
  filter_upwards [h1, h2, h3, eventually_ge_atTop (1 : ℝ)] with r h1 h2 h3 hr
  simp only [Function.comp_apply] at h1 h2
  set X := Real.exp (2 * r - 1 / 8) with hX
  set Y := Real.exp (2 * r - 7 / 48) with hY
  set ψX := ∑ n ∈ Finset.range (⌊X⌋₊ + 1), ArithmeticFunction.vonMangoldt n with hψX
  set ψY := ∑ n ∈ Finset.range (⌊Y⌋₊ + 1), ArithmeticFunction.vonMangoldt n with hψY
  have hX0 : 0 < X := Real.exp_pos _
  have hY0 : 0 < Y := Real.exp_pos _
  rw [lt_div_iff₀ hX0] at h1
  rw [div_lt_iff₀ hY0] at h2
  have hYX : Y ≤ 48 / 49 * X := by
    have e : Y = X * Real.exp (-(1 / 48)) := by rw [hX, hY, ← Real.exp_add]; ring_nf
    have h48 : 49 / 48 ≤ Real.exp (1 / 48) := by linarith [Real.add_one_le_exp (1 / 48 : ℝ)]
    have h48' : Real.exp (-(1 / 48)) ≤ 48 / 49 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
    rw [e]; nlinarith
  have hgap : X / 60 ≤ ψX - ψY := by nlinarith
  have hsq : Real.sqrt X = Real.exp (r - 1 / 16) := by
    rw [hX, ← Real.exp_half]; ring_nf
  have hsq0 : 0 < Real.sqrt X := by rw [hsq]; exact Real.exp_pos _
  have hhalf : Real.exp r / 2 ≤ Real.sqrt X := by
    rw [hsq]
    have e : Real.exp (r - 1 / 16) = Real.exp r * Real.exp (-(1 / 16)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have := Real.add_one_le_exp (-(1 / 16) : ℝ)
    nlinarith [Real.exp_pos r]
  have hXs : X = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0.le).symm
  have hband := psi_sub_div_le_sum_thinBandCore hr
  rw [← hX, ← hY, ← hψX, ← hψY] at hband
  have hdiv : Real.sqrt X / 60 ≤ (ψX - ψY) / Real.sqrt X := by
    rw [le_div_iff₀ hsq0]; nlinarith
  rw [pow_one, le_div_iff₀ (by linarith)] at h3
  have hCr : C * r + 1 ≤ (C + 1) * r := by nlinarith
  nlinarith

/-- **Unconditional refutation of the signed thin-band inequality (`Open Problem 6(c)`).**
For all sufficiently large `r`, the bipolar edge-dipole test `F = bipolarEdgeTentOdd r` is odd,
continuous, `4`-Lipschitz, and supported in `[−r, r]`, has `F(x) F(x + log n) ≥ 0` pointwise on `ℝ`
for every `n ∈ thinBand r`, and satisfies
`stripBoxEnergy F 0 r < ∑_{n ∈ thinBand r} 2Λ(n)/√n ∫ F(x) F(x + log n) dx`.
Thus keeping the even strip parts does **not** salvage allocation of the thin band to one copy of
`stripBoxEnergy F 0 r`. -/
theorem exists_bipolarEdgeTent_signed_thinBand_sharing_fails :
    ∃ r₀ : ℝ, ∀ r ≥ r₀, ∃ F : ℝ → ℝ, Continuous F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ a b, |F a - F b| ≤ 4 * |a - b|) ∧ (∀ x, r < |x| → F x = 0) ∧
      (∀ n ∈ thinBand r, (∀ x, 0 ≤ F x * F (x + Real.log n)) ∧
        0 ≤ ∫ x, F x * F (x + Real.log n)) ∧
      stripBoxEnergy F 0 r <
        ∑ n ∈ thinBand r,
          2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) := by
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp
    ((eventually_lt_sum_thinBandCore 442368).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨r₀, fun r hr => ?_⟩
  obtain ⟨hmass, hr1⟩ := hr₀ r hr
  set F := bipolarEdgeTentOdd r
  refine ⟨F, continuous_bipolarEdgeTentOdd r, hasCompactSupport_bipolarEdgeTentOdd hr1,
    bipolarEdgeTentOdd_odd r, bipolarEdgeTentOdd_lipschitz r,
    fun x hx => bipolarEdgeTentOdd_eq_zero_of_lt hr1 hx, ?_, ?_⟩
  · intro n hn
    obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hn
    have hpt : ∀ x, 0 ≤ F x * F (x + Real.log n) :=
      bipolarEdgeTentOdd_mul_shift_nonneg hr1 hlo hhi
    exact ⟨hpt, integral_nonneg hpt⟩
  · have hbox := stripBoxEnergy_bipolarEdgeTentOdd_le hr1
    have hsub : thinBandCore r ⊆ thinBand r := Finset.filter_subset _ _
    have hnonneg : ∀ n ∈ thinBand r, n ∉ thinBandCore r →
        0 ≤ 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) := by
      intro n hn _
      obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hn
      have hint0 : 0 ≤ ∫ x, F x * F (x + Real.log n) :=
        integral_nonneg (bipolarEdgeTentOdd_mul_shift_nonneg hr1 hlo hhi)
      exact mul_nonneg (by norm_num) (mul_nonneg (vonMangoldtAtom_nonneg n) hint0)
    have hterm : ∀ n ∈ thinBandCore r,
        2 * vonMangoldtAtom n * (1 / 884736) ≤
          2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) := by
      intro n hn
      obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hn
      have hge := integral_bipolarEdgeTentOdd_mul_shift_ge hr1 hlo hhi
      have hΛ0 := vonMangoldtAtom_nonneg n
      nlinarith
    have hsum1 := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum1
    have hsum2 := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    have hlt : r < 2 * (∑ n ∈ thinBandCore r, vonMangoldtAtom n) * (1 / 884736) := by linarith
    exact lt_of_le_of_lt hbox (lt_of_lt_of_le hlt (hsum1.trans hsum2))

/-- **Exact global identity for the signed thin-band charge (`Open Problem 6(c)` positive survivor).**
For every odd test `F` supported in `[−r, r]`, the signed thin-band charge equals the total prime
shift series minus the prime shifts outside `thinBand r`. -/
theorem thinBand_signedCharge_eq_tsum_sub_complement {F : ℝ → ℝ} {r : ℝ}
    (hr : 1 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) :
    (∑ n ∈ thinBand r, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) =
      (∑' n : ℕ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) -
        ∑ n ∈ primeSide r \ thinBand r,
          2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) := by
  have hsub : thinBand r ⊆ primeSide r := by
    intro n hn
    obtain ⟨_, hlo, hhi⟩ := Finset.mem_filter.mp hn
    simp only [primeSide, Finset.mem_range]
    have hn0 : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp at hlo; linarith
      · exact_mod_cast hpos
    have hlt : (n : ℝ) < Real.exp (2 * r) := by
      rw [← Real.exp_log hn0]
      exact Real.exp_lt_exp.mpr (by linarith)
    have : n ≤ ⌊Real.exp (2 * r)⌋₊ := Nat.le_floor hlt.le
    omega
  rw [tsum_primeShift_eq_sum_primeSide hsupp, ← Finset.sum_sdiff hsub]
  ring

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
