import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCountMultiScale
import GaloisForLFunctions.RHTower.ZetaCriticalAsymptotics
import GaloisForLFunctions.RHTower.FiniteOfflineCauchyEnergy

/-!
# Prime-side Lorentzian `L²` bound for critical-spacing Cauchy pair sums

For strict-right zeros at transverse shifts `0 ≤ a_j, a_k ≤ h` (`h > 0`) and any Lorentzian width
`R₀ ≥ 2h`, the shifted Cauchy Gram kernel satisfies

`4 h · transverseCauchyKernel (h + a_j) (h + a_k) Δ ≤ 4 · R₀² / (R₀² + Δ²)`.

By the half-plane Poisson convolution semigroup `P_r ⋆ P_r = P_{2r}` at `r = R₀ / 2`, the finite
double sum of `R₀² / (R₀² + (γ_{q₁} − γ_{q₂})²)` equals `(4 / (π R₀)) ∫ G_r(t)² dt`, where
`G_r(t) = Σ_{q ∈ Z} r² / (r² + (t − γ_q)²)`.

Combining the prime-cascade multiscale local zero-count regularity
(`exists_volume_multiscale_localZeroCount_gt_le`) with a dyadic superlevel-set decomposition of the
continuous profile `G_r` on `[T/2, T] ∪ [T, 2T] ∪ [2T, 4T]` and direct inverse-square decay on
`ℝ \ [T/2, 4T]` yields the unconditional bound

`Σ_{q₁, q₂ ∈ dyadicZeroWindow T} R₀² / (R₀² + (γ_{q₁} − γ_{q₂})²) ≤ C (R₀ log T) T log T`

uniformly for all `0 < R₀ ≤ 1/32` with `R₀ log T ≥ κ₂`, without any logarithmic loss.

## Main results

* `shift_mul_transverseCauchyKernel_le_four_mul_lorentz`: pointwise domination of the `h`-shifted
  transverse Cauchy kernel by `4 · R₀² / (R₀² + Δ²)` whenever `0 ≤ a, b ≤ h` and `2h ≤ R₀`.
* `lorentz_pairSum_eq_integral_windowNarrowSum_sq`: exact `L²(ℝ)` identity for finite Lorentzian
  pair sums via Poisson semigroup convolution.
* `exists_integral_Icc_windowNarrowSum_sq_le`: multiscale superlevel-set `L²` bound on `[S, 2S]`.
* `exists_dyadicZeroWindow_lorentzPairSum_le`: unconditional `O((R₀ log T) T log T)` bound for the
  full Lorentzian pair sum over all `ξ`-zero copies in `[T, 2T]`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

/-! ## Shifted Cauchy kernel domination and Poisson `L²` identity -/

/-- For shallow displacements `0 ≤ a, b ≤ h` (`h > 0`) and any width `R₀ ≥ 2h`, multiplying the
`h`-shifted transverse Cauchy kernel by `4h` is bounded by `4 · R₀² / (R₀² + Δ²)`. -/
theorem shift_mul_transverseCauchyKernel_le_four_mul_lorentz
    {h a b R₀ Δ : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (ha : a ≤ h)
    (hb0 : 0 ≤ b) (hb : b ≤ h) (hR : 2 * h ≤ R₀) :
    4 * h * transverseCauchyKernel (h + a) (h + b) Δ ≤
      4 * (R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + Δ ^ (2 : ℕ))) := by
  have hRpos : 0 < R₀ := by linarith
  set s := h + a + (h + b)
  have hs_lo : 2 * h ≤ s := by dsimp [s]; linarith
  have hs_hi : s ≤ 4 * h := by dsimp [s]; linarith
  have hstep1 :
      4 * h * (s / (s ^ (2 : ℕ) + Δ ^ (2 : ℕ))) ≤
        4 * ((2 * h) ^ (2 : ℕ) / ((2 * h) ^ (2 : ℕ) + Δ ^ (2 : ℕ))) := by
    rw [mul_div_assoc, mul_div_assoc,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 16 * h ^ (3 : ℕ) * s ≤ 16 * h ^ (2 : ℕ) * s ^ (2 : ℕ) := by
      have hhs : 2 * h * s ≤ s ^ (2 : ℕ) := by nlinarith
      nlinarith [sq_nonneg h]
    have h2 : 4 * h * s * Δ ^ (2 : ℕ) ≤ 16 * h ^ (2 : ℕ) * Δ ^ (2 : ℕ) := by
      have hhs : 4 * h * s ≤ 16 * h ^ (2 : ℕ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hhs (sq_nonneg Δ)
    nlinarith
  have hstep2 :
      (2 * h) ^ (2 : ℕ) / ((2 * h) ^ (2 : ℕ) + Δ ^ (2 : ℕ)) ≤
        R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + Δ ^ (2 : ℕ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (2 * h) ^ (2 : ℕ) ≤ R₀ ^ (2 : ℕ) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg Δ)]
  unfold transverseCauchyKernel
  exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by norm_num))

/-- Finite narrow Lorentzian sum `Σ_{q ∈ Z} r² / (r² + (t − γ_q)²)` associated with a finite
family `Z` of ordinates `γ`. -/
def windowNarrowSum {ι : Type*} (Z : Finset ι) (γ : ι → ℝ) (r t : ℝ) : ℝ :=
  ∑ q ∈ Z, r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q) ^ (2 : ℕ))

theorem windowNarrowSum_nonneg {ι : Type*} (Z : Finset ι) (γ : ι → ℝ) (r t : ℝ) :
    0 ≤ windowNarrowSum Z γ r t :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem continuous_windowNarrowSum {ι : Type*} (Z : Finset ι) (γ : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (windowNarrowSum Z γ r) := by
  unfold windowNarrowSum
  refine continuous_finset_sum Z fun q _ => ?_
  refine Continuous.div continuous_const (by fun_prop) fun t => ?_
  positivity

theorem windowNarrowSum_mono_radius {ι : Type*} (Z : Finset ι) (γ : ι → ℝ)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂) (t : ℝ) :
    windowNarrowSum Z γ r₁ t ≤ windowNarrowSum Z γ r₂ t := by
  have hr₂ : 0 < r₂ := hr₁.trans_le hle
  refine Finset.sum_le_sum fun q _ => ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : r₁ ^ (2 : ℕ) ≤ r₂ ^ (2 : ℕ) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (t - γ q))]

private theorem narrowKernel_mul_eq_poisson {r : ℝ} (hr : 0 < r) (t x y : ℝ) :
    (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ))) =
      (Real.pi * r) ^ (2 : ℕ) * (halfPlanePoisson r (x - t) * halfPlanePoisson r (t - y)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hd1 : r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ) ≠ 0 := by positivity
  have hd2 : r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ) ≠ 0 := by positivity
  have hsq : (x - t) ^ (2 : ℕ) = (t - x) ^ (2 : ℕ) := by ring
  rw [halfPlanePoisson, halfPlanePoisson, hsq]
  field_simp
  ring

theorem integrable_windowNarrowSum_sq {ι : Type*} (Z : Finset ι) (γ : ι → ℝ)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => (windowNarrowSum Z γ r t) ^ (2 : ℕ)) := by
  have hrew : (fun t : ℝ => (windowNarrowSum Z γ r t) ^ (2 : ℕ)) =
      fun t : ℝ => ∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
        (Real.pi * r) ^ (2 : ℕ) *
          (halfPlanePoisson r (γ q₁ - t) * halfPlanePoisson r (t - γ q₂)) := by
    funext t
    rw [windowNarrowSum, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => ?_
    exact narrowKernel_mul_eq_poisson hr t (γ q₁) (γ q₂)
  rw [hrew]
  exact integrable_finset_sum Z fun q₁ _ =>
    integrable_finset_sum Z fun q₂ _ =>
      (integrable_poisson_shift_product hr hr (γ q₁) (γ q₂)).const_mul _

/-- **Exact Poisson semigroup `L²` identity.** For any finite family `Z` and positive width `R₀`,
the Lorentzian pair sum at width `R₀` equals `(4 / (π R₀))` times the global `L²` integral of
`windowNarrowSum Z γ (R₀ / 2)`. -/
theorem lorentz_pairSum_eq_integral_windowNarrowSum_sq {ι : Type*} (Z : Finset ι) (γ : ι → ℝ)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    (∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
        R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + (γ q₁ - γ q₂) ^ (2 : ℕ))) =
      4 / (Real.pi * R₀) * ∫ t : ℝ, (windowNarrowSum Z γ (R₀ / 2) t) ^ (2 : ℕ) := by
  set r := R₀ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hRne : R₀ ≠ 0 := hR₀.ne'
  have hpair : ∀ x y : ℝ,
      (∫ t : ℝ,
          (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
            (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ)))) =
        (Real.pi * R₀ / 4) * (R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + (x - y) ^ (2 : ℕ))) := by
    intro x y
    have hcongr : (fun t : ℝ =>
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
          (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ)))) =
        fun t : ℝ => (Real.pi * r) ^ (2 : ℕ) *
          (halfPlanePoisson r (x - t) * halfPlanePoisson r (t - y)) := by
      funext t; exact narrowKernel_mul_eq_poisson hr t x y
    rw [hcongr, MeasureTheory.integral_const_mul, integral_poisson_shift_product hr hr x y,
      halfPlanePoisson]
    have hrr : r + r = R₀ := by dsimp [r]; ring
    rw [hrr]
    have hden : R₀ ^ (2 : ℕ) + (x - y) ^ (2 : ℕ) ≠ 0 := by positivity
    dsimp [r]
    field_simp
    ring
  have hint_inner : ∀ q₁ q₂ : ι, Integrable (fun t : ℝ =>
      (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₁) ^ (2 : ℕ))) *
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₂) ^ (2 : ℕ)))) := by
    intro q₁ q₂
    have hcongr : (fun t : ℝ =>
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₁) ^ (2 : ℕ))) *
          (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₂) ^ (2 : ℕ)))) =
        fun t : ℝ => (Real.pi * r) ^ (2 : ℕ) *
          (halfPlanePoisson r (γ q₁ - t) * halfPlanePoisson r (t - γ q₂)) := by
      funext t; exact narrowKernel_mul_eq_poisson hr t (γ q₁) (γ q₂)
    rw [hcongr]
    exact (integrable_poisson_shift_product hr hr (γ q₁) (γ q₂)).const_mul _
  have hrew : (fun t : ℝ => (windowNarrowSum Z γ r t) ^ (2 : ℕ)) =
      fun t : ℝ => ∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₁) ^ (2 : ℕ))) *
          (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₂) ^ (2 : ℕ))) := by
    funext t
    rw [windowNarrowSum, sq, Finset.sum_mul_sum]
  rw [hrew, MeasureTheory.integral_finset_sum Z (fun q₁ _ =>
    integrable_finset_sum Z fun q₂ _ => hint_inner q₁ q₂)]
  have hsum_eq :
      (∑ q₁ ∈ Z, ∫ t : ℝ, ∑ q₂ ∈ Z,
          (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₁) ^ (2 : ℕ))) *
            (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₂) ^ (2 : ℕ)))) =
        (Real.pi * R₀ / 4) * ∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
          R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + (γ q₁ - γ q₂) ^ (2 : ℕ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q₁ _ => ?_
    rw [MeasureTheory.integral_finset_sum Z (fun q₂ _ => hint_inner q₁ q₂), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q₂ _ => hpair (γ q₁) (γ q₂)
  rw [hsum_eq]
  field_simp

/-! ## Pointwise multiscale bound on `[S, 2S]` -/

/-- Height `t ∈ [S, 2S]` violates multiscale regularity above `u` if some scale `v ∈ [u, 1/16]`
carries more than `20 v log S` zero copies within ordinate distance `v` of `t`. -/
def MultiScaleBad (S u t : ℝ) : Prop :=
  t ∈ Icc S (2 * S) ∧ ∃ v : ℝ, u ≤ v ∧ v ≤ 1 / 16 ∧ ∃ F : Finset XiZeroCopy,
    (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ v) ∧ 20 * (v * Real.log S) < F.card

private theorem sum_half_pow_succ_le_one (K : ℕ) :
    ∑ j ∈ Finset.range K, ((1 / 2 : ℝ) ^ (j + 1)) ≤ 1 := by
  have hfactor : ∑ j ∈ Finset.range K, ((1 / 2 : ℝ) ^ (j + 1)) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hfactor, geom_sum_eq (by norm_num)]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
  linarith

private theorem narrowMassTerm_le_far {r t : ℝ} {q : XiZeroCopy}
    (hf : ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16) :
    narrowMassTerm r t q ≤ 257 * r ^ (2 : ℕ) * lorentzMassTerm t q := by
  have hlt : (1 / 16 : ℝ) < |((q.1 : ℂ)).im - t| := lt_of_not_ge hf
  have hsq : (1 / 256 : ℝ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
    have habs : (t - (q.1 : ℂ).im) ^ (2 : ℕ) = |((q.1 : ℂ)).im - t| ^ (2 : ℕ) := by
      rw [sq_abs]; ring
    rw [habs]
    nlinarith
  unfold narrowMassTerm lorentzMassTerm
  rw [mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  have hr2 : 0 ≤ r ^ (2 : ℕ) := sq_nonneg r
  have hden : 1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ) ≤
      257 * (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) := by nlinarith
  exact mul_le_mul_of_nonneg_left hden hr2

/-- Deterministic ceiling for `windowNarrowSum` on `[S, 2S]` once `0 ≤ r ≤ 1`. -/
theorem windowNarrowSum_le_sixteen_log (Z : Finset XiZeroCopy)
    {S r t : ℝ} (hS : 1 ≤ S) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hlog : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S)
    (ht : t ∈ Icc S (2 * S)) :
    windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤ 16 * Real.log S := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hsum : windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤ lorentzMass t := by
    calc windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t
        = ∑ q ∈ Z, narrowMassTerm r t q := rfl
      _ ≤ ∑ q ∈ Z, lorentzMassTerm t q :=
          Finset.sum_le_sum fun q _ => narrowMassTerm_le_lorentzMassTerm hr0 hr1 t q
      _ ≤ lorentzMass t :=
          (summable_lorentzMassTerm t).sum_le_tsum Z fun q _ => by
            unfold lorentzMassTerm; positivity
  have hlor := lorentzMass_le_log t
  have habs : |t| + 4 ≤ 2 * S + 4 := by rw [abs_of_nonneg ht0]; linarith [ht.2]
  have hlogt : Real.log (|t| + 4) ≤ Real.log (2 * S + 4) :=
    Real.log_le_log (by positivity) habs
  linarith

/-- Outside `MultiScaleBad S u`, the narrow Lorentzian zero sum at width `r = R₀ / 2` (`R₀ ≤ u`) is
at most `105 u log S`. -/
theorem windowNarrowSum_le_of_not_multiScaleBad (Z : Finset XiZeroCopy)
    {S R₀ u t : ℝ} (hS : 2 ≤ S) (hR₀ : 0 < R₀) (hRu : R₀ ≤ u) (hu16 : u ≤ 1 / 16)
    (hlog : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S)
    (ht : t ∈ Icc S (2 * S)) (hgood : ¬ MultiScaleBad S u t) :
    windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t ≤ 105 * (u * Real.log S) := by
  classical
  set r := R₀ / 2
  set L := Real.log S
  have hu0 : 0 < u := hR₀.trans_le hRu
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hreg : ∀ v : ℝ, u ≤ v → v ≤ 1 / 16 → ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ v) → (F.card : ℝ) ≤ 20 * (v * L) := by
    intro v hvu hv16 F hF
    by_contra hgt
    exact hgood ⟨ht, v, hvu, hv16, F, hF, lt_of_not_ge hgt⟩
  set Znear := Z.filter (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ 1 / 16)
  set Zfar := Z.filter (fun q : XiZeroCopy => ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16)
  have hsplit : windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t =
      (∑ q ∈ Znear, narrowMassTerm r t q) + ∑ q ∈ Zfar, narrowMassTerm r t q :=
    (Finset.sum_filter_add_sum_filter_not Z
      (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ 1 / 16) (narrowMassTerm r t)).symm
  -- Far contribution `|γ_q - t| > 1/16`:
  have hfar : ∑ q ∈ Zfar, narrowMassTerm r t q ≤ 65 * (u * L) := by
    have h1 : ∑ q ∈ Zfar, narrowMassTerm r t q ≤
        257 * r ^ (2 : ℕ) * ∑ q ∈ Zfar, lorentzMassTerm t q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun q hq =>
        narrowMassTerm_le_far (Finset.mem_filter.mp hq).2
    have h2 : ∑ q ∈ Zfar, lorentzMassTerm t q ≤ lorentzMass t :=
      (summable_lorentzMassTerm t).sum_le_tsum Zfar fun q _ => by
        unfold lorentzMassTerm; positivity
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have habs : |t| + 4 ≤ 2 * S + 4 := by rw [abs_of_nonneg ht0]; linarith [ht.2]
    have hlogt : Real.log (|t| + 4) ≤ Real.log (2 * S + 4) :=
      Real.log_le_log (by positivity) habs
    have hlor : lorentzMass t ≤ 16 * L := by
      have := lorentzMass_le_log t; dsimp [L]; linarith
    have hr2 : r ^ (2 : ℕ) ≤ u / 64 := by
      dsimp [r]
      have hRu16 : R₀ * R₀ ≤ u * (1 / 16) :=
        mul_le_mul hRu (hRu.trans hu16) hR₀.le hu0.le
      linarith
    have hprod : 257 * r ^ (2 : ℕ) * lorentzMass t ≤ 257 * (u / 64) * (16 * L) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hr2 (by norm_num)) hlor
        (tsum_nonneg fun _ => by unfold lorentzMassTerm; positivity) (by positivity)
    linarith [h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)), hprod]
  -- Near contribution `|γ_q - t| ≤ 1/16` via dyadic shells:
  have hex : ∃ k : ℕ, 1 / 16 < (2 : ℝ) ^ k * u := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 16 / u) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rwa [div_lt_iff₀ hu0] at hk⟩
  set K := Nat.find hex
  have hKspec : 1 / 16 < (2 : ℝ) ^ K * u := Nat.find_spec hex
  have hKmin : ∀ j < K, (2 : ℝ) ^ j * u ≤ 1 / 16 :=
    fun j hj => not_lt.mp (Nat.find_min hex hj)
  set F₀ := Znear.filter (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ u)
  let shell : ℕ → Finset XiZeroCopy := fun j =>
    Znear.filter (fun q : XiZeroCopy =>
      (2 : ℝ) ^ j * u < |((q.1 : ℂ)).im - t| ∧
        |((q.1 : ℂ)).im - t| ≤ min ((2 : ℝ) ^ (j + 1) * u) (1 / 16))
  have hsub : Znear ⊆ F₀ ∪ (Finset.range K).biUnion shell := by
    intro q hq
    have hq16 : |((q.1 : ℂ)).im - t| ≤ 1 / 16 := (Finset.mem_filter.mp hq).2
    by_cases hqu : |((q.1 : ℂ)).im - t| ≤ u
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, hqu⟩)
    · apply Finset.mem_union_right
      have hgt : u < |((q.1 : ℂ)).im - t| := lt_of_not_ge hqu
      have hexd : ∃ m : ℕ, |((q.1 : ℂ)).im - t| ≤ (2 : ℝ) ^ m * u :=
        ⟨K, hq16.trans hKspec.le⟩
      set m := Nat.find hexd
      have hm_le : m ≤ K := Nat.find_min' hexd (hq16.trans hKspec.le)
      have hm_pos : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmp
        · exfalso
          have := Nat.find_spec hexd
          rw [show m = 0 from hm0, pow_zero, one_mul] at this
          linarith
        · exact hmp
      refine Finset.mem_biUnion.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), ?_⟩
      refine Finset.mem_filter.mpr ⟨hq, ?_, le_min ?_ hq16⟩
      · exact lt_of_not_ge (Nat.find_min hexd (by omega))
      · have hms : m - 1 + 1 = m := by omega
        rw [hms]
        exact Nat.find_spec hexd
  have hF₀ : ∑ q ∈ F₀, narrowMassTerm r t q ≤ 20 * (u * L) := by
    have hle1 : ∀ q ∈ F₀, narrowMassTerm r t q ≤ 1 := fun q _ =>
      (narrowMassTerm_le_lorentzMassTerm hr0.le (by dsimp [r]; linarith) t q).trans
        (by unfold lorentzMassTerm; exact div_le_one_of_le₀ (by positivity) (by positivity))
    calc ∑ q ∈ F₀, narrowMassTerm r t q ≤ ∑ _q ∈ F₀, (1 : ℝ) := Finset.sum_le_sum hle1
      _ = F₀.card := by simp
      _ ≤ 20 * (u * L) := hreg u le_rfl hu16 F₀ fun q hq => (Finset.mem_filter.mp hq).2
  have hshell : ∀ j ∈ Finset.range K,
      ∑ q ∈ shell j, narrowMassTerm r t q ≤ 20 * (u * L) * ((1 / 2 : ℝ) ^ (j + 1)) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    set vj := min ((2 : ℝ) ^ (j + 1) * u) (1 / 16)
    have hvj_lo : u ≤ vj := le_min
      (by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
        nlinarith)
      hu16
    have hvj_hi : vj ≤ 1 / 16 := min_le_right _ _
    have hcard : ((shell j).card : ℝ) ≤ 20 * ((2 : ℝ) ^ (j + 1) * u * L) := by
      have hc := hreg vj hvj_lo hvj_hi (shell j) fun q hq => (Finset.mem_filter.mp hq).2.2
      have hvle : vj ≤ (2 : ℝ) ^ (j + 1) * u := min_le_left _ _
      exact hc.trans (by nlinarith)
    have hterm : ∀ q ∈ shell j, narrowMassTerm r t q ≤ (1 / 4 : ℝ) ^ (j + 1) := by
      intro q hq
      have hlo : (2 : ℝ) ^ j * u < |((q.1 : ℂ)).im - t| := (Finset.mem_filter.mp hq).2.1
      have hlo_r : (2 : ℝ) ^ (j + 1) * r ≤ |((q.1 : ℂ)).im - t| := by
        have hpow : (2 : ℝ) ^ (j + 1) * r = (2 : ℝ) ^ j * R₀ := by
          dsimp [r]; rw [pow_succ]; ring
        rw [hpow]
        have : (2 : ℝ) ^ j * R₀ ≤ (2 : ℝ) ^ j * u :=
          mul_le_mul_of_nonneg_left hRu (by positivity)
        linarith
      have hsq : ((2 : ℝ) ^ (j + 1) * r) ^ (2 : ℕ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have habs : (t - (q.1 : ℂ).im) ^ (2 : ℕ) = |((q.1 : ℂ)).im - t| ^ (2 : ℕ) := by
          rw [sq_abs]; ring
        rw [habs]
        exact pow_le_pow_left₀ (by positivity) hlo_r 2
      unfold narrowMassTerm
      rw [div_le_iff₀ (by positivity)]
      have hinv : ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) = 1 := by
        rw [← pow_mul, show 2 * (j + 1) = (j + 1) * 2 by ring, pow_mul]
        norm_num
      have hmul : r ^ (2 : ℕ) ≤
          ((2 : ℝ) ^ (j + 1) * r) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) := by
        calc r ^ (2 : ℕ) = r ^ (2 : ℕ) * 1 := (mul_one _).symm
          _ = r ^ (2 : ℕ) * (((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1)) := by
              rw [hinv]
          _ = ((2 : ℝ) ^ (j + 1) * r) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) := by ring
      have hc0 : 0 ≤ (1 / 4 : ℝ) ^ (j + 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hsq hc0, mul_nonneg (sq_nonneg r) hc0]
    calc ∑ q ∈ shell j, narrowMassTerm r t q
        ≤ ∑ _q ∈ shell j, (1 / 4 : ℝ) ^ (j + 1) := Finset.sum_le_sum hterm
      _ = ((shell j).card : ℝ) * (1 / 4 : ℝ) ^ (j + 1) := by simp
      _ ≤ (20 * ((2 : ℝ) ^ (j + 1) * u * L)) * (1 / 4 : ℝ) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 20 * (u * L) * ((1 / 2 : ℝ) ^ (j + 1)) := by
          have hp : (2 : ℝ) ^ (j + 1) * (1 / 4 : ℝ) ^ (j + 1) = (1 / 2 : ℝ) ^ (j + 1) := by
            rw [← mul_pow]; norm_num
          calc (20 * ((2 : ℝ) ^ (j + 1) * u * L)) * (1 / 4 : ℝ) ^ (j + 1)
              = 20 * (u * L) * ((2 : ℝ) ^ (j + 1) * (1 / 4 : ℝ) ^ (j + 1)) := by ring
            _ = 20 * (u * L) * ((1 / 2 : ℝ) ^ (j + 1)) := by rw [hp]
  have hnear : ∑ q ∈ Znear, narrowMassTerm r t q ≤ 40 * (u * L) := by
    have hnn : ∀ q : XiZeroCopy, 0 ≤ narrowMassTerm r t q := narrowMassTerm_nonneg r t
    calc ∑ q ∈ Znear, narrowMassTerm r t q
        ≤ ∑ q ∈ F₀ ∪ (Finset.range K).biUnion shell, narrowMassTerm r t q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hnn q
      _ ≤ (∑ q ∈ F₀, narrowMassTerm r t q) +
            ∑ q ∈ (Finset.range K).biUnion shell, narrowMassTerm r t q :=
          Finset.sum_union_le _ _ hnn
      _ ≤ 20 * (u * L) + ∑ j ∈ Finset.range K, ∑ q ∈ shell j, narrowMassTerm r t q :=
          add_le_add hF₀ (Finset.sum_biUnion_le _ _ hnn)
      _ ≤ 20 * (u * L) + ∑ j ∈ Finset.range K, 20 * (u * L) * ((1 / 2 : ℝ) ^ (j + 1)) :=
          add_le_add le_rfl (Finset.sum_le_sum hshell)
      _ = 20 * (u * L) + 20 * (u * L) * ∑ j ∈ Finset.range K, ((1 / 2 : ℝ) ^ (j + 1)) := by
          rw [← Finset.mul_sum]
      _ ≤ 20 * (u * L) + 20 * (u * L) * 1 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_half_pow_succ_le_one K) (by positivity))
      _ = 40 * (u * L) := by ring
  linarith [hsplit]

/-! ## Dyadic superlevel-set `L²` bound on `[S, 2S]` -/

private theorem sum_four_pow_mul_exp_neg_two_pow_le {x : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    ∑ j ∈ Finset.range M, (4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * x)) ≤ 17 := by
  rcases M with _ | m
  · simp
  · rw [Finset.sum_range_succ']
    have h0 : (4 : ℝ) ^ (0 : ℕ) * Real.exp (-((2 : ℝ) ^ (0 : ℕ) * x)) ≤ 1 := by
      simp only [pow_zero, one_mul]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hterm : ∀ k : ℕ,
        (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x)) ≤
          8 * Real.exp (-((2 : ℝ) ^ k * 1)) := by
      intro k
      have hk_sq : ((2 : ℝ) ^ k) ^ (2 : ℕ) ≤ 2 * Real.exp ((2 : ℝ) ^ k) := by
        have h2 := Real.pow_div_factorial_le_exp ((2 : ℝ) ^ k) (by positivity) 2
        have hf : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
        rw [hf] at h2
        linarith
      have h4 : (4 : ℝ) ^ (k + 1) ≤ 8 * Real.exp ((2 : ℝ) ^ k) := by
        have heq : (4 : ℝ) ^ (k + 1) = 4 * ((2 : ℝ) ^ k) ^ (2 : ℕ) := by
          rw [pow_succ, show (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ (2 : ℕ) by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          ring
        rw [heq]; linarith
      have hexp : Real.exp (-((2 : ℝ) ^ (k + 1) * x)) ≤ Real.exp (-(2 * (2 : ℝ) ^ k)) := by
        apply Real.exp_le_exp.mpr
        rw [pow_succ]
        have hk0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        nlinarith
      calc (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x))
          ≤ (8 * Real.exp ((2 : ℝ) ^ k)) * Real.exp (-(2 * (2 : ℝ) ^ k)) :=
            mul_le_mul h4 hexp (Real.exp_pos _).le (by positivity)
        _ = 8 * (Real.exp ((2 : ℝ) ^ k) * Real.exp (-(2 * (2 : ℝ) ^ k))) := by ring
        _ = 8 * Real.exp (-((2 : ℝ) ^ k * 1)) := by
            rw [← Real.exp_add]; congr 2; ring
    have hsum : ∑ k ∈ Finset.range m,
        (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x)) ≤ 16 := by
      calc ∑ k ∈ Finset.range m, (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x))
          ≤ ∑ k ∈ Finset.range m, 8 * Real.exp (-((2 : ℝ) ^ k * 1)) :=
            Finset.sum_le_sum fun k _ => hterm k
        _ = 8 * ∑ k ∈ Finset.range m, Real.exp (-((2 : ℝ) ^ k * 1)) := by
            rw [← Finset.mul_sum]
        _ ≤ 8 * (2 * Real.exp (-1)) :=
            mul_le_mul_of_nonneg_left (sum_exp_neg_two_pow_mul_le le_rfl m) (by norm_num)
        _ ≤ 16 := by
            have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
            linarith
    linarith

private theorem integral_indicator_const_le_of_volume_le {B : Set ℝ} {c V : ℝ}
    (hBm : MeasurableSet B) (hc : 0 ≤ c) (hV : 0 ≤ V)
    (hvol : volume B ≤ ENNReal.ofReal V) :
    Integrable (B.indicator fun _ : ℝ => c) volume ∧
      (∫ t : ℝ, B.indicator (fun _ : ℝ => c) t) ≤ c * V := by
  have hfin : volume B < ⊤ := lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have hint : Integrable (B.indicator fun _ : ℝ => c) volume :=
    ((integrableOn_const hfin.ne : IntegrableOn (fun _ : ℝ => c) B)).integrable_indicator hBm
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_indicator_const c hBm, smul_eq_mul, MeasureTheory.measureReal_def]
  have hle : (volume B).toReal ≤ (ENNReal.ofReal V).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  rw [ENNReal.toReal_ofReal hV] at hle
  nlinarith

private theorem eventually_log_cube_mul_rpow_three_quarters_le (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ S : ℝ in atTop, K * Real.log S ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4) ≤ S := by
  have h1 := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 12) (by norm_num)).bound
    (show (0 : ℝ) < 1 / (K + 1) by positivity)
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with S hS hS1
  have hS0 : 0 < S := by linarith
  have hL0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
    abs_of_nonneg (Real.rpow_nonneg hS0.le _)] at hS
  have hcube : Real.log S ^ (3 : ℕ) ≤ (1 / (K + 1)) ^ (3 : ℕ) * S ^ ((1 : ℝ) / 4) := by
    calc Real.log S ^ (3 : ℕ)
        ≤ (1 / (K + 1) * S ^ ((1 : ℝ) / 12)) ^ (3 : ℕ) := pow_le_pow_left₀ hL0 hS 3
      _ = (1 / (K + 1)) ^ (3 : ℕ) * (S ^ ((1 : ℝ) / 12)) ^ (3 : ℕ) := by ring
      _ = (1 / (K + 1)) ^ (3 : ℕ) * S ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast (S ^ ((1 : ℝ) / 12)), ← Real.rpow_mul hS0.le]
          norm_num
  have hK1 : 1 ≤ K + 1 := by linarith
  have hinv_le : K * (1 / (K + 1)) ^ (3 : ℕ) ≤ 1 := by
    have hp : (1 / (K + 1)) ^ (3 : ℕ) ≤ 1 / (K + 1) := by
      have h0 : 0 ≤ 1 / (K + 1) := by positivity
      have hle1 : 1 / (K + 1) ≤ 1 := div_le_one_of_le₀ hK1 (by positivity)
      calc (1 / (K + 1)) ^ (3 : ℕ)
          = (1 / (K + 1)) * (1 / (K + 1)) * (1 / (K + 1)) := by ring
        _ ≤ 1 * 1 * (1 / (K + 1)) := by nlinarith
        _ = 1 / (K + 1) := by ring
    calc K * (1 / (K + 1)) ^ (3 : ℕ)
        ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hp hK
      _ ≤ (K + 1) * (1 / (K + 1)) := by nlinarith [ (by positivity : 0 ≤ 1 / (K + 1)) ]
      _ = 1 := by field_simp
  calc K * Real.log S ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4)
      ≤ K * ((1 / (K + 1)) ^ (3 : ℕ) * S ^ ((1 : ℝ) / 4)) * S ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube hK)
          (Real.rpow_nonneg hS0.le _)
    _ = (K * (1 / (K + 1)) ^ (3 : ℕ)) * (S ^ ((1 : ℝ) / 4) * S ^ ((3 : ℝ) / 4)) := by ring
    _ = (K * (1 / (K + 1)) ^ (3 : ℕ)) * S := by
        rw [← Real.rpow_add hS0, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num, Real.rpow_one]
    _ ≤ 1 * S := mul_le_mul_of_nonneg_right hinv_le hS0.le
    _ = S := one_mul S

/-- **Multiscale `L²` bound on `[S, 2S]`.** There exist `C₁ > 0` and `κ₂ ≥ 120000` such that
eventually for large `S`, for every `0 < R₀ ≤ 1/16` with `κ₂ ≤ R₀ log S` and every finite set `Z`
of `ξ`-zero copies, the integral of `(windowNarrowSum Z im (R₀ / 2))²` over `[S, 2S]` is at most
`C₁ (R₀ log S)² S`. -/
theorem exists_integral_Icc_windowNarrowSum_sq_le :
    ∃ C₁ κ₂ : ℝ, 0 < C₁ ∧ 120000 ≤ κ₂ ∧ ∀ᶠ S : ℝ in atTop,
      ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 / 16 → κ₂ ≤ R₀ * Real.log S →
      ∀ Z : Finset XiZeroCopy,
        (∫ t in Icc S (2 * S),
            (windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
          C₁ * (R₀ * Real.log S) ^ (2 : ℕ) * S := by
  classical
  obtain ⟨C, κ₂, hC, hκ₂, hev⟩ := exists_volume_multiscale_localZeroCount_gt_le
  set C₁ : ℝ := 105 ^ (2 : ℕ) + 4 * 105 ^ (2 : ℕ) * 12 * C * 17 + 3
  refine ⟨C₁, κ₂, by dsimp [C₁]; positivity, hκ₂, ?_⟩
  have hlog_const := Real.tendsto_log_atTop.eventually_ge_atTop
    (max (|xiLineTwoLogDerivConstant| + 2)
      (6 * (3840000 : ℝ) ^ (3 : ℕ) * (256 * 12 * C)))
  filter_upwards [hev, hlog_const, eventually_ge_atTop (4 : ℝ),
    eventually_log_cube_mul_rpow_three_quarters_le (105 ^ (2 : ℕ) * C) (by positivity),
    eventually_log_cube_mul_rpow_three_quarters_le (256 * C) (by positivity)]
    with S hvol hLbig hS4 hsub1 hsub2 R₀ hR₀ hR₀16 hκ Z
  set L := Real.log S
  set r := R₀ / 2
  have hS0 : 0 < S := by linarith
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hL1 : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog_lor : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * L := by
    have h2S4 : Real.log (2 * S + 4) ≤ Real.log (3 * S) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3S : Real.log (3 * S) = Real.log 3 + L :=
      Real.log_mul (by norm_num) hS0.ne'
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hCabs : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
    have hLm : |xiLineTwoLogDerivConstant| + 2 ≤ L := (le_max_left _ _).trans hLbig
    linarith
  -- Dyadic ladder `2^j R₀` up to `1/16`:
  have hex : ∃ k : ℕ, 1 / 16 < (2 : ℝ) ^ k * R₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 16 / R₀) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rwa [div_lt_iff₀ hR₀] at hk⟩
  set K₀ := Nat.find hex
  have hK₀spec : 1 / 16 < (2 : ℝ) ^ K₀ * R₀ := Nat.find_spec hex
  have hK₀min : ∀ j < K₀, (2 : ℝ) ^ j * R₀ ≤ 1 / 16 :=
    fun j hj => not_lt.mp (Nat.find_min hex hj)
  have hK₀pos : 1 ≤ K₀ := by
    rcases Nat.eq_zero_or_pos K₀ with h0 | hp
    · exfalso; rw [h0, pow_zero, one_mul] at hK₀spec; linarith
    · exact hp
  set M := K₀ - 1
  have hM_le16 : ∀ j ≤ M, (2 : ℝ) ^ j * R₀ ≤ 1 / 16 := fun j hj => hK₀min j (by omega)
  have hM_gt32 : 1 / 32 < (2 : ℝ) ^ M * R₀ := by
    have hKM : K₀ = M + 1 := by omega
    rw [hKM, pow_succ] at hK₀spec
    linarith
  -- Continuous superlevel sets `B j`:
  set G : ℝ → ℝ := windowNarrowSum Z (fun q => (q.1 : ℂ).im) r
  have hGcont : Continuous G := continuous_windowNarrowSum Z _ hr0
  let B : ℕ → Set ℝ := fun j =>
    Icc S (2 * S) ∩ {t : ℝ | 105 * ((2 : ℝ) ^ j * R₀ * L) < G t}
  have hBm : ∀ j : ℕ, MeasurableSet (B j) := fun j =>
    measurableSet_Icc.inter (isOpen_lt continuous_const hGcont).measurableSet
  have hBvol : ∀ j ≤ M,
      volume (B j) ≤ ENNReal.ofReal
        (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * L / 120000)) +
          C * S ^ ((3 : ℝ) / 4)) := by
    intro j hj
    set uj := (2 : ℝ) ^ j * R₀
    have huj0 : 0 < uj := by dsimp [uj]; positivity
    have huj16 : uj ≤ 1 / 16 := hM_le16 j hj
    have huj_ge : R₀ ≤ uj := by
      dsimp [uj]
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      nlinarith
    have hujκ : κ₂ ≤ uj * L := by
      dsimp [L] at *
      exact hκ.trans (mul_le_mul_of_nonneg_right huj_ge (by linarith))
    have hsubB : B j ⊆ {t : ℝ | MultiScaleBad S uj t} := by
      rintro t ⟨htIcc, htgt⟩
      by_contra hngood
      have hle := windowNarrowSum_le_of_not_multiScaleBad Z (by linarith) hR₀ huj_ge huj16
        hlog_lor htIcc hngood
      dsimp [G, r, uj, L] at htgt hle
      linarith
    exact (measure_mono hsubB).trans (hvol uj huj0 huj16 hujκ)
  -- Pointwise domination on `Icc S (2 * S)`:
  let maj : ℝ → ℝ := fun t =>
    (Icc S (2 * S)).indicator (fun _ => (105 * (R₀ * L)) ^ (2 : ℕ)) t +
      (∑ j ∈ Finset.range M,
        (B j).indicator (fun _ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ)) t) +
      (B M).indicator (fun _ => (16 * L) ^ (2 : ℕ)) t
  have hpt : ∀ t ∈ Icc S (2 * S), G t ^ (2 : ℕ) ≤ maj t := by
    intro t ht
    have hG0 : 0 ≤ G t := windowNarrowSum_nonneg Z _ r t
    have hbase : 0 ≤ (Icc S (2 * S)).indicator (fun _ => (105 * (R₀ * L)) ^ (2 : ℕ)) t :=
      Set.indicator_nonneg (fun _ _ => by positivity) t
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range M,
        (B j).indicator (fun _ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ)) t :=
      Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => by positivity) t
    have htop0 : 0 ≤ (B M).indicator (fun _ => (16 * L) ^ (2 : ℕ)) t :=
      Set.indicator_nonneg (fun _ _ => by positivity) t
    by_cases htM : t ∈ B M
    · have hceil : G t ≤ 16 * L :=
        windowNarrowSum_le_sixteen_log Z (by linarith) hr0.le hr1 hlog_lor ht
      have hsq : G t ^ (2 : ℕ) ≤ (16 * L) ^ (2 : ℕ) := pow_le_pow_left₀ hG0 hceil 2
      dsimp [maj]
      rw [Set.indicator_of_mem htM]
      linarith
    · by_cases ht0 : t ∈ B 0
      · have hexk : ∃ k : ℕ, t ∉ B k := ⟨M, htM⟩
        set k := Nat.find hexk
        have hk_le : k ≤ M := Nat.find_min' hexk htM
        have hk_pos : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hkp
          · exfalso; exact (Nat.find_spec hexk) (hk0 ▸ ht0)
          · exact hkp
        set j := k - 1
        have hjM : j ∈ Finset.range M := Finset.mem_range.mpr (by omega)
        have htj : t ∈ B j := by
          by_contra hnotj
          exact Nat.find_min hexk (by omega : j < k) hnotj
        have hnot_succ : t ∉ B (j + 1) := by
          have hjk : j + 1 = k := by omega
          rw [hjk]; exact Nat.find_spec hexk
        have hGj : G t ≤ 105 * ((2 : ℝ) ^ (j + 1) * R₀ * L) := by
          by_contra hgt
          exact hnot_succ ⟨ht, lt_of_not_ge hgt⟩
        have hsq : G t ^ (2 : ℕ) ≤ (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hG0 hGj 2
        have hsingle :
            (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ) ≤
              ∑ i ∈ Finset.range M,
                (B i).indicator (fun _ => (105 * ((2 : ℝ) ^ (i + 1) * R₀ * L)) ^ (2 : ℕ)) t := by
          calc (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ)
              = (B j).indicator (fun _ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ)) t :=
                (Set.indicator_of_mem htj _).symm
            _ ≤ _ := Finset.single_le_sum
                (fun i _ => Set.indicator_nonneg (fun _ _ => by positivity) t) hjM
        dsimp [maj]
        linarith
      · have hG_base : G t ≤ 105 * (R₀ * L) := by
          by_contra hgt
          apply ht0
          refine ⟨ht, ?_⟩
          simpa using lt_of_not_ge hgt
        have hsq : G t ^ (2 : ℕ) ≤ (105 * (R₀ * L)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hG0 hG_base 2
        dsimp [maj]
        rw [Set.indicator_of_mem ht]
        linarith
  -- Integrate `maj` over `ℝ` and bound each piece:
  have hIcc_vol : volume (Icc S (2 * S)) ≤ ENNReal.ofReal S := by
    rw [Real.volume_Icc, show 2 * S - S = S by ring]
  obtain ⟨hint_base, hval_base⟩ := integral_indicator_const_le_of_volume_le
    measurableSet_Icc (c := (105 * (R₀ * L)) ^ (2 : ℕ)) (by positivity) hS0.le hIcc_vol
  let Vj : ℕ → ℝ := fun j =>
    12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * L / 120000)) + C * S ^ ((3 : ℝ) / 4)
  have hVj0 : ∀ j : ℕ, 0 ≤ Vj j := fun j => by dsimp [Vj]; positivity
  let cj : ℕ → ℝ := fun j => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ)
  have hB_est : ∀ j ≤ M,
      Integrable ((B j).indicator fun _ : ℝ => cj j) volume ∧
        (∫ t : ℝ, (B j).indicator (fun _ : ℝ => cj j) t) ≤ cj j * Vj j :=
    fun j hj => integral_indicator_const_le_of_volume_le (hBm j) (by dsimp [cj]; positivity)
      (hVj0 j) (hBvol j hj)
  obtain ⟨hint_top, hval_top⟩ := integral_indicator_const_le_of_volume_le
    (hBm M) (c := (16 * L) ^ (2 : ℕ)) (by positivity) (hVj0 M) (hBvol M le_rfl)
  have hint_sum : Integrable (fun t : ℝ => ∑ j ∈ Finset.range M,
      (B j).indicator (fun _ => cj j) t) volume :=
    integrable_finset_sum (Finset.range M) fun j hj =>
      (hB_est j (Nat.le_of_lt (Finset.mem_range.mp hj))).1
  have hint_maj : Integrable maj volume := (hint_base.add hint_sum).add hint_top
  have hint_Icc_le :
      (∫ t in Icc S (2 * S), G t ^ (2 : ℕ)) ≤ ∫ t : ℝ, maj t := by
    calc ∫ t in Icc S (2 * S), G t ^ (2 : ℕ)
        ≤ ∫ t in Icc S (2 * S), maj t := by
          refine MeasureTheory.setIntegral_mono_on
            (integrable_windowNarrowSum_sq Z _ hr0).integrableOn hint_maj.integrableOn
            measurableSet_Icc hpt
      _ ≤ ∫ t : ℝ, maj t := by
          refine MeasureTheory.setIntegral_le_integral hint_maj
            (Filter.Eventually.of_forall fun t => ?_)
          dsimp [maj]
          exact add_nonneg
            (add_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) t)
              (Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => by positivity) t))
            (Set.indicator_nonneg (fun _ _ => by positivity) t)
  have hmaj_eval :
      (∫ t : ℝ, maj t) ≤
        (105 * (R₀ * L)) ^ (2 : ℕ) * S +
          (∑ j ∈ Finset.range M, cj j * Vj j) +
          (16 * L) ^ (2 : ℕ) * Vj M := by
    have hadd1 := MeasureTheory.integral_add (hint_base.add hint_sum) hint_top
    have hadd2 := MeasureTheory.integral_add hint_base hint_sum
    have hsum_int :
        (∫ t : ℝ, ∑ j ∈ Finset.range M, (B j).indicator (fun _ => cj j) t) =
          ∑ j ∈ Finset.range M, ∫ t : ℝ, (B j).indicator (fun _ => cj j) t :=
      MeasureTheory.integral_finset_sum (Finset.range M) fun j hj =>
        (hB_est j (Nat.le_of_lt (Finset.mem_range.mp hj))).1
    have hsum_le :
        (∑ j ∈ Finset.range M, ∫ t : ℝ, (B j).indicator (fun _ => cj j) t) ≤
          ∑ j ∈ Finset.range M, cj j * Vj j :=
      Finset.sum_le_sum fun j hj => (hB_est j (Nat.le_of_lt (Finset.mem_range.mp hj))).2
    dsimp [maj] at hadd1
    linarith [hadd1, hadd2, hval_base, hsum_int, hsum_le, hval_top]
  -- Bound the sum of intermediate shells `j < M`:
  have hx₀ : 1 ≤ R₀ * L / 120000 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hRL1 : 1 ≤ (R₀ * L) ^ (2 : ℕ) := by
    have : (1 : ℝ) ≤ R₀ * L := by linarith
    nlinarith
  have hM_le_L : (M : ℝ) ≤ L := by
    have hpowM : (2 : ℝ) ^ M * R₀ ≤ 1 / 16 := hM_le16 M le_rfl
    have hRL_ge : 1 ≤ R₀ * L := by linarith
    have h2M_le : (2 : ℝ) ^ M ≤ L := by
      have : (2 : ℝ) ^ M * (R₀ * L) ≤ (1 / 16) * L := by
        have := mul_le_mul_of_nonneg_right hpowM hL1
        linarith
      nlinarith [ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ M) ]
    have hM2 : (M : ℝ) ≤ (2 : ℝ) ^ M := by
      have := Nat.lt_two_pow_self (n := M)
      have hcast : (M : ℝ) < (2 : ℝ) ^ M := by exact_mod_cast this
      exact hcast.le
    exact hM2.trans h2M_le
  have hmid_bound :
      (∑ j ∈ Finset.range M, cj j * Vj j) ≤
        (4 * 105 ^ (2 : ℕ) * 12 * C * 17 + 1) * (R₀ * L) ^ (2 : ℕ) * S := by
    have hsplit_mid :
        (∑ j ∈ Finset.range M, cj j * Vj j) =
          (4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * L) ^ (2 : ℕ) * S) *
              (∑ j ∈ Finset.range M,
                (4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * (R₀ * L / 120000)))) +
            ∑ j ∈ Finset.range M, cj j * (C * S ^ ((3 : ℝ) / 4)) := by
      trans (∑ j ∈ Finset.range M,
          cj j * (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * L / 120000))) +
        ∑ j ∈ Finset.range M, cj j * (C * S ^ ((3 : ℝ) / 4)))
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by dsimp [Vj]; ring
      · congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp [cj]
        have h4 : ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) = 4 * (4 : ℝ) ^ j := by
          rw [pow_succ, mul_pow, show ((2 : ℝ) ^ j) ^ (2 : ℕ) = (4 : ℝ) ^ j by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          ring
        have hexp_eq : -((2 : ℝ) ^ j * R₀ * L / 120000) =
            -((2 : ℝ) ^ j * (R₀ * L / 120000)) := by ring
        rw [hexp_eq]
        calc (105 * ((2 : ℝ) ^ (j + 1) * R₀ * L)) ^ (2 : ℕ) *
              (12 * C * S * Real.exp (-((2 : ℝ) ^ j * (R₀ * L / 120000))))
            = 105 ^ (2 : ℕ) * ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) * (R₀ * L) ^ (2 : ℕ) *
                (12 * C * S * Real.exp (-((2 : ℝ) ^ j * (R₀ * L / 120000)))) := by ring
          _ = 4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * L) ^ (2 : ℕ) * S *
                ((4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * (R₀ * L / 120000)))) := by
                rw [h4]; ring
    have hexp_sum := sum_four_pow_mul_exp_neg_two_pow_le hx₀ M
    have hpow_part :
        (∑ j ∈ Finset.range M, cj j * (C * S ^ ((3 : ℝ) / 4))) ≤ S := by
      have hcj_le : ∀ j ∈ Finset.range M, cj j ≤ (105 * L) ^ (2 : ℕ) := by
        intro j hj
        have hjM : j < M := Finset.mem_range.mp hj
        have h2j : (2 : ℝ) ^ (j + 1) * R₀ ≤ 1 := by
          have : (2 : ℝ) ^ j * R₀ ≤ 1 / 16 := hM_le16 j (by omega)
          rw [pow_succ]; linarith
        dsimp [cj]
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        nlinarith
      calc ∑ j ∈ Finset.range M, cj j * (C * S ^ ((3 : ℝ) / 4))
          ≤ ∑ _j ∈ Finset.range M, (105 * L) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4)) :=
            Finset.sum_le_sum fun j hj =>
              mul_le_mul_of_nonneg_right (hcj_le j hj) (by positivity)
        _ = (M : ℝ) * ((105 * L) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4))) := by simp
        _ ≤ L * ((105 * L) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4))) :=
            mul_le_mul_of_nonneg_right hM_le_L (by positivity)
        _ = 105 ^ (2 : ℕ) * C * L ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4) := by ring
        _ ≤ S := hsub1
    have hS_le_RL : S ≤ (R₀ * L) ^ (2 : ℕ) * S := by nlinarith
    rw [hsplit_mid]
    have hmain_part :
        (4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * L) ^ (2 : ℕ) * S) *
            (∑ j ∈ Finset.range M,
              (4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * (R₀ * L / 120000)))) ≤
          (4 * 105 ^ (2 : ℕ) * 12 * C * 17) * (R₀ * L) ^ (2 : ℕ) * S := by
      have hc0 : 0 ≤ 4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * L) ^ (2 : ℕ) * S := by positivity
      have := mul_le_mul_of_nonneg_left hexp_sum hc0
      linarith
    linarith
  -- Bound the top level `B M`:
  have htop_bound : (16 * L) ^ (2 : ℕ) * Vj M ≤ 2 * (R₀ * L) ^ (2 : ℕ) * S := by
    have hexp_M : Real.exp (-((2 : ℝ) ^ M * R₀ * L / 120000)) ≤
        Real.exp (-(L / 3840000)) := by
      apply Real.exp_le_exp.mpr
      have := mul_lt_mul_of_pos_right hM_gt32 (show 0 < L by linarith)
      linarith
    have hL2_exp : 256 * 12 * C * L ^ (2 : ℕ) * Real.exp (-(L / 3840000)) ≤ 1 := by
      have h3 := Real.pow_div_factorial_le_exp (L / 3840000) (by positivity) 3
      have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [hf] at h3
      have hLge : 6 * (3840000 : ℝ) ^ (3 : ℕ) * (256 * 12 * C) ≤ L :=
        (le_max_right _ _).trans hLbig
      have hcube : 256 * 12 * C * L ^ (2 : ℕ) ≤ Real.exp (L / 3840000) := by
        have hstep : 256 * 12 * C * L ^ (2 : ℕ) ≤ (L / 3840000) ^ (3 : ℕ) / 6 := by
          have heq : (L / 3840000) ^ (3 : ℕ) / 6 =
              L ^ (2 : ℕ) * (L / (6 * (3840000 : ℝ) ^ (3 : ℕ))) := by ring
          rw [heq]
          have hdiv : 256 * 12 * C ≤ L / (6 * (3840000 : ℝ) ^ (3 : ℕ)) := by
            rw [le_div_iff₀ (by norm_num)]; linarith
          have := mul_le_mul_of_nonneg_left hdiv (sq_nonneg L)
          linarith
        exact hstep.trans h3
      have := mul_le_mul_of_nonneg_right hcube (Real.exp_pos (-(L / 3840000))).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    have hp1 : (16 * L) ^ (2 : ℕ) * (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * L / 120000))) ≤
        S := by
      calc (16 * L) ^ (2 : ℕ) * (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * L / 120000)))
          ≤ (16 * L) ^ (2 : ℕ) * (12 * C * S * Real.exp (-(L / 3840000))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp_M (by positivity)) (by positivity)
        _ = (256 * 12 * C * L ^ (2 : ℕ) * Real.exp (-(L / 3840000))) * S := by ring
        _ ≤ 1 * S := mul_le_mul_of_nonneg_right hL2_exp hS0.le
        _ = S := one_mul S
    have hp2 : (16 * L) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4)) ≤ S := by
      calc (16 * L) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4))
          = 256 * C * L ^ (2 : ℕ) * S ^ ((3 : ℝ) / 4) := by ring
        _ ≤ 256 * C * L ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4) := by
            have hL23 : L ^ (2 : ℕ) ≤ L ^ (3 : ℕ) := by nlinarith
            nlinarith [ (by positivity : 0 ≤ 256 * C * S ^ ((3 : ℝ) / 4)) ]
        _ ≤ S := hsub2
    have hVj_expand : (16 * L) ^ (2 : ℕ) * Vj M =
        (16 * L) ^ (2 : ℕ) * (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * L / 120000))) +
          (16 * L) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4)) := by dsimp [Vj]; ring
    have hS_le_RL : S ≤ (R₀ * L) ^ (2 : ℕ) * S := by nlinarith
    linarith
  -- Assemble total `[S, 2S]` integral:
  have hbase_eq : (105 * (R₀ * L)) ^ (2 : ℕ) * S = 105 ^ (2 : ℕ) * (R₀ * L) ^ (2 : ℕ) * S := by
    ring
  have hC₁_expand : C₁ * (R₀ * L) ^ (2 : ℕ) * S =
      105 ^ (2 : ℕ) * (R₀ * L) ^ (2 : ℕ) * S +
        (4 * 105 ^ (2 : ℕ) * 12 * C * 17 + 1) * (R₀ * L) ^ (2 : ℕ) * S +
        2 * (R₀ * L) ^ (2 : ℕ) * S := by dsimp [C₁]; ring
  linarith [hint_Icc_le, hmaj_eval, hmid_bound, htop_bound, hbase_eq, hC₁_expand]

/-! ## Global `L²` bound and Lorentzian pair sum on `dyadicZeroWindow T` -/

/-- All multiplicity copies of `ξ`-zeros with ordinate in `[T, 2T]`. -/
def dyadicZeroWindow (T : ℝ) : Finset XiZeroCopy :=
  (zeroWindow (2 * T)).filter (fun q => T ≤ (q.1 : ℂ).im)

theorem mem_dyadicZeroWindow {T : ℝ} (hT : 0 < T) {q : XiZeroCopy} :
    q ∈ dyadicZeroWindow T ↔ T ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T := by
  rw [dyadicZeroWindow, Finset.mem_filter, mem_zeroWindow]
  constructor
  · rintro ⟨⟨_, hhi⟩, hlo⟩; exact ⟨hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩; exact ⟨⟨by linarith, hhi⟩, hlo⟩

theorem card_dyadicZeroWindow_le (T : ℝ) :
    (dyadicZeroWindow T).card ≤ (zeroWindow (2 * T)).card :=
  Finset.card_filter_le _ _

private theorem setIntegral_Iic_windowNarrowSum_sq_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    (∫ t in Iic (T / 2),
        (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
      8 * Real.pi * r ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) := by
  set Z := dyadicZeroWindow T
  set c := T / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hpt : ∀ t ∈ Iic c,
      (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ) ≤
        ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
          ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) := by
    intro t ht
    have htle : t ≤ c := ht
    have hterm1 : ∀ q ∈ Z,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) / c ^ (2 : ℕ) := by
      intro q hq
      have hqlo : T ≤ (q.1 : ℂ).im := ((mem_dyadicZeroWindow hT).mp hq).1
      have hdist : c ≤ (q.1 : ℂ).im - t := by dsimp [c] at *; linarith
      have hsq : c ^ (2 : ℕ) ≤ r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have : c ^ (2 : ℕ) ≤ ((q.1 : ℂ).im - t) ^ (2 : ℕ) := pow_le_pow_left₀ hc.le hdist 2
        nlinarith [sq_nonneg r]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hterm2 : ∀ q ∈ Z,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) := by
      intro q hq
      have hqlo : T ≤ (q.1 : ℂ).im := ((mem_dyadicZeroWindow hT).mp hq).1
      have ha : c ≤ (q.1 : ℂ).im - c := by dsimp [c]; linarith
      have hb : 0 ≤ c - t := by linarith
      have hsq : c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ) ≤
          r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have hdecomp : t - (q.1 : ℂ).im = -(((q.1 : ℂ).im - c) + (c - t)) := by ring
        rw [hdecomp]
        nlinarith [sq_nonneg r, mul_nonneg (hc.le.trans ha) hb]
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hG0 : 0 ≤ windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t :=
      windowNarrowSum_nonneg Z _ r t
    have hG1 : windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤
        (Z.card : ℝ) * (r ^ (2 : ℕ) / c ^ (2 : ℕ)) := by
      calc windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ Z, r ^ (2 : ℕ) / c ^ (2 : ℕ) := Finset.sum_le_sum hterm1
        _ = (Z.card : ℝ) * (r ^ (2 : ℕ) / c ^ (2 : ℕ)) := by simp
    have hG2 : windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤
        (Z.card : ℝ) * (r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹)) := by
      calc windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ Z, r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) :=
            Finset.sum_le_sum hterm2
        _ = (Z.card : ℝ) * (r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹)) := by simp
    calc (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
        = windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t *
            windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t := sq _
      _ ≤ ((Z.card : ℝ) * (r ^ (2 : ℕ) / c ^ (2 : ℕ))) *
            ((Z.card : ℝ) * (r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹))) :=
          mul_le_mul hG1 hG2 hG0 (by positivity)
      _ = ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
            ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) := by ring
  have hint_rhs : Integrable (fun t : ℝ =>
      ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
        ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹)) :=
    (integrable_inv_shifted_sq_add_sq hc c).const_mul _
  calc ∫ t in Iic c, (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
      ≤ ∫ t in Iic c,
          ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
            ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_mono_on
          (integrable_windowNarrowSum_sq Z _ hr).integrableOn hint_rhs.integrableOn
          measurableSet_Iic hpt
    _ ≤ ∫ t : ℝ,
          ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
            ((c ^ (2 : ℕ) + (t - c) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_le_integral hint_rhs
          (Filter.Eventually.of_forall fun t => by positivity)
    _ = ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) * (Real.pi / c) := by
        rw [MeasureTheory.integral_const_mul, integral_inv_shifted_sq_add_sq hc c]
    _ = 8 * Real.pi * r ^ (4 : ℕ) * ((Z.card : ℝ) ^ (2 : ℕ)) / T ^ (3 : ℕ) := by
        dsimp [c]; field_simp; ring

private theorem setIntegral_Ici_windowNarrowSum_sq_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    (∫ t in Ici (4 * T),
        (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
      8 * Real.pi * r ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) := by
  set Z := dyadicZeroWindow T
  set c := T / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hpt : ∀ t ∈ Ici (4 * T),
      (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ) ≤
        ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
          ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) := by
    intro t ht
    have htge : 4 * T ≤ t := ht
    have hterm1 : ∀ q ∈ Z,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) / c ^ (2 : ℕ) := by
      intro q hq
      have hqhi : (q.1 : ℂ).im ≤ 2 * T := ((mem_dyadicZeroWindow hT).mp hq).2
      have hdist : c ≤ t - (q.1 : ℂ).im := by dsimp [c] at *; linarith
      have hsq : c ^ (2 : ℕ) ≤ r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have : c ^ (2 : ℕ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := pow_le_pow_left₀ hc.le hdist 2
        nlinarith [sq_nonneg r]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hterm2 : ∀ q ∈ Z,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) := by
      intro q hq
      have hqhi : (q.1 : ℂ).im ≤ 2 * T := ((mem_dyadicZeroWindow hT).mp hq).2
      have ha : c ≤ 4 * T - (q.1 : ℂ).im := by dsimp [c]; linarith
      have hb : 0 ≤ t - 4 * T := by linarith
      have hsq : c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ) ≤
          r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have hdecomp : t - (q.1 : ℂ).im = (4 * T - (q.1 : ℂ).im) + (t - 4 * T) := by ring
        rw [hdecomp]
        nlinarith [sq_nonneg r, mul_nonneg (hc.le.trans ha) hb]
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hG0 : 0 ≤ windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t :=
      windowNarrowSum_nonneg Z _ r t
    have hG1 : windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤
        (Z.card : ℝ) * (r ^ (2 : ℕ) / c ^ (2 : ℕ)) := by
      calc windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ Z, r ^ (2 : ℕ) / c ^ (2 : ℕ) := Finset.sum_le_sum hterm1
        _ = (Z.card : ℝ) * (r ^ (2 : ℕ) / c ^ (2 : ℕ)) := by simp
    have hG2 : windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤
        (Z.card : ℝ) * (r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹)) := by
      calc windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ Z, r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) :=
            Finset.sum_le_sum hterm2
        _ = (Z.card : ℝ) *
              (r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹)) := by simp
    calc (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
        = windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t *
            windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t := sq _
      _ ≤ ((Z.card : ℝ) * (r ^ (2 : ℕ) / c ^ (2 : ℕ))) *
            ((Z.card : ℝ) *
              (r ^ (2 : ℕ) * ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹))) :=
          mul_le_mul hG1 hG2 hG0 (by positivity)
      _ = ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
            ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) := by ring
  have hint_rhs : Integrable (fun t : ℝ =>
      ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
        ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹)) :=
    (integrable_inv_shifted_sq_add_sq hc (4 * T)).const_mul _
  calc ∫ t in Ici (4 * T), (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
      ≤ ∫ t in Ici (4 * T),
          ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
            ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_mono_on
          (integrable_windowNarrowSum_sq Z _ hr).integrableOn hint_rhs.integrableOn
          measurableSet_Ici hpt
    _ ≤ ∫ t : ℝ,
          ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) *
            ((c ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_le_integral hint_rhs
          (Filter.Eventually.of_forall fun t => by positivity)
    _ = ((Z.card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / c ^ (2 : ℕ)) * (Real.pi / c) := by
        rw [MeasureTheory.integral_const_mul, integral_inv_shifted_sq_add_sq hc (4 * T)]
    _ = 8 * Real.pi * r ^ (4 : ℕ) * ((Z.card : ℝ) ^ (2 : ℕ)) / T ^ (3 : ℕ) := by
        dsimp [c]; field_simp; ring

private theorem integral_le_five_pieces {f : ℝ → ℝ} (hf : Integrable f)
    (hnn : ∀ t : ℝ, 0 ≤ f t) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, f t) ≤
      (∫ t in Iic (T / 2), f t) +
        (∫ t in Icc (T / 2) T, f t) +
        (∫ t in Icc T (2 * T), f t) +
        (∫ t in Icc (2 * T) (4 * T), f t) +
        (∫ t in Ici (4 * T), f t) := by
  have hi1 : Integrable ((Iic (T / 2)).indicator f) := hf.indicator measurableSet_Iic
  have hi2 : Integrable ((Icc (T / 2) T).indicator f) := hf.indicator measurableSet_Icc
  have hi3 : Integrable ((Icc T (2 * T)).indicator f) := hf.indicator measurableSet_Icc
  have hi4 : Integrable ((Icc (2 * T) (4 * T)).indicator f) := hf.indicator measurableSet_Icc
  have hi5 : Integrable ((Ici (4 * T)).indicator f) := hf.indicator measurableSet_Ici
  have hpt : ∀ t : ℝ, f t ≤
      (Iic (T / 2)).indicator f t +
        (Icc (T / 2) T).indicator f t +
        (Icc T (2 * T)).indicator f t +
        (Icc (2 * T) (4 * T)).indicator f t +
        (Ici (4 * T)).indicator f t := by
    intro t
    have p1 := Set.indicator_nonneg (s := Iic (T / 2)) (fun x _ => hnn x) t
    have p2 := Set.indicator_nonneg (s := Icc (T / 2) T) (fun x _ => hnn x) t
    have p3 := Set.indicator_nonneg (s := Icc T (2 * T)) (fun x _ => hnn x) t
    have p4 := Set.indicator_nonneg (s := Icc (2 * T) (4 * T)) (fun x _ => hnn x) t
    have p5 := Set.indicator_nonneg (s := Ici (4 * T)) (fun x _ => hnn x) t
    by_cases h1 : t ≤ T / 2
    · rw [Set.indicator_of_mem (show t ∈ Iic (T / 2) from h1)]; linarith
    · by_cases h2 : t ≤ T
      · rw [Set.indicator_of_mem (show t ∈ Icc (T / 2) T from ⟨by linarith, h2⟩)]; linarith
      · by_cases h3 : t ≤ 2 * T
        · rw [Set.indicator_of_mem (show t ∈ Icc T (2 * T) from ⟨by linarith, h3⟩)]; linarith
        · by_cases h4 : t ≤ 4 * T
          · rw [Set.indicator_of_mem (show t ∈ Icc (2 * T) (4 * T) from ⟨by linarith, h4⟩)]
            linarith
          · rw [Set.indicator_of_mem (show t ∈ Ici (4 * T) by linarith)]; linarith
  have hmono := MeasureTheory.integral_mono hf ((((hi1.add hi2).add hi3).add hi4).add hi5) hpt
  rw [MeasureTheory.integral_add (((hi1.add hi2).add hi3).add hi4) hi5,
    MeasureTheory.integral_add ((hi1.add hi2).add hi3) hi4,
    MeasureTheory.integral_add (hi1.add hi2) hi3,
    MeasureTheory.integral_add hi1 hi2,
    MeasureTheory.integral_indicator measurableSet_Iic,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ici] at hmono
  exact hmono

/-- **Unconditional Lorentzian pair-sum bound on `dyadicZeroWindow T`.** There exist `C_pair > 0`
and `κ₂ ≥ 120000` such that eventually for large `T`, for every `0 < R₀ ≤ 1/32` with
`κ₂ ≤ R₀ log T`,

`Σ_{q₁, q₂ ∈ dyadicZeroWindow T} R₀² / (R₀² + (γ_{q₁} − γ_{q₂})²) ≤ C_pair (R₀ log T) T log T`. -/
theorem exists_dyadicZeroWindow_lorentzPairSum_le :
    ∃ C_pair κ₂ : ℝ, 0 < C_pair ∧ 120000 ≤ κ₂ ∧ ∀ᶠ T : ℝ in atTop,
      ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 / 32 → κ₂ ≤ R₀ * Real.log T →
        (∑ q₁ ∈ dyadicZeroWindow T, ∑ q₂ ∈ dyadicZeroWindow T,
            R₀ ^ (2 : ℕ) /
              (R₀ ^ (2 : ℕ) + ((q₁.1 : ℂ).im - (q₂.1 : ℂ).im) ^ (2 : ℕ))) ≤
          C_pair * (R₀ * Real.log T) * (T * Real.log T) := by
  obtain ⟨C₁, κ₂, hC₁, hκ₂, hev_Icc⟩ := exists_integral_Icc_windowNarrowSum_sq_le
  set C_pair : ℝ := 4 * (11 * C₁ + 2) / Real.pi
  refine ⟨C_pair, κ₂, by dsimp [C_pair]; positivity, hκ₂, ?_⟩
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp hev_Icc
  have hcard_2T : ∀ᶠ T : ℝ in atTop,
      ((zeroWindow (2 * T)).card : ℝ) ≤ (2 * T) * Real.log (2 * T) / 5 :=
    (tendsto_const_nhds.mul tendsto_id).eventually eventually_card_zeroWindow_le
  have htail_small : ∀ᶠ T : ℝ in atTop,
      8 * Real.pi * Real.log T ^ (2 : ℕ) ≤ T ^ (2 : ℕ) := by
    have h1 := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).bound
      (show (0 : ℝ) < 1 / (8 * Real.pi + 1) by positivity)
    filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with T hT hT1
    have hT0 : 0 < T := by linarith
    have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
      abs_of_nonneg (by positivity), Real.rpow_one] at hT
    have hsq : Real.log T ^ (2 : ℕ) ≤ (1 / (8 * Real.pi + 1)) ^ (2 : ℕ) * T ^ (2 : ℕ) := by
      calc Real.log T ^ (2 : ℕ)
          ≤ (1 / (8 * Real.pi + 1) * T) ^ (2 : ℕ) := pow_le_pow_left₀ hL0 hT 2
        _ = (1 / (8 * Real.pi + 1)) ^ (2 : ℕ) * T ^ (2 : ℕ) := by ring
    have hc_le : 8 * Real.pi * (1 / (8 * Real.pi + 1)) ^ (2 : ℕ) ≤ 1 := by
      have hp : 1 ≤ 8 * Real.pi + 1 := by positivity
      have h0 : 0 ≤ 1 / (8 * Real.pi + 1) := by positivity
      have hle1 : 1 / (8 * Real.pi + 1) ≤ 1 := div_le_one_of_le₀ hp (by positivity)
      calc 8 * Real.pi * (1 / (8 * Real.pi + 1)) ^ (2 : ℕ)
          = 8 * Real.pi * (1 / (8 * Real.pi + 1)) * (1 / (8 * Real.pi + 1)) := by ring
        _ ≤ 8 * Real.pi * (1 / (8 * Real.pi + 1)) * 1 :=
            mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ ≤ (8 * Real.pi + 1) * (1 / (8 * Real.pi + 1)) := by nlinarith
        _ = 1 := by field_simp
    calc 8 * Real.pi * Real.log T ^ (2 : ℕ)
        ≤ 8 * Real.pi * ((1 / (8 * Real.pi + 1)) ^ (2 : ℕ) * T ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (8 * Real.pi * (1 / (8 * Real.pi + 1)) ^ (2 : ℕ)) * T ^ (2 : ℕ) := by ring
      _ ≤ 1 * T ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hc_le (sq_nonneg T)
      _ = T ^ (2 : ℕ) := one_mul _
  filter_upwards [eventually_ge_atTop (max (2 * S₀) 4), hcard_2T, htail_small]
    with T hTbig hcard htail R₀ hR₀ hR₀32 hκ
  have hT4 : 4 ≤ T := (le_max_right _ _).trans hTbig
  have hT0 : 0 < T := by linarith
  have hS_half : S₀ ≤ T / 2 := by
    have := (le_max_left _ _).trans hTbig; linarith
  have hS_T : S₀ ≤ T := by linarith
  have hS_2T : S₀ ≤ 2 * T := by linarith
  set Z := dyadicZeroWindow T
  set L := Real.log T
  set r := R₀ / 2
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  have hL1 : 1 ≤ L := by
    dsimp [L]
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hRL1 : 1 ≤ (R₀ * L) ^ (2 : ℕ) := by
    have : (1 : ℝ) ≤ R₀ * L := by linarith
    nlinarith
  -- Piece 1: `[T/2, T]` at radius `2 * R₀`:
  have hlog_half_ge : L ≤ 2 * Real.log (T / 2) := by
    have hsq_ge : T ≤ (T / 2) ^ (2 : ℕ) := by nlinarith
    have h1 := Real.log_le_log hT0 hsq_ge
    rw [Real.log_pow] at h1
    dsimp [L]
    simpa using h1
  have hlog_half_le : Real.log (T / 2) ≤ L :=
    Real.log_le_log (by positivity) (by linarith)
  have hκ_half : κ₂ ≤ (2 * R₀) * Real.log (T / 2) := by
    have := mul_le_mul_of_nonneg_left hlog_half_ge hR₀.le
    linarith
  have hIcc1 :
      (∫ t in Icc (T / 2) T,
          (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
        2 * C₁ * (R₀ * L) ^ (2 : ℕ) * T := by
    have hmono :
        (∫ t in Icc (T / 2) T,
            (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
          ∫ t in Icc (T / 2) (2 * (T / 2)),
            (windowNarrowSum Z (fun q => (q.1 : ℂ).im) ((2 * R₀) / 2) t) ^ (2 : ℕ) := by
      rw [show 2 * (T / 2) = T by ring]
      refine MeasureTheory.setIntegral_mono_on
        (integrable_windowNarrowSum_sq Z _ hr0).integrableOn
        (integrable_windowNarrowSum_sq Z _ (by positivity)).integrableOn
        measurableSet_Icc fun t _ => ?_
      exact pow_le_pow_left₀ (windowNarrowSum_nonneg Z _ r t)
        (windowNarrowSum_mono_radius Z _ hr0 (by dsimp [r]; linarith) t) 2
    have hbd := hS₀ (T / 2) hS_half (2 * R₀) (by positivity) (by linarith) hκ_half Z
    have hsq_le : ((2 * R₀) * Real.log (T / 2)) ^ (2 : ℕ) ≤ 4 * (R₀ * L) ^ (2 : ℕ) := by
      have h1 : (2 * R₀) * Real.log (T / 2) ≤ 2 * (R₀ * L) := by
        have := mul_le_mul_of_nonneg_left hlog_half_le (show 0 ≤ 2 * R₀ by positivity)
        linarith
      calc ((2 * R₀) * Real.log (T / 2)) ^ (2 : ℕ)
          ≤ (2 * (R₀ * L)) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) h1 2
        _ = 4 * (R₀ * L) ^ (2 : ℕ) := by ring
    calc ∫ t in Icc (T / 2) T, (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
        ≤ C₁ * ((2 * R₀) * Real.log (T / 2)) ^ (2 : ℕ) * (T / 2) := hmono.trans hbd
      _ ≤ C₁ * (4 * (R₀ * L) ^ (2 : ℕ)) * (T / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq_le hC₁.le) (by positivity)
      _ = 2 * C₁ * (R₀ * L) ^ (2 : ℕ) * T := by ring
  -- Piece 2: `[T, 2T]` at radius `R₀`:
  have hIcc2 :
      (∫ t in Icc T (2 * T),
          (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
        C₁ * (R₀ * L) ^ (2 : ℕ) * T :=
    hS₀ T hS_T R₀ hR₀ (by linarith) hκ Z
  -- Piece 3: `[2T, 4T]` at radius `R₀`:
  have hlog_2T_ge : L ≤ Real.log (2 * T) :=
    Real.log_le_log hT0 (by linarith)
  have hlog_2T_le : Real.log (2 * T) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hκ_2T : κ₂ ≤ R₀ * Real.log (2 * T) :=
    hκ.trans (mul_le_mul_of_nonneg_left hlog_2T_ge hR₀.le)
  have hIcc3 :
      (∫ t in Icc (2 * T) (4 * T),
          (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
        8 * C₁ * (R₀ * L) ^ (2 : ℕ) * T := by
    have hbd := hS₀ (2 * T) hS_2T R₀ hR₀ (by linarith) hκ_2T Z
    rw [show 2 * (2 * T) = 4 * T by ring] at hbd
    have hsq_le : (R₀ * Real.log (2 * T)) ^ (2 : ℕ) ≤ 4 * (R₀ * L) ^ (2 : ℕ) := by
      have h1 : R₀ * Real.log (2 * T) ≤ 2 * (R₀ * L) := by
        have := mul_le_mul_of_nonneg_left hlog_2T_le hR₀.le
        linarith
      calc (R₀ * Real.log (2 * T)) ^ (2 : ℕ)
          ≤ (2 * (R₀ * L)) ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) h1 2
        _ = 4 * (R₀ * L) ^ (2 : ℕ) := by ring
    calc ∫ t in Icc (2 * T) (4 * T), (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
        ≤ C₁ * (R₀ * Real.log (2 * T)) ^ (2 : ℕ) * (2 * T) := hbd
      _ ≤ C₁ * (4 * (R₀ * L) ^ (2 : ℕ)) * (2 * T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq_le hC₁.le) (by positivity)
      _ = 8 * C₁ * (R₀ * L) ^ (2 : ℕ) * T := by ring
  -- Exterior tails `(-∞, T/2]` and `[4T, ∞)`:
  have hZcard : (Z.card : ℝ) ≤ T * L := by
    have hc1 : (Z.card : ℝ) ≤ (zeroWindow (2 * T)).card := by
      exact_mod_cast card_dyadicZeroWindow_le T
    have hc2 : (2 * T) * Real.log (2 * T) / 5 ≤ T * L := by
      have := mul_le_mul_of_nonneg_left hlog_2T_le (show 0 ≤ 2 * T by positivity)
      linarith
    exact hc1.trans (hcard.trans hc2)
  have htail_val :
      8 * Real.pi * r ^ (4 : ℕ) * (Z.card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) ≤
        (R₀ * L) ^ (2 : ℕ) * T := by
    have hr4 : r ^ (4 : ℕ) ≤ 1 := pow_le_one₀ hr0.le hr1
    have hZsq : (Z.card : ℝ) ^ (2 : ℕ) ≤ (T * L) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hZcard 2
    have hnum : 8 * Real.pi * r ^ (4 : ℕ) * (Z.card : ℝ) ^ (2 : ℕ) ≤ T ^ (4 : ℕ) := by
      calc 8 * Real.pi * r ^ (4 : ℕ) * (Z.card : ℝ) ^ (2 : ℕ)
          ≤ 8 * Real.pi * 1 * (T * L) ^ (2 : ℕ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr4 (by positivity)) hZsq
              (by positivity) (by positivity)
        _ = (8 * Real.pi * L ^ (2 : ℕ)) * T ^ (2 : ℕ) := by ring
        _ ≤ T ^ (2 : ℕ) * T ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right htail (sq_nonneg T)
        _ = T ^ (4 : ℕ) := by ring
    have hdiv : 8 * Real.pi * r ^ (4 : ℕ) * (Z.card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      linarith [show T * T ^ (3 : ℕ) = T ^ (4 : ℕ) by ring]
    exact hdiv.trans (by nlinarith)
  have hIic := (setIntegral_Iic_windowNarrowSum_sq_le hT0 hr0).trans htail_val
  have hIci := (setIntegral_Ici_windowNarrowSum_sq_le hT0 hr0).trans htail_val
  -- Total `L²(ℝ)` integral and Poisson identity:
  have htot_L2 :
      (∫ t : ℝ, (windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
        (11 * C₁ + 2) * (R₀ * L) ^ (2 : ℕ) * T := by
    have h5 := integral_le_five_pieces (integrable_windowNarrowSum_sq Z _ hr0)
      (fun t => sq_nonneg _) hT0
    linarith [h5, hIic, hIcc1, hIcc2, hIcc3, hIci]
  rw [lorentz_pairSum_eq_integral_windowNarrowSum_sq Z (fun q => (q.1 : ℂ).im) hR₀]
  calc 4 / (Real.pi * R₀) *
        ∫ t : ℝ, (windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)
      ≤ 4 / (Real.pi * R₀) * ((11 * C₁ + 2) * (R₀ * L) ^ (2 : ℕ) * T) :=
        mul_le_mul_of_nonneg_left htot_L2 (by positivity)
    _ = C_pair * (R₀ * L) * (T * L) := by
        dsimp [C_pair]
        have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
        have hRne : R₀ ≠ 0 := hR₀.ne'
        field_simp
        ring

end RHTower

end
