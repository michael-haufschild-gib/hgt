import GaloisForLFunctions.ArithmeticIncidencePositivity.BumpBridgeOfThePrimeJumpEnergy
import GaloisForLFunctions.ArithmeticIncidencePositivity.OddPlateauFoldedWindowPositivity
import GaloisForLFunctions.ArithmeticIncidencePositivity.CubicGaugeSurplusPotential

/-!
# The archimedean part of the bump bridge and calibrated self-energy asymptotic

This module resolves **Open Problem 3** ("The archimedean part of the bump bridge") and **Research
Topic 3** ("The bump bridge") by establishing the complete small-width asymptotic structure of the
archimedean signed jump energy

`J_M^arch(u) = ∫_{t > 0} ω(t) ∫_ℝ M(x) M(x + t) (u(x) − u(x + t))² dx dt`

and the full signed jump energy `J_M(u) = J_M^arch(u) + J_M^prime(u)` on general bump profiles
`u_w(x) = Σ_{p ∈ P} κ_p β((x − p)/w)` and even lattice bump profiles
`u_w(x) = Σ_{a ∈ S} c_a (β((x − log a)/w) + β((x + log a)/w))`:

1. **Global Lipschitz-`L¹` shift domination (`abs_bumpPairShiftJump_le_mul_t`,
   `integrableOn_archLevyDensity_mul_signedShiftJump_bumpProfile`).**
   Bounding one difference factor `|β((x − q)/w) − β((x + t − q)/w)| ≤ L_β t / w` by the Lipschitz
   constant of `β` and integrating the second factor `|β((x − p)/w) − β((x + t − p)/w)|` in `L¹(ℝ)`
   (`≤ 2 w ∫|β|`) cancels the width `w` identically, giving
   `|∫_ℝ M(x) M(x + t) (u_w(x) − u_w(x + t))² dx| ≤ K t` for all `t ≥ 0` and `w > 0`. Combined with
   `integrableOn_archLevyDensity_mul_id`, this dominates `ω(t) ∫ signedShiftJump` on the entire
   half-line `(0, ∞)` and bounds the near-zero region `(0, 2w]` by `O(w)`.
2. **Single-bump logarithmic self-energy asymptotic
   (`tendsto_gaugeArchJump_singleBump_div_mul_log`).**
   For a single bump `b_{α,w}(x) = β((x − α)/w)`, shifts `t > 2w` decouple the two copies of `β`,
   leaving `w ∫ (M(α + wy) M(α + wy + t) + M(α − t + wy) M(α + wy)) β(y)² dy`. Integrating against
   `ω(t)` over `(2w, δ)` via `archLevyAntideriv` (`2 Ω(2w) = log(1/w) + O(1)`) proves that as
   `w → 0⁺`,
   `gaugeArchJump M (fun x => β((x − α)/w)) / (w log(1/w)) → M(α)² ∫ β²`.
3. **Exact `O(w²)` off-diagonal archimedean decoupling (`abs_gaugeArchJump_sub_sum_singleBump_le`,
   `tendsto_gaugeArchJump_sub_sum_singleBump_div`).**
   For a finite centre set `P` with minimum separation `s > 0` and `0 < w < s / 4`, distinct bump
   centres `p ≠ q` have zero overlap on the entire interval `t ∈ (0, s / 2]`, so the multi-bump
   archimedean integrand equals `Σ_{p ∈ P} κ_p² ∫ signedShiftJump M b_{p,w} t x` identically on
   `(0, s / 2]`. On `(s / 2, ∞)`, each `p ≠ q` shift-overlap is confined to `[|p − q| − 2w, |p − q| + 2w]`
   of measure `4w`, where the `x`-integral is `O(w)`, so the off-diagonal archimedean interaction is
   `O(w²) = o(w)`.
4. **Multi-bump, lattice, and calibrated bridges
   (`tendsto_gaugeArchJump_bumpProfile_div_mul_log`,
   `tendsto_gaugeArchJump_latticeBumpProfile_div_mul_log`,
   `tendsto_signedJumpEnergy_latticeBumpProfile_div_mul_log`,
   `tendsto_calibratedSignedJumpEnergy_latticeBumpProfile_netAtom`,
   `tendsto_integral_sq_bumpProfile_mul_div`).**
   At scale `w log(1/w)`, both `J_M^arch(u_w)` and `J_M(u_w)` converge to
   `(∫ β²) Σ_{p ∈ P} κ_p² M(p)²` (and `2 (∫ β²) Σ_{a ∈ S} c_a² M(log a)²` on the lattice).
   Subtracting the single-packet archimedean self-energies `Σ_{p ∈ P} κ_p² J_M^arch(b_{p,w})` kills
   the `w log(1/w)` diagonal and `O(w²)` off-diagonal archimedean terms, so at scale `w` the
   calibrated total jump energy converges to the exact prime incidence quadratic form in `netAtom`.
-/

open MeasureTheory Set Filter Topology RHTower
open RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {β : ℝ → ℝ}

/-! ### Part I: Definition of `gaugeArchJump` and global Lipschitz-`L¹` shift bounds -/

/-- The archimedean part of the signed jump energy `J_M`:
`J_M^arch(u) = ∫_{t > 0} ω(t) ∫_ℝ M(x) M(x + t) (u(x) − u(x + t))² dx dt`. -/
def gaugeArchJump (M u : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, signedShiftJump M u t x

/-- Exact decomposition `J_M(u) = J_M^arch(u) + J_M^prime(u)`. -/
theorem signedJumpEnergy_eq_gaugeArchJump_add_gaugePrimeJump (M u : ℝ → ℝ) :
    signedJumpEnergy M u = gaugeArchJump M u + gaugePrimeJump M u := rfl

/-- Single-centre bump `b_{α,w}(x) = β((x − α)/w)` is `shiftedBumpProfile β w {α} (fun _ => 1)`. -/
theorem singleBump_eq_shiftedBumpProfile (β : ℝ → ℝ) (w α : ℝ) :
    (fun x => β ((x - α) / w)) = shiftedBumpProfile β w {α} (fun _ => 1) := by
  funext x
  simp [shiftedBumpProfile]

/-- Integrability of `|β|` for a continuous bump `β` supported in `[−1, 1]`. -/
theorem integrable_abs_of_bump (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0) :
    Integrable (fun y => |β y|) := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1) (b := 1)) ?_
  intro y hy
  by_contra hmem
  rw [mem_Icc, not_and_or, not_le, not_le] at hmem
  have : 1 < |y| := by
    rcases hmem with h | h
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl h)
  exact hy (by simp [hβ y this])

/-- Integrability of `β²` for a continuous bump `β` supported in `[−1, 1]`. -/
theorem integrable_sq_of_bump (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0) :
    Integrable (fun y => β y ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1) (b := 1)) ?_
  intro y hy
  by_contra hmem
  rw [mem_Icc, not_and_or, not_le, not_le] at hmem
  have : 1 < |y| := by
    rcases hmem with h | h
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl h)
  exact hy (by simp [hβ y this])

/-- Rescaled `L¹` integral of a shifted bump: `∫ |β((x − α)/w)| dx = w ∫ |β(y)| dy` for `w > 0`. -/
theorem integral_abs_bump_div (α : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ x, |β ((x - α) / w)|) = w * ∫ y, |β y| := by
  rw [integral_sub_right_eq_self (fun t => |β (t / w)|) α,
    Measure.integral_comp_div (fun y => |β y|) w, abs_of_pos hw, smul_eq_mul]

/-- **Width-independent Lipschitz-`L¹` bound on a bump-pair shift integral.**
For a Lipschitz bump `β` supported in `[−1, 1]` and a gauge `M` with `|M x| ≤ C e^{−|x|}`,
bounding `|β((x − q)/w) − β((x + t − q)/w)| ≤ L_β t / w` and integrating
`|β((x − p)/w) − β((x + t − p)/w)|` in `L¹(ℝ)` (`≤ 2 w ∫|β|`) cancels `w` and gives
`|∫ M(x) M(x + t) (β_p(x) − β_p(x + t)) (β_q(x) − β_q(x + t)) dx| ≤ (2 C² L_β ∫|β|) t`
for all `t ≥ 0` and `w > 0`. -/
theorem abs_integral_bumpPair_diff_le_mul_t (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (_hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (_hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    (p q : ℝ) {w t : ℝ} (hw : 0 < w) (ht : 0 ≤ t) :
    |∫ x, M x * M (x + t) * (β ((x - p) / w) - β ((x + t - p) / w)) *
        (β ((x - q) / w) - β ((x + t - q) / w))| ≤
      (2 * C ^ 2 * Lβ * ∫ y, |β y|) * t := by
  have hβint := integrable_abs_of_bump hβc hβ
  have hint1 : Integrable (fun x => |β ((x - p) / w)|) := by
    have h := hβint.comp_div hw.ne'
    simpa [Function.comp_def] using h.comp_sub_right p
  have hint2 : Integrable (fun x => |β ((x - (p - t)) / w)|) := by
    have h := hβint.comp_div hw.ne'
    simpa [Function.comp_def] using h.comp_sub_right (p - t)
  have hdom : Integrable (fun x => C ^ 2 * (Lβ * (t / w)) *
      (|β ((x - p) / w)| + |β ((x - (p - t)) / w)|)) :=
    (hint1.add hint2).const_mul _
  have hpt : ∀ x, |M x * M (x + t) * (β ((x - p) / w) - β ((x + t - p) / w)) *
      (β ((x - q) / w) - β ((x + t - q) / w))| ≤
      C ^ 2 * (Lβ * (t / w)) * (|β ((x - p) / w)| + |β ((x - (p - t)) / w)|) := by
    intro x
    have hM_le : |M x * M (x + t)| ≤ C ^ 2 := by
      have h1 := abs_mul_shift_le hMC t x
      have hexp : Real.exp (-|t|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg t])
      nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg C)]
    have hq_le : |β ((x - q) / w) - β ((x + t - q) / w)| ≤ Lβ * (t / w) := by
      have h := hβL ((x - q) / w) ((x + t - q) / w)
      have heq : (x - q) / w - (x + t - q) / w = -(t / w) := by ring
      rw [heq, abs_neg, abs_of_nonneg (div_nonneg ht hw.le)] at h
      exact h
    have hp_le : |β ((x - p) / w) - β ((x + t - p) / w)| ≤
        |β ((x - p) / w)| + |β ((x - (p - t)) / w)| := by
      rw [show x + t - p = x - (p - t) by ring]
      exact abs_sub _ _
    rw [abs_mul, abs_mul]
    have h1 : |M x * M (x + t)| * |β ((x - p) / w) - β ((x + t - p) / w)| ≤
        C ^ 2 * (|β ((x - p) / w)| + |β ((x - (p - t)) / w)|) :=
      mul_le_mul hM_le hp_le (abs_nonneg _) (sq_nonneg C)
    calc |M x * M (x + t)| * |β ((x - p) / w) - β ((x + t - p) / w)| *
          |β ((x - q) / w) - β ((x + t - q) / w)|
        ≤ (C ^ 2 * (|β ((x - p) / w)| + |β ((x - (p - t)) / w)|)) * (Lβ * (t / w)) :=
          mul_le_mul h1 hq_le (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (Lβ * (t / w)) * (|β ((x - p) / w)| + |β ((x - (p - t)) / w)|) := by ring
  calc |∫ x, M x * M (x + t) * (β ((x - p) / w) - β ((x + t - p) / w)) *
          (β ((x - q) / w) - β ((x + t - q) / w))|
      ≤ ∫ x, |M x * M (x + t) * (β ((x - p) / w) - β ((x + t - p) / w)) *
          (β ((x - q) / w) - β ((x + t - q) / w))| := abs_integral_le_integral_abs
    _ ≤ ∫ x, C ^ 2 * (Lβ * (t / w)) * (|β ((x - p) / w)| + |β ((x - (p - t)) / w)|) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hdom
          (Eventually.of_forall hpt)
    _ = C ^ 2 * (Lβ * (t / w)) * ((∫ x, |β ((x - p) / w)|) + ∫ x, |β ((x - (p - t)) / w)|) := by
        rw [integral_const_mul, integral_add hint1 hint2]
    _ = (2 * C ^ 2 * Lβ * ∫ y, |β y|) * t := by
        rw [integral_abs_bump_div p hw, integral_abs_bump_div (p - t) hw]
        field_simp [hw.ne']
        ring

/-- The spatial shift integral for a pair of bump centres `(p, q)`:
`bumpPairShiftJump M β w p q t = ∫ x, M(x) M(x + t) (β_p(x) − β_p(x + t)) (β_q(x) − β_q(x + t)) dx`. -/
def bumpPairShiftJump (M β : ℝ → ℝ) (w p q t : ℝ) : ℝ :=
  (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w)) -
    (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w)) -
    (∫ x, M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - q) / w)) +
    ∫ x, M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - (q - t)) / w)

/-- On the diagonal `p = q`, `bumpPairShiftJump` is the single-bump shift integral. -/
theorem bumpPairShiftJump_diag (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} (hM : Continuous M) (p t : ℝ) {w : ℝ} (hw : 0 < w) :
    bumpPairShiftJump M β w p p t = ∫ x, signedShiftJump M (fun x => β ((x - p) / w)) t x := by
  rw [singleBump_eq_shiftedBumpProfile β w p,
    integral_signedShiftJump_bumpProfile hβc hβ hM {p} (fun _ => 1) t hw]
  simp [bumpPairShiftJump]

/-- Expansion of `∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x` in `bumpPairShiftJump`. -/
theorem integral_signedShiftJump_eq_sum_bumpPairShiftJump (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} (hM : Continuous M)
    (P : Finset ℝ) (κ : ℝ → ℝ) (t : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x) =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * bumpPairShiftJump M β w p q t :=
  integral_signedShiftJump_bumpProfile hβc hβ hM P κ t hw

/-- Width-independent Lipschitz-`L¹` bound `|bumpPairShiftJump M β w p q t| ≤ (2 C² L_β ∫|β|) t`. -/
theorem abs_bumpPairShiftJump_le_mul_t (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    (p q : ℝ) {w t : ℝ} (hw : 0 < w) (ht : 0 ≤ t) :
    |bumpPairShiftJump M β w p q t| ≤ (2 * C ^ 2 * Lβ * ∫ y, |β y|) * t := by
  have hbump : ∀ α : ℝ, HasCompactSupport (fun x => β ((x - α) / w)) := fun α => by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := α - w) (b := α + w)) ?_
    intro x hx
    by_contra hmem
    have : 1 < |(x - α) / w| := by
      rw [abs_div, abs_of_pos hw, lt_div_iff₀ hw, one_mul]
      rw [mem_Icc, not_and_or, not_le, not_le] at hmem
      rcases hmem with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl (by linarith))
    exact hx (hβ _ this)
  have hint : ∀ α α' : ℝ, Integrable (fun x => M x * M (x + t) * β ((x - α) / w) * β ((x - α') / w)) :=
    fun α α' => Continuous.integrable_of_hasCompactSupport (by fun_prop) ((hbump α').mul_left)
  have h1 : Integrable (fun x => M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w) -
      M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w)) :=
    (hint p q).sub (hint p (q - t))
  have h2 : Integrable (fun x => M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w) -
      M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w) -
      M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - q) / w)) :=
    h1.sub (hint (p - t) q)
  unfold bumpPairShiftJump
  rw [← integral_sub (hint p q) (hint p (q - t)), ← integral_sub h1 (hint (p - t) q),
    ← integral_add h2 (hint (p - t) (q - t))]
  have hcongr : (∫ x, (M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w) -
      M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w) -
      M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - q) / w) +
      M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - (q - t)) / w))) =
      ∫ x, M x * M (x + t) * (β ((x - p) / w) - β ((x + t - p) / w)) *
        (β ((x - q) / w) - β ((x + t - q) / w)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [show x + t - p = x - (p - t) by ring, show x + t - q = x - (q - t) by ring]
    ring
  rw [hcongr]
  exact abs_integral_bumpPair_diff_le_mul_t hβc hβ hLβ hβL hM hMC p q hw ht

/-- **Width-independent Lipschitz-`L¹` bound for `shiftedBumpProfile`.**
For all `w > 0` and `t ≥ 0`,
`|∫ signedShiftJump M (shiftedBumpProfile β w P κ) t x| ≤ ((Σ_{p ∈ P} |κ_p|)² · 2 C² L_β ∫|β|) t`. -/
theorem abs_shift_bumpProfile_le_mul_t (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    (P : Finset ℝ) (κ : ℝ → ℝ) {w t : ℝ} (hw : 0 < w) (ht : 0 ≤ t) :
    |∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x| ≤
      ((∑ p ∈ P, |κ p|) ^ 2 * (2 * C ^ 2 * Lβ * ∫ y, |β y|)) * t := by
  rw [integral_signedShiftJump_eq_sum_bumpPairShiftJump hβc hβ hM P κ t hw]
  calc |∑ p ∈ P, ∑ q ∈ P, κ p * κ q * bumpPairShiftJump M β w p q t|
      ≤ ∑ p ∈ P, |∑ q ∈ P, κ p * κ q * bumpPairShiftJump M β w p q t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, |κ p * κ q * bumpPairShiftJump M β w p q t| :=
        Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, |κ p| * |κ q| * ((2 * C ^ 2 * Lβ * ∫ y, |β y|) * t) := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_bumpPairShiftJump_le_mul_t hβc hβ hLβ hβL hM hMC p q hw ht)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ((∑ p ∈ P, |κ p|) ^ 2 * (2 * C ^ 2 * Lβ * ∫ y, |β y|)) * t := by
        have h_eq : ((∑ p ∈ P, |κ p|) ^ 2 * (2 * C ^ 2 * Lβ * ∫ y, |β y|)) * t =
            (∑ p ∈ P, |κ p|) ^ 2 * ((2 * C ^ 2 * Lβ * ∫ y, |β y|) * t) := by ring
        rw [h_eq, pow_two (∑ p ∈ P, |κ p|), Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]

/-- Continuity in `t` of a single bump-pair shift integral. -/
theorem continuous_integral_bumpPair_shift (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} (_hM : Continuous M)
    (p q c₁ c₂ : ℝ) {w : ℝ} (hw : 0 < w) :
    Continuous (fun t => ∫ x, M x * M (x + t) * β ((x - (p - c₁ * t)) / w) *
      β ((x - (q - c₂ * t)) / w)) := by
  have hcongr : (fun t => ∫ x, M x * M (x + t) * β ((x - (p - c₁ * t)) / w) *
        β ((x - (q - c₂ * t)) / w)) =
      fun t => w * ∫ y, M (p - c₁ * t + w * y) * M (p - c₁ * t + w * y + t) * β y *
        β (y + (p - c₁ * t - (q - c₂ * t)) / w) := by
    funext t
    exact integral_bump_pair_eq (fun x => M x * M (x + t)) (p - c₁ * t) (q - c₂ * t) hw
  rw [hcongr]
  refine continuous_const.mul ?_
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨Bβ, hB⟩ := exists_abs_le_of_bump hβc hβ
  have hB0 : 0 ≤ Bβ := (abs_nonneg _).trans (hB 0)
  set R := |p| + |c₁| * (|t₀| + 1) + w
  obtain ⟨K, hK⟩ : ∃ K, ∀ z : ℝ × ℝ, z ∈ Icc (-R) R ×ˢ Icc (t₀ - 1) (t₀ + 1) →
      |M z.1 * M (z.1 + z.2)| ≤ K := by
    have hc : Continuous (fun z : ℝ × ℝ => M z.1 * M (z.1 + z.2)) := by fun_prop
    exact (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc.continuousOn |>.imp
      fun K hK z hz => by simpa [Real.norm_eq_abs] using hK z hz
  have hK0 : 0 ≤ K := by
    have hmem : ((0 : ℝ), t₀) ∈ Icc (-R) R ×ˢ Icc (t₀ - 1) (t₀ + 1) := by
      refine ⟨⟨?_, ?_⟩, ⟨by linarith, by linarith⟩⟩ <;>
        { dsimp [R]; nlinarith [abs_nonneg p, abs_nonneg c₁, abs_nonneg t₀] }
    exact (abs_nonneg _).trans (hK (0, t₀) hmem)
  have hint : Integrable (fun y => (K * Bβ) * |β y|) :=
    (integrable_abs_of_bump hβc hβ).const_mul (K * Bβ)
  rw [ContinuousAt]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => (K * Bβ) * |β y|) ?_ ?_ hint ?_
  · exact Eventually.of_forall fun t => (by fun_prop : Continuous fun y =>
      M (p - c₁ * t + w * y) * M (p - c₁ * t + w * y + t) * β y *
        β (y + (p - c₁ * t - (q - c₂ * t)) / w)).aestronglyMeasurable
  · filter_upwards [Icc_mem_nhds (by linarith : t₀ - 1 < t₀) (by linarith : t₀ < t₀ + 1)] with t ht
    refine Eventually.of_forall fun y => ?_
    by_cases hy : 1 < |y|
    · rw [hβ y hy]; simp
    · rw [not_lt] at hy
      have h_abs_t : |t| ≤ |t₀| + 1 := by
        rw [abs_le]
        have := neg_abs_le t₀
        have := le_abs_self t₀
        constructor <;> linarith [ht.1, ht.2]
      have hx : p - c₁ * t + w * y ∈ Icc (-R) R := by
        rw [mem_Icc, ← abs_le]
        calc |p - c₁ * t + w * y|
            ≤ |p - c₁ * t| + |w * y| := abs_add_le _ _
          _ ≤ |p| + |c₁ * t| + |w * y| := by linarith [abs_sub p (c₁ * t)]
          _ = |p| + |c₁| * |t| + w * |y| := by rw [abs_mul, abs_mul, abs_of_pos hw]
          _ ≤ |p| + |c₁| * (|t₀| + 1) + w * 1 := by gcongr
          _ = R := by dsimp [R]; ring
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := hK (p - c₁ * t + w * y, t) ⟨hx, ht⟩
      have h2 := hB (y + (p - c₁ * t - (q - c₂ * t)) / w)
      calc |M (p - c₁ * t + w * y) * M (p - c₁ * t + w * y + t)| * |β y| *
            |β (y + (p - c₁ * t - (q - c₂ * t)) / w)|
          ≤ K * |β y| * Bβ :=
            mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2 (abs_nonneg _)
              (mul_nonneg hK0 (abs_nonneg _))
        _ = (K * Bβ) * |β y| := by ring
  · refine Eventually.of_forall fun y => ?_
    exact (Continuous.tendsto (by fun_prop : Continuous fun t =>
      M (p - c₁ * t + w * y) * M (p - c₁ * t + w * y + t) * β y *
        β (y + (p - c₁ * t - (q - c₂ * t)) / w)) t₀)

/-- Continuity in `t` of the spatial shift integral `t ↦ ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x`. -/
theorem continuous_integral_signedShiftJump_bumpProfile (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} (hM : Continuous M)
    (P : Finset ℝ) (κ : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    Continuous (fun t => ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x) := by
  have heq : (fun t => ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x) =
      fun t => ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        ((∫ x, M x * M (x + t) * β ((x - (p - 0 * t)) / w) * β ((x - (q - 0 * t)) / w)) -
          (∫ x, M x * M (x + t) * β ((x - (p - 0 * t)) / w) * β ((x - (q - 1 * t)) / w)) -
          (∫ x, M x * M (x + t) * β ((x - (p - 1 * t)) / w) * β ((x - (q - 0 * t)) / w)) +
          ∫ x, M x * M (x + t) * β ((x - (p - 1 * t)) / w) * β ((x - (q - 1 * t)) / w)) := by
    funext t
    simpa [zero_mul, one_mul, sub_zero] using
      integral_signedShiftJump_bumpProfile hβc hβ hM P κ t hw
  rw [heq]
  refine continuous_finsetSum P fun p _ => continuous_finsetSum P fun q _ => ?_
  exact continuous_const.mul
    ((((continuous_integral_bumpPair_shift hβc hβ hM p q 0 0 hw).sub
      (continuous_integral_bumpPair_shift hβc hβ hM p q 0 1 hw)).sub
      (continuous_integral_bumpPair_shift hβc hβ hM p q 1 0 hw)).add
      (continuous_integral_bumpPair_shift hβc hβ hM p q 1 1 hw))

/-- **Global integrability of the archimedean jump integrand for `shiftedBumpProfile` on `(0, ∞)`.** -/
theorem integrableOn_archLevyDensity_mul_signedShiftJump_bumpProfile (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (P : Finset ℝ) (κ : ℝ → ℝ) {w : ℝ}
    (hw : 0 < w) :
    IntegrableOn (fun t => archLevyDensity t *
      ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x) (Ioi 0) := by
  set K := (∑ p ∈ P, |κ p|) ^ 2 * (2 * C ^ 2 * Lβ * ∫ y, |β y|)
  have hmaj : IntegrableOn (fun t => K * (archLevyDensity t * t)) (Ioi 0) :=
    integrableOn_archLevyDensity_mul_id.const_mul K
  have hmeas : Measurable (fun t => archLevyDensity t *
      ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x) :=
    measurable_archLevyDensity.mul
      (continuous_integral_signedShiftJump_bumpProfile hβc hβ hM P κ hw).measurable
  refine hmaj.mono' hmeas.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hω : 0 < archLevyDensity t := archLevyDensity_pos ht0
  have hb := abs_shift_bumpProfile_le_mul_t hβc hβ hLβ hβL hM hMC P κ hw ht0.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hω]
  calc archLevyDensity t * |∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x|
      ≤ archLevyDensity t * (K * t) := mul_le_mul_of_nonneg_left hb hω.le
    _ = K * (archLevyDensity t * t) := by ring

/-- **Near-zero `(0, 2w]` bound on the archimedean jump integral.**
For `0 < w ≤ 1 / 2`, the integral of `ω(t) ∫ signedShiftJump` over `Ioc 0 (2w)` is at most
`3 w (Σ_{p ∈ P} |κ_p|)² (2 C² L_β ∫|β|)`. -/
theorem abs_setIntegral_Ioc_two_mul_w_le (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    (P : Finset ℝ) (κ : ℝ → ℝ) {w : ℝ} (hw : 0 < w) (hw_half : w ≤ 1 / 2) :
    |∫ t in Ioc 0 (2 * w), archLevyDensity t *
        ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x| ≤
      3 * ((∑ p ∈ P, |κ p|) ^ 2 * (2 * C ^ 2 * Lβ * ∫ y, |β y|)) * w := by
  set K := (∑ p ∈ P, |κ p|) ^ 2 * (2 * C ^ 2 * Lβ * ∫ y, |β y|)
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ y, |β y| := integral_nonneg fun _ => abs_nonneg _
    positivity
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 (2 * w))
    (f := fun t => archLevyDensity t * ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x)
    (C := (3 / 2) * K)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
    (fun t ht => by
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := by linarith [ht.2]
      have hω : 0 < archLevyDensity t := archLevyDensity_pos ht0
      have hω_le : archLevyDensity t * t ≤ 3 / 2 := by
        have hle := archLevyDensity_le_of_le_one ht0 ht1
        calc archLevyDensity t * t ≤ (3 / 2 / t) * t := mul_le_mul_of_nonneg_right hle ht0.le
          _ = 3 / 2 := by field_simp
      have hb := abs_shift_bumpProfile_le_mul_t hβc hβ hLβ hβL hM hMC P κ hw ht0.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hω]
      calc archLevyDensity t * |∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x|
          ≤ archLevyDensity t * (K * t) := mul_le_mul_of_nonneg_left hb hω.le
        _ = (archLevyDensity t * t) * K := by ring
        _ ≤ (3 / 2) * K := mul_le_mul_of_nonneg_right hω_le hK0)
  rw [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal (by positivity)] at h1
  linarith

private theorem integrableOn_exp_neg_Ioi (δ : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi δ) := by
  simpa only [neg_mul, one_mul] using
    integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) δ

private theorem integral_exp_neg_Ioi_eq (δ : ℝ) :
    (∫ x : ℝ in Ioi δ, Real.exp (-x)) = Real.exp (-δ) := by
  have h := integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) δ
  simpa only [neg_mul, one_mul, neg_neg, div_neg, div_one] using h

/-- **Tail `Ioi δ` bound on the archimedean jump integral.**
For any `δ > 0` and `w > 0`, the integral of `ω(t) ∫ signedShiftJump` over `Ioi δ` is at most
`w · archLevyDensity δ · (Σ_{p ∈ P} |κ_p|)² · 4 C² B_β ∫|β|`. -/
theorem abs_setIntegral_Ioi_delta_le (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {Bβ : ℝ} (hB : ∀ y, |β y| ≤ Bβ) (P : Finset ℝ) (κ : ℝ → ℝ) {w δ : ℝ}
    (hw : 0 < w) (hδ : 0 < δ) :
    |∫ t in Ioi δ, archLevyDensity t *
        ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x| ≤
      (archLevyDensity δ * ((∑ p ∈ P, |κ p|) ^ 2 * (4 * (C ^ 2 * Bβ * ∫ y, |β y|)))) * w := by
  set K₂ := (∑ p ∈ P, |κ p|) ^ 2 * (4 * (C ^ 2 * Bβ * ∫ y, |β y|))
  have hB0 : 0 ≤ Bβ := (abs_nonneg _).trans (hB 0)
  have hK₂0 : 0 ≤ K₂ := by
    have : 0 ≤ ∫ y, |β y| := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hint_all := integrableOn_archLevyDensity_mul_signedShiftJump_bumpProfile
    hβc hβ hLβ hβL hM hMC P κ hw
  have hint_δ : IntegrableOn (fun t => archLevyDensity t *
      ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x) (Ioi δ) :=
    hint_all.mono_set (Ioi_subset_Ioi hδ.le)
  have hexp_int : IntegrableOn (fun t => (archLevyDensity δ * K₂ * w) * Real.exp (-t)) (Ioi δ) :=
    (integrableOn_exp_neg_Ioi δ).const_mul (archLevyDensity δ * K₂ * w)
  have hpt : ∀ t ∈ Ioi δ, |archLevyDensity t *
      ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x| ≤
      (archLevyDensity δ * K₂ * w) * Real.exp (-t) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hδ ht
    have hω_pos : 0 < archLevyDensity t := archLevyDensity_pos ht0
    have hω_le : archLevyDensity t ≤ archLevyDensity δ :=
      strictAntiOn_archLevyDensity.antitoneOn hδ ht0 ht.le
    have hb := abs_shift_bumpProfile_div_le hβc hβ hM hMC hB P κ t hw
    rw [abs_div, abs_of_pos hw, div_le_iff₀ hw, abs_of_pos ht0] at hb
    rw [abs_mul, abs_of_pos hω_pos]
    calc archLevyDensity t * |∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x|
        ≤ archLevyDensity δ * ((∑ p ∈ P, |κ p|) ^ 2 *
            (4 * (C ^ 2 * Real.exp (-t) * Bβ * ∫ y, |β y|)) * w) :=
          mul_le_mul hω_le hb (abs_nonneg _) (archLevyDensity_pos hδ).le
      _ = (archLevyDensity δ * K₂ * w) * Real.exp (-t) := by dsimp [K₂]; ring
  calc |∫ t in Ioi δ, archLevyDensity t *
          ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x|
      ≤ ∫ t in Ioi δ, |archLevyDensity t *
          ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi δ, (archLevyDensity δ * K₂ * w) * Real.exp (-t) :=
        setIntegral_mono_on hint_δ.norm hexp_int measurableSet_Ioi fun t ht => by
          simpa [Real.norm_eq_abs] using hpt t ht
    _ = (archLevyDensity δ * K₂ * w) * Real.exp (-δ) := by
        rw [integral_const_mul, integral_exp_neg_Ioi_eq]
    _ ≤ (archLevyDensity δ * K₂) * w := by
        have hexp1 : Real.exp (-δ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have hωδ : 0 ≤ archLevyDensity δ := (archLevyDensity_pos hδ).le
        nlinarith [mul_le_mul_of_nonneg_left hexp1 (show 0 ≤ archLevyDensity δ * K₂ * w by positivity)]

/-! ### Part II: Two-sided logarithmic bracket for `archLevyAntideriv` and single-bump asymptotic -/

/-- For `0 < w ≤ 1 / 2`, `Real.log (1 / w) ≤ 2 * archLevyAntideriv (2 * w)`. -/
theorem log_one_div_le_two_mul_archLevyAntideriv {w : ℝ} (hw : 0 < w) (_hw_half : w ≤ 1 / 2) :
    Real.log (1 / w) ≤ 2 * archLevyAntideriv (2 * w) := by
  have h2w : 0 < 2 * w := by positivity
  have hge := archLevyAntideriv_ge h2w
  have hlog : -(1 / 2) * Real.log (2 * w / 4) = (Real.log (1 / w) + Real.log 2) / 2 := by
    have h1 : 2 * w / 4 = (1 / w)⁻¹ / 2 := by field_simp; ring
    rw [h1, Real.log_div (by positivity) (by norm_num), Real.log_inv]
    ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  linarith

/-- For `0 < w ≤ 1 / 2`, `2 * archLevyAntideriv (2 * w) ≤ Real.log (1 / w) + 4`. -/
theorem two_mul_archLevyAntideriv_le_log_one_div_add_four {w : ℝ} (hw : 0 < w)
    (hw_half : w ≤ 1 / 2) :
    2 * archLevyAntideriv (2 * w) ≤ Real.log (1 / w) + 4 := by
  have h2w : 0 < 2 * w := by positivity
  have hle := archLevyAntideriv_le_expansion h2w
  have hlog : -(1 / 2) * Real.log (2 * w / 4) = (Real.log (1 / w) + Real.log 2) / 2 := by
    have h1 : 2 * w / 4 = (1 / w)⁻¹ / 2 := by field_simp; ring
    rw [h1, Real.log_div (by positivity) (by norm_num), Real.log_inv]
    ring
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hw2 : (2 * w) ^ 2 ≤ 1 := by nlinarith
  have hw3 : (2 * w) ^ 3 ≤ 1 := by nlinarith
  linarith

/-- For any continuous `F : ℝ → ℝ`, `y ↦ F y * β y ^ 2` is integrable when `β` is continuous and
supported in `[−1, 1]`. -/
theorem integrable_mul_sq_of_bump (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun y => F y * β y ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport (hF.mul (hβc.pow 2)) ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1) (b := 1)) ?_
  intro y hy
  by_contra hmem
  rw [mem_Icc, not_and_or, not_le, not_le] at hmem
  have : 1 < |y| := by
    rcases hmem with h | h
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl h)
  exact hy (by simp [hβ y this])

/-- For a single bump `b_{α,w}(x) = β((x − α)/w)` and any shift `t > 2w`, the cross-shift terms
vanish and
`∫ x, signedShiftJump M b_{α,w} t x = w ∫ y, (M(α + wy) M(α + wy + t) + M(α − t + wy) M(α + wy)) β(y)² dy`. -/
theorem integral_signedShiftJump_singleBump_of_two_mul_w_lt (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} (hM : Continuous M) (α : ℝ)
    {w t : ℝ} (hw : 0 < w) (ht : 2 * w < t) :
    (∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) =
      w * ∫ y, (M (α + w * y) * M (α + w * y + t) + M (α - t + w * y) * M (α + w * y)) * β y ^ 2 := by
  have ht0 : 0 < t := by linarith
  rw [singleBump_eq_shiftedBumpProfile β w α,
    integral_signedShiftJump_bumpProfile hβc hβ hM {α} (fun _ => 1) t hw]
  simp only [Finset.sum_singleton, one_mul]
  have h2 : (∫ x, M x * M (x + t) * β ((x - α) / w) * β ((x - (α - t)) / w)) = 0 :=
    integral_bump_pair_eq_zero hβ (fun x => M x * M (x + t)) hw (by
      rw [show α - (α - t) = t by ring, abs_of_pos ht0]
      exact ht)
  have h3 : (∫ x, M x * M (x + t) * β ((x - (α - t)) / w) * β ((x - α) / w)) = 0 :=
    integral_bump_pair_eq_zero hβ (fun x => M x * M (x + t)) hw (by
      rw [show α - t - α = -t by ring, abs_neg, abs_of_pos ht0]
      exact ht)
  rw [h2, h3, sub_zero, sub_zero]
  rw [integral_bump_pair_eq (fun x => M x * M (x + t)) α α hw,
    integral_bump_pair_eq (fun x => M x * M (x + t)) (α - t) (α - t) hw]
  simp only [sub_self, zero_div, add_zero]
  rw [← mul_add]
  congr 1
  have hint1 : Integrable (fun y => (M (α + w * y) * M (α + w * y + t)) * β y ^ 2) :=
    integrable_mul_sq_of_bump hβc hβ (by fun_prop)
  have hint2 : Integrable (fun y => (M (α - t + w * y) * M (α - t + w * y + t)) * β y ^ 2) :=
    integrable_mul_sq_of_bump hβc hβ (by fun_prop)
  have hc1 : (∫ y, M (α + w * y) * M (α + w * y + t) * β y * β y) =
      ∫ y, (M (α + w * y) * M (α + w * y + t)) * β y ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => by ring)
  have hc2 : (∫ y, M (α - t + w * y) * M (α - t + w * y + t) * β y * β y) =
      ∫ y, (M (α - t + w * y) * M (α - t + w * y + t)) * β y ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [hc1, hc2, ← integral_add hint1 hint2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [show α - t + w * y + t = α + w * y by ring]
  ring

/-- **Logarithmic window approximation on `Ioc (2w) (δ/2)` for a single bump.**
If `|M u * M v - M α ^ 2| ≤ ε` for all `u, v ∈ Icc (α − δ) (α + δ)` and `0 < 2w < δ / 2 ≤ 1`, then
`|(∫_{2w}^{δ/2} ω(t) ∫ signedShiftJump M b_{α,w} t x dt) − 2 w (Ω(2w) − Ω(δ/2)) M(α)² ∫ β²|`
`≤ 2 ε w (Ω(2w) − Ω(δ/2)) ∫ β²`. -/
theorem abs_setIntegral_Ioc_singleBump_sub_le (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    (α : ℝ) {w δ ε : ℝ} (hw : 0 < w) (hwδ : 2 * w < δ / 2) (_hε : 0 ≤ ε)
    (hM_close : ∀ u ∈ Icc (α - δ) (α + δ), ∀ v ∈ Icc (α - δ) (α + δ), |M u * M v - M α ^ 2| ≤ ε) :
    |(∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t *
        ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) -
      2 * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * M α ^ 2 * ∫ y, β y ^ 2| ≤
      2 * ε * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * ∫ y, β y ^ 2 := by
  have h2w : 0 < 2 * w := by positivity
  have hint_all := integrableOn_archLevyDensity_mul_signedShiftJump_bumpProfile
    hβc hβ hLβ hβL hM hMC {α} (fun _ => 1) hw
  rw [← singleBump_eq_shiftedBumpProfile β w α] at hint_all
  have hint_Ioc : IntegrableOn (fun t => archLevyDensity t *
      ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) (Ioc (2 * w) (δ / 2)) :=
    hint_all.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h2w.le))
  have hint_ω : IntegrableOn archLevyDensity (Ioc (2 * w) (δ / 2)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hwδ.le]
    refine (continuousOn_archLevyDensity.mono fun t ht => ?_).intervalIntegrable
    rw [uIcc_of_le hwδ.le] at ht
    exact lt_of_lt_of_le h2w ht.1
  have hint_ω_eq : (∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t) =
      archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2) := by
    rw [← intervalIntegral.integral_of_le hwδ.le]
    exact integral_archLevyDensity_Icc h2w hwδ.le
  have hpt : ∀ t ∈ Ioc (2 * w) (δ / 2),
      w * (2 * M α ^ 2 - 2 * ε) * (∫ y, β y ^ 2) ≤
        (∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) ∧
      (∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) ≤
        w * (2 * M α ^ 2 + 2 * ε) * (∫ y, β y ^ 2) := by
    intro t ht
    rw [integral_signedShiftJump_singleBump_of_two_mul_w_lt hβc hβ hM α hw ht.1]
    have h_inner : ∀ y,
        (2 * M α ^ 2 - 2 * ε) * β y ^ 2 ≤
          (M (α + w * y) * M (α + w * y + t) + M (α - t + w * y) * M (α + w * y)) * β y ^ 2 ∧
        (M (α + w * y) * M (α + w * y + t) + M (α - t + w * y) * M (α + w * y)) * β y ^ 2 ≤
          (2 * M α ^ 2 + 2 * ε) * β y ^ 2 := by
      intro y
      by_cases hy : 1 < |y|
      · rw [hβ y hy]; simp
      · rw [not_lt] at hy
        have hy_bounds := abs_le.mp hy
        have hu1 : α + w * y ∈ Icc (α - δ) (α + δ) := by
          constructor <;> nlinarith [ht.1, ht.2]
        have hv1 : α + w * y + t ∈ Icc (α - δ) (α + δ) := by
          constructor <;> nlinarith [ht.1, ht.2]
        have hu2 : α - t + w * y ∈ Icc (α - δ) (α + δ) := by
          constructor <;> nlinarith [ht.1, ht.2]
        have hc1 := abs_le.mp (hM_close (α + w * y) hu1 (α + w * y + t) hv1)
        have hc2 := abs_le.mp (hM_close (α - t + w * y) hu2 (α + w * y) hu1)
        constructor
        · exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        · exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have hint_mid : Integrable (fun y =>
        (M (α + w * y) * M (α + w * y + t) + M (α - t + w * y) * M (α + w * y)) * β y ^ 2) :=
      integrable_mul_sq_of_bump hβc hβ (by fun_prop)
    have hint_low : Integrable (fun y => (2 * M α ^ 2 - 2 * ε) * β y ^ 2) :=
      (integrable_sq_of_bump hβc hβ).const_mul _
    have hint_high : Integrable (fun y => (2 * M α ^ 2 + 2 * ε) * β y ^ 2) :=
      (integrable_sq_of_bump hβc hβ).const_mul _
    have hlow := integral_mono hint_low hint_mid (fun y => (h_inner y).1)
    have hhigh := integral_mono hint_mid hint_high (fun y => (h_inner y).2)
    rw [integral_const_mul] at hlow hhigh
    exact ⟨by nlinarith, by nlinarith⟩
  have hlow_int := setIntegral_mono_on (hint_ω.const_mul (w * (2 * M α ^ 2 - 2 * ε) * ∫ y, β y ^ 2))
    hint_Ioc measurableSet_Ioc fun t ht => by
      have hω := (archLevyDensity_pos (lt_trans h2w ht.1)).le
      have := mul_le_mul_of_nonneg_left (hpt t ht).1 hω
      linarith
  have hhigh_int := setIntegral_mono_on hint_Ioc
    (hint_ω.const_mul (w * (2 * M α ^ 2 + 2 * ε) * ∫ y, β y ^ 2))
    measurableSet_Ioc fun t ht => by
      have hω := (archLevyDensity_pos (lt_trans h2w ht.1)).le
      have := mul_le_mul_of_nonneg_left (hpt t ht).2 hω
      linarith
  rw [integral_const_mul, hint_ω_eq] at hlow_int hhigh_int
  rw [abs_le]
  constructor <;> linarith

/-- **Uniform error bound for a single bump's archimedean jump energy against `w log(1/w) M(α)² ∫ β²`.** -/
theorem abs_gaugeArchJump_singleBump_sub_le (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {Bβ : ℝ} (hB : ∀ y, |β y| ≤ Bβ) (α : ℝ) {w δ ε : ℝ}
    (hw_pos : 0 < w) (hw_half : w ≤ 1 / 2) (hwδ : 2 * w < δ / 2) (hε : 0 ≤ ε)
    (hM_close : ∀ u ∈ Icc (α - δ) (α + δ), ∀ v ∈ Icc (α - δ) (α + δ), |M u * M v - M α ^ 2| ≤ ε) :
    |gaugeArchJump M (fun x => β ((x - α) / w)) -
        w * Real.log (1 / w) * (M α ^ 2 * ∫ y, β y ^ 2)| ≤
      ε * w * (Real.log (1 / w) + 4) * (∫ y, β y ^ 2) +
      (3 * (2 * C ^ 2 * Lβ * ∫ y, |β y|) +
        archLevyDensity (δ / 2) * (4 * (C ^ 2 * Bβ * ∫ y, |β y|)) +
        (4 + 2 * archLevyAntideriv (δ / 2)) * M α ^ 2 * ∫ y, β y ^ 2) * w := by
  have h2w : 0 < 2 * w := by positivity
  have hδ2 : 0 < δ / 2 := lt_trans h2w hwδ
  have hint_all := integrableOn_archLevyDensity_mul_signedShiftJump_bumpProfile
    hβc hβ hLβ hβL hM hMC {α} (fun _ => 1) hw_pos
  rw [← singleBump_eq_shiftedBumpProfile β w α] at hint_all
  have hsplit : gaugeArchJump M (fun x => β ((x - α) / w)) =
      (∫ t in Ioc 0 (2 * w), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) +
      (∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) +
      (∫ t in Ioi (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) := by
    have h1 := setIntegral_union (s := Ioc 0 (2 * w)) (t := Ioi (2 * w))
      (f := fun t => archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x)
      (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint_all.mono_set Ioc_subset_Ioi_self)
      (hint_all.mono_set (Ioi_subset_Ioi h2w.le))
    rw [Ioc_union_Ioi_eq_Ioi h2w.le] at h1
    have h2 := setIntegral_union (s := Ioc (2 * w) (δ / 2)) (t := Ioi (δ / 2))
      (f := fun t => archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x)
      (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint_all.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi h2w.le)))
      (hint_all.mono_set (Ioi_subset_Ioi hδ2.le))
    rw [Ioc_union_Ioi_eq_Ioi hwδ.le] at h2
    unfold gaugeArchJump
    rw [h1, h2, add_assoc]
  have hb1 := abs_setIntegral_Ioc_two_mul_w_le hβc hβ hLβ hβL hM hMC {α} (fun _ => 1) hw_pos hw_half
  rw [← singleBump_eq_shiftedBumpProfile β w α] at hb1
  simp only [Finset.sum_singleton, abs_one, one_pow, one_mul] at hb1
  have hb3 := abs_setIntegral_Ioi_delta_le hβc hβ hLβ hβL hM hMC hB {α} (fun _ => 1) hw_pos hδ2
  rw [← singleBump_eq_shiftedBumpProfile β w α] at hb3
  simp only [Finset.sum_singleton, abs_one, one_pow, one_mul] at hb3
  have hb2 := abs_setIntegral_Ioc_singleBump_sub_le hβc hβ hLβ hβL hM hMC α hw_pos hwδ hε hM_close
  have hΩ_low := log_one_div_le_two_mul_archLevyAntideriv hw_pos hw_half
  have hΩ_high := two_mul_archLevyAntideriv_le_log_one_div_add_four hw_pos hw_half
  have hΩδ_pos : 0 ≤ archLevyAntideriv (δ / 2) := (archLevyAntideriv_pos hδ2).le
  have hIβ_nonneg : 0 ≤ ∫ y, β y ^ 2 := integral_nonneg fun y => sq_nonneg _
  have h_ident : gaugeArchJump M (fun x => β ((x - α) / w)) - w * Real.log (1 / w) * (M α ^ 2 * ∫ y, β y ^ 2) =
      (∫ t in Ioc 0 (2 * w), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) +
      ((∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) -
        2 * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * M α ^ 2 * ∫ y, β y ^ 2) +
      (∫ t in Ioi (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) +
      w * (2 * archLevyAntideriv (2 * w) - Real.log (1 / w) - 2 * archLevyAntideriv (δ / 2)) *
        (M α ^ 2 * ∫ y, β y ^ 2) := by
    rw [hsplit]
    ring
  rw [h_ident]
  have h4_bound : |w * (2 * archLevyAntideriv (2 * w) - Real.log (1 / w) -
      2 * archLevyAntideriv (δ / 2)) * (M α ^ 2 * ∫ y, β y ^ 2)| ≤
      (4 + 2 * archLevyAntideriv (δ / 2)) * M α ^ 2 * (∫ y, β y ^ 2) * w := by
    rw [abs_mul, abs_mul, abs_of_pos hw_pos, abs_of_nonneg (mul_nonneg (sq_nonneg _) hIβ_nonneg)]
    have habs : |2 * archLevyAntideriv (2 * w) - Real.log (1 / w) - 2 * archLevyAntideriv (δ / 2)| ≤
        4 + 2 * archLevyAntideriv (δ / 2) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    calc w * |2 * archLevyAntideriv (2 * w) - Real.log (1 / w) - 2 * archLevyAntideriv (δ / 2)| *
          (M α ^ 2 * ∫ y, β y ^ 2)
        ≤ w * (4 + 2 * archLevyAntideriv (δ / 2)) * (M α ^ 2 * ∫ y, β y ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hw_pos.le)
            (mul_nonneg (sq_nonneg _) hIβ_nonneg)
      _ = (4 + 2 * archLevyAntideriv (δ / 2)) * M α ^ 2 * (∫ y, β y ^ 2) * w := by ring
  have hb2' : |(∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t *
        ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) -
      2 * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * M α ^ 2 * ∫ y, β y ^ 2| ≤
      ε * w * (Real.log (1 / w) + 4) * ∫ y, β y ^ 2 := by
    have hle : 2 * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) ≤ Real.log (1 / w) + 4 := by
      linarith
    refine hb2.trans ?_
    calc 2 * ε * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * ∫ y, β y ^ 2
        = (2 * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2))) * (ε * w * ∫ y, β y ^ 2) := by ring
      _ ≤ (Real.log (1 / w) + 4) * (ε * w * ∫ y, β y ^ 2) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (mul_nonneg hε hw_pos.le) hIβ_nonneg)
      _ = ε * w * (Real.log (1 / w) + 4) * ∫ y, β y ^ 2 := by ring
  have htri1 := abs_add_le
    ((∫ t in Ioc 0 (2 * w), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) +
      ((∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) -
        2 * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * M α ^ 2 * ∫ y, β y ^ 2) +
      (∫ t in Ioi (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x))
    (w * (2 * archLevyAntideriv (2 * w) - Real.log (1 / w) - 2 * archLevyAntideriv (δ / 2)) *
      (M α ^ 2 * ∫ y, β y ^ 2))
  have htri2 := abs_add_le
    ((∫ t in Ioc 0 (2 * w), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) +
      ((∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) -
        2 * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * M α ^ 2 * ∫ y, β y ^ 2))
    (∫ t in Ioi (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x)
  have htri3 := abs_add_le
    (∫ t in Ioc 0 (2 * w), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x)
    ((∫ t in Ioc (2 * w) (δ / 2), archLevyDensity t * ∫ x, signedShiftJump M (fun x => β ((x - α) / w)) t x) -
      2 * w * (archLevyAntideriv (2 * w) - archLevyAntideriv (δ / 2)) * M α ^ 2 * ∫ y, β y ^ 2)
  linarith

/-- **Single-bump logarithmic self-energy asymptotic.**
For a Lipschitz bump `β` supported in `[−1, 1]` and a continuous gauge `M` with
`|M x| ≤ C e^{−|x|}`,
`gaugeArchJump M (fun x => β ((x − α) / w)) / (w * log(1 / w)) → M(α)² ∫ β²` as `w → 0⁺`. -/
theorem tendsto_gaugeArchJump_singleBump_div_mul_log (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (α : ℝ) :
    Tendsto (fun w => gaugeArchJump M (fun x => β ((x - α) / w)) / (w * Real.log (1 / w)))
      (𝓝[>] 0) (𝓝 (M α ^ 2 * ∫ y, β y ^ 2)) := by
  rw [Metric.tendsto_nhds]
  intro ε₀ hε₀
  obtain ⟨Bβ, hB⟩ := exists_abs_le_of_bump hβc hβ
  have hB0 : 0 ≤ Bβ := (abs_nonneg _).trans (hB 0)
  set Iβ := ∫ y, β y ^ 2
  have hIβ_nonneg : 0 ≤ Iβ := integral_nonneg fun y => sq_nonneg _
  set ε := ε₀ / (10 * (Iβ + 1))
  have hε_pos : 0 < ε := by positivity
  have hcont_prod : ContinuousAt (fun p : ℝ × ℝ => M p.1 * M p.2) (α, α) :=
    (hM.continuousAt.comp continuousAt_fst).mul (hM.continuousAt.comp continuousAt_snd)
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.continuousAt_iff.mp hcont_prod ε hε_pos
  set δ := min (min (δ₀ / 2) 1) 1
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_one : δ ≤ 1 := min_le_right _ _
  have hM_close : ∀ u ∈ Icc (α - δ) (α + δ), ∀ v ∈ Icc (α - δ) (α + δ),
      |M u * M v - M α ^ 2| ≤ ε := by
    intro u hu v hv
    have hdist : dist (u, v) (α, α) < δ₀ := by
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      have hδ_lt : δ < δ₀ := by
        have : δ ≤ δ₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
        linarith
      exact ⟨(abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans_lt hδ_lt,
        (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩).trans_lt hδ_lt⟩
    have h := hδ₀ hdist
    simpa [Real.dist_eq, sq] using h.le
  set K₀ := 3 * (2 * C ^ 2 * Lβ * ∫ y, |β y|) +
      archLevyDensity (δ / 2) * (4 * (C ^ 2 * Bβ * ∫ y, |β y|)) +
      (4 + 2 * archLevyAntideriv (δ / 2)) * M α ^ 2 * Iβ
  set K_const := K₀ + 1
  have hK_pos : 0 < K_const := by
    have : 0 ≤ ∫ y, |β y| := integral_nonneg fun _ => abs_nonneg _
    have : 0 ≤ archLevyDensity (δ / 2) := (archLevyDensity_pos (by positivity)).le
    have : 0 ≤ archLevyAntideriv (δ / 2) := (archLevyAntideriv_pos (by positivity)).le
    dsimp [K_const, K₀]
    positivity
  set w₀ := min (δ / 6) (1 / Real.exp (2 * K_const / ε₀ + 2))
  have hw₀_pos : 0 < w₀ := by positivity
  filter_upwards [Ioo_mem_nhdsGT hw₀_pos] with w hw
  have hw_pos : 0 < w := hw.1
  have hw_lt : w < w₀ := hw.2
  have hwδ : 2 * w < δ / 2 := by
    have : w < δ / 6 := lt_of_lt_of_le hw_lt (min_le_left _ _)
    linarith
  have hw_half : w ≤ 1 / 2 := by linarith
  have hw_exp : w < 1 / Real.exp (2 * K_const / ε₀ + 2) :=
    lt_of_lt_of_le hw_lt (min_le_right _ _)
  have hlog_gt : 2 * K_const / ε₀ + 2 < Real.log (1 / w) := by
    have hexp_lt : Real.exp (2 * K_const / ε₀ + 2) < 1 / w :=
      (lt_div_iff₀ hw_pos).mpr (by
        have := (lt_div_iff₀ (Real.exp_pos _)).mp hw_exp
        linarith)
    have hlog := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rwa [Real.log_exp] at hlog
  have hlog_gt_one : 1 < Real.log (1 / w) := by
    have : 0 < 2 * K_const / ε₀ := by positivity
    linarith
  have hlog_pos : 0 < Real.log (1 / w) := by linarith
  have hmain_diff : |gaugeArchJump M (fun x => β ((x - α) / w)) -
      w * Real.log (1 / w) * (M α ^ 2 * Iβ)| ≤
      ε * w * (Real.log (1 / w) + 4) * Iβ + K_const * w := by
    have hb := abs_gaugeArchJump_singleBump_sub_le hβc hβ hLβ hβL hM hMC hB α
      hw_pos hw_half hwδ hε_pos.le hM_close
    dsimp [K_const, K₀, Iβ] at hb ⊢
    linarith
  rw [Real.dist_eq]
  have hwlog_pos : 0 < w * Real.log (1 / w) := mul_pos hw_pos hlog_pos
  have hdiv_eq : gaugeArchJump M (fun x => β ((x - α) / w)) / (w * Real.log (1 / w)) - M α ^ 2 * Iβ =
      (gaugeArchJump M (fun x => β ((x - α) / w)) - w * Real.log (1 / w) * (M α ^ 2 * Iβ)) /
        (w * Real.log (1 / w)) := by
    field_simp [hwlog_pos.ne']
  rw [hdiv_eq, abs_div, abs_of_pos hwlog_pos, div_lt_iff₀ hwlog_pos]
  have h1 : ε * (Iβ + 1) = ε₀ / 10 := by
    dsimp [ε]
    field_simp
  have h2 : ε * w * (Real.log (1 / w) + 4) * Iβ ≤ 5 * (ε * (Iβ + 1)) * (w * Real.log (1 / w)) := by
    have hlog5 : Real.log (1 / w) + 4 ≤ 5 * Real.log (1 / w) := by linarith
    have hIβ1 : Iβ ≤ Iβ + 1 := by linarith
    calc ε * w * (Real.log (1 / w) + 4) * Iβ
        = (Real.log (1 / w) + 4) * Iβ * (ε * w) := by ring
      _ ≤ (5 * Real.log (1 / w)) * (Iβ + 1) * (ε * w) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hlog5 hIβ1 hIβ_nonneg (by positivity))
            (mul_nonneg hε_pos.le hw_pos.le)
      _ = 5 * (ε * (Iβ + 1)) * (w * Real.log (1 / w)) := by ring
  have h3 : K_const * w < (ε₀ / 2) * (w * Real.log (1 / w)) := by
    have hlog_k : 2 * K_const / ε₀ < Real.log (1 / w) := by linarith
    have hk_lt : K_const < (ε₀ / 2) * Real.log (1 / w) := by
      have := (div_lt_iff₀ hε₀).mp hlog_k
      linarith
    calc K_const * w < ((ε₀ / 2) * Real.log (1 / w)) * w :=
          mul_lt_mul_of_pos_right hk_lt hw_pos
      _ = (ε₀ / 2) * (w * Real.log (1 / w)) := by ring
  have h2' : 5 * (ε * (Iβ + 1)) * (w * Real.log (1 / w)) = (ε₀ / 2) * (w * Real.log (1 / w)) := by
    rw [h1]; ring
  linarith

/-! ### Part III: Off-diagonal decoupling (`O(w)` and `O(w²)`) and multi-bump / lattice limits -/

/-- Every finite set `P : Finset ℝ` has a positive separation `s ∈ (0, 1]` between distinct points. -/
theorem exists_separation_finset (P : Finset ℝ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q → s ≤ |p - q| := by
  classical
  let D := ((P ×ˢ P).filter (fun pq : ℝ × ℝ => pq.1 ≠ pq.2)).image (fun pq : ℝ × ℝ => |pq.1 - pq.2|)
  by_cases hD : D.Nonempty
  · refine ⟨min 1 (D.min' hD), ?_, min_le_left _ _, fun p hp q hq hpq => ?_⟩
    · rw [lt_min_iff]
      refine ⟨ zero_lt_one, ?_ ⟩
      obtain ⟨pq, hpq_mem, heq⟩ := Finset.mem_image.mp (D.min'_mem hD)
      rw [← heq]
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hpq_mem).2)
    · refine (min_le_right _ _).trans (D.min'_le _ ?_)
      exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩, rfl⟩
  · refine ⟨1, zero_lt_one, le_rfl, fun p hp q hq hpq => ?_⟩
    exfalso
    exact hD ⟨|p - q|, Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩, rfl⟩⟩

/-- Uniform `O(w)` bound `|bumpPairShiftJump M β w p q t| ≤ 4 w C² B_β ∫|β|`. -/
theorem abs_bumpPairShiftJump_le_mul_w (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {M : ℝ → ℝ} {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {Bβ : ℝ} (hB : ∀ y, |β y| ≤ Bβ) (p q t : ℝ) {w : ℝ} (hw : 0 < w) :
    |bumpPairShiftJump M β w p q t| ≤ 4 * (C ^ 2 * Bβ * ∫ y, |β y|) * w := by
  have hS : ∀ z, |M z * M (z + t)| ≤ C ^ 2 := fun z => by
    have h1 := abs_mul_shift_le hMC t z
    have hexp : Real.exp (-|t|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg t])
    nlinarith [mul_le_mul_of_nonneg_left hexp (sq_nonneg C)]
  have hb := fun α α' => abs_integral_bump_pair_div_le hβc hβ (F := fun x => M x * M (x + t))
    hS hB α α' hw
  have hb1 := hb p q; rw [abs_div, abs_of_pos hw, div_le_iff₀ hw] at hb1
  have hb2 := hb p (q - t); rw [abs_div, abs_of_pos hw, div_le_iff₀ hw] at hb2
  have hb3 := hb (p - t) q; rw [abs_div, abs_of_pos hw, div_le_iff₀ hw] at hb3
  have hb4 := hb (p - t) (q - t); rw [abs_div, abs_of_pos hw, div_le_iff₀ hw] at hb4
  unfold bumpPairShiftJump
  have htri1 := abs_add_le
    ((∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w)) -
      (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w)) -
      (∫ x, M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - q) / w)))
    (∫ x, M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - (q - t)) / w))
  have htri2 := abs_sub
    ((∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w)) -
      (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w)))
    (∫ x, M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - q) / w))
  have htri3 := abs_sub
    (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w))
    (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w))
  linarith

/-- Whenever `2w < |p − q|` and `t ≥ 0` lies outside `[|p − q| − 2w, |p − q| + 2w]`,
`bumpPairShiftJump M β w p q t = 0`. -/
theorem bumpPairShiftJump_eq_zero_of_not_mem_Icc (hβ : ∀ y, 1 < |y| → β y = 0)
    (M : ℝ → ℝ) {p q w t : ℝ} (hw : 0 < w) (hpq : 2 * w < |p - q|) (ht0 : 0 ≤ t)
    (ht_not : t ∉ Icc (|p - q| - 2 * w) (|p - q| + 2 * w)) :
    bumpPairShiftJump M β w p q t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht_not
  have hgap : 2 * w < |(|p - q| - t)| := by
    rcases ht_not with h | h
    · exact lt_abs.mpr (Or.inl (by linarith))
    · exact lt_abs.mpr (Or.inr (by linarith))
  have h1 : (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - q) / w)) = 0 :=
    integral_bump_pair_eq_zero hβ (fun x => M x * M (x + t)) hw hpq
  have h2 : (∫ x, M x * M (x + t) * β ((x - p) / w) * β ((x - (q - t)) / w)) = 0 := by
    refine integral_bump_pair_eq_zero hβ (fun x => M x * M (x + t)) hw (lt_of_lt_of_le hgap ?_)
    have ha := abs_sub_abs_le_abs_sub (p - q) (-t)
    have hb := abs_sub_abs_le_abs_sub (-t) (p - q)
    rw [abs_neg, abs_of_nonneg ht0, show p - q - -t = p - (q - t) by ring] at ha
    rw [abs_neg, abs_of_nonneg ht0, show -t - (p - q) = -(p - (q - t)) by ring, abs_neg] at hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h3 : (∫ x, M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - q) / w)) = 0 := by
    refine integral_bump_pair_eq_zero hβ (fun x => M x * M (x + t)) hw (lt_of_lt_of_le hgap ?_)
    have ha := abs_sub_abs_le_abs_sub (p - q) t
    have hb := abs_sub_abs_le_abs_sub t (p - q)
    rw [abs_of_nonneg ht0, show p - q - t = p - t - q by ring] at ha
    rw [abs_of_nonneg ht0, show t - (p - q) = -(p - t - q) by ring, abs_neg] at hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h4 : (∫ x, M x * M (x + t) * β ((x - (p - t)) / w) * β ((x - (q - t)) / w)) = 0 := by
    refine integral_bump_pair_eq_zero hβ (fun x => M x * M (x + t)) hw ?_
    rw [show p - t - (q - t) = p - q by ring]
    exact hpq
  unfold bumpPairShiftJump
  rw [h1, h2, h3, h4]
  ring

/-- For distinct centres `p, q` with `s ≤ |p − q|` (`s > 0`) and `0 < w < s / 4`, the archimedean
integral of `bumpPairShiftJump M β w p q t` is bounded by `O(w²)`. -/
theorem abs_integral_archLevyDensity_mul_bumpPairShiftJump_le (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} {C : ℝ}
    (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) {Bβ : ℝ} (hB : ∀ y, |β y| ≤ Bβ)
    {p q s w : ℝ} (hs : 0 < s) (hsep : s ≤ |p - q|) (hw : 0 < w) (hws : w < s / 4) :
    |∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t| ≤
      (16 * archLevyDensity (s / 2) * (C ^ 2 * Bβ * ∫ y, |β y|)) * w ^ 2 := by
  have hs2 : 0 < s / 2 := by positivity
  have hpq : 2 * w < |p - q| := by linarith
  set g : ℝ → ℝ := fun t => if 0 < t then archLevyDensity t * bumpPairShiftJump M β w p q t else 0
  have hsupp : ∀ t, t ∉ Icc (|p - q| - 2 * w) (|p - q| + 2 * w) → g t = 0 := by
    intro t ht_not
    dsimp [g]
    split_ifs with ht0
    · rw [bumpPairShiftJump_eq_zero_of_not_mem_Icc hβ M hw hpq ht0.le ht_not, mul_zero]
    · rfl
  have hB0 : 0 ≤ Bβ := (abs_nonneg _).trans (hB 0)
  have hI0 : 0 ≤ ∫ y, |β y| := integral_nonneg fun _ => abs_nonneg _
  have hg_le : ∀ t ∈ Icc (|p - q| - 2 * w) (|p - q| + 2 * w),
      |g t| ≤ archLevyDensity (s / 2) * (4 * (C ^ 2 * Bβ * ∫ y, |β y|) * w) := by
    intro t ht_mem
    have ht_ge : s / 2 ≤ t := by linarith [ht_mem.1]
    have ht0 : 0 < t := lt_of_lt_of_le hs2 ht_ge
    dsimp [g]
    rw [if_pos ht0, abs_mul, abs_of_pos (archLevyDensity_pos ht0)]
    have hω_le : archLevyDensity t ≤ archLevyDensity (s / 2) :=
      strictAntiOn_archLevyDensity.antitoneOn hs2 ht0 ht_ge
    have hb := abs_bumpPairShiftJump_le_mul_w hβc hβ hMC hB p q t hw
    exact mul_le_mul hω_le hb (abs_nonneg _) (archLevyDensity_pos hs2).le
  have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Icc (|p - q| - 2 * w) (|p - q| + 2 * w)) (f := g)
    (C := archLevyDensity (s / 2) * (4 * (C ^ 2 * Bβ * ∫ y, |β y|) * w))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun t ht => by simpa [Real.norm_eq_abs] using hg_le t ht)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, Real.norm_eq_abs,
    Measure.real, Real.volume_Icc, show |p - q| + 2 * w - (|p - q| - 2 * w) = 4 * w by ring,
    ENNReal.toReal_ofReal (by positivity)] at hnorm
  have h_eq : (∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t) = ∫ t, g t := by
    dsimp [g]
    rw [← integral_indicator measurableSet_Ioi]
    rfl
  rw [h_eq]
  linarith

/-- **Quadratic `O(w²)` off-diagonal archimedean decoupling.**
If `∀ p ∈ P, ∀ q ∈ P, p ≠ q → s ≤ |p − q|` (`s > 0`) and `0 < w < s / 4`, then
`|gaugeArchJump M (shiftedBumpProfile β w P κ) − Σ_{p ∈ P} κ_p² gaugeArchJump M b_{p,w}|`
`≤ 16 w² · archLevyDensity (s / 2) · (Σ_{p ∈ P} |κ_p|)² · C² B_β ∫|β|`. -/
theorem abs_gaugeArchJump_sub_sum_singleBump_le (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0)
    {Lβ : ℝ} (hLβ : 0 ≤ Lβ) (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|)
    {M : ℝ → ℝ} (hM : Continuous M) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {Bβ : ℝ} (hB : ∀ y, |β y| ≤ Bβ) (P : Finset ℝ) (κ : ℝ → ℝ) {s w : ℝ}
    (hs : 0 < s) (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → s ≤ |p - q|)
    (hw : 0 < w) (hws : w < s / 4) :
    |gaugeArchJump M (shiftedBumpProfile β w P κ) -
        ∑ p ∈ P, κ p ^ 2 * gaugeArchJump M (fun x => β ((x - p) / w))| ≤
      (16 * archLevyDensity (s / 2) * (∑ p ∈ P, |κ p|) ^ 2 * (C ^ 2 * Bβ * ∫ y, |β y|)) * w ^ 2 := by
  have hint_pair : ∀ p q : ℝ, IntegrableOn
      (fun t => archLevyDensity t * bumpPairShiftJump M β w p q t) (Ioi 0) := by
    intro p q
    set K := 2 * C ^ 2 * Lβ * ∫ y, |β y|
    have hmaj : IntegrableOn (fun t => K * (archLevyDensity t * t)) (Ioi 0) :=
      integrableOn_archLevyDensity_mul_id.const_mul K
    have hcont : Continuous (fun t => bumpPairShiftJump M β w p q t) := by
      have heq : (fun t => bumpPairShiftJump M β w p q t) =
          fun t => (∫ x, M x * M (x + t) * β ((x - (p - 0 * t)) / w) * β ((x - (q - 0 * t)) / w)) -
            (∫ x, M x * M (x + t) * β ((x - (p - 0 * t)) / w) * β ((x - (q - 1 * t)) / w)) -
            (∫ x, M x * M (x + t) * β ((x - (p - 1 * t)) / w) * β ((x - (q - 0 * t)) / w)) +
            ∫ x, M x * M (x + t) * β ((x - (p - 1 * t)) / w) * β ((x - (q - 1 * t)) / w) := by
        funext t
        simp [bumpPairShiftJump]
      rw [heq]
      exact (((continuous_integral_bumpPair_shift hβc hβ hM p q 0 0 hw).sub
        (continuous_integral_bumpPair_shift hβc hβ hM p q 0 1 hw)).sub
        (continuous_integral_bumpPair_shift hβc hβ hM p q 1 0 hw)).add
        (continuous_integral_bumpPair_shift hβc hβ hM p q 1 1 hw)
    refine hmaj.mono' (measurable_archLevyDensity.mul hcont.measurable).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hω : 0 < archLevyDensity t := archLevyDensity_pos ht0
    have hb := abs_bumpPairShiftJump_le_mul_t hβc hβ hLβ hβL hM hMC p q hw ht0.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hω]
    calc archLevyDensity t * |bumpPairShiftJump M β w p q t|
        ≤ archLevyDensity t * (K * t) := mul_le_mul_of_nonneg_left hb hω.le
      _ = K * (archLevyDensity t * t) := by ring
  have h_expand : gaugeArchJump M (shiftedBumpProfile β w P κ) =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t := by
    unfold gaugeArchJump
    have hcongr : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
          ∫ x, signedShiftJump M (shiftedBumpProfile β w P κ) t x) =
        ∫ t in Ioi (0 : ℝ), ∑ p ∈ P, ∑ q ∈ P,
          (κ p * κ q) * (archLevyDensity t * bumpPairShiftJump M β w p q t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [integral_signedShiftJump_eq_sum_bumpPairShiftJump hβc hβ hM P κ t hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hcongr, integral_finsetSum P fun p _ =>
      integrable_finsetSum P fun q _ => (hint_pair p q).const_mul _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum P fun q _ => (hint_pair p q).const_mul _]
    exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
  have h_diag : ∀ p : ℝ, gaugeArchJump M (fun x => β ((x - p) / w)) =
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p p t := fun p => by
    unfold gaugeArchJump
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [bumpPairShiftJump_diag hβc hβ hM p t hw]
  have h_diff : gaugeArchJump M (shiftedBumpProfile β w P κ) -
      ∑ p ∈ P, κ p ^ 2 * gaugeArchJump M (fun x => β ((x - p) / w)) =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        (if p = q then 0 else ∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t) := by
    rw [h_expand]
    have h_sum_diag : ∑ p ∈ P, κ p ^ 2 * gaugeArchJump M (fun x => β ((x - p) / w)) =
        ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
          (if p = q then ∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t else 0) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [h_diag p]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, if_pos hp]
      ring
    rw [h_sum_diag, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> ring
  rw [h_diff]
  have hB0 : 0 ≤ Bβ := (abs_nonneg _).trans (hB 0)
  have hI0 : 0 ≤ ∫ y, |β y| := integral_nonneg fun _ => abs_nonneg _
  have hωs : 0 ≤ archLevyDensity (s / 2) := (archLevyDensity_pos (by positivity)).le
  calc |∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
          (if p = q then 0 else ∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t)|
      ≤ ∑ p ∈ P, |∑ q ∈ P, κ p * κ q *
          (if p = q then 0 else ∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, |κ p * κ q *
          (if p = q then 0 else ∫ t in Ioi (0 : ℝ), archLevyDensity t * bumpPairShiftJump M β w p q t)| :=
        Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, |κ p| * |κ q| *
          ((16 * archLevyDensity (s / 2) * (C ^ 2 * Bβ * ∫ y, |β y|)) * w ^ 2) := by
        refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
        rw [abs_mul, abs_mul]
        split_ifs with hpq
        · rw [abs_zero, mul_zero]; positivity
        · exact mul_le_mul_of_nonneg_left
            (abs_integral_archLevyDensity_mul_bumpPairShiftJump_le hβc hβ hMC hB hs
              (hsep p hp q hq hpq) hw hws)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (16 * archLevyDensity (s / 2) * (∑ p ∈ P, |κ p|) ^ 2 * (C ^ 2 * Bβ * ∫ y, |β y|)) * w ^ 2 := by
        have h_eq : (16 * archLevyDensity (s / 2) * (∑ p ∈ P, |κ p|) ^ 2 * (C ^ 2 * Bβ * ∫ y, |β y|)) * w ^ 2 =
            (∑ p ∈ P, |κ p|) ^ 2 * ((16 * archLevyDensity (s / 2) * (C ^ 2 * Bβ * ∫ y, |β y|)) * w ^ 2) := by ring
        rw [h_eq, pow_two (∑ p ∈ P, |κ p|), Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]

/-- **Off-diagonal archimedean decoupling at scale `w`.**
`(gaugeArchJump M (shiftedBumpProfile β w P κ) − Σ_{p ∈ P} κ_p² gaugeArchJump M b_{p,w}) / w → 0`
as `w → 0⁺`. -/
theorem tendsto_gaugeArchJump_sub_sum_singleBump_div (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (P : Finset ℝ) (κ : ℝ → ℝ) :
    Tendsto (fun w => (gaugeArchJump M (shiftedBumpProfile β w P κ) -
        ∑ p ∈ P, κ p ^ 2 * gaugeArchJump M (fun x => β ((x - p) / w))) / w)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Bβ, hB⟩ := exists_abs_le_of_bump hβc hβ
  obtain ⟨s, hs, _, hsep⟩ := exists_separation_finset P
  set K := 16 * archLevyDensity (s / 2) * (∑ p ∈ P, |κ p|) ^ 2 * (C ^ 2 * Bβ * ∫ y, |β y|)
  have hlim : Tendsto (fun w : ℝ => K * w) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun w : ℝ => K * w) := continuous_const.mul continuous_id
    simpa [mul_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim_neg : Tendsto (fun w : ℝ => -(K * w)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_neg hlim ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < s / 4 by positivity)] with w hw
    have hb := abs_gaugeArchJump_sub_sum_singleBump_le hβc hβ hLβ hβL hM hMC hB P κ hs hsep
      hw.1 hw.2
    have hdiv : |(gaugeArchJump M (shiftedBumpProfile β w P κ) -
        ∑ p ∈ P, κ p ^ 2 * gaugeArchJump M (fun x => β ((x - p) / w))) / w| ≤ K * w := by
      rw [abs_div, abs_of_pos hw.1, div_le_iff₀ hw.1, mul_assoc, ← sq]
      exact hb
    exact (abs_le.mp hdiv).1
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < s / 4 by positivity)] with w hw
    have hb := abs_gaugeArchJump_sub_sum_singleBump_le hβc hβ hLβ hβL hM hMC hB P κ hs hsep
      hw.1 hw.2
    have hdiv : |(gaugeArchJump M (shiftedBumpProfile β w P κ) -
        ∑ p ∈ P, κ p ^ 2 * gaugeArchJump M (fun x => β ((x - p) / w))) / w| ≤ K * w := by
      rw [abs_div, abs_of_pos hw.1, div_le_iff₀ hw.1, mul_assoc, ← sq]
      exact hb
    exact (abs_le.mp hdiv).2

/-- `(Real.log (1 / w))⁻¹ → 0` as `w → 0⁺`. -/
theorem tendsto_inv_log_one_div_nhdsGT_zero :
    Tendsto (fun w : ℝ => (Real.log (1 / w))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set w₀ := 1 / Real.exp (1 / ε + 1)
  have hw₀_pos : 0 < w₀ := by positivity
  filter_upwards [Ioo_mem_nhdsGT hw₀_pos] with w hw
  have hw_pos : 0 < w := hw.1
  have hexp_lt : Real.exp (1 / ε + 1) < 1 / w :=
    (lt_div_iff₀ hw_pos).mpr (by
      have := (lt_div_iff₀ (Real.exp_pos _)).mp hw.2
      linarith)
  have hlog : 1 / ε + 1 < Real.log (1 / w) := by
    have h := Real.log_lt_log (Real.exp_pos _) hexp_lt
    rwa [Real.log_exp] at h
  have hlog_pos : 0 < Real.log (1 / w) := by
    have : 0 < 1 / ε := by positivity
    linarith
  rw [Real.dist_eq, sub_zero, abs_inv, abs_of_pos hlog_pos, inv_lt_comm₀ hlog_pos hε, ← one_div]
  linarith

/-- If `f w / w → L` as `w → 0⁺`, then `f w / (w * log(1/w)) → 0` as `w → 0⁺`. -/
theorem tendsto_div_mul_log_zero_of_tendsto_div {f : ℝ → ℝ} {L : ℝ}
    (hf : Tendsto (fun w => f w / w) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun w => f w / (w * Real.log (1 / w))) (𝓝[>] 0) (𝓝 0) := by
  have h := hf.mul tendsto_inv_log_one_div_nhdsGT_zero
  rw [mul_zero] at h
  refine h.congr (fun w => ?_)
  ring

/-- **Multi-bump logarithmic self-energy asymptotic for `gaugeArchJump`.**
For a Lipschitz bump `β` supported in `[−1, 1]` and a continuous gauge `M` with `|M x| ≤ C e^{−|x|}`,
`gaugeArchJump M (shiftedBumpProfile β w P κ) / (w * log(1 / w)) → (∫ β²) Σ_{p ∈ P} κ_p² M(p)²`. -/
theorem tendsto_gaugeArchJump_bumpProfile_div_mul_log (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (P : Finset ℝ) (κ : ℝ → ℝ) :
    Tendsto (fun w => gaugeArchJump M (shiftedBumpProfile β w P κ) / (w * Real.log (1 / w)))
      (𝓝[>] 0) (𝓝 ((∫ y, β y ^ 2) * ∑ p ∈ P, κ p ^ 2 * M p ^ 2)) := by
  have hdiff := tendsto_div_mul_log_zero_of_tendsto_div
    (tendsto_gaugeArchJump_sub_sum_singleBump_div hβc hβ hLβ hβL hM hMC P κ)
  have hsum : Tendsto (fun w => (∑ p ∈ P, κ p ^ 2 *
        gaugeArchJump M (fun x => β ((x - p) / w))) / (w * Real.log (1 / w)))
      (𝓝[>] 0) (𝓝 ((∫ y, β y ^ 2) * ∑ p ∈ P, κ p ^ 2 * M p ^ 2)) := by
    have heq : (fun w => (∑ p ∈ P, κ p ^ 2 *
          gaugeArchJump M (fun x => β ((x - p) / w))) / (w * Real.log (1 / w))) =
        fun w => ∑ p ∈ P, κ p ^ 2 *
          (gaugeArchJump M (fun x => β ((x - p) / w)) / (w * Real.log (1 / w))) := by
      funext w
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun p _ => mul_div_assoc _ _ _
    rw [heq]
    have htarget : (∫ y, β y ^ 2) * ∑ p ∈ P, κ p ^ 2 * M p ^ 2 =
        ∑ p ∈ P, κ p ^ 2 * (M p ^ 2 * ∫ y, β y ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [htarget]
    exact tendsto_finsetSum P fun p _ =>
      (tendsto_gaugeArchJump_singleBump_div_mul_log hβc hβ hLβ hβL hM hMC p).const_mul (κ p ^ 2)
  have hcomb := hdiff.add hsum
  rw [zero_add] at hcomb
  refine hcomb.congr' (Eventually.of_forall fun w => ?_)
  dsimp
  ring

/-- **Lattice logarithmic self-energy asymptotic for `gaugeArchJump`.**
For an odd (or even) gauge `M` satisfying `M(−x)² = M(x)²` and `|M x| ≤ C e^{−|x|}`, and `S ⊆ {a ≥ 2}`,
`gaugeArchJump M (latticeBumpProfile β w S c) / (w * log(1 / w))`
`→ 2 (∫ β²) Σ_{a ∈ S} c_a² M(log a)²`. -/
theorem tendsto_gaugeArchJump_latticeBumpProfile_div_mul_log (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    (hodd : ∀ x, M (-x) = -M x) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a) (c : ℕ → ℝ) :
    Tendsto (fun w => gaugeArchJump M (latticeBumpProfile β w S c) / (w * Real.log (1 / w)))
      (𝓝[>] 0) (𝓝 (2 * (∫ y, β y ^ 2) * ∑ a ∈ S, c a ^ 2 * M (Real.log a) ^ 2)) := by
  simp_rw [latticeBumpProfile_eq hS]
  convert tendsto_gaugeArchJump_bumpProfile_div_mul_log hβc hβ hLβ hβL hM hMC
    (latticeCentres S) (latticeCoeff c) using 2
  rw [sum_latticeCentres hS]
  have hsum : ∑ a ∈ S, (latticeCoeff c (Real.log a) ^ 2 * M (Real.log a) ^ 2 +
        latticeCoeff c (-Real.log a) ^ 2 * M (-Real.log a) ^ 2) =
      2 * ∑ a ∈ S, c a ^ 2 * M (Real.log a) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := by linarith [hS a ha]
    rw [latticeCoeff_log c ha1, latticeCoeff_neg_log c ha1, hodd]
    ring
  rw [hsum]
  ring

/-- **Multi-bump logarithmic self-energy asymptotic for the total `signedJumpEnergy`.**
Since `gaugePrimeJump M u_w = O(w) = o(w log(1/w))`, the full signed jump energy `J_M(u_w)` has the
same `w log(1/w)` asymptotic as its archimedean part. -/
theorem tendsto_signedJumpEnergy_bumpProfile_div_mul_log (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (P : Finset ℝ) (κ : ℝ → ℝ) :
    Tendsto (fun w => signedJumpEnergy M (shiftedBumpProfile β w P κ) / (w * Real.log (1 / w)))
      (𝓝[>] 0) (𝓝 ((∫ y, β y ^ 2) * ∑ p ∈ P, κ p ^ 2 * M p ^ 2)) := by
  have harch := tendsto_gaugeArchJump_bumpProfile_div_mul_log hβc hβ hLβ hβL hM hMC P κ
  have hprime := tendsto_div_mul_log_zero_of_tendsto_div
    (tendsto_gaugePrimeJump_bumpProfile hβc hβ hM hMC P κ)
  have hcomb := harch.add hprime
  rw [add_zero] at hcomb
  refine hcomb.congr' (Eventually.of_forall fun w => ?_)
  dsimp
  rw [signedJumpEnergy_eq_gaugeArchJump_add_gaugePrimeJump, add_div]

/-- **Lattice logarithmic self-energy asymptotic for the total `signedJumpEnergy`.** -/
theorem tendsto_signedJumpEnergy_latticeBumpProfile_div_mul_log (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    (hodd : ∀ x, M (-x) = -M x) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a) (c : ℕ → ℝ) :
    Tendsto (fun w => signedJumpEnergy M (latticeBumpProfile β w S c) / (w * Real.log (1 / w)))
      (𝓝[>] 0) (𝓝 (2 * (∫ y, β y ^ 2) * ∑ a ∈ S, c a ^ 2 * M (Real.log a) ^ 2)) := by
  simp_rw [latticeBumpProfile_eq hS]
  convert tendsto_signedJumpEnergy_bumpProfile_div_mul_log hβc hβ hLβ hβL hM hMC
    (latticeCentres S) (latticeCoeff c) using 2
  rw [sum_latticeCentres hS]
  have hsum : ∑ a ∈ S, (latticeCoeff c (Real.log a) ^ 2 * M (Real.log a) ^ 2 +
        latticeCoeff c (-Real.log a) ^ 2 * M (-Real.log a) ^ 2) =
      2 * ∑ a ∈ S, c a ^ 2 * M (Real.log a) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := by linarith [hS a ha]
    rw [latticeCoeff_log c ha1, latticeCoeff_neg_log c ha1, hodd]
    ring
  rw [hsum]
  ring

/-- **Calibrated total `signedJumpEnergy` bridge at scale `w` on general bump profiles.**
Subtracting the single-packet archimedean self-energies `Σ_{p ∈ P} κ_p² gaugeArchJump M b_{p,w}`
from `signedJumpEnergy M (shiftedBumpProfile β w P κ)` cancels the `w log(1/w)` diagonal and the
`O(w²)` off-diagonal archimedean terms, so dividing by `w` recovers the exact prime incidence limit. -/
theorem tendsto_calibratedSignedJumpEnergy_bumpProfile_div (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|)) (P : Finset ℝ) (κ : ℝ → ℝ) :
    Tendsto (fun w => (signedJumpEnergy M (shiftedBumpProfile β w P κ) -
        ∑ p ∈ P, κ p ^ 2 * gaugeArchJump M (fun x => β ((x - p) / w))) / w)
      (𝓝[>] 0)
      (𝓝 ((∫ y, β y ^ 2) * (∑ p ∈ P, κ p ^ 2 * (M p * primeGaugeGenerator M p) -
        ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * (M p * M q) *
          (primeAtomAtGap (q - p) + primeAtomAtGap (p - q))))) := by
  have harch := tendsto_gaugeArchJump_sub_sum_singleBump_div hβc hβ hLβ hβL hM hMC P κ
  have hprime := tendsto_gaugePrimeJump_bumpProfile hβc hβ hM hMC P κ
  have hcomb := harch.add hprime
  rw [zero_add] at hcomb
  refine hcomb.congr' (Eventually.of_forall fun w => ?_)
  dsimp
  rw [signedJumpEnergy_eq_gaugeArchJump_add_gaugePrimeJump]
  ring

/-- **Calibrated total `signedJumpEnergy` bridge at scale `w` on even lattice bump profiles.**
Subtracting the single-packet archimedean self-energies from `signedJumpEnergy M (latticeBumpProfile β w S c)`
and dividing by `w` converges to the exact prime incidence quadratic form in `netAtom`:
`∫β² · (2 Σ_a c_a² M(log a) 𝒢(M)(log a) − 4 Σ_{a<b} c_a c_b M(log a) M(log b) netAtom(a,b)`
`− 2 Σ_a c_a² M(log a)² netAtom(a,a))`. -/
theorem tendsto_calibratedSignedJumpEnergy_latticeBumpProfile_netAtom (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {Lβ : ℝ} (hLβ : 0 ≤ Lβ)
    (hβL : ∀ y₁ y₂, |β y₁ - β y₂| ≤ Lβ * |y₁ - y₂|) {M : ℝ → ℝ} (hM : Continuous M)
    (hodd : ∀ x, M (-x) = -M x) {C : ℝ} (hMC : ∀ x, |M x| ≤ C * Real.exp (-|x|))
    {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a) (c : ℕ → ℝ) :
    Tendsto (fun w => (signedJumpEnergy M (latticeBumpProfile β w S c) -
        ∑ p ∈ latticeCentres S, latticeCoeff c p ^ 2 *
          gaugeArchJump M (fun x => β ((x - p) / w))) / w)
      (𝓝[>] 0)
      (𝓝 ((∫ y, β y ^ 2) * (2 * ∑ a ∈ S, c a ^ 2 * (M (Real.log a) * primeGaugeGenerator M (Real.log a)) -
        4 * ∑ a ∈ S, ∑ b ∈ S, (if a < b then
          c a * c b * (M (Real.log a) * M (Real.log b)) * netAtom a b else 0) -
        2 * ∑ a ∈ S, c a ^ 2 * M (Real.log a) ^ 2 * netAtom a a))) := by
  have harch : Tendsto (fun w => (gaugeArchJump M (latticeBumpProfile β w S c) -
        ∑ p ∈ latticeCentres S, latticeCoeff c p ^ 2 *
          gaugeArchJump M (fun x => β ((x - p) / w))) / w)
      (𝓝[>] 0) (𝓝 0) := by
    simp_rw [latticeBumpProfile_eq hS]
    exact tendsto_gaugeArchJump_sub_sum_singleBump_div hβc hβ hLβ hβL hM hMC
      (latticeCentres S) (latticeCoeff c)
  have hprime := tendsto_gaugePrimeJump_latticeBumpProfile_netAtom hβc hβ hM hodd hMC hS c
  have hcomb := harch.add hprime
  rw [zero_add] at hcomb
  refine hcomb.congr' (Eventually.of_forall fun w => ?_)
  dsimp
  rw [signedJumpEnergy_eq_gaugeArchJump_add_gaugePrimeJump]
  ring

/-- **Ground-state source potential bridge at scale `w` (`∫ u_w(x)² W(x) dx / w`).**
For any continuous weight `W : ℝ → ℝ` (in particular `W(x) = M(x) g(x)` in the ground-state
representation `markovEnergy(Φ(ω u)) = J_M(u) + ∫ u² M g`),
`(∫ x, shiftedBumpProfile β w P κ x ^ 2 * W x) / w → (∫ β²) Σ_{p ∈ P} κ_p² W(p)`. -/
theorem tendsto_integral_sq_bumpProfile_mul_div (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {W : ℝ → ℝ} (hW : Continuous W)
    (P : Finset ℝ) (κ : ℝ → ℝ) :
    Tendsto (fun w => (∫ x, shiftedBumpProfile β w P κ x ^ 2 * W x) / w)
      (𝓝[>] 0) (𝓝 ((∫ y, β y ^ 2) * ∑ p ∈ P, κ p ^ 2 * W p)) := by
  have hJ := fun p q => tendsto_integral_bump_pair_div hβc hβ hW p q
  have heq : ∀ᶠ w in 𝓝[>] (0 : ℝ),
      (∫ x, shiftedBumpProfile β w P κ x ^ 2 * W x) / w =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q *
        ((∫ x, W x * β ((x - p) / w) * β ((x - q) / w)) / w) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : 0 < w := hw
    have hbump : ∀ α : ℝ, HasCompactSupport (fun x => β ((x - α) / w)) := fun α => by
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := α - w) (b := α + w)) ?_
      intro x hx
      by_contra hmem
      have : 1 < |(x - α) / w| := by
        rw [abs_div, abs_of_pos hw', lt_div_iff₀ hw', one_mul]
        rw [mem_Icc, not_and_or, not_le, not_le] at hmem
        rcases hmem with h | h
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl (by linarith))
      exact hx (hβ _ this)
    have hint : ∀ p q : ℝ, Integrable (fun x => κ p * κ q *
        (W x * β ((x - p) / w) * β ((x - q) / w))) :=
      fun p q => (Continuous.integrable_of_hasCompactSupport (by fun_prop)
        ((hbump q).mul_left)).const_mul _
    have hpt : (fun x => shiftedBumpProfile β w P κ x ^ 2 * W x) =
        fun x => ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * (W x * β ((x - p) / w) * β ((x - q) / w)) := by
      funext x
      unfold shiftedBumpProfile
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hpt, integral_finsetSum P fun p _ => integrable_finsetSum P fun q _ => hint p q,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum P fun q _ => hint p q, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_const_mul, mul_div_assoc]
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  have htarget : (∫ y, β y ^ 2) * ∑ p ∈ P, κ p ^ 2 * W p =
      ∑ p ∈ P, ∑ q ∈ P, κ p * κ q * (if p = q then W p * ∫ y, β y ^ 2 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, if_pos hp]
    ring
  rw [htarget]
  exact tendsto_finsetSum P fun p _ => tendsto_finsetSum P fun q _ =>
    (hJ p q).const_mul (κ p * κ q)

/-- **Lattice ground-state source potential bridge at scale `w` (`∫ u_w(x)² W(x) dx / w`).**
For an even continuous weight `W` (`W (−x) = W x`) and `S ⊆ {a ≥ 2}`,
`(∫ x, latticeBumpProfile β w S c x ^ 2 * W x) / w → 2 (∫ β²) Σ_{a ∈ S} c_a² W(log a)`. -/
theorem tendsto_integral_sq_latticeBumpProfile_mul_div (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {W : ℝ → ℝ} (hW : Continuous W)
    (heven : ∀ x, W (-x) = W x) {S : Finset ℕ} (hS : ∀ a ∈ S, 2 ≤ a) (c : ℕ → ℝ) :
    Tendsto (fun w => (∫ x, latticeBumpProfile β w S c x ^ 2 * W x) / w)
      (𝓝[>] 0) (𝓝 (2 * (∫ y, β y ^ 2) * ∑ a ∈ S, c a ^ 2 * W (Real.log a))) := by
  simp_rw [latticeBumpProfile_eq hS]
  convert tendsto_integral_sq_bumpProfile_mul_div hβc hβ hW
    (latticeCentres S) (latticeCoeff c) using 2
  rw [sum_latticeCentres hS]
  have hsum : ∑ a ∈ S, (latticeCoeff c (Real.log a) ^ 2 * W (Real.log a) +
        latticeCoeff c (-Real.log a) ^ 2 * W (-Real.log a)) =
      2 * ∑ a ∈ S, c a ^ 2 * W (Real.log a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a := by linarith [hS a ha]
    rw [latticeCoeff_log c ha1, latticeCoeff_neg_log c ha1, heven]
    ring
  rw [hsum]
  ring

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
