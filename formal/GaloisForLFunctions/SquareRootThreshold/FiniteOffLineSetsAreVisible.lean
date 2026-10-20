import GaloisForLFunctions.SquareRootThreshold.EqualDepthClusterInArbitraryBackground
import GaloisForLFunctions.RHTower.LandauPairTest

/-!
# Finite off-line sets are visible at a logarithmic aperture

Let the off-line zeros of a tempered configuration form a finite set, `T` the ones right of the
critical line, with depths `δ_t = Re t − ½` and multiplicities `m_t`. The on-line zeros are
arbitrary. For a bump `b` the lag structure splits into an on-line part, bounded by the on-line
mass `M_b`, and the exponential polynomial

`2 Σ_{t∈T} e^{iγ_t v} (q_t e^{δ_t v} + q̄_t e^{−δ_t v})`,  `q_t = m_t h_b(γ_t − iδ_t) conj h_b(γ_t + iδ_t)`.

* **Lag criterion** (`finiteOffLine_lagStructure_gt`). If
  `|Σ_t q_t e^{δ_t v} e^{iγ_t v}| > 2M_b + 3Σ_t |q_t|`, the two-point minor fails at lag `v`.
* **Visibility, uniform in the background** (`finiteOffLine_visible`). Let the largest depth `D`
  be attained at `t₀` and let `g ∈ (0, D]` be a gap: every other depth is at most `D − g`. With
  `b = κ_w` modulated to the height of `t₀` there are `c, ℓ > 0`, depending only on `T`, the
  multiplicities and `w`, such that every tempered configuration with these off-line zeros is
  visible at every aperture

  `a ≥ (1/2g) log⁺((2M_b + 4Σ_t |q_t|)/c) + (|T| + 2)ℓ/2 + w`.

  The on-line zeros enter only through `log M_b`. The top level cannot cancel itself away: its
  phase sum is bounded below on every `|T|` consecutive grid lags
  (`exists_weighted_powerSum_window_lower`). The lower levels lose a factor `e^{−gv}`, and the
  modulated bump makes the weight of `t₀` nonzero. The underlying statement
  (`finiteOffLine_minor_fails`) holds for any bump whose weight at `t₀` is nonzero, with the gap
  required only at points of nonzero weight: it is a failed two-point minor at a lag `v` with
  `v/2 + w ≤ a`.

For `ξ`, `RHTower.exists_pow_integerLag_gt_of_finite_offLine` detects finite off-line sets
through the global lag function. Here detection happens at a finite aperture, uniformly over the
on-line background.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- The lag summand of a zero `z`. -/
def lagTerm (Z : ZeroConfig) (b : ℝ → ℂ) (v : ℝ) (z : ℂ) : ℂ :=
  (Z.mult z : ℂ) * paperFT (EF.weilTest b b) (gammaOf z) * cexp (I * gammaOf z * v)

/-- The weight `q_t = m h_b(γ_t − iδ_t) conj h_b(γ_t + iδ_t)` of an off-line pair. -/
def offLineWeight (b : ℝ → ℂ) (m : ℕ) (t : ℂ) : ℂ := (m : ℂ) * pairWeight b (t.re - 1 / 2) t.im

theorem eq_heightPoint (t : ℂ) : t = heightPoint (t.re - 1 / 2) t.im := by
  apply Complex.ext <;> simp [heightPoint]

theorem reflect_eq_heightPoint (t : ℂ) : reflect t = heightPoint (-(t.re - 1 / 2)) t.im := by
  apply Complex.ext
  · simp [heightPoint, reflect]; ring
  · simp [heightPoint, reflect]

/-- **The pair terms.** A zero `t` and its reflection contribute
`2 e^{iγv}(q e^{δv} + q̄ e^{−δv})` to `S(v) + conj S(−v)` and `q + q̄` to `S(0)`. -/
theorem pair_lagTerm {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b) (Z : ZeroConfig)
    {t : ℂ} (ht : t ∈ Z.carrier) (v : ℝ) :
    (lagTerm Z b v t + lagTerm Z b v (reflect t)) +
        conj (lagTerm Z b (-v) t + lagTerm Z b (-v) (reflect t)) =
      2 * cexp (I * t.im * v) *
        (offLineWeight b (Z.mult t) t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) +
          conj (offLineWeight b (Z.mult t) t) * (Real.exp (-((t.re - 1 / 2) * v)) : ℂ)) ∧
    lagTerm Z b 0 t + lagTerm Z b 0 (reflect t) =
      offLineWeight b (Z.mult t) t + conj (offLineWeight b (Z.mult t) t) := by
  have hm : Z.mult (reflect t) = Z.mult t := Z.mult_reflect t ht
  have e : ∀ v : ℝ, lagTerm Z b v t = (Z.mult t : ℂ) *
      (pairWeight b (t.re - 1 / 2) t.im * cexp (I * ((t.im : ℂ) - I * (t.re - 1 / 2 : ℝ)) * v)) ∧
      lagTerm Z b v (reflect t) = (Z.mult t : ℂ) * (conj (pairWeight b (t.re - 1 / 2) t.im) *
        cexp (I * ((t.im : ℂ) - I * (-(t.re - 1 / 2) : ℝ)) * v)) := by
    intro v
    obtain ⟨h1, h2⟩ := pair_summand hb hbc t.im (t.re - 1 / 2) v
    rw [← eq_heightPoint t] at h1
    rw [← reflect_eq_heightPoint t] at h2
    refine ⟨?_, ?_⟩
    · rw [lagTerm, mul_assoc, h1]
    · rw [lagTerm, hm, mul_assoc, h2]
  have hpl := pair_lag_identity (pairWeight b (t.re - 1 / 2) t.im) t.im (t.re - 1 / 2) v
  refine ⟨?_, ?_⟩
  · rw [(e v).1, (e v).2, (e (-v)).1, (e (-v)).2, offLineWeight]
    simp only [map_add, map_mul, Complex.conj_natCast, Complex.conj_conj] at hpl ⊢
    linear_combination (Z.mult t : ℂ) * hpl
  · rw [(e 0).1, (e 0).2, offLineWeight, map_mul, Complex.conj_natCast]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-- **Splitting the lag structure.** If `T` is the set of zeros right of the line, then
`S(v)` is the on-line part plus the finite sum of pair terms over `T`. -/
theorem lagStructure_split (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {T : Finset ℂ}
    (hT : ∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) (v : ℝ) :
    lagStructure Z b v =
      (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0) +
        ∑ t ∈ T, (lagTerm Z b v t + lagTerm Z b v (reflect t)) := by
  classical
  have hF : Summable fun ρ : Z.carrier => lagTerm Z b v ρ := summable_lagStructure Z hZ hb hbs v
  have hR : Summable fun ρ : Z.carrier => if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0 :=
    Summable.of_norm_bounded hF.norm fun ρ => by split_ifs <;> simp
  have hO : Summable fun ρ : Z.carrier => if (ρ : ℂ).re = 1 / 2 then 0 else lagTerm Z b v ρ :=
    Summable.of_norm_bounded hF.norm fun ρ => by split_ifs <;> simp
  have hre : ∀ z : ℂ, (reflect z).re = 1 - z.re := fun z => by simp [reflect]
  have hdisj : Disjoint T (T.image reflect) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz'
    have h1 := ((hT _).mp hz).2
    have h2 := ((hT _).mp ht).2
    rw [hre] at h1
    linarith
  have hoff : (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then 0 else lagTerm Z b v ρ) =
      ∑ t ∈ T, (lagTerm Z b v t + lagTerm Z b v (reflect t)) := by
    rw [tsum_subtype Z.carrier fun z => if z.re = 1 / 2 then 0 else lagTerm Z b v z,
      tsum_eq_sum (s := T ∪ T.image reflect) fun z hz => ?_]
    · rw [Finset.sum_union hdisj, Finset.sum_image fun x _ y _ h => by
        rw [← Zeta23.reflect_reflect x, h, Zeta23.reflect_reflect], ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      obtain ⟨htc, htre⟩ := (hT t).mp ht
      have h1 : t.re ≠ 1 / 2 := by linarith
      have h2 : (reflect t).re ≠ 1 / 2 := by rw [hre]; linarith
      rw [Set.indicator_of_mem htc, Set.indicator_of_mem (Z.reflect_mem t htc), if_neg h1,
        if_neg h2]
    · rw [Finset.mem_union, not_or, Finset.mem_image] at hz
      by_cases hc : z ∈ Z.carrier
      · rw [Set.indicator_of_mem hc]
        rcases lt_trichotomy z.re (1 / 2) with h | h | h
        · exfalso
          refine hz.2 ⟨reflect z, (hT _).mpr ⟨Z.reflect_mem z hc, ?_⟩, Zeta23.reflect_reflect z⟩
          rw [hre]; linarith
        · rw [if_pos h]
        · exact absurd ((hT z).mpr ⟨hc, h⟩) hz.1
      · exact Set.indicator_of_notMem hc _
  rw [lagStructure, show (∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (EF.weilTest b b)
      (gammaOf ρ) * cexp (I * gammaOf ρ * v)) = ∑' ρ : Z.carrier, lagTerm Z b v ρ from rfl,
    ← hoff, ← Summable.tsum_add hR hO]
  exact tsum_congr fun ρ => by split_ifs <;> simp

/-- **The on-line part.** It contributes at most `2M_b` to `|S(v) + conj S(−v)|` and exactly
`M_b` to `Re S(0)`. -/
theorem onLinePart_bounds (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    ‖(∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0) +
        conj (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b (-v) ρ else 0)‖ ≤
      2 * onLineMassOf Z b ∧
    (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b 0 ρ else 0).re =
      onLineMassOf Z b := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set R : ℝ → Z.carrier → ℂ := fun v ρ =>
    if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0 with hR
  have hRs : ∀ v, Summable (R v) := fun v =>
    Summable.of_norm_bounded (summable_lagStructure Z hZ hb hbs v).norm fun ρ => by
      simp only [hR]
      split_ifs
      · exact le_rfl
      · rw [norm_zero]; exact norm_nonneg _
  set R₀ : Z.carrier → ℝ := fun ρ => if (ρ : ℂ).re = 1 / 2 then
    (Z.mult ρ : ℝ) * ‖paperFT b (gammaOf ρ)‖ ^ 2 else 0 with hR₀
  have hon : ∀ v ρ, R v ρ + conj (R (-v) ρ) = 2 * R v ρ ∧ ‖R v ρ‖ = R₀ ρ ∧
      R 0 ρ = (R₀ ρ : ℂ) := by
    intro v ρ
    by_cases h : (ρ : ℂ).re = 1 / 2
    · have hg := gammaOf_eq_ofReal_of_re h
      obtain ⟨h1, h2, h3⟩ := onLine_summand hb.continuous hbc (Z.mult ρ) (ρ : ℂ).im v
      simp only [hR, hR₀, if_pos h, lagTerm, hg]
      exact ⟨h1, h2, h3⟩
    · simp only [hR, hR₀, if_neg h]
      simp
  have hR₀s : Summable R₀ := by
    refine Summable.of_norm_bounded (hRs 0).norm fun ρ => ?_
    rw [← (hon 0 ρ).2.1, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hM : onLineMassOf Z b = ∑' ρ, R₀ ρ := rfl
  refine ⟨?_, ?_⟩
  · have hconj : Summable fun ρ => conj (R (-v) ρ) :=
      (hRs (-v)).map (starRingEnd ℂ).toAddMonoidHom Complex.continuous_conj
    rw [Complex.conj_tsum, ← Summable.tsum_add (hRs v) hconj, tsum_congr fun ρ => (hon v ρ).1]
    have hn : Summable fun ρ => ‖2 * R v ρ‖ := ((hRs v).mul_left 2).norm
    refine (norm_tsum_le_tsum_norm hn).trans ?_
    rw [hM, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun ρ => ?_) hn (hR₀s.mul_left 2)
    rw [norm_mul, Complex.norm_ofNat, (hon v ρ).2.1]
  · rw [Complex.re_tsum (hRs 0), hM]
    exact tsum_congr fun ρ => by rw [(hon 0 ρ).2.2, Complex.ofReal_re]

/-- **Lag criterion for finite off-line sets.** If `T` is the set of zeros right of the line and
`|Σ_t q_t e^{δ_t v} e^{iγ_t v}| > 2M_b + 3Σ_t |q_t|`, the two-point minor fails at lag `v`. -/
theorem finiteOffLine_lagStructure_gt (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {T : Finset ℂ}
    (hT : ∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) {v : ℝ} (hv : 0 ≤ v)
    (hvis : 2 * onLineMassOf Z b + 3 * ∑ t ∈ T, ‖offLineWeight b (Z.mult t) t‖ <
      ‖∑ t ∈ T, offLineWeight b (Z.mult t) t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) *
        cexp (I * t.im * v)‖) :
    2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  obtain ⟨hon, hon0⟩ := onLinePart_bounds Z hZ hb hbs v
  set q : ℂ → ℂ := fun t => offLineWeight b (Z.mult t) t with hq
  have hpair : ∀ v, ∀ t ∈ T, (lagTerm Z b v t + lagTerm Z b v (reflect t)) +
      conj (lagTerm Z b (-v) t + lagTerm Z b (-v) (reflect t)) =
      2 * cexp (I * t.im * v) * (q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) +
        conj (q t) * (Real.exp (-((t.re - 1 / 2) * v)) : ℂ)) := fun v t ht =>
    (pair_lagTerm hb.continuous hbc Z ((hT t).mp ht).1 v).1
  have hX : lagStructure Z b v + conj (lagStructure Z b (-v)) =
      ((∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0) +
        conj (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b (-v) ρ else 0)) +
      (2 * ∑ t ∈ T, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) +
        ∑ t ∈ T, 2 * cexp (I * t.im * v) * (conj (q t) * (Real.exp (-((t.re - 1 / 2) * v)) : ℂ))) := by
    rw [lagStructure_split Z hZ hb hbs hT, lagStructure_split Z hZ hb hbs hT, map_add, map_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [show ∀ A B C D : ℂ, (A + B) + (C + D) = (A + C) + (B + D) from fun _ _ _ _ => by ring,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [hpair v t ht]
    ring
  have hS0 : (lagStructure Z b 0).re = onLineMassOf Z b + ∑ t ∈ T, 2 * (q t).re := by
    rw [lagStructure_split Z hZ hb hbs hT, Complex.add_re, hon0, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(pair_lagTerm hb.continuous hbc Z ((hT t).mp ht).1 0).2, Complex.add_re, Complex.conj_re]
    ring
  have hvis' : 2 * onLineMassOf Z b + 3 * ∑ t ∈ T, ‖q t‖ <
      ‖∑ t ∈ T, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v)‖ := hvis
  clear_value q
  have hE : ∀ t : ℂ, ‖cexp (I * t.im * v)‖ = 1 := fun t => by
    rw [show I * (t.im : ℂ) * (v : ℂ) = ((t.im * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hlow : ‖∑ t ∈ T, 2 * cexp (I * t.im * v) *
      (conj (q t) * (Real.exp (-((t.re - 1 / 2) * v)) : ℂ))‖ ≤ 2 * ∑ t ∈ T, ‖q t‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    have hδ : 0 ≤ t.re - 1 / 2 := by linarith [((hT t).mp ht).2]
    have hle : Real.exp (-((t.re - 1 / 2) * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_two, hE, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    nlinarith [norm_nonneg (q t)]
  have hsum_re : ∑ t ∈ T, 2 * (q t).re ≤ 2 * ∑ t ∈ T, ‖q t‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => by linarith [Complex.re_le_norm (q t)]
  rw [hX, hS0]
  set S := ∑ t ∈ T, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v)
  set B := ∑ t ∈ T, 2 * cexp (I * t.im * v) * (conj (q t) * (Real.exp (-((t.re - 1 / 2) * v)) : ℂ))
  set C := (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b v ρ else 0) +
    conj (∑' ρ : Z.carrier, if (ρ : ℂ).re = 1 / 2 then lagTerm Z b (-v) ρ else 0)
  have h1 := norm_sub_le (2 * S + B) B
  rw [add_sub_cancel_right, norm_mul, Complex.norm_two] at h1
  have h2 := norm_sub_le (C + (2 * S + B)) C
  rw [add_sub_cancel_left] at h2
  linarith

/-- The bump `κ_w` modulated to height `γ₀` gives the pair at height `γ₀` a nonzero weight:
`h(γ₀ ∓ iD) = κ̂_w(∓iD) ≠ 0`. -/
theorem pairWeight_modScaledBump_ne_zero {w : ℝ} (hw : 0 < w) (γ₀ D : ℝ) :
    pairWeight (modScaledBump w γ₀) D γ₀ ≠ 0 := by
  have hκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hne : ∀ y : ℝ, paperFT (scaledBump w) ((y : ℂ) * I) ≠ 0 := fun y h => by
    have := norm_paperFT_scaledBump_I_mul_ge hw y
    rw [h, norm_zero] at this
    have : 0 < 4 * w * (Real.exp (-(w * |y|)) * ∫ u, weilBump u) := by positivity
    linarith
  have hmod : ∀ z : ℂ, paperFT (modScaledBump w γ₀) z = paperFT (scaledBump w) (z - γ₀) :=
    fun z => paperFT_modulate (scaledBump w) γ₀ z
  rw [pairWeight, hmod, hmod, show (γ₀ : ℂ) - I * D - γ₀ = ((-D : ℝ) : ℂ) * I by push_cast; ring,
    show (γ₀ : ℂ) + I * D - γ₀ = (D : ℂ) * I by ring]
  exact mul_ne_zero (hne _) (by rw [Ne, map_eq_zero]; exact hne D)

/-- **Uniform minor failure for finite off-line sets.** Let `T` be a finite set right of the line,
`m` multiplicities, `t₀ ∈ T` with `Re t₀ = ½ + D`, `b` a bump with `q_{t₀} ≠ 0`, and `g ∈ (0, D]`
a gap: every `t ∈ T` off the level of `t₀` with `q_t ≠ 0` has `Re t ≤ Re t₀ − g`. There are
`c, ℓ > 0` such that for every tempered configuration whose zeros right of the line are exactly
`T`, with multiplicities `m`, and every `a ≥ (1/2g) log⁺((2M_b + 4Σ_t |q_t|)/c) + (|T| + 2)ℓ/2 + w`,
the two-point minor fails at a lag `v` with `v/2 + w ≤ a`. -/
theorem finiteOffLine_minor_fails {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ} (ht₀ : t₀ ∈ T) {g : ℝ}
    (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (hq₀ : offLineWeight b (m t₀) t₀ ≠ 0)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → offLineWeight b (m t) t ≠ 0 → t.re ≤ t₀.re - g) :
    ∃ c ℓ : ℝ, 0 < c ∧ 0 < ℓ ∧ ∀ Z : ZeroConfig, TemperedConfig Z →
      (∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) → (∀ t ∈ T, Z.mult t = m t) →
      ∀ a : ℝ, 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf Z b +
          4 * ∑ t ∈ T, ‖offLineWeight b (m t) t‖) / c)) + (T.card + 2) * ℓ / 2 + w ≤ a →
        ∃ v : ℝ, 0 ≤ v ∧ v / 2 + w ≤ a ∧
          2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : ℂ → ℂ, q = fun t => offLineWeight b (m t) t := ⟨_, rfl⟩
  have hq₀' : q t₀ ≠ 0 := by rw [hq]; exact hq₀
  -- the top level and a lag grid separating its heights
  set T₀ := T.filter fun t => t.re = t₀.re ∧ q t ≠ 0 with hT₀
  have ht₀T₀ : t₀ ∈ T₀ := Finset.mem_filter.mpr ⟨ht₀, rfl, hq₀'⟩
  haveI : Nonempty T₀ := ⟨⟨t₀, ht₀T₀⟩⟩
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = ∑ t ∈ T, |t.im| := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := hH ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hHt : ∀ t ∈ T, |t.im| ≤ H := fun t ht =>
    hH ▸ Finset.single_le_sum (f := fun t : ℂ => |t.im|) (fun _ _ => abs_nonneg _) ht
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = π / (1 + H) := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := by rw [hℓdef]; positivity
  have hnode : ∀ (y : ℝ) (k : ℕ), cexp (I * y * ℓ) ^ k = cexp (I * y * ((k * ℓ : ℝ) : ℂ)) :=
    fun y k => by rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hzn : ∀ r : T₀, ‖cexp (I * (r : ℂ).im * ℓ)‖ = 1 := fun r => by
    rw [show I * (((r : ℂ).im : ℝ) : ℂ) * (ℓ : ℂ) = (((r : ℂ).im * ℓ : ℝ) : ℂ) * I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hzinj : Function.Injective fun r : T₀ => cexp (I * (r : ℂ).im * ℓ) := by
    intro r r' h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have hr := Finset.mem_filter.mp r.2
    have hr' := Finset.mem_filter.mp r'.2
    have him : ((r : ℂ).im - (r' : ℂ).im) * ℓ = 2 * π * n := by
      have h0 : I * ((((r : ℂ).im - (r' : ℂ).im) * ℓ - 2 * π * n : ℝ) : ℂ) = 0 := by
        push_cast
        linear_combination hn
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h Complex.I_ne_zero
      · exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h)
    have hb1 : |(r : ℂ).im - (r' : ℂ).im| ≤ 2 * H := by
      have := abs_sub ((r : ℂ).im) ((r' : ℂ).im)
      linarith [hHt _ hr.1, hHt _ hr'.1]
    have hlt : |((r : ℂ).im - (r' : ℂ).im) * ℓ| < 2 * π := by
      rw [abs_mul, abs_of_pos hℓ, hℓdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    have hn0 : n = 0 := by
      rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hlt
      have : |(n : ℝ)| < 1 := by
        by_contra hc; push Not at hc; nlinarith [Real.pi_pos]
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast this)
    rw [hn0, Int.cast_zero, mul_zero] at him
    have hγ : (r : ℂ).im = (r' : ℂ).im := by
      have := mul_eq_zero.mp him
      rcases this with h | h
      · linarith
      · exact absurd h hℓ.ne'
    exact Subtype.ext (Complex.ext (by rw [hr.2.1, hr'.2.1]) hγ)
  obtain ⟨c, hc, hwin⟩ := exists_weighted_powerSum_window_lower _ hzn hzinj (fun r => q r)
    fun r => (Finset.mem_filter.mp r.2).2.2
  refine ⟨c, ℓ, hc, hℓ, fun Z hZ hT hmZ a ha => ?_⟩
  set D := t₀.re - 1 / 2 with hD
  set M := onLineMassOf Z (b)
  have hM0 : 0 ≤ M := tsum_nonneg fun ρ => by split_ifs <;> positivity
  have hQ : ∑ t ∈ T, ‖offLineWeight (b) (m t) t‖ = ∑ t ∈ T, ‖q t‖ := by
    rw [hq]
  rw [hQ] at ha
  set Sq := ∑ t ∈ T, ‖q t‖ with hSq
  have hSq0 : ‖q t₀‖ ≤ Sq := Finset.single_le_sum (f := fun t => ‖q t‖) (fun _ _ => norm_nonneg _) ht₀
  have hq₀n : 0 < ‖q t₀‖ := norm_pos_iff.mpr hq₀'
  set x := max 0 (Real.log ((2 * M + 4 * Sq) / c)) with hx
  set m₀ : ℕ := ⌈x / (g * ℓ)⌉₊ + 1 with hm₀
  obtain ⟨j, hj, hjc⟩ := hwin m₀
  rw [Fintype.card_coe] at hj
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = ((m₀ + j : ℕ) : ℝ) * ℓ := ⟨_, rfl⟩
  have hv : 0 ≤ v := by rw [hvdef]; positivity
  -- the top level at lag `v`
  have htopsum : ∑ t ∈ T with t.re = t₀.re, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) *
      cexp (I * t.im * v) = (Real.exp (D * v) : ℂ) * ∑ r : T₀, q r * cexp (I * (r : ℂ).im * ℓ) ^ (m₀ + j) := by
    rw [Finset.mul_sum, ← Finset.sum_filter_of_ne (p := fun t => q t ≠ 0) fun t _ h => by
        intro h0; rw [h0, zero_mul, zero_mul] at h; exact h rfl,
      Finset.filter_filter, ← hT₀, ← Finset.sum_coe_sort T₀]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hnode, ← hvdef, (Finset.mem_filter.mp r.2).2.1]
    ring
  have hE : ∀ t : ℂ, ‖cexp (I * t.im * v)‖ = 1 := fun t => by
    rw [show I * (t.im : ℂ) * (v : ℂ) = ((t.im * v : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hlowsum : ‖∑ t ∈ T with ¬ t.re = t₀.re, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) *
      cexp (I * t.im * v)‖ ≤ Real.exp ((D - g) * v) * Sq := by
    refine (norm_sum_le _ _).trans ?_
    rw [hSq, Finset.mul_sum]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ T)
      fun _ _ _ => by positivity).trans' (Finset.sum_le_sum fun t ht => ?_)
    obtain ⟨htT, hne⟩ := Finset.mem_filter.mp ht
    rw [norm_mul, norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_comm]
    by_cases hqt : q t = 0
    · rw [hqt, norm_zero, mul_zero, mul_zero]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have := hgap t htT hne (by simpa [hq] using hqt)
    rw [hD]
    nlinarith
  -- `e^{gv} > (2M + 4Sq)/c`
  have hgℓ : 0 < g * ℓ := mul_pos hg hℓ
  have hxm : x < g * (m₀ * ℓ) := by
    have h1 : x / (g * ℓ) < m₀ := by
      have := Nat.le_ceil (x / (g * ℓ))
      rw [hm₀]; push_cast; linarith
    rw [div_lt_iff₀ hgℓ] at h1
    linarith
  have hKpos : 0 < (2 * M + 4 * Sq) / c := div_pos (by linarith) hc
  have hexp : (2 * M + 4 * Sq) / c < Real.exp (g * v) := by
    calc (2 * M + 4 * Sq) / c = Real.exp (Real.log ((2 * M + 4 * Sq) / c)) :=
          (Real.exp_log hKpos).symm
      _ ≤ Real.exp x := Real.exp_le_exp.mpr (le_max_right _ _)
      _ < Real.exp (g * (m₀ * ℓ)) := Real.exp_lt_exp.mpr hxm
      _ ≤ Real.exp (g * v) := Real.exp_le_exp.mpr (by
          rw [hvdef]; push_cast
          have : (m₀ : ℝ) * ℓ ≤ ((m₀ : ℝ) + j) * ℓ := mul_le_mul_of_nonneg_right
            (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith) hℓ.le
          nlinarith)
  have hDg : 0 ≤ D - g := by rw [hD]; linarith
  have hsplitexp : Real.exp (D * v) = Real.exp ((D - g) * v) * Real.exp (g * v) := by
    rw [← Real.exp_add]; ring_nf
  have hE1 : 1 ≤ Real.exp ((D - g) * v) := Real.one_le_exp (by positivity)
  have htopn : Real.exp (D * v) * c ≤ ‖∑ t ∈ T with t.re = t₀.re, q t *
      (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v)‖ := by
    rw [htopsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hjc (Real.exp_pos _).le
  have hvis : 2 * M + 3 * ∑ t ∈ T, ‖offLineWeight (b) (Z.mult t) t‖ <
      ‖∑ t ∈ T, offLineWeight (b) (Z.mult t) t *
        (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v)‖ := by
    have hw' : ∀ t ∈ T, offLineWeight (b) (Z.mult t) t = q t :=
      fun t ht => by rw [hmZ t ht, hq]
    have hs1 : ∑ t ∈ T, ‖offLineWeight (b) (Z.mult t) t‖ = Sq :=
      Finset.sum_congr rfl fun t ht => by rw [hw' t ht]
    have hs2 : ∑ t ∈ T, offLineWeight (b) (Z.mult t) t *
        (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) =
        ∑ t ∈ T, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v) :=
      Finset.sum_congr rfl fun t ht => by rw [hw' t ht]
    rw [hs1, hs2, ← Finset.sum_filter_add_sum_filter_not T fun t => t.re = t₀.re]
    have h1 := norm_sub_le (∑ t ∈ T with t.re = t₀.re, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) *
        cexp (I * t.im * v) + ∑ t ∈ T with ¬ t.re = t₀.re, q t *
          (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v))
      (∑ t ∈ T with ¬ t.re = t₀.re, q t * (Real.exp ((t.re - 1 / 2) * v) : ℂ) * cexp (I * t.im * v))
    rw [add_sub_cancel_right] at h1
    have h2 : Real.exp ((D - g) * v) * (2 * M + 4 * Sq) < Real.exp (D * v) * c := by
      rw [hsplitexp, mul_assoc]
      exact mul_lt_mul_of_pos_left ((div_lt_iff₀ hc).mp hexp) (Real.exp_pos _)
    have h3 : 2 * M + 3 * Sq ≤ Real.exp ((D - g) * v) * (2 * M + 3 * Sq) :=
      le_mul_of_one_le_left (by positivity) hE1
    have h4 : Real.exp ((D - g) * v) * (2 * M + 4 * Sq) =
        Real.exp ((D - g) * v) * (2 * M + 3 * Sq) + Real.exp ((D - g) * v) * Sq := by ring
    linarith
  refine ⟨v, hv, ?_, finiteOffLine_lagStructure_gt Z hZ hb hbs hT hv hvis⟩
  have hm₀le : (m₀ : ℝ) ≤ x / (g * ℓ) + 2 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ x / (g * ℓ))
    rw [hm₀]; push_cast; linarith
  have hjle : (j : ℝ) ≤ T.card := by
    have : T₀.card ≤ T.card := Finset.card_filter_le _ _
    exact_mod_cast hj.le.trans this
  have h1 : ((m₀ : ℝ) + j) * ℓ ≤ (x / (g * ℓ) + 2 + T.card) * ℓ :=
    mul_le_mul_of_nonneg_right (by linarith) hℓ.le
  have h2 : (x / (g * ℓ) + 2 + T.card) * ℓ / 2 = 1 / (2 * g) * x + (T.card + 2) * ℓ / 2 := by
    field_simp
    ring
  rw [hvdef]
  push_cast
  linarith

/-- **Finite off-line sets are visible, uniformly in the on-line background.** Let `T` be a finite
set right of the line, `m` multiplicities, `t₀ ∈ T` with `Re t₀ = ½ + D`, and `g ∈ (0, D]` a
depth gap: every `t ∈ T` off the level of `t₀` has `Re t ≤ Re t₀ − g`. With `b = κ_w` modulated to
the height of `t₀` there are `c, ℓ > 0` such that every tempered configuration whose zeros right
of the line are exactly `T`, with multiplicities `m`, is visible at every aperture
`a ≥ (1/2g) log⁺((2M_b + 4Σ_t |q_t|)/c) + (|T| + 2)ℓ/2 + w`. -/
theorem finiteOffLine_visible {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ} (ht₀ : t₀ ∈ T)
    {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w) :
    ∃ c ℓ : ℝ, 0 < c ∧ 0 < ℓ ∧ ∀ Z : ZeroConfig, TemperedConfig Z →
      (∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) → (∀ t ∈ T, Z.mult t = m t) →
      ∀ a : ℝ, 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf Z (modScaledBump w t₀.im) +
          4 * ∑ t ∈ T, ‖offLineWeight (modScaledBump w t₀.im) (m t) t‖) / c)) +
          (T.card + 2) * ℓ / 2 + w ≤ a →
        ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0 := by
  have hb : ContDiff ℝ 2 (modScaledBump w t₀.im) :=
    (contDiff_modScaledBump w t₀.im).of_le (by norm_num)
  have hbs : ∀ u, modScaledBump w t₀.im u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra h
    push Not at h
    exact hu (modScaledBump_eq_zero hw h.le)
  -- a vanishing top multiplicity admits no configuration
  by_cases hm₀ : m t₀ = 0
  · refine ⟨1, 1, one_pos, one_pos, fun Z _ hT hmZ => ?_⟩
    have := Z.one_le_mult t₀ ((hT t₀).mp ht₀).1
    rw [hmZ t₀ ht₀, hm₀] at this
    exact absurd this (by norm_num)
  have hq₀ : offLineWeight (modScaledBump w t₀.im) (m t₀) t₀ ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hm₀) (pairWeight_modScaledBump_ne_zero hw _ _)
  obtain ⟨c, ℓ, hc, hℓ, h⟩ := finiteOffLine_minor_fails m ht₀ hg hgD hb hbs hq₀
    fun t ht hne _ => hgap t ht hne
  refine ⟨c, ℓ, hc, hℓ, fun Z hZ hT hmZ a ha => ?_⟩
  obtain ⟨v, hv, hva, hgt⟩ := h Z hZ hT hmZ a ha
  obtain ⟨f, hf, hfs, hneg⟩ := exists_visible_of_lagStructure Z hZ hb hbs hv hgt
  exact ⟨f, hf, hfs.trans (Icc_subset_Icc (neg_le_neg hva) hva), hneg⟩

end GaloisForLFunctions.SquareRootThreshold
