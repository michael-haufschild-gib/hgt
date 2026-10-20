import GaloisForLFunctions.SquareRootThreshold.IsolatedPairInArbitraryBackground

/-!
# An isolated off-line pair violates the Hodge index at a logarithmic level

The level-`a` Hodge index (`RHTower.HodgeIndexAtLevel`) asks for Weil positivity only on tests whose
transforms vanish at `±i/2`. Two-bump tests built from a polar-free profile are in this class:
the transform of `b(t + v/2) + τ b(t − v/2)` is `(e^{−izv/2} + τ e^{izv/2}) h_b(z)`, which vanishes
wherever `h_b` does (`paperFT_twoBump_eq_zero`). So a failed two-point minor of a polar-free
profile violates the Hodge index (`not_hodgeIndex_of_polarFree_minor`).

**Hodge violation** (`isolatedPair_not_hodgeIndex`). Take the polar-free bump modulated to height
`γ₀`, `b = RHTower.scaledBumpPolarFree w γ₀`, whose transform is
`−(z² + ¼) κ̂_w(z − γ₀)`. If all zeros of a tempered configuration are on the critical line except
one simple pair `½ ± δ + iγ₀`, and

`|Q_b| (sinh(δv) − 1) > M_b`,  `Q_b = h_b(γ₀ − iδ) conj h_b(γ₀ + iδ)`,
`M_b = Σ_{on-line} m_ρ |h_b(γ_ρ)|²`,

then the Hodge index fails at every level `a ≥ v/2 + w`.

The level is `≈ (1/2δ) log(M_b/|Q_b|)`: logarithmic in the local on-line mass, for any arrangement
of the on-line zeros. The polar factor `|z² + ¼|` enters `M_b` and `|Q_b|` at the same height and
does not change the order. For comparison, the cluster-robust exclusion for `ζ`
(`RHTower.not_hodgeIndex_below_cluster_horizon`) needs a level linear in the window count; the
logarithmic level here uses that no other zero is off the line.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- A two-bump test vanishes wherever its profile transform does. -/
theorem paperFT_twoBump_eq_zero {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (v : ℝ) (τ : ℂ) {z : ℂ} (hz : paperFT b z = 0) : paperFT (twoBump b v τ) z = 0 := by
  rw [paperFT_twoBump hb hbc, hz, mul_zero]

/-- **Two-bump minors.** If every unimodular two-bump test at lag `v`,
`b(t + v/2) + τ b(t − v/2)` with `|τ| = 1`, has `Re W ≥ 0`, then
`|S(v) + conj S(−v)| ≤ 2 Re S(0)`. -/
theorem norm_lagStructure_le_of_twoBump_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ)
    (h : ∀ τ : ℂ, ‖τ‖ = 1 → 0 ≤ (Z.W (twoBump b v τ) (twoBump b v τ)).re) :
    ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖ ≤ 2 * (lagStructure Z b 0).re := by
  set X := lagStructure Z b v + conj (lagStructure Z b (-v)) with hX
  have key : ∀ τ : ℂ, ‖τ‖ = 1 → 0 ≤ (1 + ‖τ‖ ^ 2) * (lagStructure Z b 0).re + (τ * X).re := by
    intro τ hτ
    have h1 := h τ hτ
    rw [W_twoBump Z hZ hb hbs v τ] at h1
    have h2 : (conj τ * lagStructure Z b (-v)).re = (τ * conj (lagStructure Z b (-v))).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj]
    rw [Complex.add_re, Complex.add_re, h2, show (1 + (‖τ‖ : ℂ) ^ 2) = ((1 + ‖τ‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul] at h1
    rw [hX, mul_add, Complex.add_re]
    linarith
  by_cases hX0 : X = 0
  · rw [hX0, norm_zero]
    have := key 1 norm_one
    simp only [hX0, mul_zero, Complex.zero_re, add_zero, norm_one] at this
    linarith
  set τ : ℂ := -(conj X / ‖X‖) with hτ
  have hτn : ‖τ‖ = 1 := by
    rw [hτ, norm_neg, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.mpr hX0)]
  have hτX : (τ * X).re = -‖X‖ := by
    rw [hτ, neg_mul, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
    rw [show ((‖X‖ ^ 2 : ℝ) : ℂ) / (‖X‖ : ℂ) = ((‖X‖ : ℝ) : ℂ) by
      have : (‖X‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hX0
      push_cast; field_simp]
    simp
  have := key τ hτn
  rw [hτn, hτX] at this
  linarith

/-- **A failed minor with a polar-free profile violates the Hodge index.** If `h_b(±i/2) = 0` and
the two-point minor fails at lag `v ≥ 0`, the Hodge index fails at every level `a ≥ v/2 + w`. -/
theorem not_hodgeIndex_of_polarFree_minor (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (hp : paperFT b (I / 2) = 0)
    (hn : paperFT b (-(I / 2)) = 0) {v : ℝ} (hv : 0 ≤ v)
    (hgt : 2 * (lagStructure Z b 0).re < ‖lagStructure Z b v + conj (lagStructure Z b (-v))‖)
    {a : ℝ} (ha : v / 2 + w ≤ a) : ¬ HodgeIndexAtLevel Z a := by
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  intro hH
  refine absurd (norm_lagStructure_le_of_twoBump_nonneg Z hZ hb hbs v fun τ _ => ?_)
    (not_le.mpr hgt)
  -- every two-bump test is in the Hodge class at level `a`
  have hf := contDiff_bumpTest hb v ![1, τ]
  have hfs := tsupport_bumpTest_subset hbs hv (a := a) (n := 2) (by push_cast; linarith) ![1, τ]
  exact hH _ hf hfs (paperFT_twoBump_eq_zero hb.continuous hbc v τ hp)
    (paperFT_twoBump_eq_zero hb.continuous hbc v τ hn)

/-- **An isolated pair violates the Hodge index.** With the polar-free bump
`b = scaledBumpPolarFree w γ₀`: if all zeros of a tempered configuration are on the critical line
except one simple pair `½ ± δ + iγ₀`, and `|Q_b| (sinh(δv) − 1) > M_b`, the level-`a` Hodge index
fails for every `a ≥ v/2 + w`. -/
theorem isolatedPair_not_hodgeIndex (Z : ZeroConfig) (hZ : TemperedConfig Z) {δ γ₀ : ℝ}
    (hδ : 0 < δ) (hp : heightPoint δ γ₀ ∈ Z.carrier) (hm : heightPoint (-δ) γ₀ ∈ Z.carrier)
    (hmp : Z.mult (heightPoint δ γ₀) = 1) (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {w v : ℝ} (hw : 0 < w) (hv : 0 ≤ v)
    (hvis : onLineMassOf Z (scaledBumpPolarFree w γ₀) <
      ‖pairWeight (scaledBumpPolarFree w γ₀) δ γ₀‖ * (Real.sinh (δ * v) - 1))
    {a : ℝ} (ha : v / 2 + w ≤ a) : ¬ HodgeIndexAtLevel Z a := by
  set b := scaledBumpPolarFree w γ₀ with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_scaledBumpPolarFree w γ₀
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra h
    push Not at h
    exact hu (scaledBumpPolarFree_eq_zero hw h)
  have hpol : ∀ z : ℂ, z ^ 2 + 1 / 4 = 0 → paperFT b z = 0 := fun z hz => by
    rw [hbdef, paperFT_scaledBumpPolarFree hw, hz, neg_zero, zero_mul]
  have hhalf : (I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  have hnhalf : (-(I / 2)) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  exact not_hodgeIndex_of_polarFree_minor Z hZ hb hbs (hpol _ hhalf) (hpol _ hnhalf) hv
    (isolatedPair_lagStructure_gt Z hZ hδ hp hm hmp hmm hon hb hbs hvis) ha

end GaloisForLFunctions.SquareRootThreshold
