import GaloisForLFunctions.SquareRootThreshold.FiniteOffLineSetsAreVisible

/-!
# The Hodge index on configurations with finitely many off-line zeros

The zeros `s = 0` and `s = 1` sit at heights `γ = ±i/2`, exactly where tests in the Hodge class
vanish. They are therefore invisible to the Hodge index, and they are the only off-line zeros that
are:

* **Converse direction** (`weil_nonneg_of_onLine`, `hodgeIndex_of_onLine_or_poles`). If every zero
  is on the critical line, `Re W(f, f) ≥ 0` for every test. If every zero is on the line or at
  `0, 1`, the Hodge index holds at every level. On-line zeros contribute `m|h_f(γ)|² ≥ 0`. No
  growth condition on the zeros is needed.
* **Uniform Hodge violation** (`finiteOffLine_not_hodgeIndex`). Let `T` be a finite set right of
  the line, `t₀ ∈ T \ {1}` with `Re t₀ = ½ + D`, and `g ∈ (0, D]` a gap below the level of `t₀`
  among `T \ {1}`. With the polar-free bump `κ_w'' − κ_w/4` modulated to the height of `t₀`
  (`RHTower.scaledBumpPolarFree`), there are `c, ℓ > 0` such that every tempered configuration
  whose zeros right of the line are `T` violates the Hodge index at every level
  `a ≥ (1/2g) log⁺((2M + 4Σ_t |q_t|)/c) + (|T| + 2)ℓ/2 + w`. The polar factor `z² + ¼` kills
  the weight of `1` and of no other point.

The converse directions hold for every tempered configuration, with finite levels but without the
explicit aperture (`weil_nonneg_iff_onLine`, `hodgeIndex_forall_iff`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

theorem gammaOf_zero : gammaOf 0 = I / 2 := by
  apply Complex.ext <;> simp [re_gammaOf, im_gammaOf]

theorem gammaOf_one : gammaOf 1 = -(I / 2) := by
  apply Complex.ext
  · simp [re_gammaOf]
  · simp [im_gammaOf]; norm_num

/-- An on-line zero contributes `m|h_f(γ)|² ≥ 0`. -/
theorem re_Wsummand_nonneg_of_onLine (Z : ZeroConfig) (f : ℝ → ℂ) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    0 ≤ (Z.Wsummand f f ρ).re := by
  rw [ZeroConfig.Wsummand, gammaOf_eq_ofReal_of_re hρ, Complex.conj_ofReal, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  positivity

/-- Zeros at `0` and `1` contribute nothing for tests in the Hodge class. -/
theorem Wsummand_eq_zero_of_pole (Z : ZeroConfig) {f : ℝ → ℂ} (hp : paperFT f (I / 2) = 0)
    (hn : paperFT f (-(I / 2)) = 0) {ρ : ℂ} (hρ : ρ = 0 ∨ ρ = 1) : Z.Wsummand f f ρ = 0 := by
  rcases hρ with rfl | rfl
  · rw [ZeroConfig.Wsummand, gammaOf_zero, hp, mul_zero, zero_mul]
  · rw [ZeroConfig.Wsummand, gammaOf_one, hn, mul_zero, zero_mul]

theorem re_W_nonneg_of_summand_nonneg (Z : ZeroConfig) {f : ℝ → ℂ}
    (h : ∀ ρ ∈ Z.carrier, 0 ≤ (Z.Wsummand f f ρ).re) : 0 ≤ (Z.W f f).re := by
  rw [ZeroConfig.W]
  by_cases hs : Summable fun ρ : Z.carrier => Z.Wsummand f f ρ
  · rw [Complex.re_tsum hs]
    exact tsum_nonneg fun ρ => h ρ ρ.2
  · rw [tsum_eq_zero_of_not_summable hs, Complex.zero_re]

/-- **On-line configurations are Weil positive**, for every test and with no growth condition. -/
theorem weil_nonneg_of_onLine (Z : ZeroConfig) (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2)
    (f : ℝ → ℂ) : 0 ≤ (Z.W f f).re :=
  re_W_nonneg_of_summand_nonneg Z fun ρ hρ => re_Wsummand_nonneg_of_onLine Z f (hon ρ hρ)

/-- **The Hodge index is blind to `0` and `1`.** If every zero is on the line or at `0, 1`, the
Hodge index holds at every level. -/
theorem hodgeIndex_of_onLine_or_poles (Z : ZeroConfig)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = 0 ∨ ρ = 1) (a : ℝ) : HodgeIndexAtLevel Z a :=
  fun f _ _ hp hn => re_W_nonneg_of_summand_nonneg Z fun ρ hρ => by
    rcases hon ρ hρ with h | h
    · exact re_Wsummand_nonneg_of_onLine Z f h
    · rw [Wsummand_eq_zero_of_pole Z hp hn h, Complex.zero_re]

/-- The polar factor `z² + ¼` vanishes at `γ ∓ iD`, `D > 0`, only for the zero `1`. -/
theorem polarFactor_ne_zero {γ₀ D : ℝ} (hD : 0 < D) (h1 : ¬ (γ₀ = 0 ∧ D = 1 / 2)) (s : ℝ)
    (hs : s = D ∨ s = -D) : ((γ₀ : ℂ) + I * s) ^ 2 + 1 / 4 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im] at hre him
  norm_num at hre him
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> [exact hD.ne'; exact neg_ne_zero.mpr hD.ne']
  have hγ : γ₀ = 0 := by
    rcases mul_eq_zero.mp (show γ₀ * s = 0 by linarith) with h | h
    · exact h
    · exact absurd h hs0
  subst hγ
  have hs2 : s * s = 1 / 4 := by linarith
  have hD2 : D * D = 1 / 4 := by rcases hs with rfl | rfl <;> linarith
  exact h1 ⟨rfl, by nlinarith⟩

/-- The polar-free bump modulated to height `γ₀` gives the pair `½ ± D + iγ₀` a nonzero weight,
unless the pair is `{0, 1}`. -/
theorem pairWeight_polarFree_ne_zero {w : ℝ} (hw : 0 < w) {γ₀ D : ℝ} (hD : 0 < D)
    (h1 : ¬ (γ₀ = 0 ∧ D = 1 / 2)) : pairWeight (scaledBumpPolarFree w γ₀) D γ₀ ≠ 0 := by
  have hκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hne : ∀ y : ℝ, paperFT (scaledBump w) ((y : ℂ) * I) ≠ 0 := fun y h => by
    have := norm_paperFT_scaledBump_I_mul_ge hw y
    rw [h, norm_zero] at this
    have : 0 < 4 * w * (Real.exp (-(w * |y|)) * ∫ u, weilBump u) := by positivity
    linarith
  have hm := polarFactor_ne_zero hD h1 (-D) (Or.inr rfl)
  have hp := polarFactor_ne_zero hD h1 D (Or.inl rfl)
  rw [show (γ₀ : ℂ) + I * ((-D : ℝ) : ℂ) = γ₀ - I * D by push_cast; ring] at hm
  rw [pairWeight, paperFT_scaledBumpPolarFree hw, paperFT_scaledBumpPolarFree hw,
    show (γ₀ : ℂ) - I * D - γ₀ = ((-D : ℝ) : ℂ) * I by push_cast; ring,
    show (γ₀ : ℂ) + I * D - γ₀ = (D : ℂ) * I by ring]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hm) (hne _))
    (by rw [Ne, map_eq_zero]; exact mul_ne_zero (neg_ne_zero.mpr hp) (hne D))

/-- The polar-free bump gives the zero `1` the weight `0`. -/
theorem offLineWeight_polarFree_one {w : ℝ} (hw : 0 < w) (γ₀ : ℝ) (m : ℕ) :
    offLineWeight (scaledBumpPolarFree w γ₀) m 1 = 0 := by
  rw [offLineWeight, pairWeight, paperFT_scaledBumpPolarFree hw]
  simp only [Complex.one_re, Complex.one_im, Complex.ofReal_zero, zero_sub]
  rw [show (-(I * ((1 - 1 / 2 : ℝ) : ℂ))) ^ 2 + 1 / 4 = (0 : ℂ) by
    push_cast; ring_nf; rw [Complex.I_sq]; ring]
  simp

/-- **Finite off-line sets violate the Hodge index, uniformly in the on-line background.** Let `T`
be a finite set right of the line, `m` multiplicities, `t₀ ∈ T` with `t₀ ≠ 1` and
`Re t₀ = ½ + D`, and `g ∈ (0, D]` a gap: every `t ∈ T \ {1}` off the level of `t₀` has
`Re t ≤ Re t₀ − g`. With `b` the polar-free bump modulated to the height of `t₀` there are
`c, ℓ > 0` such that every tempered configuration whose zeros right of the line are exactly `T`,
with multiplicities `m`, violates the Hodge index at every level
`a ≥ (1/2g) log⁺((2M_b + 4Σ_t |q_t|)/c) + (|T| + 2)ℓ/2 + w`. -/
theorem finiteOffLine_not_hodgeIndex {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ} (ht₀ : t₀ ∈ T)
    (ht₀1 : t₀ ≠ 1) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t ≠ 1 → t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w) :
    ∃ c ℓ : ℝ, 0 < c ∧ 0 < ℓ ∧ ∀ Z : ZeroConfig, TemperedConfig Z →
      (∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) → (∀ t ∈ T, Z.mult t = m t) →
      ∀ a : ℝ, 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf Z (scaledBumpPolarFree w t₀.im) +
          4 * ∑ t ∈ T, ‖offLineWeight (scaledBumpPolarFree w t₀.im) (m t) t‖) / c)) +
          (T.card + 2) * ℓ / 2 + w ≤ a → ¬ HodgeIndexAtLevel Z a := by
  set b := scaledBumpPolarFree w t₀.im with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_scaledBumpPolarFree w t₀.im
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra h
    push Not at h
    exact hu (scaledBumpPolarFree_eq_zero hw h)
  have hpol : ∀ z : ℂ, z ^ 2 + 1 / 4 = 0 → paperFT b z = 0 := fun z hz => by
    rw [hbdef, paperFT_scaledBumpPolarFree hw, hz, neg_zero, zero_mul]
  have hhalf : (I / 2) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  have hnhalf : (-(I / 2)) ^ 2 + 1 / 4 = (0 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  -- a vanishing top multiplicity admits no configuration
  by_cases hm₀ : m t₀ = 0
  · refine ⟨1, 1, one_pos, one_pos, fun Z _ hT hmZ => ?_⟩
    have := Z.one_le_mult t₀ ((hT t₀).mp ht₀).1
    rw [hmZ t₀ ht₀, hm₀] at this
    exact absurd this (by norm_num)
  have hD : 0 < t₀.re - 1 / 2 := hg.trans_le hgD
  have hq₀ : offLineWeight b (m t₀) t₀ ≠ 0 := by
    refine mul_ne_zero (Nat.cast_ne_zero.mpr hm₀) (pairWeight_polarFree_ne_zero hw hD ?_)
    rintro ⟨h1, h2⟩
    exact ht₀1 (Complex.ext (by simp; linarith) (by simpa using h1))
  obtain ⟨c, ℓ, hc, hℓ, h⟩ := finiteOffLine_minor_fails m ht₀ hg hgD hb hbs hq₀
    fun t ht hne hq => hgap t ht (fun h1 => hq (h1 ▸ offLineWeight_polarFree_one hw _ _)) hne
  refine ⟨c, ℓ, hc, hℓ, fun Z hZ hT hmZ a ha => ?_⟩
  obtain ⟨v, hv, hva, hgt⟩ := h Z hZ hT hmZ a ha
  exact not_hodgeIndex_of_polarFree_minor Z hZ hb hbs (hpol _ hhalf) (hpol _ hnhalf) hv hgt hva

end GaloisForLFunctions.SquareRootThreshold
