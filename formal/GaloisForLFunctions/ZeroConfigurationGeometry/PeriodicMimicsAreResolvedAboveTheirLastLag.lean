import GaloisForLFunctions.ZeroConfigurationGeometry.PeriodicPatternsCannotSatisfyTheirLastLag
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold

/-!
# Periodic mimics are resolved above their last lag

The configuration-level form of `eq_zero_of_lagSymbol_eq_zero`. A configuration with a lag formula
`W(f, f) = ℓ Σ_m k(mℓ) D(m)`, `k = f ⋆ f̃`, is read mode by mode by narrow bumps.
* **A tooth reads one mode** (`weilTest_twoBump`, `W_twoBump_of_lagFormula`). The test
  `b(t + nℓ/2) + τ b(t − nℓ/2)` has kernel `(1 + |τ|²)K(x) + τ̄K(x + nℓ) + τK(x − nℓ)`, so it reads
  `(1 + |τ|²)D(0) + τD(n) + τ̄D(−n)`. A single bump reads `D(0)` (`W_bump_of_lagFormula`).
* **Mimics share their symbol** (`lagSymbol_eq_of_mimic`). Weights `τ = −1` and `τ = i` separate
  `D(n)` from `D(−n)`, so mimics at aperture `a` have equal symbols at every `nℓ < 2a`.
* **Periodic mimics** (`eq_zero_of_mimic_of_periodSymbol`). If the symbols differ by a period-`N`
  pattern `Σ_r C_r cosh(m x_r) ω^{rm}` and the aperture exceeds `(N − 1)ℓ/2`, the pattern is zero.
-/

open MeasureTheory Complex Set
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 _root_.RHTower SquareRootThreshold

/-! ### Two-bump tests with a complex weight -/

/-- The kernel of `b(t + v/2) + τ b(t − v/2)`: `(1 + |τ|²)K(x) + τ̄K(x + v) + τK(x − v)`. -/
theorem weilTest_twoBump {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b) (v : ℝ)
    (τ : ℂ) (x : ℝ) :
    EF.weilTest (twoBump b v τ) (twoBump b v τ) x =
      (1 + τ * conj τ) * EF.weilTest b b x + conj τ * EF.weilTest b b (x + v) +
        τ * EF.weilTest b b (x - v) := by
  have hint : ∀ (f₁ g : ℝ → ℝ) (α β : ℝ), (∀ t, f₁ t = t + α) → (∀ t, g t = t + β) →
      Integrable fun t => b (f₁ t) * conj (b (g t)) := fun f₁ g α β hf hg => by
    have e : (fun t => b (f₁ t) * conj (b (g t))) = fun t => b (t + α) * conj (b (t + β)) :=
      funext fun t => by rw [hf, hg]
    rw [e]
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      ((hbc.comp_homeomorph (Homeomorph.addRight α)).mul_right)
  have key : ∀ (f₁ g : ℝ → ℝ) (α y : ℝ), (∀ t, f₁ t = t + α) → (∀ t, g t = t + α - y) →
      ∫ t, b (f₁ t) * conj (b (g t)) = EF.weilTest b b y := fun f₁ g α y hf hg => by
    have e : (fun t => b (f₁ t) * conj (b (g t))) = fun t => b (t + α) * conj (b (t + α - y)) :=
      funext fun t => by rw [hf, hg]
    rw [e, RHTower.weilTest_apply]
    exact integral_add_right_eq_self (fun s => b s * conj (b (s - y))) α
  have e : (fun t => twoBump b v τ t * conj (twoBump b v τ (t - x))) = fun t =>
      b (t + v / 2) * conj (b (t - x + v / 2)) + conj τ * (b (t + v / 2) * conj (b (t - x - v / 2))) +
        τ * (b (t - v / 2) * conj (b (t - x + v / 2))) +
          τ * conj τ * (b (t - v / 2) * conj (b (t - x - v / 2))) := by
    funext t
    rw [twoBump_apply, twoBump_apply]
    simp only [map_add, map_mul]
    ring
  have I1 := hint (fun t => t + v / 2) (fun t => t - x + v / 2) (v / 2) (-x + v / 2)
    (fun t => rfl) (fun t => by ring)
  have I2 := hint (fun t => t + v / 2) (fun t => t - x - v / 2) (v / 2) (-x - v / 2)
    (fun t => rfl) (fun t => by ring)
  have I3 := hint (fun t => t - v / 2) (fun t => t - x + v / 2) (-(v / 2)) (-x + v / 2)
    (fun t => by ring) (fun t => by ring)
  have I4 := hint (fun t => t - v / 2) (fun t => t - x - v / 2) (-(v / 2)) (-x - v / 2)
    (fun t => by ring) (fun t => by ring)
  have J2 : Integrable fun t => conj τ * (b (t + v / 2) * conj (b (t - x - v / 2))) :=
    I2.const_mul _
  have J3 : Integrable fun t => τ * (b (t - v / 2) * conj (b (t - x + v / 2))) := I3.const_mul _
  have J4 : Integrable fun t => τ * conj τ * (b (t - v / 2) * conj (b (t - x - v / 2))) :=
    I4.const_mul _
  have J12 : Integrable fun t => b (t + v / 2) * conj (b (t - x + v / 2)) +
      conj τ * (b (t + v / 2) * conj (b (t - x - v / 2))) := I1.add J2
  have J123 : Integrable fun t => b (t + v / 2) * conj (b (t - x + v / 2)) +
      conj τ * (b (t + v / 2) * conj (b (t - x - v / 2))) +
        τ * (b (t - v / 2) * conj (b (t - x + v / 2))) := J12.add J3
  rw [RHTower.weilTest_apply, e, integral_add J123 J4, integral_add J12 J3, integral_add I1 J2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    key (fun t => t + v / 2) (fun t => t - x + v / 2) (v / 2) x (fun t => rfl) (fun t => by ring),
    key (fun t => t + v / 2) (fun t => t - x - v / 2) (v / 2) (x + v) (fun t => rfl)
      (fun t => by ring),
    key (fun t => t - v / 2) (fun t => t - x + v / 2) (-(v / 2)) (x - v) (fun t => by ring)
      (fun t => by ring),
    key (fun t => t - v / 2) (fun t => t - x - v / 2) (-(v / 2)) x (fun t => by ring)
      (fun t => by ring)]
  ring

theorem tsupport_twoBump_subset {w v : ℝ} (hw : 0 < w) (τ : ℂ) :
    tsupport (twoBump (modScaledBump w 0) v τ) ⊆ Icc (-(|v| / 2 + w)) (|v| / 2 + w) := by
  have hbs := modScaledBump_support hw 0
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  have ht' : twoBump (modScaledBump w 0) v τ t ≠ 0 := ht
  rw [twoBump_apply] at ht'
  have hv := abs_nonneg v
  have hv1 := le_abs_self v
  have hv2 := neg_abs_le v
  by_cases h1 : modScaledBump w 0 (t + v / 2) = 0
  · have h2 : modScaledBump w 0 (t - v / 2) ≠ 0 := fun h => ht' (by rw [h1, h]; ring)
    obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h2)
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨h3, h4⟩ := abs_le.mp (hbs _ h1)
    exact ⟨by linarith, by linarith⟩

/-- **A tooth reads one mode with a complex weight.** Under the lag formula with `ℓ > 4w`, the
two-bump test at lag `nℓ` with weight `τ` has
`W = ℓ K(0)((1 + |τ|²)D(0) + τD(n) + τ̄D(−n))`. -/
theorem W_twoBump_of_lagFormula (Z : ZeroConfig) {ℓ : ℝ} (D : ℤ → ℂ)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {w : ℝ} (hw : 0 < w) (hwℓ : 4 * w < ℓ) {n : ℕ} (hn : 1 ≤ n) (τ : ℂ) :
    Z.W (twoBump (modScaledBump w 0) (n * ℓ) τ) (twoBump (modScaledBump w 0) (n * ℓ) τ) =
      ((ℓ : ℝ) : ℂ) * EF.weilTest (modScaledBump w 0) (modScaledBump w 0) 0 *
        ((1 + τ * conj τ) * D 0 + τ * D n + conj τ * D (-n)) := by
  classical
  set b := modScaledBump w 0 with hbdef
  have hbs := modScaledBump_support hw 0
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  set K := EF.weilTest b b with hK
  have h2w : 2 * w < ℓ := by linarith
  have hKj0 : ∀ j : ℤ, j ≠ 0 → K (j * ℓ) = 0 := fun j hj =>
    weilTest_self_eq_zero_of_lt hbs (lt_abs_int_mul hw h2w hj)
  set v := (n : ℝ) * ℓ with hv
  have hk : ∀ x : ℝ, EF.weilTest (twoBump b v τ) (twoBump b v τ) x =
      (1 + τ * conj τ) * K x + conj τ * K (x + v) + τ * K (x - v) :=
    weilTest_twoBump hb.continuous hbc v τ
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [hW (twoBump b v τ) (contDiff_bumpTest hb v ![1, τ]) (hasCompactSupport_twoBump hbc v τ)]
  have hp : ∀ m : ℤ, (m : ℝ) * ℓ + v = ((m + n : ℤ) : ℝ) * ℓ := fun m => by
    rw [hv]; push_cast; ring
  have hm : ∀ m : ℤ, (m : ℝ) * ℓ - v = ((m - n : ℤ) : ℝ) * ℓ := fun m => by
    rw [hv]; push_cast; ring
  have hsum : ∑' m : ℤ, EF.weilTest (twoBump b v τ) (twoBump b v τ) (m * ℓ) * D m =
      ∑ m ∈ ({0, (n : ℤ), -(n : ℤ)} : Finset ℤ),
        EF.weilTest (twoBump b v τ) (twoBump b v τ) (m * ℓ) * D m := by
    refine tsum_eq_sum fun m hm' => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm'
    obtain ⟨h1, h2, h3⟩ := hm'
    rw [hk, hKj0 m h1, hp, hKj0 (m + n) (by omega), hm, hKj0 (m - n) (by omega)]
    simp
  have T0 : EF.weilTest (twoBump b v τ) (twoBump b v τ) (((0 : ℤ) : ℝ) * ℓ) * D 0 =
      (1 + τ * conj τ) * K 0 * D 0 := by
    rw [hk, hp 0, hm 0, show ((0 : ℤ) + n : ℤ) = n by ring, show ((0 : ℤ) - n : ℤ) = -n by ring,
      hKj0 n hn0, hKj0 (-n) (by omega), Int.cast_zero, zero_mul]
    ring
  have Tn : EF.weilTest (twoBump b v τ) (twoBump b v τ) (((n : ℤ) : ℝ) * ℓ) * D n =
      τ * K 0 * D n := by
    rw [hk, hKj0 n hn0, hp n, hm n, show ((n : ℤ) + n : ℤ) = 2 * n by ring,
      show ((n : ℤ) - n : ℤ) = 0 by ring, hKj0 (2 * n) (by omega), Int.cast_zero, zero_mul]
    ring
  have Tm : EF.weilTest (twoBump b v τ) (twoBump b v τ) (((-(n : ℤ) : ℤ) : ℝ) * ℓ) * D (-n) =
      conj τ * K 0 * D (-n) := by
    rw [hk, hKj0 (-n) (by omega), hp (-n), hm (-n), show (-(n : ℤ) + n : ℤ) = 0 by ring,
      show (-(n : ℤ) - n : ℤ) = -(2 * n) by ring, hKj0 (-(2 * n)) (by omega), Int.cast_zero,
      zero_mul]
    ring
  rw [hsum, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_singleton, T0, Tn, Tm]
  ring

/-- **A single bump reads the mean mode.** -/
theorem W_bump_of_lagFormula (Z : ZeroConfig) {ℓ : ℝ} (D : ℤ → ℂ)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {w : ℝ} (hw : 0 < w) (hwℓ : 2 * w < ℓ) :
    Z.W (modScaledBump w 0) (modScaledBump w 0) =
      ((ℓ : ℝ) : ℂ) * (EF.weilTest (modScaledBump w 0) (modScaledBump w 0) 0 * D 0) := by
  have hbs := modScaledBump_support hw 0
  have hb : ContDiff ℝ 2 (modScaledBump w 0) := contDiff_modScaledBump_two w 0
  have hbc : HasCompactSupport (modScaledBump w 0) := hasCompactSupport_of_support_subset_abs hbs
  rw [hW _ hb hbc, tsum_eq_single 0 fun j hj => by
    rw [weilTest_self_eq_zero_of_lt hbs (lt_abs_int_mul hw hwℓ hj), zero_mul]]
  simp

/-! ### Mimics read the symbol -/

/-- **Mimics share their symbol up to the aperture.** If two configurations with lag formulas
`W = ℓ Σ_m k(mℓ) D(m)` are mimics at aperture `a`, then `D(n) = D'(n)` whenever `nℓ/2 < a`. -/
theorem lagSymbol_eq_of_mimic {Z Z' : ZeroConfig} {ℓ : ℝ} (hℓ : 0 < ℓ) {D D' : ℤ → ℂ}
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    (hW' : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z'.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D' m)
    {a : ℝ} (hmim : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {n : ℕ}
    (hn : (n : ℝ) * ℓ / 2 < a) : D n = D' n := by
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = min ((a - n * ℓ / 2) / 2) (ℓ / 8) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hwdef]; exact lt_min (by linarith) (by positivity)
  have hw1 : w ≤ (a - n * ℓ / 2) / 2 := hwdef ▸ min_le_left _ _
  have hw2 : w ≤ ℓ / 8 := hwdef ▸ min_le_right _ _
  have hnℓ : 0 ≤ (n : ℝ) * ℓ := by positivity
  set b := modScaledBump w 0 with hbdef
  have hbs := modScaledBump_support hw0 0
  have hK0 : EF.weilTest b b 0 ≠ 0 := by
    rw [SquareRootThreshold.weilTest_self_zero, Complex.ofReal_ne_zero]
    exact (integral_norm_sq_modScaledBump_pos hw0).ne'
  have hℓ0 : ((ℓ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  -- the mean mode
  have hD0 : D 0 = D' 0 := by
    have hwin : ApertureWindow a b := ⟨contDiff_modScaledBump_two w 0,
      closure_minimal (fun t ht => abs_le.mp ((hbs t ht).trans (by linarith))) isClosed_Icc⟩
    have h := hmim b hwin
    rw [W_bump_of_lagFormula Z D hW hw0 (by linarith),
      W_bump_of_lagFormula Z' D' hW' hw0 (by linarith)] at h
    exact mul_left_cancel₀ hK0 (mul_left_cancel₀ hℓ0 h)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact_mod_cast hD0
  -- the tooth at `nℓ`, read with weights `−1` and `i`
  have hwin : ∀ τ : ℂ, ApertureWindow a (twoBump b (n * ℓ) τ) := fun τ =>
    ⟨contDiff_bumpTest (contDiff_modScaledBump_two w 0) _ _,
      (tsupport_twoBump_subset hw0 τ).trans (Icc_subset_Icc (by rw [abs_of_nonneg hnℓ]; linarith)
        (by rw [abs_of_nonneg hnℓ]; linarith))⟩
  have hread : ∀ τ : ℂ, (1 + τ * conj τ) * D 0 + τ * D n + conj τ * D (-n) =
      (1 + τ * conj τ) * D' 0 + τ * D' n + conj τ * D' (-n) := fun τ => by
    have h := hmim _ (hwin τ)
    rw [W_twoBump_of_lagFormula Z D hW hw0 (by linarith) hnpos τ,
      W_twoBump_of_lagFormula Z' D' hW' hw0 (by linarith) hnpos τ] at h
    exact mul_left_cancel₀ hK0 (mul_left_cancel₀ hℓ0 (by rw [← mul_assoc, ← mul_assoc]; exact h))
  have h1 := hread (-1)
  have h2 := hread Complex.I
  simp only [map_neg, map_one, Complex.conj_I] at h1 h2
  rw [hD0] at h1 h2
  linear_combination (-1 / 2 : ℂ) * h1 + (-Complex.I / 2) * h2 +
    ((D n - D' n - (D (-n) - D' (-n))) / 2) * Complex.I_sq

/-! ### Periodic mimics -/

/-- **Periodic mimics are resolved above their last lag.** Two configurations with lag formulas
whose symbols differ by a period-`N` pattern `Σ_r C_r cosh(m x_r) ω^{rm}` (depths `x_r ≥ 0`, real
weights) and which are mimics at an aperture `a > (N − 1)ℓ/2` have `C = 0`. With `ℓ = 2π/(Ng)`
the threshold is `(N − 1)π/(Ng)`. -/
theorem eq_zero_of_mimic_of_periodSymbol {N : ℕ} (hN : 0 < N) {Z Z' : ZeroConfig} {ℓ : ℝ}
    (hℓ : 0 < ℓ) {D D' : ℤ → ℂ}
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    (hW' : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z'.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D' m)
    {x C : Fin N → ℝ} (hx : ∀ r, 0 ≤ x r)
    (hΔ : ∀ m : ℕ, D m - D' m =
      ∑ r : Fin N, (C r : ℂ) * (Real.cosh (m * x r) : ℂ) * lagRoot N ^ ((r : ℕ) * m))
    {a : ℝ} (ha : ((N : ℝ) - 1) * ℓ / 2 < a) (hmim : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) :
    C = 0 := by
  refine eq_zero_of_lagSymbol_eq_zero hN hx fun m hm => ?_
  rw [← hΔ m, lagSymbol_eq_of_mimic hℓ hW hW' hmim (n := m) ?_, sub_self]
  have hm' : (m : ℝ) ≤ (N : ℝ) - 1 := by
    have : m + 1 ≤ N := hm
    have h : ((m + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at h
    linarith
  nlinarith

end GaloisForLFunctions.ZeroConfigurationGeometry
