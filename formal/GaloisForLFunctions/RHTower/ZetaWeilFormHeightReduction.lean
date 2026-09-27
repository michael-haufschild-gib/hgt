import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.RHTower.ErrorExponentAbscissaExcessLaw
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# The level-`a` Weil form of `ζ` sees only its zeros below `exp(O(e^a))`

For abstract zero configurations the level-`a` Weil form sees every height: a single off-line pair
at any height `T` has eventual error exponent `½` (`offLinePairConfig_eventually_relaxed_iff`).  For
`ζ` the explicit formula supplies a horizon.

**Theorem** (`zeta_re_W_ge_of_depth_below_horizon`).  There is `A₀` such that, for `a > 0` and
`0 ≤ η ≤ ½`, suppose
* every zero of ordinate at most `H(A₀, a)` has `|β - ½| ≤ η`, and
* every unit window below `H(A₀, a)` carries off-line multiplicity at most `D`.

Then every polar-constrained `C²` test on `[-a, a]` has
`Re W(f, f) ≥ -(7000 (2a + 3) D e^{2η(a+2)} + 2) ∫|f|²`,
where `log H(A₀, a) ≤ 7000 e^a + log A₀ + 160` (`log_zetaHorizonHeight_le`).

In the form "zeros up to height `T`" (`zeta_re_W_ge_of_depth_up_to_height`), this is the global
converse `re_W_ge_of_depth_offLineDensity` for `ζ`, valid at every level `a` with `H(A₀, a) ≤ T`.
As a relaxed index it reads `zeta_relaxedHodgeIndexAtLevel_of_depth_below_horizon`.  With
`η = D = 0` it says that the Riemann hypothesis below `H(A₀, a)` gives the level-`a` Hodge index up
to `2 ∫|f|²` (`zeta_re_W_ge_neg_two_of_critical_below_horizon`).

**Proof.**  `W(f, f) = W(f, g) + (W(f, f) - W(f, g))`, with the smoothed test
`g = f ⋆ w_b ⋆ w_b/c_b²` of width `b = e^{-2E}/4` and `E = 10 + 68 e^{a+2}`.
* **Symbol side** (`re_W_sub_W_smoothedTest_ge`).  The difference has symbol density
  `|h_f|²(1 - q_b²)(μ + P_X)` and is at least `-E e^{-2E} ∫|f|² ≥ -∫|f|²`.
* **Zero side** (`re_W_smoothedTest_ge`).  The summand of `W(f, g)` is
  `m_ρ h_f(x_ρ) conj h_f(x̄_ρ) q_b(x_ρ)²`.
  - Below `H`: `Re(A B̄ c) ≥ -|A - B|²/4 - |A||B||c - q_b(γ)²|`.  The depth differences are summed
    by the height-restricted Bessel bound (`sum_low_mult_norm_sub_sq_le`), and the phase error
    `|c - q_b(γ)²| ≤ 6b|β - ½|` by a plain Bessel bound over the off-line zeros
    (`sum_low_off_mult_norm_sq_le`).
  - Above `H`: `|q_b(x_ρ)|² ≤ e·400²/(b⁶(1 + |γ|)⁴)`, and the local count gives a tail
    `≤ 24A₀ log 3/(1 + H)`, which the choice of `H` makes at most `∫|f|²`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Off-line density below a height -/

/-- The off-line multiplicity of a zero of ordinate at most `H`, and `0` otherwise. -/
def lowOffMult (Z : ZeroConfig) (H : ℝ) (ρ : Z.carrier) : ℝ :=
  if |(ρ : ℂ).im| ≤ H then offLineMult Z ρ else 0

theorem lowOffMult_nonneg (Z : ZeroConfig) (H : ℝ) (ρ : Z.carrier) : 0 ≤ lowOffMult Z H ρ := by
  unfold lowOffMult; split_ifs; exacts [offLineMult_nonneg Z ρ, le_rfl]

/-- Every unit window carries off-line multiplicity at most `D` among the zeros of ordinate at
most `H`. -/
def OffLineDensityBoundBelow (Z : ZeroConfig) (H D : ℝ) : Prop :=
  ∀ t : ℝ, ∀ s : Finset Z.carrier, (∀ ρ ∈ s, t < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ t + 1) →
    ∑ ρ ∈ s, lowOffMult Z H ρ ≤ D

theorem OffLineDensityBoundBelow.nonneg {Z : ZeroConfig} {H D : ℝ}
    (hD : OffLineDensityBoundBelow Z H D) : 0 ≤ D := by simpa using hD 0 ∅ (by simp)

theorem offLineDensityBoundBelow_of_global {Z : ZeroConfig} {D : ℝ} (hD : OffLineDensityBound Z D)
    (H : ℝ) : OffLineDensityBoundBelow Z H D := by
  intro t s hs
  refine le_trans (Finset.sum_le_sum fun ρ _ => ?_) (hD t s hs)
  unfold lowOffMult; split_ifs; exacts [le_rfl, offLineMult_nonneg Z ρ]

/-! ### Gram entries with local depth bounds -/

theorem mult_mul_norm_gram_le_of_depth (Z : ZeroConfig) {η : ℝ} (J : ℕ) (ρ σ : Z.carrier)
    (hρ : |(ρ : ℂ).re - 1 / 2| ≤ η) (hσ : |(σ : ℂ).re - 1 / 2| ≤ η) :
    (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
      offLineMult Z σ * (plateauGramConst J η / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2) := by
  unfold offLineMult
  split_ifs with hσl
  · have h0 : ∀ u, depthExp (gammaOf σ) u = 0 := depthExp_eq_zero (by
      rw [WeilEF.gammaOf_im, hσl]; ring)
    simp [h0]
  · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h := norm_gram_depthExp_le J (abs_gammaOf_im_le hρ) (abs_gammaOf_im_le hσ)
    rw [WeilEF.gammaOf_re, WeilEF.gammaOf_re, abs_sub_comm] at h
    exact h

theorem mult_mul_norm_gram_le_of_depth' (Z : ZeroConfig) {η : ℝ} (J : ℕ) (ρ σ : Z.carrier)
    (hρ : |(ρ : ℂ).re - 1 / 2| ≤ η) (hσ : |(σ : ℂ).re - 1 / 2| ≤ η) :
    (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
        (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
      offLineMult Z ρ * (plateauGramConst J η / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2) := by
  unfold offLineMult
  split_ifs with hρl
  · have h0 : ∀ u, depthExp (gammaOf ρ) u = 0 := depthExp_eq_zero (by
      rw [WeilEF.gammaOf_im, hρl]; ring)
    simp [h0]
  · refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h := norm_gram_depthExp_le J (abs_gammaOf_im_le hρ) (abs_gammaOf_im_le hσ)
    rw [WeilEF.gammaOf_re, WeilEF.gammaOf_re] at h
    exact h

/-- On the zeros of ordinate at most `H`, the off-line multiplicity is the height-restricted one. -/
theorem offLineMult_eq_lowOffMult (Z : ZeroConfig) {H : ℝ} {ρ : Z.carrier}
    (hρ : |(ρ : ℂ).im| ≤ H) : offLineMult Z ρ = lowOffMult Z H ρ := by
  unfold lowOffMult; rw [if_pos hρ]

/-- **Depth-difference Bessel bound below a height.**  If the zeros of ordinate at most `H` have
depth at most `η` and off-line density at most `D`, then for a continuous test on `[-J, J]`,
`Σ_{|γ| ≤ H} m_ρ |h_f(x_ρ) - h_f(x̄_ρ)|² ≤ K_J(η) · 10D/(3/4)^{5/2} · ∫|f|²` over every finite
family. -/
theorem sum_low_mult_norm_sub_sq_le (Z : ZeroConfig) {η D H : ℝ}
    (hη : ∀ ρ ∈ Z.carrier, |ρ.im| ≤ H → |ρ.re - 1 / 2| ≤ η)
    (hD : OffLineDensityBoundBelow Z H D) (J : ℕ) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : ∀ u, f u ≠ 0 → |u| ≤ J) (s : Finset Z.carrier) :
    ∑ ρ ∈ s, (if |(ρ : ℂ).im| ≤ H then
        (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 else 0) ≤
      plateauGramConst J η * (10 * D) / unitWeightFloor * ∫ u, ‖f u‖ ^ 2 := by
  classical
  rw [← Finset.sum_filter]
  set s' := s.filter (fun ρ : Z.carrier => |(ρ : ℂ).im| ≤ H) with hs'
  have hlow : ∀ ρ ∈ s', |(ρ : ℂ).im| ≤ H := fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hfs
  have hK := plateauGramConst_nonneg J η
  have hrow : ∀ ρ ∈ s', ∑ σ ∈ s', (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
      (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
        plateauGramConst J η * (10 * D) := by
    intro ρ hρ
    obtain ⟨hsum, hle⟩ := window_tsum_inv_sq_le (fun σ : Z.carrier => (σ : ℂ).im)
      (lowOffMult_nonneg Z H) hD (ρ : ℂ).im
    calc ∑ σ ∈ s', (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
          (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖
        ≤ ∑ σ ∈ s', plateauGramConst J η *
            (lowOffMult Z H σ / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2) := by
          refine Finset.sum_le_sum fun σ hσ => ?_
          have h := mult_mul_norm_gram_le_of_depth Z J ρ σ (hη ρ ρ.2 (hlow ρ hρ))
            (hη σ σ.2 (hlow σ hσ))
          rw [offLineMult_eq_lowOffMult Z (hlow σ hσ)] at h
          exact h.trans (le_of_eq (by ring))
      _ = plateauGramConst J η *
            ∑ σ ∈ s', lowOffMult Z H σ / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ plateauGramConst J η * (10 * D) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact (hsum.sum_le_tsum s' fun σ _ =>
            div_nonneg (lowOffMult_nonneg Z H σ) (by positivity)).trans hle
  have hcol : ∀ σ ∈ s', ∑ ρ ∈ s', (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
      (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖ ≤
        plateauGramConst J η * (10 * D) := by
    intro σ hσ
    obtain ⟨hsum, hle⟩ := window_tsum_inv_sq_le (fun ρ : Z.carrier => (ρ : ℂ).im)
      (lowOffMult_nonneg Z H) hD (σ : ℂ).im
    calc ∑ ρ ∈ s', (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
          (depthExp (gammaOf ρ) u * conj (depthExp (gammaOf σ) u))‖
        ≤ ∑ ρ ∈ s', plateauGramConst J η *
            (lowOffMult Z H ρ / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have h := mult_mul_norm_gram_le_of_depth' Z J ρ σ (hη ρ ρ.2 (hlow ρ hρ))
            (hη σ σ.2 (hlow σ hσ))
          rw [offLineMult_eq_lowOffMult Z (hlow ρ hρ)] at h
          exact h.trans (le_of_eq (by ring))
      _ = plateauGramConst J η *
            ∑ ρ ∈ s', lowOffMult Z H ρ / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ plateauGramConst J η * (10 * D) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact (hsum.sum_le_tsum s' fun ρ _ =>
            div_nonneg (lowOffMult_nonneg Z H ρ) (by positivity)).trans hle
  have h := weighted_bessel s' (m := fun ρ : Z.carrier => (Z.mult ρ : ℝ))
    (fun _ => Nat.cast_nonneg _) (φ := fun ρ : Z.carrier => depthExp (gammaOf ρ))
    (fun ρ => continuous_depthExp _) hf hcs (continuous_plateauWeight J)
    (hasCompactSupport_plateauWeight J) (plateauWeight_nonneg J) unitWeightFloor_pos
    (fun u hu => unitWeightFloor_le_plateauWeight (hfs u hu))
    (mul_nonneg hK (by linarith [hD.nonneg])) hrow hcol
  simp only [integral_mul_depthExp hf hcs] at h
  exact h

/-! ### Plain Bessel bound for the off-line zeros below a height -/

theorem integral_weight_cexp_mul_conj {h : ℝ → ℝ} (z w : ℂ) :
    ∫ u, (h u : ℂ) * (cexp (I * z * u) * conj (cexp (I * w * u))) =
      paperFT (fun u => (h u : ℂ)) (z - conj w) := by
  rw [paperFT_def]
  congr 1 with u
  rw [conj_cexp_I_mul, cexp_I_mul_mul, ← sub_eq_add_neg]

theorem norm_gram_cexp_le (J : ℕ) {η : ℝ} {z w : ℂ} (hz : |z.im| ≤ η) (hw : |w.im| ≤ η) :
    ‖∫ u, (plateauWeight J u : ℂ) * (cexp (I * z * u) * conj (cexp (I * w * u)))‖ ≤
      plateauGramConst J η / 4 / (1 + |z.re - w.re|) ^ 2 := by
  rw [integral_weight_cexp_mul_conj]
  refine (norm_paperFT_plateauWeight_le J _).trans ?_
  have him : |(z - conj w).im| ≤ 2 * η := by
    simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add]
    rw [abs_le] at hz hw ⊢; constructor <;> linarith
  have hre : (z - conj w).re = z.re - w.re := by simp
  rw [hre]
  unfold plateauGramConst
  have : (2 * (J : ℝ) + 1) * Real.exp (|(z - conj w).im| * (J + 1)) * 168 ≤
      (2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168 := by
    gcongr
  have hD : 0 < (1 + |z.re - w.re|) ^ 2 := by positivity
  calc (2 * (J : ℝ) + 1) * Real.exp (|(z - conj w).im| * (J + 1)) * 168 / (1 + |z.re - w.re|) ^ 2
      ≤ (2 * J + 1) * Real.exp (2 * η * (J + 1)) * 168 / (1 + |z.re - w.re|) ^ 2 := by gcongr
    _ = _ := by ring

theorem offLineMult_eq_mult (Z : ZeroConfig) {ρ : Z.carrier} (hρ : (ρ : ℂ).re ≠ 1 / 2) :
    offLineMult Z ρ = Z.mult ρ := by
  unfold offLineMult; rw [if_neg hρ]

/-- **Plain Bessel bound.**  For points `z_ρ` with `Re z_ρ = γ_ρ` and `|Im z_ρ| ≤ |β_ρ - ½|`, the
off-line zeros of ordinate at most `H` satisfy
`Σ m_ρ |h_f(z_ρ)|² ≤ (K_J(η)/4) · 10D/(3/4)^{5/2} · ∫|f|²`. -/
theorem sum_low_off_mult_norm_sq_le (Z : ZeroConfig) {η D H : ℝ}
    (hη : ∀ ρ ∈ Z.carrier, |ρ.im| ≤ H → |ρ.re - 1 / 2| ≤ η)
    (hD : OffLineDensityBoundBelow Z H D) (J : ℕ) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : ∀ u, f u ≠ 0 → |u| ≤ J) (zf : Z.carrier → ℂ)
    (hzre : ∀ ρ, (zf ρ).re = (ρ : ℂ).im) (hzim : ∀ ρ, |(zf ρ).im| ≤ |(ρ : ℂ).re - 1 / 2|)
    (s : Finset Z.carrier) :
    ∑ ρ ∈ s, (if |(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2 then
        (Z.mult ρ : ℝ) * ‖paperFT f (zf ρ)‖ ^ 2 else 0) ≤
      plateauGramConst J η / 4 * (10 * D) / unitWeightFloor * ∫ u, ‖f u‖ ^ 2 := by
  classical
  rw [← Finset.sum_filter]
  set s' := s.filter (fun ρ : Z.carrier => |(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2) with hs'
  have hmem : ∀ ρ ∈ s', |(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2 :=
    fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hfs
  have hK : 0 ≤ plateauGramConst J η / 4 := by have := plateauGramConst_nonneg J η; positivity
  have hzη : ∀ ρ ∈ s', |(zf ρ).im| ≤ η := fun ρ hρ =>
    (hzim ρ).trans (hη ρ ρ.2 (hmem ρ hρ).1)
  have hentry : ∀ ρ ∈ s', ∀ σ ∈ s', ‖∫ u, (plateauWeight J u : ℂ) *
      (cexp (I * zf ρ * u) * conj (cexp (I * zf σ * u)))‖ ≤
        plateauGramConst J η / 4 / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2 := by
    intro ρ hρ σ hσ
    have h := norm_gram_cexp_le J (hzη ρ hρ) (hzη σ hσ)
    rwa [hzre, hzre] at h
  have hmult : ∀ ρ ∈ s', (Z.mult ρ : ℝ) = lowOffMult Z H ρ := fun ρ hρ => by
    rw [← offLineMult_eq_lowOffMult Z (hmem ρ hρ).1, offLineMult_eq_mult Z (hmem ρ hρ).2]
  have hrow : ∀ ρ ∈ s', ∑ σ ∈ s', (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
      (cexp (I * zf ρ * u) * conj (cexp (I * zf σ * u)))‖ ≤
        plateauGramConst J η / 4 * (10 * D) := by
    intro ρ hρ
    obtain ⟨hsum, hle⟩ := window_tsum_inv_sq_le (fun σ : Z.carrier => (σ : ℂ).im)
      (lowOffMult_nonneg Z H) hD (ρ : ℂ).im
    calc ∑ σ ∈ s', (Z.mult σ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
          (cexp (I * zf ρ * u) * conj (cexp (I * zf σ * u)))‖
        ≤ ∑ σ ∈ s', plateauGramConst J η / 4 *
            (lowOffMult Z H σ / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2) := by
          refine Finset.sum_le_sum fun σ hσ => ?_
          rw [hmult σ hσ]
          have h := hentry ρ hρ σ hσ
          rw [abs_sub_comm] at h
          calc lowOffMult Z H σ * ‖∫ u, (plateauWeight J u : ℂ) *
                (cexp (I * zf ρ * u) * conj (cexp (I * zf σ * u)))‖
              ≤ lowOffMult Z H σ * (plateauGramConst J η / 4 /
                  (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2) :=
                mul_le_mul_of_nonneg_left h (lowOffMult_nonneg Z H σ)
            _ = _ := by ring
      _ = plateauGramConst J η / 4 *
            ∑ σ ∈ s', lowOffMult Z H σ / (1 + |(σ : ℂ).im - (ρ : ℂ).im|) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ plateauGramConst J η / 4 * (10 * D) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact (hsum.sum_le_tsum s' fun σ _ =>
            div_nonneg (lowOffMult_nonneg Z H σ) (by positivity)).trans hle
  have hcol : ∀ σ ∈ s', ∑ ρ ∈ s', (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
      (cexp (I * zf ρ * u) * conj (cexp (I * zf σ * u)))‖ ≤
        plateauGramConst J η / 4 * (10 * D) := by
    intro σ hσ
    obtain ⟨hsum, hle⟩ := window_tsum_inv_sq_le (fun ρ : Z.carrier => (ρ : ℂ).im)
      (lowOffMult_nonneg Z H) hD (σ : ℂ).im
    calc ∑ ρ ∈ s', (Z.mult ρ : ℝ) * ‖∫ u, (plateauWeight J u : ℂ) *
          (cexp (I * zf ρ * u) * conj (cexp (I * zf σ * u)))‖
        ≤ ∑ ρ ∈ s', plateauGramConst J η / 4 *
            (lowOffMult Z H ρ / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [hmult ρ hρ]
          calc lowOffMult Z H ρ * ‖∫ u, (plateauWeight J u : ℂ) *
                (cexp (I * zf ρ * u) * conj (cexp (I * zf σ * u)))‖
              ≤ lowOffMult Z H ρ * (plateauGramConst J η / 4 /
                  (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2) :=
                mul_le_mul_of_nonneg_left (hentry ρ hρ σ hσ) (lowOffMult_nonneg Z H ρ)
            _ = _ := by ring
      _ = plateauGramConst J η / 4 *
            ∑ ρ ∈ s', lowOffMult Z H ρ / (1 + |(ρ : ℂ).im - (σ : ℂ).im|) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ plateauGramConst J η / 4 * (10 * D) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact (hsum.sum_le_tsum s' fun ρ _ =>
            div_nonneg (lowOffMult_nonneg Z H ρ) (by positivity)).trans hle
  have h := weighted_bessel s' (m := fun ρ : Z.carrier => (Z.mult ρ : ℝ))
    (fun _ => Nat.cast_nonneg _) (φ := fun ρ : Z.carrier => fun u : ℝ => cexp (I * zf ρ * u))
    (fun ρ => by fun_prop) hf hcs (continuous_plateauWeight J)
    (hasCompactSupport_plateauWeight J) (plateauWeight_nonneg J) unitWeightFloor_pos
    (fun u hu => unitWeightFloor_le_plateauWeight (hfs u hu))
    (mul_nonneg hK (by linarith [hD.nonneg])) hrow hcol
  have hFT : ∀ ρ : Z.carrier, ∫ u, f u * cexp (I * zf ρ * u) = paperFT f (zf ρ) := fun ρ =>
    (paperFT_def f (zf ρ)).symm
  simp only [hFT] at h
  exact h

/-! ### Termwise bounds for the smoothed zero side -/

theorem exp_half_le_two_of_d9 : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- `Re(A B̄ c) ≥ -|A - B|²/4 - |A||B||c - r|` for `0 ≤ r ≤ 1`. -/
theorem re_mul_conj_mul_ge (A B c : ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    -(‖A - B‖ ^ 2 / 4) - ‖A‖ * ‖B‖ * ‖c - r‖ ≤ (A * conj B * c).re := by
  have hsplit : A * conj B * c = (r : ℂ) * (A * conj B) + A * conj B * (c - r) := by ring
  rw [hsplit, Complex.add_re, Complex.re_ofReal_mul]
  have h1 := neg_norm_sub_sq_div_four_le_re_mul_conj A B
  have h2 : -(‖A‖ * ‖B‖ * ‖c - r‖) ≤ (A * conj B * (c - r)).re := by
    have := Complex.abs_re_le_norm (A * conj B * (c - r))
    rw [norm_mul, norm_mul, Complex.norm_conj] at this
    linarith [neg_abs_le (A * conj B * (c - r)).re]
  have h3 : -(‖A - B‖ ^ 2 / 4) ≤ r * (A * conj B).re := by
    rcases le_or_gt 0 (A * conj B).re with h | h
    · have : 0 ≤ r * (A * conj B).re := mul_nonneg hr0 h
      have : 0 ≤ ‖A - B‖ ^ 2 / 4 := by positivity
      linarith
    · nlinarith
  linarith

theorem Wsummand_smoothedTest (Z : ZeroConfig) {b : ℝ} (hb : 0 ≤ b) {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (ρ : ℂ) :
    Z.Wsummand f (smoothedTest b f) ρ = (Z.mult ρ : ℂ) *
      (paperFT f (gammaOf ρ) * conj (paperFT f (conj (gammaOf ρ))) *
        kernelQ b (gammaOf ρ) ^ 2) := by
  rw [ZeroConfig.Wsummand, paperFT_smoothedTest hb hf hfc, map_mul, map_pow,
    conj_kernelQ_conj]
  ring

/-- **Low zeros.**  `Re W_ρ(f, g) ≥ -m_ρ|A - B|²/4 - m_ρ(|A|² + |B|²)/2 · 6b|β - ½|`, with
`A = h_f(x_ρ)` and `B = h_f(x̄_ρ)`. -/
theorem re_Wsummand_smoothedTest_ge_low (Z : ZeroConfig) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    -((Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 / 4) -
        (Z.mult ρ : ℝ) * ((‖paperFT f (gammaOf ρ)‖ ^ 2 + ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) / 2) *
          (6 * b * |ρ.re - 1 / 2|) ≤
      (Z.Wsummand f (smoothedTest b f) ρ).re := by
  set A := paperFT f (gammaOf ρ) with hA
  set B := paperFT f (conj (gammaOf ρ)) with hB
  set x := gammaOf ρ with hx
  obtain ⟨r, hr, hr0, -⟩ := kernelQ_real hb hb1 ρ.im
  have hst := Z.strip ρ hρ
  have hy : |ρ.re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
  have hr2 : r ^ 2 ≤ 1 := by linarith
  have hxγ : x - (ρ.im : ℂ) = I * ((1 / 2 - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hx, WeilEF.gammaOf_re]
    · simp [hx, WeilEF.gammaOf_im]
  have hnxγ : ‖x - (ρ.im : ℂ)‖ = |ρ.re - 1 / 2| := by
    rw [hxγ, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hlip := norm_kernelQ_sub_le hb hb1 (z₁ := x) (z₂ := (ρ.im : ℂ)) (by
    rw [hnxγ]; nlinarith [abs_nonneg (ρ.re - 1 / 2)])
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, mul_one] at hlip
  rw [hr, hnxγ] at hlip
  have hqx : ‖kernelQ b x‖ ≤ 2 := by
    refine (norm_kernelQ_le hb hb1 x).trans ?_
    have hxim : |x.im| ≤ 1 / 2 := by
      rw [hx, WeilEF.gammaOf_im, abs_sub_comm]; exact hy
    have : |x.im| * b ≤ 1 / 2 := by nlinarith [abs_nonneg x.im]
    exact (Real.exp_le_exp.mpr this).trans exp_half_le_two_of_d9
  have hr1 : |r| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hc : ‖kernelQ b x ^ 2 - ((r ^ 2 : ℝ) : ℂ)‖ ≤ 6 * b * |ρ.re - 1 / 2| := by
    have e : kernelQ b x ^ 2 - ((r ^ 2 : ℝ) : ℂ) = (kernelQ b x - r) * (kernelQ b x + r) := by
      push_cast; ring
    rw [e, norm_mul]
    have h2 : ‖kernelQ b x + r‖ ≤ 3 := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have h0 : 0 ≤ ‖kernelQ b x - r‖ := norm_nonneg _
    calc ‖kernelQ b x - r‖ * ‖kernelQ b x + r‖ ≤ (2 * b * |ρ.re - 1 / 2|) * 3 :=
          mul_le_mul hlip h2 (norm_nonneg _) (by positivity)
      _ = 6 * b * |ρ.re - 1 / 2| := by ring
  have hmain := re_mul_conj_mul_ge A B (kernelQ b x ^ 2) (sq_nonneg r) hr2
  have hAB : ‖A‖ * ‖B‖ ≤ (‖A‖ ^ 2 + ‖B‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  rw [Wsummand_smoothedTest Z hb.le hf hfc, show ((Z.mult ρ : ℕ) : ℂ) = ((Z.mult ρ : ℝ) : ℂ)
    by push_cast; rfl, Complex.re_ofReal_mul]
  have h6 : 0 ≤ 6 * b * |ρ.re - 1 / 2| := by positivity
  have hfin : ‖A‖ * ‖B‖ * ‖kernelQ b x ^ 2 - ((r ^ 2 : ℝ) : ℂ)‖ ≤
      (‖A‖ ^ 2 + ‖B‖ ^ 2) / 2 * (6 * b * |ρ.re - 1 / 2|) :=
    mul_le_mul hAB hc (norm_nonneg _) (by positivity)
  have hmain' : -(‖A - B‖ ^ 2 / 4) - (‖A‖ ^ 2 + ‖B‖ ^ 2) / 2 * (6 * b * |ρ.re - 1 / 2|) ≤
      (A * conj B * kernelQ b x ^ 2).re := by linarith
  have := mul_le_mul_of_nonneg_left hmain' hm
  nlinarith

/-- **High zeros.**  `Re W_ρ(f, g) ≥ -m_ρ e^a (∫|f|)² · e · 400²/(b⁶(1 + |γ|)⁴)`. -/
theorem re_Wsummand_smoothedTest_ge_high (Z : ZeroConfig) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hb1 : b ≤ 1) {f : ℝ → ℂ} (hf : Continuous f) (hfs : ∀ u, f u ≠ 0 → |u| ≤ a)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    -((Z.mult ρ : ℝ) * (Real.exp a * (∫ u, ‖f u‖) ^ 2) *
        (Real.exp 1 * 400 ^ 2 / (b ^ 6 * (1 + |ρ.im|) ^ 4))) ≤
      (Z.Wsummand f (smoothedTest b f) ρ).re := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hfs
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  have hst := Z.strip ρ hρ
  have hy : |1 / 2 - ρ.re| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
  have hN0 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
  have hA : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖paperFT f z‖ ≤ Real.exp (a / 2) * ∫ u, ‖f u‖ := by
    intro z hz
    refine (norm_paperFT_le hfi hfs z).trans ?_
    gcongr
    nlinarith
  have hx1 : |(gammaOf ρ).im| ≤ 1 / 2 := by rw [WeilEF.gammaOf_im]; exact hy
  have hx2 : |(conj (gammaOf ρ)).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg, WeilEF.gammaOf_im]; exact hy
  have hq := norm_kernelQ_le_decay hb hb1 (gammaOf ρ)
  rw [WeilEF.gammaOf_re] at hq
  have hqe : Real.exp (|(gammaOf ρ).im| * b) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (gammaOf ρ).im])
  have hq' : ‖kernelQ b (gammaOf ρ)‖ ≤ Real.exp (1 / 2) * 400 / (b ^ 3 * (1 + |ρ.im|) ^ 2) := by
    refine hq.trans ?_
    gcongr
  have hD : 0 < b ^ 3 * (1 + |ρ.im|) ^ 2 := by positivity
  have hq2 : ‖kernelQ b (gammaOf ρ) ^ 2‖ ≤ Real.exp 1 * 400 ^ 2 / (b ^ 6 * (1 + |ρ.im|) ^ 4) := by
    rw [norm_pow]
    calc ‖kernelQ b (gammaOf ρ)‖ ^ 2 ≤ (Real.exp (1 / 2) * 400 / (b ^ 3 * (1 + |ρ.im|) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hq' 2
      _ = Real.exp 1 * 400 ^ 2 / (b ^ 6 * (1 + |ρ.im|) ^ 4) := by
          rw [div_pow, mul_pow, ← Real.exp_nat_mul]
          congr 1
          · norm_num
          · ring
  have hAB : ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (conj (gammaOf ρ))‖ ≤
      Real.exp a * (∫ u, ‖f u‖) ^ 2 := by
    have h1 := hA _ hx1
    have h2 := hA _ hx2
    calc ‖paperFT f (gammaOf ρ)‖ * ‖paperFT f (conj (gammaOf ρ))‖
        ≤ (Real.exp (a / 2) * ∫ u, ‖f u‖) * (Real.exp (a / 2) * ∫ u, ‖f u‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = Real.exp a * (∫ u, ‖f u‖) ^ 2 := by
          rw [show Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) by
            rw [← Real.exp_add]; ring_nf]
          ring
  have hnorm : ‖Z.Wsummand f (smoothedTest b f) ρ‖ ≤ (Z.mult ρ : ℝ) *
      (Real.exp a * (∫ u, ‖f u‖) ^ 2) * (Real.exp 1 * 400 ^ 2 / (b ^ 6 * (1 + |ρ.im|) ^ 4)) := by
    rw [Wsummand_smoothedTest Z hb.le hf hfc, norm_mul, norm_mul, norm_mul, Complex.norm_conj,
      Complex.norm_natCast, ← mul_assoc]
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left hAB hm) hq2 (norm_nonneg _) (by positivity)
  have hre1 := Complex.abs_re_le_norm (Z.Wsummand f (smoothedTest b f) ρ)
  have hre2 := neg_abs_le (Z.Wsummand f (smoothedTest b f) ρ).re
  linarith

/-! ### Summation of the smoothed zero side -/

/-- The four error families of the smoothed zero side: the depth differences and the two phase
errors below height `H`, and the tail above it. -/
def lowDepthErr (Z : ZeroConfig) (H : ℝ) (f : ℝ → ℂ) (ρ : Z.carrier) : ℝ :=
  if |(ρ : ℂ).im| ≤ H then
    (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 else 0

def lowPhaseErr (Z : ZeroConfig) (H : ℝ) (f : ℝ → ℂ) (zf : Z.carrier → ℂ) (ρ : Z.carrier) : ℝ :=
  if |(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2 then (Z.mult ρ : ℝ) * ‖paperFT f (zf ρ)‖ ^ 2 else 0

def highTailErr (Z : ZeroConfig) (H : ℝ) (ρ : Z.carrier) : ℝ :=
  if |(ρ : ℂ).im| ≤ H then 0 else (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 4

theorem lowDepthErr_nonneg (Z : ZeroConfig) (H : ℝ) (f : ℝ → ℂ) (ρ : Z.carrier) :
    0 ≤ lowDepthErr Z H f ρ := by
  unfold lowDepthErr; split_ifs <;> positivity

theorem lowPhaseErr_nonneg (Z : ZeroConfig) (H : ℝ) (f : ℝ → ℂ) (zf : Z.carrier → ℂ)
    (ρ : Z.carrier) : 0 ≤ lowPhaseErr Z H f zf ρ := by
  unfold lowPhaseErr; split_ifs <;> positivity

theorem highTailErr_nonneg (Z : ZeroConfig) (H : ℝ) (ρ : Z.carrier) : 0 ≤ highTailErr Z H ρ := by
  unfold highTailErr; split_ifs <;> positivity

/-- The termwise bound, split into the four families. -/
theorem re_Wsummand_smoothedTest_ge_split (Z : ZeroConfig) {η H a b : ℝ}
    (hη : ∀ ρ ∈ Z.carrier, |ρ.im| ≤ H → |ρ.re - 1 / 2| ≤ η) (ha : 0 ≤ a) (hb : 0 < b)
    (hb1 : b ≤ 1) {f : ℝ → ℂ} (hf : Continuous f) (hfs : ∀ u, f u ≠ 0 → |u| ≤ a)
    (ρ : Z.carrier) :
    -(lowDepthErr Z H f ρ / 4 +
        3 * b * η * (lowPhaseErr Z H f (fun σ => gammaOf σ) ρ +
          lowPhaseErr Z H f (fun σ => conj (gammaOf σ)) ρ) +
        Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) * highTailErr Z H ρ) ≤
      (Z.Wsummand f (smoothedTest b f) ρ).re := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hfs
  unfold lowDepthErr lowPhaseErr highTailErr
  by_cases hlow : |(ρ : ℂ).im| ≤ H
  · have h := re_Wsummand_smoothedTest_ge_low Z hb hb1 hf hfc ρ.2
    have hy := hη ρ ρ.2 hlow
    have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
    rw [if_pos hlow, if_pos hlow]
    by_cases hon : (ρ : ℂ).re = 1 / 2
    · have hand : ¬(|(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2) := fun h => h.2 hon
      rw [if_neg hand, if_neg hand]
      rw [hon, sub_self, abs_zero, mul_zero, mul_zero] at h
      simp only [mul_zero, add_zero, sub_zero] at h ⊢
      linarith
    · have hand : |(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2 := ⟨hlow, hon⟩
      rw [if_pos hand, if_pos hand]
      simp only [mul_zero, add_zero]
      have hA := sq_nonneg ‖paperFT f (gammaOf ρ)‖
      have hB := sq_nonneg ‖paperFT f (conj (gammaOf ρ))‖
      have hk : (Z.mult (ρ : ℂ) : ℝ) * ((‖paperFT f (gammaOf ρ)‖ ^ 2 +
          ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) / 2) * (6 * b * |(ρ : ℂ).re - 1 / 2|) ≤
          3 * b * η * ((Z.mult (ρ : ℂ) : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 +
            (Z.mult (ρ : ℂ) : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) := by
        have hS : 0 ≤ (Z.mult (ρ : ℂ) : ℝ) * (‖paperFT f (gammaOf ρ)‖ ^ 2 +
            ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) := by positivity
        have h3 := mul_le_mul_of_nonneg_left hy (mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * b) hS)
        have e1 : (Z.mult (ρ : ℂ) : ℝ) * ((‖paperFT f (gammaOf ρ)‖ ^ 2 +
            ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) / 2) * (6 * b * |(ρ : ℂ).re - 1 / 2|) =
            3 * b * ((Z.mult (ρ : ℂ) : ℝ) * (‖paperFT f (gammaOf ρ)‖ ^ 2 +
              ‖paperFT f (conj (gammaOf ρ))‖ ^ 2)) * |(ρ : ℂ).re - 1 / 2| := by ring
        have e2 : 3 * b * η * ((Z.mult (ρ : ℂ) : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 +
            (Z.mult (ρ : ℂ) : ℝ) * ‖paperFT f (conj (gammaOf ρ))‖ ^ 2) =
            3 * b * ((Z.mult (ρ : ℂ) : ℝ) * (‖paperFT f (gammaOf ρ)‖ ^ 2 +
              ‖paperFT f (conj (gammaOf ρ))‖ ^ 2)) * η := by ring
        rw [e1, e2]; exact h3
      linarith
  · have h := re_Wsummand_smoothedTest_ge_high Z ha hb hb1 hf hfs ρ.2
    have hand : ¬(|(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2) := fun h => hlow h.1
    rw [if_neg hlow, if_neg hand, if_neg hand, if_neg hlow]
    have e : Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) *
        ((Z.mult (ρ : ℂ) : ℝ) / (1 + |(ρ : ℂ).im|) ^ 4) =
        (Z.mult (ρ : ℂ) : ℝ) * (Real.exp a * (∫ u, ‖f u‖) ^ 2) *
          (Real.exp 1 * 400 ^ 2 / (b ^ 6 * (1 + |(ρ : ℂ).im|) ^ 4)) := by
      field_simp
    rw [e]
    simpa using h

/-- The tail above height `H`: `Σ_{|γ| > H} m_ρ (1 + |γ|)^{-4} ≤ 24 A₀ log 3/(1 + H)`. -/
theorem highTailErr_summable_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {H : ℝ} (hH : 0 ≤ H) :
    Summable (highTailErr Z H) ∧
      ∑' ρ, highTailErr Z H ρ ≤ 24 * A₀ * Real.log 3 / (1 + H) := by
  obtain ⟨hws, hwle⟩ := window_tsum_le Z hA₀ hloc 0
  simp only [sub_zero, abs_zero, zero_add] at hws hwle
  have hpt : ∀ ρ : Z.carrier, highTailErr Z H ρ ≤
      1 / (1 + H) * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 3) := by
    intro ρ
    unfold highTailErr
    split_ifs with h
    · positivity
    · push Not at h
      have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
      have hD : 0 < 1 + |(ρ : ℂ).im| := by positivity
      rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (1 + H) * (1 + |(ρ : ℂ).im|) ^ 3 ≤ (1 + |(ρ : ℂ).im|) ^ 4 := by
        rw [pow_succ]; nlinarith [pow_pos hD 3]
      nlinarith
  have hs : Summable (highTailErr Z H) :=
    Summable.of_nonneg_of_le (highTailErr_nonneg Z H) hpt (hws.mul_left _)
  refine ⟨hs, ?_⟩
  calc ∑' ρ, highTailErr Z H ρ
      ≤ ∑' ρ : Z.carrier, 1 / (1 + H) * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 3) :=
        Summable.tsum_le_tsum hpt hs (hws.mul_left _)
    _ = 1 / (1 + H) * ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 3 := tsum_mul_left
    _ ≤ 1 / (1 + H) * (24 * A₀ * Real.log 3) :=
        mul_le_mul_of_nonneg_left hwle (by positivity)
    _ = 24 * A₀ * Real.log 3 / (1 + H) := by ring

/-- **The smoothed zero side.**  Let `Z` have the local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, and
let its zeros of ordinate at most `H` have depth at most `η` and off-line density at most `D`.  For
a continuous test on `[-a, a]` and `0 < b ≤ 1`, with `K = K_{⌈a⌉}(η)` and `c₀ = (3/4)^{5/2}`,
`Re W(f, g) ≥ -[K·10D/(4c₀) (1 + 6bη/2) ∫|f|² + e^a (∫|f|)² · e·400²/b⁶ · 24A₀ log 3/(1 + H)]`.
Only the zeros below `H` enter through `η` and `D`; above `H` the weight `q_b(x_ρ)²` decays like
`(1 + |γ|)^{-4}`. -/
theorem re_W_smoothedTest_ge (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {η D H a b : ℝ}
    (hη0 : 0 ≤ η) (hη : ∀ ρ ∈ Z.carrier, |ρ.im| ≤ H → |ρ.re - 1 / 2| ≤ η)
    (hD : OffLineDensityBoundBelow Z H D) (hH : 0 ≤ H) (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : ∀ u, f u ≠ 0 → |u| ≤ a) :
    -(plateauGramConst ⌈a⌉₊ η * (10 * D) / unitWeightFloor * (∫ u, ‖f u‖ ^ 2) / 4 +
        6 * b * η * (plateauGramConst ⌈a⌉₊ η / 4 * (10 * D) / unitWeightFloor *
          ∫ u, ‖f u‖ ^ 2) +
        Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) *
          (24 * A₀ * Real.log 3 / (1 + H))) ≤
      (Z.W f (smoothedTest b f)).re := by
  set J := ⌈a⌉₊ with hJ
  have hfsJ : ∀ u, f u ≠ 0 → |u| ≤ J := fun u hu => (hfs u hu).trans (Nat.le_ceil a)
  set F := ∫ u, ‖f u‖ ^ 2 with hF
  set B1 := plateauGramConst J η * (10 * D) / unitWeightFloor * F with hB1
  set B2 := plateauGramConst J η / 4 * (10 * D) / unitWeightFloor * F with hB2
  set K := Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) with hK
  set T := 24 * A₀ * Real.log 3 / (1 + H) with hT
  have hF0 : 0 ≤ F := integral_nonneg fun _ => sq_nonneg _
  have hD0 := hD.nonneg
  have hG0 := plateauGramConst_nonneg J η
  have hc0 := unitWeightFloor_pos
  have hB10 : 0 ≤ B1 := by positivity
  have hB20 : 0 ≤ B2 := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hT0 : 0 ≤ T := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  -- the four families
  have f1 : ∀ s : Finset Z.carrier, ∑ ρ ∈ s, lowDepthErr Z H f ρ ≤ B1 := fun s =>
    sum_low_mult_norm_sub_sq_le Z hη hD J hf hfsJ s
  have f2 : ∀ s : Finset Z.carrier, ∑ ρ ∈ s, lowPhaseErr Z H f (fun σ => gammaOf σ) ρ ≤ B2 :=
    fun s => sum_low_off_mult_norm_sq_le Z hη hD J hf hfsJ (fun σ => gammaOf σ)
      (fun σ => WeilEF.gammaOf_re _)
      (fun σ => by rw [WeilEF.gammaOf_im, abs_sub_comm]) s
  have f3 : ∀ s : Finset Z.carrier,
      ∑ ρ ∈ s, lowPhaseErr Z H f (fun σ => conj (gammaOf σ)) ρ ≤ B2 :=
    fun s => sum_low_off_mult_norm_sq_le Z hη hD J hf hfsJ (fun σ => conj (gammaOf σ))
      (fun σ => by rw [Complex.conj_re, WeilEF.gammaOf_re])
      (fun σ => by rw [Complex.conj_im, abs_neg, WeilEF.gammaOf_im, abs_sub_comm]) s
  obtain ⟨hs4, t4⟩ := highTailErr_summable_le Z hA₀ hloc hH
  set E : Z.carrier → ℝ := fun ρ => lowDepthErr Z H f ρ / 4 +
    3 * b * η * (lowPhaseErr Z H f (fun σ => gammaOf σ) ρ +
      lowPhaseErr Z H f (fun σ => conj (gammaOf σ)) ρ) + K * highTailErr Z H ρ with hE
  have hE0 : ∀ ρ, 0 ≤ E ρ := fun ρ => by
    have := lowDepthErr_nonneg Z H f ρ
    have := lowPhaseErr_nonneg Z H f (fun σ => gammaOf σ) ρ
    have := lowPhaseErr_nonneg Z H f (fun σ => conj (gammaOf σ)) ρ
    have := highTailErr_nonneg Z H ρ
    simp only [hE]; positivity
  have hEfin : ∀ s : Finset Z.carrier, ∑ ρ ∈ s, E ρ ≤ B1 / 4 + 3 * b * η * (B2 + B2) + K * T := by
    intro s
    have h4 : ∑ ρ ∈ s, highTailErr Z H ρ ≤ T :=
      (hs4.sum_le_tsum s fun ρ _ => highTailErr_nonneg Z H ρ).trans t4
    simp only [hE]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_add_distrib]
    have h1 := f1 s
    have h2 := f2 s
    have h3 := f3 s
    have hbη : 0 ≤ 3 * b * η := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add h2 h3) hbη
    have := mul_le_mul_of_nonneg_left h4 hK0
    linarith
  have hEs : Summable E := summable_of_sum_le hE0 hEfin
  have hEt := hEs.tsum_le_of_sum_le hEfin
  have hterm : ∀ ρ : Z.carrier, -E ρ ≤ (Z.Wsummand f (smoothedTest b f) ρ).re := fun ρ =>
    re_Wsummand_smoothedTest_ge_split Z hη ha hb hb1 hf hfs ρ
  have hbound : B1 / 4 + 3 * b * η * (B2 + B2) + K * T =
      plateauGramConst ⌈a⌉₊ η * (10 * D) / unitWeightFloor * F / 4 +
        6 * b * η * (plateauGramConst ⌈a⌉₊ η / 4 * (10 * D) / unitWeightFloor * F) +
        K * T := by rw [hB1, hB2, hJ]; ring
  by_cases hW : Summable (fun ρ : Z.carrier => Z.Wsummand f (smoothedTest b f) ρ)
  · rw [ZeroConfig.W, Complex.re_tsum hW]
    have hre : Summable (fun ρ : Z.carrier => (Z.Wsummand f (smoothedTest b f) ρ).re) :=
      (Complex.hasSum_re hW.hasSum).summable
    have hle := Summable.tsum_le_tsum hterm hEs.neg hre
    rw [tsum_neg] at hle
    linarith
  · rw [ZeroConfig.W, tsum_eq_zero_of_not_summable hW, Complex.zero_re]
    have : 0 ≤ B1 / 4 + 3 * b * η * (B2 + B2) + K * T := by positivity
    linarith

/-! ### The height reduction for `ζ` -/

/-- `E(a) = 10 + 68 e^{a+2}`, the exponent of the archimedean horizon at level `a`. -/
def zetaHorizonExp (a : ℝ) : ℝ := horizonExponent (Real.exp (2 * (a + 2)))

/-- The kernel width `b(a) = e^{-2E(a)}/4`. -/
def horizonKernelWidth (a : ℝ) : ℝ := Real.exp (-(2 * zetaHorizonExp a)) / 4

/-- The height `H(A₀, a) = 2(a+1) e^{a+1} · 400² · 24 A₀ log 3 / b(a)⁶` below which the zeros
determine the level-`a` form. -/
def zetaHorizonHeight (A₀ a : ℝ) : ℝ :=
  2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 * (24 * A₀ * Real.log 3) /
    horizonKernelWidth a ^ 6

theorem zetaHorizonExp_pos (a : ℝ) : 0 < zetaHorizonExp a := horizonExponent_pos _

theorem horizonKernelWidth_pos (a : ℝ) : 0 < horizonKernelWidth a := by
  unfold horizonKernelWidth; positivity

theorem horizonKernelWidth_le (a : ℝ) : horizonKernelWidth a ≤ 1 / 4 := by
  unfold horizonKernelWidth
  have : Real.exp (-(2 * zetaHorizonExp a)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [zetaHorizonExp_pos a])
  linarith

theorem zetaHorizonHeight_nonneg {A₀ a : ℝ} (hA₀ : 0 ≤ A₀) (ha : 0 ≤ a) :
    0 ≤ zetaHorizonHeight A₀ a := by
  unfold zetaHorizonHeight
  have := horizonKernelWidth_pos a
  have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  positivity

/-- `E (4b e^E)² = E e^{-2E} ≤ 1` at the kernel width `b = e^{-2E}/4`. -/
theorem horizon_symbol_error_le (a : ℝ) :
    horizonExponent (Real.exp (2 * (a + 2))) *
      (4 * horizonKernelWidth a * Real.exp (horizonExponent (Real.exp (2 * (a + 2))))) ^ 2 ≤ 1 := by
  have hE : zetaHorizonExp a = horizonExponent (Real.exp (2 * (a + 2))) := rfl
  rw [← hE]
  set E := zetaHorizonExp a
  have e : 4 * horizonKernelWidth a * Real.exp E = Real.exp (-E) := by
    unfold horizonKernelWidth
    rw [show 4 * (Real.exp (-(2 * E)) / 4) * Real.exp E = Real.exp (-(2 * E)) * Real.exp E by ring,
      ← Real.exp_add]
    ring_nf
  rw [e, ← Real.exp_nat_mul]
  have h := Real.add_one_le_exp (2 * E)
  have hE0 := zetaHorizonExp_pos a
  have hpos := Real.exp_pos (2 * E)
  have e2 : Real.exp ((2 : ℕ) * -E) = 1 / Real.exp (2 * E) := by
    rw [one_div, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [e2, mul_one_div, div_le_one hpos]
  linarith

/-- `1680(2J+1) e^{2η(J+1)} D/c₀ ≤ 3500 (2a+3) D e^{2η(a+2)}` for `J = ⌈a⌉`. -/
theorem plateau_constant_le {a η D : ℝ} (ha : 0 ≤ a) (hη0 : 0 ≤ η) (hD0 : 0 ≤ D) {F : ℝ}
    (hF : 0 ≤ F) :
    plateauGramConst ⌈a⌉₊ η * (10 * D) / unitWeightFloor * F / 4 ≤
      3500 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) * F := by
  set J := ⌈a⌉₊
  have hJa : (J : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
  have hc₀ := unitWeightFloor_ge
  have hc₀0 := unitWeightFloor_pos
  have he : Real.exp (2 * η * (J + 1)) ≤ Real.exp (2 * η * (a + 2)) := by
    apply Real.exp_le_exp.mpr
    have : (J : ℝ) + 1 ≤ a + 2 := by linarith
    nlinarith
  have hJ3 : 2 * (J : ℝ) + 1 ≤ 2 * a + 3 := by linarith
  have e1 : plateauGramConst J η * (10 * D) / unitWeightFloor * F / 4 =
      1680 * ((2 * J + 1) * Real.exp (2 * η * (J + 1)) * D * F) / unitWeightFloor := by
    unfold plateauGramConst; ring
  rw [e1, div_le_iff₀ hc₀0]
  have h2 : (2 * J + 1) * Real.exp (2 * η * (J + 1)) * D * F ≤
      (2 * a + 3) * Real.exp (2 * η * (a + 2)) * D * F := by
    have : 0 ≤ Real.exp (2 * η * (J + 1)) := (Real.exp_pos _).le
    gcongr
  have h3 : 0 ≤ (2 * a + 3) * Real.exp (2 * η * (a + 2)) * D * F := by positivity
  nlinarith

/-- The tail term is at most `∫|f|²` at the height `H(A₀, a)`. -/
theorem horizon_tail_le {A₀ a F N₁ : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 < a)
    (hN : N₁ ^ 2 ≤ 2 * a * F) :
    Real.exp a * N₁ ^ 2 * (Real.exp 1 * 400 ^ 2 / horizonKernelWidth a ^ 6) *
      (24 * A₀ * Real.log 3 / (1 + zetaHorizonHeight A₀ a)) ≤ F := by
  have hb := horizonKernelWidth_pos a
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set Q := Real.exp a * (Real.exp 1 * 400 ^ 2 / horizonKernelWidth a ^ 6) *
    (24 * A₀ * Real.log 3) with hQ
  have hQ0 : 0 < Q := by positivity
  have hH : zetaHorizonHeight A₀ a = 2 * (a + 1) * Q := by
    unfold zetaHorizonHeight; rw [hQ]; field_simp
  have hH0 : 0 < 1 + zetaHorizonHeight A₀ a := by rw [hH]; positivity
  have e : Real.exp a * N₁ ^ 2 * (Real.exp 1 * 400 ^ 2 / horizonKernelWidth a ^ 6) *
      (24 * A₀ * Real.log 3 / (1 + zetaHorizonHeight A₀ a)) =
      Q * N₁ ^ 2 / (1 + zetaHorizonHeight A₀ a) := by rw [hQ]; field_simp
  rw [e, div_le_iff₀ hH0, hH]
  have h1 : Q * N₁ ^ 2 ≤ Q * (2 * a * F) := mul_le_mul_of_nonneg_left hN hQ0.le
  nlinarith

/-- **The height reduction for `ζ`.**  There is `A₀` such that for every level `a > 0` and
`0 ≤ η ≤ ½`: if every zero of `ζ` of ordinate at most `H(A₀, a)` has `|β - ½| ≤ η`, and every unit
window below `H(A₀, a)` carries off-line multiplicity at most `D`, then every polar-constrained
`C²` test supported in `[-a, a]` satisfies
`Re W(f, f) ≥ -(7000 (2a + 3) D e^{2η(a+2)} + 2) ∫|f|²`.
Here `log H(A₀, a) ≤ 7000 e^a + log A₀ + 150` (`log_zetaHorizonHeight_le`): only the zeros below
the archimedean horizon `exp(O(e^a))` enter.

**Proof.**  `W(f, f) = W(f, g) + (W(f, f) - W(f, g))` with the smoothed test `g` of width
`b = e^{-2E}/4`.  The symbol side of the difference is at least `-E e^{-2E} ∫|f|²`
(`re_W_sub_W_smoothedTest_ge`).  The zero side of `W(f, g)` is bounded by the Bessel constant of
the zeros below `H`, the phase error `6bη`, and the tail above `H` (`re_W_smoothedTest_ge`). -/
theorem zeta_re_W_ge_of_depth_below_horizon :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a η D : ℝ, 0 < a → 0 ≤ η → η ≤ 1 / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ zetaHorizonHeight A₀ a → |ρ.re - 1 / 2| ≤ η) →
      OffLineDensityBoundBelow zetaZeroConfig (zetaHorizonHeight A₀ a) D →
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
        paperFT f (-(I / 2)) = 0 →
        -((7000 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) + 2) * ∫ u, ‖f u‖ ^ 2) ≤
          (zetaZeroConfig.W f f).re := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun a η D ha hη0 hη2 hη hD f hf hfs hp hm => ?_⟩
  set H := zetaHorizonHeight A₀ a with hHdef
  set b := horizonKernelWidth a with hbdef
  have hb := horizonKernelWidth_pos a
  have hb1 : b ≤ 1 := (horizonKernelWidth_le a).trans (by norm_num)
  have hH0 : 0 ≤ H := zetaHorizonHeight_nonneg (by linarith) ha.le
  have hfs' : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))
  set F := ∫ u, ‖f u‖ ^ 2 with hF
  have hF0 : 0 ≤ F := integral_nonneg fun _ => sq_nonneg _
  have hsym := re_W_sub_W_smoothedTest_ge hb hb1 hf hfs hp hm
  have hzero := re_W_smoothedTest_ge zetaZeroConfig hA₀ hloc hη0 hη hD hH0 ha.le hb hb1
    hf.continuous hfs'
  have hD0 := hD.nonneg
  -- the three error terms
  have hsymE := horizon_symbol_error_le a
  have hsym' : -F ≤ (zetaZeroConfig.W f f - zetaZeroConfig.W f (smoothedTest b f)).re := by
    refine le_trans ?_ hsym
    have := mul_le_mul_of_nonneg_right hsymE hF0
    linarith
  have hN : (∫ u, ‖f u‖) ^ 2 ≤ 2 * a * F :=
    sq_integral_norm_le_of_abs_support hf.continuous ha fun x hx => by
      by_contra h; exact absurd (hfs' x h) (not_le.mpr hx)
  have htail := horizon_tail_le hA₀ ha hN
  have hmain := plateau_constant_le ha.le hη0 hD0 hF0
  have hphase : 6 * b * η * (plateauGramConst ⌈a⌉₊ η / 4 * (10 * D) / unitWeightFloor * F) ≤
      plateauGramConst ⌈a⌉₊ η * (10 * D) / unitWeightFloor * F / 4 := by
    have h6 : 6 * b * η ≤ 1 := by
      have := horizonKernelWidth_le a
      nlinarith
    have hG0 := plateauGramConst_nonneg ⌈a⌉₊ η
    have hc0 := unitWeightFloor_pos
    have h0 : 0 ≤ plateauGramConst ⌈a⌉₊ η / 4 * (10 * D) / unitWeightFloor * F := by positivity
    have e : plateauGramConst ⌈a⌉₊ η * (10 * D) / unitWeightFloor * F / 4 =
        plateauGramConst ⌈a⌉₊ η / 4 * (10 * D) / unitWeightFloor * F := by ring
    rw [e]
    nlinarith
  have hsplit : (zetaZeroConfig.W f f).re = (zetaZeroConfig.W f (smoothedTest b f)).re +
      (zetaZeroConfig.W f f - zetaZeroConfig.W f (smoothedTest b f)).re := by
    rw [Complex.sub_re]; ring
  rw [hsplit]
  have hexp : 0 ≤ 3500 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) * F := by positivity
  nlinarith

/-- **The horizon is `exp(O(e^a))`.**  `log H(A₀, a) ≤ 7000 e^a + log A₀ + 160` for `a ≥ 0`. -/
theorem log_zetaHorizonHeight_le {A₀ a : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 ≤ a) :
    Real.log (zetaHorizonHeight A₀ a) ≤ 7000 * Real.exp a + Real.log A₀ + 160 := by
  obtain ⟨h5, h4, h6, -, he2, he1⟩ := exp_numeric_bounds
  set E := zetaHorizonExp a with hE
  have hsq : Real.sqrt (Real.exp (2 * (a + 2))) = Real.exp (a + 2) := by
    rw [show 2 * (a + 2) = (a + 2) + (a + 2) by ring, Real.exp_add,
      Real.sqrt_mul_self (Real.exp_pos _).le]
  have hEval : E = 10 + 68 * Real.exp (a + 2) := by
    rw [hE]; unfold zetaHorizonExp horizonExponent; rw [hsq]
  have hea : Real.exp (a + 2) = Real.exp a * Real.exp 2 := Real.exp_add _ _
  have hE12 : 12 * E ≤ 120 + 6120 * Real.exp a := by
    rw [hEval, hea]; nlinarith [Real.exp_pos a]
  have hb6 : 1 / horizonKernelWidth a ^ 6 = 4 ^ 6 * Real.exp (12 * E) := by
    unfold horizonKernelWidth
    rw [← hE, div_pow, one_div_div, ← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
    congr 2; push_cast; ring
  have hl3 : Real.log 3 ≤ Real.exp 1 := by
    have := Real.log_le_sub_one_of_pos (x := (3 : ℝ)) (by norm_num); linarith
  have h2a : 2 * (a + 1) ≤ Real.exp (a + 1) := by
    have h1 := mul_le_mul (Real.add_one_le_exp a) he1 (by norm_num) (Real.exp_pos a).le
    have : Real.exp (a + 1) = Real.exp a * Real.exp 1 := Real.exp_add _ _
    linarith
  have h400 : (400 : ℝ) ^ 2 ≤ Real.exp 12 := by
    rw [show (12 : ℝ) = 6 * 2 by norm_num, Real.exp_mul]
    exact_mod_cast pow_le_pow_left₀ (by norm_num) h6 2
  have h46 : (4 : ℝ) ^ 6 ≤ Real.exp 12 := by
    rw [show (12 : ℝ) = 2 * 6 by norm_num, Real.exp_mul]
    have : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [mul_le_mul he1 he1 (by norm_num) (by linarith)]
    exact_mod_cast pow_le_pow_left₀ (by norm_num) this 6
  have hH : zetaHorizonHeight A₀ a ≤
      A₀ * Real.exp (2 * a + 31 + 12 * E) := by
    unfold zetaHorizonHeight
    rw [div_eq_mul_one_div _ (horizonKernelWidth a ^ 6), hb6]
    have hexp : Real.exp (2 * a + 31 + 12 * E) = Real.exp (a + 1) * Real.exp a * Real.exp 1 *
        Real.exp 12 * Real.exp 4 * Real.exp 1 * Real.exp 12 * Real.exp (12 * E) := by
      simp only [← Real.exp_add]; ring_nf
    rw [hexp]
    have hl30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hA0 : 0 ≤ A₀ := by linarith
    have hpos : ∀ x, 0 < Real.exp x := Real.exp_pos
    calc 2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 * (24 * A₀ * Real.log 3) *
          (4 ^ 6 * Real.exp (12 * E))
        ≤ Real.exp (a + 1) * Real.exp a * Real.exp 1 * Real.exp 12 *
            (Real.exp 4 * A₀ * Real.exp 1) * (Real.exp 12 * Real.exp (12 * E)) := by
          gcongr
      _ = A₀ * (Real.exp (a + 1) * Real.exp a * Real.exp 1 * Real.exp 12 * Real.exp 4 *
            Real.exp 1 * Real.exp 12 * Real.exp (12 * E)) := by ring
  have hH0 : 0 < zetaHorizonHeight A₀ a := by
    unfold zetaHorizonHeight
    have := horizonKernelWidth_pos a
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have : 0 < A₀ := by linarith
    positivity
  calc Real.log (zetaHorizonHeight A₀ a) ≤ Real.log (A₀ * Real.exp (2 * a + 31 + 12 * E)) :=
        Real.log_le_log hH0 hH
    _ = Real.log A₀ + (2 * a + 31 + 12 * E) := by
        rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ 7000 * Real.exp a + Real.log A₀ + 160 := by
        have := Real.add_one_le_exp a
        nlinarith [Real.exp_pos a]

theorem OffLineDensityBoundBelow.mono {Z : ZeroConfig} {H T D : ℝ} (hHT : H ≤ T)
    (hD : OffLineDensityBoundBelow Z T D) : OffLineDensityBoundBelow Z H D := by
  intro t s hs
  refine le_trans (Finset.sum_le_sum fun ρ _ => ?_) (hD t s hs)
  unfold lowOffMult
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hHT) h2
  · exact offLineMult_nonneg Z ρ
  · exact le_rfl

/-- **`ζ`, zeros up to a height.**  If every zero of `ζ` up to height `T` has `|β - ½| ≤ η`, with
off-line density at most `D` there, then at every level `a` with `H(A₀, a) ≤ T` (in particular
whenever `7000 e^a + log A₀ + 160 ≤ log T`), every polar-constrained `C²` test on `[-a, a]` has
`Re W(f, f) ≥ -(7000 (2a + 3) D e^{2η(a+2)} + 2) ∫|f|²`.  For abstract configurations no such height
exists (`offLinePairConfig_eventually_relaxed_iff`). -/
theorem zeta_re_W_ge_of_depth_up_to_height :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a η D T : ℝ, 0 < a → 0 ≤ η → η ≤ 1 / 2 →
      zetaHorizonHeight A₀ a ≤ T →
      (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T → |ρ.re - 1 / 2| ≤ η) →
      OffLineDensityBoundBelow zetaZeroConfig T D →
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
        paperFT f (-(I / 2)) = 0 →
        -((7000 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) + 2) * ∫ u, ‖f u‖ ^ 2) ≤
          (zetaZeroConfig.W f f).re := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_re_W_ge_of_depth_below_horizon
  exact ⟨A₀, hA₀, fun a η D T ha hη0 hη2 hHT hη hD =>
    h a η D ha hη0 hη2 (fun ρ hρ hρH => hη ρ hρ (hρH.trans hHT)) (hD.mono hHT)⟩

/-- **The relaxed index of `ζ` from its zeros below the horizon.**  Under the hypotheses of
`zeta_re_W_ge_of_depth_below_horizon`, the relaxed Hodge index with exponent `θ` holds at level
`a` as soon as `7000 (2a + 3) D e^{2η(a+2)} + 2 ≤ e^{θa}`. -/
theorem zeta_relaxedHodgeIndexAtLevel_of_depth_below_horizon :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a η D θ : ℝ, 0 < a → 0 ≤ η → η ≤ 1 / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ zetaHorizonHeight A₀ a → |ρ.re - 1 / 2| ≤ η) →
      OffLineDensityBoundBelow zetaZeroConfig (zetaHorizonHeight A₀ a) D →
      7000 * (2 * a + 3) * D * Real.exp (2 * η * (a + 2)) + 2 ≤ Real.exp (θ * a) →
      RelaxedHodgeIndexAtLevel zetaZeroConfig θ a := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_re_W_ge_of_depth_below_horizon
  refine ⟨A₀, hA₀, fun a η D θ ha hη0 hη2 hη hD hθ f hf hfs hp hm => ?_⟩
  have hb := h a η D ha hη0 hη2 hη hD f hf hfs hp hm
  have hF : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have := mul_le_mul_of_nonneg_right hθ hF
  linarith

/-- **Finite verification.**  If every zero of `ζ` of ordinate at most `H(A₀, a)` lies on the
critical line, then every polar-constrained `C²` test on `[-a, a]` has
`Re W(f, f) ≥ -2 ∫|f|²`: the Riemann hypothesis below `exp(7000 e^a + O(1))` gives the level-`a`
Hodge index up to `2 ∫|f|²`. -/
theorem zeta_re_W_ge_neg_two_of_critical_below_horizon :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ, 0 < a →
      (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ zetaHorizonHeight A₀ a → ρ.re = 1 / 2) →
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
        paperFT f (-(I / 2)) = 0 → -(2 * ∫ u, ‖f u‖ ^ 2) ≤ (zetaZeroConfig.W f f).re := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_re_W_ge_of_depth_below_horizon
  refine ⟨A₀, hA₀, fun a ha hRH f hf hfs hp hm => ?_⟩
  have hη : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ zetaHorizonHeight A₀ a →
      |ρ.re - 1 / 2| ≤ 0 := fun ρ hρ hρH => by rw [hRH ρ hρ hρH, sub_self, abs_zero]
  have hD : OffLineDensityBoundBelow zetaZeroConfig (zetaHorizonHeight A₀ a) 0 := by
    intro t s _
    refine le_of_eq (Finset.sum_eq_zero fun ρ _ => ?_)
    unfold lowOffMult offLineMult
    split_ifs with h1 h2
    · rfl
    · exact absurd (hRH ρ ρ.2 h1) h2
    · rfl
  have hb := h a 0 0 ha le_rfl (by norm_num) hη hD f hf hfs hp hm
  simp only [mul_zero, zero_mul, zero_add] at hb
  exact hb

end RHTower
