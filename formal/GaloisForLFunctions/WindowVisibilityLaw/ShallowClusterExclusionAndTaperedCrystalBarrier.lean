import GaloisForLFunctions.WindowVisibilityLaw.CoherentClusterAndTiltAmplificationLaw
import GaloisForLFunctions.SquareRootThreshold.WindowedBlindnessForClustersAndProfiles
import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster
import GaloisForLFunctions.SquareRootThreshold.VisibilityTradeoffAndExcludedDepthLaw

/-!
# Shallow Coherent Phase Transition, Non-Lattice Hiding, and the Tapered Crystal Barrier

This module completes the shallow, non-lattice, and height-duality regimes of the window visibility
law (`B21`, `B22`, `Σ28`, `Σ41`, `A30`, `B18`):

* **Coherent shallow clusters vs `DCI` (`macroscopic_coherent_cluster_cancels_log_height`,
  `zeta_macroscopic_coherent_cluster_cancels_log_height`,
  `dci_admissible_coherent_cluster_visible_at_sub_depth`).** When a coherent cluster `S`
  (`|γ_q − γ₀| ≤ 1/(4a)`, `ρ_q.re ≥ ½ + δ`, `2 ≤ δa`) carries a fraction `c > 0` of the
  Riemann–von Mangoldt height density `A₀ log |γ₀|` — simultaneously admissible under unit-window
  RvM (`c ≤ 1`) and `DCI`'s `∑ δ_q² ≤ 40 σ_width² log(180|T|)` whenever `c A₀ δ² ≤ 40 σ_width²` —
  the `log |γ₀|` factor cancels identically from `windowPositiveAt_global_sea_cluster_bound`,
  forcing `c e^{2(δ − σ)a} ≤ 480 · 2^{26} δ (2a + 2π) e^{2π}` independent of height. Moreover, in
  a smooth `2L` RvM background (`multiplicityPairConfig`), `DCI`-admissible coherent clusters with
  `L ≤ k ≤ 20 L` are already visible (`onsetAperture < a`) down to the height-independent sub-depth
  threshold `3/2 < δ² a³` (`δ > √(3/2) a^{−3/2} ≪ 1/a`). Thus naive `(V2)` (`δ ≲ (log log T)/a`
  hides) fails for coherent shallow clusters across `a^{−3/2} ≪ δ ≲ (log log T)/a`.
* **Universal non-lattice shallow `(V2)` hiding law (`re_W_ge_of_onLineLattice_and_offLineDepthMass`,
  `windowPositiveAt_of_onLineLattice_and_offLineDepthMass`, `windowPositiveAt_runConfig`).** For
  any tempered configuration `Z` containing an on-line lattice of spacing `2π/L` (`a ≤ L/2`) and
  arbitrary (possibly countably infinite, non-lattice, coherent) off-line zeros of depth `≤ σ` and
  unit-window depth-squared mass `≤ W`, `WindowPositiveAt Z a` holds whenever
  `a² (2a + 2π) e^{2π} e^{2σa} W ≤ m₀ L` (`W ≲ L / a³` at shallow depths, matching the cubic
  seeing threshold `(2/3) k δ² a³ > L` to the exact power `a³`). Separated runs hide up to
  `2δa sinh(2δa) ≤ 1` regardless of run length.
* **Finite biquadratic tapered crystal packet & single-exponential height barrier
  (`re_W_biquadraticCrystal_ge`, `windowPositiveAt_biquadraticCrystal_of_le`,
  `exists_hidden_inv_aperture_zero_above_single_exp`).** Double summation by parts on the finite
  biquadratic depth profile `d_k = δ ((M² − (k − k₀)²)² / M⁴)` (`|k − k₀| < M`) cancels `u²`
  against `‖1 − e^{2πiu/L}‖² ≥ 16 u² / L²`, proving `WindowPositiveAt` whenever `4a ≤ L` and
  `38 a L δ² cosh(2δa) ≤ M`. Consequently, at depth `δ = 1/a` the single-exponential horizon
  `L ≍ a` (`T ≍ e^{ca}`) of `Σ28`/`Σ41` is an unbreakable barrier: for every `L ≥ 4a`, a finite
  tempered RvM configuration carries a zero of exact depth `1/a` yet satisfies
  `WindowPositiveAt Z a`.
* **Doubly-exponential height non-locality and contact-law zero exclusion
  (`doubly_exponential_height_nonlocality`, `zeta_abs_re_sub_half_lt_of_le_onsetAperture`,
  `contact_law_log_scale_cluster_bound`).** Two tempered RvM configurations agreeing identically on
  `|Im z| < exp((e^{2δa} − 2)/(4δ) − a)` have opposite window signs at half-width `a`, killing
  height-local truncation (`A30`); and `((c log T : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig` is
  directly a power-saving zero-exclusion bound (`B18`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower.CCMParityQuartet

/-! ### 1. Coherent shallow clusters vs `DCI` (`B21`): `log T` cancellation and `a^{−3/2}` seeing -/

/-- **Macroscopic coherent clusters cancel `log T` (`B21` vs `DCI`).**
In any configuration `Z` with `N(t, t+1] ≤ A₀ log(|t| + 3)`, suppose a coherent cluster `S`
(`|ρ.im − γ₀| ≤ 1/(4a)`, `ρ.re ≥ ½ + δ`, `2 ≤ δa`, `δ ≤ ½`) at height
`|γ₀| ≥ 6 + 1/(4a) + 3072 · 2^{26} A₀ log(|γ₀| + 3) (50a)⁷ e^a` carries multiplicity at least
`c · A₀ · log |γ₀|` (`c > 0`) — permitted simultaneously by RvM (`c ≤ 1`) and by `DCI`
(`∑ δ_q² ≤ 40 σ_width² log(180|T|)`) whenever `c A₀ δ² ≤ 40 σ_width²`. If all outside zeros have
depth `≤ σ`, then `WindowPositiveAt Z a` cancels `A₀ log |γ₀|` identically and forces the
**height-independent** inequality
`c e^{2(δ − σ)a} ≤ 480 · 2^{26} δ (2a + 2π) e^{2π}`. -/
theorem macroscopic_coherent_cluster_cancels_log_height (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {γ₀ a δ σ c : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hδa : 2 ≤ δ * a)
    (hσ : 0 ≤ σ)
    (hγ₀ : 6 + 1 / (4 * a) +
      3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a ≤ |γ₀|)
    (hpos : WindowPositiveAt Z a)
    (S : Finset ℂ) (hSc : ∀ ρ ∈ S, ρ ∈ Z.carrier)
    (hSδ : ∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) (hSγ : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a))
    (hmass : c * A₀ * Real.log |γ₀| ≤ ∑ ρ ∈ S, (Z.mult ρ : ℝ))
    (hsea : ∀ ρ ∈ Z.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) :
    c * Real.exp (2 * (δ - σ) * a) ≤
      480 * 2 ^ 26 * δ * (2 * a + 2 * π) * Real.exp (2 * π) := by
  have ha : 0 < a := by
    by_contra hle; push Not at hle; nlinarith
  have hγ6 : 6 ≤ |γ₀| := by
    have h1 : 0 ≤ 1 / (4 * a) := by positivity
    have h2 : 0 ≤ 3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a := by
      have := one_le_log_abs_add_three γ₀; positivity
    linarith
  have hlog_pos : 0 < Real.log |γ₀| := Real.log_pos (by linarith)
  have hSne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hmass
    have : 0 < c * A₀ * Real.log |γ₀| := by positivity
    linarith
  have hsea_bound := windowPositiveAt_global_sea_cluster_bound Z hA₀ hloc hδ hδ' hδa hσ hpos
    S hSne hSc hSδ hSγ hsea
  set X := |γ₀| + 1 / (4 * a) +
    3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a + 6
  have hX_le_sq : X ≤ |γ₀| ^ 2 := by
    have hX2 : X ≤ 2 * |γ₀| := by dsimp [X]; linarith
    nlinarith
  have hX_pos : 0 < X := by
    have := one_le_log_abs_add_three γ₀
    dsimp [X]
    positivity
  have hlog_X : Real.log X ≤ 2 * Real.log |γ₀| := by
    calc Real.log X ≤ Real.log (|γ₀| ^ 2) := Real.log_le_log hX_pos hX_le_sq
      _ = 2 * Real.log |γ₀| := by rw [Real.log_pow]; ring
  have hlhs : (1 / 2) * (c * A₀ * Real.log |γ₀|) * Real.exp (2 * (δ - σ) * a) ≤
      (1 / 2) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * Real.exp (2 * (δ - σ) * a) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num))
      (Real.exp_pos _).le
  have hrhs : 120 * 2 ^ 26 * A₀ * δ * (2 * a + 2 * π) * Real.exp (2 * π) * Real.log X ≤
      120 * 2 ^ 26 * A₀ * δ * (2 * a + 2 * π) * Real.exp (2 * π) * (2 * Real.log |γ₀|) :=
    mul_le_mul_of_nonneg_left hlog_X (by positivity)
  have hcomb : (c * Real.exp (2 * (δ - σ) * a)) * ((1 / 2) * A₀ * Real.log |γ₀|) ≤
      (480 * 2 ^ 26 * δ * (2 * a + 2 * π) * Real.exp (2 * π)) *
        ((1 / 2) * A₀ * Real.log |γ₀|) := by
    have h1 : (c * Real.exp (2 * (δ - σ) * a)) * ((1 / 2) * A₀ * Real.log |γ₀|) =
        (1 / 2) * (c * A₀ * Real.log |γ₀|) * Real.exp (2 * (δ - σ) * a) := by ring
    have h2 : (480 * 2 ^ 26 * δ * (2 * a + 2 * π) * Real.exp (2 * π)) *
          ((1 / 2) * A₀ * Real.log |γ₀|) =
        120 * 2 ^ 26 * A₀ * δ * (2 * a + 2 * π) * Real.exp (2 * π) * (2 * Real.log |γ₀|) := by
      ring
    rw [h1, h2]
    exact hlhs.trans (hsea_bound.trans hrhs)
  exact le_of_mul_le_mul_right hcomb (by positivity)

/-- **Unconditional `ζ` instantiation of `log T` cancellation for macroscopic coherent clusters**,
paired directly with `DCI`'s unconditional unit-window depth-mass bound
`sum_sq_im_xiSpectralPoint_window_le`. -/
theorem zeta_macroscopic_coherent_cluster_cancels_log_height :
    (∀ T : ℝ, 4 ≤ |T| → ∀ s : Finset XiZeroCopy,
      (∀ q ∈ s, |(xiSpectralPoint q).re - T| ≤ 1) →
      ∑ q ∈ s, (xiSpectralPoint q).im ^ 2 ≤ 40 * zetaZeroWidth ^ 2 * Real.log (180 * |T|)) ∧
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ {γ₀ a δ σ c : ℝ}, 0 < c → 0 < δ → δ ≤ 1 / 2 → 2 ≤ δ * a → 0 ≤ σ →
        6 + 1 / (4 * a) +
          3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a ≤ |γ₀| →
        ZetaWindowPositive a →
        ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) →
          (∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) → (∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a)) →
          c * A₀ * Real.log |γ₀| ≤ ∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ) →
          (∀ ρ ∈ zetaZeroConfig.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) →
          c * Real.exp (2 * (δ - σ) * a) ≤
            480 * 2 ^ 26 * δ * (2 * a + 2 * π) * Real.exp (2 * π) := by
  refine ⟨fun _ hT s hs => sum_sq_im_xiSpectralPoint_window_le hT s hs, ?_⟩
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun hc hδ hδ' hδa hσ hγ₀ hpos S hSc hSδ hSγ hmass hsea =>
    macroscopic_coherent_cluster_cancels_log_height zetaZeroConfig hA₀ hloc hc hδ hδ' hδa hσ hγ₀
      ((windowPositiveAt_zeta_iff _).mpr hpos) S hSc hSδ hSγ hmass hsea⟩

/-- **Sub-depth coherent visibility (`δ > √(3/2) a^{−3/2}`) of `DCI`-admissible clusters (`B21`).**
In `multiplicityPairConfig k hk hL hδ hδ' γ₀` with `L ≤ k ≤ 20 L`:
1. Every zero of `Z` has critical depth `|ρ.re − ½| ≤ δ` (so `δ` is the exact zero width of `Z`),
   and the total off-line depth-squared mass across the entire configuration is `2 k δ² ≤ 40 δ² L`,
   satisfying `DCI`'s unit-window bound `40 σ_Z² L` globally;
2. Yet for **every** `0 < a ≤ L/2` with `3 / 2 < δ ^ 2 * a ^ 3` — including arbitrarily shallow
   sub-depths `δa → 0` as `a → ∞` — `onsetAperture Z < a` (`¬ WindowPositiveAt Z a`). -/
theorem dci_admissible_coherent_cluster_visible_at_sub_depth (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ)
    (hk_low : L ≤ (k : ℝ)) (hk_dci : (k : ℝ) ≤ 20 * L)
    {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) (hsub : 3 / 2 < δ ^ 2 * a ^ 3) :
    (∀ ρ ∈ (multiplicityPairConfig k hk hL hδ hδ' γ₀).carrier, |ρ.re - 1 / 2| ≤ δ) ∧
      2 * (k : ℝ) * δ ^ 2 ≤ 40 * δ ^ 2 * L ∧
      onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) < (a : EReal) := by
  refine ⟨?_, by nlinarith, ?_⟩
  · rintro _ ((⟨m, rfl⟩ | h) | h)
    · simp only [verticalLatticePoint, add_zero, sub_self, abs_zero]; exact hδ.le
    · rw [Set.mem_singleton_iff] at h; subst h
      simp only [offLinePoint, add_sub_cancel_left, abs_of_pos hδ]; exact le_rfl
    · rw [Set.mem_singleton_iff] at h; subst h
      simp only [offLinePoint, add_sub_cancel_left, abs_neg, abs_of_pos hδ]; exact le_rfl
  · refine onsetAperture_multiplicityPairConfig_lt_of_lt_cubic k hk hL hδ hδ' γ₀ ha haL ?_
    calc L ≤ (k : ℝ) * 1 := by linarith
      _ < (k : ℝ) * (2 / 3 * δ ^ 2 * a ^ 3) := by
          have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
          exact mul_lt_mul_of_pos_left (by linarith) hkpos
      _ = 2 / 3 * (k : ℝ) * δ ^ 2 * a ^ 3 := by ring

/-! ### 2. Universal non-lattice shallow `(V2)` hiding law and separated run law (`B22`) -/

/-- On the critical line `ρ.re = 1/2`, `Wsummand f f ρ` is real and equals `m_ρ ‖paperFT f ρ.im‖²`. -/
theorem re_Wsummand_onLine_eq (Z : ZeroConfig) (f : ℝ → ℂ) {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    (Z.Wsummand f f ρ).re = (Z.mult ρ : ℝ) * ‖paperFT f ρ.im‖ ^ 2 := by
  have hg : gammaOf ρ = (ρ.im : ℂ) := by
    apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im, hre]
  rw [ZeroConfig.Wsummand, hg, Complex.conj_ofReal, mul_assoc, Complex.mul_conj',
    ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem re_Wsummand_onLine_nonneg (Z : ZeroConfig) (f : ℝ → ℂ) {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    0 ≤ (Z.Wsummand f f ρ).re := by
  rw [re_Wsummand_onLine_eq Z f hre]
  positivity

/-- Single-zero lower bound without reflection pairing:
`Re Wsummand(ρ) ≥ −(m_ρ / 4) ‖paperFT f (gammaOf ρ) − paperFT f (conj (gammaOf ρ))‖²`. -/
theorem neg_quarter_norm_sub_sq_le_re_Wsummand (Z : ZeroConfig) (f : ℝ → ℂ) (ρ : ℂ) :
    -(Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 / 4 ≤
      (Z.Wsummand f f ρ).re := by
  set u := paperFT f (gammaOf ρ)
  set v := paperFT f (conj (gammaOf ρ))
  have huv : -(‖u - v‖ ^ 2 / 4) ≤ (u * conj v).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (u.re + v.re), sq_nonneg (u.im + v.im)]
  have hre : (Z.Wsummand f f ρ).re = (Z.mult ρ : ℝ) * (u * conj v).re := by
    rw [ZeroConfig.Wsummand, mul_assoc, ← Complex.ofReal_natCast, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre]
  have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left huv hm0
  linarith

/-- Every `C²` compactly supported test on a tempered configuration has summable `Wsummand`. -/
theorem summable_Wsummand_of_tempered {Z : ZeroConfig} (hZ : TemperedConfig Z) {a : ℝ}
    (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    Summable (fun τ : Z.carrier => Z.Wsummand f f τ) := by
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu =>
    abs_le.mpr (hfs (subset_tsupport f hu))
  set C := Real.exp a * (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num)
      (add_nonneg (integral_nonneg fun _ => norm_nonneg _)
        (integral_nonneg fun _ => norm_nonneg _)))
  set maj : Z.carrier → ℝ := fun τ =>
    4 / 3 * C ^ 2 * ((Z.mult τ : ℝ) / (1 + Complex.normSq (gammaOf τ)))
  refine Summable.of_norm_bounded (hZ.mul_left (4 / 3 * C ^ 2)) fun τ => ?_
  have him := GaloisForLFunctions.ArithmeticCastelnuovoSeveri.abs_im_gammaOf_le Z τ
  have him_conj : |(conj (gammaOf τ)).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact him
  have hb1 : ‖paperFT f (gammaOf τ)‖ ≤ C / (1 + |(gammaOf τ).re|) ^ 2 :=
    (RHTower.norm_paperFT_le_decay hf hsupp (gammaOf τ)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (gammaOf τ).im])) (by positivity))
        (by positivity))
  have hb2 : ‖paperFT f (conj (gammaOf τ))‖ ≤ C / (1 + |(conj (gammaOf τ)).re|) ^ 2 :=
    (RHTower.norm_paperFT_le_decay hf hsupp (conj (gammaOf τ))).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (conj (gammaOf τ)).im])) (by positivity))
        (by positivity))
  have hb2' : ‖paperFT f (conj (gammaOf τ))‖ ≤ C :=
    hb2.trans (div_le_self hC0 (one_le_pow₀ (by linarith [abs_nonneg (conj (gammaOf τ)).re])))
  have hden : 1 / (1 + |(gammaOf τ).re|) ^ 2 ≤ (4 / 3) / (1 + Complex.normSq (gammaOf τ)) := by
    rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
      (by nlinarith [mul_self_nonneg (gammaOf τ).re, mul_self_nonneg (gammaOf τ).im])]
    have h1 : (gammaOf τ).im * (gammaOf τ).im ≤ 1 / 4 := by nlinarith [abs_le.mp him]
    nlinarith [abs_nonneg (gammaOf τ).re, sq_abs (gammaOf τ).re]
  have hb1' : ‖paperFT f (gammaOf τ)‖ ≤ C * ((4 / 3) / (1 + Complex.normSq (gammaOf τ))) := by
    refine hb1.trans ?_
    rw [div_eq_mul_one_div C]
    exact mul_le_mul_of_nonneg_left hden hC0
  rw [ZeroConfig.Wsummand, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
  have hm0 : (0 : ℝ) ≤ Z.mult τ := Nat.cast_nonneg _
  have hN : 0 < 1 + Complex.normSq (gammaOf τ) := by
    linarith [Complex.normSq_nonneg (gammaOf τ)]
  calc (Z.mult τ : ℝ) * ‖paperFT f (gammaOf τ)‖ * ‖paperFT f (conj (gammaOf τ))‖
      ≤ (Z.mult τ : ℝ) * (C * ((4 / 3) / (1 + Complex.normSq (gammaOf τ)))) * C :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb1' hm0) hb2' (norm_nonneg _)
          (mul_nonneg hm0 (mul_nonneg hC0 (div_nonneg (by norm_num) hN.le)))
    _ = maj τ := by dsimp [maj]; ring

/-- Depth-weighted conjugate-difference sampling on any finite off-line subset of `Z.carrier`. -/
theorem sum_offLine_norm_sub_sq_le_of_depthWeighted (Z : ZeroConfig) {a σ W : ℝ}
    (ha : 0 < a) (hσ : 0 ≤ σ)
    (hdepth : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → |ρ.re - 1 / 2| ≤ σ)
    (hW : ∀ (T : ℝ) (F : Finset ℂ),
      (∀ ρ ∈ F, ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - T| ≤ 1) →
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 ≤ W)
    {f : ℝ → ℂ} (hf : Continuous f) (hfs : tsupport f ⊆ Icc (-a) a)
    (E : Finset ℂ) (hEc : ∀ ρ ∈ E, ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2) :
    ∑ ρ ∈ E, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 ≤
      4 * a ^ 2 * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * W *
        ∫ u, ‖f u‖ ^ 2 := by
  classical
  have hf_src : IntervalSource a f :=
    { continuous := hf
      hasCompactSupport := hasCompactSupport_of_tsupport_subset_Icc hfs
      vanish := fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (hfs hm) }
  let ι := Σ ρ : E, Fin (Z.mult ρ)
  let x : ι → ℝ := fun q => (q.1 : ℂ).im
  let y : ι → ℝ := fun q => 1 / 2 - (q.1 : ℂ).re
  have hy : ∀ q : ι, |y q| ≤ σ := fun q => by
    dsimp [y]; rw [abs_sub_comm]; exact hdepth q.1 (hEc q.1 q.1.2).1 (hEc q.1 q.1.2).2
  have hW_ι : ∀ (T : ℝ) (t : Finset ι), t ⊆ Finset.univ →
      (∀ q ∈ t, |x q - T| ≤ 1) → ∑ q ∈ t, y q ^ 2 ≤ W := by
    intro T t _ ht
    have hsub : t ⊆ Finset.univ.filter (fun q : ι => |x q - T| ≤ 1) := fun q hq =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ q, ht q hq⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans ?_
    have heq : (∑ q ∈ Finset.univ.filter (fun q : ι => |x q - T| ≤ 1), y q ^ 2) =
        ∑ ρ ∈ E.filter (fun ρ => |ρ.im - T| ≤ 1), (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 := by
      rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_filter]
      refine (Finset.sum_congr rfl fun ρ _ => ?_).trans
        (Finset.univ_eq_attach (s := E) ▸ Finset.sum_attach E
          fun ρ => if |ρ.im - T| ≤ 1 then (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 else 0)
      by_cases h : |(ρ : ℂ).im - T| ≤ 1
      · simp only [x, y, h, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      · simp [x, h]
    rw [heq]
    exact hW T (E.filter fun ρ => |ρ.im - T| ≤ 1) fun ρ hρ => by
      obtain ⟨hE, hT⟩ := Finset.mem_filter.mp hρ
      exact ⟨(hEc ρ hE).1, (hEc ρ hE).2, hT⟩
  have hs := sum_norm_sq_testTransform_sub_conj_le_of_depthWeighted' ha hf_src x y hσ hy
    Finset.univ hW_ι
  have hft_eq : ∀ z, paperFT f z = testTransform f z := fun _ => rfl
  have hsum : (∑ q : ι, ‖testTransform f ((x q : ℂ) + (y q : ℂ) * I) -
      testTransform f ((x q : ℂ) - (y q : ℂ) * I)‖ ^ 2) =
      ∑ ρ ∈ E, (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 := by
    rw [Fintype.sum_sigma]
    refine (Finset.sum_congr rfl fun ρ _ => ?_).trans
      (Finset.univ_eq_attach (s := E) ▸ Finset.sum_attach E
        fun ρ => (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2)
    have hg1 : ((ρ : ℂ).im : ℂ) + ((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) * I = gammaOf ρ := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    have hg2 : ((ρ : ℂ).im : ℂ) - ((1 / 2 - (ρ : ℂ).re : ℝ) : ℂ) * I = conj (gammaOf ρ) := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    dsimp only [x, y]
    rw [hg1, hg2, ← hft_eq, ← hft_eq]
    simp
  rwa [hsum] at hs

/-- **General non-lattice quantitative Weil floor under bounded unit-window depth mass.**
For any tempered configuration `Z` containing `Set.range (verticalLatticePoint L 0)` with
multiplicity at least `m₀` (`a ≤ L/2`), if all off-line zeros of `Z` have depth `≤ σ` and unit-window
depth-squared mass `≤ W`, then for every `C²` test `f` supported in `[−a, a]` (`0 < a ≤ L/2`),
`Re W_Z(f, f) ≥ (m₀ L − a² (2a + 2π) e^{2π} e^{2σa} W) ∫ ‖f‖²`. -/
theorem re_W_ge_of_onLineLattice_and_offLineDepthMass {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {L a σ W : ℝ} (hL : 0 < L) (ha : 0 < a) (haL : a ≤ L / 2) (hσ : 0 ≤ σ)
    (m₀ : ℕ) (hsub : Set.range (verticalLatticePoint L 0) ⊆ Z.carrier)
    (hmult : ∀ k : ℤ, m₀ ≤ Z.mult (verticalLatticePoint L 0 k))
    (hdepth : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → |ρ.re - 1 / 2| ≤ σ)
    (hW : ∀ (T : ℝ) (F : Finset ℂ),
      (∀ ρ ∈ F, ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - T| ≤ 1) →
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 ≤ W)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ((m₀ : ℝ) * L - a ^ 2 * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * W) *
        ∫ u, ‖f u‖ ^ 2 ≤
      (Z.W f f).re := by
  classical
  have hfsL : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Icc_subset_Icc (by linarith) haL)
  -- Reference configuration giving the lattice exact multiplicity `2`
  let Z₀ := isolatedPairConfig hL (show (0 : ℝ) < 1 / 4 by norm_num) (by norm_num) 0
  have hZ₀_mult : ∀ k : ℤ, Z₀.mult (verticalLatticePoint L 0 k) = 2 := fun k => by
    change (if (verticalLatticePoint L 0 k).re = 1 / 2 then 2 else 1) = 2
    rw [if_pos (by simp [verticalLatticePoint])]
  have hlat_sum := hasSum_Wsummand_onLineLattice Z₀ hL hZ₀_mult hf hf.continuous hfsL hfsL
  have hlat_re : HasSum
      (fun ρ : Set.range (verticalLatticePoint L 0) => (m₀ : ℝ) / 2 * (Z₀.Wsummand f f ρ).re)
      ((m₀ : ℝ) * L * ∫ u, ‖f u‖ ^ 2) := by
    have h1 := (Complex.hasSum_re hlat_sum).mul_left ((m₀ : ℝ) / 2)
    have hval : (m₀ : ℝ) / 2 * (2 * (L : ℂ) * ∫ t, f t * conj (f t)).re =
        (m₀ : ℝ) * L * ∫ u, ‖f u‖ ^ 2 := by
      rw [integral_mul_conj_self_eq,
        show (2 * (L : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) =
          ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
      ring
    rwa [hval] at h1
  -- Embed the on-line lattice into `Z.carrier`
  let emb : Set.range (verticalLatticePoint L 0) → Z.carrier := fun ρ => ⟨ρ.1, hsub ρ.2⟩
  have hemb_inj : Function.Injective emb := fun ρ₁ ρ₂ h =>
    Subtype.ext (congrArg (fun x : Z.carrier => (x : ℂ)) h)
  set onTerm : Z.carrier → ℝ := fun τ =>
    if (τ : ℂ) ∈ Set.range (verticalLatticePoint L 0) then
      (m₀ : ℝ) / 2 * (Z₀.Wsummand f f τ).re
    else 0
  have hon_hasSum : HasSum onTerm ((m₀ : ℝ) * L * ∫ u, ‖f u‖ ^ 2) := by
    refine (hemb_inj.hasSum_iff ?_).mp ?_
    · intro τ hτ
      have hnot : (τ : ℂ) ∉ Set.range (verticalLatticePoint L 0) := fun hm =>
        hτ ⟨⟨τ.1, hm⟩, Subtype.ext rfl⟩
      dsimp only [onTerm]
      exact if_neg hnot
    · refine hlat_re.congr_fun fun ρ => ?_
      dsimp only [Function.comp_apply, onTerm, emb]
      exact if_pos ρ.2
  -- Off-line conjugate-difference majorant
  set offTerm : Z.carrier → ℝ := fun τ =>
    if (τ : ℂ).re ≠ 1 / 2 then
      (Z.mult τ : ℝ) * ‖paperFT f (gammaOf τ) - paperFT f (conj (gammaOf τ))‖ ^ 2 / 4
    else 0
  have hoff_nn : ∀ τ : Z.carrier, 0 ≤ offTerm τ := fun τ => by
    dsimp [offTerm]; split_ifs <;> positivity
  set K := a ^ 2 * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * W *
    ∫ u, ‖f u‖ ^ 2
  have hoff_fin : ∀ s : Finset Z.carrier, ∑ τ ∈ s, offTerm τ ≤ K := by
    intro s
    set s' := s.filter (fun τ : Z.carrier => (τ : ℂ).re ≠ 1 / 2)
    let E : Finset ℂ := s'.map ⟨Subtype.val, Subtype.val_injective⟩
    have hEc : ∀ ρ ∈ E, ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2 := by
      intro ρ hρ
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_map.mp hρ
      exact ⟨τ.2, (Finset.mem_filter.mp hτ).2⟩
    have hsum_eq : ∑ τ ∈ s, offTerm τ =
        (1 / 4) * ∑ ρ ∈ E,
          (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ) - paperFT f (conj (gammaOf ρ))‖ ^ 2 := by
      dsimp [offTerm, E, s']
      rw [← Finset.sum_filter, Finset.sum_map, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Function.Embedding.coeFn_mk]
      ring
    rw [hsum_eq]
    have hbound := sum_offLine_norm_sub_sq_le_of_depthWeighted Z ha hσ hdepth hW
      hf.continuous hfs E hEc
    dsimp [K]
    linarith
  have hoff_summ : Summable offTerm := summable_of_sum_le hoff_nn hoff_fin
  have hoff_tsum : ∑' τ : Z.carrier, offTerm τ ≤ K := hoff_summ.tsum_le_of_sum_le hoff_fin
  -- Pointwise comparison `onTerm τ - offTerm τ ≤ (Z.Wsummand f f τ).re`
  have hpt : ∀ τ : Z.carrier, onTerm τ - offTerm τ ≤ (Z.Wsummand f f τ).re := by
    intro τ
    by_cases hre : (τ : ℂ).re = 1 / 2
    · have hoff0 : offTerm τ = 0 := by
        dsimp only [offTerm]
        exact if_neg (not_not.mpr hre)
      rw [hoff0, sub_zero]
      by_cases hmem : (τ : ℂ) ∈ Set.range (verticalLatticePoint L 0)
      · have h1 : onTerm τ = (m₀ : ℝ) / 2 * (Z₀.Wsummand f f τ).re := by
          dsimp only [onTerm]
          exact if_pos hmem
        obtain ⟨k, hk⟩ := hmem
        rw [h1, re_Wsummand_onLine_eq Z₀ f hre, re_Wsummand_onLine_eq Z f hre, ← hk,
          hZ₀_mult k]
        have hm : (m₀ : ℝ) ≤ Z.mult (verticalLatticePoint L 0 k) := by exact_mod_cast hmult k
        have hsq : 0 ≤ ‖paperFT f (verticalLatticePoint L 0 k).im‖ ^ 2 := sq_nonneg _
        nlinarith
      · have hon0 : onTerm τ = 0 := by
          dsimp only [onTerm]
          exact if_neg hmem
        rw [hon0]
        exact re_Wsummand_onLine_nonneg Z f hre
    · have hnot_lat : (τ : ℂ) ∉ Set.range (verticalLatticePoint L 0) := by
        rintro ⟨k, hk⟩
        apply hre
        rw [← hk]
        simp [verticalLatticePoint]
      have hon0 : onTerm τ = 0 := by
        dsimp only [onTerm]
        exact if_neg hnot_lat
      have hoff_eq : offTerm τ =
          (Z.mult τ : ℝ) * ‖paperFT f (gammaOf τ) - paperFT f (conj (gammaOf τ))‖ ^ 2 / 4 := by
        dsimp only [offTerm]
        exact if_pos hre
      rw [hon0, hoff_eq, zero_sub]
      linarith [neg_quarter_norm_sub_sq_le_re_Wsummand Z f τ]
  have hW_summ : Summable (fun τ : Z.carrier => (Z.Wsummand f f τ).re) :=
    (Complex.hasSum_re (summable_Wsummand_of_tempered hZ ha.le hf hfs).hasSum).summable
  rw [ZeroConfig.W, Complex.re_tsum (summable_Wsummand_of_tempered hZ ha.le hf hfs)]
  calc ((m₀ : ℝ) * L - a ^ 2 * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * W) *
          ∫ u, ‖f u‖ ^ 2
      = (m₀ : ℝ) * L * (∫ u, ‖f u‖ ^ 2) - K := by dsimp [K]; ring
    _ ≤ (∑' τ : Z.carrier, onTerm τ) - ∑' τ : Z.carrier, offTerm τ := by
        rw [hon_hasSum.tsum_eq]
        linarith
    _ = ∑' τ : Z.carrier, (onTerm τ - offTerm τ) :=
        (hon_hasSum.summable.tsum_sub hoff_summ).symm
    _ ≤ ∑' τ : Z.carrier, (Z.Wsummand f f τ).re :=
        Summable.tsum_le_tsum hpt (hon_hasSum.summable.sub hoff_summ) hW_summ

/-- **Universal non-lattice shallow `(V2)` hiding law.**
Any tempered configuration `Z` containing an on-line lattice of spacing `2π/L` with multiplicity
`≥ m₀` (`0 < a ≤ L/2`) and arbitrary (finite or countably infinite, non-lattice, coherent or
spread) off-line zeros of depth `≤ σ` and unit-window depth-squared mass `≤ W` satisfies
`WindowPositiveAt Z a` (and `(a : EReal) ≤ onsetAperture Z`) whenever
`a² (2a + 2π) e^{2π} e^{2σa} W ≤ m₀ L`. -/
theorem windowPositiveAt_of_onLineLattice_and_offLineDepthMass {Z : ZeroConfig}
    (hZ : TemperedConfig Z) {L a σ W : ℝ} (hL : 0 < L) (ha : 0 < a) (haL : a ≤ L / 2)
    (hσ : 0 ≤ σ) (m₀ : ℕ) (hsub : Set.range (verticalLatticePoint L 0) ⊆ Z.carrier)
    (hmult : ∀ k : ℤ, m₀ ≤ Z.mult (verticalLatticePoint L 0 k))
    (hdepth : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → |ρ.re - 1 / 2| ≤ σ)
    (hW : ∀ (T : ℝ) (F : Finset ℂ),
      (∀ ρ ∈ F, ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - T| ≤ 1) →
      ∑ ρ ∈ F, (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 ≤ W)
    (hhide : a ^ 2 * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * W ≤
      (m₀ : ℝ) * L) :
    WindowPositiveAt Z a ∧ (a : EReal) ≤ onsetAperture Z := by
  have hpos : WindowPositiveAt Z a := fun f hf hfs => by
    have hge := re_W_ge_of_onLineLattice_and_offLineDepthMass hZ hL ha haL hσ m₀ hsub hmult
      hdepth hW hf hfs
    have hint : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hdiff : 0 ≤ (m₀ : ℝ) * L -
        a ^ 2 * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * W := by linarith
    exact (mul_nonneg hdiff hint).trans hge
  exact ⟨hpos, le_onsetAperture_of_windowPositiveAt ha.le hpos⟩

/-- **Separated off-line run hiding law (`B22`).** Every lattice run of constant depth `δ` and
arbitrary length `N` is window-positive at half-width `a` (`(a : EReal) ≤ onsetAperture`) whenever
`4a ≤ L` and `2δa sinh(2δa) ≤ 1`. -/
theorem windowPositiveAt_runConfig {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 ≤ a) (haL : 4 * a ≤ L) (hδa : 2 * δ * a * Real.sinh (2 * δ * a) ≤ 1)
    (k₀ : ℤ) (N : ℕ) :
    WindowPositiveAt (runConfig hL hδ hδ' (runSet k₀ N)) a ∧
      (a : EReal) ≤ onsetAperture (runConfig hL hδ hδ' (runSet k₀ N)) := by
  have hpos : WindowPositiveAt (runConfig hL hδ hδ' (runSet k₀ N)) a :=
    fun _ hf hfs => re_W_runConfig_nonneg hL hδ hδ' ha haL hδa k₀ N hf hfs
  exact ⟨hpos, le_onsetAperture_of_windowPositiveAt ha hpos⟩

/-! ### 3. Finite biquadratic tapered crystal packet and the single-exponential barrier (`Σ28`/`Σ41`) -/

/-- The finite integer support `{k₀ − M + 1, …, k₀ + M − 1}` of half-span `M`. -/
def taperedSupport (k₀ : ℤ) (M : ℕ) : Finset ℤ :=
  Finset.Ioo (k₀ - (M : ℤ)) (k₀ + (M : ℤ))

/-- The biquadratic depth polynomial `δ ((M² − (x − k₀)²)² / M⁴)`. -/
def biquadraticPoly (k₀ : ℤ) (M : ℕ) (δ x : ℝ) : ℝ :=
  δ * (((M : ℝ) ^ 2 - (x - (k₀ : ℝ)) ^ 2) ^ 2 / (M : ℝ) ^ 4)

/-- The discrete biquadratic depth profile on `ℤ`. -/
def biquadraticProfile (k₀ : ℤ) (M : ℕ) (δ : ℝ) (k : ℤ) : ℝ :=
  biquadraticPoly k₀ M δ (k : ℝ)

theorem mem_taperedSupport_iff {k₀ k : ℤ} {M : ℕ} :
    k ∈ taperedSupport k₀ M ↔ |k - k₀| < (M : ℤ) := by
  rw [taperedSupport, Finset.mem_Ioo, abs_lt]
  omega

theorem center_mem_taperedSupport (k₀ : ℤ) {M : ℕ} (hM : 1 ≤ M) :
    k₀ ∈ taperedSupport k₀ M := by
  rw [mem_taperedSupport_iff, sub_self, abs_zero]
  omega

theorem biquadraticProfile_center (k₀ : ℤ) {M : ℕ} (hM : 1 ≤ M) (δ : ℝ) :
    biquadraticProfile k₀ M δ k₀ = δ := by
  unfold biquadraticProfile biquadraticPoly
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [sub_self]
  field_simp [hM0]
  ring

theorem biquadraticProfile_pos (k₀ : ℤ) {M : ℕ} {δ : ℝ} (hδ : 0 < δ) {k : ℤ}
    (hk : k ∈ taperedSupport k₀ M) : 0 < biquadraticProfile k₀ M δ k := by
  rw [mem_taperedSupport_iff] at hk
  have hMpos : 0 < (M : ℝ) := by
    have : (0 : ℤ) < (M : ℤ) := lt_of_le_of_lt (abs_nonneg _) hk
    exact_mod_cast this
  have habs : |(k : ℝ) - (k₀ : ℝ)| < (M : ℝ) := by exact_mod_cast hk
  have hsq : ((k : ℝ) - (k₀ : ℝ)) ^ 2 < (M : ℝ) ^ 2 := by
    rw [← sq_abs ((k : ℝ) - (k₀ : ℝ))]
    exact pow_lt_pow_left₀ habs (abs_nonneg _) (by norm_num)
  unfold biquadraticProfile biquadraticPoly
  have hdiff : 0 < (M : ℝ) ^ 2 - ((k : ℝ) - (k₀ : ℝ)) ^ 2 := by linarith
  positivity

theorem biquadraticProfile_le (k₀ : ℤ) (M : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {k : ℤ}
    (hk : k ∈ taperedSupport k₀ M) : biquadraticProfile k₀ M δ k ≤ δ := by
  rw [mem_taperedSupport_iff] at hk
  have hMpos : 0 < (M : ℝ) := by
    have : (0 : ℤ) < (M : ℤ) := lt_of_le_of_lt (abs_nonneg _) hk
    exact_mod_cast this
  have habs : |(k : ℝ) - (k₀ : ℝ)| < (M : ℝ) := by exact_mod_cast hk
  have hsq : ((k : ℝ) - (k₀ : ℝ)) ^ 2 ≤ (M : ℝ) ^ 2 := by
    rw [← sq_abs ((k : ℝ) - (k₀ : ℝ))]
    exact (pow_lt_pow_left₀ habs (abs_nonneg _) (by norm_num)).le
  unfold biquadraticProfile biquadraticPoly
  have hsub_le : ((M : ℝ) ^ 2 - ((k : ℝ) - (k₀ : ℝ)) ^ 2) ^ 2 ≤ (M : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((k : ℝ) - (k₀ : ℝ))]
  have hdiv : ((M : ℝ) ^ 2 - ((k : ℝ) - (k₀ : ℝ)) ^ 2) ^ 2 / (M : ℝ) ^ 4 ≤ 1 :=
    (div_le_one (by positivity)).mpr hsub_le
  nlinarith

/-- On `|k − k₀| ≤ M` (including `|k − k₀| = M`), `zeroExt` agrees with `biquadraticPoly`. -/
private theorem zeroExt_biquadratic_eq_poly (k₀ : ℤ) (M : ℕ) (δ : ℝ) {k : ℤ}
    (hk : |k - k₀| ≤ (M : ℤ)) :
    zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) k =
      biquadraticPoly k₀ M δ (k : ℝ) := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · rw [zeroExt, if_pos (mem_taperedSupport_iff.mpr hlt), biquadraticProfile]
  · have hnot : k ∉ taperedSupport k₀ M := by
      rw [mem_taperedSupport_iff]; omega
    rw [zeroExt, if_neg hnot]
    unfold biquadraticPoly
    have habs : |(k : ℝ) - (k₀ : ℝ)| = (M : ℝ) := by exact_mod_cast heq
    have hsq : ((k : ℝ) - (k₀ : ℝ)) ^ 2 = (M : ℝ) ^ 2 := by
      rw [← sq_abs ((k : ℝ) - (k₀ : ℝ)), habs]
    rw [hsq, sub_self]
    simp

/-- First-difference bound for the zero-extended biquadratic taper: supported on
`Icc (k₀ − M + 1) (k₀ + M)` and bounded everywhere by `4 δ / M`. -/
private theorem biquadratic_first_diff_bound (k₀ : ℤ) {M : ℕ} (hM : 2 ≤ M) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ k : ℤ, k ∉ Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ)) →
      zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) k -
        zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 1) = 0) ∧
    ∀ k : ℤ,
      |zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) k -
        zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 1)| ≤ 4 * δ / (M : ℝ) := by
  set g := zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hout : ∀ k : ℤ, k ∉ Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ)) → g k - g (k - 1) = 0 := by
    intro k hk
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    have h1 : k ∉ taperedSupport k₀ M := by
      rw [mem_taperedSupport_iff, abs_lt]; omega
    have h2 : k - 1 ∉ taperedSupport k₀ M := by
      rw [mem_taperedSupport_iff, abs_lt]; omega
    simp [g, zeroExt, h1, h2]
  refine ⟨hout, fun k => ?_⟩
  by_cases hk : k ∈ Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ))
  · rw [Finset.mem_Icc] at hk
    have hk1 : |k - k₀| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    have hk2 : |k - 1 - k₀| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    rw [show g k = biquadraticPoly k₀ M δ (k : ℝ) from zeroExt_biquadratic_eq_poly k₀ M δ hk1,
      show g (k - 1) = biquadraticPoly k₀ M δ ((k - 1 : ℤ) : ℝ) from
        zeroExt_biquadratic_eq_poly k₀ M δ hk2]
    unfold biquadraticPoly
    set t : ℝ := (k : ℝ) - (k₀ : ℝ)
    have ht_lo : -(M : ℝ) + 1 ≤ t := by
      dsimp [t]; exact_mod_cast (show -(M : ℤ) + 1 ≤ k - k₀ by omega)
    have ht_hi : t ≤ (M : ℝ) := by
      dsimp [t]; exact_mod_cast (show k - k₀ ≤ (M : ℤ) by omega)
    have hsub : ((k - 1 : ℤ) : ℝ) - (k₀ : ℝ) = t - 1 := by dsimp [t]; push_cast; ring
    rw [hsub, ← mul_sub, ← sub_div, abs_mul, abs_of_nonneg hδ, abs_div,
      abs_of_pos (by positivity : 0 < (M : ℝ) ^ 4)]
    have hident : ((M : ℝ) ^ 2 - t ^ 2) ^ 2 - ((M : ℝ) ^ 2 - (t - 1) ^ 2) ^ 2 =
        (1 - 2 * t) * (((M : ℝ) ^ 2 - t ^ 2) + ((M : ℝ) ^ 2 - (t - 1) ^ 2)) := by ring
    have hf1 : |1 - 2 * t| ≤ 2 * (M : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
    have hf2_nn : 0 ≤ ((M : ℝ) ^ 2 - t ^ 2) + ((M : ℝ) ^ 2 - (t - 1) ^ 2) := by
      have h1 : t ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
      have h2 : (t - 1) ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
      linarith
    have hf2_le : ((M : ℝ) ^ 2 - t ^ 2) + ((M : ℝ) ^ 2 - (t - 1) ^ 2) ≤ 2 * (M : ℝ) ^ 2 := by
      nlinarith [sq_nonneg t, sq_nonneg (t - 1)]
    have hnum : |((M : ℝ) ^ 2 - t ^ 2) ^ 2 - ((M : ℝ) ^ 2 - (t - 1) ^ 2) ^ 2| ≤
        4 * (M : ℝ) ^ 3 := by
      rw [hident, abs_mul, abs_of_nonneg hf2_nn]
      calc |1 - 2 * t| * (((M : ℝ) ^ 2 - t ^ 2) + ((M : ℝ) ^ 2 - (t - 1) ^ 2))
          ≤ (2 * (M : ℝ)) * (2 * (M : ℝ) ^ 2) :=
            mul_le_mul hf1 hf2_le hf2_nn (by positivity)
        _ = 4 * (M : ℝ) ^ 3 := by ring
    calc δ * (|((M : ℝ) ^ 2 - t ^ 2) ^ 2 - ((M : ℝ) ^ 2 - (t - 1) ^ 2) ^ 2| / (M : ℝ) ^ 4)
        ≤ δ * (4 * (M : ℝ) ^ 3 / (M : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) hδ
      _ = 4 * δ / (M : ℝ) := by field_simp [hMpos.ne']
  · rw [hout k hk, abs_zero]
    positivity

/-- Second-difference bound for the zero-extended biquadratic taper: supported on
`Icc (k₀ − M + 1) (k₀ + M + 1)` and bounded everywhere by `8 δ / M²`. -/
private theorem biquadratic_second_diff_bound (k₀ : ℤ) {M : ℕ} (hM : 2 ≤ M) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (∀ k : ℤ, k ∉ Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ) + 1) →
      zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) k -
        2 * zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 1) +
        zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 2) = 0) ∧
    ∀ k : ℤ,
      |zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) k -
        2 * zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 1) +
        zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 2)| ≤
        8 * δ / (M : ℝ) ^ 2 := by
  set g := zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
  obtain ⟨hd1_out, _⟩ := biquadratic_first_diff_bound k₀ hM hδ
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hout : ∀ k : ℤ, k ∉ Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ) + 1) →
      g k - 2 * g (k - 1) + g (k - 2) = 0 := by
    intro k hk
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
    have h1 : g k - g (k - 1) = 0 := hd1_out k (by rw [Finset.mem_Icc]; omega)
    have h2 : g (k - 1) - g (k - 1 - 1) = 0 := hd1_out (k - 1) (by rw [Finset.mem_Icc]; omega)
    rw [show k - 2 = k - 1 - 1 by omega]
    linarith
  refine ⟨hout, fun k => ?_⟩
  by_cases hk : k ∈ Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ) + 1)
  · rw [Finset.mem_Icc] at hk
    by_cases hleft : k = k₀ - (M : ℤ) + 1
    · subst hleft
      have hg1 : g (k₀ - (M : ℤ) + 1 - 1) = 0 :=
        zeroExt_eq_zero (by rw [mem_taperedSupport_iff, abs_lt]; omega)
      have hg2 : g (k₀ - (M : ℤ) + 1 - 2) = 0 :=
        zeroExt_eq_zero (by rw [mem_taperedSupport_iff, abs_lt]; omega)
      have hk0 : |k₀ - (M : ℤ) + 1 - k₀| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
      rw [hg1, hg2, mul_zero, sub_zero, add_zero,
        show g (k₀ - (M : ℤ) + 1) = biquadraticPoly k₀ M δ ((k₀ - (M : ℤ) + 1 : ℤ) : ℝ) from
          zeroExt_biquadratic_eq_poly k₀ M δ hk0]
      unfold biquadraticPoly
      have hval : ((k₀ - (M : ℤ) + 1 : ℤ) : ℝ) - (k₀ : ℝ) = 1 - (M : ℝ) := by push_cast; ring
      rw [hval, show (M : ℝ) ^ 2 - (1 - (M : ℝ)) ^ 2 = 2 * (M : ℝ) - 1 by ring, abs_of_nonneg
        (by positivity)]
      have hsq : (2 * (M : ℝ) - 1) ^ 2 ≤ 4 * (M : ℝ) ^ 2 := by nlinarith
      calc δ * ((2 * (M : ℝ) - 1) ^ 2 / (M : ℝ) ^ 4)
          ≤ δ * (4 * (M : ℝ) ^ 2 / (M : ℝ) ^ 4) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity)) hδ
        _ = 4 * δ / (M : ℝ) ^ 2 := by field_simp [hMpos.ne']
        _ ≤ 8 * δ / (M : ℝ) ^ 2 := div_le_div_of_nonneg_right (by linarith) (by positivity)
    · by_cases hright : k = k₀ + (M : ℤ) + 1
      · subst hright
        have hg0 : g (k₀ + (M : ℤ) + 1) = 0 :=
          zeroExt_eq_zero (by rw [mem_taperedSupport_iff, abs_lt]; omega)
        have hg1 : g (k₀ + (M : ℤ) + 1 - 1) = 0 :=
          zeroExt_eq_zero (by rw [mem_taperedSupport_iff, abs_lt]; omega)
        have hk2 : |k₀ + (M : ℤ) + 1 - 2 - k₀| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        rw [hg0, hg1, mul_zero, sub_zero, zero_add,
          show g (k₀ + (M : ℤ) + 1 - 2) =
            biquadraticPoly k₀ M δ ((k₀ + (M : ℤ) + 1 - 2 : ℤ) : ℝ) from
              zeroExt_biquadratic_eq_poly k₀ M δ hk2]
        unfold biquadraticPoly
        have hval : ((k₀ + (M : ℤ) + 1 - 2 : ℤ) : ℝ) - (k₀ : ℝ) = (M : ℝ) - 1 := by
          push_cast; ring
        rw [hval, show (M : ℝ) ^ 2 - ((M : ℝ) - 1) ^ 2 = 2 * (M : ℝ) - 1 by ring,
          abs_of_nonneg (by positivity)]
        have hsq : (2 * (M : ℝ) - 1) ^ 2 ≤ 4 * (M : ℝ) ^ 2 := by nlinarith
        calc δ * ((2 * (M : ℝ) - 1) ^ 2 / (M : ℝ) ^ 4)
            ≤ δ * (4 * (M : ℝ) ^ 2 / (M : ℝ) ^ 4) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity)) hδ
          _ = 4 * δ / (M : ℝ) ^ 2 := by field_simp [hMpos.ne']
          _ ≤ 8 * δ / (M : ℝ) ^ 2 := div_le_div_of_nonneg_right (by linarith) (by positivity)
      · -- Interior range `k₀ - M + 2 ≤ k ≤ k₀ + M`: all three points lie in `[k₀ - M, k₀ + M]`
        have hk0_in : |k - k₀| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        have hk1_in : |k - 1 - k₀| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        have hk2_in : |k - 2 - k₀| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
        rw [show g k = biquadraticPoly k₀ M δ (k : ℝ) from zeroExt_biquadratic_eq_poly k₀ M δ hk0_in,
          show g (k - 1) = biquadraticPoly k₀ M δ ((k - 1 : ℤ) : ℝ) from
            zeroExt_biquadratic_eq_poly k₀ M δ hk1_in,
          show g (k - 2) = biquadraticPoly k₀ M δ ((k - 2 : ℤ) : ℝ) from
            zeroExt_biquadratic_eq_poly k₀ M δ hk2_in]
        unfold biquadraticPoly
        set s : ℝ := ((k - 1 : ℤ) : ℝ) - (k₀ : ℝ)
        have hs_lo : -((M : ℝ) - 1) ≤ s := by
          have h1 : -(M : ℤ) + 1 ≤ k - 1 - k₀ := by omega
          have h2 : ((-(M : ℤ) + 1 : ℤ) : ℝ) ≤ ((k - 1 - k₀ : ℤ) : ℝ) := Int.cast_le.mpr h1
          dsimp [s]
          push_cast at h2 ⊢
          linarith
        have hs_hi : s ≤ (M : ℝ) - 1 := by
          dsimp [s]; push_cast
          exact_mod_cast (show k - 1 - k₀ ≤ (M : ℤ) - 1 by omega)
        have ht0 : (k : ℝ) - (k₀ : ℝ) = s + 1 := by dsimp [s]; push_cast; ring
        have ht2 : ((k - 2 : ℤ) : ℝ) - (k₀ : ℝ) = s - 1 := by dsimp [s]; push_cast; ring
        rw [ht0, ht2]
        have hcomb : δ * (((M : ℝ) ^ 2 - (s + 1) ^ 2) ^ 2 / (M : ℝ) ^ 4) -
            2 * (δ * (((M : ℝ) ^ 2 - s ^ 2) ^ 2 / (M : ℝ) ^ 4)) +
            δ * (((M : ℝ) ^ 2 - (s - 1) ^ 2) ^ 2 / (M : ℝ) ^ 4) =
            δ * ((12 * s ^ 2 - 4 * (M : ℝ) ^ 2 + 2) / (M : ℝ) ^ 4) := by
          field_simp [hMpos.ne']; ring
        rw [hcomb, abs_mul, abs_of_nonneg hδ, abs_div,
          abs_of_pos (by positivity : 0 < (M : ℝ) ^ 4)]
        have hs2 : s ^ 2 ≤ ((M : ℝ) - 1) ^ 2 := by nlinarith
        have hnum : |12 * s ^ 2 - 4 * (M : ℝ) ^ 2 + 2| ≤ 8 * (M : ℝ) ^ 2 :=
          abs_le.mpr ⟨by nlinarith [sq_nonneg s], by nlinarith⟩
        calc δ * (|12 * s ^ 2 - 4 * (M : ℝ) ^ 2 + 2| / (M : ℝ) ^ 4)
            ≤ δ * (8 * (M : ℝ) ^ 2 / (M : ℝ) ^ 4) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) hδ
          _ = 8 * δ / (M : ℝ) ^ 2 := by field_simp [hMpos.ne']
  · rw [hout k hk, abs_zero]
    positivity

/-- Summed `ℓ²` first-difference and `ℓ¹` second-difference bounds for `biquadraticProfile`. -/
private theorem biquadratic_tsum_diff_bounds (k₀ : ℤ) {M : ℕ} (hM : 2 ≤ M) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (∑' k : ℤ,
        (zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) k -
          zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 1)) ^ 2 ≤
      32 * δ ^ 2 / (M : ℝ)) ∧
    (∑' k : ℤ,
        |zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) k -
          2 * zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 1) +
          zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ) (k - 2)| ≤
      24 * δ / (M : ℝ)) := by
  set g := zeroExt (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
  obtain ⟨hd1_out, hd1_le⟩ := biquadratic_first_diff_bound k₀ hM hδ
  obtain ⟨hd2_out, hd2_le⟩ := biquadratic_second_diff_bound k₀ hM hδ
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  constructor
  · set T₁ := Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ))
    rw [tsum_eq_sum (s := T₁) fun k hk => by rw [hd1_out k hk, sq, zero_mul]]
    have hcard₁ : (T₁.card : ℝ) ≤ 2 * (M : ℝ) := by
      dsimp [T₁]
      rw [Int.card_Icc]
      have htoNat : ((k₀ + (M : ℤ) + 1 - (k₀ - (M : ℤ) + 1)).toNat : ℝ) = 2 * (M : ℝ) := by
        have : (k₀ + (M : ℤ) + 1 - (k₀ - (M : ℤ) + 1)).toNat = 2 * M := by omega
        rw [this]; push_cast; ring
      linarith
    calc ∑ k ∈ T₁, (g k - g (k - 1)) ^ 2
        ≤ ∑ _k ∈ T₁, (4 * δ / (M : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [← sq_abs (g k - g (k - 1))]
          exact pow_le_pow_left₀ (abs_nonneg _) (hd1_le k) 2
      _ = (T₁.card : ℝ) * (4 * δ / (M : ℝ)) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (M : ℝ)) * (4 * δ / (M : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hcard₁ (sq_nonneg _)
      _ = 32 * δ ^ 2 / (M : ℝ) := by field_simp [hMpos.ne']; ring
  · set T₂ := Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ) + 1)
    rw [tsum_eq_sum (s := T₂) fun k hk => by rw [hd2_out k hk, abs_zero]]
    have hcard₂ : (T₂.card : ℝ) ≤ 3 * (M : ℝ) := by
      dsimp [T₂]
      rw [Int.card_Icc]
      have htoNat : ((k₀ + (M : ℤ) + 1 + 1 - (k₀ - (M : ℤ) + 1)).toNat : ℝ) =
          2 * (M : ℝ) + 1 := by
        have : (k₀ + (M : ℤ) + 1 + 1 - (k₀ - (M : ℤ) + 1)).toNat = 2 * M + 1 := by omega
        rw [this]; push_cast; ring
      linarith
    calc ∑ k ∈ T₂, |g k - 2 * g (k - 1) + g (k - 2)|
        ≤ ∑ _k ∈ T₂, (8 * δ / (M : ℝ) ^ 2) := Finset.sum_le_sum fun k _ => hd2_le k
      _ = (T₂.card : ℝ) * (8 * δ / (M : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 * (M : ℝ)) * (8 * δ / (M : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard₂ (by positivity)
      _ = 24 * δ / (M : ℝ) := by field_simp [hMpos.ne']; ring

/-- `|sinh x − sinh y| ≤ cosh B · |x − y|` for `|x|, |y| ≤ B`. -/
private theorem abs_sinh_sub_sinh_le {x y B : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |Real.sinh x - Real.sinh y| ≤ Real.cosh B * |x - y| := by
  have key : ∀ {p q : ℝ}, p < q → |p| ≤ B → |q| ≤ B →
      |Real.sinh q - Real.sinh p| ≤ Real.cosh B * (q - p) := by
    intro p q hpq hp hq
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hpq
      Real.continuous_sinh.continuousOn fun z _ => Real.hasDerivAt_sinh z
    rw [eq_div_iff (by linarith)] at hcd
    rw [← hcd, abs_mul, abs_of_pos (Real.cosh_pos c), abs_of_pos (by linarith : 0 < q - p)]
    gcongr
    have hcB : |c| ≤ B := abs_le.mpr ⟨by linarith [(abs_le.mp hp).1, hc.1],
      by linarith [(abs_le.mp hq).2, hc.2]⟩
    have hB0 : 0 ≤ B := (abs_nonneg c).trans hcB
    rw [← Real.cosh_abs c]
    exact Real.cosh_le_cosh.mpr (by rwa [abs_abs, abs_of_nonneg hB0])
  rcases lt_trichotomy x y with h | h | h
  · rw [abs_sub_comm, abs_sub_comm x y, abs_of_pos (by linarith : 0 < y - x)]
    exact key h hx hy
  · subst h; simp
  · rw [abs_of_pos (by linarith : 0 < x - y)]
    exact key h hy hx

/-- Mean-value representation `cosh(b u) − cosh(a u) = u sinh(ξ u) (b − a)` with
`min a b ≤ ξ ≤ max a b`. -/
private theorem exists_cosh_mul_sub_eq (a b u : ℝ) :
    ∃ ξ : ℝ, min a b ≤ ξ ∧ ξ ≤ max a b ∧
      Real.cosh (b * u) - Real.cosh (a * u) = u * Real.sinh (ξ * u) * (b - a) := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z => Real.cosh (z * u)) (Real.sinh (y * u) * u) y :=
    fun y => by
      have h2 : HasDerivAt (fun z : ℝ => z * u) (1 * u) y := (hasDerivAt_id y).mul_const u
      have h3 : HasDerivAt (fun z : ℝ => -(z * u)) (-(1 * u)) y := h2.neg
      have hcosh : (fun z : ℝ => Real.cosh (z * u)) =
          fun z => (Real.exp (z * u) + Real.exp (-(z * u))) / 2 :=
        funext fun z => Real.cosh_eq (z * u)
      rw [hcosh]
      exact ((h2.exp.add h3.exp).div_const 2).congr_deriv (by rw [Real.sinh_eq]; ring)
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · obtain ⟨ξ, hξ, hcd⟩ := exists_hasDerivAt_eq_slope (fun y => Real.cosh (y * u))
      (fun y => Real.sinh (y * u) * u) hlt (by fun_prop) fun y _ => hderiv y
    rw [eq_div_iff (by linarith)] at hcd
    exact ⟨ξ, (min_eq_left hlt.le).symm ▸ hξ.1.le, (max_eq_right hlt.le).symm ▸ hξ.2.le,
      by linarith⟩
  · exact ⟨a, min_le_left a a, le_max_left a a, by ring⟩
  · obtain ⟨ξ, hξ, hcd⟩ := exists_hasDerivAt_eq_slope (fun y => Real.cosh (y * u))
      (fun y => Real.sinh (y * u) * u) hgt (by fun_prop) fun y _ => hderiv y
    rw [eq_div_iff (by linarith)] at hcd
    exact ⟨ξ, (min_eq_right hgt.le).symm ▸ hξ.1.le, (max_eq_left hgt.le).symm ▸ hξ.2.le,
      by linarith⟩

/-- Second-difference `u²` bound for `y ↦ 2(cosh(y u) − 1)` on `[0, δ]`. -/
private theorem abs_secondDiff_cosh_le {u δ y₀ y₁ y₂ : ℝ} (hδ : 0 ≤ δ)
    (hy₀ : 0 ≤ y₀ ∧ y₀ ≤ δ) (hy₁ : 0 ≤ y₁ ∧ y₁ ≤ δ) (hy₂ : 0 ≤ y₂ ∧ y₂ ≤ δ) :
    |(2 * (Real.cosh (y₂ * u) - 1)) - 2 * (2 * (Real.cosh (y₁ * u) - 1)) +
        (2 * (Real.cosh (y₀ * u) - 1))| ≤
      2 * u ^ 2 * Real.cosh (δ * |u|) *
        (δ * |y₂ - 2 * y₁ + y₀| + 2 * (y₂ - y₁) ^ 2 + 2 * (y₁ - y₀) ^ 2) := by
  obtain ⟨ξ₂, hξ₂_lo, hξ₂_hi, hmv₂⟩ := exists_cosh_mul_sub_eq y₁ y₂ u
  obtain ⟨ξ₁, hξ₁_lo, hξ₁_hi, hmv₁⟩ := exists_cosh_mul_sub_eq y₀ y₁ u
  have hξ₂_in : 0 ≤ ξ₂ ∧ ξ₂ ≤ δ :=
    ⟨(le_min hy₁.1 hy₂.1).trans hξ₂_lo, hξ₂_hi.trans (max_le hy₁.2 hy₂.2)⟩
  have hξ₁_in : 0 ≤ ξ₁ ∧ ξ₁ ≤ δ :=
    ⟨(le_min hy₀.1 hy₁.1).trans hξ₁_lo, hξ₁_hi.trans (max_le hy₀.2 hy₁.2)⟩
  have hξ₂_dist : |ξ₂ - y₁| ≤ |y₂ - y₁| := by
    rw [abs_le]
    rcases le_total y₁ y₂ with h | h
    · rw [min_eq_left h] at hξ₂_lo
      rw [max_eq_right h] at hξ₂_hi
      rw [abs_of_nonneg (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · rw [min_eq_right h] at hξ₂_lo
      rw [max_eq_left h] at hξ₂_hi
      rw [abs_of_nonpos (by linarith)]
      exact ⟨by linarith, by linarith⟩
  have hξ₁_dist : |y₁ - ξ₁| ≤ |y₁ - y₀| := by
    rw [abs_le]
    rcases le_total y₀ y₁ with h | h
    · rw [min_eq_left h] at hξ₁_lo
      rw [max_eq_right h] at hξ₁_hi
      rw [abs_of_nonneg (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · rw [min_eq_right h] at hξ₁_lo
      rw [max_eq_left h] at hξ₁_hi
      rw [abs_of_nonpos (by linarith)]
      exact ⟨by linarith, by linarith⟩
  have hξ_diff : |ξ₂ - ξ₁| ≤ |y₂ - y₁| + |y₁ - y₀| :=
    (abs_sub_le ξ₂ y₁ ξ₁).trans (add_le_add hξ₂_dist hξ₁_dist)
  have hξ₂u : |ξ₂ * u| ≤ δ * |u| := by
    rw [abs_mul, abs_of_nonneg hξ₂_in.1]
    exact mul_le_mul_of_nonneg_right hξ₂_in.2 (abs_nonneg u)
  have hξ₁u : |ξ₁ * u| ≤ δ * |u| := by
    rw [abs_mul, abs_of_nonneg hξ₁_in.1]
    exact mul_le_mul_of_nonneg_right hξ₁_in.2 (abs_nonneg u)
  have h0u : |(0 : ℝ)| ≤ δ * |u| := by rw [abs_zero]; positivity
  have hsh_bound : |Real.sinh (ξ₂ * u)| ≤ Real.cosh (δ * |u|) * (δ * |u|) := by
    have h := abs_sinh_sub_sinh_le hξ₂u h0u
    rw [Real.sinh_zero, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left hξ₂u (Real.cosh_pos _).le)
  have hsh_diff : |Real.sinh (ξ₂ * u) - Real.sinh (ξ₁ * u)| ≤
      Real.cosh (δ * |u|) * (|u| * (|y₂ - y₁| + |y₁ - y₀|)) := by
    have h := abs_sinh_sub_sinh_le hξ₂u hξ₁u
    rw [← sub_mul, abs_mul, mul_comm |ξ₂ - ξ₁| |u|] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hξ_diff (abs_nonneg u)) (Real.cosh_pos _).le)
  have hident : (2 * (Real.cosh (y₂ * u) - 1)) - 2 * (2 * (Real.cosh (y₁ * u) - 1)) +
      (2 * (Real.cosh (y₀ * u) - 1)) =
      2 * u * Real.sinh (ξ₂ * u) * (y₂ - 2 * y₁ + y₀) +
        2 * u * (Real.sinh (ξ₂ * u) - Real.sinh (ξ₁ * u)) * (y₁ - y₀) := by
    linear_combination 2 * hmv₂ - 2 * hmv₁
  rw [hident]
  refine (abs_add_le _ _).trans ?_
  have ht1 : |2 * u * Real.sinh (ξ₂ * u) * (y₂ - 2 * y₁ + y₀)| ≤
      2 * u ^ 2 * Real.cosh (δ * |u|) * (δ * |y₂ - 2 * y₁ + y₀|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * |u| * |Real.sinh (ξ₂ * u)| * |y₂ - 2 * y₁ + y₀|
        ≤ 2 * |u| * (Real.cosh (δ * |u|) * (δ * |u|)) * |y₂ - 2 * y₁ + y₀| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsh_bound (by positivity)) (abs_nonneg _)
      _ = 2 * |u| ^ 2 * Real.cosh (δ * |u|) * (δ * |y₂ - 2 * y₁ + y₀|) := by ring
      _ = 2 * u ^ 2 * Real.cosh (δ * |u|) * (δ * |y₂ - 2 * y₁ + y₀|) := by rw [sq_abs]
  have ht2 : |2 * u * (Real.sinh (ξ₂ * u) - Real.sinh (ξ₁ * u)) * (y₁ - y₀)| ≤
      2 * u ^ 2 * Real.cosh (δ * |u|) * (2 * (y₂ - y₁) ^ 2 + 2 * (y₁ - y₀) ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hquad : (|y₂ - y₁| + |y₁ - y₀|) * |y₁ - y₀| ≤
        2 * (y₂ - y₁) ^ 2 + 2 * (y₁ - y₀) ^ 2 := by
      nlinarith [sq_nonneg (|y₂ - y₁| - |y₁ - y₀|), sq_abs (y₂ - y₁), sq_abs (y₁ - y₀),
        abs_nonneg (y₂ - y₁), abs_nonneg (y₁ - y₀)]
    calc 2 * |u| * |Real.sinh (ξ₂ * u) - Real.sinh (ξ₁ * u)| * |y₁ - y₀|
        ≤ 2 * |u| * (Real.cosh (δ * |u|) * (|u| * (|y₂ - y₁| + |y₁ - y₀|))) * |y₁ - y₀| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsh_diff (by positivity)) (abs_nonneg _)
      _ = 2 * |u| ^ 2 * Real.cosh (δ * |u|) * ((|y₂ - y₁| + |y₁ - y₀|) * |y₁ - y₀|) := by ring
      _ = 2 * u ^ 2 * Real.cosh (δ * |u|) * ((|y₂ - y₁| + |y₁ - y₀|) * |y₁ - y₀|) := by
          rw [sq_abs]
      _ ≤ 2 * u ^ 2 * Real.cosh (δ * |u|) * (2 * (y₂ - y₁) ^ 2 + 2 * (y₁ - y₀) ^ 2) :=
          mul_le_mul_of_nonneg_left hquad (by positivity)
  linarith

/-- **Double summation-by-parts bound for the biquadratic crystal exponential sum:** for
`0 < |u| ≤ L/2`,
`‖∑_{k ∈ taperedSupport k₀ M} 2(cosh(d_k u) − 1) e^{2πiku/L}‖ ≤ (19 L² δ² / M) cosh(δ|u|)`. -/
theorem norm_biquadraticCrystal_sum_le {L u δ : ℝ} (hL : 0 < L) (hu : u ≠ 0) (huL : |u| ≤ L / 2)
    (k₀ : ℤ) {M : ℕ} (hM : 2 ≤ M) (hδ : 0 ≤ δ) :
    ‖∑ k ∈ taperedSupport k₀ M,
        ((2 * (Real.cosh (biquadraticProfile k₀ M δ k * u) - 1) : ℝ) : ℂ) *
          cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u)‖ ≤
      19 * L ^ 2 * δ ^ 2 / (M : ℝ) * Real.cosh (δ * |u|) := by
  set S := taperedSupport k₀ M
  set d := biquadraticProfile k₀ M δ
  set g := zeroExt S d
  set z : ℂ := cexp (I * ((2 * π / L * u : ℝ) : ℂ)) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hzn : ‖z‖ = 1 := by rw [hz, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hlow := four_mul_abs_div_le_norm_cexp_sub_one hL huL
  rw [← hz, norm_sub_rev] at hlow
  have hu' : 0 < |u| := abs_pos.mpr hu
  have hlowpos : 0 < 4 * |u| / L := by positivity
  have h1z : 1 - z ≠ 0 := fun h => by
    rw [h, norm_zero] at hlow; linarith
  set c : ℤ → ℂ := fun k => ((2 * (Real.cosh (g k * u) - 1) : ℝ) : ℂ) with hc
  have hcz : ∀ k ∉ S, c k = 0 := fun k hk => by simp [hc, g, zeroExt_eq_zero hk]
  have hsum : ∑ k ∈ S, ((2 * (Real.cosh (d k * u) - 1) : ℝ) : ℂ) *
      cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u) = ∑' k : ℤ, c k * z ^ k := by
    rw [tsum_eq_sum (s := S) fun k hk => by rw [hcz k hk, zero_mul]]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc, hz, ← Complex.exp_int_mul]
    simp only [g, zeroExt, if_pos hk]
    congr 2; push_cast; ring
  rw [hsum]
  -- Apply summation by parts twice
  set T₁ : Finset ℤ := S ∪ S.map (Equiv.addRight 1).toEmbedding
  have hΔ₁z : ∀ k ∉ T₁, (c k - c (k - 1)) = 0 := fun k hk => by
    rw [Finset.mem_union, not_or] at hk
    rw [hcz k hk.1, hcz (k - 1) fun h => hk.2 (Finset.mem_map.mpr ⟨k - 1, h, by simp⟩), sub_zero]
  have habel₁ := one_sub_mul_tsum_zpow hcz hz0
  have habel₂ := one_sub_mul_tsum_zpow (c := fun k => c k - c (k - 1)) hΔ₁z hz0
  have habel_sq : (1 - z) ^ 2 * ∑' k : ℤ, c k * z ^ k =
      ∑' k : ℤ, (c k - 2 * c (k - 1) + c (k - 2)) * z ^ k := by
    calc (1 - z) ^ 2 * ∑' k : ℤ, c k * z ^ k
        = (1 - z) * ((1 - z) * ∑' k : ℤ, c k * z ^ k) := by ring
      _ = (1 - z) * ∑' k : ℤ, (c k - c (k - 1)) * z ^ k := by rw [habel₁]
      _ = ∑' k : ℤ, ((c k - c (k - 1)) - (c (k - 1) - c (k - 1 - 1))) * z ^ k := habel₂
      _ = ∑' k : ℤ, (c k - 2 * c (k - 1) + c (k - 2)) * z ^ k := by
          congr 1 with k
          rw [show k - 1 - 1 = k - 2 by omega]
          ring
  set T₂ : Finset ℤ := T₁ ∪ T₁.map (Equiv.addRight 1).toEmbedding
  have hΔ₂z : ∀ k ∉ T₂, c k - 2 * c (k - 1) + c (k - 2) = 0 := fun k hk => by
    rw [Finset.mem_union, not_or] at hk
    have h1 := hΔ₁z k hk.1
    have h2 := hΔ₁z (k - 1) fun h => hk.2 (Finset.mem_map.mpr ⟨k - 1, h, by simp⟩)
    rw [show k - 2 = k - 1 - 1 by omega]
    linear_combination h1 - h2
  have hs_norm : Summable fun k : ℤ => ‖(c k - 2 * c (k - 1) + c (k - 2)) * z ^ k‖ :=
    summable_of_ne_finset_zero (s := T₂) fun k hk => by rw [hΔ₂z k hk, zero_mul, norm_zero]
  have hg_in : ∀ k : ℤ, 0 ≤ g k ∧ g k ≤ δ := fun k => by
    by_cases hk : k ∈ S
    · simp only [g, zeroExt, if_pos hk]
      rcases hδ.eq_or_lt with rfl | hδpos
      · exact ⟨by simp [d, biquadraticProfile, biquadraticPoly], biquadraticProfile_le k₀ M le_rfl hk⟩
      · exact ⟨(biquadraticProfile_pos k₀ hδpos hk).le, biquadraticProfile_le k₀ M hδ hk⟩
    · simp [g, zeroExt, hk, hδ]
  -- Pointwise second-difference bound
  have hpt : ∀ k : ℤ, ‖(c k - 2 * c (k - 1) + c (k - 2)) * z ^ k‖ ≤
      2 * u ^ 2 * Real.cosh (δ * |u|) *
        (δ * |g k - 2 * g (k - 1) + g (k - 2)| +
          2 * (g k - g (k - 1)) ^ 2 + 2 * (g (k - 1) - g (k - 2)) ^ 2) := by
    intro k
    rw [norm_mul, norm_zpow, hzn, one_zpow, mul_one]
    have hreal : c k - 2 * c (k - 1) + c (k - 2) =
        (((2 * (Real.cosh (g k * u) - 1)) - 2 * (2 * (Real.cosh (g (k - 1) * u) - 1)) +
          (2 * (Real.cosh (g (k - 2) * u) - 1)) : ℝ) : ℂ) := by
      dsimp [c]; push_cast; ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    exact abs_secondDiff_cosh_le hδ (hg_in (k - 2)) (hg_in (k - 1)) (hg_in k)
  obtain ⟨hd1_out, _⟩ := biquadratic_first_diff_bound k₀ hM hδ
  obtain ⟨hd2_out, _⟩ := biquadratic_second_diff_bound k₀ hM hδ
  obtain ⟨hsum_d1, hsum_d2⟩ := biquadratic_tsum_diff_bounds k₀ hM hδ
  change ∑' k : ℤ, (g k - g (k - 1)) ^ 2 ≤ 32 * δ ^ 2 / (M : ℝ) at hsum_d1
  change ∑' k : ℤ, |g k - 2 * g (k - 1) + g (k - 2)| ≤ 24 * δ / (M : ℝ) at hsum_d2
  have hs_d2 : Summable fun k : ℤ => |g k - 2 * g (k - 1) + g (k - 2)| :=
    summable_of_ne_finset_zero (s := Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ) + 1))
      fun k hk => by rw [hd2_out k hk, abs_zero]
  have hs_d1 : Summable fun k : ℤ => (g k - g (k - 1)) ^ 2 :=
    summable_of_ne_finset_zero (s := Finset.Icc (k₀ - (M : ℤ) + 1) (k₀ + (M : ℤ)))
      fun k hk => by rw [hd1_out k hk, sq, zero_mul]
  have hs_d1_shift : Summable fun k : ℤ => (g (k - 1) - g (k - 2)) ^ 2 := by
    have h := hs_d1.comp_injective (Equiv.subRight (1 : ℤ)).injective
    refine h.congr fun k => ?_
    dsimp [Equiv.subRight]
    rw [show k - 1 - 1 = k - 2 by omega]
  have htsum_shift : (∑' k : ℤ, (g (k - 1) - g (k - 2)) ^ 2) = ∑' k : ℤ, (g k - g (k - 1)) ^ 2 := by
    rw [← (Equiv.subRight (1 : ℤ)).tsum_eq (fun k => (g k - g (k - 1)) ^ 2)]
    congr 1 with k
    dsimp [Equiv.subRight]
    rw [show k - 1 - 1 = k - 2 by omega]
  have hs_rhs : Summable fun k : ℤ =>
      2 * u ^ 2 * Real.cosh (δ * |u|) *
        (δ * |g k - 2 * g (k - 1) + g (k - 2)| +
          2 * (g k - g (k - 1)) ^ 2 + 2 * (g (k - 1) - g (k - 2)) ^ 2) :=
    (((hs_d2.mul_left δ).add (hs_d1.mul_left 2)).add (hs_d1_shift.mul_left 2)).mul_left _
  have hnum_le : ‖∑' k : ℤ, (c k - 2 * c (k - 1) + c (k - 2)) * z ^ k‖ ≤
      2 * u ^ 2 * Real.cosh (δ * |u|) * (152 * δ ^ 2 / (M : ℝ)) := by
    refine (norm_tsum_le_tsum_norm hs_norm).trans ?_
    refine (hs_norm.tsum_le_tsum hpt hs_rhs).trans ?_
    rw [tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Summable.tsum_add ((hs_d2.mul_left δ).add (hs_d1.mul_left 2)) (hs_d1_shift.mul_left 2),
      Summable.tsum_add (hs_d2.mul_left δ) (hs_d1.mul_left 2),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, htsum_shift]
    have h1 : δ * ∑' k : ℤ, |g k - 2 * g (k - 1) + g (k - 2)| ≤ 24 * δ ^ 2 / (M : ℝ) := by
      calc δ * ∑' k : ℤ, |g k - 2 * g (k - 1) + g (k - 2)|
          ≤ δ * (24 * δ / (M : ℝ)) := mul_le_mul_of_nonneg_left hsum_d2 hδ
        _ = 24 * δ ^ 2 / (M : ℝ) := by ring
    have hcomb : (24 * δ ^ 2 / (M : ℝ)) + 2 * (32 * δ ^ 2 / (M : ℝ)) +
        2 * (32 * δ ^ 2 / (M : ℝ)) = 152 * δ ^ 2 / (M : ℝ) := by ring
    linarith
  have h1z_sq_pos : 0 < ‖1 - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr h1z)
  have hlow_sq : 16 * u ^ 2 / L ^ 2 ≤ ‖1 - z‖ ^ 2 := by
    have := pow_le_pow_left₀ hlowpos.le hlow 2
    rwa [div_pow, mul_pow, sq_abs, show (4 : ℝ) ^ 2 = 16 by norm_num] at this
  have hnorm_div : ‖∑' k : ℤ, c k * z ^ k‖ =
      ‖∑' k : ℤ, (c k - 2 * c (k - 1) + c (k - 2)) * z ^ k‖ / ‖1 - z‖ ^ 2 := by
    rw [← habel_sq, norm_mul, norm_pow, mul_div_cancel_left₀ _ h1z_sq_pos.ne']
  rw [hnorm_div, div_le_iff₀ h1z_sq_pos]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  calc ‖∑' k : ℤ, (c k - 2 * c (k - 1) + c (k - 2)) * z ^ k‖
      ≤ 2 * u ^ 2 * Real.cosh (δ * |u|) * (152 * δ ^ 2 / (M : ℝ)) := hnum_le
    _ = 19 * L ^ 2 * δ ^ 2 / (M : ℝ) * Real.cosh (δ * |u|) * (16 * u ^ 2 / L ^ 2) := by
        field_simp [hL.ne', hMpos.ne']; ring
    _ ≤ 19 * L ^ 2 * δ ^ 2 / (M : ℝ) * Real.cosh (δ * |u|) * ‖1 - z‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hlow_sq (by positivity)

/-- **Quantitative Weil floor for the finite biquadratic crystal packet.**
For `4a ≤ L`, `2 ≤ M`, and `0 < δ ≤ ½`, every `C²` test `f` supported in `[−a, a]` satisfies
`Re W_Z(f, f) ≥ 2L (1 − 38 a L δ² cosh(2δa) / M) ∫ ‖f‖²`. -/
theorem re_W_biquadraticCrystal_ge {L δ a : ℝ} (hL : 0 < L) (k₀ : ℤ) {M : ℕ} (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (ha : 0 ≤ a) (haL : 4 * a ≤ L)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    2 * L * (1 - 38 * a * L * δ ^ 2 * Real.cosh (2 * δ * a) / (M : ℝ)) * ∫ t, ‖f t‖ ^ 2 ≤
      ((clusterConfig hL (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
        (fun _ hk => biquadraticProfile_pos k₀ hδ0 hk)
        (fun _ hk => (biquadraticProfile_le k₀ M hδ0.le hk).trans hδ1)).W f f).re := by
  have hfs' : tsupport f ⊆ Icc (-(L / 2)) (L / 2) :=
    hfs.trans (Icc_subset_Icc (by linarith) (by linarith))
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hKs : tsupport (EF.weilTest f f) ⊆ Icc (-(2 * a)) (2 * a) :=
    EF.tsupport_weilTest_subset (L := 2 * a) (by rwa [show 2 * a / 2 = a by ring])
      (by rwa [show 2 * a / 2 = a by ring])
  have hE0 : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [W_clusterConfig_eq_integral hL (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
    (fun _ hk => biquadraticProfile_pos k₀ hδ0 hk)
    (fun _ hk => (biquadraticProfile_le k₀ M hδ0.le hk).trans hδ1) hf hfs',
    integral_mul_conj_self_eq, Complex.add_re]
  set F : ℝ → ℂ := fun u => EF.weilTest f f u * ∑ k ∈ taperedSupport k₀ M,
    ((2 * (Real.cosh (biquadraticProfile k₀ M δ k * u) - 1) : ℝ) : ℂ) *
      cexp (I * (((k : ℝ) * (2 * π / L) : ℝ) : ℂ) * u)
  have hFz : ∀ u, u ∉ Icc (-(2 * a)) (2 * a) → F u = 0 := fun u hu => by
    dsimp [F]
    rw [image_eq_zero_of_notMem_tsupport (fun h => hu (hKs h)), zero_mul]
  have hFn : ∀ u ∈ Icc (-(2 * a)) (2 * a),
      ‖F u‖ ≤ (∫ t, ‖f t‖ ^ 2) * (19 * L ^ 2 * δ ^ 2 / (M : ℝ) * Real.cosh (2 * δ * a)) := by
    intro u hu
    have hu' : |u| ≤ 2 * a := abs_le.mpr ⟨hu.1, hu.2⟩
    rcases eq_or_ne u 0 with rfl | h0
    · have : F 0 = 0 := by simp [F]
      rw [this, norm_zero]; positivity
    · dsimp [F]
      rw [norm_mul]
      refine mul_le_mul (norm_weilTest_self_le hf.continuous hfc u) ?_ (norm_nonneg _) hE0
      refine (norm_biquadraticCrystal_sum_le hL h0 (by linarith) k₀ hM hδ0.le).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (show 0 ≤ δ * |u| by positivity),
        abs_of_nonneg (show 0 ≤ 2 * δ * a by positivity)]
      nlinarith
  have hbound : ‖∫ u, F u‖ ≤
      (∫ t, ‖f t‖ ^ 2) * (19 * L ^ 2 * δ ^ 2 / (M : ℝ) * Real.cosh (2 * δ * a)) * (4 * a) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hFz]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-(2 * a)) (2 * a))
      (f := F) (by simp) hFn
    rwa [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
      show 2 * a - -(2 * a) = 4 * a by ring] at this
  have hre : -‖∫ u, F u‖ ≤ (∫ u, F u).re := by
    have := Complex.abs_re_le_norm (∫ u, F u)
    linarith [neg_abs_le (∫ u, F u).re]
  rw [show ((2 : ℂ) * L * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)).re = 2 * L * ∫ t, ‖f t‖ ^ 2 by
    rw [show ((2 : ℂ) * L * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) = ((2 * L * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hsimp : (∫ t, ‖f t‖ ^ 2) * (19 * L ^ 2 * δ ^ 2 / (M : ℝ) * Real.cosh (2 * δ * a)) *
      (4 * a) = 2 * L * (38 * a * L * δ ^ 2 * Real.cosh (2 * δ * a) / (M : ℝ)) *
      ∫ t, ‖f t‖ ^ 2 := by
    field_simp [hMpos.ne']; ring
  linarith

/-- **Window positivity of the finite biquadratic crystal packet.**
Whenever `4a ≤ L`, `2 ≤ M`, `0 < δ ≤ ½`, and `38 a L δ² cosh(2δa) ≤ M`, the finite biquadratic
crystal configuration is window-positive at half-width `a` (`(a : EReal) ≤ onsetAperture`). -/
theorem windowPositiveAt_biquadraticCrystal_of_le {L δ a : ℝ} (hL : 0 < L) (k₀ : ℤ) {M : ℕ}
    (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (ha : 0 ≤ a) (haL : 4 * a ≤ L)
    (hcond : 38 * a * L * δ ^ 2 * Real.cosh (2 * δ * a) ≤ (M : ℝ)) :
    WindowPositiveAt
        (clusterConfig hL (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
          (fun _ hk => biquadraticProfile_pos k₀ hδ0 hk)
          (fun _ hk => (biquadraticProfile_le k₀ M hδ0.le hk).trans hδ1)) a ∧
      (a : EReal) ≤
        onsetAperture
          (clusterConfig hL (taperedSupport k₀ M) (biquadraticProfile k₀ M δ)
            (fun _ hk => biquadraticProfile_pos k₀ hδ0 hk)
            (fun _ hk => (biquadraticProfile_le k₀ M hδ0.le hk).trans hδ1)) := by
  have hpos : WindowPositiveAt _ a := fun f hf hfs => by
    have hge := re_W_biquadraticCrystal_ge hL k₀ hM hδ0 hδ1 ha haL hf hfs
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hdiv : 38 * a * L * δ ^ 2 * Real.cosh (2 * δ * a) / (M : ℝ) ≤ 1 :=
      (div_le_one hMpos).mpr hcond
    have hint : 0 ≤ ∫ t, ‖f t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hcoeff : 0 ≤ 2 * L * (1 - 38 * a * L * δ ^ 2 * Real.cosh (2 * δ * a) / (M : ℝ)) :=
      mul_nonneg (by positivity) (by linarith)
    exact (mul_nonneg hcoeff hint).trans hge
  exact ⟨hpos, le_onsetAperture_of_windowPositiveAt ha hpos⟩

/-- **Sharpness of the single-exponential height barrier at depth `δ = 1/a` (`Σ28` / `Σ41`).**
For every aperture `a ≥ 2`, every lattice density `L ≥ 4a` (i.e. above single-exponential height
`T = e^L ≥ e^{4a}`), and every integer ordinate index `k₀ : ℤ`, there exists a tempered
configuration `Z` (a finite biquadratic crystal packet over the `2π/L` lattice) that contains an
off-line zero `ρ₀ ∈ Z.carrier` at ordinate `2π k₀ / L` of **exact depth `ρ₀.re − ½ = 1/a`**, has
finitely many off-line zeros, and yet satisfies `WindowPositiveAt Z a` (`(a : EReal) ≤ onsetAperture Z`). -/
theorem exists_hidden_inv_aperture_zero_above_single_exp {a L : ℝ} (ha2 : 2 ≤ a) (haL : 4 * a ≤ L)
    (k₀ : ℤ) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧
      (verticalLatticePoint L (1 / a) k₀) ∈ Z.carrier ∧
      (verticalLatticePoint L (1 / a) k₀).re - 1 / 2 = 1 / a ∧
      {ρ ∈ Z.carrier | ρ.re ≠ 1 / 2}.Finite ∧
      WindowPositiveAt Z a ∧ (a : EReal) ≤ onsetAperture Z := by
  have ha0 : 0 < a := by linarith
  have hL : 0 < L := by linarith
  have hδ0 : 0 < 1 / a := one_div_pos.mpr ha0
  have hδ1 : 1 / a ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) ha2
  set M : ℕ := max 2 ⌈38 * a * L * (1 / a) ^ 2 * Real.cosh (2 * (1 / a) * a)⌉₊
  have hM2 : 2 ≤ M := le_max_left _ _
  have hcond : 38 * a * L * (1 / a) ^ 2 * Real.cosh (2 * (1 / a) * a) ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 _)
  set Z := clusterConfig hL (taperedSupport k₀ M) (biquadraticProfile k₀ M (1 / a))
    (fun _ hk => biquadraticProfile_pos k₀ hδ0 hk)
    (fun _ hk => (biquadraticProfile_le k₀ M hδ0.le hk).trans hδ1)
  have htemp : TemperedConfig Z :=
    temperedConfig_clusterConfig hL (taperedSupport k₀ M) (biquadraticProfile k₀ M (1 / a)) _ _
  have hk₀_mem : k₀ ∈ taperedSupport k₀ M := center_mem_taperedSupport k₀ (by omega)
  have hcenter : verticalLatticePoint L (1 / a) k₀ ∈ Z.carrier := by
    have hd_eq : biquadraticProfile k₀ M (1 / a) k₀ = 1 / a :=
      biquadraticProfile_center k₀ (by omega) (1 / a)
    exact Or.inl (Or.inr ⟨⟨k₀, hk₀_mem⟩, by dsimp only; rw [hd_eq]⟩)
  have hre_eq : (verticalLatticePoint L (1 / a) k₀).re - 1 / 2 = 1 / a := by
    simp [verticalLatticePoint]
  have hfin_off : {ρ ∈ Z.carrier | ρ.re ≠ 1 / 2}.Finite := by
    refine ((Set.finite_range fun k : taperedSupport k₀ M =>
        verticalLatticePoint L (biquadraticProfile k₀ M (1 / a) k) k).union
      (Set.finite_range fun k : taperedSupport k₀ M =>
        verticalLatticePoint L (-biquadraticProfile k₀ M (1 / a) k) k)).subset ?_
    rintro ρ ⟨((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩), hne⟩
    · exfalso; apply hne; simp [verticalLatticePoint]
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  obtain ⟨hpos, honset⟩ :=
    windowPositiveAt_biquadraticCrystal_of_le hL k₀ hM2 hδ0 hδ1 ha0.le haL hcond
  exact ⟨Z, htemp, hcenter, hre_eq, hfin_off, hpos, honset⟩

/-! ### 4. Doubly-exponential height non-locality (`A30`) and contact-law zero exclusion (`B18`) -/

/-- **Doubly-exponential height non-locality of window positivity (`A30`).**
For every aperture `a > 0` and off-line depth `0 < δ ≤ ½` with `log(12δa + 2) ≤ 2δa`, set
`L = (e^{2δa} − 2)/(4δ) − a` and `H = e^L = exp((e^{2δa} − 2)/(4δ) − a)`. There exist two tempered
configurations `Z_on` and `Z_off` of lattice density `L` that are **identical** (`carrier` and
`mult` agree point-for-point) on the entire strip `{z : ℂ | |z.im| < H}`, yet
`WindowPositiveAt Z_on a` holds (`onsetAperture Z_on = ⊤`) while `¬ WindowPositiveAt Z_off a`
(`onsetAperture Z_off < a`). -/
theorem doubly_exponential_height_nonlocality {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hdeep : Real.log (12 * δ * a + 2) ≤ 2 * δ * a) :
    let L := (Real.exp (2 * δ * a) - 2) / (4 * δ) - a
    let H := Real.exp L
    ∃ Z_on Z_off : ZeroConfig,
      TemperedConfig Z_on ∧ TemperedConfig Z_off ∧
      (∀ z : ℂ, |z.im| < H →
        (z ∈ Z_on.carrier ↔ z ∈ Z_off.carrier) ∧
        (z ∈ Z_on.carrier → Z_on.mult z = Z_off.mult z)) ∧
      WindowPositiveAt Z_on a ∧ onsetAperture Z_on = ⊤ ∧
      ¬ WindowPositiveAt Z_off a ∧ onsetAperture Z_off < (a : EReal) := by
  intro L H
  have hexp_ge : 12 * δ * a + 2 ≤ Real.exp (2 * δ * a) := by
    calc 12 * δ * a + 2 = Real.exp (Real.log (12 * δ * a + 2)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (2 * δ * a) := Real.exp_le_exp.mpr hdeep
  have h2a_le_L : 2 * a ≤ L := by
    dsimp [L]
    have hdiv : 3 * a ≤ (Real.exp (2 * δ * a) - 2) / (4 * δ) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hL : 0 < L := by linarith
  have haL : a ≤ L / 2 := by linarith
  set Z_on := clusterConfig hL ∅ (fun _ => 0) (by simp) (by simp)
  set Z_off := multiplicityPairConfig 1 le_rfl hL hδ hδ' H
  have htemp_on : TemperedConfig Z_on :=
    temperedConfig_clusterConfig hL ∅ (fun _ => 0) (by simp) (by simp)
  have htemp_off : TemperedConfig Z_off :=
    temperedConfig_multiplicityPairConfig 1 le_rfl hL hδ hδ' H
  have hon_line : ∀ ρ ∈ Z_on.carrier, ρ.re = 1 / 2 := by
    rintro _ ((⟨k, rfl⟩ | ⟨k, _⟩) | ⟨k, _⟩)
    · simp [verticalLatticePoint]
    · exact False.elim (Finset.notMem_empty k.1 k.2)
    · exact False.elim (Finset.notMem_empty k.1 k.2)
  have hon_top : onsetAperture Z_on = ⊤ :=
    (onsetAperture_eq_top_iff_onLine htemp_on).mpr hon_line
  have hon_pos : WindowPositiveAt Z_on a :=
    (windowPositiveAt_iff_le_onsetAperture htemp_on ha.le).mpr (hon_top ▸ le_top)
  have hlog_eq : Real.log (4 * δ * (L / (1 : ℕ) + a) + 2) ≤ 2 * δ * a := by
    have harg : 4 * δ * (L / (1 : ℕ) + a) + 2 = Real.exp (2 * δ * a) := by
      dsimp [L]
      simp only [Nat.cast_one, div_one]
      field_simp [hδ.ne']
      ring
    rw [harg, Real.log_exp]
  have hoff_lt : onsetAperture Z_off < (a : EReal) :=
    onsetAperture_multiplicityPairConfig_lt_of_log_le 1 le_rfl hL hδ hδ' H ha haL hlog_eq
  have hoff_neg : ¬ WindowPositiveAt Z_off a := by
    rw [windowPositiveAt_iff_le_onsetAperture htemp_off ha.le]
    exact not_le.mpr hoff_lt
  refine ⟨Z_on, Z_off, htemp_on, htemp_off, ?_, hon_pos, hon_top, hoff_neg, hoff_lt⟩
  intro z hz
  have hnot_pos : z ≠ offLinePoint δ H := fun heq => by
    have him : (offLinePoint δ H).im = H := by simp [offLinePoint]
    rw [heq, him] at hz
    linarith [le_abs_self H]
  have hnot_neg : z ≠ offLinePoint (-δ) H := fun heq => by
    have him : (offLinePoint (-δ) H).im = H := by simp [offLinePoint]
    rw [heq, him] at hz
    linarith [le_abs_self H]
  have hmem_on : z ∈ Z_on.carrier ↔ z ∈ Set.range (verticalLatticePoint L 0) := by
    constructor
    · rintro ((⟨k, rfl⟩ | ⟨k, _⟩) | ⟨k, _⟩)
      · exact ⟨k.1, rfl⟩
      · exact False.elim (Finset.notMem_empty k.1 k.2)
      · exact False.elim (Finset.notMem_empty k.1 k.2)
    · rintro ⟨k, rfl⟩
      exact Or.inl (Or.inl ⟨⟨k, by simp⟩, rfl⟩)
  have hmem_off : z ∈ Z_off.carrier ↔ z ∈ Set.range (verticalLatticePoint L 0) := by
    constructor
    · rintro ((h | h) | h)
      · exact h
      · exact absurd (Set.mem_singleton_iff.mp h) hnot_pos
      · exact absurd (Set.mem_singleton_iff.mp h) hnot_neg
    · exact fun h => Or.inl (Or.inl h)
  refine ⟨hmem_on.trans hmem_off.symm, fun hz_on => ?_⟩
  have hre : z.re = 1 / 2 := hon_line z hz_on
  change (if z.re = 1 / 2 then 2 else 1) = (if z.re = 1 / 2 then 2 else 1)
  rfl

/-- **Closed-endpoint excluded-depth law for `ζ` (`B18` / `Σ28` at `onsetAperture`).**
Strengthens `zeta_abs_re_sub_half_lt_of_lt_contact` from `< zetaContactAperture` to
`((R : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig` (including `R = zetaContactAperture` off RH). -/
theorem zeta_abs_re_sub_half_lt_of_le_onsetAperture :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ R : ℝ, Real.exp 6 ≤ R →
      ((R : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig →
      ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₀ R →
        |ρ.re - 1 / 2| < 1 / R := by
  obtain ⟨A₀, hA₀, h⟩ := zeta_abs_re_sub_half_lt_of_zetaWindowPositive
  refine ⟨A₀, hA₀, fun R hR6 hle ρ hρ h2 hT => ?_⟩
  have hR0 : 0 ≤ R := (Real.exp_pos 6).le.trans hR6
  have hpos : ZetaWindowPositive R :=
    (windowPositiveAt_zeta_iff R).mp
      ((windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig hR0).mpr hle)
  exact h R hR6 hpos ρ hρ h2 hT

/-- **Contact law at logarithmic scale `c log T` is a power-saving zero-location bound (`B18`).**
If `((c * Real.log T : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig` (`c > 0`, `T ≥ 3`), then every
nonempty coherent off-line cluster `S` of `ζ` at height `|γ₀| ≤ T` with `ρ.re ≥ ½ + δ`
(`2 ≤ δ c log T`, `δ ≤ ½`) over global background depth `σ` satisfies the power-saving bound
`(1 / 2) * (∑_{ρ ∈ S} m_ρ) * T ^ (2 * c * (δ − σ)) ≤ …`. -/
theorem contact_law_log_scale_cluster_bound :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      ∀ {c T γ₀ δ σ : ℝ}, 0 < c → 3 ≤ T → |γ₀| ≤ T →
        0 < δ → δ ≤ 1 / 2 → 2 ≤ δ * (c * Real.log T) → 0 ≤ σ →
        ((c * Real.log T : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig →
        ∀ S : Finset ℂ, S.Nonempty → (∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) →
          (∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) →
          (∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * (c * Real.log T))) →
          (∀ ρ ∈ zetaZeroConfig.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) →
          (1 / 2) * (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ)) *
              T ^ (2 * c * (δ - σ)) ≤
            120 * 2 ^ 26 * A₀ * δ * (2 * (c * Real.log T) + 2 * π) * Real.exp (2 * π) *
              Real.log (T + 1 / (4 * (c * Real.log T)) +
                3072 * 2 ^ 26 * A₀ * Real.log (T + 3) *
                  (50 * (c * Real.log T)) ^ 7 * T ^ c + 6) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  refine ⟨A₀, hA₀, fun {c T γ₀ δ σ} hc hT hγT hδ hδ' hδa hσ honset S hSne hSc hSδ hSγ hsea => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  set a := c * Real.log T
  have ha0 : 0 < a := mul_pos hc hlogT
  have hpos : WindowPositiveAt zetaZeroConfig a :=
    (windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig ha0.le).mpr honset
  have hsea_bound := windowPositiveAt_global_sea_cluster_bound zetaZeroConfig hA₀ hloc hδ hδ' hδa
    hσ hpos S hSne hSc hSδ hSγ hsea
  have hpow_lhs : T ^ (2 * c * (δ - σ)) = Real.exp (2 * (δ - σ) * a) := by
    rw [Real.rpow_def_of_pos hT0]
    congr 1; dsimp [a]; ring
  have hpow_ea : Real.exp a = T ^ c := by
    rw [Real.rpow_def_of_pos hT0]
    congr 1; dsimp [a]; ring
  rw [hpow_lhs]
  refine hsea_bound.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hlog3 : Real.log (|γ₀| + 3) ≤ Real.log (T + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [hpow_ea]
  apply Real.log_le_log
  · have := one_le_log_abs_add_three γ₀; positivity
  · have : 3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * T ^ c ≤
        3072 * 2 ^ 26 * A₀ * Real.log (T + 3) * (50 * a) ^ 7 * T ^ c :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog3 (by positivity)) (by positivity))
        (Real.rpow_nonneg hT0.le c)
    linarith

end GaloisForLFunctions.WindowVisibilityLaw
