import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.MomentReadout
import GaloisForLFunctions.ZeroConfigurationGeometry.TheImageHankelReadsTheSquaredGap
import GaloisForLFunctions.ZeroConfigurationGeometry.TheImageReadsTheDiscriminantOfACluster
import GaloisForLFunctions.ZeroConfigurationGeometry.TheImageLocatesTheClusterPoints

/-!
# Explicit heights for the Hankel camera

The squared gap uses order two, the discriminant order `2k−2`, and the
bordered polynomial locating a cluster order `2k−1`. Each readout holds at
its corresponding finite moment height with the original error formula.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- The squared-gap Hankel readout holds above the explicit order-two moment height. -/
theorem pair_hankel_rvm_explicit {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam) (hA : 0 ≤ A)
    (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 1 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight 2 θ lam A S M' K' ≤ T →
      ∀ Z : ZeroConfig, TemperedConfig Z →
        ∑' z, ‖multDiff Z emptyZeroConfig z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z emptyZeroConfig z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z emptyZeroConfig z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ p₁ p₂ : ℂ, ‖p₁ - z₀‖ ≤ r → ‖p₂ - z₀‖ ≤ r →
        (∀ z, ‖z - z₀‖ ≤ r → multDiff Z emptyZeroConfig z =
          (if z = p₁ then 1 else 0) + (if z = p₂ then 1 else 0)) →
        ∃ F₀ F₁ F₂ G : ℝ → ℂ, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₀ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₁ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₂ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧ Z.W F₀ G ≠ 0 ∧
          ‖4 * (Z.W F₁ G ^ 2 - Z.W F₀ G * Z.W F₂ G) / Z.W F₀ G ^ 2 -
              (gammaOf p₁ - gammaOf p₂) ^ 2‖ ≤
            pairReadError r
              (2 * r * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)))
              (2 * r ^ 2 * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)))
              (2 * r ^ 3 * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3))) := by
  classical
  have hread := discMoment_readout_rvm_explicit 2 hθ hlam hA hS hM' (by linarith only [hK'] : 0 ≤ K')
  have hT₀ := cameraMomentHeight_ge 2 θ lam A S M' K'
  intro T hT Z hZ hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso p₁ p₂ hp₁ hp₂ hc
  set s : Finset ℂ := {p₁, p₂} with hs
  have hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r := by
    intro z hz
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hds : ∀ z, multDiff Z emptyZeroConfig z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hzs
    apply hcz
    rw [hc z hzr, if_neg hzs.1, if_neg hzs.2, add_zero]
  obtain ⟨F₁, G₁, -, hG₁, hΦ, hj⟩ := hread T hT Z emptyZeroConfig hZ temperedConfig_emptyZeroConfig
    hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE, ← hP] at hj ⊢
  -- the moments of the pair
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z emptyZeroConfig z * f z = f p₁ + f p₂ := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_pair_points]
  have hN : ∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖ ≤ 2 := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_pair_points_le
  -- the scales
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hprod := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith only [hprod, Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith only [hT4]
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  have hrP : r * P ≤ 1 / 4 := by
    have hprod : T ^ (-(M' + slowExponent lam + 1)) * P = T⁻¹ := by
      rw [hP, ← Real.rpow_add hT0, show -(M' + slowExponent lam + 1) + (M' + slowExponent lam) =
        -1 by ring, Real.rpow_neg_one]
    have h1 : r * P ≤ T⁻¹ := hprod ▸ mul_le_mul_of_nonneg_right hr hP0
    have h2 : T⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hT0 (by norm_num), one_div, inv_inv]; exact hT4
    exact h1.trans h2
  have hu1 : 1 ≤ Real.log (T / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith only [hT₀, hT]
  have hE2 : E ≤ 1 / 2 := by
    rw [hE]
    refine exp_neg_le_half ?_
    have : 1 ≤ Real.log (T / (2 * π)) ^ 3 := one_le_pow₀ hu1
    nlinarith only [this, hK']
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  -- the readout at orders `0, 1, 2`
  set ω := gammaOf z₀
  have ha : ∀ p, ‖p - z₀‖ ≤ r → ‖gammaOf p - ω‖ ≤ r := fun p hp => by
    rw [norm_gammaOf_sub]; exact hp
  have hδ : ∀ j : ℕ, (∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖) * r ^ (j + 1) * P + E ≤
      2 * r ^ (j + 1) * P + E := fun j => by
    have := mul_le_mul_of_nonneg_right hN (mul_nonneg (pow_nonneg hr0 (j + 1)) hP0)
    linarith only [this]
  obtain ⟨hF0, h0⟩ := hj 0 (by norm_num)
  obtain ⟨hF1, h1⟩ := hj 1 (by norm_num)
  obtain ⟨hF2, h2⟩ := hj 2 (by norm_num)
  rw [W_emptyZeroConfig, sub_zero, hsum] at h0 h1 h2
  have e0 : (gammaOf p₁ - ω) ^ 0 + (gammaOf p₂ - ω) ^ 0 = 2 := by norm_num
  have e1 : (gammaOf p₁ - ω) ^ 1 + (gammaOf p₂ - ω) ^ 1 = (gammaOf p₁ - ω) + (gammaOf p₂ - ω) := by
    ring
  rw [e0] at h0
  rw [e1] at h1
  have h0' := h0.trans (hδ 0)
  have h1' := h1.trans (hδ 1)
  have h2' := h2.trans (hδ 2)
  rw [zero_add] at h0'
  rw [show (1 + 1 : ℕ) = 2 by rfl] at h1'
  rw [show (2 + 1 : ℕ) = 3 by rfl] at h2'
  have hδ₀1 : 2 * r ^ 1 * P + E ≤ 1 := by rw [pow_one]; linarith only [hrP, hE2]
  have hH := norm_hankel_sub_le (a₁ := gammaOf p₁ - ω) (a₂ := gammaOf p₂ - ω)
    (ha p₁ hp₁) (ha p₂ hp₂) hδ₀1 h0' h1' h2'
  -- the normalization cancels
  have hm0 : ∀ x : ℂ, ‖x - 2‖ ≤ 1 → x ≠ 0 := fun x hx h => by
    rw [h, zero_sub, norm_neg, Complex.norm_two] at hx; linarith only [hx]
  have hW0 : Z.W (localWindow z₀.im (annihilatePow (ω - z₀.im) 0 F₁))
      (localWindow z₀.im G₁) ≠ 0 := by
    intro h
    apply hm0 _ (h0'.trans hδ₀1)
    rw [h, zero_div]
  rw [hankel_ratio_eq hΦ hW0, show (gammaOf p₁ - ω) - (gammaOf p₂ - ω) = gammaOf p₁ - gammaOf p₂
    by ring] at hH
  refine ⟨_, _, _, _, hF0, hF1, hF2, apertureWindow_localWindow hG₁ _, hW0, ?_⟩
  simpa only [pow_one] using hH


/-- The cluster discriminant is read above the explicit moment height of order two k minus two. -/
theorem cluster_discriminant_rvm_explicit (k : ℕ) (hk : 1 ≤ k) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 3 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight (2 * k - 2) θ lam A S M' K' ≤ T →
      ∀ Z : ZeroConfig, TemperedConfig Z →
        ∑' z, ‖multDiff Z emptyZeroConfig z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z emptyZeroConfig z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 < r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z emptyZeroConfig z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ p : Fin k → ℂ, (∀ i, ‖p i - z₀‖ ≤ r) →
        (∀ z, ‖z - z₀‖ ≤ r → multDiff Z emptyZeroConfig z = ∑ i, (if z = p i then 1 else 0)) →
        ∃ (F : ℕ → ℝ → ℂ) (G : ℝ → ℂ),
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
          (∀ j, j ≤ 2 * k - 2 → ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) (F j)) ∧
          ‖imageDiscriminant k (fun j => Z.W (F j) G) -
              (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i))) ^ 2‖ ≤
            clusterReadError k r (T ^ (M' + slowExponent lam))
              (Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3))) := by
  classical
  have hread := discMoment_readout_rvm_explicit (2 * k - 2) hθ hlam hA hS hM'
    (by linarith only [hK'] : 0 ≤ K')
  have hT₀ := cameraMomentHeight_ge (2 * k - 2) θ lam A S M' K'
  intro T hT Z hZ hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso p hp hc
  set s : Finset ℂ := Finset.univ.image p with hs
  have hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact hp i
  have hds : ∀ z, multDiff Z emptyZeroConfig z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    apply hcz
    rw [hc z hzr]
    refine Finset.sum_eq_zero fun i _ => if_neg fun h => hzs ?_
    rw [h]; exact Finset.mem_image_of_mem p (Finset.mem_univ i)
  obtain ⟨F₁, G₁, -, hG₁, hΦ, hj⟩ := hread T hT Z emptyZeroConfig hZ temperedConfig_emptyZeroConfig
    hStail hcount z₀ hz₀ hz₀re r hr0.le hr hiso s hsd hds
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE, ← hP] at hj ⊢
  set ω := gammaOf z₀
  set Φ := pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ with hΦdef
  set W : ℕ → ℂ := fun j => Z.W (localWindow z₀.im (annihilatePow (ω - z₀.im) j F₁))
    (localWindow z₀.im G₁) with hW
  set m : ℕ → ℂ := fun j => W j / ((-I) ^ j * Φ) with hm
  set a : Fin k → ℂ := fun i => gammaOf (p i) - ω with ha
  -- the scales
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hprod := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith only [hprod, Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith only [hT4]
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  have hrP : r * P ≤ 1 / 4 := by
    have hprod : T ^ (-(M' + slowExponent lam + 1)) * P = T⁻¹ := by
      rw [hP, ← Real.rpow_add hT0, show -(M' + slowExponent lam + 1) + (M' + slowExponent lam) =
        -1 by ring, Real.rpow_neg_one]
    have h1 : r * P ≤ T⁻¹ := hprod ▸ mul_le_mul_of_nonneg_right hr hP0
    have h2 : T⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hT0 (by norm_num), one_div, inv_inv]; exact hT4
    exact h1.trans h2
  have hr1 : r ≤ 1 := by
    have hT1 : 1 ≤ T := by linarith only [hT4]
    have hx : 1 ≤ M' + slowExponent lam := by
      unfold slowExponent; have := mul_pos Real.pi_pos (show 0 < lam by linarith only [hθ, hlam]); linarith only [this, hM', hθ, hlam]
    have h := hr.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hx] : -(M' + slowExponent lam
      + 1) ≤ (-1 : ℝ)))
    rw [Real.rpow_neg_one] at h
    exact h.trans (inv_le_one_of_one_le₀ hT1)
  have hu1 : 1 ≤ Real.log (T / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith only [hT₀, hT]
  have hE4 : E ≤ 1 / 4 := by
    rw [hE, Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    have h3 : 3 ≤ K' * Real.log (T / (2 * π)) ^ 3 := by
      have : 1 ≤ Real.log (T / (2 * π)) ^ 3 := one_le_pow₀ hu1
      nlinarith only [this, hK']
    linarith only [h3, Real.add_one_le_exp (K' * Real.log (T / (2 * π)) ^ 3)]
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  -- the moments of the cluster
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z emptyZeroConfig z * f z = ∑ i, f (p i) := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_cluster_points]
  have hN : ∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖ ≤ k := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_cluster_points_le p
  have hread' : ∀ l, l ≤ 2 * k - 2 → ‖m l - ∑ i, a i ^ l‖ ≤ k * r ^ (l + 1) * P + E := by
    intro l hl
    obtain ⟨-, hb⟩ := hj l hl
    rw [W_emptyZeroConfig, sub_zero, hsum] at hb
    refine hb.trans ?_
    have := mul_le_mul_of_nonneg_right hN (mul_nonneg (pow_nonneg hr0.le (l + 1)) hP0)
    linarith only [this]
  -- assembling
  have hδ₀k : k * r * P + E ≤ k / 2 := by
    have := mul_le_mul_of_nonneg_left hrP (by linarith only [hk0] : (0 : ℝ) ≤ k)
    have e : (k : ℝ) * r * P = k * (r * P) := by ring
    linarith only [this, e, hE4, hk0]
  have hal : ∀ i, ‖a i‖ ≤ r := fun i => by
    rw [ha]; simp only; rw [norm_gammaOf_sub]; exact hp i
  have hmain := cluster_disc_of_moments hk hr0 hr1 hP0 hE0 hδ₀k hal hread'
  have hdisc : (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) =
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i)) :=
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by simp only [ha]; ring
  rw [hdisc] at hmain
  have hD := imageDiscriminant_eq (k := k) (W := W) hΦ
  refine ⟨fun j => localWindow z₀.im (annihilatePow (ω - z₀.im) j F₁), localWindow z₀.im G₁,
    apertureWindow_localWindow hG₁ _, fun j hjk => (hj j hjk).1, ?_⟩
  change ‖imageDiscriminant k W - _‖ ≤ _
  rw [hD]
  exact hmain


/-- The bordered Hankel polynomial locates the cluster above the explicit height of order two k minus one. -/
theorem cluster_location_rvm_explicit (k : ℕ) (hk : 1 ≤ k) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ)
    (hlam : θ / 2 < lam) (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight (2 * k - 1) θ lam A S M' K' ≤ T →
      ∀ Z : ZeroConfig, TemperedConfig Z →
        ∑' z, ‖multDiff Z emptyZeroConfig z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z emptyZeroConfig z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 < r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z emptyZeroConfig z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ p : Fin k → ℂ, (∀ i, ‖p i - z₀‖ ≤ r) →
        (∀ z, ‖z - z₀‖ ≤ r → multDiff Z emptyZeroConfig z = ∑ i, (if z = p i then 1 else 0)) →
        ∃ (F : ℕ → ℝ → ℂ) (G : ℝ → ℂ) (Φ : ℂ), Φ ≠ 0 ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧
          (∀ l, l ≤ 2 * k - 1 → ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) (F l)) ∧
          ∀ x : ℂ, ‖x‖ ≤ r →
            ‖(borderedHankel k (fun l => Z.W (F l) G / ((-I) ^ l * Φ)) x).det -
                (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i))) ^ 2 *
                  ∏ l, (gammaOf (p l) - gammaOf z₀ - x)‖ ≤
              borderError k r (T ^ (M' + slowExponent lam))
                (Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3))) := by
  classical
  have hread := discMoment_readout_rvm_explicit (2 * k - 1) hθ hlam hA hS hM' hK'
  have hT₀ := cameraMomentHeight_ge (2 * k - 1) θ lam A S M' K'
  intro T hT Z hZ hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso p hp hc
  set s : Finset ℂ := Finset.univ.image p with hs
  have hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact hp i
  have hds : ∀ z, multDiff Z emptyZeroConfig z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    apply hcz
    rw [hc z hzr]
    refine Finset.sum_eq_zero fun i _ => if_neg fun h => hzs ?_
    rw [h]; exact Finset.mem_image_of_mem p (Finset.mem_univ i)
  obtain ⟨F₁, G₁, -, hG₁, hΦ, hj⟩ := hread T hT Z emptyZeroConfig hZ temperedConfig_emptyZeroConfig
    hStail hcount z₀ hz₀ hz₀re r hr0.le hr hiso s hsd hds
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE, ← hP] at hj ⊢
  set ω := gammaOf z₀
  set Φ := pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ with hΦdef
  set a : Fin k → ℂ := fun i => gammaOf (p i) - ω with ha
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hprod := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith only [hprod, Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith only [hT4]
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    have hT1 : 1 ≤ T := by linarith only [hT4]
    have h := hr.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by
      unfold slowExponent; have := mul_pos Real.pi_pos (show 0 < lam by linarith only [hθ, hlam]); linarith only [this, hM', hθ, hlam] :
        -(M' + slowExponent lam + 1) ≤ (-1 : ℝ)))
    rw [Real.rpow_neg_one] at h
    exact h.trans (inv_le_one_of_one_le₀ hT1)
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z emptyZeroConfig z * f z = ∑ i, f (p i) := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_cluster_points]
  have hN : ∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖ ≤ k := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_cluster_points_le p
  have hread' : ∀ l, l ≤ 2 * k - 1 →
      ‖Z.W (localWindow z₀.im (annihilatePow (ω - z₀.im) l F₁)) (localWindow z₀.im G₁) /
          ((-I) ^ l * Φ) - ∑ i, a i ^ l‖ ≤ k * r ^ (l + 1) * P + E := by
    intro l hl
    obtain ⟨-, hb⟩ := hj l hl
    rw [W_emptyZeroConfig, sub_zero, hsum] at hb
    refine hb.trans ?_
    have := mul_le_mul_of_nonneg_right hN (mul_nonneg (pow_nonneg hr0.le (l + 1)) hP0)
    linarith only [this]
  have hal : ∀ i, ‖a i‖ ≤ r := fun i => by
    rw [ha]; simp only; rw [norm_gammaOf_sub]; exact hp i
  have hdisc : (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (a j - a i)) =
      ∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (gammaOf (p j) - gammaOf (p i)) :=
    Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by simp only [ha]; ring
  refine ⟨fun l => localWindow z₀.im (annihilatePow (ω - z₀.im) l F₁), localWindow z₀.im G₁, Φ,
    hΦ, apertureWindow_localWindow hG₁ _, fun l hl => (hj l hl).1, fun x hx => ?_⟩
  have h := bordered_of_moments hk hr0 hr1 hP0 hE0 hal hread' hx
  rw [hdisc] at h
  exact h


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.pair_hankel_rvm_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.cluster_discriminant_rvm_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.cluster_location_rvm_explicit
