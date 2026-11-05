import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.MomentReadout

/-!
# Cluster rigidity at explicit camera heights

The same moment threshold gives quantitative centre and squared-gap
comparison, and collapse of isolated dipoles to the tail scale.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- For mimics, every disc moment has the explicit polynomial error and cubic-logarithmic tail. -/
theorem norm_discMoment_rvm_le_explicit (J : ℕ) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight J θ lam A S M' K' ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ s : Finset ℂ, (∀ z ∈ s, ‖z - z₀‖ ≤ r) →
        (∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) →
        ∀ j : ℕ, j ≤ J →
          ‖∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
            (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) * T ^ (M' + slowExponent lam) +
              Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  have hread := discMoment_readout_rvm_explicit J hθ hlam hA hS hM' hK'
  intro T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds j hj
  obtain ⟨F₁, G₁, -, hG₁, -, hj'⟩ :=
    hread T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds
  obtain ⟨hFj, hbd⟩ := hj' j hj
  rw [W_eq_of_mimic hZ hZ' hW hFj (apertureWindow_localWindow hG₁ _), sub_self, zero_div, zero_sub,
    norm_neg] at hbd
  exact hbd


/-- Near pairs have matching centres and squared gaps at the same explicit moment height. -/
theorem pair_centre_and_gap_rvm_explicit {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight 2 θ lam A S M' K' ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ p₁ p₂ q₁ q₂ : ℂ, ‖p₁ - z₀‖ ≤ r → ‖p₂ - z₀‖ ≤ r → ‖q₁ - z₀‖ ≤ r → ‖q₂ - z₀‖ ≤ r →
        (∀ z, ‖z - z₀‖ ≤ r → multDiff Z Z' z = (if z = p₁ then 1 else 0) +
          (if z = p₂ then 1 else 0) - (if z = q₁ then 1 else 0) - (if z = q₂ then 1 else 0)) →
          ‖(gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂)‖ ≤
              4 * r ^ 2 * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) ∧
            ‖(gammaOf p₁ - gammaOf p₂) ^ 2 - (gammaOf q₁ - gammaOf q₂) ^ 2‖ ≤
              24 * r ^ 3 * T ^ (M' + slowExponent lam) +
                4 * Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  classical
  have hmain := norm_discMoment_rvm_le_explicit 2 hθ hlam hA hS hM' hK'
  have hT₀ := cameraMomentHeight_ge 2 θ lam A S M' K'
  intro T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso p₁ p₂ q₁ q₂
    hp₁ hp₂ hq₁ hq₂ hc
  set s : Finset ℂ := {p₁, p₂, q₁, q₂} with hs
  have hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r := by
    intro z hz
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hzs
    apply hcz
    rw [hc z hzr, if_neg hzs.1, if_neg hzs.2.1, if_neg hzs.2.2.1, if_neg hzs.2.2.2]
    ring
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE, ← hP]
  have hm := fun j hj => hmain T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s
    hsd hds j hj
  rw [← hE, ← hP] at hm
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z Z' z * f z = f p₁ + f p₂ - f q₁ - f q₂ := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_pair_cluster]
  have hN : ∑ z ∈ s, ‖multDiff Z Z' z‖ ≤ 4 := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_pair_cluster_le
  have h2πe : 2 ≤ 2 * π * Real.exp 1 := by
    have h1 := Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)
    nlinarith [Real.pi_gt_three]
  have hT2 : 2 ≤ T := h2πe.trans (hT₀.trans hT)
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg (by linarith) _
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  set ω := gammaOf z₀
  have hd : ∀ z, ‖z - z₀‖ ≤ r → ‖gammaOf z - ω‖ ≤ r := fun z hz => by
    rw [norm_gammaOf_sub]; exact hz
  -- first and second moments
  have h1 := hm 1 (by norm_num)
  have h2 := hm 2 (by norm_num)
  rw [hsum] at h1 h2
  have e1 : (gammaOf p₁ - ω) ^ 1 + (gammaOf p₂ - ω) ^ 1 - (gammaOf q₁ - ω) ^ 1 -
      (gammaOf q₂ - ω) ^ 1 = (gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂) := by ring
  rw [e1] at h1
  have hr2 : (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (1 + 1) * P ≤ 4 * r ^ 2 * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN (by positivity)) hP0
  have hcentre : ‖(gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂)‖ ≤ 4 * r ^ 2 * P + E := by
    linarith
  refine ⟨hcentre, ?_⟩
  have hr3 : (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (2 + 1) * P ≤ 4 * r ^ 3 * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN (by positivity)) hP0
  have hμ₂ : ‖(gammaOf p₁ - ω) ^ 2 + (gammaOf p₂ - ω) ^ 2 - (gammaOf q₁ - ω) ^ 2 -
      (gammaOf q₂ - ω) ^ 2‖ ≤ 4 * r ^ 3 * P + E := by linarith
  have hid : (gammaOf p₁ - gammaOf p₂) ^ 2 - (gammaOf q₁ - gammaOf q₂) ^ 2 =
      2 * ((gammaOf p₁ - ω) ^ 2 + (gammaOf p₂ - ω) ^ 2 - (gammaOf q₁ - ω) ^ 2 -
        (gammaOf q₂ - ω) ^ 2) - ((gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂)) *
          ((gammaOf p₁ - ω) + (gammaOf p₂ - ω) + (gammaOf q₁ - ω) + (gammaOf q₂ - ω)) := by
    ring
  have h4r : ‖(gammaOf p₁ - ω) + (gammaOf p₂ - ω) + (gammaOf q₁ - ω) + (gammaOf q₂ - ω)‖ ≤
      4 * r := by
    have e1 := norm_add_le ((gammaOf p₁ - ω) + (gammaOf p₂ - ω) + (gammaOf q₁ - ω))
      (gammaOf q₂ - ω)
    have e2 := norm_add_le ((gammaOf p₁ - ω) + (gammaOf p₂ - ω)) (gammaOf q₁ - ω)
    have e3 := norm_add_le (gammaOf p₁ - ω) (gammaOf p₂ - ω)
    linarith [hd p₁ hp₁, hd p₂ hp₂, hd q₁ hq₁, hd q₂ hq₂]
  have hr1 : r ≤ 1 / 2 := by
    have hT1 : 1 ≤ T := by linarith
    have hexp : -(M' + slowExponent lam + 1) ≤ (-1 : ℝ) := by
      have := mul_pos Real.pi_pos (show 0 < lam by linarith)
      unfold slowExponent
      linarith
    have h := hr.trans (Real.rpow_le_rpow_of_exponent_le hT1 hexp)
    rw [Real.rpow_neg_one] at h
    have h2 : T⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num), one_div, inv_inv]
      exact hT2
    linarith
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_two]
  have hprod := mul_le_mul hcentre h4r (norm_nonneg _) (by positivity)
  have hrE : r * E ≤ 1 / 2 * E := mul_le_mul_of_nonneg_right hr1 hE0
  linarith [hprod, hμ₂, hrE]


/-- An isolated dipole collapses to twice the cubic-logarithmic tail at the explicit height. -/
theorem dipole_collapse_rvm_explicit {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∀ T : ℝ, cameraMomentHeight 2 θ lam A S M' K' ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ p q : ℂ, |p.im - T| ≤ T / 4 → |p.re - 1 / 2| ≤ 1 / 2 →
        ‖q - p‖ ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, ‖z - p‖ ≤ ‖q - p‖ →
          multDiff Z Z' z = (if z = p then 1 else 0) - (if z = q then 1 else 0)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - p‖ ≤ ‖q - p‖ ∨ T ^ (-M') ≤ ‖z - p‖) →
          ‖gammaOf p - gammaOf q‖ ≤ 2 * Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  classical
  have hmain := norm_discMoment_rvm_le_explicit 2 hθ hlam hA hS hM' hK'
  have hT₀ := cameraMomentHeight_ge 2 θ lam A S M' K'
  intro T hT Z Z' hZ hZ' hW hStail hcount p q hp hpre hr hc hiso
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith
  set r := ‖q - p‖ with hrdef
  set s : Finset ℂ := {p, q} with hs
  have hsd : ∀ z ∈ s, ‖z - p‖ ≤ r := by
    intro z hz
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [sub_self, norm_zero]; exact norm_nonneg _
    · exact le_rfl
  have hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - p‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hzs
    apply hcz
    rw [hc z hzr, if_neg hzs.1, if_neg hzs.2, sub_zero]
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE]
  have hm := hmain T hT Z Z' hZ hZ' hW hStail hcount p hp hpre r (norm_nonneg _) hr hiso s hsd
    hds 1 (by norm_num)
  rw [← hE, ← hP] at hm
  have hsum : ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf p) ^ 1 = gammaOf p - gammaOf q := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_dipole]
    ring
  have hN : ∑ z ∈ s, ‖multDiff Z Z' z‖ ≤ 2 := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_dipole_le
  rw [hsum] at hm
  have hrγ : ‖gammaOf p - gammaOf q‖ = r := by rw [norm_gammaOf_sub, norm_sub_rev]
  rw [hrγ] at hm ⊢
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  -- `r P ≤ T⁻¹ ≤ 1/4`
  have hrP : r * P ≤ 1 / 4 := by
    have hprod : T ^ (-(M' + slowExponent lam + 1)) * P = T⁻¹ := by
      rw [hP, ← Real.rpow_add hT0, show -(M' + slowExponent lam + 1) + (M' + slowExponent lam) =
        -1 by ring, Real.rpow_neg_one]
    have h1 : r * P ≤ T⁻¹ := hprod ▸ mul_le_mul_of_nonneg_right hr hP0
    have h2 : T⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hT0 (by norm_num), one_div, inv_inv]; exact hT4
    linarith
  have hr0 : 0 ≤ r := norm_nonneg _
  have hNr : (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (1 + 1) * P ≤ 2 * r * (r * P) := by
    have h := mul_le_mul_of_nonneg_right hN (mul_nonneg (mul_nonneg hr0 hr0) hP0)
    calc (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (1 + 1) * P
        = (∑ z ∈ s, ‖multDiff Z Z' z‖) * (r * r * P) := by ring
      _ ≤ 2 * (r * r * P) := h
      _ = 2 * r * (r * P) := by ring
  have h2 : 2 * r * (r * P) ≤ r / 2 := by
    have := mul_le_mul_of_nonneg_left hrP (by linarith : (0 : ℝ) ≤ 2 * r)
    linarith
  linarith


end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.norm_discMoment_rvm_le_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.pair_centre_and_gap_rvm_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.dipole_collapse_rvm_explicit
