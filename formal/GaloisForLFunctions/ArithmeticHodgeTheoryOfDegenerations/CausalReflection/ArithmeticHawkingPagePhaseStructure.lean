import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningSourceEndpointSelection
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningMinimizerOuterAndCyclic
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningGlobalTransverseGapAndResponse
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HalfLinePolarThresholdAndGroundStateOrthogonality

/-!
# Arithmetic Hawking–Page phase law and non-exclusion of the off-line saddle

This module establishes the complete thermodynamic phase structure of the half-line
confining variational problem and resolves the three candidate exclusion mechanisms:

1. **Strict exponential excess and two-sided secant bounds:** Every normalized profile
   `F ∈ CriticalHalfLineEnergyDomain` satisfies `1 < ∫ F² e^{-8u}`. Consequently, for
   `0 < t₁ < t₂` with normalized minimizers `F₁` at `t₁⁻¹` and `F₂` at `t₂⁻¹`,
   `0 < a(1) < a(1) W₈(F₂) < (μ(t₂) - μ(t₁)) / (t₂ - t₁) < a(1) W₈(F₁)`.
2. **Coupling-endpoint sign and Legendre-intercept identification:** On every coupling
   interval `[e^u, e^u + e^v]`, `confiningCoexistenceSource u v > a(1) > 0`; hence for
   all `z ≤ a(1)` (including `z = 0`), the weak-confinement endpoint `e^u` strictly wins
   whether or not `RiemannHypothesis` holds. Evaluating `confiningSourceEnergy z s` at
   the intrinsic conjugate pressure `z_R = a(1) W₈(F_R)` makes `s = R⁻¹` its unique
   strict global maximizer on `(0, ∞)` with maximum equal to `bareHalfLineEnergy F_R`.
3. **Occupation Hawking–Page transition on `{∫ G² ≤ 1}`:** Minimizing `E_R(G)` over
   `{G ∈ CriticalHalfLineEnergyDomain : ∫ G² ≤ 1}` equals `min(0, λ(R))`. `RiemannHypothesis`
   holds iff `0 < λ(R)` for all `R > 0` (the vacuum `G = 0` uniquely wins at every scale),
   iff `0 ≤ λ(R)` for all `R > 0`, iff `0 ≤ bareHalfLineEnergy G` on the domain. Off `RH`
   (`W = W₀ < ⊤`), `R = W₀` is the unique Hawking–Page transition point: `G = 0` uniquely
   minimizes on `(0, W₀)`, `[-1, 1] · F_{W₀}` minimizes at `W₀` with positive latent
   exponential-mass jump `μ'(W₀⁻¹) = a(1) W₈(F_{W₀}) > a(1)`, and `±F_R` uniquely minimizes
   with `λ(R) < 0` on `(W₀, ∞)`.
4. **Universal saddle stability:** At every `R > 0` unconditionally, `F_R` is unique up to
   sign, closed-RHP Laplace zero-free, outer, causal-cyclic, strictly Hessian-stable
   (`γ_R > 0`), and has positive coupling susceptibility (`μ` strictly concave and `C¹`),
   proving that the saddle never exhibits negative-specific-heat self-contradiction.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
  ArithmeticPositivityTheory WindowTowerOfSpecZ HTGeometry
open GaloisForLFunctions.HTGeometry.Thermodynamics

/-- Bare unconfined Weil energy on the half-line domain, prior to adding the eighth-exponential
confinement penalty `a(R) ∫ F² e^{-8u}`. -/
def bareHalfLineEnergy (F : ℝ → ℝ) : ℝ :=
  archForm F - primeSum F + (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2)

theorem criticalHalfLineFullEnergy_eq_bare_add_confinement (R : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    criticalHalfLineFullEnergy R F = bareHalfLineEnergy F +
      criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
  unfold criticalHalfLineFullEnergy bareHalfLineEnergy
  rw [halfLineExpMass_eq_full hF.support]

/-- Every unit-norm profile supported on `(-∞, 0)` has eighth-exponential mass strictly
greater than `1`. -/
theorem one_lt_exponential_mass_of_unit_domain {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hn : (∫ u, F u ^ 2) = 1) :
    1 < ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hle := one_le_exponential_square_of_domain hF hn
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hdiff_int : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u)) - F u ^ 2) :=
      hF.exponential.sub hF.sq
    have hnonneg : ∀ u, 0 ≤ F u ^ 2 * Real.exp (-(8 * u)) - F u ^ 2 := by
      intro u
      by_cases hu : 0 ≤ u
      · rw [hF.support u hu]
        norm_num
      · have he : 1 ≤ Real.exp (-(8 * u)) := Real.one_le_exp (by linarith only [hu])
        nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg (F u))]
    have hint0 : (∫ u, (F u ^ 2 * Real.exp (-(8 * u)) - F u ^ 2)) = 0 := by
      rw [integral_sub hF.exponential hF.sq, ← heq, hn, sub_self]
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall hnonneg) hdiff_int).mp hint0
    have hF2_ae : (fun u => F u ^ 2) =ᵐ[volume] 0 := by
      filter_upwards [hae] with u hu
      change F u ^ 2 * Real.exp (-(8 * u)) - F u ^ 2 = 0 at hu
      by_cases h0 : 0 ≤ u
      · change F u ^ 2 = 0
        rw [hF.support u h0, zero_pow two_ne_zero]
      · have he : 1 < Real.exp (-(8 * u)) := Real.one_lt_exp_iff.mpr (by linarith only [h0])
        change F u ^ 2 = 0
        nlinarith only [hu, he, sq_nonneg (F u)]
    have hm0 : (∫ u, F u ^ 2) = 0 := by
      rw [integral_congr_ae hF2_ae]
      simp
    linarith only [hm0, hn]

/-- Strict two-sided secant inequalities for `confiningHalfLineGroundEnergy`: on any
ordered pair `0 < t₁ < t₂`, the secant slope lies strictly between `a(1) W₈(F₂)` and
`a(1) W₈(F₁)`, and strictly above `a(1) > 0`. -/
theorem confiningHalfLineGroundEnergy_secant_bounds
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht : t₁ < t₂) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : IsHalfLineEnergyMinimizer t₁⁻¹ F₁)
    (hF₂ : IsHalfLineEnergyMinimizer t₂⁻¹ F₂) :
    criticalAliasCoefficient 1 <
        criticalAliasCoefficient 1 * (∫ u, F₂ u ^ 2 * Real.exp (-(8 * u))) ∧
      criticalAliasCoefficient 1 * (∫ u, F₂ u ^ 2 * Real.exp (-(8 * u))) <
        (confiningHalfLineGroundEnergy t₂ - confiningHalfLineGroundEnergy t₁) / (t₂ - t₁) ∧
      (confiningHalfLineGroundEnergy t₂ - confiningHalfLineGroundEnergy t₁) / (t₂ - t₁) <
        criticalAliasCoefficient 1 * (∫ u, F₁ u ^ 2 * Real.exp (-(8 * u))) := by
  have ht₂ : 0 < t₂ := ht₁.trans ht
  have hdiff_pos : 0 < t₂ - t₁ := sub_pos.mpr ht
  have ha1 : 0 < criticalAliasCoefficient 1 := criticalAliasCoefficient_positive zero_lt_one
  have hdistinct : t₁⁻¹ ≠ t₂⁻¹ := fun h =>
    ht.ne (by simpa only [inv_inv] using congrArg Inv.inv h)
  have hw2 : 1 < ∫ u, F₂ u ^ 2 * Real.exp (-(8 * u)) :=
    one_lt_exponential_mass_of_unit_domain hF₂.1 hF₂.2.1
  have hstrict_F₂ : criticalHalfLineGroundEnergy t₁⁻¹ < criticalHalfLineFullEnergy t₁⁻¹ F₂ := by
    rcases lt_or_eq_of_le (criticalHalfLineGroundEnergy_le (inv_pos.mpr ht₁) hF₂.1 hF₂.2.1) with
      hlt | heq
    · exact hlt
    · exact False.elim (hdistinct.symm (halfLineEnergyMinimizer_ratio_unique
        (inv_pos.mpr ht₂) (inv_pos.mpr ht₁) hF₂ ⟨hF₂.1, hF₂.2.1, heq.symm⟩))
  have hstrict_F₁ : criticalHalfLineGroundEnergy t₂⁻¹ < criticalHalfLineFullEnergy t₂⁻¹ F₁ := by
    rcases lt_or_eq_of_le (criticalHalfLineGroundEnergy_le (inv_pos.mpr ht₂) hF₁.1 hF₁.2.1) with
      hlt | heq
    · exact hlt
    · exact False.elim (hdistinct (halfLineEnergyMinimizer_ratio_unique
        (inv_pos.mpr ht₁) (inv_pos.mpr ht₂) hF₁ ⟨hF₁.1, hF₁.2.1, heq.symm⟩))
  have hc₂ := criticalHalfLineFullEnergy_change_ratio t₁⁻¹ t₂⁻¹ hF₂.1
  rw [hF₂.2.2, criticalAliasCoefficient_inv, criticalAliasCoefficient_inv] at hc₂
  have hc₁ := criticalHalfLineFullEnergy_change_ratio t₂⁻¹ t₁⁻¹ hF₁.1
  rw [hF₁.2.2, criticalAliasCoefficient_inv, criticalAliasCoefficient_inv] at hc₁
  refine ⟨by simpa only [mul_one] using mul_lt_mul_of_pos_left hw2 ha1, ?_, ?_⟩
  · apply (lt_div_iff₀ hdiff_pos).mpr
    unfold confiningHalfLineGroundEnergy
    nlinarith only [hstrict_F₂, hc₂]
  · apply (div_lt_iff₀ hdiff_pos).mpr
    unfold confiningHalfLineGroundEnergy
    nlinarith only [hstrict_F₁, hc₁]

/-- `confiningHalfLineGroundEnergy` is strictly increasing on `(0, ∞)`. -/
theorem confiningHalfLineGroundEnergy_strictMonoOn :
    StrictMonoOn confiningHalfLineGroundEnergy (Ioi 0) := by
  intro t₁ ht₁ t₂ ht₂ ht
  obtain ⟨F₁, hF₁⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr ht₁)
  obtain ⟨F₂, hF₂⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr ht₂)
  obtain ⟨h1, h2, _⟩ := confiningHalfLineGroundEnergy_secant_bounds ht₁ ht hF₁ hF₂
  have hpos : 0 < (confiningHalfLineGroundEnergy t₂ - confiningHalfLineGroundEnergy t₁) /
      (t₂ - t₁) := (criticalAliasCoefficient_positive zero_lt_one).trans (h1.trans h2)
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr ht)).mp hpos)

/-- `criticalHalfLineGroundEnergy` is strictly decreasing on `(0, ∞)`. -/
theorem criticalHalfLineGroundEnergy_strictAntiOn :
    StrictAntiOn criticalHalfLineGroundEnergy (Ioi 0) := by
  intro R₁ hR₁ R₂ hR₂ hlt
  have hinv : R₂⁻¹ < R₁⁻¹ := (inv_lt_inv₀ hR₂ hR₁).mpr hlt
  have hm := confiningHalfLineGroundEnergy_strictMonoOn (inv_pos.mpr hR₂) (inv_pos.mpr hR₁) hinv
  simpa only [confiningHalfLineGroundEnergy, inv_inv] using hm

/-! ### Resolution of (1) and (2): Coupling-endpoint sign and Legendre intercept -/

/-- Unconditionally at every confinement interval `[e^u, e^u + e^v]`, the coupling
coexistence source lies strictly above `criticalAliasCoefficient 1 > 0`. -/
theorem criticalAliasCoefficient_lt_confiningCoexistenceSource (u v : ℝ) :
    criticalAliasCoefficient 1 < confiningCoexistenceSource u v := by
  have ht₁ : 0 < Real.exp u := Real.exp_pos u
  have ht : Real.exp u < Real.exp u + Real.exp v := lt_add_of_pos_right _ (Real.exp_pos v)
  have ht₂ : 0 < Real.exp u + Real.exp v := ht₁.trans ht
  obtain ⟨F₁, hF₁⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr ht₁)
  obtain ⟨F₂, hF₂⟩ := exists_criticalHalfLineGroundEnergy_minimizer (inv_pos.mpr ht₂)
  obtain ⟨h1, h2, _⟩ := confiningHalfLineGroundEnergy_secant_bounds ht₁ ht hF₁ hF₂
  have heq : (confiningHalfLineGroundEnergy (Real.exp u + Real.exp v) -
      confiningHalfLineGroundEnergy (Real.exp u)) /
      ((Real.exp u + Real.exp v) - Real.exp u) = confiningCoexistenceSource u v := by
    unfold confiningCoexistenceSource coexistenceSource
    congr 1
    ring
  rw [heq] at h2
  exact h1.trans h2

/-- **Unconditional Coupling-Endpoint Sign Law (Refuting (2)):** For every external source
`z ≤ criticalAliasCoefficient 1` (in particular at `z = 0` and for all `z ≤ 0`) and every
scale pair `(u, v) ∈ ℝ²`, the weak-confinement (larger-`R`) endpoint `t = e^u` strictly
beats the strong-confinement endpoint `t = e^u + e^v`, regardless of `RiemannHypothesis`. -/
theorem confiningSourceEnergy_weak_endpoint_strict_lt (u v : ℝ) {z : ℝ}
    (hz : z ≤ criticalAliasCoefficient 1) :
    confiningSourceEnergy z (Real.exp u) <
      confiningSourceEnergy z (Real.exp u + Real.exp v) := by
  have hcoex := hz.trans_lt (criticalAliasCoefficient_lt_confiningCoexistenceSource u v)
  have hgap := endpoint_gap (confiningHalfLineGroundEnergy (Real.exp u))
    (confiningHalfLineGroundEnergy (Real.exp u + Real.exp v)) (Real.exp u) v z
  have hpos : 0 < Real.exp v * (confiningCoexistenceSource u v - z) :=
    mul_pos (Real.exp_pos v) (sub_pos.mpr hcoex)
  unfold confiningSourceEnergy confiningCoexistenceSource at *
  linarith only [hgap, hpos]

/-- At zero external source (`z = 0`), the coupling-interval minimum equals the weak-confinement
endpoint value `confiningHalfLineGroundEnergy (e^u)` at every scale `(u, v) ∈ ℝ²`. -/
theorem confiningIntervalSourceFloor_zero_eq_weak_endpoint (u v : ℝ) :
    confiningIntervalSourceFloor u v 0 = confiningHalfLineGroundEnergy (Real.exp u) := by
  rw [confiningIntervalSourceFloor_eq]
  have hz : (0 : ℝ) ≤ confiningCoexistenceSource u v :=
    (criticalAliasCoefficient_positive zero_lt_one).le.trans
      (criticalAliasCoefficient_lt_confiningCoexistenceSource u v).le
  have heq := (endpointPotential_eq_lower_iff
    (confiningHalfLineGroundEnergy (Real.exp u))
    (confiningHalfLineGroundEnergy (Real.exp u + Real.exp v))
    (Real.exp u) v 0).mpr hz
  simpa only [zero_mul, sub_zero] using heq

/-- **Exact Legendre-Intercept Identification (Salvage of (1)):** At the intrinsic conjugate
pressure `z_R = a(1) W₈(F_R)` of a normalized minimizer `F_R` (`R > 0`), `s ↦ confiningSourceEnergy z_R s`
attains its unique strict global maximum on `(0, ∞)` at `s = R⁻¹`, and that maximum equals
the bare unconfined Weil energy `bareHalfLineEnergy F_R`. -/
theorem IsHalfLineEnergyMinimizer.confiningSourceEnergy_legendre_intercept
    {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    let zR := criticalAliasCoefficient 1 * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))
    confiningSourceEnergy zR R⁻¹ = bareHalfLineEnergy F ∧
      ∀ s : ℝ, 0 < s → s ≠ R⁻¹ → confiningSourceEnergy zR s < bareHalfLineEnergy F := by
  intro zR
  have hval : confiningSourceEnergy zR R⁻¹ = bareHalfLineEnergy F := by
    unfold confiningSourceEnergy confiningHalfLineGroundEnergy
    rw [inv_inv, ← hF.2.2, criticalHalfLineFullEnergy_eq_bare_add_confinement R hF.1,
      criticalAliasCoefficient_eq_div]
    dsimp only [zR]
    field_simp [hR.ne']
    ring
  refine ⟨hval, fun s hs hne => ?_⟩
  have hs_ne_R : s⁻¹ ≠ R := fun h => hne (by simpa only [inv_inv] using congrArg Inv.inv h)
  have hstrict : criticalHalfLineGroundEnergy s⁻¹ < criticalHalfLineFullEnergy s⁻¹ F := by
    rcases lt_or_eq_of_le (criticalHalfLineGroundEnergy_le (inv_pos.mpr hs) hF.1 hF.2.1) with
      hlt | heq
    · exact hlt
    · exact False.elim (hs_ne_R (halfLineEnergyMinimizer_ratio_unique
        (inv_pos.mpr hs) hR ⟨hF.1, hF.2.1, heq.symm⟩ hF))
  rw [criticalHalfLineFullEnergy_eq_bare_add_confinement s⁻¹ hF.1, criticalAliasCoefficient_inv]
    at hstrict
  unfold confiningSourceEnergy confiningHalfLineGroundEnergy
  dsimp only [zR]
  linarith only [hstrict]

/-! ### Occupation-ball Hawking–Page transition and exact `RH` equivalences -/

private theorem zero_mass_iff_ae_zero_domain {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    (∫ u, G u ^ 2) = 0 ↔ G =ᵐ[volume] 0 := by
  constructor
  · intro hm
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun u => sq_nonneg (G u)) hG.sq).mp hm
    filter_upwards [hae] with u hu
    change G u ^ 2 = 0 at hu
    change G u = 0
    nlinarith only [hu]
  · intro hae
    calc (∫ u, G u ^ 2) = ∫ _u : ℝ, (0 : ℝ) := by
          apply integral_congr_ae
          filter_upwards [hae] with u hu
          change G u = 0 at hu
          simp only [hu, zero_pow two_ne_zero]
      _ = 0 := by simp

private theorem fullEnergy_zero_of_ae_zero {R : ℝ} {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hae : G =ᵐ[volume] 0) :
    criticalHalfLineFullEnergy R G = 0 := by
  have hz : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) := by
    have hw : IsWindowTest 0 (fun _ : ℝ => (0 : ℝ)) :=
      { contDiff := contDiff_const, vanish := fun _ _ => rfl }
    exact criticalHalfLineEnergyDomain_of_window hw
  rw [criticalHalfLineFullEnergy_congr_ae hG hz hae]
  have hp0 : paperFT (cx (fun _ : ℝ => (0 : ℝ))) = 0 := by
    funext z; simp [paperFT, cx]
  simp [criticalHalfLineFullEnergy, archForm, hp0, primeSum, coshHalfMoment,
    sinhHalfMoment, halfLineExpMass_eq_full hz.support]

/-- **Variational Unit-Ball Envelope Law:** At every positive confinement ratio `R > 0`,
minimizing `criticalHalfLineFullEnergy R` on the occupation ball `{∫ G² ≤ 1}` reduces
to linear competition between the thermal-AdS vacuum (`G = 0`, energy `0`) and the
normalized confining saddle (`G = ±F_R`, energy `criticalHalfLineGroundEnergy R`). -/
theorem sInf_unitBall_criticalHalfLineFullEnergy_eq_min {R : ℝ} (hR : 0 < R) :
    sInf {e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧
      (∫ u, G u ^ 2) ≤ 1 ∧ criticalHalfLineFullEnergy R G = e} =
        min 0 (criticalHalfLineGroundEnergy R) := by
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  have hz : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) :=
    criticalHalfLineEnergyDomain_of_window { contDiff := contDiff_const, vanish := fun _ _ => rfl }
  have hz_mass : (∫ u, (0 : ℝ) ^ 2) ≤ 1 := by simp
  have hz_E : criticalHalfLineFullEnergy R (fun _ : ℝ => (0 : ℝ)) = 0 :=
    fullEnergy_zero_of_ae_zero hz EventuallyEq.rfl
  apply IsLeast.csInf_eq
  constructor
  · by_cases h0 : 0 ≤ criticalHalfLineGroundEnergy R
    · rw [min_eq_left h0]
      exact ⟨0, hz, hz_mass, hz_E⟩
    · rw [min_eq_right (le_of_not_ge h0)]
      exact ⟨F, hF.1, hF.2.1.le, hF.2.2⟩
  · rintro _ ⟨G, hG, hm, rfl⟩
    have hm0 : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hlow := criticalHalfLineGroundEnergy_mul_mass_le_all hR hG
    by_cases hpos : 0 ≤ criticalHalfLineGroundEnergy R
    · rw [min_eq_left hpos]
      exact (mul_nonneg hpos hm0).trans hlow
    · rw [min_eq_right (le_of_not_ge hpos)]
      have hneg : criticalHalfLineGroundEnergy R ≤ 0 := le_of_not_ge hpos
      have hm1 : criticalHalfLineGroundEnergy R ≤ criticalHalfLineGroundEnergy R * ∫ u, G u ^ 2 := by
        nlinarith only [hneg, hm, hm0]
      exact hm1.trans hlow

/-- Under `RiemannHypothesis`, `bareHalfLineEnergy G ≥ 0` on the entire half-line domain. -/
theorem bareHalfLineEnergy_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    0 ≤ bareHalfLineEnergy G := by
  have hW : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = ⊤ := by
    rw [← highConductorCriticalThreshold_eq_iInf_windowThreshold]
    exact highConductorCriticalThreshold_eq_top_iff_riemannHypothesis.mpr hRH
  let w : ℝ := ∫ u, G u ^ 2 * Real.exp (-(8 * u))
  have hpos_seq (k : ℕ) : 0 ≤ bareHalfLineEnergy G +
      criticalAliasCoefficient 1 * w * (1 / ((k : ℝ) + 1)) := by
    let S : ℝ := (k : ℝ) + 1
    have hS : 0 < S := by dsimp only [S]; positivity
    have hlt : (S : EReal) < ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
      rw [hW]; exact EReal.coe_lt_top S
    have hE := criticalHalfLineFullEnergy_nonneg_below_windowThreshold hS hlt hG
    rw [criticalHalfLineFullEnergy_eq_bare_add_confinement S hG, criticalAliasCoefficient_eq_div]
      at hE
    convert hE using 1
    dsimp only [S, w]
    ring
  have hlim : Tendsto (fun k : ℕ => bareHalfLineEnergy G +
      criticalAliasCoefficient 1 * w * (1 / ((k : ℝ) + 1))) atTop (𝓝 (bareHalfLineEnergy G)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
        (criticalAliasCoefficient 1 * w)).const_add (bareHalfLineEnergy G)
  exact ge_of_tendsto' hlim hpos_seq

/-- Under `RiemannHypothesis`, `criticalHalfLineGroundEnergy R > criticalAliasCoefficient R > 0`
at every positive confinement ratio `R > 0`. -/
theorem criticalAliasCoefficient_lt_groundEnergy_of_riemannHypothesis
    (hRH : RiemannHypothesis) {R : ℝ} (hR : 0 < R) :
    criticalAliasCoefficient R < criticalHalfLineGroundEnergy R := by
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  have hbare := bareHalfLineEnergy_nonneg_of_riemannHypothesis hRH hF.1
  have hw := one_lt_exponential_mass_of_unit_domain hF.1 hF.2.1
  have ha := criticalAliasCoefficient_positive hR
  have hgt : criticalAliasCoefficient R <
      criticalAliasCoefficient R * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left hw ha
  rw [← hF.2.2, criticalHalfLineFullEnergy_eq_bare_add_confinement R hF.1]
  linarith only [hbare, hgt]

/-- **Exact Thermodynamic Equivalences of `RiemannHypothesis`:**
`RH` is equivalent to strict positivity of `criticalHalfLineGroundEnergy R` at all `R > 0`,
nonnegativity of `criticalHalfLineGroundEnergy R` at all `R > 0`, nonnegativity of
`bareHalfLineEnergy` on the domain, nonnegativity of the intrinsic Legendre intercept
at all `R > 0`, and unique global optimality of the zero-energy vacuum `G = 0` on the
occupation ball `{∫ G² ≤ 1}` at every `R > 0`. -/
theorem riemannHypothesis_thermodynamic_equivalences :
    (RiemannHypothesis ↔ ∀ R : ℝ, 0 < R → 0 < criticalHalfLineGroundEnergy R) ∧
    (RiemannHypothesis ↔ ∀ R : ℝ, 0 < R → 0 ≤ criticalHalfLineGroundEnergy R) ∧
    (RiemannHypothesis ↔ ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → 0 ≤ bareHalfLineEnergy G) ∧
    (RiemannHypothesis ↔ ∀ (R : ℝ) (F : ℝ → ℝ), 0 < R → IsHalfLineEnergyMinimizer R F →
      0 ≤ confiningSourceEnergy
        (criticalAliasCoefficient 1 * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) R⁻¹) ∧
    (RiemannHypothesis ↔ ∀ (R : ℝ) (G : ℝ → ℝ), 0 < R → CriticalHalfLineEnergyDomain G →
      (∫ u, G u ^ 2) ≤ 1 →
        0 ≤ criticalHalfLineFullEnergy R G ∧
          (criticalHalfLineFullEnergy R G = 0 ↔ G =ᵐ[volume] 0)) := by
  have h_imp_RH : (∀ R : ℝ, 0 < R → 0 ≤ criticalHalfLineGroundEnergy R) → RiemannHypothesis := by
    intro hnonneg
    rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F₀, hW₀, ht, hF₀⟩
    · exact hRH
    · exfalso
      have hz := criticalHalfLineGroundEnergy_eq_zero hW₀ ht hF₀
      have hneg : criticalHalfLineGroundEnergy (W₀ + 1) < 0 := by
        rw [← hz]
        exact criticalHalfLineGroundEnergy_strictAntiOn hW₀ (by linarith only [hW₀])
          (lt_add_one W₀)
      linarith only [hneg, hnonneg (W₀ + 1) (by linarith only [hW₀])]
  have h1 : RiemannHypothesis ↔ ∀ R : ℝ, 0 < R → 0 < criticalHalfLineGroundEnergy R :=
    ⟨fun hRH R hR => (criticalAliasCoefficient_positive hR).trans
        (criticalAliasCoefficient_lt_groundEnergy_of_riemannHypothesis hRH hR),
      fun hpos => h_imp_RH fun R hR => (hpos R hR).le⟩
  have h2 : RiemannHypothesis ↔ ∀ R : ℝ, 0 < R → 0 ≤ criticalHalfLineGroundEnergy R :=
    ⟨fun hRH R hR => (h1.mp hRH R hR).le, h_imp_RH⟩
  have h3 : RiemannHypothesis ↔
      ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → 0 ≤ bareHalfLineEnergy G := by
    refine ⟨fun hRH _ hG => bareHalfLineEnergy_nonneg_of_riemannHypothesis hRH hG, fun hbare => ?_⟩
    apply h_imp_RH
    intro R hR
    obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
    rw [← hF.2.2, criticalHalfLineFullEnergy_eq_bare_add_confinement R hF.1]
    exact add_nonneg (hbare F hF.1) (mul_nonneg (criticalAliasCoefficient_positive hR).le
      (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
  have h4 : RiemannHypothesis ↔ ∀ (R : ℝ) (F : ℝ → ℝ), 0 < R → IsHalfLineEnergyMinimizer R F →
      0 ≤ confiningSourceEnergy
        (criticalAliasCoefficient 1 * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) R⁻¹ := by
    refine ⟨fun hRH R F hR hF => ?_, fun hleg => ?_⟩
    · rw [(hF.confiningSourceEnergy_legendre_intercept hR).1]
      exact bareHalfLineEnergy_nonneg_of_riemannHypothesis hRH hF.1
    · apply h_imp_RH
      intro R hR
      obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
      have hb : 0 ≤ bareHalfLineEnergy F := by
        rw [← (hF.confiningSourceEnergy_legendre_intercept hR).1]
        exact hleg R F hR hF
      rw [← hF.2.2, criticalHalfLineFullEnergy_eq_bare_add_confinement R hF.1]
      exact add_nonneg hb (mul_nonneg (criticalAliasCoefficient_positive hR).le
        (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
  have h5 : RiemannHypothesis ↔ ∀ (R : ℝ) (G : ℝ → ℝ), 0 < R → CriticalHalfLineEnergyDomain G →
      (∫ u, G u ^ 2) ≤ 1 →
        0 ≤ criticalHalfLineFullEnergy R G ∧
          (criticalHalfLineFullEnergy R G = 0 ↔ G =ᵐ[volume] 0) := by
    refine ⟨fun hRH R G hR hG _ => ?_, fun hvac => ?_⟩
    · have hλ := h1.mp hRH R hR
      have hm0 : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
      have hlow := criticalHalfLineGroundEnergy_mul_mass_le_all hR hG
      refine ⟨(mul_nonneg hλ.le hm0).trans hlow, ?_⟩
      constructor
      · intro hE0
        have hm_zero : (∫ u, G u ^ 2) = 0 := by nlinarith only [hλ, hm0, hlow, hE0]
        exact (zero_mass_iff_ae_zero_domain hG).mp hm_zero
      · exact fullEnergy_zero_of_ae_zero hG
    · apply h1.mpr
      intro R hR
      obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
      obtain ⟨hnonneg, hiff⟩ := hvac R F hR hF.1 hF.2.1.le
      rw [← hF.2.2]
      rcases lt_or_eq_of_le hnonneg with hpos | heq
      · exact hpos
      · exfalso
        have hm0 := (zero_mass_iff_ae_zero_domain hF.1).mpr (hiff.mp heq.symm)
        linarith only [hm0, hF.2.1]
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **Off-RH Arithmetic Hawking–Page Phase Transition:** When `¬ RiemannHypothesis`,
there exists a unique critical confinement ratio `W₀ > 0` (`W₀ = ⨅ A ≥ 0, windowThreshold A`)
separating the occupation-ball minimization into three exact regimes:
1. **Thermal-AdS vacuum phase (`0 < R < W₀`):** `0 < λ(R)`, unit-ball floor `= 0`, and `G = 0`
   is the unique unit-ball minimizer up to null sets.
2. **First-order Hawking–Page coexistence (`R = W₀`):** `λ(W₀) = 0`, unit-ball minimizers form
   the segment `{c F_{W₀} : c ∈ [-1, 1]}` a.e., and the coupling slope jumps by
   `μ'(W₀⁻¹) = a(1) W₈(F_{W₀}) > a(1) > 0`.
3. **Condensed black-hole phase (`W₀ < R`):** `λ(R) < 0`, unit-ball floor `= λ(R) < 0`, and
   `G = ±F_R` are the unique unit-ball minimizers up to null sets. -/
theorem offLine_arithmetic_hawking_page_transition (hnotRH : ¬ RiemannHypothesis) :
    ∃ (W₀ : ℝ) (F₀ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsHalfLineEnergyMinimizer W₀ F₀ ∧
      criticalHalfLineGroundEnergy W₀ = 0 ∧
      HasDerivAt confiningHalfLineGroundEnergy
        (criticalAliasCoefficient 1 * (∫ u, F₀ u ^ 2 * Real.exp (-(8 * u)))) W₀⁻¹ ∧
      criticalAliasCoefficient 1 <
        criticalAliasCoefficient 1 * (∫ u, F₀ u ^ 2 * Real.exp (-(8 * u))) ∧
      (∀ R : ℝ, 0 < R → R < W₀ →
        0 < criticalHalfLineGroundEnergy R ∧
          ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → (∫ u, G u ^ 2) ≤ 1 →
            (criticalHalfLineFullEnergy R G = 0 ↔ G =ᵐ[volume] 0)) ∧
      (∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → (∫ u, G u ^ 2) ≤ 1 →
        0 ≤ criticalHalfLineFullEnergy W₀ G ∧
          (criticalHalfLineFullEnergy W₀ G = 0 ↔
            ∃ c : ℝ, c ∈ Icc (-1 : ℝ) 1 ∧ G =ᵐ[volume] fun u => c * F₀ u)) ∧
      (∀ R : ℝ, W₀ < R →
        criticalHalfLineGroundEnergy R < 0 ∧
          ∀ F : ℝ → ℝ, IsHalfLineEnergyMinimizer R F →
            ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → (∫ u, G u ^ 2) ≤ 1 →
              criticalHalfLineGroundEnergy R ≤ criticalHalfLineFullEnergy R G ∧
                (criticalHalfLineFullEnergy R G = criticalHalfLineGroundEnergy R ↔
                  G =ᵐ[volume] F ∨ G =ᵐ[volume] fun u => -F u)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F₀, hW₀, ht, hF₀⟩
  · exact False.elim (hnotRH hRH)
  have hλ0 : criticalHalfLineGroundEnergy W₀ = 0 :=
    criticalHalfLineGroundEnergy_eq_zero hW₀ ht hF₀
  have hdF₀ := criticalHalfLineEnergyDomain_of_groundState hF₀
  have hmin₀ : IsHalfLineEnergyMinimizer W₀ F₀ := by
    refine ⟨hdF₀, hF₀.2.2.2.1, ?_⟩
    rw [hλ0]
    exact criticalHalfLineFullEnergy_groundState_eq_zero hW₀ ht hF₀
  have hderiv := hasDerivAt_confiningHalfLineGroundEnergy_of_minimizer
    (inv_pos.mpr hW₀) (by simpa only [inv_inv] using hmin₀)
  have hlatent : criticalAliasCoefficient 1 <
      criticalAliasCoefficient 1 * (∫ u, F₀ u ^ 2 * Real.exp (-(8 * u))) := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left
      (one_lt_exponential_mass_of_unit_domain hdF₀ hF₀.2.2.2.1)
      (criticalAliasCoefficient_positive zero_lt_one)
  refine ⟨W₀, F₀, hW₀, ht, hmin₀, hλ0, hderiv, hlatent, ?_, ?_, ?_⟩
  · -- Regime 1: 0 < R < W₀ (strict thermal-AdS vacuum phase).
    intro R hR hRW
    have hpos : 0 < criticalHalfLineGroundEnergy R := by
      rw [← hλ0]
      exact criticalHalfLineGroundEnergy_strictAntiOn hR hW₀ hRW
    refine ⟨hpos, fun G hG _ => ⟨fun hE0 => ?_, fullEnergy_zero_of_ae_zero hG⟩⟩
    have hm0 : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hlow := criticalHalfLineGroundEnergy_mul_mass_le_all hR hG
    have hm_zero : (∫ u, G u ^ 2) = 0 := by nlinarith only [hpos, hm0, hlow, hE0]
    exact (zero_mass_iff_ae_zero_domain hG).mp hm_zero
  · -- Regime 2: R = W₀ (first-order coexistence segment [-1, 1] · F₀).
    intro G hG hm1
    have hE_nonneg := criticalHalfLineFullEnergy_nonneg_at_windowThreshold hW₀ ht hG
    refine ⟨hE_nonneg, ?_⟩
    constructor
    · intro hE0
      obtain ⟨γ, hγ, hgap⟩ := hmin₀.controls_neutralPart hW₀
      have hQ0 : confiningShiftedEnergy W₀ G = 0 := by
        unfold confiningShiftedEnergy
        rw [hE0, hλ0, zero_mul, sub_self]
      have hn_le := hgap hG
      rw [hQ0] at hn_le
      have hn_nonneg : 0 ≤ ∫ u, criticalHalfLineNeutralPart F₀ G u ^ 2 * Real.exp (-(8 * u)) :=
        integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
      have hn0 : (∫ u, criticalHalfLineNeutralPart F₀ G u ^ 2 * Real.exp (-(8 * u))) = 0 :=
        le_antisymm (by nlinarith only [hγ, hn_le]) hn_nonneg
      have hdN := hdF₀.neutralPart hG
      have hmN0 : (∫ u, criticalHalfLineNeutralPart F₀ G u ^ 2) = 0 :=
        le_antisymm (hdN.square_mass_le_exponential_mass.trans_eq hn0)
          (integral_nonneg fun u => sq_nonneg _)
      have hNae := (zero_mass_iff_ae_zero_domain hdN).mp hmN0
      let c : ℝ := ∫ v, F₀ v * G v
      have hG_ae : G =ᵐ[volume] fun u => c * F₀ u := by
        filter_upwards [hNae] with u hu
        change G u - c * F₀ u = 0 at hu
        linarith only [hu]
      have hc2 : c ^ 2 ≤ 1 := by
        have hcm : (∫ u, G u ^ 2) = c ^ 2 := by
          calc (∫ u, G u ^ 2) = ∫ u, c ^ 2 * F₀ u ^ 2 := by
                apply integral_congr_ae
                filter_upwards [hG_ae] with u hu
                rw [hu, mul_pow]
            _ = c ^ 2 := by rw [integral_const_mul, hF₀.2.2.2.1, mul_one]
        linarith only [hcm, hm1]
      have hc_mem : c ∈ Icc (-1 : ℝ) 1 := by
        refine ⟨?_, ?_⟩
        · nlinarith only [hc2, sq_nonneg (c + 1)]
        · nlinarith only [hc2, sq_nonneg (c - 1)]
      exact ⟨c, hc_mem, hG_ae⟩
    · rintro ⟨c, _, hG_ae⟩
      rw [criticalHalfLineFullEnergy_congr_ae hG (hdF₀.const_mul c) hG_ae,
        criticalHalfLineFullEnergy_const_mul, hmin₀.2.2, hλ0, mul_zero]
  · -- Regime 3: W₀ < R (condensed black-hole phase ±F_R).
    intro R hWR
    have hR : 0 < R := hW₀.trans hWR
    have hneg : criticalHalfLineGroundEnergy R < 0 := by
      rw [← hλ0]
      exact criticalHalfLineGroundEnergy_strictAntiOn hW₀ hR hWR
    refine ⟨hneg, fun F hF G hG hm1 => ?_⟩
    have hm0 : 0 ≤ ∫ u, G u ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hlow := criticalHalfLineGroundEnergy_mul_mass_le_all hR hG
    have hm_ineq : criticalHalfLineGroundEnergy R ≤
        criticalHalfLineGroundEnergy R * (∫ u, G u ^ 2) := by
      nlinarith only [hneg, hm1, hm0]
    refine ⟨hm_ineq.trans hlow, ?_⟩
    constructor
    · intro hEq
      have hm_one : (∫ u, G u ^ 2) = 1 := by nlinarith only [hneg, hm1, hlow, hEq]
      exact halfLineEnergyMinimizer_unique_up_to_sign hR ⟨hG, hm_one, hEq⟩ hF
    · rintro (hae | hae)
      · rw [criticalHalfLineFullEnergy_congr_ae hG hF.1 hae]
        exact hF.2.2
      · rw [criticalHalfLineFullEnergy_congr_ae hG (hF.1.const_mul (-1))
          (hae.mono fun u hu => by simp only [hu, neg_one_mul]),
          criticalHalfLineFullEnergy_const_mul]
        norm_num [hF.2.2]

/-- **Exact Comparison of `confiningSourceEnergy`, `W = ⨅ A ≥ 0, windowThreshold A`, and
`polarPaymentCriticalThreshold`:**
`polarPaymentCriticalThreshold ≤ W` unconditionally, with `polarPaymentCriticalThreshold = ⊤ ↔
W = ⊤ ↔ RiemannHypothesis`. Off `RH`, `W = (W₀ : EReal)` (`0 < W₀`) is the unique zero of
`criticalHalfLineGroundEnergy` on `(0, ∞)` (and `W₀⁻¹` is the unique zero of
`confiningHalfLineGroundEnergy`), where the intrinsic Legendre intercept of `confiningSourceEnergy`
equals `-a(W₀) W₈(F) < -a(W₀) < 0` on every normalized minimizer `F` at `W₀`, and any nonzero
polar pairing `∫ F · polarSourceProfile ≠ 0` strictly lowers `polarPaymentCriticalThreshold < W₀`. -/
theorem hawking_page_threshold_and_polar_comparison :
    let W := ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A
    polarPaymentCriticalThreshold ≤ W ∧
    (polarPaymentCriticalThreshold = ⊤ ↔ W = ⊤) ∧
    (W = ⊤ ↔ RiemannHypothesis) ∧
    (¬ RiemannHypothesis → ∃ W₀ : ℝ, 0 < W₀ ∧ W = (W₀ : EReal) ∧
      polarPaymentCriticalThreshold ≤ (W₀ : EReal) ∧
      (∀ R : ℝ, 0 < R → (criticalHalfLineGroundEnergy R = 0 ↔ R = W₀)) ∧
      (∀ t : ℝ, 0 < t → (confiningHalfLineGroundEnergy t = 0 ↔ t = W₀⁻¹)) ∧
      (∀ F : ℝ → ℝ, IsHalfLineEnergyMinimizer W₀ F →
        confiningSourceEnergy
          (criticalAliasCoefficient 1 * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) W₀⁻¹ =
            -(criticalAliasCoefficient W₀ * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) ∧
        ((∫ u, F u * polarSourceProfile u) ≠ 0 →
          polarPaymentCriticalThreshold < (W₀ : EReal)))) := by
  intro W
  have hle : polarPaymentCriticalThreshold ≤ W := polarPaymentCriticalThreshold_le_iInf_windowThreshold
  have hW_iff : W = ⊤ ↔ RiemannHypothesis := by
    dsimp only [W]
    rw [← highConductorCriticalThreshold_eq_iInf_windowThreshold]
    exact highConductorCriticalThreshold_eq_top_iff_riemannHypothesis
  have hpol_iff : polarPaymentCriticalThreshold = ⊤ ↔ W = ⊤ :=
    polarPaymentCriticalThreshold_eq_top_iff_riemannHypothesis.trans hW_iff.symm
  refine ⟨hle, hpol_iff, hW_iff, fun hnotRH => ?_⟩
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F₀, hW₀, ht, hF₀⟩
  · exact False.elim (hnotRH hRH)
  have hλ0 : criticalHalfLineGroundEnergy W₀ = 0 :=
    criticalHalfLineGroundEnergy_eq_zero hW₀ ht hF₀
  have hdF₀ := criticalHalfLineEnergyDomain_of_groundState hF₀
  have hmin₀ : IsHalfLineEnergyMinimizer W₀ F₀ := by
    refine ⟨hdF₀, hF₀.2.2.2.1, ?_⟩
    rw [hλ0]
    exact criticalHalfLineFullEnergy_groundState_eq_zero hW₀ ht hF₀
  refine ⟨W₀, hW₀, ht, ht ▸ hle, ?_, ?_, ?_⟩
  · intro R hR
    refine ⟨fun h0 => ?_, fun hEq => hEq ▸ hλ0⟩
    rcases lt_trichotomy R W₀ with hlt | rfl | hgt
    · have := criticalHalfLineGroundEnergy_strictAntiOn hR hW₀ hlt
      linarith only [this, h0, hλ0]
    · rfl
    · have := criticalHalfLineGroundEnergy_strictAntiOn hW₀ hR hgt
      linarith only [this, h0, hλ0]
  · intro t ht_pos
    refine ⟨fun h0 => ?_, fun hEq => ?_⟩
    · have hR_eq : t⁻¹ = W₀ := by
        rcases lt_trichotomy t⁻¹ W₀ with hlt | heq | hgt
        · have := criticalHalfLineGroundEnergy_strictAntiOn (inv_pos.mpr ht_pos) hW₀ hlt
          unfold confiningHalfLineGroundEnergy at h0
          linarith only [this, h0, hλ0]
        · exact heq
        · have := criticalHalfLineGroundEnergy_strictAntiOn hW₀ (inv_pos.mpr ht_pos) hgt
          unfold confiningHalfLineGroundEnergy at h0
          linarith only [this, h0, hλ0]
      simpa only [inv_inv] using congrArg Inv.inv hR_eq
    · rw [hEq]
      unfold confiningHalfLineGroundEnergy
      rwa [inv_inv]
  · intro F hF
    refine ⟨?_, fun hP => ?_⟩
    · rw [(hF.confiningSourceEnergy_legendre_intercept hW₀).1]
      have hsum := criticalHalfLineFullEnergy_eq_bare_add_confinement W₀ hF.1
      rw [hF.2.2, hλ0] at hsum
      linarith only [hsum]
    · have hP₀ : (∫ u, F₀ u * polarSourceProfile u) ≠ 0 := by
        rcases halfLineEnergyMinimizer_unique_up_to_sign hW₀ hF hmin₀ with hae | hae
        · intro hz
          apply hP
          rw [← hz]
          exact integral_congr_ae (hae.mono fun u hu => by rw [hu])
        · intro hz
          apply hP
          have hneg : (∫ u, F u * polarSourceProfile u) = -(∫ u, F₀ u * polarSourceProfile u) := by
            rw [← integral_neg]
            exact integral_congr_ae (hae.mono fun u hu => by rw [hu]; ring)
          rw [hneg, hz, neg_zero]
      exact polarPaymentCriticalThreshold_lt_of_charged_criticalHalfLineGroundState hW₀ hF₀ hP₀

/-! ### Resolution of (3): Universal saddle stability and non-exclusion at every `R > 0` -/

/-- **Universal Saddle Rigidity and Stability Theorem (Refuting (3)):** At every positive
confinement ratio `R > 0` — unconditionally, whether `RiemannHypothesis` is true or false —
the normalized confining minimizer `F_R` exists and simultaneously possesses:
1. Uniqueness up to sign;
2. Nonvanishing Laplace transform on the entire closed right half-plane `Re z ≥ 0`;
3. Outer Cayley–Laplace disk multiplier;
4. Dense causal translation span `causalCyclicSubspace = ⊤` on `L²(0, ∞)`;
5. Strictly positive eighth-exponential transverse Hessian gap `γ > 0`;
6. Differentiable ground energy with locally Lipschitz state response and strictly concave
   coupling free energy (positive coupling susceptibility, never negative specific heat). -/
theorem universal_confining_saddle_rigidity_and_stability (R : ℝ) (hR : 0 < R) :
    ∃ (F : ℝ → ℝ) (hF : IsHalfLineEnergyMinimizer R F) (γ δ L : ℝ),
      0 < γ ∧ 0 < δ ∧ 0 ≤ L ∧
      (∀ H : ℝ → ℝ, IsHalfLineEnergyMinimizer R H →
        H =ᵐ[volume] F ∨ H =ᵐ[volume] fun u => -F u) ∧
      (∀ z : ℂ, 0 ≤ z.re → negativeHalfLineLaplace (cx F) z ≠ 0) ∧
      IsOuterDiskMultiplier (halfLineMinimizerLaplaceMultiplier hF) ∧
      causalCyclicSubspace (reflectedHalfLineMinimizerDatum hF) = ⊤ ∧
      (∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        γ * (∫ u, criticalHalfLineNeutralPart F G u ^ 2 * Real.exp (-(8 * u))) ≤
          confiningShiftedEnergy R G) ∧
      HasDerivAt criticalHalfLineGroundEnergy
        (-(criticalAliasCoefficient R) * (∫ u, F u ^ 2 * Real.exp (-(8 * u))) / R) R ∧
      (∀ S : ℝ, 0 < S → |criticalAliasCoefficient S - criticalAliasCoefficient R| ≤ δ →
        ∀ H : ℝ → ℝ, IsHalfLineEnergyMinimizer S H →
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            (∫ u, (H u - σ * F u) ^ 2 * Real.exp (-(8 * u))) ≤
              L ^ 2 * (criticalAliasCoefficient S - criticalAliasCoefficient R) ^ 2) := by
  obtain ⟨F, hF⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  obtain ⟨γ, hγ, hgap⟩ := hF.controls_neutralPart hR
  obtain ⟨δ, L, hδ, hL, hlip⟩ := hF.minimizer_lipschitz_stability hR
  exact ⟨F, hF, γ, δ, L, hγ, hδ, hL,
    fun _ hH => halfLineEnergyMinimizer_unique_up_to_sign hR hH hF,
    fun _ hz => hF.closedRightHalfPlaneLaplace_ne_zero hR hz,
    hF.laplaceMultiplier_outer hR,
    hF.causalCyclicSubspace_eq_top hR,
    fun _ hG => hgap hG,
    hF.hasDerivAt_criticalHalfLineGroundEnergy hR,
    fun S hS hsmall H hH => by
      obtain ⟨σ, hσ, hd, _, _⟩ := hlip S hS hsmall H hH
      exact ⟨σ, hσ, hd⟩⟩

#print axioms confiningHalfLineGroundEnergy_secant_bounds
#print axioms confiningSourceEnergy_weak_endpoint_strict_lt
#print axioms IsHalfLineEnergyMinimizer.confiningSourceEnergy_legendre_intercept
#print axioms riemannHypothesis_thermodynamic_equivalences
#print axioms offLine_arithmetic_hawking_page_transition
#print axioms hawking_page_threshold_and_polar_comparison
#print axioms universal_confining_saddle_rigidity_and_stability

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
