import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConfinedFormCountsTheZerosRightOfTheLine
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheNullVectorsOfTheConfinedForm
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalHalfLineGroundEnergyDerivative
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineGroundStateRigidity
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.WeilPaperPacketRealification

/-!
# The second critical state

Off RH the confined form `Q_R = B + a(R) W₈` acquires a second null vector at a ratio beyond the
threshold. A **negative plane** at ratio `R` is a pair of profiles on whose span `Q_R` is negative
definite (`IsNegativePlane`).

* **Monotone and left-open** (`IsNegativePlane.mono_ratio`, `IsNegativePlane.exists_left_nhds`).
  `Q_R` decreases in `R`; on a fixed plane negative definiteness is `A < 0 ∧ AC − B² > 0` for the
  `2 × 2` Gram matrix, whose entries are affine in `a(R)`.
* **Present at large ratios** (`exists_negativePlane_of_criticalState`). The confined Gram matrix of
  half-line tests has two negative squares at large `R` (the index law); its entries are real, so some
  real combination is negative and orthogonal to the ground minimizer `F₁`, and with `F₁` it spans a
  negative plane.
* **The orthogonal energy is attained** (`exists_orthEnergy_minimizer`): minimizing sequences of
  unit profiles orthogonal to `F₁` have strongly convergent window approximations; orthogonality
  passes to the limit.
* **The second critical state** (`riemannHypothesis_or_secondCriticalState`). Let `R₂` be the infimum
  of the ratios carrying a negative plane. Then `W₀ < R₂`, no ratio `R ≤ R₂` carries a negative plane,
  every ratio `R > R₂` does, and `Q_{R₂}` has a unit null vector orthogonal to the ground minimizer.
  The null equation comes from `Q(X) ≥ μ₁ ⟨F₁, X⟩²` (no negative plane, ground energy `μ₁ ≤ 0`).
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23 Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  HTGeometry HeckeKreinToeplitz

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### Two-dimensional algebra -/

/-- A real binary quadratic form is negative definite iff `A < 0` and `AC − B² > 0`. -/
theorem binary_neg_iff {A B C : ℝ} :
    (∀ s t : ℝ, (s, t) ≠ (0, 0) → s ^ 2 * A + 2 * s * t * B + t ^ 2 * C < 0) ↔
      A < 0 ∧ 0 < A * C - B ^ 2 := by
  constructor
  · intro h
    have hA : A < 0 := by simpa using h 1 0 (by simp)
    refine ⟨hA, ?_⟩
    have h2 := h (-B) A (by simp [hA.ne])
    nlinarith
  · rintro ⟨hA, hD⟩ s t hst
    have key : A * (s ^ 2 * A + 2 * s * t * B + t ^ 2 * C) = (A * s + B * t) ^ 2 + (A * C - B ^ 2) * t ^ 2 := by
      ring
    have hpos : 0 < (A * s + B * t) ^ 2 + (A * C - B ^ 2) * t ^ 2 := by
      by_cases ht : t = 0
      · have hs : s ≠ 0 := by rintro rfl; exact hst (by simp [ht])
        subst ht
        have : 0 < (A * s) ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero hA.ne hs)))
        simpa using this
      · have : 0 < (A * C - B ^ 2) * t ^ 2 := mul_pos hD (by positivity)
        nlinarith [sq_nonneg (A * s + B * t)]
    nlinarith

/-- The confined energy of a combination is the binary form of the `2 × 2` Gram matrix. -/
theorem criticalHalfLineFullEnergy_combination (R : ℝ) {G₁ G₂ : ℝ → ℝ}
    (h₁ : CriticalHalfLineEnergyDomain G₁) (h₂ : CriticalHalfLineEnergyDomain G₂) (s t : ℝ) :
    criticalHalfLineFullEnergy R (fun u => s * G₁ u + t * G₂ u) =
      s ^ 2 * criticalHalfLineFullEnergy R G₁ + 2 * s * t * criticalHalfLineMixedEnergy R G₁ G₂ +
        t ^ 2 * criticalHalfLineFullEnergy R G₂ := by
  by_cases hs : s = 0
  · subst hs
    have : (fun u => (0 : ℝ) * G₁ u + t * G₂ u) = fun u => t * G₂ u := by funext u; ring
    rw [this, criticalHalfLineFullEnergy_const_mul]
    ring
  · have hfun : (fun u => s * G₁ u + t * G₂ u) = fun u => s * (G₁ u + t / s * G₂ u) := by
      funext u; field_simp
    rw [hfun, criticalHalfLineFullEnergy_const_mul, criticalHalfLineFullEnergy_add_const_mul R h₁ h₂]
    field_simp

/-! ### Negative planes -/

/-- A plane of the energy domain on which the confined form at ratio `R` is negative definite. -/
def IsNegativePlane (R : ℝ) (G₁ G₂ : ℝ → ℝ) : Prop :=
  CriticalHalfLineEnergyDomain G₁ ∧ CriticalHalfLineEnergyDomain G₂ ∧
    ∀ s t : ℝ, (s, t) ≠ (0, 0) → criticalHalfLineFullEnergy R (fun u => s * G₁ u + t * G₂ u) < 0

theorem IsNegativePlane.iff_gram {R : ℝ} {G₁ G₂ : ℝ → ℝ} (h₁ : CriticalHalfLineEnergyDomain G₁)
    (h₂ : CriticalHalfLineEnergyDomain G₂) :
    IsNegativePlane R G₁ G₂ ↔ criticalHalfLineFullEnergy R G₁ < 0 ∧
      0 < criticalHalfLineFullEnergy R G₁ * criticalHalfLineFullEnergy R G₂ -
        criticalHalfLineMixedEnergy R G₁ G₂ ^ 2 := by
  unfold IsNegativePlane
  simp only [criticalHalfLineFullEnergy_combination R h₁ h₂, h₁, h₂, true_and]
  exact binary_neg_iff

/-- Raising the ratio keeps a negative plane: the confinement only decreases. -/
theorem IsNegativePlane.mono_ratio {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) {G₁ G₂ : ℝ → ℝ}
    (h : IsNegativePlane R G₁ G₂) : IsNegativePlane S G₁ G₂ := by
  refine ⟨h.1, h.2.1, fun s t hst => ?_⟩
  have hd := (h.1.const_mul s).add_const_mul h.2.1 t
  rw [criticalHalfLineFullEnergy_change_ratio S R hd]
  have ha := criticalAliasCoefficient_antitone hR hRS
  have hw : 0 ≤ ∫ u, (s * G₁ u + t * G₂ u) ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  nlinarith [h.2.2 s t hst]

/-- **Negative planes persist below their ratio**: the Gram entries are continuous in the ratio. -/
theorem IsNegativePlane.exists_left_nhds {R : ℝ} (hR : 0 < R) {G₁ G₂ : ℝ → ℝ}
    (h : IsNegativePlane R G₁ G₂) : ∃ ε : ℝ, 0 < ε ∧ ∀ S : ℝ, R - ε < S → IsNegativePlane S G₁ G₂ := by
  have h₁ := h.1
  have h₂ := h.2.1
  have hg := (IsNegativePlane.iff_gram (R := R) h₁ h₂).1 h
  have hacont : ContinuousAt criticalAliasCoefficient R := by
    have : criticalAliasCoefficient = fun S => criticalAliasCoefficient 1 / S :=
      funext fun S => criticalAliasCoefficient_eq_div S
    rw [this]
    exact continuousAt_const.div continuousAt_id hR.ne'
  -- the three Gram entries as continuous functions of the ratio
  have hE : ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
      Tendsto (fun S => criticalHalfLineFullEnergy S G) (𝓝 R) (𝓝 (criticalHalfLineFullEnergy R G)) := by
    intro G hG
    have h := ((hacont.tendsto.sub_const (criticalAliasCoefficient R)).mul_const
      (∫ u, G u ^ 2 * Real.exp (-(8 * u)))).const_add (criticalHalfLineFullEnergy R G)
    simp only [sub_self, zero_mul, add_zero] at h
    exact h.congr fun S => (criticalHalfLineFullEnergy_change_ratio S R hG).symm
  have hM : Tendsto (fun S => criticalHalfLineMixedEnergy S G₁ G₂) (𝓝 R)
      (𝓝 (criticalHalfLineMixedEnergy R G₁ G₂)) := by
    have h := ((hacont.tendsto.sub_const (criticalAliasCoefficient R)).mul_const
      (criticalHalfLineExponentialPair G₁ G₂)).const_add (criticalHalfLineMixedEnergy R G₁ G₂)
    simp only [sub_self, zero_mul, add_zero] at h
    exact h.congr fun S => (criticalHalfLineMixedEnergy_change_ratio S R h₁ h₂).symm
  have hev1 := (hE G₁ h₁).eventually (gt_mem_nhds hg.1)
  have hdet := (((hE G₁ h₁).mul (hE G₂ h₂)).sub (hM.pow 2)).eventually (lt_mem_nhds hg.2)
  have hev := (hev1.and hdet).and (lt_mem_nhds hR)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun S hS => ?_⟩
  by_cases hSR : S ≤ R
  · have hdist : dist S R < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    obtain ⟨⟨hA, hD⟩, hS0⟩ := hball hdist
    exact (IsNegativePlane.iff_gram h₁ h₂).2 ⟨hA, hD⟩
  · exact IsNegativePlane.mono_ratio hR (le_of_not_ge hSR) h

/-- A sequence whose squares tend to zero tends to zero. -/
theorem tendsto_zero_of_sq_tendsto_zero {f : ℕ → ℝ} (h : Tendsto (fun n => f n ^ 2) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at h1
  exact (tendsto_zero_iff_abs_tendsto_zero f).2 h1

/-! ### The orthogonal energy -/

/-- The infimum of the confined energy over unit profiles orthogonal to `F₁`. -/
def orthEnergy (R : ℝ) (F₁ : ℝ → ℝ) : ℝ :=
  sInf {e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
    (∫ u, F₁ u * G u) = 0 ∧ criticalHalfLineFullEnergy R G = e}

theorem orthEnergy_bddBelow {R : ℝ} (hR : 0 < R) (F₁ : ℝ → ℝ) :
    BddBelow {e : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      (∫ u, F₁ u * G u) = 0 ∧ criticalHalfLineFullEnergy R G = e} :=
  ⟨criticalHalfLineGroundEnergy R, by
    rintro e ⟨G, hG, hm, -, rfl⟩
    exact criticalHalfLineGroundEnergy_le hR hG hm⟩

theorem orthEnergy_le {R : ℝ} (hR : 0 < R) {F₁ G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (hm : (∫ u, G u ^ 2) = 1) (ho : (∫ u, F₁ u * G u) = 0) :
    orthEnergy R F₁ ≤ criticalHalfLineFullEnergy R G :=
  csInf_le (orthEnergy_bddBelow hR F₁) ⟨G, hG, hm, ho, rfl⟩

/-- The inner product with a square-integrable profile is controlled by the `L²` distance. -/
theorem sq_integral_mul_sub_le {F G H : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (hH : CriticalHalfLineEnergyDomain H) :
    ((∫ u, F u * H u) - ∫ u, F u * G u) ^ 2 ≤ (∫ u, F u ^ 2) * ∫ u, (H u - G u) ^ 2 := by
  have hd : CriticalHalfLineEnergyDomain fun u => H u + (-1) * G u := hH.add_const_mul hG (-1)
  have hfun : (fun u => H u + (-1) * G u) = fun u => H u - G u := by funext u; ring
  rw [hfun] at hd
  have hi1 := integrable_mul_of_sq_integrable hF.meas.aestronglyMeasurable
    hH.meas.aestronglyMeasurable hF.sq hH.sq
  have hi2 := integrable_mul_of_sq_integrable hF.meas.aestronglyMeasurable
    hG.meas.aestronglyMeasurable hF.sq hG.sq
  rw [← integral_sub hi1 hi2]
  have hc : (fun u => F u * H u - F u * G u) = fun u => F u * (H u - G u) := by funext u; ring
  rw [hc]
  exact sq_integral_mul_le hF.meas.aestronglyMeasurable hd.meas.aestronglyMeasurable hF.sq hd.sq

/-- **The orthogonal energy is attained.** -/
theorem exists_orthEnergy_minimizer {R : ℝ} (hR : 0 < R) {F₁ : ℝ → ℝ}
    (hF₁ : CriticalHalfLineEnergyDomain F₁) (hF₁m : (∫ u, F₁ u ^ 2) = 1)
    (hne : ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      (∫ u, F₁ u * G u) = 0) :
    ∃ K : ℝ → ℝ, CriticalHalfLineEnergyDomain K ∧ (∫ u, K u ^ 2) = 1 ∧ (∫ u, F₁ u * K u) = 0 ∧
      criticalHalfLineFullEnergy R K = orthEnergy R F₁ := by
  set L : ℝ := orthEnergy R F₁
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  have hele (n : ℕ) : e n ≤ 1 := by
    dsimp only [e]
    exact div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨G₀, hG₀, hm₀, ho₀⟩ := hne
  have hnonempty : ({b : ℝ | ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      (∫ u, F₁ u * G u) = 0 ∧ criticalHalfLineFullEnergy R G = b} : Set ℝ).Nonempty :=
    ⟨_, G₀, hG₀, hm₀, ho₀, rfl⟩
  have hchoose (n : ℕ) : ∃ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G ∧ (∫ u, G u ^ 2) = 1 ∧
      (∫ u, F₁ u * G u) = 0 ∧ criticalHalfLineFullEnergy R G < L + e n := by
    obtain ⟨b, ⟨G, hG, hm, ho, rfl⟩, hb⟩ := exists_lt_of_csInf_lt hnonempty
      (show orthEnergy R F₁ < L + e n from lt_add_of_pos_right L (hepos n))
    exact ⟨G, hG, hm, ho, hb⟩
  choose G hDG hmG hoG heG using hchoose
  obtain ⟨B, hB, hgard⟩ := criticalHalfLineFullEnergy_coercive_remainder hR
  have ha := criticalAliasCoefficient_positive hR
  let M : ℝ := (|L| + 1 + B) / (criticalAliasCoefficient R / 2)
  have hM : 0 ≤ M := div_nonneg
    (add_nonneg (add_nonneg (abs_nonneg _) zero_le_one) hB) (half_pos ha).le
  have hG8 (n : ℕ) : (∫ u, G n u ^ 2 * Real.exp (-(8 * u))) ≤ M := by
    apply (le_div_iff₀ (half_pos ha)).mpr
    have h := hgard (hDG n)
    rw [hmG n, mul_one] at h
    linarith only [h, heG n, hele n, le_abs_self L]
  have hrec (n : ℕ) := exists_window_energy_recovery hR (hDG n) (hmG n).le (hepos n)
  choose A H hA hHwin hmH hdH hH8 heH using hrec
  have hDH (n : ℕ) := criticalHalfLineEnergyDomain_of_window (hHwin n)
  have hdiff (n : ℕ) : CriticalHalfLineEnergyDomain (fun u => H n u - G n u) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using (hDH n).add_const_mul (hDG n) (-1)
  have herr : Tendsto (fun n => ∫ u, (H n u - G n u) ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun u => sq_nonneg _) (fun n => (hdH n).le) helim
  have hmasslim : Tendsto (fun n => ∫ u, H n u ^ 2) atTop (𝓝 1) := by
    have h := HTGeometry.tendsto_integral_sq_add_of_tendsto_zero
      (Eventually.of_forall fun n => (hDG n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hdiff n).meas.aestronglyMeasurable)
      (Eventually.of_forall fun n => (hDG n).sq)
      (Eventually.of_forall fun n => (hdiff n).sq)
      (show Tendsto (fun n => ∫ u, G n u ^ 2) atTop (𝓝 1) by
        simpa only [hmG] using (tendsto_const_nhds (x := (1 : ℝ)))) herr
    exact h.congr fun n => integral_congr_ae (Eventually.of_forall fun u => by congr 1; ring)
  have hupper (n : ℕ) : criticalHalfLineFullEnergy R (H n) ≤ L + 2 * e n := by
    linarith only [heH n, heG n]
  -- the energies of the approximations are bounded: pass to a convergent subsequence
  set μ := criticalHalfLineGroundEnergy R
  have hlower (n : ℕ) : -|μ| ≤ criticalHalfLineFullEnergy R (H n) := by
    have h1 := criticalHalfLineGroundEnergy_mul_mass_le_all hR (hDH n)
    have h2 : (∫ u, H n u ^ 2) ≤ 1 := (hmH n).trans (hmG n).le
    have h3 : 0 ≤ ∫ u, H n u ^ 2 := integral_nonneg fun u => sq_nonneg _
    nlinarith [neg_abs_le μ, abs_nonneg μ]
  obtain ⟨L', -, φ, hφ, hφlim⟩ := tendsto_subseq_of_bounded (x := fun n => criticalHalfLineFullEnergy R (H n))
    (Metric.isBounded_Icc (-|μ|) (L + 2)) fun n => ⟨hlower n, (hupper n).trans (by linarith [hele n])⟩
  have hL' : L' ≤ L := by
    have h2 : Tendsto (fun n => L + 2 * e (φ n)) atTop (𝓝 (L + 2 * 0)) :=
      tendsto_const_nhds.add ((helim.comp hφ.tendsto_atTop).const_mul 2)
    rw [mul_zero, add_zero] at h2
    exact le_of_tendsto_of_tendsto hφlim h2 (Eventually.of_forall fun n => hupper (φ n))
  obtain ⟨K, s, hs, hDK, hmK, heK, -, hL2, -⟩ := exists_domain_limit_of_smooth_energy_limit hR
    (fun n => hDH (φ n)) (fun n => (hHwin (φ n)).contDiff) (fun n => (hHwin (φ n)).hasCompactSupport)
    (fun n => (hmH (φ n)).trans (hmG (φ n)).le) (hmasslim.comp hφ.tendsto_atTop)
    (mul_nonneg (by norm_num) hM)
    (fun n => (hH8 (φ n)).trans (mul_le_mul_of_nonneg_left (hG8 (φ n)) (by norm_num)))
    (B := L + 2) (fun n => (hupper (φ n)).trans (by linarith [hele (φ n)])) hφlim
  -- orthogonality passes to the limit
  have hoK : (∫ u, F₁ u * K u) = 0 := by
    have hv : Tendsto (fun n => ∫ u, F₁ u * H (φ (s n)) u) atTop (𝓝 (∫ u, F₁ u * K u)) := by
      have hsq : Tendsto (fun n => ((∫ u, F₁ u * H (φ (s n)) u) - ∫ u, F₁ u * K u) ^ 2) atTop (𝓝 0) := by
        refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hL2
        have := sq_integral_mul_sub_le hF₁ hDK (hDH (φ (s n)))
        rw [hF₁m, one_mul] at this
        exact this
      exact tendsto_sub_nhds_zero_iff.1 (tendsto_zero_of_sq_tendsto_zero hsq)
    have hz : Tendsto (fun n => ∫ u, F₁ u * H (φ (s n)) u) atTop (𝓝 0) := by
      have herr' := herr.comp (hφ.comp hs).tendsto_atTop
      have hsq : Tendsto (fun n => ((∫ u, F₁ u * H (φ (s n)) u) - ∫ u, F₁ u * G (φ (s n)) u) ^ 2)
          atTop (𝓝 0) := by
        refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) herr'
        have := sq_integral_mul_sub_le hF₁ (hDG (φ (s n))) (hDH (φ (s n)))
        rw [hF₁m, one_mul] at this
        exact this
      simp only [hoG, sub_zero] at hsq
      exact tendsto_zero_of_sq_tendsto_zero hsq
    exact tendsto_nhds_unique hv hz
  refine ⟨K, hDK, hmK, hoK, le_antisymm (heK.trans hL') (orthEnergy_le hR hDK hmK hoK)⟩


/-! ### The ground energy around the threshold -/

theorem criticalHalfLineGroundEnergy_antitone {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    criticalHalfLineGroundEnergy S ≤ criticalHalfLineGroundEnergy R := by
  obtain ⟨H, hH⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  have hS : 0 < S := hR.trans_le hRS
  calc criticalHalfLineGroundEnergy S ≤ criticalHalfLineFullEnergy S H :=
        criticalHalfLineGroundEnergy_le hS hH.1 hH.2.1
    _ ≤ criticalHalfLineFullEnergy R H := by
        rw [criticalHalfLineFullEnergy_change_ratio S R hH.1]
        have ha := criticalAliasCoefficient_antitone hR hRS
        have hw : 0 ≤ ∫ u, H u ^ 2 * Real.exp (-(8 * u)) :=
          integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
        nlinarith
    _ = criticalHalfLineGroundEnergy R := hH.2.2

/-- The confinement mass of the critical state is at least its square mass, `1`. -/
theorem one_le_confinementMass_of_groundState {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) : 1 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  rw [← hF.2.2.2.1]
  refine integral_mono hd.sq hd.exponential fun u => ?_
  show F u ^ 2 ≤ F u ^ 2 * Real.exp (-(8 * u))
  rcases le_or_gt 0 u with hu | hu
  · rw [hd.support u hu]; simp
  · have h1 : 1 ≤ Real.exp (-(8 * u)) := Real.one_le_exp (by linarith)
    nlinarith [sq_nonneg (F u)]

/-- Beyond the threshold the ground energy is negative. -/
theorem criticalHalfLineGroundEnergy_neg_of_lt {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {R : ℝ} (hR : W₀ < R) :
    criticalHalfLineGroundEnergy R < 0 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hR0 : 0 < R := hW.trans hR
  have h0 := criticalHalfLineFullEnergy_groundState_eq_zero hW ht hF
  have hlt : criticalAliasCoefficient R < criticalAliasCoefficient W₀ :=
    lt_of_le_of_ne (criticalAliasCoefficient_antitone hW hR.le)
      fun h => hR.ne' (criticalAliasCoefficient_injective_positive hR0 hW h)
  have h8 := one_le_confinementMass_of_groundState hF
  calc criticalHalfLineGroundEnergy R ≤ criticalHalfLineFullEnergy R F :=
        criticalHalfLineGroundEnergy_le hR0 hd hF.2.2.2.1
    _ = (criticalAliasCoefficient R - criticalAliasCoefficient W₀) *
          ∫ u, F u ^ 2 * Real.exp (-(8 * u)) := by
        rw [criticalHalfLineFullEnergy_change_ratio R W₀ hd, h0, zero_add]
    _ < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)

/-- Up to the threshold the ground energy is nonnegative. -/
theorem criticalHalfLineGroundEnergy_nonneg_of_le {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {R : ℝ} (hR : 0 < R) (hRW : R ≤ W₀) :
    0 ≤ criticalHalfLineGroundEnergy R := by
  rw [← criticalHalfLineGroundEnergy_eq_zero hW ht hF]
  exact criticalHalfLineGroundEnergy_antitone hR hRW

/-! ### The null equation at a ratio without negative planes -/

/-- **Without a negative plane through the ground minimizer**, `Q(X) ≥ μ₁ ⟨F₁, X⟩²` on the domain. -/
theorem groundEnergy_mul_sq_inner_le {R : ℝ} (hR : 0 < R) {F₁ : ℝ → ℝ}
    (hF₁ : IsHalfLineEnergyMinimizer R F₁)
    (hno : ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G → ¬ IsNegativePlane R F₁ G)
    {X : ℝ → ℝ} (hX : CriticalHalfLineEnergyDomain X) :
    criticalHalfLineGroundEnergy R * (∫ u, F₁ u * X u) ^ 2 ≤ criticalHalfLineFullEnergy R X := by
  set μ := criticalHalfLineGroundEnergy R
  set b := ∫ u, F₁ u * X u
  have hfloor := criticalHalfLineGroundEnergy_mul_mass_le_all hR hX
  have hcs : b ^ 2 ≤ ∫ u, X u ^ 2 := by
    have h := sq_integral_mul_le hF₁.1.meas.aestronglyMeasurable hX.meas.aestronglyMeasurable
      hF₁.1.sq hX.sq
    rwa [hF₁.2.1, one_mul] at h
  rcases le_or_gt 0 μ with hμ | hμ
  · nlinarith [mul_le_mul_of_nonneg_left hcs hμ]
  · have hmix : criticalHalfLineMixedEnergy R F₁ X = μ * b := hF₁.weakEquation hR hX
    have hng := hno X hX
    rw [IsNegativePlane.iff_gram hF₁.1 hX, hF₁.2.2, hmix] at hng
    have hdet : μ * criticalHalfLineFullEnergy R X - (μ * b) ^ 2 ≤ 0 := by
      by_contra h; exact hng ⟨hμ, lt_of_not_ge h⟩
    nlinarith

/-- A quadratic `2cB + c²A` that is nonnegative for every `c` has `B = 0`. -/
theorem eq_zero_of_forall_quadratic_nonneg {A B : ℝ} (hA : 0 ≤ A)
    (h : ∀ c : ℝ, 0 ≤ 2 * c * B + c ^ 2 * A) : B = 0 := by
  have hden : A + 1 ≠ 0 := by linarith only [hA]
  have he : (2 * (-B / (A + 1)) * B + (-B / (A + 1)) ^ 2 * A) * (A + 1) ^ 2 =
      -(A + 2) * B ^ 2 := by
    field_simp
    ring
  have hp := mul_nonneg (h (-B / (A + 1))) (sq_nonneg (A + 1))
  rw [he] at hp
  nlinarith only [hp, mul_nonneg hA (sq_nonneg B), sq_nonneg B]

/-- **A unit profile orthogonal to the ground minimizer with zero energy is a null vector**, when
`Q(X) ≥ μ₁ ⟨F₁, X⟩²` holds on the domain. -/
theorem isConfinedNullVector_of_orth_zero {R : ℝ} {F₁ K : ℝ → ℝ}
    (hF₁ : CriticalHalfLineEnergyDomain F₁)
    (hstar : ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X →
      criticalHalfLineGroundEnergy R * (∫ u, F₁ u * X u) ^ 2 ≤ criticalHalfLineFullEnergy R X)
    (hK : CriticalHalfLineEnergyDomain K) (hKm : (∫ u, K u ^ 2) = 1)
    (hKo : (∫ u, F₁ u * K u) = 0) (hKQ : criticalHalfLineFullEnergy R K = 0) :
    IsConfinedNullVector R K := by
  refine ⟨hK, by rw [hKm]; norm_num, fun G hG => ?_⟩
  set μ := criticalHalfLineGroundEnergy R
  set b := ∫ u, F₁ u * G u
  have hiK := integrable_mul_of_sq_integrable hF₁.meas.aestronglyMeasurable
    hK.meas.aestronglyMeasurable hF₁.sq hK.sq
  have hiG := integrable_mul_of_sq_integrable hF₁.meas.aestronglyMeasurable
    hG.meas.aestronglyMeasurable hF₁.sq hG.sq
  refine eq_zero_of_forall_quadratic_nonneg (A := criticalHalfLineFullEnergy R G - μ * b ^ 2)
    (sub_nonneg.mpr (hstar G hG)) fun c => ?_
  have h := hstar _ (hK.add_const_mul hG c)
  have hin : (∫ u, F₁ u * (K u + c * G u)) = c * b := by
    have hfun : (fun u => F₁ u * (K u + c * G u)) = fun u => F₁ u * K u + c * (F₁ u * G u) := by
      funext u; ring
    rw [hfun, integral_add hiK (hiG.const_mul c), integral_const_mul, hKo, zero_add]
  rw [hin, criticalHalfLineFullEnergy_add_const_mul R hK hG, hKQ] at h
  nlinarith

/-! ### Negative planes at large ratios -/

theorem two_le_rightZeros_encard_of_not_RH (h : ¬ RiemannHypothesis) :
    (2 : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  have hne : {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re} ≠ ∅ := fun he =>
    h (ArithmeticOrientationGeometry.riemannHypothesis_iff_no_rightZero.2 he)
  have hsec : (sectorZeros zetaZeroConfig 1).encard ≠ 0 := by
    intro h0
    apply hne
    have h2 := zeta_rightZeros_encard_eq_two_mul_sectorZeros 1
    rw [h0, mul_zero] at h2
    exact Set.encard_eq_zero.mp h2
  change (2 : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard
  rw [zeta_rightZeros_encard_eq_two_mul_sectorZeros 1]
  calc (2 : ℕ∞) = 2 * 1 := by norm_num
    _ ≤ 2 * (sectorZeros zetaZeroConfig 1).encard := by
      gcongr; exact Order.one_le_iff_ne_zero.mpr hsec

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The confined Gram matrix of real tests has real entries. -/
theorem confinedGram_im (R : ℝ) (H : ι → ℝ → ℝ) (i j : ι) : (confinedGram R H i j).im = 0 := by
  have hw : EF.weilTest (cx (H i)) (cx (H j)) = fun x => ((∫ t : ℝ, H i t * H j (t - x) : ℝ) : ℂ) := by
    funext x
    rw [_root_.RHTower.WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
    congr 1
    funext t
    simp only [cx, Complex.conj_ofReal, Complex.ofReal_mul]
  simp only [confinedGram, confinementGram, weilGram, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_mul, add_zero, hw]
  exact RHTower.WeilWorkPBAP.weilFullFunctional_ofReal_im _ _

/-- **Realification.** Two negative squares of the confined Gram matrix of half-line tests give a
real combination with negative confined energy orthogonal to any given profile. -/
theorem exists_real_negative_orthogonal {S : Finset ℝ} {H : S → ℝ → ℝ}
    (hH : ∀ s, IsHalfLineTest (H s)) {R : ℝ} (h2 : 2 ≤ hermNegIndex (confinedGram R H))
    {F₁ : ℝ → ℝ} (hF₁ : CriticalHalfLineEnergyDomain F₁) :
    ∃ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X ∧ criticalHalfLineFullEnergy R X < 0 ∧
      (∫ u, F₁ u * X u) = 0 := by
  set M := confinedGram R H
  obtain ⟨W, hWr, hWpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (-M)
  have hW2 : 1 < Module.finrank ℂ W := by
    have hneg : hermNegIndex M = hermPosIndex (-M) := rfl
    omega
  let c : S → ℝ := fun s => ∫ u, F₁ u * H s u
  -- a nonzero vector of `W` annihilated by `x ↦ Σ x_s c_s`
  have hker : ∃ v : S → ℂ, v ∈ W ∧ v ≠ 0 ∧ ∑ s, v s * (c s : ℂ) = 0 := by
    haveI : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
    obtain ⟨w₁, hw₁⟩ := exists_ne (0 : W)
    by_cases h1 : ∑ s, (w₁ : S → ℂ) s * (c s : ℂ) = 0
    · exact ⟨w₁, w₁.2, fun h => hw₁ (Subtype.ext h), h1⟩
    obtain ⟨w₂, hind⟩ := exists_linearIndependent_pair_of_one_lt_finrank hW2 hw₁
    refine ⟨((∑ s, (w₂ : S → ℂ) s * (c s : ℂ)) • w₁ - (∑ s, (w₁ : S → ℂ) s * (c s : ℂ)) • w₂ : W),
      Submodule.coe_mem _, fun h => ?_, ?_⟩
    · have hx0 : (∑ s, (w₂ : S → ℂ) s * (c s : ℂ)) • w₁ +
          (-(∑ s, (w₁ : S → ℂ) s * (c s : ℂ))) • w₂ = 0 := by
        apply Subtype.ext
        simp only [Submodule.coe_sub, Submodule.coe_smul] at h
        simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero, neg_smul,
          ← sub_eq_add_neg]
        exact h
      have := (LinearIndependent.pair_iff.1 hind) _ _ hx0
      exact h1 (neg_eq_zero.mp this.2)
    · simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hs : ∀ s : S, ((∑ s, (w₂ : S → ℂ) s * (c s : ℂ)) * (w₁ : S → ℂ) s -
          (∑ s, (w₁ : S → ℂ) s * (c s : ℂ)) * (w₂ : S → ℂ) s) * (c s : ℂ) =
          (∑ s, (w₂ : S → ℂ) s * (c s : ℂ)) * ((w₁ : S → ℂ) s * c s) -
            (∑ s, (w₁ : S → ℂ) s * (c s : ℂ)) * ((w₂ : S → ℂ) s * c s) := fun s => by ring
      rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum]
      ring
  obtain ⟨v, hvW, hv0, hφv⟩ := hker
  have hneg : hermQuad M v < 0 := by
    have h := hWpos v hvW hv0
    rw [hermQuad_neg] at h
    linarith
  rw [hermQuad_eq_re_add_im (fun i j => confinedGram_im R H i j)] at hneg
  have hre : ∑ s, (v s).re * c s = 0 := by
    have := congrArg Complex.re hφv
    simpa [Complex.re_sum, Complex.mul_re] using this
  have him : ∑ s, (v s).im * c s = 0 := by
    have := congrArg Complex.im hφv
    simpa [Complex.im_sum, Complex.mul_im] using this
  obtain ⟨A, hA⟩ := exists_common_window hH
  have hDs : ∀ s, CriticalHalfLineEnergyDomain (H s) := fun s =>
    criticalHalfLineEnergyDomain_of_window ⟨(hH s).1, hA s⟩
  have hint : ∀ s, Integrable fun u => F₁ u * H s u := fun s =>
    integrable_mul_of_sq_integrable hF₁.meas.aestronglyMeasurable
      (hDs s).meas.aestronglyMeasurable hF₁.sq (hDs s).sq
  -- the real combination of a real coefficient vector
  have hcomb : ∀ y : S → ℝ, ∑ s, y s * c s = 0 →
      hermQuad M (fun s => (y s : ℂ)) < 0 →
      ∃ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X ∧ criticalHalfLineFullEnergy R X < 0 ∧
        (∫ u, F₁ u * X u) = 0 := by
    intro y hy hq
    refine ⟨fun u => ∑ s, y s * H s u, ?_, ?_, ?_⟩
    · exact criticalHalfLineEnergyDomain_of_window (A := A)
        ⟨ContDiff.sum fun s _ => contDiff_const.mul (hH s).1,
          fun u (hu : u ∉ Icc (-A) 0) => by simp [hA _ u hu]⟩
    · rwa [← hermQuad_confinedGram_ofReal R hH y]
    · have hfun : (fun u => F₁ u * ∑ s, y s * H s u) = fun u => ∑ s, y s * (F₁ u * H s u) := by
        funext u; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [hfun, integral_finsetSum _ fun s _ => (hint s).const_mul _]
      simpa [integral_const_mul] using hy
  rcases lt_or_ge (hermQuad M fun s => ((v s).re : ℂ)) 0 with hr | hr
  · exact hcomb (fun s => (v s).re) hre hr
  · exact hcomb (fun s => (v s).im) him (by linarith)

/-- **Off RH, negative planes appear beyond the threshold.** -/
theorem exists_negativePlane_of_criticalState {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ R : ℝ, W₀ < R ∧ ∃ G₁ G₂ : ℝ → ℝ, IsNegativePlane R G₁ G₂ := by
  obtain ⟨S, H, hH, hev⟩ := exists_halfLineTests_eventually_le_hermNegIndex
    (two_le_rightZeros_encard_of_not_RH (not_riemannHypothesis_of_threshold ht))
  obtain ⟨R, hR2, hRW⟩ := (hev.and (eventually_gt_atTop W₀)).exists
  have hR : 0 < R := hW.trans hRW
  obtain ⟨F₁, hF₁⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR
  obtain ⟨X, hX, hXQ, hXo⟩ := exists_real_negative_orthogonal hH hR2 hF₁.1
  have hμ := criticalHalfLineGroundEnergy_neg_of_lt hW ht hF hRW
  refine ⟨R, hRW, F₁, X, (IsNegativePlane.iff_gram hF₁.1 hX).2 ⟨by rw [hF₁.2.2]; exact hμ, ?_⟩⟩
  rw [hF₁.2.2, hF₁.weakEquation hR hX, hXo, mul_zero]
  nlinarith

/-! ### The second critical state -/

/-- A negative plane contains a unit profile orthogonal to any given profile. -/
theorem IsNegativePlane.exists_unit_orthogonal {R : ℝ} (hR : 0 < R) {G₁ G₂ : ℝ → ℝ}
    (h : IsNegativePlane R G₁ G₂) {F₁ : ℝ → ℝ} (hF₁ : CriticalHalfLineEnergyDomain F₁) :
    ∃ Y : ℝ → ℝ, CriticalHalfLineEnergyDomain Y ∧ (∫ u, Y u ^ 2) = 1 ∧ (∫ u, F₁ u * Y u) = 0 ∧
      criticalHalfLineFullEnergy R Y < 0 := by
  obtain ⟨h₁, h₂, hneg⟩ := h
  set b₁ := ∫ u, F₁ u * G₁ u
  set b₂ := ∫ u, F₁ u * G₂ u
  have hi₁ := integrable_mul_of_sq_integrable hF₁.meas.aestronglyMeasurable
    h₁.meas.aestronglyMeasurable hF₁.sq h₁.sq
  have hi₂ := integrable_mul_of_sq_integrable hF₁.meas.aestronglyMeasurable
    h₂.meas.aestronglyMeasurable hF₁.sq h₂.sq
  -- coefficients of a combination orthogonal to `F₁`
  obtain ⟨s, t, hst, hort⟩ : ∃ s t : ℝ, (s, t) ≠ (0, 0) ∧ s * b₁ + t * b₂ = 0 := by
    by_cases hb : (b₂, -b₁) = ((0 : ℝ), (0 : ℝ))
    · simp only [Prod.mk.injEq, neg_eq_zero] at hb
      exact ⟨1, 0, by simp, by rw [hb.2]; ring⟩
    · exact ⟨b₂, -b₁, hb, by ring⟩
  set X : ℝ → ℝ := fun u => s * G₁ u + t * G₂ u
  have hX : CriticalHalfLineEnergyDomain X := (h₁.const_mul s).add_const_mul h₂ t
  have hXQ : criticalHalfLineFullEnergy R X < 0 := hneg s t hst
  have hXo : (∫ u, F₁ u * X u) = 0 := by
    have hfun : (fun u => F₁ u * X u) = fun u => s * (F₁ u * G₁ u) + t * (F₁ u * G₂ u) := by
      funext u; simp only [X]; ring
    rw [hfun, integral_add (hi₁.const_mul s) (hi₂.const_mul t), integral_const_mul,
      integral_const_mul]
    exact hort
  have hm : 0 < ∫ u, X u ^ 2 := by
    rcases (integral_nonneg (fun u => sq_nonneg (X u)) : (0 : ℝ) ≤ ∫ u, X u ^ 2).lt_or_eq with hm | hm
    · exact hm
    · have := criticalHalfLineGroundEnergy_mul_mass_le_all hR hX
      rw [← hm, mul_zero] at this
      linarith
  set k : ℝ := (Real.sqrt (∫ u, X u ^ 2))⁻¹
  have hk2 : k ^ 2 * (∫ u, X u ^ 2) = 1 := by
    simp only [k, inv_pow, Real.sq_sqrt hm.le]
    exact inv_mul_cancel₀ hm.ne'
  refine ⟨fun u => k * X u, hX.const_mul k, ?_, ?_, ?_⟩
  · simp_rw [mul_pow]; rw [integral_const_mul, hk2]
  · have hfun : (fun u => F₁ u * (k * X u)) = fun u => k * (F₁ u * X u) := by funext u; ring
    rw [hfun, integral_const_mul, hXo, mul_zero]
  · rw [criticalHalfLineFullEnergy_const_mul]
    exact mul_neg_of_pos_of_neg (by positivity) hXQ

/-- **The second critical state.** Off RH (given the critical state at `W₀`) there is a ratio
`R₂ > W₀` such that no ratio `R ≤ R₂` carries a negative plane, every ratio `R > R₂` does, and the
confined form at `R₂` has a unit null vector. -/
theorem criticalState_secondCriticalState {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal)) {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ R₂ : ℝ, W₀ < R₂ ∧
      (∀ R : ℝ, 0 < R → R ≤ R₂ → ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R G₁ G₂) ∧
      (∀ R : ℝ, R₂ < R → ∃ G₁ G₂ : ℝ → ℝ, IsNegativePlane R G₁ G₂) ∧
      ∃ K : ℝ → ℝ, IsConfinedNullVector R₂ K ∧ (∫ u, K u ^ 2) = 1 := by
  set A : Set ℝ := {R | 0 < R ∧ ∃ G₁ G₂ : ℝ → ℝ, IsNegativePlane R G₁ G₂}
  -- below the threshold the confined form is nonnegative, so no negative plane
  have hlow : ∀ R ∈ A, W₀ < R := by
    rintro R ⟨hR, G₁, G₂, h⟩
    by_contra hle
    have hμ := criticalHalfLineGroundEnergy_nonneg_of_le hW ht hF hR (le_of_not_gt hle)
    have h1 := h.2.2 1 0 (by simp)
    have hfun : (fun u => (1 : ℝ) * G₁ u + 0 * G₂ u) = G₁ := by funext u; ring
    rw [hfun] at h1
    have := criticalHalfLineGroundEnergy_mul_mass_le_all hR h.1
    nlinarith [(integral_nonneg (fun u => sq_nonneg (G₁ u)) : (0 : ℝ) ≤ ∫ u, G₁ u ^ 2)]
  obtain ⟨R₀, hR₀, G₁, G₂, hG⟩ := exists_negativePlane_of_criticalState hW ht hF
  have hAne : A.Nonempty := ⟨R₀, hW.trans hR₀, G₁, G₂, hG⟩
  have hAbdd : BddBelow A := ⟨W₀, fun R hR => (hlow R hR).le⟩
  set R₂ := sInf A
  have hR₂W : W₀ ≤ R₂ := le_csInf hAne fun R hR => (hlow R hR).le
  have hR₂ : 0 < R₂ := hW.trans_le hR₂W
  -- above `R₂` every ratio carries a negative plane
  have habove : ∀ R : ℝ, R₂ < R → ∃ G₁ G₂ : ℝ → ℝ, IsNegativePlane R G₁ G₂ := by
    intro R hR
    obtain ⟨R', ⟨hR'0, H₁, H₂, hH⟩, hR'⟩ := exists_lt_of_csInf_lt hAne hR
    exact ⟨H₁, H₂, hH.mono_ratio hR'0 hR'.le⟩
  -- `R₂` itself carries none: negative planes persist to the left
  have hnot : ∀ R : ℝ, 0 < R → R ≤ R₂ → ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R G₁ G₂ := by
    intro R hR hRR G₁ G₂ h
    obtain ⟨ε, hε, hleft⟩ := h.exists_left_nhds hR
    set S := R - min ε R / 2
    have hS0 : 0 < S := by simp only [S]; linarith [min_le_right ε R, (lt_min hε hR)]
    have hSlt : S < R := by simp only [S]; linarith [lt_min hε hR]
    have hSA : S ∈ A := ⟨hS0, G₁, G₂, hleft S (by simp only [S]; linarith [min_le_left ε R])⟩
    exact absurd (csInf_le hAbdd hSA) (not_le.mpr (hSlt.trans_le hRR))
  obtain ⟨F₁, hF₁⟩ := exists_criticalHalfLineGroundEnergy_minimizer hR₂
  have hstar := fun X hX => groundEnergy_mul_sq_inner_le hR₂ hF₁
    (fun G hG => hnot R₂ hR₂ le_rfl F₁ G) (X := X) hX
  -- unit profiles orthogonal to `F₁` with almost nonpositive energy
  obtain ⟨Bc, hBc, hgard⟩ := criticalHalfLineFullEnergy_coercive_remainder (show 0 < R₂ + 1 by linarith)
  have ha1 := criticalAliasCoefficient_positive (show 0 < R₂ + 1 by linarith)
  set Mb : ℝ := Bc / (criticalAliasCoefficient (R₂ + 1) / 2)
  have happrox : ∀ n : ℕ, ∃ Y : ℝ → ℝ, CriticalHalfLineEnergyDomain Y ∧ (∫ u, Y u ^ 2) = 1 ∧
      (∫ u, F₁ u * Y u) = 0 ∧ criticalHalfLineFullEnergy R₂ Y ≤
        (criticalAliasCoefficient R₂ - criticalAliasCoefficient (R₂ + 1 / ((n : ℝ) + 1))) * Mb := by
    intro n
    set Rn := R₂ + 1 / ((n : ℝ) + 1)
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hle1 : 1 / ((n : ℝ) + 1) ≤ 1 :=
      div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
    have hRn : R₂ < Rn := by simp only [Rn]; linarith
    obtain ⟨H₁, H₂, hH⟩ := habove Rn hRn
    obtain ⟨Y, hY, hYm, hYo, hYQ⟩ := hH.exists_unit_orthogonal (hR₂.trans hRn) hF₁.1
    refine ⟨Y, hY, hYm, hYo, ?_⟩
    have hW8 : (∫ u, Y u ^ 2 * Real.exp (-(8 * u))) ≤ Mb := by
      apply (le_div_iff₀ (half_pos ha1)).mpr
      have h := hgard hY
      rw [hYm, mul_one] at h
      have hmono : criticalHalfLineFullEnergy (R₂ + 1) Y ≤ criticalHalfLineFullEnergy Rn Y := by
        rw [criticalHalfLineFullEnergy_change_ratio (R₂ + 1) Rn hY]
        have ha := criticalAliasCoefficient_antitone (hR₂.trans hRn) (show Rn ≤ R₂ + 1 by simp only [Rn]; linarith)
        have hw : 0 ≤ ∫ u, Y u ^ 2 * Real.exp (-(8 * u)) :=
          integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
        nlinarith
      linarith
    rw [criticalHalfLineFullEnergy_change_ratio R₂ Rn hY]
    have ha := criticalAliasCoefficient_antitone hR₂ hRn.le
    nlinarith [mul_le_mul_of_nonneg_left hW8 (sub_nonneg.mpr ha)]
  obtain ⟨Y₀, hY₀, hY₀m, hY₀o, -⟩ := happrox 0
  -- the orthogonal energy at `R₂` vanishes
  have horth_ge : 0 ≤ orthEnergy R₂ F₁ := by
    refine le_csInf ⟨_, Y₀, hY₀, hY₀m, hY₀o, rfl⟩ ?_
    rintro e ⟨G, hG, -, hGo, rfl⟩
    have := hstar G hG
    rwa [hGo, sq, mul_zero, mul_zero] at this
  have horth_le : orthEnergy R₂ F₁ ≤ 0 := by
    have hacont : ContinuousAt criticalAliasCoefficient R₂ := by
      have : criticalAliasCoefficient = fun S => criticalAliasCoefficient 1 / S :=
        funext fun S => criticalAliasCoefficient_eq_div S
      rw [this]
      exact continuousAt_const.div continuousAt_id hR₂.ne'
    have hseq : Tendsto (fun n : ℕ => R₂ + 1 / ((n : ℝ) + 1)) atTop (𝓝 R₂) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add R₂
    have hlim : Tendsto (fun n : ℕ => (criticalAliasCoefficient R₂ -
        criticalAliasCoefficient (R₂ + 1 / ((n : ℝ) + 1))) * Mb) atTop (𝓝 0) := by
      have h := ((tendsto_const_nhds (x := criticalAliasCoefficient R₂)).sub
        (hacont.tendsto.comp hseq)).mul_const Mb
      simpa using h
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    obtain ⟨Y, hY, hYm, hYo, hYQ⟩ := happrox n
    exact (orthEnergy_le hR₂ hY hYm hYo).trans hYQ
  obtain ⟨K, hK, hKm, hKo, hKQ⟩ := exists_orthEnergy_minimizer hR₂ hF₁.1 hF₁.2.1 ⟨Y₀, hY₀, hY₀m, hY₀o⟩
  have hKQ0 : criticalHalfLineFullEnergy R₂ K = 0 := by rw [hKQ]; linarith
  have hnull := isConfinedNullVector_of_orth_zero hF₁.1 hstar hK hKm hKo hKQ0
  -- `R₂ ≠ W₀`: at `W₀` a zero-energy unit profile is a minimizer, hence `±F₁`
  have hR₂ne : R₂ ≠ W₀ := by
    intro hEq
    have hmin : IsHalfLineEnergyMinimizer R₂ K := by
      refine ⟨hK, hKm, ?_⟩
      rw [hKQ0, hEq, criticalHalfLineGroundEnergy_eq_zero hW ht hF]
    rcases halfLineEnergyMinimizer_unique_up_to_sign hR₂ hmin hF₁ with he | he
    · have : (∫ u, F₁ u * K u) = ∫ u, K u ^ 2 :=
        integral_congr_ae (he.mono fun u hu => by
          show F₁ u * K u = K u ^ 2
          rw [← hu]; ring)
      rw [hKo, hKm] at this
      norm_num at this
    · have : (∫ u, F₁ u * K u) = -∫ u, K u ^ 2 := by
        rw [← integral_neg]
        exact integral_congr_ae (he.mono fun u hu => by
          show F₁ u * K u = -(K u ^ 2)
          have hF : F₁ u = -K u := by have := hu; simp only at this; linarith
          rw [hF]; ring)
      rw [hKo, hKm] at this
      norm_num at this
  exact ⟨R₂, lt_of_le_of_ne hR₂W (Ne.symm hR₂ne), hnot, habove, K, hnull, hKm⟩

/-- **RH or a second critical state.** Either RH holds, or beyond the threshold `W₀` of the critical
state there is a second critical ratio `R₂`, where the confined form first carries a negative plane,
with a unit null vector orthogonal to the critical state. -/
theorem riemannHypothesis_or_secondCriticalState :
    RiemannHypothesis ∨ ∃ (W₀ R₂ : ℝ) (F K : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ W₀ < R₂ ∧ IsConfinedNullVector R₂ K ∧
      (∫ u, K u ^ 2) = 1 ∧ (∫ u, F u * K u * Real.exp (-(8 * u))) = 0 ∧
      (∀ R : ℝ, 0 < R → R ≤ R₂ → ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R G₁ G₂) ∧
      (∀ R : ℝ, R₂ < R → ∃ G₁ G₂ : ℝ → ℝ, IsNegativePlane R G₁ G₂) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl h
  · obtain ⟨R₂, hR₂, hnot, habove, K, hK, hKm⟩ := criticalState_secondCriticalState hW ht hF
    have horth := (confinedNullVectors_orthogonal hW (hW.trans hR₂) hR₂.ne
      (isConfinedNullVector_of_groundState hW ht hF) hK).1
    have hd := criticalHalfLineEnergyDomain_of_groundState hF
    have hfull : (∫ u, F u * K u * Real.exp (-(8 * u))) = 0 := by
      rw [← horth]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
        rw [hd.support u (not_lt.mp hu)]; ring).symm
    exact Or.inr ⟨W₀, R₂, F, K, hW, ht, hF, hR₂, hK, hKm, hfull, hnot, habove⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
