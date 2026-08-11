import Mathlib
import GaloisForLFunctions.RHTower.SalemFermiModeIntegral

/-!
# Hasse packet formation mechanics

This module formalizes the mechanism from the universal-law-field packet-formation card.

* finite Hasse rows form an alternating cancellation packet;
* a parameter-independent geometric kernel reconstructs packet depth from Mellin scale;
* the joint packet atom factors exactly through the Salem Fermi marginal;
* absolute atomic refinement is summable exactly for `σ > 1`;
* equality of reflected normalized Fermi densities forces the critical center.

The atomic wall is the decisive formation law: packet formation remains admitted in the critical
strip, while coefficientwise refinement does not.
-/

open Real Filter
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Parameter-independent geometric success ratio in the Hasse depth kernel. -/
def hassePacketRatio (t : ℝ) : ℝ := (1 - Real.exp (-t)) / 2

/-- Conditional depth kernel recovered from the continuous Mellin scale. -/
def hassePacketRecovery (t : ℝ) (n : ℕ) : ℝ :=
  (1 - hassePacketRatio t) * hassePacketRatio t ^ n

/-- Scale marginal of the joint packet formation. -/
def hassePacketScale (t : ℝ) : ℝ :=
  Real.exp (-t) / (1 + Real.exp (-t))

/-- Unnormalized joint Hasse depth-scale atom. -/
def hassePacketJointAtom (t : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1) * Real.exp (-t) * (1 - Real.exp (-t)) ^ n

theorem hassePacketScale_eq_fermiKernel (t : ℝ) :
    hassePacketScale t = (Real.exp t + 1)⁻¹ := by
  unfold hassePacketScale
  rw [Real.exp_neg]
  have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
  field_simp

/-- The packet scale is literally the already certified Salem Fermi kernel. -/
theorem coe_hassePacketScale_eq_salemFermiKernel (t : ℝ) :
    ((hassePacketScale t : ℝ) : ℂ) = RHTower.salemFermiKernel t := by
  rw [hassePacketScale_eq_fermiKernel, RHTower.salemFermiKernel_eq]
  push_cast
  rfl

theorem hassePacketRatio_mem_Ioo {t : ℝ} (ht : 0 < t) :
    hassePacketRatio t ∈ Set.Ioo 0 1 := by
  have hq0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  constructor <;> unfold hassePacketRatio <;> linarith

/-- The common recovery kernel is a probability mass function for every positive scale. -/
theorem hasSum_hassePacketRecovery {t : ℝ} (ht : 0 < t) :
    HasSum (hassePacketRecovery t) 1 := by
  have hr := hassePacketRatio_mem_Ioo ht
  have hnorm : ‖hassePacketRatio t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr.1]
    exact hr.2
  have h :=
    (hasSum_geometric_of_norm_lt_one hnorm).mul_left (1 - hassePacketRatio t)
  have h' : HasSum (hassePacketRecovery t)
      ((1 - hassePacketRatio t) * (1 - hassePacketRatio t)⁻¹) :=
    h.congr_fun fun _ => rfl
  rw [mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hr.2))] at h'
  exact h'

/-- Exact reconstruction factorization: joint packet = Fermi scale × common depth kernel. -/
theorem hassePacketJointAtom_factor (t : ℝ) (n : ℕ) :
    hassePacketJointAtom t n = hassePacketScale t * hassePacketRecovery t n := by
  let q := Real.exp (-t)
  change (1 / 2 : ℝ) ^ (n + 1) * q * (1 - q) ^ n =
    (q / (1 + q)) * ((1 - (1 - q) / 2) * ((1 - q) / 2) ^ n)
  have hq : 1 + q ≠ 0 := by dsimp [q]; positivity
  rw [show 1 - (1 - q) / 2 = (1 + q) / 2 by ring]
  rw [pow_succ']
  rw [show ((1 - q) / 2) ^ n = (1 - q) ^ n / 2 ^ n by rw [div_pow]]
  field_simp [hq]
  have hhalf : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (1 / 2 : ℝ) ^ n * q * (1 - q) ^ n * 2 ^ n =
        q * (1 - q) ^ n * ((1 / 2 : ℝ) ^ n * 2 ^ n) := by ring
    _ = q * (1 - q) ^ n := by rw [hhalf, mul_one]

/-- Summing latent depths exactly reconstructs the Salem Fermi scale. -/
theorem hasSum_hassePacketJointAtom {t : ℝ} (ht : 0 < t) :
    HasSum (hassePacketJointAtom t) (hassePacketScale t) := by
  have h := (hasSum_hassePacketRecovery ht).mul_left (hassePacketScale t)
  have h' : HasSum (fun n => hassePacketScale t * hassePacketRecovery t n)
      (hassePacketScale t) := by
    simpa using h
  exact h'.congr_fun fun n => hassePacketJointAtom_factor t n

/-- A finite Hasse row forms its cancellation packet before any infinite refinement. -/
theorem hasseFiniteDifference_packet (q : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k * (n.choose k : ℝ) * q ^ k) = (1 - q) ^ n := by
  have h := (Commute.all (-q) (1 : ℝ)).add_pow n
  rw [neg_add_eq_sub] at h
  calc
    (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * (n.choose k : ℝ) * q ^ k) =
        ∑ k ∈ Finset.range (n + 1),
          (-q) ^ k * 1 ^ (n - k) * (n.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [neg_pow, one_pow]
      ring
    _ = (1 - q) ^ n := h.symm

/-- Absolute atom in column `k` and excess-depth coordinate `m`. -/
def hasseAtomicMass (σ : ℝ) (k m : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ σ)) *
    (((m + k).choose k : ℝ) * (1 / 2 : ℝ) ^ m)

theorem hasseAtomicMass_nonneg (σ : ℝ) (k m : ℕ) :
    0 ≤ hasseAtomicMass σ k m := by
  unfold hasseAtomicMass
  positivity

/-- Every fixed atomic column has exactly its `p`-series mass. -/
theorem hasSum_hasseAtomicMass_fixedColumn (σ : ℝ) (k : ℕ) :
    HasSum (fun m => hasseAtomicMass σ k m)
      (1 / (((k + 1 : ℕ) : ℝ) ^ σ)) := by
  have hnorm : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num [Real.norm_eq_abs]
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k hnorm
  have hscaled := h.mul_left ((1 / 2 : ℝ) ^ (k + 1) /
    (((k + 1 : ℕ) : ℝ) ^ σ))
  have hk : (((k + 1 : ℕ) : ℝ) ^ σ) ≠ 0 := by positivity
  have hvalue :
      (1 / 2 : ℝ) ^ (k + 1) / (((k + 1 : ℕ) : ℝ) ^ σ) *
        (1 / (1 - (1 / 2 : ℝ)) ^ (k + 1)) =
      1 / (((k + 1 : ℕ) : ℝ) ^ σ) := by
    rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
    field_simp [hk]
  rw [hvalue] at hscaled
  simpa only [hasseAtomicMass] using hscaled

/-- Exact atomic-refinement classification.  The double absolute packet is summable precisely
beyond the line `σ = 1`. -/
theorem summable_hasseAtomicMass_iff (σ : ℝ) :
    Summable (fun z : ℕ × ℕ => hasseAtomicMass σ z.1 z.2) ↔ 1 < σ := by
  rw [summable_prod_of_nonneg (fun z => hasseAtomicMass_nonneg σ z.1 z.2)]
  have hcol : ∀ k, Summable (fun m => hasseAtomicMass σ k m) :=
    fun k => (hasSum_hasseAtomicMass_fixedColumn σ k).summable
  have htsum : (fun k => ∑' m, hasseAtomicMass σ k m) =
      fun k => 1 / (((k + 1 : ℕ) : ℝ) ^ σ) := by
    funext k
    exact (hasSum_hasseAtomicMass_fixedColumn σ k).tsum_eq
  rw [htsum]
  have heq : (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) ^ σ)) =
      fun k : ℕ => 1 / |(k : ℝ) + 1| ^ σ := by
    funext k
    rw [abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    norm_num
  constructor
  · rintro ⟨_, houter⟩
    rw [heq] at houter
    exact (Real.summable_one_div_nat_add_rpow 1 σ).mp houter
  · intro hσ
    refine ⟨hcol, ?_⟩
    rw [heq]
    exact (Real.summable_one_div_nat_add_rpow 1 σ).mpr hσ

/-- In the critical strip, formed packets are admitted while absolute atomic refinement is not. -/
theorem packet_formation_atomic_refinement_wall
    {σ : ℝ} (_hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (∀ t : ℝ, 0 < t → Summable (hassePacketRecovery t)) ∧
      ¬Summable (fun z : ℕ × ℕ => hasseAtomicMass σ z.1 z.2) := by
  constructor
  · intro t ht
    exact (hasSum_hassePacketRecovery ht).summable
  · rw [summable_hasseAtomicMass_iff]
    linarith

/-- Normalized positive Fermi formation density with normalization constant `Z`. -/
def fermiFormationDensity (σ Z t : ℝ) : ℝ :=
  t ^ (σ - 1) / (Z * (Real.exp t + 1))

/-- Normalization cannot make two distinct Mellin exponents define the same positive density. -/
theorem fermiFormationDensity_injective
    {a b Za Zb : ℝ} (hZa : 0 < Za) (hZb : 0 < Zb)
    (h : ∀ t : ℝ, 0 < t → fermiFormationDensity a Za t =
      fermiFormationDensity b Zb t) : a = b := by
  have h1 := h 1 zero_lt_one
  have hZ : Za = Zb := by
    simp only [fermiFormationDensity, Real.one_rpow, one_div] at h1
    have he : Real.exp 1 + 1 ≠ 0 := by positivity
    field_simp [hZa.ne', hZb.ne', he] at h1
    exact h1.symm
  have h2 := h 2 (by norm_num)
  rw [hZ] at h2
  have hden : Zb * (Real.exp 2 + 1) ≠ 0 := by positivity
  unfold fermiFormationDensity at h2
  field_simp [hden] at h2
  have hab : a - 1 = b - 1 :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective h2
  linarith

/-- Reflected Fermi laws can coincide only at the critical center. -/
theorem reflected_fermiFormationDensity_eq_iff
    {σ Zσ Zr : ℝ} (_hσ0 : 0 < σ) (_hσ1 : σ < 1)
    (hZσ : 0 < Zσ) (hZr : 0 < Zr)
    (h : ∀ t : ℝ, 0 < t → fermiFormationDensity σ Zσ t =
      fermiFormationDensity (1 - σ) Zr t) : σ = 1 / 2 := by
  have hs := fermiFormationDensity_injective hZσ hZr h
  linarith

/-! ## Measure-level information properness -/

open MeasureTheory InformationTheory Set

/-- Extended nonnegative density used to form the positive Fermi measure on `(0,∞)`. -/
def fermiFormationEDensity (σ Z t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (fermiFormationDensity σ Z t)

/-- Positive Fermi formation measure.  When `Z` is its Mellin normalizer this is a probability
measure; injectivity below does not require normalization. -/
def fermiFormationMeasure (σ Z : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity (fermiFormationEDensity σ Z)

theorem continuousOn_fermiFormationDensity (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    ContinuousOn (fermiFormationDensity σ Z) (Set.Ioi 0) := by
  have hpow : ContinuousOn (fun t : ℝ => t ^ (σ - 1)) (Set.Ioi 0) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)
  have hden : Continuous (fun t : ℝ => Z * (Real.exp t + 1)) := by fun_prop
  exact hpow.div hden.continuousOn fun t ht => by positivity

theorem continuousOn_fermiFormationEDensity (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    ContinuousOn (fermiFormationEDensity σ Z) (Set.Ioi 0) := by
  exact ENNReal.continuous_ofReal.comp_continuousOn
    (continuousOn_fermiFormationDensity σ hZ)

theorem aemeasurable_fermiFormationEDensity (σ : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    AEMeasurable (fermiFormationEDensity σ Z) (volume.restrict (Set.Ioi 0)) := by
  exact (continuousOn_fermiFormationEDensity σ hZ).aemeasurable measurableSet_Ioi

/-- Equality of positive Fermi measures recovers the Mellin exponent. -/
theorem fermiFormationMeasure_eq_imp_parameter_eq
    {a b Za Zb : ℝ} (hZa : 0 < Za) (hZb : 0 < Zb)
    (h : fermiFormationMeasure a Za = fermiFormationMeasure b Zb) : a = b := by
  have hae : fermiFormationEDensity a Za =ᵐ[volume.restrict (Set.Ioi 0)]
      fermiFormationEDensity b Zb :=
    (withDensity_eq_iff_of_sigmaFinite
      (aemeasurable_fermiFormationEDensity a hZa)
      (aemeasurable_fermiFormationEDensity b hZb)).mp h
  have heq : Set.EqOn (fermiFormationEDensity a Za)
      (fermiFormationEDensity b Zb) (Set.Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      (continuousOn_fermiFormationEDensity a hZa)
      (continuousOn_fermiFormationEDensity b hZb)
  apply fermiFormationDensity_injective hZa hZb
  intro t ht
  have het := heq ht
  have ha : 0 ≤ fermiFormationDensity a Za t := by
    unfold fermiFormationDensity
    positivity
  have hb : 0 ≤ fermiFormationDensity b Zb t := by
    unfold fermiFormationDensity
    positivity
  exact (ENNReal.ofReal_eq_ofReal_iff ha hb).mp het

/-- Symmetric information work between two positive Fermi formations. -/
def fermiFormationJeffreys (a b Za Zb : ℝ) : ℝ≥0∞ :=
  klDiv (fermiFormationMeasure a Za) (fermiFormationMeasure b Zb) +
    klDiv (fermiFormationMeasure b Zb) (fermiFormationMeasure a Za)

/-- Positive Fermi formation is finite throughout `σ > 0`. -/
theorem finite_fermiFormationMeasure
    {σ Z : ℝ} (hσ : 0 < σ) (hZ : 0 < Z) :
    IsFiniteMeasure (fermiFormationMeasure σ Z) := by
  have hgamma : IntegrableOn
      (fun t : ℝ => t ^ (σ - 1) * Real.exp (-t ^ (1 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_rpow (by linarith) (by norm_num)
  have hmajor : IntegrableOn
      (fun t : ℝ => (1 / Z) * (t ^ (σ - 1) * Real.exp (-t))) (Set.Ioi 0) := by
    change Integrable (fun t : ℝ => (1 / Z) * (t ^ (σ - 1) * Real.exp (-t)))
      (volume.restrict (Set.Ioi 0))
    simpa using hgamma.const_mul (1 / Z)
  have hfint : IntegrableOn (fermiFormationDensity σ Z) (Set.Ioi 0) := by
    apply hmajor.mono'
    · exact (continuousOn_fermiFormationDensity σ hZ).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      have hpow : 0 < t ^ (σ - 1) := Real.rpow_pos_of_pos ht0 _
      have hk := RHTower.norm_salemFermiKernel_le_exp_neg t
      rw [RHTower.norm_salemFermiKernel] at hk
      have hfpos : 0 < fermiFormationDensity σ Z t := by
        unfold fermiFormationDensity
        positivity
      rw [Real.norm_eq_abs, abs_of_pos hfpos]
      have hnonneg : 0 ≤ t ^ (σ - 1) := hpow.le
      have hdiv : t ^ (σ - 1) / (Z * (Real.exp t + 1)) =
          (1 / Z) * (t ^ (σ - 1) * (Real.exp t + 1)⁻¹) := by
        field_simp [hZ.ne', ne_of_gt (by positivity : 0 < Real.exp t + 1)]
      unfold fermiFormationDensity
      rw [hdiv]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hk hnonneg) (by positivity)
  unfold fermiFormationMeasure
  exact isFiniteMeasure_withDensity_ofReal hfint.hasFiniteIntegral

/-- Vanishing Jeffreys information work between finite Fermi measures forces equal exponents. -/
theorem fermiFormationJeffreys_eq_zero_imp_parameter_eq
    {a b Za Zb : ℝ} (ha : 0 < a) (hb : 0 < b) (hZa : 0 < Za) (hZb : 0 < Zb)
    (hJ : fermiFormationJeffreys a b Za Zb = 0) : a = b := by
  letI := finite_fermiFormationMeasure ha hZa
  letI := finite_fermiFormationMeasure hb hZb
  unfold fermiFormationJeffreys at hJ
  have hzero := (add_eq_zero.mp hJ).1
  exact fermiFormationMeasure_eq_imp_parameter_eq hZa hZb (klDiv_eq_zero_iff.mp hzero)

/-- Reflected finite Fermi measures have zero Jeffreys work only at the critical center. -/
theorem reflected_fermiFormationJeffreys_eq_zero_imp_center
    {σ Zσ Zr : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hZσ : 0 < Zσ) (hZr : 0 < Zr)
    (hJ : fermiFormationJeffreys σ (1 - σ) Zσ Zr = 0) : σ = 1 / 2 := by
  have hs := fermiFormationJeffreys_eq_zero_imp_parameter_eq
    hσ0 (sub_pos.mpr hσ1) hZσ hZr hJ
  linarith

/-- Global reflected-information properness for any positive normalizer family. -/
theorem reflected_fermiFormationJeffreys_eq_zero_iff_center
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (Z : ℝ → ℝ) (hZ : ∀ a : ℝ, 0 < a → 0 < Z a) :
    fermiFormationJeffreys σ (1 - σ) (Z σ) (Z (1 - σ)) = 0 ↔ σ = 1 / 2 := by
  constructor
  · exact fun h => reflected_fermiFormationJeffreys_eq_zero_imp_center
      hσ0 hσ1 (hZ σ hσ0) (hZ (1 - σ) (sub_pos.mpr hσ1)) h
  · intro hcenter
    subst σ
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    letI := finite_fermiFormationMeasure hhalf (hZ (1 / 2) hhalf)
    norm_num [fermiFormationJeffreys]

end

end GaloisForLFunctions.HTGeometry
