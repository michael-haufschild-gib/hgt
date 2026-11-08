import Mathlib

/-!
# The nondecaying boundary of a reflected Laplace pair

Two disjoint interval packets have squared mass two. Against a decaying
exponential their moment stays positive; against a nondecaying exponential
it becomes arbitrarily negative. Thus compact square-integrable tests
already exclude a lower bound at the boundary of the decay region.
Unimodular modulation gives the same obstruction at every ordinate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity.WeightedReflectedPair

private theorem integrable_interval_indicator (l r : ℝ) (F : ℝ → ℝ)
    (hF : Continuous F) : Integrable ((Ioc l r).indicator F) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact hF.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Two disjoint intervals with equal total square mass. -/
def boundaryPacket (k t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator 1 t -
    k⁻¹ * (Ioc (1 : ℝ) (1 + k ^ 2)).indicator 1 t

/-- Real Laplace evaluation, defined whenever the weighted packet is integrable. -/
def realMoment (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ t, f t * Real.exp (-a * t)

private theorem indicator_mul_exp (l r a t : ℝ) :
    (Ioc l r).indicator (1 : ℝ → ℝ) t * Real.exp (-a * t) =
      (Ioc l r).indicator (fun t => Real.exp (-a * t)) t := by
  by_cases ht : t ∈ Ioc l r <;> simp [ht]

private theorem boundaryPacket_sq (k t : ℝ) :
    boundaryPacket k t ^ 2 = (Ioc (0 : ℝ) 1).indicator 1 t +
      (k⁻¹) ^ 2 * (Ioc (1 : ℝ) (1 + k ^ 2)).indicator 1 t := by
  by_cases h0 : t ∈ Ioc (0 : ℝ) 1
  · have h1 : t ∉ Ioc (1 : ℝ) (1 + k ^ 2) := by
      intro h
      exact (not_lt_of_ge h0.2) h.1
    simp [boundaryPacket, h0, h1]
  · by_cases h1 : t ∈ Ioc (1 : ℝ) (1 + k ^ 2) <;>
      simp [boundaryPacket, h0, h1]

theorem integral_boundaryPacket_sq {k : ℝ} (hk : 0 < k) :
    (∫ t, boundaryPacket k t ^ 2) = 2 := by
  have h0 : Integrable ((Ioc (0 : ℝ) 1).indicator (1 : ℝ → ℝ)) :=
    integrable_interval_indicator 0 1 (fun _ => 1) continuous_const
  have h1 : Integrable ((Ioc (1 : ℝ) (1 + k ^ 2)).indicator (1 : ℝ → ℝ)) :=
    integrable_interval_indicator 1 (1 + k ^ 2) (fun _ => 1) continuous_const
  simp_rw [boundaryPacket_sq]
  rw [integral_add h0 (h1.const_mul _), integral_const_mul,
    integral_indicator_one measurableSet_Ioc, integral_indicator_one measurableSet_Ioc,
    Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1),
    Real.volume_real_Ioc_of_le (by nlinarith only [sq_nonneg k] : 1 ≤ 1 + k ^ 2)]
  field_simp [ne_of_gt hk]
  ring

theorem realMoment_boundaryPacket (a k : ℝ) :
    realMoment a (boundaryPacket k) =
      (∫ t in Ioc (0 : ℝ) 1, Real.exp (-a * t)) -
        k⁻¹ * ∫ t in Ioc (1 : ℝ) (1 + k ^ 2), Real.exp (-a * t) := by
  have h0 := integrable_interval_indicator 0 1 (fun t => Real.exp (-a * t)) (by fun_prop)
  have h1 := integrable_interval_indicator 1 (1 + k ^ 2)
    (fun t => Real.exp (-a * t)) (by fun_prop)
  unfold realMoment boundaryPacket
  simp_rw [sub_mul, mul_assoc]
  simp_rw [indicator_mul_exp]
  rw [integral_sub h0 (h1.const_mul _), integral_const_mul,
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]


theorem boundaryPacket_zero_outside (k t : ℝ) (ht : t ∉ Icc 0 (1 + k ^ 2)) :
    boundaryPacket k t = 0 := by
  have h0 : t ∉ Ioc (0 : ℝ) 1 := by
    intro h
    apply ht
    exact ⟨le_of_lt h.1, le_trans h.2 (by nlinarith only [sq_nonneg k])⟩
  have h1 : t ∉ Ioc (1 : ℝ) (1 + k ^ 2) := by
    intro h
    exact ht ⟨by linarith only [h.1], h.2⟩
  simp [boundaryPacket, h0, h1]

private theorem integral_exp_base_lower {a : ℝ} (ha : 0 < a) :
    Real.exp (-a) ≤ ∫ t in Ioc (0 : ℝ) 1, Real.exp (-a * t) := by
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (-a)) (Ioc 0 1) :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioc 0 1) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-a * t))).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have h := setIntegral_mono_on hc he measurableSet_Ioc (fun t ht =>
    Real.exp_le_exp.mpr (by nlinarith only [ha, ht.2]))
  simpa using h

private theorem integral_exp_base_upper {b : ℝ} (hb : b ≤ 0) :
    (∫ t in Ioc (0 : ℝ) 1, Real.exp (-b * t)) ≤ Real.exp (-b) := by
  have hc : IntegrableOn (fun _ : ℝ => Real.exp (-b)) (Ioc 0 1) :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Ioc 0 1) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-b * t))).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have h := setIntegral_mono_on he hc measurableSet_Ioc (fun t ht =>
    Real.exp_le_exp.mpr (by nlinarith only [hb, ht.2]))
  simpa using h

private theorem integral_exp_tail_le {a : ℝ} (ha : 0 < a) (k : ℝ) :
    (∫ t in Ioc (1 : ℝ) (1 + k ^ 2), Real.exp (-a * t)) ≤ 1 / a := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) := by
      apply setIntegral_mono_set (exp_neg_integrableOn_Ioi 0 ha)
        (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
      exact Filter.Eventually.of_forall fun t ht => lt_trans zero_lt_one ht.1
    _ = 1 / a := by
      rw [integral_exp_mul_Ioi (by linarith only [ha] : -a < 0)]
      simp

private theorem integral_exp_tail_ge {b : ℝ} (hb : b ≤ 0) (k : ℝ) :
    k ^ 2 ≤ ∫ t in Ioc (1 : ℝ) (1 + k ^ 2), Real.exp (-b * t) := by
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 1 (1 + k ^ 2)) :=
    continuous_const.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Ioc 1 (1 + k ^ 2)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-b * t))).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have h := setIntegral_mono_on hc he measurableSet_Ioc (fun t ht => by
    have hbt : 0 ≤ -b * t := mul_nonneg (neg_nonneg.mpr hb) (by linarith only [ht.1])
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hbt)
  simpa [Real.volume_real_Ioc_of_le (by nlinarith only [sq_nonneg k] : 1 ≤ 1 + k ^ 2)] using h


theorem integrable_boundaryPacket_mul_exp (a k : ℝ) :
    Integrable (fun t => boundaryPacket k t * Real.exp (-a * t)) := by
  have h0 := integrable_interval_indicator 0 1 (fun t => Real.exp (-a * t)) (by fun_prop)
  have h1 := integrable_interval_indicator 1 (1 + k ^ 2)
    (fun t => Real.exp (-a * t)) (by fun_prop)
  unfold boundaryPacket
  simp_rw [sub_mul, mul_assoc]
  simp_rw [indicator_mul_exp]
  exact h0.sub (h1.const_mul _)

theorem memLp_boundaryPacket (k : ℝ) : MemLp (boundaryPacket k) 2 volume := by
  have h0 := integrable_interval_indicator 0 1 (fun _ => 1) continuous_const
  have h1 := integrable_interval_indicator 1 (1 + k ^ 2) (fun _ => 1) continuous_const
  have hf : Integrable (boundaryPacket k) := h0.sub (h1.const_mul _)
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hsq := h0.add (h1.const_mul ((k⁻¹) ^ 2))
  refine hsq.congr (Filter.Eventually.of_forall fun t => ?_)
  change (Ioc (0 : ℝ) 1).indicator 1 t +
    (k⁻¹) ^ 2 * (Ioc (1 : ℝ) (1 + k ^ 2)).indicator 1 t = ‖boundaryPacket k t‖ ^ 2
  rw [Real.norm_eq_abs, sq_abs, boundaryPacket_sq]

theorem realMoment_boundaryPacket_lower {a k : ℝ} (ha : 0 < a) (hk : 0 < k) :
    Real.exp (-a) - 1 / (a * k) ≤ realMoment a (boundaryPacket k) := by
  rw [realMoment_boundaryPacket]
  have ht := mul_le_mul_of_nonneg_left (integral_exp_tail_le ha k) (le_of_lt (inv_pos.mpr hk))
  calc
    _ = Real.exp (-a) - k⁻¹ * (1 / a) := by ring
    _ ≤ _ := sub_le_sub (integral_exp_base_lower ha) ht

theorem realMoment_boundaryPacket_upper {b k : ℝ} (hb : b ≤ 0) (hk : 0 < k) :
    realMoment b (boundaryPacket k) ≤ Real.exp (-b) - k := by
  rw [realMoment_boundaryPacket]
  have ht := mul_le_mul_of_nonneg_left (integral_exp_tail_ge hb k) (le_of_lt (inv_pos.mpr hk))
  calc
    _ ≤ Real.exp (-b) - k⁻¹ * k ^ 2 := sub_le_sub (integral_exp_base_upper hb) ht
    _ = _ := by field_simp [ne_of_gt hk]

/-- A nondecaying second evaluation makes the reflected pair unbounded below at mass two. -/
theorem exists_boundaryPacket_below {a b : ℝ} (ha : 0 < a) (hb : b ≤ 0)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ k : ℝ, 0 < k ∧
      2 * realMoment a (boundaryPacket k) * realMoment b (boundaryPacket k) < -2 * C := by
  have hE := Real.exp_pos (-a)
  obtain ⟨k, hk⟩ := exists_gt
    (max (max 1 (2 / (a * Real.exp (-a))))
      (Real.exp (-b) + 2 * C / Real.exp (-a)))
  have hk1 : 1 < k := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk0 : 0 < k := lt_trans zero_lt_one hk1
  have hkA : 2 / (a * Real.exp (-a)) < k := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkB : Real.exp (-b) + 2 * C / Real.exp (-a) < k :=
    lt_of_le_of_lt (le_max_right _ _) hk
  have hkA' : 2 < k * (a * Real.exp (-a)) :=
    (div_lt_iff₀ (mul_pos ha hE)).mp hkA
  have hinv : 1 / (a * k) < Real.exp (-a) / 2 := by
    apply (div_lt_iff₀ (mul_pos ha hk0)).mpr
    nlinarith only [hkA']
  have hA : Real.exp (-a) / 2 < realMoment a (boundaryPacket k) := by
    have h := realMoment_boundaryPacket_lower ha hk0
    linarith only [h, hinv]
  have hB : realMoment b (boundaryPacket k) < -(2 * C / Real.exp (-a)) := by
    have h := realMoment_boundaryPacket_upper hb hk0
    linarith only [h, hkB]
  have hB0 : realMoment b (boundaryPacket k) < 0 :=
    lt_of_lt_of_le hB (neg_nonpos.mpr (div_nonneg (by positivity) hE.le))
  refine ⟨k, hk0, ?_⟩
  calc
    _ ≤ Real.exp (-a) * realMoment b (boundaryPacket k) := by
      have h := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr hA.le) hB0.le
      nlinarith only [h]
    _ < Real.exp (-a) * (-(2 * C / Real.exp (-a))) := mul_lt_mul_of_pos_left hB hE
    _ = -2 * C := by field_simp [ne_of_gt hE]



theorem hasCompactSupport_boundaryPacket (k : ℝ) : HasCompactSupport (boundaryPacket k) :=
  HasCompactSupport.intro isCompact_Icc (boundaryPacket_zero_outside k)

/-- Compact square-integrable tests already detect the entire nondecaying boundary. -/
theorem exists_compact_packet_below {a b : ℝ} (ha : 0 < a) (hb : b ≤ 0)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ f : ℝ → ℝ, HasCompactSupport f ∧ MemLp f 2 volume ∧
      (∀ t : ℝ, t ≤ 0 → f t = 0) ∧
      Integrable (fun t => f t * Real.exp (-a * t)) ∧
      Integrable (fun t => f t * Real.exp (-b * t)) ∧
      (∫ t, f t ^ 2) = 2 ∧ 2 * realMoment a f * realMoment b f < -2 * C := by
  obtain ⟨k, hk, hneg⟩ := exists_boundaryPacket_below ha hb C hC
  refine ⟨boundaryPacket k, hasCompactSupport_boundaryPacket k, memLp_boundaryPacket k,
    ?_, integrable_boundaryPacket_mul_exp a k, integrable_boundaryPacket_mul_exp b k,
    integral_boundaryPacket_sq hk, hneg⟩
  intro t ht
  have h0 : t ∉ Ioc (0 : ℝ) 1 := fun h => (not_lt_of_ge ht) h.1
  have h1 : t ∉ Ioc (1 : ℝ) (1 + k ^ 2) := by
    intro h
    linarith only [ht, h.1]
  simp [boundaryPacket, h0, h1]

#print axioms exists_compact_packet_below


/-- Laplace evaluation with a specified common oscillatory phase. -/
def complexMoment (a γ : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ t, f t * Complex.exp ((-(a : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ))

/-- The Hermitian reflected pair, including rates whose evaluation kernel is not in `L²`. -/
def complexPairForm (a b γ : ℝ) (f : ℝ → ℂ) : ℝ :=
  2 * (complexMoment a γ f * starRingEnd ℂ (complexMoment b γ f)).re

/-- A common phase cancels from both reflected evaluations. -/
def modulate (γ : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  (f t : ℂ) * Complex.exp (-(γ : ℂ) * (t : ℂ) * Complex.I)

theorem norm_modulate (γ : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    ‖modulate γ f t‖ = |f t| := by
  rw [modulate, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, neg_zero, sub_zero, add_zero, Real.exp_zero, mul_one]

private theorem modulate_weighted (a γ : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    modulate γ f t *
        Complex.exp ((-(a : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ)) =
      ((f t * Real.exp (-a * t) : ℝ) : ℂ) := by
  rw [modulate, mul_assoc, ← Complex.exp_add]
  have he : -(γ : ℂ) * (t : ℂ) * Complex.I +
      (-(a : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ) = ((-a * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

theorem complexMoment_modulate (a γ : ℝ) (f : ℝ → ℝ) :
    complexMoment a γ (modulate γ f) = (realMoment a f : ℂ) := by
  unfold complexMoment realMoment
  simp_rw [modulate_weighted]
  exact integral_complex_ofReal

theorem memLp_modulate (γ : ℝ) {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    MemLp (modulate γ f) 2 volume := by
  have hfc : MemLp (fun t => (f t : ℂ)) 2 volume := hf.ofReal
  have hc : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-(γ : ℂ) * (t : ℂ) * Complex.I)) volume :=
    (by fun_prop : Continuous
      (fun t : ℝ => Complex.exp (-(γ : ℂ) * (t : ℂ) * Complex.I))).aestronglyMeasurable
  refine hfc.mono (hfc.aestronglyMeasurable.mul hc) ?_
  filter_upwards with t
  rw [norm_modulate, Complex.norm_real, Real.norm_eq_abs]

theorem complexPairForm_modulate (a b γ : ℝ) (f : ℝ → ℝ) :
    complexPairForm a b γ (modulate γ f) = 2 * realMoment a f * realMoment b f := by
  rw [complexPairForm, complexMoment_modulate, complexMoment_modulate,
    Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem complexPairForm_comm (a b γ : ℝ) (f : ℝ → ℂ) :
    complexPairForm a b γ f = complexPairForm b a γ f := by
  simp only [complexPairForm, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The compact boundary obstruction is independent of the common ordinate. -/
theorem exists_modulated_compact_packet_below {a b : ℝ} (ha : 0 < a) (hb : b ≤ 0)
    (γ C : ℝ) (hC : 0 ≤ C) :
    ∃ f : ℝ → ℂ, HasCompactSupport f ∧ MemLp f 2 volume ∧
      (∀ t : ℝ, t ≤ 0 → f t = 0) ∧
      (∀ r : ℝ, Integrable (fun t => f t *
        Complex.exp ((-(r : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ)))) ∧
      (∫ t, ‖f t‖ ^ 2) = 2 ∧ complexPairForm a b γ f < -2 * C := by
  obtain ⟨k, hk, hneg⟩ := exists_boundaryPacket_below ha hb C hC
  have hcomp : HasCompactSupport (modulate γ (boundaryPacket k)) := by
    apply HasCompactSupport.intro (K := Icc 0 (1 + k ^ 2)) isCompact_Icc
    intro t ht
    simp only [modulate, boundaryPacket_zero_outside k t ht, Complex.ofReal_zero, zero_mul]
  refine ⟨modulate γ (boundaryPacket k), hcomp, memLp_modulate γ (memLp_boundaryPacket k),
    ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h0 : t ∉ Ioc (0 : ℝ) 1 := fun h => (not_lt_of_ge ht) h.1
    have h1 : t ∉ Ioc (1 : ℝ) (1 + k ^ 2) := by
      intro h
      linarith only [ht, h.1]
    simp [modulate, boundaryPacket, h0, h1]
  · intro r
    simp_rw [modulate_weighted]
    exact (integrable_boundaryPacket_mul_exp r k).ofReal
  · simp_rw [norm_modulate, sq_abs]
    exact integral_boundaryPacket_sq hk
  · rw [complexPairForm_modulate]
    exact hneg

#print axioms exists_modulated_compact_packet_below

/-- At or below the weighted decay threshold, compact packets defeat every lower floor. -/
theorem exists_weighted_boundary_packet {p δ : ℝ} (hp : 0 < p) (hboundary : p ≤ 2 * |δ|)
    (γ C : ℝ) (hC : 0 ≤ C) :
    ∃ f : ℝ → ℂ, HasCompactSupport f ∧ MemLp f 2 volume ∧
      (∀ t : ℝ, t ≤ 0 → f t = 0) ∧
      (∀ r : ℝ, Integrable (fun t => f t *
        Complex.exp ((-(r : ℂ) + (γ : ℂ) * Complex.I) * (t : ℂ)))) ∧
      (∫ t, ‖f t‖ ^ 2) = 2 ∧
      complexPairForm (p / 2 + δ) (p / 2 - δ) γ f < -2 * C := by
  by_cases hδ : 0 ≤ δ
  · rw [abs_of_nonneg hδ] at hboundary
    exact exists_modulated_compact_packet_below
      (by linarith only [hp, hδ] : 0 < p / 2 + δ)
      (by linarith only [hboundary] : p / 2 - δ ≤ 0) γ C hC
  · have hδ' : δ ≤ 0 := (lt_of_not_ge hδ).le
    rw [abs_of_nonpos hδ'] at hboundary
    obtain ⟨f, hcomp, hLp, hzero, hint, hmass, hneg⟩ :=
      exists_modulated_compact_packet_below
        (by linarith only [hp, hδ'] : 0 < p / 2 - δ)
        (by linarith only [hboundary] : p / 2 + δ ≤ 0) γ C hC
    refine ⟨f, hcomp, hLp, hzero, hint, hmass, ?_⟩
    rw [complexPairForm_comm]
    exact hneg

#print axioms exists_weighted_boundary_packet

end GaloisForLFunctions.ArithmeticCorrespondencePositivity.WeightedReflectedPair
