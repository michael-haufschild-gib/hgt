import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CoreScatteringAsymptotics
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PhysicalCoresHaveFiniteHeckeCuspEnergy

/-!
# The PM Krein form as the linear term of physical cusp energy

Scattering-charge normalization makes actual cores asymptotic to their
spectral powers. Explicit exponential counterterms leave the existing
finite Krein pairing as the mean energy at the lower cusp.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions RenormalizedIntersectionTheory MayerScatteringCore

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The nonzero outgoing charge of an actual upper-resonant core. -/
def mayerCuspCharge (s : upperMayerResonances) : ℂ :=
  2 * riemannZeta (2 * s.1 - 1) / (2 * s.1 - 1)

theorem mayerCuspCharge_ne_zero (s : upperMayerResonances) : mayerCuspCharge s ≠ 0 := by
  have hn := eisensteinLewisPeriod_one_ne_zero s.2.2.1 s.2.2.2.1
  rw [eisensteinLewisPeriod_one_eq s.2.2.1 s.2.2.2.1] at hn
  have hd : 2 * s.1 - 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.sub_re, Complex.mul_re] at hh
    linarith only [hh, s.2.2.2.1]
  exact div_ne_zero hn hd

/-- Charge normalization gives the lower-cusp leading term `a^(1−2s)`. -/
def mayerCuspNormalizedCore (s : upperMayerResonances) (a : ℝ) : ℂ :=
  -mayerPeriodCore s.1 a / mayerCuspCharge s

/-- The literal physical packet associated to the existing PM basis coordinates. -/
def mayerCuspPacket (v : mayerPeriodKreinSpace) (a : ℝ) : ℂ :=
  (mayerPeriodBasis.repr v).sum (fun s c => c * mayerCuspNormalizedCore s a)

/-- Critical cusp weighting in logarithmic physical coordinates. -/
def mayerCuspLogPacket (v : mayerPeriodKreinSpace) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * mayerCuspPacket v (Real.exp (-x))

/-- Physical cusp square-energy integral up to logarithmic depth `T`. -/
def mayerCuspEnergy (v : mayerPeriodKreinSpace) (T : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..T, ‖mayerCuspLogPacket v x‖ ^ 2

/-- The exponent of a pair of normalized spectral modes. -/
def mayerCuspPairExponent (s t : upperMayerResonances) : ℂ :=
  2 * s.1 + 2 * conj t.1 - 1

/-- Integrated nonconstant spectral modes, retained as explicit physical
energy counterterms. -/
def mayerCuspCounterterm (v : mayerPeriodKreinSpace) (T : ℝ) : ℝ := by
  classical
  exact ((mayerPeriodBasis.repr v).sum (fun s c =>
    (mayerPeriodBasis.repr v).sum (fun t d =>
      if mayerCuspPairExponent s t = 0 then 0 else
        c * conj d * (Complex.exp (mayerCuspPairExponent s t * (T : ℂ)) - 1) /
          mayerCuspPairExponent s t))).re

private theorem normalized_core_lower_bound (s : upperMayerResonances)
    {ε : ℝ} (hε : 0 < ε) (hεs : ε < 2 * s.1.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a > 0,
      ‖mayerCuspNormalizedCore s a - (a : ℂ) ^ (1 - 2 * s.1)‖ ≤ C * a ^ (1 - ε) := by
  obtain ⟨C, hC, hb⟩ := mayerPeriodCore_scattering_lower_bound s hε hεs
  refine ⟨C / ‖mayerCuspCharge s‖, div_nonneg hC (norm_nonneg _), fun a ha => ?_⟩
  have he : mayerCuspNormalizedCore s a - (a : ℂ) ^ (1 - 2 * s.1) =
      -(mayerPeriodCore s.1 a + mayerCuspCharge s * (a : ℂ) ^ (1 - 2 * s.1)) /
        mayerCuspCharge s := by
    rw [mayerCuspNormalizedCore]
    field_simp [mayerCuspCharge_ne_zero s]
    ring
  rw [he, norm_div, norm_neg]
  exact (div_le_div_of_nonneg_right (hb a ha) (norm_nonneg _)).trans_eq (by ring)

private theorem real_exp_cpow (x : ℝ) (w : ℂ) :
    (Real.exp x : ℂ) ^ w = Complex.exp ((x : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

private theorem normalized_log_core_bound (s : upperMayerResonances)
    {ε : ℝ} (hε : 0 < ε) (hεs : ε < 2 * s.1.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖(Real.exp (x / 2) : ℂ) * mayerCuspNormalizedCore s (Real.exp (-x)) -
        Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ))‖ ≤
          C * Real.exp (-((1 / 2 - ε) * x)) := by
  obtain ⟨C, hC, hb⟩ := normalized_core_lower_bound s hε hεs
  refine ⟨C, hC, fun x => ?_⟩
  have he : (Real.exp (x / 2) : ℂ) * ((Real.exp (-x) : ℂ) ^ (1 - 2 * s.1)) =
      Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ)) := by
    rw [real_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← he, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (x / 2) * (C * (Real.exp (-x)) ^ (1 - ε)) :=
      mul_le_mul_of_nonneg_left (hb _ (Real.exp_pos _)) (Real.exp_pos _).le
    _ = _ := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [mul_left_comm (Real.exp (x / 2)), ← Real.exp_add]
      congr 2
      ring


private theorem finite_cusp_exponent (S : Finset upperMayerResonances) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∀ s ∈ S,
      ε < 2 * s.1.re ∧ 2 * s.1.re ≤ 1 - 2 * ε := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1 / 8, by norm_num, by norm_num, by simp⟩
  | @insert s S hs ih =>
    obtain ⟨η, hη, hηq, hηS⟩ := ih
    let ε := min η (min (s.1.re / 2) ((1 - 2 * s.1.re) / 4))
    have hε : 0 < ε := lt_min hη (lt_min
      (by linarith only [s.2.2.1]) (by linarith only [s.2.2.2.1]))
    have hεη : ε ≤ η := min_le_left _ _
    have hεs : ε ≤ s.1.re / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hεg : ε ≤ (1 - 2 * s.1.re) / 4 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨ε, hε, hεη.trans hηq, fun t ht => ?_⟩
    rcases Finset.mem_insert.mp ht with he | ht
    · subst t
      constructor
      · linarith only [hεs, s.2.2.1]
      · linarith only [hεg, s.2.2.2.1]
    · obtain ⟨hl, hu⟩ := hηS t ht
      exact ⟨hεη.trans_lt hl, by linarith only [hu, hεη]⟩

private theorem finite_log_core_error_bound (S : Finset upperMayerResonances)
    (c : upperMayerResonances → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hεS : ∀ s ∈ S, ε < 2 * s.1.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖∑ s ∈ S, c s *
        ((Real.exp (x / 2) : ℂ) * mayerCuspNormalizedCore s (Real.exp (-x)) -
          Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ)))‖ ≤
        C * Real.exp (-((1 / 2 - ε) * x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert s S hs ih =>
    obtain ⟨C, hC, hb⟩ := ih (fun t ht => hεS t (Finset.mem_insert_of_mem ht))
    obtain ⟨D, hD, hd⟩ := normalized_log_core_bound s hε (hεS s (Finset.mem_insert_self _ _))
    refine ⟨‖c s‖ * D + C, by positivity, fun x => ?_⟩
    rw [Finset.sum_insert hs]
    calc
      _ ≤ ‖c s * ((Real.exp (x / 2) : ℂ) * mayerCuspNormalizedCore s (Real.exp (-x)) -
          Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ)))‖ +
          ‖∑ t ∈ S, c t * ((Real.exp (x / 2) : ℂ) * mayerCuspNormalizedCore t (Real.exp (-x)) -
            Complex.exp ((2 * t.1 - 1 / 2) * (x : ℂ)))‖ := norm_add_le _ _
      _ ≤ ‖c s‖ * (D * Real.exp (-((1 / 2 - ε) * x))) +
          C * Real.exp (-((1 / 2 - ε) * x)) := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hd x) (norm_nonneg _)) (hb x)
      _ = _ := by ring

private theorem finite_log_model_bound (S : Finset upperMayerResonances)
    (c : upperMayerResonances → ℂ) {ε : ℝ}
    (hεS : ∀ s ∈ S, 2 * s.1.re ≤ 1 - 2 * ε) {x : ℝ} (hx : 0 ≤ x) :
    ‖∑ s ∈ S, c s * Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ))‖ ≤
      (∑ s ∈ S, ‖c s‖) * Real.exp ((1 / 2 - 2 * ε) * x) := by
  calc
    _ ≤ ∑ s ∈ S, ‖c s * Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ S, ‖c s‖ * Real.exp ((1 / 2 - 2 * ε) * x) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul, Complex.norm_exp]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have hre : ((2 * s.1 - 1 / 2) * (x : ℂ)).re = (2 * s.1.re - 1 / 2) * x := by simp
      rw [hre]
      exact mul_le_mul_of_nonneg_right (by linarith only [hεS s hs]) hx
    _ = _ := by rw [Finset.sum_mul]

private theorem energy_difference_bound (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * ‖b‖ * ‖a - b‖ + ‖a - b‖ ^ 2 := by
  have hdiff := abs_norm_sub_norm_le a b
  have htri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    calc
      _ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) :=
      mul_le_mul_of_nonneg_right hdiff (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖a - b‖ * (‖a - b‖ + 2 * ‖b‖) :=
      mul_le_mul_of_nonneg_left (by linarith only [htri]) (norm_nonneg _)
    _ = _ := by ring


private theorem exponential_energy_error_bound {a b : ℂ} {C D ε x : ℝ}
    (_hC : 0 ≤ C) (hD : 0 ≤ D) (hε : ε ≤ 1 / 4) (hx : 0 ≤ x)
    (hr : ‖a - b‖ ≤ C * Real.exp (-((1 / 2 - ε) * x)))
    (hb : ‖b‖ ≤ D * Real.exp ((1 / 2 - 2 * ε) * x)) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ (2 * D * C + C ^ 2) * Real.exp (-(ε * x)) := by
  have hprod := mul_le_mul hb hr (norm_nonneg (a - b)) (by positivity)
  have hsq := pow_le_pow_left₀ (norm_nonneg (a - b)) hr 2
  have hcross : Real.exp ((1 / 2 - 2 * ε) * x) * Real.exp (-((1 / 2 - ε) * x)) =
      Real.exp (-(ε * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsquare : Real.exp (-((1 / 2 - ε) * x)) * Real.exp (-((1 / 2 - ε) * x)) =
      Real.exp (-((1 - 2 * ε) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-((1 - 2 * ε) * x)) ≤ Real.exp (-(ε * x)) := by
    apply Real.exp_le_exp.mpr
    have hcoef : -(1 - 2 * ε) ≤ -ε := by linarith only [hε]
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right hcoef hx
  calc
    _ ≤ 2 * ‖b‖ * ‖a - b‖ + ‖a - b‖ ^ 2 := energy_difference_bound a b
    _ ≤ 2 * (D * Real.exp ((1 / 2 - 2 * ε) * x)) *
        (C * Real.exp (-((1 / 2 - ε) * x))) +
        (C * Real.exp (-((1 / 2 - ε) * x))) ^ 2 := by
      exact add_le_add (by nlinarith only [hprod]) hsq
    _ = 2 * D * C * Real.exp (-(ε * x)) + C ^ 2 * Real.exp (-((1 - 2 * ε) * x)) := by
      calc
        _ = 2 * D * C * (Real.exp ((1 / 2 - 2 * ε) * x) *
            Real.exp (-((1 / 2 - ε) * x))) +
            C ^ 2 * (Real.exp (-((1 / 2 - ε) * x)) * Real.exp (-((1 / 2 - ε) * x))) := by ring
        _ = _ := by rw [hcross, hsquare]
    _ ≤ 2 * D * C * Real.exp (-(ε * x)) + C ^ 2 * Real.exp (-(ε * x)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hexp (sq_nonneg C))
    _ = _ := by ring

private def cuspLogModel (v : mayerPeriodKreinSpace) (x : ℝ) : ℂ :=
  (mayerPeriodBasis.repr v).sum (fun s c => c * Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ)))

private theorem cuspLogPacket_sub_model (v : mayerPeriodKreinSpace) (x : ℝ) :
    mayerCuspLogPacket v x - cuspLogModel v x =
      ∑ s ∈ (mayerPeriodBasis.repr v).support, (mayerPeriodBasis.repr v s) *
        ((Real.exp (x / 2) : ℂ) * mayerCuspNormalizedCore s (Real.exp (-x)) -
          Complex.exp ((2 * s.1 - 1 / 2) * (x : ℂ))) := by
  classical
  simp only [mayerCuspLogPacket, mayerCuspPacket, cuspLogModel, Finsupp.sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  ring

private theorem measurable_cuspLogPacket (v : mayerPeriodKreinSpace) :
    Measurable (mayerCuspLogPacket v) := by
  classical
  have hc (s : upperMayerResonances) : Measurable (mayerCuspNormalizedCore s) :=
    (mayerPeriodCore_measurable s.2.1).neg.div_const _
  unfold mayerCuspLogPacket mayerCuspPacket Finsupp.sum
  fun_prop

private theorem continuous_cuspLogModel (v : mayerPeriodKreinSpace) :
    Continuous (cuspLogModel v) := by
  classical
  unfold cuspLogModel Finsupp.sum
  fun_prop

private theorem cusp_energy_error_integrable (v : mayerPeriodKreinSpace) :
    IntegrableOn (fun x : ℝ => ‖mayerCuspLogPacket v x‖ ^ 2 - ‖cuspLogModel v x‖ ^ 2) (Ioi 0) := by
  classical
  obtain ⟨ε, hε, hεq, hεS⟩ := finite_cusp_exponent (mayerPeriodBasis.repr v).support
  obtain ⟨C, hC, herr⟩ := finite_log_core_error_bound (mayerPeriodBasis.repr v).support
    (mayerPeriodBasis.repr v) hε (fun s hs => (hεS s hs).1)
  let D : ℝ := ∑ s ∈ (mayerPeriodBasis.repr v).support, ‖mayerPeriodBasis.repr v s‖
  have hD : 0 ≤ D := Finset.sum_nonneg (fun s hs => norm_nonneg _)
  have hbase : Integrable (fun x : ℝ => Real.exp (-(ε * |x|))) := by
    simpa only [pow_zero, one_mul, neg_mul] using
      _root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hε
  apply ((hbase.const_mul (2 * D * C + C ^ 2)).integrableOn).mono'
  · exact (((measurable_cuspLogPacket v).norm.pow_const 2).sub
      ((continuous_cuspLogModel v).measurable.norm.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (show 0 < x from hx)]
    apply exponential_energy_error_bound hC hD hεq hx.le
    · rw [cuspLogPacket_sub_model]
      exact herr x
    · exact finite_log_model_bound (mayerPeriodBasis.repr v).support (mayerPeriodBasis.repr v)
        (fun s hs => (hεS s hs).2) hx.le


private theorem cusp_pair_zero_iff (s t : upperMayerResonances) :
    mayerCuspPairExponent s t = 0 ↔ t = reflectUpperResonance s := by
  constructor
  · intro h
    apply Subtype.ext
    change t.1 = 1 / 2 - conj s.1
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num [mayerCuspPairExponent, Complex.mul_re] at hr
    norm_num [mayerCuspPairExponent, Complex.mul_im] at hi
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.conj_re]
      norm_num
      linarith only [hr]
    · simp only [Complex.sub_im, Complex.conj_im]
      norm_num
      linarith only [hi]
  · rintro rfl
    change 2 * s.1 + 2 * conj (1 / 2 - conj s.1) - 1 = 0
    simp only [map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
    ring

private theorem cusp_zero_modes (v : mayerPeriodKreinSpace) :
    (∑ s ∈ (mayerPeriodBasis.repr v).support,
      ∑ t ∈ (mayerPeriodBasis.repr v).support,
        if mayerCuspPairExponent s t = 0 then
          mayerPeriodBasis.repr v s * conj (mayerPeriodBasis.repr v t) else 0) =
      mayerKreinForm v v := by
  classical
  rw [mayerKreinForm, mayerKreinPosInner_eq_sum_of_subset Finset.Subset.rfl]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [repr_mayerKreinReflection]
  simp_rw [cusp_pair_zero_iff]
  rw [Finset.sum_eq_single (reflectUpperResonance s)]
  · simp only [ite_true]
  · intro t ht hts
    exact if_neg hts
  · intro ht
    simp only [ite_true, Finsupp.notMem_support_iff.mp ht, map_zero, mul_zero]

private theorem cusp_model_square (v : mayerPeriodKreinSpace) (x : ℝ) :
    ((‖cuspLogModel v x‖ ^ 2 : ℝ) : ℂ) =
      ∑ s ∈ (mayerPeriodBasis.repr v).support,
      ∑ t ∈ (mayerPeriodBasis.repr v).support,
        mayerPeriodBasis.repr v s * conj (mayerPeriodBasis.repr v t) *
          Complex.exp (mayerCuspPairExponent s t * (x : ℂ)) := by
  classical
  rw [Complex.sq_norm, ← Complex.mul_conj]
  unfold cuspLogModel Finsupp.sum
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun t ht => ?_
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have he : mayerCuspPairExponent s t * (x : ℂ) =
      (2 * s.1 - 1 / 2) * (x : ℂ) + conj (2 * t.1 - 1 / 2) * (x : ℂ) := by
    simp only [mayerCuspPairExponent, map_sub, map_mul, map_div₀, map_ofNat, map_one]
    ring
  rw [he, Complex.exp_add]
  ring

private theorem cusp_model_integral (v : mayerPeriodKreinSpace) (T : ℝ) :
    (∫ x in (0 : ℝ)..T, ‖cuspLogModel v x‖ ^ 2) =
      T * (mayerKreinForm v v).re + mayerCuspCounterterm v T := by
  classical
  let c := mayerPeriodBasis.repr v
  have hcont (s t : upperMayerResonances) : Continuous (fun x : ℝ =>
      c s * conj (c t) * Complex.exp (mayerCuspPairExponent s t * (x : ℂ))) := by fun_prop
  have hmode (s t : upperMayerResonances) :
      (∫ x in (0 : ℝ)..T, c s * conj (c t) *
        Complex.exp (mayerCuspPairExponent s t * (x : ℂ))) =
      (T : ℂ) * (if mayerCuspPairExponent s t = 0 then c s * conj (c t) else 0) +
        (if mayerCuspPairExponent s t = 0 then 0 else
          c s * conj (c t) * (Complex.exp (mayerCuspPairExponent s t * (T : ℂ)) - 1) /
            mayerCuspPairExponent s t) := by
    rw [intervalIntegral.integral_const_mul]
    by_cases h : mayerCuspPairExponent s t = 0
    · simp [h, mul_comm]
    · rw [integral_exp_mul_complex h]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, if_neg h, mul_zero, zero_add]
      ring
  have hcomplex : ((∫ x in (0 : ℝ)..T, ‖cuspLogModel v x‖ ^ 2 : ℝ) : ℂ) =
      (T : ℂ) * mayerKreinForm v v +
        ∑ s ∈ c.support, ∑ t ∈ c.support,
          if mayerCuspPairExponent s t = 0 then 0 else
            c s * conj (c t) * (Complex.exp (mayerCuspPairExponent s t * (T : ℂ)) - 1) /
              mayerCuspPairExponent s t := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [cusp_model_square]
    rw [intervalIntegral.integral_finsetSum (fun s hs =>
      (continuous_finsetSum _ fun t ht => hcont s t).intervalIntegrable _ _)]
    simp_rw [intervalIntegral.integral_finsetSum (fun t ht => (hcont _ t).intervalIntegrable _ _),
      hmode, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [cusp_zero_modes]
  have hr := congrArg Complex.re hcomplex
  simpa only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero, mayerCuspCounterterm, Finsupp.sum, c] using hr

/-- The linear term of the actual normalized physical cusp energy is precisely
PM's existing Krein square, after removing the explicit nonconstant modes. -/
theorem mayerCuspEnergy_renormalized_mean (v : mayerPeriodKreinSpace) :
    Tendsto (fun T : ℝ => (mayerCuspEnergy v T - mayerCuspCounterterm v T) / T)
      atTop (𝓝 (mayerKreinForm v v).re) := by
  have hi := cusp_energy_error_integrable v
  have ht := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hi
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hzero : Tendsto (fun T : ℝ =>
      (∫ x in (0 : ℝ)..T, ‖mayerCuspLogPacket v x‖ ^ 2 - ‖cuspLogModel v x‖ ^ 2) / T)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, id_eq] using ht.mul tendsto_inv_atTop_zero
  have hlim : Tendsto (fun T : ℝ =>
      (∫ x in (0 : ℝ)..T, ‖mayerCuspLogPacket v x‖ ^ 2 - ‖cuspLogModel v x‖ ^ 2) / T +
        (mayerKreinForm v v).re) atTop (𝓝 (mayerKreinForm v v).re) := by
    simpa only [zero_add] using hzero.add_const (mayerKreinForm v v).re
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have he : IntervalIntegrable
      (fun x : ℝ => ‖mayerCuspLogPacket v x‖ ^ 2 - ‖cuspLogModel v x‖ ^ 2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hi.mono_set Ioc_subset_Ioi_self)
  have hm : IntervalIntegrable (fun x : ℝ => ‖cuspLogModel v x‖ ^ 2) volume 0 T :=
    ((continuous_cuspLogModel v).norm.pow 2).intervalIntegrable _ _
  have hp : IntervalIntegrable (fun x : ℝ => ‖mayerCuspLogPacket v x‖ ^ 2) volume 0 T := by
    simpa only [sub_add_cancel] using he.add hm
  rw [intervalIntegral.integral_sub hp hm, cusp_model_integral]
  change (_ - (T * (mayerKreinForm v v).re + mayerCuspCounterterm v T)) / T +
    (mayerKreinForm v v).re = _
  dsimp only [mayerCuspEnergy]
  field_simp [hT.ne']
  ring

#print axioms mayerCuspCharge_ne_zero
#print axioms mayerCuspEnergy_renormalized_mean

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
