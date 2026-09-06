import GaloisForLFunctions.RHTower.ChronologicalHeatMellin
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# An unconditional error floor for bounded chronological heat repair

The actual Mellin integral at a critical-line zeta zero is invariant under
all finite arithmetic repairs. Pointwise bounds control the two tails;
Cauchy–Schwarz controls the middle. A closed Hardy theorem supplies a zero,
so one positive constant G gives an explicit logarithmic floor for every
cutoff and every real coefficient vector inside any fixed box.

The same theorem gives an exponential arithmetic cost in inverse squared
accuracy. It permits slow convergence and does not prove or disprove RH.
No numerical zero or computation enters any proof.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RHTower

private theorem chronological_inv_sqrt_rpow {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t)⁻¹ = t^(-(1/2:ℝ)) := by
  rw [Real.rpow_neg ht, Real.sqrt_eq_rpow]

private theorem chronological_sqrt_weight_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => (Real.sqrt t)⁻¹) (Ioc (0:ℝ) a) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
    (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := a)
      (by linarith : (-1:ℝ)< -(1/2:ℝ)))
  exact hi.congr_fun (fun t ht => (chronological_inv_sqrt_rpow ht.1.le).symm) measurableSet_Ioc

private theorem chronological_sqrt_weight_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioc (0:ℝ) a, (Real.sqrt t)⁻¹) = 2*Real.sqrt a := by
  have he : (∫ t in Ioc (0:ℝ) a, (Real.sqrt t)⁻¹) =
      ∫ t in Ioc (0:ℝ) a, t^(-(1/2:ℝ)) :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => chronological_inv_sqrt_rpow ht.1.le)
  rw [he, ← intervalIntegral.integral_of_le ha.le,
    integral_rpow (Or.inl (by linarith : (-1:ℝ)< -(1/2:ℝ)))]
  have he : (-(1/2:ℝ))+1 = 1/2 := by ring
  rw [he, Real.zero_rpow (by positivity : (0:ℝ)<1/2).ne', ← Real.sqrt_eq_rpow]
  ring

private theorem chronological_tail_weight_integral {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi b, t^(-(3/2:ℝ))) = 2/Real.sqrt b := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -(3/2:ℝ)< -1) hb]
  have he : -(3/2:ℝ)+1 = -(1/2) := by ring
  rw [he, ← chronological_inv_sqrt_rpow hb.le]
  ring

private theorem chronological_middle_weight_bound {f : ℝ → ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in Ioc a b, |f t| / Real.sqrt t) ≤
      chronologicalL2Norm f * Real.sqrt (Real.log (b/a)) := by
  have hb : 0 < b := ha.trans_le hab
  have hsub : Ioc a b ⊆ Ioi (0:ℝ) := fun t ht => lt_trans ha ht.1
  have hmeasure : volume.restrict (Ioc a b) ≤ chronologicalPositiveVolume :=
    Measure.restrict_mono hsub le_rfl
  have hf' := MemLp.mono_measure hmeasure hf
  have hgc : ContinuousOn (fun t : ℝ => (Real.sqrt t)⁻¹) (Icc a b) :=
    Real.continuous_sqrt.continuousOn.inv₀ (fun t ht =>
      ne_of_gt (Real.sqrt_pos.2 (ha.trans_le ht.1)))
  have hgm := (hgc.mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
  have hgi : IntegrableOn (fun t : ℝ => ((Real.sqrt t)⁻¹)^2) (Ioc a b) :=
    (hgc.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hg : MemLp (fun t : ℝ => (Real.sqrt t)⁻¹) 2 (volume.restrict (Ioc a b)) :=
    (memLp_two_iff_integrable_sq hgm).mpr hgi
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf') (by simpa using hg)
  have hcs' : (∫ t in Ioc a b, |f t| / Real.sqrt t) ≤
      Real.sqrt (∫ t in Ioc a b, f t^2) *
        Real.sqrt (∫ t in Ioc a b, ((Real.sqrt t)⁻¹)^2) := by
    simp only [div_eq_mul_inv]
    simpa only [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hcs
  have hsq : (∫ t in Ioc a b, ((Real.sqrt t)⁻¹)^2) = Real.log (b/a) := by
    calc
      _ = ∫ t in Ioc a b, 1/t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change ((Real.sqrt t)⁻¹)^2 = 1/t
        rw [inv_pow, Real.sq_sqrt (ha.trans ht.1).le, one_div]
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hab, integral_one_div_of_pos ha hb]
  rw [hsq] at hcs'
  have hle : (∫ t in Ioc a b, f t^2) ≤ ∫ t in Ioi (0:ℝ), f t^2 :=
    integral_mono_measure hmeasure (Filter.Eventually.of_forall (fun t => sq_nonneg _)) hf.integrable_sq
  rw [chronologicalL2Norm_eq_sqrt hf.1]
  exact hcs'.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _))

/-- Three-region estimate for the genuine critical Mellin weight. -/
theorem chronologicalCriticalWeight_three_region {f : ℝ → ℝ} {A a b : ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume)
    (hw : IntegrableOn (fun t => |f t| / Real.sqrt t) (Ioi 0))
    (ha : 0 < a) (hab : a ≤ b)
    (hsmall : ∀ t, 0 < t → |f t| ≤ A)
    (htail : ∀ t, 0 < t → |f t| ≤ A/t) :
    (∫ t in Ioi (0:ℝ), |f t| / Real.sqrt t) ≤
      2*A*Real.sqrt a + chronologicalL2Norm f * Real.sqrt (Real.log (b/a)) +
        2*A/Real.sqrt b := by
  have hb : 0 < b := ha.trans_le hab
  have hwa := hw.mono_set (Ioi_subset_Ioi ha.le)
  have hwb := hw.mono_set (Ioi_subset_Ioi hb.le)
  have hlow : (∫ t in Ioc (0:ℝ) a, |f t| / Real.sqrt t) ≤ 2*A*Real.sqrt a := by
    calc
      _ ≤ ∫ t in Ioc (0:ℝ) a, A*(Real.sqrt t)⁻¹ := by
        apply setIntegral_mono_on (hw.mono_set Ioc_subset_Ioi_self)
          ((chronological_sqrt_weight_integrable ha).const_mul A) measurableSet_Ioc
        intro t ht
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hsmall t ht.1) (inv_nonneg.mpr (Real.sqrt_nonneg _))
      _ = _ := by rw [integral_const_mul, chronological_sqrt_weight_integral ha]; ring
  have hhigh : (∫ t in Ioi b, |f t| / Real.sqrt t) ≤ 2*A/Real.sqrt b := by
    calc
      _ ≤ ∫ t in Ioi b, A*t^(-(3/2:ℝ)) := by
        apply setIntegral_mono_on hwb
          ((integrableOn_Ioi_rpow_of_lt (by linarith : -(3/2:ℝ)< -1) hb).const_mul A)
          measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := hb.trans ht
        have hh := div_le_div_of_nonneg_right (htail t ht0) (Real.sqrt_nonneg t)
        have he : A/t/Real.sqrt t = A*t^(-(3/2:ℝ)) := by
          rw [show -(3/2:ℝ)=-(1/2)-1 by ring, Real.rpow_sub_one ht0.ne',
            ← chronological_inv_sqrt_rpow ht0.le]
          ring
        exact hh.trans_eq he
      _ = _ := by rw [integral_const_mul, chronological_tail_weight_integral hb]; ring
  have hmid := chronological_middle_weight_bound hf ha hab
  have hsplit1 := intervalIntegral.integral_interval_add_Ioi hw hwa
  have hsplit2 := intervalIntegral.integral_interval_add_Ioi hwa hwb
  rw [intervalIntegral.integral_of_le ha.le] at hsplit1
  rw [intervalIntegral.integral_of_le hab] at hsplit2
  linarith


open Complex
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The critical Mellin modulus is exactly the square-root weight. -/
theorem chronologicalCriticalMellin_norm {s : ℂ} (hs : s.re = 1/2)
    (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(t:ℂ)^(s-1) • (f t : ℂ)‖ = |f t|/Real.sqrt t := by
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_real, Real.norm_eq_abs]
  have he : (s-1).re = -(1/2:ℝ) := by simp only [Complex.sub_re, Complex.one_re, hs]; ring
  rw [he, ← chronological_inv_sqrt_rpow ht.le]
  ring

/-- Every coefficient vector obeys the same zero-controlled, three-region bound. -/
theorem chronologicalHeatError_zero_three_region (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {s : ℂ} (hs : s.re = 1/2) (hz : riemannZeta s = 0)
    {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    ‖Complex.Gamma s‖ ≤ 2*(1+C*N)*Real.sqrt l +
      chronologicalL2Norm (chronologicalHeatError a N) * Real.sqrt (Real.log (u/l)) +
      2*(1+C*N)/Real.sqrt u := by
  have hstrip : s ∈ fusionMellinStrip := by
    constructor <;> rw [hs] <;> linarith
  have hm := chronologicalHeatError_mellinConvergent a N hstrip
  have hw : IntegrableOn (fun t => |chronologicalHeatError a N t|/Real.sqrt t) (Ioi 0) := by
    have hnorm : IntegrableOn (fun t : ℝ => ‖(t:ℂ)^(s-1) • (chronologicalHeatError a N t : ℂ)‖) (Ioi 0) := hm.norm
    exact hnorm.congr_fun (fun t ht => chronologicalCriticalMellin_norm hs _ ht) measurableSet_Ioi
  have hg : ‖Complex.Gamma s‖ ≤ ∫ t in Ioi (0:ℝ), |chronologicalHeatError a N t|/Real.sqrt t := by
    rw [← chronologicalHeatError_mellin_at_zero a N hstrip hz]
    unfold mellin
    calc
      _ ≤ ∫ t in Ioi (0:ℝ), ‖(t:ℂ)^(s-1) • (chronologicalHeatError a N t : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ = _ := setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => chronologicalCriticalMellin_norm hs _ ht)
  exact hg.trans (chronologicalCriticalWeight_three_region
    (chronologicalHeatError_memLp a N) hw hl hlu
    (fun t ht => (chronologicalHeatError_bounds a N C ha ht).1)
    (fun t ht => (chronologicalHeatError_bounds a N C ha ht).2))

/-- Balanced cutoffs give the exact critical zero barrier. -/
theorem chronologicalHeatError_zero_barrier (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {s : ℂ} (hs : s.re = 1/2) (hz : riemannZeta s = 0)
    {K : ℝ} (hK : 1 < K) :
    ‖Complex.Gamma s‖ ≤ 4*(1+C*N)/K +
      2*chronologicalL2Norm (chronologicalHeatError a N)*Real.sqrt (Real.log K) := by
  have hK0 : 0 < K := by linarith
  have hi0 : 0 < K⁻¹ := inv_pos.mpr hK0
  have hi1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK.le
  have hlu : (K⁻¹)^2 ≤ K^2 := by nlinarith
  have h := chronologicalHeatError_zero_three_region a N C ha hs hz
    (sq_pos_of_pos hi0) hlu
  have hl : Real.sqrt ((K⁻¹)^2) = K⁻¹ := Real.sqrt_sq hi0.le
  have hu : Real.sqrt (K^2) = K := Real.sqrt_sq hK0.le
  have hratio : K^2/(K⁻¹)^2 = K^4 := by field_simp
  have hlog : Real.log (K^2/(K⁻¹)^2) = 4*Real.log K := by
    rw [hratio, Real.log_pow]
    simp
  have hsqrt : Real.sqrt (4*Real.log K) = 2*Real.sqrt (Real.log K) := by
    rw [Real.sqrt_mul (by linarith : (0:ℝ)≤4)]
    have h4 : Real.sqrt (4:ℝ) = 2 := by
      rw [show (4:ℝ)=(2:ℝ)^2 by ring, Real.sqrt_sq (by linarith : (0:ℝ)≤2)]
    rw [h4]
  rw [hl, hu, hlog, hsqrt] at h
  convert h using 1; ring

/-- Explicit error floor at every critical zero, with all coefficients arbitrary inside the box. -/
theorem chronologicalHeatError_logarithmic_floor (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {s : ℂ} (hs : s.re = 1/2) (hz : riemannZeta s = 0) :
    ‖Complex.Gamma s‖ /
        (4*Real.sqrt (Real.log (1+8*(1+C*N)/‖Complex.Gamma s‖))) ≤
      chronologicalL2Norm (chronologicalHeatError a N) := by
  let G := ‖Complex.Gamma s‖
  let A := 1+C*N
  let K := 1+8*A/G
  have hG : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by rw [hs]; linarith))
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 1 < K := by
    have hp : 0 < 8*A/G := by positivity
    dsimp [K]
    linarith
  have h := chronologicalHeatError_zero_barrier a N C ha hs hz hK
  change G ≤ 4*A/K+2*chronologicalL2Norm (chronologicalHeatError a N)*Real.sqrt (Real.log K) at h
  have htail : 4*A/K ≤ G/2 := by
    apply (div_le_iff₀ (by linarith : 0<K)).mpr
    dsimp [K]
    field_simp
    nlinarith
  have hroot : 0 < Real.sqrt (Real.log K) := Real.sqrt_pos.2 (Real.log_pos hK)
  change G/(4*Real.sqrt (Real.log K)) ≤ _
  apply (div_le_iff₀ (by positivity : 0<4*Real.sqrt (Real.log K))).mpr
  nlinarith

/-- A closed, unconditional universal floor: one positive zeta-derived constant works for every box. -/
theorem chronologicalHeatError_exists_universal_floor :
    ∃ G : ℝ, 0 < G ∧ ∀ C : ℝ, 0 ≤ C → ∀ N : ℕ, ∀ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) →
      G/(4*Real.sqrt (Real.log (1+8*(1+C*N)/G))) ≤
        chronologicalL2Norm (chronologicalHeatError a N) := by
  obtain ⟨T₀, _, hzero⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, _, hz⟩ := hzero T₀ le_rfl
  have hs := linePt_re τ
  have hG : 0 < ‖Complex.Gamma (linePt τ)‖ := norm_pos_iff.mpr
    (Complex.Gamma_ne_zero_of_re_pos (by rw [hs]; linarith))
  exact ⟨_, hG, fun C hC N a ha => chronologicalHeatError_logarithmic_floor a N C hC ha hs hz⟩

/-- No bounded array can make the error vanish faster than its logarithmic weight. -/
theorem chronologicalHeatError_not_log_weighted_zero :
    ∃ G : ℝ, 0 < G ∧ ∀ C : ℝ, 0 ≤ C → ∀ a : ℕ → ℕ → ℝ,
      (∀ N k, k ∈ Finset.Ioc 0 N → |a N k| ≤ C) →
      ¬ Filter.Tendsto (fun N => chronologicalL2Norm (chronologicalHeatError (a N) N) *
          Real.sqrt (Real.log (1+8*(1+C*N)/G))) Filter.atTop (𝓝 0) := by
  obtain ⟨G, hG, hfloor⟩ := chronologicalHeatError_exists_universal_floor
  refine ⟨G, hG, fun C hC a ha ht => ?_⟩
  have hbound : ∀ N : ℕ, G/4 ≤ chronologicalL2Norm (chronologicalHeatError (a N) N) *
      Real.sqrt (Real.log (1+8*(1+C*N)/G)) := by
    intro N
    have h := hfloor C hC N (a N) (ha N)
    have hK : 1 < 1+8*(1+C*N)/G := by
      have hp : 0 < 8*(1+C*N)/G := by positivity
      linarith
    have hr : 0 < Real.sqrt (Real.log (1+8*(1+C*N)/G)) :=
      Real.sqrt_pos.2 (Real.log_pos hK)
    have hh := (div_le_iff₀ (by positivity : 0 < 4*Real.sqrt (Real.log (1+8*(1+C*N)/G)))).mp h
    nlinarith
  have hz : G/4 ≤ (0:ℝ) := ge_of_tendsto ht (Filter.Eventually.of_forall hbound)
  linarith

/-- Accuracy has an exponential arithmetic cost, even with arbitrary real coefficients. -/
theorem chronologicalHeatError_exponential_budget :
    ∃ G : ℝ, 0 < G ∧ ∀ C : ℝ, 0 ≤ C → ∀ N : ℕ, ∀ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) → ∀ η : ℝ, 0 < η →
      chronologicalL2Norm (chronologicalHeatError a N) ≤ η →
      G * (Real.exp ((G/(4*η))^2)-1) ≤ 8*(1+C*N) := by
  obtain ⟨G, hG, hfloor⟩ := chronologicalHeatError_exists_universal_floor
  refine ⟨G, hG, fun C hC N a ha η hη hE => ?_⟩
  let K := 1+8*(1+C*N)/G
  have hK : 1 < K := by
    have hp : 0 < 8*(1+C*N)/G := by positivity
    dsimp [K]
    linarith
  have hr : 0 < Real.sqrt (Real.log K) := Real.sqrt_pos.2 (Real.log_pos hK)
  have h := (hfloor C hC N a ha).trans hE
  change G/(4*Real.sqrt (Real.log K)) ≤ η at h
  have hGbound := (div_le_iff₀ (by positivity : 0<4*Real.sqrt (Real.log K))).mp h
  have hx : G/(4*η) ≤ Real.sqrt (Real.log K) := by
    apply (div_le_iff₀ (by positivity : 0<4*η)).mpr
    nlinarith
  have hx0 : 0 ≤ G/(4*η) := by positivity
  have hs : (G/(4*η))^2 ≤ Real.log K := by
    have hh := mul_self_le_mul_self hx0 hx
    simpa only [← pow_two, Real.sq_sqrt (Real.log_pos hK).le] using hh
  have he := Real.exp_le_exp.mpr hs
  rw [Real.exp_log (by linarith : 0<K)] at he
  have hm := mul_le_mul_of_nonneg_left he hG.le
  have hGK : G*K = G+8*(1+C*N) := by
    dsimp [K]
    field_simp
  rw [hGK] at hm
  nlinarith

end RHTower
