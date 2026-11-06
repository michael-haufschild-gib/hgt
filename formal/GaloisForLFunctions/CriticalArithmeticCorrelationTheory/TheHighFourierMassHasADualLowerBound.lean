import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheGammaFormPaysEveryFrequencyAboveAThreshold
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# Dual lower bounds for high Fourier mass

A weighted square completion bounds high-frequency mass from below by
its pairing with any smooth recovery test. Polarized Plancherel and
Cauchy–Schwarz compare that pairing with physical mixed mass, retaining
the exact normalization and the squared below-cutoff Fourier error.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Zeta23 RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticCastelnuovoSeveri

/-- The real Fourier pairing above a threshold. -/
def highFourierPair (f g : ℝ → ℝ) (T : ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ t in highFrequencies T,
    (paperFT (cx f) t * conj (paperFT (cx g) t)).re

/-- Completing a weighted square in the high-frequency region gives a dual lower bound. -/
theorem two_mul_scalar_highFourierPair_sub_le {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (T m : ℝ) :
    2 * m * highFourierPair f g T - highFourierMass g T ≤ m ^ 2 * highFourierMass f T := by
  have hfi := integrable_normSq_paperFT_ofReal hf hfc
  have hgi := integrable_normSq_paperFT_ofReal hg hgc
  have hfg := integrable_re_paperFT_mul_conj hf hfc hg hgc
  have hp (t : ℝ) : 2 * m * (paperFT (cx f) t * conj (paperFT (cx g) t)).re -
      ‖paperFT (cx g) t‖ ^ 2 ≤ m ^ 2 * ‖paperFT (cx f) t‖ ^ 2 := by
    have h0 := Complex.normSq_nonneg ((m : ℂ) * paperFT (cx f) t - paperFT (cx g) t)
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h0
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      mul_assoc, Complex.re_ofReal_mul] at h0
    linarith only [h0]
  have hi := integral_mono (μ := volume.restrict (highFrequencies T))
    ((hfg.integrableOn.const_mul (2 * m)).sub hgi.integrableOn)
    (hfi.integrableOn.const_mul (m ^ 2)) hp
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (μ := volume.restrict (highFrequencies T))
      (hfg.integrableOn.const_mul (2 * m)) hgi.integrableOn,
    integral_const_mul, integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / (2 * Real.pi))
  unfold highFourierPair highFourierMass
  simp only [cx] at hm ⊢
  convert hm using 1 <;> ring

/-- A fixed frequency boundary has zero Lebesgue measure. -/
theorem ae_abs_ne_threshold (T : ℝ) : ∀ᵐ t : ℝ, |t| ≠ T := by
  have hpos : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff]
  have hneg : ∀ᵐ t : ℝ, t ≠ -T := by simp [ae_iff]
  filter_upwards [hpos, hneg] with t ht hnt
  intro he
  rcases le_total 0 t with h | h
  · exact ht ((abs_of_nonneg h).symm.trans he)
  · exact hnt (by rw [abs_of_nonpos h] at he; linarith only [he])

private theorem sq_integral_re_mul_conj_le {F E : ℝ → ℂ}
    (hFm : AEStronglyMeasurable F) (hEm : AEStronglyMeasurable E)
    (hF : Integrable (fun t => ‖F t‖ ^ 2)) (hE : Integrable (fun t => ‖E t‖ ^ 2)) :
    (∫ t, (F t * conj (E t)).re) ^ 2 ≤
      (∫ t, ‖F t‖ ^ 2) * ∫ t, ‖E t‖ ^ 2 := by
  have hprod := HTGeometry.integrable_mul_of_sq_integrable hFm.norm hEm.norm hF hE
  have hpoint (t : ℝ) : |(F t * conj (E t)).re| ≤ ‖F t‖ * ‖E t‖ := by
    simpa only [norm_mul, Complex.norm_conj] using Complex.abs_re_le_norm (F t * conj (E t))
  have hint : Integrable (fun t => (F t * conj (E t)).re) :=
    hprod.mono' (hFm.mul (Complex.continuous_conj.comp_aestronglyMeasurable hEm)).re
      (Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using hpoint t)
  have hb : |∫ t, (F t * conj (E t)).re| ≤ ∫ t, ‖F t‖ * ‖E t‖ :=
    (abs_integral_le_integral_abs).trans (integral_mono hint.abs hprod hpoint)
  have hs := HTGeometry.sq_integral_mul_le hFm.norm hEm.norm hF hE
  have hb2 : (∫ t, (F t * conj (E t)).re) ^ 2 ≤ (∫ t, ‖F t‖ * ‖E t‖) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  exact hb2.trans hs

/-- The low-frequency pairing error is controlled by the squared Fourier approximation error. -/
theorem sq_highFourierPair_sub_mass_le {f g h : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (T m : ℝ) :
    (highFourierPair f g T - ((∫ u, f u * g u) - m * ∫ u, f u * h u)) ^ 2 ≤
      (∫ u, f u ^ 2) / (2 * Real.pi) *
        ∫ t : ℝ, ‖(if |t| ≤ T then paperFT (cx g) t else 0) -
          (m : ℂ) * paperFT (cx h) t‖ ^ 2 := by
  let F : ℝ → ℂ := fun t => paperFT (cx f) t
  let G : ℝ → ℂ := fun t => paperFT (cx g) t
  let H : ℝ → ℂ := fun t => paperFT (cx h) t
  let E : ℝ → ℂ := fun t => (if |t| ≤ T then G t else 0) - (m : ℂ) * H t
  have hcont {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v) :
      Continuous (fun t : ℝ => paperFT (cx v) t) :=
    continuous_paperFT_real_of_integrable
      ((Complex.continuous_ofReal.comp hv).integrable_of_hasCompactSupport
        (hvc.comp_left Complex.ofReal_zero))
  have hFm : AEStronglyMeasurable F := (hcont hf.continuous hfc).aestronglyMeasurable
  have hGm : AEStronglyMeasurable G := (hcont hg.continuous hgc).aestronglyMeasurable
  have hHm : AEStronglyMeasurable H := (hcont hh.continuous hhc).aestronglyMeasurable
  have hset : MeasurableSet {t : ℝ | |t| ≤ T} := measurableSet_le continuous_abs.measurable measurable_const
  have hcut : (fun t => if |t| ≤ T then G t else 0) = {t : ℝ | |t| ≤ T}.indicator G := rfl
  have hEm : AEStronglyMeasurable E := by
    change AEStronglyMeasurable
      ((fun t => if |t| ≤ T then G t else 0) - fun t => (m : ℂ) * H t)
    rw [hcut]
    exact (hGm.indicator hset).sub (hHm.const_mul (m : ℂ))
  have hF : Integrable (fun t => ‖F t‖ ^ 2) := integrable_normSq_paperFT_ofReal hf hfc
  have hG : Integrable (fun t => ‖G t‖ ^ 2) := integrable_normSq_paperFT_ofReal hg hgc
  have hH : Integrable (fun t => ‖H t‖ ^ 2) := integrable_normSq_paperFT_ofReal hh hhc
  have hE : Integrable (fun t => ‖E t‖ ^ 2) := by
    apply (memLp_two_iff_integrable_sq_norm hEm).mp
    have hgLp := (memLp_two_iff_integrable_sq_norm hGm).mpr hG
    have hhLp := (memLp_two_iff_integrable_sq_norm hHm).mpr hH
    change MemLp ((fun t => if |t| ≤ T then G t else 0) - fun t => (m : ℂ) * H t) 2
    rw [hcut]
    exact (hgLp.indicator hset).sub (hhLp.const_mul (m : ℂ))
  have hfg := integrable_re_paperFT_mul_conj hf hfc hg hgc
  have hfh := integrable_re_paperFT_mul_conj hf hfc hh hhc
  have he (t : ℝ) : (F t * conj (E t)).re =
      (if |t| ≤ T then (F t * conj (G t)).re else 0) - m * (F t * conj (H t)).re := by
    have hmre : (F t * conj ((m : ℂ) * H t)).re = m * (F t * conj (H t)).re := by
      rw [map_mul, Complex.conj_ofReal,
        show F t * ((m : ℂ) * conj (H t)) = (m : ℂ) * (F t * conj (H t)) by ring,
        Complex.re_ofReal_mul]
    dsimp only [E]
    by_cases ht : |t| ≤ T
    · simp only [if_pos ht, map_sub, mul_sub, Complex.sub_re, hmre]
    · simp only [if_neg ht, map_sub, map_zero, mul_sub, mul_zero,
        Complex.sub_re, Complex.zero_re, hmre]
  have heint : (∫ t, (F t * conj (E t)).re) =
      (∫ t in (highFrequencies T)ᶜ, (F t * conj (G t)).re) -
        m * ∫ t, (F t * conj (H t)).re := by
    simp_rw [he]
    have hind : (fun t => if |t| ≤ T then (F t * conj (G t)).re else 0) =ᵐ[volume]
        (highFrequencies T)ᶜ.indicator (fun t => (F t * conj (G t)).re) := by
      filter_upwards [ae_abs_ne_threshold T] with t ht
      simp only [Set.indicator, Set.mem_compl_iff, highFrequencies, Set.mem_setOf_eq]
      have hiff : (|t| ≤ T) ↔ (¬ T ≤ |t|) := by
        constructor
        · intro h
          exact not_le.mpr (lt_of_le_of_ne h ht)
        · intro h
          exact (lt_of_not_ge h).le
      simp only [hiff]
    rw [integral_sub ((hfg.indicator (measurableSet_highFrequencies T).compl).congr hind.symm)
      (hfh.const_mul m), integral_congr_ae hind,
      integral_indicator (measurableSet_highFrequencies T).compl, integral_const_mul]
  have hsplit := integral_add_compl (measurableSet_highFrequencies T) hfg
  have hplfg := integral_mul_eq_paperFT_re hf hfc hg hgc
  have hplfh := integral_mul_eq_paperFT_re hf hfc hh hhc
  have hpair : highFourierPair f g T - ((∫ u, f u * g u) - m * ∫ u, f u * h u) =
      -(1 / (2 * Real.pi)) * ∫ t, (F t * conj (E t)).re := by
    rw [heint, hplfg, hplfh]
    unfold highFourierPair
    change _ = -(1 / (2 * Real.pi)) *
      ((∫ t in (highFrequencies T)ᶜ, (paperFT (cx f) t * conj (paperFT (cx g) t)).re) - _)
    rw [← hsplit]
    ring
  have hpl := lowFourierMass_add_highFourierMass hf hfc T
  have hfull : 1 / (2 * Real.pi) * (∫ t, ‖F t‖ ^ 2) = ∫ u, f u ^ 2 := by
    rw [← integral_add_compl (measurableSet_highFrequencies T) hF, mul_add]
    exact (add_comm _ _).trans hpl
  rw [hpair, mul_pow, neg_sq]
  have hcs := sq_integral_re_mul_conj_le hFm hEm hF hE
  refine (mul_le_mul_of_nonneg_left hcs (sq_nonneg _)).trans_eq ?_
  rw [← hfull]
  dsimp only [E, G, H]
  ring

#print axioms two_mul_scalar_highFourierPair_sub_le
#print axioms sq_highFourierPair_sub_mass_le
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
