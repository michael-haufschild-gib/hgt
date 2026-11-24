import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.VisibilityThreshold.Local
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.Sharpness
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-! # The sharp global visibility of finite exact factors and the pole of the gas partition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology InverseSpectrum.ShellMixing

/-- Thermal visibilities of finite independent factors, with arbitrary finite prime support. -/
def allFiniteVisibilities (s : ℂ) : Set ℝ := {v | ∃ P, v ∈ attainedVisibilities P s}

/-- Normalized modulus of the full partition on the Gibbs half-plane. -/
def partitionVisibility (s : ℂ) := ‖riemannZeta s‖/‖riemannZeta (s.re:ℂ)‖

theorem envelope_limit_over_primes {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun P : Finset Nat.Primes => eulerEnvelope P s) atTop (𝓝 (partitionVisibility s)) := by
  have hEuler (w : ℂ) (hw : 1 < w.re) :
      Tendsto (fun P : Finset Nat.Primes => RHTower.thetaEulerStageZeta (primeWindow P) w) atTop (𝓝 (riemannZeta w)) := by
    have he := riemannZeta_eulerProduct_hasProd hw
    change Tendsto (fun P : Finset Nat.Primes => ∏ p ∈ P, (1-(p.val:ℂ)^(-w))⁻¹) atTop (𝓝 (riemannZeta w)) at he
    apply he.congr
    intro P
    simp only [RHTower.thetaEulerStageZeta,primeWindow,Finset.prod_map]
    rfl
  simp only [euler_normalization]
  exact (hEuler s hs).norm.div (hEuler (s.re:ℂ) hs).norm
    (norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (s := (s.re:ℂ)) hs))

private theorem le_window_of_lower_bound {s : ℂ} (hs : 0 < s.re) {c : ℝ}
    (hc : c ∈ lowerBounds (allFiniteVisibilities s)) (P : Finset Nat.Primes) : c ≤ eulerEnvelope P s :=
  (visibility_isGLB P hs).2 (fun _ hv => hc ⟨P,hv⟩)

/-- On the Gibbs half-plane the entire partition gives the infimum over finite exact subsystems. -/
theorem global_visibility_above_one {s : ℂ} (hs : 1 < s.re) :
    IsGLB (allFiniteVisibilities s) (partitionVisibility s) := by
  have hpos := zero_lt_one.trans hs
  constructor
  · rintro v ⟨P,hv⟩
    apply le_trans _ ((visibility_isGLB P hpos).1 hv)
    exact le_of_tendsto (envelope_limit_over_primes hs)
      ((eventually_ge_atTop P).mono (fun Q hQ => envelope_antitone_window hQ hpos))
  · intro c hc
    exact ge_of_tendsto (envelope_limit_over_primes hs) (Eventually.of_forall (le_window_of_lower_bound hpos hc))

/-- At nonzero time the numerator stays regular as the real partition diverges at its simple pole. -/
theorem partitionVisibility_tendsto_zero {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun σ : ℝ => partitionVisibility (thermalPoint σ t)) (𝓝[>] 1) (𝓝 0) := by
  have hreal : Tendsto (fun σ : ℝ => (σ:ℂ)) (𝓝[>] 1) (𝓝 1) := by
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hpunct : Tendsto (fun σ : ℝ => (σ:ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hreal,?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    intro he
    change (σ:ℂ) = 1 at he
    exact hσ.ne' (by exact_mod_cast he)
  have hshift : Tendsto (fun σ => thermalPoint σ t) (𝓝[>] 1) (𝓝 (thermalPoint 1 t)) := by
    simpa only [thermalPoint,Complex.ofReal_one] using hreal.add (tendsto_const_nhds (x := (t:ℂ)*Complex.I))
  have ht' : thermalPoint 1 t ≠ 1 := fun he => ht (by simpa using congrArg Complex.im he)
  have hnum := (differentiableAt_riemannZeta ht').continuousAt.tendsto.comp hshift
  have hden := riemannZeta_residue_one.comp hpunct
  have hlim := (((hreal.sub_const 1).mul hnum).div hden one_ne_zero).norm
  simp only [sub_self,zero_mul,zero_div,norm_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have hne : (σ:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (fun he => hσ.ne' (by exact_mod_cast he))
  change ‖(((σ:ℂ)-1)*riemannZeta (thermalPoint σ t))/(((σ:ℂ)-1)*riemannZeta (σ:ℂ))‖ = _
  rw [mul_div_mul_left _ _ hne,norm_div,partitionVisibility,thermalPoint_re]

/-- At and below the pole, finite subsystems have arbitrarily small visibility at every fixed nonzero time. -/
theorem global_visibility_at_or_below_one {β t : ℝ} (hβ : 0 < β) (h1 : β ≤ 1) (ht : t ≠ 0) :
    IsGLB (allFiniteVisibilities (thermalPoint β t)) 0 := by
  constructor
  · rintro v ⟨P,A,B,h,ha,rfl⟩
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro c hc
    apply ge_of_tendsto (partitionVisibility_tendsto_zero ht)
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    apply ge_of_tendsto (envelope_limit_over_primes (s := thermalPoint σ t) (by simpa using hσ))
    refine Eventually.of_forall (fun P => ?_)
    exact (le_window_of_lower_bound (s := thermalPoint β t) (by simpa using hβ) hc P).trans
      (envelope_mono_temperature P t hβ (h1.trans hσ.le))

theorem finite_visibility_pos {s : ℂ} (hs : 0 < s.re) {v : ℝ} (hv : v ∈ allFiniteVisibilities s) : 0 < v := by
  obtain ⟨_,A,B,h,_,rfl⟩ := hv
  exact div_pos (norm_pos_iff.mpr (finiteSubsystem_zero_free h hs))
    (norm_pos_iff.mpr (finiteSubsystem_zero_free h (s := (s.re:ℂ)) hs))

#print axioms envelope_limit_over_primes
#print axioms global_visibility_above_one
#print axioms partitionVisibility_tendsto_zero
#print axioms global_visibility_at_or_below_one
#print axioms finite_visibility_pos

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
