import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyMellinSymbol

/-! Real Cauchy averaging has a strictly contractive central Mellin multiplier.
Its deficit from one is half the squared discrepancy between the square roots
of its two unit densities. The actual integral bounds every central frequency. -/

open Complex Set MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRealCauchyContraction

/-- Positive real normalization of the Cauchy density. -/
def normalizer (r : ℝ) : ℝ :=
  Real.sqrt Real.pi*Real.Gamma ((r+1)/2)/Real.Gamma ((r+2)/2)/2

/-- Probability density whose two unit moments normalize Cauchy averaging. -/
def density (r t : ℝ) : ℝ := (1+t^2)^(-((r+2)/2))/normalizer r

private theorem normalizer_pos {r : ℝ} (hr : 0 < r) : 0 < normalizer r := by
  exact div_pos (div_pos (mul_pos (Real.sqrt_pos.mpr Real.pi_pos)
    (Real.Gamma_pos_of_pos (by linarith only [hr])))
    (Real.Gamma_pos_of_pos (by linarith only [hr]))) (by norm_num)

/-- The actual complex normalization is positive real at real positive parameters. -/
theorem averagingFactor_ofReal (r : ℝ) : averagingFactor r=(normalizer r : ℂ) := by
  have ha : ((r : ℂ)+2)/2=(((r+2)/2 : ℝ) : ℂ) := by push_cast; rfl
  have hb : ((r : ℂ)+2)/2-1/2=(((r+1)/2 : ℝ) : ℂ) := by push_cast; ring
  have hp : (Real.pi : ℂ)^(1/2 : ℂ)=(Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow Real.pi_pos.le,ofReal_div,ofReal_one,ofReal_ofNat]
  rw [averagingFactor,MayerScatteringNormalization.archimedeanFactor,hb,ha,
    Gamma_ofReal,Gamma_ofReal,hp]
  simp only [normalizer,ofReal_div,ofReal_mul,ofReal_ofNat]

/-- Positivity of the density is pointwise, not merely almost everywhere. -/
theorem density_pos {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 < density r t :=
  div_pos (Real.rpow_pos_of_pos (by positivity) _) (normalizer_pos hr)

/-- The actual Cauchy kernel is the multiplicative density `t p_r(t)`. -/
theorem cauchyKernel_ofReal (r t : ℝ) : cauchyKernel r t=((t*density r t : ℝ) : ℂ) := by
  have he : -(((r : ℂ)+2)/2)=((-((r+2)/2 : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [cauchyKernel,averagingFactor_ofReal,cauchyWeight,he,
    ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 1+t^2)]
  simp only [density,ofReal_mul,div_eq_mul_inv,ofReal_inv]
  ring

private theorem moment_integrand (r α : ℝ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ)^((α : ℂ)-1) • cauchyKernel r t=((t^α*density r t : ℝ) : ℂ) := by
  have he : (α : ℂ)-1=((α-1 : ℝ) : ℂ) := by push_cast; rfl
  have hp : t^(α-1)*t=t^α := by
    calc
      _ = t^(α-1)*t^(1 : ℝ) := by rw [Real.rpow_one]
      _ = t^((α-1)+1) := (Real.rpow_add ht _ _).symm
      _ = _ := by rw [sub_add_cancel]
  rw [he,← Complex.ofReal_cpow ht.le,cauchyKernel_ofReal]
  simp only [smul_eq_mul,← ofReal_mul]
  congr 1
  rw [← mul_assoc,hp]

private theorem moment_integrable {r α : ℝ} (hr : 0 < r)
    (hα : -1 < α) (hαr : α < r+1) :
    IntegrableOn (fun t : ℝ => t^α*density r t) (Ioi 0) := by
  have h := (cauchyKernel_hasMellin (w := (r : ℂ)) (u := (α : ℂ))
    (by simpa only [ofReal_re] using hr) (by simpa only [ofReal_re] using hα)
    (by simpa only [ofReal_re] using hαr)).1
  have hi : IntegrableOn (fun t : ℝ => ((t : ℂ)^((α : ℂ)-1) • cauchyKernel r t).re) (Ioi 0) := h.re
  exact MeasureTheory.IntegrableOn.congr_fun hi
    (fun t ht => by rw [moment_integrand r α ht,ofReal_re]) measurableSet_Ioi

private theorem moment_integral (r α : ℝ) :
    (∫ t in Ioi (0 : ℝ), t^α*density r t)=(mellin (cauchyKernel r) α).re := by
  have he : mellin (cauchyKernel r) α=
      ((∫ t in Ioi (0 : ℝ), t^α*density r t : ℝ) : ℂ) := by
    rw [mellin,setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => moment_integrand r α ht),integral_complex_ofReal]
  rw [he,ofReal_re]

/-- The real Cauchy density has total mass one. -/
theorem density_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), density r t)=1 := by
  have h := moment_integral r 0
  simpa only [Real.rpow_zero,one_mul,ofReal_zero,
    (cauchyKernel_mellin_zero (w := (r : ℂ)) hr).2,one_re] using h

/-- Inversion produces the second unit moment of the real density. -/
theorem spectral_moment_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), t^r*density r t)=1 := by
  rw [moment_integral,(cauchyKernel_mellin_spectral (w := (r : ℂ)) hr).2,one_re]

/-- The midpoint moment is exactly the zero-frequency central multiplier. -/
theorem central_moment_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), t^(r/2)*density r t)=centralSymbol r 0 := by
  have h := (cauchyKernel_central_hasMellin hr 0).2
  simp only [ofReal_zero,zero_mul,add_zero] at h
  rw [moment_integral,ofReal_div,ofReal_ofNat,h,ofReal_re]

/-- The uniform frequency bound is an explicit quotient of positive real Gamma values. -/
theorem centralSymbol_zero (r : ℝ) :
    centralSymbol r 0=Real.Gamma ((r+2)/4)^2/
      (Real.sqrt Real.pi*Real.Gamma ((r+1)/2)) := by
  simp only [centralSymbol,ofReal_zero,zero_div,zero_mul,add_zero,Gamma_ofReal,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Squared discrepancy between the square roots of the two unit densities. -/
def energy (r t : ℝ) : ℝ := (t^(r/2)-1)^2*density r t

private theorem energy_expand (r : ℝ) {t : ℝ} (ht : 0 < t) :
    energy r t=t^r*density r t-2*(t^(r/2)*density r t)+density r t := by
  have hp : (t^(r/2))^2=t^r := by
    rw [pow_two,← Real.rpow_add ht]
    congr 1
    ring
  rw [energy,sub_sq,hp]
  ring

/-- The squared discrepancy is integrable because all three Mellin moments converge. -/
theorem energy_integrable {r : ℝ} (hr : 0 < r) : IntegrableOn (energy r) (Ioi 0) := by
  have h0 : IntegrableOn (density r) (Ioi 0) := by
    simpa only [Real.rpow_zero,one_mul] using moment_integrable hr (α := 0) (by norm_num) (by linarith)
  have hs := moment_integrable hr (α := r) (by linarith only [hr]) (by linarith)
  have hc := moment_integrable hr (α := r/2) (by linarith only [hr]) (by linarith only [hr])
  exact MeasureTheory.IntegrableOn.congr_fun ((hs.sub (hc.const_mul 2)).add h0)
    (fun t ht => (energy_expand r ht).symm) measurableSet_Ioi

/-- Exact energy identity for the deficit of the central multiplier from one. -/
theorem energy_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), energy r t)=2*(1-centralSymbol r 0) := by
  have h0 : IntegrableOn (density r) (Ioi 0) := by
    simpa only [Real.rpow_zero,one_mul] using moment_integrable hr (α := 0) (by norm_num) (by linarith)
  have hs := moment_integrable hr (α := r) (by linarith only [hr]) (by linarith)
  have hc := moment_integrable hr (α := r/2) (by linarith only [hr]) (by linarith only [hr])
  have htw : IntegrableOn (fun t : ℝ => 2*(t^(r/2)*density r t)) (Ioi 0) := hc.const_mul 2
  have hsub : IntegrableOn (fun t : ℝ => t^r*density r t-2*(t^(r/2)*density r t)) (Ioi 0) :=
    hs.sub htw
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => energy_expand r ht),
    integral_add hsub h0,integral_sub hs htw,
    integral_const_mul,spectral_moment_integral hr,central_moment_integral hr,density_integral hr]
  ring

/-- A nonconstant power makes the squared discrepancy strictly positive on `(2,3)`. -/
theorem energy_integral_pos {r : ℝ} (hr : 0 < r) :
    0 < ∫ t in Ioi (0 : ℝ), energy r t := by
  have hnn : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), 0 ≤ energy r t :=
    Filter.Eventually.of_forall (fun t => mul_nonneg (sq_nonneg _) (density_pos hr t).le)
  rw [integral_pos_iff_support_of_nonneg_ae hnn (energy_integrable hr)]
  have hsub : Ioo (2 : ℝ) 3 ⊆ Function.support (energy r) := by
    intro t ht
    have ht1 : 1 < t := by linarith only [ht.1]
    have hp : 1 < t^(r/2) := Real.one_lt_rpow ht1 (by linarith only [hr])
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hp))) (density_pos hr t).ne'
  have hval : (volume.restrict (Ioi (0 : ℝ))) (Ioo (2 : ℝ) 3)=1 := by
    have hsub0 : Ioo (2 : ℝ) 3 ⊆ Ioi (0 : ℝ) :=
      fun t ht => lt_trans (by norm_num : (0 : ℝ)<2) ht.1
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr hsub0,Real.volume_Ioo]
    norm_num
  have hm := measure_mono (μ := volume.restrict (Ioi (0 : ℝ))) hsub
  rw [hval] at hm
  exact lt_of_lt_of_le zero_lt_one hm

/-- The real central multiplier is strictly below one, with no frequency restriction. -/
theorem centralSymbol_zero_lt_one {r : ℝ} (hr : 0 < r) : centralSymbol r 0 < 1 := by
  have hp := energy_integral_pos hr
  rw [energy_integral hr] at hp
  linarith only [hp]

/-- The modulus-one oscillation in the actual Mellin integral cannot increase its value. -/
theorem centralSymbol_le_zero {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    centralSymbol r ξ ≤ centralSymbol r 0 := by
  have hξ := (cauchyKernel_central_hasMellin hr ξ).2
  calc
    centralSymbol r ξ = ‖mellin (cauchyKernel r) ((r : ℂ)/2+(ξ : ℂ)*I)‖ := by
      rw [hξ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (centralSymbol_pos hr ξ)]
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖(t : ℂ)^(((r : ℂ)/2+(ξ : ℂ)*I)-1) • cauchyKernel r t‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (0 : ℝ), t^(r/2)*density r t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have he : (((r : ℂ)/2+(ξ : ℂ)*I)-1).re=r/2-1 := by simp
      have hp : t^(r/2-1)*t=t^(r/2) := by
        calc
          _ = t^(r/2-1)*t^(1 : ℝ) := by rw [Real.rpow_one]
          _ = t^((r/2-1)+1) := (Real.rpow_add ht _ _).symm
          _ = _ := by rw [sub_add_cancel]
      dsimp only
      rw [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos ht,he,cauchyKernel_ofReal,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mul_pos ht (density_pos hr t)),← mul_assoc,hp]
    _ = centralSymbol r 0 := central_moment_integral hr

/-- Positive central multipliers obey one explicit strict contraction bound at every frequency. -/
theorem centralSymbol_bounds {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    0 < centralSymbol r ξ ∧ centralSymbol r ξ ≤ centralSymbol r 0 ∧ centralSymbol r 0 < 1 :=
  ⟨centralSymbol_pos hr ξ,centralSymbol_le_zero hr ξ,centralSymbol_zero_lt_one hr⟩

#print axioms averagingFactor_ofReal
#print axioms density_pos
#print axioms cauchyKernel_ofReal
#print axioms density_integral
#print axioms spectral_moment_integral
#print axioms central_moment_integral
#print axioms centralSymbol_zero
#print axioms energy_integrable
#print axioms energy_integral
#print axioms energy_integral_pos
#print axioms centralSymbol_zero_lt_one
#print axioms centralSymbol_le_zero
#print axioms centralSymbol_bounds

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerRealCauchyContraction
