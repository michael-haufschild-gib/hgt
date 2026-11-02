import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyMellinSymbol
import GaloisForLFunctions.RHTower.SeamVerticalDecay
import GaloisForLFunctions.RHTower.FiniteLevelResolutionLaw

/-! Gamma reflection gives the exact Cauchy multiplier norm on the imaginary
spectral boundary. Its amplification persists at actual source parameters
with arbitrarily small positive real part and absolutely convergent Mellin integrals. -/

open Complex Set Filter
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyBoundaryAmplification

private theorem reflected_gamma_norm (z : ℂ) :
    ‖Gamma z*Gamma (1-(starRingEnd ℂ) z)‖=
      Real.pi/‖Complex.sin ((Real.pi : ℂ)*z)‖ := by
  have he : 1-(starRingEnd ℂ) z=(starRingEnd ℂ) (1-z) := by rw [map_sub,map_one]
  rw [he,Gamma_conj,norm_mul,Complex.norm_conj,← norm_mul,Gamma_mul_Gamma_one_sub,
    norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]

private theorem sine_norm_sq (α τ : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ)*
      ((((α+1)/2 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I))‖^2=
      Real.cos (Real.pi*α/2)^2+Real.sinh (Real.pi*τ/4)^2 := by
  have he : (Real.pi : ℂ)*((((α+1)/2 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I)=
      ((Real.pi/2 : ℝ) : ℂ)+(((Real.pi*α/2 : ℝ) : ℂ)+((Real.pi*τ/4 : ℝ) : ℂ)*I) := by
    push_cast
    ring
  rw [he,Complex.sin_add,← Complex.ofReal_sin,← Complex.ofReal_cos,
    Real.sin_pi_div_two,Real.cos_pi_div_two]
  simp only [ofReal_one,ofReal_zero,one_mul,zero_mul,add_zero]
  rw [_root_.RHTower.norm_cos_sq]
  simp

/-- Exact norm of the Gamma multiplier on the imaginary spectral boundary. -/
theorem symbol_boundary_norm_sq (α τ : ℝ) :
    ‖symbol ((τ : ℂ)*I) ((α : ℂ)+(τ : ℂ)/2*I)‖^2=
      Real.cosh (Real.pi*τ/2)/
        (Real.cos (Real.pi*α/2)^2+Real.sinh (Real.pi*τ/4)^2) := by
  have ha : (((α : ℂ)+(τ : ℂ)/2*I)+1)/2=
      (((α+1)/2 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I := by push_cast; ring
  have hb : ((τ : ℂ)*I+1-((α : ℂ)+(τ : ℂ)/2*I))/2=
      1-(starRingEnd ℂ) ((((α+1)/2 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I) := by
    simp only [map_add,map_mul,conj_ofReal,conj_I]
    push_cast
    ring
  have hd : ((τ : ℂ)*I+1)/2=(1 : ℂ)/2+((τ/2 : ℝ) : ℂ)*I := by push_cast; ring
  have hpi : ‖(Real.pi : ℂ)^(1/2 : ℂ)‖^2=Real.pi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (1/2 : ℂ).re=(1/2 : ℝ) := by norm_num
    rw [hre,← Real.sqrt_eq_rpow,Real.sq_sqrt Real.pi_pos.le]
  have hc : 0 < Real.cosh (Real.pi*τ/2) := Real.cosh_pos _
  have hg : ‖Gamma ((1 : ℂ)/2+((τ/2 : ℝ) : ℂ)*I)‖^2=
      Real.pi/Real.cosh (Real.pi*τ/2) := by
    apply (eq_div_iff hc.ne').mpr
    have he : Real.pi*(τ/2)=Real.pi*τ/2 := by ring
    simpa only [he] using _root_.RHTower.norm_Gamma_half_add_sq (τ/2)
  rw [symbol,ha,hb,hd,norm_div,reflected_gamma_norm,div_pow,div_pow,
    sine_norm_sq,norm_mul,mul_pow,hpi,hg]
  by_cases hS : Real.cos (Real.pi*α/2)^2+Real.sinh (Real.pi*τ/4)^2=0
  · simp only [hS,div_zero,zero_div]
  · field_simp

/-- Every real Mellin weight amplifies at a nonzero imaginary spectral parameter. -/
theorem symbol_boundary_norm_gt_one (α : ℝ) {τ : ℝ} (hτ : τ ≠ 0) :
    1 < ‖symbol ((τ : ℂ)*I) ((α : ℂ)+(τ : ℂ)/2*I)‖ := by
  have hy : Real.pi*τ/4 ≠ 0 := div_ne_zero (mul_ne_zero Real.pi_ne_zero hτ) (by norm_num)
  have hs : 0 < Real.sinh (Real.pi*τ/4)^2 := sq_pos_of_ne_zero
    (fun h => hy (Real.sinh_eq_zero.mp h))
  have hc : Real.cosh (Real.pi*τ/2)=1+2*Real.sinh (Real.pi*τ/4)^2 := by
    have h := Real.cosh_add (Real.pi*τ/4) (Real.pi*τ/4)
    rw [show Real.pi*τ/4+Real.pi*τ/4=Real.pi*τ/2 by ring] at h
    nlinarith only [h,Real.cosh_sq (Real.pi*τ/4)]
  have hd : 0 < Real.cos (Real.pi*α/2)^2+Real.sinh (Real.pi*τ/4)^2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) hs
  have hbig : 1 < ‖symbol ((τ : ℂ)*I) ((α : ℂ)+(τ : ℂ)/2*I)‖^2 := by
    rw [symbol_boundary_norm_sq]
    apply (lt_div_iff₀ hd).mpr
    nlinarith only [hc,hs,Real.cos_sq_le_one (Real.pi*α/2)]
  nlinarith only [hbig,norm_nonneg (symbol ((τ : ℂ)*I) ((α : ℂ)+(τ : ℂ)/2*I))]

#print axioms symbol_boundary_norm_sq
#print axioms symbol_boundary_norm_gt_one
/-- At the central Mellin point the two numerator Gamma factors coincide. -/
theorem symbol_half (w : ℂ) :
    symbol w (w/2)=Gamma ((w+2)/4)^2/
      ((Real.pi : ℂ)^(1/2 : ℂ)*Gamma ((w+1)/2)) := by
  unfold symbol
  rw [show (w/2+1)/2=(w+2)/4 by ring,show (w+1-w/2)/2=(w+2)/4 by ring,pow_two]

private theorem gamma_avoids_poles {z : ℂ} (hz : 0 < z.re) : ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re,natCast_re] at h
  linarith only [hz,h,Nat.cast_nonneg (α := ℝ) n]

/-- The central Gamma quotient is holomorphic across the imaginary spectral boundary. -/
theorem differentiableAt_central {w : ℂ} (hw : -1 < w.re) :
    DifferentiableAt ℂ (fun v => symbol v (v/2)) w := by
  have hA : 0 < ((w+2)/4).re := by simp; linarith only [hw]
  have hB : 0 < ((w+1)/2).re := by simp; linarith only [hw]
  have ha := (Complex.differentiableAt_Gamma _ (gamma_avoids_poles hA)).comp w
    ((differentiableAt_id.add_const (2 : ℂ)).div_const 4)
  have hb := (Complex.differentiableAt_Gamma _ (gamma_avoids_poles hB)).comp w
    ((differentiableAt_id.add_const (1 : ℂ)).div_const 2)
  have hn : (Real.pi : ℂ)^(1/2 : ℂ)*Gamma ((w+1)/2) ≠ 0 := mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    (Complex.Gamma_ne_zero (gamma_avoids_poles hB))
  simp_rw [symbol_half]
  exact (ha.pow 2).div ((differentiableAt_const ((Real.pi : ℂ)^(1/2 : ℂ))).mul hb) hn

/-- Boundary amplification persists at actual source parameters of arbitrarily small positive
real part. The central Mellin integrals in this statement converge absolutely. -/
theorem exists_source_central_amplification {τ : ℝ} (hτ : τ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ σ < ε ∧
      MellinConvergent (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I))
        (((σ : ℂ)+(τ : ℂ)*I)/2) ∧
      1 < ‖mellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I))
        (((σ : ℂ)+(τ : ℂ)*I)/2)‖ := by
  have h0 : 1 < ‖symbol ((τ : ℂ)*I) (((τ : ℂ)*I)/2)‖ := by
    rw [show ((τ : ℂ)*I)/2=(0 : ℂ)+(τ : ℂ)/2*I by ring]
    exact symbol_boundary_norm_gt_one 0 hτ
  have hc : ContinuousAt (fun σ : ℝ =>
      ‖symbol ((σ : ℂ)+(τ : ℂ)*I) (((σ : ℂ)+(τ : ℂ)*I)/2)‖) 0 := by
    have hf := (differentiableAt_central (w := (0 : ℂ)+(τ : ℂ)*I) (by simp)).continuousAt
    have hg : ContinuousAt (fun σ : ℝ => (σ : ℂ)+(τ : ℂ)*I) 0 := by fun_prop
    exact (hf.comp (f := fun σ : ℝ => (σ : ℂ)+(τ : ℂ)*I) hg).norm
  have he : ∀ᶠ σ : ℝ in 𝓝 0,
      1 < ‖symbol ((σ : ℂ)+(τ : ℂ)*I) (((σ : ℂ)+(τ : ℂ)*I)/2)‖ :=
    hc.eventually (isOpen_Ioi.mem_nhds (by simpa only [mem_Ioi,ofReal_zero,zero_add] using h0))
  obtain ⟨δ,hδ,hδf⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨σ,hσ0,hσmax⟩ := exists_between (lt_min (lt_min hε zero_lt_one) hδ)
  have hσδ : σ < δ := (lt_min_iff.mp hσmax).2
  have hσε : σ < ε := (lt_min_iff.mp (lt_min_iff.mp hσmax).1).1
  have hσ1 : σ < 1 := (lt_min_iff.mp (lt_min_iff.mp hσmax).1).2
  have hp := hδf (y := σ) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hσ0] using hσδ)
  have hw : ((σ : ℂ)+(τ : ℂ)*I).re=σ := by simp
  have hu : (((σ : ℂ)+(τ : ℂ)*I)/2).re=σ/2 := by simp
  have hm := cauchyKernel_hasMellin (w := (σ : ℂ)+(τ : ℂ)*I)
    (u := ((σ : ℂ)+(τ : ℂ)*I)/2) (by rw [hw]; exact hσ0)
    (by rw [hu]; linarith only [hσ0]) (by rw [hu,hw]; linarith only [hσ0])
  exact ⟨σ,hσ0,hσ1,hσε,hm.1,by rw [hm.2]; exact hp⟩

/-- Central Cauchy multiplier contraction fails as a uniform claim on the source critical strip. -/
theorem not_source_central_contractivity :
    ¬ ∀ w : ℂ, 0 < w.re → w.re < 1 → ‖mellin (cauchyKernel w) (w/2)‖ ≤ 1 := by
  intro h
  obtain ⟨σ,hσ0,hσ1,_,_,hp⟩ := exists_source_central_amplification
    (τ := 1) (by norm_num) (ε := 1) (by norm_num)
  have hn := h ((σ : ℂ)+(1 : ℂ)*I) (by simpa using hσ0) (by simpa using hσ1)
  exact (not_lt_of_ge hn) hp

#print axioms symbol_half
#print axioms differentiableAt_central
#print axioms exists_source_central_amplification
#print axioms not_source_central_contractivity

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyBoundaryAmplification
