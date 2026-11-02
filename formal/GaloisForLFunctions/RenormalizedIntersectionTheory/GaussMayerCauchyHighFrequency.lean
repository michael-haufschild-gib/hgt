import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCauchyMellinSymbol
import GaloisForLFunctions.HTGeometry.GammaShiftRatioGeneral

/-! The actual Cauchy multiplier has a sharp high-frequency threshold at
real part one. Duplication separates an exponential factor from a balanced
Gamma quotient whose vertical asymptotic is one, independently of Mellin weight. -/

open Complex Set Filter
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone MayerCauchyMellinSymbol
open scoped Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyHighFrequency

private theorem balanced_gamma_ratio {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hs : a+b=c+d) :
    Tendsto (fun t : ℝ => gammaLine a t*gammaLine b t/(gammaLine c t*gammaLine d t))
      atTop (𝓝 1) := by
  have hA := tendsto_gammaShift_ratio_general (σ := c) (lam := a-c) hc (by linarith only [ha])
  have hB := tendsto_gammaShift_ratio_general (σ := c) (lam := b-c) hc (by linarith only [hb])
  have hD := tendsto_gammaShift_ratio_general (σ := c) (lam := d-c) hc (by linarith only [hd])
  rw [show c+(a-c)=a by ring] at hA
  rw [show c+(b-c)=b by ring] at hB
  rw [show c+(d-c)=d by ring] at hD
  have h := (hA.mul hB).div hD one_ne_zero
  simp only [one_mul,div_one] at h
  refine h.congr (fun t => ?_)
  have hz : (c : ℂ)+(t : ℂ)*I ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re,ofReal_re,mul_I_re,ofReal_im,zero_re] at hr
    linarith only [hc,hr]
  have hpA : ((c : ℂ)+(t : ℂ)*I)^((a-c : ℝ) : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hz)
  have hpB : ((c : ℂ)+(t : ℂ)*I)^((b-c : ℝ) : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hz)
  have hp : ((c : ℂ)+(t : ℂ)*I)^((a-c : ℝ) : ℂ)*
      ((c : ℂ)+(t : ℂ)*I)^((b-c : ℝ) : ℂ)=
      ((c : ℂ)+(t : ℂ)*I)^((d-c : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hz,← ofReal_add,show (a-c)+(b-c)=d-c by linarith only [hs]]
  dsimp only [Pi.div_apply]
  rw [← hp]
  field_simp [gammaLine_ne_zero hc t,gammaLine_ne_zero hd t]

/-- Duplication isolates the exponential spectral factor from a balanced Gamma quotient. -/
theorem symbol_duplication {w : ℂ} (hw : 0 < w.re) (u : ℂ) :
    symbol w u=(2 : ℂ)^((1-w)/2)*
      (Gamma ((u+1)/2)*Gamma ((w+1-u)/2)/
        (Gamma ((w+1)/4)*Gamma ((w+3)/4))) := by
  have hd := Complex.Gamma_mul_Gamma_add_half ((w+1)/4)
  have hp : (Real.sqrt Real.pi : ℂ)=(Real.pi : ℂ)^(1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow Real.pi_pos.le,ofReal_div,ofReal_one,ofReal_ofNat]
  rw [show (w+1)/4+1/2=(w+3)/4 by ring,
    show 2*((w+1)/4)=(w+1)/2 by ring,
    show 1-(w+1)/2=(1-w)/2 by ring,hp] at hd
  have hG : Gamma ((w+1)/2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have he := congrArg Complex.re hn
    have hre : 0 < ((w+1)/2).re := by simp; linarith only [hw]
    simp only [neg_re,natCast_re] at he
    linarith only [he,hre,Nat.cast_nonneg (α := ℝ) n]
  have hpi : (Real.pi : ℂ)^(1/2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have htwo : (2 : ℂ)^((1-w)/2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [symbol,hd]
  field_simp

#print axioms symbol_duplication
/-- At half the spectral frequency, the exponential factor has constant modulus. -/
theorem norm_symbol_vertical {σ : ℝ} (hσ : 0 < σ) (α τ : ℝ) :
    ‖symbol ((σ : ℂ)+(τ : ℂ)*I) ((α : ℂ)+(τ : ℂ)/2*I)‖=
      (2 : ℝ)^((1-σ)/2)*
        ‖gammaLine ((α+1)/2) (τ/4)*gammaLine ((σ+1-α)/2) (τ/4)/
          (gammaLine ((σ+1)/4) (τ/4)*gammaLine ((σ+3)/4) (τ/4))‖ := by
  have hw : 0 < ((σ : ℂ)+(τ : ℂ)*I).re := by simpa using hσ
  have hre : ((1-((σ : ℂ)+(τ : ℂ)*I))/2).re=(1-σ)/2 := by simp
  have ha : (((α : ℂ)+(τ : ℂ)/2*I)+1)/2=
      (((α+1)/2 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I := by push_cast; ring
  have hb : (((σ : ℂ)+(τ : ℂ)*I)+1-((α : ℂ)+(τ : ℂ)/2*I))/2=
      (((σ+1-α)/2 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I := by push_cast; ring
  have hc : (((σ : ℂ)+(τ : ℂ)*I)+1)/4=
      (((σ+1)/4 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I := by push_cast; ring
  have hd : (((σ : ℂ)+(τ : ℂ)*I)+3)/4=
      (((σ+3)/4 : ℝ) : ℂ)+((τ/4 : ℝ) : ℂ)*I := by push_cast; ring
  have hn : ‖(2 : ℂ)^((1-((σ : ℂ)+(τ : ℂ)*I))/2)‖=(2 : ℝ)^((1-σ)/2) := by
    simpa only [ofReal_ofNat,hre] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ)<2)
        ((1-((σ : ℂ)+(τ : ℂ)*I))/2)
  rw [symbol_duplication hw,norm_mul,hn,ha,hb,hc,hd]
  rfl

private theorem tendsto_quarter : Tendsto (fun τ : ℝ => τ/4) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (4*b)] with τ hτ
  linarith only [hτ]

/-- The balanced Gamma arguments have equal sums, so their power asymptotics cancel. -/
theorem tendsto_norm_symbol {σ α : ℝ} (hσ : 0 < σ)
    (hα : -1 < α) (hασ : α < σ+1) :
    Tendsto (fun τ : ℝ => ‖symbol ((σ : ℂ)+(τ : ℂ)*I) ((α : ℂ)+(τ : ℂ)/2*I)‖)
      atTop (𝓝 ((2 : ℝ)^((1-σ)/2))) := by
  have ha : 0 < (α+1)/2 := by linarith only [hα]
  have hb : 0 < (σ+1-α)/2 := by linarith only [hασ]
  have hc : 0 < (σ+1)/4 := by linarith only [hσ]
  have hd : 0 < (σ+3)/4 := by linarith only [hσ]
  have hs : (α+1)/2+(σ+1-α)/2=(σ+1)/4+(σ+3)/4 := by ring
  have h := (balanced_gamma_ratio ha hb hc hd hs).comp tendsto_quarter
  have hn := (tendsto_const_nhds (x := (2 : ℝ)^((1-σ)/2))).mul h.norm
  simp only [norm_one,mul_one] at hn
  exact hn.congr (fun τ => (norm_symbol_vertical hσ α τ).symm)

/-- These spectral-frequency values are actual absolutely convergent Mellin integrals. -/
theorem vertical_hasMellin {σ α : ℝ} (hσ : 0 < σ)
    (hα : -1 < α) (hασ : α < σ+1) (τ : ℝ) :
    HasMellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I)) ((α : ℂ)+(τ : ℂ)/2*I)
      (symbol ((σ : ℂ)+(τ : ℂ)*I) ((α : ℂ)+(τ : ℂ)/2*I)) := by
  apply cauchyKernel_hasMellin
  · simpa using hσ
  · simpa using hα
  · simpa using hασ

/-- The sharp actual Cauchy multiplier limit is independent of the fixed real Mellin weight. -/
theorem tendsto_norm_mellin {σ α : ℝ} (hσ : 0 < σ)
    (hα : -1 < α) (hασ : α < σ+1) :
    Tendsto (fun τ : ℝ => ‖mellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I))
      ((α : ℂ)+(τ : ℂ)/2*I)‖) atTop (𝓝 ((2 : ℝ)^((1-σ)/2))) := by
  refine (tendsto_norm_symbol hσ hα hασ).congr (fun τ => ?_)
  rw [(vertical_hasMellin hσ hα hασ τ).2]

/-- Every fixed source abscissa below one amplifies at all sufficiently large heights. -/
theorem eventually_amplifying {σ α : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hα : -1 < α) (hασ : α < σ+1) :
    ∀ᶠ τ : ℝ in atTop, 1 < ‖mellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I))
      ((α : ℂ)+(τ : ℂ)/2*I)‖ := by
  have hc : (2 : ℝ)^((1-σ)/2) ∈ Ioi (1 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by linarith only [hσ1])
  exact (tendsto_norm_mellin hσ hα hασ).eventually (isOpen_Ioi.mem_nhds hc)

/-- Above abscissa one, this frequency family is eventually strictly contractive. -/
theorem eventually_contractive {σ α : ℝ} (hσ : 1 < σ)
    (hα : -1 < α) (hασ : α < σ+1) :
    ∀ᶠ τ : ℝ in atTop, ‖mellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I))
      ((α : ℂ)+(τ : ℂ)/2*I)‖ < 1 := by
  have hc : (2 : ℝ)^((1-σ)/2) ∈ Iio (1 : ℝ) :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hσ])
  exact (tendsto_norm_mellin (by linarith only [hσ]) hα hασ).eventually (isOpen_Iio.mem_nhds hc)

/-- The threshold abscissa has limiting modulus exactly one. -/
theorem tendsto_norm_mellin_one {α : ℝ} (hα : -1 < α) (hα2 : α < 2) :
    Tendsto (fun τ : ℝ => ‖mellin (cauchyKernel ((1 : ℂ)+(τ : ℂ)*I))
      ((α : ℂ)+(τ : ℂ)/2*I)‖) atTop (𝓝 1) := by
  simpa only [ofReal_one,sub_self,zero_div,Real.rpow_zero] using
    tendsto_norm_mellin (σ := 1) (by norm_num) hα (by linarith only [hα2])

/-- No height cutoff restores the multiplier contraction estimate below abscissa one. -/
theorem exists_amplifying_above {σ α : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (hα : -1 < α) (hασ : α < σ+1) (T : ℝ) :
    ∃ τ : ℝ, T < τ ∧
      MellinConvergent (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I)) ((α : ℂ)+(τ : ℂ)/2*I) ∧
      1 < ‖mellin (cauchyKernel ((σ : ℂ)+(τ : ℂ)*I)) ((α : ℂ)+(τ : ℂ)/2*I)‖ := by
  obtain ⟨τ,hT,hamp⟩ := ((eventually_gt_atTop T).and (eventually_amplifying hσ hσ1 hα hασ)).exists
  exact ⟨τ,hT,(vertical_hasMellin hσ hα hασ τ).1,hamp⟩

#print axioms norm_symbol_vertical
#print axioms tendsto_norm_symbol
#print axioms vertical_hasMellin
#print axioms tendsto_norm_mellin
#print axioms eventually_amplifying
#print axioms eventually_contractive
#print axioms tendsto_norm_mellin_one
#print axioms exists_amplifying_above

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyHighFrequency
