import GaloisForLFunctions.RHTower.ThetaOddCuspDerivativeFlatness
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexWard
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# Flat endpoint for the literal theta source on the imaginary arc

All complex jets needed by the Ward identity vanish at the odd cusp. The proof
uses Cauchy estimates and the exact modular bound, without numerical estimates.
The source is real on the open imaginary arc by conjugation and reflection.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.ThetaImaginaryArc

def arcEnd : ℝ := Real.pi/4

def arcOffset (t : ℝ) : ℂ := hardyAxisPoint (2*t)

theorem arcEnd_pos : 0<arcEnd := by unfold arcEnd; positivity

theorem arcOffset_eq (t : ℝ) : arcOffset t = 1+Complex.I*Complex.exp (2*((t:ℂ)*Complex.I)) := by
  have hh := I_mul_exp_axis (2*t)
  rw [show ((2*t:ℝ):ℂ)*Complex.I = 2*((t:ℂ)*Complex.I) by push_cast; ring] at hh
  dsimp [arcOffset]
  linear_combination -hh

theorem arcOffset_cone {t : ℝ} (ht : t∈Ioo 0 arcEnd) :
    0<(arcOffset t).im ∧ ‖arcOffset t‖≤2*(arcOffset t).im := by
  have hc : 0<Real.cos (2*t) := Real.cos_pos_of_mem_Ioo (by
    dsimp [arcEnd] at ht
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos])
  have hs : 0≤Real.sin (2*t) := Real.sin_nonneg_of_mem_Icc (by
    dsimp [arcEnd] at ht
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos])
  have hsq : ‖arcOffset t‖^2 = 2*(1-Real.sin (2*t)) := by
    rw [← Complex.normSq_eq_norm_sq, arcOffset, normSq_hardyAxisPoint]
  rw [arcOffset, hardyAxisPoint_im]
  refine ⟨hc, ?_⟩
  have hp := mul_nonneg (sub_nonneg.mpr (Real.sin_le_one (2*t))) hs
  dsimp [arcOffset] at hsq
  nlinarith [Real.sin_sq_add_cos_sq (2*t), norm_nonneg (hardyAxisPoint (2*t))]

theorem tendsto_arcOffset : Tendsto arcOffset (𝓝[<] arcEnd) (𝓝 0) := by
  have hc : Continuous arcOffset := by unfold arcOffset hardyAxisPoint; fun_prop
  have hz : arcOffset arcEnd = 0 := by
    unfold arcOffset arcEnd
    rw [show 2*(Real.pi/4)=Real.pi/2 by ring]
    simp [hardyAxisPoint]
  rw [← hz]
  exact (hc.tendsto arcEnd).mono_left nhdsWithin_le_nhds

theorem tendsto_oddTheta_axis (m : ℕ) :
    Tendsto (fun t => iteratedDeriv m oddTheta (arcOffset t)) (𝓝[<] arcEnd) (𝓝 0) := by
  apply tendsto_oddTheta_iteratedDeriv_zero tendsto_arcOffset _ m
  filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
  exact arcOffset_cone ht

private def tau (z : ℂ) : ℂ := Complex.I*Complex.exp (2*z)

private theorem hasDerivAt_tau (z : ℂ) : HasDerivAt tau (2*tau z) z := by
  have hh := (((hasDerivAt_id z).const_mul (2:ℂ)).cexp).const_mul Complex.I
  apply hh.congr_deriv
  dsimp [tau]
  ring

private theorem potential_eq_oddTheta (z : ℂ) :
    Potential z = Complex.exp (z/2)*oddTheta (1+tau z) := by
  unfold Potential oddTheta tau
  congr 1
  simpa only [show (1:ℂ)+(1+Complex.I*Complex.exp (2*z)) = 2+Complex.I*Complex.exp (2*z) by ring]
    using (jacobiTheta_two_add (Complex.I*Complex.exp (2*z))).symm

private def firstJet (z : ℂ) : ℂ :=
  Complex.exp (z/2)*(oddTheta (1+tau z)/2+2*tau z*deriv oddTheta (1+tau z))

private def secondJet (z : ℂ) : ℂ :=
  Complex.exp (z/2)*(oddTheta (1+tau z)/4+6*tau z*deriv oddTheta (1+tau z)+
    4*(tau z)^2*deriv (deriv oddTheta) (1+tau z))

private theorem hasDerivAt_potential_jet {z : ℂ} (hz : 0<(1+tau z).im) :
    HasDerivAt Potential (firstJet z) z := by
  have he := ((hasDerivAt_id z).div_const (2:ℂ)).cexp
  have ht := ((analytic_oddTheta (1+tau z) hz).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_tau z).const_add 1)
  have hp := he.mul ht
  have hp' : HasDerivAt Potential _ z := hp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall potential_eq_oddTheta)
  apply hp'.congr_deriv
  dsimp [firstJet]
  ring

private theorem deriv_potential_jet {z : ℂ} (hz : 0<(1+tau z).im) :
    deriv Potential z = firstJet z := (hasDerivAt_potential_jet hz).deriv

private theorem hasDerivAt_firstJet {z : ℂ} (hz : 0<(1+tau z).im) :
    HasDerivAt firstJet (secondJet z) z := by
  have he := ((hasDerivAt_id z).div_const (2:ℂ)).cexp
  have hb := (hasDerivAt_tau z).const_add 1
  have h0 := ((analytic_oddTheta (1+tau z) hz).differentiableAt.hasDerivAt).comp z hb
  have h1 := ((analytic_oddTheta.deriv (1+tau z) hz).differentiableAt.hasDerivAt).comp z hb
  have hh := he.mul ((h0.div_const 2).add (((hasDerivAt_tau z).const_mul 2).mul h1))
  apply hh.congr_deriv
  dsimp [secondJet]
  ring

private theorem deriv2_potential_jet {z : ℂ} (hz : 0<(1+tau z).im) :
    deriv (deriv Potential) z = secondJet z := by
  have hopen : IsOpen {w : ℂ | 0<(1+tau w).im} := by
    apply isOpen_lt continuous_const
    unfold tau
    fun_prop
  have heq : deriv Potential =ᶠ[𝓝 z] firstJet := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact deriv_potential_jet hw
  exact ((hasDerivAt_firstJet hz).congr_of_eventuallyEq heq).deriv

theorem axis_mem_strip {t : ℝ} (ht0 : 0≤t) (htL : t<arcEnd) :
    (t:ℂ)*Complex.I ∈ thetaCuspStrip := by
  simpa [thetaCuspStrip, arcEnd, Complex.mul_im, abs_of_nonneg ht0] using htL

/-- The potential and its first two complex derivatives all vanish at the arc endpoint. -/
theorem tendsto_potential_jets :
    Tendsto (fun t : ℝ => Potential ((t:ℂ)*Complex.I)) (𝓝[<] arcEnd) (𝓝 0) ∧
    Tendsto (fun t : ℝ => deriv Potential ((t:ℂ)*Complex.I)) (𝓝[<] arcEnd) (𝓝 0) ∧
    Tendsto (fun t : ℝ => deriv (deriv Potential) ((t:ℂ)*Complex.I)) (𝓝[<] arcEnd) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => oddTheta (1+tau ((t:ℂ)*Complex.I))) (𝓝[<] arcEnd) (𝓝 0) := by
    simpa only [iteratedDeriv_zero,arcOffset_eq,tau] using tendsto_oddTheta_axis 0
  have h1 : Tendsto (fun t : ℝ => deriv oddTheta (1+tau ((t:ℂ)*Complex.I))) (𝓝[<] arcEnd) (𝓝 0) := by
    simpa only [iteratedDeriv_one,arcOffset_eq,tau] using tendsto_oddTheta_axis 1
  have h2 : Tendsto (fun t : ℝ => deriv (deriv oddTheta) (1+tau ((t:ℂ)*Complex.I)))
      (𝓝[<] arcEnd) (𝓝 0) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,arcOffset_eq,tau] using tendsto_oddTheta_axis 2
  have he : Tendsto (fun t : ℝ => Complex.exp (((t:ℂ)*Complex.I)/2)) (𝓝[<] arcEnd)
      (𝓝 (Complex.exp (((arcEnd:ℂ)*Complex.I)/2))) := by
    exact ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (((t:ℂ)*Complex.I)/2))).tendsto _).mono_left
      nhdsWithin_le_nhds
  have hτ : Tendsto (fun t : ℝ => tau ((t:ℂ)*Complex.I)) (𝓝[<] arcEnd)
      (𝓝 (tau ((arcEnd:ℂ)*Complex.I))) := by
    have hc : Continuous (fun t : ℝ => tau ((t:ℂ)*Complex.I)) := by unfold tau; fun_prop
    exact (hc.tendsto _).mono_left nhdsWithin_le_nhds
  have hj1 : Tendsto (fun t : ℝ => firstJet ((t:ℂ)*Complex.I)) (𝓝[<] arcEnd) (𝓝 0) := by
    simpa only [firstJet,zero_div,mul_zero,add_zero] using he.mul ((h0.div_const 2).add ((hτ.const_mul 2).mul h1))
  have hj2 : Tendsto (fun t : ℝ => secondJet ((t:ℂ)*Complex.I)) (𝓝[<] arcEnd) (𝓝 0) := by
    simpa only [secondJet,zero_div,mul_zero,add_zero] using
      he.mul (((h0.div_const 4).add ((hτ.const_mul 6).mul h1)).add (((hτ.pow 2).const_mul 4).mul h2))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [potential_eq_oddTheta,mul_zero] using he.mul h0
  · apply hj1.congr'
    filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
    have hpos : 0<(1+tau ((t:ℂ)*Complex.I)).im := by
      simpa only [tau,← arcOffset_eq] using (arcOffset_cone ht).1
    exact (deriv_potential_jet hpos).symm
  · apply hj2.congr'
    filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
    have hpos : 0<(1+tau ((t:ℂ)*Complex.I)).im := by
      simpa only [tau,← arcOffset_eq] using (arcOffset_cone ht).1
    exact (deriv2_potential_jet hpos).symm

/-- The literal source, not only its potential, vanishes at the odd arc endpoint. -/
theorem tendsto_source_axis_zero :
    Tendsto (fun t : ℝ => thetaCuspStripSource ((t:ℂ)*Complex.I)) (𝓝[<] arcEnd) (𝓝 0) := by
  have hj := tendsto_potential_jets
  have hh := (hj.2.2.sub (hj.1.div_const 4)).div_const 2
  simp only [zero_div,sub_zero] at hh
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsLT arcEnd_pos] with t ht
  exact (source_complex_ward (axis_mem_strip ht.1.le ht.2)).symm

theorem source_conj (z : ℂ) :
    thetaCuspStripSource (starRingEnd ℂ z) = starRingEnd ℂ (thetaCuspStripSource z) := by
  have htwo : starRingEnd ℂ (2:ℂ) = 2 := Complex.conj_ofReal 2
  have hthree : starRingEnd ℂ (3:ℂ) = 3 := Complex.conj_ofReal 3
  rw [thetaCuspStripSource,thetaCuspStripSource,Complex.conj_tsum]
  apply tsum_congr
  intro n
  simp [thetaCuspComplexTerm,thetaCuspComplexSeed,← Complex.exp_conj,htwo,hthree]

theorem source_axis_im {t : ℝ} (ht0 : 0≤t) (htL : t<arcEnd) :
    (thetaCuspStripSource ((t:ℂ)*Complex.I)).im = 0 := by
  have hh := source_conj ((t:ℂ)*Complex.I)
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg] at hh
  rw [thetaCuspStripSource_neg (axis_mem_strip ht0 htL)] at hh
  have hi := congrArg Complex.im hh
  simp only [Complex.conj_im] at hi
  linarith

end RHTower.ThetaImaginaryArc
