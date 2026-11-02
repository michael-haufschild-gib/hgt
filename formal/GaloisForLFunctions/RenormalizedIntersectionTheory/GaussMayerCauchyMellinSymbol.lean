import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerQuadraticCone
import GaloisForLFunctions.HTGeometry.HalfLineBetaKernel

/-! The exact Mellin multiplier of normalized Cauchy averaging. The half-line
beta integral proves absolute convergence, reflection symmetry, and a strictly
positive Gamma norm square on the central line for real positive parameters. -/

open Complex Set MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerQuadraticCone
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyMellinSymbol

private theorem gamma_ne_zero {z : ℂ} (hz : 0 < z.re) : Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith only [hz,h,hn0]

private theorem beta_hasMellin {b A : ℂ} (hb : 0 < b.re) (hA : b.re < A.re) :
    HasMellin (fun x : ℝ => (1+(x : ℂ))^(-A)) b
      (Gamma b*Gamma (A-b)/Gamma A) := by
  have hv := HTGeometry.integral_halfLine_beta hb hA
  have hn : Gamma b*Gamma (A-b)/Gamma A ≠ 0 :=
    div_ne_zero (mul_ne_zero (gamma_ne_zero hb)
      (gamma_ne_zero (by simp only [sub_re]; linarith only [hA])))
      (gamma_ne_zero (lt_trans hb hA))
  constructor
  · exact Integrable.of_integral_ne_zero (by simpa only [smul_eq_mul,hv] using hn)
  · exact hv

private theorem weight_hasMellin {w u : ℂ} (hu : -1 < u.re)
    (hwu : u.re < w.re+1) :
    HasMellin (cauchyWeight w) (u+1)
      ((2 : ℂ)⁻¹*(Gamma ((u+1)/2)*Gamma ((w+1-u)/2)/Gamma ((w+2)/2))) := by
  have hb : 0 < ((u+1)/2).re := by simp; linarith only [hu]
  have hA : ((u+1)/2).re < ((w+2)/2).re := by simp; linarith only [hwu]
  have hi := beta_hasMellin hb hA
  have he : (w+2)/2-(u+1)/2=(w+1-u)/2 := by ring
  have hf : cauchyWeight w = fun t : ℝ =>
      (1+((t^(2 : ℝ) : ℝ) : ℂ))^(-((w+2)/2)) := by
    funext t
    rw [show t^(2 : ℝ)=t^2 from Real.rpow_natCast t 2]
    simp only [cauchyWeight,ofReal_add,ofReal_one]
  rw [hf]
  constructor
  · exact (MellinConvergent.comp_rpow (a := 2) (by norm_num)).mpr hi.1
  · have hm := mellin_comp_rpow (fun x : ℝ => (1+(x : ℂ))^(-((w+2)/2))) (u+1) 2
    rw [show ((2 : ℝ) : ℂ)=(2 : ℂ) from rfl, hi.2, he] at hm
    simpa only [Complex.real_smul, abs_of_pos (by norm_num : (0 : ℝ)<2),
      ofReal_inv, ofReal_ofNat] using hm

/-- The Gamma quotient which multiplies Mellin transforms under Cauchy averaging. -/
def symbol (w u : ℂ) : ℂ :=
  Gamma ((u+1)/2)*Gamma ((w+1-u)/2)/
    ((Real.pi : ℂ)^(1/2 : ℂ)*Gamma ((w+1)/2))

/-- The actual Cauchy kernel has this absolutely convergent Mellin transform
throughout its strip. The substitution `x=t²` reduces it to the half-line beta integral. -/
theorem cauchyKernel_hasMellin {w u : ℂ} (hw : 0 < w.re)
    (hu : -1 < u.re) (hwu : u.re < w.re+1) :
    HasMellin (cauchyKernel w) u (symbol w u) := by
  have hi := weight_hasMellin hu hwu
  have hk : cauchyKernel w = fun t : ℝ =>
      (averagingFactor w)⁻¹ • ((t : ℂ)^(1 : ℂ) • cauchyWeight w t) := by
    funext t
    simp only [cauchyKernel,cpow_one,smul_eq_mul,mul_assoc]
  rw [hk]
  constructor
  · exact (MellinConvergent.cpow_smul.mpr hi.1).const_smul _
  · rw [mellin_const_smul,mellin_cpow_smul,hi.2]
    have hgA : Gamma ((w+2)/2) ≠ 0 := gamma_ne_zero (by simp; linarith only [hw])
    have hgB : Gamma ((w+1)/2) ≠ 0 := gamma_ne_zero (by simp; linarith only [hw])
    have hp : (Real.pi : ℂ)^(1/2 : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    simp only [smul_eq_mul,averagingFactor,MayerScatteringNormalization.archimedeanFactor,
      symbol,show (w+2)/2-1/2=(w+1)/2 by ring]
    field_simp

/-- The two real-axis components retain unit Mellin mass on the full source half-plane. -/
theorem cauchyKernel_mellin_zero {w : ℂ} (hw : 0 < w.re) :
    HasMellin (cauchyKernel w) 0 1 := by
  have h := cauchyKernel_hasMellin hw (u := 0) (by norm_num) (by simp; linarith only [hw])
  have hg : Gamma ((w+1)/2) ≠ 0 := gamma_ne_zero (by simp; linarith only [hw])
  have hp : (Real.pi : ℂ)^(1/2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  simpa only [symbol,zero_add,sub_zero,Complex.Gamma_one_half_eq,div_self (mul_ne_zero hp hg)] using h

/-- The symbol is symmetric about the central Mellin line. -/
theorem symbol_reflection (w u : ℂ) : symbol w (w-u)=symbol w u := by
  unfold symbol
  rw [show w-u+1=w+1-u by ring,show w+1-(w-u)=u+1 by ring,mul_comm]

/-- The spectral-axis moment equals the zeroth moment by reflection. -/
theorem cauchyKernel_mellin_spectral {w : ℂ} (hw : 0 < w.re) :
    HasMellin (cauchyKernel w) w 1 := by
  have h := cauchyKernel_hasMellin hw (u := w) (by linarith only [hw]) (by linarith)
  have hz := (cauchyKernel_mellin_zero hw).2
  have hz' := (cauchyKernel_hasMellin hw (u := 0) (by norm_num) (by simp; linarith only [hw])).2
  have hs : symbol w w = 1 := by
    have hr : symbol w w=symbol w 0 := by simpa only [sub_zero] using symbol_reflection w 0
    exact hr.trans (hz'.symm.trans hz)
  simpa only [hs] using h

/-- The Cauchy multiplier never vanishes in its Mellin convergence strip. -/
theorem symbol_ne_zero {w u : ℂ} (hw : 0 < w.re)
    (hu : -1 < u.re) (hwu : u.re < w.re+1) : symbol w u ≠ 0 := by
  unfold symbol
  apply div_ne_zero
  · exact mul_ne_zero (gamma_ne_zero (by simp; linarith only [hu]))
      (gamma_ne_zero (by simp; linarith only [hwu]))
  · exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (gamma_ne_zero (by simp; linarith only [hw]))

/-- Real multiplier on the central line; its numerator is a Gamma norm square. -/
def centralSymbol (r ξ : ℝ) : ℝ :=
  ‖Gamma (((r+2 : ℝ)/4 : ℝ)+((ξ : ℂ)/2)*I)‖^2/
    (Real.sqrt Real.pi*Real.Gamma ((r+1)/2))

/-- The two numerator Gamma arguments become conjugates on the central line. -/
theorem symbol_central (r ξ : ℝ) :
    symbol r ((r : ℂ)/2+(ξ : ℂ)*I)=(centralSymbol r ξ : ℂ) := by
  have ha : (((r : ℂ)/2+(ξ : ℂ)*I)+1)/2=
      (((r+2 : ℝ)/4 : ℝ) : ℂ)+((ξ : ℂ)/2)*I := by push_cast; ring
  have hb : ((r : ℂ)+1-((r : ℂ)/2+(ξ : ℂ)*I))/2=
      (starRingEnd ℂ) ((((r+2 : ℝ)/4 : ℝ) : ℂ)+((ξ : ℂ)/2)*I) := by
    apply Complex.ext <;> simp [map_ofNat] <;> ring
  have hd : ((r : ℂ)+1)/2=(((r+1)/2 : ℝ) : ℂ) := by push_cast; rfl
  have hp : (Real.pi : ℂ)^(1/2 : ℂ)=(Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow Real.pi_pos.le,ofReal_div,ofReal_one,ofReal_ofNat]
  rw [symbol,ha,hb,Gamma_conj,Complex.mul_conj,Complex.normSq_eq_norm_sq,hd,Gamma_ofReal,hp]
  simp only [centralSymbol,ofReal_div,ofReal_mul,ofReal_pow]

/-- Strict positivity holds at every real frequency for a real positive parameter. -/
theorem centralSymbol_pos {r : ℝ} (hr : 0 < r) (ξ : ℝ) : 0 < centralSymbol r ξ := by
  apply div_pos
  · apply sq_pos_of_pos
    exact norm_pos_iff.mpr (gamma_ne_zero (by simp; linarith only [hr]))
  · exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos)
      (Real.Gamma_pos_of_pos (by linarith only [hr]))

/-- The actual central Mellin integral converges absolutely and is strictly positive real. -/
theorem cauchyKernel_central_hasMellin {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    HasMellin (cauchyKernel r) ((r : ℂ)/2+(ξ : ℂ)*I) (centralSymbol r ξ : ℂ) := by
  rw [← symbol_central]
  apply cauchyKernel_hasMellin (by simpa only [ofReal_re] using hr)
  · simp; linarith only [hr]
  · simp; linarith only [hr]

#print axioms cauchyKernel_hasMellin
#print axioms cauchyKernel_mellin_zero
#print axioms symbol_reflection
#print axioms cauchyKernel_mellin_spectral
#print axioms symbol_ne_zero
#print axioms symbol_central
#print axioms centralSymbol_pos
#print axioms cauchyKernel_central_hasMellin

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCauchyMellinSymbol
