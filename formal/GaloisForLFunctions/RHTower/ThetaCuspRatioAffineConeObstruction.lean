import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticSlopeBoundary
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology

def quadraticFamilyT (a h : ℝ) : ℝ := 1/12-7*h/72+a*h^2
def quadraticFamilySpeed (a h : ℝ) : ℝ :=
  1-6*quadraticFamilyT a h-(2/3)*h-4*quadraticFamilyT a h*h+
    (2/3)*quadraticFamilyT a h*h^2-(4/9)*h^2+(4/9)*quadraticFamilyT a h*h^3

theorem quadraticFamily_in_cone {a h : ℝ} (hh : 0<h) (hb : h<1/2)
    (ht : 0<quadraticFamilyT a h) (hth : quadraticFamilyT a h*h<1)
    (hf : 0<quadraticFamilySpeed a h) :
    StrictCoarseCone (9-h^2) h⁻¹ ((1-quadraticFamilyT a h*h)/3) := by
  have hn : h≠0 := ne_of_gt hh
  have hs : 0<h^2 := sq_pos_of_pos hh
  have hsq : h^2<1/4 := by nlinarith
  have hk : (5/4:ℝ)<h⁻¹ := by
    rw [inv_eq_one_div,lt_div_iff₀ hh]
    linarith
  have hr : h⁻¹^2*(9-(9-h^2))=1 := by field_simp [hn]; ring
  have he : h⁻¹^2*(9-(9-h^2))-6*h⁻¹-4+
      2*(9-h^2)*(h⁻¹+2/3)*((1-quadraticFamilyT a h*h)/3)=quadraticFamilySpeed a h := by
    unfold quadraticFamilySpeed
    field_simp [hn]
    ring
  unfold StrictCoarseCone
  refine ⟨by linarith,by linarith,hk,by linarith,?_,?_,?_⟩
  · have := mul_pos ht hh
    linarith
  · rw [hr]
    norm_num
  · rwa [he]

theorem quadraticFamily_eventually_in_cone (a : ℝ) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), StrictCoarseCone (9-h^2) h⁻¹ ((1-quadraticFamilyT a h*h)/3) := by
  have htC : Continuous (quadraticFamilyT a) := by unfold quadraticFamilyT; fun_prop
  have hthC : Continuous (fun h : ℝ => quadraticFamilyT a h*h) := by fun_prop
  have hfC : Continuous (quadraticFamilySpeed a) := by unfold quadraticFamilySpeed; fun_prop
  have ht0 : 0<quadraticFamilyT a 0 := by norm_num [quadraticFamilyT]
  have hth0 : quadraticFamilyT a 0*0<1 := by norm_num
  have hf0 : 0<quadraticFamilySpeed a 0 := by norm_num [quadraticFamilySpeed,quadraticFamilyT]
  have ht := htC.continuousAt.eventually_const_lt ht0
  have hth := hthC.continuousAt.eventually_lt_const hth0
  have hf := hfC.continuousAt.eventually_const_lt hf0
  have hb : ∀ᶠ h in 𝓝[>] (0:ℝ), h<1/2 :=
    (eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds,hth.filter_mono nhdsWithin_le_nhds,
    hf.filter_mono nhdsWithin_le_nhds,hb,self_mem_nhdsWithin] with h ht hth hf hb hh
  exact quadraticFamily_in_cone hh hb ht hth hf

/-- The global affine source constraint is still insufficient as a pointwise slope criterion.
This is a state-space counterexample, not an actual modular source point. -/
theorem exists_affineCone_negative_slope :
    ∃ v k z : ℝ, StrictCoarseCone v k z ∧
      1/12-7/(72*k)<(1-3*z)/(k*(9-v)) ∧
      (eval (basePoint (v:ℂ) (k:ℂ) (z:ℂ)) ThetaRatioSquare.slope).re<0 := by
  have hn := (quadraticSlope_sign 1 (1/288)).2 (by norm_num)
  have hc := quadraticFamily_eventually_in_cone (1/288)
  have hp : ∀ᶠ h in 𝓝[>] (0:ℝ), 0<h := self_mem_nhdsWithin
  obtain ⟨h,hh,hneg,hcone⟩ := (hp.and (hn.and hc)).exists
  let t : ℝ := quadraticFamilyT (1/288) h
  have hneq : h≠0 := ne_of_gt hh
  have ht : 1/12-7*h/72<t := by
    have hs := sq_pos_of_pos hh
    dsimp [t,quadraticFamilyT]
    nlinarith
  have heq : (1-3*((1-t*h)/3))/(h⁻¹*(9-(9-h^2)))=t := by
    field_simp [hneq]
    ring
  have heb : 1/12-7/(72*h⁻¹)=1/12-7*h/72 := by field_simp [hneq]
  have hreg : regularSlopeValue h 1 t<0 := by
    simpa [t,quadraticFamilyT] using hneg
  have hsl : slopeValue h 1 t<0 := by
    have hs := regularSlopeValue_eq h 1 t hneq
    have hpow := pow_pos hh 19
    by_contra hhsl
    have hnonneg := mul_nonneg hpow.le (le_of_not_gt hhsl)
    rw [hs] at hnonneg
    linarith
  have heP : sourcePoint (h:ℂ) 1 (t:ℂ)=
      basePoint ((9-h^2:ℝ):ℂ) ((h⁻¹:ℝ):ℂ) (((1-t*h)/3:ℝ):ℂ) := by
    funext i
    cases i <;> simp [sourcePoint,basePoint] <;> ring
  refine ⟨9-h^2,h⁻¹,(1-t*h)/3,hcone,?_,?_⟩
  · rwa [heq,heb]
  · simpa [slopeValue,heP] using hsl

end
end HTGeometry.ThetaRatioInfinity
