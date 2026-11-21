import GaloisForLFunctions.MultiplicativePositivityGeometry.TheEquilibriumOfTheThreeSitePrimeGram

/-!
# Site activation at the scale of the zeta pole

If the spacing of three observation sites is asymptotic to u times the
damping, the limiting equilibrium has middle mass
max(2u²−1,0)/(6u²) for u ≠ 0. Below the critical ratio the middle site
is exactly empty at all sufficiently small damping.
-/
noncomputable section
open Filter Topology Complex
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.MultiplicativePositivityGeometry

private def direction (u : ℝ) : ℂ := 1+(u:ℂ)*I

private theorem direction_ne (u : ℝ) : direction u ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simpa [direction,Complex.mul_re] using this

private theorem re_inv_direction (u : ℝ) : ((direction u)⁻¹).re = 1/(1+u^2) := by
  rw [Complex.inv_re,Complex.normSq_apply]
  simp [direction,Complex.mul_re,Complex.mul_im,sq]

/-- The prime trace has a Cauchy scaling limit for every convergent choice
of the ratio of height to damping, including either sign and ratio zero. -/
theorem pole_scale_prime_trace {ι : Type*} {l : Filter ι} {H U : ι → ℝ} {u : ℝ}
    (hh : Tendsto H l (𝓝[>] 0)) (hu : Tendsto U l (𝓝 u)) :
    Tendsto (fun i => H i*zetaRealLogDeriv (1+H i) (H i*U i)) l (𝓝 (1/(1+u^2))) := by
  let z := fun i => 1+(H i:ℂ)*direction (U i)
  have hv : Tendsto (fun i => direction (U i)) l (𝓝 (direction u)) :=
    tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto u).comp hu |>.mul_const I)
  have hH := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_nhdsWithin_iff.mp hh).1
  have hz : Tendsto z l (𝓝 (1:ℂ)) := by
    simpa only [z,Complex.ofReal_zero,zero_mul,add_zero,Function.comp_apply] using
      (tendsto_const_nhds (x:=(1:ℂ))).add (hH.mul hv)
  have hpos : ∀ᶠ i in l, 0<H i := hh.eventually self_mem_nhdsWithin
  have hz' : Tendsto z l (𝓝[≠] (1:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hz,?_⟩
    filter_upwards [hpos] with i hi
    change 1+(H i:ℂ)*direction (U i)≠1
    exact fun he => (mul_ne_zero (Complex.ofReal_ne_zero.mpr hi.ne') (direction_ne _)) (by linear_combination he)
  have hres := (RHTower.neg_logDeriv_zeta_residue.comp hz').div hv (direction_ne u)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hres
  rw [one_div,re_inv_direction] at hreal
  apply hreal.congr'
  filter_upwards with i
  have hp : ((1+H i:ℝ):ℂ)+((H i*U i:ℝ):ℂ)*I=z i := by dsimp [z,direction]; push_cast; ring
  unfold zetaRealLogDeriv
  rw [hp,← Complex.re_ofReal_mul]
  apply congrArg Complex.re
  change (z i-1)*(-deriv riemannZeta (z i)/riemannZeta (z i))/direction (U i)=_
  rw [show z i-1=(H i:ℂ)*direction (U i) by dsimp only [z]; ring]
  apply (div_eq_iff (direction_ne _)).mpr
  ring

private def middleContrast (h t : ℝ) :=
  zetaRealLogDeriv (1+h) 0-2*zetaRealLogDeriv (1+h) t+zetaRealLogDeriv (1+h) (2*t)

private def middleCurvature (h t : ℝ) :=
  3*zetaRealLogDeriv (1+h) 0-4*zetaRealLogDeriv (1+h) t+zetaRealLogDeriv (1+h) (2*t)

private def scaleDenom (u : ℝ) := (1+u^2)*(1+4*u^2)

private theorem pole_scale_contrasts {ι : Type*} {l : Filter ι} {H U : ι → ℝ} {u : ℝ}
    (hh : Tendsto H l (𝓝[>] 0)) (hu : Tendsto U l (𝓝 u)) :
    Tendsto (fun i => H i*middleContrast (H i) (H i*U i)) l
      (𝓝 (2*u^2*(2*u^2-1)/scaleDenom u)) ∧
    Tendsto (fun i => H i*middleCurvature (H i) (H i*U i)) l
      (𝓝 (12*u^4/scaleDenom u)) := by
  have h0 := pole_scale_prime_trace hh (tendsto_const_nhds (x:=(0:ℝ)))
  have h1 := pole_scale_prime_trace hh hu
  have h2 := pole_scale_prime_trace hh (hu.const_mul 2)
  simp only [mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero,div_one] at h0
  have hf : 1-2*(1/(1+u^2))+1/(1+(2*u)^2)=2*u^2*(2*u^2-1)/scaleDenom u := by
    unfold scaleDenom
    field_simp <;> ring
  have hd : 3*1-4*(1/(1+u^2))+1/(1+(2*u)^2)=12*u^4/scaleDenom u := by
    unfold scaleDenom
    field_simp <;> ring
  constructor
  · rw [←hf]
    exact ((h0.sub (h1.const_mul 2)).add h2).congr fun i => by
      change _=H i*middleContrast _ _
      unfold middleContrast
      rw [show H i*(2*U i)=2*(H i*U i) by ring]
      ring
  · rw [←hd]
    exact (((h0.const_mul 3).sub (h1.const_mul 4)).add h2).congr fun i => by
      change _=H i*middleCurvature _ _
      unfold middleCurvature
      rw [show H i*(2*U i)=2*(H i*U i) by ring]
      ring

/-- The limiting active fraction has a sharp threshold at |u| = 1/√2. -/
theorem equilibriumMiddle_pole_scale {ι : Type*} {l : Filter ι} {H U : ι → ℝ} {u : ℝ}
    (hh : Tendsto H l (𝓝[>] 0)) (hu : Tendsto U l (𝓝 u)) (hune : u≠0) :
    Tendsto (fun i => equilibriumMiddle (H i) (H i*U i)) l (𝓝 (max (2*u^2-1) 0/(6*u^2))) := by
  obtain ⟨hf,hd⟩ := pole_scale_contrasts hh hu
  have hD : 0<scaleDenom u := by dsimp [scaleDenom]; positivity
  have hq : 0<u^2 := sq_pos_of_ne_zero hune
  have hd' : 0<12*u^4/scaleDenom u := by positivity
  have hl := (hf.max (tendsto_const_nhds (x:=(0:ℝ)))).div hd hd'.ne'
  have hw : max (2*u^2*(2*u^2-1)/scaleDenom u) 0/(12*u^4/scaleDenom u)=
      max (2*u^2-1) 0/(6*u^2) := by
    rcases le_total (2*u^2-1) 0 with hc | hc
    · rw [max_eq_right hc,max_eq_right (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hc) hD.le),zero_div,zero_div]
    · rw [max_eq_left hc,max_eq_left (div_nonneg (mul_nonneg (by positivity) hc) hD.le)]
      field_simp <;> ring
  rw [←hw]
  apply hl.congr'
  filter_upwards [hh.eventually self_mem_nhdsWithin] with i hi
  have hp : 0<H i := hi
  change max (H i*middleContrast _ _) 0/(H i*middleCurvature _ _)=max (middleContrast _ _) 0/middleCurvature _ _
  rw [show max (H i*middleContrast _ _) 0=H i*max (middleContrast _ _) 0 by rw [mul_max_of_nonneg _ _ hp.le,mul_zero],mul_div_mul_left _ _ hp.ne']

/-- In the open subcritical region the absence of middle mass is eventually
exact. In the open supercritical region its weight stays strictly positive. -/
theorem equilibriumMiddle_eventual_activation {ι : Type*} {l : Filter ι} {H U : ι → ℝ} {u : ℝ}
    (hh : Tendsto H l (𝓝[>] 0)) (hu : Tendsto U l (𝓝 u)) (hune : u≠0) :
    (2*u^2<1 → ∀ᶠ i in l, equilibriumMiddle (H i) (H i*U i)=0) ∧
    (1<2*u^2 → ∀ᶠ i in l, 0<equilibriumMiddle (H i) (H i*U i)) := by
  constructor
  · intro h
    have hd : 0<scaleDenom u := by dsimp [scaleDenom]; positivity
    have hf := (pole_scale_contrasts hh hu).1.eventually_lt_const
      (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos (by norm_num) (sq_pos_of_ne_zero hune)) (sub_neg.mpr h)) hd)
    filter_upwards [hf,hh.eventually self_mem_nhdsWithin] with i hi hp
    have hp' : 0<H i := hp
    have hm : middleContrast (H i) (H i*U i)<0 := neg_of_mul_neg_right hi hp'.le
    change max (middleContrast _ _) 0/_=0
    rw [max_eq_right hm.le,zero_div]
  · intro h
    apply (equilibriumMiddle_pole_scale hh hu hune).eventually_const_lt
    rw [max_eq_left (sub_nonneg.mpr h.le)]
    exact div_pos (sub_pos.mpr h) (mul_pos (by norm_num) (sq_pos_of_ne_zero hune))

end GaloisForLFunctions.MultiplicativePositivityGeometry
