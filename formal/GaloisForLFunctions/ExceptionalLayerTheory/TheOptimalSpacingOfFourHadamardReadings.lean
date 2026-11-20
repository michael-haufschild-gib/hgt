import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Noise and spacing in a four-site residue measurement

Four horizontal readings at displacements −3h,−h,h,3h remove any
quadratic calibration drift. The exact worst-case gain for bounded
pointwise errors is minimized at h/|u| = √(5+2√13)/3. The stationarity
equation is a quadratic in squared spacing, as in the Jeans cutoff of
Boudjemâa (arXiv:2611.21911, equations 14–15).
-/

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Four real readings at one height u above the marked point. -/
def fourSiteReading (h u a b c d : ℝ) :=
  ((u^2+h^2)*(u^2+9*h^2)/(48*h^3))*(a-3*b+3*c-d)

/-- Sharp worst-case error per unit error at each site, for positive h. -/
def fourSiteNoiseGain (h u : ℝ) := (u^2+h^2)*(u^2+9*h^2)/(6*h^3)

/-- The stencil rejects even a separately chosen quadratic calibration
at each measurement. There is no bound on its three coefficients. -/
theorem four_site_quadratic_invariance (h u a b c d α β γ : ℝ) :
    let q := fun x => α+β*x+γ*x^2
    fourSiteReading h u (a+q (-3*h)) (b+q (-h)) (c+q h) (d+q (3*h)) =
      fourSiteReading h u a b c d := by
  dsimp only [fourSiteReading]
  congr 1
  ring

/-- A pole of positive, negative or zero residue is read exactly at
every nonzero horizontal spacing and any vertical offset. -/
theorem four_site_pole_exact {h : ℝ} (hh : h≠0) (u m : ℝ) :
    let f := fun x : ℝ => m*x/(x^2+u^2)
    fourSiteReading h u (f (-3*h)) (f (-h)) (f h) (f (3*h))=m := by
  have hp := sq_pos_of_ne_zero hh
  have h₁ : h^2+u^2≠0 := ne_of_gt (add_pos_of_pos_of_nonneg hp (sq_nonneg _))
  have h₃ : 9*h^2+u^2≠0 := ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (sq_nonneg _))
  dsimp only [fourSiteReading]
  rw [show (-3*h)^2=9*h^2 by ring,show (3*h)^2=9*h^2 by ring,neg_sq]
  field_simp [hh,h₁,h₃] <;> ring

/-- Independent errors of size at most e move the reading by at most
gain·e. Alternating errors attain this bound for every signal. -/
theorem four_site_sharp_noise {h e : ℝ} (hh : 0<h) (he : 0≤e) (u a b c d : ℝ) :
    (∀ A B C D : ℝ, |A-a|≤e → |B-b|≤e → |C-c|≤e → |D-d|≤e →
      |fourSiteReading h u A B C D-fourSiteReading h u a b c d|≤fourSiteNoiseGain h u*e) ∧
    fourSiteReading h u (a+e) (b-e) (c+e) (d-e)-fourSiteReading h u a b c d =
      fourSiteNoiseGain h u*e := by
  let K := (u^2+h^2)*(u^2+9*h^2)/(48*h^3)
  have hK : 0≤K := by dsimp only [K]; positivity
  have hG : fourSiteNoiseGain h u=8*K := by dsimp only [fourSiteNoiseGain,K]; ring
  constructor
  · intro A B C D hA hB hC hD
    have h₁ := abs_le.mp hA
    have h₂ := abs_le.mp hB
    have h₃ := abs_le.mp hC
    have h₄ := abs_le.mp hD
    have hbound : |(A-a)-3*(B-b)+3*(C-c)-(D-d)|≤8*e := abs_le.mpr
      ⟨by linarith only [h₁.1,h₂.2,h₃.1,h₄.2],by linarith only [h₁.2,h₂.1,h₃.2,h₄.1]⟩
    rw [show fourSiteReading h u A B C D-fourSiteReading h u a b c d=
      K*((A-a)-3*(B-b)+3*(C-c)-(D-d)) by dsimp only [fourSiteReading,K]; ring,
      abs_mul,abs_of_nonneg hK,hG]
    exact (mul_le_mul_of_nonneg_left hbound hK).trans_eq (by ring)
  · rw [hG]
    dsimp only [fourSiteReading,K]
    ring

/-- Positive stationary ratio between spacing and vertical offset. -/
def optimalFourSiteRatio : ℝ := Real.sqrt (5+2*Real.sqrt 13)/3

private theorem ratio_pos : 0<optimalFourSiteRatio := by unfold optimalFourSiteRatio; positivity

private theorem ratio_quartic : 9*optimalFourSiteRatio^4=10*optimalFourSiteRatio^2+3 := by
  have ha : 0≤5+2*Real.sqrt 13 := by positivity
  have h₂ : optimalFourSiteRatio^2=(5+2*Real.sqrt 13)/9 := by
    rw [optimalFourSiteRatio,div_pow,Real.sq_sqrt ha]; norm_num
  rw [show optimalFourSiteRatio^4=(optimalFourSiteRatio^2)^2 by ring,h₂]
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤13)]

private def gainShape (r : ℝ) := 9*r+10/r+1/r^3

private theorem gain_gap {r : ℝ} (hr : 0<r) :
    gainShape r-gainShape optimalFourSiteRatio =
      (r-optimalFourSiteRatio)^2*(10/(r*optimalFourSiteRatio^2)+
        (3*r^2+2*r*optimalFourSiteRatio+optimalFourSiteRatio^2)/(r^3*optimalFourSiteRatio^4)) := by
  let a := optimalFourSiteRatio
  have h₀ : a≠0 := ratio_pos.ne'
  have he : 9=10/a^2+3/a^4 := by
    calc (9:ℝ) = (9*a^4)/a^4 := by field_simp [h₀]
         _ = (10*a^2+3)/a^4 := by rw [show 9*a^4=10*a^2+3 from ratio_quartic]
         _ = _ := by field_simp [h₀] <;> ring
  change (9*r+10/r+1/r^3)-(9*a+10/a+1/a^3)=_
  rw [he]
  dsimp only [a] at *
  field_simp [hr.ne',h₀] <;> ring

private theorem scaled_gain {r t : ℝ} (hr : 0<r) (ht : 0<t) :
    fourSiteNoiseGain (r*t) t=t/6*gainShape r := by
  unfold fourSiteNoiseGain gainShape
  field_simp [hr.ne',ht.ne'] <;> ring

/-- Unique best spacing at every nonzero vertical offset. -/
theorem four_site_optimal_spacing {h u : ℝ} (hh : 0<h) (hu : u≠0) :
    fourSiteNoiseGain (optimalFourSiteRatio*|u|) u ≤ fourSiteNoiseGain h u ∧
      (fourSiteNoiseGain (optimalFourSiteRatio*|u|) u=fourSiteNoiseGain h u ↔
        h=optimalFourSiteRatio*|u|) := by
  let t := |u|
  let r := h/t
  have ht : 0<t := abs_pos.mpr hu
  have hr : 0<r := div_pos hh ht
  have he : r*t=h := div_mul_cancel₀ _ ht.ne'
  have habs (k : ℝ) : fourSiteNoiseGain k u=fourSiteNoiseGain k t := by
    unfold fourSiteNoiseGain t; rw [sq_abs]
  have hp : 0<10/(r*optimalFourSiteRatio^2)+
      (3*r^2+2*r*optimalFourSiteRatio+optimalFourSiteRatio^2)/(r^3*optimalFourSiteRatio^4) := by
    have := ratio_pos; positivity
  have hg := gain_gap hr
  have hn : gainShape optimalFourSiteRatio≤gainShape r := by
    apply sub_nonneg.mp
    rw [hg]
    exact mul_nonneg (sq_nonneg _) hp.le
  have heq : gainShape optimalFourSiteRatio=gainShape r ↔ r=optimalFourSiteRatio := by
    constructor
    · intro h
      rw [h,sub_self] at hg
      have hsq := (mul_eq_zero.mp hg.symm).resolve_right hp.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    · rintro h; rw [h]
  rw [habs (optimalFourSiteRatio*t),habs h,←he,scaled_gain ratio_pos ht,scaled_gain hr ht]
  refine ⟨mul_le_mul_of_nonneg_left hn (by positivity),?_⟩
  rw [mul_right_inj' (by positivity : t/6≠0),heq]
  constructor
  · rintro h; rw [h]
  · exact fun h => mul_right_cancel₀ ht.ne' h

#print axioms four_site_pole_exact
#print axioms four_site_sharp_noise
#print axioms four_site_optimal_spacing
end GaloisForLFunctions.ExceptionalLayerTheory
