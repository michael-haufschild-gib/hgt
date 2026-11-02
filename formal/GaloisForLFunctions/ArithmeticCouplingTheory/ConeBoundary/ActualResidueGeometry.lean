import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.ActualConeResolvent
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.SplineClusterBounds

/-!
# Actual atoms at the maximal-width boundary

The exact spline coefficient identifies each mixed residue with an integer
multiplicity. A zero within radial distance `s` of maximal width supplies
an eighth-power height pole. Nearby atoms contribute only a summable
negative error after phase alignment, without spacing or simplicity assumptions.
-/

open Complex
open Zeta23
open GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
open ConeCoupling ConeMoments

def zeroOffset (ρ : zetaZeroConfig.carrier) : ℂ := (ρ:ℂ)-1/2

def boundaryOffset (γ s : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  zeroOffset ρ-(zetaZeroWidth+s:ℝ)-(γ:ℂ)*I

lemma zeroOffset_re (ρ : zetaZeroConfig.carrier) :
    (zeroOffset ρ).re=(ρ:ℂ).re-1/2 := by
  simp only [zeroOffset,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]

lemma zeroOffset_im (ρ : zetaZeroConfig.carrier) :
    (zeroOffset ρ).im=(ρ:ℂ).im := by
  simp only [zeroOffset,Complex.sub_im,Complex.div_ofNat_im,Complex.one_im,zero_div,sub_zero]

lemma zeroOffset_re_le_width (ρ : zetaZeroConfig.carrier) :
    (zeroOffset ρ).re ≤ zetaZeroWidth := by
  rw [zeroOffset_re]
  exact (le_abs_self _).trans (abs_re_sub_half_le_zetaZeroWidth ρ.2)

lemma zeroOffset_re_le_half (ρ : zetaZeroConfig.carrier) :
    (zeroOffset ρ).re ≤ 1/2 := (zeroOffset_re_le_width ρ).trans zetaZeroWidth_le_half

lemma boundaryOffset_re (γ s : ℝ) (ρ : zetaZeroConfig.carrier) :
    (boundaryOffset γ s ρ).re=(zeroOffset ρ).re-zetaZeroWidth-s := by
  simp only [boundaryOffset,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
  ring

lemma boundaryOffset_im (γ s : ℝ) (ρ : zetaZeroConfig.carrier) :
    (boundaryOffset γ s ρ).im=(ρ:ℂ).im-γ := by
  simp only [boundaryOffset,Complex.sub_im,Complex.ofReal_im,Complex.mul_im,
    Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,
    sub_zero,zeroOffset_im]

lemma boundaryOffset_re_nonpos (γ : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ρ : zetaZeroConfig.carrier) : (boundaryOffset γ s ρ).re ≤ 0 := by
  rw [boundaryOffset_re]
  linarith only [zeroOffset_re_le_width ρ,hs]

lemma clockDefect_boundaryOffset (a b γ s : ℝ) (ρ : zetaZeroConfig.carrier) :
    clockDefect a b (boundaryOffset γ s ρ)=1-boundaryClock a b γ s ρ := rfl

/-- On the positive strip, the actual mixed residue is its exact spline
coefficient multiplied by the integer zero multiplicity. -/
lemma mixedResidue_eq_splineResidue (a b : ℝ) (ρ : zetaZeroConfig.carrier)
    (hρ : 0 < (zeroOffset ρ).re) :
    mixedResidue a b ρ=(zetaZeroConfig.mult ρ:ℂ)*splineResidue a b (zeroOffset ρ) := by
  have hz : zeroOffset ρ ≠ 0 := by intro he; rw [he,Complex.zero_re] at hρ; exact (lt_irrefl 0) hρ
  have hh := cubicSpline_Wsummand hz
  have he : (1/2:ℂ)+zeroOffset ρ=(ρ:ℂ) := by unfold zeroOffset; ring
  rw [he] at hh
  unfold mixedResidue wt ArithmeticCastelnuovoSeveri.cx
  rw [hh]
  unfold splineResidue mult zeroOffset
  ring

lemma one_le_zero_multiplicity (ρ : zetaZeroConfig.carrier)
    (hρ : 0 < (zeroOffset ρ).re) : 1 ≤ zetaZeroConfig.mult ρ := by
  have hw : wt ρ ≠ 0 := ArithmeticKreinLangerTheory.Wsummand_ne_zero_of_rightZero
    ⟨ρ.2,by rw [zeroOffset_re] at hρ; linarith only [hρ]⟩
  by_contra hm
  have hm0 : zetaZeroConfig.mult ρ=0 := by omega
  apply hw
  simp only [wt,ZeroConfig.Wsummand,hm0,Nat.cast_zero,zero_mul]

/-- The pole at the ordinate of an atom is real, with a denominator at most
`(a+b)s` when its width gap is at most `s`. -/
lemma clockDefect_own_atom {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (ρ : zetaZeroConfig.carrier)
    (hgap : zetaZeroWidth-(zeroOffset ρ).re ≤ s) :
    ∃ v : ℝ, 0 < v ∧ v ≤ (a+b)*s ∧
      clockDefect a b (boundaryOffset (ρ:ℂ).im s ρ)=(v:ℂ) := by
  let t := zetaZeroWidth+s-(zeroOffset ρ).re
  have ht : 0 < t := by dsimp only [t]; linarith only [zeroOffset_re_le_width ρ,hs]
  have ht2 : t ≤ 2*s := by dsimp only [t]; linarith only [hgap]
  have hw : boundaryOffset (ρ:ℂ).im s ρ=(-(t:ℝ):ℂ) := by
    apply Complex.ext
    · rw [boundaryOffset_re]; simp only [Complex.neg_re,Complex.ofReal_re,t]; ring
    · rw [boundaryOffset_im]; simp only [sub_self,Complex.neg_im,Complex.ofReal_im,neg_zero]
  let v := 1-(Real.exp (-a*t)+Real.exp (-b*t))/2
  have hea : Real.exp (-a*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos ha ht])
  have heb : Real.exp (-b*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hb ht])
  have hv : 0 < v := by dsimp only [v]; linarith only [hea,heb]
  have hlowA := Real.add_one_le_exp (-a*t)
  have hlowB := Real.add_one_le_exp (-b*t)
  have hvupper : v ≤ (a+b)*s := by
    have hh := mul_le_mul_of_nonneg_left ht2 (add_nonneg ha.le hb.le)
    dsimp only [v]
    nlinarith only [hlowA,hlowB,hh]
  refine ⟨v,hv,hvupper,?_⟩
  have he (c : ℝ) : Complex.exp ((c:ℂ)*(-(t:ℂ)))=(Real.exp (-c*t):ℂ) := by
    have harg : (c:ℂ)*(-(t:ℂ))=((-c*t:ℝ):ℂ) := by push_cast; ring
    rw [harg,← Complex.ofReal_exp]
  rw [hw,clockDefect,he a,he b]
  dsimp only [v]
  push_cast
  ring

/-- Every near-boundary zero supplies an eighth-power height pole with a
uniform positive coefficient; its multiplicity can only increase it. -/
theorem exists_actual_own_atom_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hD : 0 < zetaZeroWidth) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : zetaZeroConfig.carrier) (u : ℂ) (s : ℝ),
      0 < s → s ≤ zetaZeroWidth/2 → zetaZeroWidth-(zeroOffset ρ).re ≤ s →
      u*splineResidue a b (zeroOffset ρ)=(‖splineResidue a b (zeroOffset ρ)‖:ℂ) →
      A/((1+|(ρ:ℂ).im|)^8*s) ≤
        (u*(mixedResidue a b ρ/(1-boundaryClock a b (ρ:ℂ).im s ρ))).re := by
  let d := zetaZeroWidth/2
  have hd : 0 < d := by dsimp only [d]; positivity
  let c := (Real.sinh d)^8*(Real.exp (a*d)-1)*(Real.exp (b*d)-1)
  have hca : 0 < Real.exp (a*d)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ha hd))
  have hcb : 0 < Real.exp (b*d)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hb hd))
  have hc : 0 < c := mul_pos (mul_pos (pow_pos (Real.sinh_pos_iff.mpr hd) 8) hca) hcb
  have hab : 0 < a+b := add_pos ha hb
  refine ⟨c/(a+b),div_pos hc hab,?_⟩
  intro ρ u s hs hsD hgap hphase
  have hrd : d ≤ (zeroOffset ρ).re := by dsimp only [d]; linarith only [hsD,hgap]
  have hrpos := hd.trans_le hrd
  have hmult : 1 ≤ (zetaZeroConfig.mult ρ:ℝ) := by
    exact_mod_cast one_le_zero_multiplicity ρ hrpos
  have hg := splineResidue_lower ha hb hd hrd (zeroOffset_re_le_half ρ)
  rw [zeroOffset_im] at hg
  obtain ⟨v,hv,hvup,hveq⟩ := clockDefect_own_atom ha hb hs ρ hgap
  have he := mixedResidue_eq_splineResidue a b ρ hrpos
  have hnum : c/(1+|(ρ:ℂ).im|)^8 ≤
      (zetaZeroConfig.mult ρ:ℝ)*‖splineResidue a b (zeroOffset ρ)‖ :=
    hg.trans (le_mul_of_one_le_left (norm_nonneg _) hmult)
  have hterm : (u*(mixedResidue a b ρ/(1-boundaryClock a b (ρ:ℂ).im s ρ))).re=
      (zetaZeroConfig.mult ρ:ℝ)*‖splineResidue a b (zeroOffset ρ)‖/v := by
    rw [he,← clockDefect_boundaryOffset,hveq]
    have hr : u*((zetaZeroConfig.mult ρ:ℂ)*splineResidue a b (zeroOffset ρ)/(v:ℂ))=
        (zetaZeroConfig.mult ρ:ℂ)*(u*splineResidue a b (zeroOffset ρ))/(v:ℂ) := by ring
    rw [hr,hphase]
    norm_cast
  rw [hterm]
  calc
    _ = (c/(1+|(ρ:ℂ).im|)^8)/((a+b)*s) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ (c/(1+|(ρ:ℂ).im|)^8)/v :=
      div_le_div_of_nonneg_left (by positivity) hv hvup
    _ ≤ _ := div_le_div_of_nonneg_right hnum hv.le

/-- A whole cluster near the maximal width contributes only a summable
negative error after rotation by the central spline residue. -/
theorem exists_actual_cluster_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hD : 0 < zetaZeroWidth) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ (ρ₀ ρ : zetaZeroConfig.carrier) (u : ℂ) (s : ℝ),
      0 < s → s ≤ zetaZeroWidth/2 → zetaZeroWidth-(zeroOffset ρ₀).re ≤ s →
      ‖u‖=1 → u*splineResidue a b (zeroOffset ρ₀)=(‖splineResidue a b (zeroOffset ρ₀)‖:ℂ) →
      ‖boundaryOffset (ρ₀:ℂ).im s ρ‖ ≤ r →
      -(C*‖mixedResidue a b ρ‖) ≤
        (u*(mixedResidue a b ρ/(1-boundaryClock a b (ρ₀:ℂ).im s ρ))).re := by
  obtain ⟨C,hC,hcluster⟩ := exists_spline_cluster_re_lower (D := (1/2:ℝ)) ha hb
    (show 0 < zetaZeroWidth/2 by positivity)
  let r := min (zetaZeroWidth/2) (min 1 (1/(2*(a+b))))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrD : r ≤ zetaZeroWidth/2 := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrab : r ≤ 1/(2*(a+b)) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,C,hr,hC,?_⟩
  intro ρ₀ ρ u s hs hsD hgap hu hphase hnear
  have h₀d : zetaZeroWidth/2 ≤ (zeroOffset ρ₀).re := by linarith only [hsD,hgap]
  have hrd : zetaZeroWidth/2 ≤ (zeroOffset ρ).re := by
    have hh := Complex.re_le_norm (-(boundaryOffset (ρ₀:ℂ).im s ρ))
    rw [Complex.neg_re,norm_neg,boundaryOffset_re] at hh
    linarith only [hh,hnear,hrD,hs]
  have hdist : ‖zeroOffset ρ-zeroOffset ρ₀‖ ≤ ‖boundaryOffset (ρ₀:ℂ).im s ρ‖ := by
    have hh := norm_sub_le_norm_boundary_center (zeroOffset_re_le_width ρ)
      (zeroOffset_re_le_width ρ₀) hgap
    simpa only [zeroOffset_im,boundaryOffset] using hh
  have hh := hcluster (zeroOffset ρ) (zeroOffset ρ₀) u (boundaryOffset (ρ₀:ℂ).im s ρ)
    hrd (zeroOffset_re_le_half ρ) h₀d (zeroOffset_re_le_half ρ₀) hu hphase
    (boundaryOffset_re_nonpos _ hs.le ρ) hdist (hnear.trans hr1) (hnear.trans hrab)
  have he := mixedResidue_eq_splineResidue a b ρ (lt_of_lt_of_le (by positivity) hrd)
  have hm : 0 ≤ (zetaZeroConfig.mult ρ:ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hh hm
  rw [he,norm_mul,Complex.norm_natCast,div_eq_mul_inv,← clockDefect_boundaryOffset]
  have he' : u*((zetaZeroConfig.mult ρ:ℂ)*splineResidue a b (zeroOffset ρ)*
      (clockDefect a b (boundaryOffset (ρ₀:ℂ).im s ρ))⁻¹)=
      ((zetaZeroConfig.mult ρ:ℝ):ℂ)*(u*splineResidue a b (zeroOffset ρ)*
        (clockDefect a b (boundaryOffset (ρ₀:ℂ).im s ρ))⁻¹) := by push_cast; ring
  rw [he',Complex.re_ofReal_mul]
  nlinarith only [hmul]

#print axioms mixedResidue_eq_splineResidue
#print axioms clockDefect_own_atom
#print axioms exists_actual_own_atom_lower
#print axioms exists_actual_cluster_bound
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
