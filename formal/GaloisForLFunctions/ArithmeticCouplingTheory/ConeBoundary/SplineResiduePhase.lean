import GaloisForLFunctions.RHTower.ThetaRenewalCoshFactorization
import GaloisForLFunctions.HTGeometry.LogLinearGronwallModel

/-!
# Relative regularity of exact spline residues

The mixed spline residue has a bounded logarithmic derivative on each
positive vertical strip. Grönwall along line segments gives a relative
Lipschitz bound, independent of ordinate height. Reverse triangle estimates
also give the exact eighth-power height lower bound.
-/

open Complex Set
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- The exact spline coefficient after one difference in each clock. -/
def splineResidue (a b : ℝ) (z : ℂ) : ℂ :=
  (Complex.sinh z/z)^8*(Complex.exp ((a:ℂ)*z)-1)*(Complex.exp ((b:ℂ)*z)-1)

def splineResidueLogSlope (a b : ℝ) (z : ℂ) : ℂ :=
  8*(Complex.cosh z/Complex.sinh z-1/z)+
    (a:ℂ)*Complex.exp ((a:ℂ)*z)/(Complex.exp ((a:ℂ)*z)-1)+
    (b:ℂ)*Complex.exp ((b:ℂ)*z)/(Complex.exp ((b:ℂ)*z)-1)

private lemma sinh_re_le_norm_sinh (z : ℂ) : Real.sinh z.re ≤ ‖Complex.sinh z‖ := by
  rw [Complex.sinh,norm_div,Complex.norm_two,Real.sinh_eq]
  have hh := norm_sub_norm_le (Complex.exp z) (Complex.exp (-z))
  rw [Complex.norm_exp,Complex.norm_exp,Complex.neg_re] at hh
  linarith only [hh]

lemma splineResidue_factors_nonzero {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) {z : ℂ} (hz : d ≤ z.re) :
    z ≠ 0 ∧ Complex.sinh z ≠ 0 ∧ Complex.exp ((a:ℂ)*z)-1 ≠ 0 ∧
      Complex.exp ((b:ℂ)*z)-1 ≠ 0 := by
  have hzr : 0 < z.re := hd.trans_le hz
  have hzn : z ≠ 0 := by intro he; simp only [he,Complex.zero_re] at hzr; exact lt_irrefl _ hzr
  have hsn : Complex.sinh z ≠ 0 := by
    apply norm_pos_iff.mp
    exact (Real.sinh_pos_iff.mpr hzr).trans_le (sinh_re_le_norm_sinh z)
  have hexp (c : ℝ) (hc : 0 < c) : Complex.exp ((c:ℂ)*z)-1 ≠ 0 := by
    have hlow : Real.exp (c*z.re)-1 ≤ ‖Complex.exp ((c:ℂ)*z)-1‖ := by
      have hh := norm_sub_norm_le (Complex.exp ((c:ℂ)*z)) (1:ℂ)
      simpa only [Complex.norm_exp,Complex.re_ofReal_mul,norm_one] using hh
    apply norm_pos_iff.mp
    exact (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hc hzr))).trans_le hlow
  exact ⟨hzn,hsn,hexp a ha,hexp b hb⟩

lemma hasDerivAt_splineResidue {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) {z : ℂ} (hz : d ≤ z.re) :
    HasDerivAt (splineResidue a b)
      (splineResidue a b z*splineResidueLogSlope a b z) z := by
  obtain ⟨hzn,hsn,han,hbn⟩ := splineResidue_factors_nonzero ha hb hd hz
  have hquot : HasDerivAt (fun u : ℂ => Complex.sinh u/u)
      ((Complex.sinh z/z)*(Complex.cosh z/Complex.sinh z-1/z)) z := by
    apply ((Complex.hasDerivAt_sinh z).div (hasDerivAt_id z) hzn).congr_deriv
    simp only [id_eq,mul_one]
    field_simp [hzn,hsn]
  have hexp (c : ℝ) (hc : Complex.exp ((c:ℂ)*z)-1 ≠ 0) :
      HasDerivAt (fun u : ℂ => Complex.exp ((c:ℂ)*u)-1)
        ((Complex.exp ((c:ℂ)*z)-1)*((c:ℂ)*Complex.exp ((c:ℂ)*z)/
          (Complex.exp ((c:ℂ)*z)-1))) z := by
    apply ((((hasDerivAt_id z).const_mul (c:ℂ)).cexp).sub_const 1).congr_deriv
    simp only [id_eq,mul_one]
    field_simp [hc]
  have h := (((hquot.pow 8).mul (hexp a han)).mul (hexp b hbn))
  apply h.congr_deriv
  simp only [splineResidue,splineResidueLogSlope,Pi.pow_apply,Pi.mul_apply,Nat.cast_ofNat]
  ring

/-- A uniform bound for the logarithmic derivative on a positive strip. -/
def splineResidueLogBound (a b d D : ℝ) : ℝ :=
  8*(Real.exp D/Real.sinh d+1/d)+
    a*Real.exp (a*D)/(Real.exp (a*d)-1)+
    b*Real.exp (b*D)/(Real.exp (b*d)-1)

lemma splineResidueLogBound_pos {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (D : ℝ) : 0 < splineResidueLogBound a b d D := by
  have hs := Real.sinh_pos_iff.mpr hd
  have hea := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ha hd))
  have heb := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hb hd))
  unfold splineResidueLogBound
  positivity

lemma norm_splineResidueLogSlope_le {a b d D : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) {z : ℂ} (hzd : d ≤ z.re) (hzD : z.re ≤ D) :
    ‖splineResidueLogSlope a b z‖ ≤ splineResidueLogBound a b d D := by
  have hzpos : 0 < z.re := hd.trans_le hzd
  have hdn : d ≤ ‖z‖ := hzd.trans (Complex.re_le_norm z)
  have hsn : Real.sinh d ≤ ‖Complex.sinh z‖ :=
    (Real.sinh_le_sinh.mpr hzd).trans (sinh_re_le_norm_sinh z)
  have hsp : 0 < Real.sinh d := Real.sinh_pos_iff.mpr hd
  have hcosh : ‖Complex.cosh z‖ ≤ Real.exp D := by
    apply (_root_.RHTower.norm_cosh_le_exp_abs_re z).trans
    exact Real.exp_le_exp.mpr (by rwa [abs_of_pos hzpos])
  have hrat : ‖Complex.cosh z/Complex.sinh z-1/z‖ ≤ Real.exp D/Real.sinh d+1/d := by
    calc
      _ ≤ ‖Complex.cosh z/Complex.sinh z‖+‖(1:ℂ)/z‖ := norm_sub_le _ _
      _ = ‖Complex.cosh z‖/‖Complex.sinh z‖+1/‖z‖ := by rw [norm_div,norm_div,norm_one]
      _ ≤ _ := add_le_add
        ((div_le_div_of_nonneg_right hcosh (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hsp hsn))
        (div_le_div_of_nonneg_left zero_le_one hd hdn)
  have he (c : ℝ) (hc : 0 < c) :
      ‖(c:ℂ)*Complex.exp ((c:ℂ)*z)/(Complex.exp ((c:ℂ)*z)-1)‖ ≤
        c*Real.exp (c*D)/(Real.exp (c*d)-1) := by
    have hp : 0 < Real.exp (c*d)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hc hd))
    have hnum : ‖Complex.exp ((c:ℂ)*z)‖ ≤ Real.exp (c*D) := by
      rw [Complex.norm_exp,Complex.re_ofReal_mul]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzD hc.le)
    have hden : Real.exp (c*d)-1 ≤ ‖Complex.exp ((c:ℂ)*z)-1‖ := by
      have hh := norm_sub_norm_le (Complex.exp ((c:ℂ)*z)) (1:ℂ)
      rw [Complex.norm_exp,Complex.re_ofReal_mul,norm_one] at hh
      exact (sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzd hc.le)) 1).trans hh
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hc.le) (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left (mul_nonneg hc.le (Real.exp_pos _).le) hp hden)
  have h8 : ‖8*(Complex.cosh z/Complex.sinh z-1/z)‖ ≤ 8*(Real.exp D/Real.sinh d+1/d) := by
    rw [norm_mul,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left hrat (by norm_num)
  unfold splineResidueLogSlope splineResidueLogBound
  calc
    _ ≤ ‖8*(Complex.cosh z/Complex.sinh z-1/z)‖+
        ‖(a:ℂ)*Complex.exp ((a:ℂ)*z)/(Complex.exp ((a:ℂ)*z)-1)‖+
        ‖(b:ℂ)*Complex.exp ((b:ℂ)*z)/(Complex.exp ((b:ℂ)*z)-1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h8 (he a ha)) (he b hb)

/-- Exact spline residues are uniformly bounded below by the eighth height power. -/
lemma splineResidue_lower {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) {z : ℂ} (hzd : d ≤ z.re) (hzD : z.re ≤ 1/2) :
    (Real.sinh d)^8*(Real.exp (a*d)-1)*(Real.exp (b*d)-1)/(1+|z.im|)^8 ≤
      ‖splineResidue a b z‖ := by
  have hzpos : 0 < z.re := hd.trans_le hzd
  have hzn : 0 < ‖z‖ := hzpos.trans_le (Complex.re_le_norm z)
  have hH : 0 < 1+|z.im| := by positivity
  have hzH : ‖z‖ ≤ 1+|z.im| := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hzpos] at hh
    linarith only [hh,hzD]
  have hsp : 0 < Real.sinh d := Real.sinh_pos_iff.mpr hd
  have hsin : Real.sinh d ≤ ‖Complex.sinh z‖ :=
    (Real.sinh_le_sinh.mpr hzd).trans (sinh_re_le_norm_sinh z)
  have hratio : Real.sinh d/(1+|z.im|) ≤ ‖Complex.sinh z/z‖ := by
    rw [norm_div]
    exact (div_le_div_of_nonneg_right hsin hH.le).trans
      (div_le_div_of_nonneg_left (norm_nonneg _) hzn hzH)
  have he (c : ℝ) (hc : 0 < c) :
      Real.exp (c*d)-1 ≤ ‖Complex.exp ((c:ℂ)*z)-1‖ := by
    have hh := norm_sub_norm_le (Complex.exp ((c:ℂ)*z)) (1:ℂ)
    rw [Complex.norm_exp,Complex.re_ofReal_mul,norm_one] at hh
    exact (sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzd hc.le)) 1).trans hh
  have hea : 0 < Real.exp (a*d)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ha hd))
  have heb : 0 < Real.exp (b*d)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hb hd))
  have hh := mul_le_mul
    (mul_le_mul (pow_le_pow_left₀ (div_nonneg hsp.le hH.le) hratio 8) (he a ha)
      hea.le (pow_nonneg (norm_nonneg _) 8))
    (he b hb) heb.le (mul_nonneg (pow_nonneg (norm_nonneg _) 8) (norm_nonneg _))
  rw [splineResidue,norm_mul,norm_mul,norm_pow]
  calc
    _ = (Real.sinh d/(1+|z.im|))^8*(Real.exp (a*d)-1)*(Real.exp (b*d)-1) := by
      rw [div_pow]
      ring
    _ ≤ _ := hh

/-- The exact residue varies by at most a uniform relative linear error in a positive strip. -/
theorem exists_splineResidue_relative_lipschitz {a b d D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    ∃ L : ℝ, 0 < L ∧ ∀ z w : ℂ,
      d ≤ z.re → z.re ≤ D → d ≤ w.re → w.re ≤ D → ‖z-w‖ ≤ 1 →
      ‖splineResidue a b z-splineResidue a b w‖ ≤ L*‖splineResidue a b w‖*‖z-w‖ := by
  let K := splineResidueLogBound a b d D
  have hK : 0 < K := splineResidueLogBound_pos ha hb hd D
  refine ⟨K*Real.exp K,mul_pos hK (Real.exp_pos _),?_⟩
  intro z w hzd hzD hwd hwD hzw
  by_cases hsame : z=w
  · subst z
    simp only [sub_self,norm_zero,mul_zero,le_refl]
  have hn : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsame)
  let v : ℝ → ℂ := fun t => w+(t:ℂ)*(z-w)
  have hv (t : ℝ) (ht : t ∈ Icc 0 1) : d ≤ (v t).re ∧ (v t).re ≤ D := by
    have hvre : (v t).re=(1-t)*w.re+t*z.re := by
      simp only [v,Complex.add_re,Complex.re_ofReal_mul,Complex.sub_re]
      ring
    rw [hvre]
    constructor
    · nlinarith only [mul_nonneg (by linarith only [ht.2] : 0 ≤ 1-t) (sub_nonneg.mpr hwd),
        mul_nonneg ht.1 (sub_nonneg.mpr hzd)]
    · nlinarith only [mul_nonneg (by linarith only [ht.2] : 0 ≤ 1-t) (sub_nonneg.mpr hwD),
        mul_nonneg ht.1 (sub_nonneg.mpr hzD)]
  let F : ℝ → ℂ := fun t => splineResidue a b (v t)
  let F' : ℝ → ℂ := fun t =>
    (splineResidue a b (v t)*splineResidueLogSlope a b (v t))*(z-w)
  have hder (t : ℝ) (ht : t ∈ Icc 0 1) : HasDerivAt F (F' t) t := by
    have hh := (hasDerivAt_splineResidue ha hb hd (hv t ht).1).comp (t:ℂ)
      (((hasDerivAt_id (t:ℂ)).mul_const (z-w)).const_add w)
    simpa only [F,F',v,one_mul,Function.comp_def,id_eq] using! hh.comp_ofReal
  have hbd (t : ℝ) (ht : t ∈ Icc 0 1) : ‖F' t-(0:ℂ)*F t‖ ≤ (K*‖z-w‖)*‖F t‖ := by
    simp only [F',F,zero_mul,sub_zero,norm_mul]
    calc
      _ ≤ (‖splineResidue a b (v t)‖*K)*‖z-w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (norm_splineResidueLogSlope_le ha hb hd (hv t ht).1 (hv t ht).2)
          (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hgr := HTGeometry.norm_sub_mul_exp_le_forward (mul_pos hK hn)
    (u := 0) (w := 1) zero_le_one hder hbd
  simp only [F,v,Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,add_zero,
    add_sub_cancel,sub_zero,Complex.exp_zero,mul_one,Complex.zero_re,Real.exp_zero] at hgr
  have he : Real.exp (K*‖z-w‖)-1 ≤ (K*‖z-w‖)*Real.exp K := by
    have hh := Real.add_one_le_exp (-(K*‖z-w‖))
    have hm : Real.exp (K*‖z-w‖)*Real.exp (-(K*‖z-w‖))=1 := by
      rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
    have he0 : Real.exp (K*‖z-w‖)-1 ≤ (K*‖z-w‖)*Real.exp (K*‖z-w‖) := by
      nlinarith only [mul_le_mul_of_nonneg_left hh (Real.exp_pos (K*‖z-w‖)).le,hm]
    exact he0.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hzw,hK.le])) (mul_nonneg hK.le hn.le))
  exact hgr.trans ((mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring))

#print axioms hasDerivAt_splineResidue
#print axioms norm_splineResidueLogSlope_le
#print axioms splineResidue_lower
#print axioms exists_splineResidue_relative_lipschitz
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
