import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineSparseSupport

/-!
# Prescribed spline quartets with bounded cone coupling

Exact spline nullseries give even real kernels with unattained positive width.
Positive cone moments cancel; reflected moments are bounded by coefficient
norm. The resulting mixed cone coupling is bounded by twenty.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Sign and conjugation complete each positive-quadrant atom to four points. -/
def prescribedSplineQuartetAtom {ι : Type*} (z : ι → ℂ) (i : ι × Bool × Bool) : ℂ :=
  if i.2.1 then -(if i.2.2 then (starRingEnd ℂ) (z i.1) else z i.1)
    else (if i.2.2 then (starRingEnd ℂ) (z i.1) else z i.1)

lemma prescribedSplineQuartetAtom_re {ι : Type*} (z : ι → ℂ) (i : ι × Bool × Bool) :
    (prescribedSplineQuartetAtom z i).re=if i.2.1 then -(z i.1).re else (z i.1).re := by
  rcases i with ⟨i,b,c⟩
  cases b <;> cases c <;> simp [prescribedSplineQuartetAtom]

lemma prescribedSplineQuartetAtom_injective {ι : Type*} {z : ι → ℂ}
    (hinj : Function.Injective z) (hre : ∀ i, 0 < (z i).re) (him : ∀ i, 0 < (z i).im) :
    Function.Injective (prescribedSplineQuartetAtom z) := by
  rintro ⟨i,b,c⟩ ⟨j,b',c'⟩ h
  have hr := congrArg Complex.re h
  rw [prescribedSplineQuartetAtom_re,prescribedSplineQuartetAtom_re] at hr
  have hb : b=b' := by
    cases b <;> cases b'
    · rfl
    · have he : (z i).re=-(z j).re := by simpa using hr
      exfalso
      linarith only [he,hre i,hre j]
    · have he : -(z i).re=(z j).re := by simpa using hr
      exfalso
      linarith only [he,hre i,hre j]
    · rfl
  subst b'
  have he : (if c then (starRingEnd ℂ) (z i) else z i)=
      (if c' then (starRingEnd ℂ) (z j) else z j) := by
    cases b <;> simpa [prescribedSplineQuartetAtom] using h
  have hi := congrArg Complex.im he
  have hc : c=c' := by
    cases c <;> cases c'
    · rfl
    · have hh : (z i).im=-(z j).im := by simpa using hi
      exfalso
      linarith only [hh,him i,him j]
    · have hh : -(z i).im=(z j).im := by simpa using hi
      exfalso
      linarith only [hh,him i,him j]
    · rfl
  subst c'
  have hz : z i=z j := by
    cases c
    · simpa using he
    · simpa using congrArg (starRingEnd ℂ) he
  have hij := hinj hz
  subst j
  rfl

def prescribedSplineLaplace {ι : Type*} (z : ι → ℂ) (t : ℝ) : ℂ :=
  ∑' i, splineMomentCoefficient (z i)*Complex.exp ((t : ℂ)*z i)

lemma star_prescribedSplineLaplace {ι : Type*} (z : ι → ℂ) (t : ℝ) :
    star (prescribedSplineLaplace z t)=prescribedSplineLaplace (fun i => (starRingEnd ℂ) (z i)) t := by
  rw [prescribedSplineLaplace,tsum_star]
  apply tsum_congr
  intro i
  change (starRingEnd ℂ) (splineMomentCoefficient (z i)*Complex.exp ((t : ℂ)*z i))=
    splineMomentCoefficient ((starRingEnd ℂ) (z i))*Complex.exp ((t : ℂ)*(starRingEnd ℂ) (z i))
  rw [map_mul,← Complex.exp_conj,map_mul,Complex.conj_ofReal,← splineMomentCoefficient_conj]

lemma prescribedSplineLaplace_neg {ι : Type*} (z : ι → ℂ) (t : ℝ) :
    prescribedSplineLaplace z (-t)=prescribedSplineLaplace (fun i => -z i) t := by
  simp only [prescribedSplineLaplace,splineMomentCoefficient_neg,Complex.ofReal_neg,neg_mul,mul_neg]

/-- The four terms correspond to `z`, `conj z`, `-z`, and `-conj z`,
with their exact spline coefficients. -/
def prescribedSplineQuartetKernel {ι : Type*} (z : ι → ℂ) (t : ℝ) : ℂ :=
  prescribedSplineLaplace z t+star (prescribedSplineLaplace z t)+
    prescribedSplineLaplace z (-t)+star (prescribedSplineLaplace z (-t))

lemma prescribedSplineQuartetKernel_eq {ι : Type*} (z : ι → ℂ) (t : ℝ) :
    prescribedSplineQuartetKernel z t=prescribedSplineLaplace z t+
      prescribedSplineLaplace (fun i => (starRingEnd ℂ) (z i)) t+
      prescribedSplineLaplace (fun i => -z i) t+
      prescribedSplineLaplace (fun i => -(starRingEnd ℂ) (z i)) t := by
  rw [prescribedSplineQuartetKernel,star_prescribedSplineLaplace,star_prescribedSplineLaplace,
    prescribedSplineLaplace_neg,prescribedSplineLaplace_neg]

lemma prescribedSplineQuartetKernel_neg {ι : Type*} (z : ι → ℂ) (t : ℝ) :
    prescribedSplineQuartetKernel z (-t)=prescribedSplineQuartetKernel z t := by
  simp only [prescribedSplineQuartetKernel,neg_neg]
  ring

lemma prescribedSplineQuartetKernel_hermitian {ι : Type*} (z : ι → ℂ) (t : ℝ) :
    prescribedSplineQuartetKernel z (-t)=star (prescribedSplineQuartetKernel z t) := by
  simp only [prescribedSplineQuartetKernel,neg_neg,star_add,star_star]
  ring

lemma norm_prescribedSplineLaplace_neg_le_two {ι : Type*} (z : ι → ℂ)
    (hs : Summable (fun i => ‖splineMomentCoefficient (z i)‖))
    (hmass : (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2)
    (hz : ∀ i, 0 ≤ (z i).re) {t : ℝ} (ht : 0 ≤ t) :
    ‖prescribedSplineLaplace z (-t)‖ ≤ 2 := by
  apply le_trans (tsum_of_norm_bounded hs.hasSum ?_) hmass
  intro i
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have he : Real.exp (-t*(z i).re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hz i))
  exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (mul_one _)

lemma norm_prescribedSplineQuartetKernel_zero_le_eight {ι : Type*} (z : ι → ℂ)
    (hs : Summable (fun i => ‖splineMomentCoefficient (z i)‖))
    (hmass : (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2)
    (hz : ∀ i, 0 ≤ (z i).re) : ‖prescribedSplineQuartetKernel z 0‖ ≤ 8 := by
  have h := norm_prescribedSplineLaplace_neg_le_two z hs hmass hz (le_refl (0 : ℝ))
  simp only [neg_zero] at h
  let x := prescribedSplineLaplace z 0
  change ‖x‖ ≤ 2 at h
  have h1 := norm_add_le x (star x)
  have h2 := norm_add_le (x+star x) x
  have h3 := norm_add_le (x+star x+x) (star x)
  rw [norm_star] at h1 h3
  simp only [prescribedSplineQuartetKernel,neg_zero]
  change ‖x+star x+x+star x‖ ≤ 8
  linarith only [h,h1,h2,h3]

lemma norm_prescribedSplineQuartetKernel_le_four {ι : Type*} (z : ι → ℂ)
    (hs : Summable (fun i => ‖splineMomentCoefficient (z i)‖))
    (hmass : (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2)
    (hz : ∀ i, 0 ≤ (z i).re) {t : ℝ} (ht : 0 ≤ t)
    (hzero : HasSum (fun i => splineMomentCoefficient (z i)*Complex.exp ((t : ℂ)*z i)) 0) :
    ‖prescribedSplineQuartetKernel z t‖ ≤ 4 := by
  have he : prescribedSplineLaplace z t=0 := hzero.tsum_eq
  simp only [prescribedSplineQuartetKernel,he,star_zero,zero_add]
  have h := norm_add_le (prescribedSplineLaplace z (-t)) (star (prescribedSplineLaplace z (-t)))
  rw [norm_star] at h
  linarith only [h,norm_prescribedSplineLaplace_neg_le_two z hs hmass hz ht]

/-- Cone cancellation controls the mixed coupling with the exact spline coefficients. -/
theorem prescribed_spline_quartet_coupling_le_twenty {ι : Type*} (z : ι → ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : Summable (fun i => ‖splineMomentCoefficient (z i)‖))
    (hmass : (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2)
    (hz : ∀ i, 0 ≤ (z i).re)
    (hzero : ∀ t : PositiveCone a b,
      HasSum (fun i => splineMomentCoefficient (z i)*Complex.exp ((t.val : ℂ)*z i)) 0)
    (m n : ℕ) :
    ‖prescribedSplineQuartetKernel z (m*a+n*b)-prescribedSplineQuartetKernel z (m*a)-
      prescribedSplineQuartetKernel z (n*b)+prescribedSplineQuartetKernel z 0‖ ≤ 20 := by
  by_cases hm : m=0
  · subst m
    simp only [Nat.cast_zero,zero_mul,zero_add]
    have he : prescribedSplineQuartetKernel z (n*b)-prescribedSplineQuartetKernel z 0-
        prescribedSplineQuartetKernel z (n*b)+prescribedSplineQuartetKernel z 0=0 := by ring
    rw [he]
    norm_num
  by_cases hn : n=0
  · subst n
    simp only [Nat.cast_zero,zero_mul,add_zero]
    have he : prescribedSplineQuartetKernel z (m*a)-prescribedSplineQuartetKernel z (m*a)-
        prescribedSplineQuartetKernel z 0+prescribedSplineQuartetKernel z 0=0 := by ring
    rw [he]
    norm_num
  have hmpos : 0 < (m : ℝ)*a := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) ha
  have hnpos : 0 < (n : ℝ)*b := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hb
  let ta : PositiveCone a b := ⟨m*a,hmpos,⟨(m,0),by simp [coneFrequency]⟩⟩
  let tb : PositiveCone a b := ⟨n*b,hnpos,⟨(0,n),by simp [coneFrequency]⟩⟩
  let tab : PositiveCone a b := ⟨m*a+n*b,add_pos hmpos hnpos,⟨(m,n),rfl⟩⟩
  have hka := norm_prescribedSplineQuartetKernel_le_four z hs hmass hz hmpos.le (hzero ta)
  have hkb := norm_prescribedSplineQuartetKernel_le_four z hs hmass hz hnpos.le (hzero tb)
  have hkab := norm_prescribedSplineQuartetKernel_le_four z hs hmass hz
    (add_pos hmpos hnpos).le (hzero tab)
  have hk0 := norm_prescribedSplineQuartetKernel_zero_le_eight z hs hmass hz
  have h1 := norm_add_le (prescribedSplineQuartetKernel z (m*a+n*b)-
    prescribedSplineQuartetKernel z (m*a)-prescribedSplineQuartetKernel z (n*b))
    (prescribedSplineQuartetKernel z 0)
  have h2 := norm_sub_le (prescribedSplineQuartetKernel z (m*a+n*b)-prescribedSplineQuartetKernel z (m*a))
    (prescribedSplineQuartetKernel z (n*b))
  have h3 := norm_sub_le (prescribedSplineQuartetKernel z (m*a+n*b)) (prescribedSplineQuartetKernel z (m*a))
  linarith only [h1,h2,h3,hka,hkb,hkab,hk0]


/-- Distinct unit-multiplicity spline quartets with unattained positive width
can have bounded coupling on an actual two-prime natural cone. -/
theorem exists_two_prime_prescribed_spline_cone_model {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D : ℝ}
    (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ),
      Function.Injective z ∧ Function.Injective (prescribedSplineQuartetAtom z) ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧ (∀ i, 1 ≤ (z i).im) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, splineMomentCoefficient (z i) ≠ 0) ∧
      Summable (fun i => ‖splineMomentCoefficient (z i)‖) ∧
      (∑' i, ‖splineMomentCoefficient (z i)‖) ≤ 2 ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ t : ℝ, Summable (fun i => splineMomentCoefficient (z i)*Complex.exp ((t : ℂ)*z i))) ∧
      (∀ t : PositiveCone (Real.log p) (Real.log q),
        HasSum (fun i => splineMomentCoefficient (z i)*Complex.exp ((t.val : ℂ)*z i)) 0) ∧
      (∀ m n : ℕ, ‖prescribedSplineQuartetKernel z (m*Real.log p+n*Real.log q)-
        prescribedSplineQuartetKernel z (m*Real.log p)-prescribedSplineQuartetKernel z (n*Real.log q)+
        prescribedSplineQuartetKernel z 0‖ ≤ 20) := by
  obtain ⟨ι,hι,z,hinj,hstrip,him,hwidth,hcoeff,hs,hmass,hcount,hall,hzero⟩ :=
    exists_two_prime_prescribed_spline_nullseries hp hq hpq hd hdD
  refine ⟨ι,hι,z,hinj,prescribedSplineQuartetAtom_injective hinj
    (fun i => hd.trans_le (hstrip i).1) (fun i => zero_lt_one.trans_le (him i)),
    hstrip,him,hwidth,hcoeff,hs,hmass,hcount,hall,hzero,?_⟩
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  exact prescribed_spline_quartet_coupling_le_twenty z ha hb hs hmass
    (fun i => hd.le.trans (hstrip i).1) hzero

#print axioms prescribedSplineQuartetKernel_eq
#print axioms prescribed_spline_quartet_coupling_le_twenty
#print axioms exists_two_prime_prescribed_spline_cone_model
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
