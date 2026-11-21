import GaloisForLFunctions.GaloisTheoryOfZeros.JensenQuartetExhaustion
import GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Focal distortion of the unshifted Jensen polynomials

The upper-half-plane distortion principle of Koskela et al., Lemma 2.3,
has explicit Euclidean factors for a real boundary root. The reverse
triangle inequality at the two foci `i` and `-i` gives the lower one.
Multiplying over the roots yields a one-anchor test. A strict violation at
a rational complex argument detects a nonreal root without locating it.
-/

open Complex Polynomial Filter Topology
open FiniteFreeProbability RHTower
noncomputable section
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Difference of the distances from the two foci, divided by their separation. -/
def focalDifference (z : ℂ) : ℝ := |‖z+I‖-‖z-I‖|/2

/-- Sum of the distances from the two foci, divided by their separation. -/
def focalSum (z : ℂ) : ℝ := (‖z+I‖+‖z-I‖)/2

private theorem focal_squares (z : ℂ) : ‖z+I‖^2-‖z-I‖^2=4*z.im := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.sub_re,
    Complex.add_im,Complex.sub_im,Complex.I_re,Complex.I_im,add_zero,sub_zero]
  ring

theorem focalDifference_pos_iff (z : ℂ) : 0<focalDifference z ↔ z.im≠0 := by
  have id := focal_squares z
  have he : ‖z+I‖=‖z-I‖ ↔ z.im=0 := by
    constructor
    · intro h
      rw [h,sub_self] at id
      linarith only [id]
    · intro h
      rw [h,mul_zero] at id
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (sub_eq_zero.mp id)
  simp only [focalDifference,div_pos_iff_of_pos_right (by norm_num : (0:ℝ)<2),abs_pos,
    sub_ne_zero,ne_eq,he]

/-- The product recovers height. The two focal factors therefore contain
both the radial scale and the hyperbolic distortion from the anchor. -/
theorem focal_product (z : ℂ) : focalDifference z*focalSum z=|z.im| := by
  have h := congrArg abs (focal_squares z)
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),
    abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤4)] at h
  unfold focalDifference focalSum
  linarith only [h]

theorem focal_half_plane_factors (z : UpperHalfPlane) :
    focalSum z=Real.sqrt z.im*Real.exp (dist z UpperHalfPlane.I/2) ∧
      focalDifference z=Real.sqrt z.im*Real.exp (-(dist z UpperHalfPlane.I/2)) := by
  have hy := Real.sqrt_pos.mpr z.im_pos
  have h := UpperHalfPlane.exp_half_dist z UpperHalfPlane.I
  simp only [UpperHalfPlane.I_im,mul_one,UpperHalfPlane.coe_I,Complex.conj_I,
    dist_eq_norm,sub_neg_eq_add] at h
  have h' := (eq_div_iff (mul_pos (by norm_num) hy).ne').mp h
  have E : focalSum z=Real.sqrt z.im*Real.exp (dist z UpperHalfPlane.I/2) := by
    unfold focalSum
    linarith only [h']
  refine ⟨E,?_⟩
  rw [Real.exp_neg,←div_eq_mul_inv]
  apply (eq_div_iff (Real.exp_ne_zero _)).mpr
  apply mul_left_cancel₀ hy.ne'
  calc _ = focalDifference z*(Real.sqrt z.im*Real.exp (dist z UpperHalfPlane.I/2)) := by ring
       _ = z.im := by rw [←E,focal_product]; exact abs_of_pos z.im_pos
       _ = _ := (Real.mul_self_sqrt z.im_pos.le).symm

/-- A boundary root distorts between the focal difference and the focal
sum relative to its distance from the anchor. -/
theorem real_root_focal_bounds (z : ℂ) (r : ℝ) :
    focalDifference z*‖I-(r:ℂ)‖ ≤ ‖z-(r:ℂ)‖ ∧ ‖z-(r:ℂ)‖ ≤ focalSum z*‖I-(r:ℂ)‖ := by
  let A := (z+I)*((r:ℂ)-I)
  let B := (z-I)*((r:ℂ)+I)
  have hr : ‖(r:ℂ)+I‖=‖(r:ℂ)-I‖ := by
    simpa only [map_sub,Complex.conj_ofReal,Complex.conj_I,sub_neg_eq_add] using
      Complex.norm_conj ((r:ℂ)-I)
  have hA : ‖A‖=‖z+I‖*‖I-(r:ℂ)‖ := by dsimp only [A]; rw [norm_mul,norm_sub_rev (r:ℂ) I]
  have hB : ‖B‖=‖z-I‖*‖I-(r:ℂ)‖ := by dsimp only [B]; rw [norm_mul,hr,norm_sub_rev (r:ℂ) I]
  have diff : A-B=-(2:ℂ)*I*(z-r) := by dsimp only [A,B]; ring
  have hab : ‖A-B‖=2*‖z-(r:ℂ)‖ := by rw [diff,norm_mul,norm_mul,norm_neg,Complex.norm_I]; norm_num
  have low := abs_norm_sub_norm_le A B
  rw [hab,hA,hB,←sub_mul,abs_mul,abs_of_nonneg (norm_nonneg _)] at low
  have high := norm_sub_le A B
  rw [hab,hA,hB] at high
  unfold focalDifference focalSum
  constructor <;> linarith only [low,high]

private theorem roots_focal_product (l : Multiset ℂ) (z : ℂ) (h : ∀ a∈l, a.im=0) :
    focalDifference z^l.card*‖(l.map (fun r => I-r)).prod‖ ≤ ‖(l.map (fun r => z-r)).prod‖ ∧
      ‖(l.map (fun r => z-r)).prod‖ ≤ focalSum z^l.card*‖(l.map (fun r => I-r)).prod‖ := by
  induction l using Multiset.induction_on with
  | empty => simp
  | cons r l ih =>
    have hr := h r (Multiset.mem_cons_self ..)
    have he : (r.re:ℂ)=r := Complex.ext rfl (by simp [hr])
    have H := real_root_focal_bounds z r.re
    rw [he] at H
    have T := ih (fun a ha => h a (Multiset.mem_cons_of_mem ha))
    have h₀ : 0≤focalDifference z := div_nonneg (abs_nonneg _) (by norm_num)
    have h₁ : 0≤focalSum z := div_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    simp only [Multiset.card_cons,Multiset.map_cons,Multiset.prod_cons,norm_mul,pow_succ]
    constructor
    · have hs := mul_le_mul H.1 T.1 (mul_nonneg (pow_nonneg h₀ _) (norm_nonneg _)) (norm_nonneg _)
      linarith only [hs]
    · have hs := mul_le_mul H.2 T.2 (norm_nonneg _) (mul_nonneg h₁ (norm_nonneg _))
      linarith only [hs]

/-- Focal annulus for the values of any polynomial with only real roots.
The two radii involve only the test point, anchor modulus, and degree. -/
theorem real_roots_polynomial_focal_bounds (p : ℂ[X]) (h : ∀ a ∈ p.roots, a.im=0) (z : ℂ) :
    focalDifference z^p.natDegree*‖p.eval I‖≤‖p.eval z‖ ∧
      ‖p.eval z‖≤focalSum z^p.natDegree*‖p.eval I‖ := by
  have hp := IsAlgClosed.splits p
  have H := roots_focal_product p.roots z h
  rw [hp.natDegree_eq_card_roots,hp.eval_eq_prod_roots I,hp.eval_eq_prod_roots z,norm_mul,norm_mul]
  exact ⟨by linarith only [mul_le_mul_of_nonneg_left H.1 (norm_nonneg p.leadingCoeff)],
    by linarith only [mul_le_mul_of_nonneg_left H.2 (norm_nonneg p.leadingCoeff)]⟩

/-- A countable dense set of test points with rational Cartesian coordinates. -/
def rationalFocalPoint (v : ℚ × ℚ) : ℂ := ⟨v.1,v.2⟩

private theorem rational_focal_dense : DenseRange rationalFocalPoint := by
  let F (p : ℝ × ℝ) : ℂ := ⟨p.1,p.2⟩
  have hF : Function.Surjective F := fun z => ⟨(z.re,z.im),Complex.ext rfl rfl⟩
  have hc : Continuous F := Complex.equivRealProdCLM.symm.continuous
  have hrat : DenseRange (fun q : ℚ => (q:ℝ)) := Rat.denseRange_cast
  exact hF.denseRange.comp (hrat.prodMap hrat) hc

/-- At a nonzero anchor, just the lower inequality on rational complex
arguments characterizes real-rootedness. A nonreal root forces strict
failure on an open set of neighboring arguments. -/
theorem real_roots_iff_rational_focal_lower (p : ℂ[X]) (hI : p.eval I≠0) :
    (∀ a∈p.roots, a.im=0) ↔ ∀ v : ℚ × ℚ,
      focalDifference (rationalFocalPoint v)^p.natDegree*‖p.eval I‖ ≤ ‖p.eval (rationalFocalPoint v)‖ := by
  constructor
  · exact fun h v => (real_roots_polynomial_focal_bounds p h _).1
  · intro h a ha
    by_contra hn
    have bound := rational_focal_dense.induction_on a
      (p:=fun z : ℂ => focalDifference z^p.natDegree*‖p.eval I‖ ≤ ‖p.eval z‖)
      (isClosed_le (by unfold focalDifference; fun_prop) p.continuous.norm) h
    have hv : p.eval a=0 := Polynomial.isRoot_of_mem_roots ha
    rw [hv,norm_zero] at bound
    exact (mul_pos (pow_pos ((focalDifference_pos_iff _).mpr hn) _) (norm_pos_iff.mpr hI)).not_ge bound

/-- RH is equivalent to the fixed-anchor lower bound on rational arguments
along cofinally many unshifted degrees. -/
theorem rh_iff_cofinal_rational_focal_bounds :
    RiemannHypothesis ↔ ∃ᶠ d : ℕ in atTop, ∀ v : ℚ × ℚ,
      focalDifference (rationalFocalPoint v)^d * ‖(xiJensen (1/2) d).eval I‖ ≤
        ‖(xiJensen (1/2) d).eval (rationalFocalPoint v)‖ := by
  have criterion (d : ℕ) := real_roots_iff_rational_focal_lower (xiJensen (1/2) d)
    (by simpa only [Complex.ofReal_one,mul_one] using centered_jensen_no_imaginary_root d (t:=1) one_ne_zero)
  simp only [natDegree_xiJensen] at criterion
  constructor
  · intro h
    apply Frequently.of_forall
    intro d
    apply (criterion d).mp
    intro z hz
    apply im_eq_zero_of_isRoot_jensenRev_xiSeries h d
    have he := Polynomial.isRoot_of_mem_roots hz
    simpa only [xiJensen,mk_xiShiftCoeff_half] using he
  · intro h
    have no : ∀ m, jensenQuartetCount m≤0 := by
      intro m
      obtain ⟨n,h₁,hm⟩ := (h.and_eventually (eventually_ge_atTop m)).exists
      apply (jensenQuartetCount_mono hm).trans
      have hr := (criterion n).mpr h₁
      have emp : ((xiJensen (1/2) n).roots.filter (fun z => 0<z.re ∧ 0<z.im))=0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro z hz
        obtain ⟨hz,_,hp⟩ := Multiset.mem_filter.mp hz
        exact hp.ne' (hr z hz)
      rw [jensenQuartetCount,emp,Multiset.card_zero]
    have H := (offLine_count_le_iff_quartet_count 0).mpr no
    norm_num only [Nat.mul_zero,Nat.cast_zero,nonpos_iff_eq_zero,Set.encard_eq_zero,
      Set.eq_empty_iff_forall_notMem,Set.mem_setOf_eq,not_not] at H
    exact riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero.mpr H

end GaloisForLFunctions.GaloisTheoryOfZeros
