import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.RVMCompletionCounts
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PrescribedSplineQuartets
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.PSeries

/-!
# Critical-line slots with exact nonzero spline weights

Rational ordinates inside each unit block avoid the sine zeros. Logarithmic
block sizes and eighth-power coefficient decay give an absolutely summable
critical divisor whose paired Laplace kernel is uniformly bounded.
-/

set_option autoImplicit false
noncomputable section
open Finset Complex
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def criticalSplineSlotHeight (j n : ℕ) (k : Fin n) : ℝ :=
  (((j:ℚ)+1+((k.val:ℚ)+1)/((n:ℚ)+1) : ℚ):ℝ)

def criticalSplineSlotAtom (j n : ℕ) (k : Fin n) : ℂ :=
  (criticalSplineSlotHeight j n k:ℂ)*Complex.I

lemma criticalSplineSlotHeight_bounds (j n : ℕ) (k : Fin n) :
    (j:ℝ)+1<criticalSplineSlotHeight j n k ∧
      criticalSplineSlotHeight j n k<(j:ℝ)+2 := by
  have hk : (k.val:ℝ)<n := by exact_mod_cast k.isLt
  have hd : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hlo : 0<((k.val:ℝ)+1)/((n:ℝ)+1) := by positivity
  have hhi : ((k.val:ℝ)+1)/((n:ℝ)+1)<1 := by
    rw [div_lt_iff₀ hd]
    linarith only [hk]
  unfold criticalSplineSlotHeight
  push_cast
  constructor <;> linarith only [hlo,hhi]

lemma criticalSplineSlotHeight_injective (j n : ℕ) :
    Function.Injective (criticalSplineSlotHeight j n) := by
  intro k l he
  unfold criticalSplineSlotHeight at he
  push_cast at he
  have hd : (n:ℝ)+1≠0 := by positivity
  field_simp [hd] at he
  apply Fin.ext
  have hv : (k.val:ℝ)=l.val := by linarith only [he]
  exact_mod_cast hv

lemma sin_ratCast_ne_zero {r : ℚ} (hr : r≠0) : Real.sin (r:ℝ)≠0 := by
  intro hsin
  obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hrR : (r:ℝ)≠0 := by exact_mod_cast hr
  have hn0 : n≠0 := by
    intro he
    subst n
    simp only [Int.cast_zero,zero_mul] at hn
    exact hrR hn.symm
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn0
  apply irrational_pi.ne_rat (r/(n:ℚ))
  push_cast
  exact (eq_div_iff hnR).mpr (by simpa only [mul_comm] using hn)

/-- The exact spline coefficient on the critical line is the eighth power of sinc. -/
lemma splineMomentCoefficient_imaginary_eq {γ : ℝ} (hγ : γ≠0) :
    splineMomentCoefficient ((γ:ℂ)*Complex.I)=(((Real.sin γ/γ)^8:ℝ):ℂ) := by
  rw [splineMomentCoefficient,Complex.sinh_mul_I,← Complex.ofReal_sin]
  push_cast
  congr 1
  field_simp [Complex.I_ne_zero,Complex.ofReal_ne_zero.mpr hγ]

lemma criticalSplineSlot_coefficient_ne_zero (j n : ℕ) (k : Fin n) :
    splineMomentCoefficient (criticalSplineSlotAtom j n k)≠0 := by
  have hb := (criticalSplineSlotHeight_bounds j n k).1
  have hp : 0<criticalSplineSlotHeight j n k := by
    have hj := Nat.cast_nonneg (α := ℝ) j
    linarith only [hb,hj]
  let r : ℚ := (j:ℚ)+1+((k.val:ℚ)+1)/((n:ℚ)+1)
  have he : criticalSplineSlotHeight j n k=(r:ℝ) := rfl
  have hr : r≠0 := by
    intro hr
    apply hp.ne'
    rw [he,hr,Rat.cast_zero]
  have hs : Real.sin (criticalSplineSlotHeight j n k)≠0 := by
    rw [he]
    exact sin_ratCast_ne_zero hr
  rw [criticalSplineSlotAtom,splineMomentCoefficient_imaginary_eq hp.ne']
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 8 (div_ne_zero hs hp.ne'))

lemma criticalSplineSlot_coefficient_norm_le (j n : ℕ) (k : Fin n) :
    ‖splineMomentCoefficient (criticalSplineSlotAtom j n k)‖≤1/((j:ℝ)+1)^8 := by
  have hb := (criticalSplineSlotHeight_bounds j n k).1
  have hj : (0:ℝ)<(j:ℝ)+1 := by positivity
  have hp : 0<criticalSplineSlotHeight j n k := hj.trans hb
  rw [criticalSplineSlotAtom,splineMomentCoefficient_imaginary_eq hp.ne',
    Complex.norm_real,Real.norm_eq_abs,abs_pow,abs_div,abs_of_pos hp]
  calc
    _ ≤ (1/((j:ℝ)+1))^8 := by
      apply pow_le_pow_left₀ (by positivity)
      exact (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) hp.le).trans
        (div_le_div_of_nonneg_left zero_le_one hj hb.le)
    _ = _ := by rw [div_pow,one_pow]

/-- Any subset of the reserved rational slots inherits the same coefficient bounds. -/
def rvmCriticalSlotAtom (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1))
    (i : (j : ℕ) × Fin (K j)) : ℂ :=
  criticalSplineSlotAtom i.1 (rvmCompletionBlockSize (i.1+1))
    ⟨i.2.val,lt_of_lt_of_le i.2.isLt (hK i.1)⟩

lemma rvmCriticalSlotAtom_re (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (i : (j : ℕ) × Fin (K j)) :
    (rvmCriticalSlotAtom K hK i).re=0 := by
  simp only [rvmCriticalSlotAtom,criticalSplineSlotAtom,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]

lemma rvmCriticalSlotAtom_im_bounds (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (i : (j : ℕ) × Fin (K j)) :
    (i.1:ℝ)+1<(rvmCriticalSlotAtom K hK i).im ∧
      (rvmCriticalSlotAtom K hK i).im<(i.1:ℝ)+2 := by
  simpa only [rvmCriticalSlotAtom,criticalSplineSlotAtom,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,zero_mul,add_zero] using
    criticalSplineSlotHeight_bounds i.1 (rvmCompletionBlockSize (i.1+1))
      ⟨i.2.val,lt_of_lt_of_le i.2.isLt (hK i.1)⟩

lemma rvmCriticalSlotAtom_coefficient_ne_zero (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (i : (j : ℕ) × Fin (K j)) :
    splineMomentCoefficient (rvmCriticalSlotAtom K hK i)≠0 :=
  criticalSplineSlot_coefficient_ne_zero _ _ _

lemma conj_rvmCriticalSlotAtom (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (i : (j : ℕ) × Fin (K j)) :
    (starRingEnd ℂ) (rvmCriticalSlotAtom K hK i)= -rvmCriticalSlotAtom K hK i := by
  simp [rvmCriticalSlotAtom,criticalSplineSlotAtom]

theorem summable_rvmCriticalSlot_coefficient (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) :
    Summable (fun i : (j : ℕ) × Fin (K j) =>
      ‖splineMomentCoefficient (rvmCriticalSlotAtom K hK i)‖) := by
  obtain ⟨C,hC,hsize⟩ := exists_rvmCompletionBlockSize_linear_bound
  have hp0 : Summable (fun j : ℕ => 1/(j:ℝ)^7) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp : Summable (fun j : ℕ => 1/((j:ℝ)+1)^7) := by
    have hh := hp0.comp_injective (show Function.Injective (fun j : ℕ => j+1) by
      intro i j hij
      change i+1=j+1 at hij
      omega)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using hh
  have hn (j : ℕ) : (K j:ℝ)≤2*C*((j:ℝ)+1) := by
    have hk : (K j:ℝ)≤rvmCompletionBlockSize (j+1) := by exact_mod_cast hK j
    have hs := hsize (j+1)
    push_cast at hs
    have hj := Nat.cast_nonneg (α := ℝ) j
    nlinarith only [hk,hs,mul_nonneg hC.le hj]
  rw [summable_sigma_of_nonneg
    (f := fun i : (j : ℕ) × Fin (K j) => ‖splineMomentCoefficient (rvmCriticalSlotAtom K hK i)‖)
    (fun _ => norm_nonneg _)]
  refine ⟨fun _ => Summable.of_finite,?_⟩
  apply Summable.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => norm_nonneg _)
    (fun j => ?_) (hp.mul_left (2*C))
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _k : Fin (K j),1/((j:ℝ)+1)^8 :=
      sum_le_sum fun k _ => criticalSplineSlot_coefficient_norm_le j _ _
    _ = (K j:ℝ)*(1/((j:ℝ)+1)^8) := by
      rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ ≤ (2*C*((j:ℝ)+1))*(1/((j:ℝ)+1)^8) :=
      mul_le_mul_of_nonneg_right (hn j) (by positivity)
    _ = (2*C)*(1/((j:ℝ)+1)^7) := by
      field_simp [show (j:ℝ)+1≠0 by positivity]

def prescribedSplinePairKernel {ι : Type*} (z : ι → ℂ) (t : ℝ) : ℂ :=
  prescribedSplineLaplace z t+prescribedSplineLaplace z (-t)

lemma prescribedSplinePairKernel_neg {ι : Type*} (z : ι → ℂ) (t : ℝ) :
    prescribedSplinePairKernel z (-t)=prescribedSplinePairKernel z t := by
  simp only [prescribedSplinePairKernel,neg_neg]
  ring

lemma norm_rvmCriticalSlot_moment (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1))
    (i : (j : ℕ) × Fin (K j)) (t : ℝ) :
    ‖splineMomentCoefficient (rvmCriticalSlotAtom K hK i)*
      Complex.exp ((t:ℂ)*rvmCriticalSlotAtom K hK i)‖=
      ‖splineMomentCoefficient (rvmCriticalSlotAtom K hK i)‖ := by
  rw [norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,rvmCriticalSlotAtom_re,
    mul_zero,zero_mul,sub_zero,Real.exp_zero,mul_one]

theorem summable_rvmCriticalSlot_moment (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (t : ℝ) :
    Summable (fun i : (j : ℕ) × Fin (K j) =>
      splineMomentCoefficient (rvmCriticalSlotAtom K hK i)*
        Complex.exp ((t:ℂ)*rvmCriticalSlotAtom K hK i)) := by
  apply Summable.of_norm
  exact (summable_rvmCriticalSlot_coefficient K hK).congr fun i =>
    (norm_rvmCriticalSlot_moment K hK i t).symm

theorem norm_rvmCriticalSlot_pairKernel_le (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (t : ℝ) :
    ‖prescribedSplinePairKernel (rvmCriticalSlotAtom K hK) t‖≤
      2*∑' i,‖splineMomentCoefficient (rvmCriticalSlotAtom K hK i)‖ := by
  have hs := summable_rvmCriticalSlot_coefficient K hK
  have hL (u : ℝ) : ‖prescribedSplineLaplace (rvmCriticalSlotAtom K hK) u‖≤
      ∑' i,‖splineMomentCoefficient (rvmCriticalSlotAtom K hK i)‖ :=
    tsum_of_norm_bounded hs.hasSum fun i => (norm_rvmCriticalSlot_moment K hK i u).le
  exact (norm_add_le _ _).trans ((add_le_add (hL t) (hL (-t))).trans_eq (by ring))

theorem star_rvmCriticalSlot_pairKernel (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (t : ℝ) :
    star (prescribedSplinePairKernel (rvmCriticalSlotAtom K hK) t)=
      prescribedSplinePairKernel (rvmCriticalSlotAtom K hK) t := by
  have hs (u : ℝ) : star (prescribedSplineLaplace (rvmCriticalSlotAtom K hK) u)=
      prescribedSplineLaplace (rvmCriticalSlotAtom K hK) (-u) := by
    rw [star_prescribedSplineLaplace,prescribedSplineLaplace_neg]
    congr 1
    funext i
    exact conj_rvmCriticalSlotAtom K hK i
  change star (prescribedSplineLaplace (rvmCriticalSlotAtom K hK) t+
    prescribedSplineLaplace (rvmCriticalSlotAtom K hK) (-t))=_
  rw [star_add,hs t,hs (-t),neg_neg,prescribedSplinePairKernel]
  ring

theorem rvmCriticalSlot_pair_coupling_le (K : ℕ → ℕ)
    (hK : ∀ j,K j≤rvmCompletionBlockSize (j+1)) (x y : ℝ) :
    ‖prescribedSplinePairKernel (rvmCriticalSlotAtom K hK) (x+y)-
      prescribedSplinePairKernel (rvmCriticalSlotAtom K hK) x-
      prescribedSplinePairKernel (rvmCriticalSlotAtom K hK) y+
      prescribedSplinePairKernel (rvmCriticalSlotAtom K hK) 0‖≤
      8*∑' i,‖splineMomentCoefficient (rvmCriticalSlotAtom K hK i)‖ := by
  let F := prescribedSplinePairKernel (rvmCriticalSlotAtom K hK)
  have h1 := norm_add_le (F (x+y)-F x-F y) (F 0)
  have h2 := norm_sub_le (F (x+y)-F x) (F y)
  have h3 := norm_sub_le (F (x+y)) (F x)
  have hx := norm_rvmCriticalSlot_pairKernel_le K hK x
  have hy := norm_rvmCriticalSlot_pairKernel_le K hK y
  have hxy := norm_rvmCriticalSlot_pairKernel_le K hK (x+y)
  have h0 := norm_rvmCriticalSlot_pairKernel_le K hK 0
  change ‖F (x+y)-F x-F y+F 0‖≤_
  change ‖F x‖≤_ at hx
  change ‖F y‖≤_ at hy
  change ‖F (x+y)‖≤_ at hxy
  change ‖F 0‖≤_ at h0
  linarith only [h1,h2,h3,hx,hy,hxy,h0]

#print axioms criticalSplineSlot_coefficient_ne_zero
#print axioms criticalSplineSlot_coefficient_norm_le
#print axioms summable_rvmCriticalSlot_coefficient
#print axioms summable_rvmCriticalSlot_moment
#print axioms norm_rvmCriticalSlot_pairKernel_le
#print axioms star_rvmCriticalSlot_pairKernel
#print axioms rvmCriticalSlot_pair_coupling_le
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
