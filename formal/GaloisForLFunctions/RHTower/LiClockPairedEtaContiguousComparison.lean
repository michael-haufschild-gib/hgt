import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousSource
import GaloisForLFunctions.RHTower.LiClockPairedEtaPositiveCompletion
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
open Complex Filter Topology MeasureTheory Set Metric
open scoped ComplexConjugate
namespace RHTower
noncomputable section

def liClockPairedEtaContiguousReciprocal (L : ℝ) (k : ℤ) : ℂ :=
  (1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(L:ℂ))⁻¹

private theorem exp_pos_ne_one {L : ℝ} {s : ℂ} (hL : 0 < L) (hs : 0 < s.re) :
    Complex.exp ((L:ℂ)*s) ≠ 1 := by
  intro he
  have hn := congrArg norm he
  rw [Complex.norm_exp,norm_one] at hn
  have hre : ((L:ℂ)*s).re=L*s.re := by simp
  rw [hre] at hn
  have hgt : 1 < Real.exp (L*s.re) := Real.one_lt_exp_iff.mpr (mul_pos hL hs)
  linarith

private def contiguousAffine (L : ℝ) : ℂ := I*(L:ℂ)/(2*(Real.pi:ℂ))

private theorem contiguousAffine_ne_zero {L : ℝ} (hL : 0 < L) : contiguousAffine L ≠ 0 := by
  exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hL.ne'))
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

private theorem contiguousAffine_center_mem_upper {L : ℝ} (hL : 0 < L) :
    contiguousAffine L*(1/2) ∈ UpperHalfPlane.upperHalfPlaneSet := by
  have heq : contiguousAffine L*(1/2)=((L/(4*Real.pi):ℝ):ℂ)*I := by
    unfold contiguousAffine
    push_cast
    ring
  rw [heq]
  change 0 < (((L/(4*Real.pi):ℝ):ℂ)*I).im
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,
    Complex.I_re,mul_one,mul_zero,add_zero]
  positivity

private theorem contiguousMoment_eq_scaled {L : ℝ} (hL : 0 < L) (p : ℕ) :
    (∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^p) =
      contiguousAffine L^p*∑' k : ℤ,1/(contiguousAffine L*(1/2)+(k:ℂ))^p := by
  let a := contiguousAffine L
  have ha : a ≠ 0 := contiguousAffine_ne_zero hL
  have hl : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht (k : ℤ) : a^p*(1/(a*(1/2)+(k:ℂ))^p)=
      liClockPairedEtaContiguousReciprocal L (-k)^p := by
    have hh : a*(1/2)+(k:ℂ)=a*(1/2+2*(Real.pi:ℂ)*I*(-(k:ℂ))/(L:ℂ)) := by
      dsimp [a,contiguousAffine]
      field_simp [hl,hp]
      ring_nf
      norm_num [Complex.I_sq]
    rw [hh,mul_pow,one_div,mul_inv_rev,mul_comm,mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ ha),mul_one,← inv_pow]
    simp only [liClockPairedEtaContiguousReciprocal,Int.cast_neg]
  symm
  calc
    _ = ∑' k : ℤ,liClockPairedEtaContiguousReciprocal L (-k)^p := by
      rw [← tsum_mul_left]
      exact tsum_congr ht
    _ = _ := by
      simpa only [Equiv.neg_apply] using
        (Equiv.neg ℤ).tsum_eq (fun k : ℤ => liClockPairedEtaContiguousReciprocal L k^p)

private theorem contiguousConnection_eq_cot {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 0 < s.re) :
    liClockPairedEtaContiguousConnection L s =
      -(L:ℂ)/2+contiguousAffine L*((Real.pi:ℂ)*Complex.cot
        ((Real.pi:ℂ)*(contiguousAffine L*s))) := by
  have he : Complex.exp (2*(Real.pi:ℂ)*I*(contiguousAffine L*s))=
      (Complex.exp ((L:ℂ)*s))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    dsimp [contiguousAffine]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    norm_num [Complex.I_sq]
  rw [Complex.cot_pi_eq_exp_ratio,he]
  unfold liClockPairedEtaContiguousConnection contiguousAffine
  have hd : Complex.exp ((L:ℂ)*s)-1 ≠ 0 := sub_ne_zero.mpr (exp_pos_ne_one hL hs)
  field_simp [hd,Complex.exp_ne_zero,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,Complex.I_ne_zero]
  ring_nf

theorem iteratedDeriv_liClockPairedEtaContiguousConnection_odd {L : ℝ}
    (hL : 0 < L) (j : ℕ) :
    iteratedDeriv (2*j+1) (liClockPairedEtaContiguousConnection L) (1/2:ℂ) =
      -((2*j+1).factorial:ℂ)*∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^(2*j+2) := by
  let a := contiguousAffine L
  let x := a*(1/2)
  let f : ℂ → ℂ := fun w => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*w)
  have hx : x ∈ UpperHalfPlane.upperHalfPlaneSet := contiguousAffine_center_mem_upper hL
  have hf : ContDiffAt ℂ (2*j+1) f x := by
    have hi := UpperHalfPlane.coe_mem_integerComplement ⟨x,hx⟩
    have hh : ContDiffWithinAt ℂ (2*j+1) f UpperHalfPlane.upperHalfPlaneSet x :=
      contDiffWithinAt_const.mul (cot_pi_mul_contDiffWithinAt (2*j+1) hi)
    exact hh.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hx)
  have hcot : iteratedDeriv (2*j+1) f x =
      (-1:ℂ)^(2*j+1)*((2*j+1).factorial:ℂ)*
        ∑' k : ℤ,1/(x+(k:ℂ))^(2*j+2) := by
    rw [← iteratedDerivWithin_eq_iteratedDeriv
      UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn hf hx]
    simpa only [Nat.add_assoc] using
      iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k:=2*j+1) (by omega) hx
  have heq : liClockPairedEtaContiguousConnection L =ᶠ[𝓝 (1/2:ℂ)]
      fun s : ℂ => -(L:ℂ)/2+a*f (a*s+0) := by
    have hre : ∀ᶠ s : ℂ in 𝓝 (1/2:ℂ),0<s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hre] with s hs
    simpa only [add_zero] using contiguousConnection_eq_cot hL hs
  rw [heq.iteratedDeriv_eq (2*j+1),iteratedDeriv_const_add (by omega),
    iteratedDeriv_const_mul_field,GaloisForLFunctions.liClock_iteratedDeriv_comp_affine]
  simp only [add_zero]
  rw [hcot,show (-1:ℂ)^(2*j+1)=-1 by rw [pow_add,pow_mul]; norm_num,
    contiguousMoment_eq_scaled hL]
  dsimp only [a,x]
  rw [show 2*j+2=(2*j+1)+1 by omega,pow_succ]
  ring

theorem liClockPairedEtaContiguousReciprocal_moment_eq_exponential {L : ℝ}
    (hL : 0 < L) (j : ℕ) :
    (∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^(2*j+2)) =
      (L:ℂ)^(2*j+2)/((2*j+1).factorial:ℂ)*
        ∑' n : ℕ,(n:ℂ)^(2*j+1)*(Real.exp (-L/2):ℂ)^n := by
  let a := contiguousAffine L
  let x := a*(1/2)
  let z : UpperHalfPlane := ⟨x,contiguousAffine_center_mem_upper hL⟩
  have hq := EisensteinSeries.qExpansion_identity (k:=2*j+1) (by omega) z
  have he : Complex.exp (2*(Real.pi:ℂ)*I*x)=(Real.exp (-L/2):ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    dsimp [x,a,contiguousAffine]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    norm_num [Complex.I_sq]
  have hprod : a*(-2*(Real.pi:ℂ)*I)=(L:ℂ) := by
    dsimp [a,contiguousAffine]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    norm_num [Complex.I_sq]
  rw [contiguousMoment_eq_scaled hL]
  change a^(2*j+2)*(∑' k : ℤ,1/(x+(k:ℂ))^(2*j+2))= _
  rw [show 2*j+2=(2*j+1)+1 by omega,hq]
  simp only [z,he]
  rw [show a^((2*j+1)+1)*
      ((-2*(Real.pi:ℂ)*I)^((2*j+1)+1)/((2*j+1).factorial:ℂ)*
        ∑' n : ℕ,(n:ℂ)^(2*j+1)*(Real.exp (-L/2):ℂ)^n) =
    ((a*(-2*(Real.pi:ℂ)*I))^((2*j+1)+1)/((2*j+1).factorial:ℂ))*
      ∑' n : ℕ,(n:ℂ)^(2*j+1)*(Real.exp (-L/2):ℂ)^n by rw [mul_pow]; ring]
  rw [hprod]


theorem liClockPairedEtaContiguousReciprocal_zero {L : ℝ} :
    liClockPairedEtaContiguousReciprocal L 0 = 2 := by
  norm_num [liClockPairedEtaContiguousReciprocal]

theorem liClockPairedEtaContiguousReciprocal_norm_le_two (L : ℝ) (k : ℤ) :
    ‖liClockPairedEtaContiguousReciprocal L k‖ ≤ 2 := by
  have hre : (1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(L:ℂ)).re = 1/2 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  have hn : (1/2:ℝ) ≤ ‖(1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(L:ℂ))‖ := by
    rw [← hre]
    exact Complex.re_le_norm _
  rw [liClockPairedEtaContiguousReciprocal, norm_inv, inv_eq_one_div]
  calc
    _ ≤ 1/(1/2:ℝ) := one_div_le_one_div_of_le (by norm_num) hn
    _ = _ := by norm_num

theorem liClockPairedEtaContiguousReciprocal_norm_sq_le {L : ℝ} (hL : 0 < L) (k : ℤ) :
    ‖liClockPairedEtaContiguousReciprocal L k‖^2 ≤
      (if k=0 then 4 else 0) + L^2/(4*Real.pi^2) * (1/(k:ℝ)^2) := by
  by_cases hk : k = 0
  · subst k; norm_num [liClockPairedEtaContiguousReciprocal]
  have hkre : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hp := Real.pi_pos
  have hnorm : ‖(1/2 + 2*(Real.pi:ℂ)*I*(k:ℂ)/(L:ℂ):ℂ)‖^2 =
      1/4+(2*Real.pi*(k:ℝ)/L)^2 := by
    have hc : (1/2 + 2*(Real.pi:ℂ)*I*(k:ℂ)/(L:ℂ):ℂ) =
        (1/2:ℂ)+((2*Real.pi*(k:ℝ)/L:ℝ):ℂ)*I := by push_cast; ring
    rw [hc, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero]
    norm_num
    ring
  rw [if_neg hk,zero_add,liClockPairedEtaContiguousReciprocal, norm_inv, inv_pow,
    hnorm, inv_eq_one_div]
  have ht : 0 < (2*Real.pi*(k:ℝ)/L)^2 := sq_pos_of_ne_zero (by positivity)
  calc
    _ ≤ 1/(2*Real.pi*(k:ℝ)/L)^2 := one_div_le_one_div_of_le ht (by linarith)
    _ = _ := by field_simp; ring

theorem summable_liClockPairedEtaContiguousReciprocal_norm_sq {L : ℝ} (hL : 0 < L) :
    Summable (fun k : ℤ => ‖liClockPairedEtaContiguousReciprocal L k‖^2) := by
  have hs : Summable (fun k : ℤ => if k=0 then (4:ℝ) else 0) := (hasSum_ite_eq 0 (4:ℝ)).summable
  have ht := ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)).mul_left
    (L^2/(4*Real.pi^2))
  exact (hs.add ht).of_nonneg_of_le (fun _ => sq_nonneg _)
    (liClockPairedEtaContiguousReciprocal_norm_sq_le hL)


private theorem scaledTaylorTerm (L : ℝ) (t : ℂ) (k : ℤ) (j : ℕ) :
    GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
      (liClockPairedEtaContiguousReciprocal L) t k j =
    2*GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
      (fun k => liClockPairedEtaContiguousReciprocal L k/2) (2*t) k j := by
  unfold GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
  rw [div_pow,mul_pow,show 2*j+2=(2*j+1)+1 by omega]
  simp only [pow_succ]
  field_simp

private theorem scaledSquareSummable {L : ℝ} (hL : 0<L) :
    Summable (fun k : ℤ => ‖liClockPairedEtaContiguousReciprocal L k/2‖^2) := by
  convert (summable_liClockPairedEtaContiguousReciprocal_norm_sq hL).mul_right (1/4:ℝ) using 1 <;>
    first | rfl | (funext k; rw [norm_div,Complex.norm_ofNat,div_pow]; ring)

private theorem scaledNormLeOne (L : ℝ) (k : ℤ) :
    ‖liClockPairedEtaContiguousReciprocal L k/2‖ ≤ 1 := by
  rw [norm_div,Complex.norm_ofNat]
  exact (div_le_one (by norm_num)).mpr (liClockPairedEtaContiguousReciprocal_norm_le_two L k)

theorem summable_norm_liClockPairedEtaContiguousTaylorTerm {L : ℝ} (hL : 0<L) (t : ℂ) :
    Summable (fun p : ℤ×ℕ => ‖GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
      (liClockPairedEtaContiguousReciprocal L) t p.1 p.2‖) := by
  have hs := (GaloisForLFunctions.summable_norm_liClockCompletionHyperbolicTaylorTerm
    (fun k => liClockPairedEtaContiguousReciprocal L k/2) (scaledSquareSummable hL)
    (scaledNormLeOne L) (2*t)).mul_left 2
  convert hs using 1 <;> first | rfl | (funext p; rw [scaledTaylorTerm,norm_mul,Complex.norm_ofNat])

theorem summable_norm_liClockPairedEtaContiguousHyperbolicAtom {L : ℝ} (hL : 0<L) (t : ℂ) :
    Summable (fun k : ℤ => ‖liClockPairedEtaContiguousReciprocal L k *
      Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k)‖) := by
  have hs := summable_norm_liClockPairedEtaContiguousTaylorTerm hL t
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hs.prod
  intro k
  rw [← (GaloisForLFunctions.hasSum_liClockCompletionHyperbolicTaylorTerm
    (liClockPairedEtaContiguousReciprocal L) t k).tsum_eq]
  exact norm_tsum_le_tsum_norm (hs.prod_factor k)

theorem iteratedDeriv_liClockPairedEtaContiguousSourceTrace_odd {L : ℝ} (hL : 0<L) (j : ℕ) :
    iteratedDeriv (2*j+1) (liClockPairedEtaContiguousSourceTrace L) 0 =
      (-1:ℂ)^j*((2*j+1).factorial:ℂ)*
        ∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^(2*j+2) := by
  unfold liClockPairedEtaContiguousSourceTrace
  have hc : (fun z : ℂ => liClockPairedEtaContiguousConnection L (1/2+z*I)) =
      (fun z => liClockPairedEtaContiguousConnection L (I*z+1/2)) := by funext z; congr 1; ring
  rw [iteratedDeriv_const_mul_field,hc]
  change I*iteratedDeriv (2*j+1) (fun z => liClockPairedEtaContiguousConnection L (I*z+1/2)) 0 = _
  rw [GaloisForLFunctions.liClock_iteratedDeriv_comp_affine]
  simp only [mul_zero,zero_add]
  rw [iteratedDeriv_liClockPairedEtaContiguousConnection_odd hL]
  have hi : (I:ℂ)*(I:ℂ)^(2*j+1) = (-1:ℂ)^(j+1) := by
    rw [← pow_succ',show 2*j+1+1=2*(j+1) by omega,pow_mul,Complex.I_sq]
  rw [← mul_assoc,← mul_assoc,hi,pow_succ]
  ring

theorem liClockPairedEtaContiguousClock_eq_tsum_lattice {L : ℝ} (hL : 0<L) (t : ℂ) :
    liClockPairedEtaContiguousClock L t =
      ∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k*
        Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k) := by
  have heq (j : ℕ) : liClockCentralTraceSineContourTerm
      (liClockPairedEtaContiguousSourceTrace L) t j =
      (∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^(2*j+2))*
        t^(2*j+1)/((2*j+1).factorial:ℂ) := by
    unfold liClockCentralTraceSineContourTerm
    rw [iteratedDeriv_liClockPairedEtaContiguousSourceTrace_odd hL]
    have hfact : ((2*j+1).factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hsign : (-1:ℂ)^j * (-1:ℂ)^j = 1 := by rw [← mul_pow]; norm_num
    calc
      _ = ((-1:ℂ)^j*(-1:ℂ)^j)*
        ((∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^(2*j+2))*
        t^(2*j+1)/((2*j+1).factorial:ℂ)) := by field_simp [hfact]
      _ = _ := by rw [hsign,one_mul]
  rw [liClockPairedEtaContiguousClock,
    liClockCentralTraceSineContour_eq_neg_tsum (by norm_num : (0:ℝ)<1/4)
      (diffContOnCl_liClockPairedEtaContiguousSourceTrace hL (by norm_num)),neg_neg]
  simp_rw [heq]
  have hd := (summable_norm_liClockPairedEtaContiguousTaylorTerm hL t).of_norm
  calc
    _ = ∑' j : ℕ,∑' k : ℤ,GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
        (liClockPairedEtaContiguousReciprocal L) t k j := by
      congr 1
      funext j
      simp only [GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm,tsum_div_const,tsum_mul_right]
    _ = ∑' k : ℤ,∑' j : ℕ,GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
        (liClockPairedEtaContiguousReciprocal L) t k j := hd.tsum_comm
    _ = _ := tsum_congr fun k => (GaloisForLFunctions.hasSum_liClockCompletionHyperbolicTaylorTerm
      (liClockPairedEtaContiguousReciprocal L) t k).tsum_eq

def liClockPairedEtaContiguousOddSeriesTerm (t : ℂ) (j : ℕ) : ℂ :=
  t^(2*j+1)/((2*j+1).factorial:ℂ)^2

def liClockPairedEtaContiguousOddSeries (t : ℂ) : ℂ :=
  ∑' j : ℕ,liClockPairedEtaContiguousOddSeriesTerm t j

private theorem oddTerm_majorant {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    x^(2*j+1)/((2*j+1).factorial:ℝ)^2 ≤
      x*((Real.sqrt x)^(2*j)/((2*j).factorial:ℝ))*
        ((Real.sqrt x)^(2*j)/((2*j).factorial:ℝ)) := by
  have hf : ((2*j).factorial:ℝ) ≤ ((2*j+1).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2*j ≤ 2*j+1)
  have hpow : (Real.sqrt x)^(2*j)*(Real.sqrt x)^(2*j)=x^(2*j) := by
    rw [← mul_pow,← pow_two,Real.sq_sqrt hx]
  calc
    _ ≤ x^(2*j+1)/((2*j).factorial:ℝ)^2 := by gcongr
    _ = _ := by
      rw [show 2*j+1=2*j+1 by rfl,pow_succ]
      field_simp
      rw [pow_two,hpow]
      ring

private theorem real_exp_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x^n/(n.factorial:ℝ)) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

private theorem even_injective : Function.Injective (fun j : ℕ => 2*j) := by
  intro j k h
  change 2*j = 2*k at h
  omega

private theorem exp_even_summable (x : ℝ) :
    Summable (fun j : ℕ => (Real.sqrt x)^(2*j)/((2*j).factorial:ℝ)) := by
  convert (Real.summable_pow_div_factorial (Real.sqrt x)).comp_injective
    (i := fun j : ℕ => 2*j) even_injective using 1 <;> rfl

private theorem exp_even_le (x : ℝ) (j : ℕ) :
    (Real.sqrt x)^(2*j)/((2*j).factorial:ℝ) ≤ Real.exp (Real.sqrt x) := by
  have h := (real_exp_hasSum (Real.sqrt x)).summable.le_tsum (2*j)
    (fun n _ => div_nonneg (pow_nonneg (Real.sqrt_nonneg x) _) (Nat.cast_nonneg _))
  rwa [(real_exp_hasSum (Real.sqrt x)).tsum_eq] at h

private theorem exp_even_tsum_le (x : ℝ) :
    (∑' j : ℕ,(Real.sqrt x)^(2*j)/((2*j).factorial:ℝ)) ≤ Real.exp (Real.sqrt x) := by
  apply Real.tsum_le_of_sum_le (fun j => by positivity)
  intro u
  have heq : (∑ j ∈ u, (Real.sqrt x)^(2*j)/((2*j).factorial:ℝ)) =
      ∑ n ∈ u.image (fun j : ℕ => 2*j), (Real.sqrt x)^n/(n.factorial:ℝ) := by
    rw [Finset.sum_image]
    intro j hj k hk he
    exact even_injective he
  rw [heq, ← (real_exp_hasSum (Real.sqrt x)).tsum_eq]
  exact (real_exp_hasSum (Real.sqrt x)).summable.sum_le_tsum _
    (fun n hn => by positivity)

private theorem exp_diagonal_summable (x : ℝ) :
    Summable (fun j : ℕ => ((Real.sqrt x)^(2*j)/((2*j).factorial:ℝ))*
      ((Real.sqrt x)^(2*j)/((2*j).factorial:ℝ))) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg
    (div_nonneg (pow_nonneg (Real.sqrt_nonneg x) _) (Nat.cast_nonneg _))
    (div_nonneg (pow_nonneg (Real.sqrt_nonneg x) _) (Nat.cast_nonneg _))) _
    ((exp_even_summable x).mul_left (Real.exp (Real.sqrt x)))
  intro j
  exact mul_le_mul_of_nonneg_right (exp_even_le x j)
    (div_nonneg (pow_nonneg (Real.sqrt_nonneg x) _) (Nat.cast_nonneg _))

theorem summable_norm_liClockPairedEtaContiguousOddSeriesTerm (t : ℂ) :
    Summable (fun j => ‖liClockPairedEtaContiguousOddSeriesTerm t j‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _
    ((exp_diagonal_summable ‖t‖).mul_left ‖t‖)
  intro j
  simp only [liClockPairedEtaContiguousOddSeriesTerm,norm_div,norm_pow,Complex.norm_natCast]
  simpa only [mul_assoc] using oddTerm_majorant (norm_nonneg t) j

theorem tsum_norm_liClockPairedEtaContiguousOddSeriesTerm_le (t : ℂ) :
    (∑' j : ℕ,‖liClockPairedEtaContiguousOddSeriesTerm t j‖) ≤
      ‖t‖*Real.exp (2*Real.sqrt ‖t‖) := by
  have hd : (∑' j : ℕ,((Real.sqrt ‖t‖)^(2*j)/((2*j).factorial:ℝ))*
      ((Real.sqrt ‖t‖)^(2*j)/((2*j).factorial:ℝ))) ≤ Real.exp (2*Real.sqrt ‖t‖) := by
    calc
      _ ≤ ∑' j : ℕ,Real.exp (Real.sqrt ‖t‖)*
          ((Real.sqrt ‖t‖)^(2*j)/((2*j).factorial:ℝ)) := by
        apply (exp_diagonal_summable ‖t‖).tsum_le_tsum _
          ((exp_even_summable ‖t‖).mul_left (Real.exp (Real.sqrt ‖t‖)))
        intro j
        exact mul_le_mul_of_nonneg_right (exp_even_le ‖t‖ j)
          (div_nonneg (pow_nonneg (Real.sqrt_nonneg ‖t‖) _) (Nat.cast_nonneg _))
      _ ≤ Real.exp (Real.sqrt ‖t‖)*Real.exp (Real.sqrt ‖t‖) := by
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (exp_even_tsum_le ‖t‖) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ ∑' j : ℕ,‖t‖*(((Real.sqrt ‖t‖)^(2*j)/((2*j).factorial:ℝ))*
        ((Real.sqrt ‖t‖)^(2*j)/((2*j).factorial:ℝ))) := by
      apply (summable_norm_liClockPairedEtaContiguousOddSeriesTerm t).tsum_le_tsum _
        ((exp_diagonal_summable ‖t‖).mul_left ‖t‖)
      intro j
      simp only [liClockPairedEtaContiguousOddSeriesTerm,norm_div,norm_pow,Complex.norm_natCast]
      simpa only [mul_assoc] using oddTerm_majorant (norm_nonneg t) j
    _ = ‖t‖*∑' j : ℕ,((Real.sqrt ‖t‖)^(2*j)/((2*j).factorial:ℝ))*
        ((Real.sqrt ‖t‖)^(2*j)/((2*j).factorial:ℝ)) := by rw [tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (norm_nonneg t)

theorem norm_liClockPairedEtaContiguousOddSeries_le (t : ℂ) :
    ‖liClockPairedEtaContiguousOddSeries t‖ ≤ ‖t‖*Real.exp (2*Real.sqrt ‖t‖) :=
  (norm_tsum_le_tsum_norm (summable_norm_liClockPairedEtaContiguousOddSeriesTerm t)).trans
    (tsum_norm_liClockPairedEtaContiguousOddSeriesTerm_le t)



def liClockPairedEtaContiguousExponentialTaylorTerm (L : ℝ) (t : ℂ) (n j : ℕ) : ℂ :=
  (L:ℂ)*(Real.exp (-(n:ℝ)*L/2):ℂ)*
    liClockPairedEtaContiguousOddSeriesTerm ((n:ℂ)*(L:ℂ)*t) j

def liClockPairedEtaContiguousExponentialClockTerm (L : ℝ) (t : ℂ) (n : ℕ) : ℂ :=
  (L:ℂ)*(Real.exp (-(n:ℝ)*L/2):ℂ)*
    liClockPairedEtaContiguousOddSeries ((n:ℂ)*(L:ℂ)*t)

private theorem norm_nLt {L : ℝ} (hL : 0<L) (n : ℕ) (t : ℂ) :
    ‖(n:ℂ)*(L:ℂ)*t‖ = (n:ℝ)*L*‖t‖ := by
  simp only [norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]

private theorem norm_exponentialTaylorTerm {L : ℝ} (hL : 0<L) (t : ℂ) (n j : ℕ) :
    ‖liClockPairedEtaContiguousExponentialTaylorTerm L t n j‖ =
      L*Real.exp (-(n:ℝ)*L/2)*
      (((n:ℝ)*L*‖t‖)^(2*j+1)/((2*j+1).factorial:ℝ)^2) := by
  simp only [liClockPairedEtaContiguousExponentialTaylorTerm,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hL,abs_of_pos (Real.exp_pos _),
    liClockPairedEtaContiguousOddSeriesTerm,norm_div,norm_pow,Complex.norm_natCast,norm_nLt hL]

private theorem summable_norm_exponentialTaylorRow {L : ℝ} (hL : 0<L) (t : ℂ) (n : ℕ) :
    Summable (fun j => ‖liClockPairedEtaContiguousExponentialTaylorTerm L t n j‖) := by
  have hs := (summable_norm_liClockPairedEtaContiguousOddSeriesTerm ((n:ℂ)*(L:ℂ)*t)).mul_left
    (L*Real.exp (-(n:ℝ)*L/2))
  convert hs using 1 <;> first | rfl | (funext j; simp only [liClockPairedEtaContiguousExponentialTaylorTerm,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL,abs_of_pos (Real.exp_pos _)])

private theorem sqrt_young {x T : ℝ} (hx : 0≤x) (hT : 0≤T) :
    2*Real.sqrt (x*T) ≤ x/4+4*T := by
  have hs : Real.sqrt (x*T) ≤ x/8+2*T := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_nonneg (x/8-2*T)]
  linarith

private theorem exponentialRow_norm_tsum_le {L : ℝ} (hL : 0<L) {T : ℝ}
    (hT : 0≤T) (t : ℂ) (ht : ‖t‖≤T) (n : ℕ) :
    (∑' j : ℕ, ‖liClockPairedEtaContiguousExponentialTaylorTerm L t n j‖) ≤
      (L^2*T*Real.exp (4*T))*(n:ℝ)*(Real.exp (-L/4))^n := by
  have hn : 0≤(n:ℝ)*L := by positivity
  have hb := tsum_norm_liClockPairedEtaContiguousOddSeriesTerm_le ((n:ℂ)*(L:ℂ)*t)
  have heq : (∑' j : ℕ, ‖liClockPairedEtaContiguousExponentialTaylorTerm L t n j‖) =
      L*Real.exp (-(n:ℝ)*L/2)*
        ∑' j : ℕ, ‖liClockPairedEtaContiguousOddSeriesTerm ((n:ℂ)*(L:ℂ)*t) j‖ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [liClockPairedEtaContiguousExponentialTaylorTerm,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hL,abs_of_pos (Real.exp_pos _)]
  rw [heq]
  calc
    _ ≤ L*Real.exp (-(n:ℝ)*L/2)*
        (‖(n:ℂ)*(L:ℂ)*t‖*Real.exp (2*Real.sqrt ‖(n:ℂ)*(L:ℂ)*t‖)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ L*Real.exp (-(n:ℝ)*L/2)*
        (((n:ℝ)*L*T)*Real.exp ((n:ℝ)*L/4+4*T)) := by
      rw [norm_nLt hL]
      gcongr
      exact (sqrt_young hn (norm_nonneg t)).trans (by gcongr)
    _ = _ := by
      have he : Real.exp (-(n:ℝ)*L/2)*Real.exp ((n:ℝ)*L/4+4*T) =
          Real.exp (4*T)*(Real.exp (-L/4))^n := by
        rw [← Real.exp_add,← Real.exp_nat_mul,← Real.exp_add]
        congr 1
        ring
      calc
        _ = L^2*T*(n:ℝ)*(Real.exp (-(n:ℝ)*L/2)*Real.exp ((n:ℝ)*L/4+4*T)) := by ring
        _ = _ := by rw [he]; ring

private theorem summable_exponentialRowMajorant {L : ℝ} (hL : 0<L) (T : ℝ) :
    Summable (fun n : ℕ => (L^2*T*Real.exp (4*T))*(n:ℝ)*(Real.exp (-L/4))^n) := by
  have hr : ‖Real.exp (-L/4)‖ < 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  convert (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left
    (L^2*T*Real.exp (4*T)) using 1 <;> first | rfl | (funext n; simp only [pow_one,mul_assoc])

theorem summable_norm_liClockPairedEtaContiguousExponentialTaylorTerm {L : ℝ}
    (hL : 0<L) (t : ℂ) :
    Summable (fun p : ℕ×ℕ => ‖liClockPairedEtaContiguousExponentialTaylorTerm L t p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).2
  refine ⟨summable_norm_exponentialTaylorRow hL t,?_⟩
  exact (summable_exponentialRowMajorant hL ‖t‖).of_nonneg_of_le
    (fun n => tsum_nonneg (fun j => norm_nonneg _))
    (exponentialRow_norm_tsum_le hL (norm_nonneg t) t le_rfl)

theorem summable_norm_liClockPairedEtaContiguousExponentialClockTerm {L : ℝ}
    (hL : 0<L) (t : ℂ) :
    Summable (fun n : ℕ => ‖liClockPairedEtaContiguousExponentialClockTerm L t n‖) := by
  have hs := summable_norm_liClockPairedEtaContiguousExponentialTaylorTerm hL t
  apply hs.prod.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  have heq : liClockPairedEtaContiguousExponentialClockTerm L t n =
      ∑' j : ℕ,liClockPairedEtaContiguousExponentialTaylorTerm L t n j := by
    simp only [liClockPairedEtaContiguousExponentialClockTerm,
      liClockPairedEtaContiguousExponentialTaylorTerm,liClockPairedEtaContiguousOddSeries,tsum_mul_left]
  rw [heq]
  exact norm_tsum_le_tsum_norm (hs.prod_factor n)

private theorem exponentialTaylorTerm_eq_momentTerm (L : ℝ) (t : ℂ) (n j : ℕ) :
    liClockPairedEtaContiguousExponentialTaylorTerm L t n j =
      (L:ℂ)^(2*j+2)*((n:ℂ)^(2*j+1)*(Real.exp (-L/2):ℂ)^n)*
        t^(2*j+1)/((2*j+1).factorial:ℂ)^2 := by
  have he : (Real.exp (-(n:ℝ)*L/2):ℂ)=(Real.exp (-L/2):ℂ)^n := by
    rw [← Complex.ofReal_pow,← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  unfold liClockPairedEtaContiguousExponentialTaylorTerm liClockPairedEtaContiguousOddSeriesTerm
  rw [he,mul_pow,mul_pow,show 2*j+2=(2*j+1)+1 by omega,pow_succ]
  ring

theorem liClockPairedEtaContiguousClock_eq_tsum_moments {L : ℝ} (hL : 0<L) (t : ℂ) :
    liClockPairedEtaContiguousClock L t =
      ∑' j : ℕ,(∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^(2*j+2))*
        t^(2*j+1)/((2*j+1).factorial:ℂ) := by
  rw [liClockPairedEtaContiguousClock_eq_tsum_lattice hL]
  symm
  have hd := (summable_norm_liClockPairedEtaContiguousTaylorTerm hL t).of_norm
  calc
    _ = ∑' j : ℕ,∑' k : ℤ,GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
        (liClockPairedEtaContiguousReciprocal L) t k j := by
      congr 1
      funext j
      simp only [GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm,tsum_div_const,tsum_mul_right]
    _ = ∑' k : ℤ,∑' j : ℕ,GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
        (liClockPairedEtaContiguousReciprocal L) t k j := hd.tsum_comm
    _ = _ := tsum_congr fun k => (GaloisForLFunctions.hasSum_liClockCompletionHyperbolicTaylorTerm
      (liClockPairedEtaContiguousReciprocal L) t k).tsum_eq

theorem liClockPairedEtaContiguousClock_eq_tsum_exponential {L : ℝ} (hL : 0<L) (t : ℂ) :
    liClockPairedEtaContiguousClock L t =
      ∑' n : ℕ,liClockPairedEtaContiguousExponentialClockTerm L t n := by
  have heq (j : ℕ) :
      (∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k^(2*j+2))*
        t^(2*j+1)/((2*j+1).factorial:ℂ) =
      ∑' n : ℕ,liClockPairedEtaContiguousExponentialTaylorTerm L t n j := by
    rw [liClockPairedEtaContiguousReciprocal_moment_eq_exponential hL]
    simp_rw [exponentialTaylorTerm_eq_momentTerm]
    rw [tsum_div_const,tsum_mul_right,tsum_mul_left]
    have hfact : ((2*j+1).factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hfact]
  rw [liClockPairedEtaContiguousClock_eq_tsum_moments hL]
  simp_rw [heq]
  have hcomm : (∑' j : ℕ, ∑' n : ℕ,liClockPairedEtaContiguousExponentialTaylorTerm L t n j) =
      ∑' n : ℕ,∑' j : ℕ,liClockPairedEtaContiguousExponentialTaylorTerm L t n j :=
    Summable.tsum_comm (f := fun n j => liClockPairedEtaContiguousExponentialTaylorTerm L t n j)
      (summable_norm_liClockPairedEtaContiguousExponentialTaylorTerm hL t).of_norm
  rw [hcomm]
  apply tsum_congr
  intro n
  simp only [liClockPairedEtaContiguousExponentialClockTerm,
    liClockPairedEtaContiguousExponentialTaylorTerm,liClockPairedEtaContiguousOddSeries,tsum_mul_left]

private theorem norm_exponentialClockTerm_le_row {L : ℝ} (hL : 0<L) {T : ℝ}
    (hT : 0≤T) (t : ℂ) (ht : ‖t‖≤T) (n : ℕ) :
    ‖liClockPairedEtaContiguousExponentialClockTerm L t n‖ ≤
      (L^2*T*Real.exp (4*T))*(n:ℝ)*(Real.exp (-L/4))^n := by
  have heq : liClockPairedEtaContiguousExponentialClockTerm L t n =
      ∑' j : ℕ,liClockPairedEtaContiguousExponentialTaylorTerm L t n j := by
    simp only [liClockPairedEtaContiguousExponentialClockTerm,
      liClockPairedEtaContiguousExponentialTaylorTerm,liClockPairedEtaContiguousOddSeries,tsum_mul_left]
  rw [heq]
  exact (norm_tsum_le_tsum_norm (summable_norm_exponentialTaylorRow hL t n)).trans
    (exponentialRow_norm_tsum_le hL hT t ht n)

theorem hasSumUniformlyOn_liClockPairedEtaContiguousExponentialClockTerm {L T : ℝ}
    (hL : 0<L) (hT : 0≤T) :
    HasSumUniformlyOn (fun n t => liClockPairedEtaContiguousExponentialClockTerm L t n)
      (liClockPairedEtaContiguousClock L) (closedBall 0 T) := by
  have h := HasSumUniformlyOn.of_norm_le_summable (summable_exponentialRowMajorant hL T)
    (f := fun n t => liClockPairedEtaContiguousExponentialClockTerm L t n)
    (s := closedBall 0 T) (fun n t ht => norm_exponentialClockTerm_le_row hL hT t
      (by simpa only [mem_closedBall,dist_zero_right] using ht) n)
  have heq : (fun t => ∑' n,liClockPairedEtaContiguousExponentialClockTerm L t n) =
      liClockPairedEtaContiguousClock L := by funext t; exact (liClockPairedEtaContiguousClock_eq_tsum_exponential hL t).symm
  rw [heq] at h
  exact h

theorem summableLocallyUniformlyOn_liClockPairedEtaContiguousExponentialClockTerm {L : ℝ}
    (hL : 0<L) :
    SummableLocallyUniformlyOn (fun n t => liClockPairedEtaContiguousExponentialClockTerm L t n) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K hK hKc
  obtain ⟨C,hC⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  let T : ℝ := max C 0
  have hT : 0≤T := le_max_right _ _
  refine ⟨_,summable_exponentialRowMajorant hL T,?_⟩
  intro n t ht
  exact norm_exponentialClockTerm_le_row hL hT t
    ((hC ⟨t,ht,rfl⟩).trans (le_max_left _ _)) n

theorem summableLocallyUniformlyOn_liClockPairedEtaContiguousExponentialTaylorTerm {L : ℝ}
    (hL : 0<L) :
    SummableLocallyUniformlyOn
      (fun p : ℕ×ℕ => fun t => liClockPairedEtaContiguousExponentialTaylorTerm L t p.1 p.2) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K hK hKc
  obtain ⟨C,hC⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  let T : ℝ := max C 0
  have hT : 0≤T := le_max_right _ _
  refine ⟨(fun p : ℕ×ℕ => ‖liClockPairedEtaContiguousExponentialTaylorTerm L (T:ℂ) p.1 p.2‖),
    summable_norm_liClockPairedEtaContiguousExponentialTaylorTerm hL (T:ℂ),?_⟩
  intro p t ht
  have htn : ‖t‖ ≤ T := (hC ⟨t,ht,rfl⟩).trans (le_max_left _ _)
  simp only [norm_exponentialTaylorTerm hL,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT]
  gcongr

private theorem norm_contiguousHyperbolicAtom_le (L : ℝ) {T : ℝ}
    (t : ℂ) (ht : ‖t‖≤T) (k : ℤ) :
    ‖liClockPairedEtaContiguousReciprocal L k*
      Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k)‖ ≤
      ‖liClockPairedEtaContiguousReciprocal L k‖^2*(Real.sinh (2*T)/2) := by
  have ha : liClockPairedEtaContiguousReciprocal L k*
      Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k) =
      2*((liClockPairedEtaContiguousReciprocal L k/2)*
        Complex.sinh ((2*t)*(liClockPairedEtaContiguousReciprocal L k/2))) := by
    have hs : (2*t)*(liClockPairedEtaContiguousReciprocal L k/2) =
        t*liClockPairedEtaContiguousReciprocal L k := by ring
    rw [hs]
    ring
  rw [ha,norm_mul,Complex.norm_ofNat]
  have hh := GaloisForLFunctions.norm_liClockCompletionHyperbolicAtom_le
    (fun k => liClockPairedEtaContiguousReciprocal L k/2) (2*t) k
    (scaledNormLeOne L k) (show ‖(2:ℂ)*t‖≤2*T by rw [norm_mul,Complex.norm_ofNat]; gcongr)
  calc
    _ ≤ 2*(‖liClockPairedEtaContiguousReciprocal L k/2‖^2*Real.sinh (2*T)) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by rw [norm_div,Complex.norm_ofNat,div_pow]; ring

theorem hasSumUniformlyOn_liClockPairedEtaContiguousHyperbolicAtom {L T : ℝ}
    (hL : 0<L) :
    HasSumUniformlyOn
      (fun k t => liClockPairedEtaContiguousReciprocal L k*
        Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k))
      (liClockPairedEtaContiguousClock L) (closedBall 0 T) := by
  have hs := (summable_liClockPairedEtaContiguousReciprocal_norm_sq hL).mul_right (Real.sinh (2*T)/2)
  have h := HasSumUniformlyOn.of_norm_le_summable hs
    (f := fun k t => liClockPairedEtaContiguousReciprocal L k*
      Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k)) (s:=closedBall 0 T)
    (fun k t ht => norm_contiguousHyperbolicAtom_le L t
      (by simpa only [mem_closedBall,dist_zero_right] using ht) k)
  have heq : (fun t => ∑' k : ℤ,liClockPairedEtaContiguousReciprocal L k*
      Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k)) = liClockPairedEtaContiguousClock L := by
    funext t
    exact (liClockPairedEtaContiguousClock_eq_tsum_lattice hL t).symm
  rw [heq] at h
  exact h

theorem summableLocallyUniformlyOn_liClockPairedEtaContiguousHyperbolicAtom {L : ℝ} (hL : 0<L) :
    SummableLocallyUniformlyOn
      (fun k t => liClockPairedEtaContiguousReciprocal L k*
        Complex.sinh (t*liClockPairedEtaContiguousReciprocal L k)) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K hK hKc
  obtain ⟨C,hC⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  let T : ℝ := max C 0
  refine ⟨_,(summable_liClockPairedEtaContiguousReciprocal_norm_sq hL).mul_right
    (Real.sinh (2*T)/2),?_⟩
  intro k t ht
  exact norm_contiguousHyperbolicAtom_le L t
    ((hC ⟨t,ht,rfl⟩).trans (le_max_left _ _)) k

theorem summableLocallyUniformlyOn_liClockPairedEtaContiguousTaylorTerm {L : ℝ} (hL : 0<L) :
    SummableLocallyUniformlyOn
      (fun p : ℤ×ℕ => fun t => GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
        (liClockPairedEtaContiguousReciprocal L) t p.1 p.2) univ := by
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K hK hKc
  obtain ⟨C,hC⟩ := hKc.bddAbove_image continuous_norm.continuousOn
  let T : ℝ := max C 0
  have hT : 0≤T := le_max_right _ _
  refine ⟨(fun p : ℤ×ℕ => ‖GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm
      (liClockPairedEtaContiguousReciprocal L) (T:ℂ) p.1 p.2‖),
    summable_norm_liClockPairedEtaContiguousTaylorTerm hL (T:ℂ),?_⟩
  intro p t ht
  have htn : ‖t‖≤T := (hC ⟨t,ht,rfl⟩).trans (le_max_left _ _)
  simp only [GaloisForLFunctions.liClockCompletionHyperbolicTaylorTerm,norm_div,norm_mul,norm_pow,
    Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT]
  gcongr

def liClockPairedEtaContiguousWindowDecayRate (c : ℝ) : ℝ := 1/2-2*Real.sqrt c

def liClockPairedEtaContiguousWindowEnvelope (c L : ℝ) : ℝ :=
  L^2*Real.exp (-liClockPairedEtaContiguousWindowDecayRate c*L)/
    (1-Real.exp (-liClockPairedEtaContiguousWindowDecayRate c*L))^2

private theorem contiguousWindowDecayRate_pos {c : ℝ} (hc : 0<c) (hc16 : c<1/16) :
    0<liClockPairedEtaContiguousWindowDecayRate c := by
  unfold liClockPairedEtaContiguousWindowDecayRate
  have hs := Real.sq_sqrt hc.le
  have hp := Real.sqrt_nonneg c
  have hh : Real.sqrt c<1/4 := by nlinarith
  linarith

private theorem window_sqrt_bound {L c : ℝ} (hL : 0<L) (hc : 0<c) (n : ℕ)
    (t : ℂ) (ht : ‖t‖≤c*L) :
    Real.sqrt ((n:ℝ)*L*‖t‖) ≤ (n:ℝ)*L*Real.sqrt c := by
  have hn : (n:ℝ)≤(n:ℝ)^2 := by
    by_cases hh : n=0
    · subst n; norm_num
    have hn1 : 1≤(n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hh
    nlinarith
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      _ ≤ (n:ℝ)*L*(c*L) := by gcongr
      _ = (n:ℝ)*L^2*c := by ring
      _ ≤ (n:ℝ)^2*L^2*c := by gcongr
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hc.le]

private theorem norm_exponentialClockTerm_le_window {L c : ℝ} (hL : 0<L)
    (hc : 0<c) (t : ℂ) (ht : ‖t‖≤c*L) (n : ℕ) :
    ‖liClockPairedEtaContiguousExponentialClockTerm L t n‖ ≤
      ‖t‖*L^2*(n:ℝ)*(Real.exp (-liClockPairedEtaContiguousWindowDecayRate c*L))^n := by
  unfold liClockPairedEtaContiguousExponentialClockTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_pos hL,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ L*Real.exp (-(n:ℝ)*L/2)*
        (‖(n:ℂ)*(L:ℂ)*t‖*Real.exp (2*Real.sqrt ‖(n:ℂ)*(L:ℂ)*t‖)) :=
      mul_le_mul_of_nonneg_left (norm_liClockPairedEtaContiguousOddSeries_le _) (by positivity)
    _ ≤ L*Real.exp (-(n:ℝ)*L/2)*
        (((n:ℝ)*L*‖t‖)*Real.exp (2*((n:ℝ)*L*Real.sqrt c))) := by
      rw [norm_nLt hL]
      gcongr
      exact window_sqrt_bound hL hc n t ht
    _ = _ := by
      have he : Real.exp (-(n:ℝ)*L/2)*Real.exp (2*((n:ℝ)*L*Real.sqrt c)) =
          (Real.exp (-liClockPairedEtaContiguousWindowDecayRate c*L))^n := by
        rw [← Real.exp_add,← Real.exp_nat_mul]
        congr 1
        unfold liClockPairedEtaContiguousWindowDecayRate
        ring
      calc
        _ = ‖t‖*L^2*(n:ℝ)*(Real.exp (-(n:ℝ)*L/2)*Real.exp (2*((n:ℝ)*L*Real.sqrt c))) := by ring
        _ = _ := by rw [he]

theorem norm_liClockPairedEtaContiguousClock_le_windowEnvelope {L c : ℝ}
    (hL : 0<L) (hc : 0<c) (hc16 : c<1/16) (t : ℂ) (ht : ‖t‖≤c*L) :
    ‖liClockPairedEtaContiguousClock L t‖ ≤ ‖t‖*liClockPairedEtaContiguousWindowEnvelope c L := by
  let ρ := Real.exp (-liClockPairedEtaContiguousWindowDecayRate c*L)
  have hρ : ‖ρ‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by have := contiguousWindowDecayRate_pos hc hc16; nlinarith)
  have hm : Summable (fun n : ℕ => ‖t‖*L^2*(n:ℝ)*ρ^n) := by
    convert (summable_pow_mul_geometric_of_norm_lt_one 1 hρ).mul_left (‖t‖*L^2) using 1 <;>
      first | rfl | (funext n; simp only [pow_one,mul_assoc])
  rw [liClockPairedEtaContiguousClock_eq_tsum_exponential hL]
  calc
    _ ≤ ∑' n : ℕ,‖liClockPairedEtaContiguousExponentialClockTerm L t n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_liClockPairedEtaContiguousExponentialClockTerm hL t)
    _ ≤ ∑' n : ℕ,‖t‖*L^2*(n:ℝ)*ρ^n :=
      (summable_norm_liClockPairedEtaContiguousExponentialClockTerm hL t).tsum_le_tsum
        (norm_exponentialClockTerm_le_window hL hc t ht) hm
    _ = _ := by
      simp_rw [mul_assoc]
      rw [tsum_mul_left,tsum_mul_left,(hasSum_coe_mul_geometric_of_norm_lt_one hρ).tsum_eq]
      unfold liClockPairedEtaContiguousWindowEnvelope
      dsimp [ρ]
      ring


theorem liClockPairedEtaContiguousWindowEnvelope_tendsto_zero {c : ℝ}
    (hc : 0<c) (hc16 : c<1/16) :
    Tendsto (liClockPairedEtaContiguousWindowEnvelope c) atTop (𝓝 0) := by
  let a := liClockPairedEtaContiguousWindowDecayRate c
  have ha : 0<a := contiguousWindowDecayRate_pos hc hc16
  have hs : Tendsto (fun L : ℝ => a*L) atTop atTop := by
    simpa only [id_eq] using tendsto_id.const_mul_atTop ha
  have he : Tendsto (fun L : ℝ => Real.exp (-a*L)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hs
  have hb : Tendsto (fun L : ℝ => (a*L)^2*Real.exp (-(a*L))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hs
  have hn : Tendsto (fun L : ℝ => L^2*Real.exp (-a*L)) atTop (𝓝 0) := by
    convert hb.div_const (a^2) using 1
    · funext L
      rw [neg_mul,mul_pow]
      field_simp [ha.ne']
    · simp
  have hd0 : Tendsto (fun L : ℝ => 1-Real.exp (-a*L)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub he)
  have hd : Tendsto (fun L : ℝ => (1-Real.exp (-a*L))^2) atTop (𝓝 1) := by
    simpa only [one_pow] using hd0.pow 2
  convert hn.div hd (by norm_num : (1:ℝ)≠0) using 1
  · funext L
    rfl
  · simp

theorem eventually_norm_liClockPairedEtaContiguousClock_le_mul {c : ℝ}
    (hc : 0<c) (hc16 : c<1/16) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℂ, ‖t‖≤c*L →
      ‖liClockPairedEtaContiguousClock L t‖ ≤ ε*‖t‖ := by
  have he := (liClockPairedEtaContiguousWindowEnvelope_tendsto_zero hc hc16).eventually_le_const hε
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with L hE hL
  intro t ht
  calc
    _ ≤ ‖t‖*liClockPairedEtaContiguousWindowEnvelope c L :=
      norm_liClockPairedEtaContiguousClock_le_windowEnvelope hL hc hc16 t ht
    _ ≤ _ := by nlinarith [norm_nonneg t]

/-- Completed contiguous MODEL; no arithmetic logarithmic gaps are removed from an actual source. -/
def liClockPairedEtaContiguousCompletedModel (L : ℝ) (t : ℂ) : ℂ :=
  liClockPairedEtaCompletionKernel t-liClockPairedEtaContiguousClock L t

private theorem completionKernel_linear_floor {t : ℝ} (ht : 0≤t) :
    (181/1600:ℝ)*t ≤ (liClockPairedEtaCompletionKernel (t:ℂ)).re := by
  have hh := liClockPairedEtaCompletionClockResponse_re_ge_sinh
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)<1/2) ht
  rw [liClockPairedEtaCompletionClockResponse_eq_kernel (by norm_num) (by norm_num)] at hh
  have hs := Real.self_le_sinh_iff.mpr (show 0≤(2/5:ℝ)*t by positivity)
  nlinarith

theorem eventually_liClockPairedEtaContiguousCompletedModel_re_pos {c : ℝ}
    (hc : 0<c) (hc16 : c<1/16) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, 0<t → t≤c*L →
      0<(liClockPairedEtaContiguousCompletedModel L (t:ℂ)).re := by
  have h := eventually_norm_liClockPairedEtaContiguousClock_le_mul hc hc16
    (by norm_num : (0:ℝ)<181/3200)
  filter_upwards [h] with L hL
  intro t ht hwindow
  have htcomplex : ‖(t:ℂ)‖≤c*L := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] using hwindow
  have hK := (Complex.re_le_norm (liClockPairedEtaContiguousClock L (t:ℂ))).trans (hL (t:ℂ) htcomplex)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] at hK
  unfold liClockPairedEtaContiguousCompletedModel
  rw [Complex.sub_re]
  have hC := completionKernel_linear_floor ht.le
  nlinarith

theorem liClockPairedEtaContiguousCompletedModel_im_ofReal_eq_zero {L : ℝ}
    (hL : 0<L) (t : ℝ) : (liClockPairedEtaContiguousCompletedModel L (t:ℂ)).im=0 := by
  unfold liClockPairedEtaContiguousCompletedModel
  rw [Complex.sub_im,liClockPairedEtaContiguousClock_im_ofReal_eq_zero hL,
    ← liClockPairedEtaCompletionClockResponse_eq_kernel (by norm_num : (0:ℝ)<1/4) (by norm_num),
    liClockPairedEtaCompletionClockResponse_im_ofReal_eq_zero (by norm_num) (by norm_num)]
  simp

private theorem contiguous_traceContour_add {r : ℝ} (hr : 0 < r) {T U : ℂ → ℂ}
    (hT : ContinuousOn T (sphere 0 r)) (hU : ContinuousOn U (sphere 0 r)) (t : ℂ) :
    liClockCentralTraceSineContour (fun z => T z+U z) r t =
      liClockCentralTraceSineContour T r t + liClockCentralTraceSineContour U r t := by
  have hnz (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) : z ≠ 0 := by
    intro h
    have hn : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    rw [h, norm_zero] at hn
    linarith
  have hs : ContinuousOn (fun z : ℂ => Complex.sin (t/z)) (sphere 0 r) :=
    Complex.continuous_sin.comp_continuousOn (continuousOn_const.div continuousOn_id hnz)
  have hTi : CircleIntegrable (fun z : ℂ => T z*Complex.sin (t/z)/z) 0 r :=
    ((hT.mul hs).div continuousOn_id hnz).circleIntegrable hr.le
  have hUi : CircleIntegrable (fun z : ℂ => U z*Complex.sin (t/z)/z) 0 r :=
    ((hU.mul hs).div continuousOn_id hnz).circleIntegrable hr.le
  have hi : (∮ z in C(0,r), (T z+U z)*Complex.sin (t/z)/z) =
      (∮ z in C(0,r), T z*Complex.sin (t/z)/z) +
      (∮ z in C(0,r), U z*Complex.sin (t/z)/z) := by
    rw [← circleIntegral.integral_add hTi hUi]
    apply circleIntegral.integral_congr hr.le
    intro z _
    dsimp only
    ring
  unfold liClockCentralTraceSineContour
  rw [hi]
  ring

private theorem contiguous_traceContour_neg (T : ℂ→ℂ) (r : ℝ) (t : ℂ) :
    liClockCentralTraceSineContour (fun z => -T z) r t =
      -liClockCentralTraceSineContour T r t := by
  unfold liClockCentralTraceSineContour circleIntegral
  simp only [neg_mul,neg_div,smul_neg,intervalIntegral.integral_neg]
  ring

/-- Clock of the literal filled contiguous partition logarithmic connection. -/
def liClockPairedEtaContiguousPartitionClock (L r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour (fun z : ℂ =>
    I*logDeriv (liClockPairedEtaContiguousPartition L) (1/2+z*I)) r t

theorem liClockPairedEtaContiguousPartitionClock_eq_two_sinh_sub_clock {L r : ℝ}
    (hL : 0<L) (hr : 0<r) (hrhalf : r<1/2) (t : ℂ) :
    liClockPairedEtaContiguousPartitionClock L r t =
      2*Complex.sinh (2*t)-liClockPairedEtaContiguousClock L t := by
  have hzNorm (z : ℂ) (hz : z∈sphere (0:ℂ) r) : ‖z‖=r := by
    simpa only [mem_sphere_iff_norm,sub_zero] using hz
  have hzStrip (z : ℂ) (hz : z∈sphere (0:ℂ) r) : 0<(1/2+z*I).re := by
    have hi := (abs_le.mp ((Complex.abs_im_le_norm z).trans (hzNorm z hz).le)).2
    have heq : (1/2+z*I).re=(1/2:ℝ)-z.im := by
      norm_num [Complex.add_re,Complex.mul_re]
      ring
    rw [heq]
    linarith
  have hPhase (z : ℂ) : I/(1/2+z*I)=1/(z-I/2) := by
    have he : (1/2:ℂ)+z*I=I*(z-I/2) := by ring_nf; norm_num [Complex.I_sq]; ring
    rw [he,div_mul_eq_div_div,div_self Complex.I_ne_zero]
  have heq : liClockPairedEtaContiguousPartitionClock L r t =
      liClockCentralTraceSineContour (fun z : ℂ =>
        liClockPairedEtaContiguousSourceTrace L z+ -(1/(z-I/2))) r t := by
    unfold liClockPairedEtaContiguousPartitionClock liClockCentralTraceSineContour
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    dsimp only
    rw [logDeriv_liClockPairedEtaContiguousPartition hL (hzStrip z hz)]
    simp only [liClockPairedEtaContiguousSourceTrace]
    rw [mul_sub,← mul_div_assoc,mul_one,hPhase]
    ring
  have hQ : ContinuousOn (liClockPairedEtaContiguousSourceTrace L) (sphere 0 r) :=
    (diffContOnCl_liClockPairedEtaContiguousSourceTrace hL hrhalf).continuousOn_ball.mono sphere_subset_closedBall
  have hn (z : ℂ) (hz : z∈sphere (0:ℂ) r) : z-I/2 ≠ 0 := by
    intro he
    have heqz : z=I/2 := sub_eq_zero.mp he
    have hnz := hzNorm z hz
    rw [heqz,norm_div,Complex.norm_I,Complex.norm_ofNat] at hnz
    norm_num at hnz
    linarith
  have hP : ContinuousOn (fun z : ℂ => 1/(z-I/2)) (sphere 0 r) :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const) hn
  have hadd : liClockCentralTraceSineContour (fun z : ℂ =>
      liClockPairedEtaContiguousSourceTrace L z+ -(1/(z-I/2))) r t =
      liClockCentralTraceSineContour (liClockPairedEtaContiguousSourceTrace L) r t+
        liClockCentralTraceSineContour (fun z : ℂ => -(1/(z-I/2))) r t := by
    convert contiguous_traceContour_add hr hQ hP.neg t using 1 <;> rfl
  rw [heq,hadd,contiguous_traceContour_neg,liClockCentralTraceSineContour_eta_pole hr hrhalf]
  have hK := liClockPairedEtaContiguousClock_eq_neg_contour hL hr hrhalf t
  linear_combination hK

theorem hasSumUniformlyOn_liClockPairedEtaContiguousOddSeriesTerm {T : ℝ} (hT : 0≤T) :
    HasSumUniformlyOn (fun j t => liClockPairedEtaContiguousOddSeriesTerm t j)
      liClockPairedEtaContiguousOddSeries (closedBall 0 T) := by
  exact HasSumUniformlyOn.of_norm_le_summable
    (summable_norm_liClockPairedEtaContiguousOddSeriesTerm (T:ℂ))
    (fun j t ht => by
      have htn : ‖t‖≤T := by simpa only [mem_closedBall,dist_zero_right] using ht
      simp only [liClockPairedEtaContiguousOddSeriesTerm,norm_div,norm_pow,Complex.norm_natCast,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT]
      gcongr)

end
end RHTower

open Complex Filter Topology MeasureTheory Set Metric
namespace RHTower
noncomputable section

private theorem oddTerm_ofReal (x : ℝ) (j : ℕ) :
    liClockPairedEtaContiguousOddSeriesTerm (x:ℂ) j =
      ((x^(2*j+1)/((2*j+1).factorial:ℝ)^2 : ℝ):ℂ) := by
  unfold liClockPairedEtaContiguousOddSeriesTerm
  push_cast
  rfl

theorem liClockPairedEtaContiguousOddSeries_ofReal_eq_tsum (x : ℝ) :
    liClockPairedEtaContiguousOddSeries (x:ℂ) =
      ((∑' j : ℕ,x^(2*j+1)/((2*j+1).factorial:ℝ)^2 : ℝ):ℂ) := by
  unfold liClockPairedEtaContiguousOddSeries
  simp_rw [oddTerm_ofReal]
  rw [← Complex.ofReal_tsum]

theorem liClockPairedEtaContiguousOddSeries_re_ofReal_ge {x : ℝ} (hx : 0≤x) :
    x ≤ (liClockPairedEtaContiguousOddSeries (x:ℂ)).re := by
  have hs : Summable (fun j : ℕ => x^(2*j+1)/((2*j+1).factorial:ℝ)^2) := by
    convert (Complex.hasSum_re
      (summable_norm_liClockPairedEtaContiguousOddSeriesTerm (x:ℂ)).of_norm.hasSum).summable using 1
    funext j
    rw [oddTerm_ofReal,Complex.ofReal_re]
  rw [liClockPairedEtaContiguousOddSeries_ofReal_eq_tsum,Complex.ofReal_re]
  have h := hs.le_tsum 0 (fun j hj => div_nonneg (pow_nonneg hx _) (sq_nonneg _))
  simpa only [Nat.mul_zero,zero_add,Nat.factorial_one,Nat.cast_one,one_pow,pow_one,div_one] using h

/-- The radial positive series gives the exact absolute-coefficient majorant. -/
theorem norm_liClockPairedEtaContiguousOddSeries_le_re_ofReal_norm (z : ℂ) :
    ‖liClockPairedEtaContiguousOddSeries z‖ ≤
      (liClockPairedEtaContiguousOddSeries (‖z‖:ℂ)).re := by
  have heq : (∑' j : ℕ,‖liClockPairedEtaContiguousOddSeriesTerm z j‖) =
      (liClockPairedEtaContiguousOddSeries (‖z‖:ℂ)).re := by
    rw [liClockPairedEtaContiguousOddSeries_ofReal_eq_tsum,Complex.ofReal_re]
    apply tsum_congr
    intro j
    simp only [liClockPairedEtaContiguousOddSeriesTerm,norm_div,norm_pow,Complex.norm_natCast]
  rw [← heq]
  exact norm_tsum_le_tsum_norm (summable_norm_liClockPairedEtaContiguousOddSeriesTerm z)

theorem liClockPairedEtaContiguousOddSeries_re_ofReal_norm_le (z : ℂ) :
    (liClockPairedEtaContiguousOddSeries (‖z‖:ℂ)).re ≤
      ‖z‖*Real.exp (2*Real.sqrt ‖z‖) := by
  have h := (Complex.re_le_norm (liClockPairedEtaContiguousOddSeries (‖z‖:ℂ))).trans
    (norm_liClockPairedEtaContiguousOddSeries_le (‖z‖:ℂ))
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z)] using h

private theorem exponentialClockTerm_re_ofReal (L t : ℝ) (n : ℕ) :
    (liClockPairedEtaContiguousExponentialClockTerm L (t:ℂ) n).re =
      L*Real.exp (-(n:ℝ)*L/2)*
        (liClockPairedEtaContiguousOddSeries (((n:ℝ)*L*t:ℝ):ℂ)).re := by
  have he : (n:ℂ)*(L:ℂ)*(t:ℂ) = (((n:ℝ)*L*t:ℝ):ℂ) := by push_cast; rfl
  unfold liClockPairedEtaContiguousExponentialClockTerm
  rw [he]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero,add_zero]

/-- The complete packet is strictly positive at every positive real clock. -/
theorem liClockPairedEtaContiguousClock_re_pos {L t : ℝ} (hL : 0<L) (ht : 0<t) :
    0<(liClockPairedEtaContiguousClock L (t:ℂ)).re := by
  have hs := (summable_norm_liClockPairedEtaContiguousExponentialClockTerm hL (t:ℂ)).of_norm
  have hn (n : ℕ) : 0≤(liClockPairedEtaContiguousExponentialClockTerm L (t:ℂ) n).re := by
    rw [exponentialClockTerm_re_ofReal]
    have hx : 0≤(n:ℝ)*L*t := by positivity
    have hO := liClockPairedEtaContiguousOddSeries_re_ofReal_ge hx
    exact mul_nonneg (mul_nonneg hL.le (Real.exp_pos _).le) (hx.trans hO)
  have h1 : 0<(liClockPairedEtaContiguousExponentialClockTerm L (t:ℂ) 1).re := by
    rw [exponentialClockTerm_re_ofReal,Nat.cast_one]
    have hx : 0<(1:ℝ)*L*t := by positivity
    have hO := liClockPairedEtaContiguousOddSeries_re_ofReal_ge hx.le
    exact mul_pos (mul_pos hL (Real.exp_pos _)) (hx.trans_le hO)
  rw [liClockPairedEtaContiguousClock_eq_tsum_exponential hL,Complex.re_tsum hs]
  exact (Complex.hasSum_re hs.hasSum).summable.tsum_pos hn 1 h1

end
end RHTower
