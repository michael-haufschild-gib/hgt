import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven
import GaloisForLFunctions.VerifiedHeightRungs.LiAndHausdorffEntries
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing
import GaloisForLFunctions.RHTower.ScaleIncompatibility
import GaloisForLFunctions.RHTower.ZModLFunctionCuspRadius

/-!
# Two consecutive prime intervals at an isolated quartet

A quarter-period dilates the complex wave by a purely imaginary scalar.
The two real increments therefore measure its two coordinates. Taking
their Euclidean norm removes the starting phase at every sufficiently
large cutoff, within one doubling interval.
-/

noncomputable section

open Complex
namespace GaloisForLFunctions.ExceptionalLayerTheory
open ExclusionOfTheCriticalState VerifiedHeightRungs VerifiedHeightRungs.HadamardBudget

/-- Centered sum of ordinary prime logarithms between two exponential cutoffs. -/
def thetaIntervalIncrement (t h : ℝ) : ℝ :=
  (Chebyshev.theta (Real.exp (t+h))-Real.exp (t+h))-
  (Chebyshev.theta (Real.exp t)-Real.exp t)

private theorem quarter_scale {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    let h := Real.pi/(2*|ρ.im|)
    let A := Real.exp (ρ.re*h)
    0<h ∧ Real.exp (4*h)<2 ∧ 1<A ∧
      (Complex.exp (ρ*(h:ℂ))=(A:ℂ)*I ∨ Complex.exp (ρ*(h:ℂ))=(A:ℂ)*(-I)) := by
  intro h A
  have hg : 67<|ρ.im| := lt_abs_im_of_rhVerifiedThrough rhVerifiedThrough_sixtySeven
    hq.xi_eq_zero hq.2.1.2.1 hq.re_lt_one hq.1.ne'
  have hg0 : 0<|ρ.im| := abs_pos.mpr hq.im_ne_zero
  have hh : 0<h := div_pos Real.pi_pos (by positivity)
  have hsmall : h<1/8 := (div_lt_iff₀ (by positivity)).mpr (by linarith only [hg,Real.pi_lt_four])
  refine ⟨hh,?_,Real.one_lt_exp_iff.mpr (mul_pos (by linarith only [hq.1]) hh),?_⟩
  · rw [← Real.exp_log (by norm_num : (0:ℝ)<2)]
    exact Real.exp_lt_exp.mpr (by linarith only [hsmall,_root_.RHTower.log_two_gt_half])
  have hz : Complex.exp (ρ*(h:ℂ))=(A:ℂ)*Complex.exp (((ρ.im*h:ℝ):ℂ)*I) := by
    rw [show (A:ℂ)=Complex.exp ((ρ.re*h:ℝ):ℂ) from Complex.ofReal_exp _,← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp <;> ring
  rw [hz]
  rcases lt_or_gt_of_ne hq.im_ne_zero with hn | hp
  · right
    have he : ρ.im*h= -Real.pi/2 := by dsimp only [h]; rw [abs_of_neg hn]; field_simp [hn.ne] <;> ring
    rw [he]; congr 1
    convert _root_.RHTower.exp_neg_quarter_turn using 2 <;> push_cast <;> ring
  · left
    have he : ρ.im*h= Real.pi/2 := by dsimp only [h]; rw [abs_of_pos hp]; field_simp [hp.ne'] <;> ring
    rw [he]; congr 1
    convert _root_.RHTower.exp_quarter_turn using 2 <;> push_cast <;> ring

private theorem quarter_pair_norm {Q : ℂ} (hq : Q=I ∨ Q=-I) (z : ℂ) :
    ‖(⟨z.re,(Q*z).re⟩:ℂ)‖=‖z‖ := by
  rcases hq with rfl | rfl <;> rw [Complex.norm_def,Complex.norm_def] <;>
    congr 1 <;> simp [Complex.normSq_apply,Complex.I_mul_re]

private theorem two_increments {A m : ℝ} (hA : 1≤A) {Q : ℂ} (hQ : Q=I ∨ Q=-I)
    (z : ℂ) (e₀ e₁ e₂ B : ℝ)
    (h₀ : |e₀+m*z.re|≤B) (h₁ : |e₁+m*(((A:ℂ)*Q)*z).re|≤B)
    (h₂ : |e₂+m*(((A:ℂ)*Q)*(((A:ℂ)*Q)*z)).re|≤B) :
    |‖(⟨e₁-e₀,(e₂-e₁)/A⟩:ℂ)‖-‖(-(m:ℂ))*(((A:ℂ)*Q)-1)*z‖| ≤ 4*B := by
  let D := (A:ℂ)*Q
  let w := -(m:ℂ)*(D-1)*z
  have hAr : 0<A := zero_lt_one.trans_le hA
  have hw : w.re= -(m*((D*z).re-z.re)) := by
    rw [show w= -(m:ℂ)*(D*z-z) by dsimp only [w]; ring]
    simp
  have hw' : (Q*w).re= -(m*((D*(D*z)).re-(D*z).re))/A := by
    apply (eq_div_iff hAr.ne').mpr
    rw [← Complex.re_mul_ofReal]
    have ha : Q*w*(A:ℂ)= -(m:ℂ)*(D*(D*z)-D*z) := by dsimp only [D,w]; ring
    rw [ha]; simp
  let v : ℂ := ⟨e₁-e₀,(e₂-e₁)/A⟩
  let u : ℂ := ⟨w.re,(Q*w).re⟩
  have hr : |(v-u).re|≤2*B := by
    change |e₁-e₀-w.re|≤_
    rw [hw,show e₁-e₀- -(m*((D*z).re-z.re)) = (e₁+m*(D*z).re)-(e₀+m*z.re) by ring]
    exact (abs_sub _ _).trans ((add_le_add h₁ h₀).trans_eq (two_mul B).symm)
  have hi : |(v-u).im|≤2*B := by
    change |(e₂-e₁)/A-(Q*w).re|≤_
    rw [hw',← sub_div,show e₂-e₁- -(m*((D*(D*z)).re-(D*z).re)) =
      (e₂+m*(D*(D*z)).re)-(e₁+m*(D*z).re) by ring,abs_div,abs_of_pos hAr]
    apply (div_le_self (abs_nonneg _) hA).trans
    exact (abs_sub _ _).trans ((add_le_add h₂ h₁).trans_eq (two_mul B).symm)
  change |‖v‖-‖w‖|≤_
  rw [← quarter_pair_norm hQ w]
  exact (abs_norm_sub_norm_le v u).trans ((Complex.norm_le_abs_re_add_abs_im _).trans
    ((add_le_add hr hi).trans_eq (by ring)))

private def powerMode (ρ : ℂ) (t : ℝ) : ℂ := Complex.exp (ρ*(t:ℂ))/ρ

private theorem powerMode_add (ρ : ℂ) (t h : ℝ) :
    powerMode ρ (t+h)=Complex.exp (ρ*(h:ℂ))*powerMode ρ t := by
  rw [powerMode,powerMode,Complex.ofReal_add,mul_add,Complex.exp_add]; ring

private theorem theta_mode_bound {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t : ℝ, 0≤t → 16≤Real.exp t →
    |Chebyshev.theta (Real.exp t)-Real.exp t+2*(quartetCopyMult ρ:ℝ)*(powerMode ρ t).re| ≤
      C*Real.exp (t/2)*(1+t^2) := by
  obtain ⟨K,hK⟩ := (hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hq.1 hq.2.1).mp hq
  let L := 3*(Real.log 4+4)
  have hL : 0≤L := by dsimp only [L]; positivity
  refine ⟨|K|+L,add_nonneg (abs_nonneg _) hL,fun t _ ht => ?_⟩
  let x := Real.exp t
  have hx : Real.sqrt x=Real.exp (t/2) := (Real.exp_half t).symm
  have he := hK x ht
  have hz : ((x:ℂ)^ρ/ρ)=powerMode ρ t := by dsimp only [x,powerMode]; rw [_root_.RHTower.cpow_ofReal_exp]; congr 2 <;> ring
  rw [hz,hx,show Real.log x=t from Real.log_exp t] at he
  have hθ := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt x
  have hθ' : |Chebyshev.psi x-Chebyshev.theta x|≤L*Real.exp (t/2) := by
    rwa [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)),← hx]
  let a := 2*(quartetCopyMult ρ:ℝ)*(powerMode ρ t).re
  change |Chebyshev.theta x-x+a|≤_
  rw [show Chebyshev.theta x-x+a=(Chebyshev.psi x-x+a)-(Chebyshev.psi x-Chebyshev.theta x) by ring]
  apply (abs_sub _ _).trans
  apply (add_le_add he hθ').trans
  have hek := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le) (sq_nonneg t)
  nlinarith only [hek,mul_nonneg (mul_nonneg hL (Real.exp_pos (t/2)).le) (sq_nonneg t),
    mul_nonneg (abs_nonneg K) (Real.exp_pos (t/2)).le]

/-- The norm of two successive centered prime-logarithm counts recovers a
strictly positive amplitude at every base, with square-root error. Four
such quarter-period intervals already fit within one doubling interval. -/
theorem singleQuartet_two_theta_intervals {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    let h := Real.pi/(2*|ρ.im|)
    let A := Real.exp (ρ.re*h)
    let C := 2*(quartetCopyMult ρ:ℝ)*‖(Complex.exp (ρ*(h:ℂ))-1)/ρ‖
    0<h ∧ Real.exp (4*h)<2 ∧ 0<C ∧ ∃ K : ℝ, 0≤K ∧ ∀ t : ℝ, 0≤t → 16≤Real.exp t →
      |‖(⟨thetaIntervalIncrement t h,thetaIntervalIncrement (t+h) h/A⟩:ℂ)‖ -
        C*Real.exp (ρ.re*t)| ≤ K*Real.exp ((t+2*h)/2)*(1+(t+2*h)^2) := by
  intro h A C
  have ⟨hh,hfit,hA,hphase⟩ := quarter_scale hq
  let D := Complex.exp (ρ*(h:ℂ))
  let m := 2*(quartetCopyMult ρ:ℝ)
  have hm : 0<m := mul_pos (by norm_num) (by exact_mod_cast hq.quartetCopyMult_pos)
  have hd : ‖D‖=A := by simp [D,A,h,Complex.norm_exp]
  have hone : D-1≠0 := fun e => hA.ne' (hd.symm.trans (by rw [sub_eq_zero.mp e,norm_one]))
  have hρ : ρ≠0 := fun e => hq.im_ne_zero (by simp [e])
  refine ⟨hh,hfit,mul_pos hm (norm_pos_iff.mpr (div_ne_zero hone hρ)),?_⟩
  obtain ⟨L,hL,hE⟩ := theta_mode_bound hq
  refine ⟨4*L,by positivity,fun t ht ht16 => ?_⟩
  let B := L*Real.exp ((t+2*h)/2)*(1+(t+2*h)^2)
  let E (s : ℝ) := Chebyshev.theta (Real.exp s)-Real.exp s
  have bound {s : ℝ} (hs : t≤s) (hs' : s≤t+2*h) : |E s+m*(powerMode ρ s).re|≤B := by
    apply (hE s (ht.trans hs) (ht16.trans (Real.exp_le_exp.mpr hs))).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hs'])) hL)
      (add_le_add_left ((sq_le_sq₀ (ht.trans hs) (by linarith only [ht,hh])).mpr hs') _)
      (by positivity) (by positivity)
  have he₀ := bound (s := t) le_rfl (by linarith only [hh])
  have he₁ := bound (s := t+h) (by linarith only [hh]) (by linarith only [hh])
  have he₂ := bound (s := (t+h)+h) (by linarith only [hh]) (by ring_nf)
  simp only [powerMode_add ρ _ h] at he₁ he₂
  obtain ⟨Q,hQ,hD⟩ : ∃ Q : ℂ, (Q=I ∨ Q=-I) ∧ D=(A:ℂ)*Q :=
    hphase.elim (fun e => ⟨I,Or.inl rfl,e⟩) (fun e => ⟨-I,Or.inr rfl,e⟩)
  have hr := two_increments hA.le hQ (powerMode ρ t) (E t) (E (t+h)) (E ((t+h)+h)) B he₀
    (by rw [← hD]; exact he₁) (by rw [← hD]; exact he₂)
  rw [← hD] at hr
  have hn : ‖(-(m:ℂ))*(D-1)*powerMode ρ t‖=C*Real.exp (ρ.re*t) := by
    simp only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm,
      powerMode,norm_div,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,C]
    change m*‖D-1‖*(Real.exp (ρ.re*t)/‖ρ‖)=m*(‖D-1‖/‖ρ‖)*Real.exp (ρ.re*t)
    ring
  rw [hn] at hr
  exact hr.trans_eq (by dsimp only [B]; ring)

#print axioms singleQuartet_two_theta_intervals

end GaloisForLFunctions.ExceptionalLayerTheory
