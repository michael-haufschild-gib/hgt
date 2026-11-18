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

open Complex Filter Topology
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
  have hg : 67 < |ρ.im| := lt_abs_im_of_rhVerifiedThrough rhVerifiedThrough_sixtySeven
    hq.xi_eq_zero hq.2.1.2.1 hq.re_lt_one hq.1.ne'
  have hg0 : 0 < |ρ.im| := abs_pos.mpr hq.im_ne_zero
  have hh : 0<h := div_pos Real.pi_pos (by positivity)
  have hsmall : h<1/8 := (div_lt_iff₀ (by positivity)).mpr (by linarith only [hg,Real.pi_lt_four])
  refine ⟨hh,?_,Real.one_lt_exp_iff.mpr (mul_pos (by linarith only [hq.1]) hh),?_⟩
  · rw [← Real.exp_log (by norm_num : (0:ℝ)<2)]
    exact Real.exp_lt_exp.mpr (by linarith only [hsmall,_root_.RHTower.log_two_gt_half])
  have hz : Complex.exp (ρ*(h:ℂ))=(A:ℂ)*Complex.exp (((ρ.im*h:ℝ):ℂ)*I) := by
    rw [show (A:ℂ)=Complex.exp ((ρ.re*h:ℝ):ℂ) from Complex.ofReal_exp _,← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  rw [hz]
  rcases lt_or_gt_of_ne hq.im_ne_zero with hn | hp
  · right
    have he : ρ.im*h= -Real.pi/2 := by dsimp only [h]; rw [abs_of_neg hn]; field_simp [hn.ne]
    rw [he]; congr 1
    convert _root_.RHTower.exp_neg_quarter_turn using 2; push_cast; ring
  · left
    have he : ρ.im*h= Real.pi/2 := by dsimp only [h]; rw [abs_of_pos hp]; field_simp [hp.ne']
    rw [he]; congr 1
    convert _root_.RHTower.exp_quarter_turn using 2; push_cast; ring

private theorem quarter_pair_norm {Q : ℂ} (hq : Q=I ∨ Q=-I) (z : ℂ) :
    ‖(⟨z.re,(Q*z).re⟩:ℂ)‖=‖z‖ := by
  rcases hq with rfl | rfl <;> rw [Complex.norm_def,Complex.norm_def] <;>
    congr 1 <;> simp [Complex.normSq_apply]

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
  have hz : ((x:ℂ)^ρ/ρ)=powerMode ρ t := by
    dsimp only [x,powerMode]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
      ← Complex.ofReal_log (Real.exp_pos t).le,Real.log_exp,mul_comm (t:ℂ) ρ]
  rw [hz,hx,show Real.log x=t from Real.log_exp t] at he
  have hθ := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt x
  have hθ' : |Chebyshev.psi x-Chebyshev.theta x|≤L*Real.exp (t/2) := by
    rwa [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _)),← hx]
  let a := 2*(quartetCopyMult ρ:ℝ)*(powerMode ρ t).re
  change |Chebyshev.theta x-x+a|≤_
  rw [show Chebyshev.theta x-x+a=(Chebyshev.psi x-x+a)-(Chebyshev.psi x-Chebyshev.theta x) by ring]
  apply (abs_sub _ _).trans
  apply (add_le_add he hθ').trans
  have hek := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos (t/2)).le) (sq_nonneg t)
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
  have hm : 0 < m := mul_pos (by norm_num) (by exact_mod_cast hq.quartetCopyMult_pos)
  have hd : ‖D‖=A := by
    simp only [D,A,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  have hone : D-1≠0 := fun e => hA.ne' (hd.symm.trans (by rw [sub_eq_zero.mp e,norm_one]))
  have hρ : ρ≠0 := fun e => hq.im_ne_zero (by simp [e])
  refine ⟨hh,hfit,mul_pos hm (norm_pos_iff.mpr (div_ne_zero hone hρ)),?_⟩
  obtain ⟨L,hL,hE⟩ := theta_mode_bound hq
  refine ⟨4*L,by positivity,fun t ht ht16 => ?_⟩
  let B := L*Real.exp ((t+2*h)/2)*(1+(t+2*h)^2)
  let E (s : ℝ) := Chebyshev.theta (Real.exp s)-Real.exp s
  have bound {s : ℝ} (hs : t ≤ s) (hs' : s ≤ t+2*h) : |E s+m*(powerMode ρ s).re| ≤ B := by
    apply (hE s (ht.trans hs) (ht16.trans (Real.exp_le_exp.mpr hs))).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hs'])) hL)
      (add_le_add (le_refl 1) ((sq_le_sq₀ (ht.trans hs) (by linarith only [ht,hh])).mpr hs'))
      (by positivity) (by positivity)
  have he₀ := bound (s := t) le_rfl (by linarith only [hh])
  have he₁ := bound (s := t+h) (by linarith only [hh]) (by linarith only [hh])
  have he₂ := bound (s := (t+h)+h) (by linarith only [hh]) (by linarith only)
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

private theorem quarter_coordinate {Q : ℂ} (hQ : Q=I ∨ Q=-I) (z : ℂ) :
    ∃ j : ℕ, j<4 ∧ ‖z‖/Real.sqrt 2 ≤ (Q^j*z).re := by
  by_contra! hn
  let B := ‖z‖/Real.sqrt 2
  have hr : |z.re|<B ∧ |z.im|<B := by
    have h₀ := hn 0 (by decide)
    have h₁ := hn 1 (by decide)
    have h₂ := hn 2 (by decide)
    have h₃ := hn 3 (by decide)
    rcases hQ with rfl | rfl <;>
      simp [pow_succ] at h₀ h₁ h₂ h₃ <;>
      constructor <;> apply abs_lt.mpr <;> constructor <;>
      dsimp only [B] <;> linarith only [h₀,h₁,h₂,h₃]
  have hh := mul_lt_mul_of_pos_left (max_lt hr.1 hr.2) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
  have ht := (Complex.norm_le_sqrt_two_mul_max z).trans_lt hh
  dsimp only [B] at ht
  rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'] at ht
  exact lt_irrefl _ ht

/-- In four consecutive quarter-period intervals each prescribed sign attains
at least 1/√2 of the normalized wave amplitude, up to square-root error. -/
theorem singleQuartet_four_theta_intervals {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    let h := Real.pi/(2*|ρ.im|)
    let A := Real.exp (ρ.re*h)
    let C := 2*(quartetCopyMult ρ:ℝ)*‖(Complex.exp (ρ*(h:ℂ))-1)/ρ‖
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → 16 ≤ Real.exp t →
      ∀ ε : ℝ, |ε|=1 → ∃ j : ℕ, j<4 ∧
        C*Real.exp (ρ.re*t)/Real.sqrt 2 - K*Real.exp ((t+4*h)/2)*(1+(t+4*h)^2) ≤
          ε*thetaIntervalIncrement (t+j*h) h/A^j := by
  intro h A C
  obtain ⟨hh,_,hA,hphase⟩ := quarter_scale hq
  obtain ⟨L,hL,hE⟩ := theta_mode_bound hq
  refine ⟨2*L,by positivity,fun t ht ht16 ε hε => ?_⟩
  let m := 2*(quartetCopyMult ρ:ℝ)
  let D := Complex.exp (ρ*(h:ℂ))
  obtain ⟨Q,hQ,hD⟩ : ∃ Q : ℂ, (Q=I ∨ Q=-I) ∧ D=(A:ℂ)*Q :=
    hphase.elim (fun e => ⟨I,Or.inl rfl,e⟩) (fun e => ⟨-I,Or.inr rfl,e⟩)
  let w := -(m:ℂ)*(D-1)*powerMode ρ t
  obtain ⟨j,hj,hread⟩ := quarter_coordinate hQ ((ε:ℂ)*w)
  refine ⟨j,hj,?_⟩
  have ha : 1 ≤ A^j := one_le_pow₀ hA.le
  let u := t+(j:ℝ)*h
  let B := L*Real.exp ((t+4*h)/2)*(1+(t+4*h)^2)
  have hj' : (j:ℝ) ≤ 3 := by exact_mod_cast (show j ≤ 3 by omega)
  have hu : t ≤ u := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le)
  have huv : u+h ≤ t+4*h := by dsimp only [u]; linarith only [mul_le_mul_of_nonneg_right hj' hh.le]
  have hb (v : ℝ) (hl : t ≤ v) (hv : v ≤ t+4*h) :
      |Chebyshev.theta (Real.exp v)-Real.exp v+m*(powerMode ρ v).re| ≤ B := by
    apply (hE _ (ht.trans hl) (ht16.trans (Real.exp_le_exp.mpr hl))).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hv])) hL)
      (add_le_add (le_refl 1) ((sq_le_sq₀ (ht.trans hl) ((ht.trans hl).trans hv)).mpr hv))
      (by positivity) (by positivity)
  have hdiff := (abs_sub _ _).trans (add_le_add (hb (u+h) (hu.trans (le_add_of_nonneg_right hh.le)) huv)
    (hb u hu ((le_add_of_nonneg_right hh.le).trans huv)))
  have mode_j (k : ℕ) : powerMode ρ (t+k*h)=D^k*powerMode ρ t := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ,add_mul,one_mul,← add_assoc,powerMode_add,ih,pow_succ]; dsimp only [D]; ring
  have hw : -(m:ℂ)*(powerMode ρ (u+h)-powerMode ρ u)=(A:ℂ)^j*Q^j*w := by
    rw [powerMode_add,show powerMode ρ u=D^j*powerMode ρ t from mode_j _]
    change -(m:ℂ)*(D*(D^j*powerMode ρ t)-D^j*powerMode ρ t)=_
    dsimp only [w]
    rw [hD,mul_pow]; ring
  have H : |thetaIntervalIncrement u h - A^j*(Q^j*w).re| ≤ 2*B := by
    have e := congrArg Complex.re hw
    rw [← Complex.ofReal_pow,mul_assoc,Complex.re_ofReal_mul] at e
    simp only [neg_mul,Complex.neg_re,Complex.re_ofReal_mul,Complex.sub_re] at e
    rw [← e,thetaIntervalIncrement]
    calc
      _ = |(Chebyshev.theta (Real.exp (u+h))-Real.exp (u+h)+m*(powerMode ρ (u+h)).re)-
          (Chebyshev.theta (Real.exp u)-Real.exp u+m*(powerMode ρ u).re)| := by congr 1; ring
      _ ≤ B+B := hdiff
      _ = 2*B := (two_mul B).symm
  have signed : |ε*thetaIntervalIncrement u h/A^j-ε*(Q^j*w).re| ≤ 2*B := by
    rw [show ε*thetaIntervalIncrement u h/A^j-ε*(Q^j*w).re =
      ε*(thetaIntervalIncrement u h-A^j*(Q^j*w).re)/A^j by field_simp,
      abs_div,abs_mul,hε,one_mul,abs_of_pos (zero_lt_one.trans_le ha)]
    exact (div_le_self (abs_nonneg _) ha).trans H
  have hn : ‖(ε:ℂ)*w‖=C*Real.exp (ρ.re*t) := by
    have hm : 0 ≤ m := by dsimp only [m]; positivity
    simp only [w,C,powerMode,norm_mul,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      hε,one_mul,abs_of_nonneg hm,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero]
    dsimp only [D,m]; ring
  rw [hn,show Q^j*((ε:ℂ)*w)=(ε:ℂ)*(Q^j*w) by ring,Complex.re_ofReal_mul] at hread
  have hl := (abs_le.mp signed).1
  change _ ≤ ε*thetaIntervalIncrement u h/A^j
  dsimp only [B] at hl
  linarith only [hl,hread]

private theorem shifted_error_small {β K c : ℝ} (hβ : 1/2<β) (hK : 0≤K) (hc : 0<c) (d : ℝ) :
    ∀ᶠ t : ℝ in atTop, K*Real.exp ((t+d)/2)*(1+(t+d)^2) ≤ c*Real.exp (β*t) := by
  let k := 2*(K+1)*Real.exp (β*d)
  have hk : 0<k := by dsimp only [k]; positivity
  obtain ⟨L,hL⟩ := eventually_atTop.mp ((_root_.isLittleO_exp_mul_rpow_of_lt 2 hβ).def (div_pos hc hk))
  filter_upwards [eventually_ge_atTop (max L 1-d)] with t ht
  have htL : L ≤ t+d := by linarith only [ht,le_max_left L 1]
  have ht1 : 1 ≤ t+d := by linarith only [ht,le_max_right L 1]
  have he := hL (t+d) htL
  change ‖Real.exp ((1/2)*(t+d))*(t+d)^(2:ℝ)‖ ≤ c/k*‖Real.exp (β*(t+d))‖ at he
  simp only [Real.norm_eq_abs,Real.rpow_two,show 1/2*(t+d)=(t+d)/2 by ring,abs_mul,
    abs_of_pos (Real.exp_pos _),abs_of_nonneg (sq_nonneg (t+d))] at he
  have hpol : 1+(t+d)^2 ≤ 2*(t+d)^2 := by nlinarith only [ht1,sq_nonneg (t+d-1)]
  calc
    _ ≤ (2*(K+1))*(Real.exp ((t+d)/2)*(t+d)^2) := by
      have h := mul_le_mul_of_nonneg_left hpol (mul_nonneg hK (Real.exp_pos ((t+d)/2)).le)
      nlinarith only [h,mul_nonneg (Real.exp_pos ((t+d)/2)).le (sq_nonneg (t+d))]
    _ ≤ _ := (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by
      rw [mul_add β t d,Real.exp_add]
      dsimp only [k]
      field_simp [show K+1≠0 by linarith only [hK]] <;> ring)

/-- Every large octave contains both signs of the centered ordinary-prime
logarithm count, each with the exact real exponent of the quartet. -/
theorem singleQuartet_signed_theta_octave {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ Y : ℝ in atTop, ∀ ε : ℝ, |ε|=1 →
      ∃ l u : ℝ, Y≤l ∧ l≤u ∧ u≤2*Y ∧
        c*Y^ρ.re ≤ ε*((Chebyshev.theta u-u)-(Chebyshev.theta l-l)) := by
  let h := Real.pi/(2*|ρ.im|)
  let A := Real.exp (ρ.re*h)
  let C := 2*(quartetCopyMult ρ:ℝ)*‖(Complex.exp (ρ*(h:ℂ))-1)/ρ‖
  have ⟨hh,hfit,hC,_⟩ := singleQuartet_two_theta_intervals hq
  obtain ⟨K,hK,hreadings⟩ := singleQuartet_four_theta_intervals hq
  let c := C/(2*Real.sqrt 2)
  have hc : 0<c := div_pos hC (by positivity)
  have hscale := (quarter_scale hq).2.2.1
  obtain ⟨T,hT⟩ := eventually_atTop.mp (shifted_error_small hq.1 hK hc (4*h))
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop (max 16 (Real.exp T))] with Y hY
  have h16 : 16≤Y := (le_max_left _ _).trans hY
  have hpos : 0<Y := by linarith only [h16]
  let t := Real.log Y
  have hy : Real.exp t=Y := Real.exp_log hpos
  have ht : 0≤t := Real.log_nonneg (by linarith only [h16])
  have hTt : T≤t := (Real.le_log_iff_exp_le hpos).mpr ((le_max_right _ _).trans hY)
  intro ε hε
  obtain ⟨j,hj,hread⟩ := hreadings t ht (by rwa [hy]) ε hε
  have hj' : (j:ℝ)≤3 := by exact_mod_cast (show j≤3 by omega)
  let v := t+(j:ℝ)*h
  have hl : t≤v := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh.le)
  have hu : v+h≤t+4*h := by dsimp only [v]; linarith only [mul_le_mul_of_nonneg_right hj' hh.le]
  have ha : 1≤A^j := one_le_pow₀ hscale.le
  refine ⟨Real.exp v,Real.exp (v+h),by rw [← hy]; exact Real.exp_le_exp.mpr hl,
    Real.exp_le_exp.mpr (le_add_of_nonneg_right hh.le),?_,?_⟩
  · apply (Real.exp_le_exp.mpr hu).trans
    rw [Real.exp_add,hy,mul_comm]
    exact mul_le_mul_of_nonneg_right hfit.le hpos.le
  · have he := hT t hTt
    have hd : C/Real.sqrt 2=2*c := by dsimp only [c]; ring
    change C*Real.exp (ρ.re*t)/Real.sqrt 2-_ ≤ ε*thetaIntervalIncrement v h/A^j at hread
    rw [mul_div_right_comm,hd] at hread
    have hw : c*Real.exp (ρ.re*t) ≤ ε*thetaIntervalIncrement v h/A^j := by
      linarith only [he,hread]
    have hp := (le_div_iff₀ (zero_lt_one.trans_le ha)).mp hw
    rw [Real.rpow_def_of_pos hpos,mul_comm (Real.log Y) ρ.re]
    exact (le_mul_of_one_le_right (mul_nonneg hc.le (Real.exp_pos _).le) ha).trans hp

/-- The quartet controls all ordinary-prime error readings at its real exponent. -/
theorem singleQuartet_theta_error_power {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ y : ℝ in atTop, |Chebyshev.theta y-y| ≤ L*y^ρ.re := by
  obtain ⟨K,hK,h⟩ := theta_mode_bound hq
  obtain ⟨T,hT⟩ := eventually_atTop.mp (shifted_error_small hq.1 hK (by norm_num : (0:ℝ)<1) 0)
  let m := 2*(quartetCopyMult ρ:ℝ)
  have hm : 0 ≤ m := by dsimp only [m]; positivity
  refine ⟨1+m/‖ρ‖,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 16 (Real.exp T))] with y hy
  have h16 : 16≤y := (le_max_left _ _).trans hy
  have hp : 0<y := by linarith only [h16]
  let t := Real.log y
  have he : Real.exp t=y := Real.exp_log hp
  have ht := (Real.le_log_iff_exp_le hp).mpr ((le_max_right _ _).trans hy)
  have hsmall := hT t ht
  simp only [add_zero,one_mul] at hsmall
  have hθ := (h t (Real.log_nonneg (by linarith only [h16])) (by rwa [he])).trans hsmall
  rw [he] at hθ
  have hw := Complex.abs_re_le_norm (powerMode ρ t)
  rw [powerMode,norm_div,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] at hw
  have hsum := abs_sub (Chebyshev.theta y-y+m*(powerMode ρ t).re) (m*(powerMode ρ t).re)
  rw [add_sub_cancel_right,abs_mul,abs_of_nonneg hm] at hsum
  rw [Real.rpow_def_of_pos hp,mul_comm (Real.log y) ρ.re]
  exact (hsum.trans (add_le_add hθ (mul_le_mul_of_nonneg_left hw hm))).trans_eq (by ring)

end GaloisForLFunctions.ExceptionalLayerTheory
