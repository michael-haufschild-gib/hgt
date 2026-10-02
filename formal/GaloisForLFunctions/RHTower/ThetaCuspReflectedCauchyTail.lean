import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomReflectedApproximation
import GaloisForLFunctions.RHTower.ThetaCuspFirstAtomGaussianJetLimits
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cauchy control of the complete reflected theta tail

The literal complex source and its first two atoms are compared before
differentiation. Opposite translations cancel their exponential prefactors,
so the entire omitted double sum admits one common disk majorant. Cauchy
estimates then control every real reflected jet, without an order cutoff
or an assumed derivative bound on the omitted source.
-/

open Complex Real
namespace RHTower.ThetaCuspReflectedCauchyTail
noncomputable section

private theorem exp_small_upper : Real.exp (3/10 : ℝ) ≤ 50/37 := by
  have h1 : Real.exp 1 ≤ (2719/1000 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le h1 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  by_contra hc
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤50/37)
    (le_of_lt (lt_of_not_ge hc)) 10
  rw [← Real.exp_nat_mul] at h
  norm_num at h
  linarith

private theorem exp_disk_lower {w : ℂ} (hw : ‖w‖ ≤ 3/10) :
    Real.exp (-(3/10 : ℝ)) ≤ (Complex.exp w).re := by
  let d := w.re+3/10
  have hre := (Complex.abs_re_le_norm w).trans hw
  have hd : 0 ≤ d := by dsimp [d]; linarith [(abs_le.mp hre).1]
  have hdU : d ≤ 3/5 := by dsimp [d]; linarith [(abs_le.mp hre).2]
  have hnorm := mul_self_le_mul_self (norm_nonneg w) hw
  rw [← pow_two, Complex.sq_norm, Complex.normSq_apply] at hnorm
  have hb : w.im^2 ≤ (3/5)*d := by dsimp [d]; nlinarith [sq_nonneg (w.re+3/10)]
  have hcos : 1-(3/10)*d ≤ Real.cos w.im := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := w.im)]
  have hprod : 1 ≤ Real.exp d*Real.cos w.im := by
    calc
      1 ≤ (1+d)*(1-(3/10)*d) := by nlinarith [mul_nonneg hd (sub_nonneg.mpr hdU)]
      _ ≤ Real.exp d*Real.cos w.im := mul_le_mul
        (by linarith [Real.add_one_le_exp d]) hcos (by linarith) (Real.exp_pos _).le
  rw [Complex.exp_re]
  have he : Real.exp w.re*Real.cos w.im =
      Real.exp (-(3/10 : ℝ))*(Real.exp d*Real.cos w.im) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [d]; ring
  rw [he]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le

private theorem exp_twice_disk_lower {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    (37/50 : ℝ) ≤ Real.exp (2*z.re)*Real.cos (2*z.im) := by
  have hw : ‖(2:ℂ)*z‖ ≤ 3/10 := by rw [norm_mul]; norm_num; linarith
  have h := exp_disk_lower hw
  have hi := one_div_le_one_div_of_le (Real.exp_pos (3/10)) exp_small_upper
  rw [Real.exp_neg] at h
  norm_num at hi
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im] at h
  norm_num at h
  nlinarith only [h, hi]

private def atomPrefactor (x u : ℝ) : ℝ :=
  2*thetaCuspSingleAtomReflectionScale 1 x*Real.exp (x/2+5*u/2)*
    (2*thetaCuspSingleAtomReflectionScale 1 x*(50/37)+3)

private theorem complex_atom_bound {x : ℝ} (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    {z : ℂ} (hz : ‖z‖ ≤ 3/20) (n : ℕ) :
    ‖thetaCuspComplexTerm ((x:ℂ)+z) n‖ ≤ atomPrefactor x z.re*
      ((n:ℝ)^4*Real.exp (-(37/50)*thetaCuspSingleAtomReflectionScale 1 x*(n:ℝ)^2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [thetaCuspComplexTerm_zero]
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hqs : q=Real.pi*Real.exp (2*x) := by simp [q, thetaCuspSingleAtomReflectionScale]
  have him := (Complex.abs_im_le_norm z).trans hz
  have hre := (Complex.abs_re_le_norm z).trans hz
  have hδ : 2*|z.im| ≤ Real.pi/2 := by linarith [Real.pi_gt_three]
  have hp := norm_thetaCuspComplexTerm_le_pointwise hδ
    (z := (x:ℂ)+z) (by simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using le_rfl (a := |z.im|)) n
  simp only [Complex.add_re, Complex.ofReal_re] at hp
  have hcos : Real.cos (2*|z.im|)=Real.cos (2*z.im) := by
    calc
      _ = Real.cos |2*z.im| := by rw [abs_mul, abs_two]
      _ = _ := Real.cos_abs _
  rw [hcos] at hp
  have he2 : Real.exp (2*(x+z.re))=Real.exp (2*x)*Real.exp (2*z.re) := by
    rw [← Real.exp_add]; congr 1; ring
  have he4 : Real.exp (4*(x+z.re))=Real.exp (2*x)^2*Real.exp (2*z.re)^2 := by
    calc
      _ = Real.exp (2*(x+z.re)+2*(x+z.re)) := by congr 1; ring
      _ = Real.exp (2*(x+z.re))*Real.exp (2*(x+z.re)) := Real.exp_add _ _
      _ = _ := by rw [he2]; ring
  have hefront : Real.exp ((x+z.re)/2)*Real.exp (2*z.re)=Real.exp (x/2+5*z.re/2) := by
    rw [← Real.exp_add]; congr 1; ring
  have heU : Real.exp (2*z.re) ≤ (50/37 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hre).2])).trans exp_small_upper
  have hgauss : Real.exp (-(Real.pi*Real.cos (2*z.im))*(n:ℝ)^2*Real.exp (2*(x+z.re))) ≤
      Real.exp (-(37/50)*q*(n:ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    rw [he2]
    have hm := mul_le_mul_of_nonneg_left (exp_twice_disk_lower hz)
      (show 0 ≤ q*(n:ℝ)^2 by positivity)
    rw [hqs] at hm ⊢
    nlinarith only [hm]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hn24 : (n:ℝ)^2 ≤ (n:ℝ)^4 := by nlinarith [sq_nonneg ((n:ℝ)^2-1)]
  have hpoly : 2*q*(n:ℝ)^4*Real.exp (2*z.re)+3*(n:ℝ)^2 ≤
      (2*q*(50/37)+3)*(n:ℝ)^4 := by
    have hm := mul_le_mul_of_nonneg_left heU (show 0 ≤ 2*q*(n:ℝ)^4 by positivity)
    nlinarith only [hm, hn24]
  have hpre : Real.exp ((x+z.re)/2)*(2*Real.pi)*
      (2*Real.pi*(n:ℝ)^4*Real.exp (4*(x+z.re))+3*(n:ℝ)^2*Real.exp (2*(x+z.re))) =
      2*q*Real.exp (x/2+5*z.re/2)*(2*q*(n:ℝ)^4*Real.exp (2*z.re)+3*(n:ℝ)^2) := by
    rw [he2, he4, ← hefront, hqs]
    ring
  have hfront := mul_le_mul_of_nonneg_left hpoly
    (show 0 ≤ 2*q*Real.exp (x/2+5*z.re/2) by positivity)
  rw [hpre] at hp
  exact hp.trans ((mul_le_mul hfront hgauss (Real.exp_pos _).le (by positivity)).trans_eq (by
    dsimp [atomPrefactor, q]; ring))

private theorem exp_three_lower : (20:ℝ) ≤ Real.exp 3 := by
  have h1 : (2718/1000:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) h1 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

private theorem exp_neg_le_eight_thousand {t : ℝ} (ht : 9 ≤ t) :
    Real.exp (-t) ≤ 1/8000 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hh := hp.trans (Real.exp_le_exp.mpr ht)
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hh

private theorem quartic_head (k : ℕ) : ((k+1:ℕ):ℝ)^4 ≤ 16^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hs := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(k:ℝ)+2)
        (show (k:ℝ)+2 ≤ 2*((k:ℝ)+1) by linarith [Nat.cast_nonneg (α := ℝ) k]) 4
      push_cast at ih ⊢
      rw [pow_succ (16:ℝ) k]
      nlinarith only [hs, ih]

private theorem quartic_deep (k : ℕ) : ((k+3:ℕ):ℝ)^4 ≤ 81*4^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hs : ((k:ℝ)+4)^4 ≤ 4*((k:ℝ)+3)^4 := by
        have hh : 0 ≤ 3*(k:ℝ)^4+32*(k:ℝ)^3+120*(k:ℝ)^2+176*(k:ℝ)+68 := by positivity
        nlinarith only [hh]
      push_cast at ih ⊢
      rw [pow_succ (4:ℝ) k]
      nlinarith only [hs, ih]

private theorem gaussian_head_term {a : ℝ} (ha : 37/10 ≤ a) (k : ℕ) :
    ((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2) ≤
      Real.exp (-a)*(1/500)^k := by
  have ha0 : 0 ≤ a := by linarith
  have hk2 : (k:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by norm_num : 2≠0) k
  have hgap : 1+3*(k:ℝ) ≤ ((k+1:ℕ):ℝ)^2 := by push_cast; nlinarith
  have he : Real.exp (-a*((k+1:ℕ):ℝ)^2) ≤ Real.exp (-a)*Real.exp (-(3*a))^k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr hgap)]
  have hc := exp_neg_le_eight_thousand (t := 3*a) (by linarith)
  calc
    _ ≤ 16^k*(Real.exp (-a)*Real.exp (-(3*a))^k) :=
      mul_le_mul (quartic_head k) he (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-a)*(16*Real.exp (-(3*a)))^k := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hc]) k) (Real.exp_pos _).le

private theorem gaussian_deep_term {a : ℝ} (ha : 37/10 ≤ a) (k : ℕ) :
    ((k+3:ℕ):ℝ)^4*Real.exp (-a*((k+3:ℕ):ℝ)^2) ≤
      81*Real.exp (-9*a)*(1/1000)^k := by
  have ha0 : 0 ≤ a := by linarith
  have hk2 : (k:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by norm_num : 2≠0) k
  have hgap : 9+7*(k:ℝ) ≤ ((k+3:ℕ):ℝ)^2 := by push_cast; nlinarith
  have he : Real.exp (-a*((k+3:ℕ):ℝ)^2) ≤ Real.exp (-9*a)*Real.exp (-(7*a))^k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr hgap)]
  have hc := exp_neg_le_eight_thousand (t := 7*a) (by linarith)
  calc
    _ ≤ (81*4^k)*(Real.exp (-9*a)*Real.exp (-(7*a))^k) :=
      mul_le_mul (quartic_deep k) he (Real.exp_pos _).le (by positivity)
    _ = 81*Real.exp (-9*a)*(4*Real.exp (-(7*a)))^k := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hc]) k) (by positivity)

private theorem gaussian_head_sum {a : ℝ} (ha : 37/10 ≤ a) :
    (∑' k : ℕ, ((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2)) ≤
      (101/100)*Real.exp (-a) := by
  have hm : Summable (fun k : ℕ => Real.exp (-a)*(1/500)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/500) (by norm_num)).mul_left _
  have hs := Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_head_term ha) hm
  have h := hs.tsum_le_tsum (gaussian_head_term ha) hm
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/500) (by norm_num)] at h
  nlinarith only [h, (Real.exp_pos (-a)).le]

private theorem gaussian_deep_sum {a : ℝ} (ha : 37/10 ≤ a) :
    (∑' k : ℕ, ((k+3:ℕ):ℝ)^4*Real.exp (-a*((k+3:ℕ):ℝ)^2)) ≤
      82*Real.exp (-9*a) := by
  have hm : Summable (fun k : ℕ => 81*Real.exp (-9*a)*(1/1000)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/1000) (by norm_num)).mul_left _
  have hs := Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_deep_term ha) hm
  have h := hs.tsum_le_tsum (gaussian_deep_term ha) hm
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/1000) (by norm_num)] at h
  nlinarith only [h, (Real.exp_pos (-9*a)).le]

private theorem shifted_mem_strip (x : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    (x:ℂ)+z ∈ thetaCuspStrip := by
  have hi := (Complex.abs_im_le_norm z).trans hz
  simp only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, zero_add]
  linarith [Real.pi_gt_three]

private noncomputable def twoComplex (z : ℂ) : ℂ :=
  thetaCuspComplexTerm z 1+thetaCuspComplexTerm z 2

private noncomputable def deepComplex (z : ℂ) : ℂ :=
  thetaCuspStripSource z-twoComplex z

private theorem deep_eq_tsum {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    deepComplex z=∑' k : ℕ, thetaCuspComplexTerm z (k+3) := by
  have hs := summable_thetaCuspComplexTerm hz
  unfold deepComplex twoComplex thetaCuspStripSource
  rw [← hs.sum_add_tsum_nat_add 3]
  norm_num [Finset.sum_range_succ, thetaCuspComplexTerm_zero]

private theorem full_complex_bound {x : ℝ} (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    ‖thetaCuspStripSource ((x:ℂ)+z)‖ ≤ atomPrefactor x z.re*
      ((101/100)*Real.exp (-((37/50)*thetaCuspSingleAtomReflectionScale 1 x))) := by
  let a := (37/50)*thetaCuspSingleAtomReflectionScale 1 x
  have ha : 37/10 ≤ a := by dsimp [a]; linarith
  have hK : 0 ≤ atomPrefactor x z.re := by unfold atomPrefactor; positivity
  have hs := summable_thetaCuspComplexTerm (shifted_mem_strip x hz)
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hg : Summable (fun k : ℕ => ((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_head_term ha)
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/500) (by norm_num)).mul_left _)
  unfold thetaCuspStripSource
  rw [hs.tsum_eq_zero_add, thetaCuspComplexTerm_zero, zero_add]
  calc
    _ ≤ ∑' k : ℕ, ‖thetaCuspComplexTerm ((x:ℂ)+z) (k+1)‖ := norm_tsum_le_tsum_norm hs1.norm
    _ ≤ ∑' k : ℕ, atomPrefactor x z.re*
        (((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2)) :=
      hs1.norm.tsum_le_tsum (fun k => by simpa only [a, neg_mul] using complex_atom_bound hq hz (k+1)) (hg.mul_left _)
    _ = atomPrefactor x z.re*(∑' k : ℕ, ((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2)) :=
      tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_head_sum ha) hK

private theorem deep_complex_bound {x : ℝ} (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    ‖deepComplex ((x:ℂ)+z)‖ ≤ atomPrefactor x z.re*
      (82*Real.exp (-9*((37/50)*thetaCuspSingleAtomReflectionScale 1 x))) := by
  let a := (37/50)*thetaCuspSingleAtomReflectionScale 1 x
  have ha : 37/10 ≤ a := by dsimp [a]; linarith
  have hK : 0 ≤ atomPrefactor x z.re := by unfold atomPrefactor; positivity
  have hs := summable_thetaCuspComplexTerm (shifted_mem_strip x hz)
  have hs3 := (summable_nat_add_iff 3).mpr hs
  have hg : Summable (fun k : ℕ => ((k+3:ℕ):ℝ)^4*Real.exp (-a*((k+3:ℕ):ℝ)^2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_deep_term ha)
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/1000) (by norm_num)).mul_left _)
  rw [deep_eq_tsum (shifted_mem_strip x hz)]
  calc
    _ ≤ ∑' k : ℕ, ‖thetaCuspComplexTerm ((x:ℂ)+z) (k+3)‖ := norm_tsum_le_tsum_norm hs3.norm
    _ ≤ ∑' k : ℕ, atomPrefactor x z.re*
        (((k+3:ℕ):ℝ)^4*Real.exp (-a*((k+3:ℕ):ℝ)^2)) :=
      hs3.norm.tsum_le_tsum (fun k => by simpa only [a, neg_mul] using complex_atom_bound hq hz (k+3)) (hg.mul_left _)
    _ = atomPrefactor x z.re*(∑' k : ℕ, ((k+3:ℕ):ℝ)^4*Real.exp (-a*((k+3:ℕ):ℝ)^2)) :=
      tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_deep_sum ha) hK

private theorem prefactor_product_bound {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (u : ℝ) :
    atomPrefactor x u*atomPrefactor x (-u) ≤
      6*Real.exp (2*thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspSourceTerm x 1^2 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq5 : 5 ≤ q := hq
  have hpoly : (2*q*(50/37)+3)^2 ≤ 6*(2*q-3)^2 := by
    nlinarith only [hq5, sq_nonneg (q-5)]
  have he : Real.exp (x/2+5*u/2)*Real.exp (x/2+5*(-u)/2)=Real.exp x := by
    rw [← Real.exp_add]; congr 1; ring
  have hK : atomPrefactor x u*atomPrefactor x (-u)=4*q^2*Real.exp x*(2*q*(50/37)+3)^2 := by
    unfold atomPrefactor
    change (2*q*Real.exp (x/2+5*u/2)*(2*q*(50/37)+3))*
      (2*q*Real.exp (x/2+5*(-u)/2)*(2*q*(50/37)+3)) = _
    calc
      _ = 4*q^2*(Real.exp (x/2+5*u/2)*Real.exp (x/2+5*(-u)/2))*(2*q*(50/37)+3)^2 := by ring
      _ = _ := by rw [he]
  have he2 : Real.exp (2*q)*Real.exp (x/2-q)^2=Real.exp x := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hf : Real.exp (2*q)*thetaCuspSourceTerm x 1^2=4*q^2*Real.exp x*(2*q-3)^2 := by
    rw [thetaCuspSourceTerm_one_eq_scale_profile]
    change Real.exp (2*q)*(Real.exp (x/2-q)*(4*q^2-6*q))^2 = _
    calc
      _ = (Real.exp (2*q)*Real.exp (x/2-q)^2)*(4*q^2*(2*q-3)^2) := by ring
      _ = _ := by rw [he2]; ring
  have hm := mul_le_mul_of_nonneg_left hpoly (show 0 ≤ 4*q^2*Real.exp x by positivity)
  rw [hK]
  change _ ≤ 6*Real.exp (2*q)*thetaCuspSourceTerm x 1^2
  rw [mul_assoc 6, hf]
  nlinarith only [hm]

private theorem reflected_gaussian_bound {a : ℝ} (ha : 37/10 ≤ a) :
    6*(2*((101/100)*Real.exp (-a))*(82*Real.exp (-9*a))+
      (82*Real.exp (-9*a))^2) ≤ 1000*Real.exp (-10*a) := by
  have hc := exp_neg_le_eight_thousand (t := 8*a) (by linarith)
  have h10 : Real.exp (-a)*Real.exp (-9*a)=Real.exp (-10*a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h18 : Real.exp (-9*a)^2=Real.exp (-10*a)*Real.exp (-8*a) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have he : 6*(2*((101/100)*Real.exp (-a))*(82*Real.exp (-9*a))+
      (82*Real.exp (-9*a))^2) =
      (24846/25)*Real.exp (-10*a)+40344*Real.exp (-10*a)*Real.exp (-8*a) := by
    calc
      _ = (24846/25)*(Real.exp (-a)*Real.exp (-9*a))+40344*Real.exp (-9*a)^2 := by ring
      _ = _ := by rw [h10, h18]; ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 40344*Real.exp (-10*a) by positivity)
  simp only [neg_mul] at hm ⊢
  nlinarith only [hm, (Real.exp_pos (-(10*a))).le]

private theorem exp_twenty_seven_inverse : Real.exp (-27:ℝ) ≤ 1/500000000000 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 9
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hp])

/-- Complete reflected source minus the literal first-two-atom reflection product. -/
noncomputable def complexReflectedError (x : ℝ) (z : ℂ) : ℂ :=
  thetaCuspStripSource ((x:ℂ)+z)*thetaCuspStripSource ((x:ℂ)-z)-
    twoComplex ((x:ℂ)+z)*twoComplex ((x:ℂ)-z)

/-- Uniform disk bound retaining every omitted source atom and both cross terms. -/
theorem complex_reflected_error_bound {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    ‖complexReflectedError x z‖ ≤ thetaCuspSourceTerm x 1^2/500000000 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let a := (37/50)*q
  let Kp := atomPrefactor x z.re
  let Km := atomPrefactor x (-z.re)
  let S := (101/100)*Real.exp (-a)
  let D := 82*Real.exp (-9*a)
  have ha : 37/10 ≤ a := by dsimp [a, q]; linarith
  have hKp : 0 ≤ Kp := by dsimp [Kp, atomPrefactor]; positivity
  have hKm : 0 ≤ Km := by dsimp [Km, atomPrefactor]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hzn : ‖-z‖ ≤ 3/20 := by simpa only [norm_neg] using hz
  have hFp := full_complex_bound hq hz
  have hHp := deep_complex_bound hq hz
  have hFm := full_complex_bound hq hzn
  have hHm := deep_complex_bound hq hzn
  simp only [Complex.neg_re, ← sub_eq_add_neg] at hFm hHm
  have herr : complexReflectedError x z =
      deepComplex ((x:ℂ)+z)*thetaCuspStripSource ((x:ℂ)-z)+
      thetaCuspStripSource ((x:ℂ)+z)*deepComplex ((x:ℂ)-z)-
      deepComplex ((x:ℂ)+z)*deepComplex ((x:ℂ)-z) := by
    unfold complexReflectedError deepComplex
    ring
  have h1 := mul_le_mul hHp hFm (norm_nonneg _) (show 0 ≤ Kp*D by positivity)
  have h2 := mul_le_mul hFp hHm (norm_nonneg _) (show 0 ≤ Kp*S by positivity)
  have h3 := mul_le_mul hHp hHm (norm_nonneg _) (show 0 ≤ Kp*D by positivity)
  have hK := prefactor_product_bound hq z.re
  have hG := reflected_gaussian_bound ha
  have hb : 0 ≤ 2*S*D+D^2 := by positivity
  calc
    _ ≤ Kp*Km*(2*S*D+D^2) := by
      rw [herr]
      apply (norm_sub_le _ _).trans
      apply (add_le_add (norm_add_le _ _) le_rfl).trans
      simp only [norm_mul]
      change _ ≤ Kp*Km*(2*S*D+D^2)
      change _ ≤ (Kp*D)*(Km*S) at h1
      change _ ≤ (Kp*S)*(Km*D) at h2
      change _ ≤ (Kp*D)*(Km*D) at h3
      nlinarith only [h1, h2, h3]
    _ ≤ (6*Real.exp (2*q)*thetaCuspSourceTerm x 1^2)*(2*S*D+D^2) :=
      mul_le_mul_of_nonneg_right hK hb
    _ = thetaCuspSourceTerm x 1^2*Real.exp (2*q)*(6*(2*S*D+D^2)) := by ring
    _ ≤ thetaCuspSourceTerm x 1^2*Real.exp (2*q)*(1000*Real.exp (-10*a)) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ = 1000*thetaCuspSourceTerm x 1^2*Real.exp (-(27/5)*q) := by
      have he : Real.exp (2*q)*Real.exp (-10*a)=Real.exp (-(27/5)*q) := by
        rw [← Real.exp_add]; congr 1; dsimp [a]; ring
      calc
        _ = 1000*thetaCuspSourceTerm x 1^2*(Real.exp (2*q)*Real.exp (-10*a)) := by ring
        _ = _ := by rw [he]
    _ ≤ 1000*thetaCuspSourceTerm x 1^2*Real.exp (-27) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by dsimp [q]; linarith)) (by positivity)
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left exp_twenty_seven_inverse
        (show 0 ≤ 1000*thetaCuspSourceTerm x 1^2 by positivity)
      nlinarith only [hm]

private theorem reflected_analytic {x : ℝ} {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    AnalyticAt ℂ (complexReflectedError x) z := by
  have hp : (x:ℂ)+z ∈ thetaCuspStrip := by
    simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im,
      Complex.ofReal_im, zero_add] using hz
  have hm : (x:ℂ)-z ∈ thetaCuspStrip := by
    simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.sub_im,
      Complex.ofReal_im, zero_sub, abs_neg] using hz
  have htwo : Differentiable ℂ twoComplex :=
    (differentiable_thetaCuspComplexTerm 1).add (differentiable_thetaCuspComplexTerm 2)
  exact (((analyticOnNhd_thetaCuspStripSource _ hp).comp
      (analyticAt_const.add analyticAt_id)).mul
    ((analyticOnNhd_thetaCuspStripSource _ hm).comp
      (analyticAt_const.sub analyticAt_id))).sub
    (((htwo.analyticAt _).comp (analyticAt_const.add analyticAt_id)).mul
      ((htwo.analyticAt _).comp (analyticAt_const.sub analyticAt_id)))

private theorem complex_jet_bound (n : ℕ) {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    ‖iteratedDeriv n (complexReflectedError x) 0‖ ≤
      (n.factorial:ℝ)*(thetaCuspSourceTerm x 1^2/500000000)/(3/20)^n := by
  have hd : DifferentiableOn ℂ (complexReflectedError x) thetaCuspStrip :=
    fun z hz => (reflected_analytic hz).differentiableAt.differentiableWithinAt
  have hdisc : Metric.closedBall (0:ℂ) (3/20) ⊆ thetaCuspStrip := by
    intro z hz
    have hn : ‖z‖ ≤ 3/20 := by simpa using hz
    simpa using shifted_mem_strip 0 hn
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
    (hd.diffContOnCl_ball hdisc) (fun z hz =>
      complex_reflected_error_bound hq (by
        have he : ‖z‖ = 3/20 := by simpa using hz
        exact he.le))

private theorem restriction_jet {H : ℂ → ℂ}
    (ha : ∀ t : ℝ, AnalyticAt ℂ H (t:ℂ)) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun s : ℝ => H (s:ℂ)) t=iteratedDeriv n H (t:ℂ) := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih =>
    have he : deriv (fun s : ℝ => H (s:ℂ))=fun s : ℝ => deriv H (s:ℂ) :=
      funext fun s => ((ha s).differentiableAt.hasDerivAt.comp_ofReal).deriv
    rw [iteratedDeriv_succ', iteratedDeriv_succ', he]
    exact ih (fun s => (ha s).deriv)

private theorem real_reflected_jet (n : ℕ) (x : ℝ) :
    iteratedDeriv n (complexReflectedError x) 0=
      ((thetaCuspNativeReflectionJet n x-thetaCuspTwoAtomReflectionJet n x:ℝ):ℂ) := by
  let F : ℝ → ℝ := fun t => thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)
  let T : ℝ → ℝ := fun t => thetaCuspTwoAtomSource (x+t)*thetaCuspTwoAtomSource (x-t)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (contDiff_thetaCuspFullSource.comp (contDiff_const.add contDiff_id)).mul
      (contDiff_thetaCuspFullSource.comp (contDiff_const.sub contDiff_id))
  have hT : ContDiff ℝ (⊤ : ℕ∞) T :=
    (contDiff_thetaCuspTwoAtomSource.comp (contDiff_const.add contDiff_id)).mul
      (contDiff_thetaCuspTwoAtomSource.comp (contDiff_const.sub contDiff_id))
  have he : (fun t : ℝ => complexReflectedError x (t:ℂ))=fun t : ℝ => ((F t-T t:ℝ):ℂ) := by
    funext t
    simp only [complexReflectedError, ← Complex.ofReal_add, ← Complex.ofReal_sub,
      thetaCuspStripSource_ofReal, twoComplex, thetaCuspComplexTerm_ofReal,
      F, T, thetaCuspTwoAtomSource]
    push_cast
    rfl
  have ha (t : ℝ) : AnalyticAt ℂ (complexReflectedError x) (t:ℂ) :=
    reflected_analytic (by simp [thetaCuspStrip, Real.pi_pos])
  have hr := restriction_jet ha n 0
  rw [he, SchwartzMap.iteratedDeriv_ofReal _ (hF.sub hT)] at hr
  have hFn : ContDiffAt ℝ n F 0 := hF.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  have hTn : ContDiffAt ℝ n T 0 := hT.contDiffAt.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  rw [iteratedDeriv_fun_sub hFn hTn] at hr
  exact hr.symm

/-- All-order real jet error obtained from the complete complex reflected source. -/
theorem native_twoAtom_cauchy_error (n : ℕ) {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeReflectionJet n x-thetaCuspTwoAtomReflectionJet n x| ≤
      (n.factorial:ℝ)*(thetaCuspSourceTerm x 1^2/500000000)/(3/20)^n := by
  have h := complex_jet_bound n hq
  rw [real_reflected_jet, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end
end RHTower.ThetaCuspReflectedCauchyTail
