import GaloisForLFunctions.ThetaCuspSections.FifthEvenThreeAtomRemainder
import GaloisForLFunctions.ThetaCuspSections.FifthEvenNativeRay
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomReflectedApproximation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomGaussianJetLimits
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Cauchy control of the reflected theta tail beyond four atoms

The omitted source begins at atom five. On the complex disk of radius `3/20`,
its Gaussian majorant is `626 exp(-25a)` with `a=37q/50`. Opposite translations
cancel their prefactors. The reflected remainder is bounded by
`20000 f₁² exp(-431q/25)` for `q≥3`, yielding every real jet by Cauchy's estimate.
In normalized Gaussian coordinates, each tail entry is at most `1/100000`.
Retaining the first pure atom and all six unequal pairs leaves quadratic error
at most `1/20000`; the other three pure atoms are positive semidefinite.
-/

open Complex Real RHTower
namespace GaloisForLFunctions.ThetaCuspSections.FourAtomCauchyTail
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

private theorem complex_atom_bound {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
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

private theorem exp_neg_le_four_hundred {t : ℝ} (ht : 6 ≤ t) :
    Real.exp (-t) ≤ 1/400 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 2
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hh := hp.trans (Real.exp_le_exp.mpr ht)
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hh

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

private theorem quartic_deep (k : ℕ) : ((k+5:ℕ):ℝ)^4 ≤ 625*3^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hs : ((k:ℝ)+6)^4 ≤ 3*((k:ℝ)+5)^4 := by
        have hp := pow_le_pow_left₀
          (show (0:ℝ) ≤ (k:ℝ)+6 by positivity)
          (show (k:ℝ)+6 ≤ (6/5)*((k:ℝ)+5) by
            linarith only [Nat.cast_nonneg (α := ℝ) k]) 4
        nlinarith only [hp, pow_nonneg (show (0:ℝ) ≤ (k:ℝ)+5 by positivity) 4]
      push_cast at ih ⊢
      rw [pow_succ (3:ℝ) k]
      nlinarith only [hs, ih]

private theorem gaussian_head_term {a : ℝ} (ha : 2 ≤ a) (k : ℕ) :
    ((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2) ≤
      Real.exp (-a)*(1/25)^k := by
  have ha0 : 0 ≤ a := by linarith
  have hk2 : (k:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by norm_num : 2≠0) k
  have hgap : 1+3*(k:ℝ) ≤ ((k+1:ℕ):ℝ)^2 := by push_cast; nlinarith
  have he : Real.exp (-a*((k+1:ℕ):ℝ)^2) ≤ Real.exp (-a)*Real.exp (-(3*a))^k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr hgap)]
  have hc := exp_neg_le_four_hundred (t := 3*a) (by linarith)
  calc
    _ ≤ 16^k*(Real.exp (-a)*Real.exp (-(3*a))^k) :=
      mul_le_mul (quartic_head k) he (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-a)*(16*Real.exp (-(3*a)))^k := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hc]) k) (Real.exp_pos _).le

private theorem gaussian_deep_term {a : ℝ} (ha : 2 ≤ a) (k : ℕ) :
    ((k+5:ℕ):ℝ)^4*Real.exp (-a*((k+5:ℕ):ℝ)^2) ≤
      625*Real.exp (-25*a)*(1/1000)^k := by
  have ha0 : 0 ≤ a := by linarith
  have hk2 : (k:ℝ) ≤ (k:ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by norm_num : 2≠0) k
  have hgap : 25+10*(k:ℝ) ≤ ((k+5:ℕ):ℝ)^2 := by push_cast; nlinarith
  have he : Real.exp (-a*((k+5:ℕ):ℝ)^2) ≤ Real.exp (-25*a)*Real.exp (-(10*a))^k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg ha0 (sub_nonneg.mpr hgap)]
  have hc := exp_neg_le_eight_thousand (t := 10*a) (by linarith)
  calc
    _ ≤ (625*3^k)*(Real.exp (-25*a)*Real.exp (-(10*a))^k) :=
      mul_le_mul (quartic_deep k) he (Real.exp_pos _).le (by positivity)
    _ = 625*Real.exp (-25*a)*(3*Real.exp (-(10*a)))^k := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hc]) k) (by positivity)

private theorem gaussian_head_sum {a : ℝ} (ha : 2 ≤ a) :
    (∑' k : ℕ, ((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2)) ≤
      (105/100)*Real.exp (-a) := by
  have hm : Summable (fun k : ℕ => Real.exp (-a)*(1/25)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/25) (by norm_num)).mul_left _
  have hs := Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_head_term ha) hm
  have h := hs.tsum_le_tsum (gaussian_head_term ha) hm
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/25) (by norm_num)] at h
  nlinarith only [h, (Real.exp_pos (-a)).le]

private theorem gaussian_deep_sum {a : ℝ} (ha : 2 ≤ a) :
    (∑' k : ℕ, ((k+5:ℕ):ℝ)^4*Real.exp (-a*((k+5:ℕ):ℝ)^2)) ≤
      626*Real.exp (-25*a) := by
  have hm : Summable (fun k : ℕ => 625*Real.exp (-25*a)*(1/1000)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/1000) (by norm_num)).mul_left _
  have hs := Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_deep_term ha) hm
  have h := hs.tsum_le_tsum (gaussian_deep_term ha) hm
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/1000) (by norm_num)] at h
  nlinarith only [h, (Real.exp_pos (-25*a)).le]

private theorem shifted_mem_strip (x : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    (x:ℂ)+z ∈ thetaCuspStrip := by
  have hi := (Complex.abs_im_le_norm z).trans hz
  simp only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, zero_add]
  linarith [Real.pi_gt_three]

/-- The first four complex source atoms. -/
noncomputable def fourComplex (z : ℂ) : ℂ :=
  thetaCuspComplexTerm z 1+thetaCuspComplexTerm z 2+thetaCuspComplexTerm z 3+
    thetaCuspComplexTerm z 4

private noncomputable def deepComplex (z : ℂ) : ℂ :=
  thetaCuspStripSource z-fourComplex z

private theorem deep_eq_tsum {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    deepComplex z=∑' k : ℕ, thetaCuspComplexTerm z (k+5) := by
  have hs := summable_thetaCuspComplexTerm hz
  unfold deepComplex fourComplex thetaCuspStripSource
  rw [← hs.sum_add_tsum_nat_add 5]
  norm_num [Finset.sum_range_succ, thetaCuspComplexTerm_zero]

private theorem full_complex_bound {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    ‖thetaCuspStripSource ((x:ℂ)+z)‖ ≤ atomPrefactor x z.re*
      ((105/100)*Real.exp (-((37/50)*thetaCuspSingleAtomReflectionScale 1 x))) := by
  let a := (37/50)*thetaCuspSingleAtomReflectionScale 1 x
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hK : 0 ≤ atomPrefactor x z.re := by unfold atomPrefactor; positivity
  have hs := summable_thetaCuspComplexTerm (shifted_mem_strip x hz)
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hg : Summable (fun k : ℕ => ((k+1:ℕ):ℝ)^4*Real.exp (-a*((k+1:ℕ):ℝ)^2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_head_term ha)
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/25) (by norm_num)).mul_left _)
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

private theorem deep_complex_bound {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    ‖deepComplex ((x:ℂ)+z)‖ ≤ atomPrefactor x z.re*
      (626*Real.exp (-25*((37/50)*thetaCuspSingleAtomReflectionScale 1 x))) := by
  let a := (37/50)*thetaCuspSingleAtomReflectionScale 1 x
  have ha : 2 ≤ a := by dsimp [a]; linarith
  have hK : 0 ≤ atomPrefactor x z.re := by unfold atomPrefactor; positivity
  have hs := summable_thetaCuspComplexTerm (shifted_mem_strip x hz)
  have hs5 := (summable_nat_add_iff 5).mpr hs
  have hg : Summable (fun k : ℕ => ((k+5:ℕ):ℝ)^4*Real.exp (-a*((k+5:ℕ):ℝ)^2)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (gaussian_deep_term ha)
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/1000) (by norm_num)).mul_left _)
  rw [deep_eq_tsum (shifted_mem_strip x hz)]
  calc
    _ ≤ ∑' k : ℕ, ‖thetaCuspComplexTerm ((x:ℂ)+z) (k+5)‖ := norm_tsum_le_tsum_norm hs5.norm
    _ ≤ ∑' k : ℕ, atomPrefactor x z.re*
        (((k+5:ℕ):ℝ)^4*Real.exp (-a*((k+5:ℕ):ℝ)^2)) :=
      hs5.norm.tsum_le_tsum (fun k => by simpa only [a, neg_mul] using complex_atom_bound hq hz (k+5)) (hg.mul_left _)
    _ = atomPrefactor x z.re*(∑' k : ℕ, ((k+5:ℕ):ℝ)^4*Real.exp (-a*((k+5:ℕ):ℝ)^2)) :=
      tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_deep_sum ha) hK

private theorem prefactor_product_bound {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (u : ℝ) :
    atomPrefactor x u*atomPrefactor x (-u) ≤
      14*Real.exp (2*thetaCuspSingleAtomReflectionScale 1 x)*thetaCuspSourceTerm x 1^2 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq3 : 3 ≤ q := hq
  have hpoly : (2*q*(50/37)+3)^2 ≤ 14*(2*q-3)^2 := by
    nlinarith only [hq3, sq_nonneg (q-3)]
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
  change _ ≤ 14*Real.exp (2*q)*thetaCuspSourceTerm x 1^2
  rw [mul_assoc 14, hf]
  nlinarith only [hm]

private theorem reflected_gaussian_bound {a : ℝ} (ha : 2 ≤ a) :
    14*(2*((105/100)*Real.exp (-a))*(626*Real.exp (-25*a))+
      (626*Real.exp (-25*a))^2) ≤ 20000*Real.exp (-26*a) := by
  have hc := exp_neg_le_eight_thousand (t := 24*a) (by linarith)
  have h26 : Real.exp (-a)*Real.exp (-25*a)=Real.exp (-26*a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h50 : Real.exp (-25*a)^2=Real.exp (-26*a)*Real.exp (-24*a) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have he : 14*(2*((105/100)*Real.exp (-a))*(626*Real.exp (-25*a))+
      (626*Real.exp (-25*a))^2) =
      (14*2*(105/100)*626)*Real.exp (-26*a)+14*626^2*Real.exp (-26*a)*Real.exp (-24*a) := by
    calc
      _ = (14*2*(105/100)*626)*(Real.exp (-a)*Real.exp (-25*a))+14*626^2*Real.exp (-25*a)^2 := by ring
      _ = _ := by rw [h26, h50]; ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 14*626^2*Real.exp (-26*a) by positivity)
  simp only [neg_mul] at hm ⊢
  nlinarith only [hm, (Real.exp_pos (-(26*a))).le]

/-- Complete reflected source minus the first-four-atom reflection product. -/
noncomputable def complexReflectedError (x : ℝ) (z : ℂ) : ℂ :=
  thetaCuspStripSource ((x:ℂ)+z)*thetaCuspStripSource ((x:ℂ)-z)-
    fourComplex ((x:ℂ)+z)*fourComplex ((x:ℂ)-z)

/-- Uniform disk bound beyond four atoms on the ray `q ≥ 3`. -/
theorem complex_reflected_error_bound {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) {z : ℂ} (hz : ‖z‖ ≤ 3/20) :
    ‖complexReflectedError x z‖ ≤
      20000*thetaCuspSourceTerm x 1^2*Real.exp (-(431/25)*thetaCuspSingleAtomReflectionScale 1 x) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let a := (37/50)*q
  let Kp := atomPrefactor x z.re
  let Km := atomPrefactor x (-z.re)
  let S := (105/100)*Real.exp (-a)
  let D := 626*Real.exp (-25*a)
  have ha : 2 ≤ a := by dsimp [a, q]; linarith
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
    _ ≤ (14*Real.exp (2*q)*thetaCuspSourceTerm x 1^2)*(2*S*D+D^2) :=
      mul_le_mul_of_nonneg_right hK hb
    _ = thetaCuspSourceTerm x 1^2*Real.exp (2*q)*(14*(2*S*D+D^2)) := by ring
    _ ≤ thetaCuspSourceTerm x 1^2*Real.exp (2*q)*(20000*Real.exp (-26*a)) :=
      mul_le_mul_of_nonneg_left hG (by positivity)
    _ = 20000*thetaCuspSourceTerm x 1^2*Real.exp (-(431/25)*q) := by
      have he : Real.exp (2*q)*Real.exp (-26*a)=Real.exp (-(431/25)*q) := by
        rw [← Real.exp_add]; congr 1; dsimp [a]; ring
      calc
        _ = 20000*thetaCuspSourceTerm x 1^2*(Real.exp (2*q)*Real.exp (-26*a)) := by ring
        _ = _ := by rw [he]

private theorem reflected_analytic {x : ℝ} {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    AnalyticAt ℂ (complexReflectedError x) z := by
  have hp : (x:ℂ)+z ∈ thetaCuspStrip := by
    simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.add_im,
      Complex.ofReal_im, zero_add] using hz
  have hm : (x:ℂ)-z ∈ thetaCuspStrip := by
    simpa only [thetaCuspStrip, Set.mem_setOf_eq, Complex.sub_im,
      Complex.ofReal_im, zero_sub, abs_neg] using hz
  have hfour : Differentiable ℂ fourComplex :=
    (((differentiable_thetaCuspComplexTerm 1).add (differentiable_thetaCuspComplexTerm 2)).add
      (differentiable_thetaCuspComplexTerm 3)).add (differentiable_thetaCuspComplexTerm 4)
  exact (((analyticOnNhd_thetaCuspStripSource _ hp).comp
      (analyticAt_const.add analyticAt_id)).mul
    ((analyticOnNhd_thetaCuspStripSource _ hm).comp
      (analyticAt_const.sub analyticAt_id))).sub
    (((hfour.analyticAt _).comp (analyticAt_const.add analyticAt_id)).mul
      ((hfour.analyticAt _).comp (analyticAt_const.sub analyticAt_id)))

private theorem complex_jet_bound (n : ℕ) {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    ‖iteratedDeriv n (complexReflectedError x) 0‖ ≤
      (n.factorial:ℝ)*(20000*thetaCuspSourceTerm x 1^2*
        Real.exp (-(431/25)*thetaCuspSingleAtomReflectionScale 1 x))/(3/20)^n := by
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

/-- The first four real source atoms. -/
def thetaCuspFourAtomSource (x : ℝ) : ℝ :=
  thetaCuspSourceTerm x 1+thetaCuspSourceTerm x 2+thetaCuspSourceTerm x 3+
    thetaCuspSourceTerm x 4

theorem contDiff_thetaCuspFourAtomSource : ContDiff ℝ (⊤ : ℕ∞) thetaCuspFourAtomSource :=
  (((contDiff_thetaCuspSourceAtom 1).add (contDiff_thetaCuspSourceAtom 2)).add
    (contDiff_thetaCuspSourceAtom 3)).add (contDiff_thetaCuspSourceAtom 4)

/-- Reflected jet of the first four source atoms. -/
def thetaCuspFourAtomReflectionJet (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n (fun t => thetaCuspFourAtomSource (x+t)*thetaCuspFourAtomSource (x-t)) 0

private theorem real_reflected_jet (n : ℕ) (x : ℝ) :
    iteratedDeriv n (complexReflectedError x) 0=
      ((thetaCuspNativeReflectionJet n x-thetaCuspFourAtomReflectionJet n x:ℝ):ℂ) := by
  let F : ℝ → ℝ := fun t => thetaCuspFullSource (x+t)*thetaCuspFullSource (x-t)
  let T : ℝ → ℝ := fun t => thetaCuspFourAtomSource (x+t)*thetaCuspFourAtomSource (x-t)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (contDiff_thetaCuspFullSource.comp (contDiff_const.add contDiff_id)).mul
      (contDiff_thetaCuspFullSource.comp (contDiff_const.sub contDiff_id))
  have hT : ContDiff ℝ (⊤ : ℕ∞) T :=
    (contDiff_thetaCuspFourAtomSource.comp (contDiff_const.add contDiff_id)).mul
      (contDiff_thetaCuspFourAtomSource.comp (contDiff_const.sub contDiff_id))
  have he : (fun t : ℝ => complexReflectedError x (t:ℂ))=fun t : ℝ => ((F t-T t:ℝ):ℂ) := by
    funext t
    simp only [complexReflectedError, ← Complex.ofReal_add, ← Complex.ofReal_sub,
      thetaCuspStripSource_ofReal, fourComplex, thetaCuspComplexTerm_ofReal,
      F, T, thetaCuspFourAtomSource]
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

/-- **The reflected tail beyond four atoms.** Every real reflected jet of the complete source
differs from the four-atom jet by a Cauchy majorant decaying like `e^{-(431/25) q}`. -/
theorem native_fourAtom_cauchy_error (n : ℕ) {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeReflectionJet n x-thetaCuspFourAtomReflectionJet n x| ≤
      (n.factorial:ℝ)*(20000*thetaCuspSourceTerm x 1^2*
        Real.exp (-(431/25)*thetaCuspSingleAtomReflectionScale 1 x))/(3/20)^n := by
  have h := complex_jet_bound n hq
  rw [real_reflected_jet, Complex.norm_real, Real.norm_eq_abs] at h
  exact h


open FifthLeadingPair FifthRemainder

/-- The reflected tail after retaining four atoms, in fifth Gaussian coordinates. -/
def fourTailGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j => (-1 : ℝ)^(i.val+j.val)*
    (thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
      thetaCuspFourAtomReflectionJet (2*(i.val+j.val)) x)/
        (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^(i.val+j.val)))

private theorem exp_neg_three_multiple (n : ℕ) {t : ℝ} (ht : (n : ℝ)*3 ≤ t) :
    Real.exp (-t) ≤ 1/(20 : ℝ)^n := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) exp_three_lower n
  rw [← Real.exp_nat_mul] at hp
  have hh := hp.trans (Real.exp_le_exp.mpr ht)
  rw [Real.exp_neg,inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) hh

private theorem quadratic_ray_bound_three {q c : ℝ} (hq : 3 ≤ q) (hc : 2/3 ≤ c) :
    q^2*Real.exp (-c*q) ≤ 9*Real.exp (-3*c) := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hp : q^2*Real.exp (-((2/3)*q)) ≤ 9*Real.exp (-2) := by
    have h := _root_.RHTower.pow_mul_exp_neg_le_stationary_radius 2
      (a := 3) (t := q) (by norm_num) hq0
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have he : Real.exp (-(c-2/3)*q) ≤ Real.exp (-(c-2/3)*3) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hq)]
  calc
    _ = (q^2*Real.exp (-((2/3)*q)))*Real.exp (-(c-2/3)*q) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ (9*Real.exp (-2))*Real.exp (-(c-2/3)*3) :=
      mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

private def tailWeight (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, |gaussianBasis i u| * |gaussianBasis j v| *
    (((2*(u.val+v.val)).factorial : ℝ)*(400/27)^(u.val+v.val)*(20000*36)/20^17)
private theorem tailWeight_symm (i j : Fin 5) : tailWeight i j=tailWeight j i := by
  unfold tailWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Nat.add_comm u.val v.val]
  ring
private theorem tail_bound_0_0 : tailWeight 0 0 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_1 : tailWeight 0 1 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_2 : tailWeight 0 2 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_3 : tailWeight 0 3 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_4 : tailWeight 0 4 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_1 : tailWeight 1 1 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_2 : tailWeight 1 2 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_3 : tailWeight 1 3 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_4 : tailWeight 1 4 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_2_2 : tailWeight 2 2 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_2_3 : tailWeight 2 3 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_2_4 : tailWeight 2 4 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_3_3 : tailWeight 3 3 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_3_4 : tailWeight 3 4 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_4_4 : tailWeight 4 4 ≤ 1/100000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_basis_bound (i j : Fin 5) : tailWeight i j ≤ 1/100000 := by
  fin_cases i <;> fin_cases j
  · exact tail_bound_0_0
  · exact tail_bound_0_1
  · exact tail_bound_0_2
  · exact tail_bound_0_3
  · exact tail_bound_0_4
  · rw [tailWeight_symm]; exact tail_bound_0_1
  · exact tail_bound_1_1
  · exact tail_bound_1_2
  · exact tail_bound_1_3
  · exact tail_bound_1_4
  · rw [tailWeight_symm]; exact tail_bound_0_2
  · rw [tailWeight_symm]; exact tail_bound_1_2
  · exact tail_bound_2_2
  · exact tail_bound_2_3
  · exact tail_bound_2_4
  · rw [tailWeight_symm]; exact tail_bound_0_3
  · rw [tailWeight_symm]; exact tail_bound_1_3
  · rw [tailWeight_symm]; exact tail_bound_2_3
  · exact tail_bound_3_3
  · exact tail_bound_3_4
  · rw [tailWeight_symm]; exact tail_bound_0_4
  · rw [tailWeight_symm]; exact tail_bound_1_4
  · rw [tailWeight_symm]; exact tail_bound_2_4
  · rw [tailWeight_symm]; exact tail_bound_3_4
  · exact tail_bound_4_4
private theorem weighted_first_mass_bound {q : ℝ} (hq : 3 ≤ q) :
    (2*q-3)^2*Real.exp (-(431/25)*q) ≤ 36/(20 : ℝ)^17 := by
  have hp : (2*q-3)^2 ≤ 4*q^2 := by nlinarith only [hq]
  have hf := quadratic_ray_bound_three hq (by norm_num : (2/3 : ℝ) ≤ 431/25)
  have he : Real.exp (-3*(431/25 : ℝ)) ≤ 1/(20 : ℝ)^17 := by
    simpa only [neg_mul] using exp_neg_three_multiple 17
      (t := 3*(431/25)) (by norm_num)
  calc
    _ ≤ 4*(q^2*Real.exp (-(431/25)*q)) := by
      nlinarith only [mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(431/25)*q)).le]
    _ ≤ 36*Real.exp (-3*(431/25)) := by nlinarith only [hf]
    _ ≤ _ := by nlinarith only [he]
private theorem normalized_tail_moment_bound {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : ℕ) :
    |(-1 : ℝ)^k*(thetaCuspNativeReflectionJet (2*k) x-
      thetaCuspFourAtomReflectionJet (2*k) x)/
      (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^k)| ≤
    ((2*k).factorial : ℝ)*(400/27)^k*(20000*36)/(20 : ℝ)^17 := by
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 < q := by linarith only [hq]
  have hK : 0 < sourceUnit x := by
    change 0 < 4*q^2*Real.exp (x-2*q)
    positivity
  have hD : 0 < sourceUnit x*q^k := mul_pos hK (pow_pos hq0 _)
  have hmass := _root_.RHTower.ThetaCuspOddFourCentralBound.sourceTerm_one_sq x
  change thetaCuspSourceTerm x 1^2=sourceUnit x*(2*q-3)^2 at hmass
  have ht := native_fourAtom_cauchy_error (2*k)
    (show 3 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])
  have hb := weighted_first_mass_bound hq
  have hden : (27/400 : ℝ)^k ≤ (3/20 : ℝ)^(2*k)*q^k := by
    rw [pow_mul (3/20 : ℝ) 2 k,← mul_pow]
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
    linarith only [hq]
  have hn : 0 ≤ ((2*k).factorial : ℝ)*20000*(36/(20 : ℝ)^17) := by positivity
  calc
    _ = |thetaCuspNativeReflectionJet (2*k) x-thetaCuspFourAtomReflectionJet (2*k) x|/
        (sourceUnit x*q^k) := by
      rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_pos hD]
    _ ≤ (((2*k).factorial : ℝ)*(20000*thetaCuspSourceTerm x 1^2*
        Real.exp (-(431/25)*q))/(3/20)^(2*k))/(sourceUnit x*q^k) :=
      div_le_div_of_nonneg_right ht hD.le
    _ = (((2*k).factorial : ℝ)*20000*((2*q-3)^2*Real.exp (-(431/25)*q)))/
        ((3/20)^(2*k)*q^k) := by
      rw [hmass]
      field_simp [hK.ne', hq0.ne']
    _ ≤ (((2*k).factorial : ℝ)*20000*(36/(20 : ℝ)^17))/
        ((3/20)^(2*k)*q^k) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (((2*k).factorial : ℝ)*20000*(36/(20 : ℝ)^17))/(27/400 : ℝ)^k :=
      div_le_div_of_nonneg_left hn (by positivity) hden
    _ = _ := by
      rw [div_eq_mul_inv,← inv_pow]
      norm_num
      ring
/-- The entire reflected tail beyond four atoms fits a uniform entry reserve on the scale-three ray. -/
theorem fourTailGram_bound {x : ℝ} (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (i j : Fin 5) : |fourTailGram x i j| ≤ 1/100000 := by
  have h := gaussian_entry_majorant
    (fun u v => (-1 : ℝ)^(u.val+v.val)*
      (thetaCuspNativeReflectionJet (2*(u.val+v.val)) x-
        thetaCuspFourAtomReflectionJet (2*(u.val+v.val)) x)/
          (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^(u.val+v.val)))
    (fun k => ((2*k).factorial : ℝ)*(400/27)^k*(20000*36)/(20 : ℝ)^17)
    (fun u v => normalized_tail_moment_bound hq (u.val+v.val)) i j
  exact h.trans (tail_basis_bound i j)



open Matrix FifthNativeRay _root_.RHTower.ThetaCuspGaussianLimit

/-- The retained four-atom reflection product in normalized Gaussian coordinates. -/
def fourHeadGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j => (-1 : ℝ)^(i.val+j.val)*
    thetaCuspFourAtomReflectionJet (2*(i.val+j.val)) x/
      (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^(i.val+j.val)))

/-- Retaining four atoms splits the complete matrix exactly into its head and tail. -/
theorem sourceGram_fourAtom_decomposition (x : ℝ) :
    sourceGram x = fourHeadGram x+fourTailGram x := by
  unfold sourceGram normalizedGram fourHeadGram fourTailGram
  rw [← gaussianGram_add]
  congr 1
  ext i j
  simp only [nativeShiftedMatrix,Matrix.add_apply,add_zero]
  ring

/-- Four atoms retain the complete quadratic form up to a uniform error from scale three. -/
theorem sourceGram_fourAtom_lower {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (fourHeadGram x *ᵥ v)-(1/20000 : ℝ)*(∑ i, v i^2) ≤
      v ⬝ᵥ (sourceGram x *ᵥ v) := by
  have hr := neg_le_of_abs_le (_root_.RHTower.abs_dotProduct_mulVec_le
    (fourTailGram x) (by norm_num : (0 : ℝ) ≤ 1/100000)
    (fourTailGram_bound hq) v)
  norm_num only [Fintype.card_fin,Nat.cast_ofNat] at hr
  rw [sourceGram_fourAtom_decomposition]
  simp only [Matrix.add_mulVec,dotProduct_add]
  linarith only [hr]



open _root_.HTGeometry.SignedPoisson
open _root_.RHTower.ThetaCuspOddFourThreeAtom

private theorem fourAtomSource_eq_sum (y : ℝ) :
    thetaCuspFourAtomSource y = ∑ a ∈ Finset.range 4, thetaCuspSourceTerm y (a+1) := by
  simp [thetaCuspFourAtomSource,Finset.sum_range_succ]

/-- The retained reflected jet contains all sixteen ordered pairs. -/
theorem fourAtomJet_eq_sum (n : ℕ) (x : ℝ) :
    thetaCuspFourAtomReflectionJet n x =
      ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
        thetaCuspAtomPairReflectionJet n (a+1) (b+1) x := by
  have hf : (fun t => thetaCuspFourAtomSource (x+t)*thetaCuspFourAtomSource (x-t)) =
      fun t => ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
        thetaCuspSourceTerm (x+t) (a+1)*thetaCuspSourceTerm (x-t) (b+1) := by
    funext t
    rw [fourAtomSource_eq_sum,fourAtomSource_eq_sum,Finset.sum_mul_sum]
  have hsm (a b : ℕ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun t => thetaCuspSourceTerm (x+t) (a+1)*thetaCuspSourceTerm (x-t) (b+1)) :=
    ((contDiff_thetaCuspSourceAtom (a+1)).comp (contDiff_const.add contDiff_id)).mul
      ((contDiff_thetaCuspSourceAtom (b+1)).comp (contDiff_const.sub contDiff_id))
  unfold thetaCuspFourAtomReflectionJet
  rw [hf,iteratedDeriv_fun_sum (fun a _ => (ContDiff.sum fun b _ => hsm a b).contDiffAt.of_le
    (by exact_mod_cast le_top))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [iteratedDeriv_fun_sum (fun b _ => (hsm a b).contDiffAt.of_le (by exact_mod_cast le_top))]
  rfl

/-- The first pure atom and all six unordered unequal pairs in first-pair units. -/
def fourRetainedMoment (q : ℝ) (k : ℕ) : ℝ :=
  (thetaPairRadialEvenPolynomial (q^2) k).eval (2*q)+
    8*Real.exp (-3*q)*(thetaPairRadialEvenPolynomial (4*q^2) k).eval (5*q)+
    18*Real.exp (-8*q)*(thetaPairRadialEvenPolynomial (9*q^2) k).eval (10*q)+
    32*Real.exp (-15*q)*(thetaPairRadialEvenPolynomial (16*q^2) k).eval (17*q)+
    72*Real.exp (-11*q)*(thetaPairRadialEvenPolynomial (36*q^2) k).eval (13*q)+
    128*Real.exp (-18*q)*(thetaPairRadialEvenPolynomial (64*q^2) k).eval (20*q)+
    288*Real.exp (-23*q)*(thetaPairRadialEvenPolynomial (144*q^2) k).eval (25*q)

private theorem signed_fourAtom_decomposition (k : ℕ) (x : ℝ) :
    (-1 : ℝ)^k*thetaCuspFourAtomReflectionJet (2*k) x =
      sourceUnit x*fourRetainedMoment (thetaCuspSingleAtomReflectionScale 1 x) k+
      ((-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 2 2 x+
        (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 3 3 x+
        (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) 4 4 x) := by
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hpair (a b : ℕ) : (-1 : ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b x =
      sourceUnit x*((a : ℝ)^2*(b : ℝ)^2*Real.exp (-(((a : ℝ)^2+(b : ℝ)^2)-2)*q)*
        (thetaPairRadialEvenPolynomial ((a : ℝ)^2*(b : ℝ)^2*q^2) k).eval
          (((a : ℝ)^2+(b : ℝ)^2)*q)) := by
    rw [signed_pair_even]
    have he : Real.exp (x-((a : ℝ)^2+(b : ℝ)^2)*q) =
        Real.exp (x-2*q)*Real.exp (-(((a : ℝ)^2+(b : ℝ)^2)-2)*q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    change _ = (4*q^2*Real.exp (x-2*q))*_
    ring
  rw [fourAtomJet_eq_sum]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  have p11 := hpair 1 1
  have p12 := hpair 1 2
  have p13 := hpair 1 3
  have p14 := hpair 1 4
  have p21 := hpair 2 1
  have p23 := hpair 2 3
  have p24 := hpair 2 4
  have p31 := hpair 3 1
  have p32 := hpair 3 2
  have p34 := hpair 3 4
  have p41 := hpair 4 1
  have p42 := hpair 4 2
  have p43 := hpair 4 3
  norm_num at p11 p12 p13 p14 p21 p23 p24 p31 p32 p34 p41 p42 p43
  unfold fourRetainedMoment
  norm_num
  linear_combination p11+p12+p13+p14+p21+p23+p24+p31+p32+p34+p41+p42+p43

/-- Gaussian form of the first pure atom and all six retained unequal pairs. -/
def fourRetainedGram (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j => fourRetainedMoment q (i.val+j.val)/q^(i.val+j.val))

private theorem fourHeadGram_decomposition {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    fourHeadGram x = fourRetainedGram (thetaCuspSingleAtomReflectionScale 1 x)+
      pureGram 2 x+pureGram 3 x+pureGram 4 x := by
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hK : 0 < sourceUnit x := by unfold sourceUnit; positivity
  unfold fourHeadGram fourRetainedGram pureGram normalizedGram
  repeat rw [← gaussianGram_add]
  congr 1
  ext i j
  have ht := signed_fourAtom_decomposition (i.val+j.val) x
  simp only [Matrix.add_apply,pureMatrix]
  field_simp [hK.ne',hq0.ne'] at ht ⊢
  linear_combination ht

private theorem pureGram_posSemidef_from_three {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) {n : ℕ} (hn : 2 ≤ n) :
    (pureGram n x).PosSemidef := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (4 : ℝ) ≤ (n : ℝ)^2 := by
    nlinarith only [hnR,sq_nonneg ((n : ℝ)-2)]
  have hp := mul_le_mul hs hq (by norm_num : (0 : ℝ) ≤ 3) (sq_nonneg (n : ℝ))
  have hscale : 5 ≤ thetaCuspSingleAtomReflectionScale n x := by
    rw [scale_atom]
    linarith only [hp]
  have hq0 : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hq]
  have hK : 0 < sourceUnit x := by unfold sourceUnit; positivity
  unfold pureGram
  rw [normalizedGram_eq_congruence]
  exact ((FifthFirstAtom.atom_even_five_posDef hscale).posSemidef.conjTranspose_mul_mul_same _).smul
    (by positivity)

/-- The complete source retains every unequal pair among four atoms with a small uniform error. -/
theorem sourceGram_fourRetained_lower {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (fourRetainedGram (thetaCuspSingleAtomReflectionScale 1 x) *ᵥ v)-
      (1/20000 : ℝ)*(∑ i, v i^2) ≤ v ⬝ᵥ (sourceGram x *ᵥ v) := by
  have hr := sourceGram_fourAtom_lower hq v
  have h2 := (pureGram_posSemidef_from_three hq (by norm_num : 2 ≤ 2)).dotProduct_mulVec_nonneg v
  have h3 := (pureGram_posSemidef_from_three hq (by norm_num : 2 ≤ 3)).dotProduct_mulVec_nonneg v
  have h4 := (pureGram_posSemidef_from_three hq (by norm_num : 2 ≤ 4)).dotProduct_mulVec_nonneg v
  simp only [star_trivial] at h2 h3 h4
  rw [fourHeadGram_decomposition hq] at hr
  simp only [Matrix.add_mulVec,dotProduct_add] at hr
  linarith only [hr,h2,h3,h4]


end
end GaloisForLFunctions.ThetaCuspSections.FourAtomCauchyTail
