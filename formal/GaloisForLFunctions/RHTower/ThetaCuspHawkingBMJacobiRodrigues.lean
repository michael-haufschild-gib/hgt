import GaloisForLFunctions.HTGeometry.HypergeometricSpatialJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Weighted derivative identities for the original terminating radial Gauss factors. -/
open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
open GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def bmJacobiFactor (n : ℕ) (c : ℝ) (w z : ℂ) : ℂ :=
  ordinaryHypergeometric (-(n:ℂ)) ((n:ℂ)+(c:ℂ)+w) (c:ℂ) z

def bmJacobiDensity (n : ℕ) (c : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  power ((c:ℂ)-1) t*power w (1-t)*bmJacobiFactor n c w t

private theorem gauss_first (a b c z : ℂ) (hz : ‖z‖ₑ<1) :
    HasDerivAt (ordinaryHypergeometric a b c)
      (ordinaryHypergeometricFirstDerivativeSeriesValue a b c z) z := by
  exact ((ordinaryHypergeometricSeries ℂ a b c).hasFDerivAt_sum
    (hz.trans_le (hypergeometric_radius_one_le a b c))).hasDerivAt

private theorem gauss_second (a b c z : ℂ) (hz : ‖z‖ₑ<1) :
    HasDerivAt (ordinaryHypergeometricFirstDerivativeSeriesValue a b c)
      (ordinaryHypergeometricSecondDerivativeSeriesValue a b c z) z := by
  let p := ordinaryHypergeometricSeries ℂ a b c
  have hr : ‖z‖ₑ<p.radius := hz.trans_le (hypergeometric_radius_one_le a b c)
  have h := p.derivSeries.hasFDerivAt_sum (hr.trans_le p.radius_le_radius_derivSeries)
  simpa [p,ordinaryHypergeometricFirstDerivativeSeriesValue,
    ordinaryHypergeometricSecondDerivativeSeriesValue] using!
    (h.clm_apply (hasFDerivAt_const (1:ℂ) z)).hasDerivAt

private theorem jacobi_raising (n : ℕ) (c : ℝ) (w z : ℂ)
    (hc : 0<c) (hw : w.im≠0) (hz : ‖z‖ₑ<1) :
    z*(1-z)*ordinaryHypergeometricFirstDerivativeSeriesValue
      (-(n:ℂ)) ((n:ℂ)+((c+1:ℝ):ℂ)+(w+1)) ((c+1:ℝ):ℂ) z+
      ((c:ℂ)-((c:ℂ)+w+1)*z)*bmJacobiFactor n (c+1) (w+1) z =
        (c:ℂ)*bmJacobiFactor (n+1) c w z := by
  let a : ℂ := -((n+1:ℕ):ℂ)
  let b : ℂ := ((n+1:ℕ):ℂ)+(c:ℂ)+w
  let K : ℂ := a*b/(c:ℂ)
  have hc0 : (c:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have ha0 : a≠0 := neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
  have hb0 : b≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [b,Complex.add_im,Complex.natCast_im,Complex.ofReal_im,zero_add,Complex.zero_im] at hi
    exact hw hi
  have hK : K≠0 := div_ne_zero (mul_ne_zero ha0 hb0) hc0
  have ha1 : a+1=-(n:ℂ) := by dsimp only [a]; push_cast; ring
  have hb1 : b+1=(n:ℂ)+((c+1:ℝ):ℂ)+(w+1) := by dsimp only [b]; push_cast; ring
  have hc1 : (c:ℂ)+1=((c+1:ℝ):ℂ) := by push_cast; rfl
  have hshift (u : ℂ) (hu : ‖u‖ₑ<1) :
      ordinaryHypergeometricFirstDerivativeSeriesValue a b c u =
        K*bmJacobiFactor n (c+1) (w+1) u := by
    rw [hypergeometric_first_eq_shift a b c u hu,ha1,hb1,hc1]
    rfl
  let D := ordinaryHypergeometricFirstDerivativeSeriesValue
    (-(n:ℂ)) ((n:ℂ)+((c+1:ℝ):ℂ)+(w+1)) ((c+1:ℝ):ℂ) z
  have hQ : HasDerivAt (bmJacobiFactor n (c+1) (w+1)) D z := gauss_first _ _ _ _ hz
  have hevent : ordinaryHypergeometricFirstDerivativeSeriesValue a b c =ᶠ[𝓝 z]
      fun u => K*bmJacobiFactor n (c+1) (w+1) u := by
    have he : ∀ᶠ u : ℂ in 𝓝 z, ‖u‖ₑ<1 :=
      continuous_enorm.continuousAt.eventually (eventually_lt_nhds hz)
    filter_upwards [he] with u hu using hshift u hu
  have hD : ordinaryHypergeometricSecondDerivativeSeriesValue a b c z=K*D :=
    (gauss_second a b c z hz).unique ((hQ.const_mul K).congr_of_eventuallyEq hevent)
  have hav (j : ℕ) : (j:ℂ)≠-(c:ℂ) := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.natCast_re,Complex.neg_re,Complex.ofReal_re] at hr
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    linarith only [hc,hj,hr]
  have hODE := ordinaryHypergeometric_standardGaussODE a b c z hav
    (hz.trans_le (hypergeometric_radius_one_le a b c))
  rw [hD,hshift z hz] at hODE
  have hab : a*b=K*(c:ℂ) := by dsimp only [K]; field_simp
  have hcoef : a+b+1=(c:ℂ)+w+1 := by dsimp only [a,b]; ring
  rw [hab,hcoef] at hODE
  apply mul_left_cancel₀ hK
  change K*(z*(1-z)*D+((c:ℂ)-((c:ℂ)+w+1)*z)*bmJacobiFactor n (c+1) (w+1) z)=_
  change z*(1-z)*(K*D)+((c:ℂ)-((c:ℂ)+w+1)*z)*
    (K*bmJacobiFactor n (c+1) (w+1) z)-(K*(c:ℂ))*bmJacobiFactor (n+1) c w z=0 at hODE
  linear_combination hODE

private theorem power_succ (v : ℂ) {t : ℝ} (ht : 0<t) :
    power (v+1) t=(t:ℂ)*power v t := by
  rw [power,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'),Complex.cpow_one]
  exact mul_comm _ _

/-- Differentiation raises the actual terminating polynomial and lowers both endpoint weights. -/
theorem bmJacobiDensity_hasDerivAt (n : ℕ) (c : ℝ) (w : ℂ)
    (hc : 0<c) (hw : w.im≠0) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (bmJacobiDensity n (c+1) (w+1))
      ((c:ℂ)*bmJacobiDensity (n+1) c w t) t := by
  have hu : 0<1-t := sub_pos.mpr ht.2
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hu0 : ((1-t:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hz : ‖(t:ℂ)‖ₑ<1 := by
    rw [← ENNReal.coe_one,enorm_lt_coe]
    exact_mod_cast (show ‖(t:ℂ)‖<1 by simpa [abs_of_pos ht.1] using ht.2)
  have hP := (power_derivatives (c:ℂ) ht.1).1
  have hU := ((power_derivatives (w+1) hu).1).scomp t ((hasDerivAt_id t).const_sub (1:ℝ))
  have hQ := (gauss_first (-(n:ℂ)) ((n:ℂ)+((c+1:ℝ):ℂ)+(w+1)) ((c+1:ℝ):ℂ) t hz).comp_ofReal
  have h := (hP.mul hU).mul hQ
  have hcsub : ((c+1:ℝ):ℂ)-1=(c:ℂ) := by push_cast; ring
  change HasDerivAt (fun x : ℝ => power (c:ℂ) x*power (w+1) (1-x)*
    bmJacobiFactor n (c+1) (w+1) x) _ t at h
  change HasDerivAt (fun x : ℝ => power (((c+1:ℝ):ℂ)-1) x*power (w+1) (1-x)*
    bmJacobiFactor n (c+1) (w+1) x) _ t
  rw [hcsub]
  apply h.congr_deriv
  have he := jacobi_raising n c w t hc hw hz
  have hp : power (c:ℂ) t=(t:ℂ)*power ((c:ℂ)-1) t := by
    simpa only [sub_add_cancel] using power_succ ((c:ℂ)-1) ht.1
  have hPv : powerFirst (c:ℂ) t=(c:ℂ)*power ((c:ℂ)-1) t := by
    dsimp only [powerFirst]
    rw [hp]
    field_simp
  have hUv : powerFirst (w+1) (1-t)=(w+1)*power w (1-t) := by
    dsimp only [powerFirst]
    rw [power_succ w hu]
    field_simp
  dsimp only [bmJacobiDensity,Function.comp_apply,Pi.mul_apply]
  rw [hPv,hUv,hp,power_succ w hu]
  simp only [neg_smul,one_smul,bmJacobiFactor] at he ⊢
  push_cast at he ⊢
  linear_combination power ((c:ℂ)-1) t*power w (1-t)*he

def bmJacobiSeed (n : ℕ) (c : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  power ((c:ℂ)+(n:ℂ)-1) t*power (w+(n:ℂ)) (1-t)

private theorem bmJacobiFactor_zero (c : ℝ) (w z : ℂ) :
    bmJacobiFactor 0 c w z=1 := by
  simp only [bmJacobiFactor,Nat.cast_zero,neg_zero,zero_add]
  change (ordinaryHypergeometricSeries ℂ 0 ((c:ℂ)+w) c).sum z=1
  rw [ordinaryHypergeometric_sum_eq,tsum_eq_single 0]
  · simp
  · intro m hm
    simp [hm]

private theorem bmJacobiSeed_succ (n : ℕ) (c : ℝ) (w : ℂ) :
    bmJacobiSeed (n+1) c w=bmJacobiSeed n (c+1) (w+1) := by
  funext t
  dsimp only [bmJacobiSeed]
  push_cast
  congr 2 <;> ring

/-- The full Rodrigues identity retains both original endpoint powers at every degree. -/
theorem bmJacobiDensity_rodrigues (n : ℕ) (c : ℝ) (w : ℂ)
    (hc : 0<c) (hw : w.im≠0) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    iteratedDeriv n (bmJacobiSeed n c w) t =
      (ascPochhammer ℂ n).eval (c:ℂ)*bmJacobiDensity n c w t := by
  induction n generalizing c w t with
  | zero => simp [bmJacobiSeed,bmJacobiDensity,bmJacobiFactor_zero]
  | succ n ih =>
    have hc1 : 0<c+1 := by linarith only [hc]
    have hw1 : (w+1).im≠0 := by simpa using hw
    have hevent : iteratedDeriv n (bmJacobiSeed (n+1) c w) =ᶠ[𝓝 t]
        fun u => (ascPochhammer ℂ n).eval ((c+1:ℝ):ℂ)*bmJacobiDensity n (c+1) (w+1) u := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      rw [bmJacobiSeed_succ]
      exact ih (c+1) (w+1) hc1 hw1 hu
    have hd := (bmJacobiDensity_hasDerivAt n c w hc hw ht).const_mul
      ((ascPochhammer ℂ n).eval ((c+1:ℝ):ℂ))
    rw [iteratedDeriv_succ,hevent.deriv_eq,hd.deriv]
    rw [ascPochhammer_succ_left]
    simp only [Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_one,Complex.ofReal_add,Complex.ofReal_one]
    ring

end
end RHTower.D4BMLaplaceRadial
