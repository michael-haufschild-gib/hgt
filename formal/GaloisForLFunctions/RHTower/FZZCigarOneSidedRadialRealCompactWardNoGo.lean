import GaloisForLFunctions.RHTower.FZZCigarParityTwoMarkedFullAnnularHessianNoGo
import GaloisForLFunctions.RHTower.FZZCigarMarkedRadialReplicaResponse
import GaloisForLFunctions.HTGeometry.PolygammaReflection

/-!
# One-sided FZZ radial/real-compact Ward no-go

The Halder--Jafferis replica prescription excludes the reflected radial wave.  For the resulting
one-sided response, the real part of `ψ'(1+iq)` is strictly positive at every real `q`.  Therefore
the radial replica--momentum derivative has strictly negative imaginary part at every momentum.

The full opposite-winding annular Hessian is real.  It cannot cancel this imaginary part at any
momentum or annulus geometry.  This kills the factorized FZZ-P subroute

`one-sided radial receiver + real compact Hessian → vanishing Ward defect → p=0 → passivity → RH`.

The sharp survivor is a phase constraint: any viable compact/all-depth completion must have a
strictly positive imaginary response which cancels the one-sided radial orientation.
-/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

private theorem deriv_digamma_conj (z : ℂ) :
    deriv Complex.digamma (conj z) = conj (deriv Complex.digamma z) := by
  have hfun : (conj ∘ Complex.digamma ∘ conj) = Complex.digamma := by
    funext w
    simp [Function.comp_def, ReflectedDigammaAnomaly.digamma_conj]
  have hderiv := deriv_conj_conj (f := Complex.digamma)
  rw [hfun] at hderiv
  have h := congrFun hderiv (conj z)
  simpa [Function.comp_def] using h

private theorem sq_lt_sinh_sq_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    x ^ 2 < Real.sinh x ^ 2 := by
  have self_lt_sinh {y : ℝ} (hy : 0 < y) : y < Real.sinh y := by
    have hmono : StrictMonoOn (fun t => Real.sinh t - t) (Set.Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact (Real.continuous_sinh.sub continuous_id).continuousOn
      · intro t ht
        rw [interior_Ici] at ht
        have hd : HasDerivAt (fun s => Real.sinh s - s) (Real.cosh t - 1) t :=
          (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
        rw [hd.deriv]
        have : 1 < Real.cosh t := Real.one_lt_cosh.mpr (by
          simp only [Set.mem_Ioi] at ht
          linarith)
        linarith
    have h := hmono Set.self_mem_Ici (le_of_lt hy) hy
    simpa using h
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have h := self_lt_sinh (neg_pos.mpr hxneg)
    rw [Real.sinh_neg] at h
    have hsneg : Real.sinh x < 0 := Real.sinh_neg_iff.mpr hxneg
    nlinarith
  · have h := self_lt_sinh hxpos
    have hspos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hxpos
    nlinarith

private theorem imaginary_axis_off_integers {q : ℝ} (hq : q ≠ 0) :
    ∀ m : ℤ, ((q : ℂ) * I) ≠ (m : ℂ) := by
  intro m hm
  have him := congrArg Complex.im hm
  simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul,
    intCast_im] at him
  exact hq (by linarith)

private theorem imaginary_axis_off_digamma_poles {q : ℝ} (hq : q ≠ 0) :
    ∀ p : ℕ, ((q : ℂ) * I) ≠ -(p : ℂ) := by
  intro p hp
  have him := congrArg Complex.im hp
  simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul,
    neg_im, natCast_im] at him
  exact hq (by linarith)

/-- Exact real-part identity for trigamma on the unit vertical line away from the origin. -/
theorem two_mul_re_deriv_digamma_one_add_mul_I {q : ℝ} (hq : q ≠ 0) :
    2 * (deriv Complex.digamma (1 + (q : ℂ) * I)).re =
      1 / q ^ 2 - Real.pi ^ 2 / Real.sinh (Real.pi * q) ^ 2 := by
  have href := RHTower.trigamma_reflection
    (z := (q : ℂ) * I) (imaginary_axis_off_integers hq)
  have hshift := GaloisForLFunctions.trigamma_recurrence
    ((q : ℂ) * I) (imaginary_axis_off_digamma_poles hq)
  have hpsi : (fun z => deriv Complex.Gamma z / Complex.Gamma z) =
      Complex.digamma := by
    funext z
    rw [Complex.digamma_def, logDeriv_apply]
  rw [hpsi] at hshift
  have hconj : deriv Complex.digamma (1 - (q : ℂ) * I) =
      conj (deriv Complex.digamma (1 + (q : ℂ) * I)) := by
    rw [← deriv_digamma_conj]
    congr 1
    apply Complex.ext <;> simp
  rw [hconj] at href
  have hsin : Complex.sin ((Real.pi : ℂ) * ((q : ℂ) * I)) =
      (Real.sinh (Real.pi * q) : ℂ) * I := by
    rw [show (Real.pi : ℂ) * ((q : ℂ) * I) =
      (((Real.pi * q : ℝ) : ℂ) * I) by push_cast; ring, Complex.sin_mul_I]
    simp
  rw [hsin] at href
  have hsinh : Real.sinh (Real.pi * q) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero Real.pi_ne_zero hq
  have hsquare : ((((Real.sinh (Real.pi * q) : ℝ) : ℂ) * I) ^ 2) =
      ((-(Real.sinh (Real.pi * q) ^ 2) : ℝ) : ℂ) := by
    calc
      (((Real.sinh (Real.pi * q) : ℝ) : ℂ) * I) ^ 2 =
          ((Real.sinh (Real.pi * q) : ℂ) ^ 2) * I ^ 2 := by ring
      _ = ((Real.sinh (Real.pi * q) : ℂ) ^ 2) * (-1) := by
        rw [show I ^ 2 = (-1 : ℂ) by norm_num]
      _ = ((-(Real.sinh (Real.pi * q) ^ 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow]
        push_cast
        ring
  have hrhs : (Real.pi : ℂ) ^ 2 /
      (((Real.sinh (Real.pi * q) : ℝ) : ℂ) * I) ^ 2 =
        ((-(Real.pi ^ 2 / Real.sinh (Real.pi * q) ^ 2) : ℝ) : ℂ) := by
    rw [hsquare, ← Complex.ofReal_pow, ← Complex.ofReal_div]
    congr 1
    field_simp [hsinh]
  rw [hrhs] at href
  have hre := congrArg Complex.re href
  simp only [add_re, conj_re, ofReal_re] at hre
  have hiqsquare : (((q : ℂ) * I) ^ 2) = ((-(q ^ 2) : ℝ) : ℂ) := by
    calc
      ((q : ℂ) * I) ^ 2 = ((q : ℂ) ^ 2) * I ^ 2 := by ring
      _ = ((q : ℂ) ^ 2) * (-1) := by
        rw [show I ^ 2 = (-1 : ℂ) by norm_num]
      _ = ((-(q ^ 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow]
        push_cast
        ring
  have hrat : (-1 : ℂ) / (((q : ℂ) * I) ^ 2) =
      ((1 / q ^ 2 : ℝ) : ℂ) := by
    rw [hiqsquare]
    have hreal : (-1 : ℝ) / (-(q ^ 2)) = 1 / q ^ 2 := by
      rw [div_neg, neg_div, neg_neg]
    have hone : (-1 : ℂ) = ((-1 : ℝ) : ℂ) := by norm_num
    rw [hone, ← Complex.ofReal_div]
    exact congrArg (fun x : ℝ => (x : ℂ)) hreal
  have hrat' : (1 : ℂ) / (((q : ℂ) * I) ^ 2) =
      -((1 / q ^ 2 : ℝ) : ℂ) := by
    calc
      (1 : ℂ) / (((q : ℂ) * I) ^ 2) =
          -((-1 : ℂ) / (((q : ℂ) * I) ^ 2)) := by ring
      _ = -((1 / q ^ 2 : ℝ) : ℂ) := by rw [hrat]
  have hshift' : deriv Complex.digamma ((q : ℂ) * I) =
      deriv Complex.digamma (1 + (q : ℂ) * I) - (1 / q ^ 2 : ℝ) := by
    rw [show (q : ℂ) * I + 1 = 1 + (q : ℂ) * I by ring, hrat'] at hshift
    linear_combination -hshift
  have hshiftre := congrArg Complex.re hshift'
  simp only [sub_re, ofReal_re] at hshiftre
  rw [hshiftre] at hre
  linarith

/-- Trigamma has strictly positive real part on the entire vertical line `1+iℝ`. -/
theorem re_deriv_digamma_one_add_mul_I_pos (q : ℝ) :
    0 < (deriv Complex.digamma (1 + (q : ℂ) * I)).re := by
  by_cases hq : q = 0
  · subst q
    rw [show (1 : ℂ) + ((0 : ℝ) : ℂ) * I = 1 by norm_num,
      RHTower.trigamma_one]
    norm_num
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos Real.pi_pos
  · have hformula := two_mul_re_deriv_digamma_one_add_mul_I hq
    have hxne : Real.pi * q ≠ 0 := mul_ne_zero Real.pi_ne_zero hq
    have hsq := sq_lt_sinh_sq_of_ne_zero hxne
    have hq2 : 0 < q ^ 2 := sq_pos_of_ne_zero hq
    have hs2 : 0 < Real.sinh (Real.pi * q) ^ 2 :=
      sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr hxne)
    have hfrac : Real.pi ^ 2 / Real.sinh (Real.pi * q) ^ 2 < 1 / q ^ 2 := by
      rw [div_lt_div_iff₀ hs2 hq2]
      nlinarith
    linarith

/-- Physical one-sided radial mixed receiver has strict imaginary orientation at every momentum.
Unlike the reflected diagnostic, it never vanishes at zero momentum. -/
theorem fzzMarkedRadialReplicaResponse_momentum_deriv_im_neg
    (radialCoupling radialScale momentum : ℝ) :
    (deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) momentum).im < 0 := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaResponse_momentum
    radialCoupling radialScale momentum).deriv]
  let a : ℝ := fzzMarkedRadialReplicaRate radialScale / Real.exp radialScale
  let T : ℂ := deriv Complex.digamma
    (1 + ((momentum / Real.exp radialScale : ℝ) : ℂ) * I)
  have htrig : 0 < T.re := re_deriv_digamma_one_add_mul_I_pos
    (momentum / Real.exp radialScale)
  have hscale : 0 < a :=
    div_pos (fzzMarkedRadialReplicaRate_pos radialScale) (Real.exp_pos radialScale)
  change (-((a : ℂ)) * I * T).im < 0
  have him : (-((a : ℂ)) * I * T).im = -a * T.re := by
    simp [Complex.mul_im]
  rw [him]
  nlinarith [mul_pos hscale htrig]

/-- Any cancellation of the one-sided radial receiver requires a compact source with strictly
positive imaginary response.  This is the sharp phase condition surviving the real-sector no-go. -/
theorem compact_im_pos_of_fzzOneSidedRadialMixedResponse_add_eq_zero
    {radialCoupling radialScale momentum : ℝ} {compactResponse : ℂ}
    (hzero : deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) momentum +
      compactResponse = 0) :
    0 < compactResponse.im := by
  have him := congrArg Complex.im hzero
  simp only [add_im, zero_im] at him
  have hradial := fzzMarkedRadialReplicaResponse_momentum_deriv_im_neg
    radialCoupling radialScale momentum
  linarith

/-- No real compact correction can cancel the physical one-sided radial receiver. -/
theorem fzzOneSidedRadialMixedResponse_add_real_ne_zero
    (radialCoupling radialScale momentum compactResponse : ℝ) :
    deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) momentum +
      (compactResponse : ℂ) ≠ 0 := by
  intro hzero
  have hpos := compact_im_pos_of_fzzOneSidedRadialMixedResponse_add_eq_zero hzero
  simp only [ofReal_im] at hpos
  exact lt_irrefl 0 hpos

/-- Literal one-sided radial receiver plus the full compact annular Hessian. -/
def fzzOneSidedRadialFullAnnularMixedWardDefect
    (radialCoupling radialScale levelLog momentum separation : ℝ) : ℂ :=
  deriv (fzzMarkedRadialReplicaResponse radialCoupling radialScale) momentum +
    (fzzTwoMarkedAnnularFullMixedResponse levelLog separation : ℂ)

theorem fzzOneSidedRadialFullAnnularMixedWardDefect_im_neg
    (radialCoupling radialScale levelLog momentum separation : ℝ) :
    (fzzOneSidedRadialFullAnnularMixedWardDefect
      radialCoupling radialScale levelLog momentum separation).im < 0 := by
  unfold fzzOneSidedRadialFullAnnularMixedWardDefect
  simpa only [add_im, ofReal_im, add_zero] using
    fzzMarkedRadialReplicaResponse_momentum_deriv_im_neg
      radialCoupling radialScale momentum

theorem fzzOneSidedRadialFullAnnularMixedWardDefect_ne_zero
    (radialCoupling radialScale levelLog momentum separation : ℝ) :
    fzzOneSidedRadialFullAnnularMixedWardDefect
      radialCoupling radialScale levelLog momentum separation ≠ 0 := by
  exact fzzOneSidedRadialMixedResponse_add_real_ne_zero
    radialCoupling radialScale momentum
      (fzzTwoMarkedAnnularFullMixedResponse levelLog separation)

/-- Closed route class: the HJ one-sided radial receiver plus any real compact annular Hessian
cannot satisfy a vanishing mixed Ward identity at any momentum or geometry. -/
def FZZOneSidedRadialRealCompactWardRouteKilled : Prop :=
  ∀ radialCoupling radialScale levelLog momentum separation : ℝ,
    fzzOneSidedRadialFullAnnularMixedWardDefect
      radialCoupling radialScale levelLog momentum separation ≠ 0

/-- **FZZ-P route kill.** A real compact source cannot cancel the strictly oriented imaginary
part of the physical one-sided radial receiver. -/
theorem fzzOneSidedRadialRealCompactWardRouteKilled :
    FZZOneSidedRadialRealCompactWardRouteKilled :=
  fzzOneSidedRadialFullAnnularMixedWardDefect_ne_zero

end

end GaloisForLFunctions.RHTower
