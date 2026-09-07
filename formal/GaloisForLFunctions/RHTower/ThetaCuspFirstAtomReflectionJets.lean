import GaloisForLFunctions.RHTower.ThetaCuspNativeSixthRankBoundary

/-!
# Exact first-atom reflection jets through order twelve

The logarithmic polynomial derivative recurrence gives the six signed reflection
moments explicitly. Every polynomial identity is proved symbolically in Lean.
-/

open Polynomial Filter Topology
open scoped ContDiff
namespace RHTower
noncomputable section

/-- Polynomial differentiation after extracting the common first-atom Gaussian. -/
def thetaCuspFirstAtomJetStep (P : ℝ[X]) : ℝ[X] :=
  C (1/2) * P + C 2 * X * P.derivative - C 2 * X * P

/-- All logarithmic first-atom source derivative polynomials in the scale variable. -/
def thetaCuspFirstAtomJetPolynomial : ℕ → ℝ[X]
  | 0 => C 4 * X^2 - C 6 * X
  | n+1 => thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial n)

private def firstAtomProfile (P : ℝ[X]) (x : ℝ) : ℝ :=
  Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x) *
    P.eval (thetaCuspSingleAtomReflectionScale 1 x)

private theorem hasDerivAt_firstAtomProfile (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (firstAtomProfile P) (firstAtomProfile (thetaCuspFirstAtomJetStep P) x) x := by
  have hq := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hs := ((hasDerivAt_id x).div_const 2 |>.sub hq).exp
  have hp := (P.hasDerivAt (thetaCuspSingleAtomReflectionScale 1 x)).comp x hq
  exact (hs.mul hp).congr_deriv (by
    simp only [firstAtomProfile, thetaCuspFirstAtomJetStep, eval_add, eval_sub,
      eval_mul, eval_C, eval_X, id_eq, Function.comp_apply, Pi.sub_apply]
    ring)

private theorem sourceTerm_one_eq_firstAtomProfile :
    (fun x : ℝ => thetaCuspSourceTerm x 1) = firstAtomProfile (thetaCuspFirstAtomJetPolynomial 0) := by
  funext x
  have he : Real.exp (2*x) = Real.exp x^2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  simp only [thetaCuspSourceTerm, thetaCuspSeed, firstAtomProfile, thetaCuspFirstAtomJetPolynomial,
    thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, one_mul, mul_one,
    eval_sub, eval_mul, eval_pow, eval_C, eval_X, he, Real.exp_sub, div_eq_mul_inv]
  rw [← Real.exp_neg]
  ring

/-- Every literal first-atom derivative is its exact scale polynomial times the same Gaussian. -/
theorem iteratedDeriv_firstAtom_eq_scale_polynomial (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x) *
        (thetaCuspFirstAtomJetPolynomial n).eval (thetaCuspSingleAtomReflectionScale 1 x) := by
  have hf (n : ℕ) : iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) =
      firstAtomProfile (thetaCuspFirstAtomJetPolynomial n) := by
    induction n with
    | zero => exact sourceTerm_one_eq_firstAtomProfile
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_firstAtomProfile (thetaCuspFirstAtomJetPolynomial n) x).deriv
  exact congrFun (hf n) x

/-- The literal first-atom native reflection derivative. -/
def thetaCuspFirstAtomReflectionJet (n : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv n (fun t => thetaCuspSourceTerm (x+t) 1 * thetaCuspSourceTerm (x-t) 1) 0

/-- Exact finite Leibniz formula for every first-atom reflection jet. -/
theorem thetaCuspFirstAtomReflectionJet_eq (n : ℕ) (x : ℝ) :
    thetaCuspFirstAtomReflectionJet n x =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        iteratedDeriv i (fun y : ℝ => thetaCuspSourceTerm y 1) x *
          ((-1 : ℝ)^(n-i)*iteratedDeriv (n-i) (fun y : ℝ => thetaCuspSourceTerm y 1) x) := by
  have hf : ContDiff ℝ n (fun y : ℝ => thetaCuspSourceTerm y 1) := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  unfold thetaCuspFirstAtomReflectionJet
  have hl : ContDiffAt ℝ n (fun t : ℝ => thetaCuspSourceTerm (x+t) 1) 0 :=
    (hf.comp (contDiff_const.add contDiff_id)).contDiffAt
  have hr : ContDiffAt ℝ n (fun t : ℝ => thetaCuspSourceTerm (x-t) 1) 0 :=
    (hf.comp (contDiff_const.sub contDiff_id)).contDiffAt
  rw [iteratedDeriv_fun_mul hl hr]
  simp only [iteratedDeriv_comp_const_add _ (fun y : ℝ => thetaCuspSourceTerm y 1) x,
    iteratedDeriv_comp_const_sub _ (fun y : ℝ => thetaCuspSourceTerm y 1) x,
    add_zero, sub_zero, smul_eq_mul]

private theorem firstAtomJetPoly_0 : thetaCuspFirstAtomJetPolynomial 0 =
    C (-6) * X +
    C (4) * X^2 := by
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetPolynomial]
  ring

private theorem firstAtomJetPoly_1 : thetaCuspFirstAtomJetPolynomial 1 =
    C (-15) * X +
    C (30) * X^2 +
    C (-8) * X^3 := by
  rw [show thetaCuspFirstAtomJetPolynomial 1 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 0) from rfl, firstAtomJetPoly_0]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_2 : thetaCuspFirstAtomJetPolynomial 2 =
    C ((-75/2)) * X +
    C (165) * X^2 +
    C (-112) * X^3 +
    C (16) * X^4 := by
  rw [show thetaCuspFirstAtomJetPolynomial 2 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 1) from rfl, firstAtomJetPoly_1]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_3 : thetaCuspFirstAtomJetPolynomial 3 =
    C ((-375/4)) * X +
    C ((1635/2)) * X^2 +
    C (-1058) * X^3 +
    C (360) * X^4 +
    C (-32) * X^5 := by
  rw [show thetaCuspFirstAtomJetPolynomial 3 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 2) from rfl, firstAtomJetPoly_2]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_4 : thetaCuspFirstAtomJetPolynomial 4 =
    C ((-1875/8)) * X +
    C ((15465/4)) * X^2 +
    C (-8512) * X^3 +
    C (5176) * X^4 +
    C (-1056) * X^5 +
    C (64) * X^6 := by
  rw [show thetaCuspFirstAtomJetPolynomial 4 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 3) from rfl, firstAtomJetPoly_3]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_5 : thetaCuspFirstAtomJetPolynomial 5 =
    C ((-9375/16)) * X +
    C ((142935/8)) * X^2 +
    C ((-126121/2)) * X^3 +
    C (61020) * X^4 +
    C (-21440) * X^5 +
    C (2912) * X^6 +
    C (-128) * X^7 := by
  rw [show thetaCuspFirstAtomJetPolynomial 5 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 4) from rfl, firstAtomJetPoly_4]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_6 : thetaCuspFirstAtomJetPolynomial 6 =
    C ((-46875/32)) * X +
    C ((1305165/16)) * X^2 +
    C (-445627) * X^3 +
    C (644791) * X^4 +
    C (-347160) * X^5 +
    C (79280) * X^6 +
    C (-7680) * X^7 +
    C (256) * X^8 := by
  rw [show thetaCuspFirstAtomJetPolynomial 6 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 5) from rfl, firstAtomJetPoly_5]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_7 : thetaCuspFirstAtomJetPolynomial 7 =
    C ((-234375/64)) * X +
    C ((11840235/32)) * X^2 +
    C ((-24477769/8)) * X^3 +
    C ((12743955/2)) * X^4 +
    C (-4934762) * X^5 +
    C (1685320) * X^6 +
    C (-269920) * X^7 +
    C (19584) * X^8 +
    C (-512) * X^9 := by
  rw [show thetaCuspFirstAtomJetPolynomial 7 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 6) from rfl, firstAtomJetPoly_6]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_8 : thetaCuspFirstAtomJetPolynomial 8 =
    C ((-1171875/128)) * X +
    C ((107030865/64)) * X^2 +
    C (-20628202) * X^3 +
    C (60281251) * X^4 +
    C (-64558956) * X^5 +
    C (30936024) * X^6 +
    C (-7284480) * X^7 +
    C (862976) * X^8 +
    C (-48640) * X^9 +
    C (1024) * X^10 := by
  rw [show thetaCuspFirstAtomJetPolynomial 8 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 7) from rfl, firstAtomJetPoly_7]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_9 : thetaCuspFirstAtomJetPolynomial 9 =
    C ((-5859375/256)) * X +
    C ((965621535/128)) * X^2 +
    C ((-4397696881/32)) * X^3 +
    C ((1107294075/2)) * X^4 +
    C (-798431540) * X^5 +
    C (515818212) * X^6 +
    C (-167497008) * X^7 +
    C (28808064) * X^8 +
    C (-2625792) * X^9 +
    C (118272) * X^10 +
    C (-2048) * X^11 := by
  rw [show thetaCuspFirstAtomJetPolynomial 9 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 8) from rfl, firstAtomJetPoly_8]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_10 : thetaCuspFirstAtomJetPolynomial 10 =
    C ((-29296875/512)) * X +
    C ((8702312565/256)) * X^2 +
    C ((-14533920247/16)) * X^3 +
    C ((79693693981/16)) * X^4 +
    C (-9490825245) * X^5 +
    C (8044590730) * X^6 +
    C (-3460343040) * X^7 +
    C (810327072) * X^8 +
    C (-106193280) * X^9 +
    C (7676160) * X^10 +
    C (-282624) * X^11 +
    C (4096) * X^12 := by
  rw [show thetaCuspFirstAtomJetPolynomial 10 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 9) from rfl, firstAtomJetPoly_9]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

/-- Exact reflected first-atom derivative of order 2. -/
theorem thetaCuspFirstAtomReflectionJet_2 (x : ℝ) :
    thetaCuspFirstAtomReflectionJet 2 x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^2 *
        (let q := thetaCuspSingleAtomReflectionScale 1 x;
        (-480 : ℝ) * q^3 +
    (384 : ℝ) * q^4 +
    (-128 : ℝ) * q^5) := by
  rw [thetaCuspFirstAtomReflectionJet_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    iteratedDeriv_firstAtom_eq_scale_polynomial]
  norm_num [Nat.choose, firstAtomJetPoly_0, firstAtomJetPoly_1, firstAtomJetPoly_2]
  ring

/-- Exact reflected first-atom derivative of order 4. -/
theorem thetaCuspFirstAtomReflectionJet_4 (x : ℝ) :
    thetaCuspFirstAtomReflectionJet 4 x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^2 *
        (let q := thetaCuspSingleAtomReflectionScale 1 x;
        (-1920 : ℝ) * q^3 +
    (17664 : ℝ) * q^4 +
    (-9728 : ℝ) * q^5 +
    (3072 : ℝ) * q^6) := by
  rw [thetaCuspFirstAtomReflectionJet_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    iteratedDeriv_firstAtom_eq_scale_polynomial]
  norm_num [Nat.choose, firstAtomJetPoly_0, firstAtomJetPoly_1, firstAtomJetPoly_2, firstAtomJetPoly_3, firstAtomJetPoly_4]
  ring

/-- Exact reflected first-atom derivative of order 6. -/
theorem thetaCuspFirstAtomReflectionJet_6 (x : ℝ) :
    thetaCuspFirstAtomReflectionJet 6 x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^2 *
        (let q := thetaCuspSingleAtomReflectionScale 1 x;
        (-7680 : ℝ) * q^3 +
    (328704 : ℝ) * q^4 +
    (-1015808 : ℝ) * q^5 +
    (430080 : ℝ) * q^6 +
    (-122880 : ℝ) * q^7) := by
  rw [thetaCuspFirstAtomReflectionJet_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    iteratedDeriv_firstAtom_eq_scale_polynomial]
  norm_num [Nat.choose, firstAtomJetPoly_0, firstAtomJetPoly_1, firstAtomJetPoly_2, firstAtomJetPoly_3, firstAtomJetPoly_4, firstAtomJetPoly_5, firstAtomJetPoly_6]
  ring

/-- Exact reflected first-atom derivative of order 8. -/
theorem thetaCuspFirstAtomReflectionJet_8 (x : ℝ) :
    thetaCuspFirstAtomReflectionJet 8 x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^2 *
        (let q := thetaCuspSingleAtomReflectionScale 1 x;
        (-30720 : ℝ) * q^3 +
    (5443584 : ℝ) * q^4 +
    (-49553408 : ℝ) * q^5 +
    (78446592 : ℝ) * q^6 +
    (-27525120 : ℝ) * q^7 +
    (6881280 : ℝ) * q^8) := by
  rw [thetaCuspFirstAtomReflectionJet_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    iteratedDeriv_firstAtom_eq_scale_polynomial]
  norm_num [Nat.choose, firstAtomJetPoly_0, firstAtomJetPoly_1, firstAtomJetPoly_2, firstAtomJetPoly_3, firstAtomJetPoly_4, firstAtomJetPoly_5, firstAtomJetPoly_6, firstAtomJetPoly_7, firstAtomJetPoly_8]
  ring

/-- Exact reflected first-atom derivative of order 10. -/
theorem thetaCuspFirstAtomReflectionJet_10 (x : ℝ) :
    thetaCuspFirstAtomReflectionJet 10 x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^2 *
        (let q := thetaCuspSingleAtomReflectionScale 1 x;
        (-122880 : ℝ) * q^3 +
    (87834624 : ℝ) * q^4 +
    (-2001010688 : ℝ) * q^5 +
    (7696220160 : ℝ) * q^6 +
    (-7596933120 : ℝ) * q^7 +
    (2312110080 : ℝ) * q^8 +
    (-495452160 : ℝ) * q^9) := by
  rw [thetaCuspFirstAtomReflectionJet_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    iteratedDeriv_firstAtom_eq_scale_polynomial]
  norm_num [Nat.choose, firstAtomJetPoly_0, firstAtomJetPoly_1, firstAtomJetPoly_2, firstAtomJetPoly_3, firstAtomJetPoly_4, firstAtomJetPoly_5, firstAtomJetPoly_6, firstAtomJetPoly_7, firstAtomJetPoly_8, firstAtomJetPoly_9, firstAtomJetPoly_10]
  ring

private theorem firstAtomJetPoly_11 : thetaCuspFirstAtomJetPolynomial 11 =
    C (-146484375/1024) * X^1 +
    C (78379406835/512) * X^2 +
    C (-764466165409/128) * X^3 +
    C (1412928478665/32) * X^4 +
    C (-876923014561/8) * X^5 +
    C (119539034615) * X^6 +
    C (-66264155540) * X^7 +
    C (20291082768) * X^8 +
    C (-3585229824) * X^9 +
    C (369747840) * X^10 +
    C (-21711360) * X^11 +
    C (665600) * X^12 +
    C (-8192) * X^13 := by
  rw [show thetaCuspFirstAtomJetPolynomial 11 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 10) from rfl, firstAtomJetPoly_10]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstAtomJetPoly_12 : thetaCuspFirstAtomJetPolynomial 12 =
    C (-732421875/2048) * X^1 +
    C (705707630265/1024) * X^2 +
    C (-313013736161/8) * X^3 +
    C (12392125151357/32) * X^4 +
    C (-9914155892223/8) * X^5 +
    C (6853874745311/4) * X^6 +
    C (-1199908324560) * X^7 +
    C (467331176752) * X^8 +
    C (-106908917280) * X^9 +
    C (14750290368) * X^10 +
    C (-1228001280) * X^11 +
    C (59729920) * X^12 +
    C (-1548288) * X^13 +
    C (16384) * X^14 := by
  rw [show thetaCuspFirstAtomJetPolynomial 12 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 11) from rfl, firstAtomJetPoly_11]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

/-- Exact reflected first-atom derivative of order twelve, from the symbolic recurrence. -/
theorem thetaCuspFirstAtomReflectionJet_12 (x : ℝ) :
    thetaCuspFirstAtomReflectionJet 12 x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^2 *
        (let q := thetaCuspSingleAtomReflectionScale 1 x;
        (-491520 : ℝ) * q^3 +
    (1408303104 : ℝ) * q^4 +
    (-75547148288 : ℝ) * q^5 +
    (603009318912 : ℝ) * q^6 +
    (-1280916848640 : ℝ) * q^7 +
    (886529064960 : ℝ) * q^8 +
    (-239798845440 : ℝ) * q^9 +
    (43599790080 : ℝ) * q^10) := by
  rw [thetaCuspFirstAtomReflectionJet_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    iteratedDeriv_firstAtom_eq_scale_polynomial]
  norm_num [Nat.choose, firstAtomJetPoly_0, firstAtomJetPoly_1, firstAtomJetPoly_2, firstAtomJetPoly_3, firstAtomJetPoly_4, firstAtomJetPoly_5, firstAtomJetPoly_6, firstAtomJetPoly_7, firstAtomJetPoly_8, firstAtomJetPoly_9, firstAtomJetPoly_10, firstAtomJetPoly_11, firstAtomJetPoly_12]
  ring

end
end RHTower
