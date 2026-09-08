import GaloisForLFunctions.RHTower.DivisorContinuousHeadRegularity
import GaloisForLFunctions.RHTower.DivisorCoreMellinBoundary

/-!
# Exact physical Mellin transform of the finite signed divisor head

The physical unit Mellin integral continues from its absolute L-series
formula to the full square-root convergence half-plane. Finite Mobius
dilation then factors into the literal prime multiplier. The resulting
integral equals the previously constructed analytic core continuation;
no physical-source identity or contour hypothesis is assumed.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
namespace RHTower

private lemma empty_head (x : ℝ) :
    mobiusDivisorContinuousHead ∅ x=divisorContinuousUnitHead x := by
  simp [mobiusDivisorContinuousHead]

private lemma unit_mellin_initial {s : ℂ} (hs : 3/2 < s.re) :
    mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-s)=
      divisorSourceEntire (s-1/2)/(2*s*(s-1/2)) := by
  have hb (N : ℕ) : ‖∑ n ∈ Icc 1 N, (primeFreeDivisorIncrement n : ℂ)‖ ≤
      24*(N:ℝ)^(1/2:ℝ) := by
    rw [← Complex.ofReal_sum,sum_primeFreeDivisorIncrement,
      Complex.norm_real,Real.norm_eq_abs,← Real.sqrt_eq_rpow]
    rcases N.eq_zero_or_pos with rfl | hN
    · simp [primeFreeDivisorDefect]
    · exact abs_primeFreeDivisorDefect_le hN
  have h := hasMellin_squareRootSummatoryPrimitive (by norm_num : (0:ℝ) ≤ 24)
    hb (s := s) (by linarith) (by linarith)
    (LSeriesSummable_primeFreeDivisorIncrement_right (by
      simp only [Complex.sub_re]; norm_num; linarith))
  rw [show squareRootSummatoryPrimitive (fun n => (primeFreeDivisorIncrement n:ℂ)) =
    (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) from
      funext squareRootSummatoryPrimitive_divisor_eq_real] at h
  rw [divisorSourceEntire_eq_LSeries (by simp only [Complex.sub_re]; norm_num; linarith)]
  exact h.2

/-- The physical unit source has its exact Mellin formula throughout the
full square-root convergence half-plane. -/
theorem mellin_divisorContinuousUnitHead {s : ℂ} (hs : 1/2 < s.re) :
    mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-s)=
      divisorSourceEntire (s-1/2)/(2*s*(s-1/2)) := by
  let U : Set ℂ := {z | 1/2 < z.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hphys : DifferentiableOn ℂ (fun z => mellin
      (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-z)) U := by
    intro z hz
    have h := differentiableAt_mellin_mobiusDivisorContinuousHead ∅ hz
    simp only [empty_head] at h
    exact h.differentiableWithinAt
  have hsource : DifferentiableOn ℂ (fun z =>
      divisorSourceEntire (z-1/2)/(2*z*(z-1/2))) U := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; norm_num [U,h] at hz
    have hzH : z-1/2 ≠ 0 := by
      intro h
      have hz' := congrArg Complex.re h
      norm_num at hz'
      change 1/2 < z.re at hz
      linarith
    have hn : DifferentiableAt ℂ (fun w => divisorSourceEntire (w-1/2)) z :=
      (differentiable_divisorSourceEntire.comp (differentiable_id.sub_const (1/2))) z
    have hd : DifferentiableAt ℂ (fun w : ℂ => 2*w*(w-1/2)) z := by fun_prop
    exact (hn.div hd (mul_ne_zero (mul_ne_zero (by norm_num) hz0) hzH)).differentiableWithinAt
  have he : (fun z => mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-z))
      =ᶠ[𝓝 (2:ℂ)] (fun z => divisorSourceEntire (z-1/2)/(2*z*(z-1/2))) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (3/2:ℝ)<(2:ℂ).re)] with z hz
    exact unit_mellin_initial hz
  exact (hphys.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
    (hsource.analyticOnNhd hopen) (convex_halfSpace_re_gt (1/2)).isPreconnected
    (by norm_num [U] : (2:ℂ)∈U) he hs

private def coreMellinAF (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => ((ArithmeticFunction.moebius n:ℤ):ℂ)*(Real.sqrt n:ℂ)*(n:ℂ)^(-s),by simp⟩

private lemma coreMellinAF_mult (s : ℂ) : (coreMellinAF s).IsMultiplicative := by
  constructor
  · simp [coreMellinAF]
  · intro m n hmn
    simp only [coreMellinAF,ArithmeticFunction.coe_mk,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn,
      Int.cast_mul,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg m),Complex.ofReal_mul,
      Complex.natCast_mul_natCast_cpow]
    ring

private lemma half_factor (p : ℕ) (hp : p.Prime) (s : ℂ) :
    (Real.sqrt p:ℂ)*(p:ℂ)^(-s)=Complex.exp ((1/2-s)*(Real.log p:ℂ)) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hsqrt : (Real.sqrt p:ℂ)=Complex.exp ((Real.log p:ℂ)/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hpR,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hsqrt,Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero),
    ← Complex.natCast_log,← Complex.exp_add]
  congr 1
  ring

private lemma mellin_euler (P : Finset ℕ) (hP : ∀p∈P,p.Prime) (s : ℂ) :
    (∑d∈(∏p∈P,p).divisors,
      ((ArithmeticFunction.moebius d:ℤ):ℂ)*(Real.sqrt d:ℂ)*(d:ℂ)^(-s)) =
      divisorCoreMellinEuler P s := by
  have h := ((coreMellinAF_mult s).mul (ArithmeticFunction.isMultiplicative_zeta.natCast
    (R := ℂ))).map_prod_of_prime P hP
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  change (∑d∈(∏p∈P,p).divisors,coreMellinAF s d)=_
  rw [h,divisorCoreMellinEuler]
  apply prod_congr rfl
  intro p hp
  rw [(hP p hp).divisors,Finset.sum_pair (Ne.symm (hP p hp).ne_one)]
  simp only [coreMellinAF,ArithmeticFunction.coe_mk,ArithmeticFunction.moebius_apply_one,
    Int.cast_one,Real.sqrt_one,Complex.ofReal_one,one_mul,Nat.cast_one,Complex.one_cpow,
    ArithmeticFunction.moebius_apply_prime (hP p hp),Int.cast_neg,neg_mul,one_mul]
  rw [half_factor p (hP p hp)]
  ring

private lemma unit_mellin_convergent {s : ℂ} (hs : 1/2 < s.re) :
    MellinConvergent (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-s) := by
  simpa only [empty_head] using mellinConvergent_mobiusDivisorContinuousHead ∅ hs

private lemma unit_dilated_convergent {s : ℂ} (hs : 1/2 < s.re) {d : ℕ} (hd : 0<d) :
    MellinConvergent (fun x : ℝ => (divisorContinuousUnitHead (x/d):ℂ)) (-s) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have h := (MellinConvergent.comp_mul_left (a := (d:ℝ)⁻¹) (inv_pos.mpr hdR)).mpr
    (unit_mellin_convergent hs)
  simpa only [div_eq_mul_inv,mul_comm] using h

private lemma unit_dilated_mellin {s : ℂ} {d : ℕ} (hd : 0<d) :
    mellin (fun x : ℝ => (divisorContinuousUnitHead (x/d):ℂ)) (-s)=
      (d:ℂ)^(-s)*mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-s) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have h := mellin_comp_mul_left (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-s)
    (inv_pos.mpr hdR)
  have harg : (d:ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact ne_of_lt Real.pi_pos
  simpa only [div_eq_mul_inv,mul_comm,neg_neg,Complex.ofReal_inv,Complex.ofReal_natCast,
    Complex.inv_cpow _ _ harg,← Complex.cpow_neg,smul_eq_mul] using h

/-- The finite signed dilation has exactly its literal finite-prime Mellin multiplier. -/
theorem mellin_mobiusDivisorContinuousHead_euler (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    {s : ℂ} (hs : 1/2 < s.re) :
    mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) (-s)=
      divisorCoreMellinEuler P s*mellin (fun x : ℝ => (divisorContinuousUnitHead x:ℂ)) (-s) := by
  let D := (∏p∈P,p).divisors
  let c : ℕ→ℂ := fun d => ((ArithmeticFunction.moebius d:ℤ):ℂ)*(Real.sqrt d:ℂ)
  have hconv (d : ℕ) (hd : d∈D) :=
    (unit_dilated_convergent hs (Nat.pos_of_mem_divisors hd)).const_smul (c d)
  have he : (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) =
      fun x => ∑d∈D, c d • (divisorContinuousUnitHead (x/d):ℂ) := by
    funext x
    simp only [mobiusDivisorContinuousHead,Complex.ofReal_sum,Complex.ofReal_mul,
      Complex.ofReal_intCast,smul_eq_mul,c,D]
  rw [he,mellin]
  simp only [Finset.smul_sum]
  rw [integral_finsetSum _ hconv]
  change (∑d∈D,mellin (fun x : ℝ => c d • (divisorContinuousUnitHead (x/d):ℂ)) (-s))=_
  rw [← mellin_euler P hP s,Finset.sum_mul]
  apply sum_congr rfl
  intro d hd
  rw [mellin_const_smul (fun x : ℝ => (divisorContinuousUnitHead (x/d):ℂ)) (-s) (c d),
    smul_eq_mul,unit_dilated_mellin (Nat.pos_of_mem_divisors hd)]
  dsimp [c]
  ring

/-- The analytic processed continuation is the actual physical Mellin transform
on the entire square-root half-plane; no source-identification hypothesis remains. -/
theorem mellin_mobiusDivisorContinuousHead_eq_core (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) {s : ℂ} (hs : 1/2 < s.re) :
    mellin (fun x : ℝ => (mobiusDivisorContinuousHead P x:ℂ)) (-s)=divisorCoreMellin P s := by
  have hsH : s ≠ 1/2 := by intro h; norm_num [h] at hs
  rw [mellin_mobiusDivisorContinuousHead_euler P hprime hs,
    mellin_divisorContinuousUnitHead hs,divisorCoreMellin_eq P hP hsH]
  ring

end RHTower
