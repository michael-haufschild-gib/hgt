import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorCofinalLimit
import GaloisForLFunctions.RHTower.ThetaContinuousRateOrbitDensity
import GaloisForLFunctions.RHTower.CausalMobiusThetaTail

/-!
# Mellin laws of the theta cutoff commutator

With `G(z) = π^{−(z+1)/2} Γ((z+3)/2)` and `E_S(s) = ∏_{p∈S} (1 − p^{−s})`:

* every flux atom has `∫ e^{zy} F_d(y) dy = G(z) d^{−1−z}` (`Re z > −3`), so the finite boundary
  profile has `∫ e^{zy} C_S(y) dy = G(z)[E_S(1) − E_S(1+z)]` and zero ordinary integral;
* the moving shell has the exact complex weighted rough-number discrepancy
  `∫ e^{zy} e^{(y−log N)/2} C_{S,N}(y − log N) dy = z G(z) N^z [E_S(1+z) H_N(1+z) − H^rough_{S,N}(1+z)]`;
* the cofinal current has `∫ e^{zy} C_∞(y) dy = −G(z)/ζ(1+z)` for `Re z > 0`.
-/

open MeasureTheory Set Filter Topology ArithmeticFunction

namespace RHTower

noncomputable section

/-- The archimedean factor `G(z) = π^{−(z+1)/2} Γ((z+3)/2)`. -/
def commutatorGammaFactor (z : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-(z + 1) / 2) * Complex.Gamma ((z + 3) / 2)

/-- The finite Euler product `E_S(s) = ∏_{p ∈ S} (1 − p^{−s})`. -/
def finitePrimeEulerProduct (S : Finset ℕ) (s : ℂ) : ℂ := ∏ p ∈ S, (1 - (p : ℂ) ^ (-s))

theorem continuous_thetaFluxTerm (d : ℕ) : Continuous fun y => thetaFluxTerm y d := by
  simp only [thetaFluxTerm, rateFlux]; fun_prop

theorem ofReal_exp_cpow_eq_cexp (x : ℝ) (c : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ c = Complex.exp (x * c) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

theorem integrable_cexp_mul_thetaFluxTerm (d : ℕ) {z : ℂ} (hz : -3 < z.re) :
    Integrable fun y : ℝ => Complex.exp (z * y) * (thetaFluxTerm y d : ℂ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [thetaFluxTerm_zero, Complex.ofReal_zero, mul_zero]; exact integrable_zero _ _ _
  have hr : 0 < Real.pi * (d : ℝ) ^ 2 := by positivity
  have hb := (integrable_exp_mul_exp_neg_mul_exp_two_mul (b := z.re + 3) (by linarith) hr).const_mul
    (2 * Real.pi * (d : ℝ) ^ 2)
  refine hb.mono' ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    (Complex.continuous_ofReal.comp (continuous_thetaFluxTerm d))).aestronglyMeasurable
      (ae_of_all _ fun y => le_of_eq ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thetaFluxTerm_nonneg y d), thetaFluxTerm_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have e : Real.exp (z.re * y) * Real.exp (3 * y) = Real.exp ((z.re + 3) * y) := by
    rw [← Real.exp_add]; ring_nf
  rw [← e]
  ring

/-- **Flux-atom Mellin law.**  `∫ e^{zy} F_d(y) dy = G(z) d^{−1−z}` for `Re z > −3`. -/
theorem integral_cexp_mul_thetaFluxTerm {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : -3 < z.re) :
    (∫ y : ℝ, Complex.exp (z * y) * (thetaFluxTerm y d : ℂ)) =
      commutatorGammaFactor z * (d : ℂ) ^ (-(1 + z)) := by
  have hr : 0 < Real.pi * (d : ℝ) ^ 2 := by positivity
  have ha : 0 < ((z + 3) / 2).re := by simp; linarith
  have hG := Complex.integral_cpow_mul_exp_neg_mul_Ioi ha hr
  have hsub := setIntegral_Ioi_zero_eq_integral_exp_two_mul (fun u : ℝ =>
    ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) * ((u : ℂ) ^ ((z + 3) / 2 - 1) *
      Complex.exp (-(((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) * u))))
  rw [integral_const_mul, hG] at hsub
  have hfun : ∀ y : ℝ, (2 * Real.exp (2 * y)) • (((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) *
      (((Real.exp (2 * y) : ℝ) : ℂ) ^ ((z + 3) / 2 - 1) *
        Complex.exp (-(((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) * (Real.exp (2 * y) : ℝ))))) =
      Complex.exp (z * y) * (thetaFluxTerm y d : ℂ) := fun y => by
    rw [ofReal_exp_cpow_eq_cexp, thetaFluxTerm_eq, Complex.real_smul]
    push_cast
    have e1 : Complex.exp (2 * (y : ℂ)) * Complex.exp (2 * (y : ℂ) * ((z + 3) / 2 - 1)) =
        Complex.exp (z * y) * Complex.exp (3 * y) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    linear_combination (2 * (Real.pi : ℂ) * (d : ℂ) ^ 2 *
      Complex.exp (-((Real.pi : ℂ) * (d : ℂ) ^ 2 * Complex.exp (2 * (y : ℂ))))) * e1
  simp_rw [hfun] at hsub
  rw [← hsub, one_div_cpow_eq hr, commutatorGammaFactor]
  have hπ : ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((z + 3) / 2)) * ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) =
      (Real.pi : ℂ) ^ (-(z + 1) / 2) * (d : ℂ) ^ (-(1 + z)) := by
    have hpi0 : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
    have hne : ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [show ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((z + 3) / 2)) * ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) =
        ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((z + 3) / 2) + 1) by
          rw [Complex.cpow_add _ _ hne, Complex.cpow_one],
      show -((z + 3) / 2) + 1 = -(z + 1) / 2 by ring,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hpi0 hd0, Complex.ofReal_pow]
    congr 1
    have hlog : (Complex.log (d : ℂ)).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_im]
    rw [← Complex.cpow_natCast, ← Complex.cpow_mul]
    · congr 1; push_cast; ring
    · norm_num [Complex.mul_im, hlog]; exact Real.pi_pos
    · norm_num [Complex.mul_im, hlog]; exact Real.pi_pos.le
  rw [show ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) * (((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((z + 3) / 2)) *
    Complex.Gamma ((z + 3) / 2)) = (((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ) ^ (-((z + 3) / 2)) *
      ((Real.pi * (d : ℝ) ^ 2 : ℝ) : ℂ)) * Complex.Gamma ((z + 3) / 2) by ring, hπ]
  ring

theorem natCast_prod_primes_cpow (T : Finset ℕ) (s : ℂ) :
    (((∏ p ∈ T, p : ℕ) : ℂ)) ^ s = ∏ p ∈ T, (p : ℂ) ^ s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert p T hpT ih =>
    rw [Finset.prod_insert hpT, Finset.prod_insert hpT, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

theorem finiteEulerProduct_eq_sum_powerset (S : Finset ℕ) (s : ℂ) :
    finitePrimeEulerProduct S s = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * ((∏ p ∈ T, p : ℕ) : ℂ) ^ (-s) := by
  classical
  have h := Finset.prod_add (fun p : ℕ => -(p : ℂ) ^ (-s)) (fun _ => (1 : ℂ)) S
  simp only [Finset.prod_const_one, mul_one] at h
  rw [finitePrimeEulerProduct, show ∏ p ∈ S, (1 - (p : ℂ) ^ (-s)) = ∏ p ∈ S, (-(p : ℂ) ^ (-s) + 1) from
    Finset.prod_congr rfl fun p _ => by ring, h]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_neg, natCast_prod_primes_cpow]

/-- **(3) Mellin law of the finite boundary profile.**
`∫ e^{zy} C_S(y) dy = G(z)[E_S(1) − E_S(1+z)]` for `Re z > −3`; in particular `∫ C_S = 0`. -/
theorem integral_cexp_mul_commutatorBoundaryProfile (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    {z : ℂ} (hz : -3 < z.re) :
    (∫ y : ℝ, Complex.exp (z * y) * (commutatorBoundaryProfile S y : ℂ)) =
      commutatorGammaFactor z * (finitePrimeEulerProduct S 1 - finitePrimeEulerProduct S (1 + z)) := by
  have hpos : ∀ T ∈ S.powerset, 0 < ∏ p ∈ T, p := fun T hT =>
    Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  have hfun : (fun y : ℝ => Complex.exp (z * y) * (commutatorBoundaryProfile S y : ℂ)) = fun y : ℝ =>
      -(∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        (Complex.exp (z * y) * (thetaFluxTerm y (∏ p ∈ T, p) : ℂ))) +
      ((∏ p ∈ S, (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * (Complex.exp (z * y) * (thetaFluxTerm y 1 : ℂ)) := by
    funext y
    rw [commutatorBoundaryProfile_eq_flux S hS]
    push_cast
    rw [mul_add, mul_neg, Finset.mul_sum]
    congr 1
    · congr 1; exact Finset.sum_congr rfl fun T _ => by ring
    · ring
  rw [hfun, integral_add, integral_neg, integral_finsetSum, integral_const_mul]
  · have hE1 : finitePrimeEulerProduct S 1 = ((∏ p ∈ S, (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) := by
      rw [finitePrimeEulerProduct]; push_cast
      exact Finset.prod_congr rfl fun p _ => by rw [Complex.cpow_neg_one]
    rw [hE1, finiteEulerProduct_eq_sum_powerset, integral_cexp_mul_thetaFluxTerm one_pos hz]
    rw [Finset.sum_congr rfl fun T hT => by rw [integral_const_mul,
      integral_cexp_mul_thetaFluxTerm (hpos T hT) hz]]
    simp only [Nat.cast_one, Complex.one_cpow, mul_one]
    have hc : ∀ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (commutatorGammaFactor z *
        ((∏ p ∈ T, p : ℕ) : ℂ) ^ (-(1 + z))) = commutatorGammaFactor z *
          ((-1 : ℂ) ^ T.card * ((∏ p ∈ T, p : ℕ) : ℂ) ^ (-(1 + z))) := fun _ _ => by ring
    rw [Finset.sum_congr rfl hc, ← Finset.mul_sum]
    ring
  · exact fun T hT => (integrable_cexp_mul_thetaFluxTerm _ hz).const_mul _
  · exact (integrable_finsetSum _ fun T _ => (integrable_cexp_mul_thetaFluxTerm _ hz).const_mul _).neg
  · exact (integrable_cexp_mul_thetaFluxTerm 1 hz).const_mul _

theorem integral_commutatorBoundaryProfile (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∫ y : ℝ, commutatorBoundaryProfile S y) = 0 := by
  have h := integral_cexp_mul_commutatorBoundaryProfile S hS (z := 0) (by norm_num)
  simp only [zero_mul, Complex.exp_zero, one_mul, add_zero, sub_self, mul_zero] at h
  exact_mod_cast (integral_complex_ofReal.symm.trans h)

/-- **(5) Reciprocal-zeta Mellin law.**  `∫ e^{zy} C_∞(y) dy = −G(z)/ζ(1+z)` for `Re z > 0`. -/
theorem integral_cexp_mul_cofinalBoundaryProfile {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * (cofinalBoundaryProfile y : ℂ)) ∧
    (∫ y : ℝ, Complex.exp (z * y) * (cofinalBoundaryProfile y : ℂ)) =
      -(commutatorGammaFactor z * (riemannZeta (1 + z))⁻¹) := by
  set Gd : ℕ → ℝ → ℂ := fun d y => Complex.exp (z * y) * (((moebius d : ℝ) * thetaFluxTerm y d : ℝ) : ℂ)
  have hz3 : -3 < z.re := by linarith
  have hint : ∀ d, Integrable (Gd d) := fun d => by
    refine ((integrable_cexp_mul_thetaFluxTerm d hz3).const_mul ((moebius d : ℝ) : ℂ)).congr
      (ae_of_all _ fun y => ?_)
    simp only [Gd]; push_cast; ring
  have hval : ∀ d, (∫ y, Gd d y) = ((moebius d : ℤ) : ℂ) * (d : ℂ) ^ (-(1 + z)) *
      commutatorGammaFactor z := fun d => by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [Gd]
    · rw [show (fun y => Gd d y) = fun y : ℝ => ((moebius d : ℝ) : ℂ) *
          (Complex.exp (z * y) * (thetaFluxTerm y d : ℂ)) by funext y; simp only [Gd]; push_cast; ring,
        integral_const_mul, integral_cexp_mul_thetaFluxTerm hd hz3]
      push_cast; ring
  have hre : ∀ d, 0 < d → (∫ y : ℝ, Real.exp (z.re * y) * thetaFluxTerm y d) =
      ‖commutatorGammaFactor z.re‖ * (d : ℝ) ^ (-(1 + z.re)) := fun d hd => by
    have h := integral_cexp_mul_thetaFluxTerm hd (z := (z.re : ℂ)) (by simpa using hz3)
    rw [integral_cexp_ofReal_mul_ofReal] at h
    have hn := congrArg norm h
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y =>
      mul_nonneg (Real.exp_pos _).le (thetaFluxTerm_nonneg y d)), norm_mul,
      Complex.norm_natCast_cpow_of_pos hd] at hn
    rw [hn]
    congr 2
  have hsum : Summable fun d => ∫ y, ‖Gd d y‖ := by
    refine Summable.of_nonneg_of_le (fun d => integral_nonneg fun y => norm_nonneg _) (fun d => ?_)
      ((Real.summable_nat_rpow.2 (by linarith : -(1 + z.re) < -1)).mul_left
        ‖commutatorGammaFactor z.re‖)
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [Gd]; positivity
    · rw [← hre d hd]
      refine integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
        ((integrable_exp_mul_exp_neg_mul_exp_two_mul (b := z.re + 3) (by linarith)
          (by positivity : 0 < Real.pi * (d : ℝ) ^ 2)).const_mul (2 * Real.pi * (d : ℝ) ^ 2) |>.congr
            (ae_of_all _ fun y => by
              simp only [thetaFluxTerm_eq]
              rw [show Real.exp ((z.re + 3) * y) = Real.exp (z.re * y) * Real.exp (3 * y) by
                rw [← Real.exp_add]; ring_nf]
              ring_nf))
        (ae_of_all _ fun y => ?_)
      simp only [Gd, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (thetaFluxTerm_nonneg y d), Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      have hμ : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (thetaFluxTerm_nonneg y d) hμ)
        (Real.exp_pos _).le
  have hfun : (fun y : ℝ => Complex.exp (z * y) * (cofinalBoundaryProfile y : ℂ)) =
      fun y => -∑' d, Gd d y := by
    funext y
    rw [cofinalBoundaryProfile, Complex.ofReal_neg, Complex.ofReal_tsum, mul_neg, tsum_mul_left]
  rw [hfun]
  refine ⟨(GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hint hsum).neg, ?_⟩
  rw [integral_neg, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hval]
  rw [tsum_mul_right, tsum_moebius_mul_natCast_cpow (by simp; linarith)]
  ring

/-- The zeta partial sum `H_N(s) = Σ_{n ≤ N} n^{−s}`. -/
def harmonicCutoff (N : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)

/-- The rough partial sum `H^rough_{S,N}(s) = Σ_{m ≤ N, (m,P) = 1} m^{−s}`. -/
def roughHarmonicCutoff (S : Finset ℕ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m), (m : ℂ) ^ (-s)

theorem thetaAtomMellinFactor_add_half (z : ℂ) :
    thetaAtomMellinFactor (z + 1 / 2) = z * commutatorGammaFactor z := by
  rw [thetaAtomMellinFactor, commutatorGammaFactor, one_div_cpow_eq Real.pi_pos,
    show z + 1 / 2 - 1 / 2 = z by ring, show (z + 1 / 2) / 2 + 5 / 4 = (z + 3) / 2 by ring,
    show -((z + 1 / 2) / 2 + 1 / 4) = -(z + 1) / 2 by ring]
  ring

theorem integral_cexp_mul_atom_sum {w : ℂ} (hw : -(5 / 2) < w.re) (s : Finset ℕ) (f : ℕ → ℕ)
    (hs : ∀ m ∈ s, 0 < f m) :
    (∫ x : ℝ, Complex.exp (w * x) * ((∑ m ∈ s, thetaCuspSourceTerm x (f m) : ℝ) : ℂ)) =
      (∑ m ∈ s, (f m : ℂ) ^ (-(w + 1 / 2))) * thetaAtomMellinFactor w := by
  simp_rw [Complex.ofReal_sum, Finset.mul_sum]
  rw [integral_finsetSum _ fun m hm => integrable_cexp_mul_thetaCuspSourceTerm w hw _ (hs m hm),
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun m hm => integral_cexp_mul_thetaCuspSourceTerm w hw _ (hs m hm)

/-- **(3g) Exact complex weighted rough-number discrepancy.**  For `Re z > −3`,
`∫ e^{zy} e^{(y−log N)/2} C_{S,N}(y−log N) dy = z G(z) N^z [E_S(1+z) H_N(1+z) − H^rough_{S,N}(1+z)]`. -/
theorem integral_cexp_mul_movingCommutatorDensity (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hN : 0 < N) {z : ℂ} (hz : -3 < z.re) :
    (∫ y : ℝ, Complex.exp (z * y) * (movingCommutatorDensity S N y : ℂ)) =
      z * commutatorGammaFactor z * (N : ℂ) ^ z *
        (finitePrimeEulerProduct S (1 + z) * harmonicCutoff N (1 + z) - roughHarmonicCutoff S N (1 + z)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : -(5 / 2) < (z + 1 / 2).re := by simp; linarith
  set φ : ℝ → ℂ := fun x => Complex.exp ((z + 1 / 2) * x) * (cutoffCommutatorSource S N x : ℂ)
  have hshift : (fun y : ℝ => Complex.exp (z * y) * (movingCommutatorDensity S N y : ℂ)) =
      fun y => (N : ℂ) ^ z * φ (y - Real.log N) := by
    funext y
    simp only [φ, movingCommutatorDensity]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Complex.cpow_def_of_ne_zero hNc, show Complex.log (N : ℂ) = (Real.log N : ℂ) by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hNR.le]]
    push_cast
    simp only [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hshift, integral_const_mul, integral_sub_right_eq_self φ (Real.log N)]
  have hC : ∀ x, cutoffCommutatorSource S N x =
      (∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
        ∑ n ∈ Finset.Icc 1 N, thetaCuspSourceTerm x ((∏ p ∈ T, p) * n)) -
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m), thetaCuspSourceTerm x m := fun x => by
    rw [cutoffCommutatorSource, thetaPrimeDeletion_integerCutoffThetaSource S hS, roughCutoffThetaSource]
  have hpos : ∀ T ∈ S.powerset, 0 < ∏ p ∈ T, p := fun T hT =>
    Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  have hint1 : ∀ T ∈ S.powerset, Integrable fun x : ℝ => Complex.exp ((z + 1 / 2) * x) *
      ((∑ n ∈ Finset.Icc 1 N, thetaCuspSourceTerm x ((∏ p ∈ T, p) * n) : ℝ) : ℂ) := fun T hT => by
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    exact integrable_finsetSum _ fun n hn => integrable_cexp_mul_thetaCuspSourceTerm _ hw _
      (Nat.mul_pos (hpos T hT) (Finset.mem_Icc.1 hn).1)
  have hint2 : Integrable fun x : ℝ => Complex.exp ((z + 1 / 2) * x) *
      ((∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m), thetaCuspSourceTerm x m : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    exact integrable_finsetSum _ fun m hm => integrable_cexp_mul_thetaCuspSourceTerm _ hw _
      (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
  have hφ : φ = fun x : ℝ => (∑ T ∈ S.powerset, ((-1 : ℝ) ^ T.card : ℂ) * (Complex.exp ((z + 1 / 2) * x) *
      ((∑ n ∈ Finset.Icc 1 N, thetaCuspSourceTerm x ((∏ p ∈ T, p) * n) : ℝ) : ℂ))) -
      Complex.exp ((z + 1 / 2) * x) *
        ((∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m), thetaCuspSourceTerm x m : ℝ) : ℂ) := by
    funext x
    simp only [φ, hC]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [hφ, integral_sub (integrable_finsetSum _ fun T hT => (hint1 T hT).const_mul _) hint2,
    integral_finsetSum _ fun T hT => (hint1 T hT).const_mul _]
  simp_rw [integral_const_mul]
  have hr := integral_cexp_mul_atom_sum hw ((Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m))
    (fun m => m) fun m hm => (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
  rw [Finset.sum_congr rfl fun T hT => by rw [integral_cexp_mul_atom_sum hw _ (fun n => (∏ p ∈ T, p) * n)
      fun n hn => Nat.mul_pos (hpos T hT) (Finset.mem_Icc.1 hn).1], hr,
    thetaAtomMellinFactor_add_half, finiteEulerProduct_eq_sum_powerset, harmonicCutoff,
    roughHarmonicCutoff, show z + 1 / 2 + 1 / 2 = 1 + z by ring]
  have hA : ∀ T : Finset ℕ, (∑ n ∈ Finset.Icc 1 N, (((∏ p ∈ T, p) * n : ℕ) : ℂ) ^ (-(1 + z))) =
      ((∏ p ∈ T, p : ℕ) : ℂ) ^ (-(1 + z)) * ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(1 + z)) := fun T => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  simp_rw [hA]
  push_cast
  generalize (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-(1 + z))) = H
  generalize z * commutatorGammaFactor z = c
  have h1 : ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (((∏ i ∈ T, (i : ℂ)) ^ (-(1 + z)) * H) * c) =
      (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (∏ i ∈ T, (i : ℂ)) ^ (-(1 + z))) * H * c := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h1]
  ring

end

end RHTower
