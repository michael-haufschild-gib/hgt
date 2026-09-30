import GaloisForLFunctions.HTGeometry.PolygammaSeries
import GaloisForLFunctions.RHTower.ArchimedeanGamma
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteDeflation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionLogSlope
/-!
# Actual Gamma and complete dyadic completion moments

The literal completion factor retains both rational connections, the real Gamma
connection and every dyadic lattice copy. Its odd jets are exactly the residual
Gamma reciprocal moments plus the complete nonzero dyadic lattice moments.
The two cancelled center modes and both raw factorial normalizations remain
explicit. Finite partition clocks use their literal logarithmic derivatives;
the exact contour split requires nonvanishing only on the integration circle.
-/



open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions

theorem liClock_iteratedDeriv_comp_affine (n : ℕ) (f : ℂ → ℂ) (a b x : ℂ) :
    iteratedDeriv n (fun z => f (a * z + b)) x =
      a ^ n * iteratedDeriv n f (a * x + b) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hfun : iteratedDeriv n (fun z => f (a * z + b)) =
          fun z => a ^ n * iteratedDeriv n f (a * z + b) := funext ih
      rw [iteratedDeriv_succ, hfun, deriv_const_mul_field]
      have hd := deriv_comp_mul_left a (fun w => iteratedDeriv n f (w + b)) x
      simp only [smul_eq_mul, deriv_comp_add_const] at hd
      rw [hd, iteratedDeriv_succ, pow_succ]
      ring

private theorem gammaRealLogConnection_odd_at_pos (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (2 * j + 1) gammaRealLogConnection (x : ℂ) =
      ((2 * j + 1).factorial : ℂ) *
        ∑' n : ℕ, (2 * (n : ℂ) + (x : ℂ)) ^ (-((2 * j + 2 : ℕ) : ℤ)) := by
  have hσ : 0 < x / 2 := by positivity
  have hs := hasSum_polygamma_series hσ 0 (2 * j)
  have hsign : (-1 : ℂ) ^ (2 * j) = 1 := by
    rw [pow_mul]
    norm_num
  simp only [Complex.ofReal_zero, zero_mul, add_zero, hsign, one_div] at hs
  have hfac : ((2 * j + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * j + 1)
  have hdig : iteratedDeriv (2 * j + 1) Complex.digamma ((x / 2 : ℝ) : ℂ) =
      ((2 * j + 1).factorial : ℂ) *
        ∑' n : ℕ, ((((x / 2 : ℝ) : ℂ) + (n : ℂ)) ^ (2 * j + 2))⁻¹ := by
    rw [hs.tsum_eq]
    field_simp
  have hcompose : (fun s : ℂ => Complex.digamma (s / 2)) =
      (fun s => Complex.digamma ((1 / 2 : ℂ) * s + 0)) := by
    funext s
    congr 1
    ring
  have hpoint : (1 / 2 : ℂ) * (x : ℂ) + 0 = ((x / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hderiv : iteratedDeriv (2 * j + 1) gammaRealLogConnection (x : ℂ) =
      ((1 / 2 : ℂ) ^ (2 * j + 1) *
        iteratedDeriv (2 * j + 1) Complex.digamma ((x / 2 : ℝ) : ℂ)) / 2 := by
    unfold gammaRealLogConnection
    rw [iteratedDeriv_const_add (by omega), iteratedDeriv_div_const,
      hcompose, liClock_iteratedDeriv_comp_affine, hpoint]
  rw [hderiv, hdig]
  have hterm (n : ℕ) :
      ((1 / 2 : ℂ) ^ (2 * j + 1) / 2) *
        ((((x / 2 : ℝ) : ℂ) + (n : ℂ)) ^ (2 * j + 2))⁻¹ =
      (2 * (n : ℂ) + (x : ℂ)) ^ (-((2 * j + 2 : ℕ) : ℤ)) := by
    have hz : 2 * (n : ℂ) + (x : ℂ) =
        2 * (((x / 2 : ℝ) : ℂ) + (n : ℂ)) := by
      push_cast
      ring
    rw [hz, zpow_neg, zpow_natCast, mul_pow, mul_inv_rev]
    rw [← inv_pow (2 : ℂ), show (2 : ℂ)⁻¹ = 1 / 2 by norm_num]
    have hexp : (1 / 2 : ℂ) ^ (2 * j + 2) = (1 / 2 : ℂ) ^ (2 * j + 1) / 2 := by
      rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, pow_succ]
      ring
    rw [hexp]
    ring
  calc
    ((1 / 2 : ℂ) ^ (2 * j + 1) *
        (((2 * j + 1).factorial : ℂ) *
          ∑' n : ℕ, ((((x / 2 : ℝ) : ℂ) + (n : ℂ)) ^ (2 * j + 2))⁻¹)) / 2 =
      ((2 * j + 1).factorial : ℂ) *
        (((1 / 2 : ℂ) ^ (2 * j + 1) / 2) *
          ∑' n : ℕ, ((((x / 2 : ℝ) : ℂ) + (n : ℂ)) ^ (2 * j + 2))⁻¹) := by ring
    _ = _ := by rw [← tsum_mul_left]; congr 1; exact tsum_congr hterm

theorem liClock_gammaRealLogConnection_central_odd (j : ℕ) :
    iteratedDeriv (2 * j + 1) gammaRealLogConnection (1 / 2 : ℂ) =
      ((2 * j + 1).factorial : ℂ) *
        ∑' n : ℕ, (2 * (n : ℂ) + 1 / 2) ^ (-((2 * j + 2 : ℕ) : ℤ)) := by
  simpa using gammaRealLogConnection_odd_at_pos j (x := 1 / 2) (by norm_num)

theorem liClock_gammaRealLogConnection_filled_odd (j : ℕ) :
    iteratedDeriv (2 * j + 1) (fun s => gammaRealLogConnection (s + 2)) (1 / 2 : ℂ) =
      ((2 * j + 1).factorial : ℂ) *
        ∑' n : ℕ, (2 * (n : ℂ) + 5 / 2) ^ (-((2 * j + 2 : ℕ) : ℤ)) := by
  have hc := liClock_iteratedDeriv_comp_affine (2 * j + 1) gammaRealLogConnection
    1 2 (1 / 2)
  simp only [one_mul, one_pow] at hc
  rw [hc]
  convert gammaRealLogConnection_odd_at_pos j (x := 5 / 2) (by norm_num) using 1 <;> norm_num

end GaloisForLFunctions


open Complex Set Filter Topology
namespace RHTower
noncomputable section
def liClockPairedEtaDyadicReciprocal (k : ℤ) : ℂ :=
  if k = 0 then 0 else (1/2 + 2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ))⁻¹

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
private theorem log_two_lt : Real.log 2 < 3/4 :=
  Real.log_two_lt_d9.trans (by norm_num)

theorem liClockPairedEtaDyadicReciprocal_norm_sq_le (k : ℤ) :
    ‖liClockPairedEtaDyadicReciprocal k‖^2 ≤
      (Real.log 2)^2/(4*Real.pi^2) * (1/(k:ℝ)^2) := by
  by_cases hk : k = 0
  · subst k; simp [liClockPairedEtaDyadicReciprocal]
  have hkre : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hl := log_two_pos
  have hp := Real.pi_pos
  have hnorm : ‖(1/2 + 2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ):ℂ)‖^2 =
      1/4+(2*Real.pi*(k:ℝ)/Real.log 2)^2 := by
    have hc : (1/2 + 2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ):ℂ) =
        (1/2:ℂ)+((2*Real.pi*(k:ℝ)/Real.log 2:ℝ):ℂ)*I := by push_cast; ring
    rw [hc, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero]
    norm_num
    ring
  rw [liClockPairedEtaDyadicReciprocal, if_neg hk, norm_inv, inv_pow,
    hnorm, inv_eq_one_div]
  have ht : 0 < (2*Real.pi*(k:ℝ)/Real.log 2)^2 := sq_pos_of_ne_zero (by positivity)
  calc
    _ ≤ 1/(2*Real.pi*(k:ℝ)/Real.log 2)^2 :=
      one_div_le_one_div_of_le ht (by linarith)
    _ = _ := by field_simp; ring

theorem summable_liClockPairedEtaDyadicReciprocal_norm_sq : Summable (fun k : ℤ => ‖liClockPairedEtaDyadicReciprocal k‖^2) := by
  exact (((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)).mul_left
    ((Real.log 2)^2/(4*Real.pi^2))).of_nonneg_of_le
      (fun _ => sq_nonneg _) liClockPairedEtaDyadicReciprocal_norm_sq_le

private theorem tsum_int_reciprocal_square :
    (∑' k : ℤ, (1:ℝ)/(k:ℝ)^2) = Real.pi^2/3 := by
  have hs := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hp := (summable_nat_add_iff 1).2 hs
  have hneg (n : ℕ) : (1:ℝ)/((-(n:ℤ)-1:ℤ):ℝ)^2 = 1/((n:ℝ)+1)^2 := by
    push_cast
    congr 1
    ring
  have hp' : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  have hn : Summable (fun n : ℕ => (1:ℝ)/((-(n:ℤ)-1:ℤ):ℝ)^2) := hp'.congr (fun n => (hneg n).symm)
  rw [tsum_of_add_one_of_neg_add_one (f := fun k : ℤ => (1:ℝ)/(k:ℝ)^2)
    (by simpa using hp) (by simpa [neg_add_rev, sub_eq_add_neg, add_comm] using hn)]
  have heq (n : ℕ) : (1:ℝ)/((-((n:ℤ)+1):ℤ):ℝ)^2 = 1/((n:ℝ)+1)^2 := by
    push_cast
    rw [even_two.neg_pow]
  simp_rw [heq]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_zero,
    zero_pow (by norm_num : (2:ℕ) ≠ 0), div_zero, add_zero]
  have hsum : (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^2) = Real.pi^2/6 := by
    have hh := hs.sum_add_tsum_nat_add 1
    have hh' : (∑' n : ℕ, (1:ℝ)/((n:ℝ)+1)^2) = ∑' n : ℕ, (1:ℝ)/(n:ℝ)^2 := by simpa using hh
    exact hh'.trans hasSum_zeta_two.tsum_eq
  rw [hsum]
  ring

theorem liClockPairedEtaDyadicReciprocal_square_mass_le :
    (∑' k : ℤ, ‖liClockPairedEtaDyadicReciprocal k‖^2) ≤ 3/64 := by
  calc
    _ ≤ ∑' k : ℤ, (Real.log 2)^2/(4*Real.pi^2) * (1/(k:ℝ)^2) :=
      Summable.tsum_le_tsum liClockPairedEtaDyadicReciprocal_norm_sq_le summable_liClockPairedEtaDyadicReciprocal_norm_sq
        (((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)).mul_left _)
    _ = (Real.log 2)^2/12 := by
      rw [tsum_mul_left, tsum_int_reciprocal_square]
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ 3/64 := by nlinarith [log_two_pos, log_two_lt]

theorem liClockPairedEtaDyadicReciprocal_norm_sq_le_one_sixtyfourth (k : ℤ) :
    ‖liClockPairedEtaDyadicReciprocal k‖^2 ≤ 1/64 := by
  by_cases hk : k = 0
  · subst k; simp [liClockPairedEtaDyadicReciprocal]
  have hk1 : 1 ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hk2 : 1 ≤ (k:ℝ)^2 := by nlinarith [sq_abs (k:ℝ)]
  have hfrac : (1:ℝ)/(k:ℝ)^2 ≤ 1 := (div_le_one (by positivity)).2 hk2
  calc
    _ ≤ (Real.log 2)^2/(4*Real.pi^2)*(1/(k:ℝ)^2) := liClockPairedEtaDyadicReciprocal_norm_sq_le k
    _ ≤ (Real.log 2)^2/(4*Real.pi^2) := by
      exact (mul_le_mul_of_nonneg_left hfrac (by positivity)).trans_eq (mul_one _)
    _ ≤ 1/64 := by
      rw [div_le_iff₀ (by positivity : 0 < 4*Real.pi^2)]
      nlinarith [Real.pi_gt_three, log_two_pos, log_two_lt]

theorem liClockPairedEtaDyadicReciprocal_pow_norm_le (k : ℤ) (j : ℕ) :
    ‖liClockPairedEtaDyadicReciprocal k^(2*j+2)‖ ≤
      ‖liClockPairedEtaDyadicReciprocal k‖^2*(1/64:ℝ)^j := by
  rw [norm_pow, show 2*j+2=2*(j+1) by omega,pow_mul,pow_succ]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (sq_nonneg _) (liClockPairedEtaDyadicReciprocal_norm_sq_le_one_sixtyfourth k) j)
    (sq_nonneg ‖liClockPairedEtaDyadicReciprocal k‖)

theorem summable_liClockPairedEtaDyadicReciprocal_pow (j : ℕ) :
    Summable (fun k : ℤ => liClockPairedEtaDyadicReciprocal k^(2*j+2)) := by
  apply summable_norm_iff.mp
  exact (summable_liClockPairedEtaDyadicReciprocal_norm_sq.mul_right ((1/64:ℝ)^j)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun k => liClockPairedEtaDyadicReciprocal_pow_norm_le k j)

theorem liClockPairedEtaDyadicMoment_norm_le (j : ℕ) :
    ‖∑' k : ℤ, liClockPairedEtaDyadicReciprocal k^(2*j+2)‖ ≤ 3*(1/64:ℝ)^(j+1) := by
  calc
    _ ≤ ∑' k : ℤ, ‖liClockPairedEtaDyadicReciprocal k^(2*j+2)‖ :=
      norm_tsum_le_tsum_norm (summable_liClockPairedEtaDyadicReciprocal_pow j).norm
    _ ≤ ∑' k : ℤ, ‖liClockPairedEtaDyadicReciprocal k‖^2*(1/64:ℝ)^j :=
      Summable.tsum_le_tsum (fun k => liClockPairedEtaDyadicReciprocal_pow_norm_le k j)
        (summable_liClockPairedEtaDyadicReciprocal_pow j).norm (summable_liClockPairedEtaDyadicReciprocal_norm_sq.mul_right _)
    _ = (∑' k : ℤ, ‖liClockPairedEtaDyadicReciprocal k‖^2)*(1/64:ℝ)^j := tsum_mul_right
    _ ≤ (3/64)*(1/64:ℝ)^j := mul_le_mul_of_nonneg_right liClockPairedEtaDyadicReciprocal_square_mass_le (by positivity)
    _ = _ := by rw [pow_succ]; ring

def liClockPairedEtaGammaReciprocal (n : ℕ) : ℝ := (2*(n:ℝ)+5/2)⁻¹

theorem liClockPairedEtaGammaReciprocal_nonneg (n : ℕ) : 0 ≤ liClockPairedEtaGammaReciprocal n := by
  unfold liClockPairedEtaGammaReciprocal
  positivity

theorem liClockPairedEtaGammaReciprocal_le_two_fifths (n : ℕ) : liClockPairedEtaGammaReciprocal n ≤ 2/5 := by
  unfold liClockPairedEtaGammaReciprocal
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  calc
    _ ≤ (5/2:ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by norm_num)).2 (by linarith)
    _ = _ := by norm_num

theorem summable_liClockPairedEtaGammaReciprocal_square : Summable (fun n : ℕ => liClockPairedEtaGammaReciprocal n^2) := by
  have hs : Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
    have h := (summable_nat_add_iff 1).2 hasSum_zeta_two.summable
    simpa only [Nat.cast_add,Nat.cast_one] using h
  apply hs.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro n
  unfold liClockPairedEtaGammaReciprocal
  rw [inv_pow,inv_eq_one_div]
  apply one_div_le_one_div_of_le (by positivity)
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith

theorem summable_liClockPairedEtaGammaReciprocal_pow (j : ℕ) :
    Summable (fun n : ℕ => liClockPairedEtaGammaReciprocal n^(2*j+2)) := by
  apply (summable_liClockPairedEtaGammaReciprocal_square.mul_right ((4/25:ℝ)^j)).of_nonneg_of_le
    (fun n => pow_nonneg (liClockPairedEtaGammaReciprocal_nonneg n) _)
  intro n
  rw [show 2*j+2=2*(j+1) by omega,pow_mul,pow_succ]
  have hsq : liClockPairedEtaGammaReciprocal n^2 ≤ 4/25 := by
    nlinarith [liClockPairedEtaGammaReciprocal_nonneg n,liClockPairedEtaGammaReciprocal_le_two_fifths n]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) hsq j)
    (sq_nonneg (liClockPairedEtaGammaReciprocal n))

def liClockPairedEtaCompletionMoment (j : ℕ) : ℂ :=
  ((∑' n : ℕ, liClockPairedEtaGammaReciprocal n^(2*j+2)):ℝ)+
    ∑' k : ℤ, liClockPairedEtaDyadicReciprocal k^(2*j+2)

theorem liClockPairedEtaCompletionMoment_re_lower (j : ℕ) :
    (4/25:ℝ)^(j+1)-3*(1/64:ℝ)^(j+1) ≤ (liClockPairedEtaCompletionMoment j).re := by
  have hfirst : (4/25:ℝ)^(j+1) ≤ ∑' n : ℕ, liClockPairedEtaGammaReciprocal n^(2*j+2) := by
    have hh := (summable_liClockPairedEtaGammaReciprocal_pow j).le_tsum 0
      (fun n _ => pow_nonneg (liClockPairedEtaGammaReciprocal_nonneg n) _)
    have he : liClockPairedEtaGammaReciprocal 0^(2*j+2) = (4/25:ℝ)^(j+1) := by
      unfold liClockPairedEtaGammaReciprocal
      simp only [Nat.cast_zero,mul_zero,zero_add]
      rw [show 2*j+2=2*(j+1) by omega,pow_mul]
      norm_num
    rw [he] at hh
    exact hh
  have hnorm := liClockPairedEtaDyadicMoment_norm_le j
  have hneg := (abs_le.mp (Complex.abs_re_le_norm
    (∑' k : ℤ, liClockPairedEtaDyadicReciprocal k^(2*j+2)))).1
  unfold liClockPairedEtaCompletionMoment
  simp only [Complex.add_re,Complex.ofReal_re]
  linarith
end
end RHTower

open Complex Set Filter Topology RiemannGaussian
namespace RHTower
noncomputable section
private def dyadicAffine (s : ℂ) : ℂ :=
  I*(Real.log 2:ℂ)*(1-s)/(2*(Real.pi:ℂ))

theorem neg_pairedEtaFactorLogDerivative_eq_cot {s : ℂ} (hs : s.re < 1) :
    -pairedEtaFactorLogDerivative s = (Real.log 2:ℂ)/2+
      ((Real.log 2:ℂ)*I/(2*(Real.pi:ℂ)))*
        ((Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*dyadicAffine s)) := by
  have htwo : (2:ℂ) ≠ 0 := by norm_num
  have hlog : Complex.log 2 = (Real.log 2:ℂ) := by
    simp only [← Complex.ofReal_ofNat, Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
  have hexp : Complex.exp (2*(Real.pi:ℂ)*I*dyadicAffine s) = (2:ℂ)^(s-1) := by
    rw [Complex.cpow_def_of_ne_zero htwo, hlog]
    congr 1
    dsimp [dyadicAffine]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring_nf
    norm_num [Complex.I_sq]
  have hprod : (2:ℂ)^(s-1)*(2:ℂ)^(1-s) = 1 := by
    rw [← Complex.cpow_add _ _ htwo, show s-1+(1-s) = 0 by ring, Complex.cpow_zero]
  have hden : 1-(2:ℂ)^(s-1) ≠ 0 := by
    intro hh
    have hone : (2:ℂ)^(s-1) = 1 := (sub_eq_zero.mp hh).symm
    rw [hone, one_mul] at hprod
    have hf := pairedEtaFactor_ne_zero_of_re_lt_one hs
    apply hf
    have hr : 2*(2:ℂ)^(-s) = (2:ℂ)^(1-s) := by
      calc
        _ = (2:ℂ)^(1:ℂ)*(2:ℂ)^(-s) := by rw [Complex.cpow_one]
        _ = _ := by rw [← Complex.cpow_add _ _ htwo]; congr 1
    rw [hr, hprod]
    ring
  rw [pairedEtaFactorLogDerivative_eq_neg_log_two_div_one_sub_cpow hs,
    hlog, Complex.cot_pi_eq_exp_ratio, hexp]
  field_simp [hden, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf

theorem iteratedDeriv_neg_pairedEtaFactorLogDerivative_odd (j : ℕ) :
    iteratedDeriv (2*j+1) (fun s => -pairedEtaFactorLogDerivative s) (1/2:ℂ) =
      ((2*j+1).factorial:ℂ)*∑' k : ℤ,
        (1/2 + 2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ))⁻¹^(2*j+2) := by
  let l : ℂ := (Real.log 2:ℂ)
  let a : ℂ := -I*l/(2*(Real.pi:ℂ))
  let b : ℂ := I*l/(2*(Real.pi:ℂ))
  let x : ℂ := a*(1/2)+b
  let f : ℂ → ℂ := fun w => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*w)
  have hx : x ∈ UpperHalfPlane.upperHalfPlaneSet := by
    have hx' : x = ((Real.log 2/(4*Real.pi):ℝ):ℂ)*I := by
      dsimp [x,a,b,l]
      push_cast
      ring
    rw [hx']
    change 0 < (((Real.log 2/(4*Real.pi):ℝ):ℂ)*I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    positivity
  have hf : ContDiffAt ℂ (2*j+1) f x := by
    have hi := UpperHalfPlane.coe_mem_integerComplement ⟨x,hx⟩
    have hh : ContDiffWithinAt ℂ (2*j+1) f UpperHalfPlane.upperHalfPlaneSet x :=
      contDiffWithinAt_const.mul (cot_pi_mul_contDiffWithinAt (2*j+1) hi)
    exact hh.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hx)
  have hcot : iteratedDeriv (2*j+1) f x =
      (-1:ℂ)^(2*j+1)*((2*j+1).factorial:ℂ)*
        ∑' k : ℤ, 1/(x+(k:ℂ))^(2*j+2) := by
    rw [← iteratedDerivWithin_eq_iteratedDeriv
      UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn hf hx]
    simpa only [Nat.add_assoc] using
      iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 2*j+1) (by omega) hx
  have heq : (fun s : ℂ => -pairedEtaFactorLogDerivative s) =ᶠ[𝓝 (1/2:ℂ)]
      (fun s => l/2+(-a)*f (a*s+b)) := by
    have hlt : ∀ᶠ s : ℂ in 𝓝 (1/2:ℂ), s.re < 1 :=
      (Complex.continuous_re.continuousAt.eventually_lt_const (by norm_num))
    filter_upwards [hlt] with s hs
    rw [neg_pairedEtaFactorLogDerivative_eq_cot hs]
    change l/2+(l*I/(2*(Real.pi:ℂ)))*f (dyadicAffine s) = _
    have hcoef : l*I/(2*(Real.pi:ℂ)) = -a := by dsimp [a]; ring
    have haff : dyadicAffine s = a*s+b := by dsimp [dyadicAffine,a,b,l]; ring
    rw [hcoef,haff]
  rw [heq.iteratedDeriv_eq (2*j+1), iteratedDeriv_const_add (by omega),
    iteratedDeriv_const_mul_field, GaloisForLFunctions.liClock_iteratedDeriv_comp_affine, hcot]
  have hsign : (-1:ℂ)^(2*j+1) = -1 := by rw [pow_add,pow_mul]; norm_num
  rw [hsign]
  have hl : l ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha : a ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hl)
      (mul_ne_zero (by norm_num) hp)
  have hterm (k : ℤ) : a^(2*j+2)*(1/(x+(k:ℂ))^(2*j+2)) =
      (1/2 + 2*(Real.pi:ℂ)*I*(-(k:ℂ))/(Real.log 2:ℂ))⁻¹^(2*j+2) := by
    have hh : x+(k:ℂ) = (-a)*(1/2+2*(Real.pi:ℂ)*I*(-(k:ℂ))/(Real.log 2:ℂ)) := by
      change x+(k:ℂ) = (-a)*(1/2+2*(Real.pi:ℂ)*I*(-(k:ℂ))/l)
      dsimp [x,a,b]
      field_simp [hl,hp]
      ring_nf
      norm_num [Complex.I_sq]
    rw [hh,mul_pow,show (-a)^(2*j+2)=a^(2*j+2) by
      rw [show 2*j+2=2*(j+1) by omega,pow_mul,even_two.neg_pow,pow_mul]]
    rw [one_div, mul_inv_rev, mul_comm, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ ha), mul_one, inv_pow]
  calc
    (-a)*(a^(2*j+1)*((-1)*((2*j+1).factorial:ℂ)*
        ∑' k : ℤ, 1/(x+(k:ℂ))^(2*j+2))) =
        ((2*j+1).factorial:ℂ)*(a^(2*j+2)*∑' k : ℤ, 1/(x+(k:ℂ))^(2*j+2)) := by
      rw [show 2*j+2=(2*j+1)+1 by omega,pow_succ]
      ring
    _ = ((2*j+1).factorial:ℂ)*∑' k : ℤ,
        (1/2+2*(Real.pi:ℂ)*I*(-(k:ℂ))/(Real.log 2:ℂ))⁻¹^(2*j+2) := by
      rw [← tsum_mul_left]
      congr 1
      exact tsum_congr hterm
    _ = _ := by
      congr 1
      simpa only [Equiv.neg_apply, Int.cast_neg] using
        (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
          (1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ))⁻¹^(2*j+2))
end
end RHTower

open Complex Set Metric Filter Topology MeasureTheory RiemannGaussian
namespace RHTower
noncomputable section
def liClockPairedEtaCompletionSourceTrace (z : ℂ) : ℂ :=
  I * logDeriv pairedEtaXiCompletionFactor (1/2+z*I)
def liClockPairedEtaCompletionClockResponse (r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour liClockPairedEtaCompletionSourceTrace r t
def liClockPairedEtaPartitionSourceTrace (N : ℕ) (z : ℂ) : ℂ :=
  I * logDeriv (pairedEtaFiniteLaplacePartition N) (1/2+z*I)
def liClockPairedEtaPartitionClockResponse (N : ℕ) (r : ℝ) (t : ℂ) : ℂ :=
  liClockCentralTraceSineContour (liClockPairedEtaPartitionSourceTrace N) r t

theorem analyticAt_liClockPairedEtaCompletionSourceTrace {z : ℂ}
    (hl : 0 < (1/2+z*I).re) (hu : (1/2+z*I).re < 1) :
    AnalyticAt ℂ liClockPairedEtaCompletionSourceTrace z := by
  have ha := analyticAt_pairedEtaXiCompletionFactor hl hu
  have hg := ha.deriv.div ha (pairedEtaXiCompletionFactor_ne_zero hl hu)
  have hc : AnalyticAt ℂ (fun w : ℂ => 1/2+w*I) z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  change AnalyticAt ℂ (fun w : ℂ => I*logDeriv pairedEtaXiCompletionFactor (1/2+w*I)) z
  exact analyticAt_const.mul (hg.comp (f := fun w : ℂ => 1/2+w*I) hc)

private theorem strip {r : ℝ} (hr : r < 1/2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    0 < (1/2+z*I).re ∧ (1/2+z*I).re < 1 := by
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have heq : (1/2+z*I).re = (1/2:ℝ)-z.im := by
    norm_num [Complex.add_re, Complex.mul_re]
    ring
  rw [heq]
  constructor <;> linarith

theorem diffContOnCl_liClockPairedEtaCompletionSourceTrace {r : ℝ} (hr : r < 1/2) :
    DiffContOnCl ℂ liClockPairedEtaCompletionSourceTrace (ball 0 r) := by
  have ha : AnalyticOnNhd ℂ liClockPairedEtaCompletionSourceTrace (closedBall 0 r) := by
    intro z hz
    have hh := strip hr (show ‖z‖ ≤ r by simpa only [mem_closedBall, dist_zero_right] using hz)
    exact analyticAt_liClockPairedEtaCompletionSourceTrace hh.1 hh.2
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)

theorem liClockPairedEtaFiniteDeflatedSourceTrace_eq_partition_add_completion (N : ℕ) {z : ℂ}
    (hl : 0 < (1/2+z*I).re) (hu : (1/2+z*I).re < 1)
    (heta : pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) :
    liClockPairedEtaFiniteDeflatedSourceTrace N z =
      liClockPairedEtaPartitionSourceTrace N z+liClockPairedEtaCompletionSourceTrace z := by
  let s : ℂ := 1/2+z*I
  have hs : s ≠ 0 := by
    intro hh; have hp : 0 < s.re := hl; rw [hh] at hp; norm_num at hp
  have hL : pairedEtaFiniteLaplacePartition N s ≠ 0 := by
    intro hh
    have hE := pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition N s
    rw [hh, mul_zero] at hE
    exact heta hE
  unfold liClockPairedEtaFiniteDeflatedSourceTrace liClockPairedEtaPartitionSourceTrace
    liClockPairedEtaCompletionSourceTrace
  rw [logDeriv_mul (f := pairedEtaXiCompletionFactor)
    (g := pairedEtaFiniteLaplacePartition N) s (pairedEtaXiCompletionFactor_ne_zero hl hu)
    hL (analyticAt_pairedEtaXiCompletionFactor hl hu).differentiableAt
      (analyticAt_liClockPairedEtaFiniteLaplacePartition hs).differentiableAt]
  ring

private theorem contour_add {r : ℝ} (hr : 0 < r) {T U : ℂ → ℂ}
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
    intro z _; dsimp only; ring
  unfold liClockCentralTraceSineContour
  rw [hi]
  ring

theorem liClockPairedEtaFiniteDeflatedClockResponse_eq_partition_add_completion
    (N : ℕ) {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (heta : ∀z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) (t : ℂ) :
    liClockPairedEtaFiniteDeflatedClockResponse N r t =
      liClockPairedEtaPartitionClockResponse N r t+liClockPairedEtaCompletionClockResponse r t := by
  have hstrip (z : ℂ) (hz : z ∈ sphere (0:ℂ) r) :
      0 < (1/2+z*I).re ∧ (1/2+z*I).re < 1 := strip hrhalf
      (show ‖z‖ ≤ r by exact (show ‖z‖ = r by simpa only [mem_sphere_iff_norm, sub_zero] using hz).le)
  have hD : ContinuousOn (liClockPairedEtaFiniteDeflatedSourceTrace N) (sphere 0 r) := by
    intro z hz
    exact (analyticAt_liClockPairedEtaFiniteDeflatedSourceTrace N
      (hstrip z hz).1 (hstrip z hz).2 (heta z hz)).continuousAt.continuousWithinAt
  have hC : ContinuousOn liClockPairedEtaCompletionSourceTrace (sphere 0 r) :=
    (diffContOnCl_liClockPairedEtaCompletionSourceTrace hrhalf).continuousOn_ball.mono sphere_subset_closedBall
  have heq : ∀z ∈ sphere (0:ℂ) r, liClockPairedEtaFiniteDeflatedSourceTrace N z =
      liClockPairedEtaPartitionSourceTrace N z+liClockPairedEtaCompletionSourceTrace z := by
    intro z hz
    exact liClockPairedEtaFiniteDeflatedSourceTrace_eq_partition_add_completion N
      (hstrip z hz).1 (hstrip z hz).2 (heta z hz)
  have hP : ContinuousOn (liClockPairedEtaPartitionSourceTrace N) (sphere 0 r) := by
    have hh : EqOn (liClockPairedEtaPartitionSourceTrace N)
        (fun z => liClockPairedEtaFiniteDeflatedSourceTrace N z-liClockPairedEtaCompletionSourceTrace z)
        (sphere 0 r) := by intro z hz; have := heq z hz; linear_combination -this
    exact (hD.sub hC).congr hh
  have hc : liClockPairedEtaFiniteDeflatedClockResponse N r t =
      liClockCentralTraceSineContour (fun z => liClockPairedEtaPartitionSourceTrace N z+
        liClockPairedEtaCompletionSourceTrace z) r t := by
    unfold liClockPairedEtaFiniteDeflatedClockResponse liClockCentralTraceSineContour
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz; dsimp only; rw [heq z hz]
  rw [hc, contour_add hr hP hC]
  rfl

theorem liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_partition_add_completion
    (N : ℕ) {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (heta : ∀z ∈ sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I) ≠ 0) (t : ℂ) :
    liClockPairedEtaFiniteClockResponse N r t = -2*Complex.sinh (2*t)+
      liClockPairedEtaPartitionClockResponse N r t+liClockPairedEtaCompletionClockResponse r t := by
  rw [liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_deflated N hr hrhalf heta,
    liClockPairedEtaFiniteDeflatedClockResponse_eq_partition_add_completion N hr hrhalf heta]
  ring
end
end RHTower
open GaloisForLFunctions Complex Set Filter Topology RiemannGaussian
namespace RHTower
noncomputable section

theorem logDeriv_pairedEtaXiCompletionFactor_eq_filled_connection {s : ℂ}
    (hl : 0 < s.re) (hu : s.re < 1) :
    logDeriv pairedEtaXiCompletionFactor s =
      gammaRealLogConnection (s+2)+(1/(s-1)-pairedEtaFactorLogDerivative s) := by
  rw [logDeriv_pairedEtaXiCompletionFactor hl hu]
  unfold pairedEtaArithmeticXiRegularCorrection gammaRealLogConnection
  rw [← Complex.ofReal_log Real.pi_pos.le]
  rw [show (s+2)/2=1+s/2 by ring, digamma_half_eq_shifted_sub_two_div hl]
  ring

private theorem completion_rational_odd (j : ℕ) :
    iteratedDeriv (2*j+1) (fun s : ℂ => 1/(s-1)) (1/2:ℂ) =
      -((2*j+1).factorial:ℂ)*(2:ℂ)^(2*j+2) := by
  have heq : (fun s : ℂ => 1/(s-1)) = fun s => (1*s-1)⁻¹ := by funext s; simp
  rw [heq,iteratedDeriv_eq_iterate,iter_deriv_inv_linear_sub]
  simp only [one_mul,one_pow,mul_one]
  have hpoint : ((1/2:ℂ)-1) = -(1/2:ℂ) := by norm_num
  rw [hpoint]
  have he : (-1-(2*j+1:ℕ):ℤ) = -((2*j+2:ℕ):ℤ) := by omega
  rw [he,zpow_neg,zpow_natCast,← inv_pow]
  have hinv : (-(1/2:ℂ))⁻¹ = -2 := by norm_num
  rw [hinv]
  have hs : (-1:ℂ)^(2*j+1) = -1 := by rw [pow_add,pow_mul]; norm_num
  have hp : (-2:ℂ)^(2*j+2) = (2:ℂ)^(2*j+2) := by
    rw [show 2*j+2=2*(j+1) by omega,pow_mul,even_two.neg_pow,pow_mul]
  rw [hs,hp]
  ring

private theorem analytic_filled_gamma :
    AnalyticAt ℂ (fun s => gammaRealLogConnection (s+2)) (1/2:ℂ) := by
  have hd : AnalyticAt ℂ Complex.digamma (((1/2:ℂ)+2)/2) := by
    apply analyticAt_digamma_of_offPoles
    intro p hp
    have hh := congrArg Complex.re hp
    norm_num at hh
    have hn : 0 ≤ (p:ℝ) := Nat.cast_nonneg p
    linarith
  have ha : AnalyticAt ℂ (fun s : ℂ => (s+2)/2) (1/2:ℂ) :=
    (analyticAt_id.add analyticAt_const).div_const
  unfold gammaRealLogConnection
  exact analyticAt_const.add ((hd.comp (f := fun s : ℂ => (s+2)/2) ha).div_const)

private theorem analytic_negative_eta_factor :
    AnalyticAt ℂ (fun s => -pairedEtaFactorLogDerivative s) (1/2:ℂ) := by
  have hd : Differentiable ℂ pairedEtaFactor := fun s => (hasDerivAt_pairedEtaFactor s).differentiableAt
  have ha := hd.analyticAt (1/2:ℂ)
  have hh := (ha.deriv.div ha (pairedEtaFactor_ne_zero_of_re_lt_one (by norm_num : (1/2:ℂ).re<1))).neg
  change AnalyticAt ℂ (fun s => -logDeriv pairedEtaFactor s) (1/2:ℂ) at hh
  have he : (fun s => -logDeriv pairedEtaFactor s) =
      (fun s => -pairedEtaFactorLogDerivative s) := by funext s; rw [logDeriv_pairedEtaFactor]
  rw [he] at hh
  exact hh

private theorem dyadic_full_moment_eq (j : ℕ) :
    (∑' k : ℤ, (1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ))⁻¹^(2*j+2)) =
      (2:ℂ)^(2*j+2)+∑' k : ℤ,liClockPairedEtaDyadicReciprocal k^(2*j+2) := by
  let f : ℤ → ℂ := fun k => (1/2+2*(Real.pi:ℂ)*I*(k:ℂ)/(Real.log 2:ℂ))⁻¹^(2*j+2)
  have he (k : ℤ) : f k = (if k=0 then (2:ℂ)^(2*j+2) else 0)+
      liClockPairedEtaDyadicReciprocal k^(2*j+2) := by
    by_cases hk : k=0
    · subst k; simp [f,liClockPairedEtaDyadicReciprocal]
    · simp [f,liClockPairedEtaDyadicReciprocal,hk]
  have hs : Summable f := by
    exact ((hasSum_ite_eq (0:ℤ) ((2:ℂ)^(2*j+2))).summable.add
      (summable_liClockPairedEtaDyadicReciprocal_pow j)).congr (fun k => (he k).symm)
  have hh := hs.tsum_eq_add_tsum_ite 0
  change (∑' k : ℤ,f k) = _
  rw [hh]
  congr 1
  · simp [f]
  · apply tsum_congr
    intro k
    by_cases hk : k=0 <;> simp [f,liClockPairedEtaDyadicReciprocal,hk]

theorem iteratedDeriv_logDeriv_pairedEtaXiCompletionFactor_odd (j : ℕ) :
    iteratedDeriv (2*j+1) (logDeriv pairedEtaXiCompletionFactor) (1/2:ℂ) =
      ((2*j+1).factorial:ℂ)*liClockPairedEtaCompletionMoment j := by
  have heq : logDeriv pairedEtaXiCompletionFactor =ᶠ[𝓝 (1/2:ℂ)]
      (fun s => gammaRealLogConnection (s+2)+(1/(s-1)+ -pairedEtaFactorLogDerivative s)) := by
    have hl : ∀ᶠ s : ℂ in 𝓝 (1/2:ℂ),0<s.re :=
      Complex.continuous_re.continuousAt.eventually_const_lt (by norm_num)
    have hu : ∀ᶠ s : ℂ in 𝓝 (1/2:ℂ),s.re<1 :=
      Complex.continuous_re.continuousAt.eventually_lt_const (by norm_num)
    filter_upwards [hl,hu] with s hsl hsu
    exact logDeriv_pairedEtaXiCompletionFactor_eq_filled_connection hsl hsu
  have hP : AnalyticAt ℂ (fun s : ℂ => 1/(s-1)) (1/2:ℂ) :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)
  rw [heq.iteratedDeriv_eq (2*j+1)]
  change iteratedDeriv (2*j+1) ((fun s => gammaRealLogConnection (s+2))+
    ((fun s => 1/(s-1))+(fun s => -pairedEtaFactorLogDerivative s))) (1/2:ℂ) = _
  rw [iteratedDeriv_add analytic_filled_gamma.contDiffAt
    (hP.add analytic_negative_eta_factor).contDiffAt,
    iteratedDeriv_add hP.contDiffAt analytic_negative_eta_factor.contDiffAt,
    completion_rational_odd,iteratedDeriv_neg_pairedEtaFactorLogDerivative_odd,
    dyadic_full_moment_eq,liClock_gammaRealLogConnection_filled_odd]
  have hg : (∑' n : ℕ, (2*(n:ℂ)+5/2)^(-((2*j+2:ℕ):ℤ))) =
      (((∑' n : ℕ,liClockPairedEtaGammaReciprocal n^(2*j+2)):ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [zpow_neg,zpow_natCast,← inv_pow]
    unfold liClockPairedEtaGammaReciprocal
    push_cast
    rfl
  rw [hg]
  unfold liClockPairedEtaCompletionMoment
  ring

theorem iteratedDeriv_liClockPairedEtaCompletionSourceTrace_odd (j : ℕ) :
    iteratedDeriv (2*j+1) liClockPairedEtaCompletionSourceTrace 0 =
      (-1:ℂ)^(j+1)*((2*j+1).factorial:ℂ)*liClockPairedEtaCompletionMoment j := by
  unfold liClockPairedEtaCompletionSourceTrace
  have hc : (fun z : ℂ => logDeriv pairedEtaXiCompletionFactor (1/2+z*I)) =
      (fun z => logDeriv pairedEtaXiCompletionFactor (I*z+1/2)) := by funext z; congr 1; ring
  rw [iteratedDeriv_const_mul_field,hc]
  change I*iteratedDeriv (2*j+1) (fun z => logDeriv pairedEtaXiCompletionFactor (I*z+1/2)) 0 = _
  rw [liClock_iteratedDeriv_comp_affine]
  simp only [mul_zero,zero_add]
  rw [iteratedDeriv_logDeriv_pairedEtaXiCompletionFactor_odd]
  have hi : (I:ℂ)*(I:ℂ)^(2*j+1) = (-1:ℂ)^(j+1) := by
    rw [← pow_succ',show 2*j+1+1=2*(j+1) by omega,pow_mul,Complex.I_sq]
  rw [← mul_assoc,← mul_assoc,hi]

end
end RHTower
