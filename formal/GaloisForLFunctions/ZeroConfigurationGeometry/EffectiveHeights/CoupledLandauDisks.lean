import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LandauTangentDisks
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.RHTower.PolePurchaseLogDerivIdentity
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.MultiplicativePositivityGeometry.ZetaBoundaryDivisor

/-!
# Coupled zero counts at a height and its double

Broucke–Révész's disk comparison retains the whole divisor in the
de la Vallée Poussin inequality. Each zero near `1+it` costs four
units and each zero near `1+2it` costs one. At a common explicit radius
the two disks cannot both be occupied. Multiplicities enter throughout.
-/

noncomputable section
open Complex RHTower
namespace GaloisForLFunctions.ZeroConfigurationGeometry.Landau

private theorem inv_re_le_half {s : ℂ} (hs : 0 < s.im) : (s⁻¹).re ≤ 1/(2*s.im) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  have hn : 0 < s.re*s.re + s.im*s.im :=
    add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_pos hs hs)
  rw [div_le_div_iff₀ hn (by positivity)]
  nlinarith only [sq_nonneg (s.re-s.im)]

private def resolvent (σ t : ℝ) := (logDeriv xi ((σ : ℂ)+t*I)).re

/-- Real polar and gamma terms of the completed logarithmic derivative. -/
def archField (σ t : ℝ) : ℝ :=
  let s := (σ : ℂ)+t*I
  (s⁻¹ + (s-1)⁻¹ + logDeriv Complex.Gammaℝ s).re

open GaloisForLFunctions.MultiplicativePositivityGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem prime_field_split {h : ℝ} (hh : 0 < h) (v : ℝ) :
    zetaRealLogDeriv (1+h) v =
      archField (1+h) v - (logDeriv xi (((1+h : ℝ) : ℂ)+v*I)).re := by
  rw [zetaRealLogDeriv,Sieve.neg_div_re_eq_neg_logDeriv_re,
    logDeriv_xi_split (by simp; linarith : 1 < (((1+h : ℝ) : ℂ)+v*I).re),
    Complex.add_re,archField]
  ring

private theorem positive_prime_field {h : ℝ} (hh : 0 < h) :
    IsEvenPosDef (zetaRealLogDeriv (1+h)) := by
  have he := funext (zetaRealLogDeriv_eq_cosineTrace hh)
  rw [he]
  exact isEvenPosDef_cosineTrace (zetaBoundaryWeight_nonneg h) (summable_zetaBoundaryWeight hh) logFrequency

/-- On every finite difference set the archimedean matrix dominates the
full zero resolvent as a quadratic form. The difference is the Gram
matrix of the damped prime-power measure. The test weights may be signed. -/
theorem resolvent_gram_le {h : ℝ} (hh : 0 < h) {m : ℕ} (x c : Fin m → ℝ) :
    ∑ j, ∑ k, c j*c k*(logDeriv xi (((1+h : ℝ) : ℂ)+((x j-x k : ℝ) : ℂ)*I)).re ≤
    ∑ j, ∑ k, c j*c k*archField (1+h) (x j-x k) := by
  have hpd := (positive_prime_field hh).posDef m x c
  simp only [prime_field_split hh, mul_sub, Finset.sum_sub_distrib] at hpd
  exact sub_nonneg.mp hpd

/-- Nonnegative sampling weights convert the matrix bound into a joint
count of disks centered on every pairwise height difference. The radii
may vary independently in the interval from zero to the evaluation offset. -/
theorem difference_disk_count {h : ℝ} (hh : 0 < h) {m : ℕ} (x c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (r : Fin m → Fin m → ℝ)
    (hr : ∀ j k, r j k ∈ Set.Icc 0 h) :
    ∑ j, ∑ k, c j*c k*(((diskCopies 1 (x j-x k) (r j k)).card : ℝ)/(h+r j k)) ≤
    ∑ j, ∑ k, c j*c k*archField (1+h) (x j-x k) := by
  refine le_trans (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hc j) (hc k))) (resolvent_gram_le hh x c)
  rw [div_le_iff₀ (add_pos_of_pos_of_nonneg hh (hr j k).1), mul_comm]
  exact disk_count_le_resolvent (hr j k).1 (hr j k).2 (by linarith)

/-- The first two harmonics of the prime logarithmic derivative obey the
quadratic Toeplitz constraint. The middle coefficient in the three-point
test is chosen to minimize the Gram form. -/
theorem prime_double_gram {h : ℝ} (hh : 0 < h) (t : ℝ) :
    let f := zetaRealLogDeriv (1+h)
    2*(f t)^2 ≤ f 0*(f 0+f (2*t)) := by
  intro f
  have hf : IsEvenPosDef f := positive_prime_field hh
  rcases hf.apply_zero_nonneg.eq_or_lt with hz | hp
  · have ht := hf.abs_le_apply_zero t
    rw [← hz,abs_nonpos_iff] at ht
    rw [← hz,ht]
    norm_num
  · have he := hf.three_point t t (-2*f t) (f 0) (f 0)
    rw [← two_mul t] at he
    apply (mul_le_mul_iff_left₀ hp).mp
    linarith only [he]

/-- Nonlinear tradeoff between two disk occupancies. The positive excess
of the first disk over its archimedean budget is squared and must be paid
for by the remaining prime mass at the double height. -/
theorem quadratic_disk_count {h r v : ℝ} (hh : 0 < h) (t : ℝ)
    (hr : r ∈ Set.Icc 0 h) (hv : v ∈ Set.Icc 0 h) :
    let D := zetaRealLogDeriv (1+h) 0
    2*(max (((diskCopies 1 t r).card:ℝ)/(h+r)-archField (1+h) t) 0)^2 ≤
      D*(D+archField (1+h) (2*t)-((diskCopies 1 (2*t) v).card:ℝ)/(h+v)) := by
  intro D
  have hD : 0 ≤ D := (positive_prime_field hh).apply_zero_nonneg
  have hb (y w : ℝ) (hw : w ∈ Set.Icc 0 h) :
      ((diskCopies 1 y w).card:ℝ)/(h+w) ≤ archField (1+h) y-zetaRealLogDeriv (1+h) y := by
    rw [prime_field_split hh, sub_sub_cancel, div_le_iff₀ (add_pos_of_pos_of_nonneg hh hw.1), mul_comm]
    exact disk_count_le_resolvent hw.1 hw.2 (by linarith)
  have hmax : max (((diskCopies 1 t r).card:ℝ)/(h+r)-archField (1+h) t) 0 ≤ |zetaRealLogDeriv (1+h) t| :=
    max_le (le_trans (by linarith only [hb t r hr]) (neg_le_abs _)) (abs_nonneg _)
  have hs := sq_le_sq' (by linarith only [le_max_right (((diskCopies 1 t r).card:ℝ)/(h+r)-
    archField (1+h) t) 0,abs_nonneg (zetaRealLogDeriv (1+h) t)]) hmax
  rw [sq_abs] at hs
  have hg := prime_double_gram hh t
  change 2*(zetaRealLogDeriv (1+h) t)^2 ≤ D*(D+zetaRealLogDeriv (1+h) (2*t)) at hg
  refine (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2)).trans (hg.trans ?_)
  apply mul_le_mul_of_nonneg_left _ hD
  linarith only [hb (2*t) v hv]

private theorem arch_cost {σ t : ℝ} (hs : 1 < σ) (hs2 : σ ≤ 2) (ht : 4 ≤ t) :
    resolvent σ t + (-deriv riemannZeta ((σ : ℂ)+t*I) / riemannZeta ((σ : ℂ)+t*I)).re ≤
      Real.log t/2+1/2 := by
  let s : ℂ := (σ : ℂ)+t*I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs1im : (s-1).im = t := by simp [hsim]
  have hp := inv_re_le_half (s := s) (by rw [hsim]; linarith)
  have hp1 := inv_re_le_half (s := s-1) (by rw [hs1im]; linarith)
  rw [hsim] at hp
  rw [hs1im] at hp1
  have hb : 1/(2*t) ≤ (1:ℝ)/8 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have hg := re_logDeriv_Gammaℝ_le_half_log hs.le hs2 ht
  change (logDeriv xi s).re + (-deriv riemannZeta s / riemannZeta s).re ≤ _
  rw [Sieve.neg_div_re_eq_neg_logDeriv_re, logDeriv_xi_split (hsre.symm ▸ hs)]
  simp only [Complex.add_re]
  change (logDeriv Complex.Gammaℝ s).re ≤ _ at hg
  linarith only [hp.trans hb, hp1.trans hb, hg]

/-- Smooth cost at the two nonzero harmonics, including the real-axis
pole remainder. -/
def coupledCost (t : ℝ) := 5/2*Real.log t + dlvpHalfConstant 1

/-- Simultaneous resolvent bound retaining both positive zero measures. -/
theorem coupled_resolvent_bound {σ t : ℝ} (hs : 1 < σ) (hs2 : σ ≤ 2) (ht : 4 ≤ t) :
    4*(logDeriv xi ((σ : ℂ)+t*I)).re + (logDeriv xi ((σ : ℂ)+((2*t : ℝ) : ℂ)*I)).re ≤
      3/(σ-1)+coupledCost t := by
  have hfirst := arch_cost hs hs2 ht
  have hdouble := arch_cost hs hs2 (by linarith : 4 ≤ 2*t)
  have hreal := neg_re_logDeriv_riemannZeta_real_le hs hs2
  have hpos := vallee_poussin_log_deriv_nonneg hs t
  rw [Real.log_mul (by norm_num) (by linarith : t ≠ 0)] at hdouble
  dsimp only [resolvent] at hfirst hdouble
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hdouble hpos ⊢
  unfold coupledCost dlvpHalfConstant
  linarith only [hfirst, hdouble, hreal, hpos]

/-- Two different disk radii can be tested with the same observation offset. -/
theorem coupled_disk_count {t h r v : ℝ} (ht : 4 ≤ t) (hh : 0 < h) (hh1 : h ≤ 1)
    (hr : 0 ≤ r) (hrh : r ≤ h) (hv : 0 ≤ v) (hvh : v ≤ h) :
    4*((diskCopies 1 t r).card : ℝ)/(h+r) + ((diskCopies 1 (2*t) v).card : ℝ)/(h+v) ≤
      3/h+coupledCost t := by
  have hs : 1 < 1+h := by linarith
  have hs2 : 1+h ≤ 2 := by linarith
  have hcount (y w : ℝ) (hw : 0 ≤ w) (hwh : w ≤ h) :
      ((diskCopies 1 y w).card : ℝ)/(h+w) ≤ resolvent (1+h) y := by
    rw [div_le_iff₀ (by linarith : 0 < h+w), mul_comm]
    exact disk_count_le_resolvent hw hwh hs
  have h := coupled_resolvent_bound hs hs2 ht
  rw [add_sub_cancel_left] at h
  change 4 * resolvent _ _ + resolvent _ _ ≤ _ at h
  linarith only [hcount t r hr hrh, hcount (2*t) v hv hvh, h]

private theorem coupledCost_ge_three {t : ℝ} (ht : 4 ≤ t) : 3 ≤ coupledCost t := by
  unfold coupledCost dlvpHalfConstant
  linarith only [Real.log_nonneg (by linarith : 1 ≤ t), Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

/-- For radius `3u²/L` and offset `3u/L`, the weighted number of zeros
costs at most `3(1+u)²`, where `L = coupledCost t`. -/
theorem coupled_disk_count_optimized {t u : ℝ} (ht : 4 ≤ t) (hu : 0 < u) (hu1 : u ≤ 1) :
    let r := 3*u^2/coupledCost t
    4*((diskCopies 1 t r).card : ℝ) + ((diskCopies 1 (2*t) r).card : ℝ) ≤ 3*(1+u)^2 := by
  intro r
  let h := 3*u/coupledCost t
  have hL := coupledCost_ge_three ht
  have hL0 : 0 < coupledCost t := by linarith
  have hh : 0 < h := div_pos (by positivity) hL0
  have hh1 : h ≤ 1 := (div_le_one hL0).mpr (by linarith only [hu1,hL])
  have hr : 0 ≤ r := div_nonneg (by positivity) hL0.le
  have hrh : r ≤ h := div_le_div_of_nonneg_right
    (by nlinarith only [mul_nonneg hu.le (sub_nonneg.mpr hu1)]) hL0.le
  have hc := coupled_disk_count ht hh hh1 hr hrh hr hrh
  rw [← add_div, div_le_iff₀ (by linarith : 0 < h+r)] at hc
  refine hc.trans_eq ?_
  dsimp only [h, r]
  field_simp [hu.ne', hL0.ne'] <;> ring

/-- At the explicit radius `3/(16L)`, occupancy of the fundamental disk
forces the entire double-height disk to be empty. -/
theorem occupied_disk_excludes_double {t : ℝ} (ht : 4 ≤ t) :
    let r := 3/(16*coupledCost t)
    (diskCopies 1 t r).Nonempty → (diskCopies 1 (2*t) r) = ∅ := by
  intro r hn
  have hc := coupled_disk_count_optimized (u := 1/4) ht (by norm_num) (by norm_num)
  have he : 3*((1:ℝ)/4)^2/coupledCost t = r := by dsimp [r]; ring
  simp only [he] at hc
  have hlt : 4*(diskCopies 1 t r).card + (diskCopies 1 (2*t) r).card < 5 := by
    exact_mod_cast (hc.trans_lt (by norm_num : 3*(1+(1:ℝ)/4)^2 < 5))
  have hp := Finset.card_pos.mpr hn
  exact Finset.card_eq_zero.mp (by omega)

/-- Below the smaller radius `3/(49L)`, even one zero at the fundamental
height exceeds the combined pole and gamma budget. -/
theorem disk_empty_at_coupled_radius {t : ℝ} (ht : 4 ≤ t) :
    diskCopies 1 t (3/(49*coupledCost t)) = ∅ := by
  have hc := coupled_disk_count_optimized (u := 1/7) ht (by norm_num) (by norm_num)
  have he : 3*((1:ℝ)/7)^2/coupledCost t = 3/(49*coupledCost t) := by ring
  simp only [he] at hc
  have hlt : 4*(diskCopies 1 t (3/(49*coupledCost t))).card +
      (diskCopies 1 (2*t) (3/(49*coupledCost t))).card < 4 := by
    exact_mod_cast (hc.trans_lt (by norm_num : 3*(1+(1:ℝ)/7)^2 < 4))
  exact Finset.card_eq_zero.mp (by omega)

#print axioms coupled_resolvent_bound
#print axioms prime_double_gram
#print axioms quadratic_disk_count
#print axioms resolvent_gram_le
#print axioms difference_disk_count
#print axioms coupled_disk_count
#print axioms coupled_disk_count_optimized
#print axioms occupied_disk_excludes_double
#print axioms disk_empty_at_coupled_radius
end GaloisForLFunctions.ZeroConfigurationGeometry.Landau
