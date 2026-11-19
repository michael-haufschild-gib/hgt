import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LandauTangentDisks
import GaloisForLFunctions.RHTower.DigammaLeLog
import GaloisForLFunctions.RHTower.Sieve.FejerCorrelation
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
  have hs := pow_le_pow_left₀ (le_max_right _ 0) hmax 2
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
def coupledCost (t : ℝ) := 5/2*Real.log t + dlvpHalfConstant (-(1/5))

/-- Simultaneous resolvent bound retaining both positive zero measures. -/
theorem coupled_resolvent_bound {σ t : ℝ} (hs : 1 < σ) (hs2 : σ ≤ 2) (ht : 4 ≤ t) :
    4*(logDeriv xi ((σ : ℂ)+t*I)).re + (logDeriv xi ((σ : ℂ)+((2*t : ℝ) : ℂ)*I)).re ≤
      3/(σ-1)+coupledCost t := by
  have hfirst := arch_cost hs hs2 ht
  have hdouble := arch_cost hs hs2 (by linarith : 4 ≤ 2*t)
  have hreal := neg_re_logDeriv_riemannZeta_real_le_neg hs hs2
  have hpos := vallee_poussin_log_deriv_nonneg hs t
  rw [Real.log_mul (by norm_num) (by linarith : t ≠ 0)] at hdouble
  dsimp only [resolvent] at hfirst hdouble
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hdouble hpos ⊢
  unfold coupledCost dlvpHalfConstant
  rw [show 3/(σ-1) = 3*(1/(σ-1)) by ring]
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
  rw [mul_div_assoc]
  exact (add_le_add (mul_le_mul_of_nonneg_left (hcount t r hr hrh) (by norm_num))
    (hcount (2*t) v hv hvh)).trans h

private theorem coupledCost_ge_three {t : ℝ} (ht : 4 ≤ t) : 3 ≤ coupledCost t := by
  unfold coupledCost dlvpHalfConstant
  have h₂ := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have ht₂ := Real.log_le_log (by norm_num : (0:ℝ)<2) (by linarith : 2≤t)
  linarith only [h₂,ht₂]

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
  field_simp [hu.ne', hL0.ne']

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

/-- Total zero multiplicity over the positive absolute differences of
a sampling set. Repeated differences are counted once per ordered pair. -/
def differenceMultiplicity {m : ℕ} (x : Fin (m+1) → ℝ) (r : ℝ) : ℕ :=
  ∑ j, ∑ k ∈ Finset.univ.erase j, (diskCopies 1 |x j-x k| r).card

/-- Number of ordered pairs whose difference disk contains no zero. -/
def vacantDifferences {m : ℕ} (x : Fin (m+1) → ℝ) (r : ℝ) : ℕ :=
  ∑ j, ∑ k ∈ Finset.univ.erase j, if (diskCopies 1 |x j-x k| r).card=0 then 1 else 0

private theorem difference_count_or_vacancy {m : ℕ} (x : Fin (m+1) → ℝ) (r : ℝ) :
    (m+1)*m ≤ vacantDifferences x r + differenceMultiplicity x r := by
  simp only [vacantDifferences,differenceMultiplicity,←Finset.sum_add_distrib]
  have he : (m+1)*m = ∑ j : Fin (m+1), ∑ _k ∈ Finset.univ.erase j, (1:ℕ) := by simp
  rw [he]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> omega

/-- At separated sample heights the Gram inequality bounds the average
multiplicity over all difference disks. Only the diagonal pays the
real-axis pole; all other entries pay a logarithmic archimedean cost. -/
theorem difference_multiplicity_budget {m : ℕ} {T h r : ℝ} (x : Fin (m+1) → ℝ)
    (hx : ∀ j k, j≠k → |x j-x k| ∈ Set.Icc 4 T) (hh : 0<h) (hh₁ : h≤1)
    (hr : 0≤r) (hrh : r≤h) :
    (differenceMultiplicity x r : ℝ)/(h+r) ≤
      (m+1)*((m:ℝ)*(Real.log T/2+1/2)+1/h-1/5) := by
  let A := Real.log T/2+1/2
  let f := zetaRealLogDeriv (1+h)
  have hs : 1 < 1+h := by linarith
  have hs' : 1+h≤2 := by linarith
  have hpd := positive_prime_field hh
  have hf₀ : f 0 ≤ 1/h-1/5 := by
    simpa [f,zetaRealLogDeriv] using neg_re_logDeriv_riemannZeta_real_le_neg hs hs'
  have hsum : 0 ≤ ∑ j, ∑ k, f (x j-x k) := by
    simpa only [one_mul] using hpd.posDef (m+1) x (fun _ => 1)
  have hentry (j k : Fin (m+1)) (hn : j ≠ k) :
      ((diskCopies 1 |x j-x k| r).card:ℝ)/(h+r)+f (x j-x k) ≤ A := by
    have hu := hx j k hn
    have harch := arch_cost hs hs' hu.1
    have hcount := disk_count_le_resolvent (b := 1) (t := |x j-x k|) hr hrh hs
    have hker : ((diskCopies 1 |x j-x k| r).card:ℝ)/(h+r) ≤ resolvent (1+h) |x j-x k| :=
      (div_le_iff₀ (add_pos_of_pos_of_nonneg hh hr)).mpr (by simpa only [mul_comm] using hcount)
    have hf : f |x j-x k| = f (x j-x k) := by
      rcases le_or_gt 0 (x j-x k) with h|h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h,hpd.even]
    change resolvent (1+h) |x j-x k| + f |x j-x k| ≤ _ at harch
    rw [hf] at harch
    have hlog := Real.log_le_log (by linarith only [hu.1] : 0<|x j-x k|) hu.2
    dsimp only [A]
    linarith only [harch,hker,hlog]
  let row := fun j : Fin (m+1) => ∑ k ∈ Finset.univ.erase j, ((diskCopies 1 |x j-x k| r).card:ℝ)
  have hrow (j : Fin (m+1)) : row j/(h+r) + ∑ k, f (x j-x k) ≤ m*A+f 0 := by
    let S := Finset.univ.erase j
    have heq : (∑ k ∈ S,f (x j-x k)) + f 0 = ∑ k,f (x j-x k) := by
      simpa only [sub_self] using Finset.sum_erase_add (s := Finset.univ)
        (fun k => f (x j-x k)) (Finset.mem_univ j)
    rw [← heq,← add_assoc]
    apply add_le_add_right
    change (∑ k ∈ S, ((diskCopies 1 |x j-x k| r).card:ℝ))/(h+r) + _ ≤ _
    rw [Finset.sum_div,←Finset.sum_add_distrib]
    calc _ ≤ ∑ _k ∈ S,A := Finset.sum_le_sum fun k hk => hentry j k (Finset.ne_of_mem_erase hk).symm
         _ = _ := by simp [S]
  have hall := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hrow j)
  rw [Finset.sum_add_distrib,←Finset.sum_div] at hall
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hall
  have hcost : (m+1:ℝ)*(m*A+f 0) ≤ (m+1:ℝ)*(m*A+1/h-1/5) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hf₀]
  have hval : (differenceMultiplicity x r:ℝ)=∑ j,row j := by simp [differenceMultiplicity,row]
  rw [hval]
  exact (le_add_of_nonneg_right hsum).trans (hall.trans hcost)

/-- Empty difference disks have positive density at inverse-logarithmic
radius. Among m(m+1) ordered pairs the occupied fraction is at most
2/m + r(1+log T); multiple zeros only increase their cost. -/
theorem vacant_difference_floor {m : ℕ} {T r : ℝ} (x : Fin (m+1) → ℝ)
    (hx : ∀ j k, j≠k → |x j-x k| ∈ Set.Icc 4 T) (hr : 0<r) (hr₁ : r≤1) :
    (m+1:ℝ)*(m*(1-r*(1+Real.log T))-2) ≤ vacantDifferences x r := by
  have h := difference_multiplicity_budget x hx hr hr₁ hr.le le_rfl
  rw [div_le_iff₀ (add_pos hr hr)] at h
  have hc : ((m:ℝ)+1)*m ≤ (vacantDifferences x r:ℝ)+differenceMultiplicity x r := by
    exact_mod_cast difference_count_or_vacancy x r
  have hcancel : (m+1:ℝ)*(m*(Real.log T/2+1/2)+1/r-1/5)*(r+r) =
      (m+1:ℝ)*(m*r*(1+Real.log T)+2-2*r/5) := by field_simp [hr.ne']; ring
  rw [hcancel] at h
  linarith only [h,hc,mul_nonneg (by positivity : 0≤(m:ℝ)+1) hr.le]

#print axioms difference_multiplicity_budget
#print axioms vacant_difference_floor

private theorem abs_grid_difference {t : ℝ} (ht : 0≤t) (i j : ℕ) :
    |(i:ℝ)*t-j*t| = ((max i j-min i j : ℕ):ℝ)*t := by
  rw [←sub_mul,abs_mul,abs_of_nonneg ht,Nat.cast_sub (min_le_max ..)]
  rcases le_total i j with h|h
  · rw [max_eq_right h,min_eq_left h,abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h))]
    ring
  · rw [max_eq_left h,min_eq_right h,abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]

/-- Number of nonzero harmonics up to m at which the disk is empty. -/
def vacantHarmonics (m : ℕ) (t r : ℝ) : ℕ :=
  ((Finset.range (m+1)).filter fun k => k≠0 ∧ (diskCopies 1 (k*t) r).card=0).card

private theorem progression_vacancies_le (m : ℕ) {t : ℝ} (ht : 0≤t) (r : ℝ) :
    (vacantDifferences (fun i : Fin (m+1) => (i.val:ℝ)*t) r:ℝ) ≤
      2*((m:ℝ)+1)*vacantHarmonics m t r := by
  let f : ℕ → ℝ := fun k => if k≠0 ∧ (diskCopies 1 (k*t) r).card=0 then 1 else 0
  have h₀ : f 0 = 0 := by simp [f]
  have row (i : Fin (m+1)) :
      (∑ j ∈ Finset.univ.erase i, if (diskCopies 1 |(i.val:ℝ)*t-j.val*t| r).card=0 then (1:ℝ) else 0)
        = ∑ j : Fin (m+1), f (max i.val j.val-min i.val j.val) := by
    rw [← Finset.sum_erase_add (s := Finset.univ)
      (fun j : Fin (m+1) => f (max i.val j.val-min i.val j.val)) (Finset.mem_univ i)]
    simp only [max_self,min_self,Nat.sub_self,h₀,add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hn := Finset.ne_of_mem_erase hj
    have hv : i.val ≠ j.val := fun h => hn (Fin.ext h.symm)
    have hdiff : max i.val j.val-min i.val j.val ≠ 0 := by omega
    simp only [abs_grid_difference ht,f,hdiff,ne_eq,not_false_eq_true,true_and]
  have htot : (vacantDifferences (fun i : Fin (m+1) => (i.val:ℝ)*t) r:ℝ) =
      2 * ∑ k ∈ Finset.range (m+1), (((m:ℝ)+1)-k)*f k := by
    unfold vacantDifferences
    push_cast
    simp_rw [row,Fin.sum_univ_eq_sum_range]
    simpa only [Nat.cast_add,Nat.cast_one,h₀,mul_zero,sub_zero] using
      Sieve.sum_dist_double f (m+1)
  have hcount : (∑ k ∈ Finset.range (m+1),f k)=(vacantHarmonics m t r:ℝ) := by
    simp [f,vacantHarmonics,Finset.sum_boole]
  rw [htot,← hcount,mul_assoc,Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
    (sub_le_self _ (Nat.cast_nonneg k)) (by dsimp [f]; split <;> norm_num)

/-- At least one quarter of the first m harmonic disks are empty at
radius 1/[4(1+log(mt))], for every m≥8 and every step t≥4. Repeated
differences in the Gram form are counted with their exact Fejér weights. -/
theorem quarter_of_harmonic_disks_empty {m : ℕ} (hm : 8≤m) {t : ℝ} (ht : 4≤t) :
    let r := 1/(4*(1+Real.log (m*t)))
    (m:ℝ) ≤ 4*vacantHarmonics m t r := by
  intro r
  let x := fun i : Fin (m+1) => (i.val:ℝ)*t
  have hm₁ : (8:ℝ)≤m := by exact_mod_cast hm
  have ht₀ : 0≤t := by linarith
  have hT : 1≤(m:ℝ)*t := by nlinarith only [hm₁,ht,mul_nonneg (sub_nonneg.mpr hm₁) ht₀]
  have hlog := Real.log_nonneg hT
  have hr : 0<r := by dsimp only [r]; positivity
  have hr₁ : r≤1 := by
    dsimp only [r]
    exact (div_le_one (by positivity)).mpr (by linarith only [hlog])
  have hspace (i j : Fin (m+1)) (hn : i≠j) : |x i-x j| ∈ Set.Icc 4 ((m:ℝ)*t) := by
    rw [show |x i-x j|=_ from abs_grid_difference ht₀ i.val j.val]
    have hv : i.val≠j.val := fun h => hn (Fin.ext h)
    have h₁ : 1≤max i.val j.val-min i.val j.val := by omega
    have h₂ : max i.val j.val-min i.val j.val≤m := by have := i.isLt; have := j.isLt; omega
    exact ⟨ht.trans (le_mul_of_one_le_left ht₀ (by exact_mod_cast h₁)),
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h₂) ht₀⟩
  have hb := vacant_difference_floor x hspace hr hr₁
  have hratio : r*(1+Real.log ((m:ℝ)*t))=1/4 := by
    dsimp only [r]; field_simp [show 1+Real.log ((m:ℝ)*t)≠0 by linarith]
  rw [hratio] at hb
  have hh := hb.trans (progression_vacancies_le m ht₀ r)
  have hm₀ : 0<(m:ℝ)+1 := by positivity
  have hcan : (m:ℝ)*(1-1/4)-2 ≤ 2*vacantHarmonics m t r :=
    (mul_le_mul_iff_right₀ hm₀).mp (by convert hh using 1 <;> ring)
  linarith only [hm₁,hcan]

#print axioms quarter_of_harmonic_disks_empty

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
