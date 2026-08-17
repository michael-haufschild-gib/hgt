import Mathlib
import GaloisForLFunctions.HTGeometry.ComplexExponentialPolynomial
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialZeroBound
import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelonInfinite
import GaloisForLFunctions.RHTower.PrimeLogExponentialTypeUniqueness
import GaloisForLFunctions.RHTower.XiShiftPrimeHypertranscendence

/-!
# Prime-source cancellation budget for finite differential-translation filters

A finite differential-translation filter `L = ∑ⱼ Pⱼ(d/ds) T_{hⱼ}` acts on an ordinary Dirichlet
series `F(s) = ∑ b n · n^{-s}` by multiplying its `n`-th coefficient by the value of the fixed
exponential polynomial

`E_L(x) = ∑ⱼ Pⱼ(-x) e^{-hⱼ x}`

at `x = log n`.  Hence the primes whose source `L` erases are exactly the primes at which `E_L`
vanishes, and the cancellation budget of `L` is the zero budget of `E_L`.
-/

namespace GaloisForLFunctions.RHTower.PrimeCancellation

open LSeries Filter

/-- Translating the argument of an `L`-series twists its coefficients. -/
theorem lseries_shift (f : ℕ → ℂ) (s h : ℂ) :
    LSeries f (s + h) = LSeries (fun n => f n * (n : ℂ) ^ (-h)) s := by
  unfold LSeries
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_def, LSeries.term_def, if_neg (by omega), if_neg (by omega)]
    have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Complex.cpow_add _ _ hn0, Complex.cpow_neg]
    field_simp

/-- The `k`-th logarithmic multiple of a coefficient stream. -/
theorem logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul^[k] f) n = (Complex.log (n : ℂ)) ^ k * f n := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih]
      simp only [LSeries.logMul]
      ring

end GaloisForLFunctions.RHTower.PrimeCancellation

namespace GaloisForLFunctions.RHTower.PrimeCancellation

open LSeries Filter

theorem term_shift (f : ℕ → ℂ) (s h : ℂ) (n : ℕ) :
    LSeries.term f (s + h) n = LSeries.term (fun n => f n * (n : ℂ) ^ (-h)) s n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_def, LSeries.term_def, if_neg (by omega), if_neg (by omega)]
    have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Complex.cpow_add _ _ hn0, Complex.cpow_neg]
    field_simp

theorem lseriesSummable_shift (f : ℕ → ℂ) (s h : ℂ) :
    LSeriesSummable f (s + h) ↔ LSeriesSummable (fun n => f n * (n : ℂ) ^ (-h)) s := by
  unfold LSeriesSummable
  constructor
  · intro hsum
    exact hsum.congr (fun n => term_shift f s h n)
  · intro hsum
    exact hsum.congr (fun n => (term_shift f s h n).symm)

theorem abscissa_logMul_iterate (f : ℕ → ℂ) (k : ℕ) :
    LSeries.abscissaOfAbsConv (LSeries.logMul^[k] f) = LSeries.abscissaOfAbsConv f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', LSeries.abscissaOfAbsConv_logMul, ih]

/-- The scalar symbol of a finite differential-translation filter. -/
noncomputable def filterSymbol {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (x : ℂ) : ℂ :=
  ∑ j, (P j).eval (-x) * Complex.exp (-(h j) * x)

theorem cpow_neg_eq_exp (h : ℂ) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ (-h) = Complex.exp (-h * Complex.log (n : ℂ)) := by
  have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hn0]
  congr 1
  ring

end GaloisForLFunctions.RHTower.PrimeCancellation

namespace GaloisForLFunctions.RHTower.PrimeCancellation

open LSeries Filter

set_option maxHeartbeats 1000000 in
theorem lseries_term_eq {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (b : ℕ → ℂ) (s : ℂ)
    (hs : ∀ j, LSeries.abscissaOfAbsConv b < ((s + h j).re : EReal)) (j : Fin m) (k : ℕ) :
    (P j).coeff k * iteratedDeriv k (LSeries b) (s + h j)
      = LSeries (((P j).coeff k * (-1 : ℂ) ^ k) •
          (fun n : ℕ => (Complex.log (n : ℂ)) ^ k * b n * (n : ℂ) ^ (-(h j)))) s := by
  rw [LSeries_iteratedDeriv k (hs j)]
  have h1 : LSeries (LSeries.logMul^[k] b) (s + h j)
      = LSeries (fun n : ℕ => (Complex.log (n : ℂ)) ^ k * b n * (n : ℂ) ^ (-(h j))) s := by
    rw [lseries_shift]
    refine LSeries_congr (fun {n} _ => ?_) _
    rw [logMul_iterate_apply]
  rw [h1, LSeries_smul]
  ring

set_option maxHeartbeats 1000000 in
theorem lseries_term_summable {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (b : ℕ → ℂ)
    (s : ℂ) (hs : ∀ j, LSeries.abscissaOfAbsConv b < ((s + h j).re : EReal)) (j : Fin m) (k : ℕ) :
    LSeriesSummable (((P j).coeff k * (-1 : ℂ) ^ k) •
      (fun n : ℕ => (Complex.log (n : ℂ)) ^ k * b n * (n : ℂ) ^ (-(h j)))) s := by
  have hbase : LSeriesSummable (LSeries.logMul^[k] b) (s + h j) := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    rw [abscissa_logMul_iterate]
    exact hs j
  rw [lseriesSummable_shift] at hbase
  have hbase' : LSeriesSummable
      (fun n : ℕ => (Complex.log (n : ℂ)) ^ k * b n * (n : ℂ) ^ (-(h j))) s := by
    refine hbase.congr (fun n => ?_)
    simp only [logMul_iterate_apply]
  exact hbase'.smul _

set_option maxHeartbeats 1000000 in
/-- **The filtered coefficient law.**  A finite constant-coefficient differential-translation
filter multiplies the Dirichlet coefficients by the filter symbol evaluated at `log n`. -/
theorem filterAction {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (b : ℕ → ℂ) (s : ℂ)
    (hs : ∀ j, LSeries.abscissaOfAbsConv b < ((s + h j).re : EReal)) :
    (∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1),
        (P j).coeff k * iteratedDeriv k (LSeries b) (s + h j))
      = LSeries (fun n => b n * filterSymbol h P (Complex.log (n : ℂ))) s := by
  classical
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl
    (fun k _ => lseries_term_eq h P b s hs j k))]
  rw [Finset.sum_congr rfl (fun j _ =>
    (LSeries_sum (fun k _ => lseries_term_summable h P b s hs j k)).symm)]
  rw [← LSeries_sum (fun j _ => ?_)]
  · refine LSeries_congr (fun {n} hn => ?_) _
    rw [filterSymbol, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [cpow_neg_eq_exp (h j) (Nat.pos_of_ne_zero hn)]
    rw [Polynomial.eval_eq_sum_range (p := P j) (-(Complex.log (n : ℂ)))]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [neg_pow]
    ring
  · exact LSeriesSummable.sum (fun k _ => lseries_term_summable h P b s hs j k)

end GaloisForLFunctions.RHTower.PrimeCancellation


namespace GaloisForLFunctions.RHTower.PrimeCancellation

open Finset GaloisForLFunctions.HTGeometry.ExpZeroBound GaloisForLFunctions.HTGeometry.CExpPoly

theorem filterSymbol_eq_cexpFn {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (z : ℂ) :
    filterSymbol h P z = cexpFn (fun j => -(h j)) (fun j => negComp (P j)) z := by
  unfold filterSymbol cexpFn
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_negComp]

theorem filterSymbol_eq_cexpPoly {m : ℕ} (h : Fin m → ℝ) (P : Fin m → Polynomial ℂ) (x : ℝ) :
    filterSymbol (fun j => ((h j : ℝ) : ℂ)) P ((x : ℝ) : ℂ)
      = cexpPoly (fun j => -(h j)) (fun j => negComp (P j)) x := by
  unfold filterSymbol cexpPoly
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_negComp]
  congr 2
  push_cast
  ring

/-- **Real-shift zero budget.**  A nonzero real-shift filter symbol has fewer distinct real zeros
than its number of scalar operator coordinates. -/
theorem card_lt_of_filterSymbol_real {m : ℕ} (h : Fin (m + 1) → ℝ)
    (P : Fin (m + 1) → Polynomial ℂ) (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0)
    (S : Finset ℝ) (hS : ∀ x ∈ S, filterSymbol (fun j => ((h j : ℝ) : ℂ)) P ((x : ℝ) : ℂ) = 0) :
    S.card < ∑ j, ((P j).natDegree + 1) := by
  have hinj : Function.Injective (fun j => -(h j)) := fun i j hij => hh (neg_injective hij)
  have hQ : ∀ j, negComp (P j) ≠ 0 := fun j => negComp_ne_zero (hP j)
  have hzero : ∀ x ∈ S, cexpPoly (fun j => -(h j)) (fun j => negComp (P j)) x = 0 := by
    intro x hx
    rw [← filterSymbol_eq_cexpPoly]
    exact hS x hx
  have hbound := card_lt_of_cexpPoly_eq_zero (fun j => -(h j)) (fun j => negComp (P j))
    hinj hQ S hzero
  simpa only [natDegree_negComp] using hbound

/-- The primes whose nonzero source coefficient the filter erases. -/
def cancelledPrimes {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (b : ℕ → ℂ) :
    Set Nat.Primes :=
  {p | b (p : ℕ) ≠ 0 ∧ b (p : ℕ) * filterSymbol h P (Complex.log ((p : ℕ) : ℂ)) = 0}

theorem complex_log_prime {p : Nat.Primes} :
    Complex.log ((p : ℕ) : ℂ) = ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hlog : ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) = Complex.log (((p : ℕ) : ℝ) : ℂ) :=
    Complex.ofReal_log (by positivity)
  rw [hlog]
  push_cast
  ring

theorem primeLog_injective : Function.Injective (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) := by
  intro p q hpq
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
  have hcast : ((p : ℕ) : ℝ) = ((q : ℕ) : ℝ) :=
    Real.strictMonoOn_log.injOn hp hq hpq
  exact Subtype.ext (by exact_mod_cast hcast)

theorem filterSymbol_eq_zero_of_mem_cancelledPrimes {m : ℕ} (h : Fin m → ℂ)
    (P : Fin m → Polynomial ℂ) (b : ℕ → ℂ) {p : Nat.Primes} (hp : p ∈ cancelledPrimes h P b) :
    filterSymbol h P (((Real.log ((p : ℕ) : ℝ) : ℝ)) : ℂ) = 0 := by
  obtain ⟨hb, hzero⟩ := hp
  rw [← complex_log_prime]
  rcases mul_eq_zero.mp hzero with h1 | h2
  · exact absurd h1 hb
  · exact h2

/-- **Real-shift prime cancellation budget.**  A real-shift filter with `N` scalar operator
coordinates erases at most `N - 1` nonzero prime sources. -/
theorem card_cancelledPrimes_lt {m : ℕ} (h : Fin (m + 1) → ℝ) (P : Fin (m + 1) → Polynomial ℂ)
    (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) (b : ℕ → ℂ) (T : Finset Nat.Primes)
    (hT : ∀ p ∈ T, p ∈ cancelledPrimes (fun j => ((h j : ℝ) : ℂ)) P b) :
    T.card < ∑ j, ((P j).natDegree + 1) := by
  classical
  set S : Finset ℝ := T.image (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) with hS
  have hcard : S.card = T.card :=
    Finset.card_image_of_injective T primeLog_injective
  have hzero : ∀ x ∈ S, filterSymbol (fun j => ((h j : ℝ) : ℂ)) P ((x : ℝ) : ℂ) = 0 := by
    intro x hx
    rw [hS, Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact filterSymbol_eq_zero_of_mem_cancelledPrimes _ P b (hT p hp)
  have := card_lt_of_filterSymbol_real h P hh hP S hzero
  omega

theorem cancelledPrimes_finite {m : ℕ} (h : Fin (m + 1) → ℝ) (P : Fin (m + 1) → Polynomial ℂ)
    (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) (b : ℕ → ℂ) :
    (cancelledPrimes (fun j => ((h j : ℝ) : ℂ)) P b).Finite := by
  classical
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq (∑ j, ((P j).natDegree + 1))
  have := card_cancelledPrimes_lt h P hh hP b T (fun p hp => hTsub hp)
  omega

/-- The cancellation budget in cardinal form: erasing `q` nonzero prime sources with real shifts
costs at least `q + 1` scalar operator coordinates. -/
theorem cancelledPrimes_ncard_lt {m : ℕ} (h : Fin (m + 1) → ℝ) (P : Fin (m + 1) → Polynomial ℂ)
    (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) (b : ℕ → ℂ) :
    (cancelledPrimes (fun j => ((h j : ℝ) : ℂ)) P b).ncard < ∑ j, ((P j).natDegree + 1) := by
  classical
  have hfin := cancelledPrimes_finite h P hh hP b
  have hsub : ∀ p ∈ hfin.toFinset, p ∈ cancelledPrimes (fun j => ((h j : ℝ) : ℂ)) P b := by
    intro p hp
    simpa using hp
  have hcard := card_cancelledPrimes_lt h P hh hP b hfin.toFinset hsub
  rwa [Set.ncard_eq_toFinset_card _ hfin]

end GaloisForLFunctions.RHTower.PrimeCancellation

namespace GaloisForLFunctions.RHTower.PrimeCancellation

open Finset Metric GaloisForLFunctions.HTGeometry.CExpPoly

theorem primeLogComplex_injective :
    Function.Injective (fun p : Nat.Primes => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) :=
  fun _ _ hpq => primeLog_injective (Complex.ofReal_injective hpq)

/-- **Complex-shift cancellation law.**  With arbitrary distinct complex shifts the number of
erased prime sources below `x` is `O(log x)`. -/
theorem exists_cancelledPrimes_count_le_log {m : ℕ} (h : Fin (m + 1) → ℂ)
    (P : Fin (m + 1) → Polynomial ℂ) (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) (b : ℕ → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → ∀ T : Finset Nat.Primes,
      (∀ p ∈ T, p ∈ cancelledPrimes h P b) → (∀ p ∈ T, ((p : ℕ) : ℝ) ≤ x) →
      (T.card : ℝ) ≤ C * Real.log x := by
  classical
  have hinj : Function.Injective (fun j => -(h j)) := fun i j hij => hh (neg_injective hij)
  have hQ : ∀ j, negComp (P j) ≠ 0 := fun j => negComp_ne_zero (hP j)
  obtain ⟨z₀, K, hK, hcount⟩ :=
    exists_zeroCount_linear (fun j => -(h j)) (fun j => negComp (P j)) hinj hQ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K * (1 + (2 + ‖z₀‖) / Real.log 2), by positivity, ?_⟩
  intro x hx T hTcanc hTle
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlogx0 : 0 < Real.log x := lt_of_lt_of_le hlog2 hlogx
  set r : ℝ := Real.log x + ‖z₀‖ + 1 with hr
  have hr1 : 1 ≤ r := by
    rw [hr]
    have := norm_nonneg z₀
    linarith
  set S : Finset ℂ := T.image (fun p : Nat.Primes => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) with hS
  have hcard : S.card = T.card :=
    Finset.card_image_of_injective T primeLogComplex_injective
  have hSzero : ∀ w ∈ S, cexpFn (fun j => -(h j)) (fun j => negComp (P j)) w = 0 := by
    intro w hw
    rw [hS, Finset.mem_image] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    rw [← filterSymbol_eq_cexpFn]
    exact filterSymbol_eq_zero_of_mem_cancelledPrimes h P b (hTcanc p hp)
  have hSball : ∀ w ∈ S, w ∈ closedBall z₀ r := by
    intro w hw
    rw [hS, Finset.mem_image] at hw
    obtain ⟨p, hp, rfl⟩ := hw
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_le
    have hlogp0 : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg hp1
    have hlogp : Real.log ((p : ℕ) : ℝ) ≤ Real.log x := Real.log_le_log hp0 (hTle p hp)
    rw [mem_closedBall, Complex.dist_eq]
    calc ‖((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) - z₀‖
        ≤ ‖((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)‖ + ‖z₀‖ := norm_sub_le _ _
      _ = Real.log ((p : ℕ) : ℝ) + ‖z₀‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hlogp0]
      _ ≤ r := by rw [hr]; linarith
  have hbound := hcount r hr1 S hSzero hSball
  rw [hcard] at hbound
  refine le_trans hbound ?_
  have hstep : (2 + ‖z₀‖) ≤ (2 + ‖z₀‖) / Real.log 2 * Real.log x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    have h0 : (0 : ℝ) ≤ 2 + ‖z₀‖ := by positivity
    nlinarith
  have hK0 : 0 ≤ K := hK.le
  calc K * (1 + r) = K * (Real.log x + (2 + ‖z₀‖)) := by rw [hr]; ring
    _ ≤ K * (Real.log x + (2 + ‖z₀‖) / Real.log 2 * Real.log x) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hK0
    _ = K * (1 + (2 + ‖z₀‖) / Real.log 2) * Real.log x := by ring

end GaloisForLFunctions.RHTower.PrimeCancellation

namespace GaloisForLFunctions.RHTower.PrimeCancellation

open Finset GaloisForLFunctions.HTGeometry.CExpPoly

/-- **Cofinite prime-log uniqueness at finite exponential type.**  Dropping finitely many primes
from the sampling set does not restore a nonzero entire function of finite exponential type:
multiplying by the polynomial that vanishes at the omitted prime logarithms restores the full
prime-log sampling hypothesis without leaving finite exponential type. -/
theorem eq_zero_of_exponentialType_of_cofinite_primeLog_zeros
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hgrow : ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖))
    (E : Finset ℕ) (hprime : ∀ p : ℕ, p.Prime → p ∉ E → f ((Real.log (p : ℝ) : ℝ) : ℂ) = 0) :
    f = 0 := by
  classical
  set Q : Polynomial ℂ :=
    ∏ q ∈ E, (Polynomial.X - Polynomial.C ((Real.log ((q : ℕ) : ℝ) : ℝ) : ℂ)) with hQdef
  have hQ0 : Q ≠ 0 := by
    rw [hQdef]
    refine Finset.prod_ne_zero_iff.mpr (fun q _ => ?_)
    exact (Polynomial.monic_X_sub_C _).ne_zero
  set g : ℂ → ℂ := fun z => f z * Q.eval z with hgdef
  have hgdiff : Differentiable ℂ g := hf.mul (Polynomial.differentiable Q)
  have hgzero : ∀ p : ℕ, p.Prime → g ((Real.log (p : ℝ) : ℝ) : ℂ) = 0 := by
    intro p hp
    by_cases hpE : p ∈ E
    · have hroot : Q.eval ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) = 0 := by
        rw [hQdef, Polynomial.eval_prod]
        refine Finset.prod_eq_zero hpE ?_
        simp
      rw [hgdef]
      simp only []
      rw [hroot, mul_zero]
    · rw [hgdef]
      simp only []
      rw [hprime p hp hpE, zero_mul]
  set Sq : ℝ := ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ with hSq
  have hSq0 : 0 ≤ Sq := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have hgrowg : ∀ z : ℂ, ‖g z‖ ≤ max 1 (C * Sq) * Real.exp ((A + (Q.natDegree : ℝ)) * ‖z‖) := by
    intro z
    have hQeval : ‖Q.eval z‖ ≤ Sq * Real.exp ((Q.natDegree : ℝ) * ‖z‖) := by
      refine le_trans (norm_eval_le Q z) ?_
      exact mul_le_mul_of_nonneg_left (one_add_norm_pow_le_exp Q.natDegree z) hSq0
    calc ‖g z‖ = ‖f z‖ * ‖Q.eval z‖ := norm_mul _ _
      _ ≤ (C * Real.exp (A * ‖z‖)) * (Sq * Real.exp ((Q.natDegree : ℝ) * ‖z‖)) := by
          exact mul_le_mul (hgrow z) hQeval (norm_nonneg _) (by positivity)
      _ = (C * Sq) * Real.exp ((A + (Q.natDegree : ℝ)) * ‖z‖) := by
          rw [add_mul, Real.exp_add]
          ring
      _ ≤ max 1 (C * Sq) * Real.exp ((A + (Q.natDegree : ℝ)) * ‖z‖) := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  have hg0 : g = 0 :=
    _root_.RHTower.eq_zero_of_exponentialType_of_primeLog_zeros hgdiff
      (by positivity) (le_max_left _ _) hgrowg hgzero
  have hdense : Dense ({z : ℂ | Q.eval z = 0}ᶜ) :=
    Set.Countable.dense_compl ℂ (Polynomial.finite_setOf_isRoot hQ0).countable
  refine Continuous.ext_on hdense hf.continuous continuous_const ?_
  intro z hz
  have hgz : f z * Q.eval z = 0 := congrFun hg0 z
  rcases mul_eq_zero.mp hgz with h1 | h2
  · exact h1
  · exact absurd h2 hz

/-- **Every finite filter leaves infinitely many exposed prime sources.**  If the Dirichlet source
has nonzero coefficients at all but finitely many primes, then no nonzero finite
differential-translation filter can erase all but finitely many of them. -/
theorem infinite_survivingPrimes {m : ℕ} (h : Fin (m + 1) → ℂ) (P : Fin (m + 1) → Polynomial ℂ)
    (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) (b : ℕ → ℂ)
    (hb : {p : Nat.Primes | b (p : ℕ) = 0}.Finite) :
    {p : Nat.Primes | b (p : ℕ) * filterSymbol h P (Complex.log ((p : ℕ) : ℂ)) ≠ 0}.Infinite := by
  classical
  intro hfin
  have hinj : Function.Injective (fun j => -(h j)) := fun i j hij => hh (neg_injective hij)
  have hQ : ∀ j, negComp (P j) ≠ 0 := fun j => negComp_ne_zero (hP j)
  obtain ⟨C, A, hC, hA, hgrow⟩ :=
    exists_exponentialType_bound (fun j => -(h j)) (fun j => negComp (P j))
  set Bad : Set Nat.Primes := {p : Nat.Primes | b (p : ℕ) = 0} ∪
    {p : Nat.Primes | b (p : ℕ) * filterSymbol h P (Complex.log ((p : ℕ) : ℂ)) ≠ 0} with hBaddef
  have hBad : Bad.Finite := hb.union hfin
  set E : Finset ℕ := hBad.toFinset.image (fun p : Nat.Primes => (p : ℕ)) with hEdef
  have hzero : ∀ p : ℕ, p.Prime → p ∉ E →
      cexpFn (fun j => -(h j)) (fun j => negComp (P j)) ((Real.log (p : ℝ) : ℝ) : ℂ) = 0 := by
    intro p hp hpE
    set pp : Nat.Primes := ⟨p, hp⟩ with hpp
    have hppBad : pp ∉ Bad := by
      intro hmem
      exact hpE (by
        rw [hEdef]
        exact Finset.mem_image.mpr ⟨pp, by simpa using hmem, rfl⟩)
    rw [hBaddef] at hppBad
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hppBad
    obtain ⟨hbne, hcanc⟩ := hppBad
    have hbne' : b (pp : ℕ) ≠ 0 := hbne
    have hsym : filterSymbol h P (Complex.log ((pp : ℕ) : ℂ)) = 0 := by
      rcases mul_eq_zero.mp hcanc with h1 | h2
      · exact absurd h1 hbne'
      · exact h2
    rw [complex_log_prime] at hsym
    rw [← filterSymbol_eq_cexpFn]
    exact hsym
  have hzeroFn := eq_zero_of_exponentialType_of_cofinite_primeLog_zeros
    (differentiable_cexpFn (fun j => -(h j)) (fun j => negComp (P j))) hA hC hgrow E hzero
  obtain ⟨z, hz⟩ := exists_cexpFn_ne_zero (fun j => -(h j)) (fun j => negComp (P j)) hinj hQ
  exact hz (congrFun hzeroFn z)

end GaloisForLFunctions.RHTower.PrimeCancellation

namespace GaloisForLFunctions.RHTower.PrimeCancellation

open Finset LSeries GaloisForLFunctions.HTGeometry

/-- The filtered Dirichlet source produced by a finite differential-translation filter. -/
noncomputable def filteredSource {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (g : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := g n * filterSymbol h P (Complex.log (n : ℂ))
  map_zero' := by simp

@[simp]
theorem filteredSource_apply {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (g : ArithmeticFunction ℂ) (n : ℕ) :
    filteredSource h P g n = g n * filterSymbol h P (Complex.log (n : ℂ)) :=
  rfl

theorem filteredSource_supportedOnPositivePrimePowers {m : ℕ} (h : Fin m → ℂ)
    (P : Fin m → Polynomial ℂ) {g : ArithmeticFunction ℂ}
    (hg : SupportedOnPositivePrimePowers g) :
    SupportedOnPositivePrimePowers (filteredSource h P g) := by
  intro n hn
  refine hg (fun hzero => hn ?_)
  rw [filteredSource_apply, hzero, zero_mul]

/-- **Hypertranscendence of every filtered prime source.**  If the source is supported on
positive prime powers and has only finitely many vanishing prime coefficients, then the image of
every nonzero finite differential-translation filter is differentially independent over `ℂ`. -/
theorem filteredSource_differentialIndependent {m : ℕ} (h : Fin (m + 1) → ℂ)
    (P : Fin (m + 1) → Polynomial ℂ) (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0)
    {g : ArithmeticFunction ℂ} (hg : SupportedOnPositivePrimePowers g)
    (hzeros : {p : Nat.Primes | g (p : ℕ) = 0}.Finite) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun _ : Fin 1 => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (filteredSource h P g)) := by
  classical
  refine primeValuationLeadingEchelon_differentialIndependent_of_infinitePrimeDependent
    (fun _ : Fin 1 => filteredSource h P g)
    (fun _ : Fin 1 => 0)
    (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ p => filteredSource h P g (p : ℕ))
    (fun _ => ?_)
    (fun _ => filteredSource_supportedOnPositivePrimePowers h P hg)
    (fun r s p => ?_)
  · exact infinite_survivingPrimes h P hh hP (fun n => g n) hzeros
  · have hrs : r = s := Subsingleton.elim _ _
    subst s
    simp

end GaloisForLFunctions.RHTower.PrimeCancellation

namespace GaloisForLFunctions.RHTower.PrimeCancellation

open Finset LSeries GaloisForLFunctions.HTGeometry

/-- Summability of the filtered coefficients on the common half-plane of the shifted sources. -/
theorem lseriesSummable_filterSymbol {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (b : ℕ → ℂ) (s : ℂ) (hs : ∀ j, LSeries.abscissaOfAbsConv b < ((s + h j).re : EReal)) :
    LSeriesSummable (fun n => b n * filterSymbol h P (Complex.log (n : ℂ))) s := by
  classical
  have hsum : LSeriesSummable
      (∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1),
        (((P j).coeff k * (-1 : ℂ) ^ k) •
          (fun n : ℕ => (Complex.log (n : ℂ)) ^ k * b n * (n : ℂ) ^ (-(h j))))) s :=
    LSeriesSummable.sum (fun j _ =>
      LSeriesSummable.sum (fun k _ => lseries_term_summable h P b s hs j k))
  refine (LSeriesSummable_congr s (f := ∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1),
    (((P j).coeff k * (-1 : ℂ) ^ k) •
      (fun n : ℕ => (Complex.log (n : ℂ)) ^ k * b n * (n : ℂ) ^ (-(h j))))) ?_).mp hsum
  intro n hn
  rw [filterSymbol, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [cpow_neg_eq_exp (h j) (Nat.pos_of_ne_zero hn)]
  rw [Polynomial.eval_eq_sum_range (p := P j) (-(Complex.log (n : ℂ)))]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [neg_pow]
  ring

/-- The abscissa threshold beyond which every shifted source of a filter converges absolutely. -/
noncomputable def filterAbscissa {m : ℕ} (h : Fin m → ℂ) (H : ℝ) : ℝ :=
  H + ∑ j, max 0 (-(h j).re)

theorem lt_filterAbscissa {m : ℕ} (h : Fin m → ℂ) (H : ℝ) (j : Fin m) :
    H - (h j).re ≤ filterAbscissa h H := by
  classical
  have hle : max 0 (-(h j).re) ≤ ∑ i, max 0 (-(h i).re) :=
    Finset.single_le_sum (f := fun i : Fin m => max 0 (-(h i).re))
      (fun i _ => le_max_left _ _) (Finset.mem_univ j)
  have hbase : -(h j).re ≤ max 0 (-(h j).re) := le_max_right _ _
  unfold filterAbscissa
  linarith

/-- The filtered source of a finite-abscissa source has finite abscissa. -/
theorem filteredSource_finiteAbscissa {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ)
    (g : ArithmeticFunction ℂ) {H : ℝ}
    (hg : LSeries.abscissaOfAbsConv (fun n => g n) ≤ (H : EReal)) :
    ∀ y : ℝ, filterAbscissa h H < y →
      LSeriesSummable (fun n => filteredSource h P g n) (y : ℂ) := by
  intro y hy
  refine lseriesSummable_filterSymbol h P (fun n => g n) (y : ℂ) (fun j => ?_)
  refine lt_of_le_of_lt hg ?_
  have hlt : H - (h j).re < y := lt_of_le_of_lt (lt_filterAbscissa h H j) hy
  have hre : H < ((y : ℂ) + h j).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  exact_mod_cast hre

end GaloisForLFunctions.RHTower.PrimeCancellation

namespace RHTower

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.PrimeCancellation

local instance xiFilteredUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiFilteredUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiFilteredUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- The rationally corrected `+2` shift defect of the completed logarithmic derivative. -/
def xiShiftTwoDefect (s : ℂ) : ℂ :=
  logDeriv xi (s + 2) - logDeriv xi s - (1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1))

theorem xiShiftTwoDefect_eventuallyEq {s : ℂ} (hs : 1 < s.re) :
    xiShiftTwoDefect =ᶠ[nhds s] LSeries filteredVonMangoldtCoeff := by
  have hopen : IsOpen {w : ℂ | 1 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  have hcoeff : filteredVonMangoldtCoeff
      = fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (1 - (n : ℂ) ^ (-(2 : ℂ))) := rfl
  rw [show xiShiftTwoDefect w = logDeriv xi (w + 2) - logDeriv xi w -
      (1 / (w + 2) + 1 / (w + 1) - 1 / (w - 1)) from rfl, hcoeff]
  exact xi_logDeriv_shift_two_exposes_prime_source hw

theorem abscissaOfAbsConv_filteredVonMangoldtCoeff_le :
    LSeries.abscissaOfAbsConv filteredVonMangoldtCoeff ≤ (1 : EReal) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy => ?_)
  refine LSeriesSummable_filteredVonMangoldtCoeff ?_
  simpa using hy

/-- **Filtered xi source.**  Every finite differential-translation filter of the exposed xi shift
defect is again a Dirichlet series, with coefficients scaled by the filter symbol. -/
theorem xiFilteredAction {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (s : ℂ)
    (hs : ∀ j, 1 < (s + h j).re) :
    (∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1),
        (P j).coeff k * iteratedDeriv k xiShiftTwoDefect (s + h j))
      = LSeries (fun n => filteredSource h P filteredVonMangoldtArithmetic n) s := by
  have hs' : ∀ j, LSeries.abscissaOfAbsConv filteredVonMangoldtCoeff <
      (((s + h j).re : ℝ) : EReal) := by
    intro j
    refine lt_of_le_of_lt abscissaOfAbsConv_filteredVonMangoldtCoeff_le ?_
    exact_mod_cast hs j
  have hderiv : ∀ (j : Fin m) (k : ℕ),
      iteratedDeriv k xiShiftTwoDefect (s + h j)
        = iteratedDeriv k (LSeries filteredVonMangoldtCoeff) (s + h j) := by
    intro j k
    exact Filter.EventuallyEq.iteratedDeriv_eq k (xiShiftTwoDefect_eventuallyEq (hs j))
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by rw [hderiv j k]))]
  rw [filterAction h P filteredVonMangoldtCoeff s hs']
  rfl

/-- The filtered xi source as an element of the finite-abscissa arithmetic algebra. -/
def xiFilteredFiniteAbscissaSource {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) :
    finiteAbscissaArithmeticSubalgebra :=
  ⟨filteredSource h P filteredVonMangoldtArithmetic, filterAbscissa h 1, by
    refine filteredSource_finiteAbscissa h P filteredVonMangoldtArithmetic ?_
    simpa [filteredVonMangoldtArithmetic] using
      abscissaOfAbsConv_filteredVonMangoldtCoeff_le⟩

@[simp]
theorem xiFilteredFiniteAbscissaSource_val {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) :
    (xiFilteredFiniteAbscissaSource h P).1 = filteredSource h P filteredVonMangoldtArithmetic :=
  rfl

theorem xiFilteredSource_differentialIndependent_formal {m : ℕ} (h : Fin (m + 1) → ℂ)
    (P : Fin (m + 1) → Polynomial ℂ) (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) :
    GaloisForLFunctions.DifferentialIndependent ℂ
      (fun _ : Fin 1 => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (filteredSource h P filteredVonMangoldtArithmetic)) := by
  refine filteredSource_differentialIndependent h P hh hP
    filteredVonMangoldtArithmetic_supportedOnPositivePrimePowers ?_
  have hempty : {p : Nat.Primes | filteredVonMangoldtArithmetic (p : ℕ) = 0} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    simpa [filteredVonMangoldtArithmetic] using filteredVonMangoldtCoeff_prime_ne_zero p
  rw [hempty]
  exact Set.finite_empty

/-- Upper-end meromorphic carrier of the filtered xi source. -/
def xiFilteredUpperEndCarrier {m : ℕ} (h : Fin m → ℂ) (P : Fin m → Polynomial ℂ) :
    upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero (xiFilteredFiniteAbscissaSource h P)

theorem xiFilteredUpperEndCarrier_differentialIndependent {m : ℕ} (h : Fin (m + 1) → ℂ)
    (P : Fin (m + 1) → Polynomial ℂ) (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun _ : Fin 1 => xiFilteredUpperEndCarrier h P) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
  simpa [xiFilteredFiniteAbscissaSource] using
    xiFilteredSource_differentialIndependent_formal h P hh hP

/-- **Filtered xi hypertranscendence.**  With arbitrary distinct complex shifts and arbitrary
finite derivative orders, every nonzero finite differential-translation filter of the exposed
`+2` xi shift defect is hypertranscendental over the rational coordinate field. -/
theorem xiFilteredUpperEndCarrier_hypertranscendentalOver {m : ℕ} (h : Fin (m + 1) → ℂ)
    (P : Fin (m + 1) → Polynomial ℂ) (hh : Function.Injective h) (hP : ∀ j, P j ≠ 0) :
    HypertranscendentalOver upperEndRationalCoordinateField
      (xiFilteredUpperEndCarrier h P) := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  have hunit := (xiFilteredUpperEndCarrier_differentialIndependent h P hh hP).comp
    (fun _ : Unit ↦ (0 : Fin 1)) (fun _ _ _ ↦ Subsingleton.elim _ _)
  simpa [Function.comp_def] using hunit

end

end RHTower
