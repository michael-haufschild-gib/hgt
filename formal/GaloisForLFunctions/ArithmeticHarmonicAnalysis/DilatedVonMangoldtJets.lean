import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.ExponentialSeriesSigmaSum
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# Prime-power expansions of actual zeta-dilation logarithmic jets

Every jet of `-r ζ'(r s)/ζ(r s)` is an absolutely convergent logarithmically
weighted von Mangoldt series when `Re(r s)>1`. Prime-power reindexing gives
its exact vertical-line frequencies and coefficients, with decay separated
from phase. These are actual analytic jets, not formal coefficient carriers.
-/

open Complex LSeries ArithmeticFunction
open scoped Classical LSeries.notation
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilatedVonMangoldt
noncomputable section

/-- The negative logarithmic derivative of the actual dilate `ζ(r s)`. -/
def source (r : ℝ) (s : ℂ) : ℂ := -(r : ℂ) * _root_.RHTower.zetaLogDeriv ((r : ℂ) * s)

/-- Every actual dilation jet is an absolutely convergent logarithmically weighted von Mangoldt series. -/
theorem source_jet_eq_LSeries (r : ℝ) (k : ℕ) {s : ℂ} (hs : 1 < r * s.re) :
    iteratedDeriv k (source r) s = (r : ℂ)^(k+1) * (-1 : ℂ)^k *
      LSeries (logMul^[k] ↗Λ) ((r : ℂ)*s) := by
  have hrs : 1 < ((r : ℂ)*s).re := by simpa using hs
  change iteratedDeriv k (fun z => -(r : ℂ) * _root_.RHTower.zetaLogDeriv ((r : ℂ)*z)) s = _
  rw [iteratedDeriv_const_mul_field]
  change -(r : ℂ) * iteratedDeriv k (fun z => _root_.RHTower.zetaLogDeriv ((r : ℂ)*z)) s = _
  rw [iteratedDeriv_comp_mul_left_uncond, _root_.RHTower.iteratedDeriv_zetaLogDeriv_eq_LSeries k hrs]
  ring

/-- The actual jet's Dirichlet terms. -/
def jetTerm (k : ℕ) (s : ℂ) (n : ℕ) : ℂ := term (logMul^[k] ↗Λ) s n

private theorem logMul_iterate_apply (f : ℕ → ℂ) (k n : ℕ) :
    (logMul^[k] f) n = Complex.log n ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change Complex.log n * (logMul^[k] f) n = _
    rw [ih]
    ring

/-- Absolute convergence persists through every logarithmic twist. -/
theorem summable_norm_jetTerm (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n => ‖jetTerm k s n‖ := by
  have habs : abscissaOfAbsConv ↗Λ < s.re :=
    lt_of_le_of_lt _root_.RHTower.abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hsum : LSeriesSummable (logMul^[k] ↗Λ) s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    simpa using habs
  exact summable_norm_iff.mpr hsum

private theorem jetTerm_eq_zero_of_not_primePow (k : ℕ) (s : ℂ) (n : ℕ)
    (hn : ¬IsPrimePow n) : jetTerm k s n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [jetTerm]
  · rw [jetTerm, term_of_ne_zero hn0, logMul_iterate_apply]
    have hz := vonMangoldt_eq_zero_iff.mpr hn
    rw [hz, Complex.ofReal_zero, mul_zero, zero_div]

/-- Prime-power reindexing of every jet, with no summation exchange left implicit. -/
theorem tsum_jetTerm_eq_primePowers (k : ℕ) (s : ℂ) :
    (∑' n, jetTerm k s n) =
      ∑' pm : Nat.Primes × ℕ, jetTerm k s (pm.1.val^(pm.2+1)) := by
  have hsupp : Function.support (jetTerm k s) ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hnp
    exact hn (jetTerm_eq_zero_of_not_primePow k s n hnp)
  calc
    (∑' n, jetTerm k s n) = ∑' n : {n : ℕ // IsPrimePow n}, jetTerm k s n :=
      (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' pm : Nat.Primes × ℕ, jetTerm k s (pm.1.val^(pm.2+1)) :=
      (Nat.Primes.prodNatEquiv.tsum_eq
        (fun n : {n : ℕ // IsPrimePow n} => jetTerm k s n)).symm

theorem summable_norm_primePowers (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun pm : Nat.Primes × ℕ => ‖jetTerm k s (pm.1.val^(pm.2+1))‖ := by
  have hsub := (summable_norm_jetTerm k hs).subtype IsPrimePow
  exact (Nat.Primes.prodNatEquiv.summable_iff
    (f := fun n : {n : ℕ // IsPrimePow n} => ‖jetTerm k s n‖)).mpr hsub

private theorem term_eq_exp (f : ℕ → ℂ) (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    term f s n = f n * Complex.exp (-s * (Real.log n : ℂ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : (n : ℂ)^s = Complex.exp ((Real.log n : ℂ)*s) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn)]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnR.le]
  rw [term_of_ne_zero hn,hpow,div_eq_mul_inv,← Complex.exp_neg]
  congr 2
  ring

/-- Exact separation of decay and vertical phase for a scaled jet term. -/
theorem jetTerm_line (r sigma : ℝ) (k n : ℕ) (t : ℝ) :
    jetTerm k ((r : ℂ)*((sigma : ℂ)+(t : ℂ)*I)) n =
      jetTerm k ((r*sigma : ℝ) : ℂ) n * expChar (-r*Real.log n) t := by
  by_cases hn : n = 0
  · subst n
    simp [jetTerm]
  · rw [jetTerm,jetTerm,term_eq_exp _ _ hn,term_eq_exp _ _ hn]
    have he : Complex.exp (-((r : ℂ)*((sigma : ℂ)+(t : ℂ)*I))*(Real.log n : ℂ)) =
        Complex.exp (-((r*sigma : ℝ) : ℂ)*(Real.log n : ℂ)) *
          expChar (-r*Real.log n) t := by
      rw [expChar,← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring

/-- The physical-line coefficient of a prime-power term of an actual dilation jet. -/
def primeAmplitude (r sigma : ℝ) (k : ℕ) (pm : Nat.Primes × ℕ) : ℂ :=
  (r : ℂ)^(k+1) * (-1 : ℂ)^k * jetTerm k ((r*sigma : ℝ) : ℂ) (pm.1.val^(pm.2+1))

/-- Every actual dilation jet on a convergence line is the stated prime-power exponential series. -/
theorem source_jet_line_eq_expSeries (r sigma : ℝ) (k : ℕ) (hs : 1 < r*sigma) (t : ℝ) :
    iteratedDeriv k (source r) ((sigma : ℂ)+(t : ℂ)*I) =
      expSeriesCarrier (primeAmplitude r sigma k)
        (fun pm : Nat.Primes × ℕ => -r*Real.log ((pm.1.val^(pm.2+1) : ℕ) : ℝ)) t := by
  rw [source_jet_eq_LSeries r k (by simpa using hs)]
  change (r : ℂ)^(k+1) * (-1 : ℂ)^k *
    (∑' n, jetTerm k ((r : ℂ)*((sigma : ℂ)+(t : ℂ)*I)) n) = _
  rw [tsum_jetTerm_eq_primePowers,expSeriesCarrier,← tsum_mul_left]
  apply tsum_congr
  intro pm
  rw [jetTerm_line]
  simp only [primeAmplitude]
  ring

/-- Absolute summability needed for polynomial products of the physical-line jets. -/
theorem summable_norm_primeAmplitude (r sigma : ℝ) (k : ℕ) (hs : 1 < r*sigma) :
    Summable fun pm => ‖primeAmplitude r sigma k pm‖ := by
  have hsum := summable_norm_primePowers k (s := ((r*sigma : ℝ) : ℂ)) (by simpa using hs)
  simpa only [primeAmplitude,norm_mul] using
    hsum.mul_left (‖(r : ℂ)^(k+1)‖ * ‖(-1 : ℂ)^k‖)

/-- The literal prime-power jet coefficient, with its common decay factor displayed. -/
theorem primeAmplitude_eq (r sigma : ℝ) (k : ℕ) (p : Nat.Primes) (m : ℕ) :
    primeAmplitude r sigma k (p,m) =
      (r : ℂ) * (-((m+1 : ℕ) : ℂ)*(r : ℂ))^k * (Real.log p.val : ℂ)^(k+1) *
        Complex.exp (-(((m+1 : ℕ) : ℝ)*r*sigma*Real.log p.val : ℝ) : ℂ) := by
  have hn : p.val^(m+1) ≠ 0 := pow_ne_zero _ p.property.ne_zero
  have hlR : Real.log ((p.val^(m+1) : ℕ) : ℝ) =
      ((m+1 : ℕ) : ℝ)*Real.log (p.val : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlC : Complex.log ((p.val^(m+1) : ℕ) : ℂ) =
      ((m+1 : ℕ) : ℂ)*(Real.log p.val : ℂ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_log (Nat.cast_nonneg _),hlR,
      Complex.ofReal_mul,Complex.ofReal_natCast]
  rw [primeAmplitude,jetTerm,term_eq_exp _ _ hn,logMul_iterate_apply,hlC,
    vonMangoldt_apply_pow (Nat.succ_ne_zero m),vonMangoldt_apply_prime p.property]
  have he : Complex.exp (-((r*sigma : ℝ) : ℂ)*(Real.log ((p.val^(m+1) : ℕ) : ℝ) : ℂ)) =
      Complex.exp (-(((m+1 : ℕ) : ℝ)*r*sigma*Real.log p.val : ℝ) : ℂ) := by
    rw [hlR]
    congr 1
    push_cast
    ring
  rw [he]
  simp only [mul_pow,pow_succ]
  ring

#print axioms source_jet_eq_LSeries
#print axioms summable_norm_jetTerm
#print axioms tsum_jetTerm_eq_primePowers
#print axioms summable_norm_primePowers
#print axioms jetTerm_line
#print axioms source_jet_line_eq_expSeries
#print axioms summable_norm_primeAmplitude
#print axioms primeAmplitude_eq
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilatedVonMangoldt
