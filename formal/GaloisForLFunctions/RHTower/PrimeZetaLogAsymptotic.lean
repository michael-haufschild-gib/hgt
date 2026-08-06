import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The prime zeta function near the abscissa

For real `s > 1` the Euler product gives

```text
∑_p -log(1 - p^(-s)) = log ζ(s),
```

so the prime zeta function `P(s) = ∑_p p^(-s)` satisfies `P(s) = log ζ(s) - D(s)`, where

```text
D(s) = ∑_p (-log(1 - p^(-s)) - p^(-s))
```

is the convergent higher-prime-power defect.  Since `log ζ(s) + log(s - 1) → 0` and `D` is
continuous from the right at `1`,

```text
P(s) + log(s - 1) → -D(1) = ∑_p (log(1 - 1/p) + 1/p).
```
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Logarithm of a positive infinite product -/

theorem hasSum_log_of_hasProd {ι : Type*} {f : ι → ℝ} {a : ℝ}
    (hf : ∀ i, 0 < f i) (ha : 0 < a) (h : HasProd f a) :
    HasSum (fun i => Real.log (f i)) (Real.log a) := by
  have hcont : ContinuousAt Real.log a := Real.continuousAt_log ha.ne'
  have hcomp := hcont.tendsto.comp h
  refine hcomp.congr fun t => ?_
  rw [Function.comp_apply]
  exact Real.log_prod fun i _ => (hf i).ne'

/-! ## The real Euler product for zeta -/

private theorem primeFactor_pos {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    0 < (1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹ := by
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have hlt : ((p : ℕ) : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have : 0 < 1 - ((p : ℕ) : ℝ) ^ (-s) := by linarith
  positivity

theorem hasProd_primeEulerFactor {s : ℝ} (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => (1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹) (riemannZeta s).re := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hC := riemannZeta_eulerProduct_hasProd hsC
  have hCreal : ∀ p : Nat.Primes,
      (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))⁻¹ = ((((1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹ : ℝ)) : ℂ) := by
    intro p
    have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := by positivity
    have hcast : ((p : ℕ) : ℂ) ^ (-(s : ℂ)) = ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp0]
      norm_cast
    rw [hcast]
    push_cast
    ring
  have hC' : HasProd (fun p : Nat.Primes =>
      ((((1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹ : ℝ)) : ℂ)) (riemannZeta s) := by
    have hfun : (fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-(s : ℂ)))⁻¹) =
        fun p : Nat.Primes => ((((1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹ : ℝ)) : ℂ) := funext hCreal
    rwa [hfun] at hC
  have hre := (Complex.continuous_re.tendsto _).comp hC'
  refine hre.congr fun t => ?_
  rw [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]

theorem hasSum_negLog_primeEulerFactor {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : Nat.Primes => -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)))
      (Real.log (riemannZeta s).re) := by
  have hzpos : 0 < (riemannZeta s).re := riemannZeta_re_pos_of_one_lt hs
  have h := hasSum_log_of_hasProd (fun p => primeFactor_pos hs p) hzpos
    (hasProd_primeEulerFactor hs)
  have hfun : (fun p : Nat.Primes => Real.log ((1 - ((p : ℕ) : ℝ) ^ (-s))⁻¹)) =
      fun p : Nat.Primes => -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) := by
    funext p
    rw [Real.log_inv]
  rwa [hfun] at h

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The higher-prime-power defect -/

theorem negLog_sub_self_nonneg {x : ℝ} (hx : x < 1) : 0 ≤ -Real.log (1 - x) - x := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - x by linarith)
  linarith

theorem negLog_sub_self_le {x : ℝ} (_hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 - x) by positivity)
  rw [Real.log_div one_ne_zero hpos.ne', Real.log_one, zero_sub] at h
  have h2 : 1 / (1 - x) - 1 = x / (1 - x) := by
    field_simp
    ring
  rw [h2] at h
  have h3 : x / (1 - x) - x ≤ 2 * x ^ 2 := by
    have hkey : x / (1 - x) - x = x ^ 2 / (1 - x) := by
      field_simp
      ring
    rw [hkey, div_le_iff₀ hpos]
    nlinarith [sq_nonneg x]
  linarith

/-- The prime zeta function `P(s) = ∑_p p^(-s)`. -/
def primeZeta (s : ℝ) : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)

/-- The higher-prime-power defect `D(s) = ∑_p (-log(1 - p^(-s)) - p^(-s))`. -/
def primeLogDefect (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, (-Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s))

private theorem prime_rpow_le_half {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have h1 : ((p : ℕ) : ℝ) ^ (-s) ≤ ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) = (((p : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
  rw [h2] at h1
  have h3 : (((p : ℕ) : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [one_div, inv_le_inv₀ hp0 (by norm_num)]
    exact hp2
  linarith

private theorem prime_rpow_pos {s : ℝ} (p : Nat.Primes) : 0 < ((p : ℕ) : ℝ) ^ (-s) := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  exact Real.rpow_pos_of_pos hp0 _

theorem summable_primeSquareRecip :
    Summable (fun p : Nat.Primes => 2 * (((p : ℕ) : ℝ))⁻¹ ^ 2) := by
  have h : Summable (fun n : ℕ => ((n : ℝ))⁻¹ ^ 2) := by
    have := Real.summable_one_div_nat_rpow (p := (2 : ℝ)).mpr (by norm_num)
    refine this.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
  exact ((h.subtype (fun p : ℕ => p.Prime)).mul_left 2)

theorem summable_primeLogDefectTerm {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun p : Nat.Primes =>
      -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s)) := by
  refine Summable.of_nonneg_of_le
    (fun p => negLog_sub_self_nonneg (lt_of_le_of_lt (prime_rpow_le_half hs p) (by norm_num)))
    (fun p => ?_) summable_primeSquareRecip
  have hle := prime_rpow_le_half hs p
  have hpos := prime_rpow_pos (s := s) p
  refine le_trans (negLog_sub_self_le hpos.le hle) ?_
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have h1 : ((p : ℕ) : ℝ) ^ (-s) ≤ (((p : ℕ) : ℝ))⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := ((p : ℕ) : ℝ)) (by linarith)
      (show -s ≤ -(1 : ℝ) by linarith)
    rwa [Real.rpow_neg_one] at h
  have hnn : (0 : ℝ) ≤ (((p : ℕ) : ℝ))⁻¹ := by positivity
  nlinarith [hpos.le, sq_nonneg (((p : ℕ) : ℝ)⁻¹ - ((p : ℕ) : ℝ) ^ (-s))]

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The prime zeta asymptotic -/

theorem summable_primeZetaTerm {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) :=
    Real.summable_one_div_nat_rpow.mpr hs
  have h' : Summable (fun n : ℕ => ((n : ℝ)) ^ (-s)) := by
    refine h.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  exact h'.subtype _

theorem primeZeta_add_primeLogDefect {s : ℝ} (hs : 1 < s) :
    primeZeta s + primeLogDefect s = Real.log (riemannZeta s).re := by
  have h1 := summable_primeZetaTerm hs
  have h2 := summable_primeLogDefectTerm hs.le
  have h := hasSum_negLog_primeEulerFactor hs
  have hadd : HasSum (fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-s) + (-Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s)))
      (primeZeta s + primeLogDefect s) := h1.hasSum.add h2.hasSum
  have hfun : (fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-s) + (-Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s))) =
      fun p : Nat.Primes => -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) := by
    funext p
    ring
  rw [hfun] at hadd
  exact hadd.unique h

private theorem continuousAt_primeLogDefectTerm (p : Nat.Primes) :
    ContinuousAt (fun s : ℝ =>
      -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s)) - ((p : ℕ) : ℝ) ^ (-s)) 1 := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hle := prime_rpow_le_half (s := (1 : ℝ)) le_rfl p
  have hne : (1 : ℝ) - ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) ≠ 0 := by
    have := prime_rpow_pos (s := (1 : ℝ)) p
    intro h
    rw [sub_eq_zero] at h
    linarith [hle, h]
  have hrpow : ContinuousAt (fun s : ℝ => ((p : ℕ) : ℝ) ^ (-s)) 1 := by
    have : Continuous (fun s : ℝ => ((p : ℕ) : ℝ) ^ (-s)) := by
      simp_rw [Real.rpow_def_of_pos hp0]
      fun_prop
    exact this.continuousAt
  exact (((continuousAt_const.sub hrpow).log hne).neg).sub hrpow

theorem tendsto_primeLogDefect :
    Tendsto primeLogDefect (nhdsWithin 1 (Ioi 1)) (nhds (primeLogDefect 1)) := by
  refine tendsto_tsum_of_dominated_convergence summable_primeSquareRecip (fun p => ?_) ?_
  · exact ((continuousAt_primeLogDefectTerm p).tendsto).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs p
    have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
    have hle := prime_rpow_le_half hs1 p
    have hpos := prime_rpow_pos (s := s) p
    have hnn := negLog_sub_self_nonneg (lt_of_le_of_lt hle (by norm_num) :
      ((p : ℕ) : ℝ) ^ (-s) < 1)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine le_trans (negLog_sub_self_le hpos.le hle) ?_
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
    have h1 : ((p : ℕ) : ℝ) ^ (-s) ≤ (((p : ℕ) : ℝ))⁻¹ := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := ((p : ℕ) : ℝ)) (by linarith)
        (show -s ≤ -(1 : ℝ) by linarith)
      rwa [Real.rpow_neg_one] at h
    have hnn2 : (0 : ℝ) ≤ (((p : ℕ) : ℝ))⁻¹ := by positivity
    nlinarith [hpos.le]

/-- **The prime zeta asymptotic at the abscissa.**  `∑_p p^(-s) + log(s-1)` converges, as `s → 1⁺`,
to the negative of the higher-prime-power defect. -/
theorem tendsto_primeZeta_add_log_sub :
    Tendsto (fun s : ℝ => primeZeta s + Real.log (s - 1)) (nhdsWithin 1 (Ioi 1))
      (nhds (-primeLogDefect 1)) := by
  have hzeta : Tendsto (fun s : ℝ => Real.log (riemannZeta s).re + Real.log (s - 1))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp log_riemannZeta_add_log_sub_isLittleO_ofReal
  have hcomb := hzeta.sub tendsto_primeLogDefect
  rw [zero_sub] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [← primeZeta_add_primeLogDefect hs]
  ring

end

end RHTower
