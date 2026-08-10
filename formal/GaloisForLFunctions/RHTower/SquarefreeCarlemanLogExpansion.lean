import GaloisForLFunctions.RHTower.SquarefreeCarlemanDeterminant
import GaloisForLFunctions.HTGeometry.FredholmDeterminantZeta

/-!
# The Carleman log-determinant as a prime-zeta series, and the first-trace current split

Expanding each Carleman-corrected Euler logarithm in its Taylor series and summing over primes
gives

```text
log D₂(s) = ∑_{k ≥ 2} (-1)^{k+1} P(k s)/k,
```

a series of prime zeta values that already converges on `Re s > 1/2`, because every exponent `k s`
there has real part exceeding one.  Differentiating the factorization `Z = D₂ · exp P` splits the
squarefree fixed current into the regular determinant part and the single first-trace term

```text
J_sq(s) = -D₂'(s)/D₂(s) - P'(s),      -P'(s) = ∑_p (log p) p^{-s}.
```
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-! ## The prime-power expansion of the Carleman logarithm -/

/-- The `(p, n)` term of the Carleman log expansion, `-((-p^{-s})^{n+2}/(n+2))`. -/
def carlemanExpansionTerm (s : ℂ) (pn : Nat.Primes × ℕ) : ℂ :=
  -((-coronaPrimeEigenvalue s pn.1) ^ (pn.2 + 2) / ((pn.2 + 2 : ℕ) : ℂ))

theorem hasSum_carlemanExpansionTerm_fiber {s : ℂ} (hs : 1 / 2 ≤ s.re) (p : Nat.Primes) :
    HasSum (fun n : ℕ => carlemanExpansionTerm s (p, n)) (squarefreeCarlemanLogFactor s p) := by
  have hnorm : ‖-coronaPrimeEigenvalue s p‖ < 1 := by
    rw [norm_neg]
    have := norm_coronaPrimeEigenvalue_le hs p
    linarith
  have h := (HilbertSchmidt.hasSum_peri (-coronaPrimeEigenvalue s p) hnorm).neg
  have hval : -(-((-coronaPrimeEigenvalue s p) +
      Complex.log (1 - -coronaPrimeEigenvalue s p))) = squarefreeCarlemanLogFactor s p := by
    rw [squarefreeCarlemanLogFactor, coronaEulerMultiplier, sub_neg_eq_add]
    ring
  rw [hval] at h
  exact h

theorem norm_carlemanExpansionTerm_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (pn : Nat.Primes × ℕ) :
    ‖carlemanExpansionTerm s pn‖ ≤
      ‖coronaPrimeEigenvalue s pn.1‖ ^ 2 * (3 / 4 : ℝ) ^ pn.2 := by
  have hle : ‖coronaPrimeEigenvalue s pn.1‖ ≤ 3 / 4 := norm_coronaPrimeEigenvalue_le hs pn.1
  have hnn : (0 : ℝ) ≤ ‖coronaPrimeEigenvalue s pn.1‖ := norm_nonneg _
  have hden : (1 : ℝ) ≤ ((pn.2 + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ pn.2 + 2)
  have hnormval : ‖carlemanExpansionTerm s pn‖ =
      ‖coronaPrimeEigenvalue s pn.1‖ ^ (pn.2 + 2) / ((pn.2 + 2 : ℕ) : ℝ) := by
    rw [carlemanExpansionTerm, norm_neg, norm_div, norm_pow, norm_neg, Complex.norm_natCast]
  rw [hnormval]
  calc ‖coronaPrimeEigenvalue s pn.1‖ ^ (pn.2 + 2) / ((pn.2 + 2 : ℕ) : ℝ)
      ≤ ‖coronaPrimeEigenvalue s pn.1‖ ^ (pn.2 + 2) := div_le_self (by positivity) hden
    _ = ‖coronaPrimeEigenvalue s pn.1‖ ^ 2 * ‖coronaPrimeEigenvalue s pn.1‖ ^ pn.2 := by
        rw [← pow_add, add_comm]
    _ ≤ ‖coronaPrimeEigenvalue s pn.1‖ ^ 2 * (3 / 4 : ℝ) ^ pn.2 := by
        gcongr

theorem summable_norm_carlemanExpansionTerm {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun pn : Nat.Primes × ℕ => ‖carlemanExpansionTerm s pn‖) := by
  have hgeo : Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmaj : Summable (fun pn : Nat.Primes × ℕ =>
      ‖coronaPrimeEigenvalue s pn.1‖ ^ 2 * (3 / 4 : ℝ) ^ pn.2) :=
    Summable.mul_of_nonneg (summable_norm_sq_coronaPrimeEigenvalue hs) hgeo
      (fun p => by positivity) (fun n => by positivity)
  exact Summable.of_nonneg_of_le (fun pn => norm_nonneg _)
    (fun pn => norm_carlemanExpansionTerm_le (le_of_lt hs) pn) hmaj

theorem summable_carlemanExpansionTerm {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (carlemanExpansionTerm s) :=
  Summable.of_norm (summable_norm_carlemanExpansionTerm hs)

theorem squarefreeCarlemanLogDet_eq_tsum_prod {s : ℂ} (hs : 1 / 2 < s.re) :
    squarefreeCarlemanLogDet s = ∑' pn : Nat.Primes × ℕ, carlemanExpansionTerm s pn := by
  rw [(summable_carlemanExpansionTerm hs).tsum_prod, squarefreeCarlemanLogDet]
  exact tsum_congr fun p =>
    ((hasSum_carlemanExpansionTerm_fiber (le_of_lt hs) p).tsum_eq).symm

/-! ## The prime-zeta series -/

theorem carlemanExpansionTerm_eq (s : ℂ) (p : Nat.Primes) (n : ℕ) :
    carlemanExpansionTerm s (p, n) =
      (-1 : ℂ) ^ (n + 1) / ((n + 2 : ℕ) : ℂ) *
        coronaPrimeEigenvalue (((n + 2 : ℕ) : ℂ) * s) p := by
  rw [carlemanExpansionTerm, coronaPrimeEigenvalue, coronaPrimeEigenvalue,
    show -((((n + 2 : ℕ) : ℂ)) * s) = ((n + 2 : ℕ) : ℂ) * (-s) by ring,
    Complex.cpow_nat_mul, neg_pow, pow_succ, pow_succ, pow_succ]
  ring

theorem tsum_carlemanExpansionTerm_prime (s : ℂ) (n : ℕ) :
    ∑' p : Nat.Primes, carlemanExpansionTerm s (p, n) =
      (-1 : ℂ) ^ (n + 1) * coronaPrimeZeta (((n + 2 : ℕ) : ℂ) * s) / ((n + 2 : ℕ) : ℂ) := by
  rw [show (fun p : Nat.Primes => carlemanExpansionTerm s (p, n)) =
      fun p : Nat.Primes => (-1 : ℂ) ^ (n + 1) / ((n + 2 : ℕ) : ℂ) *
        coronaPrimeEigenvalue (((n + 2 : ℕ) : ℂ) * s) p from
    funext fun p => carlemanExpansionTerm_eq s p n]
  rw [tsum_mul_left, coronaPrimeZeta]
  ring

/-- **The Carleman log-determinant is the alternating prime-zeta series.**  On `Re s > 1/2`,
`log D₂(s) = ∑_{k ≥ 2} (-1)^{k+1} P(k s)/k`. -/
theorem squarefreeCarlemanLogDet_eq_tsum_primeZeta {s : ℂ} (hs : 1 / 2 < s.re) :
    squarefreeCarlemanLogDet s =
      ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * coronaPrimeZeta (((n + 2 : ℕ) : ℂ) * s) /
        ((n + 2 : ℕ) : ℂ) := by
  have hswap :
      ∑' n : ℕ, ∑' p : Nat.Primes, carlemanExpansionTerm s (p, n) =
        ∑' p : Nat.Primes, ∑' n : ℕ, carlemanExpansionTerm s (p, n) :=
    Summable.tsum_comm (f := fun p n => carlemanExpansionTerm s (p, n))
      (summable_carlemanExpansionTerm hs)
  rw [squarefreeCarlemanLogDet_eq_tsum_prod hs, (summable_carlemanExpansionTerm hs).tsum_prod,
    ← hswap]
  exact tsum_congr fun n => tsum_carlemanExpansionTerm_prime s n

/-! ## The first-trace current split -/

theorem differentiableOn_coronaPrimeZeta {b : ℝ} (hb : 1 < b) :
    DifferentiableOn ℂ coronaPrimeZeta {s : ℂ | b < s.re} := by
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-b))
    (Nat.Primes.summable_rpow.mpr (by linarith))
    (fun p => (differentiable_primeCpowNeg p).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re) ?_
  intro p w hw
  have hwre : b < w.re := hw
  rw [norm_coronaPrimeEigenvalue]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast p.prop.one_lt.le) (by linarith)

theorem differentiableAt_coronaPrimeZeta {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ coronaPrimeZeta s := by
  set b : ℝ := (1 + s.re) / 2 with hbdef
  have hb : 1 < b := by rw [hbdef]; linarith
  have hbs : b < s.re := by rw [hbdef]; linarith
  have hopen : IsOpen {z : ℂ | b < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact (differentiableOn_coronaPrimeZeta hb).differentiableAt (hopen.mem_nhds hbs)

theorem hasDerivAt_coronaPrimeEigenvalue (s : ℂ) (p : Nat.Primes) :
    HasDerivAt (fun w : ℂ => coronaPrimeEigenvalue w p)
      (-((Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p)) s := by
  have hne : (((p : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr p.prop.ne_zero
  have hneg : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) s := hasDerivAt_neg' s
  have h : HasDerivAt (fun w : ℂ => ((p : ℕ) : ℂ) ^ (-w))
      (((p : ℕ) : ℂ) ^ (-s) * Complex.log ((p : ℕ) : ℂ) * (-1)) s :=
    hneg.const_cpow (Or.inl hne)
  have hval : ((p : ℕ) : ℂ) ^ (-s) * Complex.log ((p : ℕ) : ℂ) * (-1) =
      -((Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p) := by
    rw [coronaPrimeEigenvalue, Complex.natCast_log]
    ring
  rw [hval] at h
  exact h

/-- **The first trace of the current.**  `-P'(s) = ∑_p (log p) p^{-s}` on `Re s > 1`. -/
theorem hasSum_neg_deriv_coronaPrimeZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes => (Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p)
      (-deriv coronaPrimeZeta s) := by
  set b : ℝ := (1 + s.re) / 2 with hbdef
  have hb : 1 < b := by rw [hbdef]; linarith
  have hbs : b < s.re := by rw [hbdef]; linarith
  have hopen : IsOpen {z : ℂ | b < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hderiv := Complex.hasSum_deriv_of_summable_norm
    (u := fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-b))
    (F := fun (p : Nat.Primes) (w : ℂ) => coronaPrimeEigenvalue w p)
    (Nat.Primes.summable_rpow.mpr (by linarith))
    (fun p => (differentiable_primeCpowNeg p).differentiableOn) hopen
    (fun p w hw => by
      have hwre : b < w.re := hw
      rw [norm_coronaPrimeEigenvalue]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast p.prop.one_lt.le) (by linarith))
    (show s ∈ {z : ℂ | b < z.re} from hbs)
  have hterm : ∀ p : Nat.Primes,
      deriv (fun w : ℂ => coronaPrimeEigenvalue w p) s =
        -((Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p) :=
    fun p => (hasDerivAt_coronaPrimeEigenvalue s p).deriv
  have hderiv' : HasSum
      (fun p : Nat.Primes => -((Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p))
      (deriv coronaPrimeZeta s) := by
    refine hderiv.congr_fun ?_
    intro p
    exact (hterm p).symm
  simpa using hderiv'.neg

theorem tsum_neg_deriv_coronaPrimeZeta {s : ℂ} (hs : 1 < s.re) :
    -deriv coronaPrimeZeta s =
      ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) * coronaPrimeEigenvalue s p :=
  (hasSum_neg_deriv_coronaPrimeZeta hs).tsum_eq.symm

/-- **The first-trace split of the squarefree fixed current.**  On `Re s > 1`,
`J_sq(s) = -D₂'(s)/D₂(s) - P'(s)`: the whole divisor-bearing part of the logarithmic current is the
single trace-class term. -/
theorem squarefreeFixedCurrent_eq_carleman_logDeriv_sub_deriv {s : ℂ} (hs : 1 < s.re) :
    GaloisForLFunctions.squarefreeFixedCurrent s =
      -logDeriv squarefreeCarlemanDet s - deriv coronaPrimeZeta s := by
  have hhalf : 1 / 2 < s.re := by linarith
  have hopen : IsOpen {z : ℂ | 1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hopenHalf : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hPdiff : DifferentiableAt ℂ coronaPrimeZeta s := differentiableAt_coronaPrimeZeta hs
  have hDdiff : DifferentiableAt ℂ squarefreeCarlemanDet s :=
    differentiableOn_squarefreeCarlemanDet.differentiableAt (hopenHalf.mem_nhds hhalf)
  have hexpdiff : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (coronaPrimeZeta w)) s :=
    hPdiff.cexp
  have hev : GaloisForLFunctions.squarefreePartition =ᶠ[𝓝 s]
      fun w : ℂ => squarefreeCarlemanDet w * Complex.exp (coronaPrimeZeta w) := by
    filter_upwards [hopen.mem_nhds hs] with w hw
    exact squarefreePartition_eq_carleman_mul_exp hw
  have hlogeq : logDeriv GaloisForLFunctions.squarefreePartition s =
      logDeriv (fun w : ℂ => squarefreeCarlemanDet w * Complex.exp (coronaPrimeZeta w)) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hlogexp : logDeriv (fun w : ℂ => Complex.exp (coronaPrimeZeta w)) s =
      deriv coronaPrimeZeta s := by
    rw [logDeriv_apply, (hPdiff.hasDerivAt.cexp).deriv]
    field_simp
  have hlogmul :
      logDeriv (fun w : ℂ => squarefreeCarlemanDet w * Complex.exp (coronaPrimeZeta w)) s =
        logDeriv squarefreeCarlemanDet s +
          logDeriv (fun w : ℂ => Complex.exp (coronaPrimeZeta w)) s :=
    logDeriv_mul s (squarefreeCarlemanDet_ne_zero s) (Complex.exp_ne_zero _) hDdiff hexpdiff
  rw [← GaloisForLFunctions.neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent hs,
    hlogeq, hlogmul, hlogexp]
  ring

end RHTower
