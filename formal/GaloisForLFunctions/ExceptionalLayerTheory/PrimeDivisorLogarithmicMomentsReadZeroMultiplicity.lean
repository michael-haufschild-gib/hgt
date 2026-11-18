import GaloisForLFunctions.ExceptionalLayerTheory.EveryFiniteCofactorSeesTheOrdinaryPrimeCount
import GaloisForLFunctions.RHTower.ExactNullCertificateOrderTransfer
import GaloisForLFunctions.RHTower.BurnolTwoPointMinimality
import GaloisForLFunctions.RHTower.PrimeZetaOneLineConvergence

/-!
# Logarithmic moments of the distinct prime divisors

The ordinary prime logarithm has a simple pole at each right zero, regardless
of multiplicity. Each derivative increases the pole order by one. Each
unrestricted integer factor contributes the entire zeta-zero multiplicity
in the opposite direction.
-/

noncomputable section

open Complex Filter Topology Set Finset ArithmeticFunction
open scoped LSeries.notation

namespace GaloisForLFunctions.ExceptionalLayerTheory
open _root_.RHTower.ExactNullDivisorTransfer

/-- The atom at an ordinary prime carries a specified logarithmic power. -/
def primeLogMomentAtom (k n : ℕ) : ℂ := if n.Prime then ((Real.log n:ℝ):ℂ)^k else 0

/-- The finite coefficient sum with r unrestricted factors equals the
ordinary-prime sum weighted by the divisor prefix through the quotient. -/
theorem primeLogMomentAtom_divisor_prefix (r k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (divisorPow r ⍟ primeLogMomentAtom k) n) =
      ∑ p ∈ Nat.primesLE N, (Real.log p:ℂ)^k *
        ∑ m ∈ Finset.Icc 1 (N/p), divisorPow r m := by
  let D : ArithmeticFunction ℂ := ⟨divisorPow r, by simp [divisorPow]⟩
  let A : ArithmeticFunction ℂ := ⟨primeLogMomentAtom k, by simp [primeLogMomentAtom,Nat.not_prime_zero]⟩
  change (∑ n ∈ Finset.Icc 1 N, (⇑D ⍟ ⇑A) n)=_
  rw [ArithmeticFunction.coe_mul,mul_comm D A,_root_.RHTower.sum_Icc_mul_apply,
    Nat.primesLE_eq_filter_Icc_one,Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  change (if p.Prime then (Real.log p:ℂ)^k else 0)*_ = _
  split <;> simp_all only [zero_mul,D,ArithmeticFunction.coe_mk]

/-- A single unrestricted factor counts the multiples of each prime. -/
theorem primeLogMomentAtom_floor (k N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (divisorPow 1 ⍟ primeLogMomentAtom k) n) =
      ∑ p ∈ Nat.primesLE N, (Real.log p:ℂ)^k*((N/p:ℕ):ℂ) := by
  rw [primeLogMomentAtom_divisor_prefix]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  have he : (∑ m ∈ Finset.Icc 1 (N/p), divisorPow 1 m) =
      ∑ _ ∈ Finset.Icc 1 (N/p), (1:ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    simp [divisorPow,ArithmeticFunction.natCoe_apply,ArithmeticFunction.zeta_apply,
      Nat.ne_of_gt (Finset.mem_Icc.mp hm).1]
  simpa using he

private theorem log_iterate (k : ℕ) :
    (LSeries.logMul^[k] (_root_.RHTower.primeLogCoeff))=primeLogMomentAtom (k+1) := by
  induction k with
  | zero => funext n; simp [primeLogMomentAtom,_root_.RHTower.primeLogCoeff]
  | succ j ih =>
    rw [Function.iterate_succ',Function.comp_apply,ih]
    funext n
    by_cases h : n.Prime <;> simp [primeLogMomentAtom,LSeries.logMul,h,← Complex.natCast_log,pow_succ,mul_comm]

private theorem log_abscissa : LSeries.abscissaOfAbsConv _root_.RHTower.primeLogCoeff≤(1:ℝ) := by
  let f := fun n : ℕ => if n.Prime then (1:ℂ) else 0
  have hf : LSeries.logMul f=_root_.RHTower.primeLogCoeff := by
    funext n
    by_cases hp : n.Prime <;> simp [f,LSeries.logMul,_root_.RHTower.primeLogCoeff,hp,Complex.natCast_log]
  rw [← hf,LSeries.abscissaOfAbsConv_logMul]
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro x hx
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ (by simpa using hx)
  intro n _
  by_cases hp : n.Prime <;> simp [f,hp]

private theorem log_series {s : ℂ} (hs : 1<s.re) :
    _root_.RHTower.xiPrimeLogDirichletContinuation s=LSeries _root_.RHTower.primeLogCoeff s := by
  rw [_root_.RHTower.xiPrimeLogDirichletContinuation_eq hs,
    _root_.RHTower.xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs,LSeries]
  let g := fun n : ℕ => (Real.log n:ℂ)/(n:ℂ)^s
  have he : LSeries.term _root_.RHTower.primeLogCoeff s={n:ℕ | n.Prime}.indicator g := by
    funext n
    by_cases hp : n.Prime
    · rw [LSeries.term_of_ne_zero hp.ne_zero,Set.indicator_of_mem (show n∈{m:ℕ | m.Prime} from hp)]
      simp only [_root_.RHTower.primeLogCoeff,if_pos hp,g]
    · simp [LSeries.term,_root_.RHTower.primeLogCoeff,g,Set.indicator,hp]
  rw [he,← _root_.tsum_subtype]
  exact tsum_congr fun p : Nat.Primes => by simp [g]

/-- The continuation before the harmless sign coming from logarithmic derivatives. -/
def primeLogDivisorSymbol (r j : ℕ) : ℂ → ℂ :=
  (riemannZeta^r)*iteratedDeriv j _root_.RHTower.xiPrimeLogDirichletContinuation

/-- On the Euler half-plane the symbol is the genuine Dirichlet convolution
of the r-fold divisor coefficient and the (j+1)-st ordinary prime logarithm. -/
theorem primeLogDivisorSymbol_euler {r : ℕ} (hr : 1≤r) (j : ℕ) {s : ℂ} (hs : 1<s.re) :
    primeLogDivisorSymbol r j s=(-1:ℂ)^j*LSeries (divisorPow r ⍟ primeLogMomentAtom (j+1)) s := by
  have hb := log_abscissa.trans_lt (show ((1:ℝ):EReal)<(s.re:EReal) by exact_mod_cast hs)
  have hlog : _root_.RHTower.xiPrimeLogDirichletContinuation =ᶠ[𝓝 s] LSeries _root_.RHTower.primeLogCoeff := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz using log_series hz
  have he := hlog.iteratedDeriv_eq j
  rw [LSeries_iteratedDeriv j hb,log_iterate] at he
  have hsum : LSeriesSummable (primeLogMomentAtom (j+1)) s := by
    rw [← log_iterate]
    exact LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa only [LSeries.absicssaOfAbsConv_logPowMul] using hb)
  have hd := riemannZeta_pow_eq_tsum hs hr
  rw [primeLogDivisorSymbol,Pi.mul_apply,Pi.pow_apply,he,LSeries_convolution' hd.1 hsum,hd.2]
  ring

private theorem log_pole {ρ : ℂ} (hb : 1/2<ρ.re) (hz : riemannZeta ρ=0) :
    MeromorphicAt _root_.RHTower.xiPrimeLogDirichletContinuation ρ ∧
    meromorphicOrderAt _root_.RHTower.xiPrimeLogDirichletContinuation ρ=((-1:ℤ):WithTop ℤ) := by
  have hζ := _root_.RHTower.meromorphicAt_riemannZeta_everywhere ρ
  have ht := (_root_.RHTower.differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re) ρ hb).meromorphicAt
  have hp : MeromorphicAt _root_.RHTower.xiPrimeLogDirichletContinuation ρ :=
    (hζ.deriv.div hζ).neg.sub ht
  obtain ⟨m,hm,hres⟩ := _root_.RHTower.xiPrimeLogDirichletContinuation_zero_residue hb hz
  exact ⟨hp,meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub (c := -(m:ℂ)) hp
    (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hres⟩

/-- Exact order of each filtered logarithmic moment at each right strip zero. -/
theorem primeLogDivisorSymbol_order (r j : ℕ) {ρ : ℂ} (hb : 1/2<ρ.re) (h1 : ρ.re<1)
    (hz : riemannZeta ρ=0) :
    meromorphicOrderAt (primeLogDivisorSymbol r j) ρ =
      (((r:ℤ)*((analyticOrderAt riemannZeta ρ).toNat:ℤ)-(j+1):ℤ):WithTop ℤ) := by
  obtain ⟨hm,ho⟩ := log_pole hb hz
  have hd (i : ℕ) : MeromorphicAt (iteratedDeriv i _root_.RHTower.xiPrimeLogDirichletContinuation) ρ ∧
      meromorphicOrderAt (iteratedDeriv i _root_.RHTower.xiPrimeLogDirichletContinuation) ρ =
        ((-((i:ℤ)+1):ℤ):WithTop ℤ) := by
    induction i with
    | zero => simpa only [iteratedDeriv_zero,Nat.cast_zero,zero_add] using And.intro hm ho
    | succ k ih =>
      rw [iteratedDeriv_succ]
      refine ⟨ih.1.deriv,?_⟩
      have hcast : (((-((k:ℤ)+1):ℤ):ℂ))≠0 := by
        exact_mod_cast (show -((k:ℤ)+1)≠0 by omega)
      rw [meromorphicOrderAt_deriv_eq_sub_one hcast ih.2]
      norm_cast
  have hz' := _root_.RHTower.meromorphicAt_riemannZeta_everywhere ρ
  rw [primeLogDivisorSymbol,meromorphicOrderAt_mul (hz'.pow _) (hd j).1,
    meromorphicOrderAt_pow hz',_root_.RHTower.meromorphicOrderAt_riemannZeta_eq_toNat_of_strip
      (by linarith only [hb]) h1,(hd j).2]
  norm_cast

end GaloisForLFunctions.ExceptionalLayerTheory
