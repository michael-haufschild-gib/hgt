import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.HTGeometry.SmoothNumbers
import GaloisForLFunctions.HTGeometry.ZetaMomentFunctionalEquation
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationHalfPlane
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldZetaPoleCarrier
import Mathlib

/-!
# The grade transform of a locally finite dilation datum and its inverse

The residue field of the grade-one prime source along a dilation ray is the Möbius transform of
the divisor datum, and the Lambert transform inverts it.  This file proves the exact inversion for
an arbitrary locally finite datum: the two transforms

`M(n) = -∑_r μ(r) ν(r n)/r`,  `ν(n) = -∑_k M(k n)/k`

are mutually inverse, by the divisor identity `∑_{r ∣ m} μ(r) = [m = 1]`.
-/

open ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace RHTower

noncomputable section

/-- The grade transform of a dilation datum: the Möbius transform along the ray. -/
def gradeMonodromyTransform (ν : ℕ → ℂ) (n : ℕ) : ℂ :=
  -∑' r : ℕ+, (moebius (r : ℕ) : ℂ) * ν ((r : ℕ) * n) / ((r : ℕ) : ℂ)

/-- The Lambert transform inverting the grade transform. -/
def gradeLambertTransform (M : ℕ → ℂ) (n : ℕ) : ℂ :=
  -∑' k : ℕ+, M ((k : ℕ) * n) / ((k : ℕ) : ℂ)

theorem sum_divisors_moebius_eq (m : ℕ) :
    ∑ d ∈ m.divisors, (moebius d : ℂ) = if m = 1 then 1 else 0 := by
  have hconv : ((moebius : ArithmeticFunction ℤ) * (ζ : ArithmeticFunction ℤ)) m
      = (1 : ArithmeticFunction ℤ) m := by
    rw [moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply] at hconv
  have hzeta : ∀ x ∈ m.divisorsAntidiagonal,
      (moebius x.1 : ℤ) * (ζ : ArithmeticFunction ℤ) x.2 = (moebius x.1 : ℤ) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have hx2 : x.2 ≠ 0 := by
      intro h0
      apply hx.2
      rw [← hx.1, h0, mul_zero]
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hx2]
    simp
  rw [Finset.sum_congr rfl hzeta] at hconv
  have hsum : ∑ x ∈ m.divisorsAntidiagonal, (moebius x.1 : ℤ) = ∑ d ∈ m.divisors, (moebius d : ℤ) :=
    Nat.sum_divisorsAntidiagonal (fun a _ => (moebius a : ℤ))
  rw [hsum] at hconv
  have hone : (1 : ArithmeticFunction ℤ) m = if m = 1 then 1 else 0 := by
    rw [ArithmeticFunction.one_apply]
  rw [hone] at hconv
  have hcast := congrArg (fun z : ℤ => (z : ℂ)) hconv
  push_cast at hcast
  rw [hcast]

/-- **Möbius pair regrouping.**  Summing a Möbius-weighted family over all factorizations
collapses it to the value at one. -/
theorem tsum_moebius_pair {F : ℕ → ℂ}
    (hsummable : Summable fun x : ℕ+ × ℕ+ =>
      (moebius (x.1 : ℕ) : ℂ) * F ((x.1 : ℕ) * (x.2 : ℕ))) :
    (∑' x : ℕ+ × ℕ+, (moebius (x.1 : ℕ) : ℂ) * F ((x.1 : ℕ) * (x.2 : ℕ))) = F 1 := by
  classical
  set G : ℕ+ × ℕ+ → ℂ := fun x => (moebius (x.1 : ℕ) : ℂ) * F ((x.1 : ℕ) * (x.2 : ℕ)) with hG
  have hpull : (∑' x : ℕ+ × ℕ+, G x)
      = ∑' p : (Σ m : ℕ+, Nat.divisorsAntidiagonal (m : ℕ)), G (sigmaAntidiagonalEquivProd p) :=
    (sigmaAntidiagonalEquivProd.tsum_eq G).symm
  have hsummableG : Summable fun p : (Σ m : ℕ+, Nat.divisorsAntidiagonal (m : ℕ)) =>
      G (sigmaAntidiagonalEquivProd p) :=
    (Equiv.summable_iff sigmaAntidiagonalEquivProd).mpr hsummable
  have hsigma : (∑' p : (Σ m : ℕ+, Nat.divisorsAntidiagonal (m : ℕ)),
        G (sigmaAntidiagonalEquivProd p))
      = ∑' m : ℕ+, ∑' q : Nat.divisorsAntidiagonal (m : ℕ),
          G (sigmaAntidiagonalEquivProd ⟨m, q⟩) := hsummableG.tsum_sigma
  have hinner : ∀ m : ℕ+, (∑' q : Nat.divisorsAntidiagonal (m : ℕ),
      G (sigmaAntidiagonalEquivProd ⟨m, q⟩)) = (if (m : ℕ) = 1 then F (m : ℕ) else 0) := by
    intro m
    have hterm : ∀ q : Nat.divisorsAntidiagonal (m : ℕ),
        G (sigmaAntidiagonalEquivProd ⟨m, q⟩) = (moebius (q.1.1) : ℂ) * F (m : ℕ) := by
      intro q
      have hprod : ((divisorsAntidiagonalFactors m q).1 : ℕ)
          * ((divisorsAntidiagonalFactors m q).2 : ℕ) = (m : ℕ) :=
        divisorsAntidiagonalFactors_eq q
      have hfst : ((divisorsAntidiagonalFactors m q).1 : ℕ) = q.1.1 := rfl
      show (moebius ((divisorsAntidiagonalFactors m q).1 : ℕ) : ℂ)
          * F (((divisorsAntidiagonalFactors m q).1 : ℕ)
            * ((divisorsAntidiagonalFactors m q).2 : ℕ)) = _
      rw [hprod, hfst]
    rw [tsum_congr hterm, Finset.tsum_subtype ((m : ℕ).divisorsAntidiagonal)
      (fun q : ℕ × ℕ => (moebius q.1 : ℂ) * F (m : ℕ)), ← Finset.sum_mul]
    have hdiv : ∑ q ∈ (m : ℕ).divisorsAntidiagonal, (moebius q.1 : ℂ)
        = ∑ d ∈ (m : ℕ).divisors, (moebius d : ℂ) :=
      Nat.sum_divisorsAntidiagonal (fun a _ => (moebius a : ℂ))
    rw [hdiv, sum_divisors_moebius_eq (m : ℕ)]
    by_cases hm1 : (m : ℕ) = 1
    · rw [if_pos hm1, if_pos hm1, one_mul]
    · rw [if_neg hm1, if_neg hm1, zero_mul]
  have hone : (∑' m : ℕ+, (if (m : ℕ) = 1 then F (m : ℕ) else 0)) = F 1 := by
    have hsingle : ∀ m : ℕ+, (if (m : ℕ) = 1 then F (m : ℕ) else 0)
        = if m = 1 then F 1 else 0 := by
      intro m
      by_cases hm : m = 1
      · subst hm
        simp
      · have hm' : (m : ℕ) ≠ 1 := fun h => hm (PNat.coe_injective (by simpa using h))
        rw [if_neg hm', if_neg hm]
    rw [tsum_congr hsingle, tsum_ite_eq]
  rw [hpull, hsigma, tsum_congr hinner, hone]

/-- The pair family whose double sum is the Lambert transform of the grade transform. -/
def gradePairFamily (ν : ℕ → ℂ) (n : ℕ) (x : ℕ+ × ℕ+) : ℂ :=
  (moebius (x.1 : ℕ) : ℂ) * ν ((x.1 : ℕ) * (x.2 : ℕ) * n) / (((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℂ)

theorem finite_support_gradePairFamily {ν : ℕ → ℂ} (hfin : (Function.support ν).Finite)
    {n : ℕ} (hn : 0 < n) : (Function.support (gradePairFamily ν n)).Finite := by
  classical
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hsub : Function.support (gradePairFamily ν n)
      ⊆ {x : ℕ+ × ℕ+ | (x.1 : ℕ) ≤ N ∧ (x.2 : ℕ) ≤ N} := by
    intro x hx
    have hν : ν ((x.1 : ℕ) * (x.2 : ℕ) * n) ≠ 0 := by
      intro h0
      apply hx
      rw [gradePairFamily, h0]
      simp
    have hmem : (x.1 : ℕ) * (x.2 : ℕ) * n ∈ Function.support ν := hν
    have hle : (x.1 : ℕ) * (x.2 : ℕ) * n ≤ N := hN hmem
    have h1 : (x.1 : ℕ) ≤ (x.1 : ℕ) * (x.2 : ℕ) * n := by
      have h2 : 1 ≤ (x.2 : ℕ) := x.2.property
      calc (x.1 : ℕ) = (x.1 : ℕ) * 1 * 1 := by ring
        _ ≤ (x.1 : ℕ) * (x.2 : ℕ) * n := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) hn
    have h2 : (x.2 : ℕ) ≤ (x.1 : ℕ) * (x.2 : ℕ) * n := by
      have h1' : 1 ≤ (x.1 : ℕ) := x.1.property
      calc (x.2 : ℕ) = 1 * (x.2 : ℕ) * 1 := by ring
        _ ≤ (x.1 : ℕ) * (x.2 : ℕ) * n := by
            exact Nat.mul_le_mul (Nat.mul_le_mul_right _ h1') hn
    exact ⟨le_trans h1 hle, le_trans h2 hle⟩
  refine Set.Finite.subset ?_ hsub
  have hfin1 : {m : ℕ+ | (m : ℕ) ≤ N}.Finite := by
    have hinj : Set.InjOn (fun m : ℕ+ => (m : ℕ)) {m : ℕ+ | (m : ℕ) ≤ N} :=
      fun a _ b _ h => PNat.coe_injective h
    refine Set.Finite.of_finite_image ?_ hinj
    refine (Set.finite_Icc 0 N).subset ?_
    rintro m ⟨y, hy, rfl⟩
    exact ⟨Nat.zero_le _, hy⟩
  exact (hfin1.prod hfin1).subset fun x hx => ⟨hx.1, hx.2⟩

theorem summable_gradePairFamily {ν : ℕ → ℂ} (hfin : (Function.support ν).Finite)
    {n : ℕ} (hn : 0 < n) : Summable (gradePairFamily ν n) :=
  summable_of_hasFiniteSupport (finite_support_gradePairFamily hfin hn)

/-- **The pair sum of the grade family is the datum itself.** -/
theorem tsum_gradePairFamily {ν : ℕ → ℂ} (hfin : (Function.support ν).Finite)
    {n : ℕ} (hn : 0 < n) : ∑' x : ℕ+ × ℕ+, gradePairFamily ν n x = ν n := by
  classical
  have hsummable := summable_gradePairFamily hfin hn
  have hpull : ∑' x : ℕ+ × ℕ+, gradePairFamily ν n x
      = ∑' p : (Σ m : ℕ+, Nat.divisorsAntidiagonal (m : ℕ)),
          gradePairFamily ν n (sigmaAntidiagonalEquivProd p) :=
    (sigmaAntidiagonalEquivProd.tsum_eq (gradePairFamily ν n)).symm
  have hsummableG : Summable fun p : (Σ m : ℕ+, Nat.divisorsAntidiagonal (m : ℕ)) =>
      gradePairFamily ν n (sigmaAntidiagonalEquivProd p) :=
    (Equiv.summable_iff sigmaAntidiagonalEquivProd).mpr hsummable
  have hsigma : (∑' p : (Σ m : ℕ+, Nat.divisorsAntidiagonal (m : ℕ)),
        gradePairFamily ν n (sigmaAntidiagonalEquivProd p))
      = ∑' m : ℕ+, ∑' q : Nat.divisorsAntidiagonal (m : ℕ),
          gradePairFamily ν n (sigmaAntidiagonalEquivProd ⟨m, q⟩) :=
    hsummableG.tsum_sigma
  have hinner : ∀ m : ℕ+, (∑' q : Nat.divisorsAntidiagonal (m : ℕ),
      gradePairFamily ν n (sigmaAntidiagonalEquivProd ⟨m, q⟩))
      = (if (m : ℕ) = 1 then ν ((m : ℕ) * n) / ((m : ℕ) : ℂ) else 0) := by
    intro m
    have hterm : ∀ q : Nat.divisorsAntidiagonal (m : ℕ),
        gradePairFamily ν n (sigmaAntidiagonalEquivProd ⟨m, q⟩)
          = (moebius (q.1.1) : ℂ) * (ν ((m : ℕ) * n) / ((m : ℕ) : ℂ)) := by
      intro q
      have hprod : ((divisorsAntidiagonalFactors m q).1 : ℕ)
          * ((divisorsAntidiagonalFactors m q).2 : ℕ) = (m : ℕ) :=
        divisorsAntidiagonalFactors_eq q
      have hfst : ((divisorsAntidiagonalFactors m q).1 : ℕ) = q.1.1 := rfl
      rw [gradePairFamily]
      show (moebius ((divisorsAntidiagonalFactors m q).1 : ℕ) : ℂ)
          * ν (((divisorsAntidiagonalFactors m q).1 : ℕ)
            * ((divisorsAntidiagonalFactors m q).2 : ℕ) * n)
          / ((((divisorsAntidiagonalFactors m q).1 : ℕ)
            * ((divisorsAntidiagonalFactors m q).2 : ℕ) : ℕ) : ℂ) = _
      rw [hprod, hfst]
      ring
    rw [tsum_congr hterm, Finset.tsum_subtype ((m : ℕ).divisorsAntidiagonal)
      (fun q : ℕ × ℕ => (moebius q.1 : ℂ) * (ν ((m : ℕ) * n) / ((m : ℕ) : ℂ)))]
    rw [← Finset.sum_mul]
    have hdiv : ∑ q ∈ (m : ℕ).divisorsAntidiagonal, (moebius q.1 : ℂ)
        = ∑ d ∈ (m : ℕ).divisors, (moebius d : ℂ) :=
      Nat.sum_divisorsAntidiagonal (fun a _ => (moebius a : ℂ))
    rw [hdiv, sum_divisors_moebius_eq (m : ℕ)]
    by_cases hm1 : (m : ℕ) = 1
    · rw [if_pos hm1, if_pos hm1, one_mul]
    · rw [if_neg hm1, if_neg hm1, zero_mul]
  have hone : ∑' m : ℕ+, (if (m : ℕ) = 1 then ν ((m : ℕ) * n) / ((m : ℕ) : ℂ) else 0)
      = ν n := by
    have hsingle : ∀ m : ℕ+, (if (m : ℕ) = 1 then ν ((m : ℕ) * n) / ((m : ℕ) : ℂ) else 0)
        = if m = 1 then ν n else 0 := by
      intro m
      by_cases hm : m = 1
      · subst hm
        simp
      · have hm' : (m : ℕ) ≠ 1 := fun h => hm (PNat.coe_injective (by simpa using h))
        rw [if_neg hm', if_neg hm]
    rw [tsum_congr hsingle, tsum_ite_eq]
  rw [hpull, hsigma, tsum_congr hinner, hone]

/-- **Mutual inversion of the grade transform.**  The Lambert transform of the Möbius grade
transform of a locally finite dilation datum returns the datum. -/
theorem gradeLambertTransform_gradeMonodromyTransform {ν : ℕ → ℂ}
    (hfin : (Function.support ν).Finite) {n : ℕ} (hn : 0 < n) :
    gradeLambertTransform (gradeMonodromyTransform ν) n = ν n := by
  classical
  have hsummable := summable_gradePairFamily hfin hn
  have hswapSummable : Summable (fun x : ℕ+ × ℕ+ => gradePairFamily ν n (x.2, x.1)) := by
    have h := (Equiv.prodComm ℕ+ ℕ+).summable_iff (f := gradePairFamily ν n)
    exact h.mpr hsummable
  have hswapEq : ∑' x : ℕ+ × ℕ+, gradePairFamily ν n (x.2, x.1)
      = ∑' x : ℕ+ × ℕ+, gradePairFamily ν n x :=
    (Equiv.prodComm ℕ+ ℕ+).tsum_eq (gradePairFamily ν n)
  have hprod : ∑' x : ℕ+ × ℕ+, gradePairFamily ν n (x.2, x.1)
      = ∑' k : ℕ+, ∑' r : ℕ+, gradePairFamily ν n (r, k) :=
    hswapSummable.tsum_prod' (fun k => (hswapSummable.prod_factor k))
  have hval : ∑' k : ℕ+, ∑' r : ℕ+, gradePairFamily ν n (r, k) = ν n := by
    rw [← hprod, hswapEq]
    exact tsum_gradePairFamily hfin hn
  rw [gradeLambertTransform]
  have hinner : ∀ k : ℕ+, gradeMonodromyTransform ν ((k : ℕ) * n) / ((k : ℕ) : ℂ)
      = -∑' r : ℕ+, gradePairFamily ν n (r, k) := by
    intro k
    rw [gradeMonodromyTransform, neg_div, ← tsum_div_const]
    congr 1
    refine tsum_congr fun r => ?_
    rw [gradePairFamily]
    have hassoc : (r : ℕ) * ((k : ℕ) * n) = (r : ℕ) * (k : ℕ) * n := by ring
    rw [hassoc]
    push_cast
    ring
  rw [tsum_congr hinner, tsum_neg, hval]
  ring

/-! ### The Lambert decomposition of the von Mangoldt current -/

/-- The grade-one prime source `Q(s) = ∑_p (log p) p^{-s}`. -/
def primeGradeSource (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s)

theorem summable_primeGradeSourceTerm {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) := by
  have hlog : Summable fun n : ℕ => |Real.log (n : ℝ)| ^ 1 * (n : ℝ) ^ (-s.re) :=
    summable_abs_log_natCast_pow_mul_rpow_neg 1 s.re hs
  have hlogp : Summable fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| ^ 1 * (((p : ℕ) : ℝ)) ^ (-s.re) :=
    hlog.comp_injective (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  refine Summable.of_norm ?_
  refine hlogp.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
  have hp0 : 0 < (p : ℕ) := p.2.pos
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos hp0]
  have hre : (-s).re = -s.re := by simp
  rw [hre, pow_one]

theorem primeGradeSource_term_eq {s : ℂ} (p : Nat.Primes) (k : ℕ) :
    LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s ((p : ℕ) ^ (k + 1))
      = (Real.log ((p : ℕ) : ℝ) : ℂ) * ((((p : ℕ) : ℂ)) ^ (-s)) ^ (k + 1) := by
  have hne : ((p : ℕ) ^ (k + 1) : ℕ) ≠ 0 := pow_ne_zero _ p.2.ne_zero
  have hvm : ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) = Real.log ((p : ℕ) : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
      ArithmeticFunction.vonMangoldt_apply_prime p.2]
  rw [LSeries.term_of_ne_zero hne, hvm, div_eq_mul_inv, ← Complex.cpow_neg,
    GaloisForLFunctions.cpow_nat_prime_power p (k + 1) s]

theorem support_vonMangoldtTerm_subset_primePow (s : ℂ) :
    Function.support (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s)
      ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra hpow
  apply hn
  have hvm : ArithmeticFunction.vonMangoldt n = 0 :=
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn0, hvm]
    simp

/-- The prime-power grade family whose double sum is the von Mangoldt current. -/
def primeGradeFamily (s : ℂ) (pk : Nat.Primes × ℕ) : ℂ :=
  (Real.log ((pk.1 : ℕ) : ℝ) : ℂ) * ((((pk.1 : ℕ) : ℂ)) ^ (-s)) ^ (pk.2 + 1)

theorem summable_primeGradeFamily {s : ℂ} (hs : 1 < s.re) : Summable (primeGradeFamily s) := by
  have hcorpus := summable_primeLog_mul_inv_rpow_mul_add s.re s.re (by linarith) hs
  refine Summable.of_norm ?_
  refine hcorpus.of_nonneg_of_le (fun pk => norm_nonneg _) (fun pk => ?_)
  have hp0 : 0 < ((pk.1 : ℕ) : ℝ) := by exact_mod_cast pk.1.2.pos
  have hnorm : ‖primeGradeFamily s pk‖
      = Real.log ((pk.1 : ℕ) : ℝ) * (((pk.1 : ℕ) : ℝ) ^ (-s.re)) ^ (pk.2 + 1) := by
    rw [primeGradeFamily, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast_cpow_of_pos pk.1.2.pos,
      abs_of_nonneg (Real.log_natCast_nonneg _)]
    congr 2
  rw [hnorm]
  have hpow : (((pk.1 : ℕ) : ℝ) ^ (-s.re)) ^ (pk.2 + 1)
      = ((((pk.1 : ℕ) : ℝ))⁻¹) ^ ((pk.2 : ℝ) * s.re + s.re) := by
    rw [Real.inv_rpow hp0.le, ← Real.rpow_natCast (((pk.1 : ℕ) : ℝ) ^ (-s.re)) (pk.2 + 1),
      ← Real.rpow_mul hp0.le, ← Real.rpow_neg hp0.le]
    congr 1
    push_cast
    ring
  rw [hpow]

/-- **The Lambert decomposition (1).**  The von Mangoldt current is the sum of the grade-one prime
source over all dilations. -/
theorem lSeries_vonMangoldt_eq_tsum_primeGradeSource {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      = ∑' k : ℕ, primeGradeSource (((k : ℂ) + 1) * s) := by
  classical
  have hsum : Summable (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hregroup := tsum_eq_tsum_primes_of_support_subset_prime_powers hsum
    (support_vonMangoldtTerm_subset_primePow s)
  have hfam := summable_primeGradeFamily hs
  have hswapSummable : Summable fun kp : ℕ × Nat.Primes => primeGradeFamily s (kp.2, kp.1) := by
    have h := (Equiv.prodComm ℕ Nat.Primes).summable_iff (f := primeGradeFamily s)
    simpa [Function.comp_def, Prod.swap] using h.mpr hfam
  have hinner : ∀ p : Nat.Primes, ∀ k : ℕ,
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s ((p : ℕ) ^ (k + 1))
        = primeGradeFamily s (p, k) := fun p k => primeGradeSource_term_eq p k
  have hstep : (∑' (p : Nat.Primes) (k : ℕ),
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s ((p : ℕ) ^ (k + 1)))
      = ∑' (p : Nat.Primes) (k : ℕ), primeGradeFamily s (p, k) :=
    tsum_congr fun p => tsum_congr fun k => hinner p k
  have hprodP : (∑' pk : Nat.Primes × ℕ, primeGradeFamily s pk)
      = ∑' (p : Nat.Primes) (k : ℕ), primeGradeFamily s (p, k) :=
    hfam.tsum_prod' (fun p => hfam.prod_factor p)
  have hprodK : (∑' kp : ℕ × Nat.Primes, primeGradeFamily s (kp.2, kp.1))
      = ∑' (k : ℕ) (p : Nat.Primes), primeGradeFamily s (p, k) :=
    hswapSummable.tsum_prod' (fun k => hswapSummable.prod_factor k)
  have hswapEq : (∑' kp : ℕ × Nat.Primes, primeGradeFamily s (kp.2, kp.1))
      = ∑' pk : Nat.Primes × ℕ, primeGradeFamily s pk :=
    (Equiv.prodComm ℕ Nat.Primes).tsum_eq (primeGradeFamily s)
  have hcomm : (∑' (p : Nat.Primes) (k : ℕ), primeGradeFamily s (p, k))
      = ∑' (k : ℕ) (p : Nat.Primes), primeGradeFamily s (p, k) := by
    rw [← hprodP, ← hswapEq, hprodK]
  have hgrade : ∀ k : ℕ, (∑' p : Nat.Primes, primeGradeFamily s (p, k))
      = primeGradeSource (((k : ℂ) + 1) * s) := by
    intro k
    rw [primeGradeSource]
    refine tsum_congr fun p => ?_
    have hp0 : (((p : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
    rw [primeGradeFamily]
    have hpow : ((((p : ℕ) : ℂ)) ^ (-s)) ^ (k + 1)
        = (((p : ℕ) : ℂ)) ^ (-(((k : ℂ) + 1) * s)) := by
      rw [← GaloisForLFunctions.HTGeometry.cpow_mul_natCast hp0 (-s) (k + 1)]
      congr 1
      push_cast
      ring
    rw [hpow]
  rw [LSeries, hregroup, hstep, hcomm, tsum_congr hgrade]

/-! ### Möbius inversion of the grade-one source -/

/-- The absolute prime-log mass at abscissa `σ`. -/
private def primeLogMass (σ : ℝ) : ℝ := ∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-σ)

theorem summable_primeLogMassTerm {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-σ) := by
  have hlog : Summable fun n : ℕ => |Real.log (n : ℝ)| ^ 1 * (n : ℝ) ^ (-σ) :=
    summable_abs_log_natCast_pow_mul_rpow_neg 1 σ hσ
  have hlogp : Summable fun p : Nat.Primes =>
      |Real.log ((p : ℕ) : ℝ)| ^ 1 * (((p : ℕ) : ℝ)) ^ (-σ) :=
    hlog.comp_injective (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  refine hlogp.congr fun p => ?_
  rw [pow_one, abs_of_nonneg (Real.log_natCast_nonneg _)]

private theorem primeLogMass_nonneg (σ : ℝ) : 0 ≤ primeLogMass σ := by
  refine tsum_nonneg fun p => ?_
  have h1 : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h2 : (0 : ℝ) < (((p : ℕ) : ℝ)) ^ (-σ) := by
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    exact Real.rpow_pos_of_pos hp0 _
  positivity

/-- **Geometric decay of the dilated grade-one source.** -/
theorem norm_primeGradeSource_dilate_le {s : ℂ} (hs : 1 < s.re) (m : ℕ) (hm : 1 ≤ m) :
    ‖primeGradeSource ((m : ℂ) * s)‖ ≤ primeLogMass s.re * (2 : ℝ) ^ (-((m : ℝ) - 1) * s.re) := by
  have hσ : 1 < s.re := hs
  have hmre : ((m : ℂ) * s).re = (m : ℝ) * s.re := by
    simp
  have hsummable : Summable fun p : Nat.Primes =>
      (Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s)) := by
    refine summable_primeGradeSourceTerm ?_
    rw [hmre]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · refine Summable.of_norm ?_
    simpa using hsummable.norm
  · have hterm : ∀ p : Nat.Primes,
        ‖(Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))‖
          ≤ (Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s.re))
            * (2 : ℝ) ^ (-((m : ℝ) - 1) * s.re) := by
      intro p
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
      have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
      have hnorm : ‖(Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))‖
          = Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-((m : ℝ) * s.re)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.log_natCast_nonneg _), Complex.norm_natCast_cpow_of_pos p.2.pos]
        congr 2
        rw [Complex.neg_re, hmre]
      rw [hnorm]
      have hsplit : ((p : ℕ) : ℝ) ^ (-((m : ℝ) * s.re))
          = ((p : ℕ) : ℝ) ^ (-s.re) * ((p : ℕ) : ℝ) ^ (-((m : ℝ) - 1) * s.re) := by
        rw [← Real.rpow_add hp0]
        congr 1
        ring
      have hmono : ((p : ℕ) : ℝ) ^ (-((m : ℝ) - 1) * s.re)
          ≤ (2 : ℝ) ^ (-((m : ℝ) - 1) * s.re) := by
        have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          linarith
        have hexp : -((m : ℝ) - 1) * s.re ≤ 0 := by nlinarith
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 hexp
      rw [hsplit, mul_assoc]
      have hnn : (0 : ℝ) ≤ Real.log ((p : ℕ) : ℝ) := Real.log_natCast_nonneg _
      have hnn2 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hp0 _
      refine mul_le_mul_of_nonneg_left ?_ hnn
      exact mul_le_mul_of_nonneg_left hmono hnn2.le
    have hmaj : Summable fun p : Nat.Primes =>
        (Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s.re)) * (2 : ℝ) ^ (-((m : ℝ) - 1) * s.re) :=
      (summable_primeLogMassTerm hσ).mul_right _
    calc (∑' p : Nat.Primes, ‖(Real.log ((p : ℕ) : ℝ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))‖)
        ≤ ∑' p : Nat.Primes,
            (Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s.re))
              * (2 : ℝ) ^ (-((m : ℝ) - 1) * s.re) := by
          refine Summable.tsum_le_tsum hterm ?_ hmaj
          refine Summable.of_norm ?_
          simpa using hsummable.norm
      _ = primeLogMass s.re * (2 : ℝ) ^ (-((m : ℝ) - 1) * s.re) := by
          rw [primeLogMass, ← tsum_mul_right]

theorem summable_geometric_pnat {σ : ℝ} (hσ : 0 < σ) :
    Summable fun r : ℕ+ => (2 : ℝ) ^ (-(((r : ℕ) : ℝ) - 1) * σ) := by
  have hbase : (0 : ℝ) < (2 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (2 : ℝ) ^ (-σ) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo : Summable fun n : ℕ => ((2 : ℝ) ^ (-σ)) ^ n :=
    summable_geometric_of_lt_one hbase.le hlt
  have hsub : Summable fun r : ℕ+ => ((2 : ℝ) ^ (-σ)) ^ ((r : ℕ) - 1) := by
    have hcomp : Summable fun r : ℕ+ => ((2 : ℝ) ^ (-σ)) ^ (((r : ℕ) - 1 : ℕ)) := by
      refine hgeo.comp_injective (i := fun r : ℕ+ => ((r : ℕ) - 1 : ℕ)) ?_
      intro a b hab
      simp only at hab
      have ha : 1 ≤ (a : ℕ) := a.property
      have hb : 1 ≤ (b : ℕ) := b.property
      exact PNat.coe_injective (by omega)
    exact hcomp
  refine hsub.congr fun r => ?_
  have hr1 : 1 ≤ (r : ℕ) := r.property
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-σ)) ((r : ℕ) - 1), ← Real.rpow_mul (by norm_num)]
  congr 1
  have hcast : (((r : ℕ) - 1 : ℕ) : ℝ) = ((r : ℕ) : ℝ) - 1 := by
    have : (1 : ℕ) ≤ (r : ℕ) := hr1
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast]
  ring

/-- **Möbius inversion (2).**  The grade-one prime source is the Möbius transform of the von
Mangoldt current along the dilation ray. -/
theorem summable_moebiusGradePair {s : ℂ} (hs : 1 < s.re) :
    Summable fun x : ℕ+ × ℕ+ =>
      (moebius (x.1 : ℕ) : ℂ) * primeGradeSource ((((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℂ) * s) := by
  have hσ : (0 : ℝ) < s.re := by linarith
  have hgeo := summable_geometric_pnat hσ
  have hmaj : Summable fun x : ℕ+ × ℕ+ =>
      (primeLogMass s.re * (2 : ℝ) ^ (-(((x.1 : ℕ) : ℝ) - 1) * s.re))
        * (2 : ℝ) ^ (-(((x.2 : ℕ) : ℝ) - 1) * s.re) := by
    refine Summable.mul_of_nonneg (hgeo.mul_left (primeLogMass s.re)) hgeo ?_ ?_
    · intro r
      have h1 : 0 ≤ primeLogMass s.re := primeLogMass_nonneg s.re
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(((r : ℕ) : ℝ) - 1) * s.re) :=
        Real.rpow_pos_of_pos (by norm_num) _
      positivity
    · intro k
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (-(((k : ℕ) : ℝ) - 1) * s.re) :=
        Real.rpow_pos_of_pos (by norm_num) _
      exact h2.le
  refine Summable.of_norm (hmaj.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_))
  have hrk1 : 1 ≤ (x.1 : ℕ) * (x.2 : ℕ) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hbound := norm_primeGradeSource_dilate_le hs ((x.1 : ℕ) * (x.2 : ℕ)) hrk1
  have hmoe : ‖((moebius (x.1 : ℕ) : ℤ) : ℂ)‖ ≤ 1 := by
    have := ArithmeticFunction.moebius_apply_of_squarefree (n := (x.1 : ℕ))
    rcases Int.abs_le_one_iff.mp (ArithmeticFunction.abs_moebius_le_one (n := (x.1 : ℕ)))
      with h | h | h <;> rw [h] <;> simp
  have hsplit : (2 : ℝ) ^ (-((((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℝ) - 1) * s.re)
      ≤ (2 : ℝ) ^ (-(((x.1 : ℕ) : ℝ) - 1) * s.re) * (2 : ℝ) ^ (-(((x.2 : ℕ) : ℝ) - 1) * s.re) := by
    rw [← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hr1 : (1 : ℝ) ≤ ((x.1 : ℕ) : ℝ) := by exact_mod_cast x.1.property
    have hk1 : (1 : ℝ) ≤ ((x.2 : ℕ) : ℝ) := by exact_mod_cast x.2.property
    have hprod : (((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℝ) = ((x.1 : ℕ) : ℝ) * ((x.2 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hprod]
    nlinarith [hσ, hr1, hk1, mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hk1)]
  calc ‖(moebius (x.1 : ℕ) : ℂ) * primeGradeSource ((((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℂ) * s)‖
      = ‖((moebius (x.1 : ℕ) : ℤ) : ℂ)‖
        * ‖primeGradeSource ((((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℂ) * s)‖ := by
        rw [norm_mul]
    _ ≤ 1 * (primeLogMass s.re * (2 : ℝ) ^ (-((((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℝ) - 1) * s.re)) := by
        refine mul_le_mul hmoe hbound (norm_nonneg _) (by norm_num)
    _ ≤ (primeLogMass s.re * (2 : ℝ) ^ (-(((x.1 : ℕ) : ℝ) - 1) * s.re))
        * (2 : ℝ) ^ (-(((x.2 : ℕ) : ℝ) - 1) * s.re) := by
        rw [one_mul, mul_assoc]
        refine mul_le_mul_of_nonneg_left hsplit (primeLogMass_nonneg s.re)

theorem tsum_succPNat {f : ℕ+ → ℂ} : ∑' k : ℕ, f (Nat.succPNat k) = ∑' p : ℕ+, f p := by
  have hbij : Function.Bijective (fun k : ℕ => Nat.succPNat k) := by
    constructor
    · intro a b hab
      have := congrArg (fun p : ℕ+ => (p : ℕ)) hab
      simpa using this
    · intro p
      refine ⟨(p : ℕ) - 1, ?_⟩
      have hp : 1 ≤ (p : ℕ) := p.property
      refine PNat.coe_injective ?_
      simp [Nat.succPNat]
      omega
  exact (Equiv.ofBijective _ hbij).tsum_eq f

/-- **Möbius inversion (2).**  The grade-one prime source is the Möbius transform of the von
Mangoldt current along the dilation ray. -/
theorem primeGradeSource_eq_tsum_moebius_lSeries {s : ℂ} (hs : 1 < s.re) :
    primeGradeSource s
      = ∑' r : ℕ+, (moebius (r : ℕ) : ℂ)
          * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (((r : ℕ) : ℂ) * s) := by
  classical
  have hsummable := summable_moebiusGradePair hs
  have hpair := tsum_moebius_pair (F := fun m : ℕ => primeGradeSource ((m : ℂ) * s)) hsummable
  have hone : primeGradeSource (((1 : ℕ) : ℂ) * s) = primeGradeSource s := by
    norm_num
  rw [hone] at hpair
  rw [← hpair]
  have hprod : (∑' x : ℕ+ × ℕ+,
        (moebius (x.1 : ℕ) : ℂ) * primeGradeSource ((((x.1 : ℕ) * (x.2 : ℕ) : ℕ) : ℂ) * s))
      = ∑' (r : ℕ+) (k : ℕ+),
        (moebius (r : ℕ) : ℂ) * primeGradeSource ((((r : ℕ) * (k : ℕ) : ℕ) : ℂ) * s) :=
    hsummable.tsum_prod' (fun r => hsummable.prod_factor r)
  rw [hprod]
  refine tsum_congr fun r => ?_
  have hrs : 1 < (((r : ℕ) : ℂ) * s).re := by
    have hr1 : (1 : ℝ) ≤ ((r : ℕ) : ℝ) := by exact_mod_cast r.property
    have hre : (((r : ℕ) : ℂ) * s).re = ((r : ℕ) : ℝ) * s.re := by simp
    rw [hre]
    nlinarith
  have hlam := lSeries_vonMangoldt_eq_tsum_primeGradeSource hrs
  rw [hlam, ← tsum_mul_left]
  have hshift : ∀ k : ℕ,
      (moebius (r : ℕ) : ℂ) * primeGradeSource (((k : ℂ) + 1) * (((r : ℕ) : ℂ) * s))
        = (moebius (r : ℕ) : ℂ)
          * primeGradeSource ((((r : ℕ) * ((Nat.succPNat k : ℕ+) : ℕ) : ℕ) : ℂ) * s) := by
    intro k
    congr 2
    push_cast [Nat.succPNat_coe]
    ring
  rw [tsum_congr hshift]
  exact (tsum_succPNat (f := fun k : ℕ+ =>
    (moebius (r : ℕ) : ℂ) * primeGradeSource ((((r : ℕ) * (k : ℕ) : ℕ) : ℂ) * s))).symm

/-! ### The monodromy of the continued grade-one source -/

theorem primeGradeSource_eq_xiPrimeLogDirichlet {s : ℂ} (hs : 1 < s.re) :
    primeGradeSource s = xiPrimeLogDirichlet s := by
  rw [xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs, primeGradeSource]
  refine tsum_congr fun p => ?_
  rw [Complex.cpow_neg, div_eq_mul_inv]

theorem primeGradeSource_eq_continuation {s : ℂ} (hs : 1 < s.re) :
    primeGradeSource s = xiPrimeLogDirichletContinuation s := by
  rw [primeGradeSource_eq_xiPrimeLogDirichlet hs, xiPrimeLogDirichletContinuation_eq hs]

/-- **(3)–(4) The grade-one prime monodromy at a strip zero.**  At every zeta zero to the right of
the critical line the continued grade-one source has residue exactly minus the multiplicity: the
higher prime-power grades are holomorphic there. -/
theorem primeGradeMonodromy_zero_residue {rho : ℂ} (hrho : 1 / 2 < rho.re)
    (hzeta : riemannZeta rho = 0) :
    ∃ m : ℕ, 1 ≤ m ∧
      Tendsto (fun s : ℂ => (s - rho) * xiPrimeLogDirichletContinuation s)
        (𝓝[≠] rho) (𝓝 (-(m : ℂ))) :=
  xiPrimeLogDirichletContinuation_zero_residue hrho hzeta

/-- A finite prime Dirichlet polynomial: the effect of changing finitely many Euler factors. -/
def finitePrimeEulerUnit (S : Finset Nat.Primes) (c : Nat.Primes → ℂ) (s : ℂ) : ℂ :=
  ∑ p ∈ S, c p * ((p : ℕ) : ℂ) ^ (-s)

theorem differentiable_finitePrimeEulerUnit (S : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Differentiable ℂ (finitePrimeEulerUnit S c) := by
  unfold finitePrimeEulerUnit
  refine Differentiable.fun_sum fun p _ => ?_
  have hp0 : (((p : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
  exact Differentiable.const_mul (differentiable_id.neg.const_cpow (Or.inl hp0)) (c p)

/-- **(6) Finite Euler-unit invariance.**  A finite prime Dirichlet polynomial contributes no
residue, so the grade-one monodromy field descends through finite Euler-unit equivalence. -/
theorem tendsto_finitePrimeEulerUnit_residue (S : Finset Nat.Primes) (c : Nat.Primes → ℂ)
    (rho : ℂ) :
    Tendsto (fun s : ℂ => (s - rho) * finitePrimeEulerUnit S c s) (𝓝[≠] rho) (𝓝 0) := by
  have hcont : Tendsto (fun s : ℂ => finitePrimeEulerUnit S c s) (𝓝[≠] rho)
      (𝓝 (finitePrimeEulerUnit S c rho)) :=
    ((differentiable_finitePrimeEulerUnit S c).continuous.tendsto rho).mono_left nhdsWithin_le_nhds
  have hlin := tendsto_sub_self_punctured_zero rho
  simpa using hlin.mul hcont

/-- **The monodromy is unchanged by finite Euler units.** -/
theorem tendsto_residue_add_finitePrimeEulerUnit {F : ℂ → ℂ} {rho L : ℂ}
    (hF : Tendsto (fun s : ℂ => (s - rho) * F s) (𝓝[≠] rho) (𝓝 L))
    (S : Finset Nat.Primes) (c : Nat.Primes → ℂ) :
    Tendsto (fun s : ℂ => (s - rho) * (F s + finitePrimeEulerUnit S c s)) (𝓝[≠] rho) (𝓝 L) := by
  have hunit := tendsto_finitePrimeEulerUnit_residue S c rho
  have hsum := hF.add hunit
  rw [add_zero] at hsum
  refine hsum.congr fun s => ?_
  ring

/-- **Only the undilated Möbius term is singular in the strip.**  For every dilation `r ≥ 2` the
dilated von Mangoldt current is holomorphic at every point of the open right strip, so the grade
monodromy at such a point is the single term `−ν(s₀)`. -/
theorem differentiableAt_lSeries_vonMangoldt_dilate {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) {r : ℕ}
    (hr : 2 ≤ r) :
    DifferentiableAt ℂ
      (fun s : ℂ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((r : ℂ) * s)) s₀ := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hre : 1 < (((r : ℂ)) * s₀).re := by
    have hval : (((r : ℂ)) * s₀).re = (r : ℝ) * s₀.re := by simp
    rw [hval]
    nlinarith
  have habs1 : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ≤ ((1 : ℝ) : EReal) := by
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)
  have habs : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      < (((r : ℂ) * s₀).re : EReal) :=
    lt_of_le_of_lt habs1 (by exact_mod_cast hre)
  have hbase : DifferentiableAt ℂ
      (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) ((r : ℂ) * s₀) :=
    (LSeries_analyticOnNhd (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
      ((r : ℂ) * s₀) habs |>.differentiableAt
  exact hbase.comp s₀ (differentiable_id.const_mul _ s₀)

end

end RHTower
