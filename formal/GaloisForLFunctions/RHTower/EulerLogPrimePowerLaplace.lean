import GaloisForLFunctions.RHTower.HeatApertureEchoHankel
import GaloisForLFunctions.RHTower.EulerLogPrimePowerHerglotzMass
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.VonMangoldtEuler
import GaloisForLFunctions.RHTower.SquarefreeCoronaCodiagonal
import GaloisForLFunctions.RHTower.PrimeTailCoPoissonBoundary

/-!
# Exact Laplace transforms of the Euler-log prime-power carrier

The normalized positive atoms `1 / ((k+1) p^(k+1))` at times `(k+1) log p` have an
absolutely convergent complex Laplace transform throughout `Re s > 0`.  This module identifies
that literal product-indexed sum with the canonical Euler logarithm at `1+s`.  Multiplying each
atom by its log position gives the full von-Mangoldt current, hence `-ζ'(1+s)/ζ(1+s)`, and is
exactly minus the derivative of the original Laplace transform.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Real Laplace damping turns the normalized carrier atom into the existing Euler moment
weight at inverse temperature `1+s`. -/
lemma eulerLogPrimePower_laplaceAtom_eq_eulerPrimePowerWeight
    (s : ℝ) (p : Nat.Primes) (k : ℕ) :
    eulerLogPrimePowerWeight p k *
      Real.exp (-s * eulerLogPrimePowerTime p k) =
      RHTower.eulerPrimePowerWeight (1 + s) (p, k) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hq : 0 < (((p : ℕ) ^ (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast pow_pos p.property.pos _
  have hexp : Real.exp (-s * eulerLogPrimePowerTime p k) =
      (((p : ℕ) ^ (k + 1) : ℕ) : ℝ) ^ (-s) := by
    rw [eulerLogPrimePowerTime, Real.rpow_def_of_pos hq, Nat.cast_pow,
      Real.log_pow]
    congr 1
    ring
  rw [hexp, eulerLogPrimePowerWeight, RHTower.eulerPrimePowerWeight,
    RHTower.eulerPrimePowerNat]
  rw [show -(1 + s) = -1 + -s by ring, Real.rpow_add hq]
  have hqinv : (((p : ℕ) ^ (k + 1) : ℕ) : ℝ) ^ (-1 : ℝ) =
      (((p : ℕ) ^ (k + 1) : ℕ) : ℝ)⁻¹ := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hq.le]
    norm_num
  rw [hqinv]
  field_simp
  push_cast
  ring

/-- On the positive real ray, the literal Euler-log carrier sums to the canonical Euler
logarithm at the shifted parameter. -/
theorem tsum_eulerLogPrimePower_laplace_eq_canonicalEulerLogZeta
    {s : ℝ} (hs : 0 < s) :
    (∑' x : Nat.Primes × ℕ,
      (eulerLogPrimePowerWeight x.1 x.2 *
        Real.exp (-s * eulerLogPrimePowerTime x.1 x.2) : ℝ) : ℂ) =
      _root_.RHTower.canonicalEulerLogZeta ((1 + s : ℝ) : ℂ) := by
  have hβ : 1 < 1 + s := by linarith
  rw [GaloisForLFunctions.canonicalEulerLogZeta_ofReal_eq_primePower_tsum hβ,
    Complex.ofReal_tsum]
  apply tsum_congr
  intro x
  exact congrArg Complex.ofReal
    (eulerLogPrimePower_laplaceAtom_eq_eulerPrimePowerWeight s x.1 x.2)

/-- Absolute convergence of the real Euler-log Laplace family for every positive parameter. -/
theorem summable_eulerLogPrimePower_laplace_term
    {s : ℝ} (hs : 0 < s) :
    Summable fun x : Nat.Primes × ℕ =>
      eulerLogPrimePowerWeight x.1 x.2 *
        Real.exp (-s * eulerLogPrimePowerTime x.1 x.2) := by
  have hβ : 1 < 1 + s := by linarith
  apply Summable.of_norm
  convert RHTower.summable_abs_eulerPrimePower_moment 0 (1 + s) hβ using 1
  ext x
  rw [Real.norm_eq_abs,
    eulerLogPrimePower_laplaceAtom_eq_eulerPrimePowerWeight]
  simp

/-- The carrier time is the existing Euler prime-power energy. -/
lemma eulerLogPrimePowerTime_eq_eulerPrimePowerEnergy
    (p : Nat.Primes) (k : ℕ) :
    eulerLogPrimePowerTime p k =
      RHTower.eulerPrimePowerEnergy (p, k) := by
  rw [eulerLogPrimePowerTime, RHTower.eulerPrimePowerEnergy,
    RHTower.eulerPrimePowerNat, Nat.cast_pow, Real.log_pow]

/-- A real log-position insertion is exactly one von-Mangoldt prime-power atom. -/
lemma eulerLogPrimePower_logPositionLaplaceAtom_eq
    (s : ℝ) (p : Nat.Primes) (k : ℕ) :
    eulerLogPrimePowerTime p k * eulerLogPrimePowerWeight p k *
        Real.exp (-s * eulerLogPrimePowerTime p k) =
      Real.log (p : ℝ) *
        (p : ℝ) ^ (-(((k : ℝ) + 1) * (1 + s))) := by
  calc
    eulerLogPrimePowerTime p k * eulerLogPrimePowerWeight p k *
        Real.exp (-s * eulerLogPrimePowerTime p k) =
      eulerLogPrimePowerTime p k *
        (eulerLogPrimePowerWeight p k *
          Real.exp (-s * eulerLogPrimePowerTime p k)) := by ring
    _ = eulerLogPrimePowerTime p k *
        RHTower.eulerPrimePowerWeight (1 + s) (p, k) := by
      rw [eulerLogPrimePower_laplaceAtom_eq_eulerPrimePowerWeight]
    _ = Real.log (p : ℝ) *
        (p : ℝ) ^ (-(((k : ℝ) + 1) * (1 + s))) := by
      rw [eulerLogPrimePowerTime, RHTower.eulerPrimePowerWeight,
        RHTower.eulerPrimePowerNat,
        GaloisForLFunctions.HTGeometry.rpow_primePow]
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      push_cast
      ring

/-- Absolute convergence of the real log-position-inserted carrier. -/
theorem summable_eulerLogPrimePower_logPositionLaplace_term
    {s : ℝ} (hs : 0 < s) :
    Summable fun x : Nat.Primes × ℕ =>
      eulerLogPrimePowerTime x.1 x.2 *
        eulerLogPrimePowerWeight x.1 x.2 *
          Real.exp (-s * eulerLogPrimePowerTime x.1 x.2) := by
  have hβ : 1 < 1 + s := by linarith
  apply Summable.of_norm
  convert RHTower.summable_abs_eulerPrimePower_moment 1 (1 + s) hβ using 1
  ext x
  rw [Real.norm_eq_abs]
  congr 1
  calc
    eulerLogPrimePowerTime x.1 x.2 *
        eulerLogPrimePowerWeight x.1 x.2 *
          Real.exp (-s * eulerLogPrimePowerTime x.1 x.2) =
      eulerLogPrimePowerTime x.1 x.2 *
        (eulerLogPrimePowerWeight x.1 x.2 *
          Real.exp (-s * eulerLogPrimePowerTime x.1 x.2)) := by ring
    _ = eulerLogPrimePowerTime x.1 x.2 *
        RHTower.eulerPrimePowerWeight (1 + s) x := by
      rw [eulerLogPrimePower_laplaceAtom_eq_eulerPrimePowerWeight]
    _ = RHTower.eulerPrimePowerWeight (1 + s) x *
        RHTower.eulerPrimePowerEnergy x ^ 1 := by
      rw [eulerLogPrimePowerTime_eq_eulerPrimePowerEnergy]
      simp [mul_comm]

/-- The real log-position-inserted carrier is `-ζ'(1+s)/ζ(1+s)`. -/
theorem tsum_eulerLogPrimePower_logPositionLaplace_eq_zetaLogDeriv
    {s : ℝ} (hs : 0 < s) :
    ((∑' x : Nat.Primes × ℕ,
      eulerLogPrimePowerTime x.1 x.2 *
        eulerLogPrimePowerWeight x.1 x.2 *
          Real.exp (-s * eulerLogPrimePowerTime x.1 x.2) : ℝ) : ℂ) =
      -deriv riemannZeta ((1 + s : ℝ) : ℂ) /
        riemannZeta ((1 + s : ℝ) : ℂ) := by
  have hβ : 1 < 1 + s := by linarith
  have hsum : Summable fun x : Nat.Primes × ℕ =>
      Real.log (x.1 : ℝ) *
        (x.1 : ℝ) ^ (-(((x.2 : ℝ) + 1) * (1 + s))) :=
    (summable_eulerLogPrimePower_logPositionLaplace_term hs).congr
      (fun x => eulerLogPrimePower_logPositionLaplaceAtom_eq s x.1 x.2)
  calc
    ((∑' x : Nat.Primes × ℕ,
      eulerLogPrimePowerTime x.1 x.2 *
        eulerLogPrimePowerWeight x.1 x.2 *
          Real.exp (-s * eulerLogPrimePowerTime x.1 x.2) : ℝ) : ℂ) =
      ((∑' x : Nat.Primes × ℕ,
        Real.log (x.1 : ℝ) *
          (x.1 : ℝ) ^ (-(((x.2 : ℝ) + 1) * (1 + s))) : ℝ) : ℂ) := by
        congr 1
        exact tsum_congr fun x =>
          eulerLogPrimePower_logPositionLaplaceAtom_eq s x.1 x.2
    _ = ((∑' p : Nat.Primes,
        Real.log (p : ℝ) * ∑' k : ℕ,
          (p : ℝ) ^ (-(((k : ℝ) + 1) * (1 + s))) : ℝ) : ℂ) := by
      congr 1
      rw [hsum.tsum_prod]
      apply tsum_congr
      intro p
      change (∑' k : ℕ, Real.log (p : ℝ) *
        (p : ℝ) ^ (-(((k : ℝ) + 1) * (1 + s)))) =
          Real.log (p : ℝ) * ∑' k : ℕ,
            (p : ℝ) ^ (-(((k : ℝ) + 1) * (1 + s)))
      rw [tsum_mul_left]
    _ = ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n *
        (n : ℝ) ^ (-(1 + s)) : ℝ) : ℂ) := by
      congr 1
      exact (GaloisForLFunctions.HTGeometry.tsum_vonMangoldt_eq_tsum_primes hβ).symm
    _ = -deriv riemannZeta ((1 + s : ℝ) : ℂ) /
        riemannZeta ((1 + s : ℝ) : ℂ) :=
      GaloisForLFunctions.HTGeometry.ofReal_tsum_vonMangoldt_eq hβ

/-- Holomorphic prime-power coefficient at complex inverse temperature. -/
noncomputable def eulerLogPrimePowerComplexWeight
    (beta : ℂ) (p : Nat.Primes) (k : ℕ) : ℂ :=
  ((p : ℂ) ^ (-beta)) ^ (k + 1) / ((k + 1 : ℕ) : ℂ)

/-- Complex Laplace damping turns one normalized carrier atom into its holomorphic Euler
prime-power coefficient at inverse temperature `1+s`. -/
lemma eulerLogPrimePower_complexLaplaceAtom_eq
    (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    (eulerLogPrimePowerWeight p k : ℂ) *
        Complex.exp (-(s * (eulerLogPrimePowerTime p k : ℂ))) =
      eulerLogPrimePowerComplexWeight (1 + s) p k := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    exact Complex.natCast_log.symm
  rw [eulerLogPrimePowerComplexWeight, Complex.cpow_def_of_ne_zero hpC,
    hlog, eulerLogPrimePowerWeight, eulerLogPrimePowerTime]
  push_cast
  rw [← Complex.exp_nat_mul]
  have hkC : ((k : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hpC, hkC]
  have hpow : (p : ℂ) ^ (k + 1) =
      Complex.exp (((k + 1 : ℕ) : ℂ) * Complex.log (p : ℂ)) := by
    rw [Complex.exp_nat_mul, Complex.exp_log hpC]
  rw [hpow, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Absolute convergence of the complex Euler-log Laplace family on `Re s > 0`. -/
theorem summable_eulerLogPrimePower_complexLaplaceTerm
    {s : ℂ} (hs : 0 < s.re) :
    Summable fun x : Nat.Primes × ℕ =>
      (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
        Complex.exp (-(s * (eulerLogPrimePowerTime x.1 x.2 : ℂ))) := by
  apply Summable.of_norm
  convert summable_eulerLogPrimePower_laplace_term hs using 1
  ext x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (eulerLogPrimePowerWeight_pos x.1 x.2), Complex.norm_exp]
  congr 1
  simp

/-- Absolute convergence of the holomorphic prime-power coefficient family on `Re beta > 1`. -/
theorem summable_eulerLogPrimePowerComplexWeight
    {beta : ℂ} (hbeta : 1 < beta.re) :
    Summable fun x : Nat.Primes × ℕ =>
      eulerLogPrimePowerComplexWeight beta x.1 x.2 := by
  have hs : 0 < (beta - 1).re := by simpa using hbeta
  exact (summable_eulerLogPrimePower_complexLaplaceTerm hs).congr
    (fun x => by
      have hparam : (1 : ℂ) + (beta - 1) = beta := by ring
      simpa only [hparam] using
        eulerLogPrimePower_complexLaplaceAtom_eq (beta - 1) x.1 x.2)

/-- One holomorphic prime-power coefficient is exactly the matching canonical Euler-log
`LSeries` term. -/
lemma eulerLogPrimePowerComplexWeight_eq_eulerLogTerm
    (beta : ℂ) (p : Nat.Primes) (k : ℕ) :
    eulerLogPrimePowerComplexWeight beta p k =
      LSeries.term RHTower.eulerLogDirichletCoeff beta ((p : ℕ) ^ (k + 1)) := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero (k + 1) p.property.ne_zero),
    RHTower.eulerLogDirichletCoeff_prime_pow_succ p k p.property]
  rw [eulerLogPrimePowerComplexWeight, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, ← Complex.cpow_nat_mul]
  rw [show ((k + 1 : ℕ) : ℂ) * (-beta) =
    -(((k + 1 : ℕ) : ℂ) * beta) by ring, Complex.cpow_neg]
  push_cast
  ring

/-- The canonical Euler logarithm is the absolutely convergent complex prime-power family. -/
theorem canonicalEulerLogZeta_eq_tsum_eulerLogPrimePowerComplexWeight
    {beta : ℂ} (hbeta : 1 < beta.re) :
    RHTower.canonicalEulerLogZeta beta =
      ∑' x : Nat.Primes × ℕ,
        eulerLogPrimePowerComplexWeight beta x.1 x.2 := by
  rw [(summable_eulerLogPrimePowerComplexWeight hbeta).tsum_prod]
  rw [RHTower.canonicalEulerLogZeta, LSeries]
  have hsum : Summable (LSeries.term RHTower.eulerLogDirichletCoeff beta) :=
    RHTower.canonicalEulerLogZeta_summable hbeta
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hsum]
  · apply tsum_congr
    intro p
    apply tsum_congr
    intro k
    exact (eulerLogPrimePowerComplexWeight_eq_eulerLogTerm beta p k).symm
  · intro n hn
    by_contra hpp
    apply hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0,
        RHTower.eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp]
      simp

/-- Literal complex Laplace transform of the normalized Euler-log prime-power carrier. -/
noncomputable def eulerLogPrimePowerLaplace (s : ℂ) : ℂ :=
  ∑' x : Nat.Primes × ℕ,
    (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
      Complex.exp (-(s * (eulerLogPrimePowerTime x.1 x.2 : ℂ)))

/-- Exact complex Euler transform: the carrier Laplace transform is the canonical Euler
logarithm at `1+s` throughout `Re s > 0`. -/
theorem eulerLogPrimePowerLaplace_eq_canonicalEulerLogZeta
    {s : ℂ} (hs : 0 < s.re) :
    eulerLogPrimePowerLaplace s =
      RHTower.canonicalEulerLogZeta (1 + s) := by
  rw [eulerLogPrimePowerLaplace]
  calc
    (∑' x : Nat.Primes × ℕ,
      (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
        Complex.exp (-(s * (eulerLogPrimePowerTime x.1 x.2 : ℂ)))) =
      ∑' x : Nat.Primes × ℕ,
        eulerLogPrimePowerComplexWeight (1 + s) x.1 x.2 :=
      tsum_congr fun x =>
        eulerLogPrimePower_complexLaplaceAtom_eq s x.1 x.2
    _ = RHTower.canonicalEulerLogZeta (1 + s) :=
      (canonicalEulerLogZeta_eq_tsum_eulerLogPrimePowerComplexWeight
        (by simpa using hs)).symm

/-- A complex log-position insertion is exactly the corresponding prime-power flux term. -/
lemma eulerLogPrimePower_complexLogPositionLaplaceAtom_eq
    (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    (eulerLogPrimePowerTime p k : ℂ) *
        (eulerLogPrimePowerWeight p k : ℂ) *
          Complex.exp (-(s * (eulerLogPrimePowerTime p k : ℂ))) =
      RHTower.primePowerFluxTerm (1 + s) (p, k) := by
  calc
    (eulerLogPrimePowerTime p k : ℂ) *
        (eulerLogPrimePowerWeight p k : ℂ) *
          Complex.exp (-(s * (eulerLogPrimePowerTime p k : ℂ))) =
      (eulerLogPrimePowerTime p k : ℂ) *
        ((eulerLogPrimePowerWeight p k : ℂ) *
          Complex.exp (-(s * (eulerLogPrimePowerTime p k : ℂ)))) := by ring
    _ = (eulerLogPrimePowerTime p k : ℂ) *
        eulerLogPrimePowerComplexWeight (1 + s) p k := by
      rw [eulerLogPrimePower_complexLaplaceAtom_eq]
    _ = RHTower.primePowerFluxTerm (1 + s) (p, k) := by
      rw [eulerLogPrimePowerTime, eulerLogPrimePowerComplexWeight,
        RHTower.primePowerFluxTerm]
      push_cast
      have hkC : ((k : ℂ) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      field_simp [hkC]

/-- Absolute convergence of the complex log-position current on `Re s > 0`. -/
theorem summable_eulerLogPrimePower_complexLogPositionLaplaceTerm
    {s : ℂ} (hs : 0 < s.re) :
    Summable fun x : Nat.Primes × ℕ =>
      (eulerLogPrimePowerTime x.1 x.2 : ℂ) *
        (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
          Complex.exp (-(s * (eulerLogPrimePowerTime x.1 x.2 : ℂ))) := by
  have hbeta : 1 < (1 + s).re := by simpa using hs
  exact (RHTower.summable_primePowerFluxTerm hbeta).congr
    (fun x => (eulerLogPrimePower_complexLogPositionLaplaceAtom_eq s x.1 x.2).symm)

/-- Literal complex Laplace transform after inserting the log-position observable. -/
noncomputable def eulerLogPrimePowerLogPositionLaplace (s : ℂ) : ℂ :=
  ∑' x : Nat.Primes × ℕ,
    (eulerLogPrimePowerTime x.1 x.2 : ℂ) *
      (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
        Complex.exp (-(s * (eulerLogPrimePowerTime x.1 x.2 : ℂ)))

/-- Log-position insertion recovers the existing full von-Mangoldt prime flux. -/
theorem eulerLogPrimePowerLogPositionLaplace_eq_infinitePrimeFlux
    {s : ℂ} (hs : 0 < s.re) :
    eulerLogPrimePowerLogPositionLaplace s =
      RHTower.infinitePrimeFlux (1 + s) := by
  rw [eulerLogPrimePowerLogPositionLaplace]
  calc
    (∑' x : Nat.Primes × ℕ,
      (eulerLogPrimePowerTime x.1 x.2 : ℂ) *
        (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
          Complex.exp (-(s * (eulerLogPrimePowerTime x.1 x.2 : ℂ)))) =
      ∑' x : Nat.Primes × ℕ, RHTower.primePowerFluxTerm (1 + s) x :=
        tsum_congr fun x =>
          eulerLogPrimePower_complexLogPositionLaplaceAtom_eq s x.1 x.2
    _ = RHTower.infinitePrimeFlux (1 + s) :=
      RHTower.tsum_primePowerFluxTerm (by simpa using hs)

/-- Exact complex logarithmic-derivative transform of the log-position current. -/
theorem eulerLogPrimePowerLogPositionLaplace_eq_zetaLogDeriv
    {s : ℂ} (hs : 0 < s.re) :
    eulerLogPrimePowerLogPositionLaplace s =
      -deriv riemannZeta (1 + s) / riemannZeta (1 + s) := by
  rw [eulerLogPrimePowerLogPositionLaplace_eq_infinitePrimeFlux hs,
    RHTower.infinitePrimeFlux, logDeriv_apply]
  ring

/-- The logarithmic twist of the Euler-log coefficient is exactly von Mangoldt. -/
lemma logMul_eulerLogDirichletCoeff_eq_vonMangoldt :
    LSeries.logMul RHTower.eulerLogDirichletCoeff =
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ) := by
  funext n
  by_cases hn : 2 ≤ n
  · rw [LSeries.logMul, ← Complex.natCast_log, mul_comm,
      RHTower.eulerLogDirichletCoeff_mul_log hn]
  · have hnle : n ≤ 1 := by omega
    interval_cases n <;> simp [LSeries.logMul,
      RHTower.eulerLogDirichletCoeff_zero,
      RHTower.eulerLogDirichletCoeff_one]

/-- Differentiating the Euler-log Laplace transform inserts minus log position. -/
theorem deriv_eulerLogPrimePowerLaplace
    {s : ℂ} (hs : 0 < s.re) :
    deriv eulerLogPrimePowerLaplace s =
      -eulerLogPrimePowerLogPositionLaplace s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : eulerLogPrimePowerLaplace =ᶠ[nhds s]
      fun z : ℂ => RHTower.canonicalEulerLogZeta (1 + z) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact eulerLogPrimePowerLaplace_eq_canonicalEulerLogZeta hz
  let c : ℝ := (1 + (1 + s).re) / 2
  have hc1 : 1 < c := by dsimp [c]; linarith
  have hcbeta : c < (1 + s).re := by dsimp [c]; linarith
  have habs : LSeries.abscissaOfAbsConv RHTower.eulerLogDirichletCoeff <
      (((1 + s).re : ℝ) : EReal) :=
    (RHTower.canonicalEulerLogZeta_summable (s := (c : ℂ))
      (by simpa using hc1)).abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hcbeta)
  have hL : HasDerivAt RHTower.canonicalEulerLogZeta
      (-LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + s))
      (1 + s) := by
    change HasDerivAt (LSeries RHTower.eulerLogDirichletCoeff)
      (-LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + s))
      (1 + s)
    convert LSeries_hasDerivAt habs using 1
    rw [logMul_eulerLogDirichletCoeff_eq_vonMangoldt]
  have hshift : HasDerivAt (fun z : ℂ => (1 : ℂ) + z) 1 s := by
    simpa only [id_eq] using (hasDerivAt_id s).const_add (1 : ℂ)
  have hcomp := hL.comp s hshift
  have hderiv : deriv
      (RHTower.canonicalEulerLogZeta ∘ fun z : ℂ => 1 + z) s =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + s) := by
    simpa only [mul_one] using hcomp.deriv
  have hflux : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + s) =
      eulerLogPrimePowerLogPositionLaplace s := by
    rw [eulerLogPrimePowerLogPositionLaplace_eq_infinitePrimeFlux hs,
      RHTower.infinitePrimeFlux_eq_vonMangoldtLSeries (by simpa using hs)]
  have hev' : eulerLogPrimePowerLaplace =ᶠ[nhds s]
      RHTower.canonicalEulerLogZeta ∘ fun z : ℂ => 1 + z := by
    filter_upwards [hev] with z hz
    exact hz
  calc
    deriv eulerLogPrimePowerLaplace s =
        deriv (RHTower.canonicalEulerLogZeta ∘ fun z : ℂ => 1 + z) s :=
      hev'.deriv_eq
    _ = -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + s) :=
      hderiv
    _ = -eulerLogPrimePowerLogPositionLaplace s := by rw [hflux]

end GaloisForLFunctions.RHTower
