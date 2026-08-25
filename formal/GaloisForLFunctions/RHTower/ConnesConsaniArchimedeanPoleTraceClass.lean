import GaloisForLFunctions.RHTower.ConnesConsaniDoublePoleFiniteRank
import GaloisForLFunctions.HTGeometry.BesselK1RayCoefficients
import GaloisForLFunctions.HTGeometry.SourceBox

open Complex
open scoped ENNReal InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Paper index attached to Lean's zero-based archimedean pole enumeration. -/
def connesConsaniArchimedeanPoleIndex (n : ℕ) : ℕ := n + 1

/-- Cayley node `x_N = 1 - 4/(4N+3)` for `N=n+1`, in reduced rational form. -/
def connesConsaniArchimedeanNode (n : ℕ) : ℂ :=
  (((4 * (n : ℝ) + 3) / (4 * (n : ℝ) + 7) : ℝ) : ℂ)

theorem connesConsaniArchimedeanNode_eq_source (n : ℕ) :
    connesConsaniArchimedeanNode n =
      (1 - 4 / (4 * ((connesConsaniArchimedeanPoleIndex n : ℕ) : ℝ) + 3) : ℝ) := by
  change (((4 * (n : ℝ) + 3) / (4 * (n : ℝ) + 7) : ℝ) : ℂ) =
    ((1 - 4 / (4 * ((n + 1 : ℕ) : ℝ) + 3) : ℝ) : ℂ)
  norm_cast
  field_simp
  push_cast
  ring

theorem norm_connesConsaniArchimedeanNode_lt_one (n : ℕ) :
    ‖connesConsaniArchimedeanNode n‖ < 1 := by
  rw [connesConsaniArchimedeanNode, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  exact (div_lt_one (by positivity)).2 (by linarith)

/-- Szegő kernel at the `n`-th nonzero archimedean pole node. -/
def connesConsaniArchimedeanKernel (n : ℕ) : HardyDisk :=
  hardyKernel (norm_connesConsaniArchimedeanNode_lt_one n)

/-- Unit Szegő kernel at the `n`-th nonzero archimedean pole node. -/
def connesConsaniArchimedeanNormalizedKernel (n : ℕ) : HardyDisk :=
  ((‖connesConsaniArchimedeanKernel n‖ : ℂ)⁻¹) •
    connesConsaniArchimedeanKernel n

@[simp] theorem norm_connesConsaniArchimedeanNormalizedKernel (n : ℕ) :
    ‖connesConsaniArchimedeanNormalizedKernel n‖ = 1 := by
  rw [connesConsaniArchimedeanNormalizedKernel, norm_smul, norm_inv,
    norm_real, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr
    (hardyKernel_ne_zero (norm_connesConsaniArchimedeanNode_lt_one n))

/-- Normalized range vector `xi_N` from Theorem 4.4. -/
def connesConsaniArchimedeanXi (n : ℕ) : CCMCircleL2 :=
  ccmNegativeHardyIsometry (connesConsaniArchimedeanNormalizedKernel n)

/-- Normalized source vector `eta_N` from Theorem 4.4. -/
def connesConsaniArchimedeanEta (n : ℕ) : CCMCircleL2 :=
  ccmPositiveHardyIsometry (connesConsaniArchimedeanNormalizedKernel n)

@[simp] theorem norm_connesConsaniArchimedeanXi (n : ℕ) :
    ‖connesConsaniArchimedeanXi n‖ = 1 := by
  rw [connesConsaniArchimedeanXi, LinearIsometry.norm_map,
    norm_connesConsaniArchimedeanNormalizedKernel]

@[simp] theorem norm_connesConsaniArchimedeanEta (n : ℕ) :
    ‖connesConsaniArchimedeanEta n‖ = 1 := by
  rw [connesConsaniArchimedeanEta, LinearIsometry.norm_map,
    norm_connesConsaniArchimedeanNormalizedKernel]

/-- Half-integer Gamma normalization in the factorial form used by the pole coefficient. -/
theorem factorial_two_mul_eq_four_pow_mul_gaussianMomentFactor (N : ℕ) :
    (((2 * N).factorial : ℕ) : ℝ) =
      4 ^ N * (N.factorial : ℝ) * gaussianMomentFactor N := by
  induction N with
  | zero => simp [gaussianMomentFactor]
  | succ N ih =>
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        Nat.factorial_succ,
        show 2 * N + 1 = 2 * N + 1 by rfl,
        Nat.factorial_succ, gaussianMomentFactor_succ, Nat.factorial_succ]
      push_cast
      rw [ih]
      ring

/-- Literal Gamma-form coefficient displayed in Connes--Consani Theorem 4.4.  The half power of
`pi` is written canonically as `pi^(2N) sqrt(pi)`. -/
def connesConsaniArchimedeanSourceCoefficient (p : Nat.Primes) (n : ℕ) : ℝ :=
  let N := connesConsaniArchimedeanPoleIndex n
  (-1 : ℝ) ^ N *
    (2 * Real.pi ^ (2 * N) * Real.sqrt Real.pi *
      (1 - (((p : ℝ) ^ (2 * N + 1))⁻¹))) /
      (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1) *
        Real.Gamma ((N : ℝ) + 1) * Real.Gamma ((N : ℝ) + 1 / 2))

/-- Exact Theorem 4.4 coefficient in factorial form, with source index `N=n+1`. -/
def connesConsaniArchimedeanCoefficient (p : Nat.Primes) (n : ℕ) : ℝ :=
  let N := connesConsaniArchimedeanPoleIndex n
  (-1 : ℝ) ^ N *
    (2 * (4 * Real.pi ^ 2) ^ N / ((2 * N).factorial : ℝ)) *
      ((1 - (((p : ℝ) ^ (2 * N + 1))⁻¹)) /
        (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1)))

/-- The factorial coefficient is exactly the Gamma coefficient in the source theorem. -/
theorem connesConsaniArchimedeanCoefficient_eq_source
    (p : Nat.Primes) (n : ℕ) :
    connesConsaniArchimedeanCoefficient p n =
      connesConsaniArchimedeanSourceCoefficient p n := by
  let N := connesConsaniArchimedeanPoleIndex n
  have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hfacN : (N.factorial : ℝ) ≠ 0 := by positivity
  have hfac2N : (((2 * N).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hpPow : (1 : ℝ) < (p : ℝ) ^ (2 * N) := by
    exact one_lt_pow₀ hp (by simp [N, connesConsaniArchimedeanPoleIndex])
  have hpDen : (p : ℝ) ^ (2 * N) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpPow)
  have hfour : (((4 * N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  change (-1 : ℝ) ^ N *
      (2 * (4 * Real.pi ^ 2) ^ N / ((2 * N).factorial : ℝ)) *
        ((1 - (((p : ℝ) ^ (2 * N + 1))⁻¹)) /
          (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1))) =
    (-1 : ℝ) ^ N *
      (2 * Real.pi ^ (2 * N) * Real.sqrt Real.pi *
        (1 - (((p : ℝ) ^ (2 * N + 1))⁻¹))) /
        (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1) *
          Real.Gamma ((N : ℝ) + 1) * Real.Gamma ((N : ℝ) + 1 / 2))
  rw [Real.Gamma_nat_eq_factorial,
    gamma_add_half,
    factorial_two_mul_eq_four_pow_mul_gaussianMomentFactor]
  field_simp [hsqrt, hfacN, hfac2N, hpDen, hfour]
  rw [mul_pow, ← pow_mul]
  ring

private theorem one_le_prime_pow_even (p : Nat.Primes) (n : ℕ) :
    (1 : ℝ) ≤ (p : ℝ) ^ (2 * connesConsaniArchimedeanPoleIndex n) := by
  apply one_le_pow₀
  exact_mod_cast (p.2.two_le.trans' (by omega : 1 ≤ 2))

private theorem connesConsaniArchimedeanArithmeticRatio_nonneg
    (p : Nat.Primes) (n : ℕ) :
    0 ≤ (1 - (((p : ℝ) ^
          (2 * connesConsaniArchimedeanPoleIndex n + 1))⁻¹)) /
      (((4 * connesConsaniArchimedeanPoleIndex n + 1 : ℕ) : ℝ) *
        ((p : ℝ) ^ (2 * connesConsaniArchimedeanPoleIndex n) - 1)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hpow : (1 : ℝ) < (p : ℝ) ^
      (2 * connesConsaniArchimedeanPoleIndex n) := by
    exact one_lt_pow₀ hp (by simp [connesConsaniArchimedeanPoleIndex])
  have hpow' : (1 : ℝ) ≤ (p : ℝ) ^
      (2 * connesConsaniArchimedeanPoleIndex n + 1) :=
    one_le_pow₀ hp.le
  have hpowpos : (0 : ℝ) < (p : ℝ) ^
      (2 * connesConsaniArchimedeanPoleIndex n + 1) := by positivity
  have hinv : ((p : ℝ) ^
      (2 * connesConsaniArchimedeanPoleIndex n + 1))⁻¹ ≤ 1 := by
    simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hpow'
  have hnum : 0 ≤ 1 - ((p : ℝ) ^
      (2 * connesConsaniArchimedeanPoleIndex n + 1))⁻¹ := by linarith
  have hden : 0 < (((4 * connesConsaniArchimedeanPoleIndex n + 1 : ℕ) : ℝ) *
      ((p : ℝ) ^ (2 * connesConsaniArchimedeanPoleIndex n) - 1)) :=
    mul_pos (by positivity) (by linarith)
  exact div_nonneg hnum hden.le

private theorem connesConsaniArchimedeanArithmeticRatio_le_one
    (p : Nat.Primes) (n : ℕ) :
    (1 - (((p : ℝ) ^
          (2 * connesConsaniArchimedeanPoleIndex n + 1))⁻¹)) /
      (((4 * connesConsaniArchimedeanPoleIndex n + 1 : ℕ) : ℝ) *
        ((p : ℝ) ^ (2 * connesConsaniArchimedeanPoleIndex n) - 1)) ≤ 1 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  let N := connesConsaniArchimedeanPoleIndex n
  have hN : 1 ≤ N := by simp [N, connesConsaniArchimedeanPoleIndex]
  have hp2 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hexp : 2 ≤ 2 * N := by omega
  have hpowmono : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (2 * N) := by
    exact pow_le_pow_right₀ (by linarith) hexp
  have hden : (1 : ℝ) ≤ (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1)) := by
    have hfac : (1 : ℝ) ≤ ((4 * N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ 4 * N + 1)
    have hsub : (1 : ℝ) ≤ (p : ℝ) ^ (2 * N) - 1 := by nlinarith
    calc
      (1 : ℝ) ≤ 1 * ((p : ℝ) ^ (2 * N) - 1) := by simpa using hsub
      _ ≤ ((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1) :=
        mul_le_mul_of_nonneg_right hfac (by linarith)
  have hnum : 1 - (((p : ℝ) ^ (2 * N + 1))⁻¹) ≤ 1 := by
    have : 0 ≤ (((p : ℝ) ^ (2 * N + 1))⁻¹) := by positivity
    linarith
  change (1 - (((p : ℝ) ^ (2 * N + 1))⁻¹)) /
      (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1)) ≤ 1
  exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).2 (hnum.trans hden)

theorem abs_connesConsaniArchimedeanCoefficient_le (p : Nat.Primes) (n : ℕ) :
    |connesConsaniArchimedeanCoefficient p n| ≤
      2 * (4 * Real.pi ^ 2) ^ connesConsaniArchimedeanPoleIndex n /
        ((connesConsaniArchimedeanPoleIndex n).factorial : ℝ) := by
  let N := connesConsaniArchimedeanPoleIndex n
  have hratio0 := connesConsaniArchimedeanArithmeticRatio_nonneg p n
  have hratio1 := connesConsaniArchimedeanArithmeticRatio_le_one p n
  have hbase0 : 0 ≤ 2 * (4 * Real.pi ^ 2) ^ N / ((2 * N).factorial : ℝ) := by
    positivity
  have hfac : (N.factorial : ℝ) ≤ ((2 * N).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : N ≤ 2 * N)
  have hinv : (((2 * N).factorial : ℝ))⁻¹ ≤ (N.factorial : ℝ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) hfac
  change |(-1 : ℝ) ^ N *
      (2 * (4 * Real.pi ^ 2) ^ N / ((2 * N).factorial : ℝ)) *
        ((1 - (((p : ℝ) ^ (2 * N + 1))⁻¹)) /
          (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1)))| ≤ _
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg hbase0, abs_of_nonneg hratio0]
  calc
    (2 * (4 * Real.pi ^ 2) ^ N / ((2 * N).factorial : ℝ)) *
          ((1 - (((p : ℝ) ^ (2 * N + 1))⁻¹)) /
            (((4 * N + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (2 * N) - 1)))
        ≤ (2 * (4 * Real.pi ^ 2) ^ N / ((2 * N).factorial : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hratio1 hbase0
    _ ≤ 2 * (4 * Real.pi ^ 2) ^ N / (N.factorial : ℝ) := by
      have hmul : 0 ≤ 2 * (4 * Real.pi ^ 2) ^ N := by positivity
      simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hinv hmul

theorem summable_norm_connesConsaniArchimedeanCoefficient (p : Nat.Primes) :
    Summable (fun n : ℕ => |connesConsaniArchimedeanCoefficient p n|) := by
  apply Summable.of_nonneg_of_le
    (fun n => abs_nonneg _)
    (fun n => abs_connesConsaniArchimedeanCoefficient_le p n)
  let R : ℝ := 4 * Real.pi ^ 2
  have hR : 0 ≤ R := by positivity
  have hsum := summable_factorialInv_jet 0 hR
  have hshift : Summable (fun n : ℕ =>
      ((connesConsaniArchimedeanPoleIndex n).factorial : ℝ)⁻¹ *
        R ^ connesConsaniArchimedeanPoleIndex n) := by
    rw [show (fun n : ℕ =>
        ((connesConsaniArchimedeanPoleIndex n).factorial : ℝ)⁻¹ *
          R ^ connesConsaniArchimedeanPoleIndex n) =
      (fun N : ℕ => ((N.factorial : ℝ))⁻¹ * R ^ N) ∘ fun n => n + 1 by
        funext n; simp [connesConsaniArchimedeanPoleIndex]]
    change Summable (fun n : ℕ => ((n + 1).factorial : ℝ)⁻¹ * R ^ (n + 1))
    exact (summable_nat_add_iff 1).2 (by simpa using hsum)
  simpa [R, mul_div_assoc, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    hshift.mul_left 2

/-- The `n`-th normalized rank-one archimedean pole contribution. -/
def connesConsaniArchimedeanTerm (p : Nat.Primes) (n : ℕ) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  InnerProductSpace.rankOne ℂ
    ((connesConsaniArchimedeanCoefficient p n : ℂ) •
      connesConsaniArchimedeanXi n)
    (connesConsaniArchimedeanEta n)

@[simp] theorem norm_connesConsaniArchimedeanTerm (p : Nat.Primes) (n : ℕ) :
    ‖connesConsaniArchimedeanTerm p n‖ =
      |connesConsaniArchimedeanCoefficient p n| := by
  rw [connesConsaniArchimedeanTerm, InnerProductSpace.norm_rankOne,
    norm_smul, norm_connesConsaniArchimedeanXi,
    norm_connesConsaniArchimedeanEta, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, mul_one]

theorem connesConsaniArchimedeanTerm_hasRankLE_one (p : Nat.Primes) (n : ℕ) :
    HasRankLE (connesConsaniArchimedeanTerm p n) 1 := by
  let x : ℕ → CCMCircleL2 := fun _ =>
    (connesConsaniArchimedeanCoefficient p n : ℂ) • connesConsaniArchimedeanXi n
  let y : ℕ → CCMCircleL2 := fun _ => connesConsaniArchimedeanEta n
  have h := hasRankLE_sum_range_rankOne x y 1
  simpa [connesConsaniArchimedeanTerm, x, y] using h

/-- Exact nonzero archimedean-pole series `E_infinity` of Theorem 4.4. -/
def connesConsaniArchimedeanPoleOperator (p : Nat.Primes) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  ∑' n : ℕ, connesConsaniArchimedeanTerm p n

/-- Literal Gamma-coefficient presentation of the source's `E_infinity` series. -/
theorem connesConsaniArchimedeanPoleOperator_eq_sourceSeries (p : Nat.Primes) :
    connesConsaniArchimedeanPoleOperator p =
      ∑' n : ℕ, InnerProductSpace.rankOne ℂ
        ((connesConsaniArchimedeanSourceCoefficient p n : ℂ) •
          connesConsaniArchimedeanXi n)
        (connesConsaniArchimedeanEta n) := by
  unfold connesConsaniArchimedeanPoleOperator
  congr 1
  funext n
  rw [connesConsaniArchimedeanTerm,
    connesConsaniArchimedeanCoefficient_eq_source]

/-- The nonzero archimedean-pole contribution is trace class. -/
theorem connesConsaniArchimedeanPoleOperator_memSchattenClass_one
    (p : Nat.Primes) :
    MemSchattenClass 1 (connesConsaniArchimedeanPoleOperator p) := by
  exact memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
    (A := fun n => connesConsaniArchimedeanTerm p n)
    (fun n => connesConsaniArchimedeanTerm_hasRankLE_one p n)
    (by simpa only [norm_connesConsaniArchimedeanTerm] using
      summable_norm_connesConsaniArchimedeanCoefficient p)

end

end RHTower
