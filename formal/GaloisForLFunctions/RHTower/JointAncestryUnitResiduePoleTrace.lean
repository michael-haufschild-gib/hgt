import GaloisForLFunctions.RHTower.JointAncestryPoleGluing
import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalHalfDensityDoubleLogBoundaryResidue
import GaloisForLFunctions.RHTower.PrimeDiagonalSingularValues

/-!
# The JAS unit residue is half the logarithm of the pole trace

The closed-flat JAS no-go attaches to every nonneutral Xi copy one unit of double-logarithmic
physical half-density energy.  This module identifies that residue exactly.

The pole sector `μ_1` is the product of circle Poisson laws with disk parameters `p⁻¹`.  Its
density at the theta point `1` is the product of the local Poisson kernels
`P_{p⁻¹}(1) = (1 + p⁻¹)/(1 - p⁻¹)`; the truncation through the `N`th prime is the pole trace
`T_N`.  The two-term logarithm expansion gives `|log P_{p⁻¹}(1) - 2/p| ≤ 4/p³`.  Since the
half-density energy of an off-line copy differs from `1/p` by a correction dominated by
`p^{-(1+|2β-1|)}`, the prefix energy `E_N(q)` and `(1/2) log T_N` differ by a convergent series:

* off the critical line, `E_N(q) - (1/2) log T_N` converges;
* on the critical line, `E_N(q) = 0` while `(1/2) log T_N → ∞`.

Both `E_N(q)` (off line) and `(1/2) log T_N` equal `log log N` plus a convergent quantity.  Thus the
unit residue is not an artifact of the half-density normalization: it is the divergence of the pole
sector's theta-point density, i.e. the pole of `ζ` at `1` seen through the prime-Poisson layer.  A
law excluding the residue must cancel the pole trace at every off-line copy.
-/

open Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

theorem primePoissonParameterValue_one_zero (p : Nat.Primes) :
    primePoissonParameterValue 1 0 p = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [primePoissonParameterValue,
    show (((-1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) * (Real.log (p : ℝ) : ℂ) =
      ((-Real.log (p : ℝ) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hp]

/-- Density of the pole sector's local factor at the theta point `1`. -/
def jasPoleTraceFactor (p : Nat.Primes) : ℝ :=
  poissonKernel 0 (primePoissonParameterValue 1 0 p) 1

theorem inv_prime_pos (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  positivity

theorem inv_prime_le_half (p : Nat.Primes) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  calc (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
    _ = 1 / 2 := by norm_num

theorem jasPoleTraceFactor_eq (p : Nat.Primes) :
    jasPoleTraceFactor p = (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) := by
  have hx0 := inv_prime_pos p
  have hx1 := inv_prime_le_half p
  set x : ℝ := (p : ℝ)⁻¹ with hx
  rw [jasPoleTraceFactor, poissonKernel_def, primePoissonParameterValue_one_zero, ← hx]
  have h1 : ‖(1 : ℂ) - 0 - ((x : ℂ) - 0)‖ = 1 - x := by
    rw [sub_zero, sub_zero, show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have h2 : ‖(x : ℂ) - 0‖ = x := by
    rw [sub_zero, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  rw [h1, h2, sub_zero, norm_one]
  have hne : (1 - x) ≠ 0 := by linarith
  field_simp
  ring

theorem jasPoleTraceFactor_pos (p : Nat.Primes) : 0 < jasPoleTraceFactor p := by
  rw [jasPoleTraceFactor_eq]
  have hx0 := inv_prime_pos p
  have hx1 := inv_prime_le_half p
  apply div_pos <;> linarith

/-- Two-term logarithm expansion of the local pole factor. -/
theorem abs_log_one_add_div_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |Real.log ((1 + x) / (1 - x)) - 2 * x| ≤ 2 * x ^ 3 / (1 - x) := by
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have habsn : |-x| < 1 := by rwa [abs_neg, abs_of_nonneg hx0]
  have hA := Real.abs_log_sub_add_sum_range_le habs 2
  have hB := Real.abs_log_sub_add_sum_range_le habsn 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_nonneg hx0,
    sub_neg_eq_add] at hA hB
  norm_num at hA hB
  rw [Real.log_div (by linarith) (by linarith)]
  have hsplit : Real.log (1 + x) - Real.log (1 - x) - 2 * x =
      (-x + x ^ 2 / 2 + Real.log (1 + x)) - (x + x ^ 2 / 2 + Real.log (1 - x)) := by ring
  rw [hsplit]
  calc |(-x + x ^ 2 / 2 + Real.log (1 + x)) - (x + x ^ 2 / 2 + Real.log (1 - x))|
      ≤ |-x + x ^ 2 / 2 + Real.log (1 + x)| + |x + x ^ 2 / 2 + Real.log (1 - x)| :=
        abs_sub _ _
    _ ≤ x ^ 3 / (1 - x) + x ^ 3 / (1 - x) := by
        apply add_le_add
        · convert hB using 2
        · convert hA using 2
    _ = 2 * x ^ 3 / (1 - x) := by ring

/-- The local pole factor is `2/p` up to a cubic error. -/
theorem abs_log_jasPoleTraceFactor_sub_le (p : Nat.Primes) :
    |Real.log (jasPoleTraceFactor p) - 2 * (p : ℝ)⁻¹| ≤ 4 * ((p : ℝ)⁻¹) ^ 3 := by
  have hx0 := inv_prime_pos p
  have hx1 := inv_prime_le_half p
  rw [jasPoleTraceFactor_eq]
  refine (abs_log_one_add_div_one_sub_sub_le hx0.le (by linarith)).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [pow_pos hx0 3]

/-- Pole trace: theta-point density of the pole sector truncated through the `N`th prime. -/
def jasPoleTracePrefix (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.range (N + 1), jasPoleTraceFactor (nthPrimeSubtype n)

theorem log_jasPoleTracePrefix (N : ℕ) :
    Real.log (jasPoleTracePrefix N) =
      ∑ n ∈ Finset.range (N + 1), Real.log (jasPoleTraceFactor (nthPrimeSubtype n)) :=
  Real.log_prod fun _ _ => (jasPoleTraceFactor_pos _).ne'

/-- The half-logarithmic pole factor minus the reciprocal prime is absolutely summable. -/
theorem summable_halfLogJasPoleTraceFactor_sub_inv :
    Summable (fun n : ℕ =>
      (1 / 2) * Real.log (jasPoleTraceFactor (nthPrimeSubtype n)) -
        ((nthPrimeSubtype n : Nat.Primes) : ℝ)⁻¹) := by
  have hcube : Summable (fun p : Nat.Primes => 2 * ((p : ℝ)⁻¹) ^ 3) := by
    refine ((summable_prime_rpow (sigma := 3) (by norm_num)).mul_left 2).congr fun p => ?_
    have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    rw [Real.rpow_neg hp.le, inv_pow]
    norm_cast
  have hcubeNat : Summable (fun n : ℕ => 2 * (((nthPrimeSubtype n : Nat.Primes) : ℝ)⁻¹) ^ 3) :=
    nthPrimeEquiv.summable_iff.mpr hcube
  refine Summable.of_norm_bounded hcubeNat fun n => ?_
  have h := abs_log_jasPoleTraceFactor_sub_le (nthPrimeSubtype n)
  rw [Real.norm_eq_abs]
  have hrw : (1 / 2) * Real.log (jasPoleTraceFactor (nthPrimeSubtype n)) -
      ((nthPrimeSubtype n : Nat.Primes) : ℝ)⁻¹ =
      (1 / 2) * (Real.log (jasPoleTraceFactor (nthPrimeSubtype n)) -
        2 * ((nthPrimeSubtype n : Nat.Primes) : ℝ)⁻¹) := by ring
  rw [hrw, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

/-- **Half-log pole trace asymptotics.**  `(1/2) log T_N - log log N` converges. -/
theorem exists_tendsto_halfLogJasPoleTracePrefix_sub_logLog :
    ∃ c : ℝ, Tendsto (fun N : ℕ =>
      (1 / 2) * Real.log (jasPoleTracePrefix N) - Real.log (Real.log (N : ℝ))) atTop (𝓝 c) := by
  have hrem := summable_halfLogJasPoleTraceFactor_sub_inv
  have hremLim := hrem.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine ⟨mertensSecondConstant + ∑' n : ℕ, ((1 / 2) *
      Real.log (jasPoleTraceFactor (nthPrimeSubtype n)) -
        ((nthPrimeSubtype n : Nat.Primes) : ℝ)⁻¹), ?_⟩
  refine (tendsto_primeDiagonalSum_sub_logLog.add hremLim).congr fun N => ?_
  simp only [Function.comp_apply]
  rw [log_jasPoleTracePrefix, primeDiagonalSum, Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [nthPrimeSubtype]
  ring

/-- The pole trace diverges: `(1/2) log T_N → ∞`. -/
theorem tendsto_halfLogJasPoleTracePrefix_atTop :
    Tendsto (fun N : ℕ => (1 / 2) * Real.log (jasPoleTracePrefix N)) atTop atTop := by
  obtain ⟨c, hc⟩ := exists_tendsto_halfLogJasPoleTracePrefix_sub_logLog
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogTop : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogTop
  refine (hloglogTop.atTop_add hc).congr fun N => ?_
  ring

/-- Off the critical line, the per-prime residue energy minus the half-log pole factor is
summable. -/
theorem summable_jasUnitResidue_sub_halfLogPoleTraceFactor (q : XiZeroCopy)
    (hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    Summable (fun n : ℕ =>
      thetaMobiusPrimeNormalProfileHalfDensityAmplitude (nthPrimeSubtype n) q ^ 2 -
        (1 / 2) * Real.log (jasPoleTraceFactor (nthPrimeSubtype n))) := by
  have hcorr : Summable (fun n : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyCorrection q (nthPrimeSubtype n)) :=
    nthPrimeEquiv.summable_iff.mpr
      (summable_thetaMobiusPrimeNormalHalfDensityEnergyCorrection_of_rate_ne_zero q hrate)
  refine (hcorr.neg.sub summable_halfLogJasPoleTraceFactor_sub_inv).congr fun n => ?_
  rw [thetaMobiusPrimeNormalHalfDensityEnergyCorrection, one_div]
  ring

/-- **Unit residue = half-log pole trace (off line).**  For an off-line copy the prefix
half-density energy differs from half the logarithm of the pole trace by a convergent quantity. -/
theorem exists_tendsto_energyPrefix_sub_halfLogJasPoleTrace_of_rate_ne_zero (q : XiZeroCopy)
    (hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    ∃ c : ℝ, Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N -
        (1 / 2) * Real.log (jasPoleTracePrefix N)) atTop (𝓝 c) := by
  have hs := summable_jasUnitResidue_sub_halfLogPoleTraceFactor q hrate
  refine ⟨_, (hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun N => ?_⟩
  simp only [Function.comp_apply]
  rw [thetaMobiusPrimeNormalHalfDensityEnergyPrefix, log_jasPoleTracePrefix, Finset.mul_sum,
    Finset.sum_sub_distrib]

/-- Off the critical line, the residue energy is `log log N` plus a convergent quantity. -/
theorem exists_tendsto_energyPrefix_sub_logLog_of_rate_ne_zero (q : XiZeroCopy)
    (hrate : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    ∃ c : ℝ, Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N - Real.log (Real.log (N : ℝ)))
      atTop (𝓝 c) := by
  obtain ⟨c₁, h₁⟩ := exists_tendsto_energyPrefix_sub_halfLogJasPoleTrace_of_rate_ne_zero q hrate
  obtain ⟨c₂, h₂⟩ := exists_tendsto_halfLogJasPoleTracePrefix_sub_logLog
  exact ⟨c₁ + c₂, (h₁.add h₂).congr fun N => by ring⟩

/-- On the critical line the residue energy vanishes identically. -/
theorem thetaMobiusPrimeNormalHalfDensityEnergyPrefix_eq_zero_of_rate_eq_zero (q : XiZeroCopy)
    (hrate : primeDepthBVWoldXiCenteredRate q.1 = 0) (N : ℕ) :
    thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N = 0 := by
  rw [thetaMobiusPrimeNormalHalfDensityEnergyPrefix]
  apply Finset.sum_eq_zero
  intro n _
  rw [thetaMobiusPrimeNormalProfileHalfDensityAmplitude, thetaMobiusPrimeNormalReflectionProfile_eq,
    hrate]
  simp

/-- On the critical line the residue minus the half-log pole trace diverges to `-∞`. -/
theorem tendsto_energyPrefix_sub_halfLogJasPoleTrace_atBot_of_rate_eq_zero (q : XiZeroCopy)
    (hrate : primeDepthBVWoldXiCenteredRate q.1 = 0) :
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N -
        (1 / 2) * Real.log (jasPoleTracePrefix N)) atTop atBot := by
  simp_rw [thetaMobiusPrimeNormalHalfDensityEnergyPrefix_eq_zero_of_rate_eq_zero q hrate,
    zero_sub]
  exact tendsto_neg_atTop_atBot.comp tendsto_halfLogJasPoleTracePrefix_atTop

/-- **Pole-trace dichotomy.**  A Xi copy is off the critical line exactly when its residue energy
tracks half the logarithm of the pole trace to a finite limit. -/
theorem exists_tendsto_energyPrefix_sub_halfLogJasPoleTrace_iff (q : XiZeroCopy) :
    (∃ c : ℝ, Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N -
        (1 / 2) * Real.log (jasPoleTracePrefix N)) atTop (𝓝 c)) ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  rw [← not_iff_not, not_not, ← primeDepthBVWoldXiCenteredRate_eq_zero_iff]
  constructor
  · intro hnone
    by_contra hrate
    exact hnone (exists_tendsto_energyPrefix_sub_halfLogJasPoleTrace_of_rate_ne_zero q hrate)
  · rintro hrate ⟨c, hc⟩
    exact not_tendsto_nhds_of_tendsto_atBot
      (tendsto_energyPrefix_sub_halfLogJasPoleTrace_atBot_of_rate_eq_zero q hrate) c hc

/-- RH is equivalent to every Xi copy failing to track the pole trace: the residue minus the
half-log pole trace diverges to `-∞` on every copy. -/
theorem forall_tendsto_energyPrefix_sub_halfLogJasPoleTrace_atBot_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N -
        (1 / 2) * Real.log (jasPoleTracePrefix N)) atTop atBot) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    by_contra hoff
    have hmult : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
      have hpos := xi_divisor_pos_on_support rho
      omega
    let q : XiZeroCopy := ⟨rho, ⟨0, hmult⟩⟩
    obtain ⟨c, hc⟩ := (exists_tendsto_energyPrefix_sub_halfLogJasPoleTrace_iff q).2 hoff
    exact not_tendsto_nhds_of_tendsto_atBot (h q) c hc
  · intro hRH q
    apply tendsto_energyPrefix_sub_halfLogJasPoleTrace_atBot_of_rate_eq_zero
    rw [primeDepthBVWoldXiCenteredRate_eq_zero_iff]
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

end

end RHTower
