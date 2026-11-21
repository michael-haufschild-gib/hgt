import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoherentShiftReadings
import GaloisForLFunctions.PrimeTorusTheory.TheLogarithmOfAFibre
import GaloisForLFunctions.HTGeometry.PositiveIntegerBlockOperators

/-!
# Euler logarithm of a coherent overlap

The inner product of two normalized Gibbs square roots is a quotient of
Dirichlet series. Its Euler logarithm separates a real prime mismatch, a
prime phase angle, and a prime-power remainder analytic at the partition pole.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology GaloisForLFunctions.HTGeometry GaloisForLFunctions.PrimeTorusTheory
open scoped ComplexConjugate

/-- Complex visibility of two preparations at the same temperature. -/
def phaseOverlap (χ ψ : ℕ+ →* Circle) (β : TraceTemperature) : ℂ :=
  inner ℂ (coherentVector χ β) (coherentVector ψ β)

/-- The character extended by zero to the zeroth Dirichlet coefficient. -/
private def natPhase (ρ : ℕ+ →* Circle) : ℕ →*₀ ℂ where
  toFun := PNatBlock.extZero (fun n => (ρ n : ℂ))
  map_zero' := PNatBlock.extZero_zero _
  map_one' := by change ((ρ 1 : Circle) : ℂ) = 1; simp
  map_mul' a b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    let m : ℕ+ := ⟨a,ha⟩
    let n : ℕ+ := ⟨b,hb⟩
    change PNatBlock.extZero _ ((m*n : ℕ+) : ℕ) = PNatBlock.extZero _ m * PNatBlock.extZero _ n
    rw [PNatBlock.extZero_coe, PNatBlock.extZero_coe, PNatBlock.extZero_coe, map_mul, Circle.coe_mul]

private theorem natPhase_pos (ρ : ℕ+ →* Circle) (n : ℕ+) : natPhase ρ n = (ρ n : ℂ) :=
  PNatBlock.extZero_coe (fun k : ℕ+ => (ρ k : ℂ)) n

private theorem natPhase_bound (ρ : ℕ+ →* Circle) (n : ℕ) : ‖natPhase ρ n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact (congrArg norm (natPhase_pos ρ ⟨n,hn⟩)).le.trans (Circle.norm_coe _).le

private theorem natPhase_prime (ρ : ℕ+ →* Circle) (n : ℕ) (hn : n.Prime) : ‖natPhase ρ n‖ = 1 :=
  (congrArg norm (natPhase_pos ρ ⟨n,hn.pos⟩)).trans (Circle.norm_coe _)

private theorem thermal_cpow (β : TraceTemperature) (n : ℕ+) :
    ((n : ℕ) : ℂ) ^ (-(β.val : ℂ)) = (thermalWeight β n : ℂ) := by
  rw [← heat_eq_cpow]
  simp only [heat, thermalWeight, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]

/-- Dirichlet trace of a relative shell phase before normalization. -/
def phaseTrace (ρ : ℕ+ →* Circle) (β : TraceTemperature) :=
  ∑' n : ℕ+, (ρ n : ℂ) * (thermalWeight β n : ℂ)

theorem phaseTrace_one (β : TraceTemperature) : phaseTrace 1 β = riemannZeta β.val := by
  simpa only [phaseTrace, MonoidHom.one_apply, Circle.coe_one, one_mul, ← Complex.ofReal_tsum] using
    thermalWeight_partition β

theorem phaseOverlap_eq_trace (χ ψ : ℕ+ →* Circle) (β : TraceTemperature) :
    phaseOverlap χ ψ β = phaseTrace (ψ/χ) β / riemannZeta β.val := by
  rw [phaseOverlap, lp.inner_eq_tsum, phaseTrace, ← tsum_div_const]
  apply tsum_congr
  intro n
  have hvec : coherentVector ψ β n = ((ψ/χ) n : ℂ) * coherentVector χ β n := by
    rw [MonoidHom.div_apply, Circle.coe_div]
    change (ψ n : ℂ) * _ / _ = ((ψ n : ℂ)/(χ n : ℂ)) * ((χ n : ℂ) * _ / _)
    rw [← mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _ (Circle.coe_ne_zero _)]
  rw [RCLike.inner_apply, hvec, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    coherentVector_shell, Complex.ofReal_div, ← thermalWeight_partition, Complex.ofReal_re, mul_div_assoc]

/-- A prime has weight 1/p at the pole. -/
def primeWeight (b : ℝ) (p : Nat.Primes) := Real.exp (-b * energy (p : ℕ+))

theorem primeWeight_one (p : Nat.Primes) : primeWeight 1 p = ((p : ℕ) : ℝ)⁻¹ := by
  change Real.exp (-1 * Real.log ((p.val : ℕ) : ℝ)) = _
  rw [neg_one_mul, Real.exp_neg, Real.exp_log (Nat.cast_pos.mpr p.2.pos)]

theorem primeWeight_le_one_weight (β : TraceTemperature) (p : Nat.Primes) :
    primeWeight β.val p ≤ primeWeight 1 p :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg β.property.le)
    (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)))

theorem primeWeight_summable (β : TraceTemperature) : Summable (primeWeight β.val) := by
  have hi : Function.Injective (fun p : Nat.Primes => (p : ℕ+)) :=
    fun p q h => Subtype.ext (congrArg PNat.val h)
  exact (thermalWeight_summable β).comp_injective hi

theorem primeWeight_limit (p : Nat.Primes) :
    Tendsto (fun β : TraceTemperature => primeWeight β.val p) atPartitionPole (𝓝 (primeWeight 1 p)) := by
  have hc : Continuous (fun b => primeWeight b p) :=
    Real.continuous_exp.comp (continuous_neg.mul continuous_const)
  exact (hc.tendsto 1).comp (tendsto_comap.mono_right nhdsWithin_le_nhds)

/-- Half the squared chord between the relative prime phase and the identity. -/
def primeMismatch (ρ : ℕ+ →* Circle) (p : Nat.Primes) : ℝ := 1 - (ρ (p : ℕ+) : ℂ).re

theorem primeMismatch_bounds (ρ : ℕ+ →* Circle) (p : Nat.Primes) :
    0 ≤ primeMismatch ρ p ∧ primeMismatch ρ p ≤ 2 := by
  have h := Complex.abs_re_le_norm (ρ (p : ℕ+) : ℂ)
  rw [Circle.norm_coe, abs_le] at h
  unfold primeMismatch
  constructor <;> linarith only [h.1,h.2]

def dampedMismatch (ρ : ℕ+ →* Circle) (b : ℝ) :=
  ∑' p : Nat.Primes, primeMismatch ρ p * primeWeight b p

/-- The first-order Euler angle, with the same thermal damping as the shell measurement. -/
def primeDrift (ρ : ℕ+ →* Circle) (β : TraceTemperature) :=
  ∑' p : Nat.Primes, (ρ (p : ℕ+) : ℂ).im * primeWeight β.val p

/-- Difference of logarithmic contributions from prime powers of order at least two. -/
def overlapRemainder (ρ : ℕ+ →* Circle) (s : ℂ) :=
  hullRem s (natPhase ρ) - hullRem s (natPhase 1)

theorem overlapRemainder_analytic (ρ : ℕ+ →* Circle) :
    AnalyticOnNhd ℂ (overlapRemainder ρ) rightHalf :=
  fun s hs => (analyticOnNhd_hullRem (natPhase_prime ρ) s hs).sub
    (analyticOnNhd_hullRem (natPhase_prime 1) s hs)

theorem overlapRemainder_limit (ρ : ℕ+ →* Circle) :
    Tendsto (fun β : TraceTemperature => overlapRemainder ρ β.val) atPartitionPole
      (𝓝 (overlapRemainder ρ 1)) :=
  (overlapRemainder_analytic ρ 1 (show (1:ℝ)/2 < (1:ℂ).re by norm_num)).continuousAt.tendsto.comp
    (tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds)

private theorem phaseTrace_exp (ρ : ℕ+ →* Circle) (β : TraceTemperature) :
    phaseTrace ρ β = Complex.exp ((∑' p : Nat.Primes, eulerVar β.val (natPhase ρ) p) +
      hullRem β.val (natPhase ρ)) := by
  rw [exp_tsum_eq_tsum (natPhase_bound ρ) (natPhase_prime ρ) (show 1 < (β.val : ℂ).re from β.2),
    ← PNatBlock.tsum_pnat _ (by simp)]
  exact tsum_congr fun n => by rw [natPhase_pos, thermal_cpow]

private theorem prime_term (ρ : ℕ+ →* Circle) (β : TraceTemperature) (p : Nat.Primes) :
    eulerVar β.val (natPhase ρ) p = (ρ (p : ℕ+) : ℂ) * (primeWeight β.val p : ℂ) := by
  change (((p : ℕ+) : ℕ) : ℂ) ^ (-(β.val : ℂ)) * natPhase ρ ((p : ℕ+) : ℕ) = _
  rw [thermal_cpow β (p : ℕ+), natPhase_pos, mul_comm]
  rfl

private theorem prime_difference (ρ : ℕ+ →* Circle) (β : TraceTemperature) :
    (∑' p : Nat.Primes, eulerVar β.val (natPhase ρ) p) -
    (∑' p : Nat.Primes, eulerVar β.val (natPhase 1) p) =
      -(dampedMismatch ρ β.val : ℂ) + (primeDrift ρ β : ℂ)*Complex.I := by
  have hs (κ : ℕ+ →* Circle) := summable_eulerVar (natPhase_prime κ) (show 1 < (β.val : ℂ).re from β.2)
  let d (p : Nat.Primes) := eulerVar β.val (natPhase ρ) p - eulerVar β.val (natPhase 1) p
  have hd : Summable d := (hs ρ).sub (hs 1)
  rw [← (hs ρ).tsum_sub (hs 1)]
  change (∑' p, d p) = _
  apply Complex.ext
  · rw [Complex.re_tsum hd]
    simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
      neg_zero, add_zero, dampedMismatch, ← tsum_neg]
    apply tsum_congr
    intro p
    simp only [d, prime_term, MonoidHom.one_apply, Circle.coe_one, one_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, primeMismatch]
    ring
  · rw [Complex.im_tsum hd]
    simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add,
      Complex.mul_I_im, Complex.ofReal_re, primeDrift]
    apply tsum_congr
    intro p
    simp only [d, prime_term, MonoidHom.one_apply, Circle.coe_one, one_mul, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, sub_zero]

/-- Exact Euler decomposition of the measured overlap. -/
theorem phaseOverlap_logarithm (χ ψ : ℕ+ →* Circle) (β : TraceTemperature) :
    phaseOverlap χ ψ β = Complex.exp (-(dampedMismatch (ψ/χ) β.val : ℂ) +
      (primeDrift (ψ/χ) β : ℂ)*Complex.I + overlapRemainder (ψ/χ) β.val) := by
  rw [phaseOverlap_eq_trace, ← phaseTrace_one, phaseTrace_exp, phaseTrace_exp, ← Complex.exp_sub,
    ← prime_difference, overlapRemainder]
  congr 1
  ring

#print axioms phaseOverlap_eq_trace
#print axioms overlapRemainder_analytic
#print axioms phaseOverlap_logarithm

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
