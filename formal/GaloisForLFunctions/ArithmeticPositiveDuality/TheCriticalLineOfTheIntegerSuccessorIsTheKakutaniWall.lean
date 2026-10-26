import GaloisForLFunctions.ArithmeticPositiveDuality.ArchimedeanPositiveDefiniteFunctionsLiveOnTheKroneckerLine
import GaloisForLFunctions.ArithmeticPositiveDuality.TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor
import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen

/-!
# The critical line of the integer successor is the Kakutani wall

The Hecke states `φ_s(x ↦ ax + b) = (nd)^{−s}·1[db ∈ ℤ]` are positive definite on `Aff(ℚ)` exactly
for `s ≥ 1/2` (`isPosDefOnGroup_heckeState_iff`). Their dilation parts `u ↦ (nd)^{−s}` are
positive definite on `ℚ_{>0}` for every `s > 0`; this file computes their spectral measure.

* **The Hecke spectrum is a prime-Poisson law** (`spectralMeasure_heckeWeight`). The spectral
  measure of `u ↦ (nd)^{−σ} u^{it}` on the prime torus is the product of the Poisson laws with
  parameters `p^{−σ+it}` (`primePoissonMeasure σ t`): the local moment `p^{−σ|k|+itk}` at the
  valuation `k = v_p(u)` multiplies to `(nd)^{−σ}u^{it}`, since `nd = Π_p p^{|v_p(u)|}`.
* **The wall** (`heckeState_kakutani_wall`). For `s > 0`: the Hecke state is positive definite iff
  `s ≥ 1/2`, and its dilation spectrum is equivalent to Haar measure iff `s > 1/2` (Kakutani:
  `Σ_p p^{−2s} < ∞`). At the critical line, the adelic Haar state of the integer successor, the
  spectrum is singular to Haar measure.

So the positivity threshold that the integer successor imposes on the Hecke weights is the
Kakutani wall of their spectral laws: admissible states live at or right of the wall, and the
critical state sits on it with a Haar-singular spectrum.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real BigOperators ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The local Poisson moment at a prime: `p^{−σ|k| + itk}`. -/
theorem circlePoissonFourierMoment_prime (σ t : ℝ) (hσ : 0 < σ) (p : Nat.Primes) (k : ℤ) :
    circlePoissonFourierMoment (primePoissonParameter σ t hσ p) k =
      cexp (((-σ * |(k : ℝ)| : ℝ) : ℂ) * Real.log (p : ℕ) + (t * k : ℝ) * I * Real.log (p : ℕ)) := by
  rcases k with n | n
  · simp only [circlePoissonFourierMoment, coe_primePoissonParameter, primePoissonParameterValue]
    rw [← Complex.exp_nat_mul]
    congr 1
    have : |((Int.ofNat n : ℤ) : ℝ)| = n := by simp
    rw [this]
    simp only [Int.ofNat_eq_coe, Int.cast_natCast]
    push_cast
    ring
  · simp only [circlePoissonFourierMoment, coe_primePoissonParameter, primePoissonParameterValue,
      ← Complex.exp_conj, ← Complex.exp_nat_mul]
    congr 1
    have : |((Int.negSucc n : ℤ) : ℝ)| = n + 1 := by
      rw [Int.cast_negSucc, abs_neg]; exact abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    rw [this, Int.cast_negSucc]
    simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

/-- `log a = Σ_{p ∈ T} v_p(a) log p` for natural `a ≠ 0` with its primes in `T`. -/
theorem log_eq_sum_padicValNat {a : ℕ} (ha : a ≠ 0) {T : Finset Nat.Primes}
    (hT : ∀ p : Nat.Primes, (p : ℕ) ∣ a → p ∈ T) :
    Real.log a = ∑ p ∈ T, (padicValNat p a : ℝ) * Real.log (p : ℕ) := by
  have h := congrArg (fun x : ℚ => Real.log (x : ℝ)) (prod_pow_padicValNat ha hT)
  simp only [Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast] at h
  rw [← h, Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => Real.log_pow _ _
  · intro p _
    exact pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)

/-- For `u = n/d` in lowest terms, `log(nd) = Σ_p |v_p(u)| log p`. -/
theorem log_index_eq_sum (u : posUnits) :
    Real.log ((((u : ℚˣ) : ℚ).num.natAbs : ℝ) * (((u : ℚˣ) : ℚ).den : ℝ)) =
      ∑ p ∈ (valFinsupp ((u : ℚˣ) : ℚ)).support,
        |((valFinsupp ((u : ℚˣ) : ℚ) p : ℤ) : ℝ)| * Real.log (p : ℕ) := by
  set q : ℚ := ((u : ℚˣ) : ℚ)
  have hq0 : q ≠ 0 := (u : ℚˣ).ne_zero
  have ha : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hq0)
  have hmem : ∀ p : Nat.Primes, (p : ℕ) ∣ q.num.natAbs * q.den → p ∈ primeSupp q := fun p h =>
    mem_primeSupp.mpr (Nat.mem_primeFactors.mpr ⟨p.2, h, mul_ne_zero ha q.den_ne_zero⟩)
  have hsub : (valFinsupp q).support ⊆ primeSupp q := fun p hp => by
    by_contra h
    exact Finsupp.mem_support_iff.mp hp (padicValRat_eq_zero_of_not_mem h)
  have hper : ∀ p : Nat.Primes, (padicValNat p q.num.natAbs : ℝ) + padicValNat p q.den =
      |((valFinsupp q p : ℤ) : ℝ)| := by
    intro p
    rw [valFinsupp_apply, padicValRat_def, padicValInt]
    have hcop : ¬ ((p : ℕ) ∣ q.num.natAbs ∧ (p : ℕ) ∣ q.den) := fun ⟨h1, h2⟩ =>
      p.2.not_dvd_one (Nat.Coprime.gcd_eq_one q.reduced ▸ Nat.dvd_gcd h1 h2)
    rcases not_and_or.mp hcop with h | h
    · rw [padicValNat.eq_zero_of_not_dvd h]
      simp only [Nat.cast_zero, zero_add, zero_sub, Int.cast_neg, Int.cast_natCast, abs_neg,
        Nat.abs_cast]
    · rw [padicValNat.eq_zero_of_not_dvd h]
      simp only [Nat.cast_zero, add_zero, sub_zero, Int.cast_natCast, Nat.abs_cast]
  rw [Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast q.den_ne_zero),
    log_eq_sum_padicValNat ha fun p h => hmem p (dvd_mul_of_dvd_left h _),
    log_eq_sum_padicValNat q.den_ne_zero fun p h => hmem p (dvd_mul_of_dvd_right h _),
    ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun p _ => by rw [← add_mul, hper p]]
  exact (Finset.sum_subset hsub fun p _ hp => by
    rw [Finsupp.notMem_support_iff.mp hp]; simp).symm

/-- The prime-Poisson integral of a valuation character: `(nd)^{−σ}u^{it}`. -/
theorem integral_ratChar_primePoissonMeasure (σ t : ℝ) (hσ : 0 < σ) (u : posUnits) :
    ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂(primePoissonMeasure σ t hσ) =
      ((((((u : ℚˣ) : ℚ).num.natAbs : ℝ) * (((u : ℚˣ) : ℚ).den : ℝ)) ^ (-σ) : ℝ) : ℂ) *
        cexp (Real.log ((u : ℚˣ) : ℚ) * t * I) := by
  set q : ℚ := ((u : ℚˣ) : ℚ)
  have hq0 : q ≠ 0 := (u : ℚˣ).ne_zero
  have hpos : (0 : ℝ) < (q.num.natAbs : ℝ) * (q.den : ℝ) := by
    have := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hq0)
    have := q.den_pos
    positivity
  show ∫ x, infiniteTorusFourier (valFinsupp q) x ∂(primePoissonMeasure σ t hσ) = _
  rw [integral_infiniteTorusFourier_primePoissonMeasure, Finsupp.prod]
  simp_rw [circlePoissonFourierMoment_prime]
  rw [← Complex.exp_sum, Real.rpow_def_of_pos hpos, Complex.ofReal_exp, ← Complex.exp_add,
    log_index_eq_sum u, log_eq_sum_valFinsupp u]
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **The Hecke spectrum is a prime-Poisson law.** Every finite measure on the prime torus
representing `u ↦ (nd)^{−σ}u^{it}` is the prime-Poisson law with parameters `p^{−σ+it}`. -/
theorem spectralMeasure_heckeWeight (σ t : ℝ) (hσ : 0 < σ) {μ : Measure PrimeTorus}
    [IsFiniteMeasure μ]
    (hμ : ∀ u : posUnits, ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ =
      ((((((u : ℚˣ) : ℚ).num.natAbs : ℝ) * (((u : ℚˣ) : ℚ).den : ℝ)) ^ (-σ) : ℝ) : ℂ) *
        cexp (Real.log ((u : ℚˣ) : ℚ) * t * I)) :
    μ = primePoissonMeasure σ t hσ :=
  finiteMeasure_ext_of_ratChar fun u => by
    rw [hμ u, integral_ratChar_primePoissonMeasure]

/-- **The critical line of the integer successor is the Kakutani wall.** For `s > 0` the Hecke
state `(nd)^{−s}·1[db ∈ ℤ]` is positive definite on `Aff(ℚ)` iff `s ≥ 1/2`; the spectral measure of
its dilation part is the prime-Poisson law `primePoissonMeasure s 0`, equivalent to Haar measure
iff `s > 1/2` and singular to it at `s = 1/2`. -/
theorem heckeState_kakutani_wall (s : ℝ) (hs : 0 < s) :
    (IsPosDefOnGroup (heckeState s) ↔ 1 / 2 ≤ s) ∧
      (∀ μ : Measure PrimeTorus, IsFiniteMeasure μ →
        (∀ u : posUnits, heckeState s (dilation (u : ℚˣ)) = ∫ x, ratChar ((u : ℚˣ) : ℚ) x ∂μ) →
          μ = primePoissonMeasure s 0 hs) ∧
      (primePoissonMeasure s 0 hs ≪ torusHaar Nat.Primes ↔ 1 / 2 < s) ∧
      (s ≤ 1 / 2 → (primePoissonMeasure s 0 hs).MutuallySingular (torusHaar Nat.Primes)) := by
  refine ⟨isPosDefOnGroup_heckeState_iff s, fun μ hμf hμ => ?_,
    primePoissonMeasure_absolutelyContinuous_torusHaar_iff s 0 hs,
    primePoissonMeasure_mutuallySingular_torusHaar_of_le_half s 0 hs⟩
  refine spectralMeasure_heckeWeight s 0 hs fun u => ?_
  rw [← hμ u, heckeState_dilation]
  simp

end GaloisForLFunctions.ArithmeticPositiveDuality
