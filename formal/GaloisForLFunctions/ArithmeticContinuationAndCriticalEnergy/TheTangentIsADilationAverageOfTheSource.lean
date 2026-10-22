import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSignedWorkChangesSignOnce
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The tangent is a dilation average of the source

Differentiating the damped Möbius row in the damping multiplies its coefficients by `−log d`, and
`Λ * μ = −μ log` turns that into a convolution by the damped prime row `Λ_ε(j) = Λ(j) j^{-ε}`.  At
the level of responses this says that the tangent row is the source row *dilated by prime powers*:

`Λ^{resp}_ε(k) = Σ_{j ∣ k} Λ(j) j^{-ε} · c^{resp}_ε(k/j)`
(`dampedVonMangoldt_eq_dilation_convolution`),

and summing over a prefix with the hyperbola rearrangement
(`sum_Icc_divisor_convolution_eq_dilation`) gives the identity the programme's last trap names, for
the **integer** prefix and with its correction written out:

`E_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε} A_ε(⌊n/j⌋) + (m₀(ε) Ψ_ε(n) − n m(ε))`,
`Ψ_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε} ⌊n/j⌋`  (`dampedChebyshevError_eq_dilation`).

Pairing with the source in the pronic metric turns the complete signed work into the **numerical
range of the prime dilation operator at the literal source**, plus that explicit polar pairing
(`signedDampingWork_eq_dilationForm_add_correction`).  The corpus's standing warning is that a
term-by-term majorant of this dilation sum meets `Σ_k Λ(k) k^{−ε−1/2}` and cannot pass below half
damping; what the identity makes available instead is the signed form, where a lower bound on one
quadratic form — not a majorant — closes the problem
(`riemannHypothesis_of_nonneg_dilationForm_add_correction`).
-/

open Finset ArithmeticFunction RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The hyperbola rearrangement -/

/-- **A prefix of a Dirichlet convolution is a dilation average of prefixes.** -/
theorem sum_Icc_divisor_convolution_eq_dilation (f g : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Icc 1 n, ∑ j ∈ k.divisors, f j * g (k / j)) =
      ∑ j ∈ Icc 1 n, f j * ∑ m ∈ Icc 1 (n / j), g m := by
  have hinner : ∀ k ∈ Icc 1 n, (∑ j ∈ k.divisors, f j * g (k / j)) =
      ∑ j ∈ Icc 1 n, if j ∣ k then f j * g (k / j) else 0 := by
    intro k hk
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    rw [mem_Icc] at hk
    ext j
    rw [Nat.mem_divisors, Finset.mem_filter, mem_Icc]
    constructor
    · rintro ⟨hjk, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hjk (by omega), (Nat.le_of_dvd (by omega) hjk).trans hk.2⟩,
        hjk⟩
    · rintro ⟨-, hjk⟩
      exact ⟨hjk, by omega⟩
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mem_Icc] at hj
  have hj0 : 0 < j := hj.1
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_nbij' (fun k => k / j) (fun m => j * m) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, mem_Icc] at hk
    rw [mem_Icc]
    exact ⟨(Nat.one_le_div_iff hj0).mpr (Nat.le_of_dvd (by omega) hk.2),
      Nat.div_le_div_right hk.1.2⟩
  · intro m hm
    rw [mem_Icc] at hm
    rw [Finset.mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, Dvd.intro m rfl⟩
    · exact Nat.mul_pos hj0 hm.1
    · have h := (Nat.le_div_iff_mul_le hj0).mp hm.2
      calc j * m = m * j := Nat.mul_comm j m
        _ ≤ n := h
  · intro k hk
    rw [Finset.mem_filter] at hk
    exact Nat.mul_div_cancel' hk.2
  · intro m _
    exact Nat.mul_div_cancel_left m hj0
  · intro k _
    rfl

/-! ## §2. The tangent row is the source row dilated by prime powers -/

/-- The damped prime row `Λ_ε(j) = Λ(j) j^{-ε}`: the dilation weights. -/
def dampedPrimeWeight (ε : ℝ) (j : ℕ) : ℝ := vonMangoldt j * (j : ℝ) ^ (-ε)

private def dampedMuAF (ε : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (moebius n : ℝ) * (n : ℝ) ^ (-ε), by simp⟩

private def dampedLambdaAF (ε : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => vonMangoldt n * (n : ℝ) ^ (-ε), by simp⟩

private def dampedMuLogAF (ε : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => -((moebius n : ℝ) * Real.log n * (n : ℝ) ^ (-ε)), by simp⟩

private theorem dampedMuAF_apply (ε : ℝ) (n : ℕ) :
    dampedMuAF ε n = (moebius n : ℝ) * (n : ℝ) ^ (-ε) := rfl

private theorem dampedLambdaAF_apply (ε : ℝ) (n : ℕ) :
    dampedLambdaAF ε n = vonMangoldt n * (n : ℝ) ^ (-ε) := rfl

private theorem dampedMuLogAF_apply (ε : ℝ) (n : ℕ) :
    dampedMuLogAF ε n = -((moebius n : ℝ) * Real.log n * (n : ℝ) ^ (-ε)) := rfl

/-- The damped form of `Λ * μ = −μ log`: the damping twist is completely multiplicative, so it
passes through the convolution. -/
private theorem dampedLambda_mul_dampedMu (ε : ℝ) :
    dampedLambdaAF ε * dampedMuAF ε = dampedMuLogAF ε := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply]
  have hsplit : ∀ x ∈ n.divisorsAntidiagonal,
      dampedLambdaAF ε x.1 * dampedMuAF ε x.2 =
        (n : ℝ) ^ (-ε) * (vonMangoldt x.1 * (moebius x.2 : ℝ)) := by
    intro x hx
    obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rw [dampedLambdaAF_apply, dampedMuAF_apply, ← hprod]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum,
    Nat.sum_divisorsAntidiagonal (fun a b => vonMangoldt a * (moebius b : ℝ)),
    dampedMuLogAF_apply]
  have hΛμ : (∑ d ∈ n.divisors, vonMangoldt d * (moebius (n / d) : ℝ)) =
      -((moebius n : ℝ) * Real.log n) := by
    rw [RHTower.Sieve.moebius_mul_log_apply n]
    ring
  rw [hΛμ]
  ring

/-- **The tangent row is the source row dilated by prime powers.**  The response of the damping
tangent at `k` is the prime-power dilation average of the source response. -/
theorem dampedVonMangoldt_eq_dilation_convolution (ε : ℝ) (k : ℕ) :
    dampedVonMangoldt ε k =
      ∑ j ∈ k.divisors, dampedPrimeWeight ε j * pmPowerDampedDivisorCoeff ε (k / j) := by
  have hcoeff : ∀ m : ℕ, pmPowerDampedDivisorCoeff ε m = (dampedMuAF ε * ↑ζ) m := by
    intro m
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    unfold pmPowerDampedDivisorCoeff
    exact Finset.sum_congr rfl fun d _ => (dampedMuAF_apply ε d).symm
  have hvm : dampedVonMangoldt ε k = (dampedMuLogAF ε * ↑ζ) k := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    unfold dampedVonMangoldt
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [dampedMuLogAF_apply]
  rw [hvm, ← dampedLambda_mul_dampedMu, mul_assoc, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => dampedLambdaAF ε a * (dampedMuAF ε * ↑ζ) b)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [dampedLambdaAF_apply, ← hcoeff, dampedPrimeWeight]

/-! ## §3. The dilation identity for the centred tangent -/

/-- The damped prime floor sum `Ψ_ε(n) = Σ_{j ≤ n} Λ(j) j^{-ε} ⌊n/j⌋`. -/
def dampedPrimeFloorSum (ε : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j * ((n / j : ℕ) : ℝ)

/-- **The centred tangent as a dilation average of the centred source**, with the exact correction
produced by the two centrings and the integer parts. -/
theorem dampedChebyshevError_eq_dilation (ε : ℝ) (n : ℕ) :
    dampedChebyshevError ε n =
      (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j *
          pmPowerDampedCenteredDivisorPrefix ε ((n / j : ℕ))) +
        ((pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε n -
          dampedReadout ε * n) := by
  have hconv : (∑ k ∈ Icc 1 n, dampedVonMangoldt ε k) =
      ∑ j ∈ Icc 1 n, dampedPrimeWeight ε j *
        ∑ m ∈ Icc 1 (n / j), pmPowerDampedDivisorCoeff ε m := by
    rw [← sum_Icc_divisor_convolution_eq_dilation (dampedPrimeWeight ε)
      (pmPowerDampedDivisorCoeff ε) n]
    exact Finset.sum_congr rfl fun k _ => dampedVonMangoldt_eq_dilation_convolution ε k
  have hcentre : ∀ j ∈ Icc 1 n,
      dampedPrimeWeight ε j * ∑ m ∈ Icc 1 (n / j), pmPowerDampedDivisorCoeff ε m =
        dampedPrimeWeight ε j * pmPowerDampedCenteredDivisorPrefix ε (n / j) +
          (pmPowerDampedDivisorDensity ε).re *
            (dampedPrimeWeight ε j * ((n / j : ℕ) : ℝ)) := by
    intro j _
    rw [pmPowerDampedCenteredDivisorPrefix_eq]
    ring
  unfold dampedChebyshevError dampedPrimeFloorSum
  rw [hconv, Finset.sum_congr rfl hcentre, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-! ## §4. The signed work is a dilation numerical range -/

/-- The pronic dilation form of the source: the numerical range of the prime dilation operator at
the literal centred source. -/
def dilationForm (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n *
    (∑ j ∈ Icc 1 n, dampedPrimeWeight ε j *
      pmPowerDampedCenteredDivisorPrefix ε (n / j)) / ((n : ℝ) * ((n : ℝ) + 1))

/-- The explicit polar pairing produced by the two centrings. -/
def polarDilationCorrection (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n *
    ((pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε n -
      dampedReadout ε * n) / ((n : ℝ) * ((n : ℝ) + 1))

/-- **The complete signed work is the dilation numerical range plus the polar pairing.** -/
theorem signedDampingWork_eq_dilationForm_add_correction (ε : ℝ) (T : ℕ) :
    signedDampingWork ε T = dilationForm ε T + polarDilationCorrection ε T := by
  unfold signedDampingWork dilationForm polarDilationCorrection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dampedChebyshevError_eq_dilation]
  ring

/-- **The dilation criterion for the Riemann hypothesis.**  A sign for the numerical range of the
prime dilation operator at the literal source, against the explicit polar pairing, gives RH. -/
theorem riemannHypothesis_of_nonneg_dilationForm_add_correction
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      0 ≤ dilationForm ε T + polarDilationCorrection ε T) :
    RiemannHypothesis :=
  riemannHypothesis_of_nonneg_signedWork fun T ε hε hε2 => by
    rw [signedDampingWork_eq_dilationForm_add_correction]
    exact h T ε hε hε2

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
