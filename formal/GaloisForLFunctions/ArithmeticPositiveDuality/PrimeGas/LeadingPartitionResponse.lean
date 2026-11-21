import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.LocalPhaseContinuation
import GaloisForLFunctions.ZeroForcingCalculus.WittMonomialsShiftedConvolutionsAndBrauerCancellation
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# A prime heat amplitude from two partition germs

At a zero of any multiplicity or at a pole, the first nonzero Laurent
coefficients of the ordinary and sign-flipped partitions recover the local
prime heat amplitude. A single prime then detects isometry of the full split.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

abbrev PositiveSpectrum := {s : ℂ // 0 < s.re}

/-- First nonzero Laurent coefficient of the ordinary partition. -/
def partitionLead (s : PositiveSpectrum) := meromorphicTrailingCoeffAt riemannZeta s.val

/-- First nonzero Laurent coefficient after rotating a single prime. -/
def rotatedLead (p : Nat.Primes) (z : Circle) (s : PositiveSpectrum) :=
  meromorphicTrailingCoeffAt (rotatedPartition p z) s.val

theorem partitionLead_ne_zero (s : PositiveSpectrum) : partitionLead s ≠ 0 :=
  (meromorphicOn_riemannZeta _ (Set.mem_univ _)).meromorphicTrailingCoeffAt_ne_zero
    (ZeroForcingCalculus.meromorphicOrderAt_riemannZeta_ne_top _)

theorem rotatedLead_eq (p : Nat.Primes) (z : Circle) (s : PositiveSpectrum) :
    rotatedLead p z s = partitionLead s * HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ) s.val := by
  obtain ⟨ha, hn⟩ := primeCorrection_analytic_unit p z s
  unfold partitionLead
  change meromorphicTrailingCoeffAt (riemannZeta * HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ)) s.val = _
  rw [(meromorphicOn_riemannZeta _ (Set.mem_univ _)).meromorphicTrailingCoeffAt_mul ha.meromorphicAt,
    ha.meromorphicTrailingCoeffAt_of_ne_zero hn]

/-- The normalized difference reads the shell even when both partitions vanish. -/
def leadingResponse (p : Nat.Primes) (s : PositiveSpectrum) :=
  (partitionLead s - rotatedLead p (-1) s) / (partitionLead s + rotatedLead p (-1) s)

private theorem signLead_eq (p : Nat.Primes) (s : PositiveSpectrum) :
    rotatedLead p (-1) s = partitionLead s *
      ((1 - heat s.val (p : ℕ+)) / (1 + heat s.val (p : ℕ+))) := by
  rw [rotatedLead_eq, heat_eq_cpow, Nat.Primes.coe_pnat_nat]
  simp only [HTGeometry.eulerFactor, Circle.coe_neg, Circle.coe_one, neg_one_mul, sub_neg_eq_add]

private theorem one_add_heat_ne (p : Nat.Primes) (s : PositiveSpectrum) :
    1 + heat s.val (p : ℕ+) ≠ 0 := by
  rw [heat_eq_cpow, Nat.Primes.coe_pnat_nat]
  simpa only [Circle.coe_neg, Circle.coe_one, neg_one_mul, sub_neg_eq_add] using
    _root_.RHTower.one_sub_phase_cpow_ne_zero p (-1) s.property

theorem sum_partitionLeads_ne_zero (p : Nat.Primes) (s : PositiveSpectrum) :
    partitionLead s + rotatedLead p (-1) s ≠ 0 := by
  let q := heat s.val (p : ℕ+)
  have hd : 1 + q ≠ 0 := one_add_heat_ne p s
  have hsum : partitionLead s + rotatedLead p (-1) s = 2 * partitionLead s / (1 + q) := by
    rw [signLead_eq]
    change partitionLead s + partitionLead s * ((1-q)/(1+q)) = _
    field_simp [hd]
    ring
  rw [hsum]
  exact div_ne_zero (mul_ne_zero two_ne_zero (partitionLead_ne_zero s)) hd

theorem leadingResponse_eq_heat (p : Nat.Primes) (s : PositiveSpectrum) :
    leadingResponse p s = heat s.val (p : ℕ+) := by
  apply (div_eq_iff (sum_partitionLeads_ne_zero p s)).mpr
  rw [signLead_eq]
  field_simp [one_add_heat_ne p s]
  ring

/-- Equality of the two weighted leading intensities characterizes the critical line. -/
theorem leading_balance_iff (p : Nat.Primes) (s : PositiveSpectrum) :
    ((p : ℕ) : ℝ) * ‖partitionLead s - rotatedLead p (-1) s‖^2 =
      ‖partitionLead s + rotatedLead p (-1) s‖^2 ↔ s.val.re = 1/2 := by
  have hd := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sum_partitionLeads_ne_zero p s))
  have hm := shellMass_eq s.val (p : ℕ+)
  rw [Nat.Primes.coe_pnat_nat, ← leadingResponse_eq_heat p s, leadingResponse, norm_div, div_pow,
    ← mul_div_assoc] at hm
  have equiv : ((p : ℕ) : ℝ) * ‖partitionLead s - rotatedLead p (-1) s‖^2 =
      ‖partitionLead s + rotatedLead p (-1) s‖^2 ↔ shellMass s.val (p : ℕ+) = 1 := by
    rw [hm, div_eq_iff hd, one_mul]
  rw [equiv, shellMass, Real.exp_eq_one_iff]
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hE : energy (p : ℕ+) ≠ 0 := (Real.log_pos hp).ne'
  rw [mul_eq_zero, or_iff_left hE]
  constructor <;> intro h <;> linarith

/-- A single prime tests whether the full two-copy operator preserves probability. -/
theorem leading_balance_iff_isometry (p : Nat.Primes) (s : PositiveSpectrum) :
    ((p : ℕ) : ℝ) * ‖partitionLead s - rotatedLead p (-1) s‖^2 =
      ‖partitionLead s + rotatedLead p (-1) s‖^2 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x :=
  (leading_balance_iff p s).trans (split_isometric_iff s.val).symm

/-- At one prime the response magnitude distinguishes all real parts. -/
theorem leadingResponse_norm_eq_iff (p : Nat.Primes) (u v : PositiveSpectrum) :
    ‖leadingResponse p u‖ = ‖leadingResponse p v‖ ↔ u.val.re = v.val.re := by
  rw [leadingResponse_eq_heat, leadingResponse_eq_heat, norm_heat, norm_heat]
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  have hE : energy (p : ℕ+) ≠ 0 := (Real.log_pos hp).ne'
  exact ⟨fun h => neg_injective (mul_right_cancel₀ hE (Real.exp_injective h)),
    fun h => by rw [h]⟩

/-- Compare the local Laurent responses at the two points paired by zeta reflection. -/
theorem reflected_leadingResponse_iff_isometry (p : Nat.Primes)
    (s : {w : ℂ // 0 < w.re ∧ w.re < 1}) :
    ‖leadingResponse p ⟨s.val,s.2.1⟩‖ =
      ‖leadingResponse p ⟨1 - conj s.val, by
        simpa only [Complex.sub_re, Complex.one_re, Complex.conj_re] using sub_pos.mpr s.2.2⟩‖ ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x := by
  rw [leadingResponse_norm_eq_iff, split_isometric_iff, Complex.sub_re, Complex.one_re, Complex.conj_re]
  constructor <;> intro h <;> linarith

/-- The two normalized Laurent responses at 2 and 3 determine the spectral point. -/
theorem two_prime_leadingResponse_injective :
    Function.Injective (fun s : PositiveSpectrum =>
      (leadingResponse ⟨2,Nat.prime_two⟩ s, leadingResponse ⟨3,Nat.prime_three⟩ s)) := by
  intro u v h
  simp only [leadingResponse_eq_heat] at h
  exact Subtype.ext (two_prime_heat_injective h)

#print axioms rotatedLead_eq
#print axioms sum_partitionLeads_ne_zero
#print axioms leadingResponse_eq_heat
#print axioms leading_balance_iff
#print axioms leading_balance_iff_isometry
#print axioms reflected_leadingResponse_iff_isometry
#print axioms two_prime_leadingResponse_injective

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
