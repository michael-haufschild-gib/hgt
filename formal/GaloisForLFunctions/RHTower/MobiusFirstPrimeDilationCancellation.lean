import GaloisForLFunctions.RHTower.MobiusReciprocalPrimitiveRatio
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeHarmonic
import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall
import GaloisForLFunctions.RHTower.RouteECofactorUnsignedMass
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# First-prime signed dilation channel of the Möbius energy

The literal Möbius coefficients at `d` and `2d` have opposite signs for every
odd squarefree `d`. Their two oriented Gamma--Hankel entries at the boundary
exponent one total `-2/(3d)`. This one source-specific off-diagonal channel
therefore has logarithmically negative mass. The same sign gives a negative
channel for the cubic reciprocal moment. Neither bound controls the *complete*
off-diagonal: other primitive ratios can compensate it.
-/

open Finset ArithmeticFunction

namespace RHTower

private theorem cubic_firstPrime_pair_kernel (d : ℕ) (hd : 0 < d) :
    cubicMomentKernel 0 d (2*d) = 4 / (243 * (d : ℝ)) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  unfold cubicMomentKernel
  norm_num
  field_simp
  ring

private theorem mobius_firstPrime_pair_sign (d : ℕ) (hcop : Nat.Coprime d 2)
    (hsf : Squarefree d) :
    mobiusRealCoefficient d * mobiusRealCoefficient (2*d) = -1 := by
  have hcop' : Nat.Coprime 2 d := hcop.symm
  have hmul := Sieve.moebius_mul_of_coprime hcop'
  have hm2 : moebius 2 = -1 := by simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hsq : ((moebius d : ℤ) : ℝ) ^ (2 : ℕ) = 1 := by
    have hne : moebius d ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;> rw [hm] <;> norm_num
  unfold mobiusRealCoefficient
  rw [hmul, hm2]
  push_cast
  nlinarith

/-- Two oriented `d,2d` entries of the cubic reciprocal energy. -/
noncomputable def firstPrimeDilationCubicContribution (M : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d 2 ∧ Squarefree d),
    2 * mobiusRealCoefficient d * mobiusRealCoefficient (2*d) *
      cubicMomentKernel 0 d (2*d)

theorem firstPrimeDilationCubicContribution_eq (M : ℕ) :
    firstPrimeDilationCubicContribution M =
      -(8 / 243 : ℝ) *
        ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d 2 ∧ Squarefree d),
          1 / (d : ℝ) := by
  unfold firstPrimeDilationCubicContribution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdI, hcop, hsf⟩ := Finset.mem_filter.mp hd
  have hdpos := (Finset.mem_Icc.mp hdI).1
  calc
    2 * mobiusRealCoefficient d * mobiusRealCoefficient (2*d) *
        cubicMomentKernel 0 d (2*d) =
      2 * (mobiusRealCoefficient d * mobiusRealCoefficient (2*d)) *
        cubicMomentKernel 0 d (2*d) := by ring
    _ = -(8 / 243 : ℝ) * (1 / (d : ℝ)) := by
      rw [mobius_firstPrime_pair_sign d hcop hsf, cubic_firstPrime_pair_kernel d hdpos]
      ring

/-- The `1:2` primitive-ratio cubic channel has a negative logarithmic drift. -/
theorem firstPrimeDilationCubicContribution_le (M : ℕ) (hM : 1 ≤ M) :
    firstPrimeDilationCubicContribution M ≤
      -(1 / 243 : ℝ) * Real.log (M : ℝ) + 7 / 243 := by
  have hmass := Sieve.sum_inv_coprime_squarefree_ge
    (M := M) (Q := 2) (by norm_num) (by norm_num) hM (by norm_num)
  rw [firstPrimeDilationCubicContribution_eq]
  nlinarith

/-- The two oriented boundary Gamma--Hankel entries are the literal
`d-1,2d-1` matrix entries of the finite Möbius source. -/
theorem gamma_firstPrime_pair_atom (d : ℕ) (hd : 1 ≤ d) :
    2 * shiftedMobiusRealCoefficient (d-1) *
        shiftedMobiusRealCoefficient (2*d-1) /
        (((d-1) + (2*d-1) + 2 : ℕ) : ℝ) =
      2 * mobiusRealCoefficient d * mobiusRealCoefficient (2*d) / (3 * (d : ℝ)) := by
  have h1 : d - 1 + 1 = d := by omega
  have h2 : 2*d - 1 + 1 = 2*d := by omega
  have hden : (d-1) + (2*d-1) + 2 = 3*d := by omega
  simp only [shiftedMobiusRealCoefficient, mobiusRealCoefficient, h1, h2, hden]
  push_cast
  ring

/-- The actual first-prime signed subfamily of the finite Gamma--Hankel covariance. -/
noncomputable def firstPrimeDilationGammaContribution (M : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d 2 ∧ Squarefree d),
    2 * mobiusRealCoefficient d * mobiusRealCoefficient (2*d) / (3 * (d : ℝ))

theorem firstPrimeDilationGammaContribution_eq_matrixSubsum (M : ℕ) :
    firstPrimeDilationGammaContribution M =
      ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d 2 ∧ Squarefree d),
        2 * shiftedMobiusRealCoefficient (d-1) *
          shiftedMobiusRealCoefficient (2*d-1) /
          (((d-1) + (2*d-1) + 2 : ℕ) : ℝ) := by
  unfold firstPrimeDilationGammaContribution
  apply Finset.sum_congr rfl
  intro d hd
  exact (gamma_firstPrime_pair_atom d (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1).symm

/-- Both indices in the signed ray belong to the finite section of size `2M`. -/
theorem firstPrimeDilationGamma_pair_indices_in_cutoff
    (M d : ℕ) (hd : d ∈ Finset.Icc 1 M) :
    d-1 ∈ Finset.range (2*M) ∧ 2*d-1 ∈ Finset.range (2*M) := by
  simp only [Finset.mem_range]
  have hd' := Finset.mem_Icc.mp hd
  omega

theorem firstPrimeDilationGammaContribution_eq (M : ℕ) :
    firstPrimeDilationGammaContribution M =
      -(2 / 3 : ℝ) *
        ∑ d ∈ (Finset.Icc 1 M).filter (fun d => Nat.Coprime d 2 ∧ Squarefree d),
          1 / (d : ℝ) := by
  unfold firstPrimeDilationGammaContribution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨_, hcop, hsf⟩ := Finset.mem_filter.mp hd
  have hs := mobius_firstPrime_pair_sign d hcop hsf
  calc
    2 * mobiusRealCoefficient d * mobiusRealCoefficient (2*d) / (3 * (d : ℝ)) =
      2 * (mobiusRealCoefficient d * mobiusRealCoefficient (2*d)) / (3 * (d : ℝ)) := by ring
    _ = -(2 / 3 : ℝ) * (1 / (d : ℝ)) := by rw [hs]; ring

/-- A single arithmetic dilation ray cancels logarithmic mass in the
boundary Gamma--Hankel off-diagonal. This is not a full-energy bound. -/
theorem firstPrimeDilationGammaContribution_le (M : ℕ) (hM : 1 ≤ M) :
    firstPrimeDilationGammaContribution M ≤
      -(1 / 12 : ℝ) * Real.log (M : ℝ) + 7 / 12 := by
  have hmass := Sieve.sum_inv_coprime_squarefree_ge
    (M := M) (Q := 2) (by norm_num) (by norm_num) hM (by norm_num)
  rw [firstPrimeDilationGammaContribution_eq]
  nlinarith

/-! ## Every fixed prime ratio supplies the same signed mechanism -/

private theorem mobius_prime_pair_sign (p d : ℕ) (hp : p.Prime)
    (hcop : Nat.Coprime d p) (hsf : Squarefree d) :
    mobiusRealCoefficient d * mobiusRealCoefficient (p*d) = -1 := by
  have hmul := Sieve.moebius_mul_of_coprime hcop.symm
  have hmp : moebius p = -1 := by simpa using ArithmeticFunction.moebius_apply_prime hp
  have hsq : ((moebius d : ℤ) : ℝ) ^ (2 : ℕ) = 1 := by
    have hne : moebius d ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
    rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;> rw [hm] <;> norm_num
  unfold mobiusRealCoefficient
  rw [hmul, hmp]
  push_cast
  nlinarith

/-- Signed `d:pd` Gamma--Hankel entries, restricting to the squarefree cofactors
coprime to both `2` and `p` so a uniform harmonic lower bound applies. -/
noncomputable def primeDilationGammaContribution (p M : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 M).filter
      (fun d => Nat.Coprime d (bandModulus {p}) ∧ Squarefree d),
    2 * mobiusRealCoefficient d * mobiusRealCoefficient (p*d) /
      (((p:ℝ)+1) * (d:ℝ))

/-- Literal shifted-index Gamma--Hankel atom on every prime dilation ray. -/
theorem gamma_prime_pair_atom (p d : ℕ) (hp : 1 ≤ p) (hd : 1 ≤ d) :
    2 * shiftedMobiusRealCoefficient (d-1) *
        shiftedMobiusRealCoefficient (p*d-1) /
        (((d-1) + (p*d-1) + 2 : ℕ) : ℝ) =
      2 * mobiusRealCoefficient d * mobiusRealCoefficient (p*d) /
        (((p:ℝ)+1) * (d:ℝ)) := by
  have hpd : 1 ≤ p*d := Nat.mul_pos hp hd
  have h1 : d-1+1=d := by omega
  have h2 : p*d-1+1=p*d := by omega
  have hden : (d-1)+(p*d-1)+2=(p+1)*d := by
    calc
      (d-1)+(p*d-1)+2 = d+p*d := by omega
      _ = (p+1)*d := by ring
  simp only [shiftedMobiusRealCoefficient, mobiusRealCoefficient, h1, h2, hden]
  push_cast
  ring

theorem primeDilationGammaContribution_eq_matrixSubsum (p M : ℕ) (hp : p.Prime) :
    primeDilationGammaContribution p M =
      ∑ d ∈ (Finset.Icc 1 M).filter
          (fun d => Nat.Coprime d (bandModulus {p}) ∧ Squarefree d),
        2 * shiftedMobiusRealCoefficient (d-1) *
          shiftedMobiusRealCoefficient (p*d-1) /
          (((d-1) + (p*d-1) + 2 : ℕ) : ℝ) := by
  unfold primeDilationGammaContribution
  apply Finset.sum_congr rfl
  intro d hd
  exact (gamma_prime_pair_atom p d hp.one_lt.le
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1).symm

theorem primeDilationGamma_pair_indices_in_cutoff
    (p M d : ℕ) (hd : d ∈ Finset.Icc 1 M) :
    d-1 ∈ Finset.range ((p+1)*M) ∧ p*d-1 ∈ Finset.range ((p+1)*M) := by
  simp only [Finset.mem_range]
  have hd' := Finset.mem_Icc.mp hd
  have hprod := Nat.mul_le_mul_left p hd'.2
  have hcut : (p+1)*M=p*M+M := by ring
  omega

theorem primeDilationGammaContribution_eq (p M : ℕ) (hp : p.Prime) :
    primeDilationGammaContribution p M =
      -(2 / ((p:ℝ)+1)) *
        ∑ d ∈ (Finset.Icc 1 M).filter
          (fun d => Nat.Coprime d (bandModulus {p}) ∧ Squarefree d),
          1 / (d:ℝ) := by
  unfold primeDilationGammaContribution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨_, hcop, hsf⟩ := Finset.mem_filter.mp hd
  have hdvd : p ∣ bandModulus {p} := by
    simp [bandModulus]
  have hcopdp : Nat.Coprime d p := Nat.Coprime.coprime_dvd_right hdvd hcop
  have hs := mobius_prime_pair_sign p d hp hcopdp hsf
  calc
    2 * mobiusRealCoefficient d * mobiusRealCoefficient (p*d) /
        (((p:ℝ)+1) * (d:ℝ)) =
      2 * (mobiusRealCoefficient d * mobiusRealCoefficient (p*d)) /
        (((p:ℝ)+1) * (d:ℝ)) := by ring
    _ = -(2 / ((p:ℝ)+1)) * (1/(d:ℝ)) := by
      rw [hs]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Every fixed prime with reciprocal mass at most `1/8` has a logarithmically
negative ratio channel. No cancellation between different ratios is asserted. -/
theorem primeDilationGammaContribution_le (p M : ℕ) (hp : p.Prime)
    (hpMass : 1 / (p:ℝ) ≤ 1/8) (hM : 1 ≤ M) :
    primeDilationGammaContribution p M ≤
      -(2 / ((p:ℝ)+1)) * ((1/8:ℝ)*Real.log (M:ℝ)-7/8) := by
  have hB : ∀ q ∈ ({p} : Finset ℕ), q.Prime := by simpa using hp
  have hBsum : ∑ q ∈ ({p} : Finset ℕ), 1/(q:ℝ) ≤ 1/8 := by simpa using hpMass
  have hmass := Sieve.sum_inv_coprime_squarefree_ge
    (M:=M) (Q:=bandModulus {p}) (bandModulus_ne_zero hB)
    (two_dvd_bandModulus {p}) hM
    (sum_inv_primeFactors_bandModulus_le hB hBsum)
  rw [primeDilationGammaContribution_eq p M hp]
  have hcoef : 0 ≤ 2 / ((p:ℝ)+1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmass hcoef]

/-- Finite prime-ratio channels combine with no loss: every selected prime
keeps its exact negative coefficient. The theorem does not bound the
complementary composite-ratio channels. -/
theorem sum_primeDilationGammaContribution_le (S : Finset Nat.Primes) (M : ℕ)
    (hS : ∀ p ∈ S, 1/((p:ℕ):ℝ) ≤ 1/8) (hM : 1 ≤ M) :
    (∑ p ∈ S, primeDilationGammaContribution p M) ≤
      -((1/8:ℝ)*Real.log (M:ℝ)-7/8) *
        (∑ p ∈ S, 2/(((p:ℕ):ℝ)+1)) := by
  calc
    (∑ p ∈ S, primeDilationGammaContribution p M) ≤
        ∑ p ∈ S,
          -(2/(((p:ℕ):ℝ)+1)) * ((1/8:ℝ)*Real.log (M:ℝ)-7/8) := by
            apply Finset.sum_le_sum
            intro p hp
            exact primeDilationGammaContribution_le p M p.property (hS p hp) hM
    _ = -((1/8:ℝ)*Real.log (M:ℝ)-7/8) *
        (∑ p ∈ S, 2/(((p:ℕ):ℝ)+1)) := by
          rw [← Finset.sum_mul]
          simp only [Finset.sum_neg_distrib]
          ring

/-! ## Prime-ratio cancellation has unbounded logarithmic coefficient -/

private theorem not_summable_primeDilationWeight :
    ¬ Summable (fun p : Nat.Primes => 2 / (((p:ℕ):ℝ)+1)) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  apply Summable.of_nonneg_of_le (fun p : Nat.Primes => by positivity)
    (fun p : Nat.Primes => ?_) h
  have hp : (1:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast p.property.one_lt.le
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<((p:ℕ):ℝ))
    (by positivity : (0:ℝ)<((p:ℕ):ℝ)+1)).2
  nlinarith

private theorem finite_small_primeDilationWeight :
    Summable (fun p : Nat.Primes =>
      if (p:ℕ)<11 then 2 / (((p:ℕ):ℝ)+1) else 0) := by
  have hfinite : ({p : Nat.Primes | (p:ℕ)<11} : Set Nat.Primes).Finite := by
    change ((Subtype.val : Nat.Primes → ℕ) ⁻¹' Set.Iio 11).Finite
    exact Set.Finite.preimage (fun a _ b _ hab => Subtype.val_injective hab)
      (Set.finite_Iio 11)
  apply summable_of_hasFiniteSupport
  change ({p : Nat.Primes |
    (if (p:ℕ)<11 then 2 / (((p:ℕ):ℝ)+1) else 0) ≠ 0} : Set Nat.Primes).Finite
  apply hfinite.subset
  intro p hp
  by_contra hnot
  change ¬ (p:ℕ)<11 at hnot
  simp [hnot] at hp

private theorem not_summable_large_primeDilationWeight :
    ¬ Summable (fun p : Nat.Primes =>
      if 11 ≤ (p:ℕ) then 2 / (((p:ℕ):ℝ)+1) else 0) := by
  intro hlarge
  apply not_summable_primeDilationWeight
  have hsum := hlarge.add finite_small_primeDilationWeight
  convert hsum using 1
  funext p
  by_cases hp : (p:ℕ)<11
  · simp [hp, Nat.not_le.mpr hp]
  · simp [hp, Nat.le_of_not_gt hp]

/-- The coefficients of finitely many large-prime ratio rays exceed every
prescribed threshold. This uses prime-harmonic divergence, not RH. -/
theorem exists_primeDilationWeight_sum_gt (C : ℝ) :
    ∃ S : Finset Nat.Primes,
      (∀ p ∈ S, 11 ≤ (p:ℕ)) ∧
      C < ∑ p ∈ S, 2 / (((p:ℕ):ℝ)+1) := by
  have hnot := not_summable_large_primeDilationWeight
  have hex : ∃ S : Finset Nat.Primes,
      C < ∑ p ∈ S, if 11 ≤ (p:ℕ) then 2 / (((p:ℕ):ℝ)+1) else 0 := by
    by_contra h
    apply hnot
    apply summable_of_sum_le (fun _ => by positivity)
    intro S
    exact le_of_not_gt (fun hgt => h ⟨S, hgt⟩)
  obtain ⟨S, hS⟩ := hex
  refine ⟨S.filter (fun p => 11 ≤ (p:ℕ)), ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · simpa [Finset.sum_filter] using hS

/-- For every demanded logarithmic slope, finitely many actual prime-dilation
matrix rays have at least that much negative aggregate. Consequently the
complete covariance can stay bounded only through other ratio channels. -/
theorem exists_primeDilationGamma_family_negative_log_slope (C : ℝ) :
    ∃ S : Finset Nat.Primes, ∀ M : ℕ, 1 ≤ M →
      7 ≤ Real.log (M : ℝ) →
      (∑ p ∈ S, primeDilationGammaContribution p M) ≤
        -C * ((1/8:ℝ)*Real.log (M:ℝ)-7/8) := by
  obtain ⟨S, hlarge, hweight⟩ := exists_primeDilationWeight_sum_gt C
  refine ⟨S, fun M hM hlog => ?_⟩
  have hmass : ∀ p ∈ S, 1/((p:ℕ):ℝ) ≤ 1/8 := by
    intro p hp
    have hpR : (11:ℝ) ≤ ((p:ℕ):ℝ) := by exact_mod_cast hlarge p hp
    have hp0 : (0:ℝ) < ((p:ℕ):ℝ) := by exact_mod_cast p.property.pos
    apply (div_le_iff₀ hp0).2
    nlinarith
  have hbound := sum_primeDilationGammaContribution_le S M hmass hM
  have hA : 0 ≤ (1/8:ℝ)*Real.log (M:ℝ)-7/8 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hweight.le hA
  nlinarith

end RHTower
